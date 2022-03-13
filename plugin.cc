///
/// Add control-flow checking instructions as described in "Control-Flow
/// Checking by Software Signatures."
/// 
/// Author: Bohan Lei <garthlei@pku.edu.cn>
/// Date: 8 November 2021
///
#include "gcc-plugin.h"
#include "context.h"
#include "tree.h"
#include "rtl.h"
#include "plugin-version.h"
#include "tree-pass.h"
#include <iostream>
#include <map>
#include <vector>

typedef uint8_t cfcss_sig_t;

#define BUF_SIZE 64

// This plugin is licensed under GPL.
#ifdef _WIN32
__declspec(dllexport)
#endif
int plugin_is_GPL_compatible;

class pass_cfcss : public rtl_opt_pass {
public:
  pass_cfcss() : rtl_opt_pass({
    RTL_PASS,
    "cfcss",
    OPTGROUP_NONE,
    TV_INTEGRATION,
    0,
    0,
    0,
    0,
    0
  }, new gcc::context) {
    sub = nullptr;
    next = nullptr;
    static_pass_number = 0;
  }

  opt_pass *clone() override { return this; }

  bool gate(function *fun) override { return true; }

  unsigned int execute(function *fun) override;
};

unsigned int pass_cfcss::execute(function *fun) {
  // The signatures of basic blocks.
  std::map<basic_block, cfcss_sig_t> sig;

  // Signature differences.
  std::map<basic_block, cfcss_sig_t> diff;

  // Call sites.
  std::vector<std::pair<rtx_call_insn *, basic_block>> call_sites;

  // Conditional branches before adjusting signature assignments for
  // fall-through multi-fan-in successors.
  std::vector<edge> fall_thru_sigs;
  // std::vector<gimple *> fall_thru_sigs;

  // A temporary accumulator.
  cfcss_sig_t acc = 0;

  // Adjusting signature values.
  std::map<basic_block, cfcss_sig_t> dmap;

  // Adjusting signature values for fall-through multi-fan-in successors.
  std::map<basic_block, cfcss_sig_t> dmap_fall_thru;

  // Basic block.
  basic_block bb;

  // Instruction.
  rtx_insn *insn;

  // Assembly expression (ASM_OPERANDS).
  rtx asm_expr;

  // Instruction string buffer.
  char asm_str_buf[BUF_SIZE];

  // Heap-allocated instruction C-style string pointer.
  char *asm_str;

  // Whether a tail call is encountered.
  bool is_tail_call;

  push_cfun(fun);

  FOR_EACH_BB_FN (bb, fun) {
    // Find all the call statements. The basic blocks are to be split after
    // those statements because subroutine calls can bring changes to the CRC
    // signature.
    bool is_last = true;
    FOR_BB_INSNS_REVERSE (bb, insn) {
      if (CALL_P(insn) && !is_last && !SIBLING_CALL_P(insn))
        call_sites.push_back(std::make_pair(as_a<rtx_call_insn *>(insn), bb));  
      if (NONDEBUG_INSN_P(insn))
        is_last = false;
    }
  }

  for (auto &pair : call_sites) {
    auto stmt = pair.first;
    auto bb = pair.second;
    auto next_bb = split_block(bb, stmt);
    if (dump_file != nullptr)
      fprintf(dump_file, "new block %d due to call site %d\n",
          next_bb->dest->index, INSN_UID(stmt));
  }

  FOR_EACH_BB_FN (bb, fun) {
    // Naïve approach to assign signatures.
    sig[bb] = acc++;
  }


  FOR_EACH_BB_FN (bb, fun) {
    if (EDGE_COUNT(bb->preds) == 1) {
      diff[bb] = sig[(*bb->preds)[0]->src] ^ sig[bb];
    } else if (EDGE_COUNT(bb->preds) >= 2) {
      basic_block base_pred = nullptr;
      for (edge pred_edge : *bb->preds) {
        base_pred = pred_edge->src;
        break;
      }

      diff[bb] = sig[base_pred] ^ sig[bb];
    
      for (edge pred_edge : *bb->preds) {
        // D[i, m] = s[i, 1] XOR s[i, m]
        dmap[pred_edge->src] = sig[pred_edge->src] ^ sig[base_pred];
      }
    } else {
      diff[bb] = sig[bb];
    }
  }

  FOR_EACH_BB_FN (bb, fun) {
    // A second adjusting signature has to be assigned when
    // (a) Both successors are multi-fan-in basic blocks, and
    // (b) The base predecessor of each successor is different.
    if (EDGE_COUNT(bb->succs) == 2
        && EDGE_COUNT((*bb->succs)[0]->dest->preds) > 1
        && EDGE_COUNT((*bb->succs)[1]->dest->preds) > 1
        && (*(*bb->succs)[0]->dest->preds)[0]->src
          != (*(*bb->succs)[1]->dest->preds)[0]->src) {
      // We have to split the fallthru edge instead of the branch edge.
      // In fact, if the branch edge were split and the destination block
      // had a fallthru multi-fan-out predecessor, that edge would also
      // be split, leading to messy problems.
      edge fallthru_edge = FALLTHRU_EDGE(bb);
      gcc_assert(fallthru_edge->flags & EDGE_FALLTHRU);
      fall_thru_sigs.push_back(fallthru_edge);
      auto br_target = BRANCH_EDGE(bb)->dest;
      dmap[bb] = sig[bb] ^ sig[(*br_target->preds)[0]->src];
    }
  }

  for (auto orig_edge : fall_thru_sigs) {
    auto pred_bb = orig_edge->src;
    auto succ_bb = orig_edge->dest;
    if (dump_file)
      fprintf(dump_file, "edge <bb %d>-><bb %d> split due to special case\n",
          pred_bb->index, succ_bb->index);
    cfcss_sig_t dmap_val = sig[pred_bb] ^ sig[(*succ_bb->preds)[0]->src];
    if ((orig_edge->flags & EDGE_ABNORMAL) != 0)
      return 0;
    bb = split_edge(orig_edge);
    gcc_assert(sig.find(pred_bb) != sig.end());
    sig[bb] = sig[pred_bb];
    diff[bb] = 0;
    dmap[bb] = dmap_val;
  }

  FOR_EACH_BB_FN (bb, fun) {
    if (dump_file)
      fprintf(dump_file, "bb %d:\n", bb->index);
    auto insert_ptr = BB_HEAD(bb);
    while (insert_ptr && insert_ptr != NEXT_INSN(BB_END(bb))
           && !NONDEBUG_INSN_P(insert_ptr))
      insert_ptr = NEXT_INSN(insert_ptr);
    gcc_assert(sig.find(bb) != sig.end());
    cfcss_sig_t cur_sig = sig[bb];
    cfcss_sig_t cur_diff = diff[bb];
    cfcss_sig_t cur_adj = dmap.find(bb) != dmap.end() ? dmap[bb] : 0;

    

    if (EDGE_COUNT(bb->preds) >= 2) {
      sprintf(asm_str_buf, "ctrlsig_m %d,%d,%d", cur_diff, cur_sig, cur_adj);
      asm_str = new char[strlen(asm_str_buf) + 1];
      strcpy(asm_str, asm_str_buf);
      asm_expr = gen_rtx_ASM_OPERANDS (VOIDmode, asm_str, "", 0,
          rtvec_alloc (0), rtvec_alloc (0),
          rtvec_alloc (0), UNKNOWN_LOCATION);
    } else {
      sprintf(asm_str_buf, "ctrlsig_s %d,%d,%d", cur_diff, cur_sig, cur_adj);
      asm_str = new char[strlen(asm_str_buf) + 1];
      strcpy(asm_str, asm_str_buf);
      asm_expr = gen_rtx_ASM_OPERANDS (VOIDmode, asm_str, "", 0,
          rtvec_alloc (0), rtvec_alloc (0),
          rtvec_alloc (0), UNKNOWN_LOCATION);
    }
    MEM_VOLATILE_P(asm_expr) = true;
    insn = make_insn_raw(asm_expr);
    if (dump_file)
      fprintf(dump_file, "inserting ctrlsig before uid %d\n",
          INSN_UID(insert_ptr));
    add_insn_before(insn, insert_ptr, bb);
    insert_ptr = insn;
    if (insert_ptr == NEXT_INSN(BB_END(bb)))
      BB_END(bb) = insn;

    if (EDGE_COUNT(bb->preds) > 0
        && (*bb->preds)[0]->src == fun->cfg->x_entry_block_ptr) {
      if (dump_file)
        fprintf(dump_file, "inserting pushsig before uid %d\n",
            INSN_UID(insert_ptr));
      asm_expr = gen_rtx_ASM_OPERANDS (VOIDmode, "pushsig", "", 0,
          rtvec_alloc (0), rtvec_alloc (0),
          rtvec_alloc (0), UNKNOWN_LOCATION);
      MEM_VOLATILE_P(asm_expr) = true;
      add_insn_before(make_insn_raw(asm_expr), insert_ptr, bb);
    }

    insert_ptr = BB_END(bb);
    while (insert_ptr && !NONDEBUG_INSN_P(insert_ptr))
      insert_ptr = PREV_INSN(insert_ptr);
    is_tail_call = false;
    if (CALL_P(insert_ptr) && SIBLING_CALL_P(insert_ptr))
      is_tail_call = true;
    if (CALL_P(insert_ptr) || JUMP_P(insert_ptr))
      do insert_ptr = PREV_INSN(insert_ptr);
      while (insert_ptr && !NONDEBUG_INSN_P(insert_ptr));
    if (CALL_P(insert_ptr) && SIBLING_CALL_P(insert_ptr)) {
      is_tail_call = true;
      do insert_ptr = PREV_INSN(insert_ptr);
      while (insert_ptr && !NONDEBUG_INSN_P(insert_ptr));
    }
    sprintf(asm_str_buf, "crcsig 0x%x",
            ((fun->funcdef_no << 8) + bb->index) & 0xffff);
    asm_str = new char[strlen(asm_str_buf) + 1];
    strcpy(asm_str, asm_str_buf);
    asm_expr = gen_rtx_ASM_OPERANDS (VOIDmode, asm_str, "", 0,
        rtvec_alloc (0), rtvec_alloc (0),
        rtvec_alloc (0), UNKNOWN_LOCATION);
    MEM_VOLATILE_P(asm_expr) = true;
    insn = make_insn_raw(asm_expr);
    if (dump_file)
      fprintf(dump_file, "inserting crcsig after uid %d\n",
          INSN_UID(insert_ptr));
    add_insn_after(insn, insert_ptr, bb);
    insert_ptr = insn;

    if ((EDGE_COUNT(bb->succs) > 0
         && (*bb->succs)[0]->dest == fun->cfg->x_exit_block_ptr)
        || EDGE_COUNT(bb->succs) == 0
        || is_tail_call) {
      asm_expr = gen_rtx_ASM_OPERANDS (VOIDmode, "popsig", "", 0,
          rtvec_alloc (0), rtvec_alloc (0),
          rtvec_alloc (0), UNKNOWN_LOCATION);
      MEM_VOLATILE_P(asm_expr) = true;
      insn = make_insn_raw(asm_expr);
      if (dump_file)
        fprintf(dump_file, "inserting popsig after uid %d\n",
            INSN_UID(insert_ptr));
      add_insn_after(insn, insert_ptr, bb);
    }
  }

  pop_cfun();

  return 0;
}

pass_cfcss pass_inst;

#ifdef _WIN32
__declspec(dllexport)
#endif
int plugin_init(plugin_name_args *plugin_info, plugin_gcc_version *version) {
  register_pass_info pass_info({
    &pass_inst,
    "*free_cfg",
    0,
    PASS_POS_INSERT_BEFORE
  });

  if (!plugin_default_version_check(version, &gcc_version))
    return 1;

  register_callback(
    plugin_info->base_name,
    PLUGIN_PASS_MANAGER_SETUP,
    nullptr,
    &pass_info
  );
  
  return 0;
}
