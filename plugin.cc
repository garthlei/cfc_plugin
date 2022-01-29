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
#include "gimple.h"
#include "gimple-iterator.h"
#include "plugin-version.h"
#include "tree-pass.h"
#include "util.h"
#include <iostream>
#include <map>
#include <vector>

typedef uint8_t cfcss_sig_t;

// This plugin is licensed under GPL.
#ifdef _WIN32
__declspec(dllexport)
#endif
int plugin_is_GPL_compatible;

class pass_cfcss : public gimple_opt_pass {
public:
  pass_cfcss() : gimple_opt_pass({
    GIMPLE_PASS,
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

  // Conditional branches before adjusting signature assignments for
  // fall-through multi-fan-in successors.
  std::vector<gimple *> fall_thru_sigs;

  // A temporary accumulator.
  cfcss_sig_t acc = 0;

  // Adjusting signature values.
  std::map<basic_block, cfcss_sig_t> dmap;

  // Adjusting signature values for fall-through multi-fan-in successors.
  std::map<basic_block, cfcss_sig_t> dmap_fall_thru;

  // Basic block.
  basic_block bb;

  push_cfun(fun);

  FOR_EACH_BB_FN (bb, fun) {
    // Naïve approach to assign signatures.
    sig[bb] = acc++;
  }


  FOR_EACH_BB_FN (bb, fun) {
    if (bb->preds->length() == 1) {
      diff[bb] = sig[(*bb->preds)[0]->src] ^ sig[bb];
    } else if (bb->preds->length() >= 2) {
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
    if (bb->succs->length() == 2
        && (*bb->succs)[0]->dest->preds->length() > 1
        && (*bb->succs)[1]->dest->preds->length() > 1
        && (*(*bb->succs)[0]->dest->preds)[0]->src
          != (*(*bb->succs)[1]->dest->preds)[0]->src) {
      auto gsi = gsi_last_bb(bb);

      // No fallthru edges are allowed according to the semantics of
      // gimple_cond. Here, we simply assume the 1-indexed one is the
      // fallthru edge.
      basic_block fallthru_succ = (*bb->succs)[1]->dest;
      fall_thru_sigs.push_back(gsi_stmt(gsi));
      auto br_target = (*bb->succs)[0]->dest;
      dmap[bb] = sig[bb] ^ sig[(*br_target->preds)[0]->src];
    }
  }

  for (auto stmt : fall_thru_sigs) {
    fprintf(stderr, "Control flow checking note: SPECIAL CASE\n");
    auto pred_bb = stmt->bb;
    auto orig_edge = (*pred_bb->succs)[1];
    auto succ_bb = orig_edge->dest;
    cfcss_sig_t dmap_val = sig[pred_bb] ^ sig[(*succ_bb->preds)[0]->src];
    bb = split_edge(orig_edge);
    sig[bb] = sig[pred_bb];
    diff[bb] = 0;
    dmap[bb] = dmap_val;
  }


  FOR_EACH_BB_FN (bb, fun) {
    auto gsi = gsi_after_labels(bb);
    gasm *stmt = nullptr;

    cfcss_sig_t cur_sig = sig[bb];
    cfcss_sig_t cur_diff = diff[bb];
    cfcss_sig_t cur_adj = dmap.find(bb) != dmap.end() ? dmap[bb] : 0;

    if (bb->preds->length() >= 2)
      stmt = gimple_build_asm_vec(inst_ctrlsig_m(cur_diff, cur_sig, cur_adj),
                                  nullptr, nullptr, nullptr, nullptr);
    else
      stmt = gimple_build_asm_vec(inst_ctrlsig_s(cur_diff, cur_sig, cur_adj),
                                  nullptr, nullptr, nullptr, nullptr);
    gimple_asm_set_volatile(stmt, true);
    gsi_insert_before(&gsi, stmt, GSI_NEW_STMT);

    if ((*bb->preds)[0]->src == fun->cfg->x_entry_block_ptr) {
      stmt = gimple_build_asm_vec(
        ".insn r CUSTOM_1, 0, 0, x2, x0, x0",
        nullptr, nullptr, nullptr, nullptr
      );
      gsi_insert_before(&gsi, stmt, GSI_SAME_STMT);
      gimple_asm_set_volatile(stmt, true);
      gimple_set_modified(stmt, false);
    }

    if ((*bb->succs)[0]->dest == fun->cfg->x_exit_block_ptr) {
      gsi = gsi_last_bb(bb);
      stmt = gimple_build_asm_vec(
        ".insn r CUSTOM_1, 0, 0, x3, x0, x0",
        nullptr, nullptr, nullptr, nullptr
      );
      gsi_insert_before(&gsi, stmt, GSI_SAME_STMT);
      gimple_asm_set_volatile(stmt, true);
      gimple_set_modified(stmt, false);
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
    "cfg",
    0,
    PASS_POS_INSERT_AFTER
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
