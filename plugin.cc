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
#include "cgraph.h"
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

class pass_cfcss : public simple_ipa_opt_pass {
public:
  pass_cfcss() : simple_ipa_opt_pass({
    SIMPLE_IPA_PASS,
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

  // Procedure call-related predecessors.
  std::multimap<basic_block, basic_block> pred_set;

  // Call sites represented by edges.
  std::vector<cgraph_edge *> call_sites;

  // Calls of functions not defined in the current module.
  std::vector<cgraph_edge *> call_sites_undef;

  // Conditional branches before adjusting signature assignments for
  // fall-through multi-fan-in successors.
  std::vector<std::pair<function *, gimple *>> fall_thru_sigs;

  // The number of clones of a function.
  std::map<cgraph_node *, size_t> num_clones;

  // The duplicate function number for a call site.
  std::map<cgraph_edge *, size_t> dup_num;

  // The clones of a function.
  std::map<std::pair<cgraph_node *, size_t>, cgraph_node *> clones;

  // A temporary accumulator.
  cfcss_sig_t acc = 0;

  // Adjusting signature values.
  std::map<basic_block, cfcss_sig_t> dmap;

  // Adjusting signature values for fall-through multi-fan-in successors.
  std::map<basic_block, cfcss_sig_t> dmap_fall_thru;

  // Call-graph code.
  cgraph_node *node;

  // Basic block.
  basic_block bb;

  // Look for the call sites. Those that invoke functions defined in this
  // module are used for interprocedural analysis, while those invoking
  // undefined functions are used to add pushsig/popsig instructions.
  FOR_EACH_FUNCTION (node) {
    // We do not rule out the compiler-created clones.
    if (!node->has_gimple_body_p())
      continue;
    for (auto it = node->callees; it != nullptr; it = it->next_callee) {
        if (it->callee->has_gimple_body_p()) {
          
          // Splitting the basic block now can affect the iteration, so we
          // choose to move the splitting part outside.
          call_sites.push_back(it);

          if (num_clones.find(it->callee) == num_clones.end()) {
            num_clones[it->callee] = 1;
          } else {
            ++num_clones[it->callee];
          }

          dup_num[it] = num_clones[it->callee] - 1;
        } else {
          call_sites_undef.push_back(it);
        }
    }
  }

  FOR_EACH_FUNCTION (node) {
    if (!node->has_gimple_body_p())
      continue;
    clones[std::make_pair(node, 0)] = node;
    for (size_t i = 1; i < num_clones[node]; ++i) {
      cgraph_node *new_fun =
        node->create_version_clone_with_body(vNULL, nullptr, nullptr, nullptr,
                                             nullptr, "");
      auto it2 = node->callees;
      while (it2->next_callee) it2 = it2->next_callee;
      for (auto it1 = new_fun->callees;
           it1 != nullptr; it1 = it1->next_callee, it2 = it2->prev_callee) {
        if (it1->callee != it2->callee) {
          std::cerr << "Fatal error in CFCSS plugin:" << std::endl;
          std::cerr << "it1->callee != it2->callee" << std::endl;
          return -1;
        }
        if (it1->callee->has_gimple_body_p()) {
          call_sites.push_back(it1);
          dup_num[it1] = dup_num[it2];
        }
      }
      clones[std::make_pair(node, i)] = new_fun;
    }
  }

  for (auto call_site : call_sites) {
    push_cfun(call_site->caller->get_fun());
    call_site->redirect_callee(clones[std::make_pair(call_site->callee,
                                                     dup_num[call_site])]);
    cgraph_edge::redirect_call_stmt_to_callee(call_site);
    split_block(call_site->call_stmt->bb, call_site->call_stmt);

    pop_cfun();
  }

  // We have to use a new for-loop to find the predecessors of blocks after
  // calls and entry blocks, because basic blocks containing call statements
  // and the return statement might have been splitted. The basic blocks of
  // call statements are not dealt this way in the LLVM version of the pass,
  // because the call sites in the same basic block in that version are in the
  // execution order, which is not true in the GCC version.
  for (auto call_site: call_sites) {
    pred_set.insert(
      std::make_pair(ENTRY_BLOCK_PTR_FOR_FN(
        call_site->callee->get_fun())->next_bb, call_site->call_stmt->bb));
    FOR_EACH_BB_FN (bb, call_site->callee->get_fun())
      for (auto i = gsi_start_bb(bb); !gsi_end_p(i); gsi_next(&i))
        if (gimple_code(gsi_stmt(i)) == GIMPLE_RETURN)
          pred_set.insert(
              std::make_pair((*call_site->call_stmt->bb->succs)[0]->dest, bb));
  }

  FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (node) {
    FOR_EACH_BB_FN (bb, node->get_fun()) {
      // Naïve approach to assign signatures.
      sig[bb] = acc++;
    }
  }

  FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (node)
    FOR_EACH_BB_FN (bb, node->get_fun()) {
      size_t pred_set_len = pred_set.count(bb);
      auto pred_set_range = pred_set.equal_range(bb);

      if (pred_set_len == 1) {
        diff[bb] = sig[pred_set_range.first->second] ^ sig[bb];
      } else if (pred_set_len >= 2) {
        basic_block base_pred = pred_set_range.first->second;

        diff[bb] = sig[base_pred] ^ sig[bb];

        for (auto i = pred_set_range.first; i != pred_set_range.second; ++i) {
          // D[i, m] = s[i, 1] XOR s[i, m]
          dmap[i->second] = sig[i->second] ^ sig[base_pred];
        }
      } else if (bb->preds->length() == 1) {
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

  FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (node)
    FOR_EACH_BB_FN (bb, node->get_fun()) {
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
        fall_thru_sigs.push_back(std::make_pair(node->get_fun(), gsi_stmt(gsi)));
        auto br_target = (*bb->succs)[0]->dest;
        dmap[bb] = sig[bb] ^ sig[(*br_target->preds)[0]->src];
      }
    }

  for (cgraph_edge *edge : call_sites_undef) {
    auto gsi = gsi_for_stmt(edge->call_stmt);
    auto stmt = gimple_build_asm_vec(
      ".insn r CUSTOM_1, 0, 0, x2, x0, x0",
      nullptr, nullptr, nullptr, nullptr
    );
    
    gsi_insert_before(&gsi, stmt, GSI_SAME_STMT);
    gimple_asm_set_volatile(stmt, true);
    gimple_set_modified(stmt, false);
    stmt = gimple_build_asm_vec(
      ".insn r CUSTOM_1, 0, 0, x3, x0, x0",
      nullptr, nullptr, nullptr, nullptr
    );
    gsi_insert_after(&gsi, stmt, GSI_SAME_STMT);
    gimple_asm_set_volatile(stmt, true);
    gimple_set_modified(stmt, false);
  }

  for (auto &pair : fall_thru_sigs) {
    fprintf(stderr, "Control flow checking note: SPECIAL CASE\n");
    push_cfun(pair.first);
    auto pred_bb = pair.second->bb;
    auto orig_edge = (*pred_bb->succs)[1];
    auto succ_bb = orig_edge->dest;
    cfcss_sig_t dmap_val = sig[pred_bb] ^ sig[(*succ_bb->preds)[0]->src];
    bb = split_edge(orig_edge);
    sig[bb] = sig[pred_bb];
    diff[bb] = 0;
    dmap[bb] = dmap_val;
    pop_cfun();
  }


  FOR_EACH_FUNCTION_WITH_GIMPLE_BODY (node) {
    push_cfun(node->get_fun());
    FOR_EACH_BB_FN (bb, cfun) {
      auto gsi = gsi_after_labels(bb);
      gasm *stmt = nullptr;

      cfcss_sig_t cur_sig = sig[bb];
      cfcss_sig_t cur_diff = diff[bb];
      cfcss_sig_t cur_adj = dmap.find(bb) != dmap.end() ? dmap[bb] : 0;

      if (bb->preds->length() >= 2 || pred_set.count(bb) >= 2)
        stmt = gimple_build_asm_vec(inst_ctrlsig_m(cur_diff, cur_sig, cur_adj),
                                    nullptr, nullptr, nullptr, nullptr);
      else
        stmt = gimple_build_asm_vec(inst_ctrlsig_s(cur_diff, cur_sig, cur_adj),
                                    nullptr, nullptr, nullptr, nullptr);
      gimple_asm_set_volatile(stmt, true);
      gsi_insert_before(&gsi, stmt, GSI_SAME_STMT);
    }
    pop_cfun();
  }

  return 0;
}

pass_cfcss pass_inst;

#ifdef _WIN32
__declspec(dllexport)
#endif
int plugin_init(plugin_name_args *plugin_info, plugin_gcc_version *version) {
  register_pass_info pass_info({
    &pass_inst,
    "pta",
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
