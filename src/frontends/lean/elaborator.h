/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <vector>
#include "util/list.h"
#include "kernel/metavar.h"
#include "kernel/type_checker.h"
#include "library/expr_lt.h"
#include "library/unifier.h"
#include "library/tactic/tactic.h"
#include "frontends/lean/elaborator_context.h"
#include "frontends/lean/coercion_elaborator.h"
#include "frontends/lean/util.h"
#include "frontends/lean/local_context.h"
#include "frontends/lean/calc_proof_elaborator.h"

namespace lean {
/** \brief Mapping from metavariable names to metavariable applications (?M ...) */
typedef name_map<expr> mvar2meta;

/** \brief Helper class for implementing the \c elaborate functions. */
class elaborator : public coercion_info_manager {
    typedef name_map<expr> local_tactic_hints;
    typedef rb_map<expr, pair<expr, constraint_seq>, expr_quick_cmp> cache;
    typedef std::vector<pair<expr, expr>> to_check_sorts;
    elaborator_context & m_ctx;
    name_generator       m_ngen;
    type_checker_ptr     m_tc[2];
    // mapping from metavariable ?m to the (?m l_1 ... l_n) where [l_1 ... l_n] are the local constants
    // representing the context where ?m was created.
    local_context        m_context; // current local context: a list of local constants
    local_context        m_full_context; // superset of m_context, it also contains non-contextual locals.
    mvar2meta            m_mvar2meta;
    // Set of metavariable that where created when m_relax_main_opaque flag is set to true.
    name_set             m_relaxed_mvars;
    cache                m_cache;
    // The following vector contains sorts that we should check
    // whether the computed universe is too specific or not.
    to_check_sorts       m_to_check_sorts;

    // mapping from metavariable name ?m to tactic expression that should be used to solve it.
    // this mapping is populated by the 'by tactic-expr' expression.
    local_tactic_hints   m_local_tactic_hints;
    // set of metavariables that we already reported unsolved/unassigned
    name_set             m_displayed_errors;
    // if m_relax_main_opaque is true, then treat opaque definitions from the main module as transparent.
    bool                 m_relax_main_opaque;
    // if m_no_info is true, we do not collect information when true,
    // we set is to true whenever we find no_info annotation.
    bool                 m_no_info;
    bool                 m_use_tactic_hints;
    info_manager         m_pre_info_data;
    bool                 m_has_sorry;
    unifier_config       m_unifier_config;
    // If m_nice_mvar_names is true, we append (when possible) a more informative name for a metavariable.
    // That is, whenever a metavariables comes from a binding, we add the binding name as a suffix
    bool                 m_nice_mvar_names;
    struct choice_expr_elaborator;

    environment const & env() const { return m_ctx.m_env; }
    io_state const & ios() const { return m_ctx.m_ios; }
    local_decls<level> const & lls() const { return m_ctx.m_lls; }
    bool use_local_instances() const { return m_ctx.m_use_local_instances; }
    info_manager * infom() const { return m_ctx.m_info_manager; }
    pos_info_provider const * pip() const { return m_ctx.m_pos_provider; }
    bool check_unassigned() const { return m_ctx.m_check_unassigned; }

    expr mk_local(name const & n, expr const & t, binder_info const & bi);

    pair<expr, constraint_seq> infer_type(expr const & e) { return m_tc[m_relax_main_opaque]->infer(e); }
    pair<expr, constraint_seq> whnf(expr const & e) { return m_tc[m_relax_main_opaque]->whnf(e); }
    expr infer_type(expr const & e, constraint_seq & s) { return m_tc[m_relax_main_opaque]->infer(e, s); }
    expr whnf(expr const & e, constraint_seq & s) { return m_tc[m_relax_main_opaque]->whnf(e, s); }
    expr mk_app(expr const & f, expr const & a, tag g) { return ::lean::mk_app(f, a, g); }

    void register_meta(expr const & meta);

    optional<expr> mvar_to_meta(expr const & mvar);
    void save_type_data(expr const & e, expr const & r);
    void save_binder_type(expr const & e, expr const & r);
    void save_extra_type_data(expr const & e, expr const & r);
    void save_proof_state_info(proof_state const & ps, expr const & e);
    void save_identifier_info(expr const & f);
    void save_synth_data(expr const & e, expr const & r);
    void save_placeholder_info(expr const & e, expr const & r);
    virtual void save_coercion_info(expr const & e, expr const & c);
    virtual void erase_coercion_info(expr const & e);
    void copy_info_to_manager(substitution s);
    /** \brief If info manager is being used, then create a metavariable suffix based on binding_name(b) */
    optional<name> mk_mvar_suffix(expr const & b);
    expr mk_placeholder_meta(optional<name> const & suffix, optional<expr> const & type,
                             tag g, bool is_strict, bool inst_implicit, constraint_seq & cs);
    expr mk_placeholder_meta(optional<expr> const & type, tag g, bool is_strict, bool inst_implicit, constraint_seq & cs) {
        return mk_placeholder_meta(optional<name>(), type, g, is_strict, inst_implicit, cs);
    }

    expr visit_expecting_type(expr const & e, constraint_seq & cs);
    expr visit_expecting_type_of(expr const & e, expr const & t, constraint_seq & cs);
    expr visit_choice(expr const & e, optional<expr> const & t, constraint_seq & cs);
    expr visit_by(expr const & e, optional<expr> const & t, constraint_seq & cs);
    expr visit_proof_qed(expr const & e, optional<expr> const & t, constraint_seq & cs);
    expr visit_calc_proof(expr const & e, optional<expr> const & t, constraint_seq & cs);
    expr add_implict_args(expr e, constraint_seq & cs, bool relax);
    pair<expr, expr> ensure_fun(expr f, constraint_seq & cs);
    bool has_coercions_from(expr const & a_type);
    bool has_coercions_to(expr d_type);
    expr apply_coercion(expr const & a, expr a_type, expr d_type);
    pair<expr, constraint_seq> mk_delayed_coercion(expr const & a, expr const & a_type, expr const & expected_type,
                                                   justification const & j);
    pair<expr, constraint_seq> ensure_has_type(expr const & a, expr const & a_type, expr const & expected_type,
                                               justification const & j, bool relax);
    bool is_choice_app(expr const & e);
    expr visit_choice_app(expr const & e, constraint_seq & cs);
    expr visit_app(expr const & e, constraint_seq & cs);
    expr visit_placeholder(expr const & e, constraint_seq & cs);
    level replace_univ_placeholder(level const & l);
    expr visit_sort(expr const & e);
    expr visit_macro(expr const & e, constraint_seq & cs);
    expr visit_constant(expr const & e);
    expr ensure_type(expr const & e, constraint_seq & cs);
    expr instantiate_rev_locals(expr const & a, unsigned n, expr const * subst);
    expr visit_binding(expr e, expr_kind k, constraint_seq & cs);
    expr visit_pi(expr const & e, constraint_seq & cs);
    expr visit_lambda(expr const & e, constraint_seq & cs);
    expr visit_typed_expr(expr const & e, constraint_seq & cs);
    expr visit_let_value(expr const & e, constraint_seq & cs);
    bool is_sorry(expr const & e) const;
    expr visit_sorry(expr const & e);
    expr visit_core(expr const & e, constraint_seq & cs);
    pair<expr, constraint_seq> visit(expr const & e);
    expr visit(expr const & e, constraint_seq & cs);
    unify_result_seq solve(constraint_seq const & cs);
    void display_unsolved_proof_state(expr const & mvar, proof_state const & ps, char const * msg, expr const & pos);
    void display_unsolved_proof_state(expr const & mvar, proof_state const & ps, char const * msg);
    optional<expr> get_pre_tactic_for(expr const & mvar);
    optional<tactic> pre_tactic_to_tactic(expr const & pre_tac);
    bool try_using(substitution & subst, expr const & mvar, proof_state const & ps, tactic const & tac,
                   bool show_failure);
    void try_using_begin_end(substitution & subst, expr const & mvar, proof_state ps, expr const & pre_tac);
    void solve_unassigned_mvar(substitution & subst, expr mvar, name_set & visited);
    expr solve_unassigned_mvars(substitution & subst, expr e, name_set & visited);
    expr solve_unassigned_mvars(substitution & subst, expr const & e);
    void display_unassigned_mvars(expr const & e, substitution const & s);
    void check_sort_assignments(substitution const & s);
    expr apply(substitution & s, expr const & e, name_set & univ_params, buffer<name> & new_params);
    std::tuple<expr, level_param_names> apply(substitution & s, expr const & e);
    pair<expr, constraints> elaborate_nested(list<expr> const & g, expr const & e,
                                             bool relax, bool use_tactic_hints);
public:
    elaborator(elaborator_context & ctx, name_generator const & ngen, bool nice_mvar_names = false);
    std::tuple<expr, level_param_names> operator()(list<expr> const & ctx, expr const & e, bool _ensure_type,
                                                   bool relax_main_opaque);
    std::tuple<expr, expr, level_param_names> operator()(expr const & t, expr const & v, name const & n, bool is_opaque);
};

std::tuple<expr, level_param_names> elaborate(elaborator_context & env, list<expr> const & ctx, expr const & e,
                                              bool relax_main_opaque, bool ensure_type = false, bool nice_mvar_names = false);

std::tuple<expr, expr, level_param_names> elaborate(elaborator_context & env, name const & n, expr const & t, expr const & v,
                                                    bool is_opaque);
void initialize_elaborator();
void finalize_elaborator();
}
