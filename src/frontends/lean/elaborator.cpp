/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <vector>
#include "util/flet.h"
#include "util/list_fn.h"
#include "util/lazy_list_fn.h"
#include "util/sstream.h"
#include "util/name_map.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/kernel_exception.h"
#include "kernel/error_msgs.h"
#include "kernel/free_vars.h"
#include "library/coercion.h"
#include "library/placeholder.h"
#include "library/choice.h"
#include "library/explicit.h"
#include "library/reducible.h"
#include "library/locals.h"
#include "library/deep_copy.h"
#include "library/tactic/tactic.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/error_handling/error_handling.h"
#include "frontends/lean/local_decls.h"
#include "frontends/lean/class.h"
#include "frontends/lean/tactic_hint.h"
#include "frontends/lean/info_manager.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/info_annotation.h"
#include "frontends/lean/local_context.h"
#include "frontends/lean/choice_iterator.h"
#include "frontends/lean/placeholder_elaborator.h"
#include "frontends/lean/proof_qed_elaborator.h"
#include "frontends/lean/calc_proof_elaborator.h"
#include "frontends/lean/info_tactic.h"
#include "frontends/lean/pp_options.h"
#include "frontends/lean/begin_end_ext.h"
#include "frontends/lean/elaborator_exception.h"
#include "frontends/lean/calc.h"

namespace lean {
/** \brief 'Choice' expressions <tt>(choice e_1 ... e_n)</tt> are mapped into a metavariable \c ?m
    and a choice constraints <tt>(?m in fn)</tt> where \c fn is a choice function.
    The choice function produces a stream of alternatives. In this case, it produces a stream of
    size \c n, one alternative for each \c e_i.
    This is a helper class for implementing this choice functions.
*/
struct elaborator::choice_expr_elaborator : public choice_iterator {
    elaborator &  m_elab;
    local_context m_context;
    local_context m_full_context;
    expr          m_meta;
    expr          m_choice;
    unsigned      m_idx;
    bool          m_relax_main_opaque;
    choice_expr_elaborator(elaborator & elab, local_context const & ctx, local_context const & full_ctx,
                           expr const & meta, expr const & c, bool relax):
        m_elab(elab), m_context(ctx), m_full_context(full_ctx), m_meta(meta), m_choice(c),
        m_idx(get_num_choices(m_choice)),
        m_relax_main_opaque(relax) {
    }

    virtual optional<constraints> next() {
        while (m_idx > 0) {
            --m_idx;
            expr const & c = get_choice(m_choice, m_idx);
            expr const & f = get_app_fn(c);
            m_elab.save_identifier_info(f);
            try {
                flet<local_context> set1(m_elab.m_context,      m_context);
                flet<local_context> set2(m_elab.m_full_context, m_full_context);
                pair<expr, constraint_seq> rcs = m_elab.visit(c);
                expr r = rcs.first;
                constraint_seq cs = mk_eq_cnstr(m_meta, r, justification(), m_relax_main_opaque) + rcs.second;
                return optional<constraints>(cs.to_list());
            } catch (exception &) {}
        }
        return optional<constraints>();
    }
};

/** \brief Helper class for implementing the \c elaborate functions. */
class elaborator {
    typedef list<expr> context;
    typedef std::vector<constraint> constraint_vect;
    typedef name_map<expr> local_tactic_hints;
    typedef name_map<expr> mvar2meta;
    typedef std::unique_ptr<type_checker> type_checker_ptr;

    environment         m_env;
    local_decls<level>  m_lls;
    io_state            m_ios;
    name_generator      m_ngen;
    type_checker_ptr    m_tc[2];
    substitution        m_subst;
    expr_map<expr>      m_cache; // (pointer equality) cache for Type and Constants (this is a trick to make sure we get the
                                 // same universe metavariable for different occurrences of the same Type/Constant
    context             m_ctx; // current local context: a list of local constants
    buffer<expr>        m_ctx_buffer; // m_ctx as a buffer
    buffer<expr>        m_ctx_domain_buffer; // m_ctx_domain_buffer[i] == abstract_locals(m_ctx_buffer[i], i, m_ctx_buffer.begin())
    pos_info_provider * m_pos_provider; // optional expression position information used when reporting errors.
    justification       m_accumulated; // accumulate justification of eagerly used substitutions
    constraint_vect     m_constraints; // constraints that must be solved for the elaborated term to be type correct.
    local_tactic_hints  m_local_tactic_hints; // mapping from metavariable name ?m to tactic expression that should be used to solve it.
                                              // this mapping is populated by the 'by tactic-expr' expression.
    mvar2meta           m_mvar2meta; // mapping from metavariable ?m to the (?m l_1 ... l_n) where [l_1 ... l_n] are the local constants
                                     // representing the context where ?m was created.
    name_set            m_displayed_errors; // set of metavariables that we already reported unsolved/unassigned
    bool                m_check_unassigned; // if true if display error messages if elaborated term still contains metavariables
    bool                m_use_local_instances; // if true class-instance resolution will use the local context
    bool                m_relax_main_opaque; // if true, then treat opaque definitions from the main module as transparent
    bool                m_flyinfo;
    typedef std::pair<pos_info, expr> flyinfo_data;
    std::vector<flyinfo_data> m_flyinfo_data;

    // Set m_ctx to ctx, and make sure m_ctx_buffer and m_ctx_domain_buffer reflect the contents of the new ctx
    void set_ctx(context const & ctx) {
        m_ctx = ctx;
        m_ctx_buffer.clear();
        m_ctx_domain_buffer.clear();
        to_buffer(ctx, m_ctx_buffer);
        std::reverse(m_ctx_buffer.begin(), m_ctx_buffer.end());
        for (unsigned i = 0; i < m_ctx_buffer.size(); i++) {
            m_ctx_domain_buffer.push_back(abstract_locals(m_ctx_buffer[i], i, m_ctx_buffer.data()));
        }
    }

    /** \brief Auxiliary object for creating backtracking points.
        \remark A scope can only be created when m_constraints and m_subst are empty,
        and m_accumulated is none.
    */
    struct scope {
        elaborator & m_main;
        context      m_old_ctx;
        scope(elaborator & e, context const & ctx, substitution const & s):m_main(e) {
            lean_assert(m_main.m_constraints.empty());
            lean_assert(m_main.m_accumulated.is_none());
            m_old_ctx    = m_main.m_ctx;
            m_main.set_ctx(ctx);
            m_main.m_tc[0]->push();
            m_main.m_tc[1]->push();
            m_main.m_subst = s;
        }
        ~scope() {
            m_main.set_ctx(m_old_ctx);
            m_main.m_tc[0]->pop();
            m_main.m_tc[1]->pop();
            m_main.m_constraints.clear();
            m_main.m_accumulated = justification();
            m_main.m_subst = substitution();
            lean_assert(m_main.m_constraints.empty());
            lean_assert(m_main.m_accumulated.is_none());
        }
    };

    /* \brief Move all constraints generated by the type checker to the buffer m_constraints. */
    void consume_tc_cnstrs() {
        for (unsigned i = 0; i < 2; i++)
            while (auto c = m_tc[i]->next_cnstr())
                m_constraints.push_back(*c);
    }

    struct choice_elaborator {
        bool m_ignore_failure;
        choice_elaborator(bool ignore_failure = false):m_ignore_failure(ignore_failure) {}
        virtual optional<constraints> next() = 0;
    };

    /** \brief 'Choice' expressions <tt>(choice e_1 ... e_n)</tt> are mapped into a metavariable \c ?m
        and a choice constraints <tt>(?m in fn)</tt> where \c fn is a choice function.
        The choice function produces a stream of alternatives. In this case, it produces a stream of
        size \c n, one alternative for each \c e_i.
        This is a helper class for implementing this choice functions.
    */
    struct choice_expr_elaborator : public choice_elaborator {
        elaborator & m_elab;
        expr         m_mvar;
        expr         m_choice;
        context      m_ctx;
        substitution m_subst;
        unsigned     m_idx;
        bool         m_relax_main_opaque;
        choice_expr_elaborator(elaborator & elab, expr const & mvar, expr const & c, context const & ctx, substitution const & s, bool relax):
            m_elab(elab), m_mvar(mvar), m_choice(c), m_ctx(ctx), m_subst(s), m_idx(0), m_relax_main_opaque(relax) {
        }

expr elaborator::mk_local(name const & n, expr const & t, binder_info const & bi) {
    return ::lean::mk_local(m_ngen.next(), n, t, bi);
}

void elaborator::register_meta(expr const & meta) {
    lean_assert(is_meta(meta));
    name const & n = mlocal_name(get_app_fn(meta));
    m_mvar2meta.insert(n, meta);
    if (m_relax_main_opaque)
        m_relaxed_mvars.insert(n);
}

/** \brief Convert the metavariable to the metavariable application that captures
    the context where it was defined.
*/
optional<expr> elaborator::mvar_to_meta(expr const & mvar) {
    lean_assert(is_metavar(mvar));
    name const & m = mlocal_name(mvar);
    if (auto it = m_mvar2meta.find(m))
        return some_expr(*it);
    else
        return none_expr();
}

/** \brief Store the pair (pos(e), type(r)) in the info_data if m_info_manager is available. */
void elaborator::save_type_data(expr const & e, expr const & r) {
    if (!m_no_info && infom() && pip() &&
        (is_constant(e) || is_local(e) || is_placeholder(e) || is_as_atomic(e) ||
         is_consume_args(e) || is_notation_info(e))) {
        if (auto p = pip()->get_pos_info(e)) {
            expr t = m_tc[m_relax_main_opaque]->infer(r).first;
            m_pre_info_data.add_type_info(p->first, p->second, t);
        }
    }
}

/** \brief Store the pair (pos(e), r) in the info_data if m_info_manager is available. */
void elaborator::save_binder_type(expr const & e, expr const & r) {
    if (!m_no_info && infom() && pip()) {
        if (auto p = pip()->get_pos_info(e)) {
            m_pre_info_data.add_type_info(p->first, p->second, r);
        }
    }
}

public:
    elaborator(environment const & env, local_decls<level> const & lls, list<expr> const & ctx, io_state const & ios, name_generator const & ngen,
               pos_info_provider * pp, bool check_unassigned):
        m_env(env), m_lls(lls), m_ios(ios),
        m_ngen(ngen),
        m_pos_provider(pp) {
        m_relax_main_opaque = false;
        m_tc[0] = mk_type_checker_with_hints(env, m_ngen.mk_child(), false);
        m_tc[1] = mk_type_checker_with_hints(env, m_ngen.mk_child(), true);
        m_check_unassigned = check_unassigned;
        m_use_local_instances = get_elaborator_local_instances(ios.get_options());
        m_flyinfo = ios.get_options().get_bool("flyinfo", false);
        set_ctx(ctx);
    }
}

/** \brief Store proof_state information at pos(e) in the info_manager */
void elaborator::save_proof_state_info(proof_state const & ps, expr const & e) {
    if (!m_no_info && infom() && pip()) {
        if (auto p = pip()->get_pos_info(e)) {
            m_pre_info_data.add_proof_state_info(p->first, p->second, ps);
        }
    }
}

/** \brief Auxiliary function for saving information about which overloaded identifier was used by the elaborator. */
void elaborator::save_identifier_info(expr const & f) {
    if (!m_no_info && infom() && pip() && is_constant(f)) {
        if (auto p = pip()->get_pos_info(f))
            m_pre_info_data.add_identifier_info(p->first, p->second, const_name(f));
    }
}

/** \brief Store actual term that was synthesized for an explicit placeholders */
void elaborator::save_synth_data(expr const & e, expr const & r) {
    if (!m_no_info && infom() && pip() && is_placeholder(e)) {
        if (auto p = pip()->get_pos_info(e))
            m_pre_info_data.add_synth_info(p->first, p->second, r);
    }
}

void elaborator::save_placeholder_info(expr const & e, expr const & r) {
    if (is_explicit_placeholder(e)) {
        save_type_data(e, r);
        save_synth_data(e, r);
    }
}

/** \brief Auxiliary function for saving information about which coercion was used by the elaborator.
    It marks that coercion c was used on e.
*/
void elaborator::save_coercion_info(expr const & e, expr const & c) {
    if (!m_no_info && infom() && pip()) {
        if (auto p = pip()->get_pos_info(e)) {
            expr t = m_tc[m_relax_main_opaque]->infer(c).first;
            m_pre_info_data.add_coercion_info(p->first, p->second, c, t);
        }
    }
}

/** \brief Remove coercion information associated with \c e */
void elaborator::erase_coercion_info(expr const & e) {
    if (!m_no_info && infom() && pip()) {
        if (auto p = pip()->get_pos_info(e))
            m_pre_info_data.erase_coercion_info(p->first, p->second);
    }
}

void elaborator::copy_info_to_manager(substitution s) {
    if (!infom())
        return;
    m_pre_info_data.instantiate(s);
    bool overwrite = true;
    infom()->merge(m_pre_info_data, overwrite);
    m_pre_info_data.clear();
}

optional<name> elaborator::mk_mvar_suffix(expr const & b) {
    if (!infom() && !m_nice_mvar_names)
        return optional<name>();
    else
        return optional<name>(binding_name(b));
}

/** \brief Create a metavariable, and attach choice constraint for generating
    solutions using class-instances and tactic-hints.
*/
expr elaborator::mk_placeholder_meta(optional<name> const & suffix, optional<expr> const & type,
                                     tag g, bool is_strict, bool is_inst_implicit, constraint_seq & cs) {
    if (is_inst_implicit) {
        auto ec = mk_placeholder_elaborator(env(), ios(), m_context,
                                            m_ngen.next(), suffix, m_relax_main_opaque, use_local_instances(),
                                            is_strict, type, g, m_unifier_config, m_ctx.m_pos_provider);
        register_meta(ec.first);
        cs += ec.second;
        return ec.first;
    } else {
        expr m = m_context.mk_meta(m_ngen, suffix, type, g);
        register_meta(m);
        return m;
    }
}

expr elaborator::visit_expecting_type(expr const & e, constraint_seq & cs) {
    if (is_placeholder(e) && !placeholder_type(e)) {
        expr r = m_context.mk_type_meta(m_ngen, e.get_tag());
        save_placeholder_info(e, r);
        return r;
    } else {
        return visit(e, cs);
    }
}

expr elaborator::visit_expecting_type_of(expr const & e, expr const & t, constraint_seq & cs) {
    if (is_placeholder(e) && !placeholder_type(e)) {
        bool inst_imp = true;
        expr r = mk_placeholder_meta(some_expr(t), e.get_tag(), is_strict_placeholder(e), inst_imp, cs);
        save_placeholder_info(e, r);
        return r;
    } else if (is_choice(e)) {
        return visit_choice(e, some_expr(t), cs);
    } else if (is_by(e)) {
        return visit_by(e, some_expr(t), cs);
    } else if (is_calc_annotation(e)) {
        return visit_calc_proof(e, some_expr(t), cs);
    } else if (is_proof_qed_annotation(e)) {
        return visit_proof_qed(e, some_expr(t), cs);
    } else {
        return visit(e, cs);
    }
}

expr elaborator::visit_choice(expr const & e, optional<expr> const & t, constraint_seq & cs) {
    lean_assert(is_choice(e));
    // Possible optimization: try to lookahead and discard some of the alternatives.
    expr m                 = m_full_context.mk_meta(m_ngen, t, e.get_tag());
    register_meta(m);
    bool relax             = m_relax_main_opaque;
    local_context ctx      = m_context;
    local_context full_ctx = m_full_context;
    auto fn = [=](expr const & meta, expr const & /* type */, substitution const & /* s */,
                  name_generator const & /* ngen */) {
        return choose(std::make_shared<choice_expr_elaborator>(*this, ctx, full_ctx, meta, e, relax));
    };
    justification j = mk_justification("none of the overloads is applicable", some_expr(e));
    cs += mk_choice_cnstr(m, fn, to_delay_factor(cnstr_group::Basic), true, j, m_relax_main_opaque);
    return m;
}

expr elaborator::visit_by(expr const & e, optional<expr> const & t, constraint_seq & cs) {
    lean_assert(is_by(e));
    expr tac = visit(get_by_arg(e), cs);
    expr m   = m_context.mk_meta(m_ngen, t, e.get_tag());
    register_meta(m);
    m_local_tactic_hints.insert(mlocal_name(get_app_fn(m)), tac);
    return m;
}

expr elaborator::visit_calc_proof(expr const & e, optional<expr> const & t, constraint_seq & cs) {
    lean_assert(is_calc_annotation(e));
    info_manager * im = nullptr;
    if (infom())
        im = &m_pre_info_data;
    pair<expr, constraint_seq> ecs = visit(get_annotation_arg(e));
    expr m                         = m_full_context.mk_meta(m_ngen, t, e.get_tag());
    register_meta(m);
    auto fn = [=](expr const & t) { save_type_data(get_annotation_arg(e), t); };
    constraint c                   = mk_calc_proof_cnstr(env(), ios().get_options(),
                                                         m_context, m, ecs.first, ecs.second, m_unifier_config,
                                                         im, m_relax_main_opaque, fn);
    cs += c;
    return m;
}

expr elaborator::visit_proof_qed(expr const & e, optional<expr> const & t, constraint_seq & cs) {
    lean_assert(is_proof_qed_annotation(e));
    info_manager * im = nullptr;
    if (infom())
        im = &m_pre_info_data;
    pair<expr, constraint_seq> ecs = visit(get_annotation_arg(e));
    expr m                         = m_full_context.mk_meta(m_ngen, t, e.get_tag());
    register_meta(m);
    constraint c                   = mk_proof_qed_cnstr(env(), m, ecs.first, ecs.second, m_unifier_config,
                                                        im, m_relax_main_opaque);
    cs += c;
    return m;
}

static bool is_implicit_pi(expr const & e) {
    if (!is_pi(e))
        return false;
    binder_info bi = binding_info(e);
    return bi.is_strict_implicit() || bi.is_implicit() || bi.is_inst_implicit();
}

/** \brief Auxiliary function for adding implicit arguments to coercions to function-class */
expr elaborator::add_implict_args(expr e, constraint_seq & cs, bool relax) {
    type_checker & tc = *m_tc[relax];
    constraint_seq new_cs;
    expr type = tc.whnf(tc.infer(e, new_cs), new_cs);
    if (!is_implicit_pi(type))
        return e;
    cs += new_cs;
    while (true) {
        lean_assert(is_pi(type));
        tag g = e.get_tag();
        bool is_strict = true;
        bool inst_imp  = binding_info(type).is_inst_implicit();
        expr imp_arg   = mk_placeholder_meta(mk_mvar_suffix(type), some_expr(binding_domain(type)),
                                             g, is_strict, inst_imp, cs);
        e              = mk_app(e, imp_arg, g);
        type           = instantiate(binding_body(type), imp_arg);
        constraint_seq new_cs;
        type           = tc.whnf(type, new_cs);
        if (!is_implicit_pi(type))
            return e;
        cs += new_cs;
    }
}

/** \brief Make sure \c f is really a function, if it is not, try to apply coercions.
    The result is a pair <tt>new_f, f_type</tt>, where new_f is the new value for \c f,
    and \c f_type is its type (and a Pi-expression)
*/
pair<expr, expr> elaborator::ensure_fun(expr f, constraint_seq & cs) {
    expr f_type = infer_type(f, cs);
    if (!is_pi(f_type))
        f_type = whnf(f_type, cs);
    if (!is_pi(f_type) && has_metavar(f_type)) {
        constraint_seq saved_cs = cs;
        expr new_f_type = whnf(f_type, cs);
        if (!is_pi(new_f_type) && m_tc[m_relax_main_opaque]->is_stuck(new_f_type)) {
            cs = saved_cs;
            // let type checker add constraint
            f_type = m_tc[m_relax_main_opaque]->ensure_pi(f_type, f, cs);
        } else {
            f_type = new_f_type;
        }
    }
    if (!is_pi(f_type)) {
        // try coercion to function-class
        list<expr> coes  = get_coercions_to_fun(env(), f_type);
        if (is_nil(coes)) {
            throw_kernel_exception(env(), f, [=](formatter const & fmt) { return pp_function_expected(fmt, f); });
        } else if (is_nil(tail(coes))) {
            expr old_f = f;
            bool relax = m_relax_main_opaque;
            f = mk_app(head(coes), f, f.get_tag());
            f = add_implict_args(f, cs, relax);
            f_type = infer_type(f, cs);
            save_coercion_info(old_f, f);
            lean_assert(is_pi(f_type));
        } else {
            bool relax             = m_relax_main_opaque;
            local_context ctx      = m_context;
            local_context full_ctx = m_full_context;
            justification j        = mk_justification(f, [=](formatter const & fmt, substitution const & subst) {
                    return pp_function_expected(fmt, substitution(subst).instantiate(f));
                });
            auto choice_fn = [=](expr const & meta, expr const &, substitution const &, name_generator const &) {
                flet<local_context> save1(m_context,      ctx);
                flet<local_context> save2(m_full_context, full_ctx);
                list<constraints> choices = map2<constraints>(coes, [&](expr const & coe) {
                        expr new_f      = copy_tag(f, ::lean::mk_app(coe, f));
                        constraint_seq cs;
                        new_f = add_implict_args(new_f, cs, relax);
                        cs += mk_eq_cnstr(meta, new_f, j, relax);
                        return cs.to_list();
                    });
                return choose(std::make_shared<coercion_elaborator>(*this, f, choices, coes, false));
            };
            f   = m_full_context.mk_meta(m_ngen, none_expr(), f.get_tag());
            register_meta(f);
            cs += mk_choice_cnstr(f, choice_fn, to_delay_factor(cnstr_group::Basic), true, j, relax);
            lean_assert(is_meta(f));
            // let type checker add constraint
            f_type = infer_type(f, cs);
            f_type = m_tc[m_relax_main_opaque]->ensure_pi(f_type, f, cs);
            lean_assert(is_pi(f_type));
        }
    } else {
        erase_coercion_info(f);
    }
    lean_assert(is_pi(f_type));
    return mk_pair(f, f_type);
}

bool elaborator::has_coercions_from(expr const & a_type) {
    try {
        expr const & a_cls = get_app_fn(whnf(a_type).first);
        return is_constant(a_cls) && ::lean::has_coercions_from(env(), const_name(a_cls));
    } catch (exception&) {
        return false;
    }
}

bool elaborator::has_coercions_to(expr d_type) {
    try {
        d_type = whnf(d_type).first;
        expr const & fn = get_app_fn(d_type);
        if (is_constant(fn))
            return ::lean::has_coercions_to(env(), const_name(fn));
        else if (is_pi(d_type))
            return ::lean::has_coercions_to_fun(env());
        else if (is_sort(d_type))
            return ::lean::has_coercions_to_sort(env());
        else
            return false;
    } catch (exception&) {
        return false;
    }
}

expr elaborator::apply_coercion(expr const & a, expr a_type, expr d_type) {
    a_type = whnf(a_type).first;
    d_type = whnf(d_type).first;
    constraint_seq aux_cs;
    list<expr> coes = get_coercions_from_to(*m_tc[m_relax_main_opaque], a_type, d_type, aux_cs);
    if (is_nil(coes)) {
        erase_coercion_info(a);
        return a;
    } else if (is_nil(tail(coes))) {
        expr r = mk_app(head(coes), a, a.get_tag());
        save_coercion_info(a, r);
        return r;
    } else {
        for (expr const & coe : coes) {
            expr r = mk_app(coe, a, a.get_tag());
            expr r_type = infer_type(r).first;
            try {
                if (m_tc[m_relax_main_opaque]->is_def_eq(r_type, d_type).first) {
                    save_coercion_info(a, r);
                    return r;
                }
            } catch (exception&) {
            }
        }
        erase_coercion_info(a);
        return a;
    }
}

/** \brief Given a term <tt>a : a_type</tt>, and an expected type generate a metavariable with a delayed coercion. */
pair<expr, constraint_seq> elaborator::mk_delayed_coercion(
    expr const & a, expr const & a_type, expr const & expected_type,
    justification const & j) {
    bool relax = m_relax_main_opaque;
    type_checker & tc = *m_tc[relax];
    expr m       = m_full_context.mk_meta(m_ngen, some_expr(expected_type), a.get_tag());
    register_meta(m);
    constraint c = mk_coercion_cnstr(tc, *this, m, a, a_type, j, to_delay_factor(cnstr_group::Basic), relax);
    return to_ecs(m, c);
}

/** \brief Given a term <tt>a : a_type</tt>, ensure it has type \c expected_type. Apply coercions if needed

    \remark relax == true affects how opaque definitions in the main module are treated.
*/
pair<expr, constraint_seq> elaborator::ensure_has_type(
    expr const & a, expr const & a_type, expr const & expected_type,
    justification const & j, bool relax) {
    if (is_meta(expected_type) && has_coercions_from(a_type)) {
        return mk_delayed_coercion(a, a_type, expected_type, j);
    } else if (is_meta(a_type) && has_coercions_to(expected_type)) {
        return mk_delayed_coercion(a, a_type, expected_type, j);
    } else {
        pair<bool, constraint_seq> dcs;
        try {
            dcs = m_tc[relax]->is_def_eq(a_type, expected_type, j);
        } catch (exception&) {
            dcs.first = false;
        }
        if (dcs.first) {
            return to_ecs(a, dcs.second);
        } else {
            expr new_a = apply_coercion(a, a_type, expected_type);
            constraint_seq cs;
            bool coercion_worked = false;
            if (!is_eqp(a, new_a)) {
                expr new_a_type = infer_type(new_a, cs);
                try {
                    coercion_worked = m_tc[relax]->is_def_eq(new_a_type, expected_type, j, cs);
                } catch (exception&) {
                    coercion_worked = false;
                }
            }
            if (coercion_worked) {
                return to_ecs(new_a, cs);
            } else if (has_metavar(a_type) || has_metavar(expected_type)) {
                // rely on unification hints to solve this constraint
                return to_ecs(a, mk_eq_cnstr(a_type, expected_type, j, relax));
            } else {
                throw unifier_exception(j, substitution());
            }
        }
    }
}

bool elaborator::is_choice_app(expr const & e) {
    expr const & f = get_app_fn(e);
    return is_choice(f) || (is_annotation(f) && is_choice(get_nested_annotation_arg(f)));
}

/** \brief Process ((choice f_1 ... f_n) a_1 ... a_k) as
    (choice (f_1 a_1 ... a_k) ... (f_n a_1 ... a_k))
*/
expr elaborator::visit_choice_app(expr const & e, constraint_seq & cs) {
    buffer<expr> args;
    expr r = get_app_rev_args(e, args);
    expr f = get_nested_annotation_arg(r);
    lean_assert(is_choice(f));
    buffer<expr> new_choices;
    unsigned num = get_num_choices(f);
    for (unsigned i = 0; i < num; i++) {
        expr f_i = get_choice(f, i);
        f_i      = copy_annotations(r, f_i);
        new_choices.push_back(mk_rev_app(f_i, args));
    }
    return visit_choice(copy_tag(e, mk_choice(new_choices.size(), new_choices.data())), none_expr(), cs);
}

    expr visit_app(expr const & e) {
        if (is_choice_app(e))
            return visit_choice_app(e);
        bool expl   = is_explicit(get_app_fn(e));
        expr f      = visit(app_fn(e));
        auto f_t    = ensure_fun(f);
        f           = f_t.first;
        expr f_type = f_t.second;
        lean_assert(is_pi(f_type));
        if (!expl) {
            bool first = true;
            while (binding_info(f_type).is_strict_implicit() || (!first && binding_info(f_type).is_implicit())) {
                tag g        = f.get_tag();
                expr imp_arg = mk_placeholder_meta(some_expr(binding_domain(f_type)), g);
                f            = mk_app(f, imp_arg, g);
                auto f_t     = ensure_fun(f);
                f            = f_t.first;
                f_type       = f_t.second;
                first        = false;
            }
        }
        if (!first) {
            // we save the info data again for application of functions with strict implicit arguments
            save_type_data(get_app_fn(e), f);
        }
    }
    constraint_seq a_cs;
    expr d_type = binding_domain(f_type);
    if (d_type == get_tactic_expr_type()) {
        expr r = mk_app(f, mk_tactic_expr(app_arg(e)), e.get_tag());
        cs += f_cs + a_cs;
        return r;
    } else {
        expr a          = visit_expecting_type_of(app_arg(e), d_type, a_cs);
        expr a_type     = infer_type(a, a_cs);
        expr r          = mk_app(f, a, e.get_tag());
        justification j = mk_app_justification(r, a, d_type, a_type);
        auto new_a_cs   = ensure_has_type(a, a_type, d_type, j, m_relax_main_opaque);
        expr new_a      = new_a_cs.first;
        cs += f_cs + new_a_cs.second + a_cs;
        return update_app(r, app_fn(r), new_a);
    }
}

expr elaborator::visit_placeholder(expr const & e, constraint_seq & cs) {
    bool inst_implicit = true;
    expr r = mk_placeholder_meta(placeholder_type(e), e.get_tag(), is_strict_placeholder(e), inst_implicit, cs);
    save_placeholder_info(e, r);
    return r;
}

level elaborator::replace_univ_placeholder(level const & l) {
    auto fn = [&](level const & l) {
        if (is_placeholder(l))
            return some_level(mk_meta_univ(m_ngen.next()));
        else
            return none_level();
    };
    return replace(l, fn);
}

static bool contains_placeholder(level const & l) {
    bool contains = false;
    auto fn = [&](level const & l) {
        if (contains) return false;
        if (is_placeholder(l))
            contains = true;
        return true;
    };
    for_each(l, fn);
    return contains;
}

expr elaborator::visit_sort(expr const & e) {
    expr r = update_sort(e, replace_univ_placeholder(sort_level(e)));
    if (contains_placeholder(sort_level(e)))
        m_to_check_sorts.emplace_back(e, r);
    return r;
}

    /** \brief Store the pair (pos(e), type(r)) in the flyinfo_data if m_flyinfo is true. */
    void save_flyinfo_data(expr const & e, expr const & r) {
        if (m_flyinfo && m_pos_provider) {
            auto p = m_pos_provider->get_pos_info(e);
            type_checker::scope scope(*m_tc[m_relax_main_opaque]);
            expr t = m_tc[m_relax_main_opaque]->infer(r);
            m_flyinfo_data.push_back(mk_pair(p, t));
        }
    }

    expr visit_constant(expr const & e) {
        auto it = m_cache.find(e);
        if (it != m_cache.end()) {
            return it->second;
        } else {
            declaration d = m_env.get(const_name(e));
            buffer<level> ls;
            for (level const & l : const_levels(e))
                ls.push_back(replace_univ_placeholder(l));
            unsigned num_univ_params = length(d.get_univ_params());
            if (num_univ_params < ls.size())
                throw_kernel_exception(m_env, sstream() << "incorrect number of universe levels parameters for '" << const_name(e) << "', #"
                                       << num_univ_params << " expected, #" << ls.size() << " provided");
            // "fill" with meta universe parameters
            for (unsigned i = ls.size(); i < num_univ_params; i++)
                ls.push_back(mk_meta_univ(m_ngen.next()));
            lean_assert(num_univ_params == ls.size());
            expr r = update_constant(e, to_list(ls.begin(), ls.end()));
            m_cache.insert(mk_pair(e, r));
            return r;
        }
    }
}

expr elaborator::visit_constant(expr const & e) {
    declaration d = env().get(const_name(e));
    buffer<level> ls;
    for (level const & l : const_levels(e))
        ls.push_back(replace_univ_placeholder(l));
    unsigned num_univ_params = length(d.get_univ_params());
    if (num_univ_params < ls.size())
        throw_kernel_exception(env(), sstream() << "incorrect number of universe levels parameters for '"
                               << const_name(e) << "', #" << num_univ_params
                               << " expected, #" << ls.size() << " provided");
    // "fill" with meta universe parameters
    for (unsigned i = ls.size(); i < num_univ_params; i++)
        ls.push_back(mk_meta_univ(m_ngen.next()));
    lean_assert(num_univ_params == ls.size());
    return update_constant(e, to_list(ls.begin(), ls.end()));
}

/** \brief Make sure \c e is a type. If it is not, then try to apply coercions. */
expr elaborator::ensure_type(expr const & e, constraint_seq & cs) {
    expr t = infer_type(e, cs);
    erase_coercion_info(e);
    if (is_sort(t))
        return e;
    t = whnf(t, cs);
    if (is_sort(t))
        return e;
    if (has_metavar(t)) {
        t = whnf(t, cs);
        if (is_sort(t))
            return e;
        if (is_meta(t)) {
            // let type checker add constraint
            m_tc[m_relax_main_opaque]->ensure_sort(t, e, cs);
            return e;
        }
    }
    list<expr> coes = get_coercions_to_sort(env(), t);
    if (is_nil(coes)) {
        throw_kernel_exception(env(), e, [=](formatter const & fmt) { return pp_type_expected(fmt, e); });
    } else {
        // Remark: we ignore other coercions to sort
        expr r = mk_app(head(coes), e, e.get_tag());
        save_coercion_info(e, r);
        return r;
    }
}

/** \brief Similar to instantiate_rev, but assumes that subst contains only local constants.
    When replacing a variable with a local, we copy the local constant and inherit the tag
    associated with the variable. This is a trick for getter better error messages */
expr elaborator::instantiate_rev_locals(expr const & a, unsigned n, expr const * subst) {
    if (closed(a))
        return a;
    auto fn = [=](expr const & m, unsigned offset) -> optional<expr> {
        if (offset >= get_free_var_range(m))
            return some_expr(m); // expression m does not contain free variables with idx >= offset
        if (is_var(m)) {
            unsigned vidx = var_idx(m);
            if (vidx >= offset) {
                unsigned h = offset + n;
                if (h < offset /* overflow, h is bigger than any vidx */ || vidx < h) {
                    expr local = subst[n - (vidx - offset) - 1];
                    lean_assert(is_local(local));
                    return some_expr(copy_tag(m, copy(local)));
                } else {
                    return some_expr(copy_tag(m, mk_var(vidx - n)));
                }
            }
        }
        return none_expr();
    };
    return replace(a, fn);
}

expr elaborator::visit_binding(expr e, expr_kind k, constraint_seq & cs) {
    flet<local_context> save1(m_context, m_context);
    flet<local_context> save2(m_full_context, m_full_context);
    buffer<expr> ds, ls, es;
    while (e.kind() == k) {
        es.push_back(e);
        expr const & d0 = binding_domain(e);
        expr d          = d0;
        d = instantiate_rev_locals(d, ls.size(), ls.data());
        d = ensure_type(visit_expecting_type(d, cs), cs);

        if (is_placeholder(d0) && !is_explicit_placeholder(d0))
            save_binder_type(d0, d);

        ds.push_back(d);
        expr l   = mk_local(binding_name(e), d, binding_info(e));
        if (binding_info(e).is_contextual())
            m_context.add_local(l);
        m_full_context.add_local(l);
        ls.push_back(l);
        e = binding_body(e);
    }
    lean_assert(ls.size() == es.size() && ls.size() == ds.size());
    e = instantiate_rev_locals(e, ls.size(), ls.data());
    e = (k == expr_kind::Pi) ? ensure_type(visit_expecting_type(e, cs), cs) : visit(e, cs);
    e = abstract_locals(e, ls.size(), ls.data());
    unsigned i = ls.size();
    while (i > 0) {
        --i;
        e = update_binding(es[i], abstract_locals(ds[i], i, ls.data()), e);
    }
    return e;
}
expr elaborator::visit_pi(expr const & e, constraint_seq & cs) {
    return visit_binding(e, expr_kind::Pi, cs);
}
expr elaborator::visit_lambda(expr const & e, constraint_seq & cs) {
    return visit_binding(e, expr_kind::Lambda, cs);
}

expr elaborator::visit_typed_expr(expr const & e, constraint_seq & cs) {
    constraint_seq t_cs;
    expr t      = visit(get_typed_expr_type(e), t_cs);
    constraint_seq v_cs;
    expr v      = visit(get_typed_expr_expr(e), v_cs);
    expr v_type = infer_type(v, v_cs);
    justification j = mk_type_mismatch_jst(v, v_type, t, e);
    auto new_vcs    = ensure_has_type(v, v_type, t, j, m_relax_main_opaque);
    v = new_vcs.first;
    cs += t_cs + new_vcs.second + v_cs;
    return v;
}

expr elaborator::visit_let_value(expr const & e, constraint_seq & cs) {
    if (auto p = m_cache.find(e)) {
        cs += p->second;
        return p->first;
    } else {
        auto ecs = visit(get_let_value_expr(e));
        expr r = copy_tag(ecs.first, mk_let_value(ecs.first));
        m_cache.insert(e, mk_pair(r, ecs.second));
        cs += ecs.second;
        return r;
    }
}

    /** \brief Similar to instantiate_rev, but assumes that subst contains only local constants.
        When replacing a variable with a local, we copy the local constant and inherit the tag
        associated with the variable. This is a trick for getter better error messages */
    expr instantiate_rev_locals(expr const & a, unsigned n, expr const * subst) {
        if (closed(a))
            return a;
        return replace(a, [=](expr const & m, unsigned offset) -> optional<expr> {
                if (offset >= get_free_var_range(m))
                    return some_expr(m); // expression m does not contain free variables with idx >= offset
                if (is_var(m)) {
                    unsigned vidx = var_idx(m);
                    if (vidx >= offset) {
                        unsigned h = offset + n;
                        if (h < offset /* overflow, h is bigger than any vidx */ || vidx < h) {
                            expr local = subst[n - (vidx - offset) - 1];
                            lean_assert(is_local(local));
                            return some_expr(copy_tag(m, copy(local)));
                        } else {
                            return some_expr(copy_tag(m, mk_var(vidx - n)));
                        }
                    }
                }
                return none_expr();
            });
    }

    expr visit_binding(expr e, expr_kind k) {
        scope_ctx scope(*this);
        buffer<expr> ds, ls, es;
        while (e.kind() == k) {
            es.push_back(e);
            expr d   = binding_domain(e);
            d = instantiate_rev_locals(d, ls.size(), ls.data());
            d = ensure_type(visit_expecting_type(d));
            ds.push_back(d);
            expr l   = mk_local(binding_name(e), d, binding_info(e));
            if (binding_info(e).is_contextual())
                add_local(l);
            ls.push_back(l);
            e = binding_body(e);
        }
        lean_assert(ls.size() == es.size() && ls.size() == ds.size());
        e = instantiate_rev_locals(e, ls.size(), ls.data());
        e = (k == expr_kind::Pi) ? ensure_type(visit_expecting_type(e)) : visit(e);
        e = abstract_locals(e, ls.size(), ls.data());
        unsigned i = ls.size();
        while (i > 0) {
            --i;
            e = update_binding(es[i], abstract_locals(ds[i], i, ls.data()), e);
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    }
}

pair<expr, constraint_seq> elaborator::visit(expr const & e) {
    if (is_extra_info(e)) {
        auto ecs = visit(get_annotation_arg(e));
        save_extra_type_data(e, ecs.first);
        return ecs;
    }
    if (is_notation_info(e)) {
        pair<expr, constraint_seq> ecs;
        {
            flet<bool> let(m_no_info, true);
            ecs = visit(get_annotation_arg(e));
        }
        save_type_data(e, ecs.first);
        return ecs;
    }
    expr r;
    expr b = e;
    constraint_seq cs;
    if (is_explicit(e)) {
        b    = get_explicit_arg(e);
        if (is_sorry(b)) {
            r = visit_constant(b);
        } else {
            r = visit_core(b, cs);
        }
    } else if (is_explicit(get_app_fn(e))) {
        r    = visit_core(e, cs);
    } else {
        bool consume_args = false;
        if (is_as_atomic(e)) {
            flet<bool> let(m_no_info, true);
            r = get_as_atomic_arg(e);
            if (is_explicit(r)) r = get_explicit_arg(r);
            r = visit_core(r, cs);
        } else if (is_consume_args(e)) {
            consume_args = true;
            r = visit_core(get_consume_args_arg(e), cs);
        } else {
            r = visit_core(e, cs);
        }
        tag  g         = e.get_tag();
        expr r_type    = whnf(infer_type(r, cs), cs);
        expr imp_arg;
        bool is_strict = true;
        while (is_pi(r_type)) {
            binder_info bi = binding_info(r_type);
            if (!bi.is_implicit() && !bi.is_inst_implicit()) {
                if (!consume_args)
                    break;
                if (!has_free_var(binding_body(r_type), 0)) {
                    // if the rest of the type does not reference argument,
                    // then we also stop consuming arguments
                    break;
                }
            }
            bool inst_imp = bi.is_inst_implicit();
            imp_arg = mk_placeholder_meta(mk_mvar_suffix(r_type), some_expr(binding_domain(r_type)),
                                          g, is_strict, inst_imp, cs);
            r       = mk_app(r, imp_arg, g);
            r_type  = whnf(instantiate(binding_body(r_type), imp_arg), cs);
        }
        if (is_constant(e) || is_local(e))
            save_flyinfo_data(e, r);
        return r;
    }
    save_type_data(b, r);
    return mk_pair(r, cs);
}

expr elaborator::visit(expr const & e, constraint_seq & cs) {
    auto r = visit(e);
    cs += r.second;
    return r.first;
}

unify_result_seq elaborator::solve(constraint_seq const & cs) {
    buffer<constraint> tmp;
    cs.linearize(tmp);
    return unify(env(), tmp.size(), tmp.data(), m_ngen.mk_child(), substitution(), m_unifier_config);
}

void elaborator::display_unsolved_proof_state(expr const & mvar, proof_state const & ps, char const * msg, expr const & pos) {
    lean_assert(is_metavar(mvar));
    if (!m_displayed_errors.contains(mlocal_name(mvar))) {
        m_displayed_errors.insert(mlocal_name(mvar));
        auto out = regular(env(), ios());
        flycheck_error err(out);
        display_error_pos(out, pip(), pos);
        out << " " << msg << "\n" << ps << endl;
    }
}

    void display_unsolved_proof_state(expr const & mvar, proof_state const & ps, char const * msg) {
        lean_assert(is_metavar(mvar));
        if (!m_displayed_errors.contains(mlocal_name(mvar))) {
            m_displayed_errors.insert(mlocal_name(mvar));
            auto out = regular(m_env, m_ios);
            flycheck_error err(out);
            display_error_pos(out, m_pos_provider, mvar);
            out << " unsolved placeholder, " << msg << "\n" << ps << endl;
        }
    }
}

optional<tactic> elaborator::pre_tactic_to_tactic(expr const & pre_tac) {
    try {
        bool relax = m_relax_main_opaque;
        auto fn = [=](goal const & g, name_generator const & ngen, expr const & e) {
            elaborator aux_elaborator(m_ctx, ngen);
            // Disable tactic hints when processing expressions nested in tactics.
            // We must do it otherwise, it is easy to make the system loop.
            bool use_tactic_hints = false;
            return aux_elaborator.elaborate_nested(g.to_context(), e, relax, use_tactic_hints);
        };
        return optional<tactic>(expr_to_tactic(env(), fn, pre_tac, pip()));
    } catch (expr_to_tactic_exception & ex) {
        auto out = regular(env(), ios());
        flycheck_error err(out);
        display_error_pos(out, pip(), ex.get_expr());
        out << " " << ex.what();
        out << pp_indent_expr(out.get_formatter(), pre_tac) << endl << "failed at:"
            << pp_indent_expr(out.get_formatter(), ex.get_expr()) << endl;
        return optional<tactic>();
    }
}

/** \brief Try to instantiate meta-variable \c mvar (modulo its state ps) using the given tactic.
    If it succeeds, then update subst with the solution.
    Return true iff the metavariable \c mvar has been assigned.

    If \c show_failure == true, then display reason for failure.
*/
bool elaborator::try_using(substitution & subst, expr const & mvar, proof_state const & ps, tactic const & tac,
                           bool show_failure) {
    lean_assert(length(ps.get_goals()) == 1);
    // make sure ps is a really a proof state for mvar.
    lean_assert(mlocal_name(get_app_fn(head(ps.get_goals()).get_meta())) == mlocal_name(mvar));
    try {
        proof_state_seq seq = tac(env(), ios(), ps);
        auto r = seq.pull();
        if (!r) {
            // tactic failed to produce any result
            if (show_failure)
                display_unsolved_proof_state(mvar, ps, "tactic failed");
            return false;
        } else if (!empty(r->first.get_goals())) {
            // tactic contains unsolved subgoals
            if (show_failure)
                display_unsolved_proof_state(mvar, r->first, "unsolved subgoals");
            return false;
        } else {
            subst = r->first.get_subst();
            expr v = subst.instantiate(mvar);
            subst.assign(mlocal_name(mvar), v);
            return true;
        }
    } catch (tactic_exception & ex) {
        if (show_failure) {
            auto out = regular(env(), ios());
            display_error_pos(out, pip(), ex.get_expr());
            out << " tactic failed: " << ex.what() << "\n";
        }
        return false;
    }
}

static void extract_begin_end_tactics(expr pre_tac, buffer<expr> & pre_tac_seq) {
    if (is_begin_end_element_annotation(pre_tac)) {
        pre_tac_seq.push_back(get_annotation_arg(pre_tac));
    } else {
        buffer<expr> args;
        if (get_app_args(pre_tac, args) == get_and_then_tac_fn()) {
            for (expr const & arg : args) {
                extract_begin_end_tactics(arg, pre_tac_seq);
            }
        } else {
            throw exception("internal error, invalid begin-end tactic");
        }
    }
}

void elaborator::try_using_begin_end(substitution & subst, expr const & mvar, proof_state ps, expr const & pre_tac) {
    lean_assert(is_begin_end_annotation(pre_tac));
    buffer<expr> pre_tac_seq;
    extract_begin_end_tactics(get_annotation_arg(pre_tac), pre_tac_seq);
    for (expr const & ptac : pre_tac_seq) {
        if (auto tac = pre_tactic_to_tactic(ptac)) {
            try {
                proof_state_seq seq = (*tac)(env(), ios(), ps);
                auto r = seq.pull();
                if (!r) {
                    // tactic failed to produce any result
                    display_unsolved_proof_state(mvar, ps, "tactic failed", ptac);
                    return;
                }
                ps = r->first;
            } catch (tactic_exception & ex) {
                auto out = regular(env(), ios());
                display_error_pos(out, pip(), ex.get_expr());
                out << " tactic failed: " << ex.what() << "\n";
                return;
            }
        } else {
            return;
        }
    }

    if (!empty(ps.get_goals())) {
        display_unsolved_proof_state(mvar, ps, "unsolved subgoals", pre_tac);
    } else {
        subst = ps.get_subst();
        expr v = subst.instantiate(mvar);
        subst.assign(mlocal_name(mvar), v);
    }
}

void elaborator::solve_unassigned_mvar(substitution & subst, expr mvar, name_set & visited) {
    if (visited.contains(mlocal_name(mvar)))
        return;
    visited.insert(mlocal_name(mvar));
    auto meta = mvar_to_meta(mvar);
    if (!meta)
        return;
    meta = instantiate_meta(*meta, subst);
    // TODO(Leo): we are discarding constraints here
    expr type = m_tc[m_relax_main_opaque]->infer(*meta).first;
    // first solve unassigned metavariables in type
    type = solve_unassigned_mvars(subst, type, visited);
    bool relax_main_opaque = m_relaxed_mvars.contains(mlocal_name(mvar));
    proof_state ps = to_proof_state(*meta, type, subst, m_ngen.mk_child(), relax_main_opaque);
    if (auto pre_tac = get_pre_tactic_for(mvar)) {
        if (is_begin_end_annotation(*pre_tac)) {
            try_using_begin_end(subst, mvar, ps, *pre_tac);
            return;
        }

        if (auto tac = pre_tactic_to_tactic(*pre_tac)) {
            bool show_failure = true;
            try_using(subst, mvar, ps, *tac, show_failure);
            return;
        }
    }

    if (m_use_tactic_hints) {
        // using tactic_hints
        for (expr const & pre_tac : get_tactic_hints(env())) {
            if (auto tac = pre_tactic_to_tactic(pre_tac)) {
                bool show_failure = false;
                if (try_using(subst, mvar, ps, *tac, show_failure))
                    return;
            }
        }
    }
}

expr elaborator::solve_unassigned_mvars(substitution & subst, expr e, name_set & visited) {
    e = subst.instantiate(e);
    metavar_closure mvars(e);
    mvars.for_each_expr_mvar([&](expr const & mvar) {
            check_interrupted();
            solve_unassigned_mvar(subst, mvar, visited);
        });
    return subst.instantiate(e);
}

expr elaborator::solve_unassigned_mvars(substitution & subst, expr const & e) {
    name_set visited;
    return solve_unassigned_mvars(subst, e, visited);
}

void elaborator::display_unassigned_mvars(expr const & e, substitution const & s) {
    if (check_unassigned() && has_metavar(e)) {
        substitution tmp_s(s);
        for_each(e, [&](expr const & e, unsigned) {
                if (!is_metavar(e))
                    return has_metavar(e);
                if (auto it = mvar_to_meta(e)) {
                    expr meta      = tmp_s.instantiate(*it);
                    expr meta_type = tmp_s.instantiate(type_checker(env()).infer(meta).first);
                    goal g(meta, meta_type);
                    bool relax     = true;
                    proof_state ps(goals(g), s, m_ngen, constraints(), relax);
                    display_unsolved_proof_state(e, ps, "don't know how to synthesize placeholder");
                }
                return false;
            });
    }
}

/** \brief Check whether the solution found by the elaborator is producing too specific
    universes.

    \remark For now, we only check if a term Type.{?u} was solved by assigning ?u to 0.
    In this case, the user should write Prop instead of Type.
*/
void elaborator::check_sort_assignments(substitution const & s) {
    for (auto const & p : m_to_check_sorts) {
        expr pre  = p.first;
        expr post = p.second;
        lean_assert(is_sort(post));
        for_each(sort_level(post), [&](level const & u) {
                if (is_meta(u) && s.is_assigned(u)) {
                    level r = *s.get_level(u);
                    if (is_explicit(r)) {
                        substitution saved_s(s);
                        throw_kernel_exception(env(), pre, [=](formatter const & fmt) {
                                options o = fmt.get_options();
                                o  = o.update(get_pp_universes_option_name(), true);
                                format r("solution computed by the elaborator forces a universe placeholder"
                                         " to be a fixed value, computed sort is");
                                r += pp_indent_expr(fmt.update_options(o), substitution(saved_s).instantiate(post));
                                return r;
                            });
                    }
                }
                return true;
            });
    }
}

/** \brief Apply substitution and solve remaining metavariables using tactics. */
expr elaborator::apply(substitution & s, expr const & e, name_set & univ_params, buffer<name> & new_params) {
    expr r = s.instantiate(e);
    if (has_univ_metavar(r))
        r = univ_metavars_to_params(env(), lls(), s, univ_params, new_params, r);
    r = solve_unassigned_mvars(s, r);
    display_unassigned_mvars(r, s);
    return r;
}

std::tuple<expr, level_param_names> elaborator::apply(substitution & s, expr const & e) {
    auto ps = collect_univ_params(e);
    buffer<name> new_ps;
    expr r = apply(s, e, ps, new_ps);
    return std::make_tuple(r, to_list(new_ps.begin(), new_ps.end()));
}

auto elaborator::operator()(list<expr> const & ctx, expr const & e, bool _ensure_type, bool relax_main_opaque)
-> std::tuple<expr, level_param_names> {
    m_context.set_ctx(ctx);
    m_full_context.set_ctx(ctx);
    flet<bool> set_relax(m_relax_main_opaque, relax_main_opaque);
    constraint_seq cs;
    expr r = visit(e, cs);
    if (_ensure_type)
        r = ensure_type(r, cs);
    auto p  = solve(cs).pull();
    lean_assert(p);
    substitution s = p->first.first;
    auto result = apply(s, r);
    check_sort_assignments(s);
    copy_info_to_manager(s);
    return result;
}

    void display_flyinfo(substitution const & _s) {
        substitution s = _s;
        for (auto p : m_flyinfo_data) {
            auto out = regular(m_env, m_ios);
            flyinfo_scope info(out);
            out << m_pos_provider->get_file_name() << ":" << p.first.first << ":" << p.first.second << ": type\n";
            out << s.instantiate(p.second) << endl;
        }
    }

    std::tuple<expr, level_param_names> operator()(expr const & e, bool _ensure_type, bool relax_main_opaque) {
        flet<bool> set_relax(m_relax_main_opaque, relax_main_opaque && !get_hide_main_opaque(m_env));
        expr r  = visit(e);
        if (_ensure_type)
            r = ensure_type(r);
        auto p  = solve().pull();
        lean_assert(p);
        substitution s = p->first;
        auto result = apply(s, r);
        display_flyinfo(s);
        return result;
    }
    throw_elaborator_exception(env, sstream() << "unknown identifier '" << local_name << "'", src);
}

    std::tuple<expr, expr, level_param_names> operator()(expr const & t, expr const & v, name const & n, bool is_opaque) {
        lean_assert(!has_local(t)); lean_assert(!has_local(v));
        expr r_t      = ensure_type(visit(t));
        // Opaque definitions in the main module may treat other opaque definitions (in the main module) as transparent.
        flet<bool> set_relax(m_relax_main_opaque, is_opaque && !get_hide_main_opaque(m_env));
        expr r_v      = visit(v);
        expr r_v_type = infer_type(r_v);
        justification j = mk_justification(r_v, [=](formatter const & fmt, substitution const & subst) {
                substitution s(subst);
                return pp_def_type_mismatch(fmt, n, s.instantiate(r_t), s.instantiate(r_v_type));
            });
        r_v = ensure_type(r_v, r_v_type, r_t, j, is_opaque);
        auto p  = solve().pull();
        lean_assert(p);
        substitution s = p->first;
        name_set univ_params = collect_univ_params(r_v, collect_univ_params(r_t));
        buffer<name> new_params;
        expr new_r_t = apply(s, r_t, univ_params, new_params);
        expr new_r_v = apply(s, r_v, univ_params, new_params);
        display_flyinfo(s);
        return std::make_tuple(new_r_t, new_r_v, to_list(new_params.begin(), new_params.end()));
    }
    expr e = translate(env(), ctx, n);
    m_context.set_ctx(ctx);
    m_full_context.set_ctx(ctx);
    flet<bool> set_relax(m_relax_main_opaque, relax);
    flet<bool> set_discard(m_unifier_config.m_discard, false);
    flet<bool> set_use_hints(m_use_tactic_hints, use_tactic_hints);
    constraint_seq cs;
    expr r  = visit(e, cs);
    auto p  = solve(cs).pull();
    lean_assert(p);
    substitution s  = p->first.first;
    constraints rcs = p->first.second;
    r = s.instantiate(r);
    r = solve_unassigned_mvars(s, r);
    copy_info_to_manager(s);
    return mk_pair(r, rcs);
}

static name * g_tmp_prefix = nullptr;

std::tuple<expr, level_param_names> elaborate(elaborator_context & env, list<expr> const & ctx, expr const & e,
                                              bool relax_main_opaque, bool ensure_type, bool nice_mvar_names) {
    return elaborator(env, name_generator(*g_tmp_prefix), nice_mvar_names)(ctx, e, ensure_type, relax_main_opaque);
}

std::tuple<expr, expr, level_param_names> elaborate(elaborator_context & env, name const & n, expr const & t, expr const & v,
                                                    bool is_opaque) {
    return elaborator(env, name_generator(*g_tmp_prefix))(t, v, n, is_opaque);
}

void initialize_elaborator() {
    g_tmp_prefix = new name(name::mk_internal_unique_name());
}

void finalize_elaborator() {
    delete g_tmp_prefix;
}
}
