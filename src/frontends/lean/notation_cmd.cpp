/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <limits>
#include <string>
#include "util/sstream.h"
#include "util/utf8.h"
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"
#include "library/scoped_ext.h"
#include "library/explicit.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"

namespace lean {
static std::string parse_symbol(parser & p, char const * msg) {
    name n;
    if (p.curr_is_identifier() || p.curr_is_quoted_symbol()) {
        n = p.get_name_val();
    } else if (p.curr_is_keyword()) {
        n = p.get_token_info().value();
    } else {
        throw parser_error(msg, p.pos());
    }
    p.next();
    return n.to_string();
}

static optional<unsigned> parse_optional_precedence(parser & p) {
    if (p.curr_is_numeral()) {
        return optional<unsigned>(p.parse_small_nat());
    } else if (p.curr_is_token_or_id(get_max_tk())) {
        p.next();
        return optional<unsigned>(get_max_prec());
    } else {
        return optional<unsigned>();
    }
}

static unsigned parse_precedence(parser & p, char const * msg) {
    auto r = parse_optional_precedence(p);
    if (!r)
        throw parser_error(msg, p.pos());
    return *r;
}

LEAN_THREAD_VALUE(bool, g_allow_local, false);

static void check_notation_expr(expr const & e, pos_info const & pos) {
    if (!g_allow_local && (has_local(e) || has_param_univ(e)))
        throw parser_error("invalid notation declaration, contains reference to local variables", pos);
}

enum class mixfix_kind { infixl, infixr, postfix, prefix };

using notation::mk_expr_action;
using notation::mk_binder_action;
using notation::mk_binders_action;
using notation::mk_exprs_action;
using notation::mk_scoped_expr_action;
using notation::mk_skip_action;
using notation::mk_ext_lua_action;
using notation::transition;
using notation::action;

static char const * g_forbidden_tokens[] = {"!", "@", nullptr};

void check_not_forbidden(char const * tk) {
    auto it = g_forbidden_tokens;
    while (*it) {
        if (strcmp(*it, tk) == 0)
            throw exception(sstream() << "invalid token `" << tk << "`, it is reserved");
        ++it;
    }
}

static auto parse_mixfix_notation(parser & p, mixfix_kind k, bool overload, bool reserve, bool parse_only)
-> pair<notation_entry, optional<token_entry>> {
    std::string tk = parse_symbol(p, "invalid notation declaration, quoted symbol or identifier expected");
    char const * tks = tk.c_str();
    check_not_forbidden(tks);
    environment const & env = p.env();
    optional<token_entry> new_token;
    optional<unsigned> prec;

    optional<parse_table> reserved_pt;
    optional<action> reserved_action;
    if (!reserve) {
        if (k == mixfix_kind::prefix) {
            if (auto at = get_reserved_nud_table(p.env()).find(tks)) {
                reserved_pt     = at->second;
                reserved_action = at->first;
            }
        } else {
            if (auto at = get_reserved_led_table(p.env()).find(tks)) {
                reserved_pt     = at->second;
                reserved_action = at->first;
            }
        }
    }

    if (p.curr_is_token(get_colon_tk())) {
        if (reserved_pt)
            throw parser_error("invalid notation declaration, invalid ':' occurrence "
                               "(declaration matches reserved notation)", p.pos());
        p.next();
        prec = parse_precedence(p, "invalid notation declaration, numeral or 'max' expected");
    }

    if (prec && k == mixfix_kind::infixr && *prec == 0)
        throw parser_error("invalid infixr declaration, precedence must be greater than zero", p.pos());

    if (!prec) {
        if (reserved_action && k == mixfix_kind::prefix && reserved_action->kind() == notation::action_kind::Expr) {
            prec = reserved_action->rbp();
        } else if (reserved_action && k == mixfix_kind::infixr && reserved_action->kind() == notation::action_kind::Expr) {
            prec = reserved_action->rbp();
        } else {
            prec = get_precedence(get_token_table(env), tk.c_str());
            if (prec && k == mixfix_kind::infixr)
                prec = *prec - 1;
        }
    } else {
        auto old_prec = get_precedence(get_token_table(env), tk.c_str());
        if (!old_prec || (k != mixfix_kind::prefix && old_prec != prec))
            new_token = token_entry(tk.c_str(), *prec);
        if (k == mixfix_kind::infixr)
            prec = *prec - 1;
    }

    if (!prec) {
        lean_assert(!reserved_pt);
        throw parser_error("invalid notation declaration, precedence was not provided, "
                           "and it is not set for the given symbol, "
                           "solution: use the 'precedence' command", p.pos());
    }

    if (reserved_action) {
        switch (k) {
        case mixfix_kind::infixl:
            if (reserved_action->kind() != notation::action_kind::Expr || reserved_action->rbp() != *prec)
                throw parser_error("invalid infixl declaration, declaration conflicts with reserved notation", p.pos());
            break;
        case mixfix_kind::infixr:
            if (reserved_action->kind() != notation::action_kind::Expr || reserved_action->rbp() != *prec)
                throw parser_error("invalid infixr declaration, declaration conflicts with reserved notation", p.pos());
            break;
        case mixfix_kind::postfix:
            if (reserved_action->kind() != notation::action_kind::Skip)
                throw parser_error("invalid postfix declaration, declaration conflicts with reserved notation", p.pos());
            break;
        case mixfix_kind::prefix:
            if (reserved_action->kind() != notation::action_kind::Expr || reserved_action->rbp() != *prec)
                throw parser_error("invalid prefix declaration, declaration conflicts with reserved notation", p.pos());
            break;
        }
    }

    if (reserve) {
        // reserve notation commands do not have a denotation
        expr dummy = mk_Prop();
        if (p.curr_is_token(get_assign_tk()))
            throw parser_error("invalid reserve notation, found `:=`", p.pos());
        switch (k) {
        case mixfix_kind::infixl:
            return mk_pair(notation_entry(false, to_list(transition(tks, mk_expr_action(*prec))),
                                          dummy, overload, reserve, parse_only), new_token);
        case mixfix_kind::infixr:
            return mk_pair(notation_entry(false, to_list(transition(tks, mk_expr_action(*prec))),
                                          dummy, overload, reserve, parse_only), new_token);
        case mixfix_kind::postfix:
            return mk_pair(notation_entry(false, to_list(transition(tks, mk_skip_action())),
                                          dummy, overload, reserve, parse_only), new_token);
        case mixfix_kind::prefix:
            return mk_pair(notation_entry(true, to_list(transition(tks, mk_expr_action(*prec))),
                                          dummy, overload, reserve, parse_only), new_token);
        }
    } else {
        p.check_token_next(get_assign_tk(), "invalid notation declaration, ':=' expected");
        auto f_pos = p.pos();
        expr f     = p.parse_expr();
        check_notation_expr(f, f_pos);
        switch (k) {
        case mixfix_kind::infixl:
#if defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
            return mk_pair(notation_entry(false, to_list(transition(tks, mk_expr_action(*prec))),
                                          mk_app(f, Var(1), Var(0)), overload, reserve, parse_only), new_token);
#endif
        case mixfix_kind::infixr:
            return mk_pair(notation_entry(false, to_list(transition(tks, mk_expr_action(*prec))),
                                          mk_app(f, Var(1), Var(0)), overload, reserve, parse_only), new_token);
        case mixfix_kind::postfix:
            return mk_pair(notation_entry(false, to_list(transition(tks, mk_skip_action())),
                                          mk_app(f, Var(0)), overload, reserve, parse_only), new_token);
        case mixfix_kind::prefix:
            return mk_pair(notation_entry(true, to_list(transition(tks, mk_expr_action(*prec))),
                                          mk_app(f, Var(0)), overload, reserve, parse_only), new_token);
        }
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

static notation_entry parse_mixfix_notation(parser & p, mixfix_kind k, bool overload, bool reserve,
                                            buffer<token_entry> & new_tokens, bool parse_only) {
    auto nt = parse_mixfix_notation(p, k, overload, reserve, parse_only);
    if (nt.second)
        new_tokens.push_back(*nt.second);
    return nt.first;
}

static name parse_quoted_symbol_or_token(parser & p, buffer<token_entry> & new_tokens, bool & used_default) {
    used_default = false;
    if (p.curr_is_quoted_symbol()) {
        environment const & env = p.env();
        auto tk   = p.get_name_val();
        auto tks  = tk.to_string();
        auto tkcs = tks.c_str();
        check_not_forbidden(tkcs);
        p.next();
        if (p.curr_is_token(get_colon_tk())) {
            p.next();
            unsigned prec = parse_precedence(p, "invalid notation declaration, precedence (small numeral) expected");
            auto old_prec = get_precedence(get_token_table(env), tkcs);
            if (!old_prec || prec != *old_prec)
                new_tokens.push_back(token_entry(tkcs, prec));
        } else if (!get_precedence(get_token_table(env), tkcs)) {
            new_tokens.push_back(token_entry(tkcs, LEAN_DEFAULT_PRECEDENCE));
            used_default = true;
        }
        return tk;
    } else if (p.curr_is_keyword()) {
        auto tk = p.get_token_info().token();
        check_not_forbidden(tk.to_string().c_str());
        p.next();
        return tk;
    } else {
        throw parser_error("invalid notation declaration, symbol expected", p.pos());
    }
}

static name parse_quoted_symbol_or_token(parser & p, buffer<token_entry> & new_tokens) {
    bool dummy;
    return parse_quoted_symbol_or_token(p, new_tokens, dummy);
}

static expr parse_notation_expr(parser & p, buffer<expr> const & locals) {
    auto pos = p.pos();
    expr r = p.parse_expr();
    r = abstract(r, locals.size(), locals.data());
    check_notation_expr(r, pos);
    return r;
}

static void parse_notation_local(parser & p, buffer<expr> & locals) {
    if (p.curr_is_identifier()) {
        name n = p.get_name_val();
        p.next();
        expr local_type = mk_Prop(); // type used in notation local declarations, it is irrelevant
        expr l = mk_local(n, local_type); // remark: the type doesn't matter
        p.add_local(l);
        locals.push_back(l);
    } else {
        throw parser_error("invalid notation declaration, identifier expected", p.pos());
    }
}

static unsigned get_precedence(environment const & env, buffer<token_entry> const & new_tokens, name const & token) {
    std::string token_str = token.to_string();
    for (auto const & e : new_tokens) {
        if (e.m_token == token_str)
            return e.m_prec;
    }
    auto prec = get_precedence(get_token_table(env), token_str.c_str());
    if (prec)
        return *prec;
    else
        return 0;
}

static action parse_action(parser & p, name const & prev_token, unsigned default_prec,
                           buffer<expr> & locals, buffer<token_entry> & new_tokens) {
    if (p.curr_is_token(get_colon_tk())) {
        p.next();
        if (p.curr_is_numeral() || p.curr_is_token_or_id(get_max_tk())) {
            unsigned prec = parse_precedence(p, "invalid notation declaration, small numeral expected");
            return mk_expr_action(prec);
        } else if (p.curr_is_token_or_id(get_prev_tk())) {
            p.next();
            return mk_expr_action(get_precedence(p.env(), new_tokens, prev_token));
        } else if (p.curr_is_string()) {
            std::string fn = p.get_str_val();
            p.next();
            return mk_ext_lua_action(fn.c_str());
        } else if (p.curr_is_token_or_id(get_scoped_tk())) {
            p.next();
            return mk_scoped_expr_action(mk_var(0));
        } else {
            p.check_token_next(get_lparen_tk(), "invalid notation declaration, '(', numeral or 'scoped' expected");
            if (p.curr_is_token_or_id(get_foldl_tk()) || p.curr_is_token_or_id(get_foldr_tk())) {
                bool is_fold_right = p.curr_is_token_or_id(get_foldr_tk());
                p.next();
                auto prec = parse_optional_precedence(p);
                name sep  = parse_quoted_symbol_or_token(p, new_tokens);
                expr rec;
                {
                    parser::local_scope scope(p);
                    p.check_token_next(get_lparen_tk(), "invalid fold notation argument, '(' expected");
                    parse_notation_local(p, locals);
                    parse_notation_local(p, locals);
                    p.check_token_next(get_comma_tk(),  "invalid fold notation argument, ',' expected");
                    rec  = parse_notation_expr(p, locals);
                    p.check_token_next(get_rparen_tk(), "invalid fold notation argument, ')' expected");
                    locals.pop_back();
                    locals.pop_back();
                }
                optional<expr> ini;
                if (!p.curr_is_token(get_rparen_tk()) && !p.curr_is_quoted_symbol())
                    ini = parse_notation_expr(p, locals);
                optional<name> terminator;
                if (!p.curr_is_token(get_rparen_tk()))
                    terminator = parse_quoted_symbol_or_token(p, new_tokens);
                p.check_token_next(get_rparen_tk(), "invalid fold notation argument, ')' expected");
                return mk_exprs_action(sep, rec, ini, terminator, is_fold_right, prec ? *prec : 0);
            } else if (p.curr_is_token_or_id(get_scoped_tk())) {
                p.next();
                auto prec = parse_optional_precedence(p);
                expr rec;
                {
                    parser::local_scope scope(p);
                    parse_notation_local(p, locals);
                    p.check_token_next(get_comma_tk(),  "invalid scoped notation argument, ',' expected");
                    rec  = parse_notation_expr(p, locals);
                    locals.pop_back();
                }
                p.check_token_next(get_rparen_tk(), "invalid scoped notation argument, ')' expected");
                return mk_scoped_expr_action(rec, prec ? *prec : 0);
            } else if (p.curr_is_token_or_id(get_call_tk())) {
                p.next();
                name fn = p.check_id_next("invalid call notation argument, identifier expected");
                p.check_token_next(get_rparen_tk(), "invalid call notation argument, ')' expected");
                return mk_ext_lua_action(fn.to_string().c_str());
            } else {
                throw parser_error("invalid notation declaration, 'foldl', 'foldr' or 'scoped' expected", p.pos());
            }
        }
    } else {
        return mk_expr_action(default_prec);
    }
}

/**
   \brief If the action for token \c tk in parse table \c pt is an Expr action,
   then return its precedence. We use this value as the default precedence
   when the user does not provide it. The idea is to minimize conflict with existing
   notation.
*/
static unsigned get_default_prec(optional<parse_table> const & pt, name const & tk) {
    if (!pt)
        return LEAN_DEFAULT_PRECEDENCE;
    if (auto at = pt->find(tk)) {
        if (at->first.kind() == notation::action_kind::Expr)
            return at->first.rbp();
    }
    return LEAN_DEFAULT_PRECEDENCE;
}

/** \brief Given a parsing table a \c pt and transition \c new_trans, if \c new_trans is a
    transition in \c pt, then return the successor table */
static optional<parse_table> find_match(optional<parse_table> const & pt, transition const & new_trans) {
    if (pt) {
        if (auto at = pt->find(new_trans.get_token())) {
            if (new_trans.get_action().is_equal(at->first))
                return optional<parse_table>(at->second);
        }
    }
    return optional<parse_table>();
}

/** \brief Lift parse_table::find method to optional<parse_table> */
static optional<pair<action, parse_table>> find_next(optional<parse_table> const & pt, name const & tk) {
    if (pt)
        return pt->find(tk);
    else
        return optional<pair<action, parse_table>>();
}

static unsigned parse_binders_rbp(parser & p) {
    if (p.curr_is_token(get_colon_tk())) {
        p.next();
        return parse_precedence(p, "invalid binder/binders, precedence expected");
    } else {
        return 0;
    }
}

static notation_entry parse_notation_core(parser & p, bool overload, bool reserve, buffer<token_entry> & new_tokens, bool parse_only) {
    buffer<expr>       locals;
    buffer<transition> ts;
    parser::local_scope scope(p);
    bool is_nud = true;
    optional<parse_table> pt;
    optional<parse_table> reserved_pt;
    if (p.curr_is_numeral()) {
        lean_assert(p.curr_is_numeral());
        mpz num = p.get_num_val().get_numerator();
        p.next();
        p.check_token_next(get_assign_tk(), "invalid numeral notation, `:=` expected");
        auto e_pos = p.pos();
        expr e     = p.parse_expr();
        check_notation_expr(e, e_pos);
        return notation_entry(num, e, overload, parse_only);
    } else if (p.curr_is_identifier()) {
        parse_notation_local(p, locals);
        is_nud = false;
        pt = get_led_table(p.env());
        if (!reserve)
            reserved_pt = get_reserved_led_table(p.env());
    } else {
        pt = get_nud_table(p.env());
        if (!reserve)
            reserved_pt = get_reserved_nud_table(p.env());
    }
    bool used_default = false;
    while ((!reserve && !p.curr_is_token(get_assign_tk())) ||
           (reserve && !p.curr_is_command() && !p.curr_is_eof())) {
        name tk = parse_quoted_symbol_or_token(p, new_tokens, used_default);
        if (auto at = find_next(reserved_pt, tk)) {
            action const & a = at->first;
            reserved_pt      = at->second;
            switch (a.kind()) {
            case notation::action_kind::Skip:
                if (!p.curr_is_quoted_symbol() && !p.curr_is_keyword() && !p.curr_is_token(get_assign_tk())) {
                    p.check_token_or_id_next(get_binders_tk(),
                                             "invalid notation declaration, quoted-symbol, keyword or `:=` expected "
                                             "(declaration prefix matches reserved notation)");
                }
                ts.push_back(transition(tk, a));
                break;
            case notation::action_kind::Binder:
                p.check_token_or_id_next(get_binders_tk(),
                                         "invalid notation declaration, 'binder' expected "
                                         "(declaration prefix matches reserved notation)");
                ts.push_back(transition(tk, a));
                break;
            case notation::action_kind::Binders:
                p.check_token_or_id_next(get_binders_tk(),
                                         "invalid notation declaration, 'binders' expected "
                                         "(declaration prefix matches reserved notation)");
                ts.push_back(transition(tk, a));
                break;
            case notation::action_kind::Expr: case notation::action_kind::Exprs: case notation::action_kind::ScopedExpr:
            case notation::action_kind::Ext:  case notation::action_kind::LuaExt: {
                name n = p.check_id_next("invalid notation declaration, identifier expected "
                                         "(declaration prefix matches reserved notation)");
                expr local_type = mk_Prop(); // type used in notation local declarations, it is irrelevant
                expr l = mk_local(n, local_type);
                p.add_local(l);
                locals.push_back(l);
                ts.push_back(transition(tk, a));
                break;
            }}
            if (p.curr_is_token(get_colon_tk()))
                throw parser_error("invalid notation declaration, invalid ':' occurrence "
                                   "(declaration prefix matches reserved notation)", p.pos());
        } else {
            reserved_pt = optional<parse_table>();
            if (p.curr_is_token_or_id(get_binder_tk())) {
                p.next();
                unsigned rbp = parse_binders_rbp(p);
                ts.push_back(transition(tk, mk_binder_action(rbp)));
            } else if (p.curr_is_token_or_id(get_binders_tk())) {
                p.next();
                unsigned rbp = parse_binders_rbp(p);
                ts.push_back(transition(tk, mk_binders_action(rbp)));
            } else if (p.curr_is_identifier()) {
                unsigned default_prec = get_default_prec(pt, tk);
                name n   = p.get_name_val();
                p.next();
                action a = parse_action(p, tk, default_prec, locals, new_tokens);
                expr local_type = mk_Prop(); // type used in notation local declarations, it is irrelevant
                expr l = mk_local(n, local_type);
                p.add_local(l);
                locals.push_back(l);
                ts.push_back(transition(tk, a));
            } else if (p.curr_is_quoted_symbol() || p.curr_is_keyword() ||
                       p.curr_is_token(get_assign_tk()) || p.curr_is_command() || p.curr_is_eof()) {
                ts.push_back(transition(tk, mk_skip_action()));
            } else {
                throw parser_error("invalid notation declaration, quoted-symbol, identifier, "
                                   "'binder', 'binders' expected", p.pos());
            }
        }
        pt = find_match(pt, ts.back());
    }
    // for atomic notation where binding power was not set, we set it to max
    if (used_default && ts.size() == 1 && ts.back().get_action().kind() == notation::action_kind::Skip) {
        lean_assert(!new_tokens.empty());
        new_tokens.back().m_prec = get_max_prec();
    }
    expr n;
    if (reserve) {
        // reserve notation commands do not have a denotation
        lean_assert(p.curr_is_command() || p.curr_is_eof());
        expr dummy = mk_Prop(); // any expression without free variables will do
        n = dummy;
    } else {
        lean_assert(p.curr_is_token(get_assign_tk()));
        p.next();
        if (ts.empty())
            throw parser_error("invalid notation declaration, empty notation is not allowed", p.pos());
        n = parse_notation_expr(p, locals);
    }
    return notation_entry(is_nud, to_list(ts.begin(), ts.end()), n, overload, reserve, parse_only);
}

bool curr_is_notation_decl(parser & p) {
    return
        p.curr_is_token(get_infix_tk()) || p.curr_is_token(get_infixl_tk()) || p.curr_is_token(get_infixr_tk()) ||
        p.curr_is_token(get_postfix_tk()) || p.curr_is_token(get_prefix_tk()) || p.curr_is_token(get_notation_tk());
}

static notation_entry parse_notation(parser & p, bool overload, bool reserve, buffer<token_entry> & new_tokens,
                                     bool allow_local) {
    bool parse_only = false;
    flet<bool> set_allow_local(g_allow_local, allow_local);
    if (p.curr_is_token(get_infix_tk()) || p.curr_is_token(get_infixl_tk())) {
        p.next();
        return parse_mixfix_notation(p, mixfix_kind::infixl, overload, reserve, new_tokens, parse_only);
    } else if (p.curr_is_token(get_infixr_tk())) {
        p.next();
        return parse_mixfix_notation(p, mixfix_kind::infixr, overload, reserve, new_tokens, parse_only);
    } else if (p.curr_is_token(get_postfix_tk())) {
        p.next();
        return parse_mixfix_notation(p, mixfix_kind::postfix, overload, reserve, new_tokens, parse_only);
    } else if (p.curr_is_token(get_prefix_tk())) {
        p.next();
        return parse_mixfix_notation(p, mixfix_kind::prefix, overload, reserve, new_tokens, parse_only);
    } else if (p.curr_is_token(get_notation_tk())) {
        p.next();
        return parse_notation_core(p, overload, reserve, new_tokens, parse_only);
    } else {
        throw parser_error("invalid notation, 'infix', 'infixl', 'infixr', 'prefix', "
                           "'postfix' or 'notation' expected", p.pos());
    }
}

notation_entry parse_notation(parser & p, bool overload, buffer<token_entry> & new_tokens, bool allow_local) {
    bool reserve = false;
    return parse_notation(p, overload, reserve, new_tokens, allow_local);
}

static char g_reserved_chars[] = {'(', ')', ',', 0};

static void check_token(char const * tk) {
    while (tk && *tk) {
        unsigned sz = get_utf8_size(*tk);
        if (sz == 0) {
            throw exception(sstream() << "invalid token `" << tk << "`, contains invalid utf-8 character");
        } else if (sz > 1) {
            // multi-size unicode character
            for (unsigned i = 0; i < sz; i++) {
                if (!*tk)
                    throw exception(sstream() << "invalid token `" << tk << "`, contains invalid utf-8 character");
                ++tk;
            }
        } else {
            auto it = g_reserved_chars;
            while (*it) {
                if (*tk == *it)
                    throw exception(sstream() << "invalid token `" << tk
                                    << "`, it contains reserved character `" << *it << "`");
                ++it;
            }
            ++tk;
        }
    }
}

static environment add_user_token(environment const & env, token_entry const & e, bool persistent) {
    check_token(e.m_token.c_str());
    return add_token(env, e, persistent);
}

static environment add_user_token(environment const & env, char const * val, unsigned prec) {
    check_token(val);
    return add_token(env, val, prec);
}

struct notation_modifiers {
    bool m_persistent;
    bool m_parse_only;
    notation_modifiers():m_persistent(true), m_parse_only(false) {}
    void parse(parser & p) {
        while (true) {
            if (p.curr_is_token(get_local_tk())) {
                p.next();
                m_persistent = false;
            } else if (p.curr_is_token(get_parsing_only_tk())) {
                p.next();
                m_parse_only = true;
            } else {
                return;
            }
        }
    }
};

static environment notation_cmd_core(parser & p, bool overload, bool reserve) {
    notation_modifiers mods;
    mods.parse(p);
    flet<bool> set_allow_local(g_allow_local, in_context(p.env()) || !mods.m_persistent);
    environment env = p.env();
    buffer<token_entry> new_tokens;
    auto ne = parse_notation_core(p, overload, reserve, new_tokens, mods.m_parse_only);
    for (auto const & te : new_tokens)
        env = add_user_token(env, te, mods.m_persistent);
    env = add_notation(env, ne, mods.m_persistent);
    return env;
}

static environment mixfix_cmd(parser & p, mixfix_kind k, bool overload, bool reserve) {
    notation_modifiers mods;
    mods.parse(p);
    flet<bool> set_allow_local(g_allow_local, in_context(p.env()) || !mods.m_persistent);
    auto nt = parse_mixfix_notation(p, k, overload, reserve, mods.m_parse_only);
    environment env = p.env();
    if (nt.second)
        env = add_user_token(env, *nt.second, mods.m_persistent);
    env = add_notation(env, nt.first, mods.m_persistent);
    return env;
}

static environment notation_cmd(parser & p) {
    bool overload = !in_context(p.env());
    bool reserve  = false;
    return notation_cmd_core(p, overload, reserve);
}

static environment infixl_cmd(parser & p) {
    bool overload = !in_context(p.env());
    bool reserve  = false;
    return mixfix_cmd(p, mixfix_kind::infixl, overload, reserve);
}

static environment infixr_cmd(parser & p) {
    bool overload = !in_context(p.env());
    bool reserve  = false;
    return mixfix_cmd(p, mixfix_kind::infixr, overload, reserve);
}

static environment postfix_cmd(parser & p) {
    bool overload = !in_context(p.env());
    bool reserve  = false;
    return mixfix_cmd(p, mixfix_kind::postfix, overload, reserve);
}

static environment prefix_cmd(parser & p) {
    bool overload = !in_context(p.env());
    bool reserve  = false;
    return mixfix_cmd(p, mixfix_kind::prefix, overload, reserve);
}

static environment reserve_cmd(parser & p) {
    bool overload = false;
    bool reserve  = true;
    if (p.curr_is_token(get_notation_tk())) {
        p.next();
        return notation_cmd_core(p, overload, reserve);
    } else if (p.curr_is_token(get_infixl_tk())) {
        p.next();
        return mixfix_cmd(p, mixfix_kind::infixl, overload, reserve);
    } else if (p.curr_is_token(get_infix_tk())) {
        p.next();
        return mixfix_cmd(p, mixfix_kind::infixl, overload, reserve);
    } else if (p.curr_is_token(get_infixr_tk())) {
        p.next();
        return mixfix_cmd(p, mixfix_kind::infixr, overload, reserve);
    } else if (p.curr_is_token(get_prefix_tk())) {
        p.next();
        return mixfix_cmd(p, mixfix_kind::prefix, overload, reserve);
    } else if (p.curr_is_token(get_postfix_tk())) {
        p.next();
        return mixfix_cmd(p, mixfix_kind::postfix, overload, reserve);
    } else {
        throw parser_error("invalid reserve notation, 'infix', 'infixl', 'infixr', 'prefix', "
                           "'postfix' or 'notation' expected", p.pos());
    }
}

static environment precedence_cmd(parser & p) {
    std::string tk = parse_symbol(p, "invalid precedence declaration, quoted symbol or identifier expected");
    p.check_token_next(get_colon_tk(), "invalid precedence declaration, ':' expected");
    unsigned prec = parse_precedence(p, "invalid precedence declaration, numeral or 'max' expected");
    return add_user_token(p.env(), tk.c_str(), prec);
}

void register_notation_cmds(cmd_table & r) {
    add_cmd(r, cmd_info("precedence",   "set token left binding power", precedence_cmd));
    add_cmd(r, cmd_info("infixl",       "declare a new infix (left) notation", infixl_cmd));
    add_cmd(r, cmd_info("infix",        "declare a new infix (left) notation", infixl_cmd));
    add_cmd(r, cmd_info("infixr",       "declare a new infix (right) notation", infixr_cmd));
    add_cmd(r, cmd_info("postfix",      "declare a new postfix notation", postfix_cmd));
    add_cmd(r, cmd_info("prefix",       "declare a new prefix notation", prefix_cmd));
    add_cmd(r, cmd_info("notation",     "declare a new notation", notation_cmd));
    add_cmd(r, cmd_info("reserve",      "reserve notation", reserve_cmd));
}
}
