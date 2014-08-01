/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "kernel/formatter.h"

namespace lean {
static std::function<void(std::ostream &, expr const & e)> * g_print = nullptr;

void set_print_fn(std::function<void(std::ostream &, expr const &)> const & fn) {
    if (g_print)
        delete g_print;
    g_print = new std::function<void(std::ostream &, expr const &)>(fn);
}

bool is_internal_name(name n) {
    while (!n.is_atomic())
        n = n.get_prefix();
    return n.is_numeral();
}

static name g_x("x");
std::pair<expr, expr> binding_body_fresh(expr const & b, bool preserve_type) {
    lean_assert(is_binding(b));
    name n = binding_name(b);
    if (is_internal_name(n))
        n = g_x;
    n = pick_unused_name(binding_body(b), n);
    expr c = mk_local(n, preserve_type ? binding_domain(b) : expr());
    return mk_pair(instantiate(binding_body(b), c), c);
}

static name g_internal("M");
name fix_internal_name(name const & a) {
    if (a.is_atomic()) {
        if (a.is_numeral())
            return g_internal;
        else
            return a;
    } else {
        throw exception("print function is not available, Lean was not initialized correctly");
    }
    return out;
}

void print(lean::expr const & a) { std::cout << a << std::endl; }

void initialize_formatter() {}

void finalize_formatter() {
    if (g_print)
        delete g_print;
}
}
