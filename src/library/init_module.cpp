/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/unifier.h"
#include "library/kernel_serializer.h"
#include "library/let.h"
#include "library/typed_expr.h"
#include "library/choice.h"
#include "library/string.h"
#include "library/num.h"
#include "library/resolve_macro.h"
#include "library/annotation.h"
#include "library/explicit.h"
#include "library/module.h"
#include "library/protected.h"
#include "library/private.h"
#include "library/scoped_ext.h"
#include "library/reducible.h"
#include "library/aliases.h"
#include "library/coercion.h"
#include "library/unifier_plugin.h"
#include "library/io_state.h"
#include "library/kernel_bindings.h"
#include "library/match.h"
#include "library/sorry.h"
#include "library/placeholder.h"
#include "library/print.h"
#include "library/fingerprint.h"

namespace lean {
void initialize_library_module() {
    initialize_fingerprint();
    initialize_print();
    initialize_placeholder();
    initialize_match();
    initialize_kernel_bindings();
    initialize_io_state();
    initialize_unifier();
    initialize_kernel_serializer();
    initialize_let();
    initialize_typed_expr();
    initialize_choice();
    initialize_num();
    initialize_string();
    initialize_resolve_macro();
    initialize_annotation();
    initialize_explicit();
    initialize_module();
    initialize_protected();
    initialize_private();
    initialize_scoped_ext();
    initialize_reducible();
    initialize_aliases();
    initialize_coercion();
    initialize_unifier_plugin();
    initialize_sorry();
}

void finalize_library_module() {
    finalize_sorry();
    finalize_unifier_plugin();
    finalize_coercion();
    finalize_aliases();
    finalize_reducible();
    finalize_scoped_ext();
    finalize_private();
    finalize_protected();
    finalize_module();
    finalize_explicit();
    finalize_annotation();
    finalize_resolve_macro();
    finalize_string();
    finalize_num();
    finalize_choice();
    finalize_typed_expr();
    finalize_let();
    finalize_kernel_serializer();
    finalize_unifier();
    finalize_io_state();
    finalize_kernel_bindings();
    finalize_match();
    finalize_placeholder();
    finalize_print();
    finalize_fingerprint();
}
}
