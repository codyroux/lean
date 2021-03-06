/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"

namespace lean {
environment mk_projections(environment const & env, name const & n, buffer<name> const & proj_names, bool inst_implicit = false);
environment mk_projections(environment const & env, name const & n, bool inst_implicit = false);
}
