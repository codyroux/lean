/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <fstream>
#include <string>
#include "util/sstream.h"
#include "util/lean_path.h"
#include "frontends/lean/scanner.h"

namespace lean {
bool display_deps(environment const & env, std::ostream & out, std::ostream & err, char const * fname) {
    name import("import");
    name period(".");
    std::ifstream in(fname);
    if (in.bad() || in.fail()) {
        err << "failed to open file '" << fname << "'" << std::endl;
        return false;
    }
    scanner s(in, fname);
    optional<unsigned> k;
    std::string base = dirname(fname);
    bool import_prefix = false;
    bool import_args   = false;
    while (true) {
        scanner::token_kind t = scanner::token_kind::Identifier;
        try {
            t = s.scan(env);
        } catch (exception &) {
            continue;
        }
        if (t == scanner::token_kind::Eof) {
            return ok;
        } else if (t == scanner::token_kind::CommandKeyword && s.get_token_info().value() == import) {
            k = optional<unsigned>();
            import_prefix = true;
        } else if (import_prefix && t == scanner::token_kind::Keyword && s.get_token_info().value() == period) {
            if (!k)
                k = 0;
            else
                k = *k + 1;
        } else if ((import_prefix || import_args) && t == scanner::token_kind::Identifier) {
            import_args = true;
            std::string m_name = find_file(base, k, name_to_file(s.get_name_val()), {".lean", ".olean", ".lua"});
            int last_idx = m_name.find_last_of(".");
            std::string rawname = m_name.substr(0, last_idx);
            std::string ext = m_name.substr(last_idx);
            if (ext == ".lean")
                m_name = rawname + ".olean";
            display_path(out, m_name);
            k = optional<unsigned>();
            import_prefix = true;
            out << "\n";
        } else {
            import_args   = false;
            import_prefix = false;
        }
    }
}
}
