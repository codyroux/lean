-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Cody Roux

import logic
using eq_proofs

abbreviation subsets (P : Type) := P → Prop.

section

hypothesis A : Type.

hypothesis r : A → subsets A.

hypothesis i : subsets A → A.

hypothesis retract {P : subsets A} {a : A} : r (i P) a = P a.

definition delta (a:A) : Prop := ¬ (r a a).

notation `δ` := delta.

hypothesis P : Prop.

check eq_rec.

-- Crashes unifier!
-- theorem false_aux : ¬ (δ (i delta))
--         := assume H : δ (i delta),
--            have H' : r (i delta) (i delta),
--                 from eq_rec H _ (symm retract),
--            H H'.

theorem delta_aux : ¬ (δ (i delta))
        := assume H : δ (i delta),
           H (subst (symm retract) H).

theorem iff_false {p : Prop} : (p ↔ ¬ p) → false
:= assume H : p ↔ ¬ p,
   have H1 : p → ¬ p, from iff_mp_left H,
   have H2 : p → false, from λ h, H1 h h,
   have H3 : p, from iff_mp_right H H2,
   H2 H3.


axiom sorry {P : Prop} : P.

theorem delta_iff_neg : δ (i delta) ↔ ¬ δ (i delta)
:= iff_intro
        (assume H: δ (i delta),
        -- something weird is happening here
        delta_aux)

        (assume H : ¬ δ (i delta),
        subst (symm retract) H).

theorem contr : false := iff_false delta_iff_neg.