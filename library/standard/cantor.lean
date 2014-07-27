-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Cody Roux

import logic classical
-- using eq_proofs

abbreviation subsets (P : Type) := P → Prop.

section

hypothesis A : Type.

hypothesis r : A → subsets A.

hypothesis i : subsets A → A.

hypothesis retract {P : subsets A} {a : A} : r (i P) a = P a.
-- hypothesis retract_r : retract r i.

definition delta (a:A) : Prop := ¬ (r a a).

notation `δ` := delta.

hypothesis P : Prop.

-- check eq_rec.

-- Crashes unifier!
-- theorem false_aux : ¬ (δ (i delta))
--         := assume H : δ (i delta),
--            have H' : r (i delta) (i delta),
--                 from eq_rec H _ (symm retract),
--            H H'.

theorem delta_aux : ¬ (δ (i delta))
        := assume H : δ (i delta),
           H (subst (symm retract) H).

check delta_aux.

theorem iff_false {p : Prop} : (p ↔ ¬ p) → false
:= assume H : p ↔ ¬ p,
   have H1 : p → ¬ p, from iff_mp_left H,
   have H2 : p → false, from λ h, H1 h h,
   have H3 : p, from iff_mp_right H H2,
   H2 H3.


-- axiom sorry {P : Prop} : P.

theorem delta_iff_neg : δ (i delta) ↔ ¬ δ (i delta)
:= iff_intro
        (assume H: δ (i delta),
        -- something weird is happening here
        delta_aux)
        -- sorry)

        (assume H : ¬ δ (i delta),
        subst (symm retract) H).

theorem contr : false := iff_false delta_iff_neg.

end

hypothesis I : Type.

-- definition F (X : Type) : Type := (X → Prop) → Prop.
hypothesis F.{l} (X : Type.{l}) : Type.{l}.

-- set_option pp.universes true.

check F.


-- check F.

hypothesis unfold : I → F I.
check unfold.
hypothesis fold   : F I → I.
check fold.
hypothesis iso1 : ∀ x : I, fold (unfold x) = x.
hypothesis iso2 : ∀ x : F I, unfold (fold x) = x.

section

definition retract {A B : Type} (f : A → B) (g : B → A) := ∀ a : A, g (f a) = a.

definition inj {A B : Type} (f : A → B):= ∀ x y : A, f x = f y → x = y.

check case.

definition ite {A : Type} : Prop → A → A → A := λ P a b, case _ a b P.

axiom sorry (t : Type) : t.

check exists_intro.

check inhabited_elim.

definition image {A B : Type} (f : A → B) : B → Prop := λ y, ∃ x : A, f x = y.

theorem inj_is_retract : ∀ (A B : Type) (f : A → B), inhabited A → inj f → ∃ g, retract f g
:= assume A B : Type,
   assume f : A → B,
   assume H : inhabited A,
   assume inj_f : inj f,
          inhabited_elim H
          (assume a : A,
           let g := sorry (B → A) in
           exists_intro g _).
