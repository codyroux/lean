/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.order
Author: Jeremy Avigad

Various types of orders. We develop weak orders (<=) and strict orders (<) separately. We also
consider structures with both, where the two are related by

  x < y ↔ (x ≤ y ∧ x ≠ y)   (order_pair)
  x ≤ y ↔ (x < y ∨ x = y)   (strong_order_pair)

These might not hold constructively in some applications, but we can define additional structures
with both < and ≤ as needed.
-/

import logic.eq logic.connectives
import data.unit data.sigma data.prod
import algebra.function algebra.binary

open eq eq.ops

namespace algebra

variable {A : Type}


/- overloaded symbols -/

structure has_le [class] (A : Type) :=
(le : A → A → Prop)

structure has_lt [class] (A : Type) :=
(lt : A → A → Prop)

infixl `<=`   := has_le.le
infixl `≤`   := has_le.le
infixl `<`   := has_lt.lt

definition has_le.ge {A : Type} [s : has_le A] (a b : A) := b ≤ a
notation a ≥ b := has_le.ge a b
notation a >= b := has_le.ge a b

definition has_lt.gt {A : Type} [s : has_lt A] (a b : A) := b < a
notation a > b := has_lt.gt a b

theorem eq_le_trans {A : Type} [s : has_le A] {a b c : A} (H1 : a = b) (H2 : b ≤ c) :
  a ≤ c := H1⁻¹ ▸ H2

theorem le_eq_trans {A : Type} [s : has_le A] {a b c : A} (H1 : a ≤ b) (H2 : b = c) :
  a ≤ c := H2 ▸ H1

theorem eq_lt_trans {A : Type} [s : has_lt A] {a b c : A} (H1 : a = b) (H2 : b < c) :
  a < c := H1⁻¹ ▸ H2

theorem lt_eq_trans {A : Type} [s : has_lt A] {a b c : A} (H1 : a < b) (H2 : b = c) :
  a < c := H2 ▸ H1

calc_trans eq_le_trans
calc_trans le_eq_trans
calc_trans eq_lt_trans
calc_trans lt_eq_trans


/- weak orders -/

structure weak_order [class] (A : Type) extends has_le A :=
(le_refl : ∀a, le a a)
(le_trans : ∀a b c, le a b → le b c → le a c)
(le_antisym : ∀a b, le a b → le b a → a = b)

theorem le_refl [s : weak_order A] (a : A) : a ≤ a := !weak_order.le_refl

theorem le_trans [s : weak_order A] {a b c : A} : a ≤ b → b ≤ c → a ≤ c := !weak_order.le_trans

calc_trans le_trans

theorem le_antisym [s : weak_order A] {a b : A} : a ≤ b → b ≤ a → a = b := !weak_order.le_antisym

structure linear_weak_order [class] (A : Type) extends weak_order A :=
(le_total : ∀a b, le a b ∨ le b a)

theorem le_total [s : linear_weak_order A] {a b : A} : a ≤ b ∨ b ≤ a :=
!linear_weak_order.le_total


/- strict orders -/

structure strict_order [class] (A : Type) extends has_lt A :=
(lt_irrefl : ∀a, ¬ lt a a)
(lt_trans : ∀a b c, lt a b → lt b c → lt a c)

theorem lt_irrefl [s : strict_order A] (a : A) : ¬ a < a := !strict_order.lt_irrefl

theorem lt_trans [s : strict_order A] {a b c : A} : a < b → b < c → a < c := !strict_order.lt_trans

calc_trans lt_trans

theorem lt_imp_ne [s : strict_order A] {a b : A} : a < b → a ≠ b :=
assume lt_ab : a < b, assume eq_ab : a = b, lt_irrefl a (eq_ab⁻¹ ▸ lt_ab)


/- well-founded orders -/

structure wf_strict_order [class] (A : Type) extends strict_order A :=
(wf_rec : ∀P : A → Type, (∀x, (∀y, lt y x → P y) → P x) → ∀x, P x)

definition wf_rec_on {A : Type} [s : wf_strict_order A] {P : A → Type}
    (x : A) (H : ∀x, (∀y, wf_strict_order.lt y x → P y) → P x) : P x :=
wf_strict_order.wf_rec P H x

theorem wf_ind_on.{u v} {A : Type.{u}} [s : wf_strict_order.{u 0} A] {P : A → Prop}
    (x : A) (H : ∀x, (∀y, wf_strict_order.lt y x → P y) → P x) : P x :=
wf_rec_on x H


/- structures with a weak and a strict order -/

structure order_pair [class] (A : Type) extends weak_order A, has_lt A :=
(lt_iff_le_ne : ∀a b, lt a b ↔ (le a b ∧ a ≠ b))

theorem lt_iff_le_ne [s : order_pair A] {a b : A} : a < b ↔ (a ≤ b ∧ a ≠ b) :=
!order_pair.lt_iff_le_ne

theorem lt_imp_le [s : order_pair A] {a b : A} (H : a < b) : a ≤ b :=
and.elim_left (iff.mp lt_iff_le_ne H)

theorem le_ne_imp_lt [s : order_pair A] {a b : A} (H1 : a ≤ b) (H2 : a ≠ b) : a < b :=
iff.mp (iff.symm lt_iff_le_ne) (and.intro H1 H2)

definition order_pair.to_strict_order [instance] [s : order_pair A] : strict_order A :=
strict_order.mk
  order_pair.lt
  (show ∀a, ¬ a < a, from
    take a,
    assume H : a < a,
    have H1 : a ≠ a, from and.elim_right (iff.mp !lt_iff_le_ne H),
    H1 rfl)
  (show ∀a b c, a < b → b < c → a < c, from
    take a b c,
    assume lt_ab : a < b,
    have le_ab : a ≤ b, from lt_imp_le lt_ab,
    assume lt_bc : b < c,
    have le_bc : b ≤ c, from lt_imp_le lt_bc,
    have le_ac : a ≤ c, from le_trans le_ab le_bc,
    have ne_ac : a ≠ c, from
      assume eq_ac : a = c,
      have le_ba : b ≤ a, from eq_ac⁻¹ ▸ le_bc,
      have eq_ab : a = b, from le_antisym le_ab le_ba,
      have ne_ab : a ≠ b, from and.elim_right (iff.mp lt_iff_le_ne lt_ab),
      ne_ab eq_ab,
    show a < c, from le_ne_imp_lt le_ac ne_ac)

theorem lt_le_trans [s : order_pair A] {a b c : A} : a < b → b ≤ c → a < c :=
assume lt_ab : a < b,
assume le_bc : b ≤ c,
have le_ac : a ≤ c, from le_trans (lt_imp_le lt_ab) le_bc,
have ne_ac : a ≠ c, from
  assume eq_ac : a = c,
  have le_ba : b ≤ a, from eq_ac⁻¹ ▸ le_bc,
  have eq_ab : a = b, from le_antisym (lt_imp_le lt_ab) le_ba,
  show false, from lt_imp_ne lt_ab eq_ab,
show a < c, from le_ne_imp_lt le_ac ne_ac

theorem le_lt_trans [s : order_pair A] {a b c : A} : a ≤ b → b < c → a < c :=
assume le_ab : a ≤ b,
assume lt_bc : b < c,
have le_ac : a ≤ c, from le_trans le_ab (lt_imp_le lt_bc),
have ne_ac : a ≠ c, from
  assume eq_ac : a = c,
  have le_cb : c ≤ b, from eq_ac ▸ le_ab,
  have eq_bc : b = c, from le_antisym (lt_imp_le lt_bc) le_cb,
  show false, from lt_imp_ne lt_bc eq_bc,
show a < c, from le_ne_imp_lt le_ac ne_ac

calc_trans le_lt_trans
calc_trans lt_le_trans

structure strong_order_pair [class] (A : Type) extends strict_order A, has_le A :=
(le_iff_lt_or_eq : ∀a b, le a b ↔ lt a b ∨ a = b)

theorem le_iff_lt_or_eq [s : strong_order_pair A] {a b : A} : a ≤ b ↔ a < b ∨ a = b :=
!strong_order_pair.le_iff_lt_or_eq

theorem le_imp_lt_or_eq [s : strong_order_pair A] {a b : A} (le_ab : a ≤ b) : a < b ∨ a = b :=
iff.mp le_iff_lt_or_eq le_ab

definition strong_order_pair.to_order_pair [instance] [s : strong_order_pair A] : order_pair A :=
order_pair.mk
  strong_order_pair.le
  (take a, show a ≤ a, from iff.mp (iff.symm le_iff_lt_or_eq) (or.intro_right _ rfl))
  (take a b c,
    assume le_ab : a ≤ b,
    assume le_bc : b ≤ c,
    show a ≤ c, from
      or.elim (le_imp_lt_or_eq le_ab)
        (assume lt_ab : a < b,
          or.elim (le_imp_lt_or_eq le_bc)
            (assume lt_bc : b < c,
              iff.elim_right le_iff_lt_or_eq (or.intro_left _ (lt_trans lt_ab lt_bc)))
            (assume eq_bc : b = c, eq_bc ▸ le_ab))
        (assume eq_ab : a = b,
            eq_ab⁻¹ ▸ le_bc))
  (take a b,
    assume le_ab : a ≤ b,
    assume le_ba : b ≤ a,
    show a = b, from
      or.elim (le_imp_lt_or_eq le_ab)
        (assume lt_ab : a < b,
          or.elim (le_imp_lt_or_eq le_ba)
            (assume lt_ba : b < a, absurd (lt_trans lt_ab lt_ba) (lt_irrefl a))
            (assume eq_ba : b = a, eq_ba⁻¹))
        (assume eq_ab : a = b, eq_ab))
  strong_order_pair.lt
  (take a b,
    iff.intro
      (assume lt_ab : a < b,
        have le_ab : a ≤ b, from iff.elim_right le_iff_lt_or_eq (or.intro_left _ lt_ab),
        show a ≤ b ∧ a ≠ b, from and.intro le_ab (lt_imp_ne lt_ab))
      (assume H : a ≤ b ∧ a ≠ b,
        have H1 : a < b ∨ a = b, from le_imp_lt_or_eq (and.elim_left H),
        show a < b, from or.resolve_left H1 (and.elim_right H)))

structure linear_order_pair (A : Type) extends order_pair A, linear_weak_order A

structure linear_strong_order_pair (A : Type) extends strong_order_pair A :=
(trichotomy : ∀a b, lt a b ∨ a = b ∨ lt b a)

end algebra
