--- Copyright (c) 2014 Floris van Doorn. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Author: Floris van Doorn, Leonardo de Moura

-- Basic operations on the natural numbers.

import .decl data.num algebra.binary

open eq.ops binary

namespace nat

definition of_num [coercion] [reducible] (n : num) : ℕ :=
num.rec zero
  (λ n, pos_num.rec (succ zero) (λ n r, r + r + (succ zero)) (λ n r, r + r) n) n

definition addl (x y : ℕ) : ℕ :=
nat.rec y (λ n r, succ r) x
infix `⊕`:65 := addl

theorem addl.succ_right (n m : ℕ) : n ⊕ succ m = succ (n ⊕ m) :=
nat.induction_on n
  rfl
  (λ n₁ ih, calc
    succ n₁ ⊕ succ m = succ (n₁ ⊕ succ m)   : rfl
             ...     = succ (succ (n₁ ⊕ m)) : ih
             ...     = succ (succ n₁ ⊕ m)   : rfl)

theorem add_eq_addl (x : ℕ) : ∀y, x + y = x ⊕ y :=
nat.induction_on x
  (λ y, nat.induction_on y
    rfl
    (λ y₁ ih, calc
      zero + succ y₁ = succ (zero + y₁)  : rfl
              ...    = succ (zero ⊕ y₁) : {ih}
              ...    = zero ⊕ (succ y₁) : rfl))
  (λ x₁ ih₁ y, nat.induction_on y
    (calc
      succ x₁ + zero  = succ (x₁ + zero)  : rfl
                  ... = succ (x₁ ⊕ zero) : {ih₁ zero}
                  ... = succ x₁ ⊕ zero   : rfl)
    (λ y₁ ih₂, calc
      succ x₁ + succ y₁ = succ (succ x₁ + y₁) : rfl
                   ...  = succ (succ x₁ ⊕ y₁) : {ih₂}
                   ...  = succ x₁ ⊕ succ y₁   : addl.succ_right))

-- Successor and predecessor
-- -------------------------

theorem succ_ne_zero (n : ℕ) : succ n ≠ 0 :=
assume H, no_confusion H

-- add_rewrite succ_ne_zero

theorem pred.zero : pred 0 = 0 :=
rfl

theorem pred.succ (n : ℕ) : pred (succ n) = n :=
rfl

irreducible pred

theorem zero_or_succ_pred (n : ℕ) : n = 0 ∨ n = succ (pred n) :=
induction_on n
  (or.inl rfl)
  (take m IH, or.inr
    (show succ m = succ (pred (succ m)), from congr_arg succ !pred.succ⁻¹))

theorem zero_or_exists_succ (n : ℕ) : n = 0 ∨ ∃k, n = succ k :=
or.imp_or (zero_or_succ_pred n) (assume H, H)
    (assume H : n = succ (pred n), exists_intro (pred n) H)

theorem case {P : ℕ → Prop} (n : ℕ) (H1: P 0) (H2 : ∀m, P (succ m)) : P n :=
induction_on n H1 (take m IH, H2 m)

theorem succ.inj {n m : ℕ} (H : succ n = succ m) : n = m :=
no_confusion H (λe, e)

theorem succ.ne_self {n : ℕ} : succ n ≠ n :=
induction_on n
  (take H : 1 = 0,
    have ne : 1 ≠ 0, from !succ_ne_zero,
    absurd H ne)
  (take k IH H, IH (succ.inj H))


theorem discriminate {B : Prop} {n : ℕ} (H1: n = 0 → B) (H2 : ∀m, n = succ m → B) : B :=
or.elim (zero_or_succ_pred n)
  (take H3 : n = 0, H1 H3)
  (take H3 : n = succ (pred n), H2 (pred n) H3)

theorem two_step_induction_on {P : ℕ → Prop} (a : ℕ) (H1 : P 0) (H2 : P 1)
    (H3 : ∀ (n : ℕ) (IH1 : P n) (IH2 : P (succ n)), P (succ (succ n))) : P a :=
have stronger : P a ∧ P (succ a), from
  induction_on a
    (and.intro H1 H2)
    (take k IH,
      have IH1 : P k, from and.elim_left IH,
      have IH2 : P (succ k), from and.elim_right IH,
        and.intro IH2 (H3 k IH1 IH2)),
  and.elim_left stronger

theorem sub_induction {P : ℕ → ℕ → Prop} (n m : ℕ) (H1 : ∀m, P 0 m)
   (H2 : ∀n, P (succ n) 0) (H3 : ∀n m, P n m → P (succ n) (succ m)) : P n m :=
have general : ∀m, P n m, from induction_on n
  (take m : ℕ, H1 m)
  (take k : ℕ,
    assume IH : ∀m, P k m,
    take m : ℕ,
    discriminate
      (assume Hm : m = 0, Hm⁻¹ ▸ (H2 k))
      (take l : ℕ, assume Hm : m = succ l, Hm⁻¹ ▸ (H3 k l (IH l)))),
general m

-- Addition
-- --------
theorem add.zero_right (n : ℕ) : n + 0 = n :=
rfl

theorem add.succ_right (n m : ℕ) : n + succ m = succ (n + m) :=
rfl

irreducible add

theorem add.zero_left (n : ℕ) : 0 + n = n :=
induction_on n
    !add.zero_right
    (take m IH, show 0 + succ m = succ m, from
      calc
        0 + succ m = succ (0 + m) : add.succ_right
               ... = succ m       : IH)

theorem add.succ_left (n m : ℕ) : (succ n) + m = succ (n + m) :=
induction_on m
    (!add.zero_right ▸ !add.zero_right)
    (take k IH, calc
      succ n + succ k = succ (succ n + k)    : add.succ_right
                  ... = succ (succ (n + k))  : IH
                  ... = succ (n + succ k)    : add.succ_right)

theorem add.comm (n m : ℕ) : n + m = m + n :=
induction_on m
    (!add.zero_right ⬝ !add.zero_left⁻¹)
    (take k IH, calc
        n + succ k = succ (n+k)   : add.succ_right
               ... = succ (k + n) : IH
               ... = succ k + n   : add.succ_left)

theorem add.move_succ (n m : ℕ) : succ n + m = n + succ m :=
!add.succ_left ⬝ !add.succ_right⁻¹

theorem add.comm_succ (n m : ℕ) : n + succ m = m + succ n :=
!add.move_succ⁻¹ ⬝ !add.comm

theorem add.assoc (n m k : ℕ) : (n + m) + k = n + (m + k) :=
induction_on k
    (!add.zero_right ▸ !add.zero_right)
    (take l IH,
      calc
        (n + m) + succ l = succ ((n + m) + l)  : add.succ_right
                     ... = succ (n + (m + l))  : IH
                     ... = n + succ (m + l)    : add.succ_right
                     ... = n + (m + succ l)    : add.succ_right)

theorem add.left_comm (n m k : ℕ) : n + (m + k) = m + (n + k) :=
left_comm add.comm add.assoc n m k

theorem add.right_comm (n m k : ℕ) : n + m + k = n + k + m :=
right_comm add.comm add.assoc n m k

-- ### cancelation

theorem add.cancel_left {n m k : ℕ} : n + m = n + k → m = k :=
induction_on n
  (take H : 0 + m = 0 + k,
    !add.zero_left⁻¹ ⬝ H ⬝ !add.zero_left)
  (take (n : ℕ) (IH : n + m = n + k → m = k) (H : succ n + m = succ n + k),
    have H2 : succ (n + m) = succ (n + k),
    from calc
      succ (n + m) = succ n + m   : add.succ_left
               ... = succ n + k   : H
               ... = succ (n + k) : add.succ_left,
    have H3 : n + m = n + k, from succ.inj H2,
    IH H3)

theorem add.cancel_right {n m k : ℕ} (H : n + m = k + m) : n = k :=
have H2 : m + n = m + k, from !add.comm ⬝ H ⬝ !add.comm,
  add.cancel_left H2

theorem add.eq_zero_left {n m : ℕ} : n + m = 0 → n = 0 :=
induction_on n
  (take (H : 0 + m = 0), rfl)
  (take k IH,
    assume H : succ k + m = 0,
    absurd
      (show succ (k + m) = 0, from calc
         succ (k + m) = succ k + m : add.succ_left
                  ... = 0          : H)
      !succ_ne_zero)

theorem add.eq_zero_right {n m : ℕ} (H : n + m = 0) : m = 0 :=
add.eq_zero_left (!add.comm ⬝ H)

theorem add.eq_zero {n m : ℕ} (H : n + m = 0) : n = 0 ∧ m = 0 :=
and.intro (add.eq_zero_left H) (add.eq_zero_right H)

-- ### misc

theorem add.one (n : ℕ) : n + 1 = succ n :=
!add.zero_right ▸ !add.succ_right

theorem add.one_left (n : ℕ) : 1 + n = succ n :=
!add.zero_left ▸ !add.succ_left

-- TODO: rename? remove?
theorem induction_plus_one {P : nat → Prop} (a : ℕ) (H1 : P 0)
    (H2 : ∀ (n : ℕ) (IH : P n), P (n + 1)) : P a :=
nat.rec H1 (take n IH, !add.one ▸ (H2 n IH)) a

-- Multiplication
-- --------------

theorem mul.zero_right (n : ℕ) : n * 0 = 0 :=
rfl

theorem mul.succ_right (n m : ℕ) : n * succ m = n * m + n :=
rfl

irreducible mul

-- ### commutativity, distributivity, associativity, identity

theorem mul.zero_left (n : ℕ) : 0 * n = 0 :=
induction_on n
  !mul.zero_right
  (take m IH, !mul.succ_right ⬝ !add.zero_right ⬝ IH)

theorem mul.succ_left (n m : ℕ) : (succ n) * m = (n * m) + m :=
induction_on m
  (!mul.zero_right ⬝ !mul.zero_right⁻¹ ⬝ !add.zero_right⁻¹)
  (take k IH, calc
    succ n * succ k = (succ n * k) + succ n   : mul.succ_right
                ... = (n * k) + k + succ n    : IH
                ... = (n * k) + (k + succ n)  : add.assoc
                ... = (n * k) + (n + succ k)  : add.comm_succ
                ... = (n * k) + n + succ k    : add.assoc
                ... = (n * succ k) + succ k   : mul.succ_right)

theorem mul.comm (n m : ℕ) : n * m = m * n :=
induction_on m
  (!mul.zero_right ⬝ !mul.zero_left⁻¹)
  (take k IH, calc
    n * succ k = n * k + n    : mul.succ_right
           ... = k * n + n    : IH
           ... = (succ k) * n : mul.succ_left)

theorem mul.distr_right (n m k : ℕ) : (n + m) * k = n * k + m * k :=
induction_on k
  (calc
    (n + m) * 0 = 0             : mul.zero_right
            ... = 0 + 0         : add.zero_right
            ... = n * 0 + 0     : mul.zero_right
            ... = n * 0 + m * 0 : mul.zero_right)
  (take l IH, calc
    (n + m) * succ l = (n + m) * l + (n + m)    : mul.succ_right
                 ... = n * l + m * l + (n + m)  : IH
                 ... = n * l + m * l + n + m    : add.assoc
                 ... = n * l + n + m * l + m    : add.right_comm
                 ... = n * l + n + (m * l + m)  : add.assoc
                 ... = n * succ l + (m * l + m) : mul.succ_right
                 ... = n * succ l + m * succ l  : mul.succ_right)

theorem mul.distr_left (n m k : ℕ) : n * (m + k) = n * m + n * k :=
calc
  n * (m + k) = (m + k) * n    : mul.comm
          ... = m * n + k * n  : mul.distr_right
          ... = n * m + k * n  : mul.comm
          ... = n * m + n * k  : mul.comm

theorem mul.assoc (n m k : ℕ) : (n * m) * k = n * (m * k) :=
induction_on k
  (calc
    (n * m) * 0 = 0           : mul.zero_right
            ... = n * 0       : mul.zero_right
            ... = n * (m * 0) : mul.zero_right)
  (take l IH,
    calc
      (n * m) * succ l = (n * m) * l + n * m : mul.succ_right
                   ... = n * (m * l) + n * m : IH
                   ... = n * (m * l + m)     : mul.distr_left
                   ... = n * (m * succ l)    : mul.succ_right)

theorem mul.left_comm (n m k : ℕ) : n * (m * k) = m * (n * k) :=
left_comm mul.comm mul.assoc n m k

theorem mul.right_comm (n m k : ℕ) : n * m * k = n * k * m :=
right_comm mul.comm mul.assoc n m k

theorem mul.one_right (n : ℕ) : n * 1 = n :=
calc
  n * 1 = n * 0 + n : mul.succ_right
    ... = 0 + n     : mul.zero_right
    ... = n         : add.zero_left

theorem mul.one_left (n : ℕ) : 1 * n = n :=
calc
  1 * n = n * 1 : mul.comm
    ... = n     : mul.one_right

theorem mul.eq_zero {n m : ℕ} (H : n * m = 0) : n = 0 ∨ m = 0 :=
discriminate
  (take Hn : n = 0, or.inl Hn)
  (take (k : ℕ),
    assume (Hk : n = succ k),
    discriminate
      (take (Hm : m = 0), or.inr Hm)
      (take (l : ℕ),
        assume (Hl : m = succ l),
        have Heq : succ (k * succ l + l) = n * m, from
         (calc
            n * m = n * succ l            : Hl
              ... = succ k * succ l       : Hk
              ... = k * succ l + succ l   : mul.succ_left
              ... = succ (k * succ l + l) : add.succ_right)⁻¹,
        absurd (Heq ⬝ H) !succ_ne_zero))

end nat
