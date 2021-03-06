import logic data.prod
open eq.ops prod

inductive tree (A : Type) :=
leaf : A → tree A,
node : tree A → tree A → tree A

inductive one.{l} : Type.{max 1 l} :=
star : one

set_option pp.universes true

namespace tree
namespace manual
  section
    universe variables l₁ l₂
    variable {A : Type.{l₁}}
    variable (C : tree A → Type.{l₂})
    definition below (t : tree A) : Type :=
    rec_on t (λ a, one.{l₂}) (λ t₁ t₂ r₁ r₂, C t₁ × C t₂ × r₁ × r₂)
  end

  section
    universe variables l₁ l₂
    variable {A : Type.{l₁}}
    variable {C : tree A → Type.{l₂}}
    definition below_rec_on (t : tree A) (H : Π (n : tree A), below C n → C n) : C t
    := have general : C t × below C t, from
        rec_on t
          (λa, (H (leaf a) one.star, one.star))
          (λ (l r : tree A) (Hl : C l × below C l) (Hr : C r × below C r),
            have b : below C (node l r), from
              (pr₁ Hl, pr₁ Hr, pr₂ Hl, pr₂ Hr),
            have c : C (node l r), from
              H (node l r) b,
            (c, b)),
       pr₁ general
  end
end manual
  section
    universe variables l₁ l₂
    variable {A : Type.{l₁}}
    variable {C : tree A → Type.{l₂+1}}
    definition below_rec_on (t : tree A) (H : Π (n : tree A), @below A C n → C n) : C t
    := have general : C t × @below A C t, from
        rec_on t
          (λa, (H (leaf a) unit.star, unit.star))
          (λ (l r : tree A) (Hl : C l × @below A C l) (Hr : C r × @below A C r),
            have b : @below A C (node l r), from
              ((pr₁ Hl, pr₂ Hl), (pr₁ Hr, pr₂ Hr)),
            have c : C (node l r), from
              H (node l r) b,
            (c, b)),
       pr₁ general
  end

  set_option pp.universes true

  theorem leaf_ne_tree {A : Type} (a : A) (l r : tree A) : leaf a ≠ node l r :=
  assume h : leaf a = node l r,
  no_confusion h
end tree
