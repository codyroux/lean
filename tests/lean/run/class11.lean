import logic

constant C {A : Type} : A → Prop
class C

constant f {A : Type} (a : A) [H : C a] : Prop

definition g {A : Type} (a b : A) {H1 : C a} {H2 : C b} : Prop :=
f a ∧ f b
