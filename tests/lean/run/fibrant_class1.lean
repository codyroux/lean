import general_notation type

inductive fibrant [class] (T : Type) : Type :=
fibrant_mk : fibrant T

inductive path {A : Type'} [fA : fibrant A] (a : A) : A → Type :=
idpath : path a a

notation a ≈ b := path a b

axiom path_fibrant {A : Type'} [fA : fibrant A] (a b : A) : fibrant (path a b)
instance [persistent] path_fibrant

axiom imp_fibrant {A : Type'} {B : Type'} [C1 : fibrant A] [C2 : fibrant B] : fibrant (A → B)
instance imp_fibrant

definition test {A : Type} [fA : fibrant A] {x y : A} :
Π (z : A), y ≈ z → fibrant (x ≈ y → x ≈ z) := _
