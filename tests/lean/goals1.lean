import tools.tactic
open tactic
set_option pp.notation false

theorem foo (A : Type) (a b c : A) (Hab : a = b) (Hbc : b = c) : a = c :=
begin
  apply eq.trans,
  apply Hbc
end