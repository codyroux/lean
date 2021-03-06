import tools.tactic logic
open tactic

theorem foo (A : Type) (a b c : A) (Hab : a = b) (Hbc : b = c) : a = c :=
begin
  apply eq.trans,
  rename Hab Foo,
  apply Foo,
  apply Hbc,
end
