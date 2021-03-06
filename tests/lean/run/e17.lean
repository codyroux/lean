inductive nat : Type :=
zero : nat,
succ : nat → nat

inductive list (A : Type) : Type :=
nil {} : list A,
cons   : A → list A → list A

inductive int : Type :=
of_nat : nat → int,
neg : nat → int

coercion int.of_nat

constants n m : nat
constants i j : int
namespace list end list open list

check cons i (cons i nil)
check cons n (cons n nil)
check cons i (cons n nil)
check cons n (cons i nil)
check cons n (cons i (cons m (cons j nil)))
