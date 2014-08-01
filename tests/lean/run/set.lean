import standard
using bool

definition set {{T : Type}} := T → bool
infix `∈` := λx A, A x = tt

check 1 ∈ (λ x, tt)
