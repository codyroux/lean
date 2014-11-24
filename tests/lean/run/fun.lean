import standard
using function num bool


constant f : num → bool
constant g : num → num

check f ∘ g ∘ g

check typeof id : num → num
check num → num ⟨is_typeof⟩ id

constant h : num → bool → num

check flip h
check flip h ff num.zero

check typeof flip h ff num.zero : num

constant f1 : num → num → bool
constant f2 : bool → num

check (f1 on f2) ff tt
