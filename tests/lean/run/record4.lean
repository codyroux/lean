import logic data.unit

structure point (A : Type) (B : Type) :=
mk :: (x : A) (y : B)

check point.eta

example (p : point num num) : point.mk (point.x p) (point.y p) = p :=
point.eta p

inductive color :=
red, green, blue

structure color_point (A : Type) (B : Type) extends point A B :=
mk :: (c : color)
