import logic

context
hypothesis P : Prop.

theorem crash
        := assume H : P,
           have H' : ¬ P,
           from H,
           _.
