-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura
import logic.eq
open eq.ops

namespace binary
  context
    variable {A : Type}
    variable f : A → A → A
    infixl `*` := f
    definition commutative := ∀{a b}, a*b = b*a
    definition associative := ∀{a b c}, (a*b)*c = a*(b*c)
  end

  context
    variable {A : Type}
    variable {f : A → A → A}
    variable H_comm : commutative f
    variable H_assoc : associative f
    infixl `*` := f
    theorem left_comm : ∀a b c, a*(b*c) = b*(a*c) :=
    take a b c, calc
      a*(b*c) = (a*b)*c  : H_assoc⁻¹
        ...   = (b*a)*c  : {H_comm}
        ...   = b*(a*c)  : H_assoc

    theorem right_comm : ∀a b c, (a*b)*c = (a*c)*b :=
    take a b c, calc
      (a*b)*c = a*(b*c) : H_assoc
        ...   = a*(c*b) : {H_comm}
        ...   = (a*c)*b : H_assoc⁻¹
  end

  context
    variable {A : Type}
    variable {f : A → A → A}
    variable H_assoc : associative f
    infixl `*` := f
    theorem assoc4helper (a b c d) : (a*b)*(c*d) = a*((b*c)*d) :=
    calc
      (a*b)*(c*d) = a*(b*(c*d)) : H_assoc
              ... = a*((b*c)*d) : {H_assoc⁻¹}
  end


end binary
