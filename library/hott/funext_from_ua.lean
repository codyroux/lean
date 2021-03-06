-- Copyright (c) 2014 Jakob von Raumer. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jakob von Raumer
-- Ported from Coq HoTT
import hott.equiv hott.funext_varieties hott.axioms.ua hott.axioms.funext
import data.prod data.sigma data.unit

open path function prod sigma truncation Equiv IsEquiv unit ua_type

context
  universe variables l
  parameter [UA : ua_type.{l+1}]

  protected theorem ua_isequiv_postcompose {A B : Type.{l+1}} {C : Type}
      {w : A → B} {H0 : IsEquiv w} : IsEquiv (@compose C A B w) :=
    let w' := Equiv.mk w H0 in
    let eqinv : A ≈ B := ((@IsEquiv.inv _ _ _ (@ua_type.inst UA A B)) w') in
    let eq' := equiv_path eqinv in
    IsEquiv.adjointify (@compose C A B w)
      (@compose C B A (IsEquiv.inv w))
      (λ (x : C → B),
        have eqretr : eq' ≈ w',
          from (@retr _ _ (@equiv_path A B) (@ua_type.inst UA A B) w'),
        have invs_eq : (equiv_fun eq')⁻¹ ≈ (equiv_fun w')⁻¹,
          from inv_eq eq' w' eqretr,
        have eqfin : (equiv_fun eq') ∘ ((equiv_fun eq')⁻¹ ∘ x) ≈ x,
          from (λ p,
            (@path.rec_on Type.{l+1} A
              (λ B' p', Π (x' : C → B'), (equiv_fun (equiv_path p'))
                ∘ ((equiv_fun (equiv_path p'))⁻¹ ∘ x') ≈ x')
              B p (λ x', idp))
            ) eqinv x,
        have eqfin' : (equiv_fun w') ∘ ((equiv_fun eq')⁻¹ ∘ x) ≈ x,
          from eqretr ▹ eqfin,
        have eqfin'' : (equiv_fun w') ∘ ((equiv_fun w')⁻¹ ∘ x) ≈ x,
          from invs_eq ▹ eqfin',
        eqfin''
      )
      (λ (x : C → A),
        have eqretr : eq' ≈ w',
          from (@retr _ _ (@equiv_path A B) ua_type.inst w'),
        have invs_eq : (equiv_fun eq')⁻¹ ≈ (equiv_fun w')⁻¹,
          from inv_eq eq' w' eqretr,
        have eqfin : (equiv_fun eq')⁻¹ ∘ ((equiv_fun eq') ∘ x) ≈ x,
          from (λ p, path.rec_on p idp) eqinv,
        have eqfin' : (equiv_fun eq')⁻¹ ∘ ((equiv_fun w') ∘ x) ≈ x,
          from eqretr ▹ eqfin,
        have eqfin'' : (equiv_fun w')⁻¹ ∘ ((equiv_fun w') ∘ x) ≈ x,
          from invs_eq ▹ eqfin',
        eqfin''
      )

  -- We are ready to prove functional extensionality,
  -- starting with the naive non-dependent version.
  protected definition diagonal [reducible] (B : Type) : Type
    := Σ xy : B × B, pr₁ xy ≈ pr₂ xy

  protected definition isequiv_src_compose {A B : Type}
      : @IsEquiv (A → diagonal B)
                 (A → B)
                 (compose (pr₁ ∘ dpr1)) :=
    @ua_isequiv_postcompose _ _ _ (pr₁ ∘ dpr1)
        (IsEquiv.adjointify (pr₁ ∘ dpr1)
          (λ x, dpair (x , x) idp) (λx, idp)
          (λ x, sigma.rec_on x
            (λ xy, prod.rec_on xy
              (λ b c p, path.rec_on p idp))))

  protected definition isequiv_tgt_compose {A B : Type}
      : @IsEquiv (A → diagonal B)
                 (A → B)
                 (compose (pr₂ ∘ dpr1)) :=
    @ua_isequiv_postcompose _ _ _ (pr2 ∘ dpr1)
        (IsEquiv.adjointify (pr2 ∘ dpr1)
          (λ x, dpair (x , x) idp) (λx, idp)
          (λ x, sigma.rec_on x
            (λ xy, prod.rec_on xy
              (λ b c p, path.rec_on p idp))))

  theorem ua_implies_funext_nondep {A : Type} {B : Type.{l+1}}
      : Π {f g : A → B}, f ∼ g → f ≈ g :=
    (λ (f g : A → B) (p : f ∼ g),
        let d := λ (x : A), dpair (f x , f x) idp in
        let e := λ (x : A), dpair (f x , g x) (p x) in
        let precomp1 :=  compose (pr₁ ∘ dpr1) in
        have equiv1 [visible] : IsEquiv precomp1,
          from @isequiv_src_compose A B,
        have equiv2 [visible] : Π x y, IsEquiv (ap precomp1),
          from IsEquiv.ap_closed precomp1,
        have H' : Π (x y : A → diagonal B),
            pr₁ ∘ dpr1 ∘ x ≈ pr₁ ∘ dpr1 ∘ y → x ≈ y,
          from (λ x y, IsEquiv.inv (ap precomp1)),
        have eq2 : pr₁ ∘ dpr1 ∘ d ≈ pr₁ ∘ dpr1 ∘ e,
          from idp,
        have eq0 : d ≈ e,
          from H' d e eq2,
        have eq1 : (pr₂ ∘ dpr1) ∘ d ≈ (pr₂ ∘ dpr1) ∘ e,
          from ap _ eq0,
        eq1
    )

end

-- Now we use this to prove weak funext, which as we know
-- implies (with dependent eta) also the strong dependent funext.
universe variables l k
theorem ua_implies_weak_funext [ua3 : ua_type.{k+1}] [ua4 : ua_type.{k+2}] : weak_funext.{l+1 k+1} :=
  (λ (A : Type) (P : A → Type) allcontr,
    let U := (λ (x : A), unit) in
  have pequiv : Π (x : A), P x ≃ U x,
    from (λ x, @equiv_contr_unit(P x) (allcontr x)),
  have psim : Π (x : A), P x ≈ U x,
    from (λ x, @IsEquiv.inv _ _
      equiv_path ua_type.inst (pequiv x)),
  have p : P ≈ U,
    from @ua_implies_funext_nondep _ A Type P U psim,
  have tU' : is_contr (A → unit),
    from is_contr.mk (λ x, ⋆)
      (λ f, @ua_implies_funext_nondep _ A unit (λ x, ⋆) f
        (λ x, unit.rec_on (f x) idp)),
  have tU : is_contr (Π x, U x),
    from tU',
  have tlast : is_contr (Πx, P x),
    from path.transport _ (p⁻¹) tU,
  tlast
)

-- In the following we will proof function extensionality using the univalence axiom
definition ua_implies_funext [instance] [ua ua2 : ua_type] : funext :=
  weak_funext_implies_funext (@ua_implies_weak_funext ua ua2)
