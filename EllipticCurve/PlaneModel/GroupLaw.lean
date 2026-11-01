/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.PlaneModel.Translation
public import EllipticCurve.Weierstrass.Rigidity
public import EllipticCurve.Weierstrass.AutConstants
public import EllipticCurve.Weierstrass.Generic
import EllipticCurve.FunctionField.Constants

/-! # Addition formulas are the group law, by rigidity

Let `W` be an elliptic curve over `F`, away from `6`, with function field `K = F(W)`, and let `ξ`
be the generic point of `W` over `K`. An automorphism `σ_Q` of the function field of `W` over `K`
that maps `O` to `Q` and satisfies `σ_Q(ξ) = σ_ξ(Q)` for an automorphism `σ_ξ` mapping `O` to `ξ`
acts on points as the translation by `Q` (`pointMapOfAlgEquiv_eq_add_bcPoint`): by rigidity both
act as `ψ + Q` and `ψ_ξ + ξ` with changes of variables `ψ`, `ψ_ξ`; these are defined over `F`
(exact constants), so `ψ(ξ) - ξ` is a point over `F`, which must be `O` since `x(ξ + P₀)` has a
pole at `-P₀`; then `ψ` fixes `ξ`, hence is the identity.

For plane models this gives the group law from a formula (`coords_add_of_rigidity`): if the
substitutions `σ_q`, `σ_ξ` given by a formula `f` move points by `f`, `f` is symmetric at
`(ξ, Q)` and has `O` as a neutral element, then `coords (P + Q) = f(coords P, coords Q)`.

With the translations built from the identities of the formula (`PlaneModel.Translation`), this
gives **the group law from identities** (`coords_add_of_isAddFormula`): a model whose formula
satisfies the curve equation, the inverse identity, symmetry and neutrality, with irreducible
equation, denominators nonzero on solutions and all solutions nonsingular, has the formula as its
group law. -/

public section

universe u

open FunctionField.RationalPlace
open WeierstrassCurve.Affine

namespace PlaneModel

variable {F : Type u} [Field F] {W : WeierstrassCurve.Affine F} [W.IsElliptic]
  {W' : WeierstrassCurve.Affine W.FunctionField} (hW : W.baseChange W.FunctionField = W')

/-! ### Base change of points to the function field -/

section BaseChange

open Classical in
/-- Points of `W` as points of `W'`, the base change of `W` to its function field. -/
noncomputable def bcPoint : W.Point →+ W'.Point :=
  (Point.equivOfEq hW).toAddMonoidHom.comp
    ((Point.map (W' := W) (Algebra.ofId F W.FunctionField)).comp W.toBaseChange.toAddMonoidHom)

/-- The generic point of `W`, as a point of `W'`. -/
noncomputable def genericPt : W'.Point :=
  Point.equivOfEq hW W.genericPoint

omit [W.IsElliptic] in
open Classical in
/-- The base change of points preserves the origin. -/
theorem bcPoint_zero : bcPoint hW 0 = 0 := _root_.map_zero _

omit [W.IsElliptic] in
open Classical in
/-- The base change of an affine point. -/
theorem bcPoint_some {x y : F} (h : W.Nonsingular x y) :
    ∃ h', bcPoint hW (.some x y h) =
      .some (Algebra.ofId F W.FunctionField x) (Algebra.ofId F W.FunctionField y) h' := by
  obtain ⟨h₁, e₁⟩ := W.toBaseChange_some h
  simp only [bcPoint, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    e₁, Point.map_some]
  exact ⟨hW ▸ (W.baseChange_nonsingular (Algebra.ofId F W.FunctionField).injective x y).mpr h₁,
    Point.equivOfEq_some hW _⟩

omit [W.IsElliptic] in
open Classical in
/-- A point of `W'` with constant coordinates comes from a point of `W`. -/
theorem exists_bcPoint_eq {x y : F}
    (h : W'.Nonsingular (algebraMap F W.FunctionField x) (algebraMap F _ y)) :
    ∃ P : W.Point, bcPoint hW P = .some _ _ h := by
  have h' : (W.baseChange W.FunctionField).Nonsingular
      (Algebra.ofId F _ x) (Algebra.ofId F _ y) := hW.symm ▸ h
  have h₀ := (W.baseChange_nonsingular (Algebra.ofId F W.FunctionField).injective x y).mp h'
  rw [W.baseChange_self] at h₀
  obtain ⟨_, e⟩ := bcPoint_some hW h₀
  exact ⟨_, e⟩

/-- The generic point has coordinates `(x, y)`. -/
theorem genericPt_eq :
    genericPt hW = .some W.fieldX W.fieldY (hW ▸ W.nonsingular_genericPoint) := by
  rw [genericPt, genericPoint_def]
  exact Point.equivOfEq_some _ _

end BaseChange

/-! ### Rigidity -/

set_option quotPrecheck false in
/-- The function field of `W`. -/
local notation "𝕂" => WeierstrassCurve.Affine.FunctionField W
/-- The constant embedding. -/
local notation "ι" => algebraMap F 𝕂

variable [W'.IsElliptic]

open Classical in
/-- **An automorphism commuting with the generic translation is a translation.** Away from `6`,
if `σ_Q` and `σ_ξ` are automorphisms of the function field of `W'` over `K = F(W)` with
`σ_Q(O) = Q`, `σ_ξ(O) = ξ` and `σ_Q(ξ) = σ_ξ(Q)` (on points), then `σ_Q` acts as `R ↦ R + Q`. -/
theorem pointMapOfAlgEquiv_eq_add_bcPoint [NeZero (6 : F)] {Q : W.Point}
    (eQ eX : W'.FunctionField ≃ₐ[𝕂] W'.FunctionField)
    (h0Q : pointMapOfAlgEquiv eQ 0 = bcPoint hW Q) (h0X : pointMapOfAlgEquiv eX 0 = genericPt hW)
    (hsym : pointMapOfAlgEquiv eQ (genericPt hW) = pointMapOfAlgEquiv eX (bcPoint hW Q))
    (R : W'.Point) : pointMapOfAlgEquiv eQ R = R + bcPoint hW Q := by
  have : NeZero (2 : 𝕂) := ⟨by
    have h2 : (2 : F) ≠ 0 := fun h => NeZero.ne (6 : F) (by linear_combination 3 * h)
    rw [← map_ofNat ι 2]; exact (map_ne_zero ι).mpr h2⟩
  have hconst : ∀ z : 𝕂, IsAlgebraic F z → ∃ c : F, z = ι c := fun _ hz =>
    FunctionField.RationalPlace.exists_eq_algebraMap_of_isAlgebraic (W.pointEquivRationalPlace 0) hz
  set ξ := genericPt hW
  obtain ⟨C, hC, hψ⟩ := exists_pointMapOfAlgEquiv_eq_add eQ
  obtain ⟨Cξ, hCξ, hψξ⟩ := exists_pointMapOfAlgEquiv_eq_add eX
  -- `ψ_ξ` is defined over `F`, so `ψ_ξ(Q) = Q₁` is a point over `F`
  have hCξ' : Cξ • W.baseChange 𝕂 = W.baseChange 𝕂 := by rw [hW]; exact hCξ
  obtain ⟨u₀, r₀, s₀, t₀, hu₀, hr₀, hs₀, ht₀⟩ :=
    WeierstrassCurve.exists_eq_algebraMap_of_smul_baseChange_eq W hconst Cξ hCξ'
  have hconstQ : ∃ Q₁ : W.Point, pointMapOfAlgEquiv eX (bcPoint hW Q) = bcPoint hW Q₁ + ξ := by
    rw [hψξ, h0X]
    simp only [add_left_inj]
    cases Q with
    | zero =>
      refine ⟨0, ?_⟩
      rw [show (Point.zero : W.Point) = 0 from rfl, bcPoint_zero, _root_.map_zero,
        _root_.map_zero]
    | some xQ yQ hQ' =>
      obtain ⟨h₁, e₁⟩ := bcPoint_some hW hQ'
      rw [e₁, Point.equivOfEq_some, Point.equivVariableChange_some]
      have hX : (Cξ.u : 𝕂) ^ 2 * Algebra.ofId F 𝕂 xQ + Cξ.r = ι (u₀ ^ 2 * xQ + r₀) := by
        rw [hu₀, hr₀]; simp only [map_add, map_mul, map_pow]; rfl
      have hY : (Cξ.u : 𝕂) ^ 3 * Algebra.ofId F 𝕂 yQ +
          (Cξ.u : 𝕂) ^ 2 * Cξ.s * Algebra.ofId F 𝕂 xQ + Cξ.t =
            ι (u₀ ^ 3 * yQ + u₀ ^ 2 * s₀ * xQ + t₀) := by
        rw [hu₀, hs₀, ht₀]; simp only [map_add, map_mul, map_pow]; rfl
      suffices H : ∀ {x y : 𝕂} (h : W'.Nonsingular x y), x = ι (u₀ ^ 2 * xQ + r₀) →
          y = ι (u₀ ^ 3 * yQ + u₀ ^ 2 * s₀ * xQ + t₀) → ∃ Q₁, Point.some x y h = bcPoint hW Q₁ from
        H _ hX hY
      rintro x y h rfl rfl
      obtain ⟨Q₁, e₃⟩ := exists_bcPoint_eq hW h
      exact ⟨Q₁, e₃.symm⟩
  obtain ⟨Q₁, hQ₁⟩ := hconstQ
  set P₀ := Q₁ - Q
  -- `ψ` is defined over `F` too
  have hC' : C • W.baseChange 𝕂 = W.baseChange 𝕂 := by rw [hW]; exact hC
  obtain ⟨u₁, r₁, s₁, t₁, hu₁, hr₁, hs₁, ht₁⟩ :=
    WeierstrassCurve.exists_eq_algebraMap_of_smul_baseChange_eq W hconst C hC'
  have hξdef : ξ = _ := genericPt_eq hW
  obtain ⟨hn, hψξdef⟩ : ∃ hn, pointMapOfAlgEquiv eQ ξ =
      Point.some ((C.u : 𝕂) ^ 2 * W.fieldX + C.r)
        ((C.u : 𝕂) ^ 3 * W.fieldY + (C.u : 𝕂) ^ 2 * C.s * W.fieldX + C.t) hn + bcPoint hW Q := by
    rw [hψ, h0Q, hξdef, Point.equivOfEq_some, Point.equivVariableChange_some]
    exact ⟨_, rfl⟩
  have hξP₀ : Point.some _ _ hn = ξ + bcPoint hW P₀ := by
    have h := hsym.trans hQ₁
    rw [hψξdef] at h
    rw [eq_sub_of_add_eq h, _root_.map_sub]
    abel
  -- `P₀ = 0`: otherwise `x(ξ + P₀)` would have a pole at `-P₀`
  have hP₀ : P₀ = 0 := by
    by_contra hne
    obtain ⟨h₁, e₁⟩ := genericPoint_add_eq (W := W) (W.toBaseChange P₀)
    have hbc : ξ + bcPoint hW P₀ = Point.equivOfEq hW (.some _ _ h₁) := by
      rw [← e₁, _root_.map_add]
      rfl
    rw [hbc, Point.equivOfEq_some, Point.some.injEq] at hξP₀
    rcases hm : -P₀ with _ | ⟨x₀, y₀, h₀⟩
    · exact hne (neg_eq_zero.mp hm)
    apply transX_not_mem P₀
    rw [hm, ← hξP₀.1, hu₁, hr₁]
    obtain ⟨hx, -, -, -⟩ := W.pointEquivRationalPlace_some x₀ y₀ h₀
    have hc := (W.pointEquivRationalPlace (.some x₀ y₀ h₀)).1.algebraMap_mem
    exact add_mem (mul_mem (pow_mem (hc u₁) 2) hx) (hc r₁)
  -- so `ψ` fixes `ξ`, hence is the identity
  rw [hP₀, bcPoint_zero, add_zero, hξdef, Point.some.injEq] at hξP₀
  rw [hu₁, hr₁, hs₁, ht₁] at hξP₀
  obtain ⟨rfl, rfl, rfl, rfl⟩ := eq_one_of_fix_generic hξP₀.1 hξP₀.2
  rw [hψ, h0Q, add_left_inj]
  rcases R with _ | ⟨x, y, h⟩
  · rw [show (Point.zero : W'.Point) = 0 from rfl, _root_.map_zero, _root_.map_zero]
  · rw [Point.equivOfEq_some, Point.equivVariableChange_some, Point.some.injEq, hu₁, hr₁,
      hs₁, ht₁]
    simp

/-! ### Addition formulas -/

open Classical in
/-- **A formula realised by translations is the group law.** Let `M` be a plane model of `W`
over `F` in which every point has coordinates, `M'` a plane model of the base change `W'` to
`K = F(W)` whose coordinates are injective and extend those of `M`, and `fF`, `fK` a formula over
`F` and over `K` compatible with `F → K`. Away from `6`, if there are automorphisms `σ_q`, `σ_ξ`
over `K` moving points by `f(·, q)` and `f(·, g)` (`g` the coordinates of the generic point),
the coordinates `o` of `O` are neutral, and `f(g, q) = f(q, g)`, then
`coords (P + Q) = f(coords P, coords Q)`. -/
theorem coords_add_of_rigidity [NeZero (6 : F)] {M : PlaneModel W} {M' : PlaneModel W'}
    {fF : F × F → F × F → F × F} {fK : 𝕂 × 𝕂 → 𝕂 × 𝕂 → 𝕂 × 𝕂}
    (hf : ∀ p q, fK (Prod.map ι ι p) (Prod.map ι ι q) = Prod.map ι ι (fF p q))
    (hcomplete : ∀ R : W.Point, ∃ r, M.coords R = some r)
    (hinj : ∀ {R S : W'.Point} {r}, M'.coords R = some r → M'.coords S = some r → R = S)
    (hbc : ∀ {R : W.Point} {r}, M.coords R = some r →
      M'.coords (bcPoint hW R) = some (Prod.map ι ι r))
    {o g : 𝕂 × 𝕂} (ho : M'.coords 0 = some o) (hg : M'.coords (genericPt hW) = some g)
    {P Q : W.Point} {p q : F × F} (hP : M.coords P = some p) (hQ : M.coords Q = some q)
    (eQ eX : W'.FunctionField ≃ₐ[𝕂] W'.FunctionField)
    (hcQ : ∀ {R : W'.Point} {r}, M'.coords R = some r →
      M'.coords (pointMapOfAlgEquiv eQ R) = some (fK r (Prod.map ι ι q)))
    (hcX : ∀ {R : W'.Point} {r}, M'.coords R = some r →
      M'.coords (pointMapOfAlgEquiv eX R) = some (fK r g))
    (hoQ : fK o (Prod.map ι ι q) = Prod.map ι ι q) (hoX : fK o g = g)
    (hsym : fK g (Prod.map ι ι q) = fK (Prod.map ι ι q) g) :
    M.coords (P + Q) = some (fF p q) := by
  have h0Q : pointMapOfAlgEquiv eQ 0 = bcPoint hW Q :=
    hinj ((hcQ ho).trans (by rw [hoQ])) (hbc hQ)
  have h0X : pointMapOfAlgEquiv eX 0 = genericPt hW := hinj ((hcX ho).trans (by rw [hoX])) hg
  have hs : pointMapOfAlgEquiv eQ (genericPt hW) = pointMapOfAlgEquiv eX (bcPoint hW Q) :=
    hinj (hcQ hg) ((hcX (hbc hQ)).trans (by rw [hsym]))
  have hpm := pointMapOfAlgEquiv_eq_add_bcPoint hW eQ eX h0Q h0X hs (bcPoint hW P)
  rw [← _root_.map_add] at hpm
  have hc₁ := hcQ (hbc hP)
  obtain ⟨r, hr⟩ := hcomplete (P + Q)
  rw [hpm, hbc hr, Option.some_inj, hf] at hc₁
  rw [hr, Option.some_inj]
  exact Prod.ext ((algebraMap F 𝕂).injective (congrArg Prod.fst hc₁))
    ((algebraMap F 𝕂).injective (congrArg Prod.snd hc₁))

open Classical in
/-- **The group law from identities.** Let `M` be a plane model of `W` over `F` in which every
point has coordinates, and `M'` a plane model of the base change `W'` to `K = F(W)`, whose
coordinates extend those of `M`, with all solutions nonsingular and `O` at `o`. Let `f` be a
formula over `F` whose image over `K` satisfies the identities of an addition law on `M'`
(`IsAddFormula`), is symmetric, and has `o` as a neutral element. Then, away from `6`,
`coords (P + Q) = f(coords P, coords Q)`. -/
theorem coords_add_of_isAddFormula [NeZero (6 : F)] {M : PlaneModel W} {M' : PlaneModel W'}
    {f : Formula F} {neg : 𝕂 × 𝕂 → 𝕂 × 𝕂} (hf : M'.IsAddFormula (f.map ι) neg)
    (hcomplete : ∀ R : W.Point, ∃ r, M.coords R = some r)
    (hns : ∀ u : 𝕂 × 𝕂, MvPolynomial.eval ![u.1, u.2] M'.G = 0 → M'.Nonsingular u.1 u.2)
    (hbc : ∀ {R : W.Point} {r}, M.coords R = some r →
      M'.coords (bcPoint hW R) = some (Prod.map ι ι r))
    {o g : 𝕂 × 𝕂} (ho : M'.coords 0 = some o) (hg : M'.coords (genericPt hW) = some g)
    (hneutral : ∀ u : 𝕂 × 𝕂, MvPolynomial.eval ![u.1, u.2] M'.G = 0 → (f.map ι).eval o u = u)
    (hsym : ∀ u v : 𝕂 × 𝕂, MvPolynomial.eval ![u.1, u.2] M'.G = 0 →
      MvPolynomial.eval ![v.1, v.2] M'.G = 0 → (f.map ι).eval u v = (f.map ι).eval v u)
    {P Q : W.Point} {p q : F × F} (hP : M.coords P = some p) (hQ : M.coords Q = some q) :
    M.coords (P + Q) = some (f.eval p q) := by
  have hq : MvPolynomial.eval ![(Prod.map ι ι q).1, (Prod.map ι ι q).2] M'.G = 0 :=
    M'.coords_equation (a := (Prod.map ι ι q).1) (b := (Prod.map ι ι q).2) (hbc hQ)
  have hgG : MvPolynomial.eval ![g.1, g.2] M'.G = 0 :=
    M'.coords_equation (a := g.1) (b := g.2) hg
  refine coords_add_of_rigidity hW (fF := f.eval) (fK := (f.map ι).eval)
    (fun p q => f.map_eval_algebraMap p q) hcomplete
    (fun {R S r} hR hS => M'.coords_injective (a := r.1) (b := r.2)
      (hns r (M'.coords_equation (a := r.1) (b := r.2) hR)) hR hS)
    hbc ho hg hP hQ (hf.translation ho (r := Prod.map ι ι q) hq) (hf.translation ho (r := g) hgG)
    (fun {R r} hR => hf.coords_pointMap_translation ho (r := Prod.map ι ι q) hq (p := r) hR)
    (fun {R r} hR => hf.coords_pointMap_translation ho (r := g) hgG (p := r) hR)
    (hneutral _ hq) (hneutral _ hgG) (hsym _ _ hgG hq)

end PlaneModel
