/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.PlaneModel.Basic
public import EllipticCurve.Weierstrass.TranslationPlaces
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # Weierstrass-type plane models

A plane model whose coordinates are an affine-linear change of the Weierstrass coordinates of its
root, `x = (X - r) / α`, `y = (Y - s X - t) / γ` (`PlaneModel.linear`): Montgomery, short
Weierstrass. Its equation is the Weierstrass equation in the new coordinates, `O` is its only
point at infinity (`linear_coords_zero`), every solution is the coordinates of exactly one affine
point (`linear_coords_some`, `linear_exists_coords`), and its group law in coordinates is Mathlib's
chord-and-tangent law carried through the change (`linear_coords_add`, `linear_coords_add_eq_zero`,
`linear_coords_neg`). No identities to check, no rigidity. -/

public section

universe u

open MvPolynomial FunctionField.RationalPlace

namespace PlaneModel

variable {F : Type u} [Field F] (W : WeierstrassCurve.Affine F)

/-- The Weierstrass polynomial `Y² + a₁ X Y + a₃ Y - (X³ + a₂ X² + a₄ X + a₆)`. -/
@[expose] noncomputable def weierstrassPoly : MvPolynomial (Fin 2) F :=
  X 1 ^ 2 + C W.a₁ * X 0 * X 1 + C W.a₃ * X 1 -
    (X 0 ^ 3 + C W.a₂ * X 0 ^ 2 + C W.a₄ * X 0 + C W.a₆)

theorem eval_weierstrassPoly (x y : F) :
    MvPolynomial.eval ![x, y] (weierstrassPoly W) = 0 ↔ W.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff, weierstrassPoly]
  simp only [map_sub, map_add, map_mul, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  exact sub_eq_zero

/-- An affine-linear change of plane coordinates `X = α x + r`, `Y = γ y + s X + t`. -/
structure LinearChange (F : Type u) [Field F] where
  /-- The scaling of the first coordinate. -/
  α : F
  /-- The scaling of the second coordinate. -/
  γ : F
  /-- The translation of the first coordinate. -/
  r : F
  /-- The shear. -/
  s : F
  /-- The translation of the second coordinate. -/
  t : F
  α_ne_zero : α ≠ 0
  γ_ne_zero : γ ≠ 0

namespace LinearChange

variable (L : LinearChange F) {K : Type*} [Field K] [Algebra F K]

/-- The root coordinates `(X, Y)` of model coordinates `p`. -/
@[expose] def toRoot (p : K × K) : K × K :=
  (algebraMap F K L.α * p.1 + algebraMap F K L.r,
    algebraMap F K L.γ * p.2 + algebraMap F K L.s *
      (algebraMap F K L.α * p.1 + algebraMap F K L.r) + algebraMap F K L.t)

/-- The model coordinates of root coordinates `(X, Y)`. -/
@[expose] noncomputable def ofRoot (P : K × K) : K × K :=
  ((P.1 - algebraMap F K L.r) / algebraMap F K L.α,
    (P.2 - algebraMap F K L.s * P.1 - algebraMap F K L.t) / algebraMap F K L.γ)

theorem toRoot_ofRoot (P : K × K) : L.toRoot (L.ofRoot P) = P := by
  have hα : algebraMap F K L.α ≠ 0 := (map_ne_zero _).mpr L.α_ne_zero
  have hγ : algebraMap F K L.γ ≠ 0 := (map_ne_zero _).mpr L.γ_ne_zero
  ext <;> simp only [toRoot, ofRoot] <;> field_simp <;> ring

theorem ofRoot_toRoot (p : K × K) : L.ofRoot (L.toRoot p) = p := by
  have hα : algebraMap F K L.α ≠ 0 := (map_ne_zero _).mpr L.α_ne_zero
  have hγ : algebraMap F K L.γ ≠ 0 := (map_ne_zero _).mpr L.γ_ne_zero
  ext <;> simp only [toRoot, ofRoot] <;> field_simp <;> ring

/-- The polynomials `X = α x + r`, `Y = γ y + s X + t`. -/
@[expose] noncomputable def polys : Fin 2 → MvPolynomial (Fin 2) F :=
  ![C L.α * X 0 + C L.r, C L.γ * X 1 + C L.s * (C L.α * X 0 + C L.r) + C L.t]

theorem aeval_polys (p : K × K) (i : Fin 2) :
    aeval ![p.1, p.2] (L.polys i) = ![(L.toRoot p).1, (L.toRoot p).2] i := by
  fin_cases i <;> simp [polys, toRoot]

end LinearChange

variable (L : LinearChange F)

/-- **The Weierstrass-type model** with coordinates `x = (X - r) / α`, `y = (Y - s X - t) / γ`. -/
noncomputable def linear : PlaneModel W where
  x := (L.ofRoot (W.fieldX, W.fieldY)).1
  y := (L.ofRoot (W.fieldX, W.fieldY)).2
  G := aeval L.polys (weierstrassPoly W)
  aeval_G := by
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    have e : (fun i => aeval ![(L.ofRoot (W.fieldX, W.fieldY)).1,
        (L.ofRoot (W.fieldX, W.fieldY)).2] (L.polys i)) = ![W.fieldX, W.fieldY] := by
      funext i
      rw [L.aeval_polys, L.toRoot_ofRoot]
    rw [e, weierstrassPoly]
    simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    exact sub_eq_zero.mpr W.fieldY_equation
  adjoin_eq_top := by
    set S := IntermediateField.adjoin F
      {(L.ofRoot (W.fieldX, W.fieldY)).1, (L.ofRoot (W.fieldX, W.fieldY)).2}
    have h₁ : (L.ofRoot (W.fieldX, W.fieldY)).1 ∈ S := IntermediateField.subset_adjoin _ _ (by simp)
    have h₂ : (L.ofRoot (W.fieldX, W.fieldY)).2 ∈ S := IntermediateField.subset_adjoin _ _ (by simp)
    have e := L.toRoot_ofRoot (W.fieldX, W.fieldY)
    have c := fun a : F => S.algebraMap_mem a
    have e₁ := congrArg Prod.fst e
    have e₂ := congrArg Prod.snd e
    simp only [LinearChange.toRoot] at e₁ e₂
    have hX : W.fieldX ∈ S := by
      rw [← e₁]
      exact add_mem (mul_mem (c _) h₁) (c _)
    have hY : W.fieldY ∈ S := by
      rw [← e₂]
      exact add_mem (add_mem (mul_mem (c _) h₂)
        (mul_mem (c _) (add_mem (mul_mem (c _) h₁) (c _)))) (c _)
    exact adjoin_eq_top_of_mem hX hY

variable {W L}

theorem linear_x : (linear W L).x = (L.ofRoot (W.fieldX, W.fieldY)).1 := by
  unfold linear; rfl

theorem linear_y : (linear W L).y = (L.ofRoot (W.fieldX, W.fieldY)).2 := by
  unfold linear; rfl

theorem linear_G : (linear W L).G = aeval L.polys (weierstrassPoly W) := by
  unfold linear; rfl

/-- The equation of the model at `p` is the Weierstrass equation at the root coordinates. -/
theorem eval_linear_G (p : F × F) :
    MvPolynomial.eval ![p.1, p.2] (linear W L).G = 0 ↔
      W.Equation (L.toRoot p).1 (L.toRoot p).2 := by
  rw [linear_G, ← eval_weierstrassPoly, ← MvPolynomial.coe_aeval_eq_eval,
    ← MvPolynomial.coe_aeval_eq_eval, RingHom.coe_coe, RingHom.coe_coe, ← AlgHom.comp_apply,
    MvPolynomial.comp_aeval]
  have e : (fun i => aeval ![p.1, p.2] (L.polys i)) = ![(L.toRoot p).1, (L.toRoot p).2] := by
    funext i; rw [L.aeval_polys]
  rw [e]

variable [W.IsElliptic]

/-- `O` is the only point at infinity: it has no coordinates. -/
theorem linear_coords_zero : (linear W L).coords 0 = none := by
  rcases hc : (linear W L).coords 0 with _ | ⟨p₁, p₂⟩
  · rfl
  exfalso
  have hx := ((linear W L).hasValue_of_coords hc).1.mem
  rw [linear_x] at hx
  apply W.fieldX_not_mem_pointEquivRationalPlace_zero
  have e := congrArg Prod.fst (L.toRoot_ofRoot (W.fieldX, W.fieldY))
  simp only [LinearChange.toRoot] at e
  rw [← e]
  have c := fun a : F => (W.pointEquivRationalPlace 0).1.algebraMap_mem a
  exact add_mem (mul_mem (c _) hx) (c _)

/-- The coordinates of an affine point. -/
theorem linear_coords_some {X₀ Y₀ : F} (h : W.Nonsingular X₀ Y₀) :
    (linear W L).coords (.some X₀ Y₀ h) = some (L.ofRoot (X₀, Y₀)) := by
  have hX := WeierstrassCurve.Affine.hasValue_fieldX_some h
  have hY := WeierstrassCurve.Affine.hasValue_fieldY_some h
  have c := fun a : F => hasValue_algebraMap (P := W.pointEquivRationalPlace (.some X₀ Y₀ h)) a
  apply coords_eq_of_hasValue
  · exact ((hX.sub (c _)).div (c _) L.α_ne_zero).congr rfl (by simp)
  · exact ((((hY.sub ((c _).mul hX)).sub (c _)).div (c _) L.γ_ne_zero)).congr rfl
      (by simp)

/-- Every solution of the model is the coordinates of an affine point. -/
theorem linear_exists_coords {p : F × F} (hp : MvPolynomial.eval ![p.1, p.2] (linear W L).G = 0) :
    ∃ h, (linear W L).coords (.some (L.toRoot p).1 (L.toRoot p).2 h) = some p := by
  have h := WeierstrassCurve.Affine.equation_iff_nonsingular.mp ((eval_linear_G p).mp hp)
  exact ⟨h, by rw [linear_coords_some]; simp [L.ofRoot_toRoot]⟩

/-- Points with coordinates are affine, with the root coordinates of their coordinates. -/
theorem linear_eq_some {P : W.Point} {p : F × F} (hP : (linear W L).coords P = some p) :
    ∃ h, P = .some (L.toRoot p).1 (L.toRoot p).2 h := by
  cases P with
  | zero => rw [show (WeierstrassCurve.Affine.Point.zero : W.Point) = 0 from rfl,
      linear_coords_zero] at hP; cases hP
  | some X₀ Y₀ h =>
    rw [linear_coords_some, Option.some_inj] at hP
    subst hP
    rw [L.toRoot_ofRoot]
    exact ⟨h, rfl⟩

open Classical in
/-- **The group law in coordinates**: off `P + Q = O`, the coordinates of `P + Q` are given by
Mathlib's chord-and-tangent formulas in the root coordinates `(X₁, Y₁)`, `(X₂, Y₂)` of `p`, `q`. -/
theorem linear_coords_add {P Q : W.Point} {p q : F × F} (hP : (linear W L).coords P = some p)
    (hQ : (linear W L).coords Q = some q)
    (hne : ¬((L.toRoot p).1 = (L.toRoot q).1 ∧
      (L.toRoot p).2 = W.negY (L.toRoot q).1 (L.toRoot q).2)) :
    (linear W L).coords (P + Q) = some (L.ofRoot
      (W.addX (L.toRoot p).1 (L.toRoot q).1
          (W.slope (L.toRoot p).1 (L.toRoot q).1 (L.toRoot p).2 (L.toRoot q).2),
        W.addY (L.toRoot p).1 (L.toRoot q).1 (L.toRoot p).2
          (W.slope (L.toRoot p).1 (L.toRoot q).1 (L.toRoot p).2 (L.toRoot q).2))) := by
  obtain ⟨h₁, rfl⟩ := linear_eq_some hP
  obtain ⟨h₂, rfl⟩ := linear_eq_some hQ
  rw [WeierstrassCurve.Affine.Point.add_some hne, linear_coords_some]

open Classical in
/-- The sum is `O` exactly in the excluded case of `linear_coords_add`. -/
theorem linear_add_eq_zero {P Q : W.Point} {p q : F × F} (hP : (linear W L).coords P = some p)
    (hQ : (linear W L).coords Q = some q)
    (h : (L.toRoot p).1 = (L.toRoot q).1 ∧
      (L.toRoot p).2 = W.negY (L.toRoot q).1 (L.toRoot q).2) : P + Q = 0 := by
  obtain ⟨h₁, rfl⟩ := linear_eq_some hP
  obtain ⟨h₂, rfl⟩ := linear_eq_some hQ
  exact WeierstrassCurve.Affine.Point.add_of_Y_eq h.1 h.2

open Classical in
/-- Negation in coordinates. -/
theorem linear_coords_neg {P : W.Point} {p : F × F} (hP : (linear W L).coords P = some p) :
    (linear W L).coords (-P) =
      some (L.ofRoot ((L.toRoot p).1, W.negY (L.toRoot p).1 (L.toRoot p).2)) := by
  obtain ⟨h₁, rfl⟩ := linear_eq_some hP
  rw [WeierstrassCurve.Affine.Point.neg_some, linear_coords_some]

end PlaneModel
