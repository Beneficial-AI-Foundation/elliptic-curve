/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Curve.Twist
public import EllipticCurve.Montgomery.Defs
public import Mathlib.Algebra.Group.Even
import all EllipticCurve.Montgomery.Defs
import EllipticCurve.Curve.Impl
import EllipticCurve.Curve.Realization
import Mathlib.Algebra.Ring.Parity
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Montgomery models: characterising lemmas

The characterising statements about `MontgomeryModel`: the defining equation of `twist`, the
coordinates `u`, `v`, the group law on `M.Point` in Montgomery coordinates (`zero_def`,
`neg_some`, the chord-and-tangent formulas `some_add_some_of_u_ne`, `some_add_some_of_v_ne`,
`some_add_some_eq_zero`), `pointEquiv_zero`, the identities of the 2-descent map `Q ↦ B u(Q)`
modulo squares (`u_mul_u_mul_u_add_of_u_ne`, `B_mul_u_two_nsmul_mul_sq`, `isSquare_B_mul_u_add`,
`isSquare_B_mul_u_two_nsmul`), the x-only differential-addition identity
(`u_add_mul_u_sub_of_u_ne`), and the equality of curves of two models with the
same `A` whose `B`s differ by a square factor (`toCurve_eq_of_B_eq_mul_sq`). These lemmas are
the whole interface to the hidden constructions of `EllipticCurve.Montgomery.Defs`: importers
never see the bodies, and a different construction of the group would only change the proofs
here. -/

public section

universe u

namespace MontgomeryModel

variable {F : Type u} [Field F] {M : MontgomeryModel F}

/-! ### The equation and the twist -/

/-- The equation in terms of `rhs`. -/
theorem equation_iff_rhs {u v : F} : M.Equation u v ↔ M.B * v ^ 2 = M.rhs u :=
  Iff.rfl

/-- If `(u, v)` is on the model then so is `(u, -v)`. -/
theorem equation_neg {u v : F} (h : M.Equation u v) : M.Equation u (-v) := by
  unfold Equation at h ⊢
  rwa [neg_sq]

/-- `(0, 0)` is on every model. -/
theorem equation_zero_zero (M : MontgomeryModel F) : M.Equation 0 0 := by
  unfold Equation
  ring

/-- On a model with `B ≠ 0`, `u = 0` forces `v = 0`. -/
theorem v_eq_zero_of_u_eq_zero (hB : M.B ≠ 0) {u v : F} (h : M.Equation u v) (hu : u = 0) :
    v = 0 := by
  subst hu
  unfold Equation at h
  have key : M.B * v ^ 2 = 0 := by linear_combination h
  exact (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp key).resolve_left hB)

/-- The defining equation of `twist`. -/
theorem twist_def (M : MontgomeryModel F) (c : F) : M.twist c = ⟨M.A, M.B * c⟩ := by
  rfl

/-- The twist keeps `A`. -/
@[simp]
theorem twist_A (M : MontgomeryModel F) (c : F) : (M.twist c).A = M.A := by
  rw [twist_def]

/-- The twist scales `B` by `c`. -/
@[simp]
theorem twist_B (M : MontgomeryModel F) (c : F) : (M.twist c).B = M.B * c := by
  rw [twist_def]

/-- The twist has the same right-hand side `rhs`. -/
@[simp]
theorem twist_rhs (M : MontgomeryModel F) (c u : F) : (M.twist c).rhs u = M.rhs u := by
  simp only [rhs, twist_A]

/-! ### Coordinates -/

/-- The `u`-coordinate of an affine point. -/
@[simp]
theorem u_some {u v : F} (h : M.Equation u v) : (Point.some u v h).u = u := by
  rfl

/-- The `v`-coordinate of an affine point. -/
@[simp]
theorem v_some {u v : F} (h : M.Equation u v) : (Point.some u v h).v = v := by
  rfl

/-! The chord-and-tangent formulas. The Weierstrass coordinates of the sum, in terms of the
Weierstrass slope, are `B` and `B²` times our `addU` and `addV` in terms of our slope. -/

private theorem addX_eq (u₁ u₂ ℓ : F) :
    M.toWeierstrass.addX (M.B * u₁) (M.B * u₂) (M.B * ℓ) = M.B * M.addU u₁ u₂ ℓ := by
  simp only [WeierstrassCurve.Affine.addX, toWeierstrass, addU]
  ring

private theorem addY_eq (u₁ u₂ v₁ ℓ : F) :
    M.toWeierstrass.addY (M.B * u₁) (M.B * u₂) (M.B ^ 2 * v₁) (M.B * ℓ) =
      M.B ^ 2 * M.addV u₁ u₂ v₁ ℓ := by
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX, toWeierstrass, addV, addU]
  ring

/-! ### The group law

Everything below assumes `M.IsNonsingular`, which is what gives `M.Point` its group structure. -/

variable [M.IsNonsingular]

/-- The zero of the group is the point at infinity. -/
theorem zero_def : (0 : M.Point) = .zero := by
  rw [zero_eq]
  rfl

/-- The `u`-coordinate of the point at infinity is `0`, by convention. -/
@[simp]
theorem u_zero : (0 : M.Point).u = 0 := by
  rw [zero_def]
  rfl

/-- The `v`-coordinate of the point at infinity is `0`, by convention. -/
@[simp]
theorem v_zero : (0 : M.Point).v = 0 := by
  rw [zero_def]
  rfl

/-- Every point is `0` or an affine point `some u v h`. -/
theorem Point.cases (P : M.Point) : P = 0 ∨ ∃ u v h, P = Point.some u v h := by
  cases P with
  | zero => exact Or.inl zero_def.symm
  | some u v h => exact Or.inr ⟨u, v, h, rfl⟩

/-- Affine points are not the point at infinity. -/
theorem some_ne_zero {u v : F} (h : M.Equation u v) : Point.some u v h ≠ 0 := by
  rw [zero_def]
  exact nofun

/-- Negation flips the sign of `v`. -/
@[simp]
theorem neg_some {u v : F} (h : M.Equation u v) :
    -Point.some u v h = Point.some u (-v) (equation_neg h) := by
  have hB : M.B ≠ 0 := IsNonsingular.B_ne_zero
  rw [neg_eq, pointEquivWeierstrass_some, WeierstrassCurve.Affine.Point.neg_some,
    pointEquivWeierstrass_symm_some, Point.some.injEq]
  simp only [WeierstrassCurve.Affine.negY, toWeierstrass, zero_mul, sub_zero]
  refine ⟨mul_div_cancel_left₀ u hB, ?_⟩
  rw [div_eq_iff (pow_ne_zero 2 hB)]
  ring

/-- Negation preserves the `u`-coordinate. -/
@[simp]
theorem u_neg (P : M.Point) : (-P).u = P.u := by
  rcases Point.cases P with rfl | ⟨u, v, h, rfl⟩
  · rw [neg_zero]
  · rw [neg_some, u_some, u_some]

/-- Negation negates the `v`-coordinate. -/
@[simp]
theorem v_neg (P : M.Point) : (-P).v = -P.v := by
  rcases Point.cases P with rfl | ⟨u, v, h, rfl⟩
  · rw [neg_zero, v_zero, neg_zero]
  · rw [neg_some, v_some, v_some]

open scoped Classical in
private theorem slope_eq_of_u_ne {u₁ v₁ u₂ v₂ : F} (hu : u₁ ≠ u₂) :
    M.toWeierstrass.slope (M.B * u₁) (M.B * u₂) (M.B ^ 2 * v₁) (M.B ^ 2 * v₂) =
      M.B * chordSlope u₁ v₁ u₂ v₂ := by
  classical
  have hB : M.B ≠ 0 := IsNonsingular.B_ne_zero
  have hu' : M.B * u₁ ≠ M.B * u₂ := fun h => hu (mul_left_cancel₀ hB h)
  rw [WeierstrassCurve.Affine.slope_of_X_ne hu', chordSlope]
  have h₁ : u₁ - u₂ ≠ 0 := sub_ne_zero.mpr hu
  have h₂ : u₂ - u₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  field_simp
  ring

open scoped Classical in
private theorem slope_eq_of_v_ne {u₁ v₁ u₂ v₂ : F} (hu : u₁ = u₂) (hv : v₁ ≠ -v₂) :
    M.toWeierstrass.slope (M.B * u₁) (M.B * u₂) (M.B ^ 2 * v₁) (M.B ^ 2 * v₂) =
      M.B * M.tangentSlope u₁ v₁ := by
  classical
  have hB : M.B ≠ 0 := IsNonsingular.B_ne_zero
  have hv' : M.B ^ 2 * v₁ ≠ M.toWeierstrass.negY (M.B * u₂) (M.B ^ 2 * v₂) := by
    simp only [WeierstrassCurve.Affine.negY, toWeierstrass, zero_mul, sub_zero]
    intro h
    exact hv (mul_left_cancel₀ (pow_ne_zero 2 hB) (by rw [h]; ring))
  rw [WeierstrassCurve.Affine.slope_of_Y_ne (by rw [hu]) hv', tangentSlope]
  simp only [WeierstrassCurve.Affine.negY, toWeierstrass, zero_mul, sub_zero]
  by_cases hv₁ : v₁ = 0
  · simp [hv₁]
  · field_simp
    ring

open scoped Classical in
/-- The equation at the sum of two affine points that are not inverse to each other, given the
Weierstrass slope as `B` times a Montgomery slope `ℓ`. -/
private theorem equation_add_of_slope {u₁ v₁ u₂ v₂ : F} (h₁ : M.Equation u₁ v₁)
    (h₂ : M.Equation u₂ v₂) (hxy : ¬(M.B * u₁ = M.B * u₂ ∧
      M.B ^ 2 * v₁ = M.toWeierstrass.negY (M.B * u₂) (M.B ^ 2 * v₂))) (ℓ : F)
    (hℓ : M.toWeierstrass.slope (M.B * u₁) (M.B * u₂) (M.B ^ 2 * v₁) (M.B ^ 2 * v₂) = M.B * ℓ) :
    M.Equation (M.addU u₁ u₂ ℓ) (M.addV u₁ u₂ v₁ ℓ) := by
  rw [M.equation_iff_toWeierstrass IsNonsingular.B_ne_zero, ← addX_eq, ← addY_eq, ← hℓ]
  exact (WeierstrassCurve.Affine.nonsingular_add (M.nonsingular_mul h₁) (M.nonsingular_mul h₂)
    hxy).1

open scoped Classical in
/-- The sum of two affine points that are not inverse to each other, given the Weierstrass slope
as `B` times a Montgomery slope `ℓ`. -/
private theorem some_add_some_eq {u₁ v₁ u₂ v₂ : F} (h₁ : M.Equation u₁ v₁)
    (h₂ : M.Equation u₂ v₂) (hxy : ¬(M.B * u₁ = M.B * u₂ ∧
      M.B ^ 2 * v₁ = M.toWeierstrass.negY (M.B * u₂) (M.B ^ 2 * v₂))) (ℓ : F)
    (hℓ : M.toWeierstrass.slope (M.B * u₁) (M.B * u₂) (M.B ^ 2 * v₁) (M.B ^ 2 * v₂) = M.B * ℓ) :
    Point.some u₁ v₁ h₁ + Point.some u₂ v₂ h₂ =
      Point.some (M.addU u₁ u₂ ℓ) (M.addV u₁ u₂ v₁ ℓ) (equation_add_of_slope h₁ h₂ hxy ℓ hℓ) := by
  have hB : M.B ≠ 0 := IsNonsingular.B_ne_zero
  rw [add_eq, pointEquivWeierstrass_some, pointEquivWeierstrass_some,
    WeierstrassCurve.Affine.Point.add_some hxy, pointEquivWeierstrass_symm_some, Point.some.injEq,
    hℓ, addX_eq, addY_eq, mul_div_cancel_left₀ _ hB, mul_div_cancel_left₀ _ (pow_ne_zero 2 hB)]
  exact ⟨rfl, rfl⟩

private theorem not_inverse_of_u_ne {u₁ v₁ u₂ v₂ : F} (hu : u₁ ≠ u₂) :
    ¬(M.B * u₁ = M.B * u₂ ∧ M.B ^ 2 * v₁ = M.toWeierstrass.negY (M.B * u₂) (M.B ^ 2 * v₂)) :=
  fun h => hu (mul_left_cancel₀ IsNonsingular.B_ne_zero h.1)

private theorem not_inverse_of_v_ne {u₁ v₁ u₂ v₂ : F} (hv : v₁ ≠ -v₂) :
    ¬(M.B * u₁ = M.B * u₂ ∧ M.B ^ 2 * v₁ = M.toWeierstrass.negY (M.B * u₂) (M.B ^ 2 * v₂)) := by
  simp only [WeierstrassCurve.Affine.negY, toWeierstrass, zero_mul, sub_zero]
  intro h
  exact hv (mul_left_cancel₀ (pow_ne_zero 2 IsNonsingular.B_ne_zero) (by rw [h.2]; ring))

private theorem ne_neg_self (h2 : (2 : F) ≠ 0) {v : F} (hv : v ≠ 0) : v ≠ -v := fun h =>
  hv (mul_left_cancel₀ h2 (by linear_combination h))

/-- The chord through two affine points with distinct `u`-coordinates meets the model again. -/
theorem equation_add_of_u_ne {u₁ v₁ u₂ v₂ : F} (h₁ : M.Equation u₁ v₁) (h₂ : M.Equation u₂ v₂)
    (hu : u₁ ≠ u₂) :
    M.Equation (M.addU u₁ u₂ (chordSlope u₁ v₁ u₂ v₂))
      (M.addV u₁ u₂ v₁ (chordSlope u₁ v₁ u₂ v₂)) :=
  equation_add_of_slope h₁ h₂ (not_inverse_of_u_ne hu) _ (slope_eq_of_u_ne hu)

/-- The chord-and-tangent formula for two affine points with distinct `u`-coordinates:
`(u₁, v₁) + (u₂, v₂) = (B ℓ² - A - u₁ - u₂, ℓ (u₁ - u₃) - v₁)` with `ℓ = (v₂ - v₁) / (u₂ - u₁)`. -/
theorem some_add_some_of_u_ne {u₁ v₁ u₂ v₂ : F} (h₁ : M.Equation u₁ v₁) (h₂ : M.Equation u₂ v₂)
    (hu : u₁ ≠ u₂) :
    Point.some u₁ v₁ h₁ + Point.some u₂ v₂ h₂ =
      Point.some (M.addU u₁ u₂ (chordSlope u₁ v₁ u₂ v₂))
        (M.addV u₁ u₂ v₁ (chordSlope u₁ v₁ u₂ v₂)) (equation_add_of_u_ne h₁ h₂ hu) :=
  some_add_some_eq h₁ h₂ (not_inverse_of_u_ne hu) _ (slope_eq_of_u_ne hu)

/-- The tangent at an affine point `(u₁, v₁)` with `v₁ ≠ 0` meets the model again (stated for
`(u₂, v₂)` with `u₂ = u₁` and `v₂ ≠ -v₁`, which forces `(u₂, v₂) = (u₁, v₁)`). -/
theorem equation_add_of_v_ne {u₁ v₁ u₂ v₂ : F} (h₁ : M.Equation u₁ v₁) (h₂ : M.Equation u₂ v₂)
    (hu : u₁ = u₂) (hv : v₁ ≠ -v₂) :
    M.Equation (M.addU u₁ u₂ (M.tangentSlope u₁ v₁)) (M.addV u₁ u₂ v₁ (M.tangentSlope u₁ v₁)) :=
  equation_add_of_slope h₁ h₂ (not_inverse_of_v_ne hv) _ (slope_eq_of_v_ne hu hv)

/-- The chord-and-tangent formula for two affine points with the same `u`-coordinate that are
not inverse to each other (so that they coincide, with `v₁ ≠ 0`): the tangent formula,
`ℓ = (3 u₁² + 2 A u₁ + 1) / (2 B v₁)`. -/
theorem some_add_some_of_v_ne {u₁ v₁ u₂ v₂ : F} (h₁ : M.Equation u₁ v₁) (h₂ : M.Equation u₂ v₂)
    (hu : u₁ = u₂) (hv : v₁ ≠ -v₂) :
    Point.some u₁ v₁ h₁ + Point.some u₂ v₂ h₂ =
      Point.some (M.addU u₁ u₂ (M.tangentSlope u₁ v₁)) (M.addV u₁ u₂ v₁ (M.tangentSlope u₁ v₁))
        (equation_add_of_v_ne h₁ h₂ hu hv) :=
  some_add_some_eq h₁ h₂ (not_inverse_of_v_ne hv) _ (slope_eq_of_v_ne hu hv)

/-- The tangent at an affine point with `v ≠ 0` meets the model again. -/
theorem equation_add_self {u v : F} (h : M.Equation u v) (hv : v ≠ 0) :
    M.Equation (M.addU u u (M.tangentSlope u v)) (M.addV u u v (M.tangentSlope u v)) :=
  equation_add_of_v_ne h h rfl (ne_neg_self (IsNonsingular.two_ne_zero (M := M)) hv)

/-- Doubling an affine point with `v ≠ 0`: the tangent formula. -/
theorem some_add_self {u v : F} (h : M.Equation u v) (hv : v ≠ 0) :
    Point.some u v h + Point.some u v h =
      Point.some (M.addU u u (M.tangentSlope u v)) (M.addV u u v (M.tangentSlope u v))
        (equation_add_self h hv) :=
  some_add_some_of_v_ne h h rfl (ne_neg_self (IsNonsingular.two_ne_zero (M := M)) hv)

/-- Two affine points with the same `u`-coordinate and opposite `v`-coordinates are inverse. -/
theorem some_add_some_eq_zero {u₁ v₁ u₂ v₂ : F} (h₁ : M.Equation u₁ v₁) (h₂ : M.Equation u₂ v₂)
    (hu : u₁ = u₂) (hv : v₁ = -v₂) : Point.some u₁ v₁ h₁ + Point.some u₂ v₂ h₂ = 0 := by
  classical
  rw [add_eq, pointEquivWeierstrass_some, pointEquivWeierstrass_some,
    WeierstrassCurve.Affine.Point.add_of_Y_eq (by rw [hu]) (by
      simp only [WeierstrassCurve.Affine.negY, toWeierstrass, zero_mul, sub_zero, hv]
      ring), zero_def]
  rfl

/-- The chord-and-tangent law closes: the sum of two affine points that are not inverse to each
other is on the model. -/
theorem equation_add [DecidableEq F] {u₁ v₁ u₂ v₂ : F} (h₁ : M.Equation u₁ v₁)
    (h₂ : M.Equation u₂ v₂) (hne : ¬(u₁ = u₂ ∧ v₁ = -v₂)) :
    M.Equation (M.addU u₁ u₂ (M.slope u₁ v₁ u₂ v₂)) (M.addV u₁ u₂ v₁ (M.slope u₁ v₁ u₂ v₂)) := by
  by_cases hu : u₁ = u₂
  · have hv : v₁ ≠ -v₂ := fun hv => hne ⟨hu, hv⟩
    simpa only [slope, hu, hv, ite_true, ite_false] using equation_add_of_v_ne h₁ h₂ hu hv
  · simpa only [slope, hu, ite_false] using equation_add_of_u_ne h₁ h₂ hu

/-- **The group law in coordinates**: the sum of two affine points that are not inverse to each
other is `(B ℓ² - A - u₁ - u₂, ℓ (u₁ - u₃) - v₁)`, `ℓ = M.slope u₁ v₁ u₂ v₂` (chord or tangent);
inverse points add to `0` (`some_add_some_eq_zero`). -/
theorem some_add_some [DecidableEq F] {u₁ v₁ u₂ v₂ : F} (h₁ : M.Equation u₁ v₁)
    (h₂ : M.Equation u₂ v₂) (hne : ¬(u₁ = u₂ ∧ v₁ = -v₂)) :
    Point.some u₁ v₁ h₁ + Point.some u₂ v₂ h₂ =
      Point.some (M.addU u₁ u₂ (M.slope u₁ v₁ u₂ v₂)) (M.addV u₁ u₂ v₁ (M.slope u₁ v₁ u₂ v₂))
        (equation_add h₁ h₂ hne) := by
  by_cases hu : u₁ = u₂
  · have hv : v₁ ≠ -v₂ := fun hv => hne ⟨hu, hv⟩
    rw [some_add_some_of_v_ne h₁ h₂ hu hv, Point.some.injEq]
    simp only [slope, hu, hv, ite_true, ite_false, and_self]
  · rw [some_add_some_of_u_ne h₁ h₂ hu, Point.some.injEq]
    simp only [slope, hu, ite_false, and_self]

/-! ### The 2-descent

The map `Q ↦ B u(Q)` modulo squares is the classical 2-descent map of the 2-torsion point
`(0, 0)`: in the Weierstrass form `y² = x (x² + A B x + B²)`, `x = B u`, it is the homomorphism
`M.Point → F* / F*²` with `∞ ↦ 1` and `(0, 0) ↦ B²`, so its kernel is the subgroup of points `Q`
with `B u(Q)` a square (with the convention `u ∞ = 0` both exceptional points have `B u = 0`, a
square). Here only what the kernel needs: the chord identity `u₁ u₂ u₃ (u₁ - u₂)² = B (u₁ v₂ -
u₂ v₁)²`, the tangent identity `B u(2 Q) (2 v)² = (u² - 1)²`, the translation `u(Q + (0, 0)) =
1 / u(Q)`, and the closure of the kernel under addition. -/

private theorem cert_u_add_of_u_ne (A B u₁ v₁ u₂ v₂ ℓ : F)
    (h₁ : B * v₁ ^ 2 = u₁ ^ 3 + A * u₁ ^ 2 + u₁) (h₂ : B * v₂ ^ 2 = u₂ ^ 3 + A * u₂ ^ 2 + u₂)
    (hℓ : ℓ * (u₂ - u₁) = v₂ - v₁) :
    u₁ * u₂ * (B * ℓ ^ 2 - A - u₁ - u₂) * (u₁ - u₂) ^ 2 = B * (u₁ * v₂ - u₂ * v₁) ^ 2 := by
  linear_combination (u₁ * u₂ * B * (ℓ * (u₂ - u₁) + (v₂ - v₁))) * hℓ
    + (u₂ - u₁) * (u₁ * h₂ - u₂ * h₁)

private theorem cert_u_two_nsmul (A B u v ℓ : F) (h : B * v ^ 2 = u ^ 3 + A * u ^ 2 + u)
    (hℓ : ℓ * (2 * B * v) = 3 * u ^ 2 + 2 * A * u + 1) :
    B * (B * ℓ ^ 2 - A - u - u) * (2 * v) ^ 2 = (u ^ 2 - 1) ^ 2 := by
  linear_combination (ℓ * (2 * B * v) + (3 * u ^ 2 + 2 * A * u + 1)) * hℓ - 4 * (A + 2 * u) * h

private theorem cert_u_add_zero (A B u v ℓ : F) (h : B * v ^ 2 = u ^ 3 + A * u ^ 2 + u)
    (hℓ : ℓ * u = v) :
    u * ((B * ℓ ^ 2 - A - 0 - u) * u - 1) = 0 := by
  linear_combination B * (ℓ * u + v) * hℓ + h

/-- The 2-descent identity for the chord: `u₁ u₂ u₃ (u₁ - u₂)² = B (u₁ v₂ - u₂ v₁)²`. -/
theorem u_mul_u_mul_u_add_of_u_ne {u₁ v₁ u₂ v₂ : F} (h₁ : M.Equation u₁ v₁)
    (h₂ : M.Equation u₂ v₂) (hu : u₁ ≠ u₂) :
    u₁ * u₂ * (Point.some u₁ v₁ h₁ + Point.some u₂ v₂ h₂).u * (u₁ - u₂) ^ 2 =
      M.B * (u₁ * v₂ - u₂ * v₁) ^ 2 := by
  rw [some_add_some_of_u_ne h₁ h₂ hu, u_some]
  exact cert_u_add_of_u_ne M.A M.B u₁ v₁ u₂ v₂ _ h₁ h₂
    (div_mul_cancel₀ _ (sub_ne_zero.mpr (Ne.symm hu)))

/-- Translation by the 2-torsion point `(0, 0)` inverts `u`. -/
theorem u_zero_zero_add_mul_u {u v : F} (h : M.Equation u v) (hu : u ≠ 0) :
    (Point.some 0 0 M.equation_zero_zero + Point.some u v h).u * u = 1 := by
  rw [some_add_some_of_u_ne _ h (Ne.symm hu), u_some]
  have key := cert_u_add_zero M.A M.B u v (chordSlope 0 0 u v) h (by
    simp only [chordSlope, sub_zero]
    exact div_mul_cancel₀ _ hu)
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hu)

/-- The 2-descent identity for the tangent: `B u(2 Q) (2 v)² = (u² - 1)²`. -/
theorem B_mul_u_two_nsmul_mul_sq {u v : F} (h : M.Equation u v) (hv : v ≠ 0) :
    M.B * (2 • Point.some u v h).u * (2 * v) ^ 2 = (u ^ 2 - 1) ^ 2 := by
  rw [two_nsmul, some_add_self h hv, u_some]
  refine cert_u_two_nsmul M.A M.B u v _ h ?_
  change (3 * u ^ 2 + 2 * M.A * u + 1) / (2 * M.B * v) * (2 * M.B * v) = _
  have h2 : (2 : F) ≠ 0 := IsNonsingular.two_ne_zero (M := M)
  exact div_mul_cancel₀ _ (mul_ne_zero (mul_ne_zero h2 IsNonsingular.B_ne_zero) hv)

/-- The differential-addition identity, by Vieta: with `s = u₂ - u₁`, the `u`-coordinates of the
sum and the difference satisfy `u(Q₁ ± Q₂) s² = C ∓ 2 B v₁ v₂` with
`C = (u₁ + u₂)(u₁ u₂ + 1) + 2 A u₁ u₂`; their product is `C² - 4 f(u₁) f(u₂)` (`B vᵢ² = f(uᵢ)`),
which is `(u₁ u₂ - 1)² (u₁ - u₂)²`. -/
private theorem u_add_mul_u_sub_aux (A B u₁ v₁ u₂ v₂ l₁ l₂ : F)
    (h₁ : B * v₁ ^ 2 = u₁ ^ 3 + A * u₁ ^ 2 + u₁) (h₂ : B * v₂ ^ 2 = u₂ ^ 3 + A * u₂ ^ 2 + u₂)
    (hl₁ : l₁ * (u₂ - u₁) = v₂ - v₁) (hl₂ : l₂ * (u₂ - u₁) = -v₂ - v₁) (hs : u₂ - u₁ ≠ 0) :
    (B * l₁ ^ 2 - A - u₁ - u₂) * (B * l₂ ^ 2 - A - u₁ - u₂) * (u₁ - u₂) ^ 2 =
      (u₁ * u₂ - 1) ^ 2 := by
  set C := (u₁ + u₂) * (u₁ * u₂ + 1) + 2 * A * u₁ * u₂
  -- the two roots
  have hsum : (B * l₁ ^ 2 - A - u₁ - u₂) * (u₂ - u₁) ^ 2 = C - 2 * B * v₁ * v₂ := by
    linear_combination B * (l₁ * (u₂ - u₁) + (v₂ - v₁)) * hl₁ + h₁ + h₂
  have hdiff : (B * l₂ ^ 2 - A - u₁ - u₂) * (u₂ - u₁) ^ 2 = C + 2 * B * v₁ * v₂ := by
    linear_combination B * (l₂ * (u₂ - u₁) + (-v₂ - v₁)) * hl₂ + h₁ + h₂
  -- their product: `C² - 4 f(u₁) f(u₂)` is a perfect square
  have hprod : (C - 2 * B * v₁ * v₂) * (C + 2 * B * v₁ * v₂) =
      (u₁ * u₂ - 1) ^ 2 * (u₁ - u₂) ^ 2 := by
    linear_combination (-4 * B * v₂ ^ 2) * h₁ + (-4 * (u₁ ^ 3 + A * u₁ ^ 2 + u₁)) * h₂
  apply mul_right_cancel₀ (pow_ne_zero 2 hs)
  linear_combination (B * l₂ ^ 2 - A - u₁ - u₂) * (u₂ - u₁) ^ 2 * hsum +
    (C - 2 * B * v₁ * v₂) * hdiff + hprod

/-- The x-only differential-addition identity (`uADD`): for affine points with distinct
`u`-coordinates, `u(Q₁ + Q₂) u(Q₁ - Q₂) (u₁ - u₂)² = (u₁ u₂ - 1)²`. It does not involve `B`. -/
theorem u_add_mul_u_sub_of_u_ne {u₁ v₁ u₂ v₂ : F} (h₁ : M.Equation u₁ v₁)
    (h₂ : M.Equation u₂ v₂) (hu : u₁ ≠ u₂) :
    (Point.some u₁ v₁ h₁ + Point.some u₂ v₂ h₂).u *
      (Point.some u₁ v₁ h₁ - Point.some u₂ v₂ h₂).u * (u₁ - u₂) ^ 2 = (u₁ * u₂ - 1) ^ 2 := by
  rw [sub_eq_add_neg, neg_some, some_add_some_of_u_ne h₁ h₂ hu,
    some_add_some_of_u_ne h₁ (equation_neg h₂) hu, u_some, u_some]
  have hs : u₂ - u₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  exact u_add_mul_u_sub_aux M.A M.B u₁ v₁ u₂ v₂ _ _ h₁ h₂ (div_mul_cancel₀ _ hs)
    (div_mul_cancel₀ _ hs) hs

/-- `B u(2 Q)` is a square: the doubles lie in the kernel of the 2-descent map. -/
theorem isSquare_B_mul_u_two_nsmul (Q : M.Point) : IsSquare (M.B * (2 • Q).u) := by
  rcases Point.cases Q with rfl | ⟨u, v, h, rfl⟩
  · rw [smul_zero, u_zero, mul_zero]
    exact IsSquare.zero
  · by_cases hv : v = 0
    · rw [two_nsmul, some_add_some_eq_zero h h rfl (by rw [hv, neg_zero]), u_zero, mul_zero]
      exact IsSquare.zero
    · have h2 : (2 : F) ≠ 0 := IsNonsingular.two_ne_zero (M := M)
      refine ⟨(u ^ 2 - 1) / (2 * v), ?_⟩
      rw [div_mul_div_comm, eq_div_iff (mul_ne_zero (mul_ne_zero h2 hv) (mul_ne_zero h2 hv))]
      linear_combination B_mul_u_two_nsmul_mul_sq h hv

/-- Negation preserves the 2-descent class. -/
theorem isSquare_B_mul_u_neg (Q : M.Point) : IsSquare (M.B * (-Q).u) ↔ IsSquare (M.B * Q.u) := by
  rw [u_neg]

/-- The 2-descent kernel is closed under addition: if `B u(Q₁)` and `B u(Q₂)` are squares then so
is `B u(Q₁ + Q₂)`. -/
theorem isSquare_B_mul_u_add {Q₁ Q₂ : M.Point} (hQ₁ : IsSquare (M.B * Q₁.u))
    (hQ₂ : IsSquare (M.B * Q₂.u)) : IsSquare (M.B * (Q₁ + Q₂).u) := by
  have hB : M.B ≠ 0 := IsNonsingular.B_ne_zero
  rcases Point.cases Q₁ with rfl | ⟨u₁, v₁, h₁, rfl⟩
  · rwa [zero_add]
  rcases Point.cases Q₂ with rfl | ⟨u₂, v₂, h₂, rfl⟩
  · rwa [add_zero]
  by_cases hu : u₁ = u₂
  · subst hu
    by_cases hv : v₁ = -v₂
    · rw [some_add_some_eq_zero h₁ h₂ rfl hv, u_zero, mul_zero]
      exact IsSquare.zero
    · have hsq : v₁ ^ 2 = v₂ ^ 2 := by
        apply mul_left_cancel₀ hB
        unfold Equation at h₁ h₂
        rw [h₁, h₂]
      obtain rfl := (sq_eq_sq_iff_eq_or_eq_neg.mp hsq).resolve_right hv
      rw [← two_nsmul]
      exact isSquare_B_mul_u_two_nsmul _
  · rw [u_some] at hQ₁ hQ₂
    by_cases hu₁ : u₁ = 0
    · subst hu₁
      obtain rfl := v_eq_zero_of_u_eq_zero hB h₁ rfl
      have hu₂ : u₂ ≠ 0 := Ne.symm hu
      have key := u_zero_zero_add_mul_u h₂ hu₂
      obtain ⟨r, hr⟩ := hQ₂
      refine ⟨r / u₂, ?_⟩
      rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hu₂ hu₂), ← hr]
      linear_combination M.B * u₂ * key
    by_cases hu₂ : u₂ = 0
    · subst hu₂
      obtain rfl := v_eq_zero_of_u_eq_zero hB h₂ rfl
      have key := u_zero_zero_add_mul_u h₁ hu₁
      obtain ⟨r, hr⟩ := hQ₁
      refine ⟨r / u₁, ?_⟩
      rw [add_comm, div_mul_div_comm, eq_div_iff (mul_ne_zero hu₁ hu₁), ← hr]
      linear_combination M.B * u₁ * key
    -- the chord identity `u₁ u₂ u₃ (u₁ - u₂)² = B (u₁ v₂ - u₂ v₁)²` makes `B u₃` a quotient of
    -- squares: `B u₃ = (B² (u₁ v₂ - u₂ v₁) / (u₁ - u₂))² / ((B u₁) (B u₂))`
    have hd : u₁ - u₂ ≠ 0 := sub_ne_zero.mpr hu
    have key := u_mul_u_mul_u_add_of_u_ne h₁ h₂ hu
    have e : M.B * (Point.some u₁ v₁ h₁ + Point.some u₂ v₂ h₂).u =
        (M.B ^ 2 * (u₁ * v₂ - u₂ * v₁) / (u₁ - u₂)) ^ 2 / ((M.B * u₁) * (M.B * u₂)) := by
      rw [eq_div_iff (mul_ne_zero (mul_ne_zero hB hu₁) (mul_ne_zero hB hu₂)), div_pow,
        eq_div_iff (pow_ne_zero 2 hd)]
      linear_combination M.B ^ 3 * key
    rw [e]
    exact (IsSquare.sq _).div (hQ₁.mul hQ₂)

/-! ### The curve -/

/-- `pointEquiv` sends the point at infinity to the zero of the curve. -/
@[simp]
theorem pointEquiv_zero [NeZero (6 : F)] : M.pointEquiv 0 = 0 :=
  map_zero _

omit [M.IsNonsingular] in
/-- The discriminant of the invariants: `c₄³ - c₆² = 1728 · 16 B⁶ (A² - 4)`. -/
theorem c₄_cube_sub_c₆_sq : M.c₄ ^ 3 - M.c₆ ^ 2 = 27648 * M.B ^ 6 * (M.A ^ 2 - 4) := by
  simp only [c₄, c₆]
  ring

theorem c₄_cube_sub_c₆_sq_ne_zero [NeZero (6 : F)] :
    M.c₄ ^ 3 - M.c₆ ^ 2 ≠ 0 := by
  rw [c₄_cube_sub_c₆_sq, show (27648 : F) = 1728 * 16 by norm_num, show (16 : F) = 2 ^ 4 by
    norm_num]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero ne_zero_1728_of_six (pow_ne_zero _ two_ne_zero))
    (pow_ne_zero _ IsNonsingular.B_ne_zero)) (sub_ne_zero.mpr IsNonsingular.A_sq_ne_four)

/-- **The curve of a Montgomery model** is the curve with invariants `M.c₄`, `M.c₆`. -/
theorem toCurve_eq_mk [NeZero (6 : F)] :
    M.toCurve = Curve.mk M.c₄ M.c₆ M.c₄_cube_sub_c₆_sq_ne_zero := by
  refine M.realization.toCurve_eq_mk _ 1 one_ne_zero ?_ ?_ <;>
    simp only [realization, toWeierstrass, c₄, c₆, WeierstrassCurve.c₄, WeierstrassCurve.c₆,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] <;> ring

/-- The j-invariant of a Montgomery model: `256 (A² - 3)³ / (A² - 4)`. -/
theorem j_toCurve [NeZero (6 : F)] :
    M.toCurve.j = 256 * (M.A ^ 2 - 3) ^ 3 / (M.A ^ 2 - 4) := by
  have hB : M.B ≠ 0 := IsNonsingular.B_ne_zero
  have hA : M.A ^ 2 - 4 ≠ 0 := sub_ne_zero.mpr IsNonsingular.A_sq_ne_four
  have h : (27648 : F) ≠ 0 := by
    rw [show (27648 : F) = 1728 * 2 ^ 4 by norm_num]
    exact mul_ne_zero ne_zero_1728_of_six (pow_ne_zero _ two_ne_zero)
  rw [toCurve_eq_mk, Curve.j_mk, c₄_cube_sub_c₆_sq, c₄]
  field_simp
  ring

omit [M.IsNonsingular] in
/-- Twisting the model by `c` (`B ↦ B c`) multiplies `c₄` by `c²`. -/
theorem twist_c₄ (c : F) : (M.twist c).c₄ = c ^ 2 * M.c₄ := by
  simp only [twist, c₄]; ring

omit [M.IsNonsingular] in
/-- The invariant `c₆` of the twist by `c`. -/
theorem twist_c₆ (c : F) : (M.twist c).c₆ = c ^ 3 * M.c₆ := by
  simp only [twist, c₆]; ring

/-- The twist of a nonsingular model by a unit is nonsingular. -/
instance isNonsingular_twist_units (c : Fˣ) : (M.twist (c : F)).IsNonsingular where
  two_ne_zero := IsNonsingular.two_ne_zero (M := M)
  B_ne_zero := by rw [twist_B]; exact mul_ne_zero IsNonsingular.B_ne_zero c.ne_zero
  A_sq_ne_four := by rw [twist_A]; exact IsNonsingular.A_sq_ne_four

/-- **The curve of the twist** of `M` by `c` is the quadratic twist by `c` of the curve of `M`. -/
theorem toCurve_twist [NeZero (6 : F)] (c : Fˣ) :
    (M.twist (c : F)).toCurve = M.toCurve.quadraticTwist c := by
  rw [toCurve_eq_mk, toCurve_eq_mk, Curve.quadraticTwist_mk]
  exact Curve.mk_congr (twist_c₄ (c : F)) (twist_c₆ (c : F))

/-- Two Montgomery models with the same `A` and `B' = B c²` (`c ≠ 0`) realise the same curve
(`v ↦ c v` identifies their points): their invariants differ by the weights `c⁴`, `c⁶`. -/
theorem toCurve_eq_of_B_eq_mul_sq (M M' : MontgomeryModel F) [M.IsNonsingular]
    [M'.IsNonsingular] [NeZero (6 : F)] (hA : M'.A = M.A) {c : F} (hc : c ≠ 0)
    (hB : M'.B = M.B * c ^ 2) :
    M'.toCurve = M.toCurve := by
  rw [toCurve_eq_mk, toCurve_eq_mk]
  exact Curve.mk_eq_mk_of c hc (by simp only [c₄, hA, hB]; ring)
    (by simp only [c₆, hA, hB]; ring)

end MontgomeryModel
