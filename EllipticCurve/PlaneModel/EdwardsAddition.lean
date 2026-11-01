/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.PlaneModel.EdwardsPoints
public import EllipticCurve.PlaneModel.EdwardsFormula
import EllipticCurve.TwistedEdwards.Formula
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # Points of a complete twisted Edwards curve

On a complete curve the denominators of the addition formula never vanish (`den_ne_zero`), every
solution of the Edwards equation is nonsingular, so points are determined by their coordinates
(`edwards_coords_injective`), and the coordinates of points commute with base change. -/

public section

universe u

open FunctionField.RationalPlace TwistedEdwardsFormula

namespace PlaneModel

variable {L : Type u} [Field L] {a d : L} {had : a - d ≠ 0} {h2 : (2 : L) ≠ 0}
  [(edwardsRoot a d).IsElliptic]

section Complete

variable (hE : (⟨a, d⟩ : TwistedEdwardsModel L).IsComplete)
include hE

omit [(edwardsRoot a d).IsElliptic] in
/-- On a complete curve, `a ≠ d c²`. -/
theorem sub_d_mul_sq_ne_zero (c : L) : a - d * c ^ 2 ≠ 0 := by
  intro h
  obtain ⟨r, hr⟩ := hE.isSquare_a
  have hc : c ≠ 0 := by rintro rfl; exact hE.a_ne_zero (by simpa using h)
  exact hE.not_isSquare_d ⟨r / c, by field_simp; linear_combination -h + hr⟩

omit [(edwardsRoot a d).IsElliptic] in
/-- On a complete curve, `d c² ≠ 1`. -/
theorem one_sub_d_mul_sq_ne_zero (c : L) : 1 - d * c ^ 2 ≠ 0 := by
  intro h
  have hc : c ≠ 0 := by rintro rfl; simp at h
  exact hE.not_isSquare_d ⟨1 / c, by field_simp; linear_combination -h⟩

omit [(edwardsRoot a d).IsElliptic] in
/-- Completeness, pointwise: the denominators of the formula never vanish. -/
theorem den_ne_zero {p₁ p₂ q₁ q₂ : L} (hp : a * p₁ ^ 2 + p₂ ^ 2 = 1 + d * p₁ ^ 2 * p₂ ^ 2)
    (hq : a * q₁ ^ 2 + q₂ ^ 2 = 1 + d * q₁ ^ 2 * q₂ ^ 2) :
    1 + d * p₁ * q₁ * p₂ * q₂ ≠ 0 ∧ 1 - d * p₁ * q₁ * p₂ * q₂ ≠ 0 := by
  have := hE
  exact ⟨TwistedEdwardsModel.addDen₁_ne_zero (E := ⟨a, d⟩) ⟨p₁, p₂, hp⟩ ⟨q₁, q₂, hq⟩,
    TwistedEdwardsModel.addDen₂_ne_zero (E := ⟨a, d⟩) ⟨p₁, p₂, hp⟩ ⟨q₁, q₂, hq⟩⟩

end Complete

/-- Coordinates of points satisfy the Edwards equation. -/
theorem edwards_equation_of_coords {P : (edwards a d had h2).Point}
    {p₁ p₂ : L} (hP : (edwards a d had h2).coords P = some (p₁, p₂)) :
    a * p₁ ^ 2 + p₂ ^ 2 = 1 + d * p₁ ^ 2 * p₂ ^ 2 := by
  have h := (edwards a d had h2).coords_equation hP
  rw [edwards_G] at h
  simp only [map_sub, map_add, map_mul, map_pow, map_one, MvPolynomial.eval_X,
    MvPolynomial.eval_C, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  linear_combination h

omit [(edwardsRoot a d).IsElliptic] in
/-- On a complete curve, every solution of the Edwards equation is nonsingular. -/
theorem edwards_nonsingular (hE : (⟨a, d⟩ : TwistedEdwardsModel L).IsComplete) {p₁ p₂ : L}
    (hp : a * p₁ ^ 2 + p₂ ^ 2 = 1 + d * p₁ ^ 2 * p₂ ^ 2) :
    (edwards a d had h2).Nonsingular p₁ p₂ := by
  refine ((edwards a d had h2).nonsingular_iff p₁ p₂).mpr ⟨?_, ?_⟩
  · rw [edwards_G]
    simp only [map_sub, map_add, map_mul, map_pow, map_one, MvPolynomial.eval_X,
      MvPolynomial.eval_C, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination hp
  · by_contra! h
    rw [edwards_G] at h
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, map_sub, map_add,
      Derivation.leibniz, Derivation.leibniz_pow, Nat.add_one_sub_one, pow_one,
      MvPolynomial.pderiv_X, Pi.single_eq_same, smul_eq_mul, mul_one, nsmul_eq_mul,
      Nat.cast_ofNat, MvPolynomial.derivation_C, mul_zero, add_zero, ne_eq, one_ne_zero,
      not_false_eq_true, Pi.single_eq_of_ne, Derivation.map_one_eq_zero, sub_zero,
      zero_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_ofNat, MvPolynomial.eval_X,
      Matrix.cons_val_zero, map_pow, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      zero_ne_one] at h
    obtain ⟨h0, h1⟩ := h
    have hp₁ : p₁ = 0 := by
      have : 2 * p₁ * (a - d * p₂ ^ 2) = 0 := by linear_combination h0
      rcases mul_eq_zero.mp this with h | h
      · exact (mul_eq_zero.mp h).resolve_left h2
      · exact absurd h (sub_d_mul_sq_ne_zero hE p₂)
    have hp₂ : p₂ = 0 := by
      have : 2 * p₂ * (1 - d * p₁ ^ 2) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp this with h | h
      · exact (mul_eq_zero.mp h).resolve_left h2
      · exact absurd h (one_sub_d_mul_sq_ne_zero hE p₁)
    subst hp₁ hp₂
    simp at hp

/-- **On a complete curve, points are determined by their coordinates.** -/
theorem edwards_coords_injective (hE : (⟨a, d⟩ : TwistedEdwardsModel L).IsComplete)
    {P Q : (edwards a d had h2).Point} {p : L × L}
    (hP : (edwards a d had h2).coords P = some p) (hQ : (edwards a d had h2).coords Q = some p) :
    P = Q :=
  (edwards a d had h2).coords_injective (edwards_nonsingular hE (edwards_equation_of_coords hP))
    hP hQ

/-! ### Coordinates in terms of the root's -/

open Classical in
/-- The Edwards coordinates of the root point `(X, Y)`: `(u / v, (u - 1) / (u + 1))` with
`u = X / B`, `v = Y / B²`, and `(0, -1)` at the Montgomery point `(0, 0)`. -/
noncomputable def edwardsOfRoot (a d X Y : L) : L × L :=
  if Y = 0 then (0, -1) else
    ((X / (4 / (a - d))) / (Y / (4 / (a - d)) ^ 2),
      (X / (4 / (a - d)) - 1) / (X / (4 / (a - d)) + 1))

omit [(edwardsRoot a d).IsElliptic] in
open Classical in
/-- The coordinate formula at the Montgomery point `(0, 0)`, and the other root points with
`Y = 0`. -/
theorem edwardsOfRoot_zero {X : L} : edwardsOfRoot a d X 0 = (0, -1) := by
  unfold edwardsOfRoot; simp

omit [(edwardsRoot a d).IsElliptic] in
open Classical in
/-- The coordinate formula off the Montgomery point `(0, 0)`. -/
theorem edwardsOfRoot_of_ne {X Y : L} (hY : Y ≠ 0) : edwardsOfRoot a d X Y =
    ((X / (4 / (a - d))) / (Y / (4 / (a - d)) ^ 2),
      (X / (4 / (a - d)) - 1) / (X / (4 / (a - d)) + 1)) := by
  unfold edwardsOfRoot; simp [hY]

open Classical in
/-- **The coordinates of an affine root point**, explicitly. -/
theorem edwards_coords_some (hE : (⟨a, d⟩ : TwistedEdwardsModel L).IsComplete) {x₀ y₀ : L}
    (h : (edwardsRoot a d).Nonsingular x₀ y₀) :
    (edwards a d had h2).coords (.some x₀ y₀ h) = some (edwardsOfRoot a d x₀ y₀) := by
  obtain ⟨hx, hy, ex, ey⟩ := (edwardsRoot a d).pointEquivRationalPlace_some x₀ y₀ h
  set p := (edwardsRoot a d).pointEquivRationalPlace (.some x₀ y₀ h)
  have hB0 : (4 / (a - d) : L) ≠ 0 :=
    div_ne_zero (by rw [show (4 : L) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2) had
  have hB : p.HasValue (edwardsB a d) (4 / (a - d)) :=
    edwardsB_def (a := a) ▸ p.hasValue_algebraMap _
  have hA := p.hasValue_algebraMap (2 * (a + d) / (a - d))
  have hU : p.HasValue (edwardsU a d) (x₀ / (4 / (a - d))) :=
    edwardsU_def (a := a) ▸ (hasValue_iff.mpr ⟨hx, ex⟩ : p.HasValue _ x₀).div hB hB0
  have hV : p.HasValue (edwardsV a d) (y₀ / (4 / (a - d)) ^ 2) :=
    edwardsV_def (a := a) ▸ (hasValue_iff.mpr ⟨hy, ey⟩ : p.HasValue _ y₀).div (hB.pow 2)
      (pow_ne_zero 2 hB0)
  have heq := h.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  rw [show (edwardsRoot a d).a₁ = 0 from rfl, show (edwardsRoot a d).a₃ = 0 from rfl,
    show (edwardsRoot a d).a₆ = 0 from rfl,
    show (edwardsRoot a d).a₂ = 2 * (a + d) / (a - d) * (4 / (a - d)) from rfl,
    show (edwardsRoot a d).a₄ = (4 / (a - d)) ^ 2 from rfl] at heq
  have hm0 := montgomery_uv (A := 2 * (a + d) / (a - d)) (X := x₀) (Y := y₀) hB0
    (by linear_combination heq)
  have hq0 := edwards_q_ne_zero (u₀ := x₀ / (4 / (a - d))) had h2 hE.isSquare_a hE.a_ne_zero
    hE.not_isSquare_d
  have hu1 := edwards_u_add_one_ne_zero had h2 hE.not_isSquare_d hm0
  have hY := (hU.sub hasValue_one).div (hU.add hasValue_one) hu1
  rw [← edwards_y (had := had) (h2 := h2)] at hY
  unfold edwardsOfRoot
  split_ifs with hy₀
  · -- the Montgomery point `(0, 0)`
    subst hy₀
    have hu0 : x₀ / (4 / (a - d)) = 0 := by
      have : x₀ / (4 / (a - d)) * ((x₀ / (4 / (a - d))) ^ 2 + 2 * (a + d) / (a - d) *
          (x₀ / (4 / (a - d))) + 1) = 0 := by linear_combination hm0
      exact (mul_eq_zero.mp this).resolve_right hq0
    obtain ⟨hq, hx2⟩ := edwards_x_sq (edwardsV_ne_zero had h2) (edwardsB_ne_zero had h2)
      (edwards_montgomery had h2)
    have hX2 := ((hB.mul hU).div (((hU.pow 2).add (hA.mul hU)).add hasValue_one) hq0).congr
      hx2.symm rfl
    rw [hu0, mul_zero, zero_div] at hX2
    have hX := hX2.of_sq_zero
    rw [← edwards_x (had := had) (h2 := h2)] at hX
    rw [hu0] at hY
    exact coords_eq_of_hasValue _ hX (hY.congr rfl (by simp))
  · have hX := hU.div hV (div_ne_zero hy₀ (pow_ne_zero 2 hB0))
    rw [← edwards_x (had := had) (h2 := h2)] at hX
    exact coords_eq_of_hasValue _ hX hY

/-! ### Base change -/

open Classical in
/-- **Negation in Edwards coordinates**: `(x, y) ↦ (-x, y)`. -/
theorem edwards_coords_neg (hE : (⟨a, d⟩ : TwistedEdwardsModel L).IsComplete)
    {R : (edwards a d had h2).Point} {p₁ p₂ : L}
    (h : (edwards a d had h2).coords R = some (p₁, p₂)) :
    (edwards a d had h2).coords (-R) = some (-p₁, p₂) := by
  cases R with
  | zero =>
    rw [show (WeierstrassCurve.Affine.Point.zero : (edwardsRoot a d).Point) = 0 from rfl,
      edwards_coords_zero, Option.some_inj, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [show (WeierstrassCurve.Affine.Point.zero : (edwardsRoot a d).Point) = 0 from rfl,
      neg_zero, edwards_coords_zero, neg_zero]
  | some X Y hR =>
    rw [edwards_coords_some hE, Option.some_inj] at h
    rw [WeierstrassCurve.Affine.Point.neg_some, edwards_coords_some hE, Option.some_inj,
      show (-p₁, p₂) = (-(edwardsOfRoot a d X Y).1, (edwardsOfRoot a d X Y).2) by rw [h]]
    have hn : (edwardsRoot a d).negY X Y = -Y := by
      simp [WeierstrassCurve.Affine.negY, edwardsRoot, montgomeryRoot]
    rw [hn]
    by_cases hY : Y = 0
    · rw [hY, neg_zero, edwardsOfRoot_zero]
      simp
    · rw [edwardsOfRoot_of_ne hY, edwardsOfRoot_of_ne (neg_ne_zero.mpr hY)]
      simp only [Prod.mk.injEq, and_true]
      rw [neg_div, div_neg]

section BaseChange

variable {F : Type u} [Field F] {K : Type*} [Field K] (f : F →+* K)

open Classical in
/-- The coordinate formula commutes with field maps. -/
theorem map_edwardsOfRoot (a d X Y : F) :
    (f (edwardsOfRoot a d X Y).1, f (edwardsOfRoot a d X Y).2) =
      edwardsOfRoot (f a) (f d) (f X) (f Y) := by
  unfold edwardsOfRoot
  by_cases hY : Y = 0
  · simp [hY]
  · have : f Y ≠ 0 := (map_ne_zero f).mpr hY
    simp [hY, this, map_div₀, map_ofNat]

/-- The addition formula commutes with field maps. -/
theorem map_addX_formula (d x₁ y₁ x₂ y₂ : F) :
    f (addX d x₁ y₁ x₂ y₂) = addX (f d) (f x₁) (f y₁) (f x₂) (f y₂) := by
  simp [addX, map_div₀]

/-- The addition formula commutes with field maps. -/
theorem map_addY_formula (a d x₁ y₁ x₂ y₂ : F) :
    f (addY a d x₁ y₁ x₂ y₂) = addY (f a) (f d) (f x₁) (f y₁) (f x₂) (f y₂) := by
  simp [addY, map_div₀]

/-- The root of the twisted Edwards curve commutes with base change. -/
theorem edwardsRoot_baseChange [Algebra F K] (a d : F) :
    (edwardsRoot a d).baseChange K = edwardsRoot (algebraMap F K a) (algebraMap F K d) := by
  rw [show (edwardsRoot a d).baseChange K = (edwardsRoot a d).map (algebraMap F K) from rfl]
  ext <;> simp [edwardsRoot, montgomeryRoot, map_div₀, map_ofNat]

/-- Completeness persists to an extension with the same constants. -/
theorem isComplete_map [Algebra F K] {a d : F} (hE : (⟨a, d⟩ : TwistedEdwardsModel F).IsComplete)
    (hconst : ∀ z : K, IsAlgebraic F z → ∃ c : F, z = algebraMap F K c) :
    (⟨algebraMap F K a, algebraMap F K d⟩ : TwistedEdwardsModel K).IsComplete where
  two_ne_zero := by
    rw [← map_ofNat (algebraMap F K) 2]; exact (map_ne_zero _).mpr hE.two_ne_zero
  isSquare_a := by
    obtain ⟨r, hr⟩ := hE.isSquare_a
    change a = r * r at hr
    exact ⟨algebraMap F K r, by change algebraMap F K a = _; rw [hr, map_mul]⟩
  a_ne_zero := (map_ne_zero _).mpr hE.a_ne_zero
  not_isSquare_d := by
    rintro ⟨r, hr⟩
    obtain ⟨c, hc⟩ := hconst r ⟨Polynomial.X ^ 2 - Polynomial.C d,
      Polynomial.X_pow_sub_C_ne_zero (by norm_num) d, by simp [sq, ← hr]⟩
    apply hE.not_isSquare_d
    refine ⟨c, (algebraMap F K).injective ?_⟩
    change algebraMap F K d = _ at hr
    rw [hr, hc, map_mul]

end BaseChange

end PlaneModel
