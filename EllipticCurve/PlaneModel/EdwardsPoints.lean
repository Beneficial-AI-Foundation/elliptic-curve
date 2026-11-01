/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.PlaneModel.Basic
public import EllipticCurve.PlaneModel.Edwards
public import EllipticCurve.TwistedEdwards.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # The points of a complete twisted Edwards plane model

On a complete twisted Edwards model (`a` a nonzero square, `d` a non-square), every point is
affine (`edwards_coords_isSome`) and `O` sits at `(0, 1)` (`edwards_coords_zero`). Both are
proved from the identification of points with rational places, by computing values at places
(`FunctionField.RationalPlace.HasValue`): with `B v² = u³ + A u² + u`,
`x² = B u / (u² + A u + 1)` and `y = (u - 1) / (u + 1)`. At `O` the function `u` has a pole, so
`x² → 0` and `y → 1`; at an affine point, completeness keeps the denominators away from zero
(a zero would make `d` a square). -/

public section

universe u

open MvPolynomial

variable {F : Type u} [Field F]

namespace PlaneModel

/-! ### The geometric facts

Both follow from the statement of (A-W) alone, by computing values at places
(`FunctionField.RationalPlace.HasValue`): with `B v² = u³ + A u² + u`,
`x² = B u / (u² + A u + 1)` and `y = (u - 1) / (u + 1)`. At `O` the function `u` has a pole, so
`x² → 0` and `y → 1`; at an affine point, completeness keeps the denominators away from zero. -/

section Algebra

variable {K : Type*} [Field K]

/-- `x² = B u / (u² + A u + 1)` on the Montgomery model. -/
theorem edwards_x_sq {A B u v : K} (hv : v ≠ 0) (hB : B ≠ 0)
    (hm : u ^ 3 + A * u ^ 2 + u - B * v ^ 2 = 0) :
    u ^ 2 + A * u + 1 ≠ 0 ∧ (u / v) ^ 2 = B * u / (u ^ 2 + A * u + 1) := by
  have hq : u ^ 2 + A * u + 1 ≠ 0 := by
    intro hq
    have : B * v ^ 2 = 0 := by linear_combination u * hq - hm
    exact mul_ne_zero hB (pow_ne_zero 2 hv) this
  refine ⟨hq, ?_⟩
  rw [div_pow, div_eq_div_iff (pow_ne_zero 2 hv) hq]
  linear_combination u * hm

/-- Near `O`, in terms of `t = u⁻¹`. -/
theorem edwards_x_sq_inv {A B u : K} (hu : u ≠ 0) (hq : u ^ 2 + A * u + 1 ≠ 0) :
    B * u / (u ^ 2 + A * u + 1) = B * u⁻¹ / (1 + A * u⁻¹ + u⁻¹ ^ 2) := by
  have hq' : 1 + A * u⁻¹ + u⁻¹ ^ 2 ≠ 0 := by
    intro h
    apply hq
    have : u ^ 2 * (1 + A * u⁻¹ + u⁻¹ ^ 2) = u ^ 2 + A * u + 1 := by field_simp
    rw [← this, h, mul_zero]
  field_simp

/-- `y = (u - 1) / (u + 1)` in terms of `t = u⁻¹`. -/
theorem edwards_y_inv {u : K} (hu : u ≠ 0) (hu1 : u + 1 ≠ 0) :
    (u - 1) / (u + 1) = (1 - u⁻¹) / (1 + u⁻¹) := by
  have h : 1 + u⁻¹ = (u + 1) / u := by field_simp
  rw [h]
  field_simp

end Algebra

section Complete

variable {a d u₀ v₀ : F}

/-- On a complete model, `u² + A u + 1` has no root in `F`. -/
theorem edwards_q_ne_zero (had : a - d ≠ 0) (h2 : (2 : F) ≠ 0) (ha : IsSquare a) (ha0 : a ≠ 0)
    (hd : ¬ IsSquare d) : u₀ ^ 2 + 2 * (a + d) / (a - d) * u₀ + 1 ≠ 0 := by
  intro hq
  obtain ⟨r, rfl⟩ := ha
  have hr : r ≠ 0 := fun h => ha0 (by rw [h, mul_zero])
  have hrd : r ^ 2 - d ≠ 0 := by rwa [sq]
  have h4 : (4 : F) ≠ 0 := by rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have h16 : (16 : F) ≠ 0 := by rw [show (16 : F) = 4 * 4 by norm_num]; exact mul_ne_zero h4 h4
  apply hd
  set w := 2 * u₀ + 2 * (r * r + d) / (r * r - d)
  have e1 : w ^ 2 = 16 * (r * r) * d / (r * r - d) ^ 2 := by
    have : w ^ 2 = (2 * (r * r + d) / (r * r - d)) ^ 2 - 4 := by linear_combination 4 * hq
    rw [this]
    field_simp
    ring
  refine ⟨w * (r * r - d) / (4 * r), ?_⟩
  have : w * (r * r - d) / (4 * r) * (w * (r * r - d) / (4 * r)) =
      w ^ 2 * (r * r - d) ^ 2 / (16 * (r * r)) := by
    field_simp; ring
  rw [this, e1]
  field_simp

/-- On a complete model, `u = -1` is not the `u`-coordinate of a point. -/
theorem edwards_u_add_one_ne_zero (had : a - d ≠ 0) (h2 : (2 : F) ≠ 0) (hd : ¬ IsSquare d)
    (hm : u₀ ^ 3 + 2 * (a + d) / (a - d) * u₀ ^ 2 + u₀ - 4 / (a - d) * v₀ ^ 2 = 0) :
    u₀ + 1 ≠ 0 := by
  intro hu
  rw [show u₀ = -1 by linear_combination hu] at hm
  apply hd
  refine ⟨v₀, ?_⟩
  have h4 : (4 : F) ≠ 0 := by rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  field_simp at hm
  exact mul_left_cancel₀ h4 (by linear_combination hm)

end Complete

section Geometric

open FunctionField.RationalPlace

variable {a d : F} {had : a - d ≠ 0} {h2 : (2 : F) ≠ 0} [(edwardsRoot a d).IsElliptic]

/-- The point `O` sits at `(0, 1)` on the twisted Edwards model. -/
theorem edwards_coords_zero : (edwards a d had h2).coords 0 = some (0, 1) := by
  set p := (edwardsRoot a d).pointEquivRationalPlace 0
  have hu0 := edwardsU_ne_zero had h2
  have hU : edwardsU a d ∉ p.1.ring := fun h => by
    apply (edwardsRoot a d).fieldX_not_mem_pointEquivRationalPlace_zero
    have := mul_mem h (p.1.algebraMap_mem (4 / (a - d)))
    rwa [edwardsU_def, ← edwardsB_def, div_mul_cancel₀ _ (edwardsB_ne_zero had h2)] at this
  have ht := p.hasValue_inv_of_not_mem hU
  obtain ⟨hq, hx2⟩ := edwards_x_sq (edwardsV_ne_zero had h2) (edwardsB_ne_zero had h2)
    (edwards_montgomery had h2)
  rw [edwards_x_sq_inv hu0 hq] at hx2
  have hB : p.HasValue (edwardsB a d) (4 / (a - d)) :=
    edwardsB_def (a := a) ▸ p.hasValue_algebraMap _
  have hA := p.hasValue_algebraMap (2 * (a + d) / (a - d))
  apply coords_eq_of_hasValue
  · rw [edwards_x]
    apply HasValue.of_sq_zero
    rw [hx2]
    exact ((hB.mul ht).div ((hasValue_one.add (hA.mul ht)).add (ht.pow 2)) (by simp)).congr rfl
      (by simp)
  · rw [edwards_y, edwards_y_inv hu0 (edwardsU_add_one_ne_zero had h2)]
    exact ((hasValue_one.sub ht).div (hasValue_one.add ht) (by simp)).congr rfl (by simp)

/-- On a complete twisted Edwards model, every point is affine. -/
theorem edwards_coords_isSome [hE : (⟨a, d⟩ : TwistedEdwardsModel F).IsComplete]
    (P : (edwards a d had h2).Point) : ∃ c, (edwards a d had h2).coords P = some c := by
  cases P with
  | zero => exact ⟨_, edwards_coords_zero⟩
  | some x₀ y₀ h =>
    obtain ⟨hx, hy, ex, ey⟩ := (edwardsRoot a d).pointEquivRationalPlace_some x₀ y₀ h
    set p := (edwardsRoot a d).pointEquivRationalPlace (.some x₀ y₀ h)
    have hB0 : (4 / (a - d) : F) ≠ 0 :=
      div_ne_zero (by rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2) had
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
    obtain ⟨hq, hx2⟩ := edwards_x_sq (edwardsV_ne_zero had h2) (edwardsB_ne_zero had h2)
      (edwards_montgomery had h2)
    have hX2 := ((hB.mul hU).div (((hU.pow 2).add (hA.mul hU)).add hasValue_one) hq0).congr
      hx2.symm rfl
    obtain ⟨c, hc, -⟩ := hX2.of_sq
    have hY := (hU.sub hasValue_one).div (hU.add hasValue_one) hu1
    rw [← edwards_y (had := had) (h2 := h2)] at hY
    rw [← edwards_x (had := had) (h2 := h2)] at hc
    exact ⟨_, coords_eq_of_hasValue _ hc hY⟩

end Geometric

end PlaneModel
