/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.TwistedEdwards.Defs
import all EllipticCurve.TwistedEdwards.Defs
import EllipticCurve.PlaneModel.EdwardsFormula
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Twisted Edwards models: the addition formula

Properties of the addition formula `addX`, `addY` of a twisted Edwards model: completeness (on a
complete model the denominators never vanish, `addDen₁_ne_zero`, `addDen₂_ne_zero`), closure
(`equation_addX_addY`, from the identity C1 of `EllipticCurve.PlaneModel.EdwardsFormula`),
symmetry, and the effect of the points `(0, ±1)`. That the formula is the group law is
`add_eq_mk` (`EllipticCurve.TwistedEdwards.Lemmas`).

The completeness argument `d_mul_sq_ne_one` is Bernstein–Birkner–Joye–Lange–Peters' as formalised
in FEC `EllipticCurves/Messy/Edwards/AddFormulaBase.lean` (`lam_sq_ne_one`). -/

public section

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] {E : TwistedEdwardsModel F}

/-! ### Completeness and closure of the addition formula -/

/-- Completeness: `λ = d x₁ x₂ y₁ y₂` satisfies `λ² ≠ 1` for two points of a complete model,
since `λ² = 1` would exhibit `d` as a square (BBJLP; after FEC `lam_sq_ne_one`). -/
theorem d_mul_sq_ne_one [E.IsComplete] {x₁ y₁ x₂ y₂ : F} (h1 : E.Equation x₁ y₁)
    (h2 : E.Equation x₂ y₂) : (E.d * x₁ * x₂ * y₁ * y₂) ^ 2 ≠ 1 := by
  unfold Equation at h1 h2
  intro hLamSq
  have hlamne : E.d * x₁ * x₂ * y₁ * y₂ ≠ 0 := by
    intro h
    rw [h] at hLamSq
    norm_num at hLamSq
  have hx1 : x₁ ≠ 0 := fun h => hlamne (by rw [h]; ring)
  have hy1 : y₁ ≠ 0 := fun h => hlamne (by rw [h]; ring)
  have hx2 : x₂ ≠ 0 := fun h => hlamne (by rw [h]; ring)
  obtain ⟨a', ha'⟩ := IsComplete.isSquare_a (E := E)
  have ha'0 : a' ≠ 0 := fun h => IsComplete.a_ne_zero (E := E) (by rw [ha', h]; ring)
  have lem1 : E.d * x₁ ^ 2 * y₁ ^ 2 * (E.a * x₂ ^ 2 + y₂ ^ 2) = E.a * x₁ ^ 2 + y₁ ^ 2 := by
    linear_combination E.d * x₁ ^ 2 * y₁ ^ 2 * h2 + hLamSq - h1
  have lem2 : (a' * x₁ + E.d * x₁ * x₂ * y₁ * y₂ * y₁) ^ 2 =
      E.d * x₁ ^ 2 * y₁ ^ 2 * (a' * x₂ + y₂) ^ 2 := by
    linear_combination (E.d * x₁ ^ 2 * y₁ ^ 2 * x₂ ^ 2 - x₁ ^ 2) * ha' + y₁ ^ 2 * hLamSq - lem1
  by_cases hcasePos : a' * x₂ + y₂ = 0
  · by_cases hcaseNeg : a' * x₂ - y₂ = 0
    · have h2x : 2 * a' * x₂ = 0 := by linear_combination hcasePos + hcaseNeg
      exact hx2 ((mul_eq_zero.mp h2x).resolve_left
        (mul_ne_zero (IsComplete.two_ne_zero (E := E)) ha'0))
    · exact IsComplete.not_isSquare_d (E := E)
        ⟨(a' * x₁ - E.d * x₁ * x₂ * y₁ * y₂ * y₁) / (x₁ * y₁ * (a' * x₂ - y₂)), by
          rw [← sq, div_pow,
            eq_div_iff (pow_ne_zero _ (mul_ne_zero (mul_ne_zero hx1 hy1) hcaseNeg))]
          linear_combination -lem2⟩
  · exact IsComplete.not_isSquare_d (E := E)
      ⟨(a' * x₁ + E.d * x₁ * x₂ * y₁ * y₂ * y₁) / (x₁ * y₁ * (a' * x₂ + y₂)), by
        rw [← sq, div_pow,
          eq_div_iff (pow_ne_zero _ (mul_ne_zero (mul_ne_zero hx1 hy1) hcasePos))]
        linear_combination -lem2⟩

/-- The denominator `1 + d x₁ x₂ y₁ y₂` is nonzero on a complete model. -/
theorem addDen₁_ne_zero [E.IsComplete] (P Q : E.Point) : addDen₁ P Q ≠ 0 := fun h =>
  d_mul_sq_ne_one P.equation Q.equation (by
    unfold addDen₁ at h
    linear_combination (E.d * P.x * Q.x * P.y * Q.y - 1) * h)

/-- The denominator `1 - d x₁ x₂ y₁ y₂` is nonzero on a complete model. -/
theorem addDen₂_ne_zero [E.IsComplete] (P Q : E.Point) : addDen₂ P Q ≠ 0 := fun h =>
  d_mul_sq_ne_one P.equation Q.equation (by
    unfold addDen₂ at h
    linear_combination -(E.d * P.x * Q.x * P.y * Q.y + 1) * h)

/-- Closure: the sum of two points of a complete model is on the model (identity C1). -/
theorem equation_addX_addY [E.IsComplete] (P Q : E.Point) :
    E.Equation (addX P Q) (addY P Q) := by
  have h := TwistedEdwardsFormula.equation_add P.equation Q.equation (addDen₁_ne_zero P Q)
    (addDen₂_ne_zero P Q)
  unfold Equation
  convert h using 2 <;> simp [addX, addY, addDen₁, addDen₂, TwistedEdwardsFormula.addX,
    TwistedEdwardsFormula.addY]

/-- The addition formula is commutative: `x`-coordinate. -/
theorem addX_comm (P Q : E.Point) : addX P Q = addX Q P := by
  unfold addX addDen₁
  ring

/-- The addition formula is commutative: `y`-coordinate. -/
theorem addY_comm (P Q : E.Point) : addY P Q = addY Q P := by
  unfold addY addDen₂
  ring

/-- Adding `(0, 1)` on the left: `x`-coordinate. -/
theorem addX_of_x_eq_zero_of_y_eq_one {P : E.Point} (Q : E.Point) (hx : P.x = 0)
    (hy : P.y = 1) : addX P Q = Q.x := by
  simp [addX, addDen₁, hx, hy]

/-- Adding `(0, 1)` on the left: `y`-coordinate. -/
theorem addY_of_x_eq_zero_of_y_eq_one {P : E.Point} (Q : E.Point) (hx : P.x = 0)
    (hy : P.y = 1) : addY P Q = Q.y := by
  simp [addY, addDen₂, hx, hy]

/-- Adding `(0, -1)` on the left: `x`-coordinate. -/
theorem addX_of_x_eq_zero_of_y_eq_neg_one {P : E.Point} (Q : E.Point) (hx : P.x = 0)
    (hy : P.y = -1) : addX P Q = -Q.x := by
  simp [addX, addDen₁, hx, hy]

/-- Adding `(0, -1)` on the left: `y`-coordinate. -/
theorem addY_of_x_eq_zero_of_y_eq_neg_one {P : E.Point} (Q : E.Point) (hx : P.x = 0)
    (hy : P.y = -1) : addY P Q = -Q.y := by
  simp [addY, addDen₂, hx, hy]

end TwistedEdwardsModel
