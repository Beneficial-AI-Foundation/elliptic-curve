/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # The twisted Edwards addition formula: identities

The identities (closure C1, inverse C3, the Montgomery coordinates) for the complete twisted
Edwards addition law
`(x₁, y₁) + (x₂, y₂) = ((x₁ y₂ + x₂ y₁) / (1 + e), (y₁ y₂ - a x₁ x₂) / (1 - e))`,
`e = d x₁ x₂ y₁ y₂`, over an arbitrary field. -/

public section

namespace TwistedEdwardsFormula

variable {K : Type*} [Field K] {a d x₁ y₁ x₂ y₂ : K}

/-- The first coordinate of the sum. -/
@[expose] def addX (d x₁ y₁ x₂ y₂ : K) : K := (x₁ * y₂ + x₂ * y₁) / (1 + d * x₁ * x₂ * y₁ * y₂)

/-- The second coordinate of the sum. -/
@[expose] def addY (a d x₁ y₁ x₂ y₂ : K) : K :=
  (y₁ * y₂ - a * x₁ * x₂) / (1 - d * x₁ * x₂ * y₁ * y₂)

/-- **C3, first coordinate**: adding `-Q` undoes adding `Q`. -/
theorem addX_addX_neg (h₁ : a * x₁ ^ 2 + y₁ ^ 2 = 1 + d * x₁ ^ 2 * y₁ ^ 2)
    (h₂ : a * x₂ ^ 2 + y₂ ^ 2 = 1 + d * x₂ ^ 2 * y₂ ^ 2)
    (hp : 1 + d * x₁ * x₂ * y₁ * y₂ ≠ 0) (hm : 1 - d * x₁ * x₂ * y₁ * y₂ ≠ 0)
    (hd : 1 + d * addX d x₁ y₁ x₂ y₂ * (-x₂) * addY a d x₁ y₁ x₂ y₂ * y₂ ≠ 0) :
    addX d (addX d x₁ y₁ x₂ y₂) (addY a d x₁ y₁ x₂ y₂) (-x₂) y₂ = x₁ := by
  have key : (x₁ * y₂ + x₂ * y₁) * y₂ * (1 - d * x₁ * x₂ * y₁ * y₂) -
      x₂ * (y₁ * y₂ - a * x₁ * x₂) * (1 + d * x₁ * x₂ * y₁ * y₂) =
      x₁ * ((1 + d * x₁ * x₂ * y₁ * y₂) * (1 - d * x₁ * x₂ * y₁ * y₂) -
        d * x₂ * y₂ * (x₁ * y₂ + x₂ * y₁) * (y₁ * y₂ - a * x₁ * x₂)) := by
    linear_combination (-d * x₁ * x₂ ^ 2 * y₂ ^ 2) * h₁ + x₁ * h₂
  set e := d * x₁ * x₂ * y₁ * y₂
  set x₃ := addX d x₁ y₁ x₂ y₂
  set y₃ := addY a d x₁ y₁ x₂ y₂
  have hx₃ : x₃ * (1 + e) = x₁ * y₂ + x₂ * y₁ := div_mul_cancel₀ _ hp
  have hy₃ : y₃ * (1 - e) = y₁ * y₂ - a * x₁ * x₂ := div_mul_cancel₀ _ hm
  rw [show addX d x₃ y₃ (-x₂) y₂ = (x₃ * y₂ + -x₂ * y₃) / (1 + d * x₃ * -x₂ * y₃ * y₂) from rfl,
    div_eq_iff hd]
  apply mul_left_cancel₀ (mul_ne_zero hp hm)
  linear_combination key + (y₂ * (1 - e) + x₁ * d * x₂ * y₂ * y₃ * (1 - e)) * hx₃ +
    (-x₂ * (1 + e) + x₁ * d * x₂ * y₂ * (x₁ * y₂ + x₂ * y₁)) * hy₃

/-- **C3, second coordinate**. -/
theorem addY_addX_neg (h₁ : a * x₁ ^ 2 + y₁ ^ 2 = 1 + d * x₁ ^ 2 * y₁ ^ 2)
    (h₂ : a * x₂ ^ 2 + y₂ ^ 2 = 1 + d * x₂ ^ 2 * y₂ ^ 2)
    (hp : 1 + d * x₁ * x₂ * y₁ * y₂ ≠ 0) (hm : 1 - d * x₁ * x₂ * y₁ * y₂ ≠ 0)
    (hd : 1 - d * addX d x₁ y₁ x₂ y₂ * (-x₂) * addY a d x₁ y₁ x₂ y₂ * y₂ ≠ 0) :
    addY a d (addX d x₁ y₁ x₂ y₂) (addY a d x₁ y₁ x₂ y₂) (-x₂) y₂ = y₁ := by
  have key : (y₁ * y₂ - a * x₁ * x₂) * y₂ * (1 + d * x₁ * x₂ * y₁ * y₂) +
      a * (x₁ * y₂ + x₂ * y₁) * x₂ * (1 - d * x₁ * x₂ * y₁ * y₂) =
      y₁ * ((1 + d * x₁ * x₂ * y₁ * y₂) * (1 - d * x₁ * x₂ * y₁ * y₂) +
        d * x₂ * y₂ * (x₁ * y₂ + x₂ * y₁) * (y₁ * y₂ - a * x₁ * x₂)) := by
    linear_combination (-d * x₂ ^ 2 * y₁ * y₂ ^ 2) * h₁ + y₁ * h₂
  set e := d * x₁ * x₂ * y₁ * y₂
  set x₃ := addX d x₁ y₁ x₂ y₂
  set y₃ := addY a d x₁ y₁ x₂ y₂
  have hx₃ : x₃ * (1 + e) = x₁ * y₂ + x₂ * y₁ := div_mul_cancel₀ _ hp
  have hy₃ : y₃ * (1 - e) = y₁ * y₂ - a * x₁ * x₂ := div_mul_cancel₀ _ hm
  rw [show addY a d x₃ y₃ (-x₂) y₂ = (y₃ * y₂ - a * x₃ * -x₂) / (1 - d * x₃ * -x₂ * y₃ * y₂)
    from rfl, div_eq_iff hd]
  apply mul_left_cancel₀ (mul_ne_zero hp hm)
  linear_combination key + ((1 - e) * a * x₂ - y₁ * d * x₂ * y₂ * (y₁ * y₂ - a * x₁ * x₂)) * hx₃ +
    ((1 + e) * y₂ - y₁ * d * x₂ * y₂ * x₃ * (1 + e)) * hy₃

/-- **C1, closure**: the sum of two points of the curve is on the curve. -/
theorem equation_add (h₁ : a * x₁ ^ 2 + y₁ ^ 2 = 1 + d * x₁ ^ 2 * y₁ ^ 2)
    (h₂ : a * x₂ ^ 2 + y₂ ^ 2 = 1 + d * x₂ ^ 2 * y₂ ^ 2)
    (hp : 1 + d * x₁ * x₂ * y₁ * y₂ ≠ 0) (hm : 1 - d * x₁ * x₂ * y₁ * y₂ ≠ 0) :
    a * addX d x₁ y₁ x₂ y₂ ^ 2 + addY a d x₁ y₁ x₂ y₂ ^ 2 =
      1 + d * addX d x₁ y₁ x₂ y₂ ^ 2 * addY a d x₁ y₁ x₂ y₂ ^ 2 := by
  set e := d * x₁ * x₂ * y₁ * y₂
  set NX := x₁ * y₂ + x₂ * y₁
  set NY := y₁ * y₂ - a * x₁ * x₂
  set x₃ := addX d x₁ y₁ x₂ y₂
  set y₃ := addY a d x₁ y₁ x₂ y₂
  have hx₃ : x₃ * (1 + e) = NX := div_mul_cancel₀ _ hp
  have hy₃ : y₃ * (1 - e) = NY := div_mul_cancel₀ _ hm
  -- With `uᵢ = xᵢ yᵢ`, `sᵢ = a xᵢ² + yᵢ²`: `y + x √-a` multiplies, so `a NX² + NY² = s₁ s₂`
  -- (norm), and with `a NX² - NY² = 4 a u₁ u₂ - w₁ w₂`, `NX NY = u₁ w₂ + u₂ w₁`
  -- (`wᵢ = yᵢ² - a xᵢ²`, `sᵢ² - wᵢ² = 4 a uᵢ²`) the cleared equation is a ring identity in
  -- `s₁, s₂, d u₁², d u₂²`; the curve equations say `d uᵢ² = sᵢ - 1`.
  have hred : a * NX ^ 2 * (1 - e) ^ 2 + NY ^ 2 * (1 + e) ^ 2 - (1 + e) ^ 2 * (1 - e) ^ 2 -
      d * NX ^ 2 * NY ^ 2 =
      (1 + e ^ 2) * (a * x₁ ^ 2 + y₁ ^ 2) * (a * x₂ ^ 2 + y₂ ^ 2) -
        d * (x₂ * y₂) ^ 2 * (a * x₁ ^ 2 + y₁ ^ 2) ^ 2 -
        d * (x₁ * y₁) ^ 2 * (a * x₂ ^ 2 + y₂ ^ 2) ^ 2 - (1 - e ^ 2) ^ 2 := by
    simp only [e, NX, NY]; ring
  have hp₁ : d * (x₁ * y₁) ^ 2 = (a * x₁ ^ 2 + y₁ ^ 2) - 1 := by
    linear_combination -h₁
  have hp₂ : d * (x₂ * y₂) ^ 2 = (a * x₂ ^ 2 + y₂ ^ 2) - 1 := by
    linear_combination -h₂
  have he : e ^ 2 = ((a * x₁ ^ 2 + y₁ ^ 2) - 1) * ((a * x₂ ^ 2 + y₂ ^ 2) - 1) := by
    rw [← hp₁, ← hp₂]; simp only [e]; ring
  have key : a * NX ^ 2 * (1 - e) ^ 2 + NY ^ 2 * (1 + e) ^ 2 - (1 + e) ^ 2 * (1 - e) ^ 2 -
      d * NX ^ 2 * NY ^ 2 = 0 := by
    rw [hred, he, hp₁, hp₂]; ring
  apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 hp) (pow_ne_zero 2 hm))
  linear_combination key +
    (a * (1 - e) ^ 2 - d * (y₃ * (1 - e)) ^ 2) * (x₃ * (1 + e) + NX) * hx₃ +
    ((1 + e) ^ 2 - d * NX ^ 2) * (y₃ * (1 - e) + NY) * hy₃

/-- **The Montgomery coordinates of a point of the Edwards curve**: `U = (1 + y) / (1 - y)` and
`V = U / x` satisfy `B V² = U³ + A U² + U` with `A = 2 (a + d) / (a - d)`, `B = 4 / (a - d)`. -/
theorem montgomery_of_edwards {x y : K} (h : a * x ^ 2 + y ^ 2 = 1 + d * x ^ 2 * y ^ 2)
    (had : a - d ≠ 0) (hx : x ≠ 0) (hy : 1 - y ≠ 0) :
    4 / (a - d) * ((1 + y) / (1 - y) / x) ^ 2 =
      ((1 + y) / (1 - y)) ^ 3 + 2 * (a + d) / (a - d) * ((1 + y) / (1 - y)) ^ 2 +
        (1 + y) / (1 - y) := by
  have hy' : y - 1 ≠ 0 := fun h0 => hy (by linear_combination -h0)
  field_simp
  linear_combination (-4 * (y + 1)) * h

end TwistedEdwardsFormula
