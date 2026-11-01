/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.TwistedEdwards.Coords.Defs
import all EllipticCurve.TwistedEdwards.Coords.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Twisted Edwards models: coordinate systems, lemmas

The characterising statements about the coordinate systems of
`EllipticCurve.TwistedEdwards.Coords.Defs`: each coordinate in terms of the represented point
(`X_eq_toPoint_x_mul_Z`, …, the form the formula proofs use), the identities and negations
(`onCurve_identity`, `toPoint_identity`, `onCurve_neg`, `toPoint_neg`), projective equality
(`projEq_refl`, `projEq_symm`, `projEq_trans`) and the conversions between the systems
(`onCurve_toProjective`, `toPoint_toProjective`, …): every conversion preserves `OnCurve` and
represents the same point, and `Point.toExtended` is a section of `toPoint`.

Ported from curve25519-dalek's Lean verification
(`Curve25519/Models/TwistedEdwards/Coords/Lemmas.lean`, commit `d2e92e7`), without the Niels
coordinate systems. -/

public section

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] {E : TwistedEdwardsModel F}

/-! ### Extended coordinates -/

namespace Extended

section IsComplete

variable [E.IsComplete] {P : E.Extended}

/-- `X = x Z` for the represented point `(x, y)`. -/
theorem X_eq_toPoint_x_mul_Z (h : P.OnCurve) : P.X = P.toPoint.x * P.Z := by
  rw [toPoint_x h, div_mul_cancel₀ _ h.1]

/-- `Y = y Z` for the represented point `(x, y)`. -/
theorem Y_eq_toPoint_y_mul_Z (h : P.OnCurve) : P.Y = P.toPoint.y * P.Z := by
  rw [toPoint_y h, div_mul_cancel₀ _ h.1]

/-- `T = x y Z` for the represented point `(x, y)`. -/
theorem T_eq_toPoint_mul_Z (h : P.OnCurve) : P.T = P.toPoint.x * P.toPoint.y * P.Z := by
  have key := h.2.1
  rw [X_eq_toPoint_x_mul_Z h, Y_eq_toPoint_y_mul_Z h] at key
  exact mul_left_cancel₀ h.1 (by linear_combination -key)

end IsComplete

/-! #### Identity and negation -/

/-- The identity `(0 : 1 : 1 : 0)` is on the curve. -/
theorem onCurve_identity : (identity : E.Extended).OnCurve := by
  refine ⟨one_ne_zero, ?_, ?_⟩
  · change (0 : F) * 1 = 1 * 0
    ring
  · change E.Equation (0 / 1) (1 / 1)
    rw [zero_div, div_one]
    exact E.equation_zero_one

/-- The identity `(0 : 1 : 1 : 0)` represents `0`. -/
theorem toPoint_identity [E.IsComplete] : (identity : E.Extended).toPoint = 0 := by
  refine Point.ext ?_ ?_
  · rw [toPoint_x onCurve_identity, zero_x]
    exact zero_div 1
  · rw [toPoint_y onCurve_identity, zero_y]
    exact div_one 1

/-- Negation preserves `OnCurve`. -/
theorem onCurve_neg {P : E.Extended} (h : P.OnCurve) : P.neg.OnCurve := by
  refine ⟨h.1, ?_, ?_⟩
  · change -P.X * P.Y = P.Z * -P.T
    linear_combination -h.2.1
  · change E.Equation (-P.X / P.Z) (P.Y / P.Z)
    rw [neg_div]
    exact equation_neg h.2.2

/-- Negation in coordinates is negation of the represented point. -/
theorem toPoint_neg [E.IsComplete] {P : E.Extended} (h : P.OnCurve) :
    P.neg.toPoint = -P.toPoint := by
  refine Point.ext ?_ ?_
  · rw [toPoint_x (onCurve_neg h), neg_x, toPoint_x h]
    exact neg_div _ _
  · rw [toPoint_y (onCurve_neg h), neg_y, toPoint_y h]
    rfl

/-! #### Projective equality -/

/-- `ProjEq` is reflexive. -/
theorem projEq_refl (P : E.Extended) : P.ProjEq P :=
  ⟨rfl, rfl⟩

/-- `ProjEq` is symmetric. -/
theorem projEq_symm {P Q : E.Extended} (h : P.ProjEq Q) : Q.ProjEq P :=
  ⟨h.1.symm, h.2.symm⟩

/-- `ProjEq` is transitive through a point with `Z ≠ 0`. -/
theorem projEq_trans {P Q R : E.Extended} (hQ : Q.Z ≠ 0) (h₁ : P.ProjEq Q) (h₂ : Q.ProjEq R) :
    P.ProjEq R :=
  ⟨mul_right_cancel₀ hQ (by linear_combination R.Z * h₁.1 + P.Z * h₂.1),
    mul_right_cancel₀ hQ (by linear_combination R.Z * h₁.2 + P.Z * h₂.2)⟩

/-! #### Conversions -/

/-- Forgetting `T` preserves `OnCurve`. -/
theorem onCurve_toProjective {P : E.Extended} (h : P.OnCurve) : P.toProjective.OnCurve :=
  ⟨h.1, h.2.2⟩

/-- Forgetting `T` represents the same point. -/
theorem toPoint_toProjective [E.IsComplete] {P : E.Extended} (h : P.OnCurve) :
    P.toProjective.toPoint = P.toPoint := by
  refine Point.ext ?_ ?_
  · rw [Projective.toPoint_x (onCurve_toProjective h), toPoint_x h]
    rfl
  · rw [Projective.toPoint_y (onCurve_toProjective h), toPoint_y h]
    rfl

end Extended

/-! ### Projective coordinates -/

namespace Projective

section IsComplete

variable [E.IsComplete] {P : E.Projective}

/-- `X = x Z` for the represented point `(x, y)`. -/
theorem X_eq_toPoint_x_mul_Z (h : P.OnCurve) : P.X = P.toPoint.x * P.Z := by
  rw [toPoint_x h, div_mul_cancel₀ _ h.1]

/-- `Y = y Z` for the represented point `(x, y)`. -/
theorem Y_eq_toPoint_y_mul_Z (h : P.OnCurve) : P.Y = P.toPoint.y * P.Z := by
  rw [toPoint_y h, div_mul_cancel₀ _ h.1]

end IsComplete

/-- The identity `(0 : 1 : 1)` is on the curve. -/
theorem onCurve_identity : (identity : E.Projective).OnCurve := by
  refine ⟨one_ne_zero, ?_⟩
  change E.Equation (0 / 1) (1 / 1)
  rw [zero_div, div_one]
  exact E.equation_zero_one

/-- The identity `(0 : 1 : 1)` represents `0`. -/
theorem toPoint_identity [E.IsComplete] : (identity : E.Projective).toPoint = 0 := by
  refine Point.ext ?_ ?_
  · rw [toPoint_x onCurve_identity, zero_x]
    exact zero_div 1
  · rw [toPoint_y onCurve_identity, zero_y]
    exact div_one 1

/-- `ProjEq` is reflexive. -/
theorem projEq_refl (P : E.Projective) : P.ProjEq P :=
  ⟨rfl, rfl⟩

/-- `ProjEq` is symmetric. -/
theorem projEq_symm {P Q : E.Projective} (h : P.ProjEq Q) : Q.ProjEq P :=
  ⟨h.1.symm, h.2.symm⟩

/-- `ProjEq` is transitive through a point with `Z ≠ 0`. -/
theorem projEq_trans {P Q R : E.Projective} (hQ : Q.Z ≠ 0) (h₁ : P.ProjEq Q)
    (h₂ : Q.ProjEq R) : P.ProjEq R :=
  ⟨mul_right_cancel₀ hQ (by linear_combination R.Z * h₁.1 + P.Z * h₂.1),
    mul_right_cancel₀ hQ (by linear_combination R.Z * h₁.2 + P.Z * h₂.2)⟩

/-- `(X Z : Y Z : Z² : X Y)` is on the curve when `(X : Y : Z)` is. -/
theorem onCurve_toExtended {P : E.Projective} (h : P.OnCurve) : P.toExtended.OnCurve := by
  refine ⟨pow_ne_zero 2 h.1, ?_, ?_⟩
  · change P.X * P.Z * (P.Y * P.Z) = P.Z ^ 2 * (P.X * P.Y)
    ring
  · change E.Equation (P.X * P.Z / P.Z ^ 2) (P.Y * P.Z / P.Z ^ 2)
    rw [sq, mul_div_mul_right _ _ h.1, mul_div_mul_right _ _ h.1]
    exact h.2

/-- `(X Z : Y Z : Z² : X Y)` represents the same point as `(X : Y : Z)`. -/
theorem toPoint_toExtended [E.IsComplete] {P : E.Projective} (h : P.OnCurve) :
    P.toExtended.toPoint = P.toPoint := by
  refine Point.ext ?_ ?_
  · rw [Extended.toPoint_x (onCurve_toExtended h), toPoint_x h]
    change P.X * P.Z / P.Z ^ 2 = P.X / P.Z
    rw [sq, mul_div_mul_right _ _ h.1]
  · rw [Extended.toPoint_y (onCurve_toExtended h), toPoint_y h]
    change P.Y * P.Z / P.Z ^ 2 = P.Y / P.Z
    rw [sq, mul_div_mul_right _ _ h.1]

end Projective

/-! ### Completed coordinates -/

namespace Completed

section IsComplete

variable [E.IsComplete] {P : E.Completed}

/-- `X = x Z` for the represented point `(x, y)`. -/
theorem X_eq_toPoint_x_mul_Z (h : P.OnCurve) : P.X = P.toPoint.x * P.Z := by
  rw [toPoint_x h, div_mul_cancel₀ _ h.1]

/-- `Y = y T` for the represented point `(x, y)`. -/
theorem Y_eq_toPoint_y_mul_T (h : P.OnCurve) : P.Y = P.toPoint.y * P.T := by
  rw [toPoint_y h, div_mul_cancel₀ _ h.2.1]

end IsComplete

/-- `(X T : Y Z : Z T : X Y)` is on the curve when `((X : Z), (Y : T))` is. -/
theorem onCurve_toExtended {P : E.Completed} (h : P.OnCurve) : P.toExtended.OnCurve := by
  refine ⟨mul_ne_zero h.1 h.2.1, ?_, ?_⟩
  · change P.X * P.T * (P.Y * P.Z) = P.Z * P.T * (P.X * P.Y)
    ring
  · change E.Equation (P.X * P.T / (P.Z * P.T)) (P.Y * P.Z / (P.Z * P.T))
    rw [mul_div_mul_right _ _ h.2.1, mul_comm P.Y P.Z, mul_div_mul_left _ _ h.1]
    exact h.2.2

/-- `(X T : Y Z : Z T : X Y)` represents the same point as `((X : Z), (Y : T))`. -/
theorem toPoint_toExtended [E.IsComplete] {P : E.Completed} (h : P.OnCurve) :
    P.toExtended.toPoint = P.toPoint := by
  refine Point.ext ?_ ?_
  · rw [Extended.toPoint_x (onCurve_toExtended h), toPoint_x h]
    change P.X * P.T / (P.Z * P.T) = P.X / P.Z
    rw [mul_div_mul_right _ _ h.2.1]
  · rw [Extended.toPoint_y (onCurve_toExtended h), toPoint_y h]
    change P.Y * P.Z / (P.Z * P.T) = P.Y / P.T
    rw [mul_comm P.Y P.Z, mul_div_mul_left _ _ h.1]

/-- `(X T : Y Z : Z T)` is on the curve when `((X : Z), (Y : T))` is. -/
theorem onCurve_toProjective {P : E.Completed} (h : P.OnCurve) : P.toProjective.OnCurve := by
  refine ⟨mul_ne_zero h.1 h.2.1, ?_⟩
  change E.Equation (P.X * P.T / (P.Z * P.T)) (P.Y * P.Z / (P.Z * P.T))
  rw [mul_div_mul_right _ _ h.2.1, mul_comm P.Y P.Z, mul_div_mul_left _ _ h.1]
  exact h.2.2

/-- `(X T : Y Z : Z T)` represents the same point as `((X : Z), (Y : T))`. -/
theorem toPoint_toProjective [E.IsComplete] {P : E.Completed} (h : P.OnCurve) :
    P.toProjective.toPoint = P.toPoint := by
  refine Point.ext ?_ ?_
  · rw [Projective.toPoint_x (onCurve_toProjective h), toPoint_x h]
    change P.X * P.T / (P.Z * P.T) = P.X / P.Z
    rw [mul_div_mul_right _ _ h.2.1]
  · rw [Projective.toPoint_y (onCurve_toProjective h), toPoint_y h]
    change P.Y * P.Z / (P.Z * P.T) = P.Y / P.T
    rw [mul_comm P.Y P.Z, mul_div_mul_left _ _ h.1]

end Completed

/-! ### From affine points -/

namespace Point

/-- `(x : y : 1 : x y)` is on the curve. -/
theorem onCurve_toExtended (P : E.Point) : P.toExtended.OnCurve := by
  refine ⟨one_ne_zero, ?_, ?_⟩
  · change P.x * P.y = 1 * (P.x * P.y)
    rw [one_mul]
  · change E.Equation (P.x / 1) (P.y / 1)
    rw [div_one, div_one]
    exact P.equation

/-- `(x : y : 1 : x y)` represents `(x, y)`: `Point.toExtended` is a section of `toPoint`. -/
theorem toPoint_toExtended [E.IsComplete] (P : E.Point) : P.toExtended.toPoint = P := by
  refine Point.ext ?_ ?_
  · rw [Extended.toPoint_x (onCurve_toExtended P)]
    exact div_one P.x
  · rw [Extended.toPoint_y (onCurve_toExtended P)]
    exact div_one P.y

/-- `Point.toExtended` is injective. -/
theorem toExtended_injective : Function.Injective (toExtended (E := E)) := fun _ _ h =>
  Point.ext (congrArg Extended.X h) (congrArg Extended.Y h)

end Point

end TwistedEdwardsModel
