/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Ring.Parity

/-! # Squares under multiplication by a square

* a non-square is nonzero (`ne_zero_of_not_isSquare`);
* multiplying by the square of a unit, or of a nonzero element of a commutative group with zero,
  does not change whether an element is a square (`IsUnit.isSquare_sq_mul_iff`,
  `isSquare_sq_mul_iff`).

Staged for Mathlib, next to `IsSquare.zero` in `Mathlib.Algebra.Ring.Parity`. -/

public section

variable {α : Type*}

/-- `0` is a square, so a non-square is nonzero. -/
theorem ne_zero_of_not_isSquare [MulZeroClass α] {c : α} (hc : ¬ IsSquare c) : c ≠ 0 :=
  fun h => hc (h ▸ IsSquare.zero)

/-- Multiplying by the square of a unit does not change whether an element is a square. -/
theorem IsUnit.isSquare_sq_mul_iff [CommMonoid α] {c x : α} (hc : IsUnit c) :
    IsSquare (c ^ 2 * x) ↔ IsSquare x := by
  obtain ⟨u, rfl⟩ := hc
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨↑u⁻¹ * r, ?_⟩
    rw [mul_mul_mul_comm, ← hr, sq, mul_assoc, mul_assoc, Units.inv_mul_cancel_left,
      Units.inv_mul_cancel_left]
  · rintro ⟨r, hr⟩
    exact ⟨u * r, by rw [hr, sq, mul_mul_mul_comm]⟩

/-- Multiplying by the square of a nonzero element does not change whether an element is a
square. -/
theorem isSquare_sq_mul_iff [CommGroupWithZero α] {c x : α} (hc : c ≠ 0) :
    IsSquare (c ^ 2 * x) ↔ IsSquare x :=
  hc.isUnit.isSquare_sq_mul_iff
