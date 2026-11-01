/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Ring.Parity

/-! # Squares in a commutative group with zero

* a non-square is nonzero (`ne_zero_of_not_isSquare`);
* multiplying by the square of a nonzero element does not change whether an element is a square
  (`isSquare_sq_mul_iff`).

Staged for Mathlib (next to `Mathlib.Algebra.Group.Even`). -/

public section

variable {α : Type*} [CommGroupWithZero α]

/-- `0` is a square, so a non-square is nonzero. -/
theorem ne_zero_of_not_isSquare {c : α} (hc : ¬ IsSquare c) : c ≠ 0 := fun h =>
  hc (h ▸ IsSquare.zero)

/-- Multiplying by the square of a nonzero element does not change whether an element is a
square. -/
theorem isSquare_sq_mul_iff {c x : α} (hc : c ≠ 0) : IsSquare (c ^ 2 * x) ↔ IsSquare x := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r / c, ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hc hc), ← hr, sq, mul_comm]
  · rintro ⟨r, hr⟩
    exact ⟨c * r, by rw [hr, sq, mul_mul_mul_comm]⟩
