/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-! # Weierstrass curves with given invariants

`WeierstrassCurve.ofC₄C₆ c₄ c₆` is the short Weierstrass curve `Y² = X³ - 27 c₄ X - 54 c₆`, whose
invariants are `6⁴ c₄` and `6⁶ c₆` (`ofC₄C₆_c₄`, `ofC₄C₆_c₆`): up to the scaling by `6`, every
pair `(c₄, c₆)` is realised, without dividing by `2` or `3`. Its discriminant is
`6¹² (c₄³ - c₆²) / 1728 = 2⁶ 3⁹ (c₄³ - c₆²)` (`ofC₄C₆_Δ`).

Staged for Mathlib (next to `Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ`). -/

public section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-- The Weierstrass curve `Y² = X³ - 27 c₄ X - 54 c₆`, with invariants `6⁴ c₄` and `6⁶ c₆`. -/
@[expose] def ofC₄C₆ (c₄ c₆ : R) : WeierstrassCurve R :=
  ⟨0, 0, 0, -27 * c₄, -54 * c₆⟩

variable (c₄ c₆ : R)

/-- The invariant `c₄` of `ofC₄C₆ c₄ c₆` is `6⁴ c₄`. -/
@[simp] theorem ofC₄C₆_c₄ : (ofC₄C₆ c₄ c₆).c₄ = 6 ^ 4 * c₄ := by
  simp only [ofC₄C₆, WeierstrassCurve.c₄, b₂, b₄]; ring

/-- The invariant `c₆` of `ofC₄C₆ c₄ c₆` is `6⁶ c₆`. -/
@[simp] theorem ofC₄C₆_c₆ : (ofC₄C₆ c₄ c₆).c₆ = 6 ^ 6 * c₆ := by
  simp only [ofC₄C₆, WeierstrassCurve.c₆, b₂, b₄, b₆]; ring

/-- The discriminant of `ofC₄C₆ c₄ c₆` is `2⁶ 3⁹ (c₄³ - c₆²) = 6¹² (c₄³ - c₆²) / 1728`. -/
theorem ofC₄C₆_Δ : (ofC₄C₆ c₄ c₆).Δ = 2 ^ 6 * 3 ^ 9 * (c₄ ^ 3 - c₆ ^ 2) := by
  simp only [ofC₄C₆, Δ, b₂, b₄, b₆, b₈]; ring

/-- `ofC₄C₆ c₄ c₆` is elliptic when `6` and `c₄³ - c₆²` are units. -/
theorem isElliptic_ofC₄C₆ (h6 : IsUnit (6 : R)) (h : IsUnit (c₄ ^ 3 - c₆ ^ 2)) :
    (ofC₄C₆ c₄ c₆).IsElliptic where
  isUnit := by
    have h6' : (6 : R) = 2 * 3 := by norm_num
    rw [h6'] at h6
    rw [ofC₄C₆_Δ]
    exact (((isUnit_of_mul_isUnit_left h6).pow 6).mul
      ((isUnit_of_mul_isUnit_right h6).pow 9)).mul h

/-- The invariants of an elliptic curve over a field with `1728 ≠ 0` are nondegenerate:
`c₄³ - c₆² = 1728 Δ`. -/
theorem c₄_cube_sub_c₆_sq_ne_zero {K : Type*} [Field K] [NeZero (1728 : K)]
    (W : WeierstrassCurve K) [W.IsElliptic] : W.c₄ ^ 3 - W.c₆ ^ 2 ≠ 0 := by
  rw [← W.c_relation]
  exact mul_ne_zero (NeZero.ne _) W.isUnit_Δ.ne_zero

end WeierstrassCurve
