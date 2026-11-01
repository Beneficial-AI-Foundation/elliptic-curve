/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Weierstrass.TranslationPlaces
import EllipticCurve.Weierstrass.Normal

/-! # The generic point

Two facts about the generic point `ξ = (x, y)` of `W` over its function field:
* a change of variables with coefficients in `F` fixing `ξ` is the identity
  (`eq_one_of_fix_generic`);
* for a point `P₀ ≠ 0` over `F`, the `x`-coordinate of `ξ + P₀` has a pole at the place of
  `-P₀` (`transX_not_mem`), so it is not of the form `u² x + r`. -/

public section

universe u

open Polynomial

namespace WeierstrassCurve.Affine

variable {L : Type u} [Field L] {W : WeierstrassCurve.Affine L}

/-- A linear polynomial `a X + b` vanishes only when `a = b = 0`. -/
theorem eq_zero_of_C_mul_X_add_C {a b : L} (h : C a * X + C b = 0) : a = 0 ∧ b = 0 :=
  ⟨by simpa using congrArg (coeff · 1) h, by simpa using congrArg (coeff · 0) h⟩

/-- **A change of variables over `L` fixing the generic point is the identity.** -/
theorem eq_one_of_fix_generic {u r s t : L}
    (hx : algebraMap L W.FunctionField u ^ 2 * W.fieldX + algebraMap L _ r = W.fieldX)
    (hy : algebraMap L W.FunctionField u ^ 3 * W.fieldY +
      algebraMap L _ u ^ 2 * algebraMap L _ s * W.fieldX + algebraMap L _ t = W.fieldY) :
    u = 1 ∧ r = 0 ∧ s = 0 ∧ t = 0 := by
  have h1 := (W.eq_zero_of_aeval_add_aeval_mul_fieldY (p := C (u ^ 2 - 1) * X + C r) (q := 0)
    (by simp only [map_add, map_mul, map_sub, map_pow, aeval_C, aeval_X, map_one, map_zero,
      zero_mul, add_zero]; linear_combination hx)).1
  have h2 := W.eq_zero_of_aeval_add_aeval_mul_fieldY (p := C (u ^ 2 * s) * X + C t)
    (q := C (u ^ 3 - 1)) (by
      simp only [map_add, map_mul, map_sub, map_pow, aeval_C, aeval_X, map_one]
      linear_combination hy)
  obtain ⟨hu2, hr⟩ := eq_zero_of_C_mul_X_add_C h1
  obtain ⟨hus, ht⟩ := eq_zero_of_C_mul_X_add_C h2.1
  have hu3 : u ^ 3 - 1 = 0 := Polynomial.C_eq_zero.mp h2.2
  have hu : u = 1 := by linear_combination hu3 - u * hu2
  refine ⟨hu, hr, ?_, ht⟩
  rw [hu, one_pow, one_mul] at hus
  exact hus

variable [W.IsElliptic]

open Classical in
/-- **The translate of the generic point by `P₀` has a pole at `-P₀`**: `x(ξ + P₀)` is not
regular at the place of `-P₀`. -/
theorem transX_not_mem (P₀ : W.Point) :
    transX (W.toBaseChange P₀) ∉ (W.pointEquivRationalPlace (-P₀)).1.ring := by
  intro h
  have key := pointEquivRationalPlace_symm_congr_translationEquiv P₀ (-P₀)
  rw [neg_add_cancel, Equiv.symm_apply_eq] at key
  apply W.fieldX_not_mem_pointEquivRationalPlace_zero
  rw [← key, FunctionField.RationalPlace.congr_apply_ring, translationEquiv_apply,
    translation_fieldX]
  exact h

end WeierstrassCurve.Affine
