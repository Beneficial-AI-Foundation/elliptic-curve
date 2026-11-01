/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Weierstrass.Normal
public import EllipticCurve.Weierstrass.Infinity
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # Functions with poles only at infinity

Tools for (B-W): a function regular at every place where `x` is regular is integral over `F[x]`
(`isIntegral_of_forall_mem`), hence in the coordinate ring away from 2; the functions of norm
degree `2` and `3` there are `c₁ x + c₀` and `c y + p₁ x + p₀`. -/

public section

universe u

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] (W : WeierstrassCurve.Affine F)

/-- Where `x` is regular, so is `y`. -/
theorem fieldY_mem_of_fieldX_mem' {O : ValuationSubring W.FunctionField}
    (hO : ∀ c : F, algebraMap F _ c ∈ O) (hx : W.fieldX ∈ O) : W.fieldY ∈ O := by
  by_contra hy
  have hinv : W.fieldY⁻¹ ∈ O := (O.mem_or_inv_mem _).resolve_left hy
  have hr : W.fieldX ^ 3 + algebraMap F _ W.a₂ * W.fieldX ^ 2 + algebraMap F _ W.a₄ * W.fieldX +
      algebraMap F _ W.a₆ ∈ O :=
    add_mem (add_mem (add_mem (pow_mem hx 3) (mul_mem (hO _) (pow_mem hx 2)))
      (mul_mem (hO _) hx)) (hO _)
  have hl : algebraMap F _ W.a₁ * W.fieldX + algebraMap F _ W.a₃ ∈ O :=
    add_mem (mul_mem (hO _) hx) (hO _)
  have hy0 := W.fieldY_ne_zero
  have e : W.fieldY = (W.fieldX ^ 3 + algebraMap F _ W.a₂ * W.fieldX ^ 2 +
      algebraMap F _ W.a₄ * W.fieldX + algebraMap F _ W.a₆) * W.fieldY⁻¹ -
        (algebraMap F _ W.a₁ * W.fieldX + algebraMap F _ W.a₃) := by
    rw [← W.fieldY_equation]
    field_simp
    ring
  exact hy (e ▸ sub_mem (mul_mem hr hinv) hl)

/-- A function in every valuation subring where `x` is regular is integral over `F[x]`. -/
theorem isIntegral_of_forall_mem {f : W.FunctionField}
    (hf : ∀ V : ValuationSubring W.FunctionField, (∀ c : F, algebraMap F _ c ∈ V) →
      W.fieldX ∈ V → f ∈ V) : IsIntegral F[X] f := by
  by_contra hint
  set R := (integralClosure F[X] W.FunctionField).toSubring
  have hfR : f ∉ R := hint
  obtain ⟨V, hRV, hfV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hfR
  apply hfV
  refine hf V (fun c => hRV ?_) (hRV ?_)
  · rw [IsScalarTower.algebraMap_apply F F[X] W.FunctionField]
    exact (integralClosure F[X] W.FunctionField).algebraMap_mem _
  · have : W.fieldX = algebraMap F[X] W.FunctionField X := by
      rw [algebraMap_polynomial_eq, aeval_X]
    rw [this]
    exact (integralClosure F[X] W.FunctionField).algebraMap_mem _

/-! ### Norm degrees -/

/-- The norm degree of `x` is `2`. -/
theorem natDegree_norm_X :
    (Algebra.norm F[X] (CoordinateRing.mk W (C X))).natDegree = 2 := by
  have h : CoordinateRing.mk W (C X) = (X : F[X]) • (1 : W.CoordinateRing) +
      (0 : F[X]) • CoordinateRing.mk W X := by
    rw [zero_smul, add_zero, CoordinateRing.smul, mul_one]
  rw [h, natDegree_norm_smul_basis (.inl X_ne_zero)]
  simp

/-- The norm degree of `y` is `3`. -/
theorem natDegree_norm_Y :
    (Algebra.norm F[X] (CoordinateRing.mk W X)).natDegree = 3 := by
  have h : CoordinateRing.mk W X = (0 : F[X]) • (1 : W.CoordinateRing) +
      (1 : F[X]) • CoordinateRing.mk W X := by
    rw [zero_smul, zero_add, one_smul]
  rw [h, natDegree_norm_smul_basis (.inr one_ne_zero)]
  simp

/-- The norm degree is additive on powers. -/
theorem natDegree_norm_pow (r : W.CoordinateRing) (n : ℕ) :
    (Algebra.norm F[X] (r ^ n)).natDegree = n * (Algebra.norm F[X] r).natDegree := by
  rw [map_pow, natDegree_pow]

/-! ### Functions of norm degree `2` and `3` -/

/-- An element of norm degree `2` is `c₁ x + c₀` with `c₁ ≠ 0`. -/
theorem exists_eq_of_natDegree_norm_eq_two {r : W.CoordinateRing}
    (h : (Algebra.norm F[X] r).natDegree = 2) : ∃ c₁ c₀ : F, c₁ ≠ 0 ∧
      algebraMap W.CoordinateRing W.FunctionField r =
        algebraMap F _ c₁ * W.fieldX + algebraMap F _ c₀ := by
  classical
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq r
  obtain ⟨hp, hq⟩ := natDegree_le_natDegree_norm (W := W) p q
  have hq0 : q = 0 := by
    by_contra hq0; have := hq hq0; omega
  subst hq0
  have : Module.Finite F[X] W.CoordinateRing := .of_basis (CoordinateRing.basis W)
  have hp0 : p ≠ 0 := by
    rintro rfl; simp [Algebra.norm_zero] at h
  rw [natDegree_norm_smul_basis (.inl hp0)] at h
  simp only [↓reduceIte] at h
  have hp1 : p.natDegree = 1 := by omega
  have hpe := eq_X_add_C_of_natDegree_le_one hp1.le
  set a := p.coeff 1
  set b := p.coeff 0
  refine ⟨a, b, ?_, ?_⟩
  · rw [show a = p.leadingCoeff by rw [leadingCoeff, hp1]]; exact leadingCoeff_ne_zero.mpr hp0
  · rw [algebraMap_smul_basis, map_zero, zero_mul, add_zero, hpe]
    simp

/-- An element of norm degree `3` is `c y + p₁ x + p₀` with `c ≠ 0`. -/
theorem exists_eq_of_natDegree_norm_eq_three {r : W.CoordinateRing}
    (h : (Algebra.norm F[X] r).natDegree = 3) : ∃ c p₁ p₀ : F, c ≠ 0 ∧
      algebraMap W.CoordinateRing W.FunctionField r =
        algebraMap F _ c * W.fieldY + algebraMap F _ p₁ * W.fieldX + algebraMap F _ p₀ := by
  classical
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq r
  obtain ⟨hp, hq⟩ := natDegree_le_natDegree_norm (W := W) p q
  have : Module.Finite F[X] W.CoordinateRing := .of_basis (CoordinateRing.basis W)
  have hq0 : q ≠ 0 := by
    rintro rfl
    by_cases hp0 : p = 0
    · subst hp0; simp [Algebra.norm_zero] at h
    rw [natDegree_norm_smul_basis (.inl hp0)] at h
    simp only [↓reduceIte] at h
    omega
  have hq' := hq hq0
  have hqdeg : q.natDegree = 0 := by omega
  have hpdeg : p.natDegree ≤ 1 := by omega
  have hpe := eq_X_add_C_of_natDegree_le_one hpdeg
  have hqe := eq_C_of_natDegree_eq_zero hqdeg
  set a := p.coeff 1
  set b := p.coeff 0
  set c := q.coeff 0
  refine ⟨c, a, b, ?_, ?_⟩
  · rw [show c = q.leadingCoeff by rw [leadingCoeff, hqdeg]]; exact leadingCoeff_ne_zero.mpr hq0
  · rw [algebraMap_smul_basis, hpe, hqe]
    simp only [map_add, map_mul, aeval_C, aeval_X]
    ring

/-! ### Recognising a change of variables -/

variable {W} in
/-- If `ξ = c₁ x' + c₀` and `η = c y' + p₁ x' + p₀` satisfy the equation of `W` in the function
field of `W'`, then `c² = c₁³` (compare the coefficients of `x'³`). -/
theorem sq_eq_cube_of_equation (W' : WeierstrassCurve.Affine F) {c c₁ c₀ p₁ p₀ : F}
    (h : (algebraMap F W'.FunctionField c * W'.fieldY + algebraMap F _ p₁ * W'.fieldX +
        algebraMap F _ p₀) ^ 2 +
      algebraMap F _ W.a₁ * (algebraMap F _ c₁ * W'.fieldX + algebraMap F _ c₀) *
        (algebraMap F _ c * W'.fieldY + algebraMap F _ p₁ * W'.fieldX + algebraMap F _ p₀) +
      algebraMap F _ W.a₃ * (algebraMap F _ c * W'.fieldY + algebraMap F _ p₁ * W'.fieldX +
        algebraMap F _ p₀) =
      (algebraMap F _ c₁ * W'.fieldX + algebraMap F _ c₀) ^ 3 +
        algebraMap F _ W.a₂ * (algebraMap F _ c₁ * W'.fieldX + algebraMap F _ c₀) ^ 2 +
        algebraMap F _ W.a₄ * (algebraMap F _ c₁ * W'.fieldX + algebraMap F _ c₀) +
        algebraMap F _ W.a₆) :
    c ^ 2 = c₁ ^ 3 := by
  set A : F[X] := C (c ^ 2 - c₁ ^ 3) * X ^ 3 +
    C (c ^ 2 * W'.a₂ + p₁ ^ 2 + W.a₁ * c₁ * p₁ - 3 * c₁ ^ 2 * c₀ - W.a₂ * c₁ ^ 2) * X ^ 2 +
    C (c ^ 2 * W'.a₄ + 2 * p₁ * p₀ + W.a₁ * (c₁ * p₀ + c₀ * p₁) + W.a₃ * p₁ - 3 * c₁ * c₀ ^ 2 -
      2 * W.a₂ * c₁ * c₀ - W.a₄ * c₁) * X +
    C (c ^ 2 * W'.a₆ + p₀ ^ 2 + W.a₁ * c₀ * p₀ + W.a₃ * p₀ - c₀ ^ 3 - W.a₂ * c₀ ^ 2 - W.a₄ * c₀ -
      W.a₆)
  set B : F[X] := C (-c ^ 2 * W'.a₁ + 2 * c * p₁ + W.a₁ * c * c₁) * X +
    C (-c ^ 2 * W'.a₃ + 2 * c * p₀ + W.a₁ * c * c₀ + W.a₃ * c)
  have hAB : aeval W'.fieldX A + aeval W'.fieldX B * W'.fieldY = 0 := by
    have hy := W'.fieldY_sq_add
    simp only [A, B, linY, cubicX, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat,
      aeval_C, aeval_X] at hy h ⊢
    linear_combination h - (algebraMap F W'.FunctionField c) ^ 2 * hy
  have h3 := congrArg (coeff · 3) (W'.eq_zero_of_aeval_add_aeval_mul_fieldY hAB).1
  simp only [A, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at h3
  norm_num at h3
  linear_combination h3

variable {W} in
/-- If `ξ = u² x' + r` and `η = u³ y' + u² s x' + t` satisfy the equation of `W` in the function
field of `W'`, then `W'` is the image of `W` under the change of variables `(u, r, s, t)`. -/
theorem variableChange_eq_of_equation (W' : WeierstrassCurve.Affine F) {u r s t : F} (hu : u ≠ 0)
    (h : (algebraMap F W'.FunctionField (u ^ 3) * W'.fieldY +
        algebraMap F _ (u ^ 2 * s) * W'.fieldX + algebraMap F _ t) ^ 2 +
      algebraMap F _ W.a₁ * (algebraMap F _ (u ^ 2) * W'.fieldX + algebraMap F _ r) *
        (algebraMap F _ (u ^ 3) * W'.fieldY + algebraMap F _ (u ^ 2 * s) * W'.fieldX +
          algebraMap F _ t) +
      algebraMap F _ W.a₃ * (algebraMap F _ (u ^ 3) * W'.fieldY +
        algebraMap F _ (u ^ 2 * s) * W'.fieldX + algebraMap F _ t) =
      (algebraMap F _ (u ^ 2) * W'.fieldX + algebraMap F _ r) ^ 3 +
        algebraMap F _ W.a₂ * (algebraMap F _ (u ^ 2) * W'.fieldX + algebraMap F _ r) ^ 2 +
        algebraMap F _ W.a₄ * (algebraMap F _ (u ^ 2) * W'.fieldX + algebraMap F _ r) +
        algebraMap F _ W.a₆) :
    (⟨Units.mk0 u hu, r, s, t⟩ : VariableChange F) • W = W' := by
  set A : F[X] := C (u ^ 6 * W'.a₂ + u ^ 4 * s ^ 2 + W.a₁ * u ^ 4 * s - 3 * u ^ 4 * r -
      W.a₂ * u ^ 4) * X ^ 2 +
    C (u ^ 6 * W'.a₄ + 2 * u ^ 2 * s * t + W.a₁ * (u ^ 2 * t + r * u ^ 2 * s) + W.a₃ * u ^ 2 * s -
      3 * u ^ 2 * r ^ 2 - 2 * W.a₂ * u ^ 2 * r - W.a₄ * u ^ 2) * X +
    C (u ^ 6 * W'.a₆ + t ^ 2 + W.a₁ * r * t + W.a₃ * t - r ^ 3 - W.a₂ * r ^ 2 - W.a₄ * r - W.a₆)
  set B : F[X] := C (-u ^ 6 * W'.a₁ + 2 * u ^ 5 * s + W.a₁ * u ^ 5) * X +
    C (-u ^ 6 * W'.a₃ + 2 * u ^ 3 * t + W.a₁ * u ^ 3 * r + W.a₃ * u ^ 3)
  have hAB : aeval W'.fieldX A + aeval W'.fieldX B * W'.fieldY = 0 := by
    have hy := W'.fieldY_sq_add
    simp only [A, B, linY, cubicX, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat,
      aeval_C, aeval_X] at hy h ⊢
    linear_combination h - (algebraMap F W'.FunctionField u) ^ 6 * hy
  obtain ⟨hA, hB⟩ := W'.eq_zero_of_aeval_add_aeval_mul_fieldY hAB
  have cA := fun n => congrArg (coeff · n) hA
  have cB := fun n => congrArg (coeff · n) hB
  have hA2 := cA 2
  have hA1 := cA 1
  have hA0 := cA 0
  have hB1 := cB 1
  have hB0 := cB 0
  simp only [A, B, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C,
    coeff_zero] at hA2 hA1 hA0 hB1 hB0
  norm_num at hA2 hA1 hA0 hB1 hB0
  ext
  · rw [variableChange_a₁]
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
    apply mul_left_cancel₀ (pow_ne_zero 5 hu)
    linear_combination hB1
  · rw [variableChange_a₂]
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
    apply mul_left_cancel₀ (pow_ne_zero 4 hu)
    linear_combination -hA2
  · rw [variableChange_a₃]
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
    apply mul_left_cancel₀ (pow_ne_zero 3 hu)
    linear_combination hB0
  · rw [variableChange_a₄]
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
    apply mul_left_cancel₀ (pow_ne_zero 2 hu)
    linear_combination -hA1
  · rw [variableChange_a₆]
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
    linear_combination -hA0

end WeierstrassCurve.Affine
