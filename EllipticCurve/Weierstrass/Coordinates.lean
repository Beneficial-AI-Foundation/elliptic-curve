/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.FunctionField.Place
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import EllipticCurve.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-! # The coordinate functions of a Weierstrass curve

For a Weierstrass curve `W` over a field `F`, the coordinate functions `W.fieldX`, `W.fieldY` of
its function field `W.FunctionField` satisfy the Weierstrass equation (`fieldY_equation`) and
generate the function field over `F` (`adjoin_fieldX_fieldY`); a nonzero polynomial in `x` is a
nonzero function (`aeval_fieldX_ne_zero`), and so is `y` (`fieldY_ne_zero`). -/

public section

universe u

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] (W : WeierstrassCurve.Affine F)

/-! ### The coordinate functions -/

/-- The function `x` on `W`. -/
noncomputable def fieldX : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C X))

/-- The function `y` on `W`. -/
noncomputable def fieldY : W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W X)

/-- The characterising equation of `fieldX`. -/
theorem fieldX_def :
    W.fieldX = algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C X)) := by
  unfold fieldX; rfl

/-- The characterising equation of `fieldY`. -/
theorem fieldY_def :
    W.fieldY = algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W X) := by
  unfold fieldY; rfl

/-- The coordinate functions satisfy the Weierstrass equation. -/
theorem fieldY_equation :
    W.fieldY ^ 2 + algebraMap F _ W.a₁ * W.fieldX * W.fieldY + algebraMap F _ W.a₃ * W.fieldY =
      W.fieldX ^ 3 + algebraMap F _ W.a₂ * W.fieldX ^ 2 + algebraMap F _ W.a₄ * W.fieldX +
        algebraMap F _ W.a₆ := by
  have h : CoordinateRing.mk W W.polynomial = 0 := AdjoinRoot.mk_self
  have h' := congrArg (algebraMap W.CoordinateRing W.FunctionField) h
  rw [map_zero] at h'
  simp only [Affine.polynomial, map_sub, map_add, map_mul, map_pow] at h'
  simp only [fieldX, fieldY, IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField]
  have hC : ∀ c : F, CoordinateRing.mk W (C (C c)) = algebraMap F W.CoordinateRing c := fun c => rfl
  simp only [hC] at h'
  linear_combination h'

/-- A polynomial in `x` is the image of a polynomial in the coordinate ring. -/
theorem aeval_fieldX (p : F[X]) :
    aeval W.fieldX p =
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C p)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n c =>
    simp only [← C_mul_X_pow_eq_monomial, map_mul, map_pow, aeval_C, aeval_X, fieldX]
    rw [IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField]
    rfl

/-- A nonzero polynomial in `x` is a nonzero function. -/
theorem aeval_fieldX_ne_zero {p : F[X]} (hp : p ≠ 0) : aeval W.fieldX p ≠ 0 := by
  rw [aeval_fieldX]
  intro h0
  apply hp
  have h1 :=
    (IsFractionRing.injective W.CoordinateRing W.FunctionField) (h0.trans (map_zero _).symm)
  have h2 : p • (1 : W.CoordinateRing) + (0 : F[X]) • CoordinateRing.mk W X = 0 := by
    rw [zero_smul, add_zero, Algebra.smul_def, mul_one]
    exact h1
  exact (CoordinateRing.smul_basis_eq_zero h2).1

/-- The function `y` is nonzero. -/
theorem fieldY_ne_zero : W.fieldY ≠ 0 := by
  intro h0
  have h1 :=
    (IsFractionRing.injective W.CoordinateRing W.FunctionField) (h0.trans (map_zero _).symm)
  have h2 : (0 : F[X]) • (1 : W.CoordinateRing) + (1 : F[X]) • CoordinateRing.mk W X = 0 := by
    rw [zero_smul, zero_add, one_smul]
    exact h1
  exact one_ne_zero (CoordinateRing.smul_basis_eq_zero h2).2

/-- The coordinate functions generate the function field. -/
theorem adjoin_fieldX_fieldY :
    IntermediateField.adjoin F {W.fieldX, W.fieldY} = ⊤ := by
  set S := IntermediateField.adjoin F ({W.fieldX, W.fieldY} : Set W.FunctionField)
  have hX : W.fieldX ∈ S := IntermediateField.subset_adjoin _ _ (by simp)
  have hY : W.fieldY ∈ S := IntermediateField.subset_adjoin _ _ (by simp)
  -- the image of the coordinate ring lies in `S`
  have hcoeff : ∀ p : F[X],
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C p)) ∈ S := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa using S.add_mem hp hq
    | monomial n c =>
      have : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C (monomial n c))) =
          algebraMap F W.FunctionField c * W.fieldX ^ n := by
        simp only [← C_mul_X_pow_eq_monomial, map_mul, map_pow, fieldX,
          IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField]
        rfl
      rw [this]
      exact S.mul_mem (S.algebraMap_mem c) (S.pow_mem hX n)
  have hring : ∀ a : W.CoordinateRing, algebraMap W.CoordinateRing W.FunctionField a ∈ S := by
    intro a
    induction a using AdjoinRoot.induction_on with | ih q =>
    induction q using Polynomial.induction_on' with
    | add p q hp hq => simpa using S.add_mem hp hq
    | monomial n p =>
      have : algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (monomial n p)) =
          algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W (C p)) *
            W.fieldY ^ n := by
        simp only [← C_mul_X_pow_eq_monomial, map_mul, map_pow, fieldY]
      rw [this]
      exact S.mul_mem (hcoeff p) (S.pow_mem hY n)
  rw [eq_top_iff]
  intro z _
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
  exact S.div_mem (hring a) (hring b)

/-- The function `p(x) + q(x) y`. -/
theorem algebraMap_smul_basis (p q : F[X]) :
    algebraMap W.CoordinateRing W.FunctionField (p • 1 + q • CoordinateRing.mk W X) =
      aeval W.fieldX p + aeval W.fieldX q * W.fieldY := by
  rw [CoordinateRing.smul, CoordinateRing.smul, mul_one, map_add, map_mul, aeval_fieldX,
    aeval_fieldX, fieldY]

end WeierstrassCurve.Affine
