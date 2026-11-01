/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Weierstrass.Coordinates
public import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Tactic.LinearCombination

/-! # Substitution maps of a function field

For `ξ, η` in the function field of a Weierstrass curve `W` over `L` satisfying the equation of
`W`, the substitution `x ↦ ξ`, `y ↦ η` is an `L`-algebra map of the coordinate ring into the
function field (`substHom`); when `ξ` is transcendental it is injective (its kernel would contain
a norm `N(r) ∈ L[x]`, a relation for `ξ`), and extends to the function field (`subst`). An
`L`-algebra map of the function field is determined by the images of `x` and `y`
(`algHom_ext_fieldX_fieldY`). -/

public section

universe u

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {L : Type u} [Field L] (W : WeierstrassCurve.Affine L)

/-- The equation of `W` at a pair `(ξ, η)` of functions. -/
def FieldEquation (ξ η : W.FunctionField) : Prop :=
  η ^ 2 + algebraMap L _ W.a₁ * ξ * η + algebraMap L _ W.a₃ * η =
    ξ ^ 3 + algebraMap L _ W.a₂ * ξ ^ 2 + algebraMap L _ W.a₄ * ξ + algebraMap L _ W.a₆

theorem fieldEquation_iff (ξ η : W.FunctionField) : W.FieldEquation ξ η ↔
    η ^ 2 + algebraMap L _ W.a₁ * ξ * η + algebraMap L _ W.a₃ * η =
      ξ ^ 3 + algebraMap L _ W.a₂ * ξ ^ 2 + algebraMap L _ W.a₄ * ξ + algebraMap L _ W.a₆ :=
  Iff.rfl

variable {W} {ξ η : W.FunctionField}

/-- The substitution `x ↦ ξ`, `y ↦ η` on the coordinate ring. -/
noncomputable def substHom (h : W.FieldEquation ξ η) : W.CoordinateRing →ₐ[L] W.FunctionField :=
  AdjoinRoot.liftAlgHom W.polynomial (Polynomial.aeval ξ) η (by
    change eval₂ _ _ (Y ^ 2 + Polynomial.C (Polynomial.C W.a₁ * X + Polynomial.C W.a₃) * Y -
      Polynomial.C (X ^ 3 + Polynomial.C W.a₂ * X ^ 2 + Polynomial.C W.a₄ * X +
        Polynomial.C W.a₆)) = 0
    simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, eval₂_pow,
      AlgHom.coe_toRingHom, map_add, map_mul, map_pow, aeval_C, aeval_X]
    rw [fieldEquation_iff] at h
    linear_combination h)

theorem substHom_mk_C (h : W.FieldEquation ξ η) (p : L[X]) :
    substHom h (CoordinateRing.mk W (Polynomial.C p)) = aeval ξ p := by
  rw [substHom, show CoordinateRing.mk W (Polynomial.C p) = AdjoinRoot.of _ p from rfl,
    AdjoinRoot.liftAlgHom_of]

theorem substHom_mk_Y (h : W.FieldEquation ξ η) : substHom h (CoordinateRing.mk W X) = η := by
  rw [substHom, show CoordinateRing.mk W X = AdjoinRoot.root _ from rfl,
    AdjoinRoot.liftAlgHom_root]

/-- The substitution is injective when `ξ` is transcendental. -/
theorem substHom_injective (h : W.FieldEquation ξ η) (hξ : Transcendental L ξ) :
    Function.Injective (substHom h) := by
  have : Module.Finite L[X] W.CoordinateRing := .of_basis (CoordinateRing.basis W)
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq r
  apply hξ
  refine ⟨Algebra.norm L[X] (p • 1 + q • CoordinateRing.mk W X), ?_, ?_⟩
  · rwa [Ne, Algebra.norm_eq_zero_iff]
  · rw [← substHom_mk_C h, show CoordinateRing.mk W (Polynomial.C _) = AdjoinRoot.of _ _ from rfl,
      CoordinateRing.coe_norm_smul_basis, map_mul,
      show CoordinateRing.mk W (Polynomial.C p + Polynomial.C q * X) =
        p • 1 + q • CoordinateRing.mk W X by
          rw [CoordinateRing.smul, CoordinateRing.smul, map_add, map_mul, mul_one],
      map_mul, hr, zero_mul]

/-- The substitution `x ↦ ξ`, `y ↦ η` on the function field, for `ξ` transcendental. -/
noncomputable def subst (h : W.FieldEquation ξ η) (hξ : Transcendental L ξ) :
    W.FunctionField →ₐ[L] W.FunctionField :=
  IsFractionRing.liftAlgHom (substHom_injective h hξ)

theorem subst_algebraMap (h : W.FieldEquation ξ η) (hξ : Transcendental L ξ)
    (r : W.CoordinateRing) : subst h hξ (algebraMap _ _ r) = substHom h r := by
  rw [subst, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

theorem subst_fieldX (h : W.FieldEquation ξ η) (hξ : Transcendental L ξ) :
    subst h hξ W.fieldX = ξ := by
  rw [fieldX_def, subst_algebraMap, substHom_mk_C, aeval_X]

theorem subst_fieldY (h : W.FieldEquation ξ η) (hξ : Transcendental L ξ) :
    subst h hξ W.fieldY = η := by
  rw [fieldY_def, subst_algebraMap, substHom_mk_Y]

/-- `L`-algebra maps of the function field agreeing on `x` and `y` are equal. -/
theorem algHom_ext_fieldX_fieldY {K' : Type*} [Field K'] [Algebra L K']
    {φ ψ : W.FunctionField →ₐ[L] K'} (hx : φ W.fieldX = ψ W.fieldX)
    (hy : φ W.fieldY = ψ W.fieldY) : φ = ψ := by
  have hR : (φ : W.FunctionField →+* K').comp (algebraMap W.CoordinateRing _) =
      (ψ : W.FunctionField →+* K').comp (algebraMap W.CoordinateRing _) := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro c
        change φ (algebraMap W.CoordinateRing _ (algebraMap L _ c)) =
          ψ (algebraMap W.CoordinateRing _ (algebraMap L _ c))
        rw [← IsScalarTower.algebraMap_apply, φ.commutes, ψ.commutes]
      · simpa [fieldX_def] using hx
    · simpa [fieldY_def] using hy
  refine AlgHom.ext fun z => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
  rw [map_div₀, map_div₀]
  have := fun r => congrArg (fun f : W.CoordinateRing →+* K' => f r) hR
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe] at this
  rw [this a, this b]

end WeierstrassCurve.Affine
