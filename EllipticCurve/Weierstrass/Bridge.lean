/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Weierstrass.Places
public import EllipticCurve.Curve.Weierstrass
import EllipticCurve.Field.AwayFromSix
import EllipticCurve.Weierstrass.Infinity
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.LinearCombination

/-! # Curves are pointed function fields (of Weierstrass type)

Away from 6, two elliptic Weierstrass curves give the same `Curve F` exactly when their function
fields are isomorphic by an isomorphism matching the places at infinity
(`toCurve_eq_toCurve_iff_exists_algEquiv`). One direction is (B-W); the other is the isomorphism
of function fields induced by a change of variables (`algEquivOfVariableChange`).

So `Curve F` classifies the elliptic function fields with a rational place that have a
Weierstrass model. That every elliptic function field with a rational place has one is the
remaining part of the bridge theorem, by Riemann–Roch. -/

public section

universe u

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] (W : WeierstrassCurve.Affine F) (C : VariableChange F)

/-- A polynomial in `x`, in the coordinate ring. -/
theorem aeval_mk_C (p : F[X]) :
    aeval (CoordinateRing.mk W (Polynomial.C X)) p = CoordinateRing.mk W (Polynomial.C p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, hp, hq, map_add, map_add]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, aeval_C, aeval_X]
    rfl

/-- The coordinates of `C • W` as functions on `W`: `x' = u⁻² (x - r)`. -/
noncomputable def vcX : W.CoordinateRing :=
  algebraMap F _ ((C.u⁻¹ : Fˣ) ^ 2 : F) *
    (CoordinateRing.mk W (Polynomial.C X) - algebraMap F _ C.r)

/-- The coordinates of `C • W` as functions on `W`: `y' = u⁻³ (y - s (x - r) - t)`. -/
noncomputable def vcY : W.CoordinateRing :=
  algebraMap F _ ((C.u⁻¹ : Fˣ) ^ 3 : F) * (CoordinateRing.mk W X -
    algebraMap F _ C.s * (CoordinateRing.mk W (Polynomial.C X) - algebraMap F _ C.r) -
      algebraMap F _ C.t)

/-- The equation of `W` in its coordinate ring. -/
theorem mk_equation :
    CoordinateRing.mk W X ^ 2 + algebraMap F _ W.a₁ * CoordinateRing.mk W (Polynomial.C X) *
        CoordinateRing.mk W X + algebraMap F _ W.a₃ * CoordinateRing.mk W X -
      (CoordinateRing.mk W (Polynomial.C X) ^ 3 +
        algebraMap F _ W.a₂ * CoordinateRing.mk W (Polynomial.C X) ^ 2 +
        algebraMap F _ W.a₄ * CoordinateRing.mk W (Polynomial.C X) + algebraMap F _ W.a₆) = 0 := by
  have h : CoordinateRing.mk W (Y ^ 2 +
      Polynomial.C (Polynomial.C W.a₁ * X + Polynomial.C W.a₃) * Y -
      Polynomial.C (X ^ 3 + Polynomial.C W.a₂ * X ^ 2 + Polynomial.C W.a₄ * X +
        Polynomial.C W.a₆)) = 0 :=
    AdjoinRoot.mk_self
  simp only [map_sub, map_add, map_mul, map_pow] at h
  have hC : ∀ c : F, CoordinateRing.mk W (Polynomial.C (Polynomial.C c)) =
    algebraMap F W.CoordinateRing c := fun c => rfl
  simp only [hC] at h
  linear_combination h

/-- The coordinate ring of `C • W` maps to that of `W` by `x' ↦ u⁻² (x - r)`,
`y' ↦ u⁻³ (y - s (x - r) - t)`. -/
noncomputable def vcHom : (C • W).CoordinateRing →ₐ[F] W.CoordinateRing :=
  AdjoinRoot.liftAlgHom (C • W).polynomial (Polynomial.aeval (W.vcX C)) (W.vcY C) (by
    change eval₂ _ _ (Y ^ 2 + Polynomial.C (Polynomial.C (C • W).a₁ * X +
      Polynomial.C (C • W).a₃) * Y - Polynomial.C (X ^ 3 + Polynomial.C (C • W).a₂ * X ^ 2 +
        Polynomial.C (C • W).a₄ * X + Polynomial.C (C • W).a₆)) = 0
    simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_C, eval₂_X, eval₂_pow,
      AlgHom.coe_toRingHom, map_add, map_mul, map_pow, aeval_C, aeval_X]
    simp only [vcX, vcY, variableChange_a₁, variableChange_a₂, variableChange_a₃,
      variableChange_a₄, variableChange_a₆, map_mul, map_add, map_sub, map_pow, map_ofNat]
    linear_combination (algebraMap F W.CoordinateRing ((C.u⁻¹ : Fˣ) : F)) ^ 6 * W.mk_equation)

theorem vcHom_mk_C (p : F[X]) :
    W.vcHom C (CoordinateRing.mk (C • W) (Polynomial.C p)) = aeval (W.vcX C) p := by
  rw [vcHom, show CoordinateRing.mk (C • W) (Polynomial.C p) = AdjoinRoot.of _ p from rfl,
    AdjoinRoot.liftAlgHom_of]

theorem vcHom_mk_Y : W.vcHom C (CoordinateRing.mk (C • W) X) = W.vcY C := by
  rw [vcHom, show CoordinateRing.mk (C • W) X = AdjoinRoot.root _ from rfl,
    AdjoinRoot.liftAlgHom_root]

/-- `x' = u⁻² (x - r)` as an element `L • 1` of the basis. -/
theorem vcX_eq : W.vcX C = CoordinateRing.mk W
    (Polynomial.C (Polynomial.C ((C.u⁻¹ : Fˣ) ^ 2 : F) * (X - Polynomial.C C.r))) := by
  rw [vcX]
  simp only [map_mul, map_sub]
  rfl

theorem vcY_eq : W.vcY C = CoordinateRing.mk W (Polynomial.C (Polynomial.C ((C.u⁻¹ : Fˣ) ^ 3 : F) *
      (-Polynomial.C C.s * (X - Polynomial.C C.r) - Polynomial.C C.t))) +
    CoordinateRing.mk W (Polynomial.C (Polynomial.C ((C.u⁻¹ : Fˣ) ^ 3 : F))) *
      CoordinateRing.mk W X := by
  have hC : ∀ c : F, CoordinateRing.mk W (Polynomial.C (Polynomial.C c)) =
    algebraMap F W.CoordinateRing c := fun c => rfl
  rw [vcY]
  simp only [map_mul, map_sub, map_neg, hC]
  ring

theorem aeval_vcX (p : F[X]) : aeval (W.vcX C) p = CoordinateRing.mk W (Polynomial.C
    (p.comp (Polynomial.C ((C.u⁻¹ : Fˣ) ^ 2 : F) * (X - Polynomial.C C.r)))) := by
  have hC : ∀ c : F, CoordinateRing.mk W (Polynomial.C (Polynomial.C c)) =
    algebraMap F W.CoordinateRing c := fun c => rfl
  rw [vcX_eq]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, hp, hq, add_comp, map_add, map_add]
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, aeval_C, aeval_X, mul_comp, C_comp, X_pow_comp, hC]

/-- The map is injective: compare coefficients in the basis `1, y`. -/
theorem vcHom_injective : Function.Injective (W.vcHom C) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq r
  rw [CoordinateRing.smul, CoordinateRing.smul, mul_one, map_add, map_mul, vcHom_mk_C,
    vcHom_mk_C, vcHom_mk_Y, aeval_vcX, aeval_vcX, vcY_eq] at hr
  set L : F[X] := Polynomial.C ((C.u⁻¹ : Fˣ) ^ 2 : F) * (X - Polynomial.C C.r)
  set M : F[X] := Polynomial.C ((C.u⁻¹ : Fˣ) ^ 3 : F) *
    (-Polynomial.C C.s * (X - Polynomial.C C.r) - Polynomial.C C.t)
  have key : (p.comp L + q.comp L * M) • (1 : W.CoordinateRing) +
      (q.comp L * Polynomial.C ((C.u⁻¹ : Fˣ) ^ 3 : F)) • CoordinateRing.mk W X = 0 := by
    rw [← hr, CoordinateRing.smul, CoordinateRing.smul, mul_one]
    simp only [map_add, map_mul]
    ring
  obtain ⟨h1, h2⟩ := CoordinateRing.smul_basis_eq_zero key
  have hL : ¬ L = Polynomial.C (L.coeff 0) := fun h => by
    have := congrArg natDegree h
    rw [natDegree_C, natDegree_C_mul (pow_ne_zero 2 (Units.ne_zero _)), natDegree_X_sub_C] at this
    exact one_ne_zero this
  have hq : q = 0 := by
    have : q.comp L = 0 := (mul_eq_zero.mp h2).resolve_right
      (Polynomial.C_ne_zero.mpr (pow_ne_zero 3 (Units.ne_zero _)))
    exact (Polynomial.comp_eq_zero_iff.mp this).resolve_right fun h => hL h.2
  subst hq
  have hp : p = 0 := by
    rw [zero_comp, zero_mul, add_zero] at h1
    exact (Polynomial.comp_eq_zero_iff.mp h1).resolve_right fun h => hL h.2
  subst hp
  simp

/-- The map is surjective: `x = u² x' + r` and `y = u³ y' + u² s x' + t` are in its image. -/
theorem vcHom_surjective : Function.Surjective (W.vcHom C) := by
  have hu : ((C.u : F)) ^ 2 * ((C.u⁻¹ : Fˣ) : F) ^ 2 = 1 := by
    rw [← mul_pow, Units.mul_inv, one_pow]
  have hu3 : ((C.u : F)) ^ 3 * ((C.u⁻¹ : Fˣ) : F) ^ 3 = 1 := by
    rw [← mul_pow, Units.mul_inv, one_pow]
  set a := algebraMap F (C • W).CoordinateRing ((C.u : F) ^ 2) *
    CoordinateRing.mk (C • W) (Polynomial.C X) + algebraMap F _ C.r
  set b := algebraMap F (C • W).CoordinateRing ((C.u : F) ^ 3) * CoordinateRing.mk (C • W) X +
    algebraMap F _ ((C.u : F) ^ 2 * C.s) * CoordinateRing.mk (C • W) (Polynomial.C X) +
      algebraMap F _ C.t
  have ha : W.vcHom C a = CoordinateRing.mk W (Polynomial.C X) := by
    simp only [a, map_add, map_mul, AlgHom.commutes, vcHom_mk_C, aeval_X, vcX]
    rw [← mul_assoc, ← map_mul, hu, map_one, one_mul, sub_add_cancel]
  have hb : W.vcHom C b = CoordinateRing.mk W X := by
    simp only [b, map_add, map_mul, AlgHom.commutes, vcHom_mk_C, vcHom_mk_Y, aeval_X, vcX, vcY]
    rw [← mul_assoc, ← map_mul, hu3, map_one, one_mul]
    have h2 : algebraMap F W.CoordinateRing ((C.u : F) ^ 2) *
        algebraMap F W.CoordinateRing (((C.u⁻¹ : Fˣ) : F) ^ 2) = 1 := by
      rw [← map_mul, hu, map_one]
    linear_combination (algebraMap F W.CoordinateRing C.s *
      (CoordinateRing.mk W (Polynomial.C X) - algebraMap F W.CoordinateRing C.r)) * h2
  intro r
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq r
  refine ⟨aeval a p + aeval a q * b, ?_⟩
  rw [map_add, map_mul, ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply, ha, hb,
    CoordinateRing.smul, CoordinateRing.smul, mul_one]
  congr 1
  · exact W.aeval_mk_C p
  · rw [W.aeval_mk_C q]

/-- The isomorphism of coordinate rings induced by a change of variables. -/
noncomputable def coordinateRingEquiv : (C • W).CoordinateRing ≃ₐ[F] W.CoordinateRing :=
  AlgEquiv.ofBijective (W.vcHom C) ⟨W.vcHom_injective C, W.vcHom_surjective C⟩

/-- **The isomorphism of function fields induced by a change of variables**:
`x' ↦ u⁻² (x - r)`, `y' ↦ u⁻³ (y - s (x - r) - t)`. -/
noncomputable def algEquivOfVariableChange : (C • W).FunctionField ≃ₐ[F] W.FunctionField :=
  IsFractionRing.algEquivOfAlgEquiv (W.coordinateRingEquiv C)

theorem algEquivOfVariableChange_fieldX :
    W.algEquivOfVariableChange C (C • W).fieldX =
      algebraMap F _ ((C.u⁻¹ : Fˣ) ^ 2 : F) * (W.fieldX - algebraMap F _ C.r) := by
  rw [fieldX_def, algEquivOfVariableChange, IsFractionRing.algEquivOfAlgEquiv_algebraMap,
    coordinateRingEquiv]
  change algebraMap W.CoordinateRing W.FunctionField
    (W.vcHom C (CoordinateRing.mk (C • W) (Polynomial.C X))) = _
  rw [vcHom_mk_C, aeval_X, vcX, map_mul, map_sub, fieldX_def, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]

variable [W.IsElliptic]

/-- The isomorphism of a change of variables matches the places at infinity. -/
theorem pointMapOfAlgEquiv_algEquivOfVariableChange_zero :
    pointMapOfAlgEquiv (W.algEquivOfVariableChange C) 0 = 0 := by
  set e := W.algEquivOfVariableChange C
  have hcongr : FunctionField.RationalPlace.congr e (W.pointEquivRationalPlace 0) =
      (C • W).pointEquivRationalPlace 0 := by
    set Q := FunctionField.RationalPlace.congr e (W.pointEquivRationalPlace 0)
    have hx : (C • W).fieldX ∉ Q.1.ring := by
      rw [FunctionField.RationalPlace.congr_apply_ring, algEquivOfVariableChange_fieldX]
      intro h
      apply W.fieldX_not_mem_pointEquivRationalPlace_zero
      have hc := (W.pointEquivRationalPlace 0).1.algebraMap_mem
      have : W.fieldX = algebraMap F _ ((C.u : F) ^ 2) *
          (algebraMap F _ ((C.u⁻¹ : Fˣ) ^ 2 : F) * (W.fieldX - algebraMap F _ C.r)) +
            algebraMap F _ C.r := by
        rw [← mul_assoc, ← map_mul, ← mul_pow, Units.val_inv_eq_inv_val,
          mul_inv_cancel₀ (Units.ne_zero _), one_pow, map_one, one_mul, sub_add_cancel]
      rw [this]
      exact add_mem (mul_mem (hc _) h) (hc _)
    exact Subtype.ext (FunctionField.Place.ext (eq_of_fieldX_not_mem Q.1.algebraMap_mem hx
      ((C • W).pointEquivRationalPlace 0).1.algebraMap_mem
      (C • W).fieldX_not_mem_pointEquivRationalPlace_zero))
  rw [pointMapOfAlgEquiv_apply, hcongr, Equiv.symm_apply_apply]

end WeierstrassCurve.Affine

namespace WeierstrassCurve

variable {F : Type u} [Field F] [NeZero (6 : F)]

/-- **Curves are pointed function fields** (of Weierstrass type): away from 6, two elliptic
Weierstrass curves give the same curve exactly when their function fields are isomorphic by an
isomorphism matching the places at infinity. -/
theorem toCurve_eq_toCurve_iff_exists_algEquiv {W W' : WeierstrassCurve F} [W.IsElliptic]
    [W'.IsElliptic] : W.toCurve = W'.toCurve ↔
      ∃ e : W.toAffine.FunctionField ≃ₐ[F] W'.toAffine.FunctionField,
        Affine.pointMapOfAlgEquiv e 0 = 0 := by
  constructor
  · intro h
    obtain ⟨C, rfl⟩ := toCurve_eq_toCurve_iff.mp h
    exact ⟨Affine.algEquivOfVariableChange W' C,
      Affine.pointMapOfAlgEquiv_algEquivOfVariableChange_zero W' C⟩
  · rintro ⟨e, h0⟩
    obtain ⟨C, hC, -⟩ := Affine.exists_variableChange_of_algEquiv e h0
    subst hC
    exact (toCurve_smul W C).symm

end WeierstrassCurve
