/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Curve.Lemmas
public import EllipticCurve.Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithC
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import all EllipticCurve.Curve.Defs
import EllipticCurve.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import EllipticCurve.Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfInvariants

/-! # Construction interface for `Curve` (internal)

The bridge between `Curve F` and Mathlib's Weierstrass curves, used by the model definition
modules (`EllipticCurve.Montgomery.Defs`, …) to build the points of their curve:

* `Curve.ofWeierstrass W`: the curve of an elliptic Weierstrass model, `mk W.c₄ W.c₆`;
* `Curve.ofWeierstrass_eq_ofWeierstrass_iff`: two models give the same curve exactly when they
  are related by a change of variables (the classification away from 6);
* `Curve.pointEquivOfWeierstrass W : (ofWeierstrass W).Point ≃+ W.Point`, the point map of a
  change of variables from `W` to the chosen short model of its curve.

**Internal.** This module must only ever be imported privately (`import EllipticCurve.Curve.Impl`)
by model definition modules: its statements mention Mathlib's `WeierstrassCurve`. The public
counterpart, for users who want Weierstrass models as one model among others, is
`EllipticCurve.Curve.Weierstrass`. -/

public section

universe u

namespace Curve

variable {F : Type u} [Field F] [NeZero (6 : F)]

/-- The curve of an elliptic Weierstrass model: its invariants `c₄`, `c₆`. -/
noncomputable def ofWeierstrass (W : WeierstrassCurve F) [W.IsElliptic] : Curve F :=
  mk W.c₄ W.c₆ (W.c₄_cube_sub_c₆_sq_ne_zero)

/-- The curve of a Weierstrass model is the curve with its invariants. -/
theorem ofWeierstrass_def (W : WeierstrassCurve F) [W.IsElliptic] :
    ofWeierstrass W = mk W.c₄ W.c₆ (W.c₄_cube_sub_c₆_sq_ne_zero) := by
  unfold ofWeierstrass; rfl

/-- Over a field away from 6, the classification of Weierstrass curves in the field form. -/
theorem exists_variableChange_iff {W W' : WeierstrassCurve F} :
    (∃ C : WeierstrassCurve.VariableChange F, C • W = W') ↔
      ∃ u : Fˣ, W'.c₄ = u ^ 4 * W.c₄ ∧ W'.c₆ = u ^ 6 * W.c₆ := by
  have := invertibleOfNonzero (NeZero.ne (2 : F))
  have := invertibleOfNonzero (NeZero.ne (3 : F))
  exact WeierstrassCurve.exists_variableChange_iff

/-- Two elliptic Weierstrass models give the same curve exactly when they are isomorphic. -/
theorem ofWeierstrass_eq_ofWeierstrass_iff {W W' : WeierstrassCurve F} [W.IsElliptic]
    [W'.IsElliptic] :
    ofWeierstrass W = ofWeierstrass W' ↔ ∃ C : WeierstrassCurve.VariableChange F, C • W' = W := by
  rw [ofWeierstrass, ofWeierstrass, mk_eq_mk_iff, exists_variableChange_iff]

/-- Isomorphic models give the same curve. -/
theorem ofWeierstrass_eq (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F) : ofWeierstrass (C • W) = ofWeierstrass W :=
  ofWeierstrass_eq_ofWeierstrass_iff.mpr ⟨C, rfl⟩

/-- Equal models give the same curve (the `IsElliptic` instances are irrelevant). -/
theorem ofWeierstrass_congr {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]
    (h : W = W') : ofWeierstrass W = ofWeierstrass W' := by
  subst h
  rfl

/-- The curve with invariants `(c₄, c₆)` is that of `ofC₄C₆ c₄ c₆`. -/
theorem ofWeierstrass_ofC₄C₆ (p : Invariants F) [(WeierstrassCurve.ofC₄C₆ p.c₄ p.c₆).IsElliptic] :
    ofWeierstrass (WeierstrassCurve.ofC₄C₆ p.c₄ p.c₆) = ofInvariants p := by
  rw [ofInvariants_eq_mk, ofWeierstrass]
  exact mk_eq_mk_of 6 (NeZero.ne _) (by simp) (by simp)

/-- The chosen model of `ofWeierstrass W` is a change of variables of `W`. -/
private theorem exists_smul_eq_toAffine (W : WeierstrassCurve F) [W.IsElliptic] :
    ∃ C : WeierstrassCurve.VariableChange F, C • W = (ofWeierstrass W).toAffine := by
  rw [exists_variableChange_iff]
  have h : ofInvariants (ofWeierstrass W).out = ofWeierstrass W := Quotient.out_eq _
  rw [ofWeierstrass, mk, ofInvariants_eq_ofInvariants_iff] at h
  obtain ⟨u, hu⟩ := h
  have hout : (ofWeierstrass W).out = u • ⟨W.c₄, W.c₆, W.c₄_cube_sub_c₆_sq_ne_zero⟩ := hu.symm
  refine ⟨Units.mk0 6 (NeZero.ne _) * u, ?_, ?_⟩
  · simp only [toAffine, WeierstrassCurve.ofC₄C₆_c₄, hout, Invariants.smul_c₄, Units.val_mul,
      Units.val_mk0]
    ring
  · simp only [toAffine, WeierstrassCurve.ofC₄C₆_c₆, hout, Invariants.smul_c₆, Units.val_mul,
      Units.val_mk0]
    ring

open scoped Classical in
/-- `pointEquivOfWeierstrass` with the classical `DecidableEq F` (the one of the hidden group law
on `Curve.Point`). Internal. -/
private noncomputable def pointEquivOfWeierstrassAux (W : WeierstrassCurve F) [W.IsElliptic] :
    (ofWeierstrass W).Point ≃+ W.toAffine.Point :=
  (WeierstrassCurve.Affine.Point.equivOfEq
      (Classical.choose_spec (exists_smul_eq_toAffine W)).symm).trans
    (WeierstrassCurve.Affine.Point.equivVariableChange W
      (Classical.choose (exists_smul_eq_toAffine W)))

/-- The points of `ofWeierstrass W` are the points of `W`, as groups: the point map of a change
of variables from `W` to the chosen model of its curve
(`WeierstrassCurve.Affine.Point.equivVariableChange`). The group law on `Curve.Point` is
Mathlib's with the classical `DecidableEq F`; this works for whichever `DecidableEq F` is in
scope, by `Subsingleton`. -/
noncomputable def pointEquivOfWeierstrass (W : WeierstrassCurve F) [W.IsElliptic]
    [DecidableEq F] : (ofWeierstrass W).Point ≃+ W.toAffine.Point := by
  obtain rfl : ‹DecidableEq F› = fun a b => Classical.propDecidable (a = b) :=
    Subsingleton.elim _ _
  exact pointEquivOfWeierstrassAux W

end Curve
