/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Curve.Fiber
public import EllipticCurve.Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithC
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.GroupTheory.GroupAction.Basic
import EllipticCurve.Curve.Impl
import EllipticCurve.Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfInvariants
import Mathlib.Tactic.FieldSimp

/-! # Weierstrass models of curves

Mathlib's Weierstrass curves as one model of `Curve F` among others (opt-in: the other models do
not import this module).

* `WeierstrassCurve.toCurve W`: the curve of an elliptic Weierstrass model, with invariants
  `W.c₄`, `W.c₆` (`toCurve_eq_mk`) and j-invariant `W.j` (`j_toCurve`);
* `WeierstrassCurve.toCurve_eq_toCurve_iff`: two models give the same curve exactly when they
  are related by a change of variables;
* `Curve.equivWeierstrass`: away from 6, `Curve F` is the set of elliptic Weierstrass curves up to
  change of variables, the classical definition of an elliptic curve up to isomorphism;
* `WeierstrassCurve.autEquiv`: the automorphisms of `W` (the changes of variables fixing it) are
  the group `Curve.aut` of its curve, hence the `n(j)`-th roots of unity
  (`Curve.aut_eq_rootsOfUnity`). For a short model they are the scalings `(x, y) ↦ (u² x, u³ y)`
  (rigidity, `WeierstrassCurve.variableChange_rst_eq_zero_of_isShortNF`). -/

public section

universe u

variable {F : Type u} [Field F] [NeZero (6 : F)]

namespace WeierstrassCurve

/-- `VariableChange F` acts on the elliptic Weierstrass curves. -/
instance instMulActionIsElliptic :
    MulAction (VariableChange F) {W : WeierstrassCurve F // W.IsElliptic} where
  smul C W := ⟨C • W.1, have := W.2; inferInstance⟩
  one_smul W := Subtype.ext (one_smul _ W.1)
  mul_smul C C' W := Subtype.ext (mul_smul C C' W.1)

/-- The curve of an elliptic Weierstrass model. -/
noncomputable def toCurve (W : WeierstrassCurve F) [W.IsElliptic] : Curve F :=
  Curve.ofWeierstrass W

/-- The curve of a Weierstrass model is the curve with invariants `W.c₄`, `W.c₆`. -/
theorem toCurve_eq_mk (W : WeierstrassCurve F) [W.IsElliptic] :
    W.toCurve = Curve.mk W.c₄ W.c₆ W.c₄_cube_sub_c₆_sq_ne_zero :=
  Curve.ofWeierstrass_def W

/-- Two elliptic Weierstrass models give the same curve exactly when they are related by a
change of variables. -/
theorem toCurve_eq_toCurve_iff {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic] :
    W.toCurve = W'.toCurve ↔ ∃ C : VariableChange F, C • W' = W :=
  Curve.ofWeierstrass_eq_ofWeierstrass_iff

/-- Isomorphic Weierstrass models give the same curve. -/
@[simp] theorem toCurve_smul (W : WeierstrassCurve F) [W.IsElliptic] (C : VariableChange F) :
    (C • W).toCurve = W.toCurve :=
  Curve.ofWeierstrass_eq W C

/-- The j-invariant of the curve of `W` is Mathlib's `W.j`. -/
@[simp] theorem j_toCurve (W : WeierstrassCurve F) [W.IsElliptic] : W.toCurve.j = W.j := by
  rw [toCurve_eq_mk, Curve.j_mk, W.j_eq, ← W.c_relation]
  have := W.isUnit_Δ.ne_zero
  have := ne_zero_1728_of_six (F := F)
  field_simp

private theorem aut_eq_stabilizer (W : WeierstrassCurve F) [W.IsElliptic] :
    W.toCurve.aut = MulAction.stabilizer Fˣ
      (⟨W.c₄, W.c₆, W.c₄_cube_sub_c₆_sq_ne_zero⟩ : Curve.Invariants F) := by
  rw [toCurve_eq_mk, Curve.mk_def, Curve.aut_ofInvariants]

open MulAction in
/-- `C ↦ C.u⁻¹`, from the automorphisms of `W` to those of its curve. Internal. -/
private noncomputable def autHom (W : WeierstrassCurve F) [W.IsElliptic] :
    stabilizer (VariableChange F) W →* W.toCurve.aut where
  toFun C := ⟨C.1.u⁻¹, by
    rw [aut_eq_stabilizer, mem_stabilizer_iff]
    have h := mem_stabilizer_iff.mp C.2
    have h₄ := congrArg WeierstrassCurve.c₄ h
    have h₆ := congrArg WeierstrassCurve.c₆ h
    rw [variableChange_c₄] at h₄
    rw [variableChange_c₆] at h₆
    ext
    · exact h₄
    · exact h₆⟩
  map_one' := Subtype.ext (by simp [VariableChange.one_def])
  map_mul' C C' := Subtype.ext (by simp [VariableChange.mul_def, mul_comm])

open MulAction in
/-- The automorphisms of a short model `W` are the scalings by the automorphisms of its curve:
`C ↦ C.u⁻¹`. -/
noncomputable def autEquivOfIsShortNF (W : WeierstrassCurve F) [W.IsElliptic] [W.IsShortNF] :
    stabilizer (VariableChange F) W ≃* W.toCurve.aut := by
  have := invertibleOfNonzero (NeZero.ne (2 : F))
  have := invertibleOfNonzero (NeZero.ne (3 : F))
  refine MulEquiv.ofBijective (autHom W) ⟨?_, ?_⟩
  · rintro ⟨C, hC⟩ ⟨C', hC'⟩ e
    have hC₁ := mem_stabilizer_iff.mp hC
    have hC₁' := mem_stabilizer_iff.mp hC'
    have : (C • W).IsShortNF := by rw [hC₁]; infer_instance
    have : (C' • W).IsShortNF := by rw [hC₁']; infer_instance
    obtain ⟨hr, hs, ht⟩ := variableChange_rst_eq_zero_of_isShortNF (S := W) (C := C)
    obtain ⟨hr', hs', ht'⟩ := variableChange_rst_eq_zero_of_isShortNF (S := W) (C := C')
    have hu : C.u = C'.u := inv_injective (congrArg Subtype.val e)
    exact Subtype.ext (VariableChange.ext hu (hr.trans hr'.symm) (hs.trans hs'.symm)
      (ht.trans ht'.symm))
  · rintro ⟨v, hv⟩
    rw [aut_eq_stabilizer, mem_stabilizer_iff] at hv
    have h₄ : W.c₄ = v ^ 4 * W.c₄ := (congrArg Curve.Invariants.c₄ hv).symm
    have h₆ : W.c₆ = v ^ 6 * W.c₆ := (congrArg Curve.Invariants.c₆ hv).symm
    exact ⟨⟨⟨v⁻¹, 0, 0, 0⟩, mem_stabilizer_iff.mpr (smul_eq_of_isShortNF v h₄ h₆)⟩,
      Subtype.ext (inv_inv v)⟩

open MulAction in
/-- **The automorphisms of a Weierstrass curve** (the changes of variables fixing it) are the
automorphisms of its curve: `n(j)`-th roots of unity, by `Curve.aut_eq_rootsOfUnity`. The map is
`C ↦ C.u⁻¹` (`coe_autEquiv_apply`). -/
noncomputable def autEquiv (W : WeierstrassCurve F) [W.IsElliptic] :
    stabilizer (VariableChange F) W ≃* W.toCurve.aut :=
  have := invertibleOfNonzero (NeZero.ne (2 : F))
  have := invertibleOfNonzero (NeZero.ne (3 : F))
  (stabilizerEquivStabilizer (g := W.toShortNF) rfl).trans <|
    (autEquivOfIsShortNF (W.toShortNF • W)).trans
      (MulEquiv.subgroupCongr (by rw [toCurve_smul]))

open MulAction in
/-- The isomorphism `autEquiv` sends an automorphism `C` of `W` to `C.u⁻¹`. -/
@[simp] theorem coe_autEquiv_apply (W : WeierstrassCurve F) [W.IsElliptic]
    (C : stabilizer (VariableChange F) W) : (autEquiv W C : Fˣ) = (C : VariableChange F).u⁻¹ := by
  simp only [autEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    autEquivOfIsShortNF, MulEquiv.ofBijective_apply, autHom, MonoidHom.coe_mk, OneHom.coe_mk,
    stabilizerEquivStabilizer, MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply,
    VariableChange.mul_def, VariableChange.inv_def]
  rw [mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

end WeierstrassCurve

namespace Curve

/-- Every curve has an elliptic Weierstrass model. -/
theorem exists_toCurve_eq (C : Curve F) :
    ∃ (W : WeierstrassCurve F) (_ : W.IsElliptic), W.toCurve = C :=
  C.ind fun p => by
    have h6 : IsUnit (6 : F) := isUnit_iff_ne_zero.mpr (NeZero.ne _)
    have := WeierstrassCurve.isElliptic_ofC₄C₆ p.c₄ p.c₆ h6 (isUnit_iff_ne_zero.mpr p.disc_ne_zero)
    exact ⟨_, this, ofWeierstrass_ofC₄C₆ p⟩

/-- The curve of an elliptic Weierstrass model, on the orbits of the changes of variables. -/
noncomputable def ofWeierstrassOrbit :
    MulAction.orbitRel.Quotient (WeierstrassCurve.VariableChange F)
      {W : WeierstrassCurve F // W.IsElliptic} → Curve F :=
  Quotient.lift (fun W => have := W.2; W.1.toCurve) <| by
    rintro _ ⟨W, hW⟩ ⟨C, rfl⟩
    exact WeierstrassCurve.toCurve_smul W C

/-- **Away from 6, curves are elliptic Weierstrass curves up to change of variables.** -/
noncomputable def equivWeierstrass :
    Curve F ≃ MulAction.orbitRel.Quotient (WeierstrassCurve.VariableChange F)
      {W : WeierstrassCurve F // W.IsElliptic} :=
  (Equiv.ofBijective ofWeierstrassOrbit ⟨by
    rintro ⟨W, hW⟩ ⟨W', hW'⟩ h
    obtain ⟨C, hC⟩ := WeierstrassCurve.toCurve_eq_toCurve_iff.mp h
    exact Quotient.sound ⟨C, Subtype.ext hC⟩, fun C => by
    obtain ⟨W, hW, rfl⟩ := exists_toCurve_eq C
    exact ⟨Quotient.mk _ ⟨W, hW⟩, rfl⟩⟩).symm

end Curve
