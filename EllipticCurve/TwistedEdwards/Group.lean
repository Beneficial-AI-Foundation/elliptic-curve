/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.TwistedEdwards.Defs
public import EllipticCurve.PlaneModel.Edwards
import all EllipticCurve.Montgomery.Defs
import EllipticCurve.PlaneModel.EdwardsIdentities
import EllipticCurve.Curve.Realization
import Mathlib.Algebra.Group.TransferInstance

/-! # Twisted Edwards models: the group (hidden construction)

On a complete model `E`, the points `E.Point` are in bijection with the points of the root
`PlaneModel.edwardsRoot a d` of the Edwards plane model: a point of the root has Edwards
coordinates, and every solution of the Edwards equation is the coordinates of exactly one point
(irreducible equation, nonsingular solutions; `PlaneModel.exists_coords_eq`,
`PlaneModel.coords_injective`). The group on `E.Point` is *defined* by transport along this
bijection (`toRoot`). The root is also the Weierstrass model of `E.toMontgomery`, so the
isomorphism with the Montgomery model (`toMontgomeryEquiv`) is the composite of the two
transports; `E.toCurve` and `E.pointEquiv` are those of `E.toMontgomery`.

Everything here is a hidden construction, characterised in `EllipticCurve.TwistedEdwards.Lemmas`
(by `import all` of this module): `zero_x`, `neg_x`, `add_x`, `u_toMontgomeryEquiv`, …. -/

public section

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] (E : TwistedEdwardsModel F) [E.IsComplete]

omit [E.IsComplete] in
/-- The Weierstrass model of `E.toMontgomery` is the Edwards root. -/
private theorem toWeierstrass_eq :
    E.toMontgomery.toWeierstrass = PlaneModel.edwardsRoot E.a E.d := by
  rw [toMontgomery_def]; rfl

private instance : (PlaneModel.edwardsRoot E.a E.d).IsElliptic :=
  toWeierstrass_eq E ▸ inferInstance

/-- The Edwards plane model of `E`. Internal. -/
private noncomputable abbrev model : PlaneModel (PlaneModel.edwardsRoot E.a E.d) :=
  PlaneModel.edwards E.a E.d (sub_ne_zero.mpr E.a_ne_d) (IsComplete.two_ne_zero (E := E))

private theorem isComplete' : (⟨E.a, E.d⟩ : TwistedEdwardsModel F).IsComplete := ‹_›

private theorem had : E.a - E.d ≠ 0 := sub_ne_zero.mpr E.a_ne_d

private theorem exists_root (P : E.Point) :
    ∃ R : (PlaneModel.edwardsRoot E.a E.d).Point, E.model.coords R = some (P.x, P.y) := by
  have hG : Irreducible E.model.G := by
    rw [PlaneModel.edwards_G]
    exact PlaneModel.edwards_G_irreducible E.had (IsComplete.two_ne_zero (E := E))
  exact E.model.exists_coords_eq hG (PlaneModel.edwards_nonsingular (had := E.had)
    (h2 := IsComplete.two_ne_zero (E := E)) E.isComplete' P.equation)

private theorem exists_coords (R : (PlaneModel.edwardsRoot E.a E.d).Point) :
    ∃ c : F × F, E.model.coords R = some c :=
  have := E.isComplete'
  PlaneModel.edwards_coords_isSome (had := E.had) (h2 := IsComplete.two_ne_zero (E := E)) R

/-- The bijection of `E.Point` with the points of the root: a point goes to the point of the
root with the same Edwards coordinates. Internal. -/
private noncomputable def toRoot : E.Point ≃ (PlaneModel.edwardsRoot E.a E.d).Point where
  toFun P := (E.exists_root P).choose
  invFun R := ⟨(E.exists_coords R).choose.1, (E.exists_coords R).choose.2,
    PlaneModel.edwards_equation_of_coords (E.exists_coords R).choose_spec⟩
  left_inv P := by
    have h := Option.some_inj.mp
      ((E.exists_coords (E.exists_root P).choose).choose_spec.symm.trans
        (E.exists_root P).choose_spec)
    ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  right_inv R := by
    apply PlaneModel.edwards_coords_injective E.isComplete'
      (E.exists_root _).choose_spec
    exact (E.exists_coords R).choose_spec

open Classical in
/-- The group law on the points of a complete `E`, transported from the root. Hidden
construction: it is characterised by `zero_x`, `zero_y`, `neg_x`, `neg_y`, `add_x` and `add_y`
(`EllipticCurve.TwistedEdwards.Lemmas`). -/
@[no_expose] noncomputable instance instAddCommGroupPoint : AddCommGroup E.Point :=
  E.toRoot.addCommGroup

open Classical in
private theorem toRoot_add (P Q : E.Point) : E.toRoot (P + Q) = E.toRoot P + E.toRoot Q := by
  change E.toRoot (E.toRoot.symm (E.toRoot P + E.toRoot Q)) = _
  exact Equiv.apply_symm_apply _ _

open Classical in
/-- The points of the Montgomery model and those of the root. Internal. -/
private noncomputable def montgomeryToRoot :
    E.toMontgomery.Point ≃ (PlaneModel.edwardsRoot E.a E.d).Point :=
  E.toMontgomery.pointEquivWeierstrass.trans
    (WeierstrassCurve.Affine.Point.equivOfEq (toWeierstrass_eq E)).toEquiv

open Classical in
private theorem montgomeryToRoot_add (Q₁ Q₂ : E.toMontgomery.Point) :
    E.montgomeryToRoot (Q₁ + Q₂) = E.montgomeryToRoot Q₁ + E.montgomeryToRoot Q₂ := by
  have h : E.toMontgomery.pointEquivWeierstrass (Q₁ + Q₂) =
      E.toMontgomery.pointEquivWeierstrass Q₁ + E.toMontgomery.pointEquivWeierstrass Q₂ := by
    rw [Curve.Realization.add_eq (R := E.toMontgomery.realization)]
    exact Equiv.apply_symm_apply _ _
  simp only [montgomeryToRoot, Equiv.trans_apply, h]
  exact (WeierstrassCurve.Affine.Point.equivOfEq (toWeierstrass_eq E)).map_add _ _

open Classical in
/-- The points of `E` are the points of its Montgomery model, as groups: both are the points of
the same root. Hidden construction, pinned by `u_toMontgomeryEquiv`, `v_toMontgomeryEquiv`,
`toMontgomeryEquiv_of_y_eq_one`, `toMontgomeryEquiv_of_x_eq_zero`, `toMontgomeryEquiv_symm_x`
and `toMontgomeryEquiv_symm_y` (`EllipticCurve.TwistedEdwards.Lemmas`). -/
noncomputable def toMontgomeryEquiv : E.Point ≃+ E.toMontgomery.Point where
  toEquiv := E.toRoot.trans E.montgomeryToRoot.symm
  map_add' P Q := by
    apply E.montgomeryToRoot.injective
    simp only [Equiv.toFun_as_coe, Equiv.trans_apply, Equiv.apply_symm_apply,
      montgomeryToRoot_add, toRoot_add]

/-- The curve realised by `E` (away from 6): that of its Montgomery model. Exposed: it only
fixes that the curve of `E` is the curve of `E.toMontgomery`; its invariants are `E.c₄`, `E.c₆`
(`toCurve_eq_mk`). -/
@[expose] noncomputable def toCurve [NeZero (6 : F)] : Curve F :=
  E.toMontgomery.toCurve

/-- The points of `E` are the points of its curve, as groups. Hidden construction. -/
noncomputable def pointEquiv [NeZero (6 : F)] : E.Point ≃+ E.toCurve.Point :=
  E.toMontgomeryEquiv.trans E.toMontgomery.pointEquiv

end TwistedEdwardsModel
