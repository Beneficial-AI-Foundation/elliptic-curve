/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Curve.Impl
public import Mathlib.Algebra.Group.TransferInstance

/-! # Realizations: how a model gets its group and its curve (internal)

A model of a curve (Montgomery, twisted Edwards, …) has its own type of points `P`. A
**realization** of `P` is a bijection `P ≃ W.Point` with the points of an elliptic Weierstrass
curve `W`. From it the model gets, with no further work:

* its group law, transported from Mathlib's (`Realization.addCommGroup`), with the
  characterising equations `zero_eq`, `neg_eq`, `add_eq`;
* its curve `Realization.toCurve` (that of `W`), identified with the curve of the model's own
  invariants by one certificate `u` (`toCurve_eq_mk`);
* the group isomorphism with the points of the curve (`Realization.pointEquiv`).

The Montgomery model is built this way. The twisted Edwards model transports its group from the
points of its plane model's root directly (`EllipticCurve.TwistedEdwards.Group`).

**Internal**, like `EllipticCurve.Curve.Impl`: import it privately in model definition modules. The
group law is transported with the classical `DecidableEq F`; write lemmas that mention the
Weierstrass sum under `open scoped Classical`. -/

public section

universe u v

namespace Curve

/-- A realization of the type `P` of points of a model: a bijection with the points of an
elliptic Weierstrass curve. -/
structure Realization (F : Type u) [Field F] (P : Type v) where
  /-- The Weierstrass curve. -/
  W : WeierstrassCurve F
  /-- It is elliptic. -/
  isElliptic : W.IsElliptic
  /-- The bijection between the points of the model and those of `W`. -/
  equiv : P ≃ W.toAffine.Point

namespace Realization

variable {F : Type u} [Field F] {P : Type v} (R : Realization F P)

attribute [instance] Realization.isElliptic

open scoped Classical in
/-- The group law on `P`, transported from Mathlib's group law on the points of `R.W`. -/
noncomputable abbrev addCommGroup : AddCommGroup P :=
  R.equiv.addCommGroup

/-- The zero of the transported group. -/
theorem zero_eq : letI := R.addCommGroup; (0 : P) = R.equiv.symm 0 := rfl

open scoped Classical in
/-- The negation of the transported group. -/
theorem neg_eq (a : P) : letI := R.addCommGroup; -a = R.equiv.symm (-R.equiv a) := rfl

open scoped Classical in
/-- The sum of the transported group. -/
theorem add_eq (a b : P) : letI := R.addCommGroup; a + b = R.equiv.symm (R.equiv a + R.equiv b) :=
  rfl

variable [NeZero (6 : F)]

/-- The curve of the model: that of `R.W`. -/
noncomputable def toCurve : Curve F :=
  ofWeierstrass R.W

/-- The curve of a realization is the curve of its Weierstrass model. -/
private theorem toCurve_def : R.toCurve = ofWeierstrass R.W := by
  unfold toCurve; rfl

/-- **The curve of a realization**, by a certificate: if the invariants of `R.W` are those of the
model up to the weights of `u`, the curve is the curve with the model's invariants. -/
theorem toCurve_eq_mk {c₄ c₆ : F} (h : c₄ ^ 3 - c₆ ^ 2 ≠ 0) (u : F) (hu : u ≠ 0)
    (h₄ : R.W.c₄ = u ^ 4 * c₄) (h₆ : R.W.c₆ = u ^ 6 * c₆) : R.toCurve = Curve.mk c₄ c₆ h := by
  rw [toCurve_def, ofWeierstrass_def]
  exact mk_eq_mk_of u hu h₄ h₆

open scoped Classical in
/-- The points of the model are the points of its curve, as groups. -/
noncomputable def pointEquiv : letI := R.addCommGroup; P ≃+ R.toCurve.Point :=
  letI := R.addCommGroup
  R.equiv.addEquiv.trans (pointEquivOfWeierstrass R.W).symm

end Realization

end Curve
