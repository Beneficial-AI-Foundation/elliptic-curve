module
public import EllipticCurve.Curve.Defs
public import EllipticCurve.Curve.Fiber
public import EllipticCurve.Curve.JD
public import EllipticCurve.Curve.Lemmas
public import EllipticCurve.Curve.Mass
public import EllipticCurve.Curve.Twist
public import EllipticCurve.Curve.Weierstrass
public import EllipticCurve.Field.AwayFromSix
public import EllipticCurve.FunctionField.Constants
public import EllipticCurve.FunctionField.Place
public import EllipticCurve.Montgomery.Count
public import EllipticCurve.Montgomery.Defs
public import EllipticCurve.Montgomery.HasModel
public import EllipticCurve.Montgomery.Lemmas
public import EllipticCurve.Montgomery.Rescale
public import EllipticCurve.Montgomery.XOnly.Defs
public import EllipticCurve.Montgomery.XOnly.Lemmas
public import EllipticCurve.PlaneModel.Basic
public import EllipticCurve.PlaneModel.EdwardsAddition
public import EllipticCurve.PlaneModel.EdwardsFormula
public import EllipticCurve.PlaneModel.EdwardsGroupLaw
public import EllipticCurve.PlaneModel.EdwardsIdentities
public import EllipticCurve.PlaneModel.EdwardsPoints
public import EllipticCurve.PlaneModel.GroupLaw
public import EllipticCurve.PlaneModel.Linear
public import EllipticCurve.PlaneModel.Montgomery
public import EllipticCurve.PlaneModel.Translation
public import EllipticCurve.TwistedEdwards.Defs
public import EllipticCurve.TwistedEdwards.Even
public import EllipticCurve.TwistedEdwards.Formula
public import EllipticCurve.TwistedEdwards.Group
public import EllipticCurve.TwistedEdwards.HasModel
public import EllipticCurve.TwistedEdwards.Lemmas
public import EllipticCurve.Weierstrass.AutConstants
public import EllipticCurve.Weierstrass.Bridge
public import EllipticCurve.Weierstrass.Generic
public import EllipticCurve.Weierstrass.Places
public import EllipticCurve.Weierstrass.Rigidity
public import EllipticCurve.Weierstrass.Subst
public import EllipticCurve.Weierstrass.Translation
public import EllipticCurve.Weierstrass.TranslationPlaces
import EllipticCurve.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import EllipticCurve.Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfInvariants
import EllipticCurve.Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithC

/-! # EllipticCurve: elliptic curves and their models

Elliptic curves over a field away from 6 (`[NeZero (6 : F)]`, `EllipticCurve.Field.AwayFromSix`)
and their models.

* `EllipticCurve.Curve.*`: the curve `Curve F`, independent of any model: invariants `(c₄, c₆)` up
  to `(u⁴ c₄, u⁶ c₆)`, with its j-invariant and group of points; quadratic twists (`Twist`); the
  (j, D) classification and the number of curves over a finite field (`Fiber`, `JD`); the mass
  formula (`Mass`); Weierstrass models and their automorphisms (`Weierstrass`).
* `EllipticCurve.Montgomery.*`: the Montgomery model, its curve and group law in coordinates, the
  criterion for a curve to have a Montgomery model (`HasModel`), rescalings (`Rescale`), point
  counts (`Count`) and x-only scalar multiplication (`XOnly`).
* `EllipticCurve.TwistedEdwards.*`: the twisted Edwards model, its complete addition formula
  (`Formula`) and group (`Group`, `Lemmas`), the criterion for a curve to have a complete twisted
  Edwards model (`HasModel`), and its even points (`Even`).
* `EllipticCurve.FunctionField.*`, `EllipticCurve.Weierstrass.*`: places of a function field and
  values of functions at them; the points of a Weierstrass curve are the rational places of its
  function field, and an isomorphism of function fields fixing the place at infinity is a change of
  variables (`Places`); rigidity of automorphisms (`Rigidity`, `AutConstants`, `Generic`).
* `EllipticCurve.PlaneModel.*`: the model framework. A plane model is a pair of generating
  functions on the function field of a Weierstrass root with their equation (`Basic`); its
  coordinates identify points with the nonsingular solutions of an irreducible equation.
  Weierstrass-type models come from Mathlib's group law (`Linear`); other models get their group
  law from the identities of their formula (`Translation`, `GroupLaw`), as twisted Edwards does
  (`EdwardsIdentities`, `EdwardsGroupLaw`).

The modules staged for Mathlib (`EllipticCurve.Mathlib.*`: the point map of a change of variables,
the classification of Weierstrass curves by their invariants, the curves with given invariants) are
imported privately here, so that no Weierstrass name reaches importers of this root through them.
`EllipticCurve.Curve.Impl` (internal to model definitions) is not part of this root. -/
