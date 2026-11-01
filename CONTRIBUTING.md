# Contributing to EllipticCurve

Guidelines for whoever works on this library (person or agent).
Read `README.md` first; it lists possible next steps.

## Scope

Elliptic curves *in the mathematical sense*, over fields away from 6: curves, models, groups, twists, invariants and classification.
Material that exists only for an application (coordinate systems for fast arithmetic, encodings, protocols) belongs to libraries built on this one.

## Constraints

* **Toolchain:** the Lean and Mathlib versions match those used by Aeneas (today Lean v4.35.0, Mathlib `v4.35.0`); bump them only together with Aeneas.
* **Characteristic:** fields **away from 6** (characteristic ≠ 2, 3), written `[NeZero (6 : F)]`, and only where needed; say "away from 6" in docstrings.
* **Provenance:** when a proof follows another source, say so in the module docstring (project, file and commit, or reference, and what changed); Apache-2.0 material keeps its credit.

## Conventions

* **Layout.** Each topic has `…/Defs.lean` (structures, definitions, instances) and `…/Lemmas.lean` (`import all …/Defs`, the characterising lemmas); a large self-contained part gets its own module in the topic folder (for example `TwistedEdwards/Group.lean`).
  `EllipticCurve/Mathlib/` mirrors Mathlib paths and follows Mathlib's names.
* **Module system.** Every file is `module` with `public section`; definitions are hidden by default.
  Only formulas that `decide` or other modules must evaluate are `@[expose]`.
  Instances on hidden types are `@[no_expose]`.
  Constructions meant to be swappable (`Curve`, the point types' groups, `toCurve`, `pointEquiv`, the model equivalences) get characterising lemmas only.
* **Public API.** Model-independent: each model has its own point type, `toCurve` and `pointEquiv : M.Point ≃+ M.toCurve.Point`.
  Weierstrass roots and plane models are tools for model authors, not part of the API.
* **Imports.** `public import` only what public statements mention.
  Order: public project, public Mathlib, `import all`, private project, private Mathlib, each sorted.
* **Computation.** `decide` must not meet a field inverse: state tested predicates without division.
* **Style.** Mathlib style.

## Adding a model

A model is its parameters, its own point type, and a plane model of a Weierstrass root.

* **Weierstrass-type models** (an affine-linear change of the root's coordinates): use `PlaneModel.linear`; points, coordinates and the group law in coordinates come from Mathlib.
* **Other models:** give the formula as a `PlaneModel.Formula` and prove its identities (`PlaneModel.IsAddFormula`: closure, inverse, denominators nonzero on solutions, an irreducible equation), plus symmetry and the neutral element; `PlaneModel.coords_add_of_isAddFormula` gives the group law.
  See `PlaneModel/EdwardsIdentities.lean`.
* **The point type:** transport the root's group along the bijection given by the coordinates (see `TwistedEdwards/Group.lean`, or `Curve.Realization` as in `Montgomery/Defs.lean`).
* Never take a model's invariants from the literature without a proof: a sign error in `c₆` is a twist, invisible to `j`.

## Checks

```sh
lake build --wfail
lake lint
lake build --wfail EllipticCurveTest
```
