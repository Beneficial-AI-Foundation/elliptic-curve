# EllipticCurve

A Lean library, built on Mathlib, of elliptic curves over fields away from 6 (characteristic ≠ 2, 3) and their models.

At the time of writing (November 2026) Mathlib contains only Weierstrass curves whereas [Tau Ceti](https://github.com/TauCetiProject/TauCeti) contains many strong and relevant results.
The purpose of this repo is as a stop-gap for those needing multiple elliptic curve models prior to such being supported in Mathlib.

## Highlights

- **A model-independent curve.** `Curve F` is a curve in its own right, not a choice of equation: invariants `(c₄, c₆)` up to `(u⁴ c₄, u⁶ c₆)`.
  Every model has a `toCurve`, and two models describe the same curve exactly when one `u` relates their invariants.
- **Points are places.** The points of a curve are the rational places of its function field, so a model is just a choice of coordinate functions; its points and group come for free, and isomorphisms of function fields are isomorphisms of curves.
- **Group law from identities (rigidity)**, making new models easy to define: a model supplies its addition formula and a handful of identities, and the group law follows (associativity never needs to be checked).

## Contents

- **`Curve F`**: elliptic curves independent of any model, as invariants `(c₄, c₆)` up to `(u⁴ c₄, u⁶ c₆)`.
  It comes with:
  - the j-invariant, quadratic twists and the (j, D) classification;
  - automorphism groups;
  - point counts over finite fields and the mass formula.
- **Models**, each with its own point type, group law in coordinates and curve:
  - Montgomery (including the x-only ladder);
  - twisted Edwards (complete);
  - Weierstrass, via Mathlib.

  Also criteria for a curve to have a Montgomery or a complete twisted Edwards model.
- **The model framework**:
  - the points of a Weierstrass curve are the rational places of its function field;
  - plane models, i.e., models given by coordinate functions and an equation;
  - a rigidity theorem: an addition formula satisfying a few identities is the group law.

Coordinate systems for fast arithmetic, encodings and protocols belong to applications built on this library.

## Possible next steps

Internally this library is still Weierstrass-centric: every group law is Mathlib's Weierstrass group law transported to a model, and a model is defined by coordinates on the function field of a Weierstrass curve.
The natural long-term direction is elliptic curves defined entirely intrinsically, as genus-one function fields with a rational place, with the group law on places from the degree-zero divisor class group, and Weierstrass coordinates obtained by Riemann–Roch.
[Tau Ceti](https://github.com/TauCetiProject/TauCeti) already proves this (Riemann–Roch, elliptic function fields and their intrinsic group law, Weierstrass coordinates of a genus-one function field).
