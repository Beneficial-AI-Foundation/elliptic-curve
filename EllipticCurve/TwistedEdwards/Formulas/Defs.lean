/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.TwistedEdwards.Coords.Lemmas

/-! # Twisted Edwards models: formulas in coordinates

The group operations in the coordinate systems of `EllipticCurve.TwistedEdwards.Coords.Defs`, as
exposed formulas for every `a`, named as in the Explicit-Formulas Database:

* `Projective.double` ("dbl-2008-bbjlp", Bernstein–Birkner–Joye–Lange–Peters, *Twisted Edwards
  curves*, 2008; here into completed coordinates);
* `Extended.add` ("add-2008-hwcd", Hisil–Wong–Carter–Dawson, *Twisted Edwards curves revisited*,
  2008: the complete extended addition), `Extended.double`, the
  structurally recursive `Extended.nsmul` by double-and-add, and the zero test `Extended.IsZero`.

Field inversion appears nowhere, so that kernel `decide` can evaluate them on constants.
Correctness with respect to `toPoint`, on a complete model, is in
`EllipticCurve.TwistedEdwards.Formulas.Lemmas`, together with the criteria that recognise a
sum in each coordinate system (`*.onCurve_of_eq_add`, `*.onCurve_and_toPoint_eq_add`), which also
prove other formulas built on these coordinates.

Ported from curve25519-dalek's Lean verification
(`Curve25519/Models/TwistedEdwards/Formulas/Defs.lean`, commit `d2e92e7`), without the mixed
additions with Niels points, and with `Projective.double` generalised from `a = -1` to every
`a`. -/

public section

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] {E : TwistedEdwardsModel F}

namespace Projective

/-- Doubling `(X : Y : Z) ↦ ((X : Z), (Y : T))` by "dbl-2008-bbjlp": `XX = X²`, `YY = Y²`,
`aXX = a XX`; the result is `((X + Y)² - XX - YY, YY - aXX, aXX + YY, 2 Z² - (aXX + YY))`, i.e.
`x = 2 X Y / (a X² + Y²)` and `y = (Y² - a X²) / (2 Z² - a X² - Y²)`. -/
@[expose] def double (P : E.Projective) : E.Completed :=
  let XX := P.X ^ 2
  let YY := P.Y ^ 2
  let aXX := E.a * XX
  ⟨(P.X + P.Y) ^ 2 - XX - YY, YY - aXX, aXX + YY, 2 * P.Z ^ 2 - (aXX + YY)⟩

end Projective

namespace Extended

/-- The complete addition in extended coordinates for any `a`, "add-2008-hwcd"
(Hisil–Wong–Carter–Dawson 2008, §3.1): `A = X₁ X₂`, `B = Y₁ Y₂`, `C = d T₁ T₂`,
`D = Z₁ Z₂`, `E = (X₁ + Y₁) (X₂ + Y₂) - A - B`, `F = D - C`, `G = D + C`, `H = B - a A`; the
result is `(E F : G H : F G : E H)`. No inversion: kernel `decide` can evaluate it. -/
@[expose] def add (P Q : E.Extended) : E.Extended :=
  let A := P.X * Q.X
  let B := P.Y * Q.Y
  let C := E.d * P.T * Q.T
  let D := P.Z * Q.Z
  let e := (P.X + P.Y) * (Q.X + Q.Y) - A - B
  let f := D - C
  let G := D + C
  let H := B - E.a * A
  ⟨e * f, G * H, f * G, e * H⟩

/-- Doubling in extended coordinates: `P.add P`. -/
@[expose] def double (P : E.Extended) : E.Extended :=
  P.add P

/-- Double-and-add with fuel `k`: `nsmulAux P k n` represents `n • P` for `n < 2 ^ k`
(`nsmulAux_spec` in `EllipticCurve.TwistedEdwards.Formulas.Lemmas`). Structural recursion on
the fuel, so that kernel `decide` can evaluate it. -/
@[expose] def nsmulAux (P : E.Extended) : ℕ → ℕ → E.Extended
  | 0, _ => identity
  | k + 1, n =>
    if n = 0 then identity
    else
      let Q := nsmulAux P k (n / 2)
      if n % 2 = 0 then Q.double else Q.double.add P

/-- Scalar multiplication `n • P` in extended coordinates by double-and-add on `add`, without
inversion, so that the kernel can evaluate it on constants (`toPoint_nsmul`). -/
@[expose] def nsmul (n : ℕ) (P : E.Extended) : E.Extended :=
  nsmulAux P n n

/-- The zero test without inversion: `(X : Y : Z : T)` represents `0 = (0, 1)` exactly when
`X = 0` and `Y = Z` (`isZero_iff`). -/
@[expose] def IsZero (P : E.Extended) : Prop :=
  P.X = 0 ∧ P.Y = P.Z

instance instDecidableIsZero [DecidableEq F] (P : E.Extended) : Decidable P.IsZero :=
  inferInstanceAs (Decidable (_ ∧ _))

end Extended

end TwistedEdwardsModel
