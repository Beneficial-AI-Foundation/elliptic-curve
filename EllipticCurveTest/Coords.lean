/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurveTest.Models
-- The tests evaluate their own definitions by `decide`, so they are exposed.
/-! # Tests: the ladder and the coordinate formulas over `𝔽₁₁`

Exhaustive checks by kernel `decide`, on the curves of `EllipticCurveTest.Models`:

* **The Montgomery ladder** (`MontgomeryModel.XZ.ladderXZ`, with `a24 = 2` for `(A, B) = (10, 1)`)
  against brute-force multiples for the chord-and-tangent law, on every point of `(10, 1)` and of
  its twist `(10, 2)` by the non-square `2`, for all scalars below `2⁴`.
* **Twisted Edwards coordinates** on `x² + y² = 1 + 8 x² y²`: the extended addition, doubling and
  scalar multiplication and the projective doubling agree with the affine formula, and their
  results are on the curve. `OnCurve` and `IsZero` are decided by the kernel, without division. -/

@[expose] public section

namespace CoordTests

open ModelTests

/-! ### The Montgomery ladder -/

/-- The ladder constant of `(10, 1)` is `a24 = (10 - 2) / 4 = 2`. -/
theorem a24_eq : (⟨10, 1⟩ : MontgomeryModel (ZMod 11)).a24 = 2 := by
  simp only [MontgomeryModel.a24, div_eq]
  decide

/-- The library's ladder of `(10, 1)` is the projective ladder at `a24 = 2`, read through
`U / W = U W⁹`. -/
theorem ladder_eq (bits k : ℕ) (u : ZMod 11) :
    (⟨10, 1⟩ : MontgomeryModel (ZMod 11)).ladder bits k u =
      (MontgomeryModel.XZ.ladderXZ 2 bits k u).U *
        (MontgomeryModel.XZ.ladderXZ 2 bits k u).W ^ 9 := by
  rw [MontgomeryModel.ladder, a24_eq, MontgomeryModel.XZ.ladder, MontgomeryModel.XZ.toU, div_eq]

/-- The ladder over 4 bits, computably. -/
def ladderU (k : ℕ) (u : ZMod 11) : ZMod 11 :=
  (MontgomeryModel.XZ.ladderXZ 2 4 k u).U * (MontgomeryModel.XZ.ladderXZ 2 4 k u).W ^ 9

/-- The points of `B v² = u³ + 10 u² + u`, with `none` the point at infinity. -/
def ptsB (B : ZMod 11) : List (Option (ZMod 11 × ZMod 11)) :=
  none :: ((List.finRange 11).flatMap fun u => (List.finRange 11).filterMap fun v =>
    let u : ZMod 11 := u
    let v : ZMod 11 := v
    if B * v ^ 2 = u ^ 3 + 10 * u ^ 2 + u then some (some (u, v)) else none)

/-- The chord-and-tangent law of `B v² = u³ + 10 u² + u`, computably. -/
def maddB (B : ZMod 11) :
    Option (ZMod 11 × ZMod 11) → Option (ZMod 11 × ZMod 11) → Option (ZMod 11 × ZMod 11)
  | none, Q => Q
  | P, none => P
  | some P, some Q =>
    if P.1 = Q.1 ∧ P.2 = -Q.2 then none
    else
      let l := if P.1 = Q.1 then (3 * P.1 ^ 2 + 2 * 10 * P.1 + 1) * (2 * B * P.2) ^ 9
        else (Q.2 - P.2) * (Q.1 - P.1) ^ 9
      let u := B * l ^ 2 - 10 - P.1 - Q.1
      some (u, l * (P.1 - u) - P.2)

/-- `k • P` by repeated addition. -/
def nsmulB (B : ZMod 11) (P : Option (ZMod 11 × ZMod 11)) : ℕ → Option (ZMod 11 × ZMod 11)
  | 0 => none
  | k + 1 => maddB B (nsmulB B P k) P

/-- The `u`-coordinate, `0` at infinity. -/
def uOf : Option (ZMod 11 × ZMod 11) → ZMod 11
  | none => 0
  | some P => P.1

/-- `2` is not a square in `𝔽₁₁`, so `(10, 2)` is the quadratic twist of `(10, 1)`. -/
example : ¬ IsSquare (2 : ZMod 11) ∧
    (⟨10, 1⟩ : MontgomeryModel (ZMod 11)).twist 2 = ⟨10, 2⟩ := by
  refine ⟨by unfold IsSquare; decide, ?_⟩
  rw [MontgomeryModel.twist_def, one_mul]

/-- Between them, the curve and its twist have every `u` as a `u`-coordinate. -/
example : ∀ u : ZMod 11, ∃ P ∈ ptsB 1 ++ ptsB 2, uOf P = u := by decide +kernel

/-- **The ladder computes `u(k • P)`** on every point of the curve and of its twist, for every
`k < 2⁴`. -/
example : ∀ B ∈ [(1 : ZMod 11), 2], ∀ P ∈ ptsB B, ∀ k ∈ List.range 16,
    ladderU k (uOf P) = uOf (nsmulB B P k) := by
  decide +kernel

/-! ### Twisted Edwards coordinates -/

/-- Extended coordinates `(x : y : 1 : x y)` of an affine point. -/
def toExt (P : ZMod 11 × ZMod 11) : E.Extended :=
  ⟨P.1, P.2, 1, P.1 * P.2⟩

/-- The affine point `(X / Z, Y / Z)` of extended coordinates. -/
def ofExt (R : E.Extended) : ZMod 11 × ZMod 11 :=
  (R.X * R.Z ^ 9, R.Y * R.Z ^ 9)

/-- The affine point `(X / Z, Y / T)` of completed coordinates. -/
def ofCompleted (R : E.Completed) : ZMod 11 × ZMod 11 :=
  (R.X * R.Z ^ 9, R.Y * R.T ^ 9)

/-- `n • P` for the affine formula. -/
def nsmulE (P : ZMod 11 × ZMod 11) : ℕ → ZMod 11 × ZMod 11
  | 0 => (0, 1)
  | n + 1 => add (nsmulE P n) P

/-- Every affine point is on the curve in extended coordinates (decided without division). -/
example : ∀ P ∈ pts, (toExt P).OnCurve := by decide +kernel

/-- The extended addition is closed and agrees with the affine formula. -/
example : ∀ P ∈ pts, ∀ Q ∈ pts,
    ((toExt P).add (toExt Q)).OnCurve ∧ ofExt ((toExt P).add (toExt Q)) = add P Q := by
  decide +kernel

/-- Scalar multiplication in extended coordinates agrees with repeated affine addition, and
`8 • P = 0` (the group has order `8`) is detected by `IsZero`. -/
example : ∀ P ∈ pts, (∀ n ∈ List.range 9,
    ((TwistedEdwardsModel.Extended.nsmul n (toExt P)).OnCurve ∧
      ofExt (TwistedEdwardsModel.Extended.nsmul n (toExt P)) = nsmulE P n)) ∧
    (TwistedEdwardsModel.Extended.nsmul 8 (toExt P)).IsZero := by
  decide +kernel

/-- Projective doubling ("dbl-2008-bbjlp", here with `a = 1`) is on the curve and agrees with the
affine formula. -/
example : ∀ P ∈ pts,
    let R := (⟨P.1, P.2, 1⟩ : E.Projective).double
    R.OnCurve ∧ ofCompleted R = add P P := by
  decide +kernel

/-- Projective equality is decided: `(x : y : 1 : x y)` and `(2 x : 2 y : 2 : 4 x y)` are equal,
`(x : y : 1 : x y)` and `(-x : y : 1 : -x y)` are not unless `x = 0`. -/
example : ∀ P ∈ pts, (toExt P).ProjEq ⟨2 * P.1, 2 * P.2, 2, 4 * P.1 * P.2⟩ ∧
    ((toExt P).ProjEq (toExt (-P.1, P.2)) ↔ P.1 = 0) := by
  decide +kernel

/-- Negation, the conversions to completed coordinates and completed projective equality, decided:
the negations represent `(-x, y)`, and every conversion of `(x : y : 1 : x y)` represents
`(x, y)`. -/
example : ∀ P ∈ pts,
    ofExt (toExt P).neg = (-P.1, P.2) ∧
    (⟨P.1, P.2, 1⟩ : E.Projective).neg.OnCurve ∧
    ofCompleted (⟨P.1, P.2, 1, 1⟩ : E.Completed).neg = (-P.1, P.2) ∧
    (toExt P).toCompleted.OnCurve ∧ ofCompleted (toExt P).toCompleted = P ∧
    (toExt P).toProjective.toCompleted.OnCurve ∧
    ofCompleted (toExt P).toProjective.toCompleted = P ∧
    (toExt P).toCompleted.ProjEq ⟨3 * P.1, 5 * P.2, 3, 5⟩ ∧
    (TwistedEdwardsModel.Completed.identity : E.Completed).OnCurve := by
  decide +kernel

end CoordTests
