/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurveTest.Models
import Mathlib.Tactic.NormNum.Prime
-- The tests evaluate their own definitions by `decide`, so they are exposed.
/-! # Tests: the ladder and the coordinate formulas

Checks by kernel `decide`, exhaustive over small prime fields, against independent computations:

* **The Montgomery ladder** (`MontgomeryModel.XZ.ladderXZ`, with `a24 = 2` for `(A, B) = (10, 1)`
  over `𝔽₁₁`) against brute-force multiples for the chord-and-tangent law (whose slope and
  coordinates are the library's, `slopeB_eq`, `maddB_eq`), on every point of `(10, 1)` and of its
  twist `(10, 2)` by the non-square `2`: for all scalars (`k % 2⁴` beyond `2⁴`), and over bit
  sequences (`ladderBitsXZ`).
* **RFC 7748 §5.2**: two X25519 test vectors, over `ZMod (2²⁵⁵ - 19)` (a commutative ring is
  enough for the projective ladder), with the RFC's decoded scalars and `u`-coordinates.
* **Twisted Edwards coordinates** on `x² + y² = 1 + 8 x² y²` over `𝔽₁₁` (`a = 1`) and on
  `-x² + y² = 1 + 2 x² y²` over `𝔽₁₃` (`a = -1`): the extended addition, doubling and scalar
  multiplication and the projective doubling agree with the affine formula; negation, the
  conversions and projective equality represent the expected points; `OnCurve`, `ProjEq` and
  `IsZero` are decided by the kernel, without division, both ways. -/

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

/-- The library's ladder of `(10, 1)` over a bit sequence, read through `U / W = U W⁹`. -/
theorem ladderBits_eq (bs : List Bool) (u : ZMod 11) :
    (⟨10, 1⟩ : MontgomeryModel (ZMod 11)).ladderBits bs u =
      (MontgomeryModel.XZ.ladderBitsXZ 2 bs u).U *
        (MontgomeryModel.XZ.ladderBitsXZ 2 bs u).W ^ 9 := by
  rw [MontgomeryModel.ladderBits, a24_eq, MontgomeryModel.XZ.ladderBits,
    MontgomeryModel.XZ.toU, div_eq]

/-- The ladder over 4 bits, computably. -/
def ladderU (k : ℕ) (u : ZMod 11) : ZMod 11 :=
  (MontgomeryModel.XZ.ladderXZ 2 4 k u).U * (MontgomeryModel.XZ.ladderXZ 2 4 k u).W ^ 9

/-- The ladder over a bit sequence, computably. -/
def ladderBitsU (bs : List Bool) (u : ZMod 11) : ZMod 11 :=
  (MontgomeryModel.XZ.ladderBitsXZ 2 bs u).U * (MontgomeryModel.XZ.ladderBitsXZ 2 bs u).W ^ 9

/-- The points of `B v² = u³ + 10 u² + u`, with `none` the point at infinity. -/
def ptsB (B : ZMod 11) : List (Option (ZMod 11 × ZMod 11)) :=
  none :: ((List.finRange 11).flatMap fun u => (List.finRange 11).filterMap fun v =>
    let u : ZMod 11 := u
    let v : ZMod 11 := v
    if B * v ^ 2 = u ^ 3 + 10 * u ^ 2 + u then some (some (u, v)) else none)

/-- The slope of the chord-and-tangent law of `B v² = u³ + 10 u² + u`, computably. -/
def slopeB (B : ZMod 11) (P Q : ZMod 11 × ZMod 11) : ZMod 11 :=
  if P.1 = Q.1 then (3 * P.1 ^ 2 + 2 * 10 * P.1 + 1) * (2 * B * P.2) ^ 9
  else (Q.2 - P.2) * (Q.1 - P.1) ^ 9

/-- The computable slope is the library's, for every `B`. -/
theorem slopeB_eq (B : ZMod 11) (P Q : ZMod 11 × ZMod 11) (h : ¬(P.1 = Q.1 ∧ P.2 = -Q.2)) :
    (⟨10, B⟩ : MontgomeryModel (ZMod 11)).slope P.1 P.2 Q.1 Q.2 = slopeB B P Q := by
  by_cases hu : P.1 = Q.1
  · have hv : P.2 ≠ -Q.2 := fun hv => h ⟨hu, hv⟩
    simp [MontgomeryModel.slope, MontgomeryModel.tangentSlope, slopeB, hu, hv, div_eq]
  · simp [MontgomeryModel.slope, MontgomeryModel.chordSlope, slopeB, hu, div_eq]

/-- The chord-and-tangent law of `B v² = u³ + 10 u² + u`, computably. -/
def maddB (B : ZMod 11) :
    Option (ZMod 11 × ZMod 11) → Option (ZMod 11 × ZMod 11) → Option (ZMod 11 × ZMod 11)
  | none, Q => Q
  | P, none => P
  | some P, some Q =>
    if P.1 = Q.1 ∧ P.2 = -Q.2 then none
    else
      let u := B * slopeB B P Q ^ 2 - 10 - P.1 - Q.1
      some (u, slopeB B P Q * (P.1 - u) - P.2)

/-- On two affine points that are not inverse, `maddB` is the library's addition formula
(`MontgomeryModel.addU`, `addV` at `MontgomeryModel.slope`; see `MontgomeryModel.some_add_some`). -/
theorem maddB_eq (B : ZMod 11) (P Q : ZMod 11 × ZMod 11) (h : ¬(P.1 = Q.1 ∧ P.2 = -Q.2)) :
    let M : MontgomeryModel (ZMod 11) := ⟨10, B⟩
    maddB B (some P) (some Q) =
      some (M.addU P.1 Q.1 (M.slope P.1 P.2 Q.1 Q.2),
        M.addV P.1 Q.1 P.2 (M.slope P.1 P.2 Q.1 Q.2)) := by
  simp only [maddB, h, ↓reduceIte, slopeB_eq B P Q h, MontgomeryModel.addU, MontgomeryModel.addV]

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

/-- **The ladder over 4 bits computes `u((k % 2⁴) • P)`** on every point of the curve and of its
twist, for every `k < 40`. -/
example : ∀ B ∈ [(1 : ZMod 11), 2], ∀ P ∈ ptsB B, ∀ k ∈ List.range 40,
    ladderU k (uOf P) = uOf (nsmulB B P (k % 16)) := by
  decide +kernel

/-- **The ladder over a bit sequence `bs` computes `u(n • P)`** for `n = Nat.ofDigits 2 bs.reverse`,
on every point of the curve and of its twist, for all sequences of 5 bits (leading zeros
included). -/
example : ∀ B ∈ [(1 : ZMod 11), 2], ∀ P ∈ ptsB B, ∀ k ∈ List.range 32,
    let bs := (List.range 5).reverse.map k.testBit
    ladderBitsU bs (uOf P) = uOf (nsmulB B P (Nat.ofDigits 2 (bs.reverse.map Bool.toNat))) := by
  decide +kernel

/-! ### RFC 7748 §5.2 -/

/-- The prime `2²⁵⁵ - 19` of Curve25519. -/
def p25519 : ℕ := 2 ^ 255 - 19

/-- RFC 7748 §5.2, first vector: decoded scalar `31029842…6496` (bytes `a546e36b…`), `u`
`34426434…4838` (bytes `e6db6867…`), output `37325765…9395` (bytes `c3da5537…`); `a24 = 121665`
for `A = 486662`. -/
example :
    let R := MontgomeryModel.XZ.ladderXZ (121665 : ZMod p25519) 255
      31029842492115040904895560451863089656472772604678260265531221036453811406496
      34426434033919594451155107781188821651316167215306631574996226621102155684838
    R.U = 37325765543539916631701301279660700968428932651319597985674090122993663859395 * R.W ∧
      R.W ≠ 0 := by
  decide +kernel

/-- RFC 7748 §6.1: Alice's public key, the ladder at `u = 9` for the decoded scalar
`48024180…5280` (bytes `77076d0a…`), is `48084050…0437` (bytes `8520f009…`). -/
example :
    let R := MontgomeryModel.XZ.ladderXZ (121665 : ZMod p25519) 255
      48024180843069071553745934684982006431825596986621126406018887516696408295280 9
    R.U = 48084050389777770101701157326923977117307187144965043058462938058489685090437 * R.W ∧
      R.W ≠ 0 := by
  decide +kernel

/-! ### Twisted Edwards coordinates, `a = 1` -/

/-- Extended coordinates `(x : y : 1 : x y)` of an affine point. -/
def toExt (P : ZMod 11 × ZMod 11) : E.Extended :=
  ⟨P.1, P.2, 1, P.1 * P.2⟩

/-- The affine point `(X / Z, Y / Z)` of extended coordinates. -/
def ofExt (R : E.Extended) : ZMod 11 × ZMod 11 :=
  (R.X * R.Z ^ 9, R.Y * R.Z ^ 9)

/-- The affine point `(X / Z, Y / Z)` of projective coordinates. -/
def ofProj (R : E.Projective) : ZMod 11 × ZMod 11 :=
  (R.X * R.Z ^ 9, R.Y * R.Z ^ 9)

/-- The affine point `(X / Z, Y / T)` of completed coordinates. -/
def ofCompleted (R : E.Completed) : ZMod 11 × ZMod 11 :=
  (R.X * R.Z ^ 9, R.Y * R.T ^ 9)

/-- `n • P` for the affine formula. -/
def nsmulE (P : ZMod 11 × ZMod 11) : ℕ → ZMod 11 × ZMod 11
  | 0 => (0, 1)
  | n + 1 => add (nsmulE P n) P

/-- The maps from affine points are the coordinates `(x : y : 1 : x y)`, `(x : y : 1)`,
`((x : 1), (y : 1))`. -/
example (P : E.Point) :
    P.toExtended = toExt (P.x, P.y) ∧ P.toProjective = ⟨P.x, P.y, 1⟩ ∧
      P.toCompleted = ⟨P.x, P.y, 1, 1⟩ :=
  ⟨rfl, rfl, rfl⟩

/-- `OnCurve` holds exactly on the curve: every affine point is on it in each system, and tuples
off the curve, with a zero denominator, or with `X Y ≠ Z T` are not. -/
example : (∀ P ∈ pts, (toExt P).OnCurve ∧ (⟨P.1, P.2, 1⟩ : E.Projective).OnCurve ∧
      (⟨P.1, P.2, 1, 1⟩ : E.Completed).OnCurve) ∧
    ¬ (⟨1, 1, 1, 1⟩ : E.Extended).OnCurve ∧ ¬ (⟨0, 1, 0, 0⟩ : E.Extended).OnCurve ∧
    ¬ (⟨0, 1, 1, 1⟩ : E.Extended).OnCurve ∧ ¬ (⟨1, 1, 1⟩ : E.Projective).OnCurve ∧
    ¬ (⟨0, 1, 1, 0⟩ : E.Completed).OnCurve ∧ ¬ (⟨1, 1, 1, 1⟩ : E.Completed).OnCurve := by
  decide +kernel

/-- The extended addition is closed and agrees with the affine formula. -/
example : ∀ P ∈ pts, ∀ Q ∈ pts,
    ((toExt P).add (toExt Q)).OnCurve ∧ ofExt ((toExt P).add (toExt Q)) = add P Q := by
  decide +kernel

/-- Scalar multiplication in extended coordinates agrees with repeated affine addition. -/
example : ∀ P ∈ pts, ∀ n ∈ List.range 9,
    (TwistedEdwardsModel.Extended.nsmul n (toExt P)).OnCurve ∧
      ofExt (TwistedEdwardsModel.Extended.nsmul n (toExt P)) = nsmulE P n := by
  decide +kernel

/-- `IsZero` detects exactly the neutral element `(0, 1)`, and `8 • P = 0` (the group has
order `8`). -/
example : ∀ P ∈ pts, ((toExt P).IsZero ↔ P = (0, 1)) ∧
    (TwistedEdwardsModel.Extended.nsmul 8 (toExt P)).IsZero := by
  decide +kernel

/-- Projective doubling ("dbl-2008-bbjlp", here with `a = 1`) is on the curve and agrees with the
affine formula, from a scaled representative. -/
example : ∀ P ∈ pts,
    let R := (⟨3 * P.1, 3 * P.2, 3⟩ : E.Projective).double
    R.OnCurve ∧ ofCompleted R = add P P := by
  decide +kernel

/-- The conversions represent the same point: from completed (a doubling result) to extended and
projective, and from projective to extended and completed. -/
example : ∀ P ∈ pts,
    let R := (⟨P.1, P.2, 1⟩ : E.Projective).double
    let S : E.Projective := ⟨2 * P.1, 2 * P.2, 2⟩
    R.toExtended.OnCurve ∧ ofExt R.toExtended = add P P ∧
    R.toProjective.OnCurve ∧ ofProj R.toProjective = add P P ∧
    S.toExtended.OnCurve ∧ ofExt S.toExtended = P ∧
    S.toCompleted.OnCurve ∧ ofCompleted S.toCompleted = P ∧
    (toExt P).toProjective.OnCurve ∧ ofProj (toExt P).toProjective = P ∧
    (toExt P).toCompleted.OnCurve ∧ ofCompleted (toExt P).toCompleted = P := by
  decide +kernel

/-- Projective equality is equality of the represented points, in each system. -/
example : ∀ P ∈ pts, ∀ Q ∈ pts,
    ((toExt P).ProjEq ⟨2 * Q.1, 2 * Q.2, 2, 4 * Q.1 * Q.2⟩ ↔ P = Q) ∧
    ((⟨P.1, P.2, 1⟩ : E.Projective).ProjEq ⟨3 * Q.1, 3 * Q.2, 3⟩ ↔ P = Q) ∧
    ((⟨P.1, P.2, 1, 1⟩ : E.Completed).ProjEq ⟨3 * Q.1, 5 * Q.2, 3, 5⟩ ↔ P = Q) := by
  decide +kernel

/-- The identities are on the curve and represent `(0, 1)`; the negations represent `(-x, y)`. -/
example : (TwistedEdwardsModel.Extended.identity : E.Extended).OnCurve ∧
    ofExt TwistedEdwardsModel.Extended.identity = (0, 1) ∧
    (TwistedEdwardsModel.Projective.identity : E.Projective).OnCurve ∧
    ofProj TwistedEdwardsModel.Projective.identity = (0, 1) ∧
    (TwistedEdwardsModel.Completed.identity : E.Completed).OnCurve ∧
    ofCompleted TwistedEdwardsModel.Completed.identity = (0, 1) ∧
    ∀ P ∈ pts, (toExt P).neg.OnCurve ∧ ofExt (toExt P).neg = (-P.1, P.2) ∧
      (⟨P.1, P.2, 1⟩ : E.Projective).neg.OnCurve ∧
      ofProj (⟨P.1, P.2, 1⟩ : E.Projective).neg = (-P.1, P.2) ∧
      (⟨P.1, P.2, 1, 1⟩ : E.Completed).neg.OnCurve ∧
      ofCompleted (⟨P.1, P.2, 1, 1⟩ : E.Completed).neg = (-P.1, P.2) := by
  decide +kernel

/-! ### Twisted Edwards coordinates, `a = -1` -/

instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- The complete twisted Edwards curve `-x² + y² = 1 + 2 x² y²` over `𝔽₁₃`. -/
def E13 : TwistedEdwardsModel (ZMod 13) := ⟨-1, 2⟩

/-- It is complete: `-1` is a nonzero square and `2` is not a square. -/
example : IsSquare (-1 : ZMod 13) ∧ ¬ IsSquare (2 : ZMod 13) := by
  unfold IsSquare; decide

/-- Its points. -/
def pts13 : List (ZMod 13 × ZMod 13) :=
  (List.finRange 13).flatMap fun x => (List.finRange 13).filterMap fun y =>
    let x : ZMod 13 := x
    let y : ZMod 13 := y
    if -x ^ 2 + y ^ 2 = 1 + 2 * x ^ 2 * y ^ 2 then some (x, y) else none

/-- The affine addition formula for `a = -1`, `d = 2`, computably (`a / b = a b¹¹` in `𝔽₁₃`). -/
def add13 (P Q : ZMod 13 × ZMod 13) : ZMod 13 × ZMod 13 :=
  ((P.1 * Q.2 + Q.1 * P.2) * (1 + 2 * P.1 * Q.1 * P.2 * Q.2) ^ 11,
    (P.2 * Q.2 + P.1 * Q.1) * (1 - 2 * P.1 * Q.1 * P.2 * Q.2) ^ 11)

/-- `n • P` for the affine formula. -/
def nsmul13 (P : ZMod 13 × ZMod 13) : ℕ → ZMod 13 × ZMod 13
  | 0 => (0, 1)
  | n + 1 => add13 (nsmul13 P n) P

/-- Extended coordinates `(x : y : 1 : x y)`. -/
def toExt13 (P : ZMod 13 × ZMod 13) : E13.Extended :=
  ⟨P.1, P.2, 1, P.1 * P.2⟩

/-- The affine point `(X / Z, Y / Z)` of extended coordinates. -/
def ofExt13 (R : E13.Extended) : ZMod 13 × ZMod 13 :=
  (R.X * R.Z ^ 11, R.Y * R.Z ^ 11)

/-- The affine point `(X / Z, Y / T)` of completed coordinates. -/
def ofCompleted13 (R : E13.Completed) : ZMod 13 × ZMod 13 :=
  (R.X * R.Z ^ 11, R.Y * R.T ^ 11)

/-- There are points besides `(0, ±1)` and `(±√-1, 0)`. -/
example : 4 < pts13.length := by decide +kernel

/-- The extended addition agrees with the affine formula for `a = -1`, and stays on the curve. -/
example : ∀ P ∈ pts13, ∀ Q ∈ pts13,
    ((toExt13 P).add (toExt13 Q)).OnCurve ∧
      ofExt13 ((toExt13 P).add (toExt13 Q)) = add13 P Q := by
  decide +kernel

/-- Scalar multiplication in extended coordinates agrees with repeated affine addition for
`a = -1`. -/
example : ∀ P ∈ pts13, ∀ n ∈ List.range 6,
    (TwistedEdwardsModel.Extended.nsmul n (toExt13 P)).OnCurve ∧
      ofExt13 (TwistedEdwardsModel.Extended.nsmul n (toExt13 P)) = nsmul13 P n := by
  decide +kernel

/-- Projective doubling for `a = -1` agrees with the affine formula and stays on the curve. -/
example : ∀ P ∈ pts13,
    let R := (⟨2 * P.1, 2 * P.2, 2⟩ : E13.Projective).double
    R.OnCurve ∧ ofCompleted13 R = add13 P P := by
  decide +kernel

end CoordTests
