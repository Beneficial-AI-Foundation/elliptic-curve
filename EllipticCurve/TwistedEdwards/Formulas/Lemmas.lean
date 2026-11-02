/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.TwistedEdwards.Formulas.Defs
import all EllipticCurve.TwistedEdwards.Formulas.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Twisted Edwards models: formulas in coordinates, correctness

The characterising statements about the formulas of `EllipticCurve.TwistedEdwards.Formulas.Defs`,
on a complete model: each operation sends points on the curve to points on the curve
(`Projective.double_onCurve`, `Extended.add_onCurve`, `Extended.double_onCurve`,
`Extended.nsmul_onCurve`) and, away from 6, represents the group operation on the represented
points (`Projective.toPoint_double`, `Extended.toPoint_add`, `Extended.toPoint_double`,
`Extended.toPoint_nsmul`); the zero test `Extended.isZero_iff`.

## Recognising a sum

The sum of `p = (x₁, y₁)` and `q = (x₂, y₂)` is `(N_x / D₁, N_y / D₂)` with
`N_x = x₁ y₂ + x₂ y₁`, `N_y = y₁ y₂ - a x₁ x₂`, `D₁ = 1 + d x₁ x₂ y₁ y₂ = addDen₁ p q` and
`D₂ = 1 - d x₁ x₂ y₁ y₂ = addDen₂ p q`. A point of a coordinate system whose coordinates are these
numerators and denominators in the shape of the system, scaled by any `c ≠ 0`, is on the curve
(`*.onCurve_of_eq_add`) and, away from 6, represents `p + q` (`*.onCurve_and_toPoint_eq_add`):

* completed: `c • (N_x, N_y, D₁, D₂)`;
* projective: `c • (N_x D₂, N_y D₁, D₁ D₂)`;
* extended: `c • (N_x D₂, N_y D₁, D₁ D₂, N_x N_y)`.

These are stated for any point of these coordinate systems, so that other formulas can use them.
Every formula here is proved by them: the coordinates of the inputs are eliminated through
`X_eq_toPoint_x_mul_Z`, … of `EllipticCurve.TwistedEdwards.Coords.Lemmas`, after which each
identity is polynomial (`ring`), except for `Projective.double`, which uses the curve equation
once.

Ported from curve25519-dalek's Lean verification
(`Curve25519/Models/TwistedEdwards/Formulas/Lemmas.lean`, commit `d2e92e7`), without the mixed
additions with Niels points, with `Projective.double` for every `a`, with the sum criteria for any
nonzero scale (and a projective one), and with the `OnCurve` statements for any characteristic. -/

public section

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] {E : TwistedEdwardsModel F} [E.IsComplete]

/-! ### Recognising a sum -/

namespace Completed

private theorem coords_of_eq_add {R : E.Completed} {c : F} (hc : c ≠ 0) (p q : E.Point)
    (hX : R.X = c * (p.x * q.y + q.x * p.y)) (hY : R.Y = c * (p.y * q.y - E.a * p.x * q.x))
    (hZ : R.Z = c * addDen₁ p q) (hT : R.T = c * addDen₂ p q) :
    R.OnCurve ∧ R.toPoint.x = addX p q ∧ R.toPoint.y = addY p q := by
  have hx : R.X / R.Z = addX p q := by
    rw [hX, hZ, mul_div_mul_left _ _ hc]
    rfl
  have hy : R.Y / R.T = addY p q := by
    rw [hY, hT, mul_div_mul_left _ _ hc]
    rfl
  have hR : R.OnCurve :=
    ⟨by rw [hZ]; exact mul_ne_zero hc (addDen₁_ne_zero p q),
      by rw [hT]; exact mul_ne_zero hc (addDen₂_ne_zero p q),
      by rw [hx, hy]; exact equation_addX_addY p q⟩
  exact ⟨hR, by rw [toPoint_x hR, hx], by rw [toPoint_y hR, hy]⟩

/-- A completed point `c • (x₁ y₂ + x₂ y₁, y₁ y₂ - a x₁ x₂, addDen₁ p q, addDen₂ p q)` with
`c ≠ 0` is on the curve. -/
theorem onCurve_of_eq_add {R : E.Completed} {c : F} (hc : c ≠ 0) (p q : E.Point)
    (hX : R.X = c * (p.x * q.y + q.x * p.y)) (hY : R.Y = c * (p.y * q.y - E.a * p.x * q.x))
    (hZ : R.Z = c * addDen₁ p q) (hT : R.T = c * addDen₂ p q) : R.OnCurve :=
  (coords_of_eq_add hc p q hX hY hZ hT).1

/-- A completed point `c • (x₁ y₂ + x₂ y₁, y₁ y₂ - a x₁ x₂, addDen₁ p q, addDen₂ p q)` with
`c ≠ 0` is on the curve and represents `p + q`. -/
theorem onCurve_and_toPoint_eq_add [NeZero (6 : F)] {R : E.Completed} {c : F} (hc : c ≠ 0)
    (p q : E.Point) (hX : R.X = c * (p.x * q.y + q.x * p.y))
    (hY : R.Y = c * (p.y * q.y - E.a * p.x * q.x)) (hZ : R.Z = c * addDen₁ p q)
    (hT : R.T = c * addDen₂ p q) : R.OnCurve ∧ R.toPoint = p + q := by
  obtain ⟨hR, hx, hy⟩ := coords_of_eq_add hc p q hX hY hZ hT
  exact ⟨hR, Point.ext (by rw [hx, add_x]) (by rw [hy, add_y])⟩

end Completed

namespace Projective

private theorem coords_of_eq_add {R : E.Projective} {c : F} (hc : c ≠ 0) (p q : E.Point)
    (hX : R.X = c * ((p.x * q.y + q.x * p.y) * addDen₂ p q))
    (hY : R.Y = c * ((p.y * q.y - E.a * p.x * q.x) * addDen₁ p q))
    (hZ : R.Z = c * (addDen₁ p q * addDen₂ p q)) :
    R.OnCurve ∧ R.toPoint.x = addX p q ∧ R.toPoint.y = addY p q := by
  have hD₁ := addDen₁_ne_zero p q
  have hD₂ := addDen₂_ne_zero p q
  have hZ0 : c * (addDen₁ p q * addDen₂ p q) ≠ 0 := mul_ne_zero hc (mul_ne_zero hD₁ hD₂)
  have hx : R.X / R.Z = addX p q := by
    rw [hX, hZ, addX, div_eq_div_iff hZ0 hD₁]
    ring
  have hy : R.Y / R.Z = addY p q := by
    rw [hY, hZ, addY, div_eq_div_iff hZ0 hD₂]
    ring
  have hR : R.OnCurve :=
    ⟨by rw [hZ]; exact hZ0, by rw [hx, hy]; exact equation_addX_addY p q⟩
  exact ⟨hR, by rw [toPoint_x hR, hx], by rw [toPoint_y hR, hy]⟩

/-- A projective point `c • ((x₁ y₂ + x₂ y₁) D₂, (y₁ y₂ - a x₁ x₂) D₁, D₁ D₂)`, with
`D₁ = addDen₁ p q`, `D₂ = addDen₂ p q` and `c ≠ 0`, is on the curve. -/
theorem onCurve_of_eq_add {R : E.Projective} {c : F} (hc : c ≠ 0) (p q : E.Point)
    (hX : R.X = c * ((p.x * q.y + q.x * p.y) * addDen₂ p q))
    (hY : R.Y = c * ((p.y * q.y - E.a * p.x * q.x) * addDen₁ p q))
    (hZ : R.Z = c * (addDen₁ p q * addDen₂ p q)) : R.OnCurve :=
  (coords_of_eq_add hc p q hX hY hZ).1

/-- A projective point `c • ((x₁ y₂ + x₂ y₁) D₂, (y₁ y₂ - a x₁ x₂) D₁, D₁ D₂)`, with
`D₁ = addDen₁ p q`, `D₂ = addDen₂ p q` and `c ≠ 0`, is on the curve and represents `p + q`. -/
theorem onCurve_and_toPoint_eq_add [NeZero (6 : F)] {R : E.Projective} {c : F} (hc : c ≠ 0)
    (p q : E.Point) (hX : R.X = c * ((p.x * q.y + q.x * p.y) * addDen₂ p q))
    (hY : R.Y = c * ((p.y * q.y - E.a * p.x * q.x) * addDen₁ p q))
    (hZ : R.Z = c * (addDen₁ p q * addDen₂ p q)) : R.OnCurve ∧ R.toPoint = p + q := by
  obtain ⟨hR, hx, hy⟩ := coords_of_eq_add hc p q hX hY hZ
  exact ⟨hR, Point.ext (by rw [hx, add_x]) (by rw [hy, add_y])⟩

end Projective

namespace Extended

private theorem coords_of_eq_add {R : E.Extended} {c : F} (hc : c ≠ 0) (p q : E.Point)
    (hX : R.X = c * ((p.x * q.y + q.x * p.y) * addDen₂ p q))
    (hY : R.Y = c * ((p.y * q.y - E.a * p.x * q.x) * addDen₁ p q))
    (hZ : R.Z = c * (addDen₁ p q * addDen₂ p q))
    (hT : R.T = c * ((p.x * q.y + q.x * p.y) * (p.y * q.y - E.a * p.x * q.x))) :
    R.OnCurve ∧ R.toPoint.x = addX p q ∧ R.toPoint.y = addY p q := by
  have hD₁ := addDen₁_ne_zero p q
  have hD₂ := addDen₂_ne_zero p q
  have hZ0 : c * (addDen₁ p q * addDen₂ p q) ≠ 0 := mul_ne_zero hc (mul_ne_zero hD₁ hD₂)
  have hx : R.X / R.Z = addX p q := by
    rw [hX, hZ, addX, div_eq_div_iff hZ0 hD₁]
    ring
  have hy : R.Y / R.Z = addY p q := by
    rw [hY, hZ, addY, div_eq_div_iff hZ0 hD₂]
    ring
  have hR : R.OnCurve :=
    ⟨by rw [hZ]; exact hZ0, by rw [hX, hY, hZ, hT]; ring,
      by rw [hx, hy]; exact equation_addX_addY p q⟩
  exact ⟨hR, by rw [toPoint_x hR, hx], by rw [toPoint_y hR, hy]⟩

/-- An extended point `c • ((x₁ y₂ + x₂ y₁) D₂, (y₁ y₂ - a x₁ x₂) D₁, D₁ D₂,
(x₁ y₂ + x₂ y₁) (y₁ y₂ - a x₁ x₂))`, with `D₁ = addDen₁ p q`, `D₂ = addDen₂ p q` and `c ≠ 0`, is
on the curve. -/
theorem onCurve_of_eq_add {R : E.Extended} {c : F} (hc : c ≠ 0) (p q : E.Point)
    (hX : R.X = c * ((p.x * q.y + q.x * p.y) * addDen₂ p q))
    (hY : R.Y = c * ((p.y * q.y - E.a * p.x * q.x) * addDen₁ p q))
    (hZ : R.Z = c * (addDen₁ p q * addDen₂ p q))
    (hT : R.T = c * ((p.x * q.y + q.x * p.y) * (p.y * q.y - E.a * p.x * q.x))) : R.OnCurve :=
  (coords_of_eq_add hc p q hX hY hZ hT).1

/-- An extended point `c • ((x₁ y₂ + x₂ y₁) D₂, (y₁ y₂ - a x₁ x₂) D₁, D₁ D₂,
(x₁ y₂ + x₂ y₁) (y₁ y₂ - a x₁ x₂))`, with `D₁ = addDen₁ p q`, `D₂ = addDen₂ p q` and `c ≠ 0`, is
on the curve and represents `p + q`. -/
theorem onCurve_and_toPoint_eq_add [NeZero (6 : F)] {R : E.Extended} {c : F} (hc : c ≠ 0)
    (p q : E.Point) (hX : R.X = c * ((p.x * q.y + q.x * p.y) * addDen₂ p q))
    (hY : R.Y = c * ((p.y * q.y - E.a * p.x * q.x) * addDen₁ p q))
    (hZ : R.Z = c * (addDen₁ p q * addDen₂ p q))
    (hT : R.T = c * ((p.x * q.y + q.x * p.y) * (p.y * q.y - E.a * p.x * q.x))) :
    R.OnCurve ∧ R.toPoint = p + q := by
  obtain ⟨hR, hx, hy⟩ := coords_of_eq_add hc p q hX hY hZ hT
  exact ⟨hR, Point.ext (by rw [hx, add_x]) (by rw [hy, add_y])⟩

end Extended

/-! ### Doubling in projective coordinates -/

namespace Projective

variable {P : E.Projective}

omit [E.IsComplete] in
/-- The coordinates of `P.double`, as a completed point recognised by
`Completed.onCurve_of_eq_add` at `p = q = P.toPoint`, with scale `Z²`. -/
private theorem double_eq (h : P.OnCurve) :
    P.double.X = P.Z ^ 2 * (P.toPoint.x * P.toPoint.y + P.toPoint.x * P.toPoint.y) ∧
    P.double.Y = P.Z ^ 2 * (P.toPoint.y * P.toPoint.y - E.a * P.toPoint.x * P.toPoint.x) ∧
    P.double.Z = P.Z ^ 2 * addDen₁ P.toPoint P.toPoint ∧
    P.double.T = P.Z ^ 2 * addDen₂ P.toPoint P.toPoint := by
  have he := P.toPoint.equation
  unfold Equation at he
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [double, X_eq_toPoint_x_mul_Z h, Y_eq_toPoint_y_mul_Z h]
    ring
  · simp only [double, X_eq_toPoint_x_mul_Z h, Y_eq_toPoint_y_mul_Z h]
    ring
  · simp only [double, X_eq_toPoint_x_mul_Z h, Y_eq_toPoint_y_mul_Z h, addDen₁]
    linear_combination P.Z ^ 2 * he
  · simp only [double, X_eq_toPoint_x_mul_Z h, Y_eq_toPoint_y_mul_Z h, addDen₂]
    linear_combination (-P.Z ^ 2) * he

/-- "dbl-2008-bbjlp" sends points on the curve to points on the curve. -/
theorem double_onCurve (h : P.OnCurve) : P.double.OnCurve :=
  let ⟨hX, hY, hZ, hT⟩ := double_eq h
  Completed.onCurve_of_eq_add (pow_ne_zero 2 h.1) _ _ hX hY hZ hT

/-- "dbl-2008-bbjlp" doubles the represented point. -/
theorem toPoint_double [NeZero (6 : F)] (h : P.OnCurve) : P.double.toPoint = 2 • P.toPoint := by
  obtain ⟨hX, hY, hZ, hT⟩ := double_eq h
  rw [two_nsmul]
  exact (Completed.onCurve_and_toPoint_eq_add (pow_ne_zero 2 h.1) _ _ hX hY hZ hT).2

end Projective

namespace Extended

/-! ### The complete extended addition, doubling and scalar multiplication (any `a`) -/

variable {P Q : E.Extended}

omit [E.IsComplete] in
/-- The coordinates of `P.add Q`, as an extended point recognised by `onCurve_of_eq_add` at
`P.toPoint`, `Q.toPoint`, with scale `(Z₁ Z₂)²`. -/
private theorem add_eq (hP : P.OnCurve) (hQ : Q.OnCurve) :
    let p := P.toPoint
    let q := Q.toPoint
    (P.add Q).X = (P.Z * Q.Z) ^ 2 * ((p.x * q.y + q.x * p.y) * addDen₂ p q) ∧
    (P.add Q).Y = (P.Z * Q.Z) ^ 2 * ((p.y * q.y - E.a * p.x * q.x) * addDen₁ p q) ∧
    (P.add Q).Z = (P.Z * Q.Z) ^ 2 * (addDen₁ p q * addDen₂ p q) ∧
    (P.add Q).T = (P.Z * Q.Z) ^ 2 * ((p.x * q.y + q.x * p.y) * (p.y * q.y - E.a * p.x * q.x)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [add, X_eq_toPoint_x_mul_Z hP, Y_eq_toPoint_y_mul_Z hP,
      T_eq_toPoint_x_mul_y_mul_Z hP, X_eq_toPoint_x_mul_Z hQ, Y_eq_toPoint_y_mul_Z hQ,
      T_eq_toPoint_x_mul_y_mul_Z hQ, addDen₁, addDen₂]
    ring

/-- "add-2008-hwcd" sends points on the curve to points on the curve. -/
theorem add_onCurve (hP : P.OnCurve) (hQ : Q.OnCurve) : (P.add Q).OnCurve :=
  let ⟨hX, hY, hZ, hT⟩ := add_eq hP hQ
  onCurve_of_eq_add (pow_ne_zero 2 (mul_ne_zero hP.1 hQ.1)) _ _ hX hY hZ hT

/-- "add-2008-hwcd" adds the represented points. -/
theorem toPoint_add [NeZero (6 : F)] (hP : P.OnCurve) (hQ : Q.OnCurve) :
    (P.add Q).toPoint = P.toPoint + Q.toPoint :=
  let ⟨hX, hY, hZ, hT⟩ := add_eq hP hQ
  (onCurve_and_toPoint_eq_add (pow_ne_zero 2 (mul_ne_zero hP.1 hQ.1)) _ _ hX hY hZ hT).2

/-- Doubling in extended coordinates sends points on the curve to points on the curve. -/
theorem double_onCurve (hP : P.OnCurve) : P.double.OnCurve :=
  add_onCurve hP hP

/-- Doubling in extended coordinates doubles the represented point. -/
theorem toPoint_double [NeZero (6 : F)] (hP : P.OnCurve) : P.double.toPoint = 2 • P.toPoint := by
  rw [two_nsmul]
  exact toPoint_add hP hP

/-- Double-and-add stays on the curve. -/
theorem nsmulAux_onCurve (hP : P.OnCurve) (k n : ℕ) : (nsmulAux P k n).OnCurve := by
  induction k generalizing n with
  | zero => exact onCurve_identity
  | succ k ih =>
    simp only [nsmulAux]
    split_ifs
    · exact onCurve_identity
    · exact double_onCurve (ih _)
    · exact add_onCurve (double_onCurve (ih _)) hP

/-- Double-and-add with enough fuel computes `n • P`. -/
theorem toPoint_nsmulAux [NeZero (6 : F)] (hP : P.OnCurve) (k n : ℕ) (hn : n < 2 ^ k) :
    (nsmulAux P k n).toPoint = n • P.toPoint := by
  induction k generalizing n with
  | zero =>
    obtain rfl : n = 0 := by simpa using hn
    rw [zero_nsmul]
    exact toPoint_identity
  | succ k ih =>
    have hQ := nsmulAux_onCurve hP k (n / 2)
    have hQe :=
      ih (n / 2) ((Nat.div_lt_iff_lt_mul two_pos).mpr (by rw [← pow_succ]; exact hn))
    simp only [nsmulAux]
    split_ifs with h0 h2
    · rw [h0, zero_nsmul]
      exact toPoint_identity
    · rw [toPoint_double hQ, hQe, smul_smul]
      congr 1
      omega
    · rw [toPoint_add (double_onCurve hQ) hP, toPoint_double hQ, hQe, smul_smul, ← succ_nsmul]
      congr 1
      omega

/-- `nsmul` sends points on the curve to points on the curve. -/
theorem nsmul_onCurve (hP : P.OnCurve) (n : ℕ) : (nsmul n P).OnCurve :=
  nsmulAux_onCurve hP n n

/-- `nsmul n` computes `n • P` on the represented points. -/
theorem toPoint_nsmul [NeZero (6 : F)] (hP : P.OnCurve) (n : ℕ) :
    (nsmul n P).toPoint = n • P.toPoint :=
  toPoint_nsmulAux hP n n Nat.lt_two_pow_self

/-! ### The zero test -/

/-- `(X : Y : Z : T)` on the curve represents `0` exactly when `X = 0` and `Y = Z`. -/
theorem isZero_iff (hP : P.OnCurve) : P.IsZero ↔ P.toPoint = 0 := by
  rw [Point.ext_iff, toPoint_x hP, toPoint_y hP, zero_x, zero_y, div_eq_zero_iff,
    or_iff_left hP.1, div_eq_one_iff_eq hP.1]
  rfl

end Extended

end TwistedEdwardsModel
