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
(`double_onCurve`, `add_onCurve`, `nsmul_onCurve`) and represents the group operation on the
represented points (`toPoint_double`, `toPoint_add`, `toPoint_nsmul`); the zero test
`isZero_iff`.

## Route

Every formula is shown to produce, in terms of the represented points `p`, `q`, a nonzero
multiple `c • (x₁ y₂ + x₂ y₁, y₁ y₂ - a x₁ x₂, 1 + d x₁ x₂ y₁ y₂, 1 - d x₁ x₂ y₁ y₂)` (in
the shape of its coordinate system), whose point is `p + q` by the group law in coordinates
(`add_x`, `add_y` of `EllipticCurve.TwistedEdwards.Lemmas`); this is
`Completed.onCurve_and_toPoint_eq_add` and `Extended.onCurve_and_toPoint_eq_add`, stated for any
point of these coordinate systems so that other formulas can use them. The coordinates of the
inputs are eliminated through `X_eq_toPoint_x_mul_Z`, … of
`EllipticCurve.TwistedEdwards.Coords.Lemmas`, after which each identity is polynomial (`ring`),
except for `Projective.double`, which uses the curve equation of `p` once.

Ported from curve25519-dalek's Lean verification
(`Curve25519/Models/TwistedEdwards/Formulas/Lemmas.lean`, commit `d2e92e7`), without the mixed
additions with Niels points, and with `Projective.double` for every `a`. -/

public section

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] [NeZero (6 : F)] {E : TwistedEdwardsModel F} [E.IsComplete]

/-! ### Recognising a sum -/

/-- A completed point `c • (x₁ y₂ + x₂ y₁, y₁ y₂ - a x₁ x₂, addDen₁ p q, addDen₂ p q)`
with `c ≠ 0` is on the curve and represents `p + q`. -/
theorem Completed.onCurve_and_toPoint_eq_add {R : E.Completed} {c : F} (hc : c ≠ 0)
    (p q : E.Point) (hX : R.X = c * (p.x * q.y + q.x * p.y))
    (hY : R.Y = c * (p.y * q.y - E.a * p.x * q.x)) (hZ : R.Z = c * addDen₁ p q)
    (hT : R.T = c * addDen₂ p q) : R.OnCurve ∧ R.toPoint = p + q := by
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
  refine ⟨hR, Point.ext ?_ ?_⟩
  · rw [Completed.toPoint_x hR, add_x, hx]
  · rw [Completed.toPoint_y hR, add_y, hy]

/-- An extended point `(e f : g h : f g : e h)` with `e = c (x₁ y₂ + x₂ y₁)`,
`h = c (y₁ y₂ - a x₁ x₂)`, `g = c addDen₁ p q`, `f = c addDen₂ p q` and `c ≠ 0` is on the
curve and represents `p + q`. -/
theorem Extended.onCurve_and_toPoint_eq_add {R : E.Extended} {c : F} (hc : c ≠ 0)
    (p q : E.Point)
    (hX : R.X = c * (p.x * q.y + q.x * p.y) * (c * addDen₂ p q))
    (hY : R.Y = c * addDen₁ p q * (c * (p.y * q.y - E.a * p.x * q.x)))
    (hZ : R.Z = c * addDen₂ p q * (c * addDen₁ p q))
    (hT : R.T = c * (p.x * q.y + q.x * p.y) * (c * (p.y * q.y - E.a * p.x * q.x))) :
    R.OnCurve ∧ R.toPoint = p + q := by
  have hD₁ := addDen₁_ne_zero p q
  have hD₂ := addDen₂_ne_zero p q
  have hZ0' : c * addDen₂ p q * (c * addDen₁ p q) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hc hD₂) (mul_ne_zero hc hD₁)
  have hZ0 : R.Z ≠ 0 := by
    rw [hZ]
    exact hZ0'
  have hx : R.X / R.Z = addX p q := by
    rw [hX, hZ, addX, div_eq_div_iff hZ0' hD₁]
    ring
  have hy : R.Y / R.Z = addY p q := by
    rw [hY, hZ, addY, div_eq_div_iff hZ0' hD₂]
    ring
  have hR : R.OnCurve :=
    ⟨hZ0, by rw [hX, hY, hZ, hT]; ring, by rw [hx, hy]; exact equation_addX_addY p q⟩
  refine ⟨hR, Point.ext ?_ ?_⟩
  · rw [Extended.toPoint_x hR, add_x, hx]
  · rw [Extended.toPoint_y hR, add_y, hy]

/-! ### Doubling in projective coordinates -/

namespace Projective

variable {P : E.Projective}

private theorem double_spec (h : P.OnCurve) :
    P.double.OnCurve ∧ P.double.toPoint = 2 • P.toPoint := by
  rw [two_nsmul]
  have he := P.toPoint.equation
  unfold Equation at he
  refine Completed.onCurve_and_toPoint_eq_add (pow_ne_zero 2 h.1) P.toPoint P.toPoint ?_ ?_ ?_ ?_
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
  (double_spec h).1

/-- "dbl-2008-bbjlp" doubles the represented point. -/
theorem toPoint_double (h : P.OnCurve) : P.double.toPoint = 2 • P.toPoint :=
  (double_spec h).2

end Projective

namespace Extended

/-! ### The complete extended addition, doubling and scalar multiplication (any `a`) -/

variable {P Q : E.Extended}

private theorem add_spec (hP : P.OnCurve) (hQ : Q.OnCurve) :
    (P.add Q).OnCurve ∧ (P.add Q).toPoint = P.toPoint + Q.toPoint := by
  refine Extended.onCurve_and_toPoint_eq_add (mul_ne_zero hP.1 hQ.1) P.toPoint Q.toPoint
    ?_ ?_ ?_ ?_ <;>
  · simp only [add, X_eq_toPoint_x_mul_Z hP, Y_eq_toPoint_y_mul_Z hP,
      T_eq_toPoint_x_mul_y_mul_Z hP, X_eq_toPoint_x_mul_Z hQ, Y_eq_toPoint_y_mul_Z hQ,
      T_eq_toPoint_x_mul_y_mul_Z hQ, addDen₁, addDen₂]
    ring

/-- "add-2008-hwcd" sends points on the curve to points on the curve. -/
theorem add_onCurve (hP : P.OnCurve) (hQ : Q.OnCurve) : (P.add Q).OnCurve :=
  (add_spec hP hQ).1

/-- "add-2008-hwcd" adds the represented points. -/
theorem toPoint_add (hP : P.OnCurve) (hQ : Q.OnCurve) :
    (P.add Q).toPoint = P.toPoint + Q.toPoint :=
  (add_spec hP hQ).2

/-- Doubling in extended coordinates sends points on the curve to points on the curve. -/
theorem double_onCurve (hP : P.OnCurve) : P.double.OnCurve :=
  add_onCurve hP hP

/-- Doubling in extended coordinates doubles the represented point. -/
theorem toPoint_double (hP : P.OnCurve) : P.double.toPoint = 2 • P.toPoint := by
  rw [two_nsmul]
  exact toPoint_add hP hP

/-- Double-and-add with enough fuel stays on the curve and computes `n • P`. -/
theorem nsmulAux_spec (hP : P.OnCurve) (k n : ℕ) (hn : n < 2 ^ k) :
    (nsmulAux P k n).OnCurve ∧ (nsmulAux P k n).toPoint = n • P.toPoint := by
  induction k generalizing n with
  | zero =>
    obtain rfl : n = 0 := by simpa using hn
    exact ⟨onCurve_identity, by rw [zero_nsmul]; exact toPoint_identity⟩
  | succ k ih =>
    obtain ⟨hQ, hQe⟩ :=
      ih (n / 2) ((Nat.div_lt_iff_lt_mul two_pos).mpr (by rw [← pow_succ]; exact hn))
    simp only [nsmulAux]
    split_ifs with h0 h2
    · exact ⟨onCurve_identity, by rw [h0, zero_nsmul]; exact toPoint_identity⟩
    · refine ⟨double_onCurve hQ, ?_⟩
      rw [toPoint_double hQ, hQe, smul_smul]
      congr 1
      omega
    · refine ⟨add_onCurve (double_onCurve hQ) hP, ?_⟩
      rw [toPoint_add (double_onCurve hQ) hP, toPoint_double hQ, hQe, smul_smul, ← succ_nsmul]
      congr 1
      omega

/-- `nsmul` sends points on the curve to points on the curve. -/
theorem nsmul_onCurve (hP : P.OnCurve) (n : ℕ) : (nsmul n P).OnCurve :=
  (nsmulAux_spec hP n n Nat.lt_two_pow_self).1

/-- `nsmul n` computes `n • P` on the represented points. -/
theorem toPoint_nsmul (hP : P.OnCurve) (n : ℕ) : (nsmul n P).toPoint = n • P.toPoint :=
  (nsmulAux_spec hP n n Nat.lt_two_pow_self).2

/-! ### The zero test -/

omit [NeZero (6 : F)] in
/-- `(X : Y : Z : T)` on the curve represents `0` exactly when `X = 0` and `Y = Z`. -/
theorem isZero_iff (hP : P.OnCurve) : P.IsZero ↔ P.toPoint = 0 := by
  rw [Point.ext_iff, toPoint_x hP, toPoint_y hP, zero_x, zero_y, div_eq_zero_iff,
    or_iff_left hP.1, div_eq_one_iff_eq hP.1]
  rfl

end Extended

end TwistedEdwardsModel
