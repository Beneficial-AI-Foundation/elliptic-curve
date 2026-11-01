/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.TwistedEdwards.Group
public import Mathlib.Algebra.Group.Subgroup.Even
import EllipticCurve.Montgomery.Lemmas
import EllipticCurve.TwistedEdwards.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Even points of a complete twisted Edwards model

Tools for talking about the even points `2 E` (Mathlib's `Even P`, `AddSubgroup.even E.Point`)
of a complete twisted Edwards model:

* the 4-torsion in coordinates: `4 • P = 0 ↔ x = 0 ∨ y = 0` (`four_nsmul_eq_zero_iff`);
* the generic half of the 2-descent: the subgroup `E.descent` of the points with
  `(a - d)(1 - y²)` a square contains the even points (`even_le_descent`, `isSquare_of_even`),
  through the descent map `Q ↦ B u(Q)` of the Montgomery model
  (`isSquare_toMontgomery_B_mul_u_iff`, `MontgomeryModel.isSquare_B_mul_u_add`).

Over a finite field the descent map has index at most `2`, so `E.descent` is the even subgroup as
soon as it is not everything; that is a statement about a particular curve. -/

public section

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] {E : TwistedEdwardsModel F} [E.IsComplete]

/-! ### The 4-torsion in coordinates -/

/-- The 4-torsion of a complete model is `{x = 0} ∪ {y = 0}`: `4 • P = 0` exactly when `P.x = 0`
or `P.y = 0` (the points `(0, ±1)` of order dividing `2` and `(±√(1/a), 0)` of order `4`). -/
theorem four_nsmul_eq_zero_iff [NeZero (6 : F)] (P : E.Point) : 4 • P = 0 ↔ P.x = 0 ∨ P.y = 0 := by
  have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
  have hden := addDen₁_ne_zero P P
  rw [show (4 : ℕ) = 2 * 2 from rfl, ← smul_smul, two_nsmul_eq_zero_iff, two_nsmul_x]
  unfold addX
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · have h' : (2 * P.x) * P.y = 0 := by linear_combination h
      rcases mul_eq_zero.mp h' with h' | h'
      · exact Or.inl ((mul_eq_zero.mp h').resolve_left h2)
      · exact Or.inr h'
    · exact absurd h hden
  · rintro (h | h)
    · left
      rw [h]
      ring
    · left
      rw [h]
      ring

/-! ### The 2-descent: the generic half

For a point `P` of `E` with Montgomery image `Q`,
`B u(Q) = (2 / ((a - d)(1 - y)))² · (a - d)(1 - y²)` (and both sides are `0` at `P = (0, 1)`),
so the kernel of the descent map `Q ↦ B u(Q)` modulo squares of `E.toMontgomery`
(`MontgomeryModel.isSquare_B_mul_u_add`) pulls back to the subgroup `E.descent` of points with
`(a - d)(1 - y²)` a square. It contains every double
(`MontgomeryModel.isSquare_B_mul_u_two_nsmul`), hence the even points. -/

private theorem isSquare_sq_mul_iff {c x : F} (hc : c ≠ 0) :
    IsSquare (c ^ 2 * x) ↔ IsSquare x := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r / c, ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hc hc), ← hr]
    ring
  · rintro ⟨r, hr⟩
    exact ⟨c * r, by rw [hr]; ring⟩

/-- The descent class of a point, on the Montgomery side and on the Edwards side:
`B u(Q)` is a square iff `(a - d)(1 - y²)` is. -/
theorem isSquare_toMontgomery_B_mul_u_iff (P : E.Point) :
    IsSquare (E.toMontgomery.B * (E.toMontgomeryEquiv P).u) ↔
      IsSquare ((E.a - E.d) * (1 - P.y ^ 2)) := by
  have had : E.a - E.d ≠ 0 := sub_ne_zero.mpr E.a_ne_d
  rw [u_toMontgomeryEquiv, toMontgomery_B]
  by_cases hy : P.y = 1
  · rw [hy]
    norm_num
  · have h1y : 1 - P.y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
    have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
    have key : 4 / (E.a - E.d) * ((1 + P.y) / (1 - P.y)) =
        (2 / ((E.a - E.d) * (1 - P.y))) ^ 2 * ((E.a - E.d) * (1 - P.y ^ 2)) := by
      field_simp
      ring
    rw [key, isSquare_sq_mul_iff (div_ne_zero h2 (mul_ne_zero had h1y))]

variable (E)

/-- The 2-descent subgroup: the points `P` with `(a - d)(1 - y²)` a square, the pullback of the
kernel of the descent map `Q ↦ B u(Q)` of `E.toMontgomery`. It contains the even points
(`even_le_descent`). Hidden; see `mem_descent`. -/
def descent : AddSubgroup E.Point where
  carrier := {P | IsSquare ((E.a - E.d) * (1 - P.y ^ 2))}
  zero_mem' := by
    change IsSquare ((E.a - E.d) * (1 - (0 : E.Point).y ^ 2))
    rw [zero_y]
    norm_num
  add_mem' {P Q} hP hQ := by
    change IsSquare ((E.a - E.d) * (1 - (P + Q).y ^ 2))
    rw [← isSquare_toMontgomery_B_mul_u_iff, map_add]
    exact MontgomeryModel.isSquare_B_mul_u_add
      ((isSquare_toMontgomery_B_mul_u_iff P).mpr (Set.mem_ofPred_eq.mp hP))
      ((isSquare_toMontgomery_B_mul_u_iff Q).mpr (Set.mem_ofPred_eq.mp hQ))
  neg_mem' {P} hP := by
    change IsSquare ((E.a - E.d) * (1 - (-P).y ^ 2))
    rw [neg_y]
    exact Set.mem_ofPred_eq.mp hP

variable {E}

/-- Membership in the 2-descent subgroup. -/
theorem mem_descent {P : E.Point} : P ∈ E.descent ↔ IsSquare ((E.a - E.d) * (1 - P.y ^ 2)) :=
  Iff.rfl

/-- Doubles lie in the 2-descent subgroup. -/
theorem two_nsmul_mem_descent (P : E.Point) : 2 • P ∈ E.descent := by
  rw [mem_descent, ← isSquare_toMontgomery_B_mul_u_iff, map_nsmul]
  exact MontgomeryModel.isSquare_B_mul_u_two_nsmul _

/-- The even points lie in the 2-descent subgroup. -/
theorem even_le_descent : AddSubgroup.even E.Point ≤ E.descent := by
  intro P hP
  obtain ⟨Q, rfl⟩ := (AddSubgroup.mem_even.mp hP).exists_two_nsmul
  exact two_nsmul_mem_descent Q

/-- An even point has `(a - d)(1 - y²)` a square: the easy direction of the 2-descent. -/
theorem isSquare_of_even {P : E.Point} (h : Even P) : IsSquare ((E.a - E.d) * (1 - P.y ^ 2)) :=
  mem_descent.mp (even_le_descent (AddSubgroup.mem_even.mpr h))

end TwistedEdwardsModel
