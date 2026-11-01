/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.TwistedEdwards.Group
public import EllipticCurve.TwistedEdwards.Formula
import all EllipticCurve.TwistedEdwards.Group
import all EllipticCurve.Montgomery.Defs
import EllipticCurve.Curve.Lemmas
import EllipticCurve.Montgomery.Lemmas
import EllipticCurve.PlaneModel.EdwardsGroupLaw
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Twisted Edwards models: characterising lemmas

The characterising statements about `TwistedEdwardsModel`: the group law on
`E.Point` in coordinates (`zero_x`, `zero_y`, `zero_eq_mk`, `neg_x`, `neg_y`, `add_x`, `add_y`),
the curve (`toCurve_toMontgomery`, `pointEquiv_eq`) and the coordinate lemmas pinning
`toMontgomeryEquiv` in both directions (`u_toMontgomeryEquiv`, `v_toMontgomeryEquiv`,
`toMontgomeryEquiv_of_y_eq_one`, `toMontgomeryEquiv_of_x_eq_zero`, `toMontgomeryEquiv_symm_x`,
`toMontgomeryEquiv_symm_y`). These lemmas are the whole interface to the hidden constructions of
`EllipticCurve.TwistedEdwards.Group`: importers never see the bodies, and a different construction
of the group would only change the proofs here. The group law in coordinates comes from
`PlaneModel.edwards_coords_add` (rigidity, away from 6); completeness and closure of the formula
are in `EllipticCurve.TwistedEdwards.Formula`. -/

public section

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] {E : TwistedEdwardsModel F}

/-! ### The addition formula on a complete model -/

section IsComplete

variable [E.IsComplete]

/-! ### The construction, in coordinates (internal) -/

private theorem coords_toRoot (P : E.Point) : E.model.coords (E.toRoot P) = some (P.x, P.y) :=
  (E.exists_root P).choose_spec

private theorem xy_eq {P : E.Point} {c : F × F} (h : E.model.coords (E.toRoot P) = some c) :
    (P.x, P.y) = c :=
  Option.some_inj.mp ((coords_toRoot P).symm.trans h)

open Classical in
private theorem toRoot_zero : E.toRoot 0 = 0 := by
  change E.toRoot (E.toRoot.symm 0) = 0
  exact Equiv.apply_symm_apply _ _

open Classical in
private theorem toRoot_neg (P : E.Point) : E.toRoot (-P) = -E.toRoot P := by
  change E.toRoot (E.toRoot.symm (-E.toRoot P)) = _
  exact Equiv.apply_symm_apply _ _

open Classical in
private theorem toRoot_eq (P : E.Point) :
    E.toRoot P = E.montgomeryToRoot (E.toMontgomeryEquiv P) := by
  change _ = E.montgomeryToRoot (E.montgomeryToRoot.symm (E.toRoot P))
  rw [Equiv.apply_symm_apply]

open Classical in
private theorem montgomeryToRoot_zero : E.montgomeryToRoot 0 = 0 := by
  simp only [montgomeryToRoot, Equiv.trans_apply, MontgomeryModel.zero_def,
    MontgomeryModel.pointEquivWeierstrass_zero]
  exact (WeierstrassCurve.Affine.Point.equivOfEq (toWeierstrass_eq E)).map_zero

open Classical in
private theorem montgomeryToRoot_some {u v : F} (hm : E.toMontgomery.Equation u v) :
    ∃ h, E.montgomeryToRoot (.some u v hm) =
      .some (E.toMontgomery.B * u) (E.toMontgomery.B ^ 2 * v) h := by
  simp only [montgomeryToRoot, Equiv.trans_apply, MontgomeryModel.pointEquivWeierstrass_some]
  exact ⟨by rw [← toWeierstrass_eq E]; exact E.toMontgomery.nonsingular_mul hm,
    WeierstrassCurve.Affine.Point.equivOfEq_some _ _⟩

private theorem xy_of_zero {P : E.Point} (hQ : E.toMontgomeryEquiv P = 0) :
    P.x = 0 ∧ P.y = 1 := by
  have h := xy_eq (P := P)
    (by rw [toRoot_eq, hQ, montgomeryToRoot_zero]; exact PlaneModel.edwards_coords_zero)
  simpa only [Prod.mk.injEq] using h

private theorem xy_of_some {P : E.Point} {u v : F} {hm : E.toMontgomery.Equation u v}
    (hQ : E.toMontgomeryEquiv P = .some u v hm) :
    (P.x, P.y) = PlaneModel.edwardsOfRoot E.a E.d (E.toMontgomery.B * u)
      (E.toMontgomery.B ^ 2 * v) := by
  obtain ⟨h, e⟩ := E.montgomeryToRoot_some hm
  exact xy_eq (by rw [toRoot_eq, hQ, e]; exact PlaneModel.edwards_coords_some E.isComplete' h)

private theorem xy_of_some_of_v_eq_zero {P : E.Point} {u v : F}
    {hm : E.toMontgomery.Equation u v} (hQ : E.toMontgomeryEquiv P = .some u v hm) (hv : v = 0) :
    P.x = 0 ∧ P.y = -1 := by
  have h := xy_of_some hQ
  rw [hv, mul_zero, PlaneModel.edwardsOfRoot_zero] at h
  simpa only [Prod.mk.injEq] using h

private theorem xy_of_some_of_v_ne_zero {P : E.Point} {u v : F}
    {hm : E.toMontgomery.Equation u v} (hQ : E.toMontgomeryEquiv P = .some u v hm) (hv : v ≠ 0) :
    P.x = u / v ∧ P.y = (u - 1) / (u + 1) := by
  have hB : E.toMontgomery.B ≠ 0 := E.toMontgomery_B_ne_zero
  have h := xy_of_some hQ
  rw [PlaneModel.edwardsOfRoot_of_ne (mul_ne_zero (pow_ne_zero 2 hB) hv),
    show 4 / (E.a - E.d) = E.toMontgomery.B from (toMontgomery_B E).symm,
    mul_div_cancel_left₀ _ hB, mul_div_cancel_left₀ _ (pow_ne_zero 2 hB)] at h
  simpa only [Prod.mk.injEq] using h

omit [E.IsComplete] in
private theorem ratio_eq {u : F} (hu1 : u + 1 ≠ 0) (h2 : (2 : F) ≠ 0) :
    (1 + (u - 1) / (u + 1)) / (1 - (u - 1) / (u + 1)) = u := by
  have e1 : 1 + (u - 1) / (u + 1) = 2 * u / (u + 1) := by
    rw [one_add_div hu1]; congr 1; ring
  have e2 : 1 - (u - 1) / (u + 1) = 2 / (u + 1) := by
    rw [one_sub_div hu1]; congr 1; ring
  rw [e1, e2, div_div_div_cancel_right₀ hu1, mul_div_cancel_left₀ u h2]

/-! ### The group law in coordinates -/

/-- The zero of the group is `(0, 1)`: `x`-coordinate. -/
@[simp]
theorem zero_x : (0 : E.Point).x = 0 :=
  congrArg Prod.fst (xy_eq (P := (0 : E.Point))
    (by rw [toRoot_zero]; exact PlaneModel.edwards_coords_zero))

/-- The zero of the group is `(0, 1)`: `y`-coordinate. -/
@[simp]
theorem zero_y : (0 : E.Point).y = 1 :=
  congrArg Prod.snd (xy_eq (P := (0 : E.Point))
    (by rw [toRoot_zero]; exact PlaneModel.edwards_coords_zero))

/-- `(0, 1)` is the zero of the group. -/
theorem zero_eq_mk : (0 : E.Point) = ⟨0, 1, E.equation_zero_one⟩ :=
  Point.ext zero_x zero_y

/-- Negation is `(x, y) ↦ (-x, y)`: `x`-coordinate. -/
@[simp]
theorem neg_x (P : E.Point) : (-P).x = -P.x :=
  congrArg Prod.fst (xy_eq (P := -P) (by
    rw [toRoot_neg]; exact PlaneModel.edwards_coords_neg E.isComplete' (coords_toRoot P)))

/-- Negation is `(x, y) ↦ (-x, y)`: `y`-coordinate. -/
@[simp]
theorem neg_y (P : E.Point) : (-P).y = P.y :=
  congrArg Prod.snd (xy_eq (P := -P) (by
    rw [toRoot_neg]; exact PlaneModel.edwards_coords_neg E.isComplete' (coords_toRoot P)))

/-- The sum of two points, as a point: the addition formula. -/
theorem add_eq_mk [NeZero (6 : F)] (P Q : E.Point) :
    P + Q = ⟨addX P Q, addY P Q, equation_addX_addY P Q⟩ := by
  have h := xy_eq (P := P + Q) (by
    rw [toRoot_add]
    exact PlaneModel.edwards_coords_add E.isComplete' (coords_toRoot P) (coords_toRoot Q))
  simp only [TwistedEdwardsFormula.addX, TwistedEdwardsFormula.addY, Prod.mk.injEq] at h
  ext
  · rw [h.1]; simp only [addX, addDen₁]
  · rw [h.2]; simp only [addY, addDen₂]

/-- **The group law in coordinates**: the `x`-coordinate of the sum is
`(x₁ y₂ + x₂ y₁) / (1 + d x₁ x₂ y₁ y₂)`. -/
@[simp]
theorem add_x [NeZero (6 : F)] (P Q : E.Point) : (P + Q).x = addX P Q := by
  rw [add_eq_mk]

/-- **The group law in coordinates**: the `y`-coordinate of the sum is
`(y₁ y₂ - a x₁ x₂) / (1 - d x₁ x₂ y₁ y₂)`. -/
@[simp]
theorem add_y [NeZero (6 : F)] (P Q : E.Point) : (P + Q).y = addY P Q := by
  rw [add_eq_mk]

/-- The `x`-coordinate of a difference. -/
theorem sub_x [NeZero (6 : F)] (P Q : E.Point) : (P - Q).x = addX P (-Q) := by
  rw [sub_eq_add_neg, add_x]

/-- The `y`-coordinate of a difference. -/
theorem sub_y [NeZero (6 : F)] (P Q : E.Point) : (P - Q).y = addY P (-Q) := by
  rw [sub_eq_add_neg, add_y]

/-- The `x`-coordinate of a double. -/
theorem two_nsmul_x [NeZero (6 : F)] (P : E.Point) : (2 • P).x = addX P P := by
  rw [two_nsmul, add_x]

/-- The `y`-coordinate of a double. -/
theorem two_nsmul_y [NeZero (6 : F)] (P : E.Point) : (2 • P).y = addY P P := by
  rw [two_nsmul, add_y]

/-- The `2`-torsion of a complete model is `{(0, 1), (0, -1)}`: `2 • P = 0` exactly when
`P.x = 0`. -/
theorem two_nsmul_eq_zero_iff (P : E.Point) : 2 • P = 0 ↔ P.x = 0 := by
  rw [two_nsmul, add_eq_zero_iff_eq_neg, Point.ext_iff, neg_x, neg_y]
  have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
  constructor
  · rintro ⟨hx, -⟩
    exact (mul_eq_zero.mp (show 2 * P.x = 0 by linear_combination hx)).resolve_left h2
  · intro hx
    exact ⟨by rw [hx, neg_zero], rfl⟩

/-! ### The curve -/

/-- The curve of the Montgomery model of `E` is the curve of `E`. -/
theorem toCurve_toMontgomery (E : TwistedEdwardsModel F) [E.IsComplete] [NeZero (6 : F)] :
    E.toMontgomery.toCurve = E.toCurve := by
  rfl

omit [E.IsComplete] in
/-- The discriminant of the invariants: `c₄³ - c₆² = 2¹⁴ 3³ a d (a - d)⁴`. -/
theorem c₄_cube_sub_c₆_sq : E.c₄ ^ 3 - E.c₆ ^ 2 = 442368 * E.a * E.d * (E.a - E.d) ^ 4 := by
  simp only [c₄, c₆]
  ring

theorem c₄_cube_sub_c₆_sq_ne_zero [NeZero (6 : F)] : E.c₄ ^ 3 - E.c₆ ^ 2 ≠ 0 := by
  rw [c₄_cube_sub_c₆_sq, show (442368 : F) = 2 ^ 14 * 3 ^ 3 by norm_num]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ two_ne_zero)
    (pow_ne_zero _ (NeZero.ne _))) IsComplete.a_ne_zero) E.d_ne_zero)
    (pow_ne_zero _ (sub_ne_zero.mpr E.a_ne_d))

/-- **The curve of a twisted Edwards model** is the curve with invariants `E.c₄`, `E.c₆`: the
invariants of its Montgomery model are `u⁴ E.c₄`, `u⁶ E.c₆` with `u = 2 / (a - d)`. -/
theorem toCurve_eq_mk [NeZero (6 : F)] :
    E.toCurve = Curve.mk E.c₄ E.c₆ E.c₄_cube_sub_c₆_sq_ne_zero := by
  have had : E.a - E.d ≠ 0 := sub_ne_zero.mpr E.a_ne_d
  rw [← toCurve_toMontgomery, MontgomeryModel.toCurve_eq_mk]
  refine Curve.mk_eq_mk_of (2 / (E.a - E.d)) (div_ne_zero two_ne_zero had) ?_ ?_ <;>
    simp only [MontgomeryModel.c₄, MontgomeryModel.c₆, toMontgomery_A, toMontgomery_B, c₄, c₆] <;>
    field_simp <;> ring

/-- The j-invariant of a twisted Edwards model: `16 (a² + 14 a d + d²)³ / (a d (a - d)⁴)`. -/
theorem j_toCurve [NeZero (6 : F)] :
    E.toCurve.j =
      16 * (E.a ^ 2 + 14 * E.a * E.d + E.d ^ 2) ^ 3 / (E.a * E.d * (E.a - E.d) ^ 4) := by
  have h : (442368 : F) ≠ 0 := by
    rw [show (442368 : F) = 2 ^ 14 * 3 ^ 3 by norm_num]
    exact mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ (NeZero.ne _))
  have ha : E.a ≠ 0 := IsComplete.a_ne_zero
  have hd : E.d ≠ 0 := E.d_ne_zero
  have had : E.a - E.d ≠ 0 := sub_ne_zero.mpr E.a_ne_d
  rw [toCurve_eq_mk, Curve.j_mk, c₄_cube_sub_c₆_sq, c₄]
  field_simp
  ring

/-- `pointEquiv` factors through the Montgomery model. -/
theorem pointEquiv_eq (E : TwistedEdwardsModel F) [E.IsComplete] [NeZero (6 : F)] :
    E.pointEquiv = E.toMontgomeryEquiv.trans E.toMontgomery.pointEquiv := by
  rfl

/-! ### The equivalence with the Montgomery model, in coordinates -/

/-- The `u`-coordinate of the image of `P` is `(1 + y) / (1 - y)` (which is `0` at `(0, 1)`,
whose image is `∞`, as the convention `u ∞ = 0` requires). -/
theorem u_toMontgomeryEquiv (P : E.Point) :
    (E.toMontgomeryEquiv P).u = (1 + P.y) / (1 - P.y) := by
  rcases MontgomeryModel.Point.cases (E.toMontgomeryEquiv P) with hQ | ⟨u, v, hm, hQ⟩
  · rw [hQ, MontgomeryModel.u_zero, (xy_of_zero hQ).2, sub_self, div_zero]
  · rw [hQ, MontgomeryModel.u_some]
    by_cases hv : v = 0
    · rw [E.toMontgomery_u_eq_zero_of_v_eq_zero hm hv, (xy_of_some_of_v_eq_zero hQ hv).2]
      norm_num
    · have hu1 := E.toMontgomery_u_add_one_ne_zero hm
      have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
      rw [(xy_of_some_of_v_ne_zero hQ hv).2, ratio_eq hu1 h2]

/-- The `v`-coordinate of the image of `P` is `(1 + y) / ((1 - y) x)` away from `(0, 1)`. -/
theorem v_toMontgomeryEquiv (P : E.Point) (hy : P.y ≠ 1) :
    (E.toMontgomeryEquiv P).v = (1 + P.y) / ((1 - P.y) * P.x) := by
  rcases MontgomeryModel.Point.cases (E.toMontgomeryEquiv P) with hQ | ⟨u, v, hm, hQ⟩
  · exact absurd (xy_of_zero hQ).2 hy
  · rw [hQ, MontgomeryModel.v_some]
    by_cases hv : v = 0
    · rw [hv, (xy_of_some_of_v_eq_zero hQ hv).1, mul_zero, div_zero]
    · have hu1 := E.toMontgomery_u_add_one_ne_zero hm
      have hu : u ≠ 0 := fun hu => hv (E.toMontgomery_v_eq_zero_of_u_eq_zero hm hu)
      have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
      obtain ⟨hx, hy⟩ := xy_of_some_of_v_ne_zero hQ hv
      rw [← div_div, hy, ratio_eq hu1 h2, hx, div_div_cancel₀ hu]

/-- The image of `(0, 1)` is the point at infinity. -/
theorem toMontgomeryEquiv_of_y_eq_one (P : E.Point) (h : P.y = 1) :
    E.toMontgomeryEquiv P = 0 := by
  have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
  rcases MontgomeryModel.Point.cases (E.toMontgomeryEquiv P) with hQ | ⟨u, v, hm, hQ⟩
  · exact hQ
  · exfalso
    by_cases hv : v = 0
    · have := (xy_of_some_of_v_eq_zero hQ hv).2
      rw [h] at this
      exact h2 (by linear_combination this)
    · have := (xy_of_some_of_v_ne_zero hQ hv).2
      have hu1 := E.toMontgomery_u_add_one_ne_zero hm
      rw [h, eq_div_iff hu1] at this
      exact h2 (by linear_combination this)

/-- The image of `(0, -1)` is `(0, 0)`. -/
theorem toMontgomeryEquiv_of_x_eq_zero (P : E.Point) (hx : P.x = 0) (hy : P.y = -1) :
    E.toMontgomeryEquiv P = .some 0 0 E.toMontgomery_equation_zero_zero := by
  have h2 : (2 : F) ≠ 0 := IsComplete.two_ne_zero (E := E)
  rcases MontgomeryModel.Point.cases (E.toMontgomeryEquiv P) with hQ | ⟨u, v, hm, hQ⟩
  · exfalso
    have := (xy_of_zero hQ).2
    rw [hy] at this
    exact h2 (by linear_combination -this)
  · rw [hQ]
    by_cases hv : v = 0
    · obtain rfl := E.toMontgomery_u_eq_zero_of_v_eq_zero hm hv
      subst hv
      rfl
    · exfalso
      have hu : u = 0 := by
        have := (xy_of_some_of_v_ne_zero hQ hv).1
        rw [hx] at this
        rcases div_eq_zero_iff.mp this.symm with h | h
        · exact h
        · exact absurd h hv
      exact hv (E.toMontgomery_v_eq_zero_of_u_eq_zero hm hu)

/-- The `x`-coordinate of the preimage of a Montgomery point `Q` with `v ≠ 0` is `u / v`. -/
theorem toMontgomeryEquiv_symm_x (Q : E.toMontgomery.Point) (hv : Q.v ≠ 0) :
    (E.toMontgomeryEquiv.symm Q).x = Q.u / Q.v := by
  rcases MontgomeryModel.Point.cases Q with rfl | ⟨u, v, h, rfl⟩
  · exact absurd MontgomeryModel.v_zero hv
  · rw [MontgomeryModel.v_some] at hv
    rw [(xy_of_some_of_v_ne_zero (E.toMontgomeryEquiv.apply_symm_apply (.some u v h)) hv).1,
      MontgomeryModel.u_some, MontgomeryModel.v_some]

/-- The `y`-coordinate of the preimage of an affine Montgomery point `Q` is
`(u - 1) / (u + 1)` (for `Q = ∞`, whose `u` is `0` by convention, the preimage is `(0, 1)`). -/
theorem toMontgomeryEquiv_symm_y (Q : E.toMontgomery.Point) (hQ : Q ≠ 0) :
    (E.toMontgomeryEquiv.symm Q).y = (Q.u - 1) / (Q.u + 1) := by
  rcases MontgomeryModel.Point.cases Q with rfl | ⟨u, v, h, rfl⟩
  · exact absurd rfl hQ
  · have e := E.toMontgomeryEquiv.apply_symm_apply (.some u v h)
    rw [MontgomeryModel.u_some]
    by_cases hv : v = 0
    · rw [(xy_of_some_of_v_eq_zero e hv).2, E.toMontgomery_u_eq_zero_of_v_eq_zero h hv]
      norm_num
    · rw [(xy_of_some_of_v_ne_zero e hv).2]

end IsComplete

end TwistedEdwardsModel
