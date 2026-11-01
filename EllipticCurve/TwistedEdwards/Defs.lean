/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Montgomery.Defs
public import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Twisted Edwards models: definitions

A twisted Edwards model `E = (a, d)` over a field `F` is the equation `a x² + y² = 1 + d x² y²`
(`TwistedEdwardsModel.Equation`); its points (`E.Point`) are the affine solutions. When `E` is
*complete* (`E.IsComplete`: `a` a nonzero square, `d` a non-square, `2 ≠ 0`), the affine points
form the whole group and the addition formula `addX`, `addY` has no exceptional case.

The Montgomery model `E.toMontgomery = (2 (a + d) / (a - d), 4 / (a - d))` of `E` is defined
here; the group structure on `E.Point`, the isomorphism `E.toMontgomeryEquiv`, `E.toCurve` and
`E.pointEquiv` are in `EllipticCurve.TwistedEdwards.Group`. -/

public section

universe u

/-- A twisted Edwards model `a x² + y² = 1 + d x² y²` over `F`: the coefficients of the
equation. -/
structure TwistedEdwardsModel (F : Type u) [Field F] where
  /-- The coefficient of `x²`. -/
  a : F
  /-- The coefficient of `x² y²`. -/
  d : F

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] (E : TwistedEdwardsModel F)

/-- The defining equation `a x² + y² = 1 + d x² y²` of the model. -/
@[expose] def Equation (x y : F) : Prop :=
  E.a * x ^ 2 + y ^ 2 = 1 + E.d * x ^ 2 * y ^ 2

/-- The invariant `c₄ = 16 (a² + 14 a d + d²)` of the model. The invariants of the Montgomery
model are `M.c₄ = u⁴ E.c₄`, `M.c₆ = u⁶ E.c₆` with `u = 2 / (a - d)` (`toCurve_eq_mk`). -/
@[expose] def c₄ : F :=
  16 * (E.a ^ 2 + 14 * E.a * E.d + E.d ^ 2)

/-- The invariant `c₆ = 64 (a + d) (a² - 34 a d + d²)` of the model. -/
@[expose] def c₆ : F :=
  64 * (E.a + E.d) * (E.a ^ 2 - 34 * E.a * E.d + E.d ^ 2)

/-- Completeness: `a` is a nonzero square, `d` is not a square, and `2 ≠ 0` in `F`. The affine
points then form the whole group and the addition formula has no exceptional case
(`addDen₁_ne_zero`, `addDen₂_ne_zero` in `EllipticCurve.TwistedEdwards.Lemmas`). -/
class IsComplete : Prop where
  two_ne_zero : (2 : F) ≠ 0
  isSquare_a : IsSquare E.a
  a_ne_zero : E.a ≠ 0
  not_isSquare_d : ¬ IsSquare E.d

/-- The points of `E`: the affine solutions of its equation. -/
@[ext] structure Point where
  /-- The `x`-coordinate. -/
  x : F
  /-- The `y`-coordinate. -/
  y : F
  /-- The point is on the model. -/
  equation : E.Equation x y
  deriving DecidableEq

/-- A model over a finite field has finitely many points. -/
instance instFinitePoint [Finite F] : Finite E.Point :=
  Finite.of_injective (fun P : E.Point => (P.x, P.y)) fun _ _ h =>
    Point.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-! ### The equation -/

/-- `(0, 1)` is on every model. -/
theorem equation_zero_one : E.Equation 0 1 := by
  unfold Equation
  ring

/-- `(0, -1)` is on every model. -/
theorem equation_zero_neg_one : E.Equation 0 (-1) := by
  unfold Equation
  ring

variable {E}

/-- If `(x, y)` is on the model then so is `(-x, y)`. -/
theorem equation_neg {x y : F} (h : E.Equation x y) : E.Equation (-x) y := by
  unfold Equation at h ⊢
  rwa [neg_sq]

/-- On the model, `x = 0` forces `y² = 1`. -/
theorem y_sq_eq_one_of_x_eq_zero {x y : F} (h : E.Equation x y) (hx : x = 0) : y ^ 2 = 1 := by
  subst hx
  unfold Equation at h
  linear_combination h

/-- On the model, `x = 0` forces `y = 1` or `y = -1`. -/
theorem y_eq_one_or_eq_neg_one_of_x_eq_zero {x y : F} (h : E.Equation x y) (hx : x = 0) :
    y = 1 ∨ y = -1 :=
  sq_eq_one_iff.mp (y_sq_eq_one_of_x_eq_zero h hx)

/-! ### Consequences of completeness -/

section IsComplete

variable (E) [E.IsComplete]

/-- `d ≠ 0` for a complete model (`0` is a square). -/
theorem d_ne_zero : E.d ≠ 0 := fun h =>
  IsComplete.not_isSquare_d (E := E) ⟨0, by rw [h, mul_zero]⟩

/-- `a ≠ d` for a complete model (`a` is a square, `d` is not). -/
theorem a_ne_d : E.a ≠ E.d := fun h =>
  IsComplete.not_isSquare_d (E := E) (h ▸ IsComplete.isSquare_a)

variable {E}

/-- On a complete model, `y² = 1` forces `x = 0` (since `a ≠ d`). -/
theorem x_eq_zero_of_y_sq_eq_one {x y : F} (h : E.Equation x y) (hy : y ^ 2 = 1) : x = 0 := by
  have key : (E.a - E.d) * x ^ 2 = 0 := by
    unfold Equation at h
    linear_combination h - (1 - E.d * x ^ 2) * hy
  exact (pow_eq_zero_iff two_ne_zero).mp
    ((mul_eq_zero.mp key).resolve_left (sub_ne_zero.mpr E.a_ne_d))

/-- On a complete model, `y = 1` forces `x = 0`: `(0, 1)` is the only point with `y = 1`. -/
theorem x_eq_zero_of_y_eq_one {x y : F} (h : E.Equation x y) (hy : y = 1) : x = 0 :=
  x_eq_zero_of_y_sq_eq_one h (by rw [hy, one_pow])

/-- On a complete model, `y = -1` forces `x = 0`: `(0, -1)` is the only point with `y = -1`. -/
theorem x_eq_zero_of_y_eq_neg_one {x y : F} (h : E.Equation x y) (hy : y = -1) : x = 0 :=
  x_eq_zero_of_y_sq_eq_one h (by rw [hy, neg_one_sq])

/-- On a complete model, `x ≠ 0` gives `y ≠ 1`. -/
theorem y_ne_one_of_x_ne_zero {x y : F} (h : E.Equation x y) (hx : x ≠ 0) : y ≠ 1 :=
  fun hy => hx (x_eq_zero_of_y_eq_one h hy)

/-- On a complete model, `x ≠ 0` gives `y ≠ -1`. -/
theorem y_ne_neg_one_of_x_ne_zero {x y : F} (h : E.Equation x y) (hx : x ≠ 0) : y ≠ -1 :=
  fun hy => hx (x_eq_zero_of_y_eq_neg_one h hy)

end IsComplete

/-! ### Addition formulas

The complete twisted Edwards addition law, as exposed functions of the two points, so that they
can be evaluated: `(x₁, y₁) + (x₂, y₂) = ((x₁ y₂ + x₂ y₁) / (1 + d x₁ x₂ y₁ y₂),
(y₁ y₂ - a x₁ x₂) / (1 - d x₁ x₂ y₁ y₂))`. They describe the group law of a complete model
(`add_x`, `add_y` in `EllipticCurve.TwistedEdwards.Lemmas`). -/

/-- The denominator `1 + d x₁ x₂ y₁ y₂` of the `x`-coordinate of the sum. -/
@[expose] def addDen₁ (P Q : E.Point) : F :=
  1 + E.d * P.x * Q.x * P.y * Q.y

/-- The denominator `1 - d x₁ x₂ y₁ y₂` of the `y`-coordinate of the sum. -/
@[expose] def addDen₂ (P Q : E.Point) : F :=
  1 - E.d * P.x * Q.x * P.y * Q.y

/-- The `x`-coordinate `(x₁ y₂ + x₂ y₁) / (1 + d x₁ x₂ y₁ y₂)` of the sum. -/
@[expose] def addX (P Q : E.Point) : F :=
  (P.x * Q.y + Q.x * P.y) / addDen₁ P Q

/-- The `y`-coordinate `(y₁ y₂ - a x₁ x₂) / (1 - d x₁ x₂ y₁ y₂)` of the sum. -/
@[expose] def addY (P Q : E.Point) : F :=
  (P.y * Q.y - E.a * P.x * Q.x) / addDen₂ P Q

/-! ### The Montgomery model of a twisted Edwards model -/

variable (E)

/-- The Montgomery model `(2 (a + d) / (a - d), 4 / (a - d))` birationally equivalent to `E`
(`E.toMontgomeryEquiv`). Hidden; see `toMontgomery_def`, `toMontgomery_A`, `toMontgomery_B`. -/
def toMontgomery : MontgomeryModel F :=
  ⟨2 * (E.a + E.d) / (E.a - E.d), 4 / (E.a - E.d)⟩

/-- The defining equation of `toMontgomery`. -/
theorem toMontgomery_def : E.toMontgomery = ⟨2 * (E.a + E.d) / (E.a - E.d), 4 / (E.a - E.d)⟩ := by
  rfl

/-- The coefficient `A = 2 (a + d) / (a - d)` of the Montgomery model of `E`. -/
theorem toMontgomery_A : E.toMontgomery.A = 2 * (E.a + E.d) / (E.a - E.d) := by
  rfl

/-- The coefficient `B = 4 / (a - d)` of the Montgomery model of `E`. -/
theorem toMontgomery_B : E.toMontgomery.B = 4 / (E.a - E.d) := by
  rfl

/-- `(0, 0)` is on the Montgomery model of `E`. -/
theorem toMontgomery_equation_zero_zero : E.toMontgomery.Equation 0 0 := by
  unfold MontgomeryModel.Equation
  ring

section IsComplete

variable [E.IsComplete]

/-- `a B = A + 2` relates the coefficients of `E` and of its Montgomery model. -/
theorem a_mul_toMontgomery_B : E.a * E.toMontgomery.B = E.toMontgomery.A + 2 := by
  have had : E.a - E.d ≠ 0 := sub_ne_zero.mpr E.a_ne_d
  rw [toMontgomery_A, toMontgomery_B]
  field_simp
  ring

/-- `d B = A - 2` relates the coefficients of `E` and of its Montgomery model. -/
theorem d_mul_toMontgomery_B : E.d * E.toMontgomery.B = E.toMontgomery.A - 2 := by
  have had : E.a - E.d ≠ 0 := sub_ne_zero.mpr E.a_ne_d
  rw [toMontgomery_A, toMontgomery_B]
  field_simp
  ring

/-- `B ≠ 0` for the Montgomery model of a complete `E`. -/
theorem toMontgomery_B_ne_zero : E.toMontgomery.B ≠ 0 := by
  rw [toMontgomery_B]
  refine div_ne_zero ?_ (sub_ne_zero.mpr E.a_ne_d)
  rw [show (4 : F) = 2 ^ 2 by norm_num]
  exact pow_ne_zero 2 (IsComplete.two_ne_zero (E := E))

/-- The Montgomery model of a complete twisted Edwards model is nonsingular:
`A² - 4 = a d B² ≠ 0`. -/
instance instIsNonsingularToMontgomery : E.toMontgomery.IsNonsingular where
  two_ne_zero := IsComplete.two_ne_zero (E := E)
  B_ne_zero := E.toMontgomery_B_ne_zero
  A_sq_ne_four := by
    intro h
    have key : E.a * E.d * E.toMontgomery.B ^ 2 = 0 := by
      linear_combination E.d * E.toMontgomery.B * E.a_mul_toMontgomery_B +
        (E.toMontgomery.A + 2) * E.d_mul_toMontgomery_B + h
    exact mul_ne_zero (mul_ne_zero (IsComplete.a_ne_zero (E := E)) E.d_ne_zero)
      (pow_ne_zero 2 E.toMontgomery_B_ne_zero) key

/-- On the Montgomery model of a complete `E`, `u + 1 ≠ 0`: `u = -1` would give `v² = d`. -/
theorem toMontgomery_u_add_one_ne_zero {u v : F} (h : E.toMontgomery.Equation u v) :
    u + 1 ≠ 0 := by
  intro hu
  have hu' : u = -1 := by linear_combination hu
  subst hu'
  apply IsComplete.not_isSquare_d (E := E)
  refine ⟨v, ?_⟩
  apply mul_left_cancel₀ E.toMontgomery_B_ne_zero
  unfold MontgomeryModel.Equation at h
  linear_combination -h + E.d_mul_toMontgomery_B

/-- Certificate for `toMontgomery_sq_add_mul_add_one_ne_zero`: if `u² + A u + 1 = 0` then
`d (s B)² = (2 u + A)²` where `a = s²`. -/
private theorem cert_no_root (a d A B u s : F) (hs : a = s * s) (haB : a * B = A + 2)
    (hdB : d * B = A - 2) (hq : u ^ 2 + A * u + 1 = 0) :
    d * (s * B * (s * B)) = (2 * u + A) * (2 * u + A) := by
  linear_combination (-d * B ^ 2) * hs + (A - 2) * haB + (a * B) * hdB + (-4) * hq

/-- On the Montgomery model of a complete `E`, `u² + A u + 1 ≠ 0`: a root would make
`A² - 4 = a d B²`, hence `d`, a square. So `(0, 0)` is the only affine point of order `2`. -/
theorem toMontgomery_sq_add_mul_add_one_ne_zero (u : F) :
    u ^ 2 + E.toMontgomery.A * u + 1 ≠ 0 := by
  intro hq
  obtain ⟨s, hs⟩ := IsComplete.isSquare_a (E := E)
  have hs0 : s ≠ 0 := fun h => IsComplete.a_ne_zero (E := E) (by rw [hs, h, mul_zero])
  have hB := E.toMontgomery_B_ne_zero
  apply IsComplete.not_isSquare_d (E := E)
  refine ⟨(2 * u + E.toMontgomery.A) / (s * E.toMontgomery.B), ?_⟩
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero (mul_ne_zero hs0 hB) (mul_ne_zero hs0 hB))]
  exact cert_no_root E.a E.d _ _ u s hs E.a_mul_toMontgomery_B E.d_mul_toMontgomery_B hq

/-- On the Montgomery model of a complete `E`, `v = 0` forces `u = 0`. -/
theorem toMontgomery_u_eq_zero_of_v_eq_zero {u v : F} (h : E.toMontgomery.Equation u v)
    (hv : v = 0) : u = 0 := by
  have key : u * (u ^ 2 + E.toMontgomery.A * u + 1) = 0 := by
    unfold MontgomeryModel.Equation at h
    rw [hv] at h
    linear_combination -h
  exact (mul_eq_zero.mp key).resolve_right (E.toMontgomery_sq_add_mul_add_one_ne_zero u)

/-- On the Montgomery model of a complete `E`, `u = 0` forces `v = 0`. -/
theorem toMontgomery_v_eq_zero_of_u_eq_zero {u v : F} (h : E.toMontgomery.Equation u v)
    (hu : u = 0) : v = 0 := by
  have key : E.toMontgomery.B * v ^ 2 = 0 := by
    unfold MontgomeryModel.Equation at h
    rw [hu] at h
    linear_combination h
  exact (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp key).resolve_left
  E.toMontgomery_B_ne_zero)

end IsComplete

end TwistedEdwardsModel
