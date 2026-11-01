/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.TwistedEdwards.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Twisted Edwards models: coordinate systems

The projective coordinate systems of a twisted Edwards model `E` used for inversion-free
arithmetic (Hisil–Wong–Carter–Dawson, *Twisted Edwards curves revisited*, 2008):

* `E.Extended`: `(X : Y : Z : T)` with `x = X / Z`, `y = Y / Z`, `x y = T / Z`;
* `E.Projective`: `(X : Y : Z)` with `x = X / Z`, `y = Y / Z`;
* `E.Completed`: `((X : Z), (Y : T)) ∈ ℙ¹ × ℙ¹` with `x = X / Z`, `y = Y / T`.

Each is a plain structure of field elements, with

* an exposed validity predicate `OnCurve`, stated with the affine point, restated without division
  by `onCurve_iff_homogeneous`, and decided through that form;
* a total hidden `toPoint` into `E.Point`: the affine point when `OnCurve`, and `(0, 1)` otherwise
  (the neutral element `0` when `E` is complete); characterised by `toPoint_x`, `toPoint_y`,
  `toPoint_of_not_onCurve`, for any model;
* the exposed, decidable projective equality `ProjEq`, with `projEq_iff_toPoint_eq`;
* the exposed identity `identity` and negation `neg`, the conversions `toExtended`,
  `toProjective`, `toCompleted` between the systems, and those from affine points
  (`Point.toExtended`, `Point.toProjective`, `Point.toCompleted`).

Their `onCurve_*` and `toPoint_*` lemmas are in `EllipticCurve.TwistedEdwards.Coords.Lemmas`. The
group operations in coordinates are in `EllipticCurve.TwistedEdwards.Formulas.*`.

Ported from curve25519-dalek's Lean verification
(`Curve25519/Models/TwistedEdwards/Coords/Defs.lean`, commit `d2e92e7`), without the Niels
coordinate systems; `OnCurve` is decided without division, `toPoint` no longer needs a complete
model, and the operations missing there (projective negation, the identity, negation and
projective equality of completed coordinates, the conversions to completed coordinates and from
affine points) are added. -/

public section

universe u

namespace TwistedEdwardsModel

variable {F : Type u} [Field F] (E : TwistedEdwardsModel F)

/-- The defining equation of `E` at `(X / Z, Y / T)`, without division. -/
theorem equation_div_iff {X Y Z T : F} (hZ : Z ≠ 0) (hT : T ≠ 0) :
    E.Equation (X / Z) (Y / T) ↔
      E.a * X ^ 2 * T ^ 2 + Y ^ 2 * Z ^ 2 = Z ^ 2 * T ^ 2 + E.d * X ^ 2 * Y ^ 2 := by
  have hZT : Z ^ 2 * T ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero 2 hZ) (pow_ne_zero 2 hT)
  have key : E.a * (X / Z) ^ 2 + (Y / T) ^ 2 - (1 + E.d * (X / Z) ^ 2 * (Y / T) ^ 2) =
      (E.a * X ^ 2 * T ^ 2 + Y ^ 2 * Z ^ 2 - (Z ^ 2 * T ^ 2 + E.d * X ^ 2 * Y ^ 2)) /
        (Z ^ 2 * T ^ 2) := by
    field_simp
  unfold Equation
  rw [← sub_eq_zero, key, div_eq_zero_iff, or_iff_left hZT, sub_eq_zero]

/-! ### The coordinate systems -/

/-- Extended coordinates `(X : Y : Z : T)`: `x = X / Z`, `y = Y / Z`, `x y = T / Z`. -/
@[ext] structure Extended (E : TwistedEdwardsModel F) where
  /-- The `X`-coordinate. -/
  X : F
  /-- The `Y`-coordinate. -/
  Y : F
  /-- The `Z`-coordinate. -/
  Z : F
  /-- The `T`-coordinate, `T / Z = x y`. -/
  T : F
  deriving DecidableEq

/-- Projective coordinates `(X : Y : Z)`: `x = X / Z`, `y = Y / Z`. -/
@[ext] structure Projective (E : TwistedEdwardsModel F) where
  /-- The `X`-coordinate. -/
  X : F
  /-- The `Y`-coordinate. -/
  Y : F
  /-- The `Z`-coordinate. -/
  Z : F
  deriving DecidableEq

/-- Completed coordinates `((X : Z), (Y : T)) ∈ ℙ¹ × ℙ¹`: `x = X / Z`, `y = Y / T`. -/
@[ext] structure Completed (E : TwistedEdwardsModel F) where
  /-- The `X`-coordinate, `x = X / Z`. -/
  X : F
  /-- The `Y`-coordinate, `y = Y / T`. -/
  Y : F
  /-- The denominator of `x`. -/
  Z : F
  /-- The denominator of `y`. -/
  T : F
  deriving DecidableEq

variable {E}

/-! ### Extended coordinates -/

namespace Extended

/-- `(X : Y : Z : T)` represents a point of `E`: `Z ≠ 0`, `X Y = Z T` and `(X / Z, Y / Z)`
satisfies the equation. -/
@[expose] def OnCurve (P : E.Extended) : Prop :=
  P.Z ≠ 0 ∧ P.X * P.Y = P.Z * P.T ∧ E.Equation (P.X / P.Z) (P.Y / P.Z)

/-- `OnCurve` without division: `a X² Z² + Y² Z² = Z⁴ + d X² Y²`. -/
theorem onCurve_iff_homogeneous (P : E.Extended) :
    P.OnCurve ↔ P.Z ≠ 0 ∧ P.X * P.Y = P.Z * P.T ∧
      E.a * P.X ^ 2 * P.Z ^ 2 + P.Y ^ 2 * P.Z ^ 2 = P.Z ^ 4 + E.d * P.X ^ 2 * P.Y ^ 2 := by
  constructor
  · rintro ⟨hZ, hT, h⟩
    rw [equation_div_iff E hZ hZ] at h
    exact ⟨hZ, hT, by linear_combination h⟩
  · rintro ⟨hZ, hT, h⟩
    exact ⟨hZ, hT, (E.equation_div_iff hZ hZ).mpr (by linear_combination h)⟩

/-- `OnCurve` is decidable through its form without division (`onCurve_iff_homogeneous`), so
that the kernel can evaluate it. -/
instance instDecidableOnCurve [DecidableEq F] (P : E.Extended) : Decidable P.OnCurve :=
  decidable_of_iff _ (onCurve_iff_homogeneous P).symm

/-- Projective equality of `(X : Y : Z)`; `T` is determined by them on the curve. -/
@[expose] def ProjEq (P Q : E.Extended) : Prop :=
  P.X * Q.Z = Q.X * P.Z ∧ P.Y * Q.Z = Q.Y * P.Z

instance instDecidableRelProjEq [DecidableEq F] : DecidableRel (ProjEq (E := E)) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

open scoped Classical in
/-- The point represented by `(X : Y : Z : T)`: `(X / Z, Y / Z)` when `OnCurve`, and `(0, 1)`
otherwise. Hidden; characterised by `toPoint_x`, `toPoint_y`, `toPoint_of_not_onCurve`. -/
noncomputable def toPoint (P : E.Extended) : E.Point :=
  if h : P.OnCurve then ⟨P.X / P.Z, P.Y / P.Z, h.2.2⟩ else ⟨0, 1, E.equation_zero_one⟩

/-- The `x`-coordinate of the point represented by `(X : Y : Z : T)` is `X / Z`. -/
theorem toPoint_x {P : E.Extended} (h : P.OnCurve) : P.toPoint.x = P.X / P.Z := by
  unfold toPoint
  rw [dite_eq_left h]

/-- The `y`-coordinate of the point represented by `(X : Y : Z : T)` is `Y / Z`. -/
theorem toPoint_y {P : E.Extended} (h : P.OnCurve) : P.toPoint.y = P.Y / P.Z := by
  unfold toPoint
  rw [dite_eq_left h]

/-- Off the curve, `toPoint` is `(0, 1)`. -/
theorem toPoint_of_not_onCurve {P : E.Extended} (h : ¬ P.OnCurve) :
    P.toPoint = ⟨0, 1, E.equation_zero_one⟩ := by
  unfold toPoint
  rw [dite_eq_right h]

/-- Off the curve of a complete model, `toPoint` is `0`. -/
theorem toPoint_eq_zero_of_not_onCurve [E.IsComplete] {P : E.Extended} (h : ¬ P.OnCurve) :
    P.toPoint = 0 := by
  rw [toPoint_of_not_onCurve h, zero_eq_mk]

/-- Projective equality is equality of the represented points. -/
theorem projEq_iff_toPoint_eq {P Q : E.Extended} (hP : P.OnCurve) (hQ : Q.OnCurve) :
    P.ProjEq Q ↔ P.toPoint = Q.toPoint := by
  rw [Point.ext_iff, toPoint_x hP, toPoint_x hQ, toPoint_y hP, toPoint_y hQ,
    div_eq_div_iff hP.1 hQ.1, div_eq_div_iff hP.1 hQ.1]
  rfl

/-- The identity `(0 : 1 : 1 : 0)` -/
@[expose] def identity : E.Extended :=
  ⟨0, 1, 1, 0⟩

/-- Negation `(X : Y : Z : T) ↦ (-X : Y : Z : -T)` -/
@[expose] def neg (P : E.Extended) : E.Extended :=
  ⟨-P.X, P.Y, P.Z, -P.T⟩

/-- Forget `T`. -/
@[expose] def toProjective (P : E.Extended) : E.Projective :=
  ⟨P.X, P.Y, P.Z⟩

/-- Completed coordinates `((X : Z), (Y : Z))`. -/
@[expose] def toCompleted (P : E.Extended) : E.Completed :=
  ⟨P.X, P.Y, P.Z, P.Z⟩

end Extended

/-! ### Projective coordinates -/

namespace Projective

/-- `(X : Y : Z)` represents a point of `E`: `Z ≠ 0` and `(X / Z, Y / Z)` satisfies the
equation. -/
@[expose] def OnCurve (P : E.Projective) : Prop :=
  P.Z ≠ 0 ∧ E.Equation (P.X / P.Z) (P.Y / P.Z)

/-- `OnCurve` without division: `a X² Z² + Y² Z² = Z⁴ + d X² Y²`. -/
theorem onCurve_iff_homogeneous (P : E.Projective) :
    P.OnCurve ↔ P.Z ≠ 0 ∧
      E.a * P.X ^ 2 * P.Z ^ 2 + P.Y ^ 2 * P.Z ^ 2 = P.Z ^ 4 + E.d * P.X ^ 2 * P.Y ^ 2 := by
  constructor
  · rintro ⟨hZ, h⟩
    rw [equation_div_iff E hZ hZ] at h
    exact ⟨hZ, by linear_combination h⟩
  · rintro ⟨hZ, h⟩
    exact ⟨hZ, (E.equation_div_iff hZ hZ).mpr (by linear_combination h)⟩

/-- `OnCurve` is decidable through its form without division (`onCurve_iff_homogeneous`), so
that the kernel can evaluate it. -/
instance instDecidableOnCurve [DecidableEq F] (P : E.Projective) : Decidable P.OnCurve :=
  decidable_of_iff _ (onCurve_iff_homogeneous P).symm

/-- Projective equality. -/
@[expose] def ProjEq (P Q : E.Projective) : Prop :=
  P.X * Q.Z = Q.X * P.Z ∧ P.Y * Q.Z = Q.Y * P.Z

instance instDecidableRelProjEq [DecidableEq F] : DecidableRel (ProjEq (E := E)) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

open scoped Classical in
/-- The point represented by `(X : Y : Z)`: `(X / Z, Y / Z)` when `OnCurve`, and `(0, 1)`
otherwise. Hidden; characterised by `toPoint_x`, `toPoint_y`, `toPoint_of_not_onCurve`. -/
noncomputable def toPoint (P : E.Projective) : E.Point :=
  if h : P.OnCurve then ⟨P.X / P.Z, P.Y / P.Z, h.2⟩ else ⟨0, 1, E.equation_zero_one⟩

/-- The `x`-coordinate of the point represented by `(X : Y : Z)` is `X / Z`. -/
theorem toPoint_x {P : E.Projective} (h : P.OnCurve) : P.toPoint.x = P.X / P.Z := by
  unfold toPoint
  rw [dite_eq_left h]

/-- The `y`-coordinate of the point represented by `(X : Y : Z)` is `Y / Z`. -/
theorem toPoint_y {P : E.Projective} (h : P.OnCurve) : P.toPoint.y = P.Y / P.Z := by
  unfold toPoint
  rw [dite_eq_left h]

/-- Off the curve, `toPoint` is `(0, 1)`. -/
theorem toPoint_of_not_onCurve {P : E.Projective} (h : ¬ P.OnCurve) :
    P.toPoint = ⟨0, 1, E.equation_zero_one⟩ := by
  unfold toPoint
  rw [dite_eq_right h]

/-- Off the curve of a complete model, `toPoint` is `0`. -/
theorem toPoint_eq_zero_of_not_onCurve [E.IsComplete] {P : E.Projective} (h : ¬ P.OnCurve) :
    P.toPoint = 0 := by
  rw [toPoint_of_not_onCurve h, zero_eq_mk]

/-- Projective equality is equality of the represented points. -/
theorem projEq_iff_toPoint_eq {P Q : E.Projective} (hP : P.OnCurve) (hQ : Q.OnCurve) :
    P.ProjEq Q ↔ P.toPoint = Q.toPoint := by
  rw [Point.ext_iff, toPoint_x hP, toPoint_x hQ, toPoint_y hP, toPoint_y hQ,
    div_eq_div_iff hP.1 hQ.1, div_eq_div_iff hP.1 hQ.1]
  rfl

/-- The identity `(0 : 1 : 1)` -/
@[expose] def identity : E.Projective :=
  ⟨0, 1, 1⟩

/-- Negation `(X : Y : Z) ↦ (-X : Y : Z)`. -/
@[expose] def neg (P : E.Projective) : E.Projective :=
  ⟨-P.X, P.Y, P.Z⟩

/-- Extended coordinates `(X Z : Y Z : Z² : X Y)` -/
@[expose] def toExtended (P : E.Projective) : E.Extended :=
  ⟨P.X * P.Z, P.Y * P.Z, P.Z ^ 2, P.X * P.Y⟩

/-- Completed coordinates `((X : Z), (Y : Z))`. -/
@[expose] def toCompleted (P : E.Projective) : E.Completed :=
  ⟨P.X, P.Y, P.Z, P.Z⟩

end Projective

/-! ### Completed coordinates -/

namespace Completed

/-- `((X : Z), (Y : T))` represents a point of `E`: `Z ≠ 0`, `T ≠ 0` and `(X / Z, Y / T)`
satisfies the equation. -/
@[expose] def OnCurve (P : E.Completed) : Prop :=
  P.Z ≠ 0 ∧ P.T ≠ 0 ∧ E.Equation (P.X / P.Z) (P.Y / P.T)

/-- `OnCurve` without division: `a X² T² + Y² Z² = Z² T² + d X² Y²`. -/
theorem onCurve_iff_homogeneous (P : E.Completed) :
    P.OnCurve ↔ P.Z ≠ 0 ∧ P.T ≠ 0 ∧
      E.a * P.X ^ 2 * P.T ^ 2 + P.Y ^ 2 * P.Z ^ 2 =
        P.Z ^ 2 * P.T ^ 2 + E.d * P.X ^ 2 * P.Y ^ 2 := by
  constructor
  · rintro ⟨hZ, hT, h⟩
    exact ⟨hZ, hT, (E.equation_div_iff hZ hT).mp h⟩
  · rintro ⟨hZ, hT, h⟩
    exact ⟨hZ, hT, (E.equation_div_iff hZ hT).mpr h⟩

/-- `OnCurve` is decidable through its form without division (`onCurve_iff_homogeneous`), so
that the kernel can evaluate it. -/
instance instDecidableOnCurve [DecidableEq F] (P : E.Completed) : Decidable P.OnCurve :=
  decidable_of_iff _ (onCurve_iff_homogeneous P).symm

/-- Projective equality in `ℙ¹ × ℙ¹`: `(X : Z)` and `(Y : T)` agree separately. -/
@[expose] def ProjEq (P Q : E.Completed) : Prop :=
  P.X * Q.Z = Q.X * P.Z ∧ P.Y * Q.T = Q.Y * P.T

instance instDecidableRelProjEq [DecidableEq F] : DecidableRel (ProjEq (E := E)) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

open scoped Classical in
/-- The point represented by `((X : Z), (Y : T))`: `(X / Z, Y / T)` when `OnCurve`, and `(0, 1)`
otherwise. Hidden; characterised by `toPoint_x`, `toPoint_y`, `toPoint_of_not_onCurve`. -/
noncomputable def toPoint (P : E.Completed) : E.Point :=
  if h : P.OnCurve then ⟨P.X / P.Z, P.Y / P.T, h.2.2⟩ else ⟨0, 1, E.equation_zero_one⟩

/-- The `x`-coordinate of the point represented by `((X : Z), (Y : T))` is `X / Z`. -/
theorem toPoint_x {P : E.Completed} (h : P.OnCurve) : P.toPoint.x = P.X / P.Z := by
  unfold toPoint
  rw [dite_eq_left h]

/-- The `y`-coordinate of the point represented by `((X : Z), (Y : T))` is `Y / T`. -/
theorem toPoint_y {P : E.Completed} (h : P.OnCurve) : P.toPoint.y = P.Y / P.T := by
  unfold toPoint
  rw [dite_eq_left h]

/-- Off the curve, `toPoint` is `(0, 1)`. -/
theorem toPoint_of_not_onCurve {P : E.Completed} (h : ¬ P.OnCurve) :
    P.toPoint = ⟨0, 1, E.equation_zero_one⟩ := by
  unfold toPoint
  rw [dite_eq_right h]

/-- Off the curve of a complete model, `toPoint` is `0`. -/
theorem toPoint_eq_zero_of_not_onCurve [E.IsComplete] {P : E.Completed} (h : ¬ P.OnCurve) :
    P.toPoint = 0 := by
  rw [toPoint_of_not_onCurve h, zero_eq_mk]

/-- Projective equality is equality of the represented points. -/
theorem projEq_iff_toPoint_eq {P Q : E.Completed} (hP : P.OnCurve) (hQ : Q.OnCurve) :
    P.ProjEq Q ↔ P.toPoint = Q.toPoint := by
  rw [Point.ext_iff, toPoint_x hP, toPoint_x hQ, toPoint_y hP, toPoint_y hQ,
    div_eq_div_iff hP.1 hQ.1, div_eq_div_iff hP.2.1 hQ.2.1]
  rfl

/-- The identity `((0 : 1), (1 : 1))`. -/
@[expose] def identity : E.Completed :=
  ⟨0, 1, 1, 1⟩

/-- Negation `((X : Z), (Y : T)) ↦ ((-X : Z), (Y : T))`. -/
@[expose] def neg (P : E.Completed) : E.Completed :=
  ⟨-P.X, P.Y, P.Z, P.T⟩

/-- Extended coordinates `(X T : Y Z : Z T : X Y)` -/
@[expose] def toExtended (P : E.Completed) : E.Extended :=
  ⟨P.X * P.T, P.Y * P.Z, P.Z * P.T, P.X * P.Y⟩

/-- Projective coordinates `(X T : Y Z : Z T)` -/
@[expose] def toProjective (P : E.Completed) : E.Projective :=
  ⟨P.X * P.T, P.Y * P.Z, P.Z * P.T⟩

end Completed

/-! ### From affine points -/

namespace Point

/-- Extended coordinates `(x : y : 1 : x y)` of an affine point. -/
@[expose] def toExtended (P : E.Point) : E.Extended :=
  ⟨P.x, P.y, 1, P.x * P.y⟩

/-- Projective coordinates `(x : y : 1)` of an affine point. -/
@[expose] def toProjective (P : E.Point) : E.Projective :=
  ⟨P.x, P.y, 1⟩

/-- Completed coordinates `((x : 1), (y : 1))` of an affine point. -/
@[expose] def toCompleted (P : E.Point) : E.Completed :=
  ⟨P.x, P.y, 1, 1⟩

end Point

end TwistedEdwardsModel
