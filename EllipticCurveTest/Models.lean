/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.Prime
-- The tests evaluate their own definitions by `decide`, so they are exposed.
/-! # Tests: the formulas of the models over small prime fields

Light, exhaustive checks of the model definitions against independent computations, by kernel
`decide`. In `𝔽_p` division is multiplication by the `(p - 2)`-th power (also at `0`), which
`decide` can evaluate; the bridging lemmas (`addX_eq`, `montgomery_eq`, …) show that the
computable copies are the library's formulas.

* **Twisted Edwards**, `x² + y² = 1 + 8 x² y²` over `𝔽₁₁` (complete, 8 points): the denominators
  never vanish, and the formula is closed, has neutral element `(0, 1)` and inverse `(-x, y)`, and
  is commutative and associative on all points; the library's group is this formula. A curve with
  `d` a square has a vanishing denominator.
* **Edwards → Montgomery**: `(x, y) ↦ ((1 + y) / (1 - y), u / x)`, `(0, 1) ↦ ∞`, is a bijection
  onto the points of `E.toMontgomery = (10, 1)` and is additive for the Montgomery
  chord-and-tangent law.
* **The Montgomery criterion** (`Curve.hasMontgomeryModel_mk_iff`) against a brute-force search
  over all Montgomery models and scalings, for every curve over `𝔽₅`. -/

@[expose] public section

namespace ModelTests

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance : NeZero (6 : ZMod 11) := ⟨by decide⟩
instance : NeZero (6 : ZMod 5) := ⟨by decide⟩

/-- In `𝔽₁₁`, `a / b = a b⁹` (Fermat; both sides are `0` at `b = 0`). -/
theorem div_eq (a b : ZMod 11) : a / b = a * b ^ 9 := by
  by_cases hb : b = 0
  · subst hb; simp
  · rw [div_eq_mul_inv]
    congr 1
    have h : b ^ 10 = 1 := ZMod.pow_card_sub_one_eq_one hb
    exact (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h)).symm

/-! ### Twisted Edwards -/

/-- The complete twisted Edwards curve `x² + y² = 1 + 8 x² y²` over `𝔽₁₁`. -/
def E : TwistedEdwardsModel (ZMod 11) := ⟨1, 8⟩

instance : E.IsComplete where
  two_ne_zero := by decide +kernel
  isSquare_a := ⟨1, by decide⟩
  a_ne_zero := by decide +kernel
  not_isSquare_d := by unfold IsSquare; decide

/-- Its points. -/
def pts : List (ZMod 11 × ZMod 11) :=
  [(0, 1), (0, 10), (1, 0), (2, 2), (2, 9), (9, 2), (9, 9), (10, 0)]

theorem equation_iff (x y : ZMod 11) : E.Equation x y ↔ (x, y) ∈ pts := by
  unfold TwistedEdwardsModel.Equation E; revert x y; decide +kernel

/-- The addition formula, computably. -/
def add (P Q : ZMod 11 × ZMod 11) : ZMod 11 × ZMod 11 :=
  ((P.1 * Q.2 + Q.1 * P.2) * (1 + 8 * P.1 * Q.1 * P.2 * Q.2) ^ 9,
    (P.2 * Q.2 - 1 * P.1 * Q.1) * (1 - 8 * P.1 * Q.1 * P.2 * Q.2) ^ 9)

/-- The computable formula is the library's. -/
theorem addX_eq (P Q : E.Point) :
    (TwistedEdwardsModel.addX P Q, TwistedEdwardsModel.addY P Q) = add (P.x, P.y) (Q.x, Q.y) := by
  simp only [TwistedEdwardsModel.addX, TwistedEdwardsModel.addY, TwistedEdwardsModel.addDen₁,
    TwistedEdwardsModel.addDen₂, div_eq, add, E]

/-- The library's group on `E` is the formula. -/
theorem group_eq (P Q : E.Point) : ((P + Q).x, (P + Q).y) = add (P.x, P.y) (Q.x, Q.y) := by
  rw [TwistedEdwardsModel.add_x, TwistedEdwardsModel.add_y, addX_eq]

/-- Completeness: the denominators never vanish. -/
example : ∀ P ∈ pts, ∀ Q ∈ pts,
    1 + 8 * P.1 * Q.1 * P.2 * Q.2 ≠ 0 ∧ 1 - 8 * P.1 * Q.1 * P.2 * Q.2 ≠ 0 := by decide +kernel

/-- Closure. -/
example : ∀ P ∈ pts, ∀ Q ∈ pts, add P Q ∈ pts := by decide +kernel

/-- `(0, 1)` is neutral and `(-x, y)` is the inverse. -/
example : ∀ P ∈ pts, add (0, 1) P = P ∧ add P (-P.1, P.2) = (0, 1) := by decide +kernel

/-- Commutativity. -/
example : ∀ P ∈ pts, ∀ Q ∈ pts, add P Q = add Q P := by decide +kernel

/-- Associativity. -/
example : ∀ P ∈ pts, ∀ Q ∈ pts, ∀ R ∈ pts, add (add P Q) R = add P (add Q R) := by decide +kernel

/-- With `d = 3`, a square, the curve `x² + y² = 1 + 3 x² y²` is not complete: `(4, 4)` and
`(5, 5)` are on it and a denominator of the formula vanishes. -/
example : IsSquare (3 : ZMod 11) ∧
    (4 : ZMod 11) ^ 2 + 4 ^ 2 = 1 + 3 * 4 ^ 2 * 4 ^ 2 ∧
    (5 : ZMod 11) ^ 2 + 5 ^ 2 = 1 + 3 * 5 ^ 2 * 5 ^ 2 ∧
    ((1 : ZMod 11) + 3 * 4 * 5 * 4 * 5 = 0 ∨ (1 : ZMod 11) - 3 * 4 * 5 * 4 * 5 = 0) := by
  unfold IsSquare; decide +kernel

/-! ### Edwards → Montgomery -/

/-- The Montgomery model of `E` is `(A, B) = (10, 1)`. -/
theorem montgomery_eq : E.toMontgomery = ⟨10, 1⟩ := by
  rw [TwistedEdwardsModel.toMontgomery_def]
  simp only [E, div_eq, MontgomeryModel.mk.injEq]
  decide

/-- The points of `(A, B) = (10, 1)`, with `none` the point at infinity. -/
def mpts : List (Option (ZMod 11 × ZMod 11)) :=
  [none, some (0, 0), some (1, 1), some (1, 10), some (7, 2), some (7, 9), some (8, 4),
    some (8, 7)]

theorem montgomery_equation_iff (u v : ZMod 11) :
    (⟨10, 1⟩ : MontgomeryModel (ZMod 11)).Equation u v ↔ some (u, v) ∈ mpts := by
  unfold MontgomeryModel.Equation; revert u v; decide +kernel

/-- The slope of the chord-and-tangent law of `(10, 1)`, computably. -/
def slope (P Q : ZMod 11 × ZMod 11) : ZMod 11 :=
  if P.1 = Q.1 then (3 * P.1 ^ 2 + 2 * 10 * P.1 + 1) * (2 * 1 * P.2) ^ 9
  else (Q.2 - P.2) * (Q.1 - P.1) ^ 9

/-- The computable slope is the library's. -/
theorem slope_eq (P Q : ZMod 11 × ZMod 11) (h : ¬(P.1 = Q.1 ∧ P.2 = -Q.2)) :
    (⟨10, 1⟩ : MontgomeryModel (ZMod 11)).slope P.1 P.2 Q.1 Q.2 = slope P Q := by
  by_cases hu : P.1 = Q.1
  · have hv : P.2 ≠ -Q.2 := fun hv => h ⟨hu, hv⟩
    simp [MontgomeryModel.slope, MontgomeryModel.tangentSlope, slope, hu, hv, div_eq]
  · simp [MontgomeryModel.slope, MontgomeryModel.chordSlope, slope, hu, div_eq]

/-- The chord-and-tangent law of `(10, 1)` (`MontgomeryModel.some_add_some`), computably. -/
def madd : Option (ZMod 11 × ZMod 11) → Option (ZMod 11 × ZMod 11) → Option (ZMod 11 × ZMod 11)
  | none, Q => Q
  | P, none => P
  | some P, some Q =>
    if P.1 = Q.1 ∧ P.2 = -Q.2 then none
    else
      let u := 1 * slope P Q ^ 2 - 10 - P.1 - Q.1
      some (u, slope P Q * (P.1 - u) - P.2)

/-- The map to the Montgomery model (`TwistedEdwardsModel.u_toMontgomeryEquiv`,
`v_toMontgomeryEquiv`), computably. -/
def toMont (P : ZMod 11 × ZMod 11) : Option (ZMod 11 × ZMod 11) :=
  if P.2 = 1 then none
  else some ((1 + P.2) * (1 - P.2) ^ 9, (1 + P.2) * (1 - P.2) ^ 9 * P.1 ^ 9)

/-- The map lands on the Montgomery model. -/
example : ∀ P ∈ pts, toMont P ∈ mpts := by decide +kernel

/-- It is injective, hence (8 points on each side) a bijection. -/
example : (∀ P ∈ pts, ∀ Q ∈ pts, toMont P = toMont Q → P = Q) ∧ pts.length = mpts.length := by
  decide +kernel

/-- It is additive: Edwards addition goes to the Montgomery chord-and-tangent law. -/
example : ∀ P ∈ pts, ∀ Q ∈ pts, toMont (add P Q) = madd (toMont P) (toMont Q) := by decide +kernel

/-! ### The Montgomery criterion -/

/-- **The criterion against brute force** over `𝔽₅`: for every curve `(c₄, c₆)`, the criterion of
`Curve.hasMontgomeryModel_mk_iff` holds exactly when some nonsingular Montgomery model has
invariants `(u⁴ c₄, u⁶ c₆)`. -/
example : ∀ c₄ c₆ : ZMod 5, c₄ ^ 3 ≠ c₆ ^ 2 →
    ((∃ x : ZMod 5, x ^ 3 - 27 * c₄ * x - 54 * c₆ = 0 ∧ ∃ r, 3 * x ^ 2 - 27 * c₄ = r * r) ↔
      ∃ A B u : ZMod 5, B ≠ 0 ∧ A ^ 2 ≠ 4 ∧ u ≠ 0 ∧
        (⟨A, B⟩ : MontgomeryModel (ZMod 5)).c₄ = u ^ 4 * c₄ ∧
        (⟨A, B⟩ : MontgomeryModel (ZMod 5)).c₆ = u ^ 6 * c₆) := by
  unfold MontgomeryModel.c₄ MontgomeryModel.c₆; decide +kernel

end ModelTests
