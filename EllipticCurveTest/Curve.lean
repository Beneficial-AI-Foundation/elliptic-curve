/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime
-- The tests evaluate their own definitions by `decide`, so they are exposed.
/-! # Tests: curves over small prime fields

The counting theorem `Curve.natCard_eq` is checked against an independent brute-force count of
orbit representatives by kernel `decide` (inverse-free predicates on `ZMod p`), and equality of
curves of models is decided through `Curve.mk_eq_mk_iff'`. -/

@[expose] public section

/-! ### Orbit representatives, by brute force -/

/-- `x ≤ y` lexicographically, comparing `val`s. -/
def lexLE {p : ℕ} (x y : ZMod p × ZMod p) : Prop :=
  x.1.val < y.1.val ∨ (x.1.val = y.1.val ∧ x.2.val ≤ y.2.val)

instance {p : ℕ} (x y : ZMod p × ZMod p) : Decidable (lexLE x y) := by
  unfold lexLE; infer_instance

/-- `(c₄, c₆)` is nondegenerate and lexicographically least in its orbit under
`(c₄, c₆) ↦ (u⁴ c₄, u⁶ c₆)`: one representative per curve. -/
def IsRep (p : ℕ) (x : ZMod p × ZMod p) : Prop :=
  x.1 ^ 3 ≠ x.2 ^ 2 ∧ ∀ u : ZMod p, u ≠ 0 → lexLE x (u ^ 4 * x.1, u ^ 6 * x.2)

instance (p : ℕ) [NeZero p] (x : ZMod p × ZMod p) : Decidable (IsRep p x) := by
  unfold IsRep; infer_instance

/-! ### The number of curves -/

instance : NeZero (6 : ZMod 5) := ⟨by decide⟩
instance : NeZero (6 : ZMod 7) := ⟨by decide⟩
instance : NeZero (6 : ZMod 11) := ⟨by decide⟩
instance : NeZero (6 : ZMod 13) := ⟨by decide⟩
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

example : Nat.card (Curve (ZMod 5)) = 12 := by rw [Curve.natCard_eq, Nat.card_zmod]; norm_num
example : Nat.card (Curve (ZMod 7)) = 18 := by rw [Curve.natCard_eq, Nat.card_zmod]; norm_num
example : Nat.card (Curve (ZMod 11)) = 22 := by rw [Curve.natCard_eq, Nat.card_zmod]; norm_num
example : Nat.card (Curve (ZMod 13)) = 32 := by rw [Curve.natCard_eq, Nat.card_zmod]; norm_num

example : (Finset.univ.filter (IsRep 5)).card = 12 := by decide
example : (Finset.univ.filter (IsRep 7)).card = 18 := by decide
example : (Finset.univ.filter (IsRep 11)).card = 22 := by decide
example : (Finset.univ.filter (IsRep 13)).card = 32 := by decide

/-! ### Fibres of `j` -/

example : Nat.card {C : Curve (ZMod 13) // C.j = 0} = 6 := by
  rw [Curve.card_fiber, Nat.card_zmod, Curve.twistExponent_zero]; norm_num

example : Nat.card {C : Curve (ZMod 7) // C.j = 1728} = 2 := by
  rw [Curve.card_fiber, Nat.card_zmod, Curve.twistExponent_1728]; norm_num

/-! ### Montgomery models -/

/-- `B v² = u³ + 3 u² + u` over `𝔽₁₃`. -/
def M13 : MontgomeryModel (ZMod 13) := ⟨3, 1⟩

instance : M13.IsNonsingular := ⟨by decide, by decide, by decide⟩

instance : (M13.twist 2).IsNonsingular := M13.isNonsingular_twist (by decide)

instance : (M13.twist 4).IsNonsingular := M13.isNonsingular_twist (by decide)

/-- `2` is not a square mod 13, so the twist by `2` is a different curve. -/
example : (M13.twist 2).toCurve ≠ M13.toCurve := by
  rw [MontgomeryModel.toCurve_eq_mk, MontgomeryModel.toCurve_eq_mk, Ne, Curve.mk_eq_mk_iff',
    MontgomeryModel.twist_c₄, MontgomeryModel.twist_c₆]
  decide

/-- The twist by `4 = 2²` is the same curve. -/
example : (M13.twist 4).toCurve = M13.toCurve :=
  MontgomeryModel.toCurve_eq_of_B_eq_mul_sq M13 (M13.twist 4) (MontgomeryModel.twist_A _ _)
    (c := 2) (by decide) (by rw [MontgomeryModel.twist_B]; decide)

/-! ### Which curves have a Montgomery model -/

/-- No curve with `j = 0` over `𝔽₇` has a Montgomery model: `3` is not a square mod 7, while a
Montgomery model with `j = 0` has `A² = 3`. -/
example : ¬ (Curve.mk (0 : ZMod 7) 1 (by decide)).HasMontgomeryModel := by
  rw [Curve.hasMontgomeryModel_mk_iff]
  unfold IsSquare
  decide

/-- The curve of `M13` has a Montgomery model, found by the criterion. -/
example : (Curve.mk (M13.c₄) M13.c₆ (by decide)).HasMontgomeryModel := by
  rw [Curve.hasMontgomeryModel_mk_iff]
  unfold IsSquare
  decide
