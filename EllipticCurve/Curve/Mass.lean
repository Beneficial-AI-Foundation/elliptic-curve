/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Curve.Fiber
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Rat.Defs
import all EllipticCurve.Curve.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # The mass formula

Over a finite field `𝔽_q` away from 6, the curves weighted by the inverse of the order of their
automorphism group add up to `q` (`Curve.finsum_inv_card_aut`):

  `∑_C 1 / |Aut C| = q`.

It is the orbit–stabiliser theorem for the weighted action of `𝔽_qˣ` on the `q² - q` invariants
(`Curve.Invariants.natCard_eq`): the singular pairs `c₄³ = c₆²` are exactly the `q` pairs
`(t², t³)` (`Curve.Invariants.cuspEquiv`). -/

public section

universe u

open MulAction

namespace Curve

variable {F : Type u} [Field F]

namespace Invariants

/-- The singular pairs `c₄³ = c₆²` are the pairs `(t², t³)`. -/
def cuspEquiv [DecidableEq F] : {p : F × F // p.1 ^ 3 - p.2 ^ 2 = 0} ≃ F where
  toFun p := if p.1.1 = 0 then 0 else p.1.2 / p.1.1
  invFun t := ⟨(t ^ 2, t ^ 3), by ring⟩
  left_inv := by
    rintro ⟨⟨a, b⟩, h⟩
    simp only at h
    by_cases ha : a = 0
    · have hb : b = 0 := by subst ha; simpa using h
      subst ha hb
      simp
    · simp only [ha, ite_false, Subtype.mk.injEq, Prod.mk.injEq]
      constructor
      · field_simp
        linear_combination -h
      · field_simp
        linear_combination -b * h
  right_inv t := by
    by_cases ht : t = 0
    · simp [ht]
    · simp only [pow_eq_zero_iff two_ne_zero, ht, ite_false]
      field_simp

/-- The invariants are the pairs off the cusp. -/
def equivSubtype : Invariants F ≃ {p : F × F // ¬ (p.1 ^ 3 - p.2 ^ 2 = 0)} where
  toFun p := ⟨(p.c₄, p.c₆), p.disc_ne_zero⟩
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- There are `q² - q` invariants over `𝔽_q`. -/
theorem natCard_eq [Finite F] : Nat.card (Invariants F) = Nat.card F ^ 2 - Nat.card F := by
  classical
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card (α := F), Nat.card_congr equivSubtype, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl, Fintype.card_prod, Fintype.card_congr cuspEquiv, sq]

end Invariants

/-- **The mass formula**: over `𝔽_q` away from 6, the curves weighted by `1 / |Aut C|` add up to
`q`. (The proof does not use `NeZero 6`, but only away from 6 does `Curve F` describe the elliptic
curves and `Curve.aut` their automorphism groups.) -/
theorem finsum_inv_card_aut [Finite F] :
    ∑ᶠ C : Curve F, (Nat.card C.aut : ℚ)⁻¹ = Nat.card F := by
  classical
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card (α := F)]
  have : Fintype (Curve F) := Fintype.ofFinite _
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hq1 : (Fintype.card F : ℚ) - 1 ≠ 0 := by
    have : (2 : ℚ) ≤ Fintype.card F := by exact_mod_cast hq
    linarith
  -- each orbit: `|orbit| · |aut| = q - 1`
  have horb : ∀ C : Curve F,
      (Nat.card (orbitRel.Quotient.orbit (G := Fˣ) C) : ℚ) * Nat.card C.aut =
        Fintype.card F - 1 := fun C => by
    induction C using ind with | h p =>
    rw [aut_ofInvariants]
    have e := (stabilizer Fˣ p).card_mul_index
    rw [index_stabilizer, ← Nat.card_coe_set_eq, Nat.card_units,
      Nat.card_eq_fintype_card (α := F)] at e
    rw [show orbitRel.Quotient.orbit (G := Fˣ) (ofInvariants p) = orbit Fˣ p from
      orbitRel.Quotient.orbit_mk p, mul_comm, ← Nat.cast_mul, e, Nat.cast_sub (by omega),
      Nat.cast_one]
  have hsum : ∑ C : Curve F, (Nat.card (orbitRel.Quotient.orbit (G := Fˣ) C) : ℚ) =
      Fintype.card F ^ 2 - Fintype.card F := by
    have hc := Invariants.natCard_eq (F := F)
    rw [Nat.card_eq_fintype_card (α := F)] at hc
    let : Fintype (orbitRel.Quotient Fˣ (Invariants F)) := ‹Fintype (Curve F)›
    rw [Nat.card_congr (selfEquivSigmaOrbits' Fˣ (Invariants F)), Nat.card_sigma] at hc
    rw [show (Fintype.card F : ℚ) ^ 2 - Fintype.card F =
      ((Fintype.card F ^ 2 - Fintype.card F : ℕ) : ℚ) by
        rw [Nat.cast_sub (Nat.le_self_pow two_ne_zero _)]; push_cast; ring, ← hc]
    push_cast
    rfl
  rw [finsum_eq_sum_of_fintype]
  have hC : ∀ C : Curve F, (Nat.card C.aut : ℚ)⁻¹ =
      Nat.card (orbitRel.Quotient.orbit (G := Fˣ) C) / (Fintype.card F - 1) := fun C => by
    have h0 : (Nat.card C.aut : ℚ) ≠ 0 := by
      have : 0 < Nat.card C.aut := Nat.card_pos
      exact_mod_cast this.ne'
    rw [eq_div_iff hq1, ← horb C]
    field_simp
  simp only [hC, ← Finset.sum_div, hsum]
  field_simp

end Curve
