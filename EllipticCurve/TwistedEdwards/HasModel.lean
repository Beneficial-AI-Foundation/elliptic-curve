/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Montgomery.HasModel
public import EllipticCurve.TwistedEdwards.Group
public import Mathlib.Algebra.Group.Even
import EllipticCurve.Curve.Lemmas
import EllipticCurve.Montgomery.Lemmas
import EllipticCurve.TwistedEdwards.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Which curves have a complete twisted Edwards model

A curve away from 6 has a complete twisted Edwards model `a x² + y² = 1 + d x² y²` (`a` a nonzero
square, `d` not a square) if and only if its short model `y² = x³ - 27 c₄ x - 54 c₆` has a point
`(x, 0)` of order 2 with `3 x² - 27 c₄ = s²`, such that `3 x + 2 s` is a nonzero square and
`3 x - 2 s` is not a square (`Curve.hasCompleteEdwardsModel_mk_iff`). Both directions are
explicit:

* from `E` with `E.c₄ = u⁴ c₄`, `E.c₆ = u⁶ c₆` (as for Montgomery models): `x = 24 u⁻² (a + d)`,
  `s = 36 u⁻² (a - d)`, so that `3 x + 2 s = (12 u⁻¹)² a` and `3 x - 2 s = (12 u⁻¹)² d`;
* from `x`, `s`: the model `a = (3 x + 2 s) / 144`, `d = (3 x - 2 s) / 144`, whose invariants are
  exactly `(c₄, c₆)`.

With `x` and `s` as in `Curve.hasMontgomeryModel_mk_iff`, the Edwards model is that of the
Montgomery model `A = 3 x / s`, `B = s` (Bernstein–Birkner–Joye–Lange–Peters: `a = (A + 2) / B`,
`d = (A - 2) / B`); in particular a curve with a complete Edwards model has a Montgomery
model; conversely, a Montgomery model with `(A + 2) / B` a nonzero square and `(A - 2) / B` not a
square comes from a complete twisted Edwards model
(`MontgomeryModel.exists_isComplete_toMontgomery_eq`, `hasCompleteEdwardsModel_toCurve`). -/

public section

universe u

namespace Curve

variable {F : Type u} [Field F] [NeZero (6 : F)]

/-- The curve `C` has a complete twisted Edwards model. -/
def HasCompleteEdwardsModel (C : Curve F) : Prop :=
  ∃ (E : TwistedEdwardsModel F) (_ : E.IsComplete), E.toCurve = C

theorem hasCompleteEdwardsModel_iff {C : Curve F} :
    C.HasCompleteEdwardsModel ↔
      ∃ (E : TwistedEdwardsModel F) (_ : E.IsComplete), E.toCurve = C := by
  unfold HasCompleteEdwardsModel; rfl

/-- **Complete twisted Edwards models of a curve.** -/
theorem hasCompleteEdwardsModel_mk_iff {c₄ c₆ : F} {h : c₄ ^ 3 - c₆ ^ 2 ≠ 0} :
    (mk c₄ c₆ h).HasCompleteEdwardsModel ↔
      ∃ x s : F, x ^ 3 - 27 * c₄ * x - 54 * c₆ = 0 ∧ s * s = 3 * x ^ 2 - 27 * c₄ ∧
        IsSquare (3 * x + 2 * s) ∧ 3 * x + 2 * s ≠ 0 ∧ ¬ IsSquare (3 * x - 2 * s) := by
  have h12 : (12 : F) ≠ 0 := by
    rw [show (12 : F) = 2 ^ 2 * 3 by norm_num]
    exact mul_ne_zero (pow_ne_zero _ (NeZero.ne _)) (NeZero.ne _)
  have h144 : (144 : F) = 12 ^ 2 := by norm_num
  have h144' : (144 : F) ≠ 0 := by rw [h144]; exact pow_ne_zero _ h12
  constructor
  · rw [hasCompleteEdwardsModel_iff]
    rintro ⟨E, hE, hC⟩
    rw [E.toCurve_eq_mk, mk_eq_mk_iff] at hC
    obtain ⟨u, h₄, h₆⟩ := hC
    have hu : (u : F) ≠ 0 := u.ne_zero
    have e₄ : c₄ = (u : F)⁻¹ ^ 4 * E.c₄ := by rw [h₄]; field_simp
    have e₆ : c₆ = (u : F)⁻¹ ^ 6 * E.c₆ := by rw [h₆]; field_simp
    have ha : 3 * ((u : F)⁻¹ ^ 2 * (24 * (E.a + E.d))) + 2 * ((u : F)⁻¹ ^ 2 * (36 * (E.a - E.d)))
        = (12 * (u : F)⁻¹) ^ 2 * E.a := by ring
    have hd : 3 * ((u : F)⁻¹ ^ 2 * (24 * (E.a + E.d))) - 2 * ((u : F)⁻¹ ^ 2 * (36 * (E.a - E.d)))
        = (12 * (u : F)⁻¹) ^ 2 * E.d := by ring
    refine ⟨(u : F)⁻¹ ^ 2 * (24 * (E.a + E.d)), (u : F)⁻¹ ^ 2 * (36 * (E.a - E.d)), ?_, ?_, ?_,
      ?_, ?_⟩
    · rw [e₄, e₆]
      simp only [TwistedEdwardsModel.c₄, TwistedEdwardsModel.c₆]
      ring
    · rw [e₄]
      simp only [TwistedEdwardsModel.c₄]
      ring
    · rw [ha]
      obtain ⟨r, hr⟩ := TwistedEdwardsModel.IsComplete.isSquare_a (E := E)
      exact ⟨12 * (u : F)⁻¹ * r, by rw [hr]; ring⟩
    · rw [ha]
      exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero h12 (inv_ne_zero hu)))
        TwistedEdwardsModel.IsComplete.a_ne_zero
    · rw [hd]
      rintro ⟨t, ht⟩
      apply TwistedEdwardsModel.IsComplete.not_isSquare_d (E := E)
      refine ⟨t * u / 12, ?_⟩
      calc E.d = (12 * (u : F)⁻¹) ^ 2 * E.d * u ^ 2 / 144 := by field_simp; ring
        _ = t * u / 12 * (t * u / 12) := by rw [ht]; field_simp; ring
  · rintro ⟨x, s, hx, hs, ⟨r, hr⟩, ha0, hd⟩
    let E : TwistedEdwardsModel F := ⟨(3 * x + 2 * s) / 144, (3 * x - 2 * s) / 144⟩
    have hE : E.IsComplete :=
      { two_ne_zero := NeZero.ne _
        isSquare_a := ⟨r / 12, by simp only [E]; rw [hr, h144]; field_simp⟩
        a_ne_zero := by
          simp only [E]
          exact div_ne_zero ha0 (by rw [h144]; exact pow_ne_zero _ h12)
        not_isSquare_d := by
          rintro ⟨t, ht⟩
          apply hd
          refine ⟨12 * t, ?_⟩
          simp only [E] at ht
          rw [div_eq_iff (by rw [h144]; exact pow_ne_zero _ h12)] at ht
          rw [ht, h144]
          ring }
    have hc₄ : E.c₄ = c₄ := by
      simp only [E, TwistedEdwardsModel.c₄]
      field_simp
      linear_combination (-768 : F) * hs
    have hc₆ : E.c₆ = c₆ := by
      simp only [E, TwistedEdwardsModel.c₆]
      field_simp
      linear_combination (55296 * x : F) * hs + 55296 * hx
    refine hasCompleteEdwardsModel_iff.mpr ⟨E, hE, ?_⟩
    rw [E.toCurve_eq_mk]
    exact mk_congr hc₄ hc₆

/-- A curve with a complete twisted Edwards model has a Montgomery model. -/
theorem HasCompleteEdwardsModel.hasMontgomeryModel {C : Curve F}
    (h : C.HasCompleteEdwardsModel) : C.HasMontgomeryModel := by
  obtain ⟨E, hE, rfl⟩ := h
  rw [← E.toCurve_toMontgomery]
  exact E.toMontgomery.hasMontgomeryModel_toCurve

end Curve

namespace MontgomeryModel

variable {F : Type u} [Field F] (M : MontgomeryModel F) [M.IsNonsingular]

/-- **From Montgomery to complete twisted Edwards** (Bernstein–Birkner–Joye–Lange–Peters): if
`(A + 2) / B` is a nonzero square and `(A - 2) / B` is not a square, then `M` is the Montgomery
model of the complete twisted Edwards model `a = (A + 2) / B`, `d = (A - 2) / B`. -/
theorem exists_isComplete_toMontgomery_eq (ha : IsSquare ((M.A + 2) / M.B)) (ha0 : M.A + 2 ≠ 0)
    (hd : ¬ IsSquare ((M.A - 2) / M.B)) :
    ∃ (E : TwistedEdwardsModel F) (_ : E.IsComplete), E.toMontgomery = M := by
  have hB : M.B ≠ 0 := IsNonsingular.B_ne_zero
  have h2 : (2 : F) ≠ 0 := IsNonsingular.two_ne_zero (M := M)
  have h4 : (4 : F) ≠ 0 := by rw [show (4 : F) = 2 ^ 2 by norm_num]; exact pow_ne_zero _ h2
  let E : TwistedEdwardsModel F := ⟨(M.A + 2) / M.B, (M.A - 2) / M.B⟩
  have hE : E.IsComplete := ⟨h2, ha, div_ne_zero ha0 hB, hd⟩
  refine ⟨E, hE, ?_⟩
  have hsub : E.a - E.d = 4 / M.B := by simp only [E]; field_simp; ring
  have hadd : E.a + E.d = 2 * M.A / M.B := by simp only [E]; field_simp; ring
  obtain ⟨A, B⟩ := M
  rw [TwistedEdwardsModel.toMontgomery_def, hsub, hadd]
  simp only at hB ⊢
  congr 1
  · field_simp
    ring
  · field_simp

/-- The curve of a Montgomery model with `(A + 2) / B` a nonzero square and `(A - 2) / B` not a
square has a complete twisted Edwards model. -/
theorem hasCompleteEdwardsModel_toCurve [NeZero (6 : F)] (ha : IsSquare ((M.A + 2) / M.B))
    (ha0 : M.A + 2 ≠ 0) (hd : ¬ IsSquare ((M.A - 2) / M.B)) :
    M.toCurve.HasCompleteEdwardsModel := by
  obtain ⟨E, hE, hEM⟩ := M.exists_isComplete_toMontgomery_eq ha ha0 hd
  refine Curve.hasCompleteEdwardsModel_iff.mpr ⟨E, hE, ?_⟩
  rw [← E.toCurve_toMontgomery, MontgomeryModel.toCurve_eq_mk, MontgomeryModel.toCurve_eq_mk]
  exact Curve.mk_congr (by rw [hEM]) (by rw [hEM])

end MontgomeryModel
