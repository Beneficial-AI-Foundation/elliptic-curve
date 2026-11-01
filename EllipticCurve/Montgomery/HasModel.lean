/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Montgomery.Defs
public import Mathlib.Algebra.Group.Even
import EllipticCurve.Montgomery.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Which curves have a Montgomery model

A curve away from 6 has a Montgomery model `B v² = u³ + A u² + u` if and only if its short model
`y² = x³ - 27 c₄ x - 54 c₆` has a rational point `(x, 0)` of order 2 at which
`3 x² - 27 c₄` is a square (`Curve.hasMontgomeryModel_mk_iff`; Okeya–Kurumatani–Sakurai,
*Elliptic curves with the Montgomery-form and their cryptographic applications*, PKC 2000,
Proposition 1). Both directions are explicit:

* from `M` with `M.c₄ = u⁴ c₄`, `M.c₆ = u⁶ c₆`: the point `x = 12 u⁻² A B` (the image of the
  2-torsion point `(0, 0)` of `M`), with `3 x² - 27 c₄ = (36 u⁻² B)²`;
* from `x` with `3 x² - 27 c₄ = s²`: the model `A = 3 x / s`, `B = s`, whose invariants are
  `6⁴ c₄`, `6⁶ c₆`.

In particular the criterion depends only on the curve: it is unchanged by `x ↦ u² x`. -/

public section

universe u

namespace Curve

variable {F : Type u} [Field F] [NeZero (6 : F)]

/-- The curve `C` has a (nonsingular) Montgomery model. -/
def HasMontgomeryModel (C : Curve F) : Prop :=
  ∃ (M : MontgomeryModel F) (_ : M.IsNonsingular), M.toCurve = C

theorem hasMontgomeryModel_iff {C : Curve F} :
    C.HasMontgomeryModel ↔ ∃ (M : MontgomeryModel F) (_ : M.IsNonsingular), M.toCurve = C := by
  unfold HasMontgomeryModel; rfl

/-- The curve of a Montgomery model has a Montgomery model. -/
theorem _root_.MontgomeryModel.hasMontgomeryModel_toCurve (M : MontgomeryModel F)
    [M.IsNonsingular] :
    M.toCurve.HasMontgomeryModel :=
  hasMontgomeryModel_iff.mpr ⟨M, inferInstance, rfl⟩

/-- **Montgomery models of a curve.** The curve with invariants `(c₄, c₆)` has a Montgomery model
if and only if `x³ - 27 c₄ x - 54 c₆` has a root `x` at which `3 x² - 27 c₄` is a square. -/
theorem hasMontgomeryModel_mk_iff {c₄ c₆ : F} {h : c₄ ^ 3 - c₆ ^ 2 ≠ 0} :
    (mk c₄ c₆ h).HasMontgomeryModel ↔
      ∃ x : F, x ^ 3 - 27 * c₄ * x - 54 * c₆ = 0 ∧ IsSquare (3 * x ^ 2 - 27 * c₄) := by
  rw [hasMontgomeryModel_iff]
  constructor
  · rintro ⟨M, hM, hC⟩
    rw [M.toCurve_eq_mk, mk_eq_mk_iff] at hC
    obtain ⟨u, h₄, h₆⟩ := hC
    have hu : (u : F) ≠ 0 := u.ne_zero
    have e₄ : c₄ = (u : F)⁻¹ ^ 4 * M.c₄ := by rw [h₄]; field_simp
    have e₆ : c₆ = (u : F)⁻¹ ^ 6 * M.c₆ := by rw [h₆]; field_simp
    refine ⟨(u : F)⁻¹ ^ 2 * (12 * M.A * M.B), ?_, 36 * (u : F)⁻¹ ^ 2 * M.B, ?_⟩
    · rw [e₄, e₆]
      simp only [MontgomeryModel.c₄, MontgomeryModel.c₆]
      ring
    · rw [e₄]
      simp only [MontgomeryModel.c₄]
      ring
  · rintro ⟨x, hx, s, hs⟩
    have h2 : (2 : F) ≠ 0 := NeZero.ne _
    have h3 : (3 : F) ≠ 0 := NeZero.ne _
    have hs0 : s ≠ 0 := by
      rintro rfl
      apply h
      -- `x` is a common root of `x³ - 27 c₄ x - 54 c₆` and its derivative `3 x² - 27 c₄`
      have hx2 : x ^ 2 = 9 * c₄ := mul_left_cancel₀ h3 (by linear_combination hs)
      have hcx : c₄ * x = -3 * c₆ := by
        have e : (2 * 3 ^ 2 : F) * (c₄ * x + 3 * c₆) = 0 := by linear_combination -hx + x * hx2
        linear_combination (mul_eq_zero.mp e).resolve_left
          (mul_ne_zero h2 (pow_ne_zero 2 h3))
      -- so `c₄² x² = 9 c₆²` and `x² = 9 c₄`: `c₄³ = c₆²`
      have e : (3 : F) ^ 2 * (c₄ ^ 3 - c₆ ^ 2) = 0 := by
        linear_combination (-c₄ ^ 2) * hx2 + (c₄ * x - 3 * c₆) * hcx
      exact (mul_eq_zero.mp e).resolve_left (pow_ne_zero 2 h3)
    let M : MontgomeryModel F := ⟨3 * x / s, s⟩
    have hc₄ : M.c₄ = 6 ^ 4 * c₄ := by
      simp only [M, MontgomeryModel.c₄]
      field_simp
      linear_combination 48 * hs
    have hc₆ : M.c₆ = 6 ^ 6 * c₆ := by
      simp only [M, MontgomeryModel.c₆]
      field_simp
      linear_combination (-864 * x : F) * hs + 864 * hx
    have hA : M.A ^ 2 ≠ 4 := by
      intro hA
      have e := M.c₄_cube_sub_c₆_sq
      rw [hc₄, hc₆, hA, sub_self, mul_zero] at e
      apply h
      have : (6 : F) ^ 12 * (c₄ ^ 3 - c₆ ^ 2) = 0 := by linear_combination e
      exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ (NeZero.ne _))
    have hM : M.IsNonsingular := ⟨h2, hs0, hA⟩
    refine ⟨M, hM, ?_⟩
    rw [M.toCurve_eq_mk]
    exact mk_eq_mk_of 6 (NeZero.ne _) hc₄ hc₆

end Curve
