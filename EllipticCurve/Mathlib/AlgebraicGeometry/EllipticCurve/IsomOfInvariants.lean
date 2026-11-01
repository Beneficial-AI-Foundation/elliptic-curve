/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-! # Isomorphism of Weierstrass curves away from 6

Over a commutative ring `R` in which `2` and `3` are invertible, two Weierstrass curves are
related by a change of variables if and only if their invariants `c₄`, `c₆` differ by the
weights `u⁴`, `u⁶` of a unit `u` (`WeierstrassCurve.exists_variableChange_iff`). No ellipticity
and no separable closure are needed: the change of variables is explicit, a reduction to short
normal form (`WeierstrassCurve.toShortNF`, which does not scale) followed by the scaling
`(X, Y) ↦ (u⁻² X, u⁻³ Y)` between two short normal forms (`smul_eq_of_isShortNF`).

Mathlib's `WeierstrassCurve.exists_variableChange_of_j_eq` (over a separably closed field) is the
case where the unit `u` is found by extracting roots.

**Rigidity** (`WeierstrassCurve.variableChange_rst_eq_zero_of_isShortNF`): a change of variables
between two short normal forms is a pure scaling `C = ⟨C.u, 0, 0, 0⟩`, i.e. `X = u² X'`,
`Y = u³ Y'` in Mathlib's convention.

Staged for Mathlib (`Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms` or a new file). -/

public section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

section ShortNF

variable [Invertible (2 : R)] [Invertible (3 : R)]

/-- The change of variables to short normal form does not scale. -/
theorem toShortNF_u : W.toShortNF.u = 1 := by
  simp [toShortNF, VariableChange.mul_def, toCharNeTwoNF]

/-- The reduction to short normal form preserves `c₄`. -/
theorem c₄_toShortNF : (W.toShortNF • W).c₄ = W.c₄ := by
  rw [variableChange_c₄, toShortNF_u, inv_one, Units.val_one, one_pow, one_mul]

/-- The reduction to short normal form preserves `c₆`. -/
theorem c₆_toShortNF : (W.toShortNF • W).c₆ = W.c₆ := by
  rw [variableChange_c₆, toShortNF_u, inv_one, Units.val_one, one_pow, one_mul]

end ShortNF

/-- Two short normal forms whose invariants differ by the weights `u⁴`, `u⁶` are related by the
scaling `⟨u⁻¹, 0, 0, 0⟩`. -/
theorem smul_eq_of_isShortNF [Invertible (2 : R)] [Invertible (3 : R)]
    {S S' : WeierstrassCurve R} [S.IsShortNF] [S'.IsShortNF] (u : Rˣ)
    (h₄ : S'.c₄ = u ^ 4 * S.c₄) (h₆ : S'.c₆ = u ^ 6 * S.c₆) :
    (⟨u⁻¹, 0, 0, 0⟩ : VariableChange R) • S = S' := by
  rw [c₄_of_isShortNF, c₄_of_isShortNF] at h₄
  rw [c₆_of_isShortNF, c₆_of_isShortNF] at h₆
  have h2 : IsUnit (2 : R) := isUnit_of_invertible _
  have h3 : IsUnit (3 : R) := isUnit_of_invertible _
  have h₄' : S'.a₄ = u ^ 4 * S.a₄ :=
    ((h2.pow 4).mul h3).mul_left_cancel (by linear_combination (-1 : R) * h₄)
  have h₆' : S'.a₆ = u ^ 6 * S.a₆ :=
    ((h2.pow 5).mul (h3.pow 3)).mul_left_cancel (by linear_combination (-1 : R) * h₆)
  ext <;> simp [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, h₄', h₆']

/-- **Classification away from 6.** Over a ring in which `2` and `3` are invertible, two
Weierstrass curves are related by a change of variables if and only if their invariants
`(c₄, c₆)` differ by the weights `(u⁴, u⁶)` of a unit `u`. -/
theorem exists_variableChange_iff [Invertible (2 : R)] [Invertible (3 : R)]
    {W W' : WeierstrassCurve R} :
    (∃ C : VariableChange R, C • W = W') ↔
      ∃ u : Rˣ, W'.c₄ = u ^ 4 * W.c₄ ∧ W'.c₆ = u ^ 6 * W.c₆ := by
  constructor
  · rintro ⟨C, rfl⟩
    exact ⟨C.u⁻¹, variableChange_c₄ .., variableChange_c₆ ..⟩
  · rintro ⟨u, h₄, h₆⟩
    have hS := smul_eq_of_isShortNF (S := W.toShortNF • W) (S' := W'.toShortNF • W') u
      (by rw [c₄_toShortNF, c₄_toShortNF, h₄]) (by rw [c₆_toShortNF, c₆_toShortNF, h₆])
    refine ⟨W'.toShortNF⁻¹ * (⟨u⁻¹, 0, 0, 0⟩ * W.toShortNF), ?_⟩
    rw [mul_smul, mul_smul, hS, ← mul_smul, inv_mul_cancel, one_smul]

/-- **Rigidity of short normal forms**: a change of variables between two short normal forms is a
pure scaling, `r = s = t = 0` (so `C = ⟨C.u, 0, 0, 0⟩`). -/
theorem variableChange_rst_eq_zero_of_isShortNF [Invertible (2 : R)] [Invertible (3 : R)]
    {S : WeierstrassCurve R} [S.IsShortNF] {C : VariableChange R} [(C • S).IsShortNF] :
    C.r = 0 ∧ C.s = 0 ∧ C.t = 0 := by
  have h1 : (C • S).a₁ = 0 := IsShortNF.a₁
  have h2 : (C • S).a₂ = 0 := IsShortNF.a₂
  have h3 : (C • S).a₃ = 0 := IsShortNF.a₃
  rw [variableChange_a₁, a₁_of_isShortNF] at h1
  rw [variableChange_a₂, a₁_of_isShortNF, a₂_of_isShortNF] at h2
  rw [variableChange_a₃, a₁_of_isShortNF, a₃_of_isShortNF] at h3
  have hu : ∀ n : ℕ, IsUnit ((C.u⁻¹ : Rˣ) ^ n : R) := fun n => (Units.isUnit _).pow n
  have h2u : IsUnit (2 : R) := isUnit_of_invertible _
  have h3u : IsUnit (3 : R) := isUnit_of_invertible _
  have hs : C.s = 0 := by
    have : ((C.u⁻¹ : Rˣ) : R) * 2 * C.s = 0 := by linear_combination h1
    exact ((Units.isUnit _).mul h2u).mul_right_eq_zero.mp this
  have ht : C.t = 0 := by
    have : ((C.u⁻¹ : Rˣ) : R) ^ 3 * 2 * C.t = 0 := by linear_combination h3
    exact ((hu 3).mul h2u).mul_right_eq_zero.mp this
  have hr : C.r = 0 := by
    have : ((C.u⁻¹ : Rˣ) : R) ^ 2 * 3 * C.r = 0 := by rw [hs] at h2; linear_combination h2
    exact ((hu 2).mul h3u).mul_right_eq_zero.mp this
  exact ⟨hr, hs, ht⟩

end WeierstrassCurve
