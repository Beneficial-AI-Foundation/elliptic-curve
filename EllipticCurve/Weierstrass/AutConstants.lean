/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.RingTheory.Algebraic.Defs
import EllipticCurve.Field.AwayFromSix
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # Automorphisms of a base-changed curve are defined over the base

Away from 6, a change of variables `C` over an extension `K / F` preserving the base change of an
elliptic curve `W` over `F` has `u¹² = 1` (from `c₄`, `c₆`), and `s`, `r`, `t` rational in `u`;
so when `F` is algebraically closed in `K`, all its coefficients lie in `F`
(`exists_eq_algebraMap_of_smul_baseChange_eq`). -/

public section

universe u v

open Polynomial

namespace WeierstrassCurve

variable {F : Type u} [Field F] [NeZero (6 : F)] (W : WeierstrassCurve F) [W.IsElliptic]
  {K : Type v} [Field K] [Algebra F K]

/-- **Automorphisms over an extension with the same constants are defined over the base.** -/
theorem exists_eq_algebraMap_of_smul_baseChange_eq
    (hconst : ∀ z : K, IsAlgebraic F z → ∃ c : F, z = algebraMap F K c)
    (C : VariableChange K) (hC : C • W.baseChange K = W.baseChange K) :
    ∃ u r s t : F, (C.u : K) = algebraMap F K u ∧ C.r = algebraMap F K r ∧
      C.s = algebraMap F K s ∧ C.t = algebraMap F K t := by
  set f := algebraMap F K
  rw [show W.baseChange K = W.map f from rfl] at hC
  set u' : K := (C.u : K)
  set v : K := ((C.u⁻¹ : Kˣ) : K)
  have huv : u' * v = 1 := by simp [u', v]
  have hv0 : v ≠ 0 := Units.ne_zero _
  have h2 : (2 : K) ≠ 0 := by
    rw [← map_ofNat f 2]; exact (map_ne_zero f).mpr two_ne_zero
  have h3 : (3 : K) ≠ 0 := by
    rw [← map_ofNat f 3]; exact (map_ne_zero f).mpr three_ne_zero
  -- the invariants force `v¹² = 1`
  have hc₄ : v ^ 4 * f W.c₄ = f W.c₄ := by
    have := congrArg WeierstrassCurve.c₄ hC
    simpa [variableChange_c₄, map_c₄, v] using this
  have hc₆ : v ^ 6 * f W.c₆ = f W.c₆ := by
    have := congrArg WeierstrassCurve.c₆ hC
    simpa [variableChange_c₆, map_c₆, v] using this
  have hv12 : v ^ 12 = 1 := by
    by_cases h4 : W.c₄ = 0
    · have h6 : W.c₆ ≠ 0 := by
        intro h6
        have := W.c_relation
        rw [h4, h6] at this
        have h1728 : (1728 : F) ≠ 0 := NeZero.ne _
        exact W.isUnit_Δ.ne_zero ((mul_eq_zero.mp (by simpa using this)).resolve_left h1728)
      have : v ^ 6 = 1 := by
        have hne : f W.c₆ ≠ 0 := (map_ne_zero f).mpr h6
        exact (mul_left_eq_self₀.mp hc₆).resolve_right hne
      rw [show v ^ 12 = (v ^ 6) ^ 2 by ring, this, one_pow]
    · have : v ^ 4 = 1 := by
        have hne : f W.c₄ ≠ 0 := (map_ne_zero f).mpr h4
        exact (mul_left_eq_self₀.mp hc₄).resolve_right hne
      rw [show v ^ 12 = (v ^ 4) ^ 3 by ring, this, one_pow]
  obtain ⟨v₀, hv₀⟩ := hconst v ⟨X ^ 12 - 1, X_pow_sub_C_ne_zero (by norm_num) 1, by simp [hv12]⟩
  have hv₀0 : v₀ ≠ 0 := by rintro rfl; rw [map_zero] at hv₀; exact hv0 hv₀
  have hu : u' = f v₀⁻¹ := by
    rw [map_inv₀, ← hv₀]; exact eq_inv_of_mul_eq_one_left huv
  -- the coefficients
  have ha₁ := congrArg WeierstrassCurve.a₁ hC
  have ha₂ := congrArg WeierstrassCurve.a₂ hC
  have ha₃ := congrArg WeierstrassCurve.a₃ hC
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, map_a₁, map_a₂, map_a₃,
    Units.val_inv_eq_inv_val] at ha₁ ha₂ ha₃
  change (u')⁻¹ * _ = _ at ha₁
  change (u')⁻¹ ^ 2 * _ = _ at ha₂
  change (u')⁻¹ ^ 3 * _ = _ at ha₃
  have hu0 : u' ≠ 0 := Units.ne_zero _
  set s₀ := (W.a₁ * v₀⁻¹ - W.a₁) / 2
  have hs : C.s = f s₀ := by
    simp only [s₀, map_div₀, map_sub, map_mul, map_ofNat, ← hu]
    field_simp at ha₁ ⊢
    linear_combination ha₁
  set r₀ := (v₀⁻¹ ^ 2 * W.a₂ - W.a₂ + s₀ * W.a₁ + s₀ ^ 2) / 3
  have hr : C.r = f r₀ := by
    simp only [r₀, map_div₀, map_sub, map_add, map_mul, map_pow, map_ofNat, ← hu, ← hs]
    field_simp at ha₂ ⊢
    linear_combination ha₂
  set t₀ := (v₀⁻¹ ^ 3 * W.a₃ - W.a₃ - r₀ * W.a₁) / 2
  have ht : C.t = f t₀ := by
    simp only [t₀, map_div₀, map_sub, map_mul, map_pow, map_ofNat, ← hu, ← hr]
    field_simp at ha₃ ⊢
    linear_combination ha₃
  exact ⟨v₀⁻¹, r₀, s₀, t₀, hu, hr, hs, ht⟩

end WeierstrassCurve
