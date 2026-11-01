/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Weierstrass.Coordinates
public import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.Adjoin.Polynomial.Basic

/-! # The place at infinity of a Weierstrass curve

A place of `W.FunctionField` where `x` has a pole is unique, and rational. -/

public section

universe u v

open Polynomial

section Valuation

variable {F : Type u} {K : Type v} [Field F] [Field K] [Algebra F K] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

/-- If the constants are units for `v` and `v x > 1`, the leading term of a polynomial in `x`
dominates. -/
theorem Valuation.map_aeval_eq_pow_natDegree (hc : ∀ c : F, c ≠ 0 → v (algebraMap F K c) = 1)
    {x : K} (hx : 1 < v x) {p : F[X]} (hp : p ≠ 0) : v (aeval x p) = v x ^ p.natDegree := by
  induction h : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
  have hlead : v (aeval x (C p.leadingCoeff * X ^ p.natDegree)) = v x ^ n := by
    rw [map_mul, map_pow, aeval_C, aeval_X, map_mul, map_pow,
      hc _ (leadingCoeff_ne_zero.mpr hp), one_mul, h]
  rw [← eraseLead_add_C_mul_X_pow p, map_add]
  by_cases he : p.eraseLead = 0
  · rw [he, map_zero, zero_add, hlead]
  rw [Valuation.map_add_eq_of_lt_right, hlead]
  rw [hlead]
  have hlt : p.eraseLead.natDegree < n :=
    h ▸ (eraseLead_natDegree_lt_or_eraseLead_eq_zero p).resolve_right he
  rw [ih _ hlt he rfl]
  exact pow_lt_pow_right₀ hx hlt

end Valuation

namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] {W : WeierstrassCurve.Affine F}

open scoped Classical in
/-- The norm degree of `p + q y`, as a natural number. -/
theorem natDegree_norm_smul_basis {p q : F[X]} (h : p ≠ 0 ∨ q ≠ 0) :
    (Algebra.norm F[X] (p • (1 : W.CoordinateRing) + q • CoordinateRing.mk W X)).natDegree =
      if q = 0 then 2 * p.natDegree else if p = 0 then 2 * q.natDegree + 3 else
        max (2 * p.natDegree) (2 * q.natDegree + 3) := by
  apply natDegree_eq_of_degree_eq_some
  rw [CoordinateRing.degree_norm_smul_basis]
  split_ifs with hq hp
  · subst hq
    have hp : p ≠ 0 := h.resolve_right (not_not.mpr rfl)
    rw [degree_zero, degree_eq_natDegree hp]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    norm_cast
  · subst hp
    rw [degree_zero, degree_eq_natDegree hq]
    simp only [nsmul_eq_mul, Nat.cast_ofNat, WithBot.mul_bot (two_ne_zero), max_bot_left]
    norm_cast
  · rw [degree_eq_natDegree hp, degree_eq_natDegree hq]
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    norm_cast

/-! ### Valuations with a pole of `x` -/

section Pole

variable (O : ValuationSubring W.FunctionField) (hO : ∀ c : F, algebraMap F _ c ∈ O)
  (hx : W.fieldX ∉ O)
include hO

/-- Nonzero constants are units for the valuation of a place. -/
theorem valuation_algebraMap_eq_one {c : F} (hc : c ≠ 0) :
    O.valuation (algebraMap F W.FunctionField c) = 1 := by
  have h1 := (O.valuation_le_one_iff _).mpr (hO c)
  have h2 := (O.valuation_le_one_iff _).mpr (hO c⁻¹)
  have h0 : O.valuation (algebraMap F W.FunctionField c) ≠ 0 := by
    rw [Ne, Valuation.zero_iff, map_eq_zero_iff _ (algebraMap F _).injective]
    exact hc
  rw [map_inv₀, map_inv₀, inv_le_one₀ (zero_lt_iff.mpr h0)] at h2
  exact le_antisymm h1 h2

include hx

omit hO in
/-- At a pole of `x`, `v(x) > 1`. -/
theorem one_lt_valuation_fieldX : 1 < O.valuation W.fieldX := by
  rw [← not_le, O.valuation_le_one_iff]
  exact hx

/-- The leading term of a polynomial in `x` dominates at a pole of `x`. -/
theorem valuation_aeval_fieldX {p : F[X]} (hp : p ≠ 0) :
    O.valuation (aeval W.fieldX p) = O.valuation W.fieldX ^ p.natDegree :=
  O.valuation.map_aeval_eq_pow_natDegree (fun _ hc => valuation_algebraMap_eq_one O hO hc)
    (one_lt_valuation_fieldX O hx) hp

/-- At a pole of `x`, `v(y)² = v(x)³`. -/
theorem valuation_fieldY_sq :
    O.valuation W.fieldY ^ 2 = O.valuation W.fieldX ^ 3 := by
  set v := O.valuation
  have hx1 := one_lt_valuation_fieldX O hx
  have hc : ∀ c : F, v (algebraMap F _ c) ≤ 1 := fun c => (O.valuation_le_one_iff _).mpr (hO c)
  -- the right-hand side
  have hr : v (W.fieldX ^ 3 + algebraMap F _ W.a₂ * W.fieldX ^ 2 + algebraMap F _ W.a₄ * W.fieldX +
      algebraMap F _ W.a₆) = v W.fieldX ^ 3 := by
    have h := valuation_aeval_fieldX O hO hx (p := C 1 * X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X +
      C W.a₆) (by rw [← degree_ne_bot, degree_cubic one_ne_zero]; decide)
    rw [natDegree_cubic one_ne_zero] at h
    simpa using h
  -- the linear coefficient of `y`
  have hL : v (algebraMap F _ W.a₁ * W.fieldX + algebraMap F _ W.a₃) ≤ v W.fieldX := by
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · rw [map_mul]; exact mul_le_of_le_one_left' (hc _)
    · exact (hc _).trans hx1.le
  have hx0 : 0 < v W.fieldX := zero_lt_one.trans hx1
  have hxx : 0 < v W.fieldX * v W.fieldX := mul_pos hx0 hx0
  have e := W.fieldY_equation
  rw [← hr, ← e]
  have hyx : v W.fieldX < v W.fieldY := by
    by_contra! hyx
    have : v (W.fieldY ^ 2 + algebraMap F _ W.a₁ * W.fieldX * W.fieldY +
        algebraMap F _ W.a₃ * W.fieldY) < v W.fieldX ^ 3 := by
      rw [show W.fieldY ^ 2 + algebraMap F _ W.a₁ * W.fieldX * W.fieldY +
        algebraMap F _ W.a₃ * W.fieldY = W.fieldY * W.fieldY +
          (algebraMap F _ W.a₁ * W.fieldX + algebraMap F _ W.a₃) * W.fieldY by ring]
      refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ ?_)
      · rw [map_mul, pow_succ, pow_two]
        exact (mul_le_mul' hyx hyx).trans_lt (by simpa using mul_lt_mul_of_pos_left hx1 hxx)
      · rw [map_mul, pow_succ, pow_two]
        exact (mul_le_mul' hL hyx).trans_lt (by simpa using mul_lt_mul_of_pos_left hx1 hxx)
    rw [e, hr] at this
    exact lt_irrefl _ this
  rw [show W.fieldY ^ 2 + algebraMap F _ W.a₁ * W.fieldX * W.fieldY +
    algebraMap F _ W.a₃ * W.fieldY = (algebraMap F _ W.a₁ * W.fieldX + algebraMap F _ W.a₃) *
      W.fieldY + W.fieldY ^ 2 by ring]
  rw [Valuation.map_add_eq_of_lt_right, map_pow]
  rw [map_mul, map_pow, pow_two]
  exact mul_lt_mul_of_pos_right (hL.trans_lt hyx) (hx0.trans hyx)

/-- **The valuation at a pole of `x`**: `v(p(x) + q(x) y)² = v(x) ^ deg N(p + q y)`. -/
theorem valuation_sq_smul_basis {p q : F[X]} (h : p ≠ 0 ∨ q ≠ 0) :
    O.valuation (aeval W.fieldX p + aeval W.fieldX q * W.fieldY) ^ 2 =
      O.valuation W.fieldX ^
        (Algebra.norm F[X] (p • (1 : W.CoordinateRing) + q • CoordinateRing.mk W X)).natDegree := by
  set v := O.valuation
  have hx1 := one_lt_valuation_fieldX O hx
  have hy := valuation_fieldY_sq O hO hx
  have hP : p ≠ 0 → v (aeval W.fieldX p) ^ 2 = v W.fieldX ^ (2 * p.natDegree) := fun hp => by
    rw [valuation_aeval_fieldX O hO hx hp, ← pow_mul, mul_comm]
  have hQ : q ≠ 0 → v (aeval W.fieldX q * W.fieldY) ^ 2 = v W.fieldX ^ (2 * q.natDegree + 3) :=
    fun hq => by
      rw [map_mul, mul_pow, valuation_aeval_fieldX O hO hx hq, hy, ← pow_mul, pow_add, mul_comm 2]
  rw [natDegree_norm_smul_basis (W := W) h]
  split_ifs with hq hp
  · subst hq
    rw [map_zero, zero_mul, add_zero]
    exact hP (h.resolve_right (not_not.mpr rfl))
  · subst hp
    rw [map_zero, zero_add]
    exact hQ hq
  · have hne : v (aeval W.fieldX p) ≠ v (aeval W.fieldX q * W.fieldY) := fun e => by
      have := (hP hp).symm.trans ((congrArg (· ^ 2) e).trans (hQ hq))
      have := pow_right_injective₀ (zero_lt_one.trans hx1) hx1.ne' this
      omega
    rw [Valuation.map_add_of_distinct_val _ hne, (pow_right_mono₀ hx1.le).map_max, ← hP hp, ← hQ hq]
    rcases le_total (v (aeval W.fieldX p)) (v (aeval W.fieldX q * W.fieldY)) with hle | hle
    · rw [max_eq_right hle, max_eq_right (pow_le_pow_left₀ zero_le hle 2)]
    · rw [max_eq_left hle, max_eq_left (pow_le_pow_left₀ zero_le hle 2)]

/-- At a pole of `x`, `v(f)² = v(x) ^ deg N(f)` for every nonzero `f` in the coordinate ring. -/
theorem valuation_sq_algebraMap {f : W.CoordinateRing} (hf : f ≠ 0) :
    O.valuation (algebraMap W.CoordinateRing W.FunctionField f) ^ 2 =
      O.valuation W.fieldX ^ (Algebra.norm F[X] f).natDegree := by
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq f
  rw [algebraMap_smul_basis]
  refine valuation_sq_smul_basis O hO hx (not_and_or.mp fun ⟨hp, hq⟩ => hf ?_)
  rw [hp, hq, zero_smul, zero_smul, add_zero]

/-- **The place at infinity, characterised**: at a pole of `x`, a quotient `f / g` of elements of
the coordinate ring is regular exactly when `deg N(f) ≤ deg N(g)`. -/
theorem div_mem_iff {f g : W.CoordinateRing} (hg : g ≠ 0) :
    algebraMap W.CoordinateRing W.FunctionField f / algebraMap _ _ g ∈ O ↔
      (Algebra.norm F[X] f).natDegree ≤ (Algebra.norm F[X] g).natDegree := by
  set v := O.valuation
  have hx1 := one_lt_valuation_fieldX O hx
  by_cases hf : f = 0
  · subst hf
    have : Module.Finite F[X] W.CoordinateRing := .of_basis (CoordinateRing.basis W)
    simp only [map_zero, zero_div, O.zero_mem, Algebra.norm_zero, natDegree_zero, zero_le]
  have hg' : v (algebraMap W.CoordinateRing W.FunctionField g) ≠ 0 := by
    rw [Ne, Valuation.zero_iff, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
    exact hg
  rw [← O.valuation_le_one_iff, map_div₀, div_le_one₀ (zero_lt_iff.mpr hg'),
    ← pow_le_pow_iff_left₀ zero_le zero_le two_ne_zero, valuation_sq_algebraMap O hO hx hf,
    valuation_sq_algebraMap O hO hx hg, pow_le_pow_iff_right₀ hx1]

end Pole

/-! ### Uniqueness and existence -/

/-- **Uniqueness**: there is at most one place where `x` has a pole. -/
theorem eq_of_fieldX_not_mem {O O' : ValuationSubring W.FunctionField}
    (hO : ∀ c : F, algebraMap F _ c ∈ O) (hx : W.fieldX ∉ O)
    (hO' : ∀ c : F, algebraMap F _ c ∈ O') (hx' : W.fieldX ∉ O') : O = O' := by
  ext z
  obtain ⟨f, g, hg, rfl⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
  rw [div_mem_iff O hO hx (nonZeroDivisors.ne_zero hg),
    div_mem_iff O' hO' hx' (nonZeroDivisors.ne_zero hg)]

/-- `x` is not a polynomial in `1 / x`. -/
theorem fieldX_not_mem_adjoin_inv : W.fieldX ∉ Algebra.adjoin F {W.fieldX⁻¹} := by
  intro h
  rw [Algebra.adjoin_singleton_eq_range_aeval] at h
  obtain ⟨p, hp⟩ := h
  change aeval W.fieldX⁻¹ p = W.fieldX at hp
  have hx0 : W.fieldX ≠ 0 := by
    simpa using W.aeval_fieldX_ne_zero (p := X) X_ne_zero
  let : Invertible W.fieldX⁻¹ := invertibleOfNonzero (inv_ne_zero hx0)
  have hrev := eval₂_reverse_mul_pow (algebraMap F W.FunctionField) W.fieldX⁻¹ p
  rw [invOf_eq_inv, inv_inv] at hrev
  change aeval W.fieldX p.reverse * _ = aeval W.fieldX⁻¹ p at hrev
  rw [hp] at hrev
  -- `x` is a root of `X ^ (n + 1) - reverse p`
  have h2 : aeval W.fieldX p.reverse = W.fieldX ^ (p.natDegree + 1) :=
    calc aeval W.fieldX p.reverse
        = aeval W.fieldX p.reverse * W.fieldX⁻¹ ^ p.natDegree * W.fieldX ^ p.natDegree := by
          rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hx0, one_pow, mul_one]
      _ = W.fieldX ^ (p.natDegree + 1) := by rw [hrev]; ring
  have hr : aeval W.fieldX (X ^ (p.natDegree + 1) - p.reverse) = 0 := by
    rw [map_sub, map_pow, aeval_X, h2, sub_self]
  refine W.aeval_fieldX_ne_zero ?_ hr
  intro h0
  have := congrArg natDegree h0
  rw [natDegree_zero, natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow] at this
  · omega
  · rw [natDegree_X_pow]
    exact (reverse_natDegree_le p).trans_lt (Nat.lt_succ_self _)

/-- **Existence**: there is a place where `x` has a pole. -/
theorem exists_valuationSubring_fieldX_not_mem :
    ∃ O : ValuationSubring W.FunctionField, (∀ c : F, algebraMap F _ c ∈ O) ∧ W.fieldX ∉ O := by
  set A := (Algebra.adjoin F {W.fieldX⁻¹}).toSubring
  have ht : W.fieldX⁻¹ ∈ A := Algebra.subset_adjoin rfl
  have hI : Ideal.span {(⟨W.fieldX⁻¹, ht⟩ : A)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    rintro ⟨⟨_, ⟨s, hs⟩, hts, -⟩, rfl⟩
    apply W.fieldX_not_mem_adjoin_inv
    have hx0 : W.fieldX ≠ 0 := by
      simpa using W.aeval_fieldX_ne_zero (p := X) X_ne_zero
    have e : W.fieldX⁻¹ * s = 1 := congrArg Subtype.val hts
    have hsx : s = W.fieldX := by rw [eq_inv_of_mul_eq_one_right e, inv_inv]
    have hs' : s ∈ Algebra.adjoin F {W.fieldX⁻¹} := hs
    rwa [hsx] at hs'
  obtain ⟨V, hAV, hV⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  refine ⟨V, fun c => hAV (Subalgebra.algebraMap_mem _ c), ?_⟩
  have hmem := hV ⟨_, Ideal.subset_span rfl, rfl⟩
  exact ((V.inv_mem_nonunits_iff).mp hmem).resolve_left
    (by simpa using W.aeval_fieldX_ne_zero (p := X) X_ne_zero)

/-! ### Rationality -/

/-- Removing the coefficient of `X ^ k` from a polynomial of degree at most `k`. -/
theorem natDegree_sub_C_mul_X_pow_lt {p : F[X]} {k : ℕ} (hp : p.natDegree ≤ k)
    (h : p - C (p.coeff k) * X ^ k ≠ 0) : (p - C (p.coeff k) * X ^ k).natDegree < k := by
  rw [natDegree_lt_iff_degree_lt h, degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_sub, coeff_C_mul_X_pow]
  rcases hm.lt_or_eq with hm | rfl
  · simp [hm.ne', coeff_eq_zero_of_natDegree_lt (hp.trans_lt hm)]
  · simp

/-- Bounds on the parts of `p + q y` from its norm degree. -/
theorem natDegree_le_natDegree_norm (p q : F[X]) :
    2 * p.natDegree ≤
        (Algebra.norm F[X] (p • (1 : W.CoordinateRing) + q • CoordinateRing.mk W X)).natDegree ∧
      (q ≠ 0 → 2 * q.natDegree + 3 ≤ (Algebra.norm F[X]
        (p • (1 : W.CoordinateRing) + q • CoordinateRing.mk W X)).natDegree) := by
  classical
  by_cases h : p ≠ 0 ∨ q ≠ 0
  · rw [natDegree_norm_smul_basis h]
    split_ifs with hq hp
    · exact ⟨le_rfl, fun h => absurd hq h⟩
    · subst hp; exact ⟨by simp, fun _ => le_rfl⟩
    · exact ⟨le_max_left _ _, fun _ => le_max_right _ _⟩
  · simp only [not_or, not_not] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp, fun h => absurd rfl h⟩

/-- Degree bound `2 deg p < D`, in `WithBot ℕ`. -/
theorem two_nsmul_degree_lt {p : F[X]} {D : ℕ} (h : p = 0 ∨ 2 * p.natDegree < D) :
    2 • p.degree < (D : WithBot ℕ) := by
  rcases h with rfl | h
  · simp only [degree_zero, nsmul_eq_mul]
    exact WithBot.bot_lt_coe D |>.trans_le' (by simp)
  · by_cases hp : p = 0
    · subst hp
      simp only [degree_zero, nsmul_eq_mul]
      exact WithBot.bot_lt_coe D |>.trans_le' (by simp)
    rw [degree_eq_natDegree hp, nsmul_eq_mul]
    exact_mod_cast h

/-- Degree bound `2 deg q + 3 < D`, in `WithBot ℕ`. -/
theorem two_nsmul_degree_add_three_lt {q : F[X]} {D : ℕ}
    (h : q = 0 ∨ 2 * q.natDegree + 3 < D) :
    2 • q.degree + 3 < (D : WithBot ℕ) := by
  by_cases hq : q = 0
  · subst hq
    simp only [degree_zero, nsmul_eq_mul]
    exact WithBot.bot_lt_coe D |>.trans_le' (by simp)
  rw [degree_eq_natDegree hq, nsmul_eq_mul]
  exact_mod_cast h.resolve_left hq

/-- **The leading coefficient**: for `D ≠ 1` there is a monomial `m` (`x ^ k` for `D = 2 k`,
`x ^ k y` for `D = 2 k + 3`) such that every element of norm degree at most `D` differs from a
constant multiple of `m` by an element of smaller norm degree. -/
theorem exists_degree_norm_sub_lt {D : ℕ} (hD : D ≠ 1) :
    ∃ m : W.CoordinateRing, ∀ h : W.CoordinateRing, (Algebra.norm F[X] h).natDegree ≤ D →
      ∃ c : F, (Algebra.norm F[X] (h - algebraMap F _ c * m)).degree < D := by
  have hsmul : ∀ (c : F) (r : F[X]) (b : W.CoordinateRing),
      algebraMap F W.CoordinateRing c * (r • b) = (C c * r) • b := by
    intro c r b
    rw [CoordinateRing.smul, CoordinateRing.smul, ← mul_assoc, C_mul, map_mul]
    rfl
  rcases Nat.even_or_odd D with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · refine ⟨(X ^ k : F[X]) • 1, fun h hh => ?_⟩
    obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq h
    obtain ⟨hp, hq⟩ := natDegree_le_natDegree_norm (W := W) p q
    refine ⟨p.coeff k, ?_⟩
    rw [hsmul, add_sub_right_comm, ← sub_smul, CoordinateRing.degree_norm_smul_basis]
    refine max_lt (two_nsmul_degree_lt ?_) (two_nsmul_degree_add_three_lt ?_)
    · by_cases h0 : p - C (p.coeff k) * X ^ k = 0
      · exact .inl h0
      · exact .inr (by have := natDegree_sub_C_mul_X_pow_lt (by omega) h0; omega)
    · by_cases h0 : q = 0
      · exact .inl h0
      · exact .inr (by have := hq h0; omega)
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    refine ⟨(X ^ j : F[X]) • CoordinateRing.mk W X, fun h hh => ?_⟩
    obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq h
    obtain ⟨hp, hq⟩ := natDegree_le_natDegree_norm (W := W) p q
    refine ⟨q.coeff j, ?_⟩
    rw [hsmul, add_sub_assoc, ← sub_smul, CoordinateRing.degree_norm_smul_basis]
    refine max_lt (two_nsmul_degree_lt (.inr (by omega))) (two_nsmul_degree_add_three_lt ?_)
    by_cases h0 : q - C (q.coeff j) * X ^ j = 0
    · exact .inl h0
    · refine .inr ?_
      have hqj : q.natDegree ≤ j := by
        by_cases hq0 : q = 0
        · simp [hq0]
        · have := hq hq0; omega
      have := natDegree_sub_C_mul_X_pow_lt hqj h0
      omega

section Rational

variable {O : ValuationSubring W.FunctionField} (hO : ∀ c : F, algebraMap F _ c ∈ O)
  (hx : W.fieldX ∉ O)
include hO hx

/-- At a pole of `x`, a quotient `h / g` with `deg N(h) < deg N(g)` vanishes. -/
theorem div_mem_nonunits {h g : W.CoordinateRing}
    (hlt : (Algebra.norm F[X] h).degree < (Algebra.norm F[X] g).natDegree) :
    algebraMap W.CoordinateRing W.FunctionField h / algebraMap _ _ g ∈ O.nonunits := by
  have : Module.Finite F[X] W.CoordinateRing := .of_basis (CoordinateRing.basis W)
  rw [O.mem_nonunits_iff_or]
  by_cases h0 : h = 0
  · left; rw [h0, map_zero, zero_div]
  right
  rw [inv_div, div_mem_iff O hO hx h0, not_le]
  have hN : Algebra.norm F[X] h ≠ 0 := by rwa [Ne, Algebra.norm_eq_zero_iff]
  exact (natDegree_lt_iff_degree_lt hN).mpr hlt

/-- **Rationality of the place at infinity**: every regular function differs from a constant
by a function vanishing there. -/
theorem exists_sub_mem_nonunits {z : W.FunctionField} (hz : z ∈ O) :
    ∃ c : F, z - algebraMap F _ c ∈ O.nonunits := by
  have : Module.Finite F[X] W.CoordinateRing := .of_basis (CoordinateRing.basis W)
  obtain ⟨f, g, hg, rfl⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
  have hg0 := nonZeroDivisors.ne_zero hg
  set D := (Algebra.norm F[X] g).natDegree
  have hf : (Algebra.norm F[X] f).natDegree ≤ D := (div_mem_iff O hO hx hg0).mp hz
  obtain ⟨m, hm⟩ := exists_degree_norm_sub_lt (W := W)
    (CoordinateRing.natDegree_norm_ne_one g)
  obtain ⟨cf, hcf⟩ := hm f hf
  obtain ⟨cg, hcg⟩ := hm g le_rfl
  have hN : Algebra.norm F[X] g ≠ 0 := by rwa [Ne, Algebra.norm_eq_zero_iff]
  have hcg0 : cg ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul, sub_zero, degree_eq_natDegree hN] at hcg
    exact lt_irrefl _ hcg
  refine ⟨cf / cg, ?_⟩
  have h1 := div_mem_nonunits hO hx hcf
  have h2 := div_mem_nonunits hO hx hcg
  have hg' : algebraMap W.CoordinateRing W.FunctionField g ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hg0
  have e : algebraMap W.CoordinateRing W.FunctionField f / algebraMap _ _ g -
      algebraMap F _ (cf / cg) =
      algebraMap W.CoordinateRing W.FunctionField (f - algebraMap F _ cf * m) / algebraMap _ _ g -
        algebraMap F _ (cf / cg) *
          (algebraMap W.CoordinateRing W.FunctionField (g - algebraMap F _ cg * m) /
            algebraMap _ _ g) := by
    simp only [map_sub, map_mul, ← IsScalarTower.algebraMap_apply, map_div₀]
    have hcg' : algebraMap F W.FunctionField cg ≠ 0 := (_root_.map_ne_zero _).mpr hcg0
    field_simp
    ring
  rw [e, O.mem_nonunits_iff]
  rw [O.mem_nonunits_iff] at h1 h2
  refine (Valuation.map_sub _ _ _).trans_lt (max_lt h1 ?_)
  rw [map_mul]
  exact (mul_le_of_le_one_left' ((O.valuation_le_one_iff _).mpr (hO _))).trans_lt h2

/-- The place at infinity is rational, in the elementwise form of `Place.isRational_iff`. -/
theorem exists_eq_or_inv_not_mem {z : W.FunctionField} (hz : z ∈ O) :
    ∃ c : F, z = algebraMap F _ c ∨ (z - algebraMap F _ c)⁻¹ ∉ O := by
  obtain ⟨c, hc⟩ := exists_sub_mem_nonunits hO hx hz
  rw [O.mem_nonunits_iff_or, sub_eq_zero] at hc
  exact ⟨c, hc⟩

end Rational

end WeierstrassCurve.Affine
