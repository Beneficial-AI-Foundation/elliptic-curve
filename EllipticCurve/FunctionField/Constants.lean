/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.FunctionField.Place
public import Mathlib.RingTheory.Algebraic.Defs
import EllipticCurve.Weierstrass.Infinity
import Mathlib.RingTheory.Algebraic.Integral

/-! # Exact constants

An element algebraic over `F` is regular at every place (`mem_of_isAlgebraic`). So a field with
a rational place has exact constants: its elements algebraic over `F` lie in `F`
(`RationalPlace.exists_eq_algebraMap_of_isAlgebraic`). -/

public section

universe u v

open Polynomial

namespace FunctionField

variable {F : Type u} {K : Type v} [Field F] [Field K] [Algebra F K]

/-- An element algebraic over `F` is in every valuation subring containing `F`. -/
theorem mem_of_isAlgebraic {O : ValuationSubring K} (hO : ∀ c : F, algebraMap F K c ∈ O)
    {z : K} (hz : IsAlgebraic F z) : z ∈ O := by
  by_contra hzO
  obtain ⟨p, hp, hpz⟩ := hz
  have hc : ∀ c : F, c ≠ 0 → O.valuation (algebraMap F K c) = 1 := by
    intro c hc0
    have h1 := (O.valuation_le_one_iff _).mpr (hO c)
    have h2 := (O.valuation_le_one_iff _).mpr (hO c⁻¹)
    have h0 : O.valuation (algebraMap F K c) ≠ 0 := by
      rw [Ne, Valuation.zero_iff, map_eq_zero_iff _ (algebraMap F K).injective]
      exact hc0
    rw [map_inv₀, map_inv₀, inv_le_one₀ (zero_lt_iff.mpr h0)] at h2
    exact le_antisymm h1 h2
  have hz1 : 1 < O.valuation z := by
    rw [← not_le, O.valuation_le_one_iff]
    exact hzO
  have := O.valuation.map_aeval_eq_pow_natDegree hc hz1 hp
  rw [hpz, map_zero] at this
  exact pow_ne_zero _ (zero_lt_one.trans hz1).ne' this.symm

namespace RationalPlace

/-- **Exact constants**: in a field with a rational place, an element algebraic over `F` is a
constant. -/
theorem exists_eq_algebraMap_of_isAlgebraic (P : RationalPlace F K) {z : K}
    (hz : IsAlgebraic F z) : ∃ c : F, z = algebraMap F K c := by
  have hzP := mem_of_isAlgebraic P.1.algebraMap_mem hz
  refine ⟨P.eval z hzP, ?_⟩
  by_contra hne
  set w := z - algebraMap F K (P.eval z hzP)
  have hw0 : w ≠ 0 := sub_ne_zero.mpr hne
  have hw : P.HasValue w 0 :=
    ((HasValue.of_mem hzP).sub (hasValue_algebraMap _)).congr rfl (sub_self _)
  have hwalg : IsAlgebraic F w := hz.sub (isAlgebraic_algebraMap _)
  have hwinv := mem_of_isAlgebraic P.1.algebraMap_mem hwalg.inv
  obtain ⟨hwm, hwe⟩ := hasValue_iff.mp hw
  rcases (eval_eq_zero_iff hwm).mp hwe with h | h
  · exact hw0 h
  · exact h hwinv

end RationalPlace

end FunctionField
