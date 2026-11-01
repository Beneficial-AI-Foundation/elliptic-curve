/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.PlaneModel.Local
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # The equation of a plane model generates all relations

If `x, y` generate a field that is not algebraic over `F`, and `G` is an irreducible polynomial
with `G(x, y) = 0`, then every polynomial relation between `x` and `y` is a multiple of `G`
(`ker_aeval_eq_span`). The kernel `I` of `F[X, Y] → K` is a prime containing `(G)`; it is not
maximal (else `F[x, y]` would be a field of finite type, hence finite over `F` by Zariski's
lemma, and `F(x, y)` would be algebraic); so `I = (G)`, since otherwise `⊥ < (G) < I < M` would be a
chain of primes of length `3` in `F[X, Y]`, of Krull dimension `2`. -/

public section

universe u v

open MvPolynomial

namespace PlaneCurve

variable {F : Type u} [Field F] {K : Type v} [Field K] [Algebra F K] {x y : K}
  {G : MvPolynomial (Fin 2) F}

/-- The kernel of `F[X, Y] → K` is not maximal when `F(x, y)` is not algebraic. -/
theorem ker_aeval_not_isMaximal {z : K} (hzmem : z ∈ IntermediateField.adjoin F {x, y})
    (hz : Transcendental F z) : ¬ (RingHom.ker (aeval (R := F) ![x, y])).IsMaximal := by
  intro hmax
  set I := RingHom.ker (aeval (R := F) ![x, y])
  -- `F[x, y] ≃ F[X, Y] / I` is a field of finite type, hence finite over `F`
  have hker : RingHom.ker (aeval (R := F) ![x, y]).rangeRestrict = I := by
    ext H
    simp only [RingHom.mem_ker, I, Subtype.ext_iff]
    rfl
  let e : (MvPolynomial (Fin 2) F ⧸ I) ≃ₐ[F] coordRing F x y :=
    (Ideal.quotientEquivAlgOfEq F hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (AlgHom.rangeRestrict_surjective (aeval ![x, y])))
  let : Field (MvPolynomial (Fin 2) F ⧸ I) := Ideal.Quotient.field I
  have hfin : Module.Finite F (MvPolynomial (Fin 2) F ⧸ I) :=
    finite_of_finite_type_of_isJacobsonRing F _
  have hfield : IsField (coordRing F x y) := e.toMulEquiv.symm.isField (Field.toIsField _)
  have hfin' : Module.Finite F (coordRing F x y) := Module.Finite.equiv e.toLinearEquiv
  -- so `F[x, y]` is an intermediate field containing `x` and `y`, hence all of `K`
  set L := (coordRing F x y).toIntermediateField' hfield
  have hL : IntermediateField.adjoin F {x, y} ≤ L := by
    rw [IntermediateField.adjoin_le_iff]
    rintro w (rfl | rfl)
    · exact ⟨X 0, by simp⟩
    · exact ⟨X 1, by simp⟩
  have hzL : z ∈ L := hL hzmem
  have : FiniteDimensional F L := hfin'
  exact hz (IsIntegral.isAlgebraic (IsIntegral.of_finite F (⟨z, hzL⟩ : L) |>.map L.val))

/-- **The equation generates all relations**: for `G` irreducible with `G(x, y) = 0`, where
`F(x, y)` is not algebraic, the kernel of `F[X, Y] → K` is `(G)`. -/
theorem ker_aeval_eq_span (hG : Irreducible G) (hGx : aeval ![x, y] G = 0) {z : K}
    (hzmem : z ∈ IntermediateField.adjoin F {x, y}) (hz : Transcendental F z) :
    RingHom.ker (aeval (R := F) ![x, y]) = Ideal.span {G} := by
  set I := RingHom.ker (aeval (R := F) ![x, y])
  have hle : Ideal.span {G} ≤ I := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hGx
  by_contra hne
  have hlt : Ideal.span {G} < I := lt_of_le_of_ne hle (Ne.symm hne)
  have hIp : I.IsPrime := RingHom.ker_isPrime _
  have hGp : (Ideal.span {G}).IsPrime := (Ideal.span_singleton_prime hG.ne_zero).mpr hG.prime
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hIp.ne_top
  have hIM' : I < M := lt_of_le_of_ne hIM fun h => ker_aeval_not_isMaximal hzmem hz (by
    change I.IsMaximal; rw [h]; exact hM)
  have hbG : (⊥ : Ideal (MvPolynomial (Fin 2) F)) < Ideal.span {G} := by
    rw [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]
    exact hG.ne_zero
  let p : Fin 4 → PrimeSpectrum (MvPolynomial (Fin 2) F) :=
    ![⟨⊥, Ideal.isPrime_bot⟩, ⟨_, hGp⟩, ⟨I, hIp⟩, ⟨M, hM.isPrime⟩]
  let s : LTSeries (PrimeSpectrum (MvPolynomial (Fin 2) F)) :=
    ⟨3, p, fun i => by
      fin_cases i
      · exact (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp hbG
      · exact (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp hlt
      · exact (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp hIM'⟩
  have h3 := Order.LTSeries.length_le_krullDim s
  have h2 : ringKrullDim (MvPolynomial (Fin 2) F) = 2 := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  change ((3 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin 2) F) at h3
  rw [h2] at h3
  norm_num at h3

end PlaneCurve
