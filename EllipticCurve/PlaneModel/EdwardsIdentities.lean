/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.PlaneModel.EdwardsAddition
public import EllipticCurve.PlaneModel.Translation
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.Tactic.LinearCombination

/-! # The twisted Edwards formula satisfies the identities of an addition law

The twisted Edwards addition formula as a `PlaneModel.Formula` (`edwardsFormula`), and the
identities making it an addition law on a complete twisted Edwards curve over any field
(`edwards_isAddFormula`): the equation is irreducible (Eisenstein at `y = 1`, as a quadratic in
`x` over `L[y]`: `(a - d y²) x² + (y² - 1)`), the denominators never vanish (completeness), and the
closure (C1) and inverse (C3) identities of `EdwardsFormula.lean`. -/

public section

universe u

open TwistedEdwardsFormula

namespace PlaneModel

/-! ### Irreducibility -/

section Irreducible

variable {L : Type u} [Field L] {a d : L}

open Polynomial in
/-- `(a - d y²) x² + (y² - 1)` is irreducible in `L[y][x]` for `a ≠ d`, away from 2: Eisenstein
at `y - 1`. -/
theorem edwards_poly_irreducible (had : a - d ≠ 0) (h2 : (2 : L) ≠ 0) :
    Irreducible (C (C a - C d * X ^ 2) * X ^ 2 + C (X ^ 2 - 1) : L[X][X]) := by
  set A : L[X] := C a - C d * X ^ 2
  set B : L[X] := X ^ 2 - 1
  have hA : A.eval 1 = a - d := by simp [A]
  have hA0 : A ≠ 0 := fun h => had (by rw [← hA, h, eval_zero])
  set g : L[X][X] := C A * X ^ 2 + C B
  have hdeg : g.natDegree = 2 := by
    simp only [g]; rw [natDegree_add_C, natDegree_C_mul_X_pow 2 A hA0]
  have c2 : g.coeff 2 = A := by simp [g, coeff_X_pow]
  have c0 : g.coeff 0 = B := by simp [g, coeff_X_pow]
  have c1 : g.coeff 1 = 0 := by simp [g, coeff_X_pow]
  have hP : (Ideal.span {X - 1} : Ideal L[X]).IsPrime :=
    (Ideal.span_singleton_prime (by simpa using X_sub_C_ne_zero (1 : L))).mpr
      (by simpa using prime_X_sub_C (1 : L))
  have mem : ∀ p : L[X], p ∈ Ideal.span {X - 1} ↔ p.eval 1 = 0 := fun p => by
    rw [Ideal.mem_span_singleton, ← C_1, dvd_iff_isRoot]; rfl
  refine IsEisensteinAt.irreducible (𝓟 := Ideal.span {X - 1}) ?_ hP ?_ (by rw [hdeg]; norm_num)
  · refine ⟨?_, ?_, ?_⟩
    · rw [leadingCoeff, hdeg, c2, mem, hA]; exact had
    · intro n hn
      rw [hdeg] at hn
      interval_cases n
      · rw [c0, mem]; simp [B]
      · rw [c1]; exact Ideal.zero_mem _
    · rw [c0, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      rintro ⟨q, hq⟩
      have h := congrArg (fun p => (derivative p).eval 1) hq
      simp only [B, derivative_sub, derivative_pow, derivative_X, derivative_one, derivative_mul,
        eval_sub, eval_mul, eval_add, eval_pow, eval_X, eval_one, eval_C, Nat.cast_ofNat,
        Nat.add_one_sub_one, pow_one, sub_self, mul_zero, zero_mul, zero_add, sub_zero,
        mul_one, zero_pow two_ne_zero] at h
      exact h2 (by linear_combination h)
  · intro r hr
    rw [C_dvd_iff_dvd_coeff] at hr
    have hu : r ∣ C (a - d) := by
      have := dvd_add (hr 2) (dvd_mul_of_dvd_right (hr 0) (C d))
      rw [c2, c0] at this
      convert this using 1
      simp only [A, B, C_sub]; ring
    exact isUnit_of_dvd_unit hu (isUnit_C.mpr (Ne.isUnit had))

open MvPolynomial in
/-- **The twisted Edwards equation is irreducible** for `a ≠ d`, away from 2. -/
theorem edwards_G_irreducible (had : a - d ≠ 0) (h2 : (2 : L) ≠ 0) :
    Irreducible (C a * X 0 ^ 2 + X 1 ^ 2 - 1 - C d * X 0 ^ 2 * X 1 ^ 2 :
      MvPolynomial (Fin 2) L) := by
  let e : MvPolynomial (Fin 2) L ≃ₐ[L] Polynomial (Polynomial L) :=
    (finSuccEquiv L 1).trans (Polynomial.mapAlgEquiv
      ((finSuccEquiv L 0).trans (Polynomial.mapAlgEquiv (isEmptyAlgEquiv L (Fin 0)))))
  have h1 : e (X 1) = Polynomial.C Polynomial.X := by
    rw [show (X 1 : MvPolynomial (Fin 2) L) = X (Fin.succ 0) from rfl,
      AlgEquiv.trans_apply, finSuccEquiv_X_succ]
    simp [finSuccEquiv_X_zero]
  have h0 : e (X 0) = Polynomial.X := by simp [e, finSuccEquiv_X_zero]
  have hC : ∀ c : L, e (C c) = Polynomial.C (Polynomial.C c) := fun c => by
    rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]; rfl
  have he : e (C a * X 0 ^ 2 + X 1 ^ 2 - 1 - C d * X 0 ^ 2 * X 1 ^ 2) =
      Polynomial.C (Polynomial.C a - Polynomial.C d * Polynomial.X ^ 2) * Polynomial.X ^ 2 +
        Polynomial.C (Polynomial.X ^ 2 - 1) := by
    simp only [map_sub, map_add, map_mul, map_pow, map_one, h0, h1, hC]
    ring
  rw [← MulEquiv.irreducible_iff e.toMulEquiv]
  change Irreducible (e _)
  rw [he]
  exact edwards_poly_irreducible had h2

end Irreducible

open MvPolynomial

/-! ### The formula -/

section Formula

variable {L : Type u} [Field L]

/-- **The twisted Edwards addition formula**, in the variables `(x₁, y₁, x₂, y₂)`:
`((x₁ y₂ + x₂ y₁) / (1 + d x₁ x₂ y₁ y₂), (y₁ y₂ - a x₁ x₂) / (1 - d x₁ x₂ y₁ y₂))`. -/
noncomputable def edwardsFormula (a d : L) : Formula L where
  numX := X 0 * X 3 + X 2 * X 1
  denX := 1 + C d * X 0 * X 2 * X 1 * X 3
  numY := X 1 * X 3 - C a * X 0 * X 2
  denY := 1 - C d * X 0 * X 2 * X 1 * X 3

variable {K : Type*} [Field K] [Algebra L K]

/-- The value of the Edwards formula. -/
theorem edwardsFormula_eval (a d : L) (p q : K × K) :
    (edwardsFormula a d).eval p q = (addX (algebraMap L K d) p.1 p.2 q.1 q.2,
      addY (algebraMap L K a) (algebraMap L K d) p.1 p.2 q.1 q.2) := by
  simp [Formula.eval, Formula.args, edwardsFormula, addX, addY]

/-- The Edwards formula is defined where its denominators do not vanish. -/
theorem edwardsFormula_defined_iff (a d : L) (p q : K × K) :
    (edwardsFormula a d).Defined p q ↔
      1 + algebraMap L K d * p.1 * q.1 * p.2 * q.2 ≠ 0 ∧
        1 - algebraMap L K d * p.1 * q.1 * p.2 * q.2 ≠ 0 := by
  simp [Formula.Defined, Formula.args, edwardsFormula]

/-- The Edwards formula over an extension. -/
theorem edwardsFormula_map {L' : Type*} [Field L'] (φ : L →+* L') (a d : L) :
    (edwardsFormula a d).map φ = edwardsFormula (φ a) (φ d) := by
  simp [Formula.map, edwardsFormula]

/-- The equation of the Edwards model at a pair. -/
theorem aeval_edwards_G {a d : L} {had : a - d ≠ 0} {h2 : (2 : L) ≠ 0} (u : K × K) :
    aeval ![u.1, u.2] (edwards a d had h2).G = 0 ↔
      algebraMap L K a * u.1 ^ 2 + u.2 ^ 2 = 1 + algebraMap L K d * u.1 ^ 2 * u.2 ^ 2 := by
  rw [edwards_G]
  simp only [map_sub, map_add, map_mul, map_pow, map_one, aeval_X, aeval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> intro h <;> linear_combination h

/-- The equation of the Edwards model at a pair, over `L`. -/
theorem eval_edwards_G {a d : L} {had : a - d ≠ 0} {h2 : (2 : L) ≠ 0} (u : L × L) :
    MvPolynomial.eval ![u.1, u.2] (edwards a d had h2).G = 0 ↔
      a * u.1 ^ 2 + u.2 ^ 2 = 1 + d * u.1 ^ 2 * u.2 ^ 2 := by
  rw [edwards_G]
  simp only [map_sub, map_add, map_mul, map_pow, map_one, MvPolynomial.eval_X,
    MvPolynomial.eval_C, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> intro h <;> linear_combination h

end Formula

/-! ### The identities -/

variable {L : Type u} [Field L] {a d : L} {had : a - d ≠ 0} {h2 : (2 : L) ≠ 0}

/-- **The twisted Edwards formula is an addition law** on a complete twisted Edwards curve, with
negation `(x, y) ↦ (-x, y)`. -/
theorem edwards_isAddFormula (hE : (⟨a, d⟩ : TwistedEdwardsModel L).IsComplete) :
    (edwards a d had h2).IsAddFormula (edwardsFormula a d) (fun q => (-q.1, q.2)) where
  irreducible := by rw [edwards_G]; exact edwards_G_irreducible had h2
  defined p q hp hq := by
    rw [eval_edwards_G] at hp hq
    have := den_ne_zero hE hp hq
    rw [edwardsFormula_defined_iff]
    simpa using this
  neg_mem q hq := by
    rw [eval_edwards_G] at hq ⊢
    linear_combination hq
  neg_neg q _ := by simp
  equation K _ _ u q hu hq hd := by
    rw [aeval_edwards_G] at hu ⊢
    rw [eval_edwards_G] at hq
    rw [edwardsFormula_defined_iff] at hd
    have hq' : algebraMap L K a * algebraMap L K q.1 ^ 2 + algebraMap L K q.2 ^ 2 =
        1 + algebraMap L K d * algebraMap L K q.1 ^ 2 * algebraMap L K q.2 ^ 2 := by
      have := congrArg (algebraMap L K) hq
      simpa only [map_add, map_mul, map_pow, map_one] using this
    rw [edwardsFormula_eval]
    exact equation_add hu hq' hd.1 hd.2
  inverse K _ _ u q hu hq hd hd' := by
    rw [aeval_edwards_G] at hu
    rw [eval_edwards_G] at hq
    rw [edwardsFormula_defined_iff] at hd hd'
    have hq' : algebraMap L K a * algebraMap L K q.1 ^ 2 + algebraMap L K q.2 ^ 2 =
        1 + algebraMap L K d * algebraMap L K q.1 ^ 2 * algebraMap L K q.2 ^ 2 := by
      have := congrArg (algebraMap L K) hq
      simpa only [map_add, map_mul, map_pow, map_one] using this
    rw [edwardsFormula_eval] at hd' ⊢
    simp only [Prod.map_fst, Prod.map_snd, map_neg] at hd' ⊢
    rw [edwardsFormula_eval]
    exact Prod.ext (addX_addX_neg hu hq' hd.1 hd.2 hd'.1) (addY_addX_neg hu hq' hd.1 hd.2 hd'.2)

end PlaneModel
