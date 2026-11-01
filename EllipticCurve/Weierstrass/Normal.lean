/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Weierstrass.Coordinates
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Tactic.LinearCombination

/-! # The coordinate ring of an elliptic curve is integrally closed (away from 2)

An element of the function field integral over `F[x]` lies in the coordinate ring
(`exists_algebraMap_eq_of_isIntegral`). Write it as `(p + q y) / h` with `p, q, h ∈ F[x]`; its
trace `(2 p - q (a₁ x + a₃)) / h` and norm `N(p + q y) / h²` are integral over `F[x]`, so `h`
divides `2 p - q (a₁ x + a₃)` and `h²` divides `N(p + q y)`; since
`(2 p - q (a₁ x + a₃))² - 4 N(p + q y) = q² ψ` with `ψ` the squarefree `2`-torsion polynomial,
`h` divides `q`, and then `p`. -/

public section

universe u

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F]

/-! ### Polynomial lemmas -/

/-- In `F[X]`, `a² ∣ b² c` with `c` squarefree gives `a ∣ b`. -/
theorem dvd_of_sq_dvd_sq_mul {a b c : F[X]} (hc : Squarefree c) (h : a ^ 2 ∣ b ^ 2 * c) :
    a ∣ b := by
  classical
  by_cases ha : a = 0
  · subst ha
    rw [zero_pow two_ne_zero, zero_dvd_iff, mul_eq_zero, pow_eq_zero_iff two_ne_zero] at h
    rcases h with rfl | rfl
    · exact dvd_refl 0
    · exact absurd hc not_squarefree_zero
  set d := gcd b a
  have hd : d ≠ 0 := fun h0 => ha (gcd_eq_zero_iff _ _ |>.mp h0).2
  have hb : b = d * (b / d) :=
    (EuclideanDomain.mul_div_cancel' hd (gcd_dvd_left b a)).symm
  have ha' : a = d * (a / d) :=
    (EuclideanDomain.mul_div_cancel' hd (gcd_dvd_right b a)).symm
  have hcop : IsCoprime (b / d) (a / d) := isCoprime_div_gcd_div_gcd ha
  rw [ha', hb, mul_pow, mul_pow, mul_assoc] at h
  have h' : (a / d) ^ 2 ∣ (b / d) ^ 2 * c := (mul_dvd_mul_iff_left (pow_ne_zero 2 hd)).mp h
  have hc' : (a / d) ^ 2 ∣ c := (hcop.symm.pow).dvd_of_dvd_mul_left h'
  have hu : IsUnit (a / d) := hc (a / d) (by rwa [← sq])
  rw [ha', hb]
  exact mul_dvd_mul_left d hu.dvd

variable {K : Type*} [Field K] [Algebra F[X] K]

/-- If `r / h` is integral over `F[X]` (embedded in a field), then `h ∣ r`. -/
theorem dvd_of_isIntegral_div (hinj : Function.Injective (algebraMap F[X] K)) {r h : F[X]}
    (hh : h ≠ 0) (hint : IsIntegral F[X] (algebraMap F[X] K r / algebraMap F[X] K h)) :
    h ∣ r := by
  classical
  set d := gcd r h
  have hd : d ≠ 0 := fun h0 => hh (gcd_eq_zero_iff _ _ |>.mp h0).2
  have hr : r = d * (r / d) :=
    (EuclideanDomain.mul_div_cancel' hd (gcd_dvd_left r h)).symm
  have hh' : h = d * (h / d) :=
    (EuclideanDomain.mul_div_cancel' hd (gcd_dvd_right r h)).symm
  have hcop : IsCoprime (r / d) (h / d) := isCoprime_div_gcd_div_gcd hh
  set r₁ := r / d
  set h₁ := h / d
  have hh₁ : h₁ ≠ 0 := fun h0 => hh (by rw [hh', h0, mul_zero])
  have hmap : ∀ p : F[X], p ≠ 0 → algebraMap F[X] K p ≠ 0 := fun p hp =>
    (map_ne_zero_iff _ hinj).mpr hp
  obtain ⟨P, hmon, hP⟩ := hint
  have hz : algebraMap F[X] K h₁ * (algebraMap F[X] K r / algebraMap F[X] K h) =
      algebraMap F[X] K r₁ := by
    rw [hr, hh', map_mul, map_mul]
    field_simp [hmap d hd, hmap h₁ hh₁]
  have hQ := scaleRoots_aeval_eq_zero (r := h₁)
    (a := algebraMap F[X] K r / algebraMap F[X] K h) (p := P) hP
  rw [hz, aeval_algebraMap_apply, map_eq_zero_iff _ hinj] at hQ
  have hdvd : h₁ ∣ (P.scaleRoots h₁).coeff P.natDegree * r₁ ^ P.natDegree := by
    refine dvd_term_of_isRoot_of_dvd_terms P.natDegree hQ fun j hj => ?_
    rw [coeff_scaleRoots]
    rcases lt_or_gt_of_ne hj with hj | hj
    · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self _ (Nat.sub_ne_zero_of_lt hj)) _) _
    · rw [coeff_eq_zero_of_natDegree_lt hj, zero_mul, zero_mul]
      exact dvd_zero _
  rw [coeff_scaleRoots_natDegree, hmon.leadingCoeff, one_mul] at hdvd
  have hu : IsUnit h₁ := (hcop.symm.pow_right (n := P.natDegree)).isUnit_of_dvd' dvd_rfl hdvd
  rw [hr, hh']
  exact mul_dvd_mul_left d hu.dvd

/-! ### The curve -/

variable (W : WeierstrassCurve.Affine F)

/-- Away from 2, the `2`-torsion polynomial `4 X³ + b₂ X² + 2 b₄ X + b₆` of an elliptic curve is
squarefree: its discriminant is `16 Δ`. -/
theorem squarefree_twoTorsionPolynomial [NeZero (2 : F)] [W.IsElliptic] :
    Squarefree W.twoTorsionPolynomial.toPoly := by
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero two_ne_zero two_ne_zero
  have ha : W.twoTorsionPolynomial.a ≠ 0 := h4
  set φ := algebraMap F (AlgebraicClosure F)
  have hs : (W.twoTorsionPolynomial.toPoly.map φ).Splits := IsAlgClosed.splits _
  have hd : W.twoTorsionPolynomial.discr ≠ 0 := by
    rw [twoTorsionPolynomial_discr]
    exact mul_ne_zero (by rw [show (16 : F) = 4 * 4 by norm_num]; exact mul_ne_zero h4 h4)
      W.isUnit_Δ.ne_zero
  have hnd := (Cubic.discr_ne_zero_iff_roots_nodup ha hs).mp hd
  rw [Cubic.map_roots] at hnd
  have h0 : W.twoTorsionPolynomial.toPoly.map φ ≠ 0 :=
    (Polynomial.map_ne_zero_iff φ.injective).mpr (Cubic.ne_zero_of_a_ne_zero ha)
  exact ((separable_map φ).mp ((nodup_roots_iff_of_splits h0 hs).mp hnd)).squarefree

/-- The image of a polynomial in `x` in the function field. -/
theorem algebraMap_polynomial_eq (p : F[X]) :
    algebraMap F[X] W.FunctionField p = aeval W.fieldX p := by
  rw [aeval_fieldX, IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField]
  rfl

/-- `F[x]` embeds in the function field. -/
theorem algebraMap_polynomial_injective :
    Function.Injective (algebraMap F[X] W.FunctionField) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra h0
  rw [algebraMap_polynomial_eq] at hp
  exact W.aeval_fieldX_ne_zero h0 hp

/-- The linear coefficient `a₁ x + a₃` of `y` in the equation, as a polynomial in `x`. -/
noncomputable abbrev linY : F[X] := C W.a₁ * X + C W.a₃

/-- The cubic `x³ + a₂ x² + a₄ x + a₆` of the equation. -/
noncomputable abbrev cubicX : F[X] := X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆

/-- The equation, as `y² + (a₁ x + a₃) y = x³ + a₂ x² + a₄ x + a₆`. -/
theorem fieldY_sq_add :
    W.fieldY ^ 2 + aeval W.fieldX W.linY * W.fieldY = aeval W.fieldX W.cubicX := by
  simp only [linY, cubicX, map_add, map_mul, map_pow, aeval_C, aeval_X]
  linear_combination W.fieldY_equation

/-- The conjugation `y ↦ -y - a₁ x - a₃`, on the coordinate ring into the function field. -/
noncomputable def conjHom : W.CoordinateRing →ₐ[F[X]] W.FunctionField :=
  AdjoinRoot.liftAlgHom W.polynomial (Algebra.ofId F[X] W.FunctionField)
    (-W.fieldY - aeval W.fieldX W.linY) (by
      change eval₂ (algebraMap F[X] W.FunctionField) _ (Y ^ 2 + C (C W.a₁ * X + C W.a₃) * Y -
        C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) = 0
      simp only [eval₂_sub, eval₂_add, eval₂_X_pow, eval₂_mul, eval₂_C, eval₂_X]
      simp only [algebraMap_polynomial_eq, map_add, map_mul, aeval_C, aeval_X, map_pow]
      have := W.fieldY_sq_add
      simp only [linY, cubicX, map_add, map_mul, map_pow, aeval_C, aeval_X] at this ⊢
      linear_combination this)

/-- The conjugation on `p + q y`. -/
theorem conjHom_smul_basis (p q : F[X]) :
    W.conjHom (p • 1 + q • CoordinateRing.mk W X) =
      aeval W.fieldX p + aeval W.fieldX q * (-W.fieldY - aeval W.fieldX W.linY) := by
  rw [map_add, map_smul, map_smul, map_one, conjHom]
  rw [show CoordinateRing.mk W X = AdjoinRoot.root W.polynomial from rfl,
    AdjoinRoot.liftAlgHom_root, Algebra.smul_def, Algebra.smul_def, mul_one,
    algebraMap_polynomial_eq, algebraMap_polynomial_eq]

/-- `1` and `y` are linearly independent over `F[x]` in the function field. -/
theorem eq_zero_of_aeval_add_aeval_mul_fieldY {p q : F[X]}
    (h : aeval W.fieldX p + aeval W.fieldX q * W.fieldY = 0) : p = 0 ∧ q = 0 := by
  rw [← algebraMap_smul_basis, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h
  exact CoordinateRing.smul_basis_eq_zero h

/-- The conjugation is injective. -/
theorem conjHom_injective : Function.Injective W.conjHom := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq r
  rw [conjHom_smul_basis] at hr
  have h0 := W.eq_zero_of_aeval_add_aeval_mul_fieldY (p := p - q * W.linY) (q := -q) (by
    rw [map_sub, map_mul, map_neg]; linear_combination hr)
  obtain rfl : q = 0 := neg_eq_zero.mp h0.2
  obtain rfl : p = 0 := by simpa using h0.1
  simp

/-- The conjugation of the function field over `F(x)`. -/
noncomputable def conj : W.FunctionField →ₐ[F[X]] W.FunctionField :=
  IsFractionRing.liftAlgHom W.conjHom_injective

/-- The conjugation on the coordinate ring. -/
theorem conj_algebraMap (r : W.CoordinateRing) :
    W.conj (algebraMap W.CoordinateRing W.FunctionField r) = W.conjHom r := by
  rw [conj, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

/-- A function times its conjugate is its norm. -/
theorem algebraMap_mul_conjHom (p q : F[X]) :
    algebraMap W.CoordinateRing W.FunctionField (p • 1 + q • CoordinateRing.mk W X) *
        W.conjHom (p • 1 + q • CoordinateRing.mk W X) =
      algebraMap F[X] W.FunctionField (Algebra.norm F[X] (p • 1 + q • CoordinateRing.mk W X)) := by
  rw [algebraMap_smul_basis, conjHom_smul_basis, algebraMap_polynomial_eq,
    CoordinateRing.norm_smul_basis]
  have := W.fieldY_sq_add
  simp only [linY, cubicX, map_add, map_mul, map_pow, map_sub, aeval_C, aeval_X] at this ⊢
  linear_combination (-(aeval W.fieldX q) ^ 2) * this

/-- The conjugate of `p + q y` is `(p - q (a₁ x + a₃)) - q y`. -/
theorem conjHom_eq_algebraMap (p q : F[X]) :
    W.conjHom (p • 1 + q • CoordinateRing.mk W X) =
      algebraMap W.CoordinateRing W.FunctionField
        ((p - q * W.linY) • 1 + (-q) • CoordinateRing.mk W X) := by
  rw [conjHom_smul_basis, algebraMap_smul_basis, map_sub, map_mul, map_neg]
  ring

/-- **The coordinate ring is integrally closed** (away from 2): an element of the function field
integral over `F[x]` lies in the coordinate ring. -/
theorem exists_algebraMap_eq_of_isIntegral [NeZero (2 : F)] [W.IsElliptic] {f : W.FunctionField}
    (hf : IsIntegral F[X] f) : ∃ r : W.CoordinateRing, algebraMap _ _ r = f := by
  have : Module.Finite F[X] W.CoordinateRing := .of_basis (CoordinateRing.basis W)
  have hinj := W.algebraMap_polynomial_injective
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨pb, qb, rfl⟩ := CoordinateRing.exists_smul_basis_eq b
  set h := Algebra.norm F[X] (pb • (1 : W.CoordinateRing) + qb • CoordinateRing.mk W X)
  have hh0 : h ≠ 0 := by rwa [Ne, Algebra.norm_eq_zero_iff]
  have hbK :
      algebraMap W.CoordinateRing W.FunctionField (pb • 1 + qb • CoordinateRing.mk W X) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0
  have hhK : algebraMap F[X] W.FunctionField h ≠ 0 := (map_ne_zero_iff _ hinj).mpr hh0
  -- clear the denominator with the conjugate
  obtain ⟨p, q, hpq⟩ := CoordinateRing.exists_smul_basis_eq
    (a * ((pb - qb * W.linY) • 1 + (-qb) • CoordinateRing.mk W X))
  have hf' : algebraMap W.CoordinateRing W.FunctionField a /
      algebraMap W.CoordinateRing W.FunctionField (pb • 1 + qb • CoordinateRing.mk W X) =
      algebraMap W.CoordinateRing W.FunctionField (p • 1 + q • CoordinateRing.mk W X) /
        algebraMap F[X] W.FunctionField h := by
    rw [hpq, map_mul, ← conjHom_eq_algebraMap, ← algebraMap_mul_conjHom]
    have : W.conjHom (pb • 1 + qb • CoordinateRing.mk W X) ≠ 0 :=
      (map_ne_zero_iff _ W.conjHom_injective).mpr hb0
    field_simp
  rw [hf'] at hf ⊢
  -- trace and norm
  have hc : W.conj
      (algebraMap W.CoordinateRing W.FunctionField (p • 1 + q • CoordinateRing.mk W X) /
      algebraMap F[X] W.FunctionField h) =
      W.conjHom (p • 1 + q • CoordinateRing.mk W X) / algebraMap F[X] W.FunctionField h := by
    rw [map_div₀, conj_algebraMap, AlgHom.commutes]
  have e1 : algebraMap W.CoordinateRing W.FunctionField (p • 1 + q • CoordinateRing.mk W X) /
      algebraMap F[X] W.FunctionField h +
      W.conj (algebraMap W.CoordinateRing W.FunctionField (p • 1 + q • CoordinateRing.mk W X) /
        algebraMap F[X] W.FunctionField h) =
      algebraMap F[X] W.FunctionField (2 * p - q * W.linY) / algebraMap F[X] W.FunctionField h := by
    rw [hc, algebraMap_smul_basis, conjHom_smul_basis, algebraMap_polynomial_eq,
      algebraMap_polynomial_eq]
    simp only [map_sub, map_mul, map_ofNat]
    field_simp
    ring
  have e2 : algebraMap W.CoordinateRing W.FunctionField (p • 1 + q • CoordinateRing.mk W X) /
      algebraMap F[X] W.FunctionField h *
      W.conj (algebraMap W.CoordinateRing W.FunctionField (p • 1 + q • CoordinateRing.mk W X) /
        algebraMap F[X] W.FunctionField h) =
      algebraMap F[X] W.FunctionField (p ^ 2 - p * q * W.linY - q ^ 2 * W.cubicX) /
        algebraMap F[X] W.FunctionField (h ^ 2) := by
    rw [hc, div_mul_div_comm, algebraMap_mul_conjHom, CoordinateRing.norm_smul_basis, map_pow,
      sq (algebraMap F[X] W.FunctionField h)]
  have d1 := dvd_of_isIntegral_div hinj hh0 (e1 ▸ hf.add (hf.map W.conj))
  have d2 := dvd_of_isIntegral_div hinj (pow_ne_zero 2 hh0) (e2 ▸ hf.mul (hf.map W.conj))
  have key : (2 * p - q * W.linY) ^ 2 - 4 * (p ^ 2 - p * q * W.linY - q ^ 2 * W.cubicX) =
      q ^ 2 * W.twoTorsionPolynomial.toPoly := by
    rw [show W.twoTorsionPolynomial.toPoly =
      C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ from rfl]
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, map_add, map_mul,
      map_ofNat, map_pow]
    ring
  have hq : h ∣ q := dvd_of_sq_dvd_sq_mul (W.squarefree_twoTorsionPolynomial)
    (key ▸ dvd_sub (pow_dvd_pow_of_dvd d1 2) (dvd_mul_of_dvd_right d2 4))
  have h2 : IsUnit (2 : F[X]) := by
    rw [← map_ofNat C 2]
    exact isUnit_C.mpr (IsUnit.mk0 2 two_ne_zero)
  have hp : h ∣ p := by
    have := dvd_add d1 (dvd_mul_of_dvd_left hq W.linY)
    rw [sub_add_cancel] at this
    exact h2.dvd_mul_left.mp this
  obtain ⟨p', rfl⟩ := hp
  obtain ⟨q', rfl⟩ := hq
  refine ⟨p' • 1 + q' • CoordinateRing.mk W X, ?_⟩
  rw [algebraMap_smul_basis, algebraMap_smul_basis, ← algebraMap_polynomial_eq,
    ← algebraMap_polynomial_eq, ← algebraMap_polynomial_eq, ← algebraMap_polynomial_eq, map_mul,
    map_mul]
  field_simp

end WeierstrassCurve.Affine
