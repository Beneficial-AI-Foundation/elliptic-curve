/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.FunctionField.Place
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.LinearCombination

/-! # The local ring of a plane curve at a nonsingular point

For functions `x`, `y` generating a field `K` over `F` and satisfying `G(x, y) = 0`, and a
nonsingular solution `(a, b)` of `G` at which `F[x, y]` can be evaluated, the local ring of
`F[x, y]` at `(a, b)` is a discrete valuation ring, hence a rational place of `K`; it is the only
rational place where `x`, `y` take the values `a`, `b`. This is (A-coord) for plane models.

The first-order Taylor expansion `G - G(a, b) = (X - a) P + (Y - b) Q` with
`P(a, b) = ∂G/∂X (a, b)` and `Q(a, b) = ∂G/∂Y (a, b)` (`exists_taylor`) gives both the
generators `x - a`, `y - b` of the maximal ideal and, at a nonsingular point, a single one. -/

public section

universe u v

open MvPolynomial

namespace PlaneCurve

variable {F : Type u} [Field F]

/-- **First-order Taylor expansion** of a polynomial in two variables at a point. -/
theorem exists_taylor (G : MvPolynomial (Fin 2) F) (a b : F) :
    ∃ P Q : MvPolynomial (Fin 2) F,
      G - C (eval ![a, b] G) = (X 0 - C a) * P + (X 1 - C b) * Q ∧
        eval ![a, b] P = eval ![a, b] (pderiv 0 G) ∧
        eval ![a, b] Q = eval ![a, b] (pderiv 1 G) := by
  induction G using MvPolynomial.induction_on with
  | C c => exact ⟨0, 0, by simp, by simp, by simp⟩
  | add G₁ G₂ h₁ h₂ =>
    obtain ⟨P₁, Q₁, e₁, p₁, q₁⟩ := h₁
    obtain ⟨P₂, Q₂, e₂, p₂, q₂⟩ := h₂
    refine ⟨P₁ + P₂, Q₁ + Q₂, ?_, by simp [p₁, p₂], by simp [q₁, q₂]⟩
    rw [map_add, map_add]
    linear_combination e₁ + e₂
  | mul_X G i h =>
    obtain ⟨P, Q, e, p, q⟩ := h
    fin_cases i
    · refine ⟨P * X 0 + C (eval ![a, b] G), Q * X 0, ?_, ?_, ?_⟩
      · simp only [map_mul, eval_X]
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        linear_combination (X 0 : MvPolynomial (Fin 2) F) * e
      · simp [p, Derivation.leibniz, pderiv_X]
        ring
      · simp [q, Derivation.leibniz, pderiv_X]
        ring
    · refine ⟨P * X 1, Q * X 1 + C (eval ![a, b] G), ?_, ?_, ?_⟩
      · simp only [map_mul, eval_X]
        simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one]
        simp only [Matrix.cons_val_fin_one]
        linear_combination (X 1 : MvPolynomial (Fin 2) F) * e
      · simp [p, Derivation.leibniz, pderiv_X]
        ring
      · simp [q, Derivation.leibniz, pderiv_X]
        ring

/-! ### The coordinate ring and the evaluation at a point -/

/-- The coordinate ring `F[x, y]` of the plane curve, inside `K`. -/
noncomputable abbrev coordRing (F : Type u) [Field F] {K : Type v} [Field K] [Algebra F K]
    (x y : K) : Subalgebra F K :=
  (aeval ![x, y]).range

variable {K : Type v} [Field K] [Algebra F K] (x y : K)

/-- `K` is the fraction field of `F[x, y]` when `x, y` generate it. -/
theorem isFractionRing_coordRing (htop : IntermediateField.adjoin F {x, y} = ⊤) :
    IsFractionRing (coordRing F x y) K := by
  refine IsFractionRing.of_field _ K fun z => ?_
  have hz : z ∈ IntermediateField.adjoin F {x, y} := htop ▸ IntermediateField.mem_top
  obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
  have hS : Algebra.adjoin F {x, y} = coordRing F x y := by
    change _ = (aeval ![x, y]).range
    rw [← Algebra.adjoin_range_eq_range_aeval]
    congr 1
    ext w
    simp [eq_comm, or_comm]
  rw [hS] at hr hs
  exact ⟨⟨r, hr⟩, ⟨s, hs⟩, rfl⟩

variable {x y} {a b : F}

/-- The hypothesis that evaluation at `(a, b)` is well defined on `F[x, y]`. -/
def EvalWellDefined (x y : K) (a b : F) : Prop :=
  ∀ H : MvPolynomial (Fin 2) F, aeval ![x, y] H = 0 → eval ![a, b] H = 0

/-- The definition of `EvalWellDefined`. -/
theorem evalWellDefined_iff : EvalWellDefined x y a b ↔
    ∀ H : MvPolynomial (Fin 2) F, aeval ![x, y] H = 0 → eval ![a, b] H = 0 :=
  Iff.rfl

/-- Polynomials with the same value at `(x, y)` have the same value at `(a, b)`. -/
theorem EvalWellDefined.eval_eq (hε : EvalWellDefined x y a b) {H H' : MvPolynomial (Fin 2) F}
    (h : aeval ![x, y] H = aeval ![x, y] H') : eval ![a, b] H = eval ![a, b] H' := by
  have := hε (H - H') (by rw [map_sub, h, sub_self])
  rwa [map_sub, sub_eq_zero] at this

/-- The chosen polynomial expression of an element of `F[x, y]`. -/
theorem choose_spec_coordRing (s : coordRing F x y) :
    MvPolynomial.aeval (R := F) ![x, y] s.2.choose = (s : K) :=
  s.2.choose_spec

/-- Evaluation of `F[x, y]` at a point `(a, b)`, when it is well defined. -/
noncomputable def evalAt (hε : EvalWellDefined x y a b) : coordRing F x y →ₐ[F] F where
  toFun s := eval ![a, b] s.2.choose
  map_one' := by
    have h : aeval ![x, y] (1 : coordRing F x y).2.choose =
        aeval ![x, y] (1 : MvPolynomial (Fin 2) F) := by
      rw [choose_spec_coordRing, map_one]; rfl
    change eval ![a, b] _ = 1
    rw [hε.eval_eq h, map_one]
  map_mul' s t := by
    have h : aeval ![x, y] (s * t).2.choose = aeval ![x, y] (s.2.choose * t.2.choose) := by
      rw [map_mul, choose_spec_coordRing, choose_spec_coordRing, choose_spec_coordRing]; rfl
    change eval ![a, b] _ = eval ![a, b] _ * eval ![a, b] _
    rw [hε.eval_eq h, map_mul]
  map_zero' := by
    have h : aeval ![x, y] (0 : coordRing F x y).2.choose =
        aeval ![x, y] (0 : MvPolynomial (Fin 2) F) := by
      rw [choose_spec_coordRing, map_zero]; rfl
    change eval ![a, b] _ = 0
    rw [hε.eval_eq h, map_zero]
  map_add' s t := by
    have h : aeval ![x, y] (s + t).2.choose = aeval ![x, y] (s.2.choose + t.2.choose) := by
      rw [map_add, choose_spec_coordRing, choose_spec_coordRing, choose_spec_coordRing]; rfl
    change eval ![a, b] _ = eval ![a, b] _ + eval ![a, b] _
    rw [hε.eval_eq h, map_add]
  commutes' c := by
    have h : aeval ![x, y] (algebraMap F (coordRing F x y) c).2.choose = aeval ![x, y] (C c) := by
      rw [choose_spec_coordRing, aeval_C]; rfl
    change eval ![a, b] _ = c
    rw [hε.eval_eq h, eval_C]

/-- Evaluation of `H(x, y)` at the point is `H(a, b)`. -/
theorem evalAt_apply (hε : EvalWellDefined x y a b) (H : MvPolynomial (Fin 2) F) :
    evalAt hε ⟨aeval ![x, y] H, H, rfl⟩ = eval ![a, b] H :=
  hε.eval_eq (choose_spec_coordRing _)

/-! ### The local ring at a nonsingular point -/

/-- The data of a nonsingular point of the plane curve `G(x, y) = 0` in `K`: `x, y` generate `K`,
`(a, b)` is a nonsingular solution of `G`, evaluation at it is well defined on `F[x, y]`, and
`x, y` are not both constant. -/
structure NonsingularPoint (G : MvPolynomial (Fin 2) F) (x y : K) (a b : F) : Prop where
  aeval_G : aeval ![x, y] G = 0
  adjoin_eq_top : IntermediateField.adjoin F {x, y} = ⊤
  eval_G : eval ![a, b] G = 0
  pderiv_ne_zero : eval ![a, b] (pderiv 0 G) ≠ 0 ∨ eval ![a, b] (pderiv 1 G) ≠ 0
  evalWellDefined : EvalWellDefined x y a b
  ne_const : x ≠ algebraMap F K a ∨ y ≠ algebraMap F K b

variable {G : MvPolynomial (Fin 2) F} (h : NonsingularPoint G x y a b)

/-- The maximal ideal of the point in `F[x, y]`. -/
noncomputable def pointIdeal : Ideal (coordRing F x y) :=
  RingHom.ker (evalAt h.evalWellDefined)

include h in
/-- The ideal of the point is maximal. -/
theorem isMaximal_pointIdeal : (pointIdeal h).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun c => ⟨algebraMap F _ c, by simp⟩

/-- The local ring at the point, as a subalgebra of `K`. -/
noncomputable def localRing : Subalgebra (coordRing F x y) K :=
  haveI := isFractionRing_coordRing x y h.adjoin_eq_top
  haveI := (isMaximal_pointIdeal h).isPrime
  Localization.subalgebra.ofField K (pointIdeal h).primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors _)

/-- The local ring is the localization at the ideal of the point. -/
theorem isLocalization_localRing :
    haveI := (isMaximal_pointIdeal h).isPrime
    IsLocalization.AtPrime (localRing h) (pointIdeal h) := by
  have := isFractionRing_coordRing x y h.adjoin_eq_top
  have := (isMaximal_pointIdeal h).isPrime
  exact Localization.subalgebra.isLocalization_ofField _ _ _

/-- Membership in the local ring: quotients with denominator not vanishing at the point. -/
theorem mem_localRing {z : K} :
    z ∈ localRing h ↔ ∃ r s : coordRing F x y, s ∉ pointIdeal h ∧
      z = (r : K) * (s : K)⁻¹ := by
  have := isFractionRing_coordRing x y h.adjoin_eq_top
  have := (isMaximal_pointIdeal h).isPrime
  unfold localRing
  rw [Localization.subalgebra.ofField]
  change (∃ r s, ∃ _ : s ∈ (pointIdeal h).primeCompl, z = _) ↔ _
  simp only [Ideal.mem_primeCompl_iff, exists_prop]
  rfl

/-- The function `x - a`, in `F[x, y]`. -/
noncomputable def uX (x y : K) (a : F) : coordRing F x y := ⟨aeval ![x, y] (X 0 - C a), _, rfl⟩

/-- The function `y - b`, in `F[x, y]`. -/
noncomputable def uY (x y : K) (b : F) : coordRing F x y := ⟨aeval ![x, y] (X 1 - C b), _, rfl⟩

/-- `x - a` vanishes at the point. -/
theorem uX_mem : uX x y a ∈ pointIdeal h := by
  rw [pointIdeal, RingHom.mem_ker, uX, evalAt_apply]
  simp

/-- `y - b` vanishes at the point. -/
theorem uY_mem : uY x y b ∈ pointIdeal h := by
  rw [pointIdeal, RingHom.mem_ker, uY, evalAt_apply]
  simp

/-- The function `uX` is `x - a`. -/
theorem coe_uX : (uX x y a : K) = x - algebraMap F K a := by
  simp [uX]

/-- The function `uY` is `y - b`. -/
theorem coe_uY : (uY x y b : K) = y - algebraMap F K b := by
  simp [uY]

/-- The ideal of the point is generated by `x - a` and `y - b`. -/
theorem pointIdeal_eq : pointIdeal h = Ideal.span {uX x y a, uY x y b} := by
  refine le_antisymm (fun r hr => ?_) ?_
  · obtain ⟨H, hH⟩ := r.2
    obtain ⟨P, Q, e, -, -⟩ := exists_taylor H a b
    have h0 : eval ![a, b] H = 0 := by
      rw [pointIdeal, RingHom.mem_ker] at hr
      rw [← hr, ← evalAt_apply h.evalWellDefined H]
      congr 1
      exact Subtype.ext hH
    rw [h0, map_zero, sub_zero] at e
    rw [Ideal.mem_span_pair]
    refine ⟨⟨aeval ![x, y] P, _, rfl⟩, ⟨aeval ![x, y] Q, _, rfl⟩, Subtype.ext ?_⟩
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, uX, uY]
    rw [← hH, e]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_mul]
    ring
  · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨uX_mem h, uY_mem h⟩

/-- **The uniformizer**: the maximal ideal of the local ring is principal, generated by `x - a`
or by `y - b`. -/
theorem exists_maximalIdeal_localRing_eq_span :
    haveI := (isMaximal_pointIdeal h).isPrime
    haveI := isLocalization_localRing h
    haveI := IsLocalization.AtPrime.isLocalRing (localRing h) (pointIdeal h)
    ∃ π ∈ ({uX x y a, uY x y b} : Set (coordRing F x y)),
      IsLocalRing.maximalIdeal (localRing h) =
        Ideal.span {algebraMap (coordRing F x y) (localRing h) π} := by
  have := (isMaximal_pointIdeal h).isPrime
  have := isLocalization_localRing h
  have := IsLocalization.AtPrime.isLocalRing (localRing h) (pointIdeal h)
  set φ := algebraMap (coordRing F x y) (localRing h)
  have hunit : ∀ s ∉ pointIdeal h, IsUnit (φ s) := fun s hs =>
    IsLocalization.map_units (localRing h) (⟨s, hs⟩ : (pointIdeal h).primeCompl)
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (pointIdeal h) (localRing h), pointIdeal_eq h,
    Ideal.map_span, Set.image_pair]
  obtain ⟨P, Q, e, hP, hQ⟩ := exists_taylor G a b
  rw [h.eval_G, map_zero, sub_zero] at e
  have key : φ (uX x y a) * φ ⟨aeval ![x, y] P, _, rfl⟩ +
      φ (uY x y b) * φ ⟨aeval ![x, y] Q, _, rfl⟩ = 0 := by
    rw [← map_mul, ← map_mul, ← map_add, ← map_zero φ]
    congr 1
    apply Subtype.ext
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, uX, uY, Subalgebra.coe_zero]
    rw [← map_mul, ← map_mul, ← map_add, ← e, h.aeval_G]
  have hnm : ∀ H : MvPolynomial (Fin 2) F, eval ![a, b] H ≠ 0 →
      (⟨aeval ![x, y] H, _, rfl⟩ : coordRing F x y) ∉ pointIdeal h := fun H hH hm => by
    rw [pointIdeal, RingHom.mem_ker, evalAt_apply] at hm
    exact hH hm
  rcases h.pderiv_ne_zero with hp | hq
  · -- `∂G/∂X ≠ 0`: `x - a = -(y - b) Q / P`
    obtain ⟨v, hv⟩ := hunit _ (hnm P (hP ▸ hp))
    refine ⟨uY x y b, Set.mem_insert_of_mem _ rfl, le_antisymm ?_ ?_⟩
    · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨?_, Ideal.subset_span rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_span_singleton']
      refine ⟨-(φ ⟨aeval ![x, y] Q, _, rfl⟩ * ↑v⁻¹), ?_⟩
      have : φ (uX x y a) = φ (uX x y a) * (φ ⟨aeval ![x, y] P, _, rfl⟩ * ↑v⁻¹) := by
        rw [← hv, Units.mul_inv, mul_one]
      rw [this]
      linear_combination (-(↑v⁻¹ : localRing h)) * key
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  · -- `∂G/∂Y ≠ 0`: `y - b = -(x - a) P / Q`
    obtain ⟨v, hv⟩ := hunit _ (hnm Q (hQ ▸ hq))
    refine ⟨uX x y a, Set.mem_insert _ _, le_antisymm ?_ ?_⟩
    · rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      refine ⟨Ideal.subset_span rfl, ?_⟩
      rw [SetLike.mem_coe, Ideal.mem_span_singleton']
      refine ⟨-(φ ⟨aeval ![x, y] P, _, rfl⟩ * ↑v⁻¹), ?_⟩
      have : φ (uY x y b) = φ (uY x y b) * (φ ⟨aeval ![x, y] Q, _, rfl⟩ * ↑v⁻¹) := by
        rw [← hv, Units.mul_inv, mul_one]
      rw [this]
      linear_combination (-(↑v⁻¹ : localRing h)) * key
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.subset_span (Set.mem_insert _ _)

/-- `F[x, y]` is contained in the local ring. -/
theorem coe_mem_localRing (r : coordRing F x y) : (r : K) ∈ localRing h :=
  (mem_localRing h).mpr ⟨r, 1, fun hm => (isMaximal_pointIdeal h).ne_top
    (Ideal.eq_top_of_isUnit_mem _ hm isUnit_one), by simp⟩

/-- The inverse of an element not vanishing at the point is in the local ring. -/
theorem inv_mem_localRing {s : coordRing F x y} (hs : s ∉ pointIdeal h) :
    (s : K)⁻¹ ∈ localRing h :=
  (mem_localRing h).mpr ⟨1, s, hs, by simp⟩

/-- The inverse of a nonzero element of the ideal of the point is not in the local ring. -/
theorem inv_not_mem_localRing {r : coordRing F x y} (hr : r ∈ pointIdeal h) (h0 : (r : K) ≠ 0) :
    (r : K)⁻¹ ∉ localRing h := by
  have := (isMaximal_pointIdeal h).isPrime
  have := isLocalization_localRing h
  have := IsLocalization.AtPrime.isLocalRing (localRing h) (pointIdeal h)
  intro hinv
  have hmax : algebraMap (coordRing F x y) (localRing h) r ∈
      IsLocalRing.maximalIdeal (localRing h) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (pointIdeal h) (localRing h)]
    exact Ideal.mem_map_of_mem _ hr
  apply (IsLocalRing.maximalIdeal.isMaximal (localRing h)).ne_top
  refine Ideal.eq_top_of_isUnit_mem _ hmax ⟨⟨_, ⟨_, hinv⟩, ?_, ?_⟩, rfl⟩ <;>
    exact Subtype.ext (by simp [h0])

/-- The local ring at a nonsingular point is a valuation ring. -/
theorem valuationRing_localRing : ValuationRing (localRing h) := by
  have := (isMaximal_pointIdeal h).isPrime
  have := isLocalization_localRing h
  have := IsLocalization.AtPrime.isLocalRing (localRing h) (pointIdeal h)
  have : IsNoetherianRing (coordRing F x y) :=
    isNoetherianRing_of_surjective _ _ (aeval ![x, y]).rangeRestrict.toRingHom
      (AlgHom.rangeRestrict_surjective _)
  have : IsNoetherianRing (localRing h) :=
    IsLocalization.isNoetherianRing (pointIdeal h).primeCompl _ inferInstance
  obtain ⟨π, -, hπ⟩ := exists_maximalIdeal_localRing_eq_span h
  have hp : (IsLocalRing.maximalIdeal (localRing h)).IsPrincipal := ⟨_, hπ⟩
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (R := localRing h)).out 5 2).mp hp

/-- The place of the point. -/
noncomputable def place : FunctionField.Place F K where
  ring := ValuationSubring.ofSubring (localRing h).toSubring fun z => by
    have := isFractionRing_coordRing x y h.adjoin_eq_top
    have hv := valuationRing_localRing h
    rcases (ValuationRing.iff_isInteger_or_isInteger (localRing h) K).mp hv z with
      ⟨a, ha⟩ | ⟨a, ha⟩
    · exact .inl (ha ▸ a.2)
    · exact .inr (ha ▸ a.2)
  algebraMap_mem c := by
    change algebraMap F K c ∈ localRing h
    have := coe_mem_localRing h (algebraMap F _ c)
    simpa using this
  ne_top htop := by
    rcases h.ne_const with hx | hy
    · have hm : ((uX x y a : K))⁻¹ ∈ (⊤ : ValuationSubring K) := ValuationSubring.mem_top _
      rw [← htop] at hm
      exact inv_not_mem_localRing h (uX_mem h) (by rw [coe_uX]; exact sub_ne_zero.mpr hx) hm
    · have hm : ((uY x y b : K))⁻¹ ∈ (⊤ : ValuationSubring K) := ValuationSubring.mem_top _
      rw [← htop] at hm
      exact inv_not_mem_localRing h (uY_mem h) (by rw [coe_uY]; exact sub_ne_zero.mpr hy) hm

/-- Membership in the place of the point. -/
theorem mem_place {z : K} : z ∈ (place h).ring ↔ z ∈ localRing h :=
  Iff.rfl

/-- The place of a nonsingular point is rational. -/
theorem isRational_place : (place h).IsRational := by
  rw [FunctionField.Place.isRational_iff]
  intro z hz
  obtain ⟨r, s, hs, rfl⟩ := (mem_localRing h).mp hz
  set ε := evalAt h.evalWellDefined
  have hcs : ε s ≠ 0 := hs
  set c := ε r / ε s
  have hr : r - algebraMap F _ c * s ∈ pointIdeal h := by
    rw [pointIdeal, RingHom.mem_ker, map_sub, map_mul, AlgHom.commutes]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, c]
    field_simp
    ring
  refine ⟨c, ?_⟩
  have hs0 : (s : K) ≠ 0 := fun h0 => hs (by
    have : s = 0 := Subtype.ext h0
    rw [this]; exact Ideal.zero_mem _)
  have hz : (r : K) * (s : K)⁻¹ - algebraMap F K c =
      ((r - algebraMap F _ c * s : coordRing F x y) : K) * (s : K)⁻¹ := by
    simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
    field_simp
  by_cases h0 : ((r - algebraMap F _ c * s : coordRing F x y) : K) = 0
  · left
    rw [← sub_eq_zero, hz, h0, zero_mul]
  · right
    rw [hz]
    intro hinv
    apply inv_not_mem_localRing h hr h0
    have := mul_mem (inv_mem_localRing h hs) hinv
    convert this using 1
    field_simp

/-- The rational place of a nonsingular point. -/
noncomputable def rationalPlace : FunctionField.RationalPlace F K :=
  ⟨place h, isRational_place h⟩

/-- An element of the ideal of the point vanishes at its place. -/
theorem hasValue_of_mem {r : coordRing F x y} (hr : r ∈ pointIdeal h) :
    (rationalPlace h).HasValue (r : K) 0 := by
  have hm : (r : K) ∈ (rationalPlace h).1.ring := coe_mem_localRing h r
  refine FunctionField.RationalPlace.hasValue_iff.mpr ⟨hm, ?_⟩
  rw [FunctionField.RationalPlace.eval_eq_zero_iff]
  by_cases h0 : (r : K) = 0
  · left; exact h0
  · right; exact inv_not_mem_localRing h hr h0

/-- `x` takes the value `a` at the place of the point. -/
theorem hasValue_x : (rationalPlace h).HasValue x a := by
  have h1 := (hasValue_of_mem h (uX_mem h)).add
    (FunctionField.RationalPlace.hasValue_algebraMap (P := rationalPlace h) a)
  rwa [coe_uX, sub_add_cancel, zero_add] at h1

/-- `y` takes the value `b` at the place of the point. -/
theorem hasValue_y : (rationalPlace h).HasValue y b := by
  have h1 := (hasValue_of_mem h (uY_mem h)).add
    (FunctionField.RationalPlace.hasValue_algebraMap (P := rationalPlace h) b)
  rwa [coe_uY, sub_add_cancel, zero_add] at h1

/-! ### Uniqueness -/

open FunctionField.RationalPlace in
/-- A polynomial in two regular functions has the value of the polynomial. -/
theorem hasValue_aeval {P : FunctionField.RationalPlace F K} (hx : P.HasValue x a)
    (hy : P.HasValue y b) (H : MvPolynomial (Fin 2) F) :
    P.HasValue (aeval ![x, y] H) (eval ![a, b] H) := by
  induction H using MvPolynomial.induction_on with
  | C c => simpa using hasValue_algebraMap (P := P) c
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp =>
    fin_cases i
    · simpa using hp.mul hx
    · simpa using hp.mul hy

open FunctionField.RationalPlace in
/-- **Uniqueness**: a rational place where `x`, `y` take the values `a`, `b` is the place of the
point. -/
theorem eq_rationalPlace {P : FunctionField.RationalPlace F K} (hx : P.HasValue x a)
    (hy : P.HasValue y b) : P = rationalPlace h := by
  have hval : ∀ r : coordRing F x y, P.HasValue (r : K) (evalAt h.evalWellDefined r) := by
    rintro ⟨_, H, rfl⟩
    rw [show (⟨_, H, rfl⟩ : coordRing F x y) = ⟨aeval ![x, y] H, H, rfl⟩ from rfl, evalAt_apply]
    exact hasValue_aeval hx hy H
  have hle : ∀ z ∈ localRing h, z ∈ P.1.ring := by
    intro z hz
    obtain ⟨r, s, hs, rfl⟩ := (mem_localRing h).mp hz
    exact ((hval r).mul ((hval s).inv hs)).mem
  refine Subtype.ext (FunctionField.Place.ext ?_)
  ext z
  refine ⟨fun hz => ?_, fun hz => hle z hz⟩
  change z ∈ localRing h
  by_contra hzA
  have := (isMaximal_pointIdeal h).isPrime
  have := isLocalization_localRing h
  have := IsLocalization.AtPrime.isLocalRing (localRing h) (pointIdeal h)
  have hzi : z⁻¹ ∈ localRing h := ((place h).ring.mem_or_inv_mem z).resolve_left hzA
  have hz0 : z ≠ 0 := fun h0 => hzA (h0 ▸ (localRing h).zero_mem)
  have hmax : (⟨z⁻¹, hzi⟩ : localRing h) ∈ IsLocalRing.maximalIdeal (localRing h) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨⟨_, w, hw, -⟩, rfl⟩
    apply hzA
    have hw' : z⁻¹ * (w : K) = 1 := congrArg Subtype.val hw
    have hwz : (w : K) = z := by rw [eq_inv_of_mul_eq_one_right hw', inv_inv]
    exact hwz ▸ w.2
  obtain ⟨π, hπ, hπm⟩ := exists_maximalIdeal_localRing_eq_span h
  rw [hπm, Ideal.mem_span_singleton'] at hmax
  obtain ⟨c, hc⟩ := hmax
  have hc' : (c : K) * (π : K) = z⁻¹ := congrArg Subtype.val hc
  have hπ0 : P.HasValue (π : K) 0 := by
    have hm : π ∈ pointIdeal h := by
      rcases hπ with rfl | rfl
      · exact uX_mem h
      · exact uY_mem h
    have := hval π
    rwa [show evalAt h.evalWellDefined π = 0 from hm] at this
  have hzinv := (HasValue.of_mem (hle c c.2)).mul hπ0
  rw [hc'] at hzinv
  have h1 := (HasValue.of_mem hz).mul hzinv
  rw [mul_inv_cancel₀ hz0] at h1
  exact one_ne_zero ((hasValue_one.unique h1).trans (by simp))

end PlaneCurve
