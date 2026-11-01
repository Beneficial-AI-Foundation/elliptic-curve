/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.PlaneModel.Basic
public import EllipticCurve.PlaneModel.Kernel
public import EllipticCurve.Weierstrass.Places
import EllipticCurve.FunctionField.Constants

/-! # Translations of a plane model from an addition formula

For a plane model `M` of `W` over `L` with irreducible equation `G`:

* **Substitution** (`PlaneModel.subst`): for `ξ, η` in the function field with `G(ξ, η) = 0`, not
  both algebraic, `x ↦ ξ`, `y ↦ η` is an `L`-algebra map of the function field. Both pairs `(x, y)`
  and `(ξ, η)` have exactly the multiples of `G` as relations (`PlaneCurve.ker_aeval_eq_span`).
* **Formulas** (`PlaneModel.Formula`): a pair of rational functions of two points, given by
  numerators and denominators; their values at places are computed termwise.
* **Translations** (`PlaneModel.translation`): if the formula `f` satisfies the identities of an
  addition law (`IsAddFormula`: the curve equation C1 and the inverse identity C3, with
  denominators nonzero at pairs of solutions), then for a solution `r` the substitution
  `(x, y) ↦ f((x, y), r)` is an automorphism `σ_r` of the function field, moving the point with
  coordinates `p` to the point with coordinates `f(p, r)` (`coords_pointMap_translation`). -/

public section

universe u

open MvPolynomial FunctionField.RationalPlace

namespace PlaneModel

/-! ### Formulas -/

/-- An addition formula: two rational functions of two points of the plane, given by numerators
and denominators, polynomials in `(p₁, p₂, q₁, q₂)`. -/
structure Formula (L : Type u) [CommRing L] where
  /-- The numerator of the first coordinate. -/
  numX : MvPolynomial (Fin 4) L
  /-- The denominator of the first coordinate. -/
  denX : MvPolynomial (Fin 4) L
  /-- The numerator of the second coordinate. -/
  numY : MvPolynomial (Fin 4) L
  /-- The denominator of the second coordinate. -/
  denY : MvPolynomial (Fin 4) L

namespace Formula

variable {L : Type u} [Field L] (f : Formula L) {K : Type*} [Field K] [Algebra L K]

/-- The arguments `(p₁, p₂, q₁, q₂)`. -/
@[expose] def args (p q : K × K) : Fin 4 → K := ![p.1, p.2, q.1, q.2]

/-- The value of the formula at `(p, q)`. -/
@[expose] noncomputable def eval (p q : K × K) : K × K :=
  (aeval (args p q) f.numX / aeval (args p q) f.denX,
    aeval (args p q) f.numY / aeval (args p q) f.denY)

/-- The denominators of the formula do not vanish at `(p, q)`. -/
@[expose] def Defined (p q : K × K) : Prop :=
  aeval (args p q) f.denX ≠ 0 ∧ aeval (args p q) f.denY ≠ 0

/-- The formula over an extension of the field of coefficients. -/
@[expose] noncomputable def map {L' : Type*} [Field L'] (φ : L →+* L') : Formula L' :=
  ⟨f.numX.map φ, f.denX.map φ, f.numY.map φ, f.denY.map φ⟩

theorem aeval_args_map {K' : Type*} [Field K'] [Algebra L K'] (φ : K →ₐ[L] K') (p q : K × K)
    (H : MvPolynomial (Fin 4) L) :
    φ (aeval (args p q) H) = aeval (args (Prod.map φ φ p) (Prod.map φ φ q)) H := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  refine congrArg (fun v => aeval v H) ?_
  funext i; fin_cases i <;> rfl

/-- Algebra maps commute with the formula. -/
theorem map_eval {K' : Type*} [Field K'] [Algebra L K'] (φ : K →ₐ[L] K') (p q : K × K) :
    Prod.map φ φ (f.eval p q) = f.eval (Prod.map φ φ p) (Prod.map φ φ q) := by
  ext <;> simp only [eval, Prod.map_fst, Prod.map_snd, map_div₀, aeval_args_map]

/-- Injective algebra maps preserve definedness. -/
theorem defined_map {K' : Type*} [Field K'] [Algebra L K'] (φ : K →ₐ[L] K') {p q : K × K}
    (h : f.Defined p q) : f.Defined (Prod.map φ φ p) (Prod.map φ φ q) := by
  simp only [Defined, ← aeval_args_map]
  exact ⟨(map_ne_zero φ).mpr h.1, (map_ne_zero φ).mpr h.2⟩

/-- The formula at constant arguments. -/
theorem eval_algebraMap (p q : L × L) :
    f.eval (Prod.map (algebraMap L K) (algebraMap L K) p)
        (Prod.map (algebraMap L K) (algebraMap L K) q) =
      Prod.map (algebraMap L K) (algebraMap L K) (f.eval p q) :=
  (f.map_eval (Algebra.ofId L K) p q).symm

/-- The formula is defined at constant arguments where it is defined. -/
theorem defined_algebraMap {p q : L × L} (h : f.Defined p q) :
    f.Defined (Prod.map (algebraMap L K) (algebraMap L K) p)
      (Prod.map (algebraMap L K) (algebraMap L K) q) :=
  f.defined_map (Algebra.ofId L K) h

/-- The formula over an extension, at constant arguments. -/
theorem map_eval_algebraMap {L' : Type*} [Field L'] [Algebra L L'] [Algebra L' K]
    [IsScalarTower L L' K] (p q : L × L) :
    (f.map (algebraMap L L')).eval (Prod.map (algebraMap L K) (algebraMap L K) p)
        (Prod.map (algebraMap L K) (algebraMap L K) q) =
      Prod.map (algebraMap L K) (algebraMap L K) (f.eval p q) := by
  have h : ∀ H : MvPolynomial (Fin 4) L,
      aeval (R := L') (args (Prod.map (algebraMap L K) (algebraMap L K) p)
        (Prod.map (algebraMap L K) (algebraMap L K) q)) (H.map (algebraMap L L')) =
        algebraMap L K (aeval (args p q) H) := fun H => by
    rw [MvPolynomial.aeval_map_algebraMap, ← Algebra.ofId_apply, ← AlgHom.comp_apply,
      MvPolynomial.comp_aeval]
    refine congrArg (fun v => aeval v H) ?_
    funext i; fin_cases i <;> rfl
  ext <;> simp only [eval, map, Prod.map_fst, Prod.map_snd, map_div₀, h]

/-- The formula over an extension is defined at constant arguments where it is defined. -/
theorem defined_map_algebraMap {L' : Type*} [Field L'] [Algebra L L'] [Algebra L' K]
    [IsScalarTower L L' K] {p q : L × L} (h : f.Defined p q) :
    (f.map (algebraMap L L')).Defined (Prod.map (algebraMap L K) (algebraMap L K) p)
      (Prod.map (algebraMap L K) (algebraMap L K) q) := by
  have e : ∀ H : MvPolynomial (Fin 4) L,
      aeval (R := L') (args (Prod.map (algebraMap L K) (algebraMap L K) p)
        (Prod.map (algebraMap L K) (algebraMap L K) q)) (H.map (algebraMap L L')) =
        algebraMap L K (aeval (args p q) H) := fun H => by
    rw [MvPolynomial.aeval_map_algebraMap, ← Algebra.ofId_apply, ← AlgHom.comp_apply,
      MvPolynomial.comp_aeval]
    refine congrArg (fun v => aeval v H) ?_
    funext i; fin_cases i <;> rfl
  simp only [Defined, map, e]
  exact ⟨(map_ne_zero _).mpr h.1, (map_ne_zero _).mpr h.2⟩

variable {f}

/-- A polynomial in functions with values has the value of the polynomial. -/
theorem hasValue_aeval {ι : Type*} {P : FunctionField.RationalPlace L K} {v : ι → K} {c : ι → L}
    (h : ∀ i, P.HasValue (v i) (c i)) (H : MvPolynomial ι L) :
    P.HasValue (aeval v H) (MvPolynomial.eval c H) := by
  induction H using MvPolynomial.induction_on with
  | C a => simpa using hasValue_algebraMap (P := P) a
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (h i)

/-- **Values of the formula** (C5): at a place where `u` has the value `p`, `f(u, r)` has the
value `f(p, r)`, if the formula is defined at `(p, r)`. -/
theorem hasValue_eval {P : FunctionField.RationalPlace L K} {u : K × K} {p r : L × L}
    (hu₁ : P.HasValue u.1 p.1) (hu₂ : P.HasValue u.2 p.2) (hd : f.Defined p r) :
    P.HasValue (f.eval u (Prod.map (algebraMap L K) (algebraMap L K) r)).1 (f.eval p r).1 ∧
      P.HasValue (f.eval u (Prod.map (algebraMap L K) (algebraMap L K) r)).2 (f.eval p r).2 := by
  have h : ∀ i, P.HasValue (args u (Prod.map (algebraMap L K) (algebraMap L K) r) i)
      (args p r i) := fun i => by
    fin_cases i
    · exact hu₁
    · exact hu₂
    · exact hasValue_algebraMap (P := P) r.1
    · exact hasValue_algebraMap (P := P) r.2
  have e : ∀ H : MvPolynomial (Fin 4) L, MvPolynomial.eval (args p r) H = aeval (args p r) H :=
    fun H => by rw [← MvPolynomial.coe_aeval_eq_eval]; rfl
  refine ⟨((hasValue_aeval h _).div (hasValue_aeval h _) ?_).congr rfl ?_,
    ((hasValue_aeval h _).div (hasValue_aeval h _) ?_).congr rfl ?_⟩
  · rw [e]; exact hd.1
  · simp only [eval, e]
  · rw [e]; exact hd.2
  · simp only [eval, e]

/-- At a place where `u` has the value `p`, the formula is defined at `(u, r)` if it is defined
at `(p, r)`. -/
theorem defined_of_hasValue {P : FunctionField.RationalPlace L K} {u : K × K} {p r : L × L}
    (hu₁ : P.HasValue u.1 p.1) (hu₂ : P.HasValue u.2 p.2) (hd : f.Defined p r) :
    f.Defined u (Prod.map (algebraMap L K) (algebraMap L K) r) := by
  have h : ∀ i, P.HasValue (args u (Prod.map (algebraMap L K) (algebraMap L K) r) i)
      (args p r i) := fun i => by
    fin_cases i
    · exact hu₁
    · exact hu₂
    · exact hasValue_algebraMap (P := P) r.1
    · exact hasValue_algebraMap (P := P) r.2
  have e : ∀ H : MvPolynomial (Fin 4) L, MvPolynomial.eval (args p r) H = aeval (args p r) H :=
    fun H => by rw [← MvPolynomial.coe_aeval_eq_eval]; rfl
  exact ⟨(hasValue_aeval h _).ne_zero (by rw [e]; exact hd.1),
    (hasValue_aeval h _).ne_zero (by rw [e]; exact hd.2)⟩

end Formula

/-! ### Substitution -/

variable {L : Type u} [Field L] {W : WeierstrassCurve.Affine L} (M : PlaneModel W)

section Subst

variable {ξ η : W.FunctionField}

/-- For an irreducible equation, a solution `(ξ, η)`, not both algebraic, has the same relations
as `(x, y)`: the multiples of `G`. -/
theorem ker_aeval_eq (hG : Irreducible M.G) (h : aeval ![ξ, η] M.G = 0)
    (ht : Transcendental L ξ ∨ Transcendental L η) :
    RingHom.ker (aeval (R := L) ![ξ, η]) = RingHom.ker (aeval (R := L) ![M.x, M.y]) := by
  have hX : Transcendental L W.fieldX := fun ⟨p, hp, hp0⟩ => W.aeval_fieldX_ne_zero hp hp0
  rw [PlaneCurve.ker_aeval_eq_span hG M.aeval_G (M.adjoin_eq_top ▸ IntermediateField.mem_top) hX]
  rcases ht with ht | ht
  · exact PlaneCurve.ker_aeval_eq_span hG h (IntermediateField.subset_adjoin _ _ (by simp)) ht
  · exact PlaneCurve.ker_aeval_eq_span hG h (IntermediateField.subset_adjoin _ _ (by simp)) ht

/-- The substitution `x ↦ ξ`, `y ↦ η` on `L[x, y]`. -/
noncomputable def substHom (hG : Irreducible M.G) (h : aeval ![ξ, η] M.G = 0)
    (ht : Transcendental L ξ ∨ Transcendental L η) :
    PlaneCurve.coordRing L M.x M.y →ₐ[L] W.FunctionField :=
  (Ideal.Quotient.liftₐ (RingHom.ker (aeval (R := L) ![M.x, M.y]).rangeRestrict)
    (aeval ![ξ, η]) fun a ha => by
      have ha' : a ∈ RingHom.ker (aeval (R := L) ![M.x, M.y]) := by
        rw [RingHom.mem_ker] at ha ⊢
        exact congrArg Subtype.val ha
      rw [← M.ker_aeval_eq hG h ht, RingHom.mem_ker] at ha'
      exact ha').comp
    (Ideal.quotientKerAlgEquivOfSurjective
      (aeval (R := L) ![M.x, M.y]).rangeRestrict_surjective).symm.toAlgHom

theorem substHom_apply (hG : Irreducible M.G) (h : aeval ![ξ, η] M.G = 0)
    (ht : Transcendental L ξ ∨ Transcendental L η) (H : MvPolynomial (Fin 2) L) :
    M.substHom hG h ht ⟨aeval ![M.x, M.y] H, H, rfl⟩ = aeval ![ξ, η] H := by
  have e : (Ideal.quotientKerAlgEquivOfSurjective
      (aeval (R := L) ![M.x, M.y]).rangeRestrict_surjective).symm ⟨aeval ![M.x, M.y] H, H, rfl⟩ =
      Ideal.Quotient.mk _ H := by
    rw [AlgEquiv.symm_apply_eq]; rfl
  rw [substHom, AlgHom.comp_apply]
  erw [e]
  rfl

theorem substHom_injective (hG : Irreducible M.G) (h : aeval ![ξ, η] M.G = 0)
    (ht : Transcendental L ξ ∨ Transcendental L η) : Function.Injective (M.substHom hG h ht) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨s, H, rfl⟩ hs
  have hs : M.substHom hG h ht ⟨aeval ![M.x, M.y] H, H, rfl⟩ = 0 := hs
  rw [substHom_apply] at hs
  have hH : H ∈ RingHom.ker (aeval (R := L) ![ξ, η]) := hs
  rw [M.ker_aeval_eq hG h ht, RingHom.mem_ker] at hH
  exact Subtype.ext hH

/-- **The substitution** `x ↦ ξ`, `y ↦ η` on the function field. -/
noncomputable def subst (hG : Irreducible M.G) (h : aeval ![ξ, η] M.G = 0)
    (ht : Transcendental L ξ ∨ Transcendental L η) : W.FunctionField →ₐ[L] W.FunctionField :=
  haveI := PlaneCurve.isFractionRing_coordRing M.x M.y M.adjoin_eq_top
  IsFractionRing.liftAlgHom (M.substHom_injective hG h ht)

theorem subst_x (hG : Irreducible M.G) (h : aeval ![ξ, η] M.G = 0)
    (ht : Transcendental L ξ ∨ Transcendental L η) : M.subst hG h ht M.x = ξ := by
  have := PlaneCurve.isFractionRing_coordRing M.x M.y M.adjoin_eq_top
  have e : M.x = algebraMap (PlaneCurve.coordRing L M.x M.y) W.FunctionField
      ⟨aeval ![M.x, M.y] (X 0), X 0, rfl⟩ := by simp
  rw [e, subst, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  change M.substHom hG h ht _ = _
  rw [substHom_apply]; simp

theorem subst_y (hG : Irreducible M.G) (h : aeval ![ξ, η] M.G = 0)
    (ht : Transcendental L ξ ∨ Transcendental L η) : M.subst hG h ht M.y = η := by
  have := PlaneCurve.isFractionRing_coordRing M.x M.y M.adjoin_eq_top
  have e : M.y = algebraMap (PlaneCurve.coordRing L M.x M.y) W.FunctionField
      ⟨aeval ![M.x, M.y] (X 1), X 1, rfl⟩ := by simp
  rw [e, subst, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  change M.substHom hG h ht _ = _
  rw [substHom_apply]; simp

/-- `L`-algebra maps of the function field agreeing on `x` and `y` are equal. -/
theorem algHom_ext {K' : Type*} [Field K'] [Algebra L K'] {φ ψ : W.FunctionField →ₐ[L] K'}
    (hx : φ M.x = ψ M.x) (hy : φ M.y = ψ M.y) : φ = ψ := by
  have h := IntermediateField.algHom_ext_of_eq_adjoin L M.adjoin_eq_top.symm
    (φ₁ := φ.comp (IntermediateField.topEquiv (F := L) (E := W.FunctionField)).toAlgHom)
    (φ₂ := ψ.comp (IntermediateField.topEquiv (F := L) (E := W.FunctionField)).toAlgHom)
    (by rintro z (rfl | rfl) <;> simpa)
  refine AlgHom.ext fun z => ?_
  have hz := congrArg (fun χ => χ ⟨z, IntermediateField.mem_top⟩) h
  exact hz

end Subst

/-! ### Translations -/

/-- The identities making `f` an addition law on the model `M`, with negation `neg`: the
equation is irreducible; the denominators do not vanish at pairs of solutions (completeness);
`neg` is an involution of the solutions; the curve equation (C1) and the inverse identity (C3)
hold over every extension. -/
structure IsAddFormula (f : Formula L) (neg : L × L → L × L) : Prop where
  irreducible : Irreducible M.G
  defined : ∀ p q : L × L, MvPolynomial.eval ![p.1, p.2] M.G = 0 →
    MvPolynomial.eval ![q.1, q.2] M.G = 0 → f.Defined p q
  neg_mem : ∀ q : L × L, MvPolynomial.eval ![q.1, q.2] M.G = 0 →
    MvPolynomial.eval ![(neg q).1, (neg q).2] M.G = 0
  neg_neg : ∀ q : L × L, MvPolynomial.eval ![q.1, q.2] M.G = 0 → neg (neg q) = q
  equation : ∀ (K : Type u) [Field K] [Algebra L K] (u : K × K) (q : L × L),
    aeval ![u.1, u.2] M.G = 0 → MvPolynomial.eval ![q.1, q.2] M.G = 0 →
      f.Defined u (Prod.map (algebraMap L K) (algebraMap L K) q) →
        aeval ![(f.eval u (Prod.map (algebraMap L K) (algebraMap L K) q)).1,
          (f.eval u (Prod.map (algebraMap L K) (algebraMap L K) q)).2] M.G = 0
  inverse : ∀ (K : Type u) [Field K] [Algebra L K] (u : K × K) (q : L × L),
    aeval ![u.1, u.2] M.G = 0 → MvPolynomial.eval ![q.1, q.2] M.G = 0 →
      f.Defined u (Prod.map (algebraMap L K) (algebraMap L K) q) →
      f.Defined (f.eval u (Prod.map (algebraMap L K) (algebraMap L K) q))
        (Prod.map (algebraMap L K) (algebraMap L K) (neg q)) →
        f.eval (f.eval u (Prod.map (algebraMap L K) (algebraMap L K) q))
          (Prod.map (algebraMap L K) (algebraMap L K) (neg q)) = u

section Translation

variable [W.IsElliptic] {M} {f : Formula L} {neg : L × L → L × L} (hf : M.IsAddFormula f neg)
  {o : L × L} (ho : M.coords 0 = some o)

set_option quotPrecheck false in
/-- Constant pairs in the function field. -/
local notation "ιp" => Prod.map (algebraMap L W.FunctionField) (algebraMap L W.FunctionField)

include hf

omit [W.IsElliptic] in
/-- The formula maps pairs of solutions to solutions. -/
theorem IsAddFormula.eval_mem {p q : L × L} (hp : MvPolynomial.eval ![p.1, p.2] M.G = 0)
    (hq : MvPolynomial.eval ![q.1, q.2] M.G = 0) :
    MvPolynomial.eval ![(f.eval p q).1, (f.eval p q).2] M.G = 0 := by
  have hp' : aeval (R := L) ![p.1, p.2] M.G = 0 := hp
  have h := hf.equation L p q hp' hq (by simpa using hf.defined p q hp hq)
  simp only [Algebra.algebraMap_self, RingHom.coe_id, Prod.map_id, id_eq] at h
  exact h

include ho

/-- The formula is defined at `((x, y), r)`. -/
theorem IsAddFormula.defined_xy {r : L × L} (hr : MvPolynomial.eval ![r.1, r.2] M.G = 0) :
    f.Defined (M.x, M.y) (ιp r) := by
  obtain ⟨hx, hy⟩ := M.hasValue_of_coords ho
  exact Formula.defined_of_hasValue hx hy (hf.defined o r (M.coords_equation ho) hr)

/-- The formula is defined at `(f((x, y), q), r)`. -/
theorem IsAddFormula.defined_eval_xy {q r : L × L} (hq : MvPolynomial.eval ![q.1, q.2] M.G = 0)
    (hr : MvPolynomial.eval ![r.1, r.2] M.G = 0) :
    f.Defined (f.eval (M.x, M.y) (ιp q)) (ιp r) := by
  obtain ⟨hx, hy⟩ := M.hasValue_of_coords ho
  have ho' := M.coords_equation ho
  obtain ⟨h₁, h₂⟩ := Formula.hasValue_eval (u := (M.x, M.y)) hx hy (hf.defined o q ho' hq)
  exact Formula.defined_of_hasValue h₁ h₂ (hf.defined _ r (hf.eval_mem ho' hq) hr)

/-- The substituted coordinates are not both constant. -/
theorem IsAddFormula.transcendental {r : L × L} (hr : MvPolynomial.eval ![r.1, r.2] M.G = 0) :
    Transcendental L (f.eval (M.x, M.y) (ιp r)).1 ∨
      Transcendental L (f.eval (M.x, M.y) (ιp r)).2 := by
  by_contra hc
  rw [not_or, Transcendental, Transcendental, not_not, not_not] at hc
  set P₀ := W.pointEquivRationalPlace 0
  obtain ⟨c₁, hc₁⟩ := P₀.exists_eq_algebraMap_of_isAlgebraic hc.1
  obtain ⟨c₂, hc₂⟩ := P₀.exists_eq_algebraMap_of_isAlgebraic hc.2
  have hu : f.eval (M.x, M.y) (ιp r) = ιp (c₁, c₂) := Prod.ext hc₁ hc₂
  have hn := hf.neg_mem r hr
  have hinv := hf.inverse W.FunctionField (M.x, M.y) r M.aeval_G hr (hf.defined_xy ho hr)
    (hf.defined_eval_xy ho hr hn)
  rw [hu, Formula.eval_algebraMap] at hinv
  rcases M.ne_const (f.eval (c₁, c₂) (neg r)).1 (f.eval (c₁, c₂) (neg r)).2 with h | h
  · exact h (congrArg Prod.fst hinv).symm
  · exact h (congrArg Prod.snd hinv).symm

/-- The substituted coordinates satisfy the equation. -/
theorem IsAddFormula.equation_xy {r : L × L} (hr : MvPolynomial.eval ![r.1, r.2] M.G = 0) :
    aeval ![(f.eval (M.x, M.y) (ιp r)).1, (f.eval (M.x, M.y) (ιp r)).2] M.G = 0 :=
  hf.equation W.FunctionField (M.x, M.y) r M.aeval_G hr (hf.defined_xy ho hr)

/-- **The substitution `σ_r`**, `(x, y) ↦ f((x, y), r)`. -/
noncomputable def IsAddFormula.translationHom {r : L × L}
    (hr : MvPolynomial.eval ![r.1, r.2] M.G = 0) : W.FunctionField →ₐ[L] W.FunctionField :=
  M.subst hf.irreducible (hf.equation_xy ho hr) (hf.transcendental ho hr)

theorem IsAddFormula.translationHom_xy {r : L × L} (hr : MvPolynomial.eval ![r.1, r.2] M.G = 0) :
    Prod.map (hf.translationHom ho hr) (hf.translationHom ho hr) (M.x, M.y) =
      f.eval (M.x, M.y) (ιp r) :=
  Prod.ext (M.subst_x _ _ _) (M.subst_y _ _ _)

theorem IsAddFormula.translationHom_congr {r r' : L × L} (h : r = r')
    (hr : MvPolynomial.eval ![r.1, r.2] M.G = 0) (hr' : MvPolynomial.eval ![r'.1, r'.2] M.G = 0) :
    hf.translationHom ho hr = hf.translationHom ho hr' := by
  subst h; rfl

/-- `σ_{neg r} ∘ σ_r = id` (C3). -/
theorem IsAddFormula.translationHom_comp {r : L × L} (hr : MvPolynomial.eval ![r.1, r.2] M.G = 0) :
    (hf.translationHom ho (hf.neg_mem r hr)).comp (hf.translationHom ho hr) = AlgHom.id L _ := by
  set σ := hf.translationHom ho (hf.neg_mem r hr)
  have hn := hf.neg_mem r hr
  have hinv := hf.inverse W.FunctionField (M.x, M.y) (neg r) M.aeval_G hn
    (hf.defined_xy ho hn) (hf.defined_eval_xy ho hn (hf.neg_mem _ hn))
  rw [hf.neg_neg r hr] at hinv
  have hσ : Prod.map σ σ (f.eval (M.x, M.y) (ιp r)) = (M.x, M.y) := by
    rw [Formula.map_eval, hf.translationHom_xy ho hn]
    convert hinv using 2
    ext <;> simp
  have hxy := hf.translationHom_xy ho hr
  apply M.algHom_ext
  · rw [AlgHom.comp_apply, show hf.translationHom ho hr M.x = _ from congrArg Prod.fst hxy,
      AlgHom.id_apply]
    exact congrArg Prod.fst hσ
  · rw [AlgHom.comp_apply, show hf.translationHom ho hr M.y = _ from congrArg Prod.snd hxy,
      AlgHom.id_apply]
    exact congrArg Prod.snd hσ

/-- **The translation `σ_r`** as an automorphism of the function field. -/
noncomputable def IsAddFormula.translation {r : L × L}
    (hr : MvPolynomial.eval ![r.1, r.2] M.G = 0) : W.FunctionField ≃ₐ[L] W.FunctionField :=
  AlgEquiv.ofAlgHom (hf.translationHom ho hr) (hf.translationHom ho (hf.neg_mem r hr))
    (by
      have h := hf.translationHom_comp ho (hf.neg_mem r hr)
      rwa [hf.translationHom_congr ho (hf.neg_neg r hr) (hf.neg_mem _ (hf.neg_mem r hr)) hr] at h)
    (hf.translationHom_comp ho hr)

theorem IsAddFormula.translation_apply {r : L × L} (hr : MvPolynomial.eval ![r.1, r.2] M.G = 0)
    (z : W.FunctionField) : hf.translation ho hr z = hf.translationHom ho hr z := by
  unfold IsAddFormula.translation; rfl

/-- **`σ_r` moves the point with coordinates `p` to the point with coordinates `f(p, r)`.** -/
theorem IsAddFormula.coords_pointMap_translation {r : L × L}
    (hr : MvPolynomial.eval ![r.1, r.2] M.G = 0) {P : M.Point} {p : L × L}
    (hP : M.coords P = some p) :
    M.coords (WeierstrassCurve.Affine.pointMapOfAlgEquiv (hf.translation ho hr) P) =
      some (f.eval p r) := by
  obtain ⟨p₁, p₂⟩ := p
  obtain ⟨hx, hy⟩ := M.hasValue_of_coords hP
  obtain ⟨h₁, h₂⟩ := Formula.hasValue_eval (u := (M.x, M.y)) hx hy
    (hf.defined (p₁, p₂) r (M.coords_equation hP) hr)
  apply M.coords_eq_of_hasValue
  · rw [WeierstrassCurve.Affine.pointMapOfAlgEquiv_apply, Equiv.apply_symm_apply,
      hasValue_congr_iff, translation_apply, IsAddFormula.translationHom, M.subst_x]
    exact h₁
  · rw [WeierstrassCurve.Affine.pointMapOfAlgEquiv_apply, Equiv.apply_symm_apply,
      hasValue_congr_iff, translation_apply, IsAddFormula.translationHom, M.subst_y]
    exact h₂

end Translation

end PlaneModel
