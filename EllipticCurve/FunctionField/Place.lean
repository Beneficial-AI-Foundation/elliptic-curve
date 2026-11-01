/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.Algebra.MvPolynomial.Basic

/-! # Places of a function field

A **place** of a field `K` over a subfield `F` is a valuation subring of `K` that contains `F`
and is not all of `K`. It is **rational** (of degree one) when its residue field is `F`, that is,
when the composite `F → O → O/𝔪` is surjective. The rational places of the function field of an
elliptic curve are its points (`WeierstrassCurve.Affine.pointEquivRationalPlace`).

A rational place `P` evaluates the functions that are regular at it (those in its valuation
ring): `P.eval f hf ∈ F` is the residue class of `f`, read in `F`. Evaluation is a ring
homomorphism on the valuation ring (`RationalPlace.evalHom`), so it commutes with polynomial
expressions (`RationalPlace.evalHom_eval₂Hom`).

An `F`-isomorphism of fields `K ≃ₐ[F] K'` carries places to places by pulling back valuation
rings, preserving rationality (`RationalPlace.congr`).

## Provenance

The representation of places as valuation subrings follows `EllipticCurve/FunctionField/
Places.lean` of lana-agents/elliptic-curves (Apache-2.0); TauCeti represents them as valuations
up to equivalence. The definitions here are our own. -/

public section

universe u v w

/-- A place of `K` over `F`: a valuation subring of `K` containing `F`, other than `K`. -/
@[ext] structure FunctionField.Place (F : Type u) (K : Type v) [Field F] [Field K] [Algebra F K]
    where
  /-- The valuation ring of the place: the functions regular at it. -/
  ring : ValuationSubring K
  /-- The constants are regular everywhere. -/
  algebraMap_mem : ∀ c : F, algebraMap F K c ∈ ring
  /-- A place is not the trivial valuation. -/
  ne_top : ring ≠ ⊤

namespace FunctionField.Place

variable {F : Type u} {K : Type v} {K' : Type w} [Field F] [Field K] [Field K'] [Algebra F K]
  [Algebra F K'] (P : Place F K)

/-- The constants, as elements of the valuation ring of a place. -/
def constHom : F →+* P.ring where
  toFun c := ⟨algebraMap F K c, P.algebraMap_mem c⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

/-- The constants, in the residue field of a place. -/
noncomputable def residueConst : F →+* IsLocalRing.ResidueField P.ring :=
  (IsLocalRing.residue P.ring).comp P.constHom

/-- A place is **rational** (of degree one) when its residue field is `F`. -/
def IsRational : Prop :=
  Function.Surjective P.residueConst

/-- In a valuation subring of a field, an element is a unit exactly when it is nonzero with its
inverse in the ring. -/
theorem isUnit_iff_inv_mem {A : ValuationSubring K} {a : K} (ha : a ∈ A) :
    IsUnit (⟨a, ha⟩ : A) ↔ a ≠ 0 ∧ a⁻¹ ∈ A := by
  constructor
  · rintro ⟨⟨u, w, huw, _⟩, hu⟩
    have hu' : (u : K) = a := congrArg Subtype.val hu
    have h1 : a * (w : K) = 1 := by
      rw [← hu']; exact congrArg Subtype.val huw
    refine ⟨left_ne_zero_of_mul_eq_one h1, ?_⟩
    rw [inv_eq_of_mul_eq_one_right h1]
    exact w.2
  · rintro ⟨h0, hinv⟩
    exact ⟨⟨⟨a, ha⟩, ⟨a⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ h0),
      Subtype.ext (inv_mul_cancel₀ h0)⟩, rfl⟩

/-- Rationality, elementwise: every regular function differs from a constant by an element of the
maximal ideal, that is, equals the constant or has a non-regular inverse difference. -/
theorem isRational_iff : P.IsRational ↔
    ∀ z ∈ P.ring, ∃ c : F, z = algebraMap F K c ∨ (z - algebraMap F K c)⁻¹ ∉ P.ring := by
  have key : ∀ (z : K) (hz : z ∈ P.ring) (c : F),
      P.residueConst c = IsLocalRing.residue P.ring ⟨z, hz⟩ ↔
        z = algebraMap F K c ∨ (z - algebraMap F K c)⁻¹ ∉ P.ring := by
    intro z hz c
    have hzc : z - algebraMap F K c ∈ P.ring := P.ring.sub_mem hz (P.algebraMap_mem c)
    rw [residueConst, RingHom.comp_apply, eq_comm, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    change ¬ IsUnit (⟨z - algebraMap F K c, hzc⟩ : P.ring) ↔ _
    rw [isUnit_iff_inv_mem, not_and_or, not_not, sub_eq_zero]
  constructor
  · intro h z hz
    obtain ⟨c, hc⟩ := h (IsLocalRing.residue P.ring ⟨z, hz⟩)
    exact ⟨c, (key z hz c).mp hc⟩
  · intro h r
    obtain ⟨⟨z, hz⟩, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨c, hc⟩ := h z hz
    exact ⟨c, (key z hz c).mpr hc⟩

/-- The pullback of a place of `K'` along an `F`-isomorphism `K ≃ₐ[F] K'`. -/
def comap (P : Place F K') (e : K ≃ₐ[F] K') : Place F K where
  ring := P.ring.comap e.toRingHom
  algebraMap_mem c := by
    change e (algebraMap F K c) ∈ P.ring
    rw [e.commutes]
    exact P.algebraMap_mem c
  ne_top h := P.ne_top <| by
    ext z
    simp only [ValuationSubring.mem_top, iff_true]
    have : e.symm z ∈ P.ring.comap e.toRingHom := h ▸ ValuationSubring.mem_top _
    simpa using this

/-- Membership in the pulled-back place. -/
@[simp] theorem mem_comap_ring (P : Place F K') (e : K ≃ₐ[F] K') (z : K) :
    z ∈ (P.comap e).ring ↔ e z ∈ P.ring :=
  Iff.rfl

/-- Pulling back twice is pulling back along the composite. -/
theorem comap_comap {K'' : Type*} [Field K''] [Algebra F K''] (P : Place F K'')
    (e : K ≃ₐ[F] K') (e' : K' ≃ₐ[F] K'') : (P.comap e').comap e = P.comap (e.trans e') := by
  ext z
  simp

/-- Pulling back along the identity does nothing. -/
theorem comap_refl (P : Place F K) : P.comap (AlgEquiv.refl) = P := by
  ext z
  simp

/-- Pulling back along an isomorphism preserves rationality. -/
theorem IsRational.comap {P : Place F K'} (hP : P.IsRational) (e : K ≃ₐ[F] K') :
    (P.comap e).IsRational := by
  rw [isRational_iff] at hP ⊢
  intro z hz
  obtain ⟨c, hc | hc⟩ := hP (e z) hz
  · refine ⟨c, Or.inl ?_⟩
    apply e.injective
    rw [hc, e.commutes]
  · refine ⟨c, Or.inr fun h => hc ?_⟩
    have := (mem_comap_ring P e _).mp h
    rwa [map_inv₀, map_sub, e.commutes] at this

end FunctionField.Place

/-- The rational places of `K` over `F`. -/
abbrev FunctionField.RationalPlace (F : Type u) (K : Type v) [Field F] [Field K] [Algebra F K] :=
  {P : FunctionField.Place F K // P.IsRational}

namespace FunctionField.RationalPlace

variable {F : Type u} {K : Type v} {K' : Type w} [Field F] [Field K] [Field K'] [Algebra F K]
  [Algebra F K'] (P : RationalPlace F K)

/-- The residue field of a rational place is `F`. -/
noncomputable def residueEquiv : F ≃+* IsLocalRing.ResidueField P.1.ring :=
  RingEquiv.ofBijective P.1.residueConst ⟨P.1.residueConst.injective, P.2⟩

/-- Evaluation at a rational place, on the functions regular there. -/
noncomputable def evalHom : P.1.ring →+* F :=
  P.residueEquiv.symm.toRingHom.comp (IsLocalRing.residue P.1.ring)

/-- The value at `P` of a function regular at `P`. -/
noncomputable def eval (f : K) (hf : f ∈ P.1.ring) : F :=
  P.evalHom ⟨f, hf⟩

/-- Evaluation of a constant is the constant. -/
@[simp] theorem evalHom_constHom (c : F) : P.evalHom (P.1.constHom c) = c :=
  P.residueEquiv.symm_apply_apply c

/-- The value of a constant is the constant. -/
@[simp] theorem eval_algebraMap (c : F) : P.eval (algebraMap F K c) (P.1.algebraMap_mem c) = c :=
  P.evalHom_constHom c

/-- A polynomial expression in functions regular at a place, computed in its valuation ring. -/
theorem coe_eval₂Hom {ι : Type*} (f : ι → K) (hf : ∀ i, f i ∈ P.1.ring) (G : MvPolynomial ι F) :
    ((MvPolynomial.eval₂Hom P.1.constHom (fun i => ⟨f i, hf i⟩) G : P.1.ring) : K) =
      MvPolynomial.aeval f G := by
  have h := MvPolynomial.comp_eval₂Hom P.1.constHom (fun i => (⟨f i, hf i⟩ : P.1.ring))
    P.1.ring.toSubring.subtype
  exact congrArg (fun φ : MvPolynomial ι F →+* K => φ G) h

/-- Evaluation at a rational place commutes with polynomial expressions. -/
theorem evalHom_eval₂Hom {ι : Type*} (f : ι → K) (hf : ∀ i, f i ∈ P.1.ring)
    (G : MvPolynomial ι F) :
    P.evalHom (MvPolynomial.eval₂Hom P.1.constHom (fun i => ⟨f i, hf i⟩) G) =
      MvPolynomial.eval (fun i => P.eval (f i) (hf i)) G := by
  have h := MvPolynomial.comp_eval₂Hom P.1.constHom (fun i => (⟨f i, hf i⟩ : P.1.ring)) P.evalHom
  have hc : P.evalHom.comp P.1.constHom = RingHom.id F := RingHom.ext P.evalHom_constHom
  rw [hc] at h
  exact congrArg (fun φ : MvPolynomial ι F →+* F => φ G) h

/-! ### Computing values -/

variable {P}

/-- Evaluation respects equality of functions. -/
theorem eval_congr {f g : K} (h : f = g) (hf : f ∈ P.1.ring) :
    P.eval f hf = P.eval g (h ▸ hf) := by
  subst h; rfl

/-- The value of `0` is `0`. -/
@[simp] theorem eval_zero : P.eval (0 : K) P.1.ring.zero_mem = 0 :=
  map_zero P.evalHom

/-- The value of `1` is `1`. -/
@[simp] theorem eval_one : P.eval (1 : K) P.1.ring.one_mem = 1 :=
  map_one P.evalHom

/-- Values of sums. -/
theorem eval_add {f g : K} (hf : f ∈ P.1.ring) (hg : g ∈ P.1.ring) :
    P.eval (f + g) (add_mem hf hg) = P.eval f hf + P.eval g hg :=
  map_add P.evalHom ⟨f, hf⟩ ⟨g, hg⟩

/-- Values of differences. -/
theorem eval_sub {f g : K} (hf : f ∈ P.1.ring) (hg : g ∈ P.1.ring) :
    P.eval (f - g) (sub_mem hf hg) = P.eval f hf - P.eval g hg :=
  map_sub P.evalHom ⟨f, hf⟩ ⟨g, hg⟩

/-- Values of products. -/
theorem eval_mul {f g : K} (hf : f ∈ P.1.ring) (hg : g ∈ P.1.ring) :
    P.eval (f * g) (mul_mem hf hg) = P.eval f hf * P.eval g hg :=
  map_mul P.evalHom ⟨f, hf⟩ ⟨g, hg⟩

/-- Values of powers. -/
theorem eval_pow {f : K} (hf : f ∈ P.1.ring) (n : ℕ) :
    P.eval (f ^ n) (pow_mem hf n) = P.eval f hf ^ n :=
  map_pow P.evalHom ⟨f, hf⟩ n

/-- A regular function vanishes at a place exactly when it is zero or its inverse is not
regular. -/
theorem eval_eq_zero_iff {f : K} (hf : f ∈ P.1.ring) :
    P.eval f hf = 0 ↔ f = 0 ∨ f⁻¹ ∉ P.1.ring := by
  have h : P.eval f hf = P.residueEquiv.symm (IsLocalRing.residue P.1.ring ⟨f, hf⟩) := rfl
  rw [h, map_eq_zero_iff _ P.residueEquiv.symm.injective, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Place.isUnit_iff_inv_mem, not_and_or,
    not_not]

/-- The inverse of a function with a pole is regular. -/
theorem inv_mem_of_not_mem {f : K} (hf : f ∉ P.1.ring) : f⁻¹ ∈ P.1.ring :=
  (P.1.ring.mem_or_inv_mem f).resolve_left hf

/-- The inverse of a function with a pole vanishes. -/
theorem eval_inv_of_not_mem {f : K} (hf : f ∉ P.1.ring) :
    P.eval f⁻¹ (inv_mem_of_not_mem hf) = 0 :=
  (eval_eq_zero_iff _).mpr (Or.inr (by rwa [inv_inv]))

/-- The inverse of a function with a nonzero value is regular. -/
theorem inv_mem_of_eval_ne_zero {f : K} (hf : f ∈ P.1.ring) (h : P.eval f hf ≠ 0) :
    f⁻¹ ∈ P.1.ring := by
  rw [Ne, eval_eq_zero_iff, not_or, not_not] at h
  exact h.2

/-- The value of an inverse. -/
theorem eval_inv {f : K} (hf : f ∈ P.1.ring) (h : P.eval f hf ≠ 0) :
    P.eval f⁻¹ (inv_mem_of_eval_ne_zero hf h) = (P.eval f hf)⁻¹ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact h eval_zero
  refine (eq_inv_of_mul_eq_one_right ?_)
  rw [← eval_mul, eval_congr (mul_inv_cancel₀ hf0), eval_one]

/-- A function whose square is regular is regular (valuation rings are integrally closed). -/
theorem mem_of_sq_mem {f : K} (h : f ^ 2 ∈ P.1.ring) : f ∈ P.1.ring := by
  by_contra hf
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf P.1.ring.zero_mem
  apply hf
  have := mul_mem h (inv_mem_of_not_mem hf)
  rwa [sq, mul_assoc, mul_inv_cancel₀ hf0, mul_one] at this

/-! ### Values, compositionally -/

variable (P) in
/-- `f` is regular at `P` with value `c`. -/
def HasValue (f : K) (c : F) : Prop :=
  ∃ hf : f ∈ P.1.ring, P.eval f hf = c

/-- The definition of `HasValue`. -/
theorem hasValue_iff {f : K} {c : F} : P.HasValue f c ↔ ∃ hf : f ∈ P.1.ring, P.eval f hf = c :=
  Iff.rfl

/-- A constant has its own value. -/
theorem hasValue_algebraMap (c : F) : P.HasValue (algebraMap F K c) c :=
  ⟨P.1.algebraMap_mem c, eval_algebraMap P c⟩

/-- `1` has value `1`. -/
theorem hasValue_one : P.HasValue (1 : K) 1 :=
  ⟨P.1.ring.one_mem, eval_one⟩

namespace HasValue

variable {f g : K} {c c' : F}

/-- Transport of a value along equalities. -/
theorem congr (h : P.HasValue f c) (hfg : f = g) (hc : c = c') : P.HasValue g c' := by
  subst hfg hc; exact h

/-- Values of sums. -/
theorem add (hf : P.HasValue f c) (hg : P.HasValue g c') : P.HasValue (f + g) (c + c') := by
  obtain ⟨hf, rfl⟩ := hf; obtain ⟨hg, rfl⟩ := hg; exact ⟨_, eval_add hf hg⟩

/-- Values of differences. -/
theorem sub (hf : P.HasValue f c) (hg : P.HasValue g c') : P.HasValue (f - g) (c - c') := by
  obtain ⟨hf, rfl⟩ := hf; obtain ⟨hg, rfl⟩ := hg; exact ⟨_, eval_sub hf hg⟩

/-- Values of negatives. -/
theorem neg (hf : P.HasValue f c) : P.HasValue (-f) (-c) := by
  obtain ⟨hf, rfl⟩ := hf; exact ⟨neg_mem hf, map_neg P.evalHom ⟨f, hf⟩⟩

/-- Values of products. -/
theorem mul (hf : P.HasValue f c) (hg : P.HasValue g c') : P.HasValue (f * g) (c * c') := by
  obtain ⟨hf, rfl⟩ := hf; obtain ⟨hg, rfl⟩ := hg; exact ⟨_, eval_mul hf hg⟩

/-- Values of powers. -/
theorem pow (hf : P.HasValue f c) (n : ℕ) : P.HasValue (f ^ n) (c ^ n) := by
  obtain ⟨hf, rfl⟩ := hf; exact ⟨_, eval_pow hf n⟩

/-- Values of inverses, at a nonzero value. -/
theorem inv (hf : P.HasValue f c) (hc : c ≠ 0) : P.HasValue f⁻¹ c⁻¹ := by
  obtain ⟨hf, rfl⟩ := hf; exact ⟨_, eval_inv hf hc⟩

/-- Values of quotients, at a nonzero value of the denominator. -/
theorem div (hf : P.HasValue f c) (hg : P.HasValue g c') (hc : c' ≠ 0) :
    P.HasValue (f / g) (c / c') := by
  simpa only [div_eq_mul_inv] using hf.mul (hg.inv hc)

/-- Values are unique. -/
theorem unique (h : P.HasValue f c) (h' : P.HasValue f c') : c = c' := by
  obtain ⟨hf, rfl⟩ := h; obtain ⟨hf', rfl⟩ := h'; rfl

/-- A regular function has a value. -/
theorem of_mem (hf : f ∈ P.1.ring) : P.HasValue f (P.eval f hf) :=
  ⟨hf, rfl⟩

/-- A function with a value is regular. -/
theorem mem (h : P.HasValue f c) : f ∈ P.1.ring :=
  h.1

/-- The value of `f` from that of `f²`. -/
theorem of_sq (h : P.HasValue (f ^ 2) c) : ∃ c', P.HasValue f c' ∧ c' ^ 2 = c := by
  obtain ⟨h2, rfl⟩ := h
  have hf := mem_of_sq_mem h2
  exact ⟨_, ⟨hf, rfl⟩, (eval_pow hf 2).symm⟩

/-- A function with a nonzero value is nonzero. -/
theorem ne_zero (h : P.HasValue f c) (hc : c ≠ 0) : f ≠ 0 := by
  rintro rfl
  exact hc (h.unique ((hasValue_algebraMap (P := P) 0).congr (map_zero _) rfl))

/-- A function whose square vanishes vanishes. -/
theorem of_sq_zero (h : P.HasValue (f ^ 2) 0) : P.HasValue f 0 := by
  obtain ⟨c', h', hc⟩ := h.of_sq
  exact h'.congr rfl (pow_eq_zero_iff two_ne_zero |>.mp hc)

end HasValue

/-- A polynomial in a regular function has the value of the polynomial. -/
theorem HasValue.aeval {f : K} {c : F} (h : P.HasValue f c) (p : Polynomial F) :
    P.HasValue (Polynomial.aeval f p) (p.eval c) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add hq
  | monomial n a =>
    simpa [← Polynomial.C_mul_X_pow_eq_monomial] using (hasValue_algebraMap a).mul (h.pow n)

/-- The inverse of a function with a pole vanishes. -/
theorem hasValue_inv_of_not_mem {f : K} (hf : f ∉ P.1.ring) : P.HasValue f⁻¹ 0 :=
  ⟨_, eval_inv_of_not_mem hf⟩

variable (P)

/-- Values through the maximal ideal: `f` has value `c` when `f - c` is regular and vanishes. -/
theorem hasValue_iff_sub {f : K} {c : F} : P.HasValue f c ↔
    f - algebraMap F K c ∈ P.1.ring ∧
      (f - algebraMap F K c = 0 ∨ (f - algebraMap F K c)⁻¹ ∉ P.1.ring) := by
  constructor
  · intro h
    have h0 := h.sub (hasValue_algebraMap c)
    rw [sub_self] at h0
    obtain ⟨hm, he⟩ := h0
    exact ⟨hm, (eval_eq_zero_iff hm).mp he⟩
  · rintro ⟨hm, h0⟩
    have h1 : P.HasValue (f - algebraMap F K c) 0 := ⟨hm, (eval_eq_zero_iff hm).mpr h0⟩
    have := h1.add (hasValue_algebraMap c)
    rwa [sub_add_cancel, zero_add] at this

/-- The bijection of rational places along an `F`-isomorphism of fields. -/
def congr (e : K ≃ₐ[F] K') : RationalPlace F K' ≃ RationalPlace F K where
  toFun P := ⟨P.1.comap e, P.2.comap e⟩
  invFun P := ⟨P.1.comap e.symm, P.2.comap e.symm⟩
  left_inv P := Subtype.ext (by
    change (P.1.comap e).comap e.symm = P.1
    rw [Place.comap_comap]
    ext z
    simp)
  right_inv P := Subtype.ext (by
    change (P.1.comap e.symm).comap e = P.1
    rw [Place.comap_comap]
    ext z
    simp)

/-- Membership in the place pulled back along an isomorphism. -/
theorem congr_apply_ring (e : K ≃ₐ[F] K') (P : RationalPlace F K') (z : K) :
    z ∈ (congr e P).1.ring ↔ e z ∈ P.1.ring :=
  Iff.rfl

/-- Values along an isomorphism: `z` has value `c` at the pulled-back place exactly when `e z` has
value `c`. -/
theorem hasValue_congr_iff (e : K ≃ₐ[F] K') (P : RationalPlace F K') {z : K} {c : F} :
    (congr e P).HasValue z c ↔ P.HasValue (e z) c := by
  rw [hasValue_iff_sub, hasValue_iff_sub, congr_apply_ring, congr_apply_ring, map_sub,
    AlgEquiv.commutes, map_inv₀, map_sub, AlgEquiv.commutes]
  have : z - algebraMap F K c = 0 ↔ e z - algebraMap F K' c = 0 := by
    rw [← AlgEquiv.commutes e c, ← map_sub, map_eq_zero_iff _ e.injective]
  rw [this]

end FunctionField.RationalPlace
