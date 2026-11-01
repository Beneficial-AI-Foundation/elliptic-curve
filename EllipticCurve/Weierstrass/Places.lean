/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Weierstrass.Coordinates
import EllipticCurve.Weierstrass.Affine
import EllipticCurve.Weierstrass.Infinity
import EllipticCurve.Weierstrass.Iso
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # The places of a Weierstrass curve

Two statements:

* **(A-W)** `exists_pointEquivRationalPlace`: the points of an elliptic curve are the rational
  places of its function field; an affine point `(x₀, y₀)` is the place where `x` and `y` take
  the values `x₀`, `y₀` (`EllipticCurve.Weierstrass.Affine`), and `0` is the place where
  `x` has a pole (`EllipticCurve.Weierstrass.Infinity`).
* **(B-W)** `exists_variableChange_of_algEquiv` (away from 2): an `F`-isomorphism of the
  function fields of two elliptic curves that matches their places at infinity is induced by a
  change of variables, so the bijection of points it induces is a group isomorphism
  (`pointMapOfAlgEquiv_add`). It uses that the coordinate ring is integrally closed
  (`EllipticCurve.Weierstrass.Normal`).

The point–place dictionary `W.pointEquivRationalPlace` is chosen by (A-W). -/

public section

universe u

open Polynomial

namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] (W : WeierstrassCurve.Affine F)

/-! ### Points and places: (A-W) -/

/-- **(A-W)** The points of an elliptic curve are the rational places of its function field: an
affine point `(x₀, y₀)` is the place where `x` and `y` are regular with values `x₀`, `y₀`, and the
point at infinity is the place where `x` has a pole.

## Provenance

The proof follows the route of `placeEquiv` in lana-agents/elliptic-curves
(`EllipticCurve/FunctionField/Places.lean`, Apache-2.0): split on whether `x` is regular. At the
affine points the local ring is a discrete valuation ring (`WeierstrassCurve.Affine.localRing`);
the place at infinity is unique by a valuation computation in the norm degree
(`WeierstrassCurve.Affine.div_mem_iff`), in the spirit of TauCeti's
`…/FunctionField/InfinityPlace/Unique.lean`. -/
theorem exists_pointEquivRationalPlace [W.IsElliptic] :
    ∃ e : W.Point ≃ FunctionField.RationalPlace F W.FunctionField,
      (∀ (x₀ y₀ : F) (h : W.Nonsingular x₀ y₀),
        ∃ (hx : W.fieldX ∈ (e (.some x₀ y₀ h)).1.ring) (hy : W.fieldY ∈ (e (.some x₀ y₀ h)).1.ring),
          (e (.some x₀ y₀ h)).eval _ hx = x₀ ∧ (e (.some x₀ y₀ h)).eval _ hy = y₀) ∧
      W.fieldX ∉ (e 0).1.ring := by
  classical
  open FunctionField.RationalPlace in
  obtain ⟨O, hO, hx⟩ := W.exists_valuationSubring_fieldX_not_mem
  have hne : O ≠ ⊤ := fun h => hx (h ▸ ValuationSubring.mem_top _)
  let Pinf : FunctionField.RationalPlace F W.FunctionField :=
    ⟨⟨O, hO, hne⟩, (FunctionField.Place.isRational_iff _).mpr fun _ hz =>
      exists_eq_or_inv_not_mem hO hx hz⟩
  let f : W.Point → FunctionField.RationalPlace F W.FunctionField
    | .zero => Pinf
    | .some x y h => pointRationalPlace h
  have hinj : Function.Injective f := by
    rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hPQ
    · rfl
    · change Pinf = pointRationalPlace h' at hPQ
      have := (hasValue_fieldX h').mem
      rw [← hPQ] at this
      exact absurd this hx
    · change pointRationalPlace h = Pinf at hPQ
      have := (hasValue_fieldX h).mem
      rw [hPQ] at this
      exact absurd this hx
    · change pointRationalPlace h = pointRationalPlace h' at hPQ
      have hx' := hasValue_fieldX h'
      have hy' := hasValue_fieldY h'
      rw [← hPQ] at hx' hy'
      have ex := (hasValue_fieldX h).unique hx'
      have ey := (hasValue_fieldY h).unique hy'
      subst ex ey
      rfl
  have hsurj : Function.Surjective f := by
    intro P
    by_cases hxP : W.fieldX ∈ P.1.ring
    · have hyP := fieldY_mem_of_fieldX_mem hxP
      have hns := (W.equation_iff_nonsingular).mp
        (equation_of_hasValue (FunctionField.RationalPlace.HasValue.of_mem hxP)
          (FunctionField.RationalPlace.HasValue.of_mem hyP))
      exact ⟨.some _ _ hns, (eq_pointRationalPlace hns
        (FunctionField.RationalPlace.HasValue.of_mem hxP)
        (FunctionField.RationalPlace.HasValue.of_mem hyP)).symm⟩
    · exact ⟨0, Subtype.ext (FunctionField.Place.ext
        (eq_of_fieldX_not_mem hO hx P.1.algebraMap_mem hxP))⟩
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun x₀ y₀ h => ?_, hx⟩
  obtain ⟨hx', ex⟩ := FunctionField.RationalPlace.hasValue_iff.mp (hasValue_fieldX h)
  obtain ⟨hy', ey⟩ := FunctionField.RationalPlace.hasValue_iff.mp (hasValue_fieldY h)
  exact ⟨hx', hy', ex, ey⟩

/-- The point–place dictionary of an elliptic curve, chosen by (A-W). -/
noncomputable def pointEquivRationalPlace [W.IsElliptic] :
    W.Point ≃ FunctionField.RationalPlace F W.FunctionField :=
  W.exists_pointEquivRationalPlace.choose

/-- The place of an affine point is where `x`, `y` take its coordinates. -/
theorem pointEquivRationalPlace_some [W.IsElliptic] (x₀ y₀ : F) (h : W.Nonsingular x₀ y₀) :
    ∃ (hx : W.fieldX ∈ (W.pointEquivRationalPlace (.some x₀ y₀ h)).1.ring)
      (hy : W.fieldY ∈ (W.pointEquivRationalPlace (.some x₀ y₀ h)).1.ring),
      (W.pointEquivRationalPlace (.some x₀ y₀ h)).eval _ hx = x₀ ∧
        (W.pointEquivRationalPlace (.some x₀ y₀ h)).eval _ hy = y₀ :=
  W.exists_pointEquivRationalPlace.choose_spec.1 x₀ y₀ h

/-- `x` has a pole at the place of `0`. -/
theorem fieldX_not_mem_pointEquivRationalPlace_zero [W.IsElliptic] :
    W.fieldX ∉ (W.pointEquivRationalPlace 0).1.ring :=
  W.exists_pointEquivRationalPlace.choose_spec.2

/-! ### Isomorphisms of function fields: (B-W) -/

variable {W} {W' : WeierstrassCurve.Affine F} [W.IsElliptic] [W'.IsElliptic]

/-- The bijection of points induced by an `F`-isomorphism of function fields. -/
noncomputable def pointMapOfAlgEquiv (e : W.FunctionField ≃ₐ[F] W'.FunctionField) :
    W'.Point ≃ W.Point :=
  W'.pointEquivRationalPlace.trans
    ((FunctionField.RationalPlace.congr e).trans W.pointEquivRationalPlace.symm)

/-- The characterising equation of `pointMapOfAlgEquiv`. -/
theorem pointMapOfAlgEquiv_apply (e : W.FunctionField ≃ₐ[F] W'.FunctionField) (P : W'.Point) :
    pointMapOfAlgEquiv e P = W.pointEquivRationalPlace.symm
      (FunctionField.RationalPlace.congr e (W'.pointEquivRationalPlace P)) := by
  unfold pointMapOfAlgEquiv; rfl

/-- An isomorphism matching the places at infinity maps `x` and `y` into the coordinate ring
(away from 2). -/
theorem exists_algebraMap_eq_of_algEquiv [NeZero (2 : F)]
    (e : W.FunctionField ≃ₐ[F] W'.FunctionField)
    (hmem : ∀ z, z ∈ (W.pointEquivRationalPlace 0).1.ring ↔
      e z ∈ (W'.pointEquivRationalPlace 0).1.ring) :
    (∃ r, algebraMap W'.CoordinateRing W'.FunctionField r = e W.fieldX) ∧
      ∃ r, algebraMap W'.CoordinateRing W'.FunctionField r = e W.fieldY := by
  have hO := (W.pointEquivRationalPlace 0).1.algebraMap_mem
  have hx := W.fieldX_not_mem_pointEquivRationalPlace_zero
  have hx' := W'.fieldX_not_mem_pointEquivRationalPlace_zero
  have key : ∀ z, (z = W.fieldX ∨ z = W.fieldY) → IsIntegral F[X] (e z) := by
    intro z hz
    refine W'.isIntegral_of_forall_mem fun V hV hxV => ?_
    by_contra hzV
    let U := V.comap e.toRingHom
    have hU : ∀ c : F, algebraMap F W.FunctionField c ∈ U := fun c => by
      change e (algebraMap F _ c) ∈ V
      rw [e.commutes]
      exact hV c
    have hXU : W.fieldX ∉ U := by
      intro hXU
      rcases hz with rfl | rfl
      · exact hzV hXU
      · exact hzV (W.fieldY_mem_of_fieldX_mem' hU hXU)
    have hUO := eq_of_fieldX_not_mem hU hXU hO hx
    apply hx'
    have : e.symm W'.fieldX ∈ U := by
      change e (e.symm _) ∈ V
      rwa [AlgEquiv.apply_symm_apply]
    rw [hUO, hmem, AlgEquiv.apply_symm_apply] at this
    exact this
  exact ⟨W'.exists_algebraMap_eq_of_isIntegral (key _ (.inl rfl)),
    W'.exists_algebraMap_eq_of_isIntegral (key _ (.inr rfl))⟩

open scoped Classical in
/-- **(B-W)** (away from 2). An `F`-isomorphism of the function fields of two elliptic curves
that maps the place at infinity to the place at infinity is induced by a change of variables,
and the bijection of points it induces is the point map of that change of variables.

The proof: `e x` and `e y` are regular wherever `x'` is (by the uniqueness of the place at
infinity), so they lie in the coordinate ring of `W'`, which is integrally closed
(`exists_algebraMap_eq_of_isIntegral`); their norm degrees are `2` and `3`, read off at infinity
(`div_mem_iff`), so they are `u² x' + r` and `u³ y' + u² s x' + t`; substituting them in the
equation of `W` gives `W'` (`variableChange_eq_of_equation`). -/
theorem exists_variableChange_of_algEquiv [NeZero (2 : F)]
    (e : W.FunctionField ≃ₐ[F] W'.FunctionField) (h0 : pointMapOfAlgEquiv e 0 = 0) :
    ∃ (C : VariableChange F) (hC : C • W = W'), ∀ P : W'.Point,
      pointMapOfAlgEquiv e P = Point.equivVariableChange W C (Point.equivOfEq hC.symm P) := by
  have : Module.Finite F[X] W.CoordinateRing := .of_basis (CoordinateRing.basis W)
  have : Module.Finite F[X] W'.CoordinateRing := .of_basis (CoordinateRing.basis W')
  -- the places at infinity correspond
  have hcongr : FunctionField.RationalPlace.congr e (W'.pointEquivRationalPlace 0) =
      W.pointEquivRationalPlace 0 := by
    have := congrArg W.pointEquivRationalPlace h0
    simpa [pointMapOfAlgEquiv] using this
  have hmem : ∀ z, z ∈ (W.pointEquivRationalPlace 0).1.ring ↔
      e z ∈ (W'.pointEquivRationalPlace 0).1.ring := fun z => by
    rw [← hcongr, FunctionField.RationalPlace.congr_apply_ring]
  have hmem' : ∀ z, z ∈ (W'.pointEquivRationalPlace 0).1.ring ↔
      e.symm z ∈ (W.pointEquivRationalPlace 0).1.ring := fun z => by
    rw [hmem, AlgEquiv.apply_symm_apply]
  have hO := (W.pointEquivRationalPlace 0).1.algebraMap_mem
  have hO' := (W'.pointEquivRationalPlace 0).1.algebraMap_mem
  have hx := W.fieldX_not_mem_pointEquivRationalPlace_zero
  have hx' := W'.fieldX_not_mem_pointEquivRationalPlace_zero
  obtain ⟨⟨rX, hrX⟩, ⟨rY, hrY⟩⟩ := exists_algebraMap_eq_of_algEquiv e hmem
  obtain ⟨⟨sX, hsX⟩, ⟨sY, hsY⟩⟩ := exists_algebraMap_eq_of_algEquiv e.symm hmem'
  -- norm degrees, read off at infinity
  have dm := fun f g (hg : g ≠ 0) => div_mem_iff (W.pointEquivRationalPlace 0).1.ring hO hx
    (f := f) (g := g) hg
  have dm' := fun f g (hg : g ≠ 0) => div_mem_iff (W'.pointEquivRationalPlace 0).1.ring hO' hx'
    (f := f) (g := g) hg
  have hmX : ∀ (V : WeierstrassCurve.Affine F), CoordinateRing.mk V (C X) ≠ 0 := fun V h => by
    apply V.aeval_fieldX_ne_zero (p := X) X_ne_zero
    rw [aeval_fieldX, h, map_zero]
  have hmY : ∀ (V : WeierstrassCurve.Affine F), CoordinateRing.mk V X ≠ 0 := fun V h => by
    apply V.fieldY_ne_zero; rw [fieldY_def, h, map_zero]
  have hne : ∀ r : W'.CoordinateRing, algebraMap _ W'.FunctionField r ≠ 0 → r ≠ 0 :=
    fun r hr h0 => hr (by rw [h0, map_zero])
  have hneW : ∀ r : W.CoordinateRing, algebraMap _ W.FunctionField r ≠ 0 → r ≠ 0 :=
    fun r hr h0 => hr (by rw [h0, map_zero])
  have hX0 : W.fieldX ≠ 0 := by simpa using W.aeval_fieldX_ne_zero (p := X) X_ne_zero
  have hX0' : W'.fieldX ≠ 0 := by simpa using W'.aeval_fieldX_ne_zero (p := X) X_ne_zero
  have hrX0 : rX ≠ 0 := hne _ (by rw [hrX]; exact (_root_.map_ne_zero _).mpr hX0)
  have hrY0 : rY ≠ 0 := hne _ (by rw [hrY]; exact (_root_.map_ne_zero _).mpr W.fieldY_ne_zero)
  have hsX0 : sX ≠ 0 := hneW _ (by rw [hsX]; exact (_root_.map_ne_zero _).mpr hX0')
  set dX := (Algebra.norm F[X] rX).natDegree
  set dY := (Algebra.norm F[X] rY).natDegree
  set dS := (Algebra.norm F[X] sX).natDegree
  -- `x³ / y²` is a unit at infinity, so `3 deg(e x) = 2 deg(e y)`
  have e1 : e (algebraMap _ _ (CoordinateRing.mk W (C X) ^ 3) /
      algebraMap _ _ (CoordinateRing.mk W X ^ 2)) =
        algebraMap _ _ (rX ^ 3) / algebraMap _ _ (rY ^ 2) := by
    simp only [map_pow, map_div₀, ← fieldX_def, ← fieldY_def, hrX, hrY]
  have e2 : e (algebraMap _ _ (CoordinateRing.mk W X ^ 2) /
      algebraMap _ _ (CoordinateRing.mk W (C X) ^ 3)) =
        algebraMap _ _ (rY ^ 2) / algebraMap _ _ (rX ^ 3) := by
    simp only [map_pow, map_div₀, ← fieldX_def, ← fieldY_def, hrX, hrY]
  have h32 : 3 * dX = 2 * dY := by
    have a := (dm (CoordinateRing.mk W (C X) ^ 3) _ (pow_ne_zero 2 (hmY W))).mpr (by
      rw [natDegree_norm_pow, natDegree_norm_pow, natDegree_norm_X, natDegree_norm_Y])
    have b := (dm (CoordinateRing.mk W X ^ 2) _ (pow_ne_zero 3 (hmX W))).mpr (by
      rw [natDegree_norm_pow, natDegree_norm_pow, natDegree_norm_X, natDegree_norm_Y])
    rw [hmem, e1, dm' _ _ (pow_ne_zero 2 hrY0), natDegree_norm_pow, natDegree_norm_pow] at a
    rw [hmem, e2, dm' _ _ (pow_ne_zero 3 hrX0), natDegree_norm_pow, natDegree_norm_pow] at b
    omega
  -- `x` has a pole at infinity, so `deg(e x) ≠ 0`
  have hdX : dX ≠ 0 := by
    intro h
    apply hx
    rw [hmem, ← hrX, ← div_one (algebraMap _ _ rX), ← map_one (algebraMap W'.CoordinateRing _),
      dm' _ _ one_ne_zero, map_one, natDegree_one]
    exact h.le
  have hdS : dS ≠ 0 := by
    intro h
    apply hx'
    rw [hmem', ← hsX, ← div_one (algebraMap _ _ sX), ← map_one (algebraMap W.CoordinateRing _),
      dm _ _ one_ne_zero, map_one, natDegree_one]
    exact h.le
  -- the same for `e⁻¹`
  have h32' : 3 * dS = 2 * (Algebra.norm F[X] sY).natDegree := by
    have hsY0 : sY ≠ 0 := hneW _ (by rw [hsY]; exact (_root_.map_ne_zero _).mpr W'.fieldY_ne_zero)
    have e1' : e.symm (algebraMap _ _ (CoordinateRing.mk W' (C X) ^ 3) /
        algebraMap _ _ (CoordinateRing.mk W' X ^ 2)) =
          algebraMap _ _ (sX ^ 3) / algebraMap _ _ (sY ^ 2) := by
      simp only [map_pow, map_div₀, ← fieldX_def, ← fieldY_def, hsX, hsY]
    have e2' : e.symm (algebraMap _ _ (CoordinateRing.mk W' X ^ 2) /
        algebraMap _ _ (CoordinateRing.mk W' (C X) ^ 3)) =
          algebraMap _ _ (sY ^ 2) / algebraMap _ _ (sX ^ 3) := by
      simp only [map_pow, map_div₀, ← fieldX_def, ← fieldY_def, hsX, hsY]
    have a := (dm' (CoordinateRing.mk W' (C X) ^ 3) _ (pow_ne_zero 2 (hmY W'))).mpr (by
      rw [natDegree_norm_pow, natDegree_norm_pow, natDegree_norm_X, natDegree_norm_Y])
    have b := (dm' (CoordinateRing.mk W' X ^ 2) _ (pow_ne_zero 3 (hmX W'))).mpr (by
      rw [natDegree_norm_pow, natDegree_norm_pow, natDegree_norm_X, natDegree_norm_Y])
    rw [hmem', e1', dm _ _ (pow_ne_zero 2 hsY0), natDegree_norm_pow, natDegree_norm_pow] at a
    rw [hmem', e2', dm _ _ (pow_ne_zero 3 hsX0), natDegree_norm_pow, natDegree_norm_pow] at b
    omega
  -- `x^k' / e⁻¹(x')` is a unit at infinity, so `k' deg(e x) = 2`
  obtain ⟨k', hk'⟩ : ∃ k', dS = 2 * k' := ⟨dS / 2, by omega⟩
  have e3 : e (algebraMap _ _ (CoordinateRing.mk W (C X) ^ k') / algebraMap _ _ sX) =
      algebraMap _ _ (rX ^ k') / algebraMap _ _ (CoordinateRing.mk W' (C X)) := by
    simp only [map_pow, map_div₀, ← fieldX_def, hrX, hsX, AlgEquiv.apply_symm_apply]
  have e4 : e (algebraMap _ _ sX / algebraMap _ _ (CoordinateRing.mk W (C X) ^ k')) =
      algebraMap _ _ (CoordinateRing.mk W' (C X)) / algebraMap _ _ (rX ^ k') := by
    simp only [map_pow, map_div₀, ← fieldX_def, hrX, hsX, AlgEquiv.apply_symm_apply]
  have hdX2 : dX = 2 := by
    have a := (dm (CoordinateRing.mk W (C X) ^ k') _ hsX0).mpr (by
      rw [natDegree_norm_pow, natDegree_norm_X]; omega)
    have b := (dm sX _ (pow_ne_zero k' (hmX W))).mpr (by
      rw [natDegree_norm_pow, natDegree_norm_X]; omega)
    rw [hmem, e3, dm' _ _ (hmX W'), natDegree_norm_pow, natDegree_norm_X] at a
    rw [hmem, e4, dm' _ _ (pow_ne_zero k' hrX0), natDegree_norm_pow, natDegree_norm_X] at b
    have : k' * dX = 2 := le_antisymm a b
    rcases Nat.even_or_odd dX with ⟨m, hm⟩ | ⟨m, hm⟩ <;> [skip; omega]
    have : k' * m = 1 := by nlinarith
    have hm1 : m ∣ 1 := ⟨k', by rw [mul_comm]; exact this.symm⟩
    rw [Nat.dvd_one] at hm1
    omega
  have hdY3 : dY = 3 := by omega
  -- the shapes of `e x` and `e y`
  obtain ⟨c₁, c₀, hc₁, hX'⟩ := exists_eq_of_natDegree_norm_eq_two W' hdX2
  obtain ⟨c, p₁, p₀, hc, hY'⟩ := exists_eq_of_natDegree_norm_eq_three W' hdY3
  rw [hrX] at hX'
  rw [hrY] at hY'
  have heq := congrArg e W.fieldY_equation
  simp only [map_add, map_mul, map_pow, AlgEquiv.commutes, hX', hY'] at heq
  have hcc := sq_eq_cube_of_equation W' heq
  -- the change of variables
  have hu : c / c₁ ≠ 0 := div_ne_zero hc hc₁
  have hu2 : (c / c₁) ^ 2 = c₁ := by
    field_simp; linear_combination hcc
  have hu3 : (c / c₁) ^ 3 = c := by
    field_simp; linear_combination hcc
  have hs : (c / c₁) ^ 2 * (p₁ / (c / c₁) ^ 2) = p₁ := by
    field_simp
  set u := c / c₁
  set s' := p₁ / u ^ 2
  rw [← hu2, ← hu3, ← hs] at heq
  have hC := variableChange_eq_of_equation W' hu heq
  refine ⟨_, hC, fun P => ?_⟩
  cases P with
  | zero =>
    rw [show (Point.zero : W'.Point) = 0 from rfl, h0, Point.equivOfEq_zero,
      Point.equivVariableChange_zero]
  | some x' y' h' =>
    rw [Point.equivOfEq_some, Point.equivVariableChange_some]
    simp only [Units.val_mk0]
    obtain ⟨hx₀, hy₀, ex, ey⟩ := W'.pointEquivRationalPlace_some x' y' h'
    set P' := W'.pointEquivRationalPlace (.some x' y' h')
    have hXv : (FunctionField.RationalPlace.congr e P').HasValue W.fieldX (u ^ 2 * x' + c₀) := by
      rw [FunctionField.RationalPlace.hasValue_congr_iff, hX', ← hu2]
      exact ((FunctionField.RationalPlace.hasValue_algebraMap (P := P') _).mul
        (FunctionField.RationalPlace.hasValue_iff.mpr ⟨hx₀, ex⟩)).add
          (FunctionField.RationalPlace.hasValue_algebraMap _)
    have hYv : (FunctionField.RationalPlace.congr e P').HasValue W.fieldY
        (u ^ 3 * y' + u ^ 2 * s' * x' + p₀) := by
      rw [FunctionField.RationalPlace.hasValue_congr_iff, hY', ← hu3, ← hs]
      exact (((FunctionField.RationalPlace.hasValue_algebraMap (P := P') _).mul
        (FunctionField.RationalPlace.hasValue_iff.mpr ⟨hy₀, ey⟩)).add
          ((FunctionField.RationalPlace.hasValue_algebraMap _).mul
            (FunctionField.RationalPlace.hasValue_iff.mpr ⟨hx₀, ex⟩))).add
              (FunctionField.RationalPlace.hasValue_algebraMap _)
    generalize_proofs hns
    apply W.pointEquivRationalPlace.injective
    change W.pointEquivRationalPlace (W.pointEquivRationalPlace.symm
      (FunctionField.RationalPlace.congr e P')) = _
    rw [Equiv.apply_symm_apply]
    obtain ⟨hx₁, hy₁, ex₁, ey₁⟩ := W.pointEquivRationalPlace_some _ _ hns
    rw [eq_pointRationalPlace hns hXv hYv, eq_pointRationalPlace hns
      (FunctionField.RationalPlace.hasValue_iff.mpr ⟨hx₁, ex₁⟩)
      (FunctionField.RationalPlace.hasValue_iff.mpr ⟨hy₁, ey₁⟩)]

open scoped Classical in
/-- An isomorphism of function fields fixing the point at infinity induces a group isomorphism
of points. -/
theorem pointMapOfAlgEquiv_add [NeZero (2 : F)] (e : W.FunctionField ≃ₐ[F] W'.FunctionField)
    (h0 : pointMapOfAlgEquiv e 0 = 0) (P Q : W'.Point) :
    pointMapOfAlgEquiv e (P + Q) = pointMapOfAlgEquiv e P + pointMapOfAlgEquiv e Q := by
  obtain ⟨C, hC, h⟩ := exists_variableChange_of_algEquiv e h0
  rw [h, h, h, map_add, map_add]

end WeierstrassCurve.Affine
