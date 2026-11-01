/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Curve.Twist
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # The curves with a given j-invariant: the (j, D) classification

Over a field away from 6, the curves with a given j-invariant are classified by a twist datum
`D ∈ Fˣ ⧸ (Fˣ)ⁿ`, where `n = twistExponent j` is `6` at `j = 0`, `4` at `j = 1728` and `2`
otherwise. Here this is a consequence of the weighted description of `Curve F`:

* `Fˣ` acts on curves by **twisting** (`Curve.instMulActionTwist`, a scoped instance: `open Curve`
  to use it): `d` sends the invariants `(c₄, c₆)` to `(d² c₄, d³ c₆)` (the quadratic twist) when
  `c₄ c₆ ≠ 0`, to `(0, d c₆)` (a sextic twist) when `c₄ = 0`, and to `(d c₄, 0)` (a quartic twist)
  when `c₆ = 0` (`smul_eq_quadraticTwist`, `quadraticTwist_eq_smul_of_j_eq_zero`,
  `quadraticTwist_eq_smul_of_j_eq_1728`);
* its orbits are the fibres of `j` (`Curve.mem_orbit_iff_j_eq`), and the stabiliser of a curve is
  the subgroup of `n`-th powers (`Curve.stabilizer_eq`);
* hence, by orbit–stabiliser, `{C // C.j = j} ≃ Fˣ ⧸ (Fˣ)ⁿ` (`Curve.fiberEquiv`), with base
  point the standard curve `Curve.ofJ j`, and
  `Curve F ≃ Σ j : F, Fˣ ⧸ (Fˣ)^{twistExponent j}` (`Curve.equivSigma`): a curve **is** a pair
  `(j, D)`;
* the automorphism group of a curve (the stabiliser of its invariants) is the group of
  `n(j)`-th roots of unity in `F` (`Curve.aut_eq_rootsOfUnity`);
* over a finite field `𝔽_q`, there are `gcd(q - 1, n)` curves with j-invariant `j`
  (`Curve.card_fiber`), and `2 (q - 2) + gcd(q - 1, 6) + gcd(q - 1, 4)` curves in all
  (`Curve.natCard_eq`).

No Galois cohomology is needed: the quotient `Fˣ ⧸ (Fˣ)ⁿ` is the answer over every field away
from 6. -/

public section

universe u

open MulAction

namespace Curve

variable {F : Type u} [Field F]

/-! ### The twist exponent -/

open Classical in
/-- The twist exponent `n(j)`: `6` at `j = 0`, `4` at `j = 1728`, `2` otherwise. Away from 6, it
is the order of the automorphism group of a curve with j-invariant `j` over an algebraic
closure. -/
noncomputable def twistExponent (j : F) : ℕ :=
  if j = 0 then 6 else if j = 1728 then 4 else 2

/-- `n(0) = 6`. -/
theorem twistExponent_zero : twistExponent (0 : F) = 6 := by
  simp [twistExponent]

/-- `n(1728) = 4` away from 6. -/
theorem twistExponent_1728 [NeZero (6 : F)] : twistExponent (1728 : F) = 4 := by
  simp [twistExponent, ne_zero_1728_of_six]

/-- `n(j) = 2` for `j ≠ 0, 1728`. -/
theorem twistExponent_of_ne {j : F} (h₀ : j ≠ 0) (h₁ : j ≠ 1728) : twistExponent j = 2 := by
  simp [twistExponent, h₀, h₁]

/-! ### Twisting at the level of invariants -/

namespace Invariants

/-- At `c₄ = 0` (j-invariant `0`), `c₆ ≠ 0`. -/
theorem c₆_ne_zero_of_c₄_eq_zero {p : Invariants F} (h : p.c₄ = 0) : p.c₆ ≠ 0 :=
  fun h' => p.disc_ne_zero (by simp [h, h'])

/-- At `c₆ = 0` (j-invariant `1728`), `c₄ ≠ 0`. -/
theorem c₄_ne_zero_of_c₆_eq_zero {p : Invariants F} (h : p.c₆ = 0) : p.c₄ ≠ 0 :=
  fun h' => p.disc_ne_zero (by simp [h, h'])

open Classical in
/-- Twisting the invariants by `d`: `(0, d c₆)`, `(d c₄, 0)` or `(d² c₄, d³ c₆)` according as
`c₄ = 0`, `c₆ = 0` or neither. -/
noncomputable def twist (d : Fˣ) (p : Invariants F) : Invariants F :=
  if h₄ : p.c₄ = 0 then
    ⟨0, d * p.c₆, by simpa [d.ne_zero] using c₆_ne_zero_of_c₄_eq_zero h₄⟩
  else if p.c₆ = 0 then
    ⟨d * p.c₄, 0, by simpa [d.ne_zero] using h₄⟩
  else
    ⟨d ^ 2 * p.c₄, d ^ 3 * p.c₆, by
      have h : ((d : F) ^ 2 * p.c₄) ^ 3 - (d ^ 3 * p.c₆) ^ 2 = d ^ 6 * (p.c₄ ^ 3 - p.c₆ ^ 2) := by
        ring
      rw [h]
      exact mul_ne_zero (pow_ne_zero _ d.ne_zero) p.disc_ne_zero⟩

open Classical in
/-- The twist exponent of the stratum of `p`: `6`, `4` or `2` according as `c₄ = 0`, `c₆ = 0` or
neither. -/
noncomputable def twistExponent (p : Invariants F) : ℕ :=
  if p.c₄ = 0 then 6 else if p.c₆ = 0 then 4 else 2

/-- Twisting commutes with the weighted action. -/
theorem twist_smul (d u : Fˣ) (p : Invariants F) : (u • p).twist d = u • p.twist d := by
  have hu := u.ne_zero
  by_cases h₄ : p.c₄ = 0
  · ext <;> simp [twist, h₄]; ring
  by_cases h₆ : p.c₆ = 0
  · ext <;> simp [twist, h₄, h₆, hu]; ring
  · ext <;> simp [twist, h₄, h₆, hu] <;> ring

/-- Twisting by `1` does nothing. -/
theorem twist_one (p : Invariants F) : p.twist 1 = p := by
  by_cases h₄ : p.c₄ = 0
  · ext <;> simp [twist, h₄]
  by_cases h₆ : p.c₆ = 0
  · ext <;> simp [twist, h₄, h₆]
  · ext <;> simp [twist, h₄, h₆]

/-- Twisting is an action: twisting by `d e` is twisting by `e`, then by `d`. -/
theorem twist_mul (d e : Fˣ) (p : Invariants F) : p.twist (d * e) = (p.twist e).twist d := by
  have he := e.ne_zero
  by_cases h₄ : p.c₄ = 0
  · ext <;> simp [twist, h₄]; ring
  by_cases h₆ : p.c₆ = 0
  · ext <;> simp [twist, h₄, h₆, he]; ring
  · ext <;> simp [twist, h₄, h₆, he] <;> ring

/-- The stratum, hence the twist exponent, is unchanged by the weighted action. -/
theorem twistExponent_smul (u : Fˣ) (p : Invariants F) :
    (u • p).twistExponent = p.twistExponent := by
  have hu := u.ne_zero
  unfold twistExponent
  split_ifs <;> simp_all

/-- `p.twist d` is in the orbit of `p` if and only if `d` is an `n`-th power. -/
theorem exists_smul_eq_twist_iff (d : Fˣ) (p : Invariants F) :
    (∃ u : Fˣ, u • p = p.twist d) ↔ ∃ k : Fˣ, k ^ p.twistExponent = d := by
  by_cases h₄ : p.c₄ = 0
  · have h₆ := c₆_ne_zero_of_c₄_eq_zero h₄
    simp only [twistExponent, h₄, ite_true]
    constructor
    · rintro ⟨u, hu⟩
      have e : (u : F) ^ 6 * p.c₆ = d * p.c₆ := by
        simpa [twist, h₄] using congrArg Invariants.c₆ hu
      exact ⟨u, Units.ext (by simpa using mul_right_cancel₀ h₆ e)⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, by ext <;> simp [twist, h₄]⟩
  by_cases h₆ : p.c₆ = 0
  · simp only [twistExponent, h₄, h₆, ite_true, ite_false]
    constructor
    · rintro ⟨u, hu⟩
      have e : (u : F) ^ 4 * p.c₄ = d * p.c₄ := by
        simpa [twist, h₄, h₆] using congrArg Invariants.c₄ hu
      exact ⟨u, Units.ext (by simpa using mul_right_cancel₀ h₄ e)⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, by ext <;> simp [twist, h₄, h₆]⟩
  · simp only [twistExponent, h₄, h₆, ite_false]
    constructor
    · rintro ⟨u, hu⟩
      have e₄ : (u : F) ^ 4 * p.c₄ = d ^ 2 * p.c₄ := by
        simpa [twist, h₄, h₆] using congrArg Invariants.c₄ hu
      have e₆ : (u : F) ^ 6 * p.c₆ = d ^ 3 * p.c₆ := by
        simpa [twist, h₄, h₆] using congrArg Invariants.c₆ hu
      replace e₄ := mul_right_cancel₀ h₄ e₄
      replace e₆ := mul_right_cancel₀ h₆ e₆
      refine ⟨u, Units.ext ?_⟩
      have : (d : F) ^ 2 * (d - u ^ 2) = 0 := by
        linear_combination (-1 : F) * e₆ + (u : F) ^ 2 * e₄
      rw [Units.val_pow_eq_pow_val]
      exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left
        (pow_ne_zero _ d.ne_zero))).symm
    · rintro ⟨k, rfl⟩
      exact ⟨k, by ext <;> simp [twist, h₄, h₆] <;> ring⟩

/-- **The automorphisms of a curve**: the stabiliser of its invariants under the weighted
action (the scalings `(x, y) ↦ (u² x, u³ y)` of a short model that preserve it) is the group of
`n`-th roots of unity, `n = 2, 4, 6`. -/
theorem stabilizer_eq_rootsOfUnity (p : Invariants F) :
    stabilizer Fˣ p = rootsOfUnity p.twistExponent F := by
  ext u
  have hu : (u : F) ≠ 0 := u.ne_zero
  rw [mem_stabilizer_iff, mem_rootsOfUnity]
  constructor
  · intro h
    have e₄ : (u : F) ^ 4 * p.c₄ = p.c₄ := congrArg Invariants.c₄ h
    have e₆ : (u : F) ^ 6 * p.c₆ = p.c₆ := congrArg Invariants.c₆ h
    by_cases h₄ : p.c₄ = 0
    · have h₆ := c₆_ne_zero_of_c₄_eq_zero h₄
      simp only [twistExponent, h₄, ite_true]
      exact Units.ext (by simpa using mul_right_cancel₀ h₆ (e₆.trans (one_mul _).symm))
    by_cases h₆ : p.c₆ = 0
    · simp only [twistExponent, h₄, h₆, ite_true, ite_false]
      exact Units.ext (by simpa using mul_right_cancel₀ h₄ (e₄.trans (one_mul _).symm))
    · simp only [twistExponent, h₄, h₆, ite_false]
      have a : (u : F) ^ 4 = 1 := by simpa using mul_right_cancel₀ h₄ (e₄.trans (one_mul _).symm)
      have b : (u : F) ^ 6 = 1 := by simpa using mul_right_cancel₀ h₆ (e₆.trans (one_mul _).symm)
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      linear_combination b - (u : F) ^ 2 * a
  · intro h
    have h' : (u : F) ^ p.twistExponent = 1 := by simpa using congrArg Units.val h
    by_cases h₄ : p.c₄ = 0
    · simp only [twistExponent, h₄, ite_true] at h'
      ext <;> simp [h₄, h']
    by_cases h₆ : p.c₆ = 0
    · simp only [twistExponent, h₄, h₆, ite_true, ite_false] at h'
      ext <;> simp [h₆, h']
    · simp only [twistExponent, h₄, h₆, ite_false] at h'
      ext
      · simp [show (u : F) ^ 4 = 1 by rw [show 4 = 2 * 2 from rfl, pow_mul, h', one_pow]]
      · simp [show (u : F) ^ 6 = 1 by rw [show 6 = 2 * 3 from rfl, pow_mul, h', one_pow]]

end Invariants

/-! ### The twisting action on curves -/

/-- `Fˣ` acts on curves by twisting: quadratic twists by `d` when `j ≠ 0, 1728`, quartic and
sextic twists at `j = 1728` and `j = 0`. -/
noncomputable scoped instance instMulActionTwist : MulAction Fˣ (Curve F) where
  smul d := lift (fun p => ofInvariants (p.twist d)) fun u p => by
    rw [Invariants.twist_smul, ofInvariants_smul]
  one_smul C := C.ind fun p => by
    change lift _ _ (ofInvariants p) = _
    rw [lift_ofInvariants, Invariants.twist_one]
  mul_smul d e C := C.ind fun p => by
    change lift _ _ (ofInvariants p) = lift _ _ (lift _ _ (ofInvariants p))
    simp only [lift_ofInvariants, Invariants.twist_mul]

/-- Twisting a curve twists its invariants. -/
@[simp] theorem smul_ofInvariants (d : Fˣ) (p : Invariants F) :
    d • ofInvariants p = ofInvariants (p.twist d) := by
  change lift _ _ (ofInvariants p) = _
  rw [lift_ofInvariants]

/-- The twist exponent of the stratum of a curve (equal to `twistExponent C.j` away from 6).
Internal. -/
private noncomputable def n : Curve F → ℕ :=
  lift Invariants.twistExponent fun u p => Invariants.twistExponent_smul u p

/-- The twist exponent of the curve with invariants `p` is that of `p`. -/
private theorem n_ofInvariants (p : Invariants F) :
    (ofInvariants p).n = p.twistExponent := by
  simp [n]

/-- The automorphism group of a curve: the stabiliser of its invariants under the weighted action
(independent of the invariants chosen, `Fˣ` being commutative). -/
noncomputable def aut : Curve F → Subgroup Fˣ :=
  lift (fun p => stabilizer Fˣ p) fun u p => by
    ext v
    simp only [mem_stabilizer_iff]
    rw [smul_comm v u]
    exact ⟨fun h => smul_left_cancel u h, fun h => by rw [h]⟩

/-- The automorphism group of the curve with invariants `p` is the stabiliser of `p`. -/
@[simp] theorem aut_ofInvariants (p : Invariants F) : (ofInvariants p).aut = stabilizer Fˣ p := by
  simp [aut]

/-- **The stabiliser** of a curve under twisting is the subgroup of `n`-th powers. -/
private theorem stabilizer_eq_range_n (C : Curve F) :
    stabilizer Fˣ C = (powMonoidHom C.n : Fˣ →* Fˣ).range :=
  C.ind fun p => by
    ext d
    rw [mem_stabilizer_iff, smul_ofInvariants, ofInvariants_eq_ofInvariants_iff,
      MonoidHom.mem_range, n_ofInvariants, Invariants.exists_smul_eq_twist_iff]
    simp [powMonoidHom_apply]

variable [NeZero (6 : F)]

/-- The twist exponent of a curve is that of its j-invariant. -/
private theorem n_eq_twistExponent (C : Curve F) : C.n = twistExponent C.j :=
  C.ind fun p => by
    rw [n_ofInvariants, Invariants.twistExponent, twistExponent, j_ofInvariants_eq_zero_iff,
      j_ofInvariants_eq_1728_iff]

/-- **The automorphism group** of a curve is the group of `n(j)`-th roots of unity in `F`
(`μ₂`, and `μ₄`, `μ₆` at `j = 1728`, `j = 0`). -/
theorem aut_eq_rootsOfUnity (C : Curve F) : C.aut = rootsOfUnity (twistExponent C.j) F := by
  rw [← n_eq_twistExponent]
  exact C.ind fun p => by rw [aut_ofInvariants, n_ofInvariants,
    Invariants.stabilizer_eq_rootsOfUnity]

/-- **The stabiliser** of a curve under twisting is the subgroup of `n(j)`-th powers. -/
theorem stabilizer_eq (C : Curve F) :
    stabilizer Fˣ C = (powMonoidHom (twistExponent C.j) : Fˣ →* Fˣ).range := by
  rw [stabilizer_eq_range_n, n_eq_twistExponent]

omit [NeZero (6 : F)] in
/-- Twisting preserves the j-invariant. -/
@[simp] theorem j_smul (d : Fˣ) (C : Curve F) : (d • C).j = C.j :=
  C.ind fun p => by
    rw [smul_ofInvariants, j_ofInvariants, j_ofInvariants]
    have h1 := (p.twist d).disc_ne_zero
    have h2 := p.disc_ne_zero
    by_cases h₄ : p.c₄ = 0
    · simp [Invariants.twist, h₄]
    by_cases h₆ : p.c₆ = 0
    · simp only [Invariants.twist, h₄, h₆, ↓reduceDIte, ↓reduceIte] at h1 h2 ⊢
      field_simp
      ring
    · simp only [Invariants.twist, h₄, h₆, ↓reduceDIte, ↓reduceIte] at h1 ⊢
      field_simp

/-- Two invariants with the same j-invariant are related by twisting, with an explicit
twisting element. -/
theorem exists_twist_eq {p q : Invariants F} (hj : (ofInvariants p).j = (ofInvariants q).j) :
    ∃ d : Fˣ, p.twist d = q := by
  by_cases h₄ : p.c₄ = 0
  · have h₄' : q.c₄ = 0 :=
      j_ofInvariants_eq_zero_iff.mp (hj ▸ j_ofInvariants_eq_zero_iff.mpr h₄)
    have h₆ := Invariants.c₆_ne_zero_of_c₄_eq_zero h₄
    refine ⟨Units.mk0 (q.c₆ / p.c₆)
      (div_ne_zero (Invariants.c₆_ne_zero_of_c₄_eq_zero h₄') h₆), ?_⟩
    ext <;> simp [Invariants.twist, h₄, h₄', h₆]
  by_cases h₆ : p.c₆ = 0
  · have h₆' : q.c₆ = 0 :=
      j_ofInvariants_eq_1728_iff.mp (hj ▸ j_ofInvariants_eq_1728_iff.mpr h₆)
    refine ⟨Units.mk0 (q.c₄ / p.c₄)
      (div_ne_zero (Invariants.c₄_ne_zero_of_c₆_eq_zero h₆') h₄), ?_⟩
    ext <;> simp [Invariants.twist, h₄, h₆, h₆']
  · have h₄' : q.c₄ ≠ 0 := fun h =>
      h₄ (j_ofInvariants_eq_zero_iff.mp (hj.symm ▸ j_ofInvariants_eq_zero_iff.mpr h))
    have h₆' : q.c₆ ≠ 0 := fun h =>
      h₆ (j_ofInvariants_eq_1728_iff.mp (hj.symm ▸ j_ofInvariants_eq_1728_iff.mpr h))
    have key : p.c₄ ^ 3 * q.c₆ ^ 2 = q.c₄ ^ 3 * p.c₆ ^ 2 := by
      rw [j_ofInvariants, j_ofInvariants, div_eq_div_iff p.disc_ne_zero q.disc_ne_zero] at hj
      have : (1728 : F) * (p.c₄ ^ 3 * q.c₆ ^ 2 - q.c₄ ^ 3 * p.c₆ ^ 2) = 0 := by
        linear_combination -hj
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ne_zero_1728_of_six)
    refine ⟨Units.mk0 (q.c₆ * p.c₄ / (p.c₆ * q.c₄))
      (div_ne_zero (mul_ne_zero h₆' h₄) (mul_ne_zero h₆ h₄')), ?_⟩
    ext <;> simp [Invariants.twist, h₄, h₆] <;> field_simp <;> linear_combination key

/-- **The orbits** of twisting are the fibres of `j`. -/
theorem mem_orbit_iff_j_eq {C C' : Curve F} : C' ∈ orbit Fˣ C ↔ C'.j = C.j := by
  induction C using ind with | h p =>
  induction C' using ind with | h q =>
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨d, hd⟩
    rw [← hd, j_smul]
  · intro h
    obtain ⟨d, hd⟩ := exists_twist_eq h.symm
    exact ⟨d, by rw [smul_ofInvariants, hd]⟩

/-- The curves with the j-invariant of `C`, as `Fˣ` modulo the stabiliser of `C`. -/
noncomputable def fiberEquivOfBase (C : Curve F) :
    {C' : Curve F // C'.j = C.j} ≃ Fˣ ⧸ (powMonoidHom (twistExponent C.j) : Fˣ →* Fˣ).range :=
  (Equiv.subtypeEquivRight fun _ => mem_orbit_iff_j_eq.symm).trans <|
    (orbitEquivQuotientStabilizer Fˣ C).trans (Subgroup.quotientEquivOfEq (stabilizer_eq C))

/-- Away from `j = 0, 1728`, twisting is the quadratic twist. -/
theorem smul_eq_quadraticTwist (d : Fˣ) {C : Curve F} (h₀ : C.j ≠ 0) (h₁ : C.j ≠ 1728) :
    d • C = C.quadraticTwist d := by
  induction C using ind with | h p =>
  have h₄ : p.c₄ ≠ 0 := fun h => h₀ (j_ofInvariants_eq_zero_iff.mpr h)
  have h₆ : p.c₆ ≠ 0 := fun h => h₁ (j_ofInvariants_eq_1728_iff.mpr h)
  rw [smul_ofInvariants, quadraticTwist_ofInvariants]
  congr 1
  ext <;> simp [Invariants.twist, h₄, h₆]

/-- At `j = 0`, the quadratic twist by `d` is the sextic twist by `d³`. -/
theorem quadraticTwist_eq_smul_of_j_eq_zero (d : Fˣ) {C : Curve F} (h₀ : C.j = 0) :
    C.quadraticTwist d = d ^ 3 • C := by
  induction C using ind with | h p =>
  have h₄ : p.c₄ = 0 := j_ofInvariants_eq_zero_iff.mp h₀
  rw [smul_ofInvariants, quadraticTwist_ofInvariants]
  congr 1
  ext <;> simp [Invariants.twist, h₄]

/-- At `j = 1728`, the quadratic twist by `d` is the quartic twist by `d²`. -/
theorem quadraticTwist_eq_smul_of_j_eq_1728 (d : Fˣ) {C : Curve F} (h₁ : C.j = 1728) :
    C.quadraticTwist d = d ^ 2 • C := by
  induction C using ind with | h p =>
  have h₆ : p.c₆ = 0 := j_ofInvariants_eq_1728_iff.mp h₁
  have h₄ : p.c₄ ≠ 0 := Invariants.c₄_ne_zero_of_c₆_eq_zero h₆
  rw [smul_ofInvariants, quadraticTwist_ofInvariants]
  congr 1
  ext <;> simp [Invariants.twist, h₄, h₆]

/-- **A quadratic twist is a different curve** exactly when `d` is not a square, for
`j ≠ 0, 1728`. -/
theorem quadraticTwist_eq_self_iff (d : Fˣ) {C : Curve F} (h₀ : C.j ≠ 0) (h₁ : C.j ≠ 1728) :
    C.quadraticTwist d = C ↔ IsSquare (d : F) := by
  rw [← smul_eq_quadraticTwist d h₀ h₁, ← mem_stabilizer_iff, stabilizer_eq,
    twistExponent_of_ne h₀ h₁, MonoidHom.mem_range]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp [sq]⟩
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by rintro rfl; simp at hr
    exact ⟨Units.mk0 r hr0, Units.ext (by simp [sq, hr])⟩

/-! ### The standard curves and the classification -/

/-- The invariants `(t, t)`, `t = j / (j - 1728)`, of the standard curve are nondegenerate. -/
theorem disc_ofJ_ne_zero {j : F} (h₀ : j ≠ 0) (h₁ : j ≠ 1728) :
    (j / (j - 1728)) ^ 3 - (j / (j - 1728)) ^ 2 ≠ 0 := by
  have h : j - 1728 ≠ 0 := sub_ne_zero.mpr h₁
  have e : (j / (j - 1728)) ^ 3 - (j / (j - 1728)) ^ 2 = 1728 * j ^ 2 / (j - 1728) ^ 3 := by
    field_simp
    ring
  rw [e]
  exact div_ne_zero (mul_ne_zero ne_zero_1728_of_six (pow_ne_zero _ h₀)) (pow_ne_zero _ h)

open Classical in
/-- The standard curve with j-invariant `j`: invariants `(0, 1)` at `j = 0`, `(1, 0)` at
`j = 1728`, and `(t, t)` with `t = j / (j - 1728)` otherwise. -/
noncomputable def ofJ (j : F) : Curve F :=
  if h₀ : j = 0 then mk 0 1 (by norm_num)
  else if h₁ : j = 1728 then mk 1 0 (by norm_num)
  else mk (j / (j - 1728)) (j / (j - 1728)) (disc_ofJ_ne_zero h₀ h₁)

/-- The standard curve `ofJ j` has j-invariant `j`. -/
@[simp] theorem j_ofJ (j : F) : (ofJ j).j = j := by
  by_cases h₀ : j = 0
  · simp [ofJ, h₀]
  by_cases h₁ : j = 1728
  · simp [ofJ, h₁, ne_zero_1728_of_six]
  · have h : j - 1728 ≠ 0 := sub_ne_zero.mpr h₁
    have hd := disc_ofJ_ne_zero h₀ h₁
    simp only [ofJ, h₀, h₁, dite_false, j_mk]
    rw [div_eq_iff hd]
    field_simp
    ring

/-- Away from 6, every `j ∈ F` is the j-invariant of a curve. -/
theorem j_surjective : Function.Surjective (j : Curve F → F) :=
  fun j => ⟨ofJ j, j_ofJ j⟩

/-- **The curves with j-invariant `j`** are `Fˣ ⧸ (Fˣ)ⁿ`, `n = twistExponent j`: the class of `d`
is the curve `d • ofJ j`. -/
noncomputable def fiberEquiv (j : F) :
    {C : Curve F // C.j = j} ≃ Fˣ ⧸ (powMonoidHom (twistExponent j) : Fˣ →* Fˣ).range :=
  (Equiv.subtypeEquivRight fun C => by rw [j_ofJ]).trans <|
    (fiberEquivOfBase (ofJ j)).trans (Subgroup.quotientEquivOfEq (by rw [j_ofJ]))

/-- **The (j, D) classification**: a curve away from 6 is its j-invariant together with a twist
datum `D ∈ Fˣ ⧸ (Fˣ)^{twistExponent j}`. -/
noncomputable def equivSigma :
    Curve F ≃ Σ j : F, Fˣ ⧸ (powMonoidHom (twistExponent j) : Fˣ →* Fˣ).range :=
  (Equiv.sigmaFiberEquiv Curve.j).symm.trans (Equiv.sigmaCongrRight fiberEquiv)

/-- The first component of the (j, D) data of a curve is its j-invariant. -/
@[simp] theorem equivSigma_fst (C : Curve F) : (equivSigma C).1 = C.j := by
  rfl

/-- The curve with j-invariant `j` and twist datum `D` is the twist `D • ofJ j` of the standard
curve. -/
theorem fiberEquiv_symm_coe (j : F) (D : Fˣ) :
    ((fiberEquiv j).symm (D : Fˣ ⧸ _)).1 = D • ofJ j := by
  simp [fiberEquiv, fiberEquivOfBase, Subgroup.quotientEquivOfEq,
    MulAction.orbitEquivQuotientStabilizer_symm_apply]

/-- The curve with j-invariant `j` and twist datum `D` is `D • ofJ j`. -/
theorem equivSigma_symm_mk (j : F) (D : Fˣ) :
    equivSigma.symm ⟨j, (D : Fˣ ⧸ _)⟩ = D • ofJ j := by
  simp only [equivSigma, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sigmaFiberEquiv_apply]
  exact fiberEquiv_symm_coe j D

/-! ### Counting over a finite field -/

/-- **The number of curves with a given j-invariant** over a finite field `𝔽_q` is
`gcd(q - 1, n(j))`. -/
theorem card_fiber [Finite F] (j : F) :
    Nat.card {C : Curve F // C.j = j} = (Nat.card F - 1).gcd (twistExponent j) := by
  rw [Nat.card_congr (fiberEquiv j), ← Subgroup.index_eq_card,
    IsCyclic.index_powMonoidHom_range, Nat.card_units]

/-- **The number of curves** over a finite field `𝔽_q` away from 6:
`2 (q - 2) + gcd(q - 1, 6) + gcd(q - 1, 4)`, the curves with `j ≠ 0, 1728` coming in pairs of
quadratic twists. That is `2q + 6`, `2q + 2`, `2q + 4`, `2q` for `q ≡ 1, 5, 7, 11 (mod 12)`. -/
theorem natCard_eq [Finite F] :
    Nat.card (Curve F) =
      2 * (Nat.card F - 2) + (Nat.card F - 1).gcd 6 + (Nat.card F - 1).gcd 4 := by
  classical
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card (α := F)]
  have hq : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two fun h =>
    NeZero.ne (2 : F) (by exact_mod_cast (ringChar.spec F 2).mpr (h ▸ dvd_rfl))
  have h2 : (Fintype.card F - 1).gcd 2 = 2 := Nat.gcd_eq_right (by omega)
  have hfib : ∀ j : F, Nat.card (Fˣ ⧸ (powMonoidHom (twistExponent j) : Fˣ →* Fˣ).range) =
      (Fintype.card F - 1).gcd (twistExponent j) := fun j => by
    rw [← Nat.card_congr (fiberEquiv j), card_fiber, Nat.card_eq_fintype_card]
  have h1728 : (1728 : F) ∈ (Finset.univ : Finset F).erase 0 := by
    simp [ne_zero_1728_of_six]
  rw [Nat.card_congr equivSigma, Nat.card_sigma]
  simp only [hfib]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0), ← Finset.add_sum_erase _ _ h1728,
    twistExponent_zero, twistExponent_1728,
    Finset.sum_congr rfl fun j hj => by
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
      rw [twistExponent_of_ne hj.2 hj.1, h2]]
  rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem h1728,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  omega

end Curve
