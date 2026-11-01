/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Curve.Defs
public import EllipticCurve.Field.AwayFromSix
import all EllipticCurve.Curve.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Curves away from 6: characterising lemmas

* equality of curves: `Curve.ofInvariants_eq_ofInvariants_iff`, `Curve.mk_eq_mk_iff`, and the
  certificate form `Curve.mk_eq_mk_of` (exhibit a nonzero `u` with `c₄ = u⁴ c₄'`, `c₆ = u⁶ c₆'`);
* every curve has invariants: `Curve.ofInvariants_surjective`, `Curve.exists_eq_mk`,
  `Curve.ind`;
* the `j`-invariant: `Curve.j_mk`, and away from 6 its special values `j = 0 ↔ c₄ = 0`,
  `j = 1728 ↔ c₆ = 0`;
* finiteness over a finite field. -/

public section

universe u

namespace Curve

variable {F : Type u} [Field F]

/-- Two invariants give the same curve exactly when they are in one orbit. -/
theorem ofInvariants_eq_ofInvariants_iff {p q : Invariants F} :
    ofInvariants p = ofInvariants q ↔ ∃ u : Fˣ, u • q = p := by
  change (Quotient.mk _ _ : Quotient (MulAction.orbitRel Fˣ (Invariants F))) = Quotient.mk _ _ ↔ _
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]

/-- The curve does not depend on the invariants chosen in an orbit. -/
@[simp] theorem ofInvariants_smul (u : Fˣ) (p : Invariants F) :
    ofInvariants (u • p) = ofInvariants p :=
  ofInvariants_eq_ofInvariants_iff.mpr ⟨u, rfl⟩

/-- Every curve has invariants. -/
theorem ofInvariants_surjective : Function.Surjective (ofInvariants : Invariants F → Curve F) :=
  Quotient.mk_surjective

/-- `lift f` on the curve with invariants `p` is `f p`. -/
@[simp] theorem lift_ofInvariants {α : Sort*} (f : Invariants F → α)
    (hf : ∀ (u : Fˣ) (p : Invariants F), f (u • p) = f p) (p : Invariants F) :
    lift f hf (ofInvariants p) = f p := by
  unfold lift ofInvariants; rfl

/-- Induction on curves: a statement about all curves follows from one about all invariants. -/
@[elab_as_elim] theorem ind {motive : Curve F → Prop} (h : ∀ p, motive (ofInvariants p))
    (C : Curve F) : motive C := by
  obtain ⟨p, rfl⟩ := ofInvariants_surjective C
  exact h p

/-- `mk a b h` is the curve with invariants `⟨a, b, h⟩`. -/
theorem mk_def (a b : F) (h : a ^ 3 - b ^ 2 ≠ 0) : mk a b h = ofInvariants ⟨a, b, h⟩ := by
  unfold mk; rfl

/-- The curve with invariants `p` is `mk p.c₄ p.c₆`. -/
theorem ofInvariants_eq_mk (p : Invariants F) : ofInvariants p = mk p.c₄ p.c₆ p.disc_ne_zero := by
  unfold mk; rfl

/-- Every curve is `mk c₄ c₆` for some nondegenerate `c₄`, `c₆`. -/
theorem exists_eq_mk (C : Curve F) : ∃ (c₄ c₆ : F) (h : c₄ ^ 3 - c₆ ^ 2 ≠ 0), C = mk c₄ c₆ h :=
  C.ind fun p => ⟨p.c₄, p.c₆, p.disc_ne_zero, rfl⟩

/-- **Equality of curves**: the invariants differ by the weights `(u⁴, u⁶)` of a unit. -/
theorem mk_eq_mk_iff {a b a' b' : F} {h : a ^ 3 - b ^ 2 ≠ 0} {h' : a' ^ 3 - b' ^ 2 ≠ 0} :
    mk a b h = mk a' b' h' ↔ ∃ u : Fˣ, a = u ^ 4 * a' ∧ b = u ^ 6 * b' := by
  rw [mk, mk, ofInvariants_eq_ofInvariants_iff]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, (congrArg Invariants.c₄ hu).symm, (congrArg Invariants.c₆ hu).symm⟩
  · rintro ⟨u, h₄, h₆⟩
    exact ⟨u, by ext <;> simp [h₄, h₆]⟩

/-- `mk_eq_mk_iff` with a field element in place of a unit. -/
theorem mk_eq_mk_iff' {a b a' b' : F} {h : a ^ 3 - b ^ 2 ≠ 0} {h' : a' ^ 3 - b' ^ 2 ≠ 0} :
    mk a b h = mk a' b' h' ↔ ∃ u : F, u ≠ 0 ∧ a = u ^ 4 * a' ∧ b = u ^ 6 * b' := by
  rw [mk_eq_mk_iff]
  constructor
  · rintro ⟨u, h₄, h₆⟩; exact ⟨u, u.ne_zero, h₄, h₆⟩
  · rintro ⟨u, hu, h₄, h₆⟩; exact ⟨Units.mk0 u hu, h₄, h₆⟩

/-- **Certificate for equality of curves**: a nonzero `u` with `c₄ = u⁴ c₄'` and `c₆ = u⁶ c₆'`. -/
theorem mk_eq_mk_of {a b a' b' : F} {h : a ^ 3 - b ^ 2 ≠ 0} {h' : a' ^ 3 - b' ^ 2 ≠ 0}
    (u : F) (hu : u ≠ 0) (h₄ : a = u ^ 4 * a') (h₆ : b = u ^ 6 * b') : mk a b h = mk a' b' h' :=
  mk_eq_mk_iff'.mpr ⟨u, hu, h₄, h₆⟩

/-- Scaling the invariants by the weights of a unit does not change the curve. -/
@[simp] theorem mk_smul (u : Fˣ) (a b : F) (h : (u ^ 4 * a : F) ^ 3 - (u ^ 6 * b) ^ 2 ≠ 0)
    (h' : a ^ 3 - b ^ 2 ≠ 0) : mk (u ^ 4 * a) (u ^ 6 * b) h = mk a b h' :=
  mk_eq_mk_iff.mpr ⟨u, rfl, rfl⟩

/-- Equal invariants give equal curves (the proofs of nondegeneracy are irrelevant). -/
theorem mk_congr {a b a' b' : F} {h : a ^ 3 - b ^ 2 ≠ 0} {h' : a' ^ 3 - b' ^ 2 ≠ 0}
    (ha : a = a') (hb : b = b') : mk a b h = mk a' b' h' := by
  subst ha hb; rfl

/-! ### The `j`-invariant -/

/-- The j-invariant of the curve with invariants `p`: `1728 c₄³ / (c₄³ - c₆²)`. -/
@[simp] theorem j_ofInvariants (p : Invariants F) :
    (ofInvariants p).j = 1728 * p.c₄ ^ 3 / (p.c₄ ^ 3 - p.c₆ ^ 2) := by
  unfold j ofInvariants; rfl

/-- The j-invariant of `mk a b`: `1728 a³ / (a³ - b²)`. -/
@[simp] theorem j_mk (a b : F) (h : a ^ 3 - b ^ 2 ≠ 0) :
    (mk a b h).j = 1728 * a ^ 3 / (a ^ 3 - b ^ 2) := by
  rw [mk, j_ofInvariants]

variable [NeZero (6 : F)]

/-- Away from 6, `j = 0` exactly when `c₄ = 0`. -/
theorem j_mk_eq_zero_iff {a b : F} {h : a ^ 3 - b ^ 2 ≠ 0} : (mk a b h).j = 0 ↔ a = 0 := by
  simp [div_eq_zero_iff, h, ne_zero_1728_of_six]

/-- Away from 6, `j = 1728` exactly when `c₆ = 0`. -/
theorem j_mk_eq_1728_iff {a b : F} {h : a ^ 3 - b ^ 2 ≠ 0} : (mk a b h).j = 1728 ↔ b = 0 := by
  rw [j_mk, div_eq_iff h]
  constructor
  · intro e
    have : (1728 : F) * b ^ 2 = 0 := by linear_combination e
    exact pow_eq_zero_iff two_ne_zero |>.mp ((mul_eq_zero.mp this).resolve_left ne_zero_1728_of_six)
  · rintro rfl; ring

/-- Away from 6, `j = 0` exactly when `c₄ = 0`. -/
theorem j_ofInvariants_eq_zero_iff {p : Invariants F} : (ofInvariants p).j = 0 ↔ p.c₄ = 0 := by
  rw [ofInvariants_eq_mk, j_mk_eq_zero_iff]

/-- Away from 6, `j = 1728` exactly when `c₆ = 0`. -/
theorem j_ofInvariants_eq_1728_iff {p : Invariants F} :
    (ofInvariants p).j = 1728 ↔ p.c₆ = 0 := by
  rw [ofInvariants_eq_mk, j_mk_eq_1728_iff]

/-! ### Finiteness -/

/-- There are finitely many curves over a finite field. -/
instance instFinite [Finite F] : Finite (Curve F) :=
  Quotient.finite _

end Curve
