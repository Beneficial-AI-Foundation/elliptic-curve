/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Curve.Lemmas
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.Ring

/-! # Quadratic twists

The quadratic twist of a curve by `d ∈ Fˣ` multiplies its invariants by `(d², d³)`
(`Curve.quadraticTwist`). For a short model `y² = x³ + a x + b` it is `d y² = x³ + a x + b`, i.e.
`y² = x³ + a d² x + b d³`; for a Montgomery model `B v² = u³ + A u² + u` it is the model with
`B d` (`MontgomeryModel.twist`). The twist depends only on the class of `d` modulo squares
(`quadraticTwist_mul_sq`), preserves `j` (`j_quadraticTwist`) and is an involution
(`quadraticTwist_quadraticTwist`).

The convention agrees with the FLT project's `WeierstrassCurve.quadraticTwistOf t n`
(`FLT/KnownIn1980s/EllipticCurve/QuadraticTwists`), which multiplies `c₄`, `c₆` by `D²`, `D³`
with `D = t² - 4 n` the discriminant of the quadratic extension: for `K(√d)`, `D = 4 d`, which is
`d` up to a square. -/

public section

universe u

namespace Curve

variable {F : Type u} [Field F]

namespace Invariants

/-- The quadratic twist preserves nondegeneracy: the discriminant scales by `d⁶`. -/
theorem disc_quadraticTwist_ne_zero (d : Fˣ) (p : Invariants F) :
    (d ^ 2 * p.c₄ : F) ^ 3 - (d ^ 3 * p.c₆) ^ 2 ≠ 0 := by
  have h : ((d : F) ^ 2 * p.c₄) ^ 3 - (d ^ 3 * p.c₆) ^ 2 = d ^ 6 * (p.c₄ ^ 3 - p.c₆ ^ 2) := by ring
  rw [h]
  exact mul_ne_zero (pow_ne_zero _ d.ne_zero) p.disc_ne_zero

/-- The invariants of the quadratic twist by `d`: `(d² c₄, d³ c₆)`. -/
def quadraticTwist (d : Fˣ) (p : Invariants F) : Invariants F :=
  ⟨d ^ 2 * p.c₄, d ^ 3 * p.c₆, p.disc_quadraticTwist_ne_zero d⟩

/-- The quadratic twist by `d` multiplies `c₄` by `d²`. -/
@[simp] theorem quadraticTwist_c₄ (d : Fˣ) (p : Invariants F) :
    (p.quadraticTwist d).c₄ = d ^ 2 * p.c₄ := by
  rfl

/-- The quadratic twist by `d` multiplies `c₆` by `d³`. -/
@[simp] theorem quadraticTwist_c₆ (d : Fˣ) (p : Invariants F) :
    (p.quadraticTwist d).c₆ = d ^ 3 * p.c₆ := by
  rfl

/-- The quadratic twist commutes with the weighted action. -/
theorem quadraticTwist_smul (d u : Fˣ) (p : Invariants F) :
    (u • p).quadraticTwist d = u • p.quadraticTwist d := by
  ext <;> simp <;> ring

end Invariants

/-- The quadratic twist of a curve by `d`: invariants `(d² c₄, d³ c₆)`. -/
def quadraticTwist (d : Fˣ) : Curve F → Curve F :=
  lift (fun p => ofInvariants (p.quadraticTwist d)) fun u p => by
    rw [Invariants.quadraticTwist_smul, ofInvariants_smul]

/-- The quadratic twist of the curve with invariants `p` has invariants `(d² c₄, d³ c₆)`. -/
@[simp] theorem quadraticTwist_ofInvariants (d : Fˣ) (p : Invariants F) :
    quadraticTwist d (ofInvariants p) = ofInvariants (p.quadraticTwist d) := by
  simp [quadraticTwist]

/-- The quadratic twist of `mk a b` is `mk (d² a) (d³ b)`. -/
@[simp] theorem quadraticTwist_mk (d : Fˣ) (a b : F) (h : a ^ 3 - b ^ 2 ≠ 0) :
    quadraticTwist d (mk a b h) =
      mk (d ^ 2 * a) (d ^ 3 * b) (Invariants.disc_quadraticTwist_ne_zero d ⟨a, b, h⟩) := by
  rw [mk_def, mk_def, quadraticTwist_ofInvariants]
  rfl

/-- The quadratic twist by `1` does nothing. -/
@[simp] theorem quadraticTwist_one (C : Curve F) : quadraticTwist 1 C = C :=
  C.ind fun p => by
    rw [quadraticTwist_ofInvariants]
    congr 1
    ext <;> simp

/-- Twisting by `d e` is twisting by `e`, then by `d`. -/
theorem quadraticTwist_mul (d e : Fˣ) (C : Curve F) :
    quadraticTwist (d * e) C = quadraticTwist d (quadraticTwist e C) :=
  C.ind fun p => by
    simp only [quadraticTwist_ofInvariants]
    congr 1
    ext <;> simp <;> ring

/-- Twisting by a square does nothing: the twist depends on `d` modulo squares. -/
@[simp] theorem quadraticTwist_sq (d : Fˣ) (C : Curve F) : quadraticTwist (d ^ 2) C = C :=
  C.ind fun p => by
    rw [quadraticTwist_ofInvariants, ofInvariants_eq_ofInvariants_iff]
    exact ⟨d, by
      ext <;> simp only [Invariants.smul_c₄, Invariants.smul_c₆, Invariants.quadraticTwist_c₄,
        Invariants.quadraticTwist_c₆, Units.val_pow_eq_pow_val] <;> ring⟩

/-- The quadratic twist depends on `d` only modulo squares. -/
theorem quadraticTwist_mul_sq (d e : Fˣ) (C : Curve F) :
    quadraticTwist (d * e ^ 2) C = quadraticTwist d C := by
  rw [quadraticTwist_mul, quadraticTwist_sq]

/-- The quadratic twist by `d` is an involution. -/
theorem quadraticTwist_quadraticTwist (d : Fˣ) (C : Curve F) :
    quadraticTwist d (quadraticTwist d C) = C := by
  rw [← quadraticTwist_mul, ← sq, quadraticTwist_sq]

/-- Twisting preserves the j-invariant. -/
@[simp] theorem j_quadraticTwist (d : Fˣ) (C : Curve F) : (quadraticTwist d C).j = C.j :=
  C.ind fun p => by
    rw [quadraticTwist_ofInvariants, j_ofInvariants, j_ofInvariants]
    have h := p.disc_quadraticTwist_ne_zero d
    simp only [Invariants.quadraticTwist_c₄, Invariants.quadraticTwist_c₆]
    rw [div_eq_div_iff h p.disc_ne_zero]
    ring

end Curve
