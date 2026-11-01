/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Data.Fintype.Defs
import EllipticCurve.Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithC
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Curves away from 6

`Curve F` is an elliptic curve over the field `F`, up to `F`-isomorphism, defined independently of
any model. A curve is given by its **invariants** `(c₄, c₆)`, with `c₄³ ≠ c₆²`, taken up to the
weighted action `u • (c₄, c₆) = (u⁴ c₄, u⁶ c₆)` of `Fˣ`:

  `Curve F = {(c₄, c₆) : c₄³ ≠ c₆²} / Fˣ`,

the weighted projective plane `P(4, 6)` over `F` minus the discriminant locus. The invariants of a
curve are those of the pair (curve, invariant differential `ω`); replacing `ω` by `u⁻¹ ω` scales
them by `u⁴`, `u⁶`, so their class is an invariant of the curve alone. For a Weierstrass model
they are Mathlib's `WeierstrassCurve.c₄`, `WeierstrassCurve.c₆`; a model of any other kind
supplies its own (`MontgomeryModel.c₄`, …), and two models give the same curve exactly when a
`u` relates their invariants (`Curve.mk_eq_mk_iff`).

The description is faithful over fields **away from 6** (`[NeZero (6 : F)]`): there, two elliptic
Weierstrass curves are isomorphic if and only if their invariants are in one orbit
(`WeierstrassCurve.exists_variableChange_iff`). The type itself needs no hypothesis; in
characteristic 2 and 3 every Weierstrass curve has `c₄³ = c₆²`, so no model maps to `Curve F`
there and its elements describe no elliptic curve.

The group of `F`-rational points `C.Point` is a hidden construction (the points of the short model
`y² = x³ - 27 c₄ x - 54 c₆` of a chosen representative), characterised through the models of `C`.
It is canonical only up to the automorphisms of `C` (`-1`, and more at `j = 0, 1728`). -/

public section

universe u

/-- The invariants `(c₄, c₆)` of an elliptic curve with a chosen invariant differential: a pair
with nonzero discriminant `c₄³ - c₆²` (`= 1728 Δ`). -/
@[ext] structure Curve.Invariants (F : Type u) [Field F] where
  /-- The invariant `c₄` (weight 4). -/
  c₄ : F
  /-- The invariant `c₆` (weight 6). -/
  c₆ : F
  /-- Nondegeneracy: the discriminant `c₄³ - c₆²` (`= 1728 Δ`) is nonzero. -/
  disc_ne_zero : c₄ ^ 3 - c₆ ^ 2 ≠ 0

namespace Curve.Invariants

variable {F : Type u} [Field F]

/-- The weighted action preserves nondegeneracy: the discriminant scales by `u¹²`. -/
theorem disc_smul_ne_zero (p : Invariants F) (u : Fˣ) :
    (u ^ 4 * p.c₄ : F) ^ 3 - (u ^ 6 * p.c₆) ^ 2 ≠ 0 := by
  have h : ((u : F) ^ 4 * p.c₄) ^ 3 - (u ^ 6 * p.c₆) ^ 2 = u ^ 12 * (p.c₄ ^ 3 - p.c₆ ^ 2) := by
    ring
  rw [h]
  exact mul_ne_zero (pow_ne_zero _ u.ne_zero) p.disc_ne_zero

/-- The weighted action `u • (c₄, c₆) = (u⁴ c₄, u⁶ c₆)`: a change of invariant differential. -/
instance instMulAction : MulAction Fˣ (Invariants F) where
  smul u p := ⟨u ^ 4 * p.c₄, u ^ 6 * p.c₆, p.disc_smul_ne_zero u⟩
  one_smul p := by ext <;> simp [HSMul.hSMul]
  mul_smul u v p := by ext <;> simp [HSMul.hSMul, SMul.smul] <;> ring

/-- The weighted action multiplies `c₄` by `u⁴`. -/
@[simp] theorem smul_c₄ (u : Fˣ) (p : Invariants F) : (u • p).c₄ = u ^ 4 * p.c₄ := rfl

/-- The weighted action multiplies `c₆` by `u⁶`. -/
@[simp] theorem smul_c₆ (u : Fˣ) (p : Invariants F) : (u • p).c₆ = u ^ 6 * p.c₆ := rfl

/-- The invariants as a pair of field elements. -/
def toProd (p : Invariants F) : F × F := (p.c₄, p.c₆)

/-- Invariants are determined by the pair `(c₄, c₆)`. -/
theorem toProd_injective : Function.Injective (toProd : Invariants F → F × F) := by
  rintro ⟨a, b, h⟩ ⟨a', b', h'⟩ e
  simp only [toProd, Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  rfl

/-- Over a finite field there are finitely many invariants. -/
instance [Finite F] : Finite (Invariants F) := Finite.of_injective _ toProd_injective

end Curve.Invariants

/-- An elliptic curve over a field `F` away from 6, up to `F`-isomorphism: its invariants
`(c₄, c₆)` up to the weighted action of `Fˣ`. (The type is defined for every field, but describes
elliptic curves only away from 6.) -/
def Curve (F : Type u) [Field F] : Type u :=
  MulAction.orbitRel.Quotient Fˣ (Curve.Invariants F)

namespace Curve

variable {F : Type u} [Field F]

/-- The curve with invariants `p`. -/
def ofInvariants (p : Invariants F) : Curve F :=
  Quotient.mk _ p

/-- The curve with invariants `(c₄, c₆)`, `c₄³ ≠ c₆²`. -/
def mk (c₄ c₆ : F) (h : c₄ ^ 3 - c₆ ^ 2 ≠ 0) : Curve F :=
  ofInvariants ⟨c₄, c₆, h⟩

/-- A function of the invariants that is unchanged by the weighted action is a function of the
curve. -/
def lift {α : Sort*} (f : Invariants F → α) (hf : ∀ (u : Fˣ) (p : Invariants F), f (u • p) = f p) :
    Curve F → α :=
  Quotient.lift f <| by rintro _ p ⟨u, rfl⟩; exact hf u p

/-- The `j`-invariant `1728 c₄³ / (c₄³ - c₆²)`. -/
def j : Curve F → F :=
  Quotient.lift (fun p : Invariants F => 1728 * p.c₄ ^ 3 / (p.c₄ ^ 3 - p.c₆ ^ 2)) <| by
    rintro _ p ⟨u, rfl⟩
    have hu : (u : F) ^ 12 ≠ 0 := pow_ne_zero _ u.ne_zero
    simp only [Invariants.smul_c₄, Invariants.smul_c₆]
    rw [div_eq_div_iff (p.disc_smul_ne_zero u) p.disc_ne_zero]
    ring

/-- Invariants representing `C` (hidden, internal). -/
private noncomputable def out (C : Curve F) : Invariants F :=
  Quotient.out C

/-- The short Weierstrass model `y² = x³ - 27 c₄ x - 54 c₆` of the chosen invariants of `C`
(hidden, internal). -/
private noncomputable def toAffine (C : Curve F) : WeierstrassCurve.Affine F :=
  WeierstrassCurve.ofC₄C₆ C.out.c₄ C.out.c₆

/-- The group of `F`-rational points of `C`. Hidden construction: only the instances below and
the lemmas about the models of `C` are visible. -/
def Point (C : Curve F) : Type u :=
  C.toAffine.Point

/-- The group law on the points of `C`. Hidden construction; it is characterised through the
models, e.g. by `MontgomeryModel.some_add_some_of_u_ne`. -/
@[no_expose] noncomputable instance instAddCommGroupPoint (C : Curve F) :
    AddCommGroup C.Point := by
  classical exact inferInstanceAs (AddCommGroup C.toAffine.Point)

/-- Equality of points of a curve is decidable when equality in `F` is. Hidden construction. -/
@[no_expose] noncomputable instance instDecidableEqPoint (C : Curve F) [DecidableEq F] :
    DecidableEq C.Point :=
  inferInstanceAs (DecidableEq C.toAffine.Point)

/-- The coordinates of a point, with `none` at infinity (hidden, internal). -/
private noncomputable def coords {C : Curve F} : C.Point → Option (F × F)
  | .zero => none
  | .some x y _ => some (x, y)

private theorem coords_injective (C : Curve F) : Function.Injective (coords (C := C))
  | .zero, .zero, _ => rfl
  | .some _ _ _, .some _ _ _, e => by
    simp only [coords, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    rfl

/-- A curve over a finite field has finitely many points. -/
instance instFinitePoint (C : Curve F) [Finite F] : Finite C.Point :=
  Finite.of_injective _ (coords_injective C)

/-- The points of a curve over a finite field, as a `Fintype`. Hidden construction. -/
@[no_expose] noncomputable instance instFintypePoint (C : Curve F) [Fintype F] :
    Fintype C.Point :=
  Fintype.ofFinite C.Point

end Curve
