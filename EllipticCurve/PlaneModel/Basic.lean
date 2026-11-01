/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Weierstrass.Places
public import EllipticCurve.PlaneModel.Local
import EllipticCurve.PlaneModel.Kernel
public import EllipticCurve.Curve.Weierstrass
public import Mathlib.Algebra.MvPolynomial.PDeriv
import EllipticCurve.Curve.Impl
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Plane models of an elliptic curve

A **plane model** of the elliptic curve `W` (its *root*) is a pair of functions `x`, `y` on the
function field of `W` that generates it, together with an equation `G(x, y) = 0` they satisfy.
Defining a model costs two identities: `aeval_G`, and the
generation `adjoin_eq_top`, which follows from writing the root's coordinates in terms of `x`, `y`
(`adjoin_eq_top_of_mem`).

Everything else is inherited from the root:

* the points are the points of `W` (`PlaneModel.Point`), with its group law;
* the curve is that of `W` (`PlaneModel.toCurve`), and `PlaneModel.pointEquiv` identifies the
  points with those of the curve;
* the **coordinate view** `PlaneModel.coords`: a point whose place makes `x` and `y` regular has
  coordinates `(x(P), y(P))`, a solution of `G = 0` (`coords_equation`); the other points are the
  points at infinity of the model.

**(A-coord)** (`coords_injective`, `exists_coords_eq`): when `G` is irreducible and the affine
curve `G = 0` is nonsingular, the coordinate view is a bijection between the points with
coordinates and the solutions of `G = 0`. -/

public section

universe u

open Polynomial

variable {F : Type u} [Field F]

/-- A plane model of the elliptic curve `W`: coordinate functions `x`, `y` on its function field
that generate it, and an equation `G(x, y) = 0` they satisfy. -/
structure PlaneModel (W : WeierstrassCurve.Affine F) where
  /-- The first coordinate function. -/
  x : W.FunctionField
  /-- The second coordinate function. -/
  y : W.FunctionField
  /-- The equation of the model. -/
  G : MvPolynomial (Fin 2) F
  /-- The coordinates satisfy the equation. -/
  aeval_G : MvPolynomial.aeval ![x, y] G = 0
  /-- The coordinates generate the function field. -/
  adjoin_eq_top : IntermediateField.adjoin F {x, y} = ⊤

namespace PlaneModel

variable {W : WeierstrassCurve.Affine F}

/-- Generation from inverse formulas: if the root's coordinates are rational in `x` and `y`, then
`x` and `y` generate the function field. -/
theorem adjoin_eq_top_of_mem {x y : W.FunctionField}
    (hX : W.fieldX ∈ IntermediateField.adjoin F {x, y})
    (hY : W.fieldY ∈ IntermediateField.adjoin F {x, y}) :
    IntermediateField.adjoin F {x, y} = ⊤ := by
  rw [eq_top_iff, ← W.adjoin_fieldX_fieldY, IntermediateField.adjoin_le_iff]
  intro z hz
  rcases hz with rfl | rfl
  · exact hX
  · exact hY

/-- The root as a model of itself, with its own coordinates. -/
noncomputable def root (W : WeierstrassCurve.Affine F) : PlaneModel W where
  x := W.fieldX
  y := W.fieldY
  G := MvPolynomial.X 1 ^ 2 + MvPolynomial.C W.a₁ * MvPolynomial.X 0 * MvPolynomial.X 1 +
    MvPolynomial.C W.a₃ * MvPolynomial.X 1 - (MvPolynomial.X 0 ^ 3 +
      MvPolynomial.C W.a₂ * MvPolynomial.X 0 ^ 2 + MvPolynomial.C W.a₄ * MvPolynomial.X 0 +
      MvPolynomial.C W.a₆)
  aeval_G := by
    simp only [map_sub, map_add, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [W.fieldY_equation, sub_self]
  adjoin_eq_top := W.adjoin_fieldX_fieldY

variable (M : PlaneModel W)

/-- The points of a model: the points of its root. -/
@[nolint unusedArguments]
abbrev Point (_M : PlaneModel W) := W.Point

variable [W.IsElliptic]

open scoped Classical in
/-- The coordinates of a point: `(x(P), y(P))` when `x` and `y` are regular at the place of `P`,
and `none` for the points at infinity of the model. -/
noncomputable def coords (P : M.Point) : Option (F × F) :=
  let p := W.pointEquivRationalPlace P
  if h : M.x ∈ p.1.ring ∧ M.y ∈ p.1.ring then some (p.eval _ h.1, p.eval _ h.2) else none

/-- The coordinates of a point from the values of `x` and `y` at its place. -/
theorem coords_eq_of_hasValue {P : M.Point} {a b : F}
    (hx : (W.pointEquivRationalPlace P).HasValue M.x a)
    (hy : (W.pointEquivRationalPlace P).HasValue M.y b) : M.coords P = some (a, b) := by
  classical
  obtain ⟨hx', rfl⟩ := FunctionField.RationalPlace.hasValue_iff.mp hx
  obtain ⟨hy', rfl⟩ := FunctionField.RationalPlace.hasValue_iff.mp hy
  simp [coords, hx', hy']

/-- The coordinates of a point satisfy the equation of the model. -/
theorem coords_equation {P : M.Point} {a b : F} (h : M.coords P = some (a, b)) :
    MvPolynomial.eval ![a, b] M.G = 0 := by
  classical
  simp only [coords] at h
  split_ifs at h with hreg
  obtain ⟨rfl, rfl⟩ : _ ∧ _ := by simpa using h
  set p := W.pointEquivRationalPlace P
  have hf : ∀ i, (![M.x, M.y] i) ∈ p.1.ring := by
    intro i; fin_cases i
    · exact hreg.1
    · exact hreg.2
  have h1 := p.coe_eval₂Hom ![M.x, M.y] hf M.G
  rw [M.aeval_G] at h1
  have h2 := p.evalHom_eval₂Hom ![M.x, M.y] hf M.G
  have h0 : MvPolynomial.eval₂Hom p.1.constHom (fun i => ⟨![M.x, M.y] i, hf i⟩) M.G = 0 :=
    Subtype.ext h1
  rw [h0, map_zero] at h2
  rw [h2]
  refine congrArg (fun v => MvPolynomial.eval v M.G) ?_
  funext i
  fin_cases i <;> rfl

/-- Nonsingularity of the affine curve `G = 0` at a solution: a partial derivative is nonzero. -/
def Nonsingular (a b : F) : Prop :=
  MvPolynomial.eval ![a, b] M.G = 0 ∧
    (MvPolynomial.eval ![a, b] (MvPolynomial.pderiv 0 M.G) ≠ 0 ∨
      MvPolynomial.eval ![a, b] (MvPolynomial.pderiv 1 M.G) ≠ 0)

omit [W.IsElliptic] in
/-- The definition of `Nonsingular`. -/
theorem nonsingular_iff (a b : F) : M.Nonsingular a b ↔ MvPolynomial.eval ![a, b] M.G = 0 ∧
    (MvPolynomial.eval ![a, b] (MvPolynomial.pderiv 0 M.G) ≠ 0 ∨
      MvPolynomial.eval ![a, b] (MvPolynomial.pderiv 1 M.G) ≠ 0) :=
  Iff.rfl

/-- The values of `x` and `y` at the place of a point with coordinates. -/
theorem hasValue_of_coords {P : M.Point} {a b : F} (h : M.coords P = some (a, b)) :
    (W.pointEquivRationalPlace P).HasValue M.x a ∧
      (W.pointEquivRationalPlace P).HasValue M.y b := by
  classical
  simp only [coords] at h
  split_ifs at h with hreg
  obtain ⟨rfl, rfl⟩ : _ ∧ _ := by simpa using h
  exact ⟨FunctionField.RationalPlace.HasValue.of_mem hreg.1,
    FunctionField.RationalPlace.HasValue.of_mem hreg.2⟩

omit [W.IsElliptic] in
/-- The coordinates of a model are not both constant. -/
theorem ne_const (a b : F) : M.x ≠ algebraMap F _ a ∨ M.y ≠ algebraMap F _ b := by
  by_contra! h
  have hbot : IntermediateField.adjoin F {M.x, M.y} = ⊥ := by
    rw [eq_bot_iff, IntermediateField.adjoin_le_iff, h.1, h.2]
    rintro z (rfl | rfl) <;> exact IntermediateField.algebraMap_mem _ _
  have hX : W.fieldX ∈ (⊥ : IntermediateField F W.FunctionField) := by
    rw [← hbot, M.adjoin_eq_top]; exact IntermediateField.mem_top
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hX
  apply W.aeval_fieldX_ne_zero (p := X - C c) (X_sub_C_ne_zero c)
  rw [map_sub, aeval_X, aeval_C, hc, sub_self]

/-- The data of a nonsingular solution that is the coordinates of some point. -/
theorem nonsingularPoint_of_coords {P : M.Point} {a b : F} (hab : M.Nonsingular a b)
    (hP : M.coords P = some (a, b)) : PlaneCurve.NonsingularPoint M.G M.x M.y a b where
  aeval_G := M.aeval_G
  adjoin_eq_top := M.adjoin_eq_top
  eval_G := hab.1
  pderiv_ne_zero := hab.2
  evalWellDefined := PlaneCurve.evalWellDefined_iff.mpr fun H hH => by
    obtain ⟨hx, hy⟩ := M.hasValue_of_coords hP
    have := PlaneCurve.hasValue_aeval hx hy H
    rw [hH] at this
    exact this.unique (FunctionField.RationalPlace.hasValue_algebraMap (P := _) 0 |>.congr
      (map_zero _) rfl)
  ne_const := M.ne_const a b

/-- **(A-coord)** At a nonsingular solution, the coordinate view is injective: two points with the
same nonsingular coordinates are equal (both places are the place of the solution,
`PlaneCurve.eq_rationalPlace`). -/
theorem coords_injective {P Q : M.Point} {a b : F} (hab : M.Nonsingular a b)
    (hP : M.coords P = some (a, b)) (hQ : M.coords Q = some (a, b)) : P = Q := by
  have h := M.nonsingularPoint_of_coords hab hP
  obtain ⟨hPx, hPy⟩ := M.hasValue_of_coords hP
  obtain ⟨hQx, hQy⟩ := M.hasValue_of_coords hQ
  apply W.pointEquivRationalPlace.injective
  rw [PlaneCurve.eq_rationalPlace h hPx hPy, PlaneCurve.eq_rationalPlace h hQx hQy]

/-- **(A-coord)** Every nonsingular solution of an irreducible equation of the model is the
coordinates of a point.

Both hypotheses are needed: for a reducible `G` (for example `G = 0`) the solutions off the curve
carry no place, and over a singular solution the places need not be rational (a node with
conjugate tangents). With `G` irreducible, every relation between `x` and `y` is a multiple of
`G` (`PlaneCurve.ker_aeval_eq_span`), so evaluation at the solution is well defined on `F[x, y]`,
and the local ring there is the valuation ring of a rational place
(`PlaneCurve.rationalPlace`). -/
theorem exists_coords_eq (hG : Irreducible M.G) {a b : F} (hab : M.Nonsingular a b) :
    ∃ P : M.Point, M.coords P = some (a, b) := by
  have hz : Transcendental F W.fieldX := fun ⟨p, hp, hp0⟩ => W.aeval_fieldX_ne_zero hp hp0
  have hker := PlaneCurve.ker_aeval_eq_span hG M.aeval_G
    (M.adjoin_eq_top ▸ IntermediateField.mem_top) hz
  have h : PlaneCurve.NonsingularPoint M.G M.x M.y a b :=
    { aeval_G := M.aeval_G
      adjoin_eq_top := M.adjoin_eq_top
      eval_G := hab.1
      pderiv_ne_zero := hab.2
      evalWellDefined := PlaneCurve.evalWellDefined_iff.mpr fun H hH => by
        have hm : H ∈ RingHom.ker (MvPolynomial.aeval (R := F) ![M.x, M.y]) := hH
        rw [hker, Ideal.mem_span_singleton] at hm
        obtain ⟨Q, rfl⟩ := hm
        rw [map_mul, hab.1, zero_mul]
      ne_const := M.ne_const a b }
  refine ⟨W.pointEquivRationalPlace.symm (PlaneCurve.rationalPlace h), ?_⟩
  apply M.coords_eq_of_hasValue <;> rw [Equiv.apply_symm_apply]
  · exact PlaneCurve.hasValue_x h
  · exact PlaneCurve.hasValue_y h

/-! ### The curve of a model -/

variable [NeZero (6 : F)]

/-- The curve of a model: that of its root. -/
@[nolint unusedArguments]
noncomputable def toCurve (_M : PlaneModel W) : Curve F :=
  Curve.ofWeierstrass (W : WeierstrassCurve F)

open scoped Classical in
/-- The points of a model are the points of its curve, as groups. -/
noncomputable def pointEquiv : M.Point ≃+ M.toCurve.Point :=
  (Curve.pointEquivOfWeierstrass (W : WeierstrassCurve F)).symm

end PlaneModel
