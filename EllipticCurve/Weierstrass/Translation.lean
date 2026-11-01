/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Weierstrass.Subst
public import EllipticCurve.Weierstrass.Places
public import EllipticCurve.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import EllipticCurve.FunctionField.Constants
import Mathlib.Tactic.LinearCombination

/-! # Translations as automorphisms of the function field

For a point `R` of an elliptic curve `W` over `L`, translation by `R` is induced by an
`L`-automorphism `τ_R` of the function field `K` (`translation`): the generic point
`ξ = (x, y) ∈ W(K)` goes to `ξ + R`, computed by Mathlib's group law over `K`. That `τ_{-R}` inverts
`τ_R` is Mathlib's `Point.map` being additive (`map_translation_genericPoint`). -/

public section

universe u

open Polynomial

namespace WeierstrassCurve.Affine

variable {L : Type u} [Field L] (W : WeierstrassCurve.Affine L) [W.IsElliptic]

/-- A base change of an elliptic curve is elliptic. -/
instance instIsEllipticBaseChange (K : Type*) [Field K] [Algebra L K] :
    (W.baseChange K).IsElliptic :=
  inferInstanceAs (W.map (algebraMap L K)).IsElliptic

omit [W.IsElliptic] in
/-- The base change of `W` to its own field of definition is `W`. -/
theorem baseChange_self : W.baseChange L = W := by
  rw [show W.baseChange L = W.map (algebraMap L L) from rfl, Algebra.algebraMap_self]
  exact WeierstrassCurve.map_id _

open Classical in
/-- The points of `W` are its points over `L`. -/
noncomputable def toBaseChange : W.Point ≃+ (W.baseChange L).Point :=
  Point.equivOfEq W.baseChange_self.symm

open Classical in
omit [W.IsElliptic] in
/-- `toBaseChange` on an affine point. -/
theorem toBaseChange_some {x y : L} (h : W.Nonsingular x y) :
    ∃ h', W.toBaseChange (.some x y h) = .some x y h' := by
  unfold toBaseChange
  exact ⟨_, Point.equivOfEq_some _ _⟩

open Classical in
omit [W.IsElliptic] in
/-- `toBaseChange` on `0`. -/
theorem toBaseChange_zero : W.toBaseChange 0 = 0 :=
  _root_.map_zero _

/-- The generic point `(x, y)` is a nonsingular point over the function field. -/
theorem nonsingular_genericPoint :
    (W.baseChange W.FunctionField).Nonsingular W.fieldX W.fieldY :=
  (equation_iff_nonsingular).mp (by
    rw [equation_iff]
    simpa [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] using W.fieldY_equation)

/-- The generic point `(x, y)` of `W`, a point over its function field. -/
noncomputable def genericPoint : (W.baseChange W.FunctionField).Point :=
  .some W.fieldX W.fieldY W.nonsingular_genericPoint

/-- The characterising equation of `genericPoint`. -/
theorem genericPoint_def : W.genericPoint = .some W.fieldX W.fieldY W.nonsingular_genericPoint := by
  unfold genericPoint; rfl

open Classical Point in
/-- The generic point is not defined over `L`. -/
theorem genericPoint_ne_map (P : (W.baseChange L).Point) :
    W.genericPoint ≠ Point.map (W' := W) (Algebra.ofId L W.FunctionField) P := by
  cases P with
  | zero => exact fun h => by cases h
  | some x y h =>
    intro he
    rw [genericPoint, Point.map_some, some.injEq] at he
    apply W.aeval_fieldX_ne_zero (p := X - C x) (X_sub_C_ne_zero x)
    rw [map_sub, aeval_X, aeval_C, he.1]
    exact sub_self _

variable {W}

open Classical Point in
/-- The generic point plus a point over `L` is affine. -/
theorem exists_genericPoint_add_eq (R : (W.baseChange L).Point) :
    ∃ (ξ η : W.FunctionField) (h : (W.baseChange W.FunctionField).Nonsingular ξ η),
      W.genericPoint + Point.map (W' := W) (Algebra.ofId L W.FunctionField) R = .some ξ η h := by
  rcases hS : W.genericPoint + Point.map (W' := W) (Algebra.ofId L W.FunctionField) R with
    _ | ⟨ξ, η, h⟩
  · exfalso
    apply W.genericPoint_ne_map (-R)
    rw [_root_.map_neg, ← add_eq_zero_iff_eq_neg.mp hS]
  · exact ⟨ξ, η, h, rfl⟩

open Classical in
/-- The `x`-coordinate of `ξ + R`. -/
noncomputable def transX (R : (W.baseChange L).Point) : W.FunctionField :=
  (exists_genericPoint_add_eq R).choose

open Classical in
/-- The `y`-coordinate of `ξ + R`. -/
noncomputable def transY (R : (W.baseChange L).Point) : W.FunctionField :=
  (exists_genericPoint_add_eq R).choose_spec.choose

open Classical in
/-- The defining property of `transX`, `transY`. -/
theorem genericPoint_add_eq (R : (W.baseChange L).Point) :
    ∃ h, W.genericPoint + Point.map (W' := W) (Algebra.ofId L W.FunctionField) R =
      .some (transX R) (transY R) h :=
  (exists_genericPoint_add_eq R).choose_spec.choose_spec

open Classical in
/-- `ξ + R` satisfies the equation. -/
theorem fieldEquation_trans (R : (W.baseChange L).Point) :
    W.FieldEquation (transX R) (transY R) := by
  obtain ⟨h, -⟩ := genericPoint_add_eq R
  have := (equation_iff _ _).mp h.1
  rw [fieldEquation_iff]
  simpa [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] using this

open Classical in
/-- The `x`-coordinate of `ξ + R` is not a constant. -/
theorem transcendental_transX (R : (W.baseChange L).Point) : Transcendental L (transX R) := by
  intro halg
  set P₀ := W.pointEquivRationalPlace 0
  obtain ⟨c, hc⟩ := P₀.exists_eq_algebraMap_of_isAlgebraic halg
  have heq := fieldEquation_trans R
  rw [fieldEquation_iff, hc] at heq
  have hηalg : IsAlgebraic L (transY R) := by
    refine ⟨X ^ 2 + C (W.a₁ * c + W.a₃) * X - C (c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆), ?_, ?_⟩
    · apply Polynomial.Monic.ne_zero
      monicity!
    · simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C]
      linear_combination heq
  obtain ⟨c', hc'⟩ := P₀.exists_eq_algebraMap_of_isAlgebraic hηalg
  obtain ⟨h, he⟩ := genericPoint_add_eq R
  have h' : (W.baseChange W.FunctionField).Nonsingular
      (Algebra.ofId L W.FunctionField c) (Algebra.ofId L W.FunctionField c') := by
    change (W.baseChange _).Nonsingular (algebraMap L _ c) (algebraMap L _ c')
    rw [← hc, ← hc']; exact h
  have h₀ := (W.baseChange_nonsingular (Algebra.ofId L W.FunctionField).injective c c').mp h'
  apply W.genericPoint_ne_map (.some c c' h₀ - R)
  rw [_root_.map_sub, Point.map_some, eq_sub_iff_add_eq, he]
  simp only [Point.some.injEq]
  exact ⟨hc, hc'⟩

open Classical in
/-- **Translation by `R`** on the function field: `x ↦ x(ξ + R)`, `y ↦ y(ξ + R)`. -/
noncomputable def translation (R : (W.baseChange L).Point) :
    W.FunctionField →ₐ[L] W.FunctionField :=
  subst (fieldEquation_trans R) (transcendental_transX R)

open Classical in
/-- The translation sends `x` to `x(ξ + R)`. -/
theorem translation_fieldX (R : (W.baseChange L).Point) : translation R W.fieldX = transX R :=
  subst_fieldX _ _

open Classical in
/-- The translation sends `y` to `y(ξ + R)`. -/
theorem translation_fieldY (R : (W.baseChange L).Point) : translation R W.fieldY = transY R :=
  subst_fieldY _ _

open Classical in
/-- The translation moves the generic point by `R`. -/
theorem map_translation_genericPoint (R : (W.baseChange L).Point) :
    Point.map (W' := W) (translation R) W.genericPoint =
      W.genericPoint + Point.map (W' := W) (Algebra.ofId L W.FunctionField) R := by
  obtain ⟨h, he⟩ := genericPoint_add_eq R
  rw [he, genericPoint, Point.map_some]
  simp only [Point.some.injEq]
  exact ⟨translation_fieldX R, translation_fieldY R⟩

open Classical in
omit [W.IsElliptic] in
/-- An `L`-algebra map fixes the points defined over `L`. -/
theorem map_map_ofId (f : W.FunctionField →ₐ[L] W.FunctionField) (P : (W.baseChange L).Point) :
    Point.map (W' := W) f (Point.map (W' := W) (Algebra.ofId L W.FunctionField) P) =
      Point.map (W' := W) (Algebra.ofId L W.FunctionField) P := by
  rw [Point.map_map, show f.comp (Algebra.ofId L W.FunctionField) = Algebra.ofId L _ from
    Subsingleton.elim _ _]

open Classical in
/-- Translations compose: `τ_S ∘ τ_R = τ_{R + S}` on the generic point. -/
theorem map_translation_comp (R S : (W.baseChange L).Point) :
    Point.map (W' := W) ((translation S).comp (translation R)) W.genericPoint =
      W.genericPoint + Point.map (W' := W) (Algebra.ofId L W.FunctionField) (R + S) := by
  rw [← Point.map_map, map_translation_genericPoint, _root_.map_add,
    map_translation_genericPoint, map_map_ofId, _root_.map_add]
  abel

open Classical in
/-- `τ_{-R}` inverts `τ_R`. -/
theorem translation_neg_comp (R : (W.baseChange L).Point) :
    (translation (-R)).comp (translation R) = AlgHom.id L W.FunctionField := by
  have key := map_translation_comp R (-R)
  rw [add_neg_cancel, _root_.map_zero, add_zero, genericPoint, Point.map_some] at key
  simp only [Point.some.injEq, AlgHom.comp_apply] at key
  exact algHom_ext_fieldX_fieldY key.1 key.2

open Classical in
/-- **Translation by `R`**, as an automorphism of the function field. -/
noncomputable def translationEquiv (R : (W.baseChange L).Point) :
    W.FunctionField ≃ₐ[L] W.FunctionField :=
  AlgEquiv.ofAlgHom (translation R) (translation (-R))
    (by simpa using translation_neg_comp (-R)) (translation_neg_comp R)

open Classical in
/-- The automorphism `translationEquiv R` is `translation R`. -/
theorem translationEquiv_apply (R : (W.baseChange L).Point) (z : W.FunctionField) :
    translationEquiv R z = translation R z := by
  unfold translationEquiv; rfl

end WeierstrassCurve.Affine
