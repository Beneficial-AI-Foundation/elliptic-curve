/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Weierstrass.TranslationPlaces

/-! # Automorphisms of the function field act on points by affine maps

An `L`-automorphism `e` of the function field of an elliptic curve `W` acts on points by
`P ↦ ψ(P) + e(O)`, with `ψ` the point map of a change of variables preserving `W`
(`exists_pointMapOfAlgEquiv_eq_add`): compose with the translation by `-e(O)`, which fixes the
place at infinity, and apply (B-W). -/

public section

universe u

namespace WeierstrassCurve.Affine

variable {L : Type u} [Field L] {W : WeierstrassCurve.Affine L} [W.IsElliptic]

/-- The point map of a composite is the composite of the point maps. -/
theorem pointMapOfAlgEquiv_trans (e₁ e₂ : W.FunctionField ≃ₐ[L] W.FunctionField) (P : W.Point) :
    pointMapOfAlgEquiv (e₁.trans e₂) P = pointMapOfAlgEquiv e₁ (pointMapOfAlgEquiv e₂ P) := by
  rw [pointMapOfAlgEquiv_apply, pointMapOfAlgEquiv_apply, pointMapOfAlgEquiv_apply,
    Equiv.apply_symm_apply]
  congr 1
  refine Subtype.ext (FunctionField.Place.ext ?_)
  ext z
  change _ ∈ (FunctionField.RationalPlace.congr _ _).1.ring ↔
    _ ∈ (FunctionField.RationalPlace.congr _ _).1.ring
  rw [FunctionField.RationalPlace.congr_apply_ring, FunctionField.RationalPlace.congr_apply_ring,
    FunctionField.RationalPlace.congr_apply_ring]
  rfl

open Classical in
/-- The point map of a translation. -/
theorem pointMapOfAlgEquiv_translationEquiv (R P : W.Point) :
    pointMapOfAlgEquiv (translationEquiv (W.toBaseChange R)) P = P + R := by
  rw [pointMapOfAlgEquiv_apply, pointEquivRationalPlace_symm_congr_translationEquiv]

open Classical in
/-- Auxiliary form of `exists_pointMapOfAlgEquiv_eq_add`, for the classical decidable
equality. -/
private theorem exists_pointMapOfAlgEquiv_eq_add_aux [NeZero (2 : L)]
    (e : W.FunctionField ≃ₐ[L] W.FunctionField) :
    ∃ (C : VariableChange L) (hC : C • W = W), ∀ P : W.Point,
      pointMapOfAlgEquiv e P =
        Point.equivVariableChange W C (Point.equivOfEq hC.symm P) + pointMapOfAlgEquiv e 0 := by
  set Q := pointMapOfAlgEquiv e 0
  set ρ := (translationEquiv (W.toBaseChange (-Q))).trans e
  have hρ : ∀ P, pointMapOfAlgEquiv ρ P = pointMapOfAlgEquiv e P - Q := fun P => by
    rw [pointMapOfAlgEquiv_trans, pointMapOfAlgEquiv_translationEquiv, sub_eq_add_neg]
  obtain ⟨C, hC, h⟩ := exists_variableChange_of_algEquiv ρ (by rw [hρ, sub_self])
  refine ⟨C, hC, fun P => ?_⟩
  rw [← h, hρ, sub_add_cancel]

/-- **Rigidity at a fixed point**: away from 2, an automorphism of the function field acts on
points as a change of variables preserving `W`, followed by the translation by `e(O)`. -/
theorem exists_pointMapOfAlgEquiv_eq_add [DecidableEq L] [NeZero (2 : L)]
    (e : W.FunctionField ≃ₐ[L] W.FunctionField) :
    ∃ (C : VariableChange L) (hC : C • W = W), ∀ P : W.Point,
      pointMapOfAlgEquiv e P =
        Point.equivVariableChange W C (Point.equivOfEq hC.symm P) + pointMapOfAlgEquiv e 0 := by
  obtain ⟨C, hC, h⟩ := exists_pointMapOfAlgEquiv_eq_add_aux e
  exact ⟨C, hC, fun P => by convert h P⟩

end WeierstrassCurve.Affine
