/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Curve.Fiber

/-! # The (j, D) description as a flat quotient

The classification `Curve.equivSigma : Curve F ≃ Σ j, Fˣ ⧸ (Fˣ)^{n(j)}` in the flat form of the
original EllipticCurve design (`IsoClasses.lean`, removed; commit `d1962df`): pairs
`(j, D) ∈ F × Fˣ` with `(j, D) ~ (j', D')` when `j = j'` and `D' / D` is an `n(j)`-th power
(`Curve.jdSetoid`), and `Curve.equivJD : Curve F ≃ Quotient Curve.jdSetoid`. The curve with datum
`(j, D)` is the twist `D • Curve.ofJ j` of the standard curve with j-invariant `j`
(`Curve.equivJD_symm_mk`). -/

public section

universe u

namespace Curve

variable {F : Type u} [Field F]

/-- `(j, D) ~ (j', D')` when `j = j'` and `D⁻¹ D'` is an `n(j)`-th power. -/
def jdSetoid : Setoid (F × Fˣ) where
  r x y := x.1 = y.1 ∧ x.2⁻¹ * y.2 ∈ (powMonoidHom (twistExponent x.1) : Fˣ →* Fˣ).range
  iseqv := by
    refine ⟨fun x => ⟨rfl, by simp⟩, ?_, ?_⟩
    · rintro ⟨j, D⟩ ⟨j', D'⟩ ⟨rfl, h⟩
      refine ⟨rfl, ?_⟩
      simpa using Subgroup.inv_mem _ h
    · rintro ⟨j, D⟩ ⟨j', D'⟩ ⟨j'', D''⟩ ⟨rfl, h⟩ ⟨rfl, h'⟩
      refine ⟨rfl, ?_⟩
      simpa [mul_assoc] using Subgroup.mul_mem _ h h'

/-- The sigma form and the flat form of the (j, D) data agree. -/
noncomputable def sigmaEquivJD :
    (Σ j : F, Fˣ ⧸ (powMonoidHom (twistExponent j) : Fˣ →* Fˣ).range) ≃ Quotient (jdSetoid (F := F))
    where
  toFun x := Quotient.liftOn' x.2 (fun D => Quotient.mk _ (x.1, D)) fun D D' h =>
    Quotient.sound ⟨rfl, QuotientGroup.leftRel_apply.mp h⟩
  invFun := Quotient.lift (fun x => ⟨x.1, (x.2 : Fˣ ⧸ _)⟩) <| by
    rintro ⟨j, D⟩ ⟨j', D'⟩ ⟨rfl, h⟩
    exact Sigma.ext rfl (heq_of_eq (QuotientGroup.eq.mpr h))
  left_inv := by
    rintro ⟨j, q⟩
    induction q using QuotientGroup.induction_on with | H D => rfl
  right_inv x := by
    induction x using Quotient.inductionOn with | h x => rfl

variable [NeZero (6 : F)]

/-- **The (j, D) classification**, flat form: a curve away from 6 is a pair `(j, D)` up to
`D ↦ D k^{n(j)}`. -/
noncomputable def equivJD : Curve F ≃ Quotient (jdSetoid (F := F)) :=
  equivSigma.trans sigmaEquivJD

/-- The curve with datum `(j, D)` is `D • ofJ j`. -/
theorem equivJD_symm_mk (j : F) (D : Fˣ) :
    equivJD.symm (Quotient.mk _ (j, D)) = D • ofJ j := by
  simp only [equivJD, Equiv.symm_trans_apply]
  exact equivSigma_symm_mk j D

/-- The (j, D) data of the twist `D • ofJ j` of the standard curve are `(j, D)`. -/
theorem equivJD_smul_ofJ (j : F) (D : Fˣ) : equivJD (D • ofJ j) = Quotient.mk _ (j, D) := by
  rw [← Equiv.eq_symm_apply, equivJD_symm_mk]

end Curve
