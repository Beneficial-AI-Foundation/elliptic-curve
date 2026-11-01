/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.PlaneModel.EdwardsIdentities
public import EllipticCurve.PlaneModel.GroupLaw
import EllipticCurve.FunctionField.Constants

/-! # The twisted Edwards addition formula is the group law, by rigidity

On a complete twisted Edwards curve over `F`,
`coords (P + Q) = f(coords P, coords Q)` (`edwards_coords_add`), proved from identities only:
over `K = F(W)`, the substitutions `σ_q` and `σ_ξ` (`ξ` the generic point) are automorphisms of
the function field moving points by the formula (`EdwardsTranslation.lean`), and the formula is
symmetric with neutral element `(0, 1)`; `coords_add_of_rigidity` does the rest. -/

public section

universe u

open FunctionField.RationalPlace TwistedEdwardsFormula
open WeierstrassCurve.Affine hiding addX addY

namespace PlaneModel

variable {F : Type u} [Field F] {a d : F} {had : a - d ≠ 0} {h2 : (2 : F) ≠ 0}
  [(edwardsRoot a d).IsElliptic]

/-! ### Base change to the function field -/

section BaseChange

variable (a d)

/-- The root over the function field. -/
noncomputable abbrev rootK : WeierstrassCurve.Affine (edwardsRoot a d).FunctionField :=
  edwardsRoot (algebraMap F (edwardsRoot a d).FunctionField a)
    (algebraMap F (edwardsRoot a d).FunctionField d)

omit [(edwardsRoot a d).IsElliptic] in
/-- The base change of the root curve to its own function field. -/
theorem baseChange_eq_rootK :
    (edwardsRoot a d).baseChange (edwardsRoot a d).FunctionField = rootK a d :=
  edwardsRoot_baseChange a d

instance : (rootK a d).IsElliptic := by
  rw [← baseChange_eq_rootK]; infer_instance

open Classical in
/-- Points of the root, over the function field. -/
noncomputable abbrev bc : (edwardsRoot a d).Point →+ (rootK a d).Point :=
  bcPoint (baseChange_eq_rootK a d)

end BaseChange

/-! ### Coordinates over the function field -/

section Coords

omit [(edwardsRoot a d).IsElliptic] in
/-- `a ≠ d` over the function field. -/
theorem had_K (had : a - d ≠ 0) : algebraMap F (edwardsRoot a d).FunctionField a -
    algebraMap F (edwardsRoot a d).FunctionField d ≠ 0 := by
  rw [← map_sub]; exact (map_ne_zero _).mpr had

omit [(edwardsRoot a d).IsElliptic] in
/-- `2 ≠ 0` over the function field. -/
theorem h2_K (h2 : (2 : F) ≠ 0) : (2 : (edwardsRoot a d).FunctionField) ≠ 0 :=
  edwards_two_ne_zero (a := a) (d := d) h2

/-- The Edwards model over the function field. -/
noncomputable abbrev edwardsK (had : a - d ≠ 0) (h2 : (2 : F) ≠ 0) : PlaneModel (rootK a d) :=
  edwards _ _ (had_K had) (h2_K h2)

/-- Exact constants of the function field. -/
theorem hconst_K (z : (edwardsRoot a d).FunctionField) (hz : IsAlgebraic F z) :
    ∃ c : F, z = algebraMap F _ c :=
  FunctionField.RationalPlace.exists_eq_algebraMap_of_isAlgebraic
    ((edwardsRoot a d).pointEquivRationalPlace 0) hz

/-- Completeness over the function field. -/
theorem isComplete_K (hE : (⟨a, d⟩ : TwistedEdwardsModel F).IsComplete) :
    (⟨algebraMap F (edwardsRoot a d).FunctionField a, algebraMap F _ d⟩ :
      TwistedEdwardsModel (edwardsRoot a d).FunctionField).IsComplete :=
  isComplete_map hE hconst_K

/-- The coordinates of a base-changed point are the images of the coordinates. -/
theorem coords_bc (hE : (⟨a, d⟩ : TwistedEdwardsModel F).IsComplete) {P : (edwardsRoot a d).Point}
    {p : F × F} (hP : (edwards a d had h2).coords P = some p) :
    (edwardsK had h2).coords (bc a d P) = some (algebraMap F _ p.1, algebraMap F _ p.2) := by
  cases P with
  | zero =>
    rw [show (Point.zero : (edwardsRoot a d).Point) = 0 from rfl] at hP ⊢
    rw [edwards_coords_zero, Option.some_inj] at hP
    subst hP
    rw [bcPoint_zero, edwards_coords_zero, map_zero, map_one]
  | some x y h =>
    rw [edwards_coords_some hE, Option.some_inj] at hP
    subst hP
    obtain ⟨h', e⟩ := bcPoint_some (baseChange_eq_rootK a d) h
    rw [e, edwards_coords_some (isComplete_K hE), Option.some_inj]
    exact (map_edwardsOfRoot (algebraMap F _) a d x y).symm

/-- The generic point, as a point of the root over the function field. -/
noncomputable abbrev genericK : (rootK a d).Point :=
  genericPt (baseChange_eq_rootK a d)

/-- The coordinates of the generic point are the Edwards coordinate functions. -/
theorem coords_genericK (hE : (⟨a, d⟩ : TwistedEdwardsModel F).IsComplete) :
    (edwardsK had h2).coords (genericK (a := a) (d := d)) =
      some ((edwards a d had h2).x, (edwards a d had h2).y) := by
  unfold genericK
  rw [genericPt_eq, edwards_coords_some (isComplete_K hE),
    Option.some_inj, edwardsOfRoot_of_ne (edwardsRoot a d).fieldY_ne_zero, edwards_x,
    edwards_y, edwardsU_def, edwardsV_def, edwardsB_def]
  simp only [map_div₀, map_ofNat, map_sub]

end Coords

/-! ### Helpers -/

section Helpers

omit [(edwardsRoot a d).IsElliptic] in
/-- The formula is symmetric. -/
theorem addX_comm {K : Type*} [Field K] (d x₁ y₁ x₂ y₂ : K) :
    TwistedEdwardsFormula.addX d x₁ y₁ x₂ y₂ = TwistedEdwardsFormula.addX d x₂ y₂ x₁ y₁ := by
  unfold TwistedEdwardsFormula.addX; congr 1 <;> ring

omit [(edwardsRoot a d).IsElliptic] in
/-- The formula is symmetric. -/
theorem addY_comm {K : Type*} [Field K] (a d x₁ y₁ x₂ y₂ : K) :
    TwistedEdwardsFormula.addY a d x₁ y₁ x₂ y₂ =
      TwistedEdwardsFormula.addY a d x₂ y₂ x₁ y₁ := by
  unfold TwistedEdwardsFormula.addY; congr 1 <;> ring

end Helpers

/-! ### The group law -/

set_option quotPrecheck false in
/-- The function field of the root curve. -/
local notation "𝕂" => (edwardsRoot a d).FunctionField
/-- The constant embedding. -/
local notation "ι" => algebraMap F 𝕂

open Classical in
/-- **The twisted Edwards addition formula is the group law** (away from 6, on a complete
curve), proved from identities by rigidity: `coords (P + Q) = f(coords P, coords Q)`. -/
theorem edwards_coords_add [NeZero (6 : F)] (hE : (⟨a, d⟩ : TwistedEdwardsModel F).IsComplete)
    {P Q : (edwards a d had h2).Point} {p q : F × F}
    (hP : (edwards a d had h2).coords P = some p) (hQ : (edwards a d had h2).coords Q = some q) :
    (edwards a d had h2).coords (P + Q) =
      some (TwistedEdwardsFormula.addX d p.1 p.2 q.1 q.2,
        TwistedEdwardsFormula.addY a d p.1 p.2 q.1 q.2) := by
  have hE' := isComplete_K (a := a) (d := d) hE
  have : (⟨a, d⟩ : TwistedEdwardsModel F).IsComplete := hE
  have hf : (edwardsK had h2).IsAddFormula ((edwardsFormula a d).map ι)
      (fun q => (-q.1, q.2)) := by
    rw [edwardsFormula_map]; exact edwards_isAddFormula hE'
  have h := coords_add_of_isAddFormula (baseChange_eq_rootK a d) hf
    (edwards_coords_isSome (had := had) (h2 := h2))
    (fun u hu => edwards_nonsingular hE' ((eval_edwards_G u).mp hu))
    (coords_bc hE) edwards_coords_zero (coords_genericK hE)
    (fun u _ => by rw [edwardsFormula_map, edwardsFormula_eval]; simp [addX, addY])
    (fun u v _ _ => by
      rw [edwardsFormula_map, edwardsFormula_eval, edwardsFormula_eval, addX_comm, addY_comm])
    hP hQ
  rw [h, edwardsFormula_eval]
  simp

end PlaneModel
