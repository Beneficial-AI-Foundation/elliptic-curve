/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.PlaneModel.Montgomery
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! # The twisted Edwards model as a plane model

The twisted Edwards model `a x² + y² = 1 + d x² y²` on the root of its Montgomery model
`A = 2 (a + d) / (a - d)`, `B = 4 / (a - d)`: with the Montgomery coordinates `u`, `v`, the
coordinates are `x = u / v`, `y = (u - 1) / (u + 1)`. The equation reduces to Montgomery's by
the identity

  `a x² + y² - 1 - d x² y² = 4 u / (B v² (u + 1)²) · (u³ + A u² + u - B v²)`,

and generation by the inverse formulas `u = (1 + y) / (1 - y)`, `v = u / x`. -/

public section

universe u

open MvPolynomial

variable {F : Type u} [Field F]

namespace PlaneModel

/-! ### The identities, as pure algebra -/

section Algebra

variable {K : Type*} [Field K]

/-- The Montgomery equation in the coordinates `u = X / B`, `v = Y / B²`. -/
theorem montgomery_uv {A B X Y : K} (hB : B ≠ 0)
    (h : Y ^ 2 = X ^ 3 + A * B * X ^ 2 + B ^ 2 * X) :
    (X / B) ^ 3 + A * (X / B) ^ 2 + X / B - B * (Y / B ^ 2) ^ 2 = 0 := by
  have e : (X / B) ^ 3 + A * (X / B) ^ 2 + X / B - B * (Y / B ^ 2) ^ 2 =
      (X ^ 3 + A * B * X ^ 2 + B ^ 2 * X - Y ^ 2) / B ^ 3 := by
    field_simp
  rw [e, h, sub_self, zero_div]

/-- The twisted Edwards equation in terms of the Montgomery equation. -/
theorem edwards_eq {a d u v : K} (had : a - d ≠ 0) (hv : v ≠ 0) (hu1 : u + 1 ≠ 0) :
    a * (u / v) ^ 2 + ((u - 1) / (u + 1)) ^ 2 - 1 - d * (u / v) ^ 2 * ((u - 1) / (u + 1)) ^ 2 =
      (a - d) * u / (v ^ 2 * (u + 1) ^ 2) *
        (u ^ 3 + 2 * (a + d) / (a - d) * u ^ 2 + u - 4 / (a - d) * v ^ 2) := by
  field_simp
  ring

/-- The inverse formula `u = (1 + y) / (1 - y)`. -/
theorem edwards_u_eq {u : K} (h2 : (2 : K) ≠ 0) (hu1 : u + 1 ≠ 0) :
    1 - (u - 1) / (u + 1) ≠ 0 ∧ u = (1 + (u - 1) / (u + 1)) / (1 - (u - 1) / (u + 1)) := by
  have h : 1 - (u - 1) / (u + 1) = 2 / (u + 1) := by field_simp; ring
  refine ⟨by rw [h]; exact div_ne_zero h2 hu1, ?_⟩
  rw [h]
  field_simp
  ring

end Algebra

/-- The Weierstrass root of the twisted Edwards model `(a, d)`: the root of its Montgomery model
`A = 2 (a + d) / (a - d)`, `B = 4 / (a - d)`. -/
@[expose] noncomputable def edwardsRoot (a d : F) : WeierstrassCurve.Affine F :=
  montgomeryRoot (2 * (a + d) / (a - d)) (4 / (a - d))

section Edwards

variable {a d : F}

/-- The Montgomery `B = 4 / (a - d)`, in the function field. -/
noncomputable def edwardsB (a d : F) : (edwardsRoot a d).FunctionField :=
  algebraMap F _ (4 / (a - d))

/-- The Montgomery coordinate `u = X / B`. -/
noncomputable def edwardsU (a d : F) : (edwardsRoot a d).FunctionField :=
  (edwardsRoot a d).fieldX / edwardsB a d

/-- The Montgomery coordinate `v = Y / B²`. -/
noncomputable def edwardsV (a d : F) : (edwardsRoot a d).FunctionField :=
  (edwardsRoot a d).fieldY / edwardsB a d ^ 2

/-- The characterising equation of `edwardsB`. -/
theorem edwardsB_def : edwardsB a d = algebraMap F _ (4 / (a - d)) := by
  unfold edwardsB; rfl

/-- The characterising equation of `edwardsU`. -/
theorem edwardsU_def : edwardsU a d = (edwardsRoot a d).fieldX / edwardsB a d := by
  unfold edwardsU; rfl

/-- The characterising equation of `edwardsV`. -/
theorem edwardsV_def : edwardsV a d = (edwardsRoot a d).fieldY / edwardsB a d ^ 2 := by
  unfold edwardsV; rfl

variable (had : a - d ≠ 0) (h2 : (2 : F) ≠ 0)
include had h2

/-- `B = 4 / (a - d)` is nonzero. -/
theorem edwardsB_ne_zero : edwardsB a d ≠ 0 :=
  (map_ne_zero _).mpr (div_ne_zero
    (by rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2) had)

omit h2 in
/-- `a - d` is nonzero in the function field. -/
theorem edwards_sub_ne_zero :
    algebraMap F (edwardsRoot a d).FunctionField a - algebraMap F _ d ≠ 0 := by
  rw [← map_sub]; exact (map_ne_zero _).mpr had

omit had in
/-- `2` is nonzero in the function field. -/
theorem edwards_two_ne_zero : (2 : (edwardsRoot a d).FunctionField) ≠ 0 := by
  rw [← map_ofNat (algebraMap F (edwardsRoot a d).FunctionField) 2]
  exact (map_ne_zero _).mpr h2

omit had h2 in
/-- The root's `x` is a nonzero function. -/
theorem edwards_fieldX_ne_zero : (edwardsRoot a d).fieldX ≠ 0 := by
  simpa using (edwardsRoot a d).aeval_fieldX_ne_zero (p := Polynomial.X) Polynomial.X_ne_zero

/-- The Montgomery `u` is a nonzero function. -/
theorem edwardsU_ne_zero : edwardsU a d ≠ 0 :=
  div_ne_zero edwards_fieldX_ne_zero (edwardsB_ne_zero had h2)

/-- The Montgomery `v` is a nonzero function. -/
theorem edwardsV_ne_zero : edwardsV a d ≠ 0 :=
  div_ne_zero (edwardsRoot a d).fieldY_ne_zero (pow_ne_zero 2 (edwardsB_ne_zero had h2))

/-- The function `u + 1` is nonzero. -/
theorem edwardsU_add_one_ne_zero : edwardsU a d + 1 ≠ 0 := by
  have h := (edwardsRoot a d).aeval_fieldX_ne_zero (p := Polynomial.X + Polynomial.C (4 / (a - d)))
    (Polynomial.X_add_C_ne_zero _)
  simp only [map_add, Polynomial.aeval_X, Polynomial.aeval_C] at h
  rw [edwardsU, div_add_one (edwardsB_ne_zero had h2)]
  exact div_ne_zero h (edwardsB_ne_zero had h2)

/-- The Montgomery equation in `u`, `v`. -/
theorem edwards_montgomery :
    edwardsU a d ^ 3 + algebraMap F _ (2 * (a + d) / (a - d)) * edwardsU a d ^ 2 + edwardsU a d -
      edwardsB a d * edwardsV a d ^ 2 = 0 := by
  have h := (edwardsRoot a d).fieldY_equation
  rw [show (edwardsRoot a d).a₁ = 0 from rfl, show (edwardsRoot a d).a₃ = 0 from rfl,
    show (edwardsRoot a d).a₆ = 0 from rfl,
    show (edwardsRoot a d).a₂ = 2 * (a + d) / (a - d) * (4 / (a - d)) from rfl,
    show (edwardsRoot a d).a₄ = (4 / (a - d)) ^ 2 from rfl, map_zero, map_mul, map_pow] at h
  exact montgomery_uv (edwardsB_ne_zero had h2) (by
    rw [edwardsB]; linear_combination h)

end Edwards

/-- The twisted Edwards model `a x² + y² = 1 + d x² y²`, for `a ≠ d` and `2 ≠ 0`. -/
noncomputable def edwards (a d : F) (had : a - d ≠ 0) (h2 : (2 : F) ≠ 0) :
    PlaneModel (edwardsRoot a d) where
  x := edwardsU a d / edwardsV a d
  y := (edwardsU a d - 1) / (edwardsU a d + 1)
  G := C a * X 0 ^ 2 + X 1 ^ 2 - 1 - C d * X 0 ^ 2 * X 1 ^ 2
  aeval_G := by
    simp only [map_sub, map_add, map_mul, map_pow, map_one, aeval_X, aeval_C,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [edwards_eq (edwards_sub_ne_zero had) (edwardsV_ne_zero had h2)
      (edwardsU_add_one_ne_zero had h2)]
    have hm := edwards_montgomery had h2
    simp only [edwardsB, map_div₀, map_mul, map_add, map_sub, map_ofNat] at hm
    rw [hm, mul_zero]
  adjoin_eq_top := by
    set S := IntermediateField.adjoin F
      {edwardsU a d / edwardsV a d, (edwardsU a d - 1) / (edwardsU a d + 1)}
    have hx : edwardsU a d / edwardsV a d ∈ S :=
      IntermediateField.subset_adjoin F _ (Set.mem_insert _ _)
    have hy : (edwardsU a d - 1) / (edwardsU a d + 1) ∈ S :=
      IntermediateField.subset_adjoin F _ (Set.mem_insert_of_mem _ rfl)
    obtain ⟨-, hu⟩ := edwards_u_eq (edwards_two_ne_zero h2) (edwardsU_add_one_ne_zero had h2)
    have huS : edwardsU a d ∈ S := by
      rw [hu]
      exact div_mem (add_mem (one_mem _) hy) (sub_mem (one_mem _) hy)
    have hvS : edwardsV a d ∈ S := by
      rw [← div_div_cancel₀ (edwardsU_ne_zero had h2) (b := edwardsV a d)]
      exact div_mem huS hx
    have hB := edwardsB_ne_zero had h2
    apply adjoin_eq_top_of_mem
    · have m := mul_mem (IntermediateField.algebraMap_mem S (4 / (a - d))) huS
      rwa [← edwardsB, edwardsU, mul_div_cancel₀ _ hB] at m
    · have m := mul_mem (pow_mem (IntermediateField.algebraMap_mem S (4 / (a - d))) 2) hvS
      rwa [← edwardsB, edwardsV, mul_div_cancel₀ _ (pow_ne_zero 2 hB)] at m

/-- The first coordinate of the twisted Edwards model is `u / v`. -/
theorem edwards_x (a d : F) (had : a - d ≠ 0) (h2 : (2 : F) ≠ 0) :
    (edwards a d had h2).x = edwardsU a d / edwardsV a d := by
  unfold edwards; rfl

/-- The second coordinate of the twisted Edwards model is `(u - 1) / (u + 1)`. -/
theorem edwards_y (a d : F) (had : a - d ≠ 0) (h2 : (2 : F) ≠ 0) :
    (edwards a d had h2).y = (edwardsU a d - 1) / (edwardsU a d + 1) := by
  unfold edwards; rfl

/-- The equation of the twisted Edwards model. -/
theorem edwards_G (a d : F) (had : a - d ≠ 0) (h2 : (2 : F) ≠ 0) :
    (edwards a d had h2).G = C a * X 0 ^ 2 + X 1 ^ 2 - 1 - C d * X 0 ^ 2 * X 1 ^ 2 := by
  unfold edwards; rfl

end PlaneModel
