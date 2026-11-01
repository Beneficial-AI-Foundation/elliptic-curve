/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Weierstrass.Translation
import EllipticCurve.Weierstrass.Affine
import EllipticCurve.Weierstrass.Infinity
import EllipticCurve.Weierstrass.Normal
import Mathlib.Tactic.LinearCombination

/-! # Translations act on points by translation

The automorphism `τ_R` of the function field moves the place of a point `P` to the place of
`P + R` (`pointEquivRationalPlace_symm_congr_translationEquiv`). At a point `P` with
`x(P) ≠ x(R)` the values of `x(ξ + R)`, `y(ξ + R)` at `P` are the chord formulas; at `P = R` the
slope is rewritten as `g(x) / (y + y_R + a₁ x + a₃)`, the tangent slope; at `P = -R` the slope
has a pole, so `x(ξ + R)` does; the point `O` is the one left, by injectivity. -/

public section

universe u

open Polynomial FunctionField.RationalPlace

namespace WeierstrassCurve.Affine

variable {L : Type u} [Field L] {W : WeierstrassCurve.Affine L} [W.IsElliptic]

/-! ### Values of the group-law formulas -/

section Values

variable {P : FunctionField.RationalPlace L W.FunctionField} {x₁ x₂ y₁ ℓ : W.FunctionField}
  {c₁ c₂ d₁ m : L}

omit [W.IsElliptic] in
/-- Values of `addX`. -/
theorem hasValue_addX (h₁ : P.HasValue x₁ c₁) (h₂ : P.HasValue x₂ c₂) (hℓ : P.HasValue ℓ m) :
    P.HasValue ((W.baseChange W.FunctionField).addX x₁ x₂ ℓ) (W.addX c₁ c₂ m) := by
  simp only [addX]
  exact ((((hℓ.pow 2).add ((hasValue_algebraMap _).mul hℓ)).sub (hasValue_algebraMap _)).sub
    h₁).sub h₂

omit [W.IsElliptic] in
/-- Values of `addY`. -/
theorem hasValue_addY (h₁ : P.HasValue x₁ c₁) (h₂ : P.HasValue x₂ c₂) (hy : P.HasValue y₁ d₁)
    (hℓ : P.HasValue ℓ m) :
    P.HasValue ((W.baseChange W.FunctionField).addY x₁ x₂ y₁ ℓ) (W.addY c₁ c₂ d₁ m) := by
  have hX := hasValue_addX (W := W) h₁ h₂ hℓ
  simp only [addY, negY, negAddY] at hX ⊢
  exact (((hℓ.mul (hX.sub h₁)).add hy).neg.sub ((hasValue_algebraMap _).mul hX)).sub
    (hasValue_algebraMap _)

end Values

/-! ### The chord formula for `ξ + R` -/

section Formula

variable (W)

/-- The slope `(y - y_R) / (x - x_R)` of the chord through the generic point and `R`. -/
noncomputable def chordSlope (xR yR : L) : W.FunctionField :=
  (W.fieldY - algebraMap L _ yR) / (W.fieldX - algebraMap L _ xR)

omit [W.IsElliptic] in
/-- `x - c` is a nonzero function. -/
theorem fieldX_sub_ne_zero (c : L) : W.fieldX - algebraMap L W.FunctionField c ≠ 0 := by
  have := W.aeval_fieldX_ne_zero (p := X - C c) (X_sub_C_ne_zero c)
  rwa [map_sub, aeval_X, aeval_C] at this

variable {W}

open Classical in
/-- The coordinates of `ξ + R` for an affine point `R`: the chord formulas. -/
theorem transX_transY_some {xR yR : L} (hR : (W.baseChange L).Nonsingular xR yR) :
    transX (W := W) (.some xR yR hR) = (W.baseChange W.FunctionField).addX W.fieldX
        (algebraMap L _ xR) (W.chordSlope xR yR) ∧
      transY (W := W) (.some xR yR hR) = (W.baseChange W.FunctionField).addY W.fieldX
        (algebraMap L _ xR) W.fieldY (W.chordSlope xR yR) := by
  obtain ⟨h, he⟩ := genericPoint_add_eq (W := W) (.some xR yR hR)
  have hx : W.fieldX ≠ algebraMap L W.FunctionField xR := sub_ne_zero.mp (W.fieldX_sub_ne_zero xR)
  rw [genericPoint_def, Point.map_some] at he
  rw [Point.add_some (fun h => hx (h.1.trans (Algebra.ofId_apply _ _)))] at he
  simp only [Point.some.injEq, Algebra.ofId_apply] at he
  rw [slope_of_X_ne hx] at he
  exact ⟨he.1.symm, he.2.symm⟩

end Formula

/-! ### From values to points -/

/-- A rational place where `x`, `y` take the values `(a, b)` is the place of the point `(a, b)`. -/
theorem pointEquivRationalPlace_symm_eq_some {Q : FunctionField.RationalPlace L W.FunctionField}
    {a b : L} (h : W.Nonsingular a b) (hx : Q.HasValue W.fieldX a) (hy : Q.HasValue W.fieldY b) :
    W.pointEquivRationalPlace.symm Q = .some a b h := by
  rw [Equiv.symm_apply_eq, eq_pointRationalPlace h hx hy]
  obtain ⟨hx', hy', ex, ey⟩ := W.pointEquivRationalPlace_some a b h
  exact (eq_pointRationalPlace h (hasValue_iff.mpr ⟨hx', ex⟩) (hasValue_iff.mpr ⟨hy', ey⟩)).symm

/-- A rational place where `x` has a pole is the place of `0`. -/
theorem pointEquivRationalPlace_symm_eq_zero {Q : FunctionField.RationalPlace L W.FunctionField}
    (hx : W.fieldX ∉ Q.1.ring) : W.pointEquivRationalPlace.symm Q = 0 := by
  rw [Equiv.symm_apply_eq]
  exact Subtype.ext (FunctionField.Place.ext (eq_of_fieldX_not_mem Q.1.algebraMap_mem hx
    (W.pointEquivRationalPlace 0).1.algebraMap_mem W.fieldX_not_mem_pointEquivRationalPlace_zero))

theorem hasValue_fieldX_some {a b : L} (h : W.Nonsingular a b) :
    (W.pointEquivRationalPlace (.some a b h)).HasValue W.fieldX a := by
  obtain ⟨hx, -, ex, -⟩ := W.pointEquivRationalPlace_some a b h
  exact hasValue_iff.mpr ⟨hx, ex⟩

theorem hasValue_fieldY_some {a b : L} (h : W.Nonsingular a b) :
    (W.pointEquivRationalPlace (.some a b h)).HasValue W.fieldY b := by
  obtain ⟨-, hy, -, ey⟩ := W.pointEquivRationalPlace_some a b h
  exact hasValue_iff.mpr ⟨hy, ey⟩

/-! ### The tangent slope -/

section Tangent

variable (W)

/-- The function `y + y_R + a₁ x + a₃`. -/
noncomputable def tanS (yR : L) : W.FunctionField :=
  W.fieldY + algebraMap L _ (yR + W.a₃) + algebraMap L _ W.a₁ * W.fieldX

/-- The function `g(x) = x² + x_R x + x_R² + a₂ (x + x_R) + a₄ - a₁ y_R`. -/
noncomputable def tanG (xR yR : L) : W.FunctionField :=
  W.fieldX ^ 2 + algebraMap L _ (xR + W.a₂) * W.fieldX +
    algebraMap L _ (xR ^ 2 + W.a₂ * xR + W.a₄ - W.a₁ * yR)

variable {W}

omit [W.IsElliptic] in
/-- The identity `(y - y_R)(y + y_R + a₁ x + a₃) = (x - x_R) g(x)` for a point `R` on `W`. -/
theorem chord_mul_tanS {xR yR : L} (hR : W.Equation xR yR) :
    (W.fieldY - algebraMap L _ yR) * W.tanS yR =
      (W.fieldX - algebraMap L _ xR) * W.tanG xR yR := by
  have h := W.fieldY_equation
  have hR' := congrArg (algebraMap L W.FunctionField) ((equation_iff _ _).mp hR)
  simp only [map_add, map_mul, map_pow] at hR'
  simp only [tanS, tanG, map_add, map_mul, map_pow, map_sub]
  linear_combination h - hR'

omit [W.IsElliptic] in
/-- The function `s` is nonzero. -/
theorem tanS_ne_zero (yR : L) : W.tanS yR ≠ 0 := by
  intro h0
  have := (W.eq_zero_of_aeval_add_aeval_mul_fieldY (p := C (yR + W.a₃) + C W.a₁ * X) (q := 1)
    (by rw [← h0, tanS]; simp only [map_add, map_mul, aeval_C, aeval_X, map_one, one_mul]; ring)).2
  exact one_ne_zero this

omit [W.IsElliptic] in
/-- Off the vertical through `R`, the chord slope is `g / s`. -/
theorem chordSlope_eq {xR yR : L} (hR : W.Equation xR yR) :
    W.chordSlope xR yR = W.tanG xR yR / W.tanS yR := by
  rw [chordSlope, div_eq_div_iff (W.fieldX_sub_ne_zero xR) (tanS_ne_zero yR)]
  linear_combination chord_mul_tanS hR

variable {P : FunctionField.RationalPlace L W.FunctionField} {a b : L}

omit [W.IsElliptic] in
/-- The value of `s` at a place. -/
theorem hasValue_tanS (hx : P.HasValue W.fieldX a) (hy : P.HasValue W.fieldY b) (yR : L) :
    P.HasValue (W.tanS yR) (b + (yR + W.a₃) + W.a₁ * a) :=
  (hy.add (hasValue_algebraMap _)).add ((hasValue_algebraMap _).mul hx)

omit [W.IsElliptic] in
/-- The value of `g` at a place. -/
theorem hasValue_tanG (hx : P.HasValue W.fieldX a) (xR yR : L) :
    P.HasValue (W.tanG xR yR)
      (a ^ 2 + (xR + W.a₂) * a + (xR ^ 2 + W.a₂ * xR + W.a₄ - W.a₁ * yR)) :=
  ((hx.pow 2).add ((hasValue_algebraMap _).mul hx)).add (hasValue_algebraMap _)

end Tangent

/-! ### Translations act by translation -/

section Action

open Classical in
/-- The translation by `0` is the identity. -/
theorem translation_zero : translation (W := W) 0 = AlgHom.id L W.FunctionField := by
  have key := map_translation_genericPoint (W := W) 0
  rw [_root_.map_zero, add_zero, genericPoint_def, Point.map_some] at key
  simp only [Point.some.injEq] at key
  exact algHom_ext_fieldX_fieldY key.1 key.2

open Classical in
/-- The common conclusion: if the slope has the value `slope(P, R)` at the place of an affine
point `P ≠ -R`, the translation moves `P` to `P + R`. -/
theorem translation_affine_of_hasValue {xR yR x₀ y₀ : L} (hR : W.Nonsingular xR yR)
    (h₀ : W.Nonsingular x₀ y₀) (hxy : ¬(x₀ = xR ∧ y₀ = W.negY xR yR))
    (hsl : (W.pointEquivRationalPlace (.some x₀ y₀ h₀)).HasValue (W.chordSlope xR yR)
      (W.slope x₀ xR y₀ yR)) :
    W.pointEquivRationalPlace.symm (FunctionField.RationalPlace.congr
      (translationEquiv (W.toBaseChange (.some xR yR hR)))
        (W.pointEquivRationalPlace (.some x₀ y₀ h₀))) = .some x₀ y₀ h₀ + .some xR yR hR := by
  obtain ⟨hR', hR'eq⟩ := W.toBaseChange_some hR
  obtain ⟨eX, eY⟩ := transX_transY_some (W := W) hR'
  have hx := hasValue_fieldX_some h₀
  have hy := hasValue_fieldY_some h₀
  rw [Point.add_some hxy]
  apply pointEquivRationalPlace_symm_eq_some
  · rw [hasValue_congr_iff, translationEquiv_apply, hR'eq, translation_fieldX, eX]
    exact hasValue_addX hx (hasValue_algebraMap _) hsl
  · rw [hasValue_congr_iff, translationEquiv_apply, hR'eq, translation_fieldY, eY]
    exact hasValue_addY hx (hasValue_algebraMap _) hy hsl

open Classical in
/-- **The chord case**: `x(P) ≠ x(R)`. -/
theorem hasValue_chordSlope_of_ne {xR yR x₀ y₀ : L} (h₀ : W.Nonsingular x₀ y₀) (hx₀ : x₀ ≠ xR) :
    (W.pointEquivRationalPlace (.some x₀ y₀ h₀)).HasValue (W.chordSlope xR yR)
      (W.slope x₀ xR y₀ yR) := by
  rw [slope_of_X_ne hx₀, chordSlope]
  exact ((hasValue_fieldY_some h₀).sub (hasValue_algebraMap _)).div
    ((hasValue_fieldX_some h₀).sub (hasValue_algebraMap _)) (sub_ne_zero.mpr hx₀)

open Classical in
/-- **The tangent case**: `P = R ≠ -R`. -/
theorem hasValue_chordSlope_tangent {xR yR : L} (hR : W.Nonsingular xR yR)
    (hneg : yR ≠ W.negY xR yR) :
    (W.pointEquivRationalPlace (.some xR yR hR)).HasValue (W.chordSlope xR yR)
      (W.slope xR xR yR yR) := by
  rw [slope_of_Y_ne rfl hneg, chordSlope_eq hR.1]
  have hS := hasValue_tanS (hasValue_fieldX_some hR) (hasValue_fieldY_some hR) yR
  have hG := hasValue_tanG (hasValue_fieldX_some hR) xR yR
  have hS0 : yR + (yR + W.a₃) + W.a₁ * xR ≠ 0 := by
    intro h; apply hneg; rw [negY]; linear_combination h
  refine (hG.div hS hS0).congr rfl ?_
  rw [negY]
  congr 1 <;> ring

omit [W.IsElliptic] in
/-- A regular function `λ` with `λ² + a λ` regular (`a` a constant) is regular. -/
theorem mem_of_sq_add_mul_mem {P : FunctionField.RationalPlace L W.FunctionField}
    {lam : W.FunctionField} (c : L) (h : lam ^ 2 + algebraMap L _ c * lam ∈ P.1.ring) :
    lam ∈ P.1.ring := by
  by_contra hl
  have hl0 : lam ≠ 0 := fun h0 => hl (h0 ▸ P.1.ring.zero_mem)
  have hinv := inv_mem_of_not_mem hl
  have e : lam = (lam ^ 2 + algebraMap L _ c * lam) * lam⁻¹ - algebraMap L _ c := by
    field_simp; ring
  exact hl (e ▸ sub_mem (mul_mem h hinv) (P.1.algebraMap_mem c))

open Classical in
/-- **The pole case**: at `P = -R` the chord slope has a pole. -/
theorem chordSlope_not_mem {xR yR : L} (hR : W.Nonsingular xR yR)
    (h₀ : W.Nonsingular xR (W.negY xR yR)) :
    W.chordSlope xR yR ∉ (W.pointEquivRationalPlace (.some xR (W.negY xR yR) h₀)).1.ring := by
  set p := W.pointEquivRationalPlace (.some xR (W.negY xR yR) h₀)
  have hx := hasValue_fieldX_some h₀
  have hy := hasValue_fieldY_some h₀
  intro hl
  by_cases htors : yR = W.negY xR yR
  · -- `R` is `2`-torsion: `λ = g / s` with `g` a unit and `s` vanishing
    rw [chordSlope_eq hR.1] at hl
    have hS := hasValue_tanS hx hy yR
    have hG := hasValue_tanG hx xR yR
    have hS0 : W.negY xR yR + (yR + W.a₃) + W.a₁ * xR = 0 := by
      rw [negY]; ring
    have hG0 : xR ^ 2 + (xR + W.a₂) * xR + (xR ^ 2 + W.a₂ * xR + W.a₄ - W.a₁ * yR) ≠ 0 := by
      rcases ((nonsingular_iff' _ _).mp hR).2 with h | h
      · intro h'; apply h; linear_combination -h'
      · exfalso; apply h; rw [negY] at htors; linear_combination htors
    rw [hS0] at hS
    have hGinv := (hG.inv hG0).mem
    have hGne : W.tanG xR yR ≠ 0 := fun h0 => hG0 (hG.unique
      ((hasValue_algebraMap (P := p) 0).congr (by rw [map_zero, h0]) rfl))
    obtain ⟨hSm, hSe⟩ := hasValue_iff.mp hS
    rcases (eval_eq_zero_iff hSm).mp hSe with h0 | h0
    · exact tanS_ne_zero yR h0
    · apply h0
      have := mul_mem hl hGinv
      have e : W.tanG xR yR / W.tanS yR * (W.tanG xR yR)⁻¹ = (W.tanS yR)⁻¹ := by
        field_simp
      rwa [e] at this
  · -- otherwise `y - y_R` is a unit and `x - x_R` vanishes
    have hY := hy.sub (hasValue_algebraMap (P := p) yR)
    have hX := (hx.sub (hasValue_algebraMap (P := p) xR)).congr rfl (sub_self _)
    have hY0 : W.negY xR yR - yR ≠ 0 := sub_ne_zero.mpr (Ne.symm htors)
    have hYinv := (hY.inv hY0).mem
    obtain ⟨hXm, hXe⟩ := hasValue_iff.mp hX
    rcases (eval_eq_zero_iff hXm).mp hXe with h0 | h0
    · exact W.fieldX_sub_ne_zero xR h0
    · apply h0
      have hYne : W.fieldY - algebraMap L _ yR ≠ 0 := fun h0 => hY0 (hY.unique
        ((hasValue_algebraMap (P := p) 0).congr (by rw [map_zero, h0]) rfl))
      have := mul_mem hl hYinv
      have e : W.chordSlope xR yR * (W.fieldY - algebraMap L _ yR)⁻¹ =
          (W.fieldX - algebraMap L _ xR)⁻¹ := by
        rw [chordSlope]; field_simp
      rwa [e] at this

open Classical in
/-- **Translations act by translation**: the automorphism `τ_R` moves the place of `P` to the
place of `P + R`. -/
theorem pointEquivRationalPlace_symm_congr_translationEquiv (R P : W.Point) :
    W.pointEquivRationalPlace.symm (FunctionField.RationalPlace.congr
      (translationEquiv (W.toBaseChange R)) (W.pointEquivRationalPlace P)) = P + R := by
  cases R with
  | zero =>
    rw [show (Point.zero : W.Point) = 0 from rfl, W.toBaseChange_zero, add_zero]
    have hid : FunctionField.RationalPlace.congr (translationEquiv (W := W) 0)
        (W.pointEquivRationalPlace P) = W.pointEquivRationalPlace P := by
      refine Subtype.ext (FunctionField.Place.ext ?_)
      ext z
      change _ ∈ (FunctionField.RationalPlace.congr _ _).1.ring ↔ _
      rw [FunctionField.RationalPlace.congr_apply_ring, translationEquiv_apply, translation_zero,
        AlgHom.id_apply]
    rw [hid, Equiv.symm_apply_apply]
  | some xR yR hR =>
    set T : W.Point → W.Point := fun Q => W.pointEquivRationalPlace.symm
      (FunctionField.RationalPlace.congr (translationEquiv (W.toBaseChange (.some xR yR hR)))
        (W.pointEquivRationalPlace Q)) with hTdef
    have hT : ∀ Q : W.Point, Q ≠ 0 → T Q = Q + .some xR yR hR := by
      rintro (_ | ⟨x₀, y₀, h₀⟩) hQ
      · exact absurd rfl hQ
      by_cases hx₀ : x₀ = xR
      · subst hx₀
        by_cases hpole : y₀ = W.negY x₀ yR
        · subst hpole
          rw [Point.add_of_Y_eq rfl rfl]
          apply pointEquivRationalPlace_symm_eq_zero
          intro hX
          obtain ⟨hR', hR'eq⟩ := W.toBaseChange_some hR
          rw [FunctionField.RationalPlace.congr_apply_ring, translationEquiv_apply, hR'eq,
            translation_fieldX, (transX_transY_some hR').1] at hX
          apply chordSlope_not_mem hR h₀
          apply mem_of_sq_add_mul_mem W.a₁
          have hx := (hasValue_fieldX_some h₀).mem
          have e : W.chordSlope x₀ yR ^ 2 + algebraMap L _ W.a₁ * W.chordSlope x₀ yR =
              (W.baseChange W.FunctionField).addX W.fieldX (algebraMap L _ x₀)
                (W.chordSlope x₀ yR) + algebraMap L _ W.a₂ + W.fieldX + algebraMap L _ x₀ := by
            simp only [addX]
            rw [show (W.baseChange W.FunctionField).a₁ = algebraMap L _ W.a₁ from rfl,
              show (W.baseChange W.FunctionField).a₂ = algebraMap L _ W.a₂ from rfl]
            ring
          rw [e]
          exact add_mem (add_mem (add_mem hX ((W.pointEquivRationalPlace _).1.algebraMap_mem _))
            hx) ((W.pointEquivRationalPlace _).1.algebraMap_mem _)
        · have hy₀ : y₀ = yR := ((Y_eq_of_X_eq h₀.1 hR.1 rfl).resolve_right hpole)
          subst hy₀
          exact translation_affine_of_hasValue hR h₀ (fun h => hpole h.2)
            (hasValue_chordSlope_tangent hR hpole)
      · exact translation_affine_of_hasValue hR h₀ (fun h => hx₀ h.1)
          (hasValue_chordSlope_of_ne h₀ hx₀)
    have hTinj : Function.Injective T := by
      intro Q₁ Q₂ h
      exact W.pointEquivRationalPlace.injective
        ((FunctionField.RationalPlace.congr _).injective
          (W.pointEquivRationalPlace.symm.injective h))
    cases P with
    | some x₀ y₀ h₀ => exact hT _ (Point.some_ne_zero _)
    | zero =>
      change T 0 = 0 + _
      rw [zero_add]
      by_contra hne
      have h1 : T 0 - .some xR yR hR ≠ 0 := sub_ne_zero.mpr hne
      have h2 := hT _ h1
      rw [sub_add_cancel] at h2
      exact h1 (hTinj h2)

end Action

end WeierstrassCurve.Affine
