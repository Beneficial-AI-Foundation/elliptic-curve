/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Montgomery.XOnly.Defs
public import Mathlib.Algebra.Group.Even
import all EllipticCurve.Montgomery.XOnly.Defs
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Montgomery models: x-only arithmetic, lemmas

The characterising statements about the x-only arithmetic of `EllipticCurve.Montgomery.XOnly.Defs`:

- which `u` are `u`-coordinates of points (`exists_point_with_u_iff`), and the twist dichotomy
  over a finite field (`exists_point_u_or_twist`);
- the multiples of points with the same `u`-coordinate (`u_nsmul_eq_of_u_eq`), on `M` and on
  its twist (`u_nsmul_eq_u_nsmul_twist`);
- the well-definedness of `xMul` (`xMul_eq_u_nsmul`, `xMul_eq_u_nsmul_twist`), its values at
  `0` and `1`, and `xMul_mul`. -/

public section

universe u

namespace MontgomeryModel

variable {F : Type u} [Field F] {M : MontgomeryModel F}

/-! ### The twist -/

/-- `0` is a square, so a non-square is nonzero. -/
theorem ne_zero_of_not_isSquare {c : F} (hc : ¬ IsSquare c) : c ≠ 0 := fun h =>
  hc (h ▸ IsSquare.zero)

/-! ### Points with a given `u`-coordinate -/

section Points

variable [M.IsNonsingular]

/-- `u` is the `u`-coordinate of a point of `M` iff `u = 0` (the points `∞` and `(0, 0)`) or
`rhs u / B` is a square. -/
theorem exists_point_with_u_iff (u : F) :
    (∃ P : M.Point, P.u = u) ↔ u = 0 ∨ IsSquare (M.rhs u / M.B) := by
  have hB : M.B ≠ 0 := IsNonsingular.B_ne_zero
  constructor
  · rintro ⟨P, rfl⟩
    rcases Point.cases P with rfl | ⟨u, v, h, rfl⟩
    · exact Or.inl u_zero
    · refine Or.inr ⟨v, ?_⟩
      rw [u_some, div_eq_iff hB]
      linear_combination -(equation_iff_rhs.mp h)
  · rintro (rfl | ⟨r, hr⟩)
    · exact ⟨0, u_zero⟩
    · refine ⟨Point.some u r ?_, u_some _⟩
      rw [equation_iff_rhs]
      rw [div_eq_iff hB] at hr
      linear_combination -hr

/-- Over a finite field, every `u` is the `u`-coordinate of a point of `M` or of its twist by a
non-square `c`: `rhs u / B` or `rhs u / (B c)` is a square. -/
theorem exists_point_u_or_twist [Finite F] {c : F} (hc : ¬ IsSquare c) (u : F) :
    (∃ P : M.Point, P.u = u) ∨ ∃ P : (M.twist c).Point, P.u = u := by
  classical
  have hc0 : c ≠ 0 := ne_zero_of_not_isSquare hc
  have := M.isNonsingular_twist hc0
  have hB : M.B ≠ 0 := IsNonsingular.B_ne_zero
  rw [exists_point_with_u_iff, exists_point_with_u_iff, twist_B, twist_rhs]
  by_cases hu : u = 0
  · exact Or.inl (Or.inl hu)
  by_cases hr : IsSquare (M.rhs u / M.B)
  · exact Or.inl (Or.inr hr)
  refine Or.inr (Or.inr ?_)
  by_cases hr0 : M.rhs u = 0
  · rw [hr0, zero_div]
    exact IsSquare.zero
  let _ := Fintype.ofFinite F
  have h1 := quadraticChar_neg_one_iff_not_isSquare.mpr hr
  have h2 := quadraticChar_neg_one_iff_not_isSquare.mpr hc
  rw [← quadraticChar_one_iff_isSquare (div_ne_zero hr0 (mul_ne_zero hB hc0))]
  have h : M.rhs u / M.B = M.rhs u / (M.B * c) * c := by
    field_simp
  rw [h, map_mul, h2] at h1
  linear_combination -h1

end Points

/-! ### Multiples of 2-torsion points and of points with the same `u` -/

private theorem nsmul_of_add_self_eq_zero {G : Type*} [AddMonoid G] {Q : G} (h : Q + Q = 0)
    (n : ℕ) : n • Q = if Even n then 0 else Q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, ih]
    by_cases hn : Even n
    · rw [ite_eq_left hn, ite_eq_right (by rwa [Nat.even_add_one, not_not]), zero_add]
    · rw [ite_eq_right hn, ite_eq_left (by rwa [Nat.even_add_one]), h]

section Nsmul

variable [M.IsNonsingular]

/-- A point with `u = 0` (`∞` or `(0, 0)`) is 2-torsion. -/
theorem add_self_eq_zero_of_u_eq_zero {Q : M.Point} (h : Q.u = 0) : Q + Q = 0 := by
  rcases Point.cases Q with rfl | ⟨u, v, hQ, rfl⟩
  · exact add_zero 0
  · rw [u_some] at h
    subst h
    obtain rfl := v_eq_zero_of_u_eq_zero IsNonsingular.B_ne_zero hQ rfl
    exact some_add_some_eq_zero hQ hQ rfl (by rw [neg_zero])

/-- All multiples of a point with `u = 0` have `u = 0`. -/
theorem u_nsmul_of_u_eq_zero {Q : M.Point} (h : Q.u = 0) (n : ℕ) : (n • Q).u = 0 := by
  rw [nsmul_of_add_self_eq_zero (add_self_eq_zero_of_u_eq_zero h)]
  split_ifs
  · exact u_zero
  · exact h

/-- Two points with the same nonzero `u`-coordinate are equal or opposite. -/
theorem eq_or_eq_neg_of_u_eq {Q Q' : M.Point} (h : Q.u = Q'.u) (hu : Q.u ≠ 0) :
    Q' = Q ∨ Q' = -Q := by
  rcases Point.cases Q with rfl | ⟨u, v, hQ, rfl⟩
  · exact absurd u_zero hu
  rw [u_some] at hu
  rcases Point.cases Q' with rfl | ⟨u', v', hQ', rfl⟩
  · rw [u_some, u_zero] at h
    exact absurd h hu
  rw [u_some, u_some] at h
  subst h
  have hsq : v' ^ 2 = v ^ 2 := by
    apply mul_left_cancel₀ (IsNonsingular.B_ne_zero (M := M))
    unfold Equation at hQ hQ'
    rw [hQ, hQ']
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (by rw [neg_some])

/-- The `u`-coordinate of `n • Q` only depends on the `u`-coordinate of `Q`. -/
theorem u_nsmul_eq_of_u_eq {Q Q' : M.Point} (h : Q.u = Q'.u) (n : ℕ) :
    (n • Q).u = (n • Q').u := by
  by_cases hu : Q.u = 0
  · rw [u_nsmul_of_u_eq_zero hu, u_nsmul_of_u_eq_zero (h ▸ hu)]
  · rcases eq_or_eq_neg_of_u_eq h hu with rfl | rfl
    · rfl
    · rw [neg_nsmul, u_neg]

/-- A `u`-coordinate attained both on `M` and on its twist by a non-square `c` is `0` or that
of a 2-torsion point, and the multiples of the two points have the same `u`. -/
theorem u_nsmul_eq_u_nsmul_twist {c : F} (hc : ¬ IsSquare c) [(M.twist c).IsNonsingular]
    {P : M.Point} {Q : (M.twist c).Point} (h : P.u = Q.u) (n : ℕ) : (n • P).u = (n • Q).u := by
  have hc0 : c ≠ 0 := ne_zero_of_not_isSquare hc
  have hB : M.B ≠ 0 := IsNonsingular.B_ne_zero
  by_cases hu : P.u = 0
  · rw [u_nsmul_of_u_eq_zero hu, u_nsmul_of_u_eq_zero (h ▸ hu)]
  rcases Point.cases P with rfl | ⟨u, v, hP, rfl⟩
  · exact absurd u_zero hu
  rw [u_some] at hu
  rcases Point.cases Q with rfl | ⟨u', w, hQ, rfl⟩
  · rw [u_some, u_zero] at h
    exact absurd h hu
  rw [u_some, u_some] at h
  subst h
  have hP' : M.B * v ^ 2 = M.rhs u := equation_iff_rhs.mp hP
  have hQ' : M.B * c * w ^ 2 = M.rhs u := by
    have := equation_iff_rhs.mp hQ
    rwa [twist_B, twist_rhs] at this
  by_cases hv : v = 0
  · subst hv
    have hw : w = 0 := by
      have h0 : M.B * c * w ^ 2 = 0 := by rw [hQ', ← hP']; ring
      exact (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp h0).resolve_left (mul_ne_zero hB hc0))
    subst hw
    rw [nsmul_of_add_self_eq_zero (some_add_some_eq_zero hP hP rfl (by rw [neg_zero])),
      nsmul_of_add_self_eq_zero (some_add_some_eq_zero hQ hQ rfl (by rw [neg_zero]))]
    split_ifs
    · rw [u_zero, u_zero]
    · rw [u_some, u_some]
  · exfalso
    have hw : w ≠ 0 := by
      rintro rfl
      apply hv
      have h0 : M.B * v ^ 2 = 0 := by rw [hP', ← hQ']; ring
      exact (pow_eq_zero_iff two_ne_zero).mp ((mul_eq_zero.mp h0).resolve_left hB)
    apply hc
    refine ⟨v / w, ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hw hw)]
    apply mul_left_cancel₀ hB
    linear_combination hQ' - hP'

end Nsmul

/-! ### `xMul` -/

section XMul

variable [M.IsNonsingular]

/-- `xMul` computes `u(n • Q)` on the `u`-coordinate of any point `Q` of `M`. -/
theorem xMul_eq_u_nsmul (c : F) (n : ℕ) (Q : M.Point) : M.xMul c n Q.u = (n • Q).u := by
  have h : ∃ P : M.Point, P.u = Q.u := ⟨Q, rfl⟩
  unfold xMul
  rw [dite_eq_left h]
  exact u_nsmul_eq_of_u_eq h.choose_spec n

/-- `xMul` computes `u(n • Q)` on the `u`-coordinate of any point `Q` of the twist by a
non-square `c`. -/
theorem xMul_eq_u_nsmul_twist {c : F} (hc : ¬ IsSquare c) [(M.twist c).IsNonsingular] (n : ℕ)
    (Q : (M.twist c).Point) : M.xMul c n Q.u = (n • Q).u := by
  have hc0 : c ≠ 0 := ne_zero_of_not_isSquare hc
  unfold xMul
  by_cases h : ∃ P : M.Point, P.u = Q.u
  · rw [dite_eq_left h]
    exact u_nsmul_eq_u_nsmul_twist hc h.choose_spec n
  · have h' : ∃ Q' : (M.twist c).Point, Q'.u = Q.u := ⟨Q, rfl⟩
    rw [dite_eq_right h, dite_eq_right hc0, dite_eq_left h']
    exact u_nsmul_eq_of_u_eq h'.choose_spec n

/-- `xMul` at `u = 0` is `0`. -/
@[simp]
theorem xMul_zero_right (c : F) (n : ℕ) : M.xMul c n 0 = 0 := by
  have h := xMul_eq_u_nsmul c n (0 : M.Point)
  rwa [u_zero, smul_zero, u_zero] at h

/-- `xMul` by `0` is `0`. -/
@[simp]
theorem xMul_zero_left (c : F) (u : F) : M.xMul c 0 u = 0 := by
  unfold xMul
  split_ifs <;> simp only [zero_nsmul, u_zero]

/-- `xMul` by `1` is the identity, over a finite field and for a non-square `c` (every `u`
lifts to `M` or to the twist). -/
theorem xMul_one [Finite F] {c : F} (hc : ¬ IsSquare c) (u : F) : M.xMul c 1 u = u := by
  have := M.isNonsingular_twist (ne_zero_of_not_isSquare hc)
  rcases exists_point_u_or_twist (M := M) hc u with ⟨Q, rfl⟩ | ⟨Q, rfl⟩
  · rw [xMul_eq_u_nsmul, one_nsmul]
  · rw [xMul_eq_u_nsmul_twist hc, one_nsmul]

/-- `xMul` by `m * n` is `xMul` by `n` followed by `xMul` by `m`, over a finite field and for a
non-square `c`. -/
theorem xMul_mul [Finite F] {c : F} (hc : ¬ IsSquare c) (m n : ℕ) (u : F) :
    M.xMul c (m * n) u = M.xMul c m (M.xMul c n u) := by
  have := M.isNonsingular_twist (ne_zero_of_not_isSquare hc)
  rcases exists_point_u_or_twist (M := M) hc u with ⟨Q, rfl⟩ | ⟨Q, rfl⟩
  · rw [xMul_eq_u_nsmul, xMul_eq_u_nsmul, xMul_eq_u_nsmul, mul_nsmul']
  · rw [xMul_eq_u_nsmul_twist hc, xMul_eq_u_nsmul_twist hc, xMul_eq_u_nsmul_twist hc,
      mul_nsmul']

end XMul

end MontgomeryModel
