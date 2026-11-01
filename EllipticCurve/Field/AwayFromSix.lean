/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-! # Fields away from 6

The library is about elliptic curves over fields **away from 6**: fields in which `6 ≠ 0`, that
is, of characteristic neither `2` nor `3`. The hypothesis is written `[NeZero (6 : F)]`. This
module derives the nonvanishing of the constants that appear in the theory of curves away from
6: `2`, `3` (as instances) and `1728 = 2⁶ 3³`. -/

public section

variable {F : Type*} [Field F] [NeZero (6 : F)]

/-- Away from 6, `2 ≠ 0`. -/
instance NeZero.two_of_six : NeZero (2 : F) :=
  ⟨fun h => NeZero.ne (6 : F) (by linear_combination 3 * h)⟩

/-- Away from 6, `3 ≠ 0`. -/
instance NeZero.three_of_six : NeZero (3 : F) :=
  ⟨fun h => NeZero.ne (6 : F) (by linear_combination 2 * h)⟩

/-- Away from 6, `1728 ≠ 0`. -/
theorem ne_zero_1728_of_six : (1728 : F) ≠ 0 := by
  rw [show (1728 : F) = 2 ^ 6 * 3 ^ 3 by norm_num]
  exact mul_ne_zero (pow_ne_zero _ (NeZero.ne _)) (pow_ne_zero _ (NeZero.ne _))

/-- Away from 6, `1728 ≠ 0`. -/
instance NeZero.n1728_of_six : NeZero (1728 : F) :=
  ⟨ne_zero_1728_of_six⟩
