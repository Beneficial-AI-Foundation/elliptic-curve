/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.Montgomery.Defs
import EllipticCurve.Montgomery.Lemmas
import Mathlib.Algebra.GroupWithZero.Basic

/-! # Montgomery models: x-only arithmetic, definitions

The x-only arithmetic of a Montgomery model `M`, i.e. what depends only on the
`u`-coordinate:

- the nonsingularity of the twist `M.twist c` (`isNonsingular_twist`);
- the hidden x-only scalar multiplication `M.xMul c n u`, defined through any lift of `u` to a
  point of `M` or, failing that, of the twist `M.twist c`, and characterised by
  `xMul_eq_u_nsmul`, `xMul_eq_u_nsmul_twist` (`EllipticCurve.Montgomery.XOnly.Lemmas`).

Algorithms computing `xMul` (the Montgomery ladder, projective `(U : W)` formulas) belong to
applications, not to this library. -/

public section

universe u

namespace MontgomeryModel

variable {F : Type u} [Field F] (M : MontgomeryModel F)

/-! ### The twist -/

/-- The twist of a nonsingular model by `c ≠ 0` is nonsingular. Not an instance, since `c ≠ 0`
is a hypothesis. -/
theorem isNonsingular_twist [M.IsNonsingular] {c : F} (hc : c ≠ 0) :
    (M.twist c).IsNonsingular where
  two_ne_zero := IsNonsingular.two_ne_zero (M := M)
  B_ne_zero := by
    rw [twist_B]
    exact mul_ne_zero IsNonsingular.B_ne_zero hc
  A_sq_ne_four := by
    rw [twist_A]
    exact IsNonsingular.A_sq_ne_four

/-! ### x-only scalar multiplication -/

open Classical in
/-- x-only scalar multiplication `u ↦ u(n • Q)`, total in `u`: through a point `Q` of `M` with
`Q.u = u` if one exists, else through a point of the twist `M.twist c` with that `u` if one
exists, else `0`. Hidden construction, characterised by `xMul_eq_u_nsmul` and
`xMul_eq_u_nsmul_twist` (for `c` a non-square); for a finite field every `u` lifts to `M` or to
the twist (`exists_point_u_or_twist`). -/
noncomputable def xMul [M.IsNonsingular] (c : F) (n : ℕ) (u : F) : F :=
  if h : ∃ Q : M.Point, Q.u = u then (n • h.choose).u
  else if hc : c = 0 then 0
  else
    haveI := M.isNonsingular_twist hc
    if h' : ∃ Q : (M.twist c).Point, Q.u = u then (n • h'.choose).u else 0

end MontgomeryModel
