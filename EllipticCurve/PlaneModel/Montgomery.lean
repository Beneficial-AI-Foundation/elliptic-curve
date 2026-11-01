/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BAIF
-/
module
public import EllipticCurve.PlaneModel.Linear

/-! # The Montgomery model as a plane model

The Montgomery model `B v² = u³ + A u² + u` over its Weierstrass root
`y² = x³ + A B x² + B² x`: the Weierstrass-type plane model with coordinates `u = x / B`,
`v = y / B²` (`PlaneModel.linear`). -/

public section

universe u

variable {F : Type u} [Field F]

namespace PlaneModel

/-- The Weierstrass root of the Montgomery model `(A, B)`: `y² = x³ + A B x² + B² x`. -/
@[expose] def montgomeryRoot (A B : F) : WeierstrassCurve.Affine F :=
  ⟨0, A * B, 0, B ^ 2, 0⟩

/-- The Montgomery model `B v² = u³ + A u² + u`, for `B ≠ 0`: coordinates `u = x / B`,
`v = y / B²` on its root. -/
noncomputable def montgomery (A B : F) (hB : B ≠ 0) : PlaneModel (montgomeryRoot A B) :=
  linear (montgomeryRoot A B) ⟨B, B ^ 2, 0, 0, 0, hB, pow_ne_zero 2 hB⟩

end PlaneModel
