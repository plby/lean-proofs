import Mathlib.Order.Interval.Set.IsoIoo
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The open unit interval as the real line

The affine order isomorphism to `(-1,1)` followed by the existing ordered-field
isomorphism gives an actual homeomorphism, without a choice of coordinates.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SixSphereCube

/-- The ordinary open unit interval in the real line. -/
abbrev OpenUnitInterval := Set.Ioo (0 : ℝ) 1

/-- Affine rescaling of the open unit interval. -/
def openUnitIntervalAffineOrderIso : OpenUnitInterval ≃o Set.Ioo (-1 : ℝ) 1 where
  toFun t := ⟨2 * (t : ℝ) - 1, by
    constructor <;> linarith [t.property.1, t.property.2]⟩
  invFun t := ⟨((t : ℝ) + 1) / 2, by
    constructor <;> linarith [t.property.1, t.property.2]⟩
  left_inv t := by
    apply Subtype.ext
    change (2 * (t : ℝ) - 1 + 1) / 2 = (t : ℝ)
    ring
  right_inv t := by
    apply Subtype.ext
    change 2 * (((t : ℝ) + 1) / 2) - 1 = (t : ℝ)
    ring
  map_rel_iff' := by
    intro t s
    change 2 * (t : ℝ) - 1 ≤ 2 * (s : ℝ) - 1 ↔ (t : ℝ) ≤ (s : ℝ)
    constructor <;> intro h <;> linarith

/-- A concrete homeomorphism from `(0,1)` onto the real line. -/
def openUnitIntervalHomeomorph : OpenUnitInterval ≃ₜ ℝ :=
  openUnitIntervalAffineOrderIso.toHomeomorph.trans
    (orderIsoIooNegOneOne ℝ).toHomeomorph.symm

end Wikipedia.HopfProblem.SixSphereCube
