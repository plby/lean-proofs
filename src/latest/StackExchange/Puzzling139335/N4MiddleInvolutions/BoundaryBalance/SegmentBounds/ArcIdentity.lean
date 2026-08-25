import StackExchange.Puzzling139335.Definitions
import Wikipedia.SchoenfliesTheorem.MatchedArc

/-! An arc in one straight segment is the subsegment between its endpoints. -/

open Set

namespace Puzzling139335.N4MiddleInvolutions.BoundaryBalance

/-- A parametrized genuine arc has distinct named endpoints. -/
theorem arc_endpoints_ne {A : Set Plane} {x y : Plane}
    (hA : Schoenflies.IsArcBetween A x y) : x ≠ y := by
  obtain ⟨f, _, hfi, _, hx, hy⟩ := hA
  intro hxy
  exact zero_ne_one (hfi ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
    (hx.trans (hxy.trans hy.symm)))

/-- Uniqueness of subarcs identifies the actual carrier of an arc contained
in a straight segment with its endpoint segment. -/
theorem arc_eq_segment_of_subset_segment {A : Set Plane} {x y a b : Plane}
    (hA : Schoenflies.IsArcBetween A x y) (hsub : A ⊆ segment ℝ a b) :
    A = segment ℝ x y := by
  have hab : a ≠ b := by
    intro heq
    have hx := hsub hA.left_mem
    have hy := hsub hA.right_mem
    rw [heq, segment_same, mem_singleton_iff] at hx hy
    exact arc_endpoints_ne hA (hx.trans hy.symm)
  exact hA.eq_of_subset_arc (Schoenflies.isArcBetween_segment (arc_endpoints_ne hA))
    (Schoenflies.isArcBetween_segment hab) hsub
    ((convex_segment a b).segment_subset (hsub hA.left_mem) (hsub hA.right_mem))

end Puzzling139335.N4MiddleInvolutions.BoundaryBalance
