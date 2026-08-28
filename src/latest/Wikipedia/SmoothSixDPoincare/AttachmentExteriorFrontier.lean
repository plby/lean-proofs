import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# The actual frontier of an attachment away from its closed handle piece

Outside the closed added piece, the union has precisely the old frontier.
For a scalar sublevel, that frontier lies on the original scalar level.
-/

open Set

namespace Wikipedia.SmoothSixDPoincare

variable {X : Type*} [TopologicalSpace X]

theorem mem_frontier_union_iff_of_not_mem_closed {A K : Set X} (hK : IsClosed K)
    {x : X} (hx : x ∉ K) : x ∈ frontier (A ∪ K) ↔ x ∈ frontier A := by
  constructor
  · intro h
    rcases frontier_union_subset A K h with ha | hk
    · exact ha.1
    · exact (hx (hK.closure_eq ▸ frontier_subset_closure hk.2)).elim
  · intro h
    refine ⟨closure_mono subset_union_left h.1, ?_⟩
    intro hint
    apply h.2
    apply interior_maximal (s := A) (t := interior (A ∪ K) ∩ Kᶜ) _
      (isOpen_interior.inter hK.isOpen_compl) ⟨hint, hx⟩
    intro y hy
    exact (interior_subset hy.1).resolve_right hy.2

theorem height_of_attachment_frontier {f : X → ℝ} (hf : Continuous f)
    {a : ℝ} {K : Set X} (hK : IsClosed K) {x : X}
    (hfront : x ∈ frontier ({y | f y ≤ a} ∪ K)) (hx : x ∉ K) : f x = a :=
  frontier_le_subset_eq hf continuous_const
    ((mem_frontier_union_iff_of_not_mem_closed hK hx).mp hfront)

end Wikipedia.SmoothSixDPoincare
