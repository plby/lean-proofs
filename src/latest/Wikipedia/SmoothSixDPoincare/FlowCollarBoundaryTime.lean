import Wikipedia.SmoothSixDPoincare.FlowCollarBoundary

/-!
# The original backward boundary time of a flow-collar homeomorphism

The time is obtained from the existing forward entry time and the existing
inverse homeomorphism. It is continuous everywhere on the inner region and
reconstructs the original inverse map on the whole inner frontier.
-/

noncomputable section

open Set
open scoped Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction.FlowCollarData

variable {X : Type*} [TopologicalSpace X] [T2Space X] {F : Flow ℝ X} {A B : Set X}
  [CompactSpace B] (d : FlowCollarData F A B)

def inverseBoundaryTime (y : A) : ℝ := -entryTime F A (d.homeomorph.symm y).val

theorem continuous_inverseBoundaryTime : Continuous d.inverseBoundaryTime := by
  have htime : ContinuousOn (entryTime F A) B :=
    continuousOn_entryTime F d.closed_inner d.forward_inner d.strict_inner
      (fun _ hx => d.hits_inner hx)
  exact (htime.comp_continuous
    (continuous_subtype_val.comp d.homeomorph.symm.continuous)
    (fun y => (d.homeomorph.symm y).property)).neg

theorem inverseBoundaryTime_orbit (y : A) (hy : y.val ∈ frontier A) :
    F (d.inverseBoundaryTime y) y.val = (d.homeomorph.symm y).val := by
  let q : B := d.homeomorph.symm y
  have hqy : d.homeomorph q = y := d.homeomorph.apply_symm_apply y
  have hqfront : q.val ∈ frontier B :=
    (d.homeomorph_mem_frontier_iff q).mp (by rwa [hqy])
  have horbit : F (entryTime F A q.val) q.val = y.val :=
    (d.homeomorph_eq_flow_entryTime q hqfront).symm.trans (congrArg Subtype.val hqy)
  change F (-entryTime F A q.val) y.val = q.val
  rw [← horbit, ← F.map_add, neg_add_cancel, F.map_zero_apply]

end Wikipedia.SmoothSixDPoincare.FlowConstruction.FlowCollarData
