import Wikipedia.SmoothSixDPoincare.FlowStoppingTime
import Mathlib.Topology.Order.LeftRight

/-!
# Translating first-entry times along flow trajectories

These identities retain the actual time coordinate, rather than just the
stopped deformation. They will allow continuous radial rescaling of a flow collar.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {X : Type*} [TopologicalSpace X] (F : Flow ℝ X) {A : Set X}

/-- Before entry, nonnegative flow time subtracts exactly from the remaining entry time. -/
theorem entryTime_flow_of_le (hA : IsClosed A)
    {x : X} (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) {t : ℝ}
    (ht : 0 ≤ t) (hle : t ≤ entryTime F A x) :
    entryTime F A (F t x) = entryTime F A x - t := by
  have hhit : F (entryTime F A x - t) (F t x) ∈ A := by
    rw [← F.map_add, sub_add_cancel]
    exact flow_entryTime_mem F hA hx
  have hy : ∃ u : ℝ, 0 ≤ u ∧ F u (F t x) ∈ A :=
    ⟨_, sub_nonneg.mpr hle, hhit⟩
  apply le_antisymm (entryTime_le_of_mem F (sub_nonneg.mpr hle) hhit)
  have hh := flow_entryTime_mem F hA hy
  rw [← F.map_add] at hh
  have hb := entryTime_le_of_mem F
    (add_nonneg (entryTime_nonneg F hy) ht) hh
  linarith

/-- A point already in the interior at a positive time must have entered earlier. -/
theorem entryTime_lt_of_flow_mem_interior {x : X} {t : ℝ} (ht : 0 < t)
    (hx : F t x ∈ interior A) : entryTime F A x < t := by
  have he : ∀ᶠ s in 𝓝 t, 0 < s ∧ F s x ∈ interior A :=
    (eventually_gt_nhds ht).and
      ((F.continuous continuous_id continuous_const).continuousAt.preimage_mem_nhds
        (isOpen_interior.mem_nhds hx))
  obtain ⟨s, hst, hs⟩ := he.exists_lt
  exact (entryTime_le_of_mem F hs.1.le (interior_subset hs.2)).trans_lt hst

/-- If positive time has not finished entry, it adds back to the remaining entry time. -/
theorem entryTime_eq_add_of_flow_pos (hA : IsClosed A)
    (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    {x : X} (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) {t : ℝ} (ht : 0 ≤ t)
    (hpos : 0 < entryTime F A (F t x)) :
    entryTime F A x = t + entryTime F A (F t x) := by
  have hle : t ≤ entryTime F A x := by
    by_contra h
    have hh := (entryTime_le_iff F hA hforward hx ht).mp (le_of_not_ge h)
    rw [entryTime_eq_zero F hh] at hpos
    exact lt_irrefl _ hpos
  rw [entryTime_flow_of_le F hA hx ht hle]
  ring

end Wikipedia.SmoothSixDPoincare.FlowConstruction
