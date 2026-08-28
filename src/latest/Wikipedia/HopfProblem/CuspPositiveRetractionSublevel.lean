import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Compact small sublevels

A compact positive sublevel of a continuous nonnegative real-valued function
contains its compact zero set. Every open neighborhood of that zero set contains
a sufficiently small positive closed sublevel.
-/

open Set Topology

namespace Wikipedia.HopfProblem.CuspRetraction.Patching

variable {X : Type*} [TopologicalSpace X]

/-- The zero set is compact if a positive closed sublevel is compact. -/
theorem zeroSet_isCompact (f : C(X, ℝ)) {r : ℝ} (hr : 0 < r)
    (hc : IsCompact {x : X | f x ≤ r}) : IsCompact {x : X | f x = 0} := by
  apply hc.of_isClosed_subset (isClosed_eq f.continuous continuous_const)
  intro x hx
  change f x ≤ r
  rw [show f x = 0 from hx]
  exact hr.le

/-- A compact positive sublevel shrinks into any open neighborhood of the zero set. -/
theorem exists_positive_sublevel_subset_open (f : C(X, ℝ))
    (hf : ∀ x, 0 ≤ f x) {r : ℝ} (hr : 0 < r)
    (hc : IsCompact {x : X | f x ≤ r}) {U : Set X} (hU : IsOpen U)
    (hS : {x : X | f x = 0} ⊆ U) :
    ∃ η : ℝ, 0 < η ∧ η ≤ r ∧ {x : X | f x ≤ η} ⊆ U := by
  have hK : IsCompact (f '' ({x : X | f x ≤ r} \ U)) :=
    (hc.diff hU).image f.continuous
  have hzero : (0 : ℝ) ∈ (f '' ({x : X | f x ≤ r} \ U))ᶜ := by
    rintro ⟨x, hx, hfx⟩
    exact hx.2 (hS hfx)
  obtain ⟨a, b, hab, hsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hK.isClosed.isOpen_compl.mem_nhds hzero)
  refine ⟨min r (b / 2), lt_min hr (half_pos hab.2), min_le_left _ _, ?_⟩
  intro x hx
  change f x ≤ min r (b / 2) at hx
  by_contra hxu
  have hfx : f x < b :=
    (hx.trans (min_le_right r (b / 2))).trans_lt (half_lt_self hab.2)
  apply hsub ⟨hab.1.trans_le (hf x), hfx⟩
  exact ⟨x, ⟨hx.trans (min_le_left r (b / 2)), hxu⟩, rfl⟩

end Wikipedia.HopfProblem.CuspRetraction.Patching
