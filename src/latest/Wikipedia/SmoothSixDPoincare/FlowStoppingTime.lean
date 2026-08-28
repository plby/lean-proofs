import Wikipedia.SmoothSixDPoincare.FlowTrapping
import Mathlib.Topology.Order.Monotone

/-!
# A continuous first-entry time for a strictly absorbing closed set

This is an abstract flow theorem: its closedness, forward invariance,
strict entry, and finite hitting hypotheses are explicit. Applying it to
a Morse attachment requires proving those properties of the actual set.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {X : Type*} [TopologicalSpace X] (F : Flow ℝ X) (A : Set X)

/-- The first nonnegative time the trajectory reaches `A`. Only used on the finite hitting basin. -/
def entryTime (x : X) : ℝ := sInf {t : ℝ | 0 ≤ t ∧ F t x ∈ A}

variable {A}

theorem entryTime_nonneg {x : X} (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) :
    0 ≤ entryTime F A x :=
  le_csInf hx (fun _ ht => ht.1)

theorem entryTime_le_of_mem {x : X} {t : ℝ} (ht : 0 ≤ t) (hx : F t x ∈ A) :
    entryTime F A x ≤ t :=
  csInf_le ⟨0, fun _ hs => hs.1⟩ ⟨ht, hx⟩

/-- Closedness makes the first-entry infimum an actual hitting time. -/
theorem flow_entryTime_mem (hA : IsClosed A) {x : X}
    (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) : F (entryTime F A x) x ∈ A := by
  have hclosed : IsClosed {t : ℝ | 0 ≤ t ∧ F t x ∈ A} :=
    isClosed_Ici.inter (hA.preimage (F.continuous continuous_id continuous_const))
  exact (hclosed.csInf_mem hx ⟨0, fun _ hs => hs.1⟩).2

theorem entryTime_eq_zero {x : X} (hx : x ∈ A) : entryTime F A x = 0 := by
  have hhit : F 0 x ∈ A := by simpa only [F.map_zero_apply] using hx
  exact le_antisymm (entryTime_le_of_mem F le_rfl hhit)
    (entryTime_nonneg F ⟨0, le_rfl, hhit⟩)

/-- Once entry occurs, every later nonnegative time is in the absorbing set. -/
theorem entryTime_le_iff (hA : IsClosed A)
    (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    {x : X} (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) {t : ℝ} (ht : 0 ≤ t) :
    entryTime F A x ≤ t ↔ F t x ∈ A := by
  constructor
  · intro h
    have hh := hforward _ (flow_entryTime_mem F hA hx) (t - entryTime F A x) (sub_nonneg.mpr h)
    rw [← F.map_add, sub_add_cancel] at hh
    exact hh
  · exact entryTime_le_of_mem F ht

theorem flow_mem_interior_of_entryTime_lt (hA : IsClosed A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A)
    {x : X} (hx : ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) {t : ℝ} (ht : entryTime F A x < t) :
    F t x ∈ interior A := by
  have hh := hentry _ (flow_entryTime_mem F hA hx) (t - entryTime F A x) (sub_pos.mpr ht)
  rw [← F.map_add, sub_add_cancel] at hh
  exact hh

/-- A nonnegative hit on the frontier must be the first entry: strict absorption
rules out an earlier hit. -/
theorem entryTime_eq_of_flow_mem_frontier (hA : IsClosed A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A)
    {x : X} {t : ℝ} (ht : 0 ≤ t) (hfront : F t x ∈ frontier A) :
    entryTime F A x = t := by
  have hmem : F t x ∈ A := by
    simpa only [hA.closure_eq] using frontier_subset_closure hfront
  apply le_antisymm (entryTime_le_of_mem F ht hmem)
  apply le_of_not_gt
  intro hlt
  exact hfront.2 (flow_mem_interior_of_entryTime_lt F hA hentry ⟨t, ht, hmem⟩ hlt)

/-- The actual first-entry time is continuous on any subset of the finite hitting basin. -/
theorem continuousOn_entryTime (hA : IsClosed A)
    (hforward : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A)
    (hentry : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A)
    {B : Set X} (hhit : ∀ x ∈ B, ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A) :
    ContinuousOn (entryTime F A) B := by
  intro x hx
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases hneg : a < 0
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact hneg.trans_le (entryTime_nonneg F (hhit y hy))
    · have ha₀ : 0 ≤ a := le_of_not_gt hneg
      have hnot : F a x ∉ A := fun h => not_le_of_gt ha (entryTime_le_of_mem F ha₀ h)
      have hevent : ∀ᶠ y in 𝓝 x, F a y ∉ A :=
        (F.continuous continuous_const continuous_id).continuousAt.preimage_mem_nhds
          (hA.isOpen_compl.mem_nhds hnot)
      filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds hevent]
        with y hy hya
      apply lt_of_not_ge
      intro hle
      exact hya ((entryTime_le_iff F hA hforward (hhit y hy) ha₀).mp hle)
  · intro b hb
    obtain ⟨t, hxt, htb⟩ := exists_between hb
    have ht₀ : 0 ≤ t := (entryTime_nonneg F (hhit x hx)).trans hxt.le
    have hi := flow_mem_interior_of_entryTime_lt F hA hentry (hhit x hx) hxt
    have hevent : ∀ᶠ y in 𝓝 x, F t y ∈ interior A :=
      (F.continuous continuous_const continuous_id).continuousAt.preimage_mem_nhds
        (isOpen_interior.mem_nhds hi)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hevent] with y hy
    exact (entryTime_le_of_mem F ht₀ (interior_subset hy)).trans_lt htb

end Wikipedia.SmoothSixDPoincare.FlowConstruction
