import Wikipedia.SmoothSixDPoincare.FlowEntryTranslation

/-!
# Continuous coordinates on a compact flow collar

The inner core is a fixed positive-time image of the outer region. Both
regions are actual subsets of the ambient space. A strictly absorbing
intermediate set determines a continuous rescaling along each trajectory.
-/

noncomputable section

open Set
open scoped Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {X : Type*} [TopologicalSpace X]

/-- The geometric hypotheses for rescaling the collar between two absorbing sets. -/
structure FlowCollarData (F : Flow ℝ X) (A B : Set X) where
  time : ℝ
  time_pos : 0 < time
  closed_outer : IsClosed B
  closed_inner : IsClosed A
  inner_subset : A ⊆ B
  forward_outer : ∀ x ∈ B, ∀ t : ℝ, 0 ≤ t → F t x ∈ B
  forward_inner : ∀ x ∈ A, ∀ t : ℝ, 0 ≤ t → F t x ∈ A
  strict_outer : ∀ x ∈ B, ∀ t : ℝ, 0 < t → F t x ∈ interior B
  strict_inner : ∀ x ∈ A, ∀ t : ℝ, 0 < t → F t x ∈ interior A
  core_inside : ∀ x ∈ B, F time x ∈ interior A

namespace FlowCollarData

variable {F : Flow ℝ X} {A B : Set X} (d : FlowCollarData F A B)

/-- The actual positive-time image of the outer region. -/
def core : Set X := (F (-d.time)) ⁻¹' B

theorem closed_core : IsClosed d.core :=
  d.closed_outer.preimage (F.continuous continuous_const continuous_id)

theorem core_subset : d.core ⊆ A := by
  intro x hx
  have h := interior_subset (d.core_inside (F (-d.time) x) hx)
  simpa only [← F.map_add, add_neg_cancel, F.map_zero_apply] using h

theorem forward_core : ∀ x ∈ d.core, ∀ t : ℝ, 0 ≤ t → F t x ∈ d.core := by
  intro x hx t ht
  change F (-d.time) (F t x) ∈ B
  rw [← F.map_add, add_comm, F.map_add]
  exact d.forward_outer _ hx t ht

theorem strict_core : ∀ x ∈ d.core, ∀ t : ℝ, 0 < t → F t x ∈ interior d.core := by
  intro x hx t ht
  apply preimage_interior_subset_interior_preimage
    (F.continuous continuous_const continuous_id)
  change F (-d.time) (F t x) ∈ interior B
  rw [← F.map_add, add_comm, F.map_add]
  exact d.strict_outer _ hx t ht

theorem flow_time_mem_core {x : X} (hx : x ∈ B) : F d.time x ∈ d.core := by
  change F (-d.time) (F d.time x) ∈ B
  simpa only [← F.map_add, neg_add_cancel, F.map_zero_apply] using hx

theorem hits_core {x : X} (hx : x ∈ B) :
    ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ d.core :=
  ⟨d.time, d.time_pos.le, d.flow_time_mem_core hx⟩

include d in
theorem hits_inner {x : X} (hx : x ∈ B) :
    ∃ t : ℝ, 0 ≤ t ∧ F t x ∈ A :=
  ⟨d.time, d.time_pos.le, interior_subset (d.core_inside x hx)⟩

/-- Remaining flow time to the inner core. -/
def duration (x : B) : ℝ := entryTime F d.core x.1

theorem duration_nonneg (x : B) : 0 ≤ d.duration x :=
  entryTime_nonneg F (d.hits_core x.2)

theorem duration_le (x : B) : d.duration x ≤ d.time :=
  entryTime_le_of_mem F d.time_pos.le (d.flow_time_mem_core x.2)

theorem continuous_duration : Continuous d.duration :=
  continuousOn_iff_continuous_domRestrict.mp
    (continuousOn_entryTime F d.closed_core d.forward_core d.strict_core
      (fun _ hx => d.hits_core hx))

/-- The start of the length-`time` flow segment through a point in the outer region. -/
def origin (x : B) : B :=
  ⟨F (d.duration x - d.time) x.1, by
    have h := flow_entryTime_mem F d.closed_core (d.hits_core x.2)
    change F (-d.time) (F (d.duration x) x.1) ∈ B at h
    simpa only [← F.map_add, sub_eq_add_neg, add_comm] using h⟩

theorem continuous_origin : Continuous d.origin :=
  (F.continuous (d.continuous_duration.sub continuous_const)
    continuous_subtype_val).subtype_mk _

theorem origin_reconstruct (x : B) :
    F (d.time - d.duration x) (d.origin x).1 = x.1 := by
  change F (d.time - d.duration x) (F (d.duration x - d.time) x.1) = x.1
  rw [← F.map_add, sub_add_sub_cancel, sub_self, F.map_zero_apply]

/-- Time at which the same segment reaches the intermediate absorbing set. -/
def delay (x : B) : ℝ := entryTime F A (d.origin x).1

theorem delay_nonneg (x : B) : 0 ≤ d.delay x :=
  entryTime_nonneg F (d.hits_inner (d.origin x).2)

theorem delay_lt (x : B) : d.delay x < d.time :=
  entryTime_lt_of_flow_mem_interior F d.time_pos (d.core_inside _ (d.origin x).2)

theorem continuous_delay : Continuous d.delay :=
  (continuousOn_iff_continuous_domRestrict.mp
    (continuousOn_entryTime F d.closed_inner d.forward_inner d.strict_inner
      (fun _ hx => d.hits_inner hx))).comp d.continuous_origin

/-- Positive fraction of the original collar length retained inside the intermediate set. -/
def factor (x : B) : ℝ := (d.time - d.delay x) / d.time

theorem factor_pos (x : B) : 0 < d.factor x :=
  div_pos (sub_pos.mpr (d.delay_lt x)) d.time_pos

theorem factor_le_one (x : B) : d.factor x ≤ 1 := by
  apply (div_le_one d.time_pos).mpr
  linarith [d.delay_nonneg x]

theorem time_mul_factor (x : B) : d.time * d.factor x = d.time - d.delay x := by
  dsimp [factor]
  field_simp [d.time_pos.ne']

theorem continuous_factor : Continuous d.factor :=
  (continuous_const.sub d.continuous_delay).div_const _

/-- A point already in the intermediate set lies in the retained part of its segment. -/
theorem duration_le_retained (x : B) (hx : x.1 ∈ A) :
    d.duration x ≤ d.time * d.factor x := by
  have hhit : F (d.time - d.duration x) (d.origin x).1 ∈ A := by
    rwa [d.origin_reconstruct]
  have h := entryTime_le_of_mem F (sub_nonneg.mpr (d.duration_le x)) hhit
  change d.delay x ≤ d.time - d.duration x at h
  rw [d.time_mul_factor]
  linarith

end FlowCollarData
end Wikipedia.SmoothSixDPoincare.FlowConstruction
