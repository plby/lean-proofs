import Wikipedia.HopfProblem.DegreeCollapseFlowBarrier

/-!
# Signed time to a strictly crossed level

Every real crossing time is unique, not only the first nonnegative one.
Choosing that time on the full level basin gives an exact signed time
coordinate. Its translation identity follows from the original flow law.
No continuity or smoothness of the choice is assumed here.
-/

noncomputable section

open Set Function
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {X : Type*} [TopologicalSpace X]

def levelBasin (F : Flow ℝ X) (f : X → ℝ) (c : ℝ) : Set X :=
  {x | ∃ t : ℝ, f (F t x) = c}

def signedLevelTime (F : Flow ℝ X) (f : X → ℝ) (c : ℝ) (x : X) : ℝ := by
  classical
  exact if h : x ∈ levelBasin F f c then h.choose else 0

theorem signedLevelTime_hits (F : Flow ℝ X) (f : X → ℝ) (c : ℝ) {x : X}
    (hx : x ∈ levelBasin F f c) : f (F (signedLevelTime F f c x) x) = c := by
  rw [signedLevelTime, dif_pos hx]
  exact hx.choose_spec

theorem levelBasin_flow_iff (F : Flow ℝ X) (f : X → ℝ) (c s : ℝ) (x : X) :
    F s x ∈ levelBasin F f c ↔ x ∈ levelBasin F f c := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t + s, by simpa only [F.map_add] using ht⟩
  · rintro ⟨t, ht⟩
    refine ⟨t - s, ?_⟩
    simpa only [← F.map_add, sub_add_cancel] using ht

variable (F : Flow ℝ X) {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
  (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t)
  {c : ℝ} (hboundary : ∀ x, f x = c → D x < 0)

include hf hD hder hboundary

/-- A strictly absorbing level can be crossed at most once over the entire real time axis. -/
theorem flow_level_time_unique (x : X) {s t : ℝ}
    (hs : f (F s x) = c) (ht : f (F t x) = c) : s = t := by
  have hnot {a b : ℝ} (ha : f (F a x) = c) (hb : f (F b x) = c) : ¬ a < b := by
    intro hab
    have hh := strict_sublevel_entry_of_boundary F hf hD hder hboundary
      (F a x) ha.le (b - a) (sub_pos.mpr hab)
    rw [← F.map_add, sub_add_cancel, hb] at hh
    exact lt_irrefl _ hh
  exact le_antisymm (le_of_not_gt (hnot ht hs)) (le_of_not_gt (hnot hs ht))

theorem signedLevelTime_eq_of_level {x : X} {t : ℝ} (ht : f (F t x) = c) :
    signedLevelTime F f c x = t :=
  flow_level_time_unique F hf hD hder hboundary x
    (signedLevelTime_hits F f c ⟨t, ht⟩) ht

theorem signedLevelTime_eq_zero {x : X} (hx : f x = c) : signedLevelTime F f c x = 0 :=
  signedLevelTime_eq_of_level F hf hD hder hboundary (by simpa only [F.map_zero_apply] using hx)

/-- Signed hitting time subtracts exactly the elapsed time along the original flow. -/
theorem signedLevelTime_flow {x : X} (hx : x ∈ levelBasin F f c) (s : ℝ) :
    signedLevelTime F f c (F s x) = signedLevelTime F f c x - s := by
  apply signedLevelTime_eq_of_level F hf hD hder hboundary
  rw [← F.map_add, sub_add_cancel]
  exact signedLevelTime_hits F f c hx

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
