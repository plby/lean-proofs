import Wikipedia.HopfProblem.DegreeCollapseFlowBarrier
import Wikipedia.SmoothSixDPoincare.FlowStoppingTime

/-!
# Directed passage and continuous hitting time across a band

Negative derivatives are needed only at the two boundary levels. Uniform
finite residence then gives one time which carries the entire upper
sublevel strictly below the lower boundary. Reversing this implication
gives backward crossing of the upper boundary. The actual first entry
into the lower sublevel is continuous on the whole upper sublevel.
-/

noncomputable section

open Set Function Filter
open scoped Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {X : Type*} [TopologicalSpace X] (F : Flow ℝ X)
  {f D : X → ℝ} (hf : Continuous f) (hD : Continuous D)
  (hder : ∀ x t, HasDerivAt (fun s : ℝ => f (F s x)) (D (F t x)) t)

include hf hD hder

/-- Finite residence and the two level barriers give uniform directed crossing in both times. -/
theorem exists_uniform_directed_band_crossing {c d : ℝ}
    (hlower : ∀ x, f x = c → D x < 0) (hupper : ∀ x, f x = d → D x < 0)
    (hres : ∃ T : ℝ, 0 < T ∧ ∀ x, ∃ t ∈ Icc (0 : ℝ) T, f (F t x) ∉ Icc c d) :
    ∃ T : ℝ, 0 < T ∧ (∀ x, f x ≤ d → f (F T x) < c) ∧
      ∀ x, c ≤ f x → d < f (F (-T) x) := by
  obtain ⟨T, hT, hexit⟩ := hres
  have hforward : ∀ x, f x ≤ d → f (F T x) < c := by
    intro x hx
    obtain ⟨t, ht, hout⟩ := hexit x
    have hhi := forwardInvariant_sublevel_of_boundary F hf hD hder hupper x hx t ht.1
    have hlo : f (F t x) < c := lt_of_not_ge (fun h => hout ⟨h, hhi⟩)
    rcases ht.2.eq_or_lt with he | he
    · simpa only [he] using hlo
    · have hh := strict_sublevel_entry_of_boundary F hf hD hder hlower
        (F t x) hlo.le (T - t) (sub_pos.mpr he)
      simpa only [← F.map_add, sub_add_cancel] using hh
  refine ⟨T, hT, hforward, ?_⟩
  intro x hx
  apply lt_of_not_ge
  intro hback
  have hh := hforward (F (-T) x) hback
  rw [← F.map_add, add_neg_cancel, F.map_zero_apply] at hh
  exact (not_lt_of_ge hx) hh

/-- The actual lower-sublevel entry time is continuous throughout the upper sublevel. -/
theorem continuousOn_band_entryTime {c d : ℝ}
    (hlower : ∀ x, f x = c → D x < 0) (hupper : ∀ x, f x = d → D x < 0)
    (hres : ∃ T : ℝ, 0 < T ∧ ∀ x, ∃ t ∈ Icc (0 : ℝ) T, f (F t x) ∉ Icc c d) :
    ContinuousOn (FlowConstruction.entryTime F {x | f x ≤ c}) {x | f x ≤ d} := by
  obtain ⟨T, hT, hforward, -⟩ :=
    exists_uniform_directed_band_crossing F hf hD hder hlower hupper hres
  have hclosed : IsClosed {x | f x ≤ c} := isClosed_le hf continuous_const
  have hentry : ∀ x ∈ {y | f y ≤ c}, ∀ t : ℝ, 0 < t → F t x ∈ interior {y | f y ≤ c} := by
    intro x hx t ht
    have hh := strict_sublevel_entry_of_boundary F hf hD hder hlower x hx t ht
    exact Eq.mpr (congrArg (fun S : Set X => F t x ∈ S)
      (interior_sublevel_eq_of_boundary F hf hder hlower)) hh
  exact FlowConstruction.continuousOn_entryTime F hclosed
    (forwardInvariant_sublevel_of_boundary F hf hD hder hlower) hentry
    (fun x hx => ⟨T, hT.le, (hforward x hx).le⟩)

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
