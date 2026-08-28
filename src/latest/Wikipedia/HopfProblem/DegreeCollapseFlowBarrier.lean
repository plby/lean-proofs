import Wikipedia.SmoothSixDPoincare.FlowTrapping
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Strict level barriers from the actual flow derivative

Only the derivative on the boundary level is required to be negative.
The height may increase in the interior after field cancellation.
Continuous induction gives forward invariance, and the nonzero boundary
derivative gives strict entry and the exact sublevel interior.
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

/-- Strict negative speed at a point gives an actual two-sided time interval of strict descent. -/
theorem exists_local_strict_flow_descent {x : X} (hx : D x < 0) :
    ∃ ε : ℝ, 0 < ε ∧ StrictAntiOn (fun t : ℝ => f (F t x)) (Icc (-ε) ε) := by
  have hcont : Continuous (fun t : ℝ => D (F t x)) :=
    hD.comp (F.continuous continuous_id continuous_const)
  have he : ∀ᶠ t : ℝ in 𝓝 0, D (F t x) < 0 := by
    have hx0 : D (F 0 x) < 0 := by simpa only [F.map_zero_apply] using hx
    exact hcont.continuousAt (eventually_lt_nhds hx0)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r / 2, half_pos hr, ?_⟩
  have hfc : Continuous (fun t : ℝ => f (F t x)) :=
    hf.comp (F.continuous continuous_id continuous_const)
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hfc.continuousOn
  intro t ht
  rw [(hder x t).deriv]
  apply hball
  rw [Real.dist_eq, sub_zero, abs_lt]
  have ht' := interior_subset ht
  constructor <;> linarith [ht'.1, ht'.2]

/-- Every point of the sublevel enters its strict sublevel for a short positive time. -/
theorem exists_local_strict_sublevel_entry {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) {x : X} (hx : f x ≤ c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioc (0 : ℝ) ε, f (F t x) < c := by
  rcases hx.lt_or_eq with hx | hx
  · have he : ∀ᶠ t : ℝ in 𝓝 0, f (F t x) < c := by
      have hfc : Continuous (fun t : ℝ => f (F t x)) :=
        hf.comp (F.continuous continuous_id continuous_const)
      have hx0 : f (F 0 x) < c := by simpa only [F.map_zero_apply] using hx
      exact hfc.continuousAt (eventually_lt_nhds hx0)
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
    refine ⟨r / 2, half_pos hr, ?_⟩
    intro t ht
    apply hball
    rw [Real.dist_eq, sub_zero, abs_of_pos ht.1]
    linarith [ht.2]
  · obtain ⟨ε, hε, hanti⟩ := exists_local_strict_flow_descent F hf hD hder (hboundary x hx)
    refine ⟨ε, hε, ?_⟩
    intro t ht
    have hh := hanti (show (0 : ℝ) ∈ Icc (-ε) ε from ⟨by linarith, hε.le⟩)
      (show t ∈ Icc (-ε) ε from ⟨by linarith [ht.1], ht.2⟩) ht.1
    simpa only [F.map_zero_apply, hx] using hh

/-- A negative boundary derivative prevents any forward crossing out of the sublevel. -/
theorem forwardInvariant_sublevel_of_boundary {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) :
    ∀ x, f x ≤ c → ∀ t : ℝ, 0 ≤ t → f (F t x) ≤ c := by
  apply FlowConstruction.forwardInvariant_of_local F (isClosed_le hf continuous_const)
  intro x hx
  obtain ⟨ε, hε, hentry⟩ := exists_local_strict_sublevel_entry F hf hD hder hboundary hx
  refine ⟨ε, hε, ?_⟩
  intro t ht
  rcases ht.1.eq_or_lt with ht0 | htpos
  · simpa only [← ht0, F.map_zero_apply] using hx
  · exact (hentry t ⟨htpos, ht.2⟩).le

omit hD in
/-- The boundary derivative rules out an interior point on the level itself. -/
theorem interior_sublevel_eq_of_boundary {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) :
    interior {x | f x ≤ c} = {x | f x < c} := by
  apply Subset.antisymm
  · intro x hx
    have hle : f x ≤ c :=
      (interior_subset : interior {y | f y ≤ c} ⊆ {y | f y ≤ c}) hx
    apply lt_of_le_of_ne hle
    intro heq
    have hnhds : ∀ᶠ t : ℝ in 𝓝 0, F t x ∈ interior {y | f y ≤ c} := by
      have hfc : Continuous (fun t : ℝ => F t x) :=
        F.continuous continuous_id continuous_const
      have hx0 : F 0 x ∈ interior {y | f y ≤ c} := by
        simpa only [F.map_zero_apply] using hx
      exact hfc.continuousAt (isOpen_interior.mem_nhds hx0)
    have hmax : IsLocalMax (fun t : ℝ => f (F t x)) 0 := by
      filter_upwards [hnhds] with t ht
      change f (F t x) ≤ f (F 0 x)
      rw [F.map_zero_apply, heq]
      exact (interior_subset : interior {y | f y ≤ c} ⊆ {y | f y ≤ c}) ht
    have hz := hmax.hasDerivAt_eq_zero (hder x 0)
    rw [F.map_zero_apply] at hz
    exact (hboundary x heq).ne hz
  · exact interior_maximal (fun _ (hx : f _ < c) => hx.le) (isOpen_lt hf continuous_const)

/-- Every positive time enters the strict sublevel, without any global height monotonicity. -/
theorem strict_sublevel_entry_of_boundary {c : ℝ}
    (hboundary : ∀ x, f x = c → D x < 0) :
    ∀ x, f x ≤ c → ∀ t : ℝ, 0 < t → f (F t x) < c := by
  have hforward := forwardInvariant_sublevel_of_boundary F hf hD hder hboundary
  have hlocal : ∀ x ∈ {y | f y ≤ c}, ∃ ε > (0 : ℝ),
      ∀ t ∈ Ioc 0 ε, F t x ∈ interior {y | f y ≤ c} := by
    intro x hx
    obtain ⟨ε, hε, hentry⟩ := exists_local_strict_sublevel_entry F hf hD hder hboundary hx
    refine ⟨ε, hε, ?_⟩
    intro t ht
    rw [interior_sublevel_eq_of_boundary F hf hder hboundary]
    exact hentry t ht
  intro x hx t ht
  have hi := FlowConstruction.interior_entry_of_local F hforward hlocal x hx t ht
  have hi' : F t x ∈ interior {y | f y ≤ c} := hi
  exact Eq.mp (congrArg (fun S : Set X => F t x ∈ S)
    (interior_sublevel_eq_of_boundary F hf hder hboundary)) hi'

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
