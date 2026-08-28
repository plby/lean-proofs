import Wikipedia.HopfProblem.DegreeCollapseSignedLevelTime
import Wikipedia.SmoothSixDPoincare.MorseCompactStability

/-!
# Actual compact time tubes around a crossed level

Compactness of the boundary level gives one two-sided time interval whose
whole flow tube stays in any prescribed open neighborhood. Every point
with sufficiently small signed hitting time belongs to that actual tube.
No collar parametrization or abstract compactness of the basin is assumed.
-/

noncomputable section

open Set Function Filter
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {X : Type*} [TopologicalSpace X]

def flowTube (F : Flow ℝ X) (S : Set X) (ε : ℝ) : Set X :=
  (fun q : ℝ × X => F q.1 q.2) '' (Icc (-ε) ε ×ˢ S)

theorem isCompact_flowTube (F : Flow ℝ X) {S : Set X} (hS : IsCompact S) (ε : ℝ) :
    IsCompact (flowTube F S ε) :=
  (isCompact_Icc.prod hS).image (F.continuous continuous_fst continuous_snd)

theorem exists_flowTube_subset (F : Flow ℝ X) {S N : Set X}
    (hS : IsCompact S) (hN : IsOpen N) (hSN : S ⊆ N) :
    ∃ ε : ℝ, 0 < ε ∧ flowTube F S ε ⊆ N := by
  have hopen : IsOpen {t : ℝ | ∀ x ∈ S, F t x ∈ N} :=
    Wikipedia.SmoothSixDPoincare.MorsePerturbation.isOpen_forall_mem_compact hS
      (hN.preimage (F.continuous continuous_fst continuous_snd))
  have hzero : (0 : ℝ) ∈ {t : ℝ | ∀ x ∈ S, F t x ∈ N} := by
    intro x hx
    simpa only [F.map_zero_apply] using hSN hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hzero)
  refine ⟨r / 2, half_pos hr, ?_⟩
  rintro y ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
  apply hball ?_ x hx
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
  constructor <;> linarith [ht.1, ht.2]

theorem mem_flowTube_of_signedTime (F : Flow ℝ X) (f : X → ℝ) (c : ℝ)
    {ε : ℝ} {x : X} (hx : x ∈ levelBasin F f c)
    (ht : |signedLevelTime F f c x| ≤ ε) : x ∈ flowTube F {y | f y = c} ε := by
  refine ⟨(-signedLevelTime F f c x, F (signedLevelTime F f c x) x),
    ⟨?_, signedLevelTime_hits F f c hx⟩, ?_⟩
  · constructor <;> linarith [(abs_le.mp ht).1, (abs_le.mp ht).2]
  · simp only [← F.map_add, neg_add_cancel, F.map_zero_apply]

theorem flowTube_subset_levelBasin (F : Flow ℝ X) (f : X → ℝ) (c ε : ℝ) :
    flowTube F {y | f y = c} ε ⊆ levelBasin F f c := by
  rintro y ⟨⟨t, x⟩, ⟨-, hx⟩, rfl⟩
  change f x = c at hx
  exact (levelBasin_flow_iff F f c t x).mpr
    ⟨0, by simpa only [F.map_zero_apply] using hx⟩

/-- A continuous strictly negative function on a compact set has a uniform
strict negative margin, including when that compact set is empty. -/
theorem exists_compact_negative_margin {S : Set X} (hS : IsCompact S)
    {D : X → ℝ} (hD : ContinuousOn D S) (hneg : ∀ x ∈ S, D x < 0) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x ∈ S, D x < -μ := by
  by_cases hne : S.Nonempty
  · obtain ⟨p, hp, hmax⟩ := hS.exists_isMaxOn hne hD
    refine ⟨-D p / 2, by linarith [hneg p hp], ?_⟩
    intro x hx
    have hle : D x ≤ D p := hmax hx
    linarith [hneg p hp]
  · exact ⟨1, zero_lt_one, fun x hx => (hne ⟨x, hx⟩).elim⟩

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
