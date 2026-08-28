import Wikipedia.HopfProblem.DegreeCollapseNativeExteriorFlow

/-!
# Connecting orbits meet the actual boundary sections

An actual orbit with critical endpoint limits crosses both intermediate
regular levels in the correct order. When a supported band change retains
the exterior flow tails, its boundary points have the original endpoint
limits. Thus the new infinite-time connection supplies a finite transition
between the original ascending and descending boundary sets.
-/

noncomputable section

open Set Function Filter
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {X : Type*} [TopologicalSpace X]

/-- A continuous orbit with endpoint heights on opposite sides meets the intermediate level. -/
theorem exists_level_crossing_of_endpoint_limits (F : Flow ℝ X) {f : X → ℝ}
    (hf : Continuous f) {x p q : X}
    (hp : Tendsto (fun t => F t x) atBot (𝓝 p))
    (hq : Tendsto (fun t => F t x) atTop (𝓝 q))
    {c : ℝ} (hpc : c < f p) (hqc : f q < c) : ∃ t, f (F t x) = c := by
  have htop : Tendsto (fun t => f (F t x)) atTop (𝓝 (f q)) := hf.continuousAt.tendsto.comp hq
  have hbot : Tendsto (fun t => f (F t x)) atBot (𝓝 (f p)) := hf.continuousAt.tendsto.comp hp
  obtain ⟨s, hs⟩ := (htop.eventually (eventually_lt_nhds hqc)).exists
  obtain ⟨t, ht⟩ := (hbot.eventually (eventually_gt_nhds hpc)).exists
  exact mem_range_of_exists_le_of_exists_ge
    (hf.comp (F.continuous continuous_id continuous_const)) ⟨s, hs.le⟩ ⟨t, ht.le⟩

/-- A connection for the modified flow gives an ordered finite segment
whose boundary points retain the original flow's two endpoint limits. -/
theorem exists_connection_section_segment (F G : Flow ℝ X) {f D : X → ℝ}
    (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s => f (G s x)) (D (G t x)) t)
    {a b : ℝ} (hab : a < b) (hboundary : ∀ x, f x = a → D x < 0)
    (hlo : ∀ x, f x = a → ∀ t : ℝ, 0 ≤ t → G t x = F t x)
    (hhi : ∀ x, f x = b → ∀ t : ℝ, t ≤ 0 → G t x = F t x)
    {x p q : X} (hpb : b < f p) (hqa : f q < a)
    (hp : Tendsto (fun t => G t x) atBot (𝓝 p))
    (hq : Tendsto (fun t => G t x) atTop (𝓝 q)) :
    ∃ (u v : X) (T s : ℝ), f u = b ∧ f v = a ∧ 0 < T ∧
      G T u = v ∧ G s u = x ∧
      Tendsto (fun t => F t u) atBot (𝓝 p) ∧
      Tendsto (fun t => F t v) atTop (𝓝 q) := by
  obtain ⟨tb, htb⟩ := exists_level_crossing_of_endpoint_limits G hf hp hq hpb (hqa.trans hab)
  obtain ⟨ta, hta⟩ := exists_level_crossing_of_endpoint_limits G hf hp hq (hab.trans hpb) hqa
  have horder : tb < ta := by
    by_contra hn
    have hh := forwardInvariant_sublevel_of_boundary G hf hD hder hboundary
      (G ta x) hta.le (tb - ta) (sub_nonneg.mpr (le_of_not_gt hn))
    rw [← G.map_add, sub_add_cancel, htb] at hh
    exact (not_le_of_gt hab) hh
  have hp' : Tendsto (fun t => G t (G tb x)) atBot (𝓝 p) := by
    simpa only [comp_def, id_eq, ← G.map_add] using
      hp.comp (tendsto_atBot_add_const_right atBot tb tendsto_id)
  have hq' : Tendsto (fun t => G t (G ta x)) atTop (𝓝 q) := by
    simpa only [comp_def, id_eq, ← G.map_add] using
      hq.comp (tendsto_atTop_add_const_right atTop ta tendsto_id)
  refine ⟨G tb x, G ta x, ta - tb, -tb, htb, hta, sub_pos.mpr horder, ?_, ?_, ?_, ?_⟩
  · rw [← G.map_add, sub_add_cancel]
  · rw [← G.map_add, neg_add_cancel, G.map_zero_apply]
  · apply hp'.congr'
    filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
    exact hhi (G tb x) htb t ht
  · apply hq'.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hlo (G ta x) hta t ht

/-- Uniqueness of the finite transition intersection proves uniqueness of
the actual complete connecting orbit after the band perturbation. -/
theorem unique_connection_of_section_intersections (F G : Flow ℝ X) {f D : X → ℝ}
    (hf : Continuous f) (hD : Continuous D)
    (hder : ∀ x t, HasDerivAt (fun s => f (G s x)) (D (G t x)) t)
    {a b : ℝ} (hab : a < b) (hboundary : ∀ x, f x = a → D x < 0)
    (hlo : ∀ x, f x = a → ∀ t : ℝ, 0 ≤ t → G t x = F t x)
    (hhi : ∀ x, f x = b → ∀ t : ℝ, t ≤ 0 → G t x = F t x)
    {p q z : X} (hpb : b < f p) (hqa : f q < a)
    (hsection : ∀ u, f u = b → Tendsto (fun t => F t u) atBot (𝓝 p) →
      ∀ T : ℝ, 0 < T → f (G T u) = a →
        Tendsto (fun t => F t (G T u)) atTop (𝓝 q) → u = z) :
    ∀ x, Tendsto (fun t => G t x) atBot (𝓝 p) →
      Tendsto (fun t => G t x) atTop (𝓝 q) → ∃ s, G s z = x := by
  intro x hp hq
  obtain ⟨u, v, T, s, hu, hv, hT, hTv, hs, hup, hvq⟩ :=
    exists_connection_section_segment F G hf hD hder hab hboundary hlo hhi hpb hqa hp hq
  have hfirst : u = z := hsection u hu hup T hT ((congrArg f hTv).trans hv)
    (by rw [hTv]; exact hvq)
  exact ⟨s, hfirst ▸ hs⟩

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
