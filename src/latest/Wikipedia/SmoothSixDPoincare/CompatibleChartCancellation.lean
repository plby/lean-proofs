import Wikipedia.SmoothSixDPoincare.CompatibleChartGraphMotion
import Wikipedia.SmoothSixDPoincare.NativeGraphMotion
import Wikipedia.SmoothSixDPoincare.SupportedIntersectionRemoval

/-!
# Removal of exactly the two native Whitney intersections

The full-image chart identifies its original intersection set with the two
endpoints of the actual joining arc. The constructed supported isotopy
removes precisely these points, retaining all other intersections. This
is a native sheet cancellation, not yet a handle-cancellation theorem.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.TubularBigon.CompatibleChart

open WhitneyPairModel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
  {k : CleanStripPatch (E := E) S T a k₀ k₁}
  {l : CleanStripPatch (E := E) T S b l₀ l₁}
  {tube : TubularBigon (E := E) S T a b k.map l.map h}
  (c : CompatibleChart tube)

/-- The entire chart contains exactly the two chosen original intersections. -/
theorem intersection_in_target_eq : (S ∩ T) ∩ c.chart.target = {a 0, a 1} := by
  have hc0 : c.chart (firstSheet (-1, 0)) = a 0 := by
    calc
      c.chart (firstSheet (-1, 0)) = tube.map (-1, 0) := c.zero_section (-1, 0)
      _ = a 0 := by simpa using tube.lower 0 (by simp)
  have hc1 : c.chart (firstSheet (1, 0)) = a 1 := by
    calc
      c.chart (firstSheet (1, 0)) = tube.map (1, 0) := c.zero_section (1, 0)
      _ = a 1 := by
        have he := tube.lower 1 (by simp)
        norm_num at he
        exact he
  have hcorner : ∀ s : ℝ, s = -1 ∨ s = 1 →
      c.chart (firstSheet (s, 0)) ∈ (S ∩ T) ∩ c.chart.target := by
    intro s hs
    have hb : (s, (0 : ℝ)) ∈ bigon h := by
      rcases hs with rfl | rfl <;> simp [bigon]
    have hsource : firstSheet (s, 0) ∈ c.chart.source :=
      c.source_contains ⟨hb, Metric.mem_closedBall_self c.radius_pos.le⟩
    refine ⟨⟨(c.first_sheet _ hsource).mpr ⟨(s, 0), rfl⟩,
      (c.second_sheet _ hsource).mpr ?_⟩, c.chart.map_source' hsource⟩
    refine ⟨(s, 0), ?_⟩
    rcases hs with rfl | rfl <;> simp [firstSheet, secondSheet]
  ext y
  change y ∈ (S ∩ T) ∩ c.chart.target ↔ y = a 0 ∨ y = a 1
  constructor
  · intro hy
    have hz := c.chart.map_target' hy.2
    have hzy : c.chart (c.chart.symm y) = y := c.chart.right_inv' hy.2
    have hlo : c.chart.symm y ∈ range firstSheet := by
      apply (c.first_sheet _ hz).mp
      change c.chart (c.chart.symm y) ∈ S
      rw [hzy]
      exact hy.1.1
    have hhi : c.chart.symm y ∈ range (secondSheet h) := by
      apply (c.second_sheet _ hz).mp
      change c.chart (c.chart.symm y) ∈ T
      rw [hzy]
      exact hy.1.2
    obtain ⟨p, hp⟩ := hlo
    obtain ⟨q, hq⟩ := hhi
    obtain ⟨hst, hu, _, hends⟩ :=
      (firstSheet_eq_secondSheet_iff tube.height_pos p q).mp (hp.trans hq.symm)
    have hpq : p = (q.1, 0) := Prod.ext hst hu
    rw [hpq] at hp
    have hycorner : y = c.chart (firstSheet (q.1, 0)) :=
      hzy.symm.trans (congrArg c.chart hp.symm)
    rcases hends with hm | hp
    · left
      rw [hm] at hycorner
      exact hycorner.trans hc0
    · right
      rw [hp] at hycorner
      exact hycorner.trans hc1
  · rintro (rfl | rfl)
    · rw [← hc0]
      exact hcorner (-1) (Or.inl rfl)
    · rw [← hc1]
      exact hcorner 1 (Or.inr rfl)

variable [T2Space M]

/-- A constructed compactly supported native isotopy removes exactly the two arc endpoints. -/
theorem exists_cancellation :
    ∃ K : Set M, IsCompact K ∧ K ⊆ c.chart.target ∧ ∃ A : ℝ × M → M,
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
      (∀ y, A (0, y) = y) ∧
      (∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ y, A (t, y) = d y) ∧
      (∀ t y, y ∉ K → A (t, y) = y) ∧
      ((fun y => A (1, y)) '' S) ∩ T = (S ∩ T) \ {a 0, a 1} := by
  obtain ⟨K, hK, hKsource, A, hA, hzero, hdiff, hfix, hdisjoint⟩ :=
    exists_supported_native_bigon_cancellation c.chart tube.height_pos
      (fun _ hp => c.source_contains ⟨hp, Metric.mem_closedBall_self c.radius_pos.le⟩)
  rw [c.nativeFirstSheet_eq, c.nativeSecondSheet_eq] at hdisjoint
  obtain ⟨d, hd⟩ := hdiff 1
  have hdfix : ∀ y ∉ c.chart.target, d y = y := by
    intro y hy
    exact (hd y).symm.trans (hfix 1 y (fun h => hy (hKsource h)))
  have hdeq : (fun y => A (1, y)) = d := funext hd
  have hdisjoint' : Disjoint (d '' (S ∩ c.chart.target)) (T ∩ c.chart.target) := by
    rw [← hdeq]
    exact hdisjoint
  have hinter : (d '' S) ∩ T = (S ∩ T) \ c.chart.target :=
    SupportedDiffeomorph.image_inter_eq_diff d.toEquiv hdfix hdisjoint'
  refine ⟨K, hK, hKsource, A, hA, hzero, hdiff, hfix, ?_⟩
  rw [hdeq, hinter, ← c.intersection_in_target_eq]
  ext y
  simp only [mem_sdiff, mem_inter_iff]
  tauto

end Wikipedia.SmoothSixDPoincare.TubularBigon.CompatibleChart
