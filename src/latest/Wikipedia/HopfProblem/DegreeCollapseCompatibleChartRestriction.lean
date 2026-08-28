import Wikipedia.HopfProblem.DegreeCollapseBigonBranchIsolation
import Wikipedia.SmoothSixDPoincare.CompatibleWhitneyChart

/-!
# Exact Whitney charts restricted to the whole-bigon isolating neighborhood

Restriction keeps the actual map, both exact full-patch recognition
identities, and the whole zero section. Compactness supplies a new positive
tubular radius. The resulting chart sees only the selected source patches.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open Wikipedia.SmoothSixDPoincare WhitneyPairModel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
  {k : CleanStripPatch (E := E) S T a k₀ k₁}
  {l : CleanStripPatch (E := E) T S b l₀ l₁}
  {tube : TubularBigon (E := E) S T a b k.map l.map h}

theorem exists_compatibleChart_in_open (c : TubularBigon.CompatibleChart tube)
    {O : Set M} (hO : IsOpen O) (hB : tube.map '' bigon h ⊆ O) :
    ∃ c' : TubularBigon.CompatibleChart tube,
      c'.chart.target ⊆ O ∧ ∀ z : Space, c'.chart z = c.chart z := by
  let Φ := PartialChart.restrictTarget c.chart hO
  have hz : bigon h ×ˢ {(0 : Plane × Plane)} ⊆ Φ.source := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    refine ⟨c.source_contains ⟨hp, Metric.mem_closedBall_self c.radius_pos.le⟩, ?_⟩
    change c.chart (p, 0) ∈ O
    rw [c.zero_section]
    exact hB ⟨p, hp, rfl⟩
  obtain ⟨ε, hε, hsource⟩ := DiskFraming.exists_pos_prod_closedBall_subset
    (isCompact_bigon tube.height_pos) Φ.open_source hz
  let c' : TubularBigon.CompatibleChart tube := {
    radius := ε
    radius_pos := hε
    chart := Φ
    source_contains := hsource
    zero_section := c.zero_section
    target_subset := fun _ hy => c.target_subset hy.1
    first_sheet := fun z hz => c.first_sheet z hz.1
    second_sheet := fun z hz => c.second_sheet z hz.1 }
  exact ⟨c', fun _ hy => hy.2, fun _ => rfl⟩

theorem exists_branch_isolated_compatibleChart
    {N : Type*} [TopologicalSpace N] [CompactSpace N] [T2Space M]
    (c : TubularBigon.CompatibleChart tube) {F : N → M} (hF : Continuous F)
    {U V : Set N} (hU : IsOpen U) (hV : IsOpen V)
    {O : Set M} (ha : MapsTo a (Icc (0 : ℝ) 1) O) (hb : MapsTo b (Icc (0 : ℝ) 1) O)
    (hpre : F ⁻¹' O ⊆ U ∪ V)
    (havoid : ∀ p ∈ interior (bigon h), tube.map p ∉ range F) :
    ∃ c' : TubularBigon.CompatibleChart tube, F ⁻¹' c'.chart.target ⊆ U ∪ V := by
  obtain ⟨W, hW, hBW, hpreW⟩ :=
    exists_whole_bigon_branch_neighborhood tube hF hU hV ha hb hpre havoid
  obtain ⟨c', htarget, _⟩ := exists_compatibleChart_in_open c hW hBW
  exact ⟨c', fun _ hx => hpreW (htarget hx)⟩

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
