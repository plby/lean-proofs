import Wikipedia.SmoothSixDPoincare.ParametrizedSheetRecognition
import Wikipedia.SmoothSixDPoincare.BigonSheetContacts

/-!
# Full-image recognition on an open neighborhood of the whole bigon

At modeled points use the native inverse-chart recognition theorem. Elsewhere
on the disk, its exact contact description and closedness of the original
sheet give an avoiding neighborhood. The interior of the recognition locus
then contains the entire zero section. No finite-cover choice is needed here.
-/

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SheetRecognition

variable {W E M : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem exists_open_recognition_domain
    (Φ : PartialDiffeomorph 𝓘(ℝ, W) 𝓘(ℝ, E) W M ∞)
    {S : Set M} {A K : Set W} (hS : IsClosed S) (hK : K ⊆ Φ.source)
    (hforward : ∀ z ∈ Φ.source, z ∈ A → Φ z ∈ S)
    (hlocal : ∀ z ∈ Φ.source, z ∈ A →
      ∀ᶠ w in 𝓝 z, w ∈ Φ.source ∧ (Φ w ∈ S ↔ w ∈ A))
    (hcontact : ∀ z ∈ K, Φ z ∈ S ↔ z ∈ A) :
    ∃ U : Set W, IsOpen U ∧ K ⊆ U ∧ U ⊆ Φ.source ∧
      ∀ z ∈ U, Φ z ∈ S ↔ z ∈ A := by
  have hnear : ∀ z ∈ K, ∀ᶠ w in 𝓝 z, w ∈ Φ.source ∧ (Φ w ∈ S ↔ w ∈ A) := by
    intro z hz
    by_cases hzA : z ∈ A
    · exact hlocal z (hK hz) hzA
    have hzS : Φ z ∉ S := fun hs => hzA ((hcontact z hz).mp hs)
    have hΦ : ContinuousAt Φ z :=
      (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hK hz))).continuousAt
    have havoid : ∀ᶠ w in 𝓝 z, Φ w ∉ S :=
      hΦ.preimage_mem_nhds (hS.isOpen_compl.mem_nhds hzS)
    filter_upwards [Φ.open_source.mem_nhds (hK hz), havoid] with w hw hwS
    exact ⟨hw, ⟨fun hs => (hwS hs).elim, fun ha => (hwS (hforward w hw ha)).elim⟩⟩
  let U := interior {z : W | z ∈ Φ.source ∧ (Φ z ∈ S ↔ z ∈ A)}
  have hsub : U ⊆ {z : W | z ∈ Φ.source ∧ (Φ z ∈ S ↔ z ∈ A)} := interior_subset
  exact ⟨U, isOpen_interior, fun z hz => mem_interior_iff_mem_nhds.mpr (hnear z hz),
    fun _ hz => (hsub hz).1, fun _ hz => (hsub hz).2⟩

end Wikipedia.SmoothSixDPoincare.SheetRecognition

namespace Wikipedia.SmoothSixDPoincare.TubularBigon.SheetParametrizedChart

open WhitneyPairModel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
  {k : CleanStripPatch (E := E) S T a k₀ k₁}
  {l : CleanStripPatch (E := E) T S b l₀ l₁}
  {tube : TubularBigon (E := E) S T a b k.map l.map h}
  {d : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) S k.map}
  {e : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) T l.map}
  (c : SheetParametrizedChart tube d e)

/-- Recognize both full original sheet images throughout one open disk neighborhood. -/
theorem exists_open_full_sheet_neighborhood (hS : IsClosed S) (hT : IsClosed T) :
    ∃ U : Set Space, IsOpen U ∧ bigon h ×ˢ {(0 : Plane × Plane)} ⊆ U ∧ U ⊆ c.chart.source ∧
      (∀ z ∈ U, c.chart z ∈ S ↔ z ∈ range firstSheet) ∧
      ∀ z ∈ U, c.chart z ∈ T ↔ z ∈ range (secondSheet h) := by
  have hzero : bigon h ×ˢ {(0 : Plane × Plane)} ⊆ c.chart.source := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact c.source_contains ⟨hp, Metric.mem_closedBall_self c.radius_pos.le⟩
  have hfirst : ∀ z ∈ bigon h ×ˢ {(0 : Plane × Plane)},
      c.chart z ∈ S ↔ z ∈ range firstSheet := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    rw [c.zero_section]
    exact (tube.map_mem_first_iff hp).trans (bigonEmbedding_mem_firstSheet_iff p).symm
  have hsecond : ∀ z ∈ bigon h ×ˢ {(0 : Plane × Plane)},
      c.chart z ∈ T ↔ z ∈ range (secondSheet h) := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    rw [c.zero_section]
    exact (tube.map_mem_second_iff hp).trans (bigonEmbedding_mem_secondSheet_iff h p).symm
  obtain ⟨U, hU, hKU, hUsource, hUS⟩ := SheetRecognition.exists_open_recognition_domain c.chart
    (A := range firstSheet) hS
    hzero (fun z hz ⟨q, hq⟩ => by
      rw [← hq] at hz ⊢
      exact c.lower_mem_sheet hz)
    (fun z hz ⟨q, hq⟩ => by
      rw [← hq] at hz ⊢
      exact c.eventually_lower_mem_iff hz) hfirst
  obtain ⟨V, hV, hKV, -, hVT⟩ := SheetRecognition.exists_open_recognition_domain c.chart
    (A := range (secondSheet h)) hT
    hzero (fun z hz ⟨q, hq⟩ => by
      rw [← hq] at hz ⊢
      exact c.upper_mem_sheet hz)
    (fun z hz ⟨q, hq⟩ => by
      rw [← hq] at hz ⊢
      exact c.eventually_upper_mem_iff hz) hsecond
  exact ⟨U ∩ V, hU.inter hV, fun z hz => ⟨hKU hz, hKV hz⟩,
    fun _ hz => hUsource hz.1, fun z hz => hUS z hz.1, fun z hz => hVT z hz.2⟩

end Wikipedia.SmoothSixDPoincare.TubularBigon.SheetParametrizedChart
