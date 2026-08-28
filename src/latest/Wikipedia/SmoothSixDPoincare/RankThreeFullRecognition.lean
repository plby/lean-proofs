import Wikipedia.SmoothSixDPoincare.RankThreeLocalRecognition
import Wikipedia.SmoothSixDPoincare.FullSheetRecognition

/-! # Recognition of both full original sheets near the five-dimensional bigon -/

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.RankThreeWhitneyModel

theorem zero_mem_firstSheet_iff (p : ℝ × ℝ) :
    (p, (0 : Lower × Upper)) ∈ range firstSheet ↔ p.2 = 0 := by
  constructor
  · rintro ⟨q, hq⟩
    exact (congrArg (fun z : Space => z.1.2) hq).symm
  · intro hp
    refine ⟨(p.1, 0), ?_⟩
    exact Prod.ext (Prod.ext rfl hp.symm) rfl

theorem zero_mem_secondSheet_iff (h : ℝ) (p : ℝ × ℝ) :
    (p, (0 : Lower × Upper)) ∈ range (secondSheet h) ↔ p.2 = h * (1 - p.1 ^ 2) := by
  constructor
  · rintro ⟨q, hq⟩
    have hs : q.1 = p.1 := congrArg (fun z : Space => z.1.1) hq
    have ht : h * (1 - q.1 ^ 2) = p.2 := congrArg (fun z : Space => z.1.2) hq
    rw [hs] at ht
    exact ht.symm
  · intro hp
    refine ⟨(p.1, 0), ?_⟩
    exact Prod.ext (Prod.ext rfl hp.symm) rfl

end Wikipedia.SmoothSixDPoincare.RankThreeWhitneyModel

namespace Wikipedia.SmoothSixDPoincare.TubularBigon.RankThreeSheetParametrizedChart

open WhitneyPairModel (bigon)
open RankThreeWhitneyModel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
  {k : CleanStripPatch (E := E) S T a k₀ k₁}
  {l : CleanStripPatch (E := E) T S b l₀ l₁}
  {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
  {d : StripNormalData Lower (EuclideanSpace ℝ (Fin 3)) (E := E) S k.map}
  {e : StripNormalData Upper (EuclideanSpace ℝ (Fin 2)) (E := E) T l.map}
  (c : RankThreeSheetParametrizedChart tube d e)

/-- Recognize both full original sheet images throughout one open disk neighborhood. -/
theorem exists_open_full_sheet_neighborhood (hS : IsClosed S) (hT : IsClosed T) :
    ∃ U : Set Space, IsOpen U ∧ bigon h ×ˢ {(0 : Lower × Upper)} ⊆ U ∧ U ⊆ c.chart.source ∧
      (∀ z ∈ U, c.chart z ∈ S ↔ z ∈ range firstSheet) ∧
      ∀ z ∈ U, c.chart z ∈ T ↔ z ∈ range (secondSheet h) := by
  have hzero : bigon h ×ˢ {(0 : Lower × Upper)} ⊆ c.chart.source := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact c.source_contains ⟨hp, Metric.mem_closedBall_self c.radius_pos.le⟩
  have hfirst : ∀ z ∈ bigon h ×ˢ {(0 : Lower × Upper)},
      c.chart z ∈ S ↔ z ∈ range firstSheet := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    rw [c.zero_section]
    exact (tube.map_mem_first_iff hp).trans (zero_mem_firstSheet_iff p).symm
  have hsecond : ∀ z ∈ bigon h ×ˢ {(0 : Lower × Upper)},
      c.chart z ∈ T ↔ z ∈ range (secondSheet h) := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    rw [c.zero_section]
    exact (tube.map_mem_second_iff hp).trans (zero_mem_secondSheet_iff h p).symm
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

end Wikipedia.SmoothSixDPoincare.TubularBigon.RankThreeSheetParametrizedChart
