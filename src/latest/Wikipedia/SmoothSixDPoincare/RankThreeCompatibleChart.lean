import Wikipedia.SmoothSixDPoincare.RankThreeFullRecognition

/-!
# A constructed Whitney chart for the full original sheets

Restrict the actual native chart to the open full-image recognition locus.
The forward map and global zero section are unchanged. Compactness supplies
a new positive uniform radius. Both full original sheets have exactly their
model preimages throughout the entire chart source.

The original sheets must be closed for this neighborhood result; compact
native sheet images supply this hypothesis in its intended application.
Support containment for the Whitney motion is not asserted here.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.RankThreeWhitneyModel

variable {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Space) J Space M ∞)

def nativeFirstSheet : Set M := Φ '' (range firstSheet ∩ Φ.source)

def nativeSecondSheet (h : ℝ) : Set M := Φ '' (range (secondSheet h) ∩ Φ.source)

end Wikipedia.SmoothSixDPoincare.RankThreeWhitneyModel

namespace Wikipedia.SmoothSixDPoincare.TubularBigon

open WhitneyPairModel (bigon isCompact_bigon)
open RankThreeWhitneyModel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
  {k : CleanStripPatch (E := E) S T a k₀ k₁}
  {l : CleanStripPatch (E := E) T S b l₀ l₁}

/-- An actual positive-radius native chart with exact full-image descriptions of both sheets. -/
structure RankThreeCompatibleChart (tube : TubularBigon (E := E) S T a b k.map l.map h 3) where
  radius : ℝ
  radius_pos : 0 < radius
  chart : PartialDiffeomorph 𝓘(ℝ, Space) 𝓘(ℝ, E) Space M ∞
  source_contains : bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = tube.map p
  target_subset : chart.target ⊆ tube.chart.target
  first_sheet : ∀ z ∈ chart.source, chart z ∈ S ↔ z ∈ range firstSheet
  second_sheet : ∀ z ∈ chart.source, chart z ∈ T ↔ z ∈ range (secondSheet h)

namespace RankThreeSheetParametrizedChart

variable {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
  {d : StripNormalData Lower (EuclideanSpace ℝ (Fin 3)) (E := E) S k.map}
  {e : StripNormalData Upper (EuclideanSpace ℝ (Fin 2)) (E := E) T l.map}

/-- Shrink the parametrized chart to recognize both full original sheets. -/
theorem nonempty_rankThreeCompatibleChart (c : RankThreeSheetParametrizedChart tube d e)
    (hS : IsClosed S) (hT : IsClosed T) : Nonempty (RankThreeCompatibleChart tube) := by
  obtain ⟨U, hU, hKU, hUsource, hfirst, hsecond⟩ := c.exists_open_full_sheet_neighborhood hS hT
  have hlocal : IsLocalDiffeomorphOn 𝓘(ℝ, Space) 𝓘(ℝ, E) ∞ c.chart U :=
    fun z => ⟨c.chart, hUsource z.property, fun _ _ => rfl⟩
  let Φ := partialDiffeomorphOfInjectiveLocal hU (c.chart.toPartialEquiv.injOn.mono hUsource) hlocal
  have hzero : bigon h ×ˢ {(0 : Lower × Upper)} ⊆ Φ.source := hKU
  obtain ⟨ε, hε, hsource⟩ := DiskFraming.exists_pos_prod_closedBall_subset
    (isCompact_bigon tube.height_pos) Φ.open_source hzero
  refine ⟨{
    radius := ε
    radius_pos := hε
    chart := Φ
    source_contains := hsource
    zero_section := c.zero_section
    target_subset := ?_
    first_sheet := hfirst
    second_sheet := hsecond }⟩
  intro y hy
  change y ∈ c.chart '' U at hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact c.target_subset (c.chart.map_source' (hUsource hz))

end RankThreeSheetParametrizedChart

/-- Opposite actual corner signs construct a compatible chart for both closed native sheets. -/
theorem nonempty_rankThreeCompatibleChart_of_opposite_corner_signs
    (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
    (d : StripNormalData Lower (EuclideanSpace ℝ (Fin 3)) (E := E) S k.map)
    (e : StripNormalData Upper (EuclideanSpace ℝ (Fin 2)) (E := E) T l.map)
    (hS : IsClosed S) (hT : IsClosed T)
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    Nonempty (RankThreeCompatibleChart tube) := by
  obtain ⟨c⟩ := tube.nonempty_rankThreeSheetParametrizedChart_of_opposite_corner_signs d e hsign
  exact c.nonempty_rankThreeCompatibleChart hS hT

/-- Compact original sheet images supply closedness; it is not extra geometric input. -/
theorem nonempty_rankThreeCompatibleChart_of_compact_sheet_images
    {N P : Type*} [TopologicalSpace N] [CompactSpace N]
    [TopologicalSpace P] [CompactSpace P] [T2Space M]
    {F : N → M} {G : P → M} (hF : Continuous F) (hG : Continuous G)
    {k : CleanStripPatch (E := E) (range F) (range G) a k₀ k₁}
    {l : CleanStripPatch (E := E) (range G) (range F) b l₀ l₁}
    (tube : TubularBigon (E := E) (range F) (range G) a b k.map l.map h 3)
    (d : StripNormalData Lower (EuclideanSpace ℝ (Fin 3)) (E := E) (range F) k.map)
    (e : StripNormalData Upper (EuclideanSpace ℝ (Fin 2)) (E := E) (range G) l.map)
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    Nonempty (RankThreeCompatibleChart tube) :=
  tube.nonempty_rankThreeCompatibleChart_of_opposite_corner_signs d e
    (isCompact_range hF).isClosed (isCompact_range hG).isClosed hsign

namespace RankThreeCompatibleChart

variable {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
  (c : RankThreeCompatibleChart tube)

/-- The first sheet in the motion theorem is exactly the original sheet inside the chart. -/
theorem nativeFirstSheet_eq : nativeFirstSheet c.chart = S ∩ c.chart.target := by
  ext y
  constructor
  · rintro ⟨z, ⟨hzModel, hzSource⟩, rfl⟩
    exact ⟨(c.first_sheet z hzSource).mpr hzModel, c.chart.map_source' hzSource⟩
  · intro hy
    have hz := c.chart.map_target' hy.2
    have hzy : c.chart (c.chart.symm y) = y := c.chart.right_inv' hy.2
    refine ⟨c.chart.symm y, ⟨?_, hz⟩, hzy⟩
    apply (c.first_sheet _ hz).mp
    change c.chart (c.chart.symm y) ∈ S
    rw [hzy]
    exact hy.1

/-- The second modeled sheet is likewise exactly the full original sheet inside the chart. -/
theorem nativeSecondSheet_eq : nativeSecondSheet c.chart h = T ∩ c.chart.target := by
  ext y
  constructor
  · rintro ⟨z, ⟨hzModel, hzSource⟩, rfl⟩
    exact ⟨(c.second_sheet z hzSource).mpr hzModel, c.chart.map_source' hzSource⟩
  · intro hy
    have hz := c.chart.map_target' hy.2
    have hzy : c.chart (c.chart.symm y) = y := c.chart.right_inv' hy.2
    refine ⟨c.chart.symm y, ⟨?_, hz⟩, hzy⟩
    apply (c.second_sheet _ hz).mp
    change c.chart (c.chart.symm y) ∈ T
    rw [hzy]
    exact hy.1

end RankThreeCompatibleChart

end Wikipedia.SmoothSixDPoincare.TubularBigon
