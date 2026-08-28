import Wikipedia.SmoothSixDPoincare.ParametrizedWhitneyChart
import Wikipedia.SmoothSixDPoincare.LocalSheetRecognition
import Wikipedia.SmoothSixDPoincare.SheetTimeInverse

/-!
# Local full-image recognition in the constructed Whitney chart

The native sheet chart recovers the actual model parameters near every
modeled sheet point. This gives a neighborhood equivalence with membership
in the entire original sheet, for either sheet, including at the corners.
-/

open Set Function Filter Topology
open scoped ContDiff Manifold

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

theorem eventually_lower_mem_iff {q : Sheet} (hq : firstSheet q ∈ c.chart.source) :
    ∀ᶠ z in 𝓝 (firstSheet q), z ∈ c.chart.source ∧ (c.chart z ∈ S ↔ z ∈ range firstSheet) :=
  SheetRecognition.eventually_mem_sheet_iff c.chart d.chart d.sheet
    contDiff_firstSheet.continuous contDiff_sheetTimeInverse.continuous
    sheetTimeInverse_leftInverse sheetTimeInverse_rightInverse
    (fun q hq => ⟨c.lower_source q hq, c.lower q hq⟩) hq

theorem eventually_upper_mem_iff {q : Sheet} (hq : secondSheet h q ∈ c.chart.source) :
    ∀ᶠ z in 𝓝 (secondSheet h q), z ∈ c.chart.source ∧
      (c.chart z ∈ T ↔ z ∈ range (secondSheet h)) :=
  SheetRecognition.eventually_mem_sheet_iff c.chart e.chart e.sheet
    (contDiff_secondSheet h).continuous contDiff_sheetTimeInverse.continuous
    sheetTimeInverse_leftInverse sheetTimeInverse_rightInverse
    (fun q hq => ⟨c.upper_source q hq, c.upper q hq⟩) hq

end Wikipedia.SmoothSixDPoincare.TubularBigon.SheetParametrizedChart
