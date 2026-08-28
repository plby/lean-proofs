import Wikipedia.SmoothSixDPoincare.SphereCountOrientationUnit
import Wikipedia.SmoothSixDPoincare.MorseCollapseDegree
import Wikipedia.SmoothSixDPoincare.MorseIndexTwoHomology
import Wikipedia.SmoothSixDPoincare.MorseBandHomology
import Wikipedia.SmoothSixDPoincare.TransverseBeltSphere

/-!
# The original index-two homology coordinate and the signed belt count

For an actual transverse embedded two-sphere in the upper level, its
collapse coordinate is its original signed belt-intersection count times
the source orientation unit. Consequently their absolute values agree on
the constructed primitive top class.
-/

noncomputable section

open Set Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open Wikipedia.HopfProblem.SphereHomology
  Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {p : M} (d : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

theorem indexTwoCoordinate_signed_count (q : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (g : C(Hemisphere.Sphere 2, d.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (hg : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (hinj : Function.Injective g)
      (ht : ∀ x y, NativeTransversality.At (𝓡 2) (𝓡 q) 𝓘(ℝ, RegularLevel.Model E)
        g d.surgery.beltSphere x y)
      (a : SingularHomology (UnitSphere 2) 2),
      d.indexTwoCollapseCoordinate hf.continuous hindex
        (singularHomologyMap (d.upperLevelInclusion.comp g) 2 a) =
      d.beltIntersectionCount 2 j g
        (d.finite_beltIntersectionPoints hf q 2 hindex g hg hinj ht) *
          SpherePoint.sourceCountMark 0 j (d.indexTwoNormalModel hindex) a := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg hinj ht a
  have h := SpherePoint.countMark_of_connecting 0 j (d.indexTwoNormalModel hindex)
    _ a _ (d.collapse_homology_signed_count hf q 0 hindex j
      (d.indexTwoNormalModel hindex) g hg hinj ht 1 zero_lt_one 0 a)
  have hc : d.attachingCollapse hf.continuous 2 g =
      (d.upperCollapseMap hf.continuous).comp (d.upperLevelInclusion.comp g) := rfl
  rw [hc, singularHomologyMap_comp] at h
  exact h

theorem indexTwoCoordinate_topClass_natAbs (q : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (g : C(Hemisphere.Sphere 2, d.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (hg : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (hinj : Function.Injective g)
      (ht : ∀ x y, NativeTransversality.At (𝓡 2) (𝓡 q) 𝓘(ℝ, RegularLevel.Model E)
        g d.surgery.beltSphere x y),
      (d.indexTwoCollapseCoordinate hf.continuous hindex
        (singularHomologyMap (d.upperLevelInclusion.comp g) 2 (unitSphereTopClass 1))).natAbs =
      (d.beltIntersectionCount 2 j g
        (d.finite_beltIntersectionPoints hf q 2 hindex g hg hinj ht)).natAbs := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg hinj ht
  rw [d.indexTwoCoordinate_signed_count hf q hindex j g hg hinj ht,
    Int.natAbs_mul, SpherePoint.sourceCountMark_topClass_natAbs, mul_one]

theorem indexTwoCoordinate_transverse_natAbs (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (g : C(Hemisphere.Sphere 2, d.UpperLevel))
    (hgood : d.IsTransverseBeltSphere hf hdim hindex g) :
    (d.indexTwoCollapseCoordinate hf.continuous hindex
      (singularHomologyMap (d.upperLevelInclusion.comp g) 2 (unitSphereTopClass 1))).natAbs =
    (d.beltIntersectionCount 2 j g
      (d.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood)).natAbs := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have h := d.chart.finrank_negative_add_positive; omega⟩
  obtain ⟨hg, hinj, _, ht⟩ := hgood
  exact d.indexTwoCoordinate_topClass_natAbs hf 3 hindex j g hg hinj ht

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
