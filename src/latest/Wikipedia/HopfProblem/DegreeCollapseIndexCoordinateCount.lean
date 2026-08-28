import Wikipedia.HopfProblem.DegreeCollapseIndexHomologyBasis
import Wikipedia.SmoothSixDPoincare.SphereCountOrientationUnit
import Wikipedia.SmoothSixDPoincare.MorseCollapseDegree
import Wikipedia.SmoothSixDPoincare.MorseBandHomology

/-!
# The actual integral collapse coordinate equals the native signed belt count

The coherent basis coordinate uses the original upper collapse map and
its fixed integer marking. The native signed-count formula therefore
identifies it with the actual belt count times the source orientation
unit. Their absolute values on the primitive sphere class agree. The
case k=1 applies to the remaining three/four handles in dimension seven.
-/

noncomputable section

open Set Metric Function ContinuousMap
open scoped ContDiff Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleBasis

open SphereHomology SingularMayerVietoris PeriodTorusHigherHomology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {p : M} (d : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

theorem coordinate_signed_count (q k : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = k + 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient ((k + 2) + 1))
    (γ : C(Hemisphere.Sphere (k + 2), d.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (hγ : ContMDiff (𝓡 (k + 2)) 𝓘(ℝ, RegularLevel.Model E) ∞ γ)
      (hinj : Injective γ)
      (ht : ∀ x y, NativeTransversality.At (𝓡 (k + 2)) (𝓡 q)
        𝓘(ℝ, RegularLevel.Model E) γ d.surgery.beltSphere x y)
      (a : SingularHomology (UnitSphere (k + 2)) (k + 2)),
      collapseCoordinate d k hf.continuous hindex
        (singularHomologyMap (d.upperLevelInclusion.comp γ) (k + 2) a) =
      d.beltIntersectionCount (k + 2) j γ
        (d.finite_beltIntersectionPoints hf q (k + 2) hindex γ hγ hinj ht) *
          SpherePoint.sourceCountMark k j (collapseModel d k hindex) a := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hγ hinj ht a
  have h := SpherePoint.countMark_of_connecting k j (collapseModel d k hindex)
    _ a _ (d.collapse_homology_signed_count hf q k hindex j
      (collapseModel d k hindex) γ hγ hinj ht 1 zero_lt_one k a)
  have hc : d.attachingCollapse hf.continuous (k + 2) γ =
      (d.upperCollapseMap hf.continuous).comp (d.upperLevelInclusion.comp γ) := rfl
  rw [hc, singularHomologyMap_comp] at h
  exact h

theorem coordinate_topClass_natAbs (q k : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = k + 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient ((k + 2) + 1))
    (γ : C(Hemisphere.Sphere (k + 2), d.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (hγ : ContMDiff (𝓡 (k + 2)) 𝓘(ℝ, RegularLevel.Model E) ∞ γ)
      (hinj : Injective γ)
      (ht : ∀ x y, NativeTransversality.At (𝓡 (k + 2)) (𝓡 q)
        𝓘(ℝ, RegularLevel.Model E) γ d.surgery.beltSphere x y),
      (collapseCoordinate d k hf.continuous hindex
        (singularHomologyMap (d.upperLevelInclusion.comp γ) (k + 2)
          (unitSphereTopClass (k + 1)))).natAbs =
      (d.beltIntersectionCount (k + 2) j γ
        (d.finite_beltIntersectionPoints hf q (k + 2) hindex γ hγ hinj ht)).natAbs := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hγ hinj ht
  rw [coordinate_signed_count d hf q k hindex j γ hγ hinj ht,
    Int.natAbs_mul, SpherePoint.sourceCountMark_topClass_natAbs, mul_one]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleBasis
