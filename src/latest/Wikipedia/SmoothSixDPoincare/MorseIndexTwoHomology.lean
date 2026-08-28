import Wikipedia.SmoothSixDPoincare.MorseHomologyPropagation
import Wikipedia.SmoothSixDPoincare.MorseCollapseSurjectivity
import Wikipedia.SmoothSixDPoincare.SphereCountMarking
import Wikipedia.SmoothSixDPoincare.IntegerHomologyExtension

/-!
# An actual index-two handle adds one independent integer homology coordinate

The original collapse supplies the integer coordinate. Exactness identifies
its kernel with the original realized lower-sublevel image, and the attaching
circle calculation makes that image injective. If the lower first homology
vanishes, a constructed section gives a product isomorphism retaining both
maps. This is the basis-extension step for the middle handle matrices.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open Wikipedia.HopfProblem.SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

def indexTwoNormalModel (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2) :
    EuclideanSpace ℝ (Fin 2) ≃L[ℝ] d.chart.NegativeCoordinates :=
  ContinuousLinearEquiv.ofFinrankEq (by simp [hindex])

def indexTwoCollapseCoordinate (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2) :
    SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} 2 →ₗ[ℤ] ℤ :=
  (SpherePoint.targetCountMark 0 (d.indexTwoNormalModel hindex)).toLinearMap.comp
    (singularHomologyMap (d.upperCollapseMap hf) 2)

theorem indexTwoCoordinate_surjective (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    [Subsingleton (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} 1)] :
    Surjective (d.indexTwoCollapseCoordinate hf hindex) :=
  (SpherePoint.targetCountMark 0 (d.indexTwoNormalModel hindex)).surjective.comp
    (d.upperCollapse_surjective_of_lower hf 0)

theorem indexTwoCoordinate_kernel (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2) :
    LinearMap.ker (d.indexTwoCollapseCoordinate hf hindex) =
      LinearMap.range (d.lowerRealizationHomologyMap 2) := by
  rw [← d.upperCollapse_homology_kernel hf 1]
  ext a
  let C := SpherePoint.targetCountMark 0 (d.indexTwoNormalModel hindex)
  change C (singularHomologyMap (d.upperCollapseMap hf) 2 a) = 0 ↔
    singularHomologyMap (d.upperCollapseMap hf) 2 a = 0
  constructor
  · intro h
    exact C.injective (h.trans (map_zero C).symm)
  · intro h
    rw [h, map_zero]

theorem lowerRealization_two_injective (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2) :
    Injective (d.lowerRealizationHomologyMap 2) := by
  let : Subsingleton (SingularHomology (sphere (0 : d.chart.NegativeCoordinates) 1) 2) :=
    d.attachingHomology_subsingleton_of_index 2 (by norm_num) (by omega) (by omega)
  apply LinearMap.ker_eq_bot.mp
  rw [← d.morse_exact_at_lower hf 2 (by norm_num)]
  apply LinearMap.range_eq_bot.mpr
  apply LinearMap.ext
  intro a
  change d.coreBoundaryHomologyMap 2 a = 0
  rw [Subsingleton.elim a 0, map_zero]

theorem exists_indexTwoHomology_split (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    [Subsingleton (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} 1)] :
    ∃ H : (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} 2 × ℤ) ≃ₗ[ℤ]
        SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} 2,
      (∀ a, H (a, 0) = d.lowerRealizationHomologyMap 2 a) ∧
        ∀ z, d.indexTwoCollapseCoordinate hf hindex (H z) = z.2 := by
  obtain ⟨H, hH, hcoord⟩ :=
    HomologyTransport.exists_add_split_rank_one_extension (d.lowerRealizationHomologyMap 2)
      (d.indexTwoCollapseCoordinate hf hindex) (d.lowerRealization_two_injective hf hindex)
      (d.indexTwoCoordinate_surjective hf hindex) (d.indexTwoCoordinate_kernel hf hindex)
  exact ⟨H.toIntLinearEquiv, hH, hcoord⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
