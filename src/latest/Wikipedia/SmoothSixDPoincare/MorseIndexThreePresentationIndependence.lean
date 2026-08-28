import Wikipedia.SmoothSixDPoincare.MorseIndexThreePresentation
import Wikipedia.SmoothSixDPoincare.MorseIndexThreeIndependence
import Wikipedia.SmoothSixDPoincare.IntegerPresentationIndependence

/-!
# Actual index-three attachment preserves independence of the retained columns

Upper third-homology vanishing proves that the original attaching class has
infinite order. The constructed finite-presentation update therefore keeps
its entire actual relation matrix injective, without assuming column independence
for the newly attached handle.
-/

noncomputable section

open Set Metric Function ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open Wikipedia.HopfProblem.SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

theorem indexThreePresentation_matrix_injective (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3)
    [Subsingleton (SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} 3)]
    {r c : ℕ}
    (P : IntegerPresentation (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} 2) r c)
    (hP : Injective P.matrix.mulVec) :
    Injective (d.indexThreePresentation hf hindex P).matrix.mulVec :=
  P.adjoin_matrix_injective _ _ _ _ hP (d.indexThreeAttaching_zsmul_eq_zero hf hindex)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
