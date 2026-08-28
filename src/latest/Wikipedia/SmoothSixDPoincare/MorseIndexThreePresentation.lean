import Wikipedia.SmoothSixDPoincare.MorseIndexThreeRelation
import Wikipedia.SmoothSixDPoincare.IntegerPresentation

/-!
# Adjoin the original index-three attaching column to the retained presentation

Lift the actual attaching class through the preceding presentation map.
The new presentation map is the original realized lower inclusion composed
with that map, and the new column maps back to the original attaching class.
All older columns are retained exactly.
-/

noncomputable section

open Set Metric ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open Wikipedia.HopfProblem.SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p) (hf : Continuous f)
  (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3)
  {r c : ℕ}
  (P : IntegerPresentation (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} 2) r c)

def indexThreePresentation :
    IntegerPresentation (SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} 2) r (c + 1) :=
  P.adjoin (d.lowerRealizationHomologyMap 2) (d.indexThree_lowerRealization_surjective hf hindex)
    (d.indexThreeAttachingClass hindex) (d.indexThree_lowerRealization_kernel hf hindex)

theorem indexThreePresentation_map (v : Fin r → ℤ) :
    (d.indexThreePresentation hf hindex P).map v =
      d.lowerRealizationHomologyMap 2 (P.map v) := rfl

theorem indexThreePresentation_column_zero :
    P.map ((d.indexThreePresentation hf hindex P).columns 0) = d.indexThreeAttachingClass hindex :=
  P.adjoin_column_zero _ _ _ _

theorem indexThreePresentation_column_succ (i : Fin c) :
    (d.indexThreePresentation hf hindex P).columns i.succ = P.columns i := rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
