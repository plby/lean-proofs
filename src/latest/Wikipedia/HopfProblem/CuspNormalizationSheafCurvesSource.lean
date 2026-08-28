import Wikipedia.HopfProblem.CuspNormalizationSheafCurvesHolomorphic
import Wikipedia.HopfProblem.CuspNormalizationSheafCurvesOrientation

/-!
# Double-curve lifts in the source's orientation

The source orders its double curves by the directions `e₁, e₁-e₂, -e₂`.
Thus the last curve reverses the positive/negative convention of the existing
unoriented edge list. This file makes that reversal explicit in the actual
holomorphic maps to the normalization component.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient.NormalizationCurves

open ToricCharts ToricFan ToricSpace ToricComponent Triangle

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The existing actual double curves, reordered as in Lemma 9.12. -/
abbrev sourceDoubleCurve (k : Fin 3) : Set (QuotientSpace C ε) :=
  doubleCurve C ε hε (sourceEdgeIndex k)

/-- The lift to `Cₖ`, with the source's signed direction. -/
def sourcePlusLift (k : Fin 3) (x : sourceDoubleCurve C ε hε k) : rayDivisor 0 :=
  if k = 2 then minusLift C ε hε (sourceEdgeIndex k) x
  else plusLift C ε hε (sourceEdgeIndex k) x

/-- The lift to `Cₖ₊₃`, with the source's opposite signed direction. -/
def sourceMinusLift (k : Fin 3) (x : sourceDoubleCurve C ε hε k) : rayDivisor 0 :=
  if k = 2 then plusLift C ε hε (sourceEdgeIndex k) x
  else minusLift C ε hε (sourceEdgeIndex k) x

@[simp] theorem componentProjection_sourcePlusLift (k : Fin 3)
    (x : sourceDoubleCurve C ε hε k) :
    componentProjection C ε hε (sourcePlusLift C ε hε k x) = x := by
  unfold sourcePlusLift
  split_ifs <;> simp

@[simp] theorem componentProjection_sourceMinusLift (k : Fin 3)
    (x : sourceDoubleCurve C ε hε k) :
    componentProjection C ε hε (sourceMinusLift C ε hε k x) = x := by
  unfold sourceMinusLift
  split_ifs <;> simp

theorem sourcePlusLift_mem_boundary (k : Fin 3) (x : sourceDoubleCurve C ε hε k) :
    sourcePlusLift C ε hε k x ∈ componentBoundary (sourceDirection k) := by
  rw [sourceDirection_eq_edgeDirection]
  unfold sourcePlusLift
  split_ifs
  · exact minusLift_mem_boundary C ε hε (sourceEdgeIndex k) x
  · exact plusLift_mem_boundary C ε hε (sourceEdgeIndex k) x

theorem sourceMinusLift_mem_boundary (k : Fin 3) (x : sourceDoubleCurve C ε hε k) :
    sourceMinusLift C ε hε k x ∈ componentBoundary (-sourceDirection k) := by
  rw [sourceDirection_eq_edgeDirection]
  unfold sourceMinusLift
  split_ifs
  · simpa only [neg_neg] using plusLift_mem_boundary C ε hε (sourceEdgeIndex k) x
  · exact minusLift_mem_boundary C ε hε (sourceEdgeIndex k) x

theorem sourcePlusLift_range (k : Fin 3) :
    range (sourcePlusLift C ε hε k) = componentBoundary (sourceDirection k) := by
  rw [sourceDirection_eq_edgeDirection]
  unfold sourcePlusLift
  split_ifs
  · exact minusLift_range C ε hε (sourceEdgeIndex k)
  · exact plusLift_range C ε hε (sourceEdgeIndex k)

theorem sourceMinusLift_range (k : Fin 3) :
    range (sourceMinusLift C ε hε k) = componentBoundary (-sourceDirection k) := by
  rw [sourceDirection_eq_edgeDirection]
  unfold sourceMinusLift
  split_ifs
  · simpa only [neg_neg] using plusLift_range C ε hε (sourceEdgeIndex k)
  · exact minusLift_range C ε hε (sourceEdgeIndex k)

theorem sourcePlusLift_eq_of_project (k : Fin 3) (x : sourceDoubleCurve C ε hε k)
    (y : rayDivisor 0) (hy : y ∈ componentBoundary (sourceDirection k))
    (he : componentProjection C ε hε y = x) : sourcePlusLift C ε hε k x = y := by
  rw [sourceDirection_eq_edgeDirection] at hy
  unfold sourcePlusLift
  split_ifs at hy ⊢
  · exact minusLift_eq_of_project C ε hε (sourceEdgeIndex k) x y hy he
  · exact plusLift_eq_of_project C ε hε (sourceEdgeIndex k) x y hy he

theorem sourceMinusLift_eq_of_project (k : Fin 3) (x : sourceDoubleCurve C ε hε k)
    (y : rayDivisor 0) (hy : y ∈ componentBoundary (-sourceDirection k))
    (he : componentProjection C ε hε y = x) : sourceMinusLift C ε hε k x = y := by
  rw [sourceDirection_eq_edgeDirection] at hy
  unfold sourceMinusLift
  split_ifs at hy ⊢
  · exact plusLift_eq_of_project C ε hε (sourceEdgeIndex k) x y (by simpa using hy) he
  · exact minusLift_eq_of_project C ε hε (sourceEdgeIndex k) x y hy he

variable (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

theorem sourcePlusLift_holomorphic (k : Fin 3) :
    letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
    ContMDiff (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (sourcePlusLift C ε hε k) := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  unfold sourcePlusLift
  split_ifs
  · exact minusLift_holomorphic C ε hε hε1 hC hR (sourceEdgeIndex k)
  · exact plusLift_holomorphic C ε hε hε1 hC hR (sourceEdgeIndex k)

theorem sourceMinusLift_holomorphic (k : Fin 3) :
    letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
    ContMDiff (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (sourceMinusLift C ε hε k) := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  unfold sourceMinusLift
  split_ifs
  · exact plusLift_holomorphic C ε hε hε1 hC hR (sourceEdgeIndex k)
  · exact minusLift_holomorphic C ε hε hε1 hC hR (sourceEdgeIndex k)

include hε1 hC hR

theorem sourcePlusLift_isEmbedding (k : Fin 3) :
    IsEmbedding (sourcePlusLift C ε hε k) := by
  unfold sourcePlusLift
  split_ifs
  · exact minusLift_isEmbedding C ε hε hε1 hC hR (sourceEdgeIndex k)
  · exact plusLift_isEmbedding C ε hε hε1 hC hR (sourceEdgeIndex k)

theorem sourceMinusLift_isEmbedding (k : Fin 3) :
    IsEmbedding (sourceMinusLift C ε hε k) := by
  unfold sourceMinusLift
  split_ifs
  · exact plusLift_isEmbedding C ε hε hε1 hC hR (sourceEdgeIndex k)
  · exact minusLift_isEmbedding C ε hε hε1 hC hR (sourceEdgeIndex k)

end Wikipedia.HopfProblem.CuspQuotient.NormalizationCurves
