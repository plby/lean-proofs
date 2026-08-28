import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinatesLiftMaps

/-!
# Actual signed lifts and the normalization fibre equivalence

Inside an adapted quotient chart, each double curve through the chosen
point has its actual axis chart, and its two signed lifts are exactly the
points selected by the positive and negative active coordinate indices.
The comparison uses the existing equivalence with the entire normalization
fibre, not only a collection of candidate branches.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates

open ToricCharts ToricFan ToricSpace ToricComponent Triangle NormalizationCurves
open CuspNormalization.Germs

local notation "E₂" => CoordinateSpace 2
local notation "E₃" => CoordinateSpace 3

theorem eq_axisPoint_of_pair_active (s : Triangle) (b : E₃) (k : Fin 3)
    (hk : sourcePair s k ⊆ activeBranches b) :
    b = axisPoint s (sourceEdgeIndex k) (b (s.axisIndex (sourceEdgeIndex k))) :=
  (eq_axisPoint_iff s (sourceEdgeIndex k) b).mpr fun j hj =>
    (mem_activeBranches b j).mp (hk ((mem_sourcePair s k j).mpr hj))

/-- The positive coordinate index as an actual active branch. -/
def chartPlusIndex (s : Triangle) (b : E₃) (k : Fin 3)
    (hk : sourcePair s k ⊆ activeBranches b) : activeBranches b :=
  ⟨plusBranch s k, hk ((mem_sourcePair s k _).mpr (plusBranch_ne_axisIndex s k))⟩

/-- The negative coordinate index as an actual active branch. -/
def chartMinusIndex (s : Triangle) (b : E₃) (k : Fin 3)
    (hk : sourcePair s k ⊆ activeBranches b) : activeBranches b :=
  ⟨minusBranch s k, hk ((mem_sourcePair s k _).mpr (minusBranch_ne_axisIndex s k))⟩

theorem chartPlusIndex_ne_chartMinusIndex (s : Triangle) (b : E₃) (k : Fin 3)
    (hk : sourcePair s k ⊆ activeBranches b) : chartPlusIndex s b k hk ≠ chartMinusIndex s b k hk :=
  fun h => plusBranch_ne_minusBranch s k (congrArg Subtype.val h)

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (a : Tube (disc ε)) (s : Triangle) (b : E₃)

local notation "e" => normalizationChart C ε hε hε1 hC hR a s

/-- The chart point, regarded as a point of an actual incident double curve. -/
def chartCurvePoint (hb : b ∈ (e).target) (k : Fin 3)
    (hk : sourcePair s k ⊆ activeBranches b) : sourceDoubleCurve C ε hε k :=
  ⟨(e).symm b, (mem_sourceDoubleCurve_iff_pair_active C ε hε hε1 hC hR a s b hb k).mpr hk⟩

@[simp] theorem chartCurvePoint_coe (hb : b ∈ (e).target) (k : Fin 3)
    (hk : sourcePair s k ⊆ activeBranches b) :
    (chartCurvePoint C ε hε hε1 hC hR a s b hb k hk : QuotientSpace C ε) = (e).symm b := rfl

theorem chartCurvePoint_eq_axisSection (hb : b ∈ (e).target) (k : Fin 3)
    (hk : sourcePair s k ⊆ activeBranches b) :
    chartCurvePoint C ε hε hε1 hC hR a s b hb k hk =
      axisSection C ε hε s (sourceEdgeIndex k) (b (s.axisIndex (sourceEdgeIndex k))) := by
  apply Subtype.ext
  have hbaxis := eq_axisPoint_of_pair_active s b k hk
  change (e).symm b = axisMap C ε hε s (sourceEdgeIndex k) _
  rw [axisMap_eq_centralChartMap]
  calc
    _ = (e).symm (axisPoint s (sourceEdgeIndex k) (b (s.axisIndex (sourceEdgeIndex k)))) :=
      congrArg (e).symm hbaxis
    _ = _ := normalizationChart_symm_central C ε hε hε1 hC hR a s
      (centralAxis s (sourceEdgeIndex k) (b (s.axisIndex (sourceEdgeIndex k))))
      (by change axisPoint s _ _ ∈ (e).target; rwa [← hbaxis])

theorem chartCurvePoint_mem_axisChart (hb : b ∈ (e).target) (k : Fin 3)
    (hk : sourcePair s k ⊆ activeBranches b) :
    chartCurvePoint C ε hε hε1 hC hR a s b hb k hk ∈
      (axisParametrization C ε hε hε1 hC hR s (sourceEdgeIndex k)).target := by
  rw [chartCurvePoint_eq_axisSection]
  exact axisSection_mem_target C ε hε hε1 hC hR s _ _

theorem chartCurvePoint_axisCoordinates (hb : b ∈ (e).target) (k : Fin 3)
    (hk : sourcePair s k ⊆ activeBranches b) :
    (axisParametrization C ε hε hε1 hC hR s (sourceEdgeIndex k)).symm
      (chartCurvePoint C ε hε hε1 hC hR a s b hb k hk) = b (s.axisIndex (sourceEdgeIndex k)) := by
  rw [chartCurvePoint_eq_axisSection, axisParametrization_symm_apply]

theorem chartCurvePoint_plusLift (hb : b ∈ (e).target) (k : Fin 3)
    (hk : sourcePair s k ⊆ activeBranches b) :
    sourcePlusLift C ε hε k (chartCurvePoint C ε hε hε1 hC hR a s b hb k hk) =
      branchAffine C s (plusBranch s k) (removeCoordinate (plusBranch s k) b) := by
  rw [chartCurvePoint_eq_axisSection, sourcePlusLift_axisSection]
  unfold affineLift
  rw [← eq_axisPoint_of_pair_active s b k hk]

theorem chartCurvePoint_minusLift (hb : b ∈ (e).target) (k : Fin 3)
    (hk : sourcePair s k ⊆ activeBranches b) :
    sourceMinusLift C ε hε k (chartCurvePoint C ε hε hε1 hC hR a s b hb k hk) =
      branchAffine C s (minusBranch s k) (removeCoordinate (minusBranch s k) b) := by
  rw [chartCurvePoint_eq_axisSection, sourceMinusLift_axisSection]
  unfold affineLift
  rw [← eq_axisPoint_of_pair_active s b k hk]

theorem chartCurvePoint_plusLift_eq_fibre (hb : b ∈ (e).target) (k : Fin 3)
    (hk : sourcePair s k ⊆ activeBranches b) :
    sourcePlusLift C ε hε k (chartCurvePoint C ε hε hε1 hC hR a s b hb k hk) =
      (activeFibreEquiv C ε hε hε1 hC hR a s b hb (chartPlusIndex s b k hk) : rayDivisor 0) :=
  chartCurvePoint_plusLift C ε hε hε1 hC hR a s b hb k hk

theorem chartCurvePoint_minusLift_eq_fibre (hb : b ∈ (e).target) (k : Fin 3)
    (hk : sourcePair s k ⊆ activeBranches b) :
    sourceMinusLift C ε hε k (chartCurvePoint C ε hε hε1 hC hR a s b hb k hk) =
      (activeFibreEquiv C ε hε hε1 hC hR a s b hb (chartMinusIndex s b k hk) : rayDivisor 0) :=
  chartCurvePoint_minusLift C ε hε hε1 hC hR a s b hb k hk

theorem chartCurvePoint_plusBranch_mem (hb : b ∈ (e).target) (k : Fin 3)
    (hk : sourcePair s k ⊆ activeBranches b) :
    sourcePlusLift C ε hε k (chartCurvePoint C ε hε hε1 hC hR a s b hb k hk) ∈
      (branchParametrization C s (plusBranch s k)).target := by
  rw [chartCurvePoint_eq_axisSection]
  exact sourcePlusLift_mem_branchChart C ε hε s k _

theorem chartCurvePoint_minusBranch_mem (hb : b ∈ (e).target) (k : Fin 3)
    (hk : sourcePair s k ⊆ activeBranches b) :
    sourceMinusLift C ε hε k (chartCurvePoint C ε hε hε1 hC hR a s b hb k hk) ∈
      (branchParametrization C s (minusBranch s k)).target := by
  rw [chartCurvePoint_eq_axisSection]
  exact sourceMinusLift_mem_branchChart C ε hε s k _

end Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates
