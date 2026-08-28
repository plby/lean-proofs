import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinatesPairs
import Wikipedia.HopfProblem.CuspNormalizationSheafLocalCoordinatesAxisCharts
import Wikipedia.HopfProblem.CuspNormalizationSheafGermComplexAxes

/-!
# The actual signed lifts in centered branch coordinates

Use an arbitrary toric axis chart on a double curve and the corresponding
translated plane chart on the normalization. In these genuine charts the
centered positive and negative lifts are exactly coordinate-axis inclusions.
Their analytic-germ pullbacks are therefore the actual axis restrictions.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates

open ToricCharts ToricFan ToricSpace ToricComponent Triangle NormalizationCurves
open CuspNormalization.Germs CuspNormalization.SheafGermComplex

local notation "E₂" => CoordinateSpace 2
local notation "E₃" => CoordinateSpace 3

/-- The position of a surviving ambient coordinate after one coordinate
has been removed. -/
def branchAxisIndex (j k : Fin 3) (hkj : k ≠ j) : Fin 2 :=
  (finSuccAboveEquiv j).symm ⟨k, hkj⟩

theorem succAbove_branchAxisIndex (j k : Fin 3) (hkj : k ≠ j) :
    j.succAbove (branchAxisIndex j k hkj) = k :=
  congrArg Subtype.val ((finSuccAboveEquiv j).apply_symm_apply ⟨k, hkj⟩)

theorem removeCoordinate_single (j k : Fin 3) (hkj : k ≠ j) (z : ℂ) :
    removeCoordinate j (Pi.single k z) = Pi.single (branchAxisIndex j k hkj) z := by
  ext l
  change (Pi.single k z : E₃) (j.succAbove l) =
    (Pi.single (branchAxisIndex j k hkj) z : E₂) l
  conv_lhs => rw [← succAbove_branchAxisIndex j k hkj]
  simp only [Pi.single_apply, Fin.succAbove_right_injective.eq_iff]

theorem axisPoint_add (s : Triangle) (i : Fin 3) (z w : ℂ) :
    axisPoint s i (z + w) = axisPoint s i z + axisPoint s i w :=
  Pi.single_add _ _ _

theorem removeCoordinate_add (j : Fin 3) (z w : E₃) :
    removeCoordinate j (z + w) = removeCoordinate j z + removeCoordinate j w := rfl

/-- The source-positive axis position inside its two-dimensional branch. -/
def plusAxisIndex (s : Triangle) (k : Fin 3) : Fin 2 :=
  branchAxisIndex (plusBranch s k) (s.axisIndex (sourceEdgeIndex k))
    (plusBranch_ne_axisIndex s k).symm

/-- The source-negative axis position inside its two-dimensional branch. -/
def minusAxisIndex (s : Triangle) (k : Fin 3) : Fin 2 :=
  branchAxisIndex (minusBranch s k) (s.axisIndex (sourceEdgeIndex k))
    (minusBranch_ne_axisIndex s k).symm

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

@[simp] theorem branchCoordinates_affineLift (s : Triangle) (i j : Fin 3) (z : ℂ) :
    (branchParametrization C s j).symm (affineLift C s i j z) =
      removeCoordinate j (axisPoint s i z) :=
  (branchParametrization C s j).left_inv (by simp)

@[simp] theorem sourcePlusLift_axisSection (s : Triangle) (k : Fin 3) (z : ℂ) :
    sourcePlusLift C ε hε k (axisSection C ε hε s (sourceEdgeIndex k) z) =
      affineLift C s (sourceEdgeIndex k) (plusBranch s k) z := by
  unfold sourcePlusLift plusBranch
  split_ifs
  · exact minusLift_axisMap C ε hε s (sourceEdgeIndex k) z
  · exact plusLift_axisMap C ε hε s (sourceEdgeIndex k) z

@[simp] theorem sourceMinusLift_axisSection (s : Triangle) (k : Fin 3) (z : ℂ) :
    sourceMinusLift C ε hε k (axisSection C ε hε s (sourceEdgeIndex k) z) =
      affineLift C s (sourceEdgeIndex k) (minusBranch s k) z := by
  unfold sourceMinusLift minusBranch
  split_ifs
  · exact plusLift_axisMap C ε hε s (sourceEdgeIndex k) z
  · exact minusLift_axisMap C ε hε s (sourceEdgeIndex k) z

theorem sourcePlusLift_mem_branchChart (s : Triangle) (k : Fin 3) (z : ℂ) :
    sourcePlusLift C ε hε k (axisSection C ε hε s (sourceEdgeIndex k) z) ∈
      (branchParametrization C s (plusBranch s k)).target := by
  rw [sourcePlusLift_axisSection, branchParametrization_target]
  exact mem_range_self _

theorem sourceMinusLift_mem_branchChart (s : Triangle) (k : Fin 3) (z : ℂ) :
    sourceMinusLift C ε hε k (axisSection C ε hε s (sourceEdgeIndex k) z) ∈
      (branchParametrization C s (minusBranch s k)).target := by
  rw [sourceMinusLift_axisSection, branchParametrization_target]
  exact mem_range_self _

variable (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (s : Triangle) (k : Fin 3)

local notation "α" => axisParametrization C ε hε hε1 hC hR s (sourceEdgeIndex k)

/-- The actual positive lift written in the centered axis and plane charts. -/
def plusChartMap (d : sourceDoubleCurve C ε hε k) (z : ℂ) : E₂ :=
  (branchParametrization C s (plusBranch s k)).symm
      (sourcePlusLift C ε hε k ((α) ((α).symm d + z))) -
    (branchParametrization C s (plusBranch s k)).symm (sourcePlusLift C ε hε k d)

/-- The actual negative lift written in the centered axis and plane charts. -/
def minusChartMap (d : sourceDoubleCurve C ε hε k) (z : ℂ) : E₂ :=
  (branchParametrization C s (minusBranch s k)).symm
      (sourceMinusLift C ε hε k ((α) ((α).symm d + z))) -
    (branchParametrization C s (minusBranch s k)).symm (sourceMinusLift C ε hε k d)

theorem plusChartMap_eq_axis (d : sourceDoubleCurve C ε hε k) (hd : d ∈ (α).target) :
    plusChartMap C ε hε hε1 hC hR s k d =
      fun z : ℂ => (Pi.single (plusAxisIndex s k) z : E₂) := by
  rw [axisParametrization_target] at hd
  obtain ⟨t, rfl⟩ := hd
  funext z
  simp only [plusChartMap, axisParametrization_symm_apply, axisParametrization_apply,
    sourcePlusLift_axisSection, branchCoordinates_affineLift, axisPoint_add,
    removeCoordinate_add, add_sub_cancel_left]
  exact removeCoordinate_single _ _ (plusBranch_ne_axisIndex s k).symm z

theorem minusChartMap_eq_axis (d : sourceDoubleCurve C ε hε k) (hd : d ∈ (α).target) :
    minusChartMap C ε hε hε1 hC hR s k d =
      fun z : ℂ => (Pi.single (minusAxisIndex s k) z : E₂) := by
  rw [axisParametrization_target] at hd
  obtain ⟨t, rfl⟩ := hd
  funext z
  simp only [minusChartMap, axisParametrization_symm_apply, axisParametrization_apply,
    sourceMinusLift_axisSection, branchCoordinates_affineLift, axisPoint_add,
    removeCoordinate_add, add_sub_cancel_left]
  exact removeCoordinate_single _ _ (minusBranch_ne_axisIndex s k).symm z

theorem plusChartMap_analyticAt (d : sourceDoubleCurve C ε hε k) (hd : d ∈ (α).target) :
    AnalyticAt ℂ (plusChartMap C ε hε hε1 hC hR s k d) 0 := by
  rw [plusChartMap_eq_axis C ε hε hε1 hC hR s k d hd]
  exact coordinateInclusion_analyticAt 2 _

theorem minusChartMap_analyticAt (d : sourceDoubleCurve C ε hε k) (hd : d ∈ (α).target) :
    AnalyticAt ℂ (minusChartMap C ε hε hε1 hC hR s k d) 0 := by
  rw [minusChartMap_eq_axis C ε hε hε1 hC hR s k d hd]
  exact coordinateInclusion_analyticAt 2 _

theorem plusChartMap_zero (d : sourceDoubleCurve C ε hε k) (hd : d ∈ (α).target) :
    plusChartMap C ε hε hε1 hC hR s k d 0 = 0 := by
  rw [plusChartMap_eq_axis C ε hε hε1 hC hR s k d hd]
  exact coordinateInclusion_zero 2 _

theorem minusChartMap_zero (d : sourceDoubleCurve C ε hε k) (hd : d ∈ (α).target) :
    minusChartMap C ε hε hε1 hC hR s k d 0 = 0 := by
  rw [minusChartMap_eq_axis C ε hε hε1 hC hR s k d hd]
  exact coordinateInclusion_zero 2 _

/-- Analytic-germ pullback along the actual positive lift in these charts. -/
def plusGermPullback (d : sourceDoubleCurve C ε hε k) (hd : d ∈ (α).target) :
    BranchGerm →+* AxisGerm :=
  pullbackAt (plusChartMap C ε hε hε1 hC hR s k d)
    (plusChartMap_analyticAt C ε hε hε1 hC hR s k d hd)
    (plusChartMap_zero C ε hε hε1 hC hR s k d hd)

/-- Analytic-germ pullback along the actual negative lift in these charts. -/
def minusGermPullback (d : sourceDoubleCurve C ε hε k) (hd : d ∈ (α).target) :
    BranchGerm →+* AxisGerm :=
  pullbackAt (minusChartMap C ε hε hε1 hC hR s k d)
    (minusChartMap_analyticAt C ε hε hε1 hC hR s k d hd)
    (minusChartMap_zero C ε hε hε1 hC hR s k d hd)

theorem plusGermPullback_eq_axisRestriction (d : sourceDoubleCurve C ε hε k)
    (hd : d ∈ (α).target) :
    plusGermPullback C ε hε hε1 hC hR s k d hd = axisRestriction (plusAxisIndex s k) :=
  pullbackAt_congr _ _ _ _
    (Filter.Eventually.of_forall
      (congrFun (plusChartMap_eq_axis C ε hε hε1 hC hR s k d hd)))

theorem minusGermPullback_eq_axisRestriction (d : sourceDoubleCurve C ε hε k)
    (hd : d ∈ (α).target) :
    minusGermPullback C ε hε hε1 hC hR s k d hd = axisRestriction (minusAxisIndex s k) :=
  pullbackAt_congr _ _ _ _
    (Filter.Eventually.of_forall
      (congrFun (minusChartMap_eq_axis C ε hε hε1 hC hR s k d hd)))

end Wikipedia.HopfProblem.CuspQuotient.NormalizationLocalCoordinates
