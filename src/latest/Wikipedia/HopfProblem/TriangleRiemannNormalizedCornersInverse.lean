import Wikipedia.HopfProblem.TriangleRiemannNormalizedCorners
import Wikipedia.HopfProblem.SpecialPeriodsModularLocalChartsInverse
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Analytic inverse charts for the actual normalized corner germs

The already proved analytic inverse-function theorem supplies actual open
partial homeomorphisms whose forward maps are the normalized corner germs
everywhere.  Their source and target have been restricted to the analytic
loci, so both directions are analytic throughout their declared domains.
The cubic chart is centered at `0 → 0`, and the quartic chart at `0 → 1`.
-/

noncomputable section

open Complex Set
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.RiemannMapping

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- The actual inverse-function chart for the normalized cubic quotient germ. -/
def triangleNormalizedCornerThreeChart : OpenPartialHomeomorph ℂ ℂ :=
  Classical.choose (SpecialPeriods.exists_analytic_openPartialHomeomorph
    triangleNormalizedCornerThreeGerm_analyticAt
    triangleNormalizedCornerThreeGerm_deriv_ne_zero)

/-- The actual inverse-function chart for the normalized quartic quotient germ. -/
def triangleNormalizedCornerFourChart : OpenPartialHomeomorph ℂ ℂ :=
  Classical.choose (SpecialPeriods.exists_analytic_openPartialHomeomorph
    triangleNormalizedCornerFourGerm_analyticAt
    triangleNormalizedCornerFourGerm_deriv_ne_zero)

private theorem triangleNormalizedCornerThreeChart_spec :
    (0 : ℂ) ∈ triangleNormalizedCornerThreeChart.source ∧
      (∀ z, triangleNormalizedCornerThreeChart z = triangleNormalizedCornerThreeGerm z) ∧
      AnalyticOnNhd ℂ triangleNormalizedCornerThreeChart
        triangleNormalizedCornerThreeChart.source ∧
      AnalyticOnNhd ℂ triangleNormalizedCornerThreeChart.symm
        triangleNormalizedCornerThreeChart.target :=
  Classical.choose_spec (SpecialPeriods.exists_analytic_openPartialHomeomorph
    triangleNormalizedCornerThreeGerm_analyticAt
    triangleNormalizedCornerThreeGerm_deriv_ne_zero)

private theorem triangleNormalizedCornerFourChart_spec :
    (0 : ℂ) ∈ triangleNormalizedCornerFourChart.source ∧
      (∀ z, triangleNormalizedCornerFourChart z = triangleNormalizedCornerFourGerm z) ∧
      AnalyticOnNhd ℂ triangleNormalizedCornerFourChart
        triangleNormalizedCornerFourChart.source ∧
      AnalyticOnNhd ℂ triangleNormalizedCornerFourChart.symm
        triangleNormalizedCornerFourChart.target :=
  Classical.choose_spec (SpecialPeriods.exists_analytic_openPartialHomeomorph
    triangleNormalizedCornerFourGerm_analyticAt
    triangleNormalizedCornerFourGerm_deriv_ne_zero)

theorem triangleNormalizedCornerThreeChart_zero_mem_source :
    (0 : ℂ) ∈ triangleNormalizedCornerThreeChart.source :=
  triangleNormalizedCornerThreeChart_spec.1

theorem triangleNormalizedCornerFourChart_zero_mem_source :
    (0 : ℂ) ∈ triangleNormalizedCornerFourChart.source :=
  triangleNormalizedCornerFourChart_spec.1

@[simp] theorem triangleNormalizedCornerThreeChart_apply (z : ℂ) :
    triangleNormalizedCornerThreeChart z = triangleNormalizedCornerThreeGerm z :=
  triangleNormalizedCornerThreeChart_spec.2.1 z

@[simp] theorem triangleNormalizedCornerFourChart_apply (z : ℂ) :
    triangleNormalizedCornerFourChart z = triangleNormalizedCornerFourGerm z :=
  triangleNormalizedCornerFourChart_spec.2.1 z

theorem triangleNormalizedCornerThreeChart_analyticOnNhd :
    AnalyticOnNhd ℂ triangleNormalizedCornerThreeChart
      triangleNormalizedCornerThreeChart.source :=
  triangleNormalizedCornerThreeChart_spec.2.2.1

theorem triangleNormalizedCornerFourChart_analyticOnNhd :
    AnalyticOnNhd ℂ triangleNormalizedCornerFourChart
      triangleNormalizedCornerFourChart.source :=
  triangleNormalizedCornerFourChart_spec.2.2.1

theorem triangleNormalizedCornerThreeChart_symm_analyticOnNhd :
    AnalyticOnNhd ℂ triangleNormalizedCornerThreeChart.symm
      triangleNormalizedCornerThreeChart.target :=
  triangleNormalizedCornerThreeChart_spec.2.2.2

theorem triangleNormalizedCornerFourChart_symm_analyticOnNhd :
    AnalyticOnNhd ℂ triangleNormalizedCornerFourChart.symm
      triangleNormalizedCornerFourChart.target :=
  triangleNormalizedCornerFourChart_spec.2.2.2

theorem triangleNormalizedCornerThreeChart_zero_mem_target :
    (0 : ℂ) ∈ triangleNormalizedCornerThreeChart.target := by
  simpa only [triangleNormalizedCornerThreeChart_apply, triangleNormalizedCornerThreeGerm_zero]
    using triangleNormalizedCornerThreeChart.map_source
      triangleNormalizedCornerThreeChart_zero_mem_source

theorem triangleNormalizedCornerFourChart_one_mem_target :
    (1 : ℂ) ∈ triangleNormalizedCornerFourChart.target := by
  simpa only [triangleNormalizedCornerFourChart_apply, triangleNormalizedCornerFourGerm_zero]
    using triangleNormalizedCornerFourChart.map_source
      triangleNormalizedCornerFourChart_zero_mem_source

@[simp] theorem triangleNormalizedCornerThreeChart_symm_zero :
    triangleNormalizedCornerThreeChart.symm 0 = 0 := by
  simpa only [triangleNormalizedCornerThreeChart_apply, triangleNormalizedCornerThreeGerm_zero]
    using triangleNormalizedCornerThreeChart.left_inv
      triangleNormalizedCornerThreeChart_zero_mem_source

@[simp] theorem triangleNormalizedCornerFourChart_symm_one :
    triangleNormalizedCornerFourChart.symm 1 = 0 := by
  simpa only [triangleNormalizedCornerFourChart_apply, triangleNormalizedCornerFourGerm_zero]
    using triangleNormalizedCornerFourChart.left_inv
      triangleNormalizedCornerFourChart_zero_mem_source

theorem triangleNormalizedCornerThreeChart_symm_analyticAt_zero :
    AnalyticAt ℂ triangleNormalizedCornerThreeChart.symm 0 :=
  triangleNormalizedCornerThreeChart_symm_analyticOnNhd 0
    triangleNormalizedCornerThreeChart_zero_mem_target

theorem triangleNormalizedCornerFourChart_symm_analyticAt_one :
    AnalyticAt ℂ triangleNormalizedCornerFourChart.symm 1 :=
  triangleNormalizedCornerFourChart_symm_analyticOnNhd 1
    triangleNormalizedCornerFourChart_one_mem_target

private def analyticChartPartialDiffeomorph (e : OpenPartialHomeomorph ℂ ℂ)
    (hf : AnalyticOnNhd ℂ e e.source) (hi : AnalyticOnNhd ℂ e.symm e.target) :
    PartialDiffeomorph I₁ I₁ ℂ ℂ ω where
  toPartialEquiv := e.toPartialEquiv
  open_source := e.open_source
  open_target := e.open_target
  contMDiffOn_toFun := hf.contDiffOn_of_completeSpace.contMDiffOn
  contMDiffOn_invFun := hi.contDiffOn_of_completeSpace.contMDiffOn

/-- The normalized cubic germ is a local biholomorphism in the inherited plane atlas. -/
theorem triangleNormalizedCornerThreeGerm_isLocalDiffeomorphAt :
    IsLocalDiffeomorphAt I₁ I₁ ω triangleNormalizedCornerThreeGerm 0 := by
  refine ⟨analyticChartPartialDiffeomorph triangleNormalizedCornerThreeChart
    triangleNormalizedCornerThreeChart_analyticOnNhd
    triangleNormalizedCornerThreeChart_symm_analyticOnNhd,
    triangleNormalizedCornerThreeChart_zero_mem_source, ?_⟩
  intro z _hz
  exact (triangleNormalizedCornerThreeChart_apply z).symm

/-- The normalized quartic germ is a local biholomorphism in the inherited plane atlas. -/
theorem triangleNormalizedCornerFourGerm_isLocalDiffeomorphAt :
    IsLocalDiffeomorphAt I₁ I₁ ω triangleNormalizedCornerFourGerm 0 := by
  refine ⟨analyticChartPartialDiffeomorph triangleNormalizedCornerFourChart
    triangleNormalizedCornerFourChart_analyticOnNhd
    triangleNormalizedCornerFourChart_symm_analyticOnNhd,
    triangleNormalizedCornerFourChart_zero_mem_source, ?_⟩
  intro z _hz
  exact (triangleNormalizedCornerFourChart_apply z).symm

end Wikipedia.HopfProblem.RiemannMapping
