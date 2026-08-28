import Wikipedia.HopfProblem.CuspNormalizationGermsClosureModel
import Wikipedia.HopfProblem.CuspNormalizationGermsChartAlgebra

/-!
# Integral closure for the actual normalization pullback at cusp-chart points

The source ring is the actual ambient-analytic function-germ ring on the
actual central fibre in an adapted quotient chart. Its branch map is the
proved actual pullback along the component projection. The branch product
is identified with its literal integral closure in its genuine total
fraction ring, and the equivalence commutes with actual pullback.

All analytic branch normality, finite-generation, and total-fraction
comparison inputs have been proved in the imported files.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

open CuspQuotient ToricCharts ToricFan ToricSpace ToricComponent

local notation "E₃" => CoordinateSpace 3

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (a : Tube (disc ε)) (s : Triangle) (b : E₃)
  (hb : b ∈ (normalizationChart C ε hε hε1 hC hR a s).target)

local notation "R" => ChartRestrictedAnalyticGerm C ε hε hε1 hC hR a s b

include hb

theorem chartRestrictedTotalFractionEquiv_restriction_diagram (φ : R) :
    chartRestrictedTotalFractionEquiv C ε hε hε1 hC hR a s b hb
      (algebraMap R (FractionRing R) φ) =
      GermsFractions.productFractionMap (fun _ : activeBranches b => BranchGerm)
        (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb φ) := by
  funext j
  exact chartRestrictedTotalFractionEquiv_algebraMap_apply C ε hε hε1 hC hR a s b hb φ j

/-- The genuine branch product included in the actual central germ
ring's total fraction ring through the proved coordinate comparison. -/
def chartProductToTotalFraction :
    (activeBranches b → BranchGerm) →+* FractionRing R :=
  GermsClosure.totalProductMap (fun _ : activeBranches b => BranchGerm)
    (chartRestrictedTotalFractionEquiv C ε hε hε1 hC hR a s b hb)

@[simp] theorem chartProductToTotalFraction_diagram (f : activeBranches b → BranchGerm) :
    chartRestrictedTotalFractionEquiv C ε hε hε1 hC hR a s b hb
      (chartProductToTotalFraction C ε hε hε1 hC hR a s b hb f) =
        GermsFractions.productFractionMap (fun _ : activeBranches b => BranchGerm) f :=
  (chartRestrictedTotalFractionEquiv C ε hε hε1 hC hR a s b hb).apply_symm_apply _

/-- The actual analytic branch product is an integral closure in the
literal total fraction ring of the actual chart-restricted singular ring. -/
theorem chartProduct_isIntegralClosure :
    letI := (chartProductToTotalFraction C ε hε hε1 hC hR a s b hb).toAlgebra
    IsIntegralClosure (activeBranches b → BranchGerm) R (FractionRing R) :=
  GermsClosure.totalProduct_isIntegralClosure (fun _ : activeBranches b => BranchGerm)
    (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb)
    (chartRestrictionToBranches_finite C ε hε hε1 hC hR a s b hb)
    (chartRestrictedTotalFractionEquiv C ε hε hε1 hC hR a s b hb)
    (chartRestrictedTotalFractionEquiv_restriction_diagram C ε hε hε1 hC hR a s b hb)

/-- The actual product of normalization-branch germs is canonically the
literal integral-closure subring of the actual singular germ ring. -/
def chartBranchIntegralClosureEquiv :
    (activeBranches b → BranchGerm) ≃+* integralClosure R (FractionRing R) :=
  GermsClosure.totalProductIntegralClosureEquiv (fun _ : activeBranches b => BranchGerm)
    (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb)
    (chartRestrictionToBranches_finite C ε hε hε1 hC hR a s b hb)
    (chartRestrictedTotalFractionEquiv C ε hε hε1 hC hR a s b hb)
    (chartRestrictedTotalFractionEquiv_restriction_diagram C ε hε hε1 hC hR a s b hb)

@[simp] theorem chartBranchIntegralClosureEquiv_coe (f : activeBranches b → BranchGerm) :
    (chartBranchIntegralClosureEquiv C ε hε hε1 hC hR a s b hb f : FractionRing R) =
      chartProductToTotalFraction C ε hε hε1 hC hR a s b hb f :=
  GermsClosure.totalProductIntegralClosureEquiv_coe (fun _ : activeBranches b => BranchGerm)
    (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb)
    (chartRestrictionToBranches_finite C ε hε hε1 hC hR a s b hb)
    (chartRestrictedTotalFractionEquiv C ε hε hε1 hC hR a s b hb)
    (chartRestrictedTotalFractionEquiv_restriction_diagram C ε hε hε1 hC hR a s b hb) f

/-- Actual normalization pullback corresponds to the canonical map of
the singular ring into its literal integral closure. -/
@[simp] theorem chartBranchIntegralClosureEquiv_restriction (φ : R) :
    chartBranchIntegralClosureEquiv C ε hε hε1 hC hR a s b hb
      (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb φ) =
        algebraMap R (integralClosure R (FractionRing R)) φ :=
  GermsClosure.totalProductIntegralClosureEquiv_restriction (fun _ : activeBranches b => BranchGerm)
    (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb)
    (chartRestrictionToBranches_finite C ε hε hε1 hC hR a s b hb)
    (chartRestrictedTotalFractionEquiv C ε hε hε1 hC hR a s b hb)
    (chartRestrictedTotalFractionEquiv_restriction_diagram C ε hε hε1 hC hR a s b hb) φ

/-- The commuting statement on actual ambient analytic representatives. -/
theorem chartBranchIntegralClosureEquiv_ambient (φ : AmbientGerm) :
    chartBranchIntegralClosureEquiv C ε hε hε1 hC hR a s b hb
      (normalizationBranchesPullback C ε hε hε1 hC hR a s b hb φ) =
        algebraMap R (integralClosure R (FractionRing R))
          ((toChartCentral C ε hε hε1 hC hR a s b).rangeRestrict φ) := by
  rw [← chartRestrictionToBranches_rangeRestrict, chartBranchIntegralClosureEquiv_restriction]

end Wikipedia.HopfProblem.CuspNormalization.Germs
