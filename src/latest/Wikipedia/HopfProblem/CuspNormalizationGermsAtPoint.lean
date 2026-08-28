import Wikipedia.HopfProblem.CuspNormalization
import Wikipedia.HopfProblem.CuspNormalizationGermsClosureChart
import Wikipedia.HopfProblem.CuspNormalizationGermsLocalRingChart

/-!
# Integral-closure normalization at every actual central point

Every point of the actual cusp central fibre admits an adapted analytic
quotient chart.  In that chart the actual pullback by the component map
is an injective finite integral map from the actual singular analytic
function-germ ring to the product of its smooth branch-germ rings.  That
product is the literal integral closure in the singular ring's genuine
total fraction ring, compatibly with this actual pullback.

The branch rings are actual rings of holomorphic function germs and their
integral closedness has been proved analytically.  No normalization or
integral-closure hypothesis appears in the theorem.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

open CuspQuotient ToricCharts ToricFan ToricSpace ToricComponent

local notation "E₃" => CoordinateSpace 3

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual component map has the integral-closure normalization
property on analytic function germs at every actual central-fibre point.
The returned equivalence commutes with its actual branch pullback. -/
theorem componentProjection_local_integral_closure (x : QuotientSpace C ε)
    (hx : projection C ε x = 0) :
    ∃ (a : Tube (disc ε)) (s : Triangle) (b : E₃)
      (hb : b ∈ (normalizationChart C ε hε hε1 hC hR a s).target),
      (normalizationChart C ε hε hε1 hC hR a s).symm b = x ∧
      Triangle.time b = 0 ∧
      ((activeBranches b).card = 1 ∨ (activeBranches b).card = 2 ∨
        (activeBranches b).card = 3) ∧
      IsLocalRing (ChartRestrictedAnalyticGerm C ε hε hε1 hC hR a s b) ∧
      Function.Injective (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb) ∧
      (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb).Finite ∧
      (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb).IsIntegral ∧
      (∀ φ : AmbientGerm,
        chartRestrictionToBranches C ε hε hε1 hC hR a s b hb
          ((toChartCentral C ε hε hε1 hC hR a s b).rangeRestrict φ) =
            normalizationBranchesPullback C ε hε hε1 hC hR a s b hb φ) ∧
      ∃ Ψ : (activeBranches b → BranchGerm) ≃+*
          integralClosure (ChartRestrictedAnalyticGerm C ε hε hε1 hC hR a s b)
            (FractionRing (ChartRestrictedAnalyticGerm C ε hε hε1 hC hR a s b)),
        ∀ φ : ChartRestrictedAnalyticGerm C ε hε hε1 hC hR a s b,
          Ψ (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb φ) =
            algebraMap (ChartRestrictedAnalyticGerm C ε hε hε1 hC hR a s b)
              (integralClosure (ChartRestrictedAnalyticGerm C ε hε hε1 hC hR a s b)
                (FractionRing (ChartRestrictedAnalyticGerm C ε hε hε1 hC hR a s b))) φ := by
  let := chartedSpace C ε hε hε1 hC hR
  obtain ⟨a, s, _, hsource, _, _, _⟩ :=
    componentProjection_local_coordinate_normalization C ε hε hε1 hC hR x
  let e := normalizationChart C ε hε hε1 hC hR a s
  let b : E₃ := e x
  have hb : b ∈ e.target := e.map_source hsource
  have hbx : e.symm b = x := e.left_inv hsource
  have htime : Triangle.time b = 0 := by
    rw [← normalizationChart_projection C ε hε hε1 hC hR a s hb, hbx]
    exact hx
  refine ⟨a, s, b, hb, hbx, htime, activeBranches_card b htime,
    chartRestrictedAnalyticGerm_isLocalRing C ε hε hε1 hC hR a s b hb htime,
    chartRestrictionToBranches_injective C ε hε hε1 hC hR a s b hb,
    chartRestrictionToBranches_finite C ε hε hε1 hC hR a s b hb,
    chartRestrictionToBranches_isIntegral C ε hε hε1 hC hR a s b hb,
    chartRestrictionToBranches_rangeRestrict C ε hε hε1 hC hR a s b hb,
    chartBranchIntegralClosureEquiv C ε hε hε1 hC hR a s b hb, ?_⟩
  exact chartBranchIntegralClosureEquiv_restriction C ε hε hε1 hC hR a s b hb

end Wikipedia.HopfProblem.CuspNormalization.Germs
