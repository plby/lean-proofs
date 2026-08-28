import Wikipedia.HopfProblem.CuspNormalizationSheafCuspTerms
import Wikipedia.HopfProblem.CuspNormalizationSheafReducedChartStalk
import Wikipedia.HopfProblem.CuspNormalizationSheafCuspStalkTranslation
import Wikipedia.HopfProblem.CuspNormalizationSheafCuspStalkAmbient
import Wikipedia.HopfProblem.CuspNormalizationSheafCuspStalkBranchRepresentatives
import Wikipedia.HopfProblem.CuspNormalizationSheafManifoldStalk
import Wikipedia.HopfProblem.CuspNormalizationGermsLocalRingChart

/-!
# The actual reduced central-fibre sheaf stalk in normalization coordinates

The source below is the categorical stalk of the independently defined
reduced holomorphic-function sheaf on the actual cusp central fibre.
The actual normalization chart, followed by analytic translation to
zero, identifies it with the previously constructed central-set germ
ring. The proved local equation then identifies it with the active
coordinate-plane-union germ ring. The comparison is computed on every
actual ambient holomorphic representative.
-/

noncomputable section

open Set Filter Topology TopologicalSpace CategoryTheory Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace ToricFan

local notation "E₃" => CoordinateSpace 3
local notation "I₃" => 𝓘(ℂ, CoordinateSpace 3)

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (a : Tube (disc ε)) (s : Triangle)

local notation "e" => normalizationChart C ε hε hε1 hC hR a s

/-- Centering the actual reduced chart subset gives exactly the
previously defined actual centered central set, not a substitute set. -/
theorem centeredReducedChartSubset_eq (b : E₃) :
    SheafReduced.centeredSubset (SheafReduced.chartSubset e (centralSet C ε)) b =
      Germs.centeredChartCentral C ε hε hε1 hC hR a s b := rfl

/-- The genuine categorical reduced stalk, in the actual centered
normalization chart, is the actual central-set analytic restriction image. -/
def cuspChartStalkEquiv (x : CentralSpace C ε) (hx : x.val ∈ (e).source) :
    (reducedRingSheaf C ε hε hε1 hC hR).presheaf.stalk x ≃+*
      Germs.ChartRestrictedAnalyticGerm C ε hε hε1 hC hR a s (e x.val) := by
  letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  letI := CuspQuotient.isManifold C ε hε hε1 hC hR
  exact (SheafReduced.chartStalkEquiv e
    (normalizationChart_mem_maximalAtlas C ε hε hε1 hC hR a s)
    (centralSet C ε) x hx).trans
      (SheafReduced.restrictedTranslateToZero
        (SheafReduced.chartSubset e (centralSet C ε))
        (SheafReduced.chartPoint e (centralSet C ε) x hx))

/-- The actual singular holomorphic-function stalk is the literal
active-plane-union analytic germ ring. -/
def cuspStalkEquiv (x : CentralSpace C ε) (hx : x.val ∈ (e).source) :
    (reducedRingSheaf C ε hε hε1 hC hR).presheaf.stalk x ≃+*
      Germs.RestrictedAnalyticGerm (Germs.activeBranches (e x.val)) :=
  (cuspChartStalkEquiv C ε hε hε1 hC hR a s x hx).trans
    (Germs.chartRestrictedEquivRestricted C ε hε hε1 hC hR a s (e x.val)
      ((e).map_source hx))

/-- The chart coordinate of an actual central-fibre point satisfies
the genuine normal-crossing equation. -/
theorem cuspChartPoint_time (x : CentralSpace C ε) (hx : x.val ∈ (e).source) :
    Triangle.time (e x.val) = 0 := by
  rw [← normalizationChart_projection C ε hε hε1 hC hR a s ((e).map_source hx),
    (e).left_inv hx]
  exact x.property

/-- The actual categorical reduced holomorphic stalk is a local ring. -/
theorem reducedRingSheaf_stalk_isLocalRing
    (x : CentralSpace C ε) (hx : x.val ∈ (e).source) :
    IsLocalRing ((reducedRingSheaf C ε hε hε1 hC hR).presheaf.stalk x) := by
  let := Germs.chartRestrictedAnalyticGerm_isLocalRing C ε hε hε1 hC hR a s
    (e x.val) ((e).map_source hx) (cuspChartPoint_time C ε hε hε1 hC hR a s x hx)
  exact (cuspChartStalkEquiv C ε hε hε1 hC hR a s x hx).symm.isLocalRing

/-- The comparison on an actual ambient section is its literal inverse
chart representative, centered at the actual coordinate of the point. -/
theorem cuspChartStalkEquiv_ambient
    (x : CentralSpace C ε) (hx : x.val ∈ (e).source)
    (V : Opens (QuotientSpace C ε)) (hxV : x.val ∈ V) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ∀ g : HolomorphicFunctionSheaf.Section I₃ (QuotientSpace C ε) V,
    cuspChartStalkEquiv C ε hε hε1 hC hR a s x hx
      ((reducedRingSheaf C ε hε hε1 hC hR).presheaf.germ
        (SheafReduced.ambientOpen (centralSet C ε) V) x hxV
        (SheafReduced.ambientRestriction I₃ (centralSet C ε) V g)) =
      (Germs.toChartCentral C ε hε hε1 hC hR a s (e x.val)).rangeRestrict
        (Germs.ofAnalytic (SheafManifoldStalk.centeredRepresentative e x.val V g)
          (SheafManifoldStalk.centeredRepresentative_analyticAt e
            (normalizationChart_mem_maximalAtlas C ε hε hε1 hC hR a s)
            x.val hx V g hxV)) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  let := CuspQuotient.isManifold C ε hε hε1 hC hR
  intro g
  change SheafReduced.restrictedTranslateToZero
    (SheafReduced.chartSubset e (centralSet C ε))
    (SheafReduced.chartPoint e (centralSet C ε) x hx)
    (SheafReduced.chartStalkEquiv e
      (normalizationChart_mem_maximalAtlas C ε hε hε1 hC hR a s)
      (centralSet C ε) x hx
      ((SheafReduced.presheaf I₃ (centralSet C ε)).germ
        (SheafReduced.ambientOpen (centralSet C ε) V) x hxV
        (SheafReduced.ambientRestriction I₃ (centralSet C ε) V g))) = _
  rw [SheafReduced.chartStalkEquiv_ambient,
    SheafReduced.restrictedTranslateToZero_rangeRestrict]
  exact congrArg
    (fun φ : Germs.AmbientGerm =>
      (Germs.toChartCentral C ε hε hε1 hC hR a s (e x.val)).rangeRestrict φ)
    (SheafManifoldStalk.translateToZero_ofAnalytic (e x.val)
      (SheafReduced.chartAmbientRepresentative e V g)
      (SheafReduced.chartAmbientRepresentative_analyticAt e
        (normalizationChart_mem_maximalAtlas C ε hε hε1 hC hR a s)
        x.val hx V hxV g))

/-- The same actual representative formula in the active-plane model. -/
theorem cuspStalkEquiv_ambient
    (x : CentralSpace C ε) (hx : x.val ∈ (e).source)
    (V : Opens (QuotientSpace C ε)) (hxV : x.val ∈ V) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ∀ g : HolomorphicFunctionSheaf.Section I₃ (QuotientSpace C ε) V,
    cuspStalkEquiv C ε hε hε1 hC hR a s x hx
      ((reducedRingSheaf C ε hε hε1 hC hR).presheaf.germ
        (SheafReduced.ambientOpen (centralSet C ε) V) x hxV
        (SheafReduced.ambientRestriction I₃ (centralSet C ε) V g)) =
      (Germs.toPlaneUnion (Germs.activeBranches (e x.val))).rangeRestrict
        (Germs.ofAnalytic (SheafManifoldStalk.centeredRepresentative e x.val V g)
          (SheafManifoldStalk.centeredRepresentative_analyticAt e
            (normalizationChart_mem_maximalAtlas C ε hε hε1 hC hR a s)
            x.val hx V g hxV)) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  intro g
  change Germs.chartRestrictedEquivRestricted C ε hε hε1 hC hR a s (e x.val)
    ((e).map_source hx) (cuspChartStalkEquiv C ε hε hε1 hC hR a s x hx _) = _
  rw [cuspChartStalkEquiv_ambient, Germs.chartRestrictedEquivRestricted_rangeRestrict]

/-- The old induced branch map on the actual sheaf stalk is the actual
normalization pullback on every ambient holomorphic representative. -/
theorem cuspChartStalkEquiv_ambient_branchPullback
    (x : CentralSpace C ε) (hx : x.val ∈ (e).source)
    (V : Opens (QuotientSpace C ε)) (hxV : x.val ∈ V) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ∀ g : HolomorphicFunctionSheaf.Section I₃ (QuotientSpace C ε) V,
    Germs.chartRestrictionToBranches C ε hε hε1 hC hR a s (e x.val) ((e).map_source hx)
      (cuspChartStalkEquiv C ε hε hε1 hC hR a s x hx
        ((reducedRingSheaf C ε hε hε1 hC hR).presheaf.germ
          (SheafReduced.ambientOpen (centralSet C ε) V) x hxV
          (SheafReduced.ambientRestriction I₃ (centralSet C ε) V g))) =
      Germs.normalizationBranchesPullback C ε hε hε1 hC hR a s (e x.val)
        ((e).map_source hx)
        (Germs.ofAnalytic (SheafManifoldStalk.centeredRepresentative e x.val V g)
          (SheafManifoldStalk.centeredRepresentative_analyticAt e
            (normalizationChart_mem_maximalAtlas C ε hε hε1 hC hR a s)
            x.val hx V g hxV)) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  intro g
  rw [cuspChartStalkEquiv_ambient, Germs.chartRestrictionToBranches_rangeRestrict]

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
