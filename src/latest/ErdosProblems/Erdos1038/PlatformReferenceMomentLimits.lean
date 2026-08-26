import ErdosProblems.Erdos1038.PlatformReferenceQuantileRiemann

/-!
# Actual moment limits for the canonical platform refinement

Uniform left-Riemann convergence now applies to the concrete canonical
samples.  This file instantiates it for inverse moments, logarithmic
moments, material inverse moments, and the exterior logarithmic potential.
In particular, a positive continuum exterior potential makes every
sufficiently fine discrete reference strictly separated.
-/

set_option warningAsError false

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1038

noncomputable section

variable {iota : Type*} [Fintype iota] [LinearOrder iota]

/-- Continuum limit of a block-dependent observable evaluated on the
canonical platform reference quantile. -/
def platformReferenceBlockObservableLimit
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (F : iota → ℝ → ℝ) : ℝ :=
  ∑ i, residualLagrangeAlpha C k i *
    (∫ t in (0 : ℝ)..1,
      platformResidualBlockReferenceIntegrand C i
        k a hk ha ha2 hthreshold (F i) t)

theorem tendsto_platformResidualRefinement_blockObservable
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (F : iota → ℝ → ℝ) (hF : ∀ i, ContinuousOn (F i) (Icc a 2)) :
    Tendsto
      (fun n ↦ ∑ p,
        platformResidualRefinementAlpha C k n p *
          F p.1 (platformResidualRefinementReference C k a
            hk ha ha2 hthreshold n p))
      atTop
      (nhds (platformReferenceBlockObservableLimit C k a
        hk ha ha2 hthreshold F)) := by
  exact tendsto_sum_platformResidualRefinementAlpha_mul_blockObservable
    C k a hk ha ha2 hthreshold F hF

/-- Continuum inverse moment of order `ell`, with the Lagrange weight
`q_i / k`. -/
def platformReferenceInverseMomentLimit
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (ell : ℕ) : ℝ :=
  platformReferenceBlockObservableLimit C k a hk ha ha2 hthreshold
    (fun _i d ↦ d⁻¹ ^ ell)

theorem tendsto_platformResidualRefinement_inverseMoment
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (ell : ℕ) :
    Tendsto
      (fun n ↦ ∑ p,
        platformResidualRefinementAlpha C k n p *
          (platformResidualRefinementReference C k a
            hk ha ha2 hthreshold n p)⁻¹ ^ ell)
      atTop
      (nhds (platformReferenceInverseMomentLimit C k a
        hk ha ha2 hthreshold ell)) := by
  apply tendsto_platformResidualRefinement_blockObservable
  intro i
  exact (continuousOn_id.inv₀ fun d hd ↦
    (ha.trans_le hd.1).ne').pow ell

/-- Continuum logarithmic moment determining the reference scale `R`. -/
def platformReferenceLogMomentLimit
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) : ℝ :=
  platformReferenceBlockObservableLimit C k a hk ha ha2 hthreshold
    (fun _i d ↦ Real.log d)

theorem tendsto_platformResidualRefinement_logMoment
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    Tendsto
      (fun n ↦ ∑ p,
        platformResidualRefinementAlpha C k n p *
          Real.log (platformResidualRefinementReference C k a
            hk ha ha2 hthreshold n p))
      atTop
      (nhds (platformReferenceLogMomentLimit C k a
        hk ha ha2 hthreshold)) := by
  apply tendsto_platformResidualRefinement_blockObservable
  intro i
  exact continuousOn_id.log fun d hd ↦ (ha.trans_le hd.1).ne'

theorem tendsto_inverseMonomial_platformResidualRefinementReference
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) :
    Tendsto
      (fun n ↦ inverseMonomial
        (platformResidualRefinementAlpha C k n)
        (platformResidualRefinementReference C k a
          hk ha ha2 hthreshold n))
      atTop
      (nhds (Real.exp (-platformReferenceLogMomentLimit C k a
        hk ha ha2 hthreshold))) := by
  have hlog := tendsto_platformResidualRefinement_logMoment
    C k a hk ha ha2 hthreshold
  simpa only [inverseMonomial] using!
    (Real.continuous_exp.tendsto _).comp hlog.neg

/-- Continuum limit of the material inverse-moment integrand.  Multiplying
this scalar by `-ell` gives the derivative of the order-`ell` moment. -/
def platformReferenceMaterialInverseMomentLimit
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (ell : ℕ) : ℝ :=
  platformReferenceBlockObservableLimit C k a hk ha ha2 hthreshold
    (fun i d ↦ (C.location i - d) * d⁻¹ ^ (ell + 1))

theorem tendsto_platformResidualRefinement_materialInverseMoment
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (ell : ℕ) :
    Tendsto
      (fun n ↦ ∑ p,
        platformResidualRefinementAlpha C k n p *
          (platformResidualRefinementTarget C n p -
            platformResidualRefinementReference C k a
              hk ha ha2 hthreshold n p) *
          (platformResidualRefinementReference C k a
              hk ha ha2 hthreshold n p)⁻¹ ^ (ell + 1))
      atTop
      (nhds (platformReferenceMaterialInverseMomentLimit C k a
        hk ha ha2 hthreshold ell)) := by
  have h := tendsto_platformResidualRefinement_blockObservable
    C k a hk ha ha2 hthreshold
    (fun i d ↦ (C.location i - d) * d⁻¹ ^ (ell + 1)) (by
      intro i
      exact (continuousOn_const.sub continuousOn_id).mul
        ((continuousOn_id.inv₀ fun d hd ↦
          (ha.trans_le hd.1).ne').pow (ell + 1)))
  simpa only [platformResidualRefinementTarget, refinedCoordinates,
    platformReferenceMaterialInverseMomentLimit, mul_assoc] using! h

/-- Continuum exterior logarithmic potential at a comparison point below
the platform edge. -/
def platformReferenceExteriorLogPotentialLimit
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (s : ℝ) : ℝ :=
  Real.log s +
    platformReferenceBlockObservableLimit C k a hk ha ha2 hthreshold
      (fun _i d ↦ Real.log (d - s))

theorem tendsto_platformResidualRefinement_exteriorLogPotential
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {s : ℝ} (hsa : s < a) :
    Tendsto
      (fun n ↦ Real.log s +
        ∑ p,
          platformResidualRefinementAlpha C k n p *
            Real.log
              (platformResidualRefinementReference C k a
                hk ha ha2 hthreshold n p - s))
      atTop
      (nhds (platformReferenceExteriorLogPotentialLimit C k a
        hk ha ha2 hthreshold s)) := by
  have h := tendsto_platformResidualRefinement_blockObservable
    C k a hk ha ha2 hthreshold
    (fun _i d ↦ Real.log (d - s)) (by
      intro i
      exact (continuousOn_id.sub continuousOn_const).log fun d hd ↦
        (sub_pos.mpr (hsa.trans_le hd.1)).ne')
  simpa only [platformReferenceExteriorLogPotentialLimit] using!
    tendsto_const_nhds.add h

/-- A positive continuum exterior potential gives strict comparison on
every sufficiently fine canonical mesh. -/
theorem eventually_platformResidualRefinement_exteriorLogPotential_pos
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {s : ℝ} (hsa : s < a)
    (hlimit : 0 < platformReferenceExteriorLogPotentialLimit C k a
      hk ha ha2 hthreshold s) :
    ∀ᶠ n in atTop,
      0 < Real.log s +
        ∑ p,
          platformResidualRefinementAlpha C k n p *
            Real.log
              (platformResidualRefinementReference C k a
                hk ha ha2 hthreshold n p - s) := by
  exact (tendsto_platformResidualRefinement_exteriorLogPotential
    C k a hk ha ha2 hthreshold hsa).eventually
      (Ioi_mem_nhds hlimit)

/-- Quantitative version of eventual strict separation: after discarding
finitely many meshes, at least half of the positive continuum potential
margin remains.  The fixed half-margin produces a mesh-independent
geometric ratio for the inverse-series coefficients. -/
theorem eventually_half_platformReferenceExteriorLogPotentialLimit_le
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {s : ℝ} (hsa : s < a)
    (hlimit : 0 < platformReferenceExteriorLogPotentialLimit C k a
      hk ha ha2 hthreshold s) :
    ∀ᶠ n in atTop,
      platformReferenceExteriorLogPotentialLimit C k a
          hk ha ha2 hthreshold s / 2 ≤
        Real.log s +
          ∑ p,
            platformResidualRefinementAlpha C k n p *
              Real.log
                (platformResidualRefinementReference C k a
                  hk ha ha2 hthreshold n p - s) := by
  have hhalf :
      platformReferenceExteriorLogPotentialLimit C k a
          hk ha ha2 hthreshold s / 2 <
        platformReferenceExteriorLogPotentialLimit C k a
          hk ha ha2 hthreshold s := by
    linarith
  exact (tendsto_platformResidualRefinement_exteriorLogPotential
      C k a hk ha ha2 hthreshold hsa).eventually
    (Ici_mem_nhds hhalf)

end

end Erdos1038
