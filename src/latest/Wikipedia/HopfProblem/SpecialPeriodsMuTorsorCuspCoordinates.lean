import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCuspCoordinatesCore
import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCuspCoordinatesEscape

/-!
# The reciprocal finite coordinate in the actual source cusp parameter

On the high source horodisc the inverse of the genuine filled cusp chart
recovers the actual compactified orbit projection. Consequently the
analytic function `t` of the source parameter is the reciprocal of the
finite target coordinate. Together with its divided-slope factorization,
this removes the apparent source-parameter pole in a cusp correction.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.CuspCoordinates

open Triangle

attribute [local instance] triangleCompactifiedChartedSpace

/-- The actual filled cusp chart inverts the original exponential
coordinate on its high horodisc. -/
theorem cuspChart_symm_cuspQ_of_mem (z : ℍ) (hz : z ∈ horodisc width) :
    (cuspFullChart width le_rfl).symm (cuspQ z) = triangleCompactifiedProjection z := by
  have hs : triangleCompactifiedProjection z ∈ (cuspFullChart width le_rfl).source := by
    rw [cuspFullChart_source]
    exact (openInclusion_mem_cuspNeighborhood width _).mpr ⟨z, hz, rfl⟩
  have he := cuspFullChart_mk width le_rfl ⟨z, hz⟩
  exact (congrArg (cuspFullChart width le_rfl).symm he).symm.trans
    ((cuspFullChart width le_rfl).left_inv hs)

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)
  (hπ : π triangleCuspPoint = (∞ : RiemannSphere))

include hπ

/-- The precise source/target cusp coordinate identity wherever the source
is in the high horodisc and the target finite coordinate is nonzero. -/
theorem t_cuspQ_eq_inv_finiteProjection_of_mem (z : ℍ) (hz : z ∈ horodisc width)
    (hp : BetaTorsor.finiteProjection π z ≠ 0) :
    t π (cuspQ z) = (BetaTorsor.finiteProjection π z)⁻¹ := by
  rw [t, cuspChart_symm_cuspQ_of_mem z hz, ← finiteProjection_coe π hπ z]
  exact sphereReciprocalCoordinate_coe hp

/-- The identity holds throughout a sufficiently high source cusp region;
nonvanishing of the finite target coordinate is proved by actual escape. -/
theorem t_cuspQ_eq_inv_finiteProjection :
    ∀ᶠ z in atImInfty, t π (cuspQ z) = (BetaTorsor.finiteProjection π z)⁻¹ := by
  filter_upwards [eventually_mem_horodisc width, finiteProjection_eventually_ne_zero π hπ]
    with z hz hp
  exact t_cuspQ_eq_inv_finiteProjection_of_mem π hπ z hz hp

theorem inv_finiteProjection_eq_cuspQ_mul_tDivQ :
    ∀ᶠ z in atImInfty,
      (BetaTorsor.finiteProjection π z)⁻¹ = cuspQ z * tDivQ π (cuspQ z) := by
  filter_upwards [t_cuspQ_eq_inv_finiteProjection π hπ] with z hz
  exact hz.symm.trans (t_eq_mul_tDivQ π hπ (cuspQ z))

theorem t_cuspQ_tendsto_zero :
    Tendsto (fun z : ℍ => t π (cuspQ z)) atImInfty (𝓝 (0 : ℂ)) := by
  have ht := (t_analyticAt_zero π hπ).continuousAt.tendsto.comp
    (cuspQ_tendsto_atImInfty.mono_right nhdsWithin_le_nhds)
  simpa only [Function.comp_def, t_zero π hπ] using ht

/-- The analytic expression used after cancellation of the simple source
cusp pole is genuinely analytic at zero. -/
theorem analyticAt_correction {v S : ℂ → ℂ}
    (hv : AnalyticAt ℂ v 0) (hS : AnalyticAt ℂ S 0) :
    AnalyticAt ℂ (fun q => -v q * tDivQ π q * S (t π q)) 0 := by
  have hS' : AnalyticAt ℂ S (t π 0) := by simpa only [t_zero π hπ] using hS
  exact (hv.neg.mul (tDivQ_analyticAt_zero π hπ)).mul
    (hS'.comp (t_analyticAt_zero π hπ))

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.CuspCoordinates
