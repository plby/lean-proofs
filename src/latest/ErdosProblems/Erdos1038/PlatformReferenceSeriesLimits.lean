import ErdosProblems.Erdos1038.PlatformReferenceUniformDirectionalDomination

/-!
# Full canonical platform series limits

The two fixed-degree recurrence limits and the explicit uniform geometric
majorants now feed directly into Tannery's theorem.  This file packages the
result for the material inverse-width series; the base counterpart is
`tendsto_inverseWidthSeries_platformResidualRefinement`.
-/

set_option warningAsError false

open Filter Set
open scoped BigOperators Topology

namespace Erdos1038

noncomputable section

variable {iota : Type*} [Fintype iota] [LinearOrder iota]

/-- The actual material inverse-width series on canonical platform meshes
converges to the odd series of continuum linearized-moment coefficients. -/
theorem tendsto_inverseWidthSeriesDirectional_platformResidualRefinement
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {s : ℝ} (hs : 0 < s) (hsa : s < a)
    (hlimit : 0 < platformReferenceExteriorLogPotentialLimit C k a
      hk ha ha2 hthreshold s) :
    Tendsto
      (fun n ↦ inverseWidthSeriesDirectional
        (platformResidualRefinementAlpha C k n)
        (platformResidualRefinementReference C k a
          hk ha ha2 hthreshold n)
        (platformResidualRefinementTarget C n))
      atTop
      (nhds (2 * ∑' j,
        platformReferenceScaledLagrangeCoefficientDirectionalLimit
          C k a hk ha ha2 hthreshold (2 * j + 1))) := by
  apply tendsto_inverseWidthSeriesDirectional_of_dominated_coefficients
    (fun n ↦ iota × Fin (n + 1))
    (fun n ↦ platformResidualRefinementAlpha C k n)
    (fun n ↦ platformResidualRefinementReference C k a
      hk ha ha2 hthreshold n)
    (fun n ↦ platformResidualRefinementTarget C n)
    (fun j ↦
      platformReferenceScaledLagrangeCoefficientDirectionalLimit
        C k a hk ha ha2 hthreshold (2 * j + 1))
    (platformReferenceDirectionalCoefficientMajorant C k a
      hk ha ha2 hthreshold s)
  · exact summable_platformReferenceDirectionalCoefficientMajorant
      C k a hk ha ha2 hthreshold hlimit
  · intro j
    exact
      tendsto_scaledLagrangeCoefficientDirectional_platformRefinement
        C k a hk ha ha2 hthreshold (by omega)
  · exact
      eventually_norm_scaledLagrangeCoefficientDirectional_platformResidualRefinement_le
        C k a hk ha ha2 hthreshold hs hsa hlimit

end

end Erdos1038

