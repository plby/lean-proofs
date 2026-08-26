import ErdosProblems.Erdos1002.GaussPrefixAnnularFinalAssembly
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperRetainedLimit
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperFactorizedBridgeLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Kernel-checked conclusion of Erdős Problem 1002

This module closes the last upper-retained Fourier interface and exposes the
original distributional statement without any additional hypothesis.
-/

open Filter
open scoped Topology

namespace Erdos1002

noncomputable section

/-- The fully discharged fixed-contraction upper-retained Fourier limit. -/
theorem gaussPrefixAnnularContractedUpperRetainedFourierLimits :
    GaussPrefixAnnularContractedUpperRetainedFourierLimits := by
  intro ε A hε hεA grid hgrid k hr htime hsigned mode hmode
    rho hrho eta heta
  have htagged :=
    tendsto_annularContractedUpperRetainedMovingSum_zero_of_factorizedBridge
      hε hεA heta hrho hgrid k hr htime hsigned mode hmode
      (tendsto_annularContractedUpperRetainedAffineFactorizedMeanSum_sub_shallow_zero
        hε hεA heta hrho hgrid k hr htime hsigned mode hmode)
  exact htagged.congr'
    (Eventually.of_forall fun N ↦
      annularContractedUpperRetainedMovingSum_eq_nested
        ε A eta rho N k hr mode hmode)

/-- The literal upper-retained Fourier limit, after restoring the contracted
time boundary. -/
theorem gaussPrefixAnnularUpperRetainedFourierLimits :
    GaussPrefixAnnularUpperRetainedFourierLimits :=
  gaussPrefixAnnularUpperRetainedFourierLimits_of_contracted
    gaussPrefixAnnularContractedUpperRetainedFourierLimits

/-- Erdős Problem 1002: for every real threshold, the fixed-start normalized
rotation sum converges in distribution to the centered Cauchy law of scale
`1 / (2π)`. -/
theorem erdos1002 :
    ∀ c : ℝ,
      Tendsto (fun N : ℕ ↦ distributionValue N c) atTop
        (nhds (cauchyLimitCDF c)) :=
  erdos1002Conclusion_of_upperRetained
    gaussPrefixAnnularUpperRetainedFourierLimits

end

end Erdos1002
