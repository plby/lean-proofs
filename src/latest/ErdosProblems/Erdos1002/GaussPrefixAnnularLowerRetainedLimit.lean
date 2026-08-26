import ErdosProblems.Erdos1002.GaussPrefixAnnularLowerRestoration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Completed lower-retained annular Fourier limit

This leaf packages the fixed-contraction oscillatory estimate and the
independently proved time-boundary restoration into the exact interface
consumed by the annular midpoint assembly.
-/

open Filter
open scoped Topology

namespace Erdos1002

noncomputable section

/-- The fixed-contraction lower-retained Fourier limit, with exactly the
quantifier order required by the restoration interface. -/
theorem gaussPrefixAnnularContractedLowerRetainedFourierLimits :
    GaussPrefixAnnularContractedLowerRetainedFourierLimits := by
  intro ε A hε hεA grid hgrid k hr htime hsigned
    mode hmode rho hrho eta heta
  have htagged :=
    tendsto_annularContractedLowerRetainedMovingSum_zero
      hε hεA heta hrho hgrid k hr htime hsigned mode hmode
  exact htagged.congr'
    (Eventually.of_forall fun N ↦
      annularContractedLowerRetainedMovingSum_eq_nested
        ε A eta rho N k hr mode hmode)

/-- The exact, uncontracted lower-retained Fourier limit. -/
theorem gaussPrefixAnnularLowerRetainedFourierLimits :
    GaussPrefixAnnularLowerRetainedFourierLimits :=
  gaussPrefixAnnularLowerRetainedFourierLimits_of_contracted
    gaussPrefixAnnularContractedLowerRetainedFourierLimits

end

end Erdos1002
