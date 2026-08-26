import ErdosProblems.Erdos1002.GaussPrefixAnnularInteriorAssembly
import ErdosProblems.Erdos1002.GaussPrefixAnnularLiteralTransferLimit
import ErdosProblems.Erdos1002.GaussPrefixAnnularLowerRetainedLimit
import ErdosProblems.Erdos1002.GaussPrefixAnnularMidpointAssembly
import ErdosProblems.Erdos1002.UnconditionalFinalReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Final assembly of the annular Gauss-prefix argument

This file records the exact logical composition of the three remaining
annular inputs.  It introduces no asymptotic or probabilistic assumption
beyond the interfaces proved by the retained lower, retained upper, and
literal-to-canonical modules.
-/

namespace Erdos1002

noncomputable section

/-- Lower and upper retained Fourier cancellation, together with the
literal-to-canonical box transfer, imply the complete Gauss-prefix annular
factorial limits. -/
theorem gaussPrefixAnnularGridFactorialLimits_of_retained_transfer
    (hlower : GaussPrefixAnnularLowerRetainedFourierLimits)
    (hupper : GaussPrefixAnnularUpperRetainedFourierLimits)
    (htransfer : GaussPrefixAnnularLiteralCanonicalBoxTransfer) :
    GaussPrefixAnnularGridFactorialLimits := by
  apply gaussPrefixAnnularGridFactorialLimits_of_fourier_transfer
  · exact
      gaussPrefixAnnularReindexedNonzeroFourierLimits_of_retained
        hlower hupper
  · exact htransfer

/-- The exact original Erdős 1002 conclusion follows from the three
annular interfaces, all other analytic and probabilistic reductions having
already been discharged unconditionally. -/
theorem erdos1002Conclusion_of_retained_transfer
    (hlower : GaussPrefixAnnularLowerRetainedFourierLimits)
    (hupper : GaussPrefixAnnularUpperRetainedFourierLimits)
    (htransfer : GaussPrefixAnnularLiteralCanonicalBoxTransfer) :
    Erdos1002Conclusion :=
  erdos1002Conclusion_of_gaussPrefix
    (gaussPrefixAnnularGridFactorialLimits_of_retained_transfer
      hlower hupper htransfer)

/-- With the literal transfer now discharged unconditionally, the two
retained Fourier cancellation interfaces are the only inputs to the
Gauss-prefix factorial theorem. -/
theorem gaussPrefixAnnularGridFactorialLimits_of_retained
    (hlower : GaussPrefixAnnularLowerRetainedFourierLimits)
    (hupper : GaussPrefixAnnularUpperRetainedFourierLimits) :
    GaussPrefixAnnularGridFactorialLimits :=
  gaussPrefixAnnularGridFactorialLimits_of_retained_transfer
    hlower hupper gaussPrefixAnnularLiteralCanonicalBoxTransfer

/-- Exact Erdős 1002 conclusion from the two retained Fourier
cancellation interfaces. -/
theorem erdos1002Conclusion_of_retained
    (hlower : GaussPrefixAnnularLowerRetainedFourierLimits)
    (hupper : GaussPrefixAnnularUpperRetainedFourierLimits) :
    Erdos1002Conclusion :=
  erdos1002Conclusion_of_gaussPrefix
    (gaussPrefixAnnularGridFactorialLimits_of_retained hlower hupper)

/-- With literal transfer and lower retained cancellation discharged, the
upper retained late-case interface is the sole remaining input to the
complete Gauss-prefix factorial theorem. -/
theorem gaussPrefixAnnularGridFactorialLimits_of_upperRetained
    (hupper : GaussPrefixAnnularUpperRetainedFourierLimits) :
    GaussPrefixAnnularGridFactorialLimits :=
  gaussPrefixAnnularGridFactorialLimits_of_retained
    gaussPrefixAnnularLowerRetainedFourierLimits hupper

/-- Exact original Erdős 1002 conclusion from the upper retained
late-case interface alone. -/
theorem erdos1002Conclusion_of_upperRetained
    (hupper : GaussPrefixAnnularUpperRetainedFourierLimits) :
    Erdos1002Conclusion :=
  erdos1002Conclusion_of_gaussPrefix
    (gaussPrefixAnnularGridFactorialLimits_of_upperRetained hupper)

end

end Erdos1002
