import ErdosProblems.Erdos215.FinalBridge
import ErdosProblems.Erdos215.GlobalAssembly
import ErdosProblems.Erdos215.SelectorFrame

/-!
# Final conditional assembly for Erdős Problem 215

This module isolates the last composition step.  Once the literal finite
prime-extension theorem is supplied, the arithmetic selector, Davies global
construction, rational-rotation transfer, and inverse-motion bridge produce
the strong Jackson--Mauldin conclusion used by the public theorem.
-/

namespace Erdos215

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- The literal finite prime-extension theorem implies the strong
Jackson--Mauldin conclusion. -/
theorem exists_partial_hitsEveryLattice_of_literalPrimeExtension
    (hprime : Selector.LiteralPrimeExtensionHypothesis) :
    ∃ S : Set Point, IsPartialSteinhaus S ∧ HitsEveryLattice S := by
  let selector : Global.RichSelectorTheorem :=
    SelectorFrame.richSelectorTheorem_of_literalPrimeExtension hprime
  obtain ⟨S, hpartial, hclasses⟩ :=
    Global.CodedDavies.global_rational_classes selector
  refine ⟨S, hpartial, hitsEveryLattice_of_hitsEveryRationalClass ?_⟩
  intro L K hKL
  exact hclasses L K hKL

end

end Erdos215
