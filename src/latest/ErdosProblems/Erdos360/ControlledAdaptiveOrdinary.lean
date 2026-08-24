/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.ControlledNumericalLedger
import ErdosProblems.Erdos360.PrimePoolAdaptiveOrdinary

/-!
# The structured ordinary callback from adaptive pool numerics

This module installs the finite adaptive-pool theorem into the exact
callback retained by the truthful controlled numerical ledger.
-/

namespace Erdos360

attribute [local instance] Classical.propDecidable

/-- Uniform adaptive pool numerics in the post-extraction cardinal range
give the exact ordinary source callback. -/
theorem controlledPrimeOrdinarySourceCompletion_of_adaptive_post
    {n colors y U B L M Q ell : ℕ} {hy : 2 * y < n}
    (hnum : CFPControlledPrimeNumericalLedger n y U B L M Q ell)
    (hadaptive : ∀ d z : ℕ, 0 < d → d ≤ U → Q ≤ z → z ≤ M →
      CFPPrimePoolAdaptiveNumerics y U z ell d) :
    CFPControlledPrimeOrdinarySourceCompletion
      n colors y U B L M ell (primeStructuredBelowTarget n y U hy) := by
  intro c i W d Z hW hWcard hd hdB hscale hloss hdiverse hdn hdU
  intro P hPlower hPcard hPdiverse
  have hZupper : Z.card ≤ M := by
    simpa [hWcard] using card_le_of_positive_scale_subset hd hscale
  have hZlower : Q ≤ Z.card :=
    extracted_card_lower_of_controlled_loss hd hWcard hscale hloss
      hnum.loss_room
  have hWsource : W ⊆ primeStructuredTestSet n y U := by
    intro a ha
    obtain ⟨x, hxY, _hxi, hxa⟩ := mem_integerColorClass.mp (hW ha)
    rw [← hxa]
    exact mem_primeStructuredBelowTarget_iff.mp hxY
  have hPZ : P ⊆ Z :=
    hPlower.trans (lowerPart_subset Z (Z.card % (8 * ell)))
  have hZrange : Z ⊆ Finset.Icc (y / d + 1) (2 * y / d) := by
    apply extracted_dyadic_quotient_exact_Icc
      (Y := primeStructuredBelowTarget n y U hy) (c := c) (i := i)
      (fun x hx ↦ primeStructuredBelowTarget_dyadic hx) hd
    intro z hz
    exact hW (hscale z hz)
  exact exists_primePoolOrdinaryGrowthCertificate_of_adaptive_numerics
    hd hdn hWsource hscale hPZ hPcard (hPZ.trans hZrange)
      hPdiverse (hadaptive d Z.card hd hdU hZlower hZupper)

end Erdos360

#print axioms Erdos360.controlledPrimeOrdinarySourceCompletion_of_adaptive_post
