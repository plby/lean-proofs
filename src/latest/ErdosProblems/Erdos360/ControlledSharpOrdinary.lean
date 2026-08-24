/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.ControlledNumericalLedger
import ErdosProblems.Erdos360.PrimePoolSharpOrdinary

/-!
# The controlled ordinary callback from sharp CFP pool numerics

This module installs the finite sharp prime-pool theorem into the exact
ordinary callback retained by the controlled numerical ledger.
-/

namespace Erdos360

attribute [local instance] Classical.propDecidable

/-- Uniform sharp pool numerics in the post-extraction cardinal range give
the exact controlled ordinary source callback. -/
theorem controlledPrimeOrdinarySourceCompletion_of_sharp_post
    (A C ratio : ℝ)
    (hsieve :
      ∀ n y sieveLevel K growth target stepBound Q : ℕ,
        ∀ X : Finset ℕ, ∀ ratio : ℝ,
        0 < n → 2 ≤ y → 101 ≤ sieveLevel → 0 < Q →
        Real.log A ≤ 2 * (sieveLevel - 100 : ℕ) / 99 →
        X.Nonempty →
        HasStepBoundedLongProgressionCover X (K * growth) stepBound →
        (∀ x ∈ X, Nat.Coprime (missingPrimeProduct n y) x) →
        (Q * (y ^ sieveLevel) ^ 2) ^ 3 ≤ X.card →
        0 ≤ ratio →
        (∀ step : ℕ, 0 < step → step ≤ stepBound →
          ((n * step : ℕ) : ℝ) / Nat.totient (n * step) ≤ ratio) →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (sieveLevel - 100)
        let V := C * ratio / Real.log (y : ℝ)
        ((K : ℝ) * target) * (((1 + eta) * V) + 1 / (Q : ℝ)) <
            (X.card : ℝ) →
        target < growth)
    {n colors y U B L M Q ell sieveLevel sieveCutoff sieveQ : ℕ}
    {hy : 2 * y < n}
    (hnum : CFPControlledPrimeNumericalLedger n y U B L M Q ell)
    (hcut : sieveCutoff ≤ y / U)
    (hsharp : ∀ d z : ℕ, 0 < d → d ≤ U → Q ≤ z → z ≤ M →
      CFPPrimePoolSharpNumerics A C ratio n sieveLevel sieveCutoff sieveQ
        y U z ell d) :
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
  exact exists_primePoolOrdinaryGrowthCertificate_of_sharp_numerics
    A C hsieve ratio hd hdn hnum.U_pos hcut hWsource hscale hPZ hPcard
      (hPZ.trans hZrange) hPdiverse
      (hsharp d Z.card hd hdU hZlower hZupper)

end Erdos360

#print axioms Erdos360.controlledPrimeOrdinarySourceCompletion_of_sharp_post
