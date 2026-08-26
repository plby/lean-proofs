import ErdosProblems.Erdos1002.GaussPrefixAnnularMidpointAssembly
import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperContracted
import ErdosProblems.Erdos1002.IteratedBoundaryRestoration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Restoring the upper retained time boxes

The oscillatory late-case proof is naturally carried out for time boxes
contracted by a fixed `eta > 0`.  This file isolates the final order of
limits: first `N → ∞` at fixed contraction, then `eta ↓ 0`.  The already
proved time-boundary estimate controls the difference from the literal
upper retained family.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

/-- Fixed-contraction version of upper retained Fourier cancellation. -/
def GaussPrefixAnnularContractedUpperRetainedFourierLimits : Prop :=
  ∀ {ε A : ℝ}, 0 < ε → ε < A →
    ∀ {grid : ℕ}, 0 < grid →
      ∀ (k : AnnularGridIndex grid → ℕ),
        ∀ (hr : 0 < MixedOccurrenceCount k),
        ∀ (_htime : ∀ i, 0 < k i → i.time.1 < grid),
        ∀ (_hsigned : ∀ i, 0 < k i → i.signed.1 < grid),
        ∀ (mode :
          (Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k) →
            Fin (MixedOccurrenceCount k) → ℤ),
          ∀ (hmode : ∀ e, mode e ≠ 0),
          ∀ rho : ℝ, 0 < rho →
            ∀ eta : ℝ, 0 < eta →
              Tendsto
                (fun N : ℕ ↦
                  ∑ e : Fin (MixedOccurrenceCount k) ≃
                      GaussPrefixMixedOccurrence k,
                    uniformMovingSignedMarkedFourierTupleSum
                      N (Real.log (N : ℝ))
                      (flattenedAnnularSignedLower ε A e)
                      (flattenedAnnularSignedUpper ε A e)
                      (mode e)
                      (contractedAnnularCanonicalLaterUpperMidpointTupleFamily
                        eta rho N k hr e (mode e) (hmode e)))
                atTop (nhds 0)

/-- Cancellation for every fixed positive contraction restores to
cancellation of the full upper retained family, with the contraction
chosen before the main asymptotic limit. -/
theorem gaussPrefixAnnularUpperRetainedFourierLimits_of_contracted
    (hcontracted :
      GaussPrefixAnnularContractedUpperRetainedFourierLimits) :
    GaussPrefixAnnularUpperRetainedFourierLimits := by
  intro ε A hε hεA grid hgrid k hr htime hsigned mode hmode rho hrho
  let full : ℕ → ℂ := fun N ↦
    annularCanonicalUniformUpperRetainedMarkedFourierSum
      ε A rho N k hr mode hmode
  let contracted : ℕ → ℕ → ℂ := fun m N ↦
    ∑ e : Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k,
      uniformMovingSignedMarkedFourierTupleSum
        N (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        (mode e)
        (contractedAnnularCanonicalLaterUpperMidpointTupleFamily
          (1 / ((m : ℝ) + 1)) rho N k hr e
          (mode e) (hmode e))
  let boundary : ℕ → ℕ → ℝ := fun m N ↦
    ∑ e : Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k,
      ‖uniformMovingSignedMarkedFourierTupleSum
            N (Real.log (N : ℝ))
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e)
            (mode e)
            (annularCanonicalLaterUpperMidpointTupleFamily
              rho N k hr e (mode e) (hmode e)) -
        uniformMovingSignedMarkedFourierTupleSum
            N (Real.log (N : ℝ))
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e)
            (mode e)
            (contractedAnnularCanonicalLaterUpperMidpointTupleFamily
              (1 / ((m : ℝ) + 1)) rho N k hr e
              (mode e) (hmode e))‖
  have hdifference :
      ∀ m : ℕ, ∀ᶠ N : ℕ in atTop,
        ‖full N - contracted m N‖ ≤ boundary m N := by
    intro m
    exact Eventually.of_forall fun N ↦ by
      dsimp only [full, contracted, boundary,
        annularCanonicalUniformUpperRetainedMarkedFourierSum]
      rw [← Finset.sum_sub_distrib]
      exact norm_sum_le _ _
  have hfixed :
      ∀ m : ℕ, Tendsto (contracted m) atTop (nhds 0) := by
    intro m
    have heta : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    simpa only [contracted] using!
      hcontracted hε hεA hgrid k hr htime hsigned
        mode hmode rho hrho (1 / ((m : ℝ) + 1)) heta
  have hboundary :
      ∀ {δ : ℝ}, 0 < δ →
        ∀ᶠ m : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
          boundary m N < δ := by
    intro δ hδ
    simpa only [boundary] using!
      eventually_eventually_sum_norm_upperRetained_sub_contracted_lt
        hε hεA rho hgrid k hr htime hsigned mode hmode hδ
  simpa only [full] using!
    tendsto_zero_of_iterated_contracted_boundary
      full contracted boundary hdifference hfixed hboundary

end

end Erdos1002
