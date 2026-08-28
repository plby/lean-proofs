import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFourierDerivativesAll
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The mode derivatives do not depend on the ambient extension

Every ambient function agreeing with the original inverse mode on the
original open base has exactly the same complex derivatives there. Thus
the zero extension used for notation does not alter the native germs.
In particular all derivatives of the actual zero Fourier mode vanish.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeFourier

open Set Topology TopologicalSpace PeriodTorusLineBundleClassification

variable {U₀ : Opens ℂ} (P : HolomorphicPeriodMap ℂ U₀)

/-- Every derivative is fixed by the original inverse-mode germ, regardless
of how an ambient representative is defined outside the original base. -/
theorem iteratedDeriv_ambientInverse_eq (p₀ : PeriodDomain) (k : Fin 4 → ℤ)
    (g : ℂ → ℂ)
    (hg : ∀ b : U₀, g b = denominatorInverse p₀ (P.point b) (integerFrequency k))
    (n : ℕ) (b : U₀) :
    iteratedDeriv n (ambientInverse P p₀ k) (b : ℂ) = iteratedDeriv n g (b : ℂ) := by
  have heq : EqOn (ambientInverse P p₀ k) g (U₀ : Set ℂ) := by
    intro z hz
    exact (ambientInverse_apply P p₀ k ⟨z, hz⟩).trans (hg ⟨z, hz⟩).symm
  exact heq.iteratedDeriv_of_isOpen U₀.isOpen n b.property

/-- The original zero-frequency multiplier and all its base derivatives
vanish identically on the original open base. -/
theorem iteratedDeriv_ambientInverse_zero (p₀ : PeriodDomain) (n : ℕ) (b : U₀) :
    iteratedDeriv n (ambientInverse P p₀ 0) (b : ℂ) = 0 := by
  have h := iteratedDeriv_ambientInverse_eq P p₀ 0 (fun _ => 0)
    (by intro z; simp only [integerFrequency_zero, denominatorInverse_zero]) n b
  simpa only [iteratedDeriv_fun_const_zero] using h

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeFourier
