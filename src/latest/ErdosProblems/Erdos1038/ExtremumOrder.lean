import ErdosProblems.Erdos1038.SupremumExamples

/-!
# Order-theoretic packaging of the two extremal problems

This file isolates the complete-lattice bookkeeping from the analytic
arguments.  In particular, a convergent sequence of admissible examples is
enough for the upper inequality at the infimum; no member of the sequence
needs to attain its limit.
-/

open scoped ENNReal
open Filter MeasureTheory Polynomial Topology

namespace Erdos1038

noncomputable section

/-- A uniform lower bound for all admissible polynomials is a lower bound for
the infimum. -/
theorem lowerBound_le_infimumLength {c : ℝ≥0∞}
    (h : ∀ f : Polynomial ℝ, IsAdmissible f → c ≤ sublevelVolume f) :
    c ≤ infimumLength := by
  rw [infimumLength]
  exact le_iInf fun f ↦ h f.1 f.2

/-- Every individual admissible example bounds the infimum from above. -/
theorem infimumLength_le_sublevelVolume {f : Polynomial ℝ}
    (hf : IsAdmissible f) : infimumLength ≤ sublevelVolume f := by
  let g : AdmissiblePolynomial := ⟨f, hf⟩
  exact iInf_le (fun p : AdmissiblePolynomial ↦ sublevelVolume p.1) g

/-- A limit of admissible sublevel volumes bounds the infimum from above. -/
theorem infimumLength_le_of_tendsto
    (f : ℕ → AdmissiblePolynomial) {c : ℝ≥0∞}
    (hlim : Tendsto (fun n ↦ sublevelVolume (f n).1) atTop (𝓝 c)) :
    infimumLength ≤ c := by
  exact ge_of_tendsto' hlim fun n ↦ infimumLength_le_sublevelVolume (f n).2

/-- Uniform lower control plus a recovering sequence identifies the
infimum exactly. -/
theorem infimumLength_eq_of_lower_and_tendsto
    (f : ℕ → AdmissiblePolynomial) {c : ℝ≥0∞}
    (hlower : ∀ g : Polynomial ℝ, IsAdmissible g → c ≤ sublevelVolume g)
    (hlim : Tendsto (fun n ↦ sublevelVolume (f n).1) atTop (𝓝 c)) :
    infimumLength = c := by
  exact le_antisymm (infimumLength_le_of_tendsto f hlim)
    (lowerBound_le_infimumLength hlower)

/-- A uniform upper bound for all admissible polynomials bounds the
supremum. -/
theorem supremumLength_le_upperBound {c : ℝ≥0∞}
    (h : ∀ f : Polynomial ℝ, IsAdmissible f → sublevelVolume f ≤ c) :
    supremumLength ≤ c := by
  rw [supremumLength]
  exact iSup_le fun f ↦ h f.1 f.2

/-- Tao's uniform upper inequality, once formalized, combines with the
explicit family to give the exact supremum. -/
theorem supremumLength_eq_proposed
    (hupper : ∀ f : Polynomial ℝ, IsAdmissible f →
      sublevelVolume f ≤ ENNReal.ofReal (2 * Real.sqrt 2)) :
    supremumLength = ENNReal.ofReal (2 * Real.sqrt 2) := by
  exact le_antisymm (supremumLength_le_upperBound hupper)
    proposedSupremum_le_supremumLength

end

end Erdos1038
