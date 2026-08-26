import ErdosProblems.Erdos745.Model
import ErdosProblems.Erdos745.Components
import ErdosProblems.Erdos745.Moments
import ErdosProblems.Erdos745.PairRatio
import ErdosProblems.Erdos745.EdgeLaw
import ErdosProblems.Erdos745.TreeComponents
import ErdosProblems.Erdos745.Prufer
import ErdosProblems.Erdos745.TreeCounting
import ErdosProblems.Erdos745.TreeMoments
import ErdosProblems.Erdos745.CriticalLower
import ErdosProblems.Erdos745.CriticalUpper
import ErdosProblems.Erdos745.MacroscopicUniqueness

/-!
# Erdős Problem 745

The two parameter regimes are kept separate: the KSS logarithmic conclusion
uses a fixed parameter `λ > 1`, whereas `λ = 1` has scale `n^(2/3)`.
-/

namespace Erdos745

open scoped Topology

/-- The corrected KSS logarithmic upper bound, with the sharp threshold for
its leading coefficient, for each fixed supercritical parameter. -/
theorem erdos745_supercritical (lam : ℝ) (hlam : 1 < lam) (A : ℝ)
    (hA : 1 / (lam - 1 - Real.log lam) < A) :
    Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1) := by
  apply kss_logarithmic lam hlam A
  simpa only [logarithmicConstant, logarithmicDecay, one_div] using hA

/-- The critical conclusion with all probability and eventuality quantifiers
explicit: the constants may depend on the error tolerance, but not on `n`. -/
theorem erdos745_critical :
    ∀ ε : ℝ, 0 < ε → ∃ c C : ℝ, 0 < c ∧ c < C ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        1 - ε ≤ criticalProbability n (fun G ↦
          c * (n : ℝ) ^ (2 / 3 : ℝ) ≤ (secondLargestComponentOrder G : ℝ) ∧
          (secondLargestComponentOrder G : ℝ) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ)) := by
  intro ε hε
  obtain ⟨c, C, hc, hcC, hprob⟩ := critical_secondLargest_scaling ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hprob
  exact ⟨c, C, hc, hcC, N, hN⟩

/-- Both parameter regimes in the corrected resolution of Erdős Problem 745. -/
theorem erdos745 : KSSLogarithmicStatement ∧ CriticalSecondLargestScaling :=
  ⟨kss_logarithmic, critical_secondLargest_scaling⟩

/-- The logarithmic second-component bound belongs to the supercritical
regime `lam > 1`, not to the critical graph `G(n, 1 / n)`. -/
theorem erdos_745_supercritical (lam : ℝ) (hlam : 1 < lam) (A : ℝ)
    (hA : 1 / (lam - 1 - Real.log lam) < A) :
    Filter.Tendsto (fun n : ℕ ↦ probability lam n (fun G ↦
      (secondLargestComponentOrder G : ℝ) ≤ A * Real.log (n : ℝ)))
      Filter.atTop (𝓝 1) :=
  erdos745_supercritical lam hlam A hA

/-- At the literal parameter in Erdős Problem 745, the second-largest
component has order `n ^ (2 / 3)` in probability. -/
theorem erdos_745 :
    ∀ ε : ℝ, 0 < ε → ∃ c C : ℝ, 0 < c ∧ c < C ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        1 - ε ≤ criticalProbability n (fun G ↦
          c * (n : ℝ) ^ (2 / 3 : ℝ) ≤ (secondLargestComponentOrder G : ℝ) ∧
          (secondLargestComponentOrder G : ℝ) ≤ C * (n : ℝ) ^ (2 / 3 : ℝ)) :=
  erdos745_critical

end Erdos745
