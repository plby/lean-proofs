import ErdosProblems.Erdos336.Proof

/-!
Colin Snyder and GPT-5.6's F-160 proof claim for Erdős Problem 336,
ported to Lean 4.33.0. See Erdos336/README.md for provenance and prior work.
-/

namespace Erdos336

/-- The finite attained maxima exist, and their normalized limit is one third. -/
theorem erdos_336 :
    (∃ h : ℕ → ℕ, IsExtremalFunction h) ∧
    ∀ h : ℕ → ℕ, IsExtremalFunction h →
      Filter.Tendsto (fun r : ℕ => (h r : ℝ) / (r : ℝ) ^ 2)
        Filter.atTop (nhds (1 / 3 : ℝ)) := by
  exact problem336

end Erdos336

#print axioms Erdos336.erdos_336
