/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1161.
https://www.erdosproblems.com/forum/thread/1161

Informal authors:
- Adrian Beker

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1161.md
-/
import ErdosProblems.Erdos1161.ResolutionGlue
import ErdosProblems.Erdos1161.LocalError
import ErdosProblems.Erdos1161.LargeOrders

/-!
# Erdős Problem 1161

For `n m : ℕ`, `orderCount n m` is the number of permutations in `Sₙ`
whose order is exactly `m`.  Beker proved that its largest fiber is
asymptotic to `(n - 1)!`, that every fiber at least this large eventually
satisfies the least-common-multiple condition, and that the eventual unique
mode is the least positive integer satisfying that condition.

The last clause corrects a transcription error on the local Erdős Problems
page: the source theorem characterizes equality with the *maximum fiber*, not
equality with `(n - 1)!`.  The detailed mathematical reconstruction and the
correspondence with the formal lemmas are in `tex/1161.tex`.
-/

open Filter Asymptotics

namespace Erdos1161

/-- Beker's resolution of Erdős Problem 1161.

The three clauses say, respectively:

* the maximum number of permutations of any one order is asymptotic to
  `(n - 1)!`;
* eventually, a fiber of size at least `(n - 1)!` has `m ≤ n` and satisfies
  `lcm(1, …, n - m) ∣ m`;
* eventually, `m` is a modal order exactly when it is the least positive
  integer satisfying that divisibility condition.
-/
theorem erdos_1161 :
    ((fun n : ℕ ↦ (maxOrderCount n : ℝ)) ~[atTop]
      (fun n : ℕ ↦ ((n - 1).factorial : ℝ))) ∧
    (∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      (n - 1).factorial ≤ orderCount n m →
        m ≤ n ∧ BekerCandidate n m) ∧
    (∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      IsMode n m ↔ IsLeast {k : ℕ | BekerCandidate n k} m) := by
  exact resolution_components_of_inputs
    eventual_threshold_structure uniform_local_expansion

end Erdos1161

#print axioms Erdos1161.erdos_1161
