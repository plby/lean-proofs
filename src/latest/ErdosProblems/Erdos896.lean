/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 896.
https://www.erdosproblems.com/forum/thread/896

Informal authors:
- Przemek Chojecki
- GPT-5.5 Pro

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos896.md
-/
import ErdosProblems.Erdos896.UpperBridge
import ErdosProblems.Erdos896.LowerBridge
import ErdosProblems.Erdos896.Ford.TableUpper
import ErdosProblems.Erdos896.Ford.LowerAnalytic

/-!
# Erdős Problem 896

For `A, B ⊆ {1, ..., N}`, `F A B` counts the products having exactly one
ordered representation `a * b` with `a ∈ A` and `b ∈ B`. The main result is
the Ford-scale estimate

`maxF N = Θ(N² / ((log N)^δ (log log N)^(3/2)))`.

The detailed mathematical proof and Leanization map are in `tex/896.tex`.
-/

namespace Erdos896

open Filter Asymptotics

/-- Erdős Problem 896: the largest number of uniquely represented products
from two subsets of `{1, ..., N}` has the Erdős--Tenenbaum--Ford order of
magnitude. -/
theorem erdos_896 :
    (fun N : ℕ ↦ (maxF N : ℝ)) =Θ[atTop] scale896 := by
  obtain ⟨c, hc, hmass, hloss⟩ :=
    Ford.exists_massLower_and_multipleLossSmall
  exact maxF_isTheta_scale896_of_upper_and_lower
    Ford.multiplicationTable_isBigO_scale896
    (maxF_isBigOmega_scale896_of_lower_inputs hc hmass hloss)

end Erdos896

#print axioms Erdos896.erdos_896
