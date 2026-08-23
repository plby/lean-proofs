/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 921.
https://www.erdosproblems.com/forum/thread/921

Informal authors:
- H. A. Kierstead
- Endre Szemerédi
- William T. Trotter Jr.

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos921.md
-/
import ErdosProblems.Erdos921.Assembly

/-!
# Erdős Problem 921

For fixed `k ≥ 4`, the largest possible odd-girth threshold of a
`k`-chromatic graph on `n` vertices has order `n ^ (1 / (k - 2))`.

The upper bound is the local-colouring argument of Kierstead, Szemerédi and
Trotter. The lower bound uses Schrijver's stable Kneser graphs; their exact
chromatic number is proved here from a finite octahedral Tucker lemma. A
detailed mathematical proof and Leanization map are in `tex/921.tex`.
-/

open Filter

namespace Erdos921

/-- Resolution of Erdős Problem 921. The function `f` is exactly the largest
`m` for which an `n`-vertex graph of chromatic number `k` has no odd cycle of
length at most `m`. -/
theorem erdos_921 (k : ℕ) (hk : 4 ≤ k) :
    (fun n : ℕ ↦ (f k n : ℝ)) =Θ[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (1 / (((k - 2 : ℕ) : ℝ)))) := by
  have hd : 2 ≤ k - 2 := by omega
  have h := erdos_921_aux (k - 2) hd
  simp only [one_div]
  change (fun n : ℕ ↦ (f k n : ℝ)) =Θ[atTop] rootScale (k - 2)
  simpa only [Nat.sub_add_cancel (by omega : 2 ≤ k)] using h

#print axioms Erdos921.erdos_921

end Erdos921
