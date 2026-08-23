/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 814.
https://www.erdosproblems.com/forum/thread/814

Informal authors:
- Lisa Sauermann

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos814.md
-/
import ErdosProblems.Erdos814.Sauermann

/-!
# Erdős Problem 814

This file states the problem exactly for finite simple graphs on `Fin n` and
specializes the signed-shortage form of Sauermann's theorem proved in the
supporting modules.  A detailed mathematical proof and Leanization map are in
`tex/814.tex`.
-/

open Finset SimpleGraph

namespace Erdos814

/-- The stronger, published "at least the threshold" form of Problem 814. -/
def Erdos814AtLeastStatement : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, k - 1 ≤ n →
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          edgeThreshold k n ≤ G.edgeFinset.card →
            ∃ S : Finset (Fin n),
              S.Nonempty ∧
              (S.card : ℝ) ≤ (1 - c) * (n : ℝ) ∧
              k ≤ (G.induce (↑S : Set (Fin n))).minDegree

/-- The page-literal form, in which the graph has exactly the displayed number
of edges.  The factor `n + 2 - k` is the faithful natural-number encoding of
the mathematical integer expression `n-k+2` under `k-1 ≤ n`. -/
def Erdos814Statement : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, k - 1 ≤ n →
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          G.edgeFinset.card = edgeThreshold k n →
            ∃ S : Finset (Fin n),
              S.Nonempty ∧
              (S.card : ℝ) ≤ (1 - c) * (n : ℝ) ∧
              k ≤ (G.induce (↑S : Set (Fin n))).minDegree

/-- Sauermann's theorem yields the uniform explicit choice
`c_k = 1 / (10000 k^3)`, and in fact proves the stronger at-least form. -/
theorem erdos_814_atLeast : Erdos814AtLeastStatement := by
  intro k hk
  refine ⟨1 / (10000 * (k : ℝ) ^ 3), ?_, ?_⟩
  · positivity
  intro n hn G _ hEdges
  have hEdgesInt : (edgeThreshold k n : ℤ) ≤ (G.edgeFinset.card : ℤ) := by
    exact_mod_cast hEdges
  have hThreshold := edgeThreshold_cast_eq k n hk hn
  have hshort : shortage k G (Finset.univ : Finset (Fin n)) ≤ problemT k := by
    simp only [shortage, edgeCount_univ, Finset.card_univ, Fintype.card_fin]
    rw [hThreshold] at hEdgesInt
    push_cast at hEdgesInt ⊢
    omega
  obtain ⟨S, -, hSnonempty, hSmin, hSsmall⟩ :=
    sauermann_uniform_on G (k := k) (t := problemT k) hk
      (problemT_add_one_le_Tmax k) (Finset.univ : Finset (Fin n))
      (by simpa using hn) hshort
  refine ⟨S, hSnonempty, card_le_one_sub_inv_mul k S.card n hk ?_, ?_⟩
  · simpa using hSsmall
  · exact (hasMinDegreeOn_iff_induce_minDegree G S k).mp hSmin |>.2

/-- Positive resolution of Erdős Problem 814. -/
theorem erdos_814 : Erdos814Statement := by
  refine Iff.mp ?_ trivial
  constructor
  · intro _ k hk
    obtain ⟨c, hc, hstrong⟩ := erdos_814_atLeast k hk
    refine ⟨c, hc, ?_⟩
    intro n hn G _ hEdges
    exact hstrong n hn G hEdges.symm.le
  · intro _
    trivial

#print axioms Erdos814.erdos_814

end Erdos814
