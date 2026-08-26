/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Formalization of Erdős Problem 71, ported from Lean/Mathlib 4.28.0.
Informal author: Béla Bollobás.
Formal authors: Andres Gutierrez, Aristotle, GPT-5.5, Opus 4.7.
Source: https://www.erdosproblems.com/forum/thread/71#post-6635
The exact online-editor source is preserved as andresg535_71 in data/urls.yaml.
This file has been modified for the repository and Lean/Mathlib 4.33.0.
-/
import ErdosProblems.Erdos71.Proof

namespace Erdos71

/-- **Erdős Problem 71** (Bollobás, *Cycles modulo k*, 1977).

For every infinite arithmetic progression `P` containing an even number,
there is a constant `c = c(P)` such that every finite simple graph `G`
with average degree at least `c` contains a cycle whose length lies in `P`.

The heavy lifting is done by `erdos_71_of_edge_density`, which states the
same result with the integer-valued hypothesis `c · |V| ≤ |E|`. The wrapper
scales the constant by `2` (since `avgDegree G = 2 |E| / |V|`) and
converts the rational inequality. -/
theorem erdos_71 (P : InfiniteAP) (heven : P.ContainsEven) :
    ∃ c : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V] [Nonempty V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      (c : ℚ) ≤ avgDegree G →
      ∃ n ∈ P, HasCycleOfLength G n := by
  obtain ⟨c, hc⟩ := erdos_71_of_edge_density P heven
  refine ⟨2 * c, fun V _ _ _ G _ hdeg => hc V G ?_⟩
  -- `hdeg : (2 * c : ℚ) ≤ 2 |E| / |V|` ⟹ `c · |V| ≤ |E|` in ℕ.
  have hV_pos : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  unfold avgDegree at hdeg
  have h_ℚ : (c * Fintype.card V : ℚ) ≤ G.edgeFinset.card := by
    have := (le_div_iff₀ hV_pos).mp hdeg
    push_cast at this
    linarith
  exact_mod_cast h_ℚ

#print axioms erdos_71
-- 'Erdos71.erdos_71' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos71
