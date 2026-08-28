/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos577.FinalCount

/-!
# The Erdős--Faudree quadrilateral theorem (Erdős Problem 577)

Every finite simple graph on `4 * k` vertices with minimum degree at least
`2 * k` has `k` pairwise vertex-disjoint cycles of exactly length four.
The cycles need not be induced. The cases `k = 0` and `k = 1` are explicit.

The proof follows Hong Wang, Graphs and Combinatorics 26 (2010), 833--877,
Theorem B. All dependencies are proved in the supporting modules; the
mathematical reconstruction and Leanization map are in `tex/577.tex`.
-/

namespace Erdos577

variable {V : Type*} [Fintype V]

/-- The exact Erdős--Faudree theorem, with the boundary degree included. -/
theorem erdos_faudree (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) : HasPacking G k := by
  classical
  by_cases hzero : k = 0
  · subst k
    exact hasPacking_zero G
  by_cases hone : k = 1
  · subst k
    exact hasPacking_one G (by simpa using hcard) (by simpa using hdeg)
  by_contra hn
  obtain ⟨H, hGH, hH⟩ := exists_saturated_extension hn
  have hdegree : ∀ v, 2 * k ≤ H.degree v := minimum_degree_mono hGH (2 * k) hdeg
  obtain ⟨c, hc⟩ := hH.exists_strong_chain hcard hdegree
  exact hc.false_of_minimum_degree hcard hdegree hH.1

/-- An explicit injective product-indexed witness for all `k` ordinary four-cycles. -/
theorem exists_disjoint_four_cycles (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) :
    ∃ f : Fin k × Fin 4 ↪ V, ∀ i j, G.Adj (f (i, j)) (f (i, j + 1)) := by
  obtain ⟨p⟩ := erdos_faudree G k hcard hdeg
  exact ⟨p.vertices, p.adjacent⟩

/-- The same theorem stated directly using Mathlib's minimum degree. -/
theorem erdos_faudree_min_degree (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hcard : Fintype.card V = 4 * k) (hdeg : 2 * k ≤ G.minDegree) : HasPacking G k :=
  erdos_faudree G k hcard (fun v ↦ hdeg.trans (G.minDegree_le_degree v))

/-- Minimum degree `2 * k` on `4 * k` vertices gives `k` disjoint ordinary four-cycles. -/
theorem erdos_577 (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hcard : Fintype.card V = 4 * k) (hdeg : 2 * k ≤ G.minDegree) :
    ∃ f : Fin k × Fin 4 ↪ V, ∀ i j, G.Adj (f (i, j)) (f (i, j + 1)) :=
  exists_disjoint_four_cycles G k hcard (fun v ↦ hdeg.trans (G.minDegree_le_degree v))

end Erdos577
