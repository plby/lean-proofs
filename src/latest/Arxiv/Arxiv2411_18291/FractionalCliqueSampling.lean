import Arxiv.Arxiv2411_18291.FiniteCountSampling
import Arxiv.Arxiv2411_18291.RootedCliqueExtensions

/-!
# From fractional edge regularity to an actual clique family

Use the fractional coefficients as independent sampling probabilities.
The sampled family consists only of graph cliques, and a finite union-bound
criterion ensures simultaneous relative error at every graph edge.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem exists_clique_family_from_fractional (G : Hypergraph V r) (p : Block V q → ℝ)
    (hp : ∀ Q, 0 ≤ p Q ∧ p Q ≤ 1) (hs : ∀ Q, ¬cliqueEdges r Q ⊆ G → p Q = 0)
    {μ c : ℝ} (hboundary : boundary r p = fun e => if e ∈ G then μ else 0) (hc : 0 ≤ c)
    (hsmall : G.card * (2 * Real.exp (-(μ * c ^ 2 / (2 * (1 + 2 * c))))) < 1) :
    ∃ H : Finset (Block V q), H ⊆ cliqueFamily G q ∧ ∀ e ∈ G,
      |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - μ| ≤ c * μ := by
  let D := cliqueFamily G q
  let s (e : Block V r) := D.filter fun Q => e.val ⊆ Q.val
  let p' (Q : Block V q) : unitInterval := ⟨p Q, hp Q⟩
  have hmean (e : Block V r) (he : e ∈ G) : (∑ Q ∈ s e, (p' Q : ℝ)) = μ := by
    calc
      _ = ∑ Q ∈ D, if e.val ⊆ Q.val then p Q else 0 := by
        simp only [s, p', sum_filter]
      _ = ∑ Q, if e.val ⊆ Q.val then p Q else 0 := by
        apply sum_subset (subset_univ _)
        intro Q _ hQ
        have hz : p Q = 0 := hs Q (fun h => hQ (mem_filter.mpr ⟨mem_univ _, h⟩))
        simp only [hz, ite_self]
      _ = μ := by
        change boundary r p e = μ
        simpa only [if_pos he] using congrFun hboundary e
  obtain ⟨H, hH, hcounts⟩ := IndependentBernoulliChoice.exists_subset_with_concentrated_counts
    D G s (fun _ _ => filter_subset _ _) p' hc hmean hsmall
  refine ⟨H, hH, ?_⟩
  intro e he
  have heq : H ∩ s e = H.filter fun Q => e.val ⊆ Q.val := by
    ext Q
    simp only [s, mem_inter, mem_filter]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hH h.1, h.2⟩⟩
  simpa only [heq] using hcounts e he

end Arxiv2411_18291
