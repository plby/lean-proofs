import Arxiv.Arxiv2411_18291.CliqueRemovalCounts
import Arxiv.Arxiv2411_18291.CliqueRefinement

/-! # Available cliques after a prescribed family has been selected -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

def remainingCliques (r : ℕ) (H D : Finset (Block V q)) : Finset (Block V q) :=
  H.filter fun Q => ∀ P ∈ D, Disjoint (cliqueEdges r Q) (cliqueEdges r P)

theorem mem_remainingCliques {H D : Finset (Block V q)} {Q : Block V q} :
    Q ∈ remainingCliques r H D ↔
      Q ∈ H ∧ ∀ P ∈ D, Disjoint (cliqueEdges r Q) (cliqueEdges r P) := mem_filter

@[simp] theorem remainingCliques_empty (H : Finset (Block V q)) :
    remainingCliques r H ∅ = H := by
  ext Q
  simp [remainingCliques]

theorem remainingCliques_subset (H D : Finset (Block V q)) : remainingCliques r H D ⊆ H :=
  filter_subset _ _

theorem remainingCliques_insert (H D : Finset (Block V q)) (Q : Block V q) :
    remainingCliques r H (insert Q D) = cliqueRemoval r (remainingCliques r H D) Q := by
  ext P
  rw [mem_remainingCliques, mem_cliqueRemoval, mem_remainingCliques]
  constructor
  · rintro ⟨hPH, hd⟩
    exact ⟨⟨hPH, fun R hR => hd R (mem_insert_of_mem hR)⟩, hd Q (mem_insert_self _ _)⟩
  · rintro ⟨⟨hPH, hd⟩, hPQ⟩
    refine ⟨hPH, ?_⟩
    intro R hR
    rcases mem_insert.mp hR with rfl | hRD
    · exact hPQ
    · exact hd R hRD

theorem remainingClique_not_selected (hqr : r ≤ q) {H D : Finset (Block V q)}
    {Q : Block V q} (hQ : Q ∈ remainingCliques r H D) : Q ∉ D := by
  intro hQD
  have hd := (mem_remainingCliques.mp hQ).2 Q hQD
  obtain ⟨e, he⟩ := cliqueEdges_nonempty hqr Q
  exact disjoint_left.mp hd he he

theorem remainingCliques_eq_graph_filter (G : Hypergraph V r) (H D : Finset (Block V q))
    (hH : ∀ Q ∈ H, cliqueEdges r Q ⊆ G) :
    remainingCliques r H D = H.filter (fun Q => cliqueEdges r Q ⊆ G \ cliqueSupport r D) := by
  ext Q
  rw [mem_remainingCliques, mem_filter]
  constructor
  · rintro ⟨hQH, hd⟩
    refine ⟨hQH, ?_⟩
    intro e he
    refine mem_sdiff.mpr ⟨hH Q hQH he, ?_⟩
    intro hD
    obtain ⟨P, hPD, heP⟩ := mem_biUnion.mp hD
    exact disjoint_left.mp (hd P hPD) he heP
  · rintro ⟨hQH, hQG⟩
    refine ⟨hQH, ?_⟩
    intro P hPD
    apply disjoint_left.mpr
    intro e heQ heP
    exact (mem_sdiff.mp (hQG heQ)).2 (mem_biUnion.mpr ⟨P, hPD, heP⟩)

end Arxiv2411_18291
