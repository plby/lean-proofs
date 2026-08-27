import Arxiv.Arxiv2411_18291.Decomposition

/-!
# Refining a clique decomposition into all smaller cliques

Replace every clique in a decomposition by all of its `q`-vertex subsets.
Every edge then has multiplicity exactly `choose(k-r,q-r)` in the original
host and zero outside it. The proof uses the unique containing large clique,
so it counts distinct smaller cliques rather than indexed occurrences.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {k q r : ℕ}

def cliqueRefinement (q : ℕ) (D : Finset (Block V k)) : Finset (Block V q) :=
  D.biUnion fun Q => cliqueEdges q Q

def cliqueSupport (r : ℕ) (D : Finset (Block V q)) : Hypergraph V r :=
  D.biUnion fun Q => cliqueEdges r Q

@[simp] theorem mem_cliqueRefinement (D : Finset (Block V k)) (P : Block V q) :
    P ∈ cliqueRefinement q D ↔ ∃ Q ∈ D, P.val ⊆ Q.val := by
  simp only [cliqueRefinement, mem_biUnion, mem_cliqueEdges]

theorem IsDecomposition.refinement_clique_subset {G : Hypergraph V r}
    {D : Finset (Block V k)} (hD : IsDecomposition G D)
    {P : Block V q} (hP : P ∈ cliqueRefinement q D) : cliqueEdges r P ⊆ G := by
  obtain ⟨Q, hQ, hPQ⟩ := (mem_cliqueRefinement D P).mp hP
  intro e he
  exact hD.clique_subset hQ ((mem_cliqueEdges _ _).mpr
    (((mem_cliqueEdges _ _).mp he).trans hPQ))

theorem IsDecomposition.refinement_support_subset {G : Hypergraph V r}
    {D : Finset (Block V k)} (hD : IsDecomposition G D) :
    cliqueSupport r (cliqueRefinement q D) ⊆ G := by
  intro e he
  obtain ⟨P, hP, heP⟩ := mem_biUnion.mp he
  exact hD.refinement_clique_subset hP heP

theorem IsDecomposition.refinement_multiplicity {G : Hypergraph V r}
    {D : Finset (Block V k)} (hD : IsDecomposition G D) (hqr : r ≤ q) (e : Block V r) :
    ((cliqueRefinement q D).filter fun P => e.val ⊆ P.val).card =
      if e ∈ G then (k - r).choose (q - r) else 0 := by
  by_cases he : e ∈ G
  · rw [if_pos he]
    obtain ⟨Q, ⟨hQ, heQ⟩, huniq⟩ := hD.unique he
    have hfilter : (cliqueRefinement q D).filter (fun P => e.val ⊆ P.val) =
        (cliqueEdges q Q).filter (fun P => e.val ⊆ P.val) := by
      ext P
      simp only [mem_filter, mem_cliqueRefinement, mem_cliqueEdges]
      constructor
      · rintro ⟨⟨Q', hQ', hPQ'⟩, heP⟩
        have heq : Q' = Q := huniq Q' ⟨hQ', heP.trans hPQ'⟩
        exact ⟨heq ▸ hPQ', heP⟩
      · rintro ⟨hPQ, heP⟩
        exact ⟨⟨Q, hQ, hPQ⟩, heP⟩
    rw [hfilter]
    have hc := card_blocks_between e.val Q.val heQ (by simpa only [e.property] using hqr)
    simpa only [cliqueEdges, filter_filter, Q.property, e.property, and_comm] using hc
  · rw [if_neg he, card_eq_zero]
    apply eq_empty_iff_forall_notMem.mpr
    intro P hP
    obtain ⟨hP, heP⟩ := mem_filter.mp hP
    exact he (hD.refinement_clique_subset hP ((mem_cliqueEdges _ _).mpr heP))

theorem IsDecomposition.refinement_multiplicity_le {G : Hypergraph V r}
    {D : Finset (Block V k)} (hD : IsDecomposition G D) (hqr : r ≤ q) (e : Block V r) :
    ((cliqueRefinement q D).filter fun P => e.val ⊆ P.val).card ≤ (k - r).choose (q - r) := by
  rw [hD.refinement_multiplicity hqr e]
  split_ifs <;> omega

theorem IsDecomposition.boundary_refinement {G : Hypergraph V r}
    {D : Finset (Block V k)} (hD : IsDecomposition G D) (hqr : r ≤ q) :
    boundary r (indicator (cliqueRefinement q D)) =
      fun e => ((k - r).choose (q - r) : ℤ) * indicator G e := by
  funext e
  rw [boundary_indicator, hD.refinement_multiplicity hqr e]
  by_cases he : e ∈ G <;> simp only [indicator, he, if_true, if_false, Nat.cast_zero,
    mul_one, mul_zero]

end Arxiv2411_18291
