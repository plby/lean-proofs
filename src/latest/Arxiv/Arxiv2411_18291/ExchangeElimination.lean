import Arxiv.Arxiv2411_18291.ExchangeNearFar

/-!
# Eliminating a pair of opposite signs

Remove the positive base and a designated negative clique from the two
decompositions. The remaining signed cliques have the boundary of the
cancelled pair. They avoid its common edge; the negative replacements are
edge-disjoint and avoid the positive root. The strengthened exchange
construction bounds their intersections with the negative root as well.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem IsCrossSimple.inter_eq {P N : Finset (Block V q)} (h : IsCrossSimple r P N)
    {Q R : Block V q} (hQ : Q ∈ P) (hR : R ∈ N) {e : Block V r}
    (heQ : e ∈ cliqueEdges r Q) (heR : e ∈ cliqueEdges r R) : Q.val ∩ R.val = e.val := by
  have he : e.val ⊆ Q.val ∩ R.val :=
    subset_inter ((mem_cliqueEdges _ _).mp heQ) ((mem_cliqueEdges _ _).mp heR)
  exact (eq_of_subset_of_card_le he (by simpa only [e.property] using h Q hQ R hR)).symm

def ExchangeSystem.eliminationPositive (S : ExchangeSystem V q r) (N : Block V q) :=
  S.negative.erase N

def ExchangeSystem.eliminationNegative (S : ExchangeSystem V q r) := S.positive.erase S.base

def ExchangeSystem.eliminationCliques (S : ExchangeSystem V q r) (N : Block V q) :=
  S.eliminationPositive N ∪ S.eliminationNegative

def ExchangeSystem.eliminationVector (S : ExchangeSystem V q r) (N : Block V q) :
    Block V q → ℤ := indicator (S.eliminationPositive N) - indicator S.eliminationNegative

theorem ExchangeSystem.boundary_elimination (S : ExchangeSystem V q r)
    {N : Block V q} (hN : N ∈ S.negative) :
    boundary r (S.eliminationVector N) =
      indicator (cliqueEdges r S.base) - indicator (cliqueEdges r N) := by
  have hn : indicator (S.negative.erase N) = indicator S.negative - indicator {N} := by
    rw [← sdiff_singleton_eq_erase, indicator_sdiff (singleton_subset_iff.mpr hN)]
  have hp : indicator (S.positive.erase S.base) = indicator S.positive - indicator {S.base} := by
    rw [← sdiff_singleton_eq_erase, indicator_sdiff (singleton_subset_iff.mpr S.base_mem)]
  rw [eliminationVector, eliminationPositive, eliminationNegative, hn, hp, boundary_sub,
    boundary_sub, boundary_sub, S.negative_decomposition, S.positive_decomposition,
    boundary_indicator_singleton, boundary_indicator_singleton]
  funext e
  simp only [Pi.sub_apply]
  ring

theorem ExchangeSystem.elimination_signs_disjoint (S : ExchangeSystem V q r) (N : Block V q) :
    Disjoint (S.eliminationPositive N) S.eliminationNegative :=
  Disjoint.mono (erase_subset _ _) (erase_subset _ _) S.disjoint.symm

theorem ExchangeSystem.elimination_clique_subset (S : ExchangeSystem V q r)
    (N : Block V q) {Q : Block V q} (hQ : Q ∈ S.eliminationCliques N) :
    cliqueEdges r Q ⊆ S.graph := by
  rcases mem_union.mp hQ with hp | hn
  · exact S.negative_decomposition.clique_subset (mem_erase.mp hp).2
  · exact S.positive_decomposition.clique_subset (mem_erase.mp hn).2

theorem ExchangeSystem.eliminationPositive_disjoint_negative (S : ExchangeSystem V q r)
    {N Q : Block V q} (hN : N ∈ S.negative) (hQ : Q ∈ S.eliminationPositive N) :
    Disjoint (cliqueEdges r Q) (cliqueEdges r N) :=
  S.negative_decomposition.cliques_disjoint (mem_erase.mp hQ).2 hN (mem_erase.mp hQ).1

theorem ExchangeSystem.eliminationNegative_disjoint_base (S : ExchangeSystem V q r)
    {Q : Block V q} (hQ : Q ∈ S.eliminationNegative) :
    Disjoint (cliqueEdges r Q) (cliqueEdges r S.base) :=
  S.positive_decomposition.cliques_disjoint (mem_erase.mp hQ).2 S.base_mem (mem_erase.mp hQ).1

theorem ExchangeSystem.elimination_avoids_common (S : ExchangeSystem V q r)
    {N : Block V q} (hN : N ∈ S.negative) {e : Block V r}
    (heP : e ∈ cliqueEdges r S.base) (heN : e ∈ cliqueEdges r N)
    {Q : Block V q} (hQ : Q ∈ S.eliminationCliques N) : e ∉ cliqueEdges r Q := by
  intro heQ
  rcases mem_union.mp hQ with hp | hn
  · exact disjoint_left.mp (S.eliminationPositive_disjoint_negative hN hp) heQ heN
  · exact disjoint_left.mp (S.eliminationNegative_disjoint_base hn) heQ heP

theorem ExchangeSystem.eliminationNegative_pairwise (S : ExchangeSystem V q r) :
    (S.eliminationNegative : Set (Block V q)).Pairwise
      (fun P Q => Disjoint (cliqueEdges r P) (cliqueEdges r Q)) := by
  intro P hP Q hQ hPQ
  exact S.positive_decomposition.cliques_disjoint
    (mem_erase.mp hP).2 (mem_erase.mp hQ).2 hPQ

theorem ExchangeSystem.eliminationNegative_inter (S : ExchangeSystem V q r)
    (hcross : IsCrossSimple r S.positive S.negative) {N Q : Block V q}
    (hN : N ∈ S.negative) (hQ : Q ∈ S.eliminationNegative) {e : Block V r}
    (heQ : e ∈ cliqueEdges r Q) (heN : e ∈ cliqueEdges r N) :
    Q.val ∩ N.val = e.val := hcross.inter_eq (mem_erase.mp hQ).2 hN heQ heN

theorem IsExchangeFamily.pair_local {S : ExchangeSystem V q r}
    {A : Finset (Block V q)} (hA : IsExchangeFamily S A) {N : Block V q} (hN : N ∈ A)
    {e : Block V r} (he : e ∈ S.graph) :
    e.val ∩ (S.base.val ∪ N.val) ⊆ S.base.val ∨
      e.val ∩ (S.base.val ∪ N.val) ⊆ N.val := by
  have hsub : S.base.val ∪ N.val ⊆ S.base.val ∪ A.biUnion Subtype.val :=
    union_subset_union_right (subset_biUnion_of_mem Subtype.val hN)
  rcases hA.2.2.2.2 e he with hb | ⟨Q, hQ, hlocal⟩
  · exact Or.inl ((inter_subset_inter Subset.rfl hsub).trans hb)
  · by_cases hQN : Q = N
    · exact Or.inr ((inter_subset_inter Subset.rfl hsub).trans (hQN ▸ hlocal))
    · left
      intro v hv
      by_contra hvB
      have hvN : v ∈ N.val := (mem_union.mp (mem_inter.mp hv).2).resolve_left hvB
      have hvQ := hlocal ((inter_subset_inter Subset.rfl hsub) hv)
      exact disjoint_left.mp (hA.2.2.2.1 hQ hN hQN)
        (mem_sdiff.mpr ⟨hvQ, hvB⟩) (mem_sdiff.mpr ⟨hvN, hvB⟩)

theorem IsExchangeFamily.pair_admissible {S : ExchangeSystem V q (r + 1)}
    {A : Finset (Block V q)} (hA : IsExchangeFamily S A) (hqr : r + 1 ≤ q)
    {N : Block V q} (hN : N ∈ A) : IsAdmissible S.graph (S.base.val ∪ N.val) := by
  intro e he _
  have hc : (e.val ∩ (S.base.val ∪ N.val)).card ≤ r + 1 := by
    simpa only [e.property] using card_le_card
      (inter_subset_left (s₁ := e.val) (s₂ := S.base.val ∪ N.val))
  rcases hA.pair_local hN he with hb | hn
  · obtain ⟨s, hs, hsB, hsr⟩ := exists_subsuperset_card_eq hb hc
      (by simpa only [S.base.property] using hqr)
    refine ⟨⟨s, hsr⟩, S.positive_decomposition.clique_subset S.base_mem
      ((mem_cliqueEdges _ _).mpr hsB), hsB.trans subset_union_left, hs⟩
  · obtain ⟨s, hs, hsN, hsr⟩ := exists_subsuperset_card_eq hn hc
      (by simpa only [N.property] using hqr)
    refine ⟨⟨s, hsr⟩, S.negative_decomposition.clique_subset (hA.1 hN)
      ((mem_cliqueEdges _ _).mpr hsN), hsN.trans subset_union_right, hs⟩

end Arxiv2411_18291
