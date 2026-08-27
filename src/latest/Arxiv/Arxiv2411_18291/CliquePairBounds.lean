import Arxiv.Arxiv2411_18291.RepeatedCliqueRoots

/-!
# Repetition bounds for pairs of overlapping cliques

If the input clique family covers each edge at most `M` times, a fixed
clique has at most `choose(q,r)*M` possible partners sharing an edge.
Thus a sequence of distinct ordered pairs has bounded repetition in
either coordinate, and its prescribed root-edge families are bounded.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r M : ℕ}

omit [Fintype V] in
theorem overlapping_cliques_count_le [Finite V] (D : Finset (Block V q))
    (hmult : ∀ e : Block V r, (D.filter fun Q => e.val ⊆ Q.val).card ≤ M)
    (P : Block V q) :
    (D.filter fun Q => r ≤ (Q.val ∩ P.val).card).card ≤ q.choose r * M := by
  let : Fintype V := Fintype.ofFinite V
  have hsub : D.filter (fun Q => r ≤ (Q.val ∩ P.val).card) ⊆
      (cliqueEdges r P).biUnion (fun e => D.filter fun Q => e.val ⊆ Q.val) := by
    intro Q hQ
    obtain ⟨hQD, hcard⟩ := mem_filter.mp hQ
    obtain ⟨s, hs, hsr⟩ := exists_subset_card_eq hcard
    exact mem_biUnion.mpr ⟨⟨s, hsr⟩, (mem_cliqueEdges _ _).mpr (hs.trans inter_subset_right),
      mem_filter.mpr ⟨hQD, hs.trans inter_subset_left⟩⟩
  calc
    _ ≤ ∑ e ∈ cliqueEdges r P, (D.filter fun Q => e.val ⊆ Q.val).card :=
      (card_le_card hsub).trans card_biUnion_le
    _ ≤ ∑ _e ∈ cliqueEdges r P, M := sum_le_sum fun e _ => hmult e
    _ = _ := by simp only [sum_const, nsmul_eq_mul, card_cliqueEdges, Nat.cast_id]

variable {I : Type*} [Fintype I]

omit [Fintype V] in
theorem clique_pair_first_count_le [Finite V] (D : Finset (Block V q)) (P N : I → Block V q)
    (hN : ∀ i, N i ∈ D) (hinj : Function.Injective fun i => (P i, N i))
    (hcommon : ∀ i, r ≤ ((P i).val ∩ (N i).val).card)
    (hmult : ∀ e : Block V r, (D.filter fun Q => e.val ⊆ Q.val).card ≤ M)
    (Q : Block V q) : (univ.filter fun i => P i = Q).card ≤ q.choose r * M := by
  have hc : (univ.filter fun i => P i = Q).card ≤
      (D.filter fun R => r ≤ (R.val ∩ Q.val).card).card := by
    apply card_le_card_of_injOn N
    · intro i hi
      refine mem_filter.mpr ⟨hN i, ?_⟩
      have heq := (mem_filter.mp hi).2
      simpa only [heq, inter_comm] using hcommon i
    · intro i hi j hj h
      apply hinj
      exact Prod.ext (((mem_filter.mp hi).2).trans ((mem_filter.mp hj).2).symm) h
  exact hc.trans (overlapping_cliques_count_le D hmult Q)

omit [Fintype V] in
theorem clique_pair_second_count_le [Finite V] (D : Finset (Block V q)) (P N : I → Block V q)
    (hP : ∀ i, P i ∈ D) (hinj : Function.Injective fun i => (P i, N i))
    (hcommon : ∀ i, r ≤ ((P i).val ∩ (N i).val).card)
    (hmult : ∀ e : Block V r, (D.filter fun Q => e.val ⊆ Q.val).card ≤ M)
    (Q : Block V q) : (univ.filter fun i => N i = Q).card ≤ q.choose r * M := by
  apply clique_pair_first_count_le D N P hP _ _ hmult Q
  · intro i j h
    exact hinj (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))
  · intro i
    simpa only [inter_comm] using hcommon i

theorem IsCliqueFamilyBounded.paired_edgeFamily (hqr : r + 1 ≤ q)
    {D : Finset (Block V q)} {θ : ℝ} (hD : IsCliqueFamilyBounded r D θ) (hM : 0 < M)
    (hmult : ∀ e : Block V (r + 1), (D.filter fun Q => e.val ⊆ Q.val).card ≤ M)
    (P N : I → Block V q) (hP : ∀ i, P i ∈ D) (hN : ∀ i, N i ∈ D)
    (hinj : Function.Injective fun i => (P i, N i))
    (hcommon : ∀ i, r + 1 ≤ ((P i).val ∩ (N i).val).card)
    (E : I → Block V (r + 1))
    (hside : (∀ i, (E i).val ⊆ (P i).val) ∨ (∀ i, (E i).val ⊆ (N i).val)) :
    IsEdgeFamilyBounded E (((q.choose (r + 1) * M : ℕ) : ℝ) * θ) := by
  have hC : 0 < q.choose (r + 1) * M := Nat.mul_pos (Nat.choose_pos hqr) hM
  rcases hside with hp | hn
  · exact hD.repeated_edgeFamily hqr P hP hC
      (clique_pair_first_count_le D P N hN hinj hcommon hmult) E hp
  · exact hD.repeated_edgeFamily hqr N hN hC
      (clique_pair_second_count_le D P N hP hinj hcommon hmult) E hn

end Arxiv2411_18291
