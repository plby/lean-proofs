import Arxiv.Arxiv2411_18291.EliminationSupport

/-!
# Uniform multiplicity bounds for elimination families

Only copies whose roots contain an old edge can contribute to it.
Distinct root pairs have bounded repetition in each coordinate. Combining
these observations with the two-clique bound inside each copy gives a
uniform multiplicity bound for both signs and their boundary multigraph.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {I : Type*} [Fintype I] {q r M : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {N : Block W q} {e₀ : Block W (r + 1)}
variable {B : Hypergraph V (r + 1)} {P Q : I → Block V q} {θ : ℝ}

theorem EliminationFamily.copy_count_original (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (i : I) (e : Block V (r + 1)) (heB : e ∈ B) :
    ((mapGraph (F.embedding i) (S.eliminationCliques N)).filter fun R => e.val ⊆ R.val).card ≤
      2 * ((if e.val ⊆ (P i).val then 1 else 0) + (if e.val ⊆ (Q i).val then 1 else 0)) := by
  by_cases heP : e.val ⊆ (P i).val
  · rw [if_pos heP]
    exact (F.copy_count_le_two i e).trans (by omega)
  · by_cases heQ : e.val ⊆ (Q i).val
    · rw [if_pos heQ]
      exact (F.copy_count_le_two i e).trans (by omega)
    · rw [if_neg heP, if_neg heQ]
      simp only [add_zero, mul_zero, Nat.le_zero, card_eq_zero]
      apply eq_empty_iff_forall_notMem.mpr
      intro R hR
      obtain ⟨hR, heR⟩ := mem_filter.mp hR
      have heRoot : e ∈ cliqueEdges (r + 1) (P i) ∪ cliqueEdges (r + 1) (Q i) := by
        rw [← F.copy_inter_original hpair i]
        exact mem_inter.mpr ⟨F.clique_copy_graph i hR ((mem_cliqueEdges _ _).mpr heR), heB⟩
      rcases mem_union.mp heRoot with hp | hq
      · exact heP ((mem_cliqueEdges _ _).mp hp)
      · exact heQ ((mem_cliqueEdges _ _).mp hq)

theorem EliminationFamily.clique_count_original (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (D : Finset (Block V q))
    (hP : ∀ i, P i ∈ D) (hQ : ∀ i, Q i ∈ D)
    (hinj : Function.Injective fun i => (P i, Q i))
    (hcommon : ∀ i, r + 1 ≤ ((P i).val ∩ (Q i).val).card)
    (hmult : ∀ e : Block V (r + 1), (D.filter fun R => e.val ⊆ R.val).card ≤ M)
    (e : Block V (r + 1)) (heB : e ∈ B) :
    (F.cliques.filter fun R => e.val ⊆ R.val).card ≤ 4 * q.choose (r + 1) * M ^ 2 := by
  have hsum (R : I → Block V q) :
      (∑ i, if e.val ⊆ (R i).val then (1 : ℕ) else 0) = familyDegree R e.val := by
    rw [familyDegree, ← sum_filter]
    simp only [sum_const, nsmul_eq_mul, Nat.cast_id, mul_one]
  have hPc : familyDegree P e.val ≤ (q.choose (r + 1) * M) * M :=
    (repeated_clique_degree_le D P hP
      (clique_pair_first_count_le D P Q hQ hinj hcommon hmult) e.val).trans
      (Nat.mul_le_mul_left _ (hmult e))
  have hQc : familyDegree Q e.val ≤ (q.choose (r + 1) * M) * M :=
    (repeated_clique_degree_le D Q hQ
      (clique_pair_second_count_le D P Q hP hinj hcommon hmult) e.val).trans
      (Nat.mul_le_mul_left _ (hmult e))
  rw [cliques, filter_biUnion]
  calc
    _ ≤ ∑ i, ((mapGraph (F.embedding i) (S.eliminationCliques N)).filter
        fun R => e.val ⊆ R.val).card := card_biUnion_le
    _ ≤ ∑ i, 2 * ((if e.val ⊆ (P i).val then 1 else 0) +
        (if e.val ⊆ (Q i).val then 1 else 0)) :=
      sum_le_sum fun i _ => F.copy_count_original hpair i e heB
    _ = 2 * (familyDegree P e.val + familyDegree Q e.val) := by
      rw [← mul_sum, sum_add_distrib, hsum P, hsum Q]
    _ ≤ 2 * ((q.choose (r + 1) * M) * M + (q.choose (r + 1) * M) * M) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add hPc hQc)
    _ = _ := by ring

theorem EliminationFamily.clique_multiplicity (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (D : Finset (Block V q))
    (hP : ∀ i, P i ∈ D) (hQ : ∀ i, Q i ∈ D)
    (hinj : Function.Injective fun i => (P i, Q i))
    (hcommon : ∀ i, r + 1 ≤ ((P i).val ∩ (Q i).val).card)
    (hmult : ∀ e : Block V (r + 1), (D.filter fun R => e.val ⊆ R.val).card ≤ M)
    (e : Block V (r + 1)) :
    (F.cliques.filter fun R => e.val ⊆ R.val).card ≤ 4 * q.choose (r + 1) * M ^ 2 + 2 := by
  by_cases heB : e ∈ B
  · exact (F.clique_count_original hpair D hP hQ hinj hcommon hmult e heB).trans
      (Nat.le_add_right _ _)
  · exact (F.clique_count_outside hpair e heB).trans (Nat.le_add_left _ _)

theorem EliminationFamily.cliques_bounded (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (D : Finset (Block V q))
    (hP : ∀ i, P i ∈ D) (hQ : ∀ i, Q i ∈ D)
    (hinj : Function.Injective fun i => (P i, Q i))
    (hcommon : ∀ i, r + 1 ≤ ((P i).val ∩ (Q i).val).card)
    (hmult : ∀ e : Block V (r + 1), (D.filter fun R => e.val ⊆ R.val).card ≤ M) :
    IsCliqueFamilyBounded r F.cliques (((4 * q.choose (r + 1) * M ^ 2 + 2 : ℕ) : ℝ) * θ) :=
  F.bounded.cliqueFamilyBounded F.cliques (by omega)
    (F.clique_multiplicity hpair D hP hQ hinj hcommon hmult) (F.cliques_support hpair)

theorem EliminationFamily.union_cliques_support (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (D : Finset (Block V q))
    (hsupport : cliqueSupport (r + 1) D ⊆ B) :
    cliqueSupport (r + 1) (D ∪ F.cliques) ⊆ F.graph := by
  intro e he
  obtain ⟨R, hR, heR⟩ := mem_biUnion.mp he
  rcases mem_union.mp hR with hd | hf
  · exact mem_union_left _ (hsupport (mem_biUnion.mpr ⟨R, hd, heR⟩))
  · exact F.cliques_support hpair (mem_biUnion.mpr ⟨R, hf, heR⟩)

theorem EliminationFamily.union_cliques_multiplicity (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (D : Finset (Block V q))
    (hP : ∀ i, P i ∈ D) (hQ : ∀ i, Q i ∈ D)
    (hinj : Function.Injective fun i => (P i, Q i))
    (hcommon : ∀ i, r + 1 ≤ ((P i).val ∩ (Q i).val).card)
    (hmult : ∀ e : Block V (r + 1), (D.filter fun R => e.val ⊆ R.val).card ≤ M)
    (e : Block V (r + 1)) :
    ((D ∪ F.cliques).filter fun R => e.val ⊆ R.val).card ≤
      M + 4 * q.choose (r + 1) * M ^ 2 + 2 := by
  rw [filter_union]
  have hF := F.clique_multiplicity hpair D hP hQ hinj hcommon hmult e
  exact (card_union_le _ _).trans (by have hD := hmult e; omega)

theorem EliminationFamily.union_cliques_bounded (F : EliminationFamily S N B P Q θ)
    (hpair : IsEliminationPair S N e₀) (D : Finset (Block V q))
    (hsupport : cliqueSupport (r + 1) D ⊆ B)
    (hP : ∀ i, P i ∈ D) (hQ : ∀ i, Q i ∈ D)
    (hinj : Function.Injective fun i => (P i, Q i))
    (hcommon : ∀ i, r + 1 ≤ ((P i).val ∩ (Q i).val).card)
    (hmult : ∀ e : Block V (r + 1), (D.filter fun R => e.val ⊆ R.val).card ≤ M) :
    IsCliqueFamilyBounded r (D ∪ F.cliques)
      (((M + 4 * q.choose (r + 1) * M ^ 2 + 2 : ℕ) : ℝ) * θ) :=
  F.bounded.cliqueFamilyBounded (D ∪ F.cliques) (by omega)
    (F.union_cliques_multiplicity hpair D hP hQ hinj hcommon hmult)
    (F.union_cliques_support hpair D hsupport)

end Arxiv2411_18291
