import Arxiv.Arxiv2411_18291.GeneratorSplitting

/-!
# Multiplicities after splitting generators

Splitting does not increase multiplicities on the original support. Every
edge outside that support occurs in at most two replacement cliques, and
each replacement clique has at most one edge in the original support.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
variable {q r : ℕ} {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)} {θ : ℝ}

theorem GeneratorSplitting.copy_count_original (F : GeneratorSplitting S D θ)
    (Q : D) (e : Block V (r + 1)) (heD : e ∈ cliqueSupport (r + 1) D) :
    ((S.map (F.embedding Q)).replacementCliques.filter fun P => e.val ⊆ P.val).card ≤
      if e.val ⊆ Q.val.val then 1 else 0 := by
  by_cases heQ : e.val ⊆ Q.val.val
  · rw [if_pos heQ]
    apply (S.map (F.embedding Q)).replacement_count_le_one_of_base
    change e ∈ cliqueEdges (r + 1) (mapBlock (F.embedding Q) S.base)
    rw [F.base Q]
    exact (mem_cliqueEdges _ _).mpr heQ
  · rw [if_neg heQ]
    apply Nat.le_zero.mpr
    rw [card_eq_zero]
    apply eq_empty_iff_forall_notMem.mpr
    intro P hP
    obtain ⟨hP, heP⟩ := mem_filter.mp hP
    rw [S.replacementCliques_map] at hP
    obtain ⟨P₀, hP₀, rfl⟩ := (mem_mapGraph _ _ _).mp hP
    have hinter := mem_inter.mpr ⟨(mem_cliqueEdges _ _).mpr heP, heD⟩
    rw [F.copy_clique_inter Q P₀ (S.replacement_clique_subset hP₀), mapGraph_inter,
      map_cliqueEdges, map_cliqueEdges, F.base Q] at hinter
    exact heQ ((mem_cliqueEdges _ _).mp (mem_inter.mp hinter).2)

theorem GeneratorSplitting.clique_count_original (F : GeneratorSplitting S D θ)
    (e : Block V (r + 1)) (heD : e ∈ cliqueSupport (r + 1) D) :
    (F.cliques.filter fun P => e.val ⊆ P.val).card ≤
      (D.filter fun Q => e.val ⊆ Q.val).card := by
  rw [cliques, filter_biUnion]
  calc
    _ ≤ ∑ Q : D,
        ((S.map (F.embedding Q)).replacementCliques.filter fun P => e.val ⊆ P.val).card :=
      card_biUnion_le
    _ ≤ ∑ Q : D, if e.val ⊆ Q.val.val then 1 else 0 :=
      sum_le_sum fun Q _ => F.copy_count_original Q e heD
    _ = _ := by
      rw [Finset.sum_coe_sort D (fun Q => if e.val ⊆ Q.val then 1 else 0), ← sum_filter]
      simp only [sum_const, nsmul_eq_mul, Nat.cast_id, mul_one]

theorem GeneratorSplitting.clique_count_outside (F : GeneratorSplitting S D θ)
    (e : Block V (r + 1)) (heD : e ∉ cliqueSupport (r + 1) D) :
    (F.cliques.filter fun P => e.val ⊆ P.val).card ≤ 2 := by
  by_cases hex : ∃ P ∈ F.cliques, e.val ⊆ P.val
  · obtain ⟨P, hP, heP⟩ := hex
    obtain ⟨Q, _, hQ⟩ := mem_biUnion.mp hP
    have heQ : e ∈ mapGraph (F.embedding Q) S.graph :=
      (S.map (F.embedding Q)).replacement_clique_subset hQ ((mem_cliqueEdges _ _).mpr heP)
    apply (card_le_card (show F.cliques.filter (fun P => e.val ⊆ P.val) ⊆
        (S.map (F.embedding Q)).replacementCliques.filter (fun P => e.val ⊆ P.val) from ?_)).trans
      ((S.map (F.embedding Q)).replacement_count_le_two e)
    intro R hR
    obtain ⟨hR, heR⟩ := mem_filter.mp hR
    obtain ⟨Q', _, hQ'⟩ := mem_biUnion.mp hR
    have heQ' : e ∈ mapGraph (F.embedding Q') S.graph :=
      (S.map (F.embedding Q')).replacement_clique_subset hQ' ((mem_cliqueEdges _ _).mpr heR)
    have hQQ' := F.copy_index_unique heQ heQ' heD
    subst Q'
    exact mem_filter.mpr ⟨hQ', heR⟩
  · have hz : F.cliques.filter (fun P => e.val ⊆ P.val) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro P hP
      exact hex ⟨P, (mem_filter.mp hP).1, (mem_filter.mp hP).2⟩
    rw [hz, card_empty]
    omega

theorem GeneratorSplitting.clique_inter_card_le_one (F : GeneratorSplitting S D θ)
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    {P : Block V q} (hP : P ∈ F.cliques) :
    (cliqueEdges (r + 1) P ∩ cliqueSupport (r + 1) D).card ≤ 1 := by
  obtain ⟨Q, _, hQ⟩ := mem_biUnion.mp hP
  rw [S.replacementCliques_map] at hQ
  obtain ⟨P₀, hP₀, rfl⟩ := (mem_mapGraph _ _ _).mp hQ
  rw [F.copy_clique_inter Q P₀ (S.replacement_clique_subset hP₀), card_mapGraph]
  by_cases hnear : P₀ ∈ S.nearCliques
  · rw [hA.nearRoot_inter (Nat.succ_pos r) ⟨P₀, hnear⟩, card_singleton]
  · rw [disjoint_iff_inter_eq_empty.mp (S.far_disjoint_base (mem_sdiff.mpr ⟨hP₀, hnear⟩)),
      card_empty]
    omega

end Arxiv2411_18291
