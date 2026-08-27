import Arxiv.Arxiv2411_18291.VariableSplittingPartners
import Arxiv.Arxiv2411_18291.SplittingMultiplicity

/-! # Splitting multiplicities controlled by actual root capacities

Old edges are counted using the sum of capacities on roots containing them.
Every other edge is in at most two replacement cliques. No maximum capacity
or uniform multiplicity bound is introduced.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r : ℕ} {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {C : Block V q → ℕ} {θ : ℝ}

def VariableSplittingFamily.graph (F : VariableSplittingFamily S D B C θ) :
    Hypergraph V (r + 1) :=
  B ∪ univ.biUnion fun s => mapGraph (F.embedding s) (newEdges S.base.val S.graph)

def VariableSplittingFamily.cliques (F : VariableSplittingFamily S D B C θ) : Finset (Block V q) :=
  exchangeSupport fun s => S.map (F.embedding s)

theorem VariableSplittingFamily.cliques_eq_signs (F : VariableSplittingFamily S D B C θ) :
    F.cliques = F.positiveCliques ∪ F.negativeCliques := by
  have hparts (T : ExchangeSystem V q (r + 1)) (b : Bool) :
      T.replacementCliques = T.positiveReplacement b ∪ T.negativeReplacement b := by
    cases b
    · exact union_comm _ _
    · rfl
  unfold cliques exchangeSupport positiveCliques negativeCliques
  rw [← biUnion_union]
  apply congrArg (fun f : VariableCliqueSlots D C → Finset (Block V q) => univ.biUnion f)
  funext s
  exact hparts _ s.2.1

theorem VariableSplittingFamily.copy_count_original (F : VariableSplittingFamily S D B C θ)
    (s : VariableCliqueSlots D C) (e : Block V (r + 1)) (heB : e ∈ B) :
    ((S.map (F.embedding s)).replacementCliques.filter fun Q => e.val ⊆ Q.val).card ≤
      if e.val ⊆ s.1.val.val then 1 else 0 := by
  by_cases heRoot : e.val ⊆ s.1.val.val
  · rw [if_pos heRoot]
    apply (S.map (F.embedding s)).replacement_count_le_one_of_base
    change e ∈ cliqueEdges (r + 1) (mapBlock (F.embedding s) S.base)
    rw [F.base s]
    exact (mem_cliqueEdges _ _).mpr heRoot
  · rw [if_neg heRoot]
    apply Nat.le_zero.mpr
    rw [card_eq_zero]
    apply eq_empty_iff_forall_notMem.mpr
    intro Q hQ
    obtain ⟨hQR, heQ⟩ := mem_filter.mp hQ
    rw [S.replacementCliques_map] at hQR
    obtain ⟨Q₀, hQ₀, rfl⟩ := (mem_mapGraph _ _ _).mp hQR
    have heI := mem_inter.mpr ⟨(mem_cliqueEdges _ _).mpr heQ, heB⟩
    rw [F.copy_clique_inter s Q₀ (S.replacement_clique_subset hQ₀)] at heI
    have hroot := (mem_cliqueEdges _ _).mp (mem_inter.mp heI).2
    rw [F.base s] at hroot
    exact heRoot hroot

theorem VariableSplittingFamily.clique_count_original (F : VariableSplittingFamily S D B C θ)
    (e : Block V (r + 1)) (heB : e ∈ B) :
    (F.cliques.filter fun Q => e.val ⊆ Q.val).card ≤
      2 * cliqueCapacityDegree D C e.val := by
  rw [cliques, exchangeSupport, filter_biUnion]
  calc
    _ ≤ ∑ s : VariableCliqueSlots D C,
        ((S.map (F.embedding s)).replacementCliques.filter fun Q => e.val ⊆ Q.val).card :=
      card_biUnion_le
    _ ≤ ∑ s : VariableCliqueSlots D C, if e.val ⊆ s.1.val.val then 1 else 0 :=
      sum_le_sum fun s _ => F.copy_count_original s e heB
    _ = familyDegree (fun s : VariableCliqueSlots D C => s.1.val) e.val := by
      rw [familyDegree, ← sum_filter]
      simp only [sum_const, nsmul_eq_mul, Nat.cast_id, mul_one]
    _ = _ := variableCliqueSlots_degree D C e.val

theorem VariableSplittingFamily.clique_count_outside (F : VariableSplittingFamily S D B C θ)
    (e : Block V (r + 1)) (heB : e ∉ B) :
    (F.cliques.filter fun Q => e.val ⊆ Q.val).card ≤ 2 := by
  by_cases hex : ∃ Q ∈ F.cliques, e.val ⊆ Q.val
  · obtain ⟨Q, hQ, heQ⟩ := hex
    obtain ⟨s, _, hs⟩ := mem_biUnion.mp hQ
    have hes : e ∈ mapGraph (F.embedding s) S.graph :=
      (S.map (F.embedding s)).replacement_clique_subset hs ((mem_cliqueEdges _ _).mpr heQ)
    apply (card_le_card (show F.cliques.filter (fun Q => e.val ⊆ Q.val) ⊆
        (S.map (F.embedding s)).replacementCliques.filter (fun Q => e.val ⊆ Q.val) from ?_)).trans
      ((S.map (F.embedding s)).replacement_count_le_two e)
    intro R hR
    obtain ⟨hR, heR⟩ := mem_filter.mp hR
    obtain ⟨t, _, ht⟩ := mem_biUnion.mp hR
    have het : e ∈ mapGraph (F.embedding t) S.graph :=
      (S.map (F.embedding t)).replacement_clique_subset ht ((mem_cliqueEdges _ _).mpr heR)
    have hst := F.copy_index_unique hes het heB
    subst t
    exact mem_filter.mpr ⟨ht, heR⟩
  · have hzero : F.cliques.filter (fun Q => e.val ⊆ Q.val) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro Q hQ
      exact hex ⟨Q, (mem_filter.mp hQ).1, (mem_filter.mp hQ).2⟩
    rw [hzero, card_empty]
    omega

theorem VariableSplittingFamily.cliques_support (F : VariableSplittingFamily S D B C θ) :
    cliqueSupport (r + 1) F.cliques ⊆
      B ∪ univ.biUnion (fun s => mapGraph (F.embedding s) (newEdges S.base.val S.graph)) := by
  intro e he
  obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.mp he
  obtain ⟨s, _, hs⟩ := mem_biUnion.mp hQ
  by_cases heB : e ∈ B
  · exact mem_union_left _ heB
  · refine mem_union_right _ (mem_biUnion.mpr ⟨s, mem_univ _, ?_⟩)
    exact F.copy_new_of_notMem s e ((S.map (F.embedding s)).replacement_clique_subset hs heQ) heB

end Arxiv2411_18291
