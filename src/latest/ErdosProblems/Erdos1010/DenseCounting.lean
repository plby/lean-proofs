import ErdosProblems.Erdos1010.CutBipartite
import ErdosProblems.Erdos1010.LeafSupports

/-! # Finite counting for the dense odd reduction -/

open Finset

namespace Erdos1010

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma edges_add_compl_edges (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeFinset.card + Gᶜ.edgeFinset.card = (Fintype.card V).choose 2 := by
  have hd : Disjoint G.edgeFinset Gᶜ.edgeFinset := SimpleGraph.disjoint_edgeFinset.mpr disjoint_compl_right
  have hu : G.edgeFinset ∪ Gᶜ.edgeFinset = (⊤ : SimpleGraph V).edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      by_cases hab : G.Adj a b
      · simp [hab, hab.ne]
      · simp [hab, SimpleGraph.compl_adj]
  rw [← card_union_of_disjoint hd, hu]
  exact SimpleGraph.card_edgeFinset_top_eq_card_choose_two

lemma twice_choose_succ_two (D : ℕ) : 2 * (D + 1).choose 2 = D * (D + 1) := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [show D.succ + 1 = (D + 1).succ by omega, Nat.choose_succ_succ]
    simp only [Nat.choose_one_right]
    nlinarith

lemma choose_add_two (D : ℕ) : (D + 2).choose 2 = (D + 1).choose 2 + D + 1 := by
  rw [show D + 2 = (D + 1).succ by omega, Nat.choose_succ_succ]
  simp [Nat.choose_one_right, add_comm, add_left_comm, add_assoc]

def antiNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  (insert v (G.neighborFinset v))ᶜ

lemma mem_antiNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (v x : V) :
    x ∈ antiNeighbors G v ↔ x ≠ v ∧ ¬G.Adj v x := by
  simp [antiNeighbors]

lemma compl_neighborFinset (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Gᶜ.neighborFinset v = antiNeighbors G v := by
  ext x
  simp [mem_antiNeighbors, SimpleGraph.compl_adj, ne_comm]

lemma card_antiNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (antiNeighbors G v).card = Fintype.card V - 1 - G.degree v := by
  rw [← compl_neighborFinset, SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.degree_compl]

lemma compl_antiNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (antiNeighbors G v)ᶜ = insert v (G.neighborFinset v) := by simp [antiNeighbors]

lemma degree_induce_finset_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : (S : Set V)) : (G.induce (S : Set V)).degree v ≤ G.degree v.val := by
  rw [degree_induce_finset, ← SimpleGraph.card_neighborFinset_eq_degree]
  exact card_le_card inter_subset_left

lemma saturated_induce_neighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : (S : Set V)) (D : ℕ)
    (hcap : G.degree v.val ≤ D) (hd : (G.induce (S : Set V)).degree v = D) :
    G.degree v.val = D ∧ G.neighborFinset v.val ⊆ S := by
  have hle := degree_induce_finset_le G S v
  have hdeg : G.degree v.val = D := by omega
  refine ⟨hdeg, ?_⟩
  have heq : G.neighborFinset v.val ∩ S = G.neighborFinset v.val := by
    apply eq_of_subset_of_card_le inter_subset_left
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg, ← degree_induce_finset G S v, hd]
  exact inter_eq_left.mp heq

lemma rightDegree_presentCross (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : ((Sᶜ : Finset V) : Set V)) :
    Bipartite.rightDegree (presentCross G S) v = (G.neighborFinset v.val ∩ S).card := by
  rw [← Bipartite.card_left_neighbors]
  simp only [presentCross, mem_filter, mem_univ, true_and]
  simpa [G.adj_comm] using card_neighbor_filter_subtype G S v.val

lemma sum_external_neighbors (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (∑ v ∈ Sᶜ, (G.neighborFinset v ∩ S).card) = cutSize G S := by
  have h := Bipartite.sum_rightDegree_univ (presentCross G S)
  simp only [rightDegree_presentCross, card_presentCross] at h
  change (∑ v : (Sᶜ : Finset V), (G.neighborFinset v.val ∩ S).card) = cutSize G S at h
  exact (Finset.sum_coe_sort (s := Sᶜ) (f := fun v : V ↦ (G.neighborFinset v ∩ S).card)).symm.trans h

lemma selected_external_neighbors_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V) (hT : T ⊆ Sᶜ) (D : ℕ) (hcap : ∀ v ∈ S, G.degree v ≤ D) :
    (∑ v ∈ T, (G.neighborFinset v ∩ S).card) + 2 * (internalPairs G S).card ≤ S.card * D := by
  have hcross : (∑ v ∈ T, (G.neighborFinset v ∩ S).card) ≤ cutSize G S := by
    rw [← sum_external_neighbors]
    exact sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ ↦ Nat.zero_le _)
  have hdeg : (∑ v ∈ S, G.degree v) ≤ S.card * D := by
    calc
      _ ≤ ∑ _v ∈ S, D := sum_le_sum hcap
      _ = _ := by simp
  have hcut := cut_degree_sum G S
  have hcutN : cutSize G S + 2 * (internalPairs G S).card = ∑ v ∈ S, G.degree v := by
    exact_mod_cast hcut
  omega

lemma leaf_complement_induce_anti (F : SimpleGraph V) [DecidableRel F.Adj]
    (S : Finset V) (D : ℕ) (hS : S.card = D + 2) (hcap : ∀ v, F.degree v ≤ D)
    (u w : (S : Set V)) (hu : (F.induce (S : Set V))ᶜ.degree u = 1)
    (huw : (F.induce (S : Set V))ᶜ.Adj u w) :
    F.degree u.val = D ∧ antiNeighbors F u.val = Sᶜ ∪ {w.val} := by
  let H := (F.induce (S : Set V))ᶜ
  have hcard : Fintype.card (S : Set V) = D + 2 := by simpa using hS
  have hdegH := SimpleGraph.degree_compl (G := F.induce (S : Set V)) (v := u)
  have hdegF : (F.induce (S : Set V)).degree u = D := by
    have hle := (degree_induce_finset_le F S u).trans (hcap u.val)
    rw [hcard] at hdegH
    omega
  obtain ⟨hdu, hNu⟩ := saturated_induce_neighbors F S u D (hcap u.val) hdegF
  refine ⟨hdu, ?_⟩
  ext x
  by_cases hxS : x ∈ S
  · let z : (S : Set V) := ⟨x, hxS⟩
    have hleaf := adj_iff_eq_of_degree_one H u w hu huw z
    have hiff : (u.val ≠ x ∧ ¬F.Adj u.val x) ↔ x = w.val := by
      simpa [H, z, SimpleGraph.compl_adj, SimpleGraph.induce_adj, Subtype.ext_iff] using hleaf
    simp only [mem_antiNeighbors, mem_union, mem_compl, mem_singleton, hxS, not_true_eq_false, false_or]
    simpa [ne_comm] using hiff
  · have hxu : x ≠ u.val := by intro h; exact hxS (h ▸ u.property)
    have hnot : ¬F.Adj u.val x := by
      intro h
      exact hxS (hNu ((F.mem_neighborFinset u.val x).mpr h))
    simp [mem_antiNeighbors, hxu, hnot, hxS]

lemma internalPairs_neighborhood_insert_two (F : SimpleGraph V) [DecidableRel F.Adj]
    (v w : V) (hwv : w ≠ v) (hvw : ¬F.Adj v w) :
    (internalPairs F (insert w (insert v (F.neighborFinset v)))).card =
      (internalPairs F (F.neighborFinset v)).card + F.degree v +
        (F.neighborFinset w ∩ F.neighborFinset v).card := by
  have hvN : v ∉ F.neighborFinset v := by simp
  have hwN : w ∉ insert v (F.neighborFinset v) := by simp [hwv, hvw]
  rw [card_internalPairs_insert F _ w hwN, card_internalPairs_insert F _ v hvN]
  have heq : F.neighborFinset w ∩ insert v (F.neighborFinset v) =
      F.neighborFinset w ∩ F.neighborFinset v := by
    ext x
    simp only [mem_inter, mem_insert, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hwx, rfl | hvx⟩
      · exact (hvw hwx.symm).elim
      · exact ⟨hwx, hvx⟩
    · exact fun h ↦ ⟨h.1, Or.inr h.2⟩
  rw [heq, inter_self, SimpleGraph.card_neighborFinset_eq_degree]

lemma internalPairs_add_compl (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (internalPairs G S).card + (internalPairs Gᶜ S).card = S.card.choose 2 := by
  have hEdges : ((G.induce (S : Set V))ᶜ).edgeFinset = (Gᶜ.induce (S : Set V)).edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.compl_adj, SimpleGraph.induce_adj]
      constructor
      · rintro ⟨hne, hnot⟩
        exact ⟨fun h ↦ hne (Subtype.ext h), hnot⟩
      · rintro ⟨hne, hnot⟩
        exact ⟨fun h ↦ hne (congrArg Subtype.val h), hnot⟩
  have h := edges_add_compl_edges (G.induce (S : Set V))
  rw [hEdges] at h
  have hcard : Fintype.card (S : Set V) = S.card := Fintype.card_coe S
  rw [hcard] at h
  rw [card_internalPairs, card_internalPairs]
  exact h

end Erdos1010
