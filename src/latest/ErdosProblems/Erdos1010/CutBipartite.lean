import ErdosProblems.Erdos1010.GraphCuts
import ErdosProblems.Erdos1010.Bipartite

/-! # The bipartite representation attached to a vertex cut -/

open Finset

namespace Erdos1010

open Bipartite

variable {V : Type*} [Fintype V] [DecidableEq V]

def missingDegree (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) : ℕ :=
  (S.filter fun w ↦ ¬G.Adj v w).card

def missingCross (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Finset (↥(S : Set V) × ↥((Sᶜ : Finset V) : Set V)) :=
  univ.filter fun e ↦ ¬G.Adj e.1.val e.2.val

def presentCross (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Finset (↥(S : Set V) × ↥((Sᶜ : Finset V) : Set V)) :=
  univ.filter fun e ↦ G.Adj e.1.val e.2.val

lemma card_filter_subtype (S : Finset V) (P : V → Prop) [DecidablePred P] :
    ((univ : Finset (S : Set V)).filter fun v ↦ P v.val).card = (S.filter P).card := by
  apply card_bij (fun v _ ↦ v.val)
  · intro v hv
    exact mem_filter.mpr ⟨v.property, (mem_filter.mp hv).2⟩
  · intro a ha b hb h
    exact Subtype.ext h
  · intro v hv
    obtain ⟨hvS, hvP⟩ := mem_filter.mp hv
    exact ⟨⟨v, hvS⟩, mem_filter.mpr ⟨mem_univ _, hvP⟩, rfl⟩

lemma card_neighbor_filter_subtype (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) :
    ((univ : Finset (S : Set V)).filter fun w ↦ G.Adj v w.val).card = (G.neighborFinset v ∩ S).card := by
  rw [card_filter_subtype]
  congr 1
  ext w
  simp [and_comm]

lemma degree_induce_finset (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : (S : Set V)) :
    (G.induce (S : Set V)).degree v = (G.neighborFinset v.val ∩ S).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have heq : (G.induce (S : Set V)).neighborFinset v = univ.filter (fun w ↦ G.Adj v.val w.val) := by
    ext w
    simp
  rw [heq]
  exact card_neighbor_filter_subtype G S v.val

lemma leftDegree_missingCross (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : (S : Set V)) :
    leftDegree (missingCross G S) v = missingDegree G Sᶜ v.val := by
  rw [← card_right_neighbors]
  simp only [missingCross, mem_filter, mem_univ, true_and]
  exact card_filter_subtype Sᶜ (fun w ↦ ¬G.Adj v.val w)

lemma rightDegree_missingCross (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : ((Sᶜ : Finset V) : Set V)) :
    rightDegree (missingCross G S) v = missingDegree G S v.val := by
  rw [← card_left_neighbors]
  simp only [missingCross, mem_filter, mem_univ, true_and]
  simpa [missingDegree, G.adj_comm] using card_filter_subtype S (fun w ↦ ¬G.Adj w v.val)

lemma missingDegree_add_neighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) : missingDegree G S v + (G.neighborFinset v ∩ S).card = S.card := by
  have h := card_filter_add_card_filter_not (s := S) (fun w ↦ G.Adj v w)
  have heq : S.filter (G.Adj v) = G.neighborFinset v ∩ S := by ext w; simp [and_comm]
  rw [heq] at h
  unfold missingDegree
  omega

lemma crossing_pair_representation (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {p : Finset V} (hp : p ∈ crossingPairs G S) :
    ∃ a b, a ∈ S ∧ b ∉ S ∧ G.Adj a b ∧ p = {a, b} := by
  obtain ⟨hpG, hpI⟩ := mem_filter.mp hp
  obtain ⟨a, ha⟩ := card_eq_one.mp hpI
  have ham : a ∈ p ∩ S := by rw [ha]; simp
  have hap := (mem_inter.mp ham).1
  have haS := (mem_inter.mp ham).2
  have hc := (G.mem_cliqueFinset_iff.mp hpG).card_eq
  obtain ⟨b, hba, hpair⟩ := pair_eq_of_mem hc hap
  have hbS : b ∉ S := by
    intro hb
    have hbp : b ∈ p := by rw [hpair]; simp
    have hbi : b ∈ p ∩ S := mem_inter.mpr ⟨hbp, hb⟩
    rw [ha] at hbi
    exact hba (mem_singleton.mp hbi)
  exact ⟨a, b, haS, hbS, (mem_pair_clique_iff G a b).mp (hpair ▸ hpG), hpair⟩

lemma card_presentCross (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (presentCross G S).card = cutSize G S := by
  apply card_bij (fun e _ ↦ ({e.1.val, e.2.val} : Finset V))
  · intro e he
    have hadj := (mem_filter.mp he).2
    have hleft : e.1.val ∈ S := e.1.property
    have hright : e.2.val ∉ S := mem_compl.mp e.2.property
    apply mem_filter.mpr
    refine ⟨(mem_pair_clique_iff G _ _).mpr hadj, ?_⟩
    have hi : ({e.1.val, e.2.val} : Finset V) ∩ S = {e.1.val} := by
      ext v
      simp only [mem_inter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hv⟩
        · rfl
        · exact (hright hv).elim
      · rintro rfl
        exact ⟨Or.inl rfl, hleft⟩
    rw [hi, card_singleton]
  · intro e he f hf h
    change ({e.1.val, e.2.val} : Finset V) = {f.1.val, f.2.val} at h
    have hleft : e.1.val = f.1.val := by
      have hem : e.1.val ∈ ({f.1.val, f.2.val} : Finset V) := by rw [← h]; simp
      rcases mem_insert.mp hem with h1 | h2
      · exact h1
      · have heq := mem_singleton.mp h2
        exact ((mem_compl.mp f.2.property) (heq ▸ e.1.property)).elim
    have hright : e.2.val = f.2.val := by
      have hem : e.2.val ∈ ({f.1.val, f.2.val} : Finset V) := by rw [← h]; simp
      rcases mem_insert.mp hem with h1 | h2
      · exact ((mem_compl.mp e.2.property) (h1.symm ▸ f.1.property)).elim
      · exact mem_singleton.mp h2
    exact Prod.ext (Subtype.ext hleft) (Subtype.ext hright)
  · intro p hp
    obtain ⟨a, b, ha, hb, hab, hp⟩ := crossing_pair_representation G S hp
    exact ⟨(⟨a, ha⟩, ⟨b, mem_compl.mpr hb⟩), mem_filter.mpr ⟨mem_univ _, hab⟩, hp.symm⟩

lemma cutSize_add_missingCross (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    cutSize G S + (missingCross G S).card = S.card * Sᶜ.card := by
  have h := card_filter_add_card_filter_not
    (s := (univ : Finset (↥(S : Set V) × ↥((Sᶜ : Finset V) : Set V)))) (fun e ↦ G.Adj e.1.val e.2.val)
  change (presentCross G S).card + (missingCross G S).card = _ at h
  rw [card_presentCross] at h
  simpa [Finset.card_compl] using h

lemma maximum_cut_left_cap (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (hmax : IsMaximumCut G S) (a : (S : Set V)) :
    (G.induce (S : Set V)).degree a + leftDegree (missingCross G S) a ≤ Sᶜ.card := by
  rw [degree_induce_finset, leftDegree_missingCross]
  have hlocal := maximum_cut_external_ge_internal G Sᶜ ((isMaximumCut_compl G S).mpr hmax)
    a.val (by simpa using a.property)
  rw [compl_compl] at hlocal
  have hcount := missingDegree_add_neighbors G Sᶜ a.val
  omega

lemma maximum_cut_right_cap (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (hmax : IsMaximumCut G S) (b : ((Sᶜ : Finset V) : Set V)) :
    (G.induce ((Sᶜ : Finset V) : Set V)).degree b + rightDegree (missingCross G S) b ≤ S.card := by
  rw [degree_induce_finset, rightDegree_missingCross]
  have hlocal := maximum_cut_external_ge_internal G S hmax b.val (mem_compl.mp b.property)
  have hcount := missingDegree_add_neighbors G S b.val
  omega

lemma minimum_imbalance_right_cap (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (hmax : IsMaximumCut G S) (hmin : ∀ T, IsMaximumCut G T → cutImbalance S ≤ cutImbalance T)
    (hgap : S.card + 2 ≤ Sᶜ.card) (b : ((Sᶜ : Finset V) : Set V)) :
    (G.induce ((Sᶜ : Finset V) : Set V)).degree b + rightDegree (missingCross G S) b < S.card := by
  rw [degree_induce_finset, rightDegree_missingCross]
  have hlocal := minimum_imbalance_external_gt_internal G S hmax hmin hgap b.val (mem_compl.mp b.property)
  have hcount := missingDegree_add_neighbors G S b.val
  omega

lemma cut_induced_edge_partition (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (G.induce (S : Set V)).edgeFinset.card +
      (G.induce ((Sᶜ : Finset V) : Set V)).edgeFinset.card + cutSize G S = G.edgeFinset.card := by
  have h := cut_partition_edges G S
  rwa [card_internalPairs, card_internalPairs] at h

end Erdos1010
