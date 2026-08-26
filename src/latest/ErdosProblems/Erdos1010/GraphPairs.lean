import ErdosProblems.Erdos1010.PairFamily

/-! # The unordered-pair representation of the edges of a simple graph -/

open Finset

namespace Erdos1010

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma mem_pair_clique_iff (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) :
    {a, b} ∈ G.cliqueFinset 2 ↔ G.Adj a b := by
  by_cases h : a = b
  · subst b
    simp [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff]
  · simp [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.isNClique_iff, h]

lemma pairDegree_cliqueFinset (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    pairDegree (G.cliqueFinset 2) v = G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  symm
  unfold pairDegree
  apply card_bij (fun w _ ↦ ({v, w} : Finset V))
  · intro w hw
    apply mem_filter.mpr
    exact ⟨(mem_pair_clique_iff G v w).mpr (G.mem_neighborFinset v w |>.mp hw), by simp⟩
  · intro w hw u hu h
    have hwv : w ≠ v := (G.mem_neighborFinset v w |>.mp hw).ne.symm
    have hp : w ∈ ({v, u} : Finset V) := by rw [← h]; simp
    simpa [hwv] using hp
  · intro p hp
    obtain ⟨hpc, hv⟩ := mem_filter.mp hp
    have hc := (G.mem_cliqueFinset_iff.mp hpc).card_eq
    have herase : (p.erase v).card = 1 := by rw [card_erase_of_mem hv, hc]
    obtain ⟨w, hw⟩ := card_eq_one.mp herase
    have hpw : p = {v, w} := by rw [← hw, insert_erase hv]
    refine ⟨w, ?_, hpw.symm⟩
    apply G.mem_neighborFinset v w |>.mpr
    apply (mem_pair_clique_iff G v w).mp
    rwa [← hpw]

lemma pairCharge_cliqueFinset_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℤ) : pairCharge (G.cliqueFinset 2) w = ∑ v, (G.degree v : ℤ) * w v := by
  rw [pairCharge_eq_sum_degree univ _ _ (fun _ _ ↦ subset_univ _)]
  simp only [pairDegree_cliqueFinset]

lemma card_cliqueFinset_two (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.cliqueFinset 2).card = G.edgeFinset.card := by
  have hsum := pairCharge_cliqueFinset_eq G (fun _ ↦ 1)
  have hleft : pairCharge (G.cliqueFinset 2) (fun _ ↦ (1 : ℤ)) =
      2 * (G.cliqueFinset 2).card := by
    unfold pairCharge
    calc
      _ = ∑ _ ∈ G.cliqueFinset 2, (2 : ℤ) := by
        apply sum_congr rfl
        intro p hp
        simp [(G.mem_cliqueFinset_iff.mp hp).card_eq]
      _ = _ := by simp [mul_comm]
  have hdegree : (∑ v, (G.degree v : ℤ)) = 2 * (G.edgeFinset.card : ℤ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  rw [hleft] at hsum
  simp only [mul_one] at hsum
  have : ((G.cliqueFinset 2).card : ℤ) = G.edgeFinset.card := by omega
  exact_mod_cast this

lemma graph_weighted_degree_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℤ) (k : ℤ) :
    (∑ v, (G.degree v : ℤ) * w v) ≤ k * G.edgeFinset.card + pairExcess univ w k := by
  rw [← pairCharge_cliqueFinset_eq G]
  have hsub : G.cliqueFinset 2 ⊆ (univ : Finset V).powersetCard 2 := by
    intro p hp
    exact mem_powersetCard.mpr ⟨subset_univ _, (G.mem_cliqueFinset_iff.mp hp).card_eq⟩
  simpa [card_cliqueFinset_two] using pairCharge_le_baseline univ (G.cliqueFinset 2) w k hsub

lemma indicator_pairExcess (s : Finset V) :
    pairExcess univ (fun v ↦ if v ∈ s then (1 : ℤ) else 0) 1 = s.card.choose 2 := by
  rw [pairExcess_restrict univ s _ 1 (subset_univ _) (by
    intro a ha b hb has
    simp only [if_neg has, zero_add]
    split_ifs <;> omega)]
  unfold pairExcess
  calc
    _ = ∑ _p ∈ s.powersetCard 2, (1 : ℤ) := by
      apply sum_congr rfl
      intro p hp
      obtain ⟨hps, hc⟩ := mem_powersetCard.mp hp
      have hs : (∑ v ∈ p, if v ∈ s then (1 : ℤ) else 0) = 2 := by
        simp only [sum_congr rfl (fun v hv ↦ if_pos (hps hv)), sum_const,
          nsmul_eq_mul, mul_one, hc, Nat.cast_ofNat]
      rw [hs]
      norm_num
    _ = _ := by simp [card_powersetCard]

/-- A leaf set contributes at most one per edge, plus its internal pairs. -/
lemma degree_sum_subset_le_edges_add_pairs (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) : (∑ v ∈ s, (G.degree v : ℤ)) ≤
      G.edgeFinset.card + (s.card.choose 2 : ℤ) := by
  have h := graph_weighted_degree_le G (fun v ↦ if v ∈ s then (1 : ℤ) else 0) 1
  rw [indicator_pairExcess] at h
  simpa [mul_ite] using h

lemma degree_sum_subset_le_twice_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) : (∑ v ∈ s, (G.degree v : ℤ)) ≤ 2 * G.edgeFinset.card := by
  have h : (∑ v ∈ s, (G.degree v : ℤ)) ≤ ∑ v, (G.degree v : ℤ) :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ ↦ Nat.cast_nonneg _)
  have hd : (∑ v, (G.degree v : ℤ)) = 2 * G.edgeFinset.card := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  rwa [hd] at h

lemma graph_weighted_degree_hub_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℤ) (k c : ℤ) (u : V) :
    (∑ v, (G.degree v : ℤ) * w v) ≤ k * G.edgeFinset.card + c * G.degree u +
      pairExcess univ (fun v ↦ w v - if v = u then c else 0) k := by
  rw [← pairCharge_cliqueFinset_eq G]
  have hsub : G.cliqueFinset 2 ⊆ (univ : Finset V).powersetCard 2 := by
    intro p hp
    exact mem_powersetCard.mpr ⟨subset_univ _, (G.mem_cliqueFinset_iff.mp hp).card_eq⟩
  simpa [card_cliqueFinset_two, pairDegree_cliqueFinset] using
    pairCharge_le_hub_baseline univ (G.cliqueFinset 2) w k c u hsub

lemma graph_weighted_degree_hub_sum_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℤ) (k l h : ℤ) (u : V) (hu : w u = k)
    (hw : ∀ v, v ≠ u → 0 ≤ w v) (hs : ∑ v ∈ univ.erase u, w v = h) (hh : h ≤ l) :
    (∑ v, (G.degree v : ℤ) * w v) ≤ l * G.edgeFinset.card +
      (k - l) * G.degree u + h := by
  let z : V → ℤ := fun v ↦ w v - if v = u then k - l else 0
  have hz : z u = l := by simp [z, hu]
  have hrest : ∀ v ∈ univ.erase u, z v = w v := by
    intro v hv
    simp [z, ne_of_mem_erase hv]
  have hsz : ∑ v ∈ univ.erase u, z v = h := by
    simpa only [sum_congr rfl hrest] using hs
  have he := pairExcess_hub univ z l u (mem_univ _) hz
    (fun v hv ↦ by rw [hrest v hv]; exact hw v (ne_of_mem_erase hv)) (by omega)
  have hc := graph_weighted_degree_hub_le G w l (k - l) u
  change (∑ v, (G.degree v : ℤ) * w v) ≤ _ + pairExcess univ z l at hc
  rwa [he, hsz] at hc

lemma graph_weighted_degree_hub_unit_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℤ) (k l h : ℤ) (u : V) (hu : w u = k) (hl : 2 ≤ l)
    (hw : ∀ v, v ≠ u → 0 ≤ w v ∧ w v ≤ 1) (hs : ∑ v ∈ univ.erase u, w v = h) :
    (∑ v, (G.degree v : ℤ) * w v) ≤ l * G.edgeFinset.card +
      (k - l) * G.degree u + h := by
  let z : V → ℤ := fun v ↦ w v - if v = u then k - l else 0
  have hz : z u = l := by simp [z, hu]
  have hrest : ∀ v ∈ univ.erase u, z v = w v := by
    intro v hv
    simp [z, ne_of_mem_erase hv]
  have hsz : ∑ v ∈ univ.erase u, z v = h := by
    simpa only [sum_congr rfl hrest] using hs
  have he := pairExcess_hub_unit_weights univ z l u (mem_univ _) hl hz
    (fun v hv ↦ by rw [hrest v hv]; exact hw v (ne_of_mem_erase hv))
  have hc := graph_weighted_degree_hub_le G w l (k - l) u
  change (∑ v, (G.degree v : ℤ) * w v) ≤ _ + pairExcess univ z l at hc
  rwa [he, hsz] at hc

end Erdos1010
