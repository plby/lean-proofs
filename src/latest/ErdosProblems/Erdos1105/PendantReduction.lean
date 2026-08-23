import ErdosProblems.Erdos1105.PendantSwap

namespace Erdos1105

open SimpleGraph Finset

/-- The color-preserving pendant swap is independent of path parity.
The order hypothesis ensures the dense core stays connected after
deleting any single representative edge. -/
theorem connected_pendant_reduction {V C : Type*} [Fintype V] [Fintype C]
    (c : (⊤ : SimpleGraph V).edgeSet → C) {k : ℕ} (hk : 6 ≤ k)
    (hn : k ≤ Fintype.card V) (hsmall : 2 * Fintype.card V ≤ 3 * (k - 2))
    (hq : (k - 2).choose 2 + 2 ≤ Fintype.card C)
    (hshapes : ∀ Q : SimpleGraph V, IsFullRepresentative c Q → Q.Preconnected → PendantCliqueShape Q k)
    (R : SimpleGraph V) (hR : IsFullRepresentative c R) (hconn : R.Preconnected) :
    k < Fintype.card V ∧ ∃ v, ∃ Q : SimpleGraph {w // w ≠ v},
      IsFullRepresentative (restrictVertexColoring c v) Q ∧ Q.Preconnected := by
  classical
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨S, hS, u, hu, hpend⟩ := hshapes R hR hconn
  have hedges : S.card.choose 2 + 2 ≤ R.edgeFinset.card := by
    rw [hR.card_edges, hS]
    exact hq
  have hout : 1 < Sᶜ.card := by rw [card_compl]; omega
  obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp hout
  have hx : x ∉ S := mem_compl.mp hx
  have hy : y ∉ S := mem_compl.mp hy
  let d : (⊤ : SimpleGraph V).edgeSet := ⟨s(x, y), hxy⟩
  obtain ⟨e, he⟩ := hR.palette (c d)
  have hcol : extendColor c d.val = extendColor c e.val := by
    rw [extendColor_edge]
    exact he.symm
  let R' := swapRepresentative R e.val d.val
  have hR' : IsFullRepresentative c R' := hR.swap e d hcol
  have hmin (v : (S : Set V)) :
      S.card ≤ 2 * ((R.deleteEdges {e.val}).induce (S : Set V)).degree v ∧
      2 ≤ ((R.deleteEdges {e.val}).induce (S : Set V)).degree v := by
    rw [← degreeWithin_eq_induce_degree (R.deleteEdges {e.val}) S v]
    have h₁ := pendant_core_degree_lower R S hpend hedges v.property
    have h₂ := degreeWithin_delete_edge_lower R S v.val e.val
    omega
  have hcard : 3 ≤ Fintype.card (S : Set V) := by simpa using (show 3 ≤ S.card by omega)
  have hham : ((R.deleteEdges {e.val}).induce (S : Set V)).IsHamiltonian := by
    apply SimpleGraph.dirac_theorem hcard
    intro v
    have h := (hmin v).1
    have hcard' : Fintype.card (S : Set V) = S.card := by simp
    omega
  have hcore := hham.connected.preconnected
  have hdeg (v : V) (hv : v ∈ S) : 2 ≤ R'.degree v := by
    have h₂ := (Copy.induce (R.deleteEdges {e.val}) (S : Set V)).degree_le ⟨v, hv⟩
    have h₃ := (R.deleteEdges {e.val}).degree_le_of_le (v := v)
      (deleteEdges_le_swapRepresentative R e.val d)
    exact (hmin ⟨v, hv⟩).2.trans (h₂.trans h₃)
  have hisolated : ∃ z, ∀ w, ¬R'.Adj z w := by
    by_contra! hnoiso
    obtain ⟨hconn', z, hz, a, b, hab, hza, hzb⟩ := pendant_swap_connected R S hu hx hy hxy e.val
      hpend (fun v ↦ hconn.exists_adj_of_nontrivial v) hnoiso hcore
    exact not_pendantShape_of_many_degree_two R' S hS hdeg hz
      (two_le_degree_of_two_neighbors R' hab hza hzb) (hshapes R' hR' hconn')
  obtain ⟨z, hz⟩ := hisolated
  have hzS : z ∉ S := by
    intro hzS
    obtain ⟨w, hw⟩ := (R'.degree_pos_iff_exists_adj z).mp (by have := hdeg z hzS; omega)
    exact hz w hw
  have hnew : R'.Adj x y := (mem_swapRepresentative R e.val d d.val).mpr (Or.inr rfl)
  have hzx : z ≠ x := fun h ↦ hz y (h ▸ hnew)
  have hzy : z ≠ y := fun h ↦ hz x (h ▸ hnew.symm)
  have hnlarge : k < Fintype.card V := by
    have hc := card_le_card (subset_univ (insert z (insert x (insert y S))))
    have hxnot : x ∉ insert y S := by simp [hx, hxy]
    have hznot : z ∉ insert x (insert y S) := by simp [hzS, hzx, hzy]
    rw [card_insert_of_notMem hznot, card_insert_of_notMem hxnot,
      card_insert_of_notMem hy, card_univ, hS] at hc
    omega
  have hconn₀ : (R.induce {w | w ≠ z}).Preconnected := by
    apply hconn.induce_of_degree_eq_one
    intro v hv
    have hvz : v = z := by simpa only [Set.mem_ofPred_eq, not_not] using hv
    subst v
    intro a ha b hb
    exact (hpend z hzS a ha).trans (hpend z hzS b hb).symm
  have hzu : R.Adj z u := by
    obtain ⟨w, hw⟩ := hconn.exists_adj_of_nontrivial z
    rwa [hpend z hzS w hw] at hw
  have hez : s(z, u) = e.val := by
    by_contra hne
    exact hz u ((deleteEdges_le_swapRepresentative R e.val d)
      (deleteEdges_adj.mpr ⟨hzu, hne⟩))
  have hsub : R.induce {w | w ≠ z} ≤ R'.induce {w | w ≠ z} := by
    intro a b hab
    apply (mem_swapRepresentative R e.val d s(a.val, b.val)).mpr
    refine Or.inl ⟨hab, ?_⟩
    intro heq
    rcases Sym2.eq_iff.mp (heq.trans hez.symm) with h | h
    · exact a.property h.1
    · exact b.property h.2
  exact ⟨hnlarge, z, R'.induce {w | w ≠ z}, hR'.delete_isolated hz, hconn₀.mono hsub⟩

end Erdos1105

#print axioms Erdos1105.connected_pendant_reduction
