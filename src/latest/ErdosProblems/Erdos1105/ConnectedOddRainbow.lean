import ErdosProblems.Erdos1105.PendantSwap
import ErdosProblems.Erdos1105.PathFormulaArithmetic

namespace Erdos1105

open SimpleGraph Finset

theorem fullRepresentative_odd_pendant {V C : Type*} [Fintype V] [Fintype C]
    (c : (⊤ : SimpleGraph V).edgeSet → C) {l : ℕ} (hl : 4 ≤ l)
    (hn : 2 * l + 1 ≤ Fintype.card V)
    (hfree : ∀ f : (pathGraph (2 * l + 1)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (hq : pathFormula (Fintype.card V) (2 * l + 1) < Fintype.card C)
    (R : SimpleGraph V) (hR : IsFullRepresentative c R) (hconn : R.Preconnected) :
    PendantCliqueShape R (2 * l + 1) := by
  classical
  apply connected_path_high_edges_pendant R (by omega) hn hconn (hR.free hfree)
  have h₁ : 2 * l + 1 - 1 = 2 * l := by omega
  have h₂ : (2 * l + 1 - 2) / 2 = l - 1 := by omega
  rw [h₁, h₂, hR.card_edges]
  exact (odd_path_stability_threshold (Fintype.card V) l hl hn).trans_lt hq

/-- In the connected-representative case for odd paths, a coloring above
the claimed bound has a vertex whose deletion loses no colors. This is
the reduction step used by induction on the number of vertices. -/
theorem connected_odd_high_colors_reduction {V C : Type*} [Fintype V] [Fintype C]
    (c : (⊤ : SimpleGraph V).edgeSet → C) {l : ℕ} (hl : 4 ≤ l)
    (hn : 2 * l + 1 ≤ Fintype.card V)
    (hfree : ∀ f : (pathGraph (2 * l + 1)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (hq : pathFormula (Fintype.card V) (2 * l + 1) < Fintype.card C)
    (R : SimpleGraph V) (hR : IsFullRepresentative c R) (hconn : R.Preconnected) :
    2 * l + 1 < Fintype.card V ∧ ∃ v, (privateColors c v).card = 0 ∧
      ∃ Q : SimpleGraph {w // w ≠ v}, IsFullRepresentative (restrictVertexColoring c v) Q ∧
        Q.Preconnected := by
  classical
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hshape := fullRepresentative_odd_pendant c hl hn hfree hq R hR hconn
  have hupper : Fintype.card C ≤ pathExtremalEdges (Fintype.card V) (2 * l) 1 := by
    have h := hshape.edge_bound (by omega) hn
    rw [hR.card_edges] at h
    simpa using h
  have hnsmall := odd_pendant_order_bound (Fintype.card V) l (Fintype.card C) hl hn hq hupper
  obtain ⟨S, hS, u, hu, hpend⟩ := hshape
  have hScard : S.card = 2 * l - 1 := by omega
  have hedges : S.card.choose 2 + 2 ≤ R.edgeFinset.card := by
    rw [hR.card_edges, hScard]
    rw [pathFormula_odd (Fintype.card V) l (by omega) (by omega)] at hq
    have h := lt_of_le_of_lt (le_max_left _ _) hq
    omega
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
  have hmin (v : (S : Set V)) : l ≤ ((R.deleteEdges {e.val}).induce (S : Set V)).degree v := by
    rw [← degreeWithin_eq_induce_degree (R.deleteEdges {e.val}) S v]
    have h₁ := pendant_core_degree_lower R S hpend hedges v.property
    have h₂ := degreeWithin_delete_edge_lower R S v.val e.val
    omega
  have hcard : 3 ≤ Fintype.card (S : Set V) := by simpa using (show 3 ≤ S.card by omega)
  have hham : ((R.deleteEdges {e.val}).induce (S : Set V)).IsHamiltonian := by
    apply SimpleGraph.dirac_theorem hcard
    intro v
    have h := hmin v
    have hcard' : Fintype.card (S : Set V) = S.card := by simp
    omega
  have hcore := hham.connected.preconnected
  have hdeg (v : V) (hv : v ∈ S) : 2 ≤ R'.degree v := by
    have h₁ := hmin ⟨v, hv⟩
    have h₂ := (Copy.induce (R.deleteEdges {e.val}) (S : Set V)).degree_le ⟨v, hv⟩
    have h₃ := (R.deleteEdges {e.val}).degree_le_of_le (v := v)
      (deleteEdges_le_swapRepresentative R e.val d)
    exact (show 2 ≤ l by omega).trans (h₁.trans (h₂.trans h₃))
  have hisolated : ∃ z, ∀ w, ¬R'.Adj z w := by
    by_contra! hnoiso
    obtain ⟨hconn', z, hz, a, b, hab, hza, hzb⟩ := pendant_swap_connected R S hu hx hy hxy e.val
      hpend (fun v ↦ hconn.exists_adj_of_nontrivial v) hnoiso hcore
    have hshape' := fullRepresentative_odd_pendant c hl hn hfree hq R' hR' hconn'
    exact not_pendantShape_of_many_degree_two R' S hS hdeg hz
      (two_le_degree_of_two_neighbors R' hab hza hzb) hshape'
  obtain ⟨z, hz⟩ := hisolated
  have hzS : z ∉ S := by
    intro hzS
    obtain ⟨w, hw⟩ := (R'.degree_pos_iff_exists_adj z).mp (by have := hdeg z hzS; omega)
    exact hz w hw
  have hnew : R'.Adj x y := (mem_swapRepresentative R e.val d d.val).mpr (Or.inr rfl)
  have hzx : z ≠ x := fun h ↦ hz y (h ▸ hnew)
  have hzy : z ≠ y := fun h ↦ hz x (h ▸ hnew.symm)
  have hnlarge : 2 * l + 1 < Fintype.card V := by
    have hc := card_le_card (subset_univ (insert z (insert x (insert y S))))
    have hxnot : x ∉ insert y S := by simp [hx, hxy]
    have hznot : z ∉ insert x (insert y S) := by simp [hzS, hzx, hzy]
    rw [card_insert_of_notMem hznot, card_insert_of_notMem hxnot,
      card_insert_of_notMem hy, card_univ, hScard] at hc
    omega
  have hzprivate : (privateColors c z).card = 0 := by
    by_contra hne
    obtain ⟨i, hi⟩ := card_pos.mp (Nat.pos_of_ne_zero hne)
    obtain ⟨w, hw⟩ := hR'.neighbor_of_private ((mem_privateColors c z i).mp hi)
    exact hz w hw
  have hconn₀ : (R.induce {w | w ≠ z}).Preconnected := by
    apply hconn.induce_of_degree_eq_one
    intro v hv
    have hvz : v = z := by simpa only [Set.mem_setOf_eq, not_not] using hv
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
  exact ⟨hnlarge, z, hzprivate, R'.induce {w | w ≠ z}, hR'.delete_isolated hz,
    hconn₀.mono hsub⟩

theorem connected_high_colors_odd_reduction {V C : Type*} [Fintype V] [Fintype C]
    (c : (⊤ : SimpleGraph V).edgeSet → C) {k : ℕ} (hk : 5 ≤ k) (hodd : Odd k)
    (hn : k ≤ Fintype.card V)
    (hfree : ∀ f : (pathGraph k).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (hq : pathFormula (Fintype.card V) k < Fintype.card C)
    (R : SimpleGraph V) (hR : IsFullRepresentative c R) (hconn : R.Preconnected) :
    k < Fintype.card V ∧ ∃ v, (privateColors c v).card = 0 ∧
      ∃ Q : SimpleGraph {w // w ≠ v}, IsFullRepresentative (restrictVertexColoring c v) Q ∧
        Q.Preconnected := by
  classical
  obtain ⟨l, rfl⟩ := hodd
  by_cases hl : 4 ≤ l
  · exact connected_odd_high_colors_reduction c hl hn hfree hq R hR hconn
  · have hcases : l = 2 ∨ l = 3 := by omega
    have hb := connected_path_edges_le R (by omega : 4 ≤ 2 * l + 1) hn hconn (hR.free hfree)
    rw [hR.card_edges] at hb
    rcases hcases with rfl | rfl <;>
      norm_num [pathFormula, pathExtremalEdges, Nat.choose] at hb hq <;> omega

end Erdos1105

#print axioms Erdos1105.connected_high_colors_odd_reduction
