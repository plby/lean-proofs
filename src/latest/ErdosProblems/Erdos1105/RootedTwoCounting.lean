import ErdosProblems.Erdos1105.RootedTwoStructure
import ErdosProblems.Erdos1105.BetweenCounting
import ErdosProblems.Erdos1105.CoreBasics

namespace Erdos1105

open SimpleGraph Finset

/-- The edges between neighbors of the root count all excess over a tree. -/
theorem rooted_two_edge_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Preconnected) (u : V)
    (hpath : ∀ w, ∀ p : G.Walk u w, p.IsPath → p.length ≤ 2) :
    G.edgeFinset.card ≤ Fintype.card V - 1 +
      (E767EGApi.edgesInside G (G.neighborFinset u)).card := by
  classical
  let A := G.neighborFinset u
  have hu : u ∈ Aᶜ := by simp [A]
  have hcover : ∀ x y, G.Adj x y → x ∈ A ∨ y ∈ A := by
    intro x y hxy
    simpa only [A, mem_neighborFinset] using rooted_two_neighbor_cover G hconn u hpath x y hxy
  have hbound := vertex_cover_edge_count_le G A hcover
  have hdegu : degreeWithin G A u = A.card := by
    apply degreeWithin_eq_card_of_all_adj
    intro w hw
    simpa only [A, mem_neighborFinset] using hw
  have hout (w : V) (hw : w ∈ Aᶜ.erase u) : degreeWithin G A w ≤ 1 := by
    have hwu := (mem_erase.mp hw).1
    have hnot : ¬G.Adj u w := by
      simpa only [A, mem_neighborFinset] using mem_compl.mp (mem_erase.mp hw).2
    exact (degreeWithin_mono G (subset_univ A) w).trans
      ((degreeWithin_univ G w).le.trans (rooted_two_outside_degree G hconn u hpath hwu hnot))
  have hsum : ∑ w ∈ Aᶜ.erase u, degreeWithin G A w ≤ (Aᶜ.erase u).card := by
    simpa only [sum_const_nat, Nat.mul_one] using sum_le_sum hout
  have hsplit := sum_erase_add Aᶜ (degreeWithin G A) hu
  rw [hdegu] at hsplit
  rw [card_erase_of_mem hu, card_compl] at hsum
  have hpos : 0 < Aᶜ.card := card_pos.mpr ⟨u, hu⟩
  rw [card_compl] at hpos
  change G.edgeFinset.card ≤ Fintype.card V - 1 + (E767EGApi.edgesInside G A).card
  omega

/-- Distinct edges between neighbors of the root have disjoint endpoints. -/
theorem rooted_two_neighbor_edges_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V)
    (hpath : ∀ w, ∀ p : G.Walk u w, p.IsPath → p.length ≤ 2)
    {e f : Sym2 V} (he : e ∈ E767EGApi.edgesInside G (G.neighborFinset u))
    (hf : f ∈ E767EGApi.edgesInside G (G.neighborFinset u)) (hef : e ≠ f) :
    Disjoint e.toFinset f.toFinset := by
  classical
  apply Finset.disjoint_left.mpr
  intro b hbe hbf
  obtain ⟨a, rfl⟩ := Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp hbe)
  obtain ⟨c, rfl⟩ := Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp hbf)
  have hba : G.Adj b a := mem_edgeFinset.mp (mem_filter.mp he).1
  have hbc : G.Adj b c := mem_edgeFinset.mp (mem_filter.mp hf).1
  have hua : G.Adj u a := by
    have h := (mem_filter.mp he).2 (by simp : a ∈ s(b, a).toFinset)
    simpa only [mem_neighborFinset] using h
  have hub : G.Adj u b := by
    have h := (mem_filter.mp he).2 (by simp : b ∈ s(b, a).toFinset)
    simpa only [mem_neighborFinset] using h
  have huc : G.Adj u c := by
    have h := (mem_filter.mp hf).2 (by simp : c ∈ s(b, c).toFinset)
    simpa only [mem_neighborFinset] using h
  exact rooted_two_no_chain hpath hua hba.symm hbc hub.ne.symm huc.ne.symm
    (fun h ↦ hef (congrArg (fun z ↦ s(b, z)) h.symm))

end Erdos1105

#print axioms Erdos1105.rooted_two_edge_count
