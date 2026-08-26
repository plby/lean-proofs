import ErdosProblems.Erdos556.CrossCoreCounting

/-! A long cycle in one of two opposite dense cores with outside vertices. -/

namespace Erdos556

open SimpleGraph Finset

theorem exists_cycle_from_two_dense_cores {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) (a k d : ℕ)
    (hdis : Disjoint A B) (hA : a ≤ A.card) (hB : a ≤ B.card)
    (hlarge : 4 * k < a) (hsize : k + 2 * d ≤ a) (hN : 3 ≤ a + k)
    (hred : ∀ v ∈ A, A.card ≤ (G.neighborFinset v ∩ A).card + d)
    (hblue : ∀ v ∈ B, B.card ≤ (Gᶜ.neighborFinset v ∩ B).card + d) :
    (∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = a + k) ∨
    (∃ (v : V) (c : Gᶜ.Walk v v), c.IsCycle ∧ c.length = a + k) := by
  classical
  obtain ⟨A', hA'A, hA'⟩ := exists_subset_card_eq hA
  obtain ⟨B', hB'B, hB'⟩ := exists_subset_card_eq hB
  have hdis' : Disjoint A' B' := hdis.mono hA'A hB'B
  have hred' := dense_core_bound_subset G A' A d hA'A hred
  have hblue' := dense_core_bound_subset Gᶜ B' B d hB'B hblue
  rcases exists_absorbable_cross_set G A' B' a k hdis' hA' hB' hlarge with
    ⟨W, hWB, hW, hgood⟩ | ⟨W, hWA, hW, hgood⟩
  · left
    obtain ⟨v, c, hc, hlen⟩ := exists_cycle_of_dense_core G A' W d
      (hdis'.mono_right hWB) (by omega) (by omega) hred'
      (fun v hv => by simpa only [hW] using hgood v hv)
    exact ⟨v, c, hc, by omega⟩
  · right
    obtain ⟨v, c, hc, hlen⟩ := exists_cycle_of_dense_core Gᶜ B' W d
      (hdis'.symm.mono_right hWA) (by omega) (by omega) hblue'
      (fun v hv => by simpa only [hW] using hgood v hv)
    exact ⟨v, c, hc, by omega⟩

#print axioms exists_cycle_from_two_dense_cores

end Erdos556
