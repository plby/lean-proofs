import ErdosProblems.Erdos1105.DegreeObstruction
import ErdosProblems.Erdos1105.CoreBasics

namespace Erdos1105

open SimpleGraph Finset

/-- At the boundary order, a large clique and the minimum-degree bound
force all outside vertices to have degree `d` and identical neighbors
inside the clique. -/
theorem clique_boundary_degrees_and_neighbors {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {S : Finset V} {d : ℕ}
    (hd : 2 ≤ d) (hn : Fintype.card V = 2 * d + 3)
    (hS : G.IsClique (S : Set V)) (hScard : S.card = d + 3)
    (hnot : ¬G.IsHamiltonian) (hmin : ∀ v, d ≤ G.degree v) :
    (∀ v ∉ S, G.degree v = d) ∧
      (∀ v ∉ S, ∀ s ∈ S, (∃ w ∉ S, G.Adj s w) → G.Adj v s) := by
  classical
  let H := G.closure
  have hnotH : ¬H.IsHamiltonian := fun h ↦ hnot ((from_closure_iff (G := G)).mp h)
  have hminH (v : V) : d ≤ H.degree v :=
    (hmin v).trans (G.degree_le_of_le G.self_le_closure)
  have hSdeg (s : V) (hs : s ∈ S) : d + 2 ≤ H.degree s := by
    have hsub : S.erase s ⊆ H.neighborFinset s := by
      intro w hw
      simpa only [mem_neighborFinset] using G.self_le_closure
        (hS hs (mem_erase.mp hw).2 (mem_erase.mp hw).1.symm)
    have hcard := card_le_card hsub
    rw [card_erase_of_mem hs, hScard, card_neighborFinset_eq_degree] at hcard
    omega
  obtain ⟨i, hdi, hiN, hlow, hhigh⟩ := nonhamiltonian_degree_obstruction H (by omega) hnotH hminH
  have hid : i = d := by
    by_contra h
    have hieq : i = d + 1 := by omega
    have hsub : S ⊆ univ.filter (fun v ↦ Fintype.card V - i ≤ H.degree v) := by
      intro v hv
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      have := hSdeg v hv
      omega
    have := (card_le_card hsub).trans hhigh
    omega
  subst i
  have hlowSub : univ.filter (fun v ↦ H.degree v ≤ d) ⊆ Sᶜ := by
    intro v hv
    apply mem_compl.mpr
    intro hvS
    have := hSdeg v hvS
    have := (mem_filter.mp hv).2
    omega
  have hlowEq : univ.filter (fun v ↦ H.degree v ≤ d) = Sᶜ := by
    apply eq_of_subset_of_card_le hlowSub
    rw [card_compl, hScard, hn]
    omega
  have hdegH (v : V) (hv : v ∉ S) : H.degree v = d := by
    have hlowv : v ∈ univ.filter (fun v ↦ H.degree v ≤ d) :=
      hlowEq.symm ▸ mem_compl.mpr hv
    have := (mem_filter.mp hlowv).2
    have := hminH v
    omega
  have hdegG (v : V) (hv : v ∉ S) : G.degree v = d := by
    have hle : G.degree v ≤ H.degree v := G.degree_le_of_le G.self_le_closure
    have := hdegH v hv
    have := hmin v
    omega
  refine ⟨hdegG, ?_⟩
  intro v hv s hs houtside
  obtain ⟨w, hw, hsw⟩ := houtside
  have hSdeg' : d + 3 ≤ H.degree s := by
    have hsub : insert w (S.erase s) ⊆ H.neighborFinset s := by
      intro z hz
      rcases mem_insert.mp hz with rfl | hz
      · simpa only [mem_neighborFinset] using G.self_le_closure hsw
      · simpa only [mem_neighborFinset] using G.self_le_closure
          (hS hs (mem_erase.mp hz).2 (mem_erase.mp hz).1.symm)
    have hcard := card_le_card hsub
    rw [card_insert_of_notMem (fun h ↦ hw (mem_erase.mp h).2),
      card_erase_of_mem hs, hScard, card_neighborFinset_eq_degree] at hcard
    omega
  have hvs : v ≠ s := fun h ↦ hv (h ▸ hs)
  have hHvs : H.Adj v s := G.closure_spec hvs (by
    change Fintype.card V ≤ H.degree v + H.degree s
    rw [hn, hdegH v hv]
    omega)
  have hsub : G.neighborFinset v ⊆ H.neighborFinset v := by
    intro z hz
    have h : G.Adj v z := by simpa only [mem_neighborFinset] using hz
    simpa only [mem_neighborFinset] using G.self_le_closure h
  have heq : G.neighborFinset v = H.neighborFinset v := by
    apply eq_of_subset_of_card_le hsub
    rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree, hdegG v hv, hdegH v hv]
  have hm : s ∈ H.neighborFinset v := by simpa only [mem_neighborFinset] using hHvs
  rw [← heq] at hm
  simpa only [mem_neighborFinset] using hm

end Erdos1105

#print axioms Erdos1105.clique_boundary_degrees_and_neighbors
