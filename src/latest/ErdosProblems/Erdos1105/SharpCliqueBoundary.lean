import ErdosProblems.Erdos1105.CliqueClosure
import ErdosProblems.Erdos1105.SharpCoreCount
import ErdosProblems.Erdos1105.ThreeCliqueCycle

namespace Erdos1105

open SimpleGraph Finset

/-- At the boundary order, equality in the clique-core edge count forces
the exceptional join with a three-vertex remainder. -/
theorem sharp_clique_boundary_join {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 2 ≤ d) (hn : Fintype.card V = 2 * d + 3)
    (hclique : G.IsClique (vertexCore G d : Set V))
    (hcard : (vertexCore G d).card = d + 3) (hnot : ¬G.IsHamiltonian)
    (hsharp : G.edgeFinset.card = (vertexCore G d).card.choose 2 +
      d * (Fintype.card V - (vertexCore G d).card)) :
    ∃ A T : Finset V, A.card = d ∧ T.card = 3 ∧ Disjoint A T ∧
      (∀ u, G.IsUniversal u → u ∈ A) ∧ threeCliqueJoin A T ≤ G := by
  classical
  have hactual := sharp_core_count_actual G d hsharp
  have hmin (v : V) : d ≤ G.degree v := by
    rw [← degreeWithin_univ G v]
    by_cases hv : v ∈ vertexCore G d
    · exact (vertexCore_degree G d hv).le.trans (degreeWithin_mono G (subset_univ _) v)
    · exact degreeWithin_ge_of_sharp_core_count G d univ (subset_univ _) hactual (mem_univ _) hv
  obtain ⟨hdeg, hcommon⟩ := clique_boundary_degrees_and_neighbors G hd hn hclique hcard hnot hmin
  have hindep := sharp_core_outside_independent G d univ (subset_univ _) hactual
    (fun v _ hv ↦ by rw [degreeWithin_univ G v]; exact hdeg v hv)
  have hWcard : (vertexCore G d)ᶜ.card = d := by rw [card_compl, hcard, hn]; omega
  obtain ⟨v, hv⟩ := card_pos.mp (by omega : 0 < (vertexCore G d)ᶜ.card)
  have hvc : v ∉ vertexCore G d := mem_compl.mp hv
  let A := G.neighborFinset v
  let T := vertexCore G d \ A
  have hA : A.card = d := by rw [card_neighborFinset_eq_degree]; exact hdeg v hvc
  have hAsub : A ⊆ vertexCore G d := by
    intro w hw
    have hvw : G.Adj v w := by simpa only [A, mem_neighborFinset] using hw
    by_contra hwc
    exact hindep v (mem_univ _) hvc w (mem_univ _) hwc hvw
  have hT : T.card = 3 := by
    dsimp [T]
    rw [card_sdiff_of_subset hAsub, hcard, hA]
    omega
  have hAT : Disjoint A T := by
    rw [Finset.disjoint_left]
    intro w hw hwt
    exact (mem_sdiff.mp hwt).2 hw
  have hAall (w : V) (hw : w ∈ A) : G.IsUniversal w := by
    intro z hwz
    by_cases hz : z ∈ vertexCore G d
    · exact hclique (hAsub hw) hz hwz
    · have hvw : G.Adj v w := by simpa only [A, mem_neighborFinset] using hw
      exact (hcommon z hz w (hAsub hw) ⟨v, hvc, hvw.symm⟩).symm
  refine ⟨A, T, hA, hT, hAT, ?_, ?_⟩
  · intro u hu
    have huCore := universal_mem_vertexCore G d (card_pos.mp (by omega)) hu
    have hvu : v ≠ u := fun h ↦ hvc (h ▸ huCore)
    have hadj : G.Adj v u := (hu hvu.symm).symm
    simpa only [A, mem_neighborFinset] using hadj
  · intro x y hxy
    rcases hxy.2 with hx | hy | hTxy
    · exact hAall x hx hxy.1
    · exact (hAall y hy hxy.1.symm).symm
    · exact hclique (mem_sdiff.mp hTxy.1).1 (mem_sdiff.mp hTxy.2).1 hxy.1

end Erdos1105

#print axioms Erdos1105.sharp_clique_boundary_join
