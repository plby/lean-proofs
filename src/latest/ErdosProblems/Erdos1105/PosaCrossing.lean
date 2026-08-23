import ErdosProblems.Erdos1105.PathCycleSplice
import ErdosProblems.Erdos1105.CrossingCount
import ErdosProblems.Erdos1105.CycleSaturation

/-!
# The crossing case of the Pósa--Kopylov path lemma
-/

namespace Erdos1105

open SimpleGraph Finset

noncomputable def startNeighborIndices {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) : Finset ℕ := by
  classical
  exact (range p.length).filter fun i ↦ G.Adj x (p.getVert (i + 1))

noncomputable def endNeighborIndices {V : Type*} {G : SimpleGraph V} {x y : V}
    (p : G.Walk x y) : Finset ℕ := by
  classical
  exact (range p.length).filter fun i ↦ G.Adj y (p.getVert i)

theorem crossing_chords_bound {V : Type*} {G : SimpleGraph V} {x y : V} {k : ℕ}
    (hG : NoLongCycle G k) (hk : 3 ≤ k) (p : G.Walk x y) (hp : p.IsPath)
    {i j : ℕ} (hi : i ∈ endNeighborIndices p) (hj : j ∈ startNeighborIndices p)
    (hij : i ≤ j) : i + (p.length - (j + 1)) + 2 < k := by
  classical
  have hiadj : G.Adj y (p.getVert i) := (mem_filter.mp hi).2
  have hjadj : G.Adj x (p.getVert (j + 1)) := (mem_filter.mp hj).2
  have hjL : j < p.length := mem_range.mp (mem_filter.mp hj).1
  by_cases hlen : 3 ≤ i + (p.length - (j + 1)) + 2
  · obtain ⟨v, s, hs, hslen⟩ := cycle_of_crossing_chords p hp (by omega) (by omega)
      hiadj hjadj hlen
    have h := hG v s hs
    rwa [hslen] at h
  · omega

theorem disjoint_neighbor_indices_of_no_long_cycle {V : Type*} {G : SimpleGraph V}
    {x y : V} {k : ℕ} (hG : NoLongCycle G k) (hk : 3 ≤ k)
    (p : G.Walk x y) (hp : p.IsPath) (hlen : k ≤ p.length + 1) :
    Disjoint (startNeighborIndices p) (endNeighborIndices p) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiA hiB
  have hiL : i < p.length := mem_range.mp (mem_filter.mp hiA).1
  have h := crossing_chords_bound hG hk p hp hiB hiA le_rfl
  omega

/-- If a long path has crossing endpoint neighbors, its endpoint degree
sum along the path is smaller than the forbidden cycle length. -/
theorem neighbor_indices_card_lt_of_crossing {V : Type*} {G : SimpleGraph V}
    {x y : V} {k : ℕ} (hG : NoLongCycle G k) (hk : 3 ≤ k)
    (p : G.Walk x y) (hp : p.IsPath) (hlen : k ≤ p.length + 1)
    (hcross : ∃ i ∈ endNeighborIndices p, ∃ j ∈ startNeighborIndices p, i ≤ j) :
    (startNeighborIndices p).card + (endNeighborIndices p).card < k := by
  classical
  obtain ⟨i, hi, j, hj, hij, hcard⟩ := exists_crossing_with_card_bound
    (startNeighborIndices p) (endNeighborIndices p)
    (filter_subset _ _) (filter_subset _ _)
    (disjoint_neighbor_indices_of_no_long_cycle hG hk p hp hlen) hcross
  exact hcard.trans_lt (crossing_chords_bound hG hk p hp hi hj hij)

end Erdos1105

#print axioms Erdos1105.neighbor_indices_card_lt_of_crossing
