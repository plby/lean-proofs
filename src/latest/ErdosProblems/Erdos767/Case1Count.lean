import ErdosProblems.Erdos767.Lollipop
import ErdosProblems.Erdos767.NoConsecutive
import ErdosProblems.Erdos767.Case1Core

open Finset
open scoped SimpleGraph

namespace E767Case1Fixed

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Cycle-neighbour indices other than the lollipop attachment at index zero.
The attachment is already counted on the tail side of the degree estimate. -/
def positiveCycleNeighborIndices {x : V} (C : G.Walk x x) (y : V) : Finset ℕ :=
  (E767DiracCase1.cycleNeighborIndices G C y).erase 0

@[simp] lemma mem_positiveCycleNeighborIndices {x y : V}
    {C : G.Walk x x} {i : ℕ} :
    i ∈ positiveCycleNeighborIndices C y ↔
      i ≠ 0 ∧ i < C.length ∧ G.Adj y (C.getVert i) := by
  simp [positiveCycleNeighborIndices, E767DiracCase1.cycleNeighborIndices,
    and_assoc]

/-- Corrected endpoint-degree estimate.  The index-zero cycle vertex is the
initial tail vertex, so it is charged to the tail rather than to the set of
cycle indices. -/
lemma degree_le_tail_add_positive_cycle_indices
    {x y : V} {C : G.Walk x x} {P : G.Walk x y}
    (hC : C.IsCycle) (hP : P.IsPath)
    (hcover : G.neighborFinset y ⊆
      C.support.dropLast.toFinset ∪ P.support.toFinset) :
    G.degree y ≤ P.length + (positiveCycleNeighborIndices C y).card := by
  let A : Finset V := G.neighborFinset y ∩ P.support.toFinset
  let S : Finset ℕ := positiveCycleNeighborIndices C y
  have hcover' : G.neighborFinset y ⊆ A ∪ S.image C.getVert := by
    intro z hz
    rcases Finset.mem_union.mp (hcover hz) with hzC | hzP
    · by_cases hzP' : z ∈ P.support.toFinset
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hz, hzP'⟩)
      · apply Finset.mem_union_right
        have hzI : z ∈ G.neighborFinset y ∩ C.support.dropLast.toFinset :=
          Finset.mem_inter.mpr ⟨hz, hzC⟩
        obtain ⟨i, hi, hiz⟩ := Finset.mem_image.mp
          (E767DiracCase1.cycle_neighbors_subset_index_image G hC hzI)
        refine Finset.mem_image.mpr ⟨i, ?_, hiz⟩
        have hi0 : i ≠ 0 := by
          intro hi0
          subst i
          have hzx : z = x := by simpa using hiz.symm
          apply hzP'
          rw [hzx]
          exact List.mem_toFinset.mpr P.start_mem_support
        exact Finset.mem_erase.mpr ⟨hi0, hi⟩
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hz, hzP⟩)
  rw [← G.card_neighborFinset_eq_degree]
  calc
    (G.neighborFinset y).card ≤ (A ∪ S.image C.getVert).card :=
      Finset.card_le_card hcover'
    _ ≤ A.card + (S.image C.getVert).card := Finset.card_union_le _ _
    _ ≤ P.length + S.card := Nat.add_le_add
      (E767DiracCase1.card_path_neighbors_le_length G hP) Finset.card_image_le

/-- The corrected counting core for Case 1 of the best-lollipop proof. -/
theorem case1_of_positive_indices
    {x y : V} {C : G.Walk x x} {P : G.Walk x y} {k : ℕ}
    (hC : C.IsCycle) (hP : P.IsPath)
    (hcover : G.neighborFinset y ⊆
      C.support.dropLast.toFinset ∪ P.support.toFinset)
    (hcycle : (positiveCycleNeighborIndices C y).Nonempty)
    (hlower : ∀ i ∈ positiveCycleNeighborIndices C y,
      P.length + 1 ≤ i)
    (hupper : ∀ i ∈ positiveCycleNeighborIndices C y,
      i ≤ C.length - P.length - 1)
    (hnext : ∀ i ∈ positiveCycleNeighborIndices C y,
      i + 1 ∉ positiveCycleNeighborIndices C y)
    (hdegree : k ≤ G.degree y) :
    2 * k ≤ C.length := by
  have hdeg := degree_le_tail_add_positive_cycle_indices hC hP hcover
  have hcard := Erdos767.two_mul_card_le_of_no_consecutive
    (positiveCycleNeighborIndices C y) P.length C.length hlower hupper hnext
  obtain ⟨i, hi⟩ := hcycle
  have hil := hlower i hi
  have hiu := hupper i hi
  omega

end

end E767Case1Fixed

