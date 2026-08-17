import ErdosProblems.Erdos767.Case1Geometry
import ErdosProblems.Erdos767.WalkIndex

open Finset
open scoped SimpleGraph

namespace Erdos767Scratch

open SimpleGraph

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Tail maximality gives the standard terminal-neighbour cover. -/
lemma BestLollipop.neighbor_mem_cycle_or_tail' (B : BestLollipop G)
    {w : V} (hw : G.Adj B.terminal w) :
    w ∈ B.cycle.support ∨ w ∈ B.tail.support := by
  by_contra hout
  push Not at hout
  let L : Lollipop G :=
    { cycleBase := B.cycleBase
      cycle := B.cycle
      cycle_isCycle := B.cycle_isCycle
      start := B.start
      terminal := w
      tail := B.tail.concat hw
      tail_isPath := B.tail_isPath.concat hout.2 hw
      start_mem_cycle := B.start_mem_cycle
      cycle_tail_inter := by
        intro v hvC hvP
        simp only [Walk.support_concat, List.mem_append, List.mem_singleton] at hvP
        rcases hvP with hvP | rfl
        · exact B.cycle_tail_inter hvC hvP
        · exact (hout.1 hvC).elim }
  have hle := B.tail_maximal L rfl
  simp [L] at hle

/-- The non-repeated carrier of the rooted cycle is exactly the carrier of
the original longest cycle. -/
lemma BestLollipop.rotated_dropLast_toFinset_eq_cycle (B : BestLollipop G) :
    B.rotatedCycle.support.dropLast.toFinset = B.cycle.support.toFinset := by
  let C := B.rotatedCycle
  have hdrop : C.support.toFinset = C.support.dropLast.toFinset := by
    simpa [E767WalkIndex.cycleVertexFinset] using
      E767WalkIndex.cycle_support_toFinset_eq_cycleVertexFinset
        B.rotatedCycle_isCycle
  rw [← hdrop]
  ext w
  simp only [List.mem_toFinset]
  exact Walk.mem_support_rotate_iff B.cycle B.start B.start_mem_cycle

/-- The exact finset cover consumed by the checked Case-1 counting theorem. -/
lemma BestLollipop.neighborFinset_subset_rotatedCycle_union_tail
    (B : BestLollipop G) :
    G.neighborFinset B.terminal ⊆
      B.rotatedCycle.support.dropLast.toFinset ∪ B.tail.support.toFinset := by
  intro w hw
  have hadj : G.Adj B.terminal w := (G.mem_neighborFinset _ _).mp hw
  rcases B.neighbor_mem_cycle_or_tail' hadj with hwC | hwP
  · apply Finset.mem_union_left
    rw [B.rotated_dropLast_toFinset_eq_cycle]
    exact List.mem_toFinset.mpr hwC
  · exact Finset.mem_union_right _ (List.mem_toFinset.mpr hwP)

/-- If the positive cycle-neighbour set is empty, every terminal neighbour
lies on the tail (the index-zero attachment already lies there). -/
lemma BestLollipop.all_neighbors_tail_of_positive_cycle_indices_empty
    (B : BestLollipop G)
    (hempty : E767Case1Fixed.positiveCycleNeighborIndices
      B.rotatedCycle B.terminal = ∅) :
    G.neighborFinset B.terminal ⊆ B.tail.support.toFinset := by
  intro w hw
  have hadj : G.Adj B.terminal w := (G.mem_neighborFinset _ _).mp hw
  rcases B.neighbor_mem_cycle_or_tail' hadj with hwC | hwP
  · by_cases hws : w = B.start
    · subst w
      exact List.mem_toFinset.mpr B.tail.start_mem_support
    have hwR : w ∈ B.rotatedCycle.support :=
      (Walk.mem_support_rotate_iff B.cycle B.start B.start_mem_cycle).mpr hwC
    have hwCarrier : w ∈ E767WalkIndex.cycleVertexFinset B.rotatedCycle := by
      rw [← E767WalkIndex.cycle_support_toFinset_eq_cycleVertexFinset
        B.rotatedCycle_isCycle, List.mem_toFinset]
      exact hwR
    rw [E767WalkIndex.cycleVertexFinset_eq_image_cycleIndices
      B.rotatedCycle_isCycle] at hwCarrier
    obtain ⟨i, hi, hiw⟩ := Finset.mem_image.mp hwCarrier
    have hi0 : i ≠ 0 := by
      intro hi0
      subst i
      apply hws
      simpa using hiw.symm
    have hiS : i ∈ E767Case1Fixed.positiveCycleNeighborIndices
        B.rotatedCycle B.terminal := by
      rw [E767Case1Fixed.mem_positiveCycleNeighborIndices]
      refine ⟨hi0, E767WalkIndex.mem_cycleIndices.mp hi, ?_⟩
      exact hiw ▸ hadj
    rw [hempty] at hiS
    simp at hiS
  · exact List.mem_toFinset.mpr hwP

/-- The complete output of Case 1, phrased as a dichotomy ready for the
aligned-fan Case 2: either the relative Dirac degree bound already holds, or
all neighbours of the terminal lie on the tail. -/
theorem BestLollipop.degree_bound_or_all_neighbors_tail
    (B : BestLollipop G) (hpos : 0 < B.tail.length) :
    2 * G.degree B.terminal ≤ B.cycle.length ∨
      G.neighborFinset B.terminal ⊆ B.tail.support.toFinset := by
  by_cases hS : (E767Case1Fixed.positiveCycleNeighborIndices
      B.rotatedCycle B.terminal).Nonempty
  · left
    exact B.two_mul_degree_terminal_le_cycle_length_case1 hpos
      B.neighborFinset_subset_rotatedCycle_union_tail hS
  · right
    rw [Finset.not_nonempty_iff_eq_empty] at hS
    exact B.all_neighbors_tail_of_positive_cycle_indices_empty hS

end

end Erdos767Scratch

