import ErdosProblems.Erdos547.FiniteSelection
import ErdosProblems.Erdos547.LeafBunch
import ErdosProblems.Erdos547.HighDegreeCore

/-!
# Pruning a pair with few edges to a dense pair in the other colour
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph BigOperators

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

open scoped Classical in
theorem prune_sparse_cross_pair (A B : Finset V) (hdis : Disjoint A B)
    (t : ℕ) (hbudget : (∑ a ∈ A, degreeIn G B a) ≤ t ^ 2) :
    ∃ P ⊆ A, ∃ Q ⊆ B, A.card ≤ P.card + t ∧ B.card ≤ Q.card + t ∧
      (∀ p ∈ P, B.card ≤ degreeIn Gᶜ Q p + 2 * t) ∧
      (∀ q ∈ Q, A.card ≤ degreeIn Gᶜ P q + 2 * t) := by
  classical
  let ZA := A.filter fun a ↦ t < degreeIn G B a
  let ZB := B.filter fun b ↦ t < degreeIn G A b
  have hZA : ZA.card ≤ t := card_filter_gt_le_of_sum_le_square A
    (degreeIn G B) t hbudget
  have hswap : (∑ a ∈ A, degreeIn G B a) = ∑ b ∈ B, degreeIn G A b := by
    exact_mod_cast sum_degreeIn_swap G A B
  have hZB : ZB.card ≤ t := card_filter_gt_le_of_sum_le_square B
    (degreeIn G A) t (by rwa [← hswap])
  let P := A \ ZA
  let Q := B \ ZB
  have hPA : P ⊆ A := Finset.sdiff_subset
  have hQB : Q ⊆ B := Finset.sdiff_subset
  have hPsize : A.card ≤ P.card + t := by
    have hsum := Finset.card_sdiff_add_card_inter A ZA
    rw [Finset.inter_eq_right.mpr (Finset.filter_subset _ _)] at hsum
    change P.card + ZA.card = A.card at hsum
    omega
  have hQsize : B.card ≤ Q.card + t := by
    have hsum := Finset.card_sdiff_add_card_inter B ZB
    rw [Finset.inter_eq_right.mpr (Finset.filter_subset _ _)] at hsum
    change Q.card + ZB.card = B.card at hsum
    omega
  refine ⟨P, hPA, Q, hQB, hPsize, hQsize, ?_, ?_⟩
  · intro p hp
    obtain ⟨hpA, hpZA⟩ := Finset.mem_sdiff.mp hp
    have hred : degreeIn G B p ≤ t := by
      by_contra h
      exact hpZA (Finset.mem_filter.mpr ⟨hpA, by omega⟩)
    have hredQ := degreeIn_mono G hQB p
    have hpQ : p ∉ Q := fun h ↦ Finset.disjoint_left.mp hdis hpA (hQB h)
    have hsum := degreeIn_add_compl_of_not_mem G Q hpQ
    omega
  · intro q hq
    obtain ⟨hqB, hqZB⟩ := Finset.mem_sdiff.mp hq
    have hred : degreeIn G A q ≤ t := by
      by_contra h
      exact hqZB (Finset.mem_filter.mpr ⟨hqB, by omega⟩)
    have hredP := degreeIn_mono G hPA q
    have hqP : q ∉ P := fun h ↦ Finset.disjoint_left.mp hdis (hPA h) hqB
    have hsum := degreeIn_add_compl_of_not_mem G P hqP
    omega

end Erdos547

#print axioms Erdos547.prune_sparse_cross_pair
