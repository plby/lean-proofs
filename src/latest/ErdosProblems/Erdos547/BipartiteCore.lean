import ErdosProblems.Erdos547.HighDegreeCore
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Extracting a bipartite pair with large minimum cross degree
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

open scoped Classical in
theorem degreeIn_between_left (A B S : Finset V) (hdis : Disjoint A B)
    {z : V} (hz : z ∈ A) :
    degreeIn (G.between (A : Set V) (B : Set V)) S z = degreeIn G (S ∩ B) z := by
  classical
  have hzB : z ∉ B := fun h ↦ Finset.disjoint_left.mp hdis hz h
  unfold degreeIn
  congr 1
  ext w
  simp only [Finset.mem_filter, SimpleGraph.between_adj, Finset.mem_coe, hz, hzB,
    true_and, false_and, or_false, Finset.mem_inter]
  tauto

open scoped Classical in
theorem degreeIn_between_right (A B S : Finset V) (hdis : Disjoint A B)
    {z : V} (hz : z ∈ B) :
    degreeIn (G.between (A : Set V) (B : Set V)) S z = degreeIn G (S ∩ A) z := by
  classical
  have hzA : z ∉ A := fun h ↦ Finset.disjoint_left.mp hdis h hz
  unfold degreeIn
  congr 1
  ext w
  simp only [Finset.mem_filter, SimpleGraph.between_adj, Finset.mem_coe, hz, hzA,
    true_and, false_and, false_or, Finset.mem_inter]
  tauto

open scoped Classical in
theorem degreeMass_between_union (A B : Finset V) (hdis : Disjoint A B) :
    degreeMass (G.between (A : Set V) (B : Set V)) (A ∪ B) =
      2 * ∑ a ∈ A, (degreeIn G B a : ℝ) := by
  classical
  unfold degreeMass
  rw [Finset.sum_union hdis]
  have hleft : (∑ a ∈ A, (degreeIn (G.between (A : Set V) (B : Set V)) (A ∪ B) a : ℝ)) =
      ∑ a ∈ A, (degreeIn G B a : ℝ) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [degreeIn_between_left G A B (A ∪ B) hdis ha, Finset.union_inter_cancel_right]
  have hright : (∑ b ∈ B, (degreeIn (G.between (A : Set V) (B : Set V)) (A ∪ B) b : ℝ)) =
      ∑ b ∈ B, (degreeIn G A b : ℝ) := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [degreeIn_between_right G A B (A ∪ B) hdis hb, Finset.union_inter_cancel_left]
  rw [hleft, hright, sum_degreeIn_swap G B A]
  ring

open scoped Classical in
/-- More than `k*(|A|+|B|)` cross edges force nonempty subsets on which every
cross degree is strictly greater than `k`. -/
theorem exists_bipartite_degree_core (A B : Finset V) (hdis : Disjoint A B) (k : ℕ)
    (hmass : (k : ℝ) * (A.card + B.card) < ∑ a ∈ A, (degreeIn G B a : ℝ)) :
    ∃ P ⊆ A, ∃ Q ⊆ B, P.Nonempty ∧ Q.Nonempty ∧
      (∀ p ∈ P, k < degreeIn G Q p) ∧ (∀ q ∈ Q, k < degreeIn G P q) := by
  classical
  let H := G.between (A : Set V) (B : Set V)
  have hpositive : 2 * (k : ℝ) * (A ∪ B).card < degreeMass H (A ∪ B) := by
    rw [degreeMass_between_union G A B hdis, Finset.card_union_of_disjoint hdis, Nat.cast_add]
    linarith
  obtain ⟨C, hCsub, hC, hCdeg⟩ := exists_core_of_positive_excess H (A ∪ B) k hpositive
  let P := C ∩ A
  let Q := C ∩ B
  have hPdeg : ∀ p ∈ P, k < degreeIn G Q p := by
    intro p hp
    obtain ⟨hpC, hpA⟩ := Finset.mem_inter.mp hp
    have hdeg := hCdeg p hpC
    change (k : ℝ) < (degreeIn (G.between (A : Set V) (B : Set V)) C p : ℝ) at hdeg
    rw [degreeIn_between_left G A B C hdis hpA] at hdeg
    exact_mod_cast hdeg
  have hQdeg : ∀ q ∈ Q, k < degreeIn G P q := by
    intro q hq
    obtain ⟨hqC, hqB⟩ := Finset.mem_inter.mp hq
    have hdeg := hCdeg q hqC
    change (k : ℝ) < (degreeIn (G.between (A : Set V) (B : Set V)) C q : ℝ) at hdeg
    rw [degreeIn_between_right G A B C hdis hqB] at hdeg
    exact_mod_cast hdeg
  have hnonempty : P.Nonempty ∧ Q.Nonempty := by
    obtain ⟨z, hz⟩ := hC
    rcases Finset.mem_union.mp (hCsub hz) with hzA | hzB
    · have hzP : z ∈ P := Finset.mem_inter.mpr ⟨hz, hzA⟩
      have hdeg := hPdeg z hzP
      have hle := degreeIn_le_card G Q z
      exact ⟨⟨z, hzP⟩, Finset.card_pos.mp (by omega)⟩
    · have hzQ : z ∈ Q := Finset.mem_inter.mpr ⟨hz, hzB⟩
      have hdeg := hQdeg z hzQ
      have hle := degreeIn_le_card G P z
      exact ⟨Finset.card_pos.mp (by omega), ⟨z, hzQ⟩⟩
  exact ⟨P, Finset.inter_subset_right, Q, Finset.inter_subset_right,
    hnonempty.1, hnonempty.2, hPdeg, hQdeg⟩

end Erdos547

#print axioms Erdos547.exists_bipartite_degree_core
