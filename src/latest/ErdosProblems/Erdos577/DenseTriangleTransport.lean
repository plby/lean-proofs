import ErdosProblems.Erdos577.DenseTriangleModel
import ErdosProblems.Erdos577.DenseOutsideTransport
import ErdosProblems.Erdos577.DiagonalDegrees
import ErdosProblems.Erdos577.Replacements

/-! Exact diamond rows and strict gains in the original feasible chain. -/

namespace Erdos577.DenseTriangle

open Finset Function Unattached
open scoped BigOperators

lemma triangleCount_eq_sum (m : ℕ) :
    DenseOutside.triangleCount m =
      ∑ i : Fin 3, ∑ j : Fin 4, (m.testBit (4 * (i.val + 1) + j.val)).toNat := by
  simp [DenseOutside.triangleCount, List.range_succ, Fin.sum_univ_succ]
  omega

lemma DiamondRows.triangleCount {diagonal : Fin 4} {m : ℕ} (h : DiamondRows diagonal m) :
    DenseOutside.triangleCount m = 10 := by
  obtain ⟨h0, h3, low, hrows⟩ := h
  rw [triangleCount_eq_sum]
  simp_rw [hrows]
  fin_cases diagonal <;> fin_cases low <;> first | contradiction | decide +kernel

lemma DiamondRows.oldEdges {diagonal : Fin 4} {m : ℕ} (h : DiamondRows diagonal m) :
    Unattached.oldEdges diagonal = 5 := by
  obtain ⟨h0, h3, _⟩ := h
  fin_cases diagonal <;> first | contradiction | decide +kernel

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Positive.transport (c : TriangleChain G) (q : Quadrilateral G)
    (hd : Disjoint c.remainder q.support) (h : Positive (diagonal q) (encoded c q).val) :
    StrictImprovement G (c.remainder ∪ q.support) (edgeCount G q.support) := by
  have hg := h.image (modelCopy c q hd)
  rw [modelCopy_image, oldEdges_diagonal] at hg
  exact hg

lemma triangle_bit (c : TriangleChain G) (q : Quadrilateral G) (i : Fin 3) (j : Fin 4) :
    (encoded c q).val.testBit (4 * (i.val + 1) + j.val) =
      decide (G.Adj (c.triangleTuple i) (q j)) := by
  have he := encoded_bit c q (Fin.natAdd 1 i) j
  rw [c.remainderTuple_triangle] at he
  simpa only [Fin.val_natAdd, Nat.add_comm i.val 1] using he

lemma full_row_degree (c : TriangleChain G) (q : Quadrilateral G) (i : Fin 3)
    (h : ∀ j : Fin 4, (encoded c q).val.testBit (4 * (i.val + 1) + j.val) = true) :
    degreeIn G (c.triangleTuple i) q.support = 4 := by
  rw [← q.card_support]
  apply (degreeIn_eq_card_iff _ _).mpr
  intro v hv
  obtain ⟨j, rfl⟩ := (q.mem_support v).mp hv
  have hj := h j
  rw [triangle_bit] at hj
  exact of_decide_eq_true hj

lemma DiamondRows.full_pair (c : TriangleChain G) (q : Quadrilateral G)
    (h : DiamondRows (diagonal q) (encoded c q).val) :
    ∃ u ∈ c.triangle, ∃ v ∈ c.triangle, u ≠ v ∧
      degreeIn G u q.support = 4 ∧ degreeIn G v q.support = 4 := by
  obtain ⟨_, _, low, hrows⟩ := h
  have hp : ∃ i j : Fin 3, i ≠ j ∧ i ≠ low ∧ j ≠ low := by
    fin_cases low
    · exact ⟨1, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 1, by decide, by decide, by decide⟩
  obtain ⟨i, j, hij, hil, hjl⟩ := hp
  refine ⟨c.triangleTuple i, c.triangleTuple_mem i, c.triangleTuple j,
    c.triangleTuple_mem j, fun he ↦ hij (c.triangleTuple.injective he), ?_, ?_⟩
  · exact full_row_degree c q i (fun k ↦ by rw [hrows, if_neg hil])
  · exact full_row_degree c q j (fun k ↦ by rw [hrows, if_neg hjl])

lemma DiamondRows.exact_shape (c : TriangleChain G) (q : Quadrilateral G)
    (h : DiamondRows (diagonal q) (encoded c q).val) :
    ∃ low ∈ c.triangle,
      (∀ j : Fin 4, G.Adj low (q j) ↔ G.Adj (q j) (q (j + 2))) ∧
      ∀ v ∈ c.triangle, v ≠ low → degreeIn G v q.support = 4 := by
  obtain ⟨_, _, low, hrows⟩ := h
  refine ⟨c.triangleTuple low, c.triangleTuple_mem low, ?_, ?_⟩
  · intro j
    have he := hrows low j
    rw [triangle_bit, if_pos rfl] at he
    rw [← q.diagonal_bit_iff]
    exact ⟨fun h ↦ by rw [← he]; exact decide_eq_true h,
      fun h ↦ of_decide_eq_true (he.trans h)⟩
  · intro v hv hne
    rw [← c.triangleTuple_support] at hv
    obtain ⟨i, rfl⟩ := (mem_tupleSupport _ _).mp hv
    have hil : i ≠ low := fun h ↦ hne (congrArg c.triangleTuple h)
    exact full_row_degree c q i (fun j ↦ by rw [hrows, if_neg hil])

end Erdos577.DenseTriangle
