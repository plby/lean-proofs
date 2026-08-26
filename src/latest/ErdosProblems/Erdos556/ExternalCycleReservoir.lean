import ErdosProblems.Erdos556.IndexedCyclePaths

/-!
# The exterior-reservoir geometry

Vertices of one parity in a short cycle interval can serve as one side
of a reservoir. Its two extreme vertices are joined by the complementary
cycle arc, which is long and avoids the other reservoir vertices.
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_long_path_outside_cycle_interval {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {w : V} (c : G.Walk w w) (hc : c.IsCycle)
    (A : Finset ℕ) (hA : 2 ≤ A.card) (M : ℕ) (hM : M < c.length)
    (hAM : ∀ i ∈ A, i ≤ M) (hpar : ∀ i ∈ A, ∀ j ∈ A, i % 2 = j % 2)
    (Y : Finset V) (hY : ∀ y ∈ Y, y ∉ c.support) :
    ∃ u ∈ A.image c.getVert, ∃ v ∈ A.image c.getVert, u ≠ v ∧
      ∃ p : G.Walk u v, p.IsPath ∧ c.length ≤ p.length + M ∧
        p.length % 2 = c.length % 2 ∧
        ∀ z ∈ p.support, z ∈ A.image c.getVert ∪ Y → z = u ∨ z = v := by
  classical
  have hAnon : A.Nonempty := card_pos.mp (by omega)
  let i := A.min' hAnon
  let j := A.max' hAnon
  have hiA : i ∈ A := A.min'_mem hAnon
  have hjA : j ∈ A := A.max'_mem hAnon
  have hij : i < j := A.min'_lt_max'_of_card (by omega)
  have hiM := hAM i hiA
  have hjM := hAM j hjA
  have huv : c.getVert j ≠ c.getVert i := by
    intro heq
    have h := hc.getVert_injOn' (by change j ≤ c.length - 1; omega)
      (by change i ≤ c.length - 1; omega) heq
    omega
  refine ⟨c.getVert j, mem_image.mpr ⟨j, hjA, rfl⟩,
    c.getVert i, mem_image.mpr ⟨i, hiA, rfl⟩, huv,
    cycleOutsideArc c i j, cycleOutsideArc_isPath c hc i j hij (by omega), ?_, ?_, ?_⟩
  · rw [cycleOutsideArc_length c i j (by omega)]
    omega
  · rw [cycleOutsideArc_length c i j (by omega)]
    have h := hpar i hiA j hjA
    omega
  · intro z hz hzR
    rcases mem_union.mp hzR with hzA | hzY
    · obtain ⟨a, haA, haz⟩ := mem_image.mp hzA
      have hia : i ≤ a := A.min'_le a haA
      have haj : a ≤ j := A.le_max' a haA
      have haz' : c.getVert a ∈ (cycleOutsideArc c i j).support := haz ▸ hz
      rcases cycleOutsideArc_meets_interval_only_at_ends c hc i j a hia haj (by omega) haz'
        with hai | haj
      · right
        rw [← haz, hai]
      · left
        rw [← haz, haj]
    · exact (hY z hzY (cycleOutsideArc_support_subset c i j (by omega) (by omega) hz)).elim

#print axioms exists_long_path_outside_cycle_interval

end Erdos556
