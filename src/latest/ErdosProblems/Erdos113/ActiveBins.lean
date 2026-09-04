import ErdosProblems.Erdos113.Regularization

open scoped BigOperators

namespace Erdos113ActiveBins

open Erdos113Regular

abbrev ActiveDegreeBin {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] :=
  {i : Fin (degreeBinCount (W := W)) // (degreeBin A i).Nonempty}

lemma activeDegreeBin_nonempty {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (hedge : ∃ x y, A.Adj x y) : Nonempty (ActiveDegreeBin A) := by
  obtain ⟨x, y, hxy⟩ := hedge
  have hxpos : 0 < A.degree x := by
    apply Finset.card_pos.mpr
    exact ⟨y, (A.mem_neighborFinset x y).mpr hxy⟩
  exact ⟨⟨degreeBinIndex A x, ⟨x, mem_degreeBinIndex A x hxpos⟩⟩⟩

lemma cellCount_eq_zero_of_inactive_right {W : Type*} [Fintype W]
    [DecidableEq W] (A : SimpleGraph W) [DecidableRel A.Adj]
    (i j : Fin (degreeBinCount (W := W)))
    (hj : ¬(degreeBin A j).Nonempty) : cellCount A i j = 0 := by
  unfold cellCount
  apply Finset.sum_eq_zero
  intro x _
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun y ↦ ?_⟩
  exact hj ⟨y.1.1, y.1.2⟩

lemma sum_cellCount_active_row {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (i : ActiveDegreeBin A) :
    ∑ j : ActiveDegreeBin A, cellCount A i.1 j.1 =
      ∑ j : Fin (degreeBinCount (W := W)), cellCount A i.1 j := by
  rw [← Finset.sum_subtype
    (Finset.univ.filter fun j : Fin (degreeBinCount (W := W)) ↦
      (degreeBin A j).Nonempty) (by simp) (fun j ↦ cellCount A i.1 j)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : (degreeBin A j).Nonempty
  · simp [hj]
  · simp [hj, cellCount_eq_zero_of_inactive_right A i.1 j hj]

lemma active_binWeight_pos {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (i : ActiveDegreeBin A) :
    0 < (degreeBin A i.1).card * 2 ^ (i.1.val + 1) := by
  exact Nat.mul_pos i.2.card_pos (pow_pos (by omega) _)

lemma exists_active_degree_cell {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (hedge : ∃ x y, A.Adj x y) :
    ∃ i j : Fin (degreeBinCount (W := W)),
      0 < cellCount A i j ∧
      (degreeBin A i).card * 2 ^ (i.val + 1) +
          (degreeBin A j).card * 2 ^ (j.val + 1) ≤
        4 * degreeBinCount (W := W) * cellCount A i j := by
  let : Nonempty (ActiveDegreeBin A) := activeDegreeBin_nonempty A hedge
  have hrow (i : ActiveDegreeBin A) :
      (degreeBin A i.1).card * 2 ^ (i.1.val + 1) ≤
        2 * ∑ j : ActiveDegreeBin A, cellCount A i.1 j.1 := by
    rw [sum_cellCount_active_row A i]
    exact binWeight_le_two_row A i.1
  obtain ⟨i, j, hij⟩ := exists_balanced_cell
    (fun i : ActiveDegreeBin A ↦
      (degreeBin A i.1).card * 2 ^ (i.1.val + 1))
    (fun i j : ActiveDegreeBin A ↦ cellCount A i.1 j.1)
    (fun i j ↦ cellCount_symm A i.1 j.1) hrow
  refine ⟨i.1, j.1, ?_, ?_⟩
  · by_contra! hzero
    have hz : cellCount A i.1 j.1 = 0 := Nat.eq_zero_of_le_zero hzero
    rw [hz, mul_zero] at hij
    have hi := active_binWeight_pos A i
    have hj := active_binWeight_pos A j
    omega
  · calc
      (degreeBin A i.1).card * 2 ^ (i.1.val + 1) +
          (degreeBin A j.1).card * 2 ^ (j.1.val + 1) ≤
          4 * Fintype.card (ActiveDegreeBin A) * cellCount A i.1 j.1 := hij
      _ ≤ 4 * degreeBinCount (W := W) * cellCount A i.1 j.1 := by
        gcongr
        simpa only [Fintype.card_fin] using
          (Fintype.card_subtype_le
            (fun i : Fin (degreeBinCount (W := W)) ↦ (degreeBin A i).Nonempty))

/-- A degree cell can simultaneously be chosen dense and balanced.  Its
edge count loses only the square of the number of dyadic bins, while the
balance inequality is the input needed by the two-sided pruning lemma. -/
lemma exists_dense_active_degree_cell
    {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (hedge : ∃ x y, A.Adj x y) :
    ∃ i j : Fin (degreeBinCount (W := W)),
      0 < cellCount A i j ∧
      A.edgeFinset.card ≤
        (degreeBinCount (W := W)) ^ 2 * cellCount A i j ∧
      (degreeBin A i).card * 2 ^ (i.val + 1) +
          (degreeBin A j).card * 2 ^ (j.val + 1) ≤
        4 * degreeBinCount (W := W) * cellCount A i j := by
  classical
  let L := degreeBinCount (W := W)
  let : Nonempty (Fin L) :=
    ⟨⟨0, by dsimp [L, degreeBinCount]; omega⟩⟩
  let w : Fin L → ℕ := fun i ↦
    (degreeBin A i).card * 2 ^ (i.val + 1)
  obtain ⟨i, _hiuniv, himax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin L)) w Finset.univ_nonempty
  obtain ⟨j, _hjuniv, hjmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin L)) (cellCount A i) Finset.univ_nonempty
  have hLcard : Fintype.card (Fin L) = L := Fintype.card_fin L
  have hrow_le_w (k : Fin L) :
      ∑ x ∈ degreeBin A k, A.degree x ≤ w k := by
    calc
      (∑ x ∈ degreeBin A k, A.degree x) ≤
          ∑ _x ∈ degreeBin A k, 2 ^ (k.val + 1) := by
        apply Finset.sum_le_sum
        intro x hx
        exact (degree_bounds_of_mem_bin A k hx).2.le
      _ = w k := by
        simp [w]
  have htwice_edges_le : 2 * A.edgeFinset.card ≤ L * w i := by
    calc
      2 * A.edgeFinset.card = ∑ x : W, A.degree x :=
        A.sum_degrees_eq_twice_card_edges.symm
      _ = ∑ k : Fin L, ∑ x ∈ degreeBin A k, A.degree x := by
        simpa [L] using (sum_degreeBins_eq_sum_degrees A).symm
      _ ≤ ∑ k : Fin L, w k := by
        apply Finset.sum_le_sum
        intro k _
        exact hrow_le_w k
      _ ≤ ∑ _k : Fin L, w i := by
        apply Finset.sum_le_sum
        intro k hk
        exact himax k hk
      _ = L * w i := by simp [hLcard]
  have hwi_row : w i ≤ 2 * ∑ k : Fin L, cellCount A i k := by
    simpa [w, L] using binWeight_le_two_row A i
  have hrow_cell : ∑ k : Fin L, cellCount A i k ≤ L * cellCount A i j := by
    calc
      (∑ k : Fin L, cellCount A i k) ≤
          ∑ _k : Fin L, cellCount A i j := by
        apply Finset.sum_le_sum
        intro k hk
        exact hjmax k hk
      _ = L * cellCount A i j := by simp [hLcard]
  have hdense_twice :
      2 * A.edgeFinset.card ≤
        2 * (L ^ 2 * cellCount A i j) := by
    calc
      2 * A.edgeFinset.card ≤ L * w i := htwice_edges_le
      _ ≤ L * (2 * ∑ k : Fin L, cellCount A i k) :=
        Nat.mul_le_mul_left L hwi_row
      _ ≤ L * (2 * (L * cellCount A i j)) := by
        gcongr
      _ = 2 * (L ^ 2 * cellCount A i j) := by ring
  have hdense : A.edgeFinset.card ≤ L ^ 2 * cellCount A i j := by
    omega
  have hedgepos : 0 < A.edgeFinset.card := by
    obtain ⟨x, y, hxy⟩ := hedge
    apply Finset.card_pos.mpr
    exact ⟨s(x, y), by simpa using hxy⟩
  have hcellpos : 0 < cellCount A i j := by
    by_contra! hz
    have hz' : cellCount A i j = 0 := Nat.eq_zero_of_le_zero hz
    rw [hz', mul_zero] at hdense
    omega
  have hwj : w j ≤ w i := himax j (Finset.mem_univ _)
  have hbalanced : w i + w j ≤ 4 * L * cellCount A i j := by
    calc
      w i + w j ≤ 2 * w i := by omega
      _ ≤ 4 * ∑ k : Fin L, cellCount A i k := by omega
      _ ≤ 4 * (L * cellCount A i j) := Nat.mul_le_mul_left 4 hrow_cell
      _ = 4 * L * cellCount A i j := by ring
  refine ⟨i, j, hcellpos, ?_, ?_⟩
  · simpa [L] using hdense
  · simpa [w, L] using hbalanced

end Erdos113ActiveBins
