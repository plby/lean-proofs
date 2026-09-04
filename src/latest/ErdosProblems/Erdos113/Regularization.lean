import Mathlib

open scoped BigOperators

namespace Erdos113Regular

lemma exists_balanced_cell {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (w : I → ℕ) (e : I → I → ℕ)
    (hsymm : ∀ i j, e i j = e j i)
    (hrow : ∀ i, w i ≤ 2 * ∑ j, e i j) :
    ∃ i j, w i + w j ≤ 4 * Fintype.card I * e i j := by
  by_contra! hnone
  have hsumw : ∑ i, w i ≤ 2 * ∑ i, ∑ j, e i j := by
    calc
      ∑ i, w i ≤ ∑ i, 2 * ∑ j, e i j := by
        apply Finset.sum_le_sum
        intro i _
        exact hrow i
      _ = 2 * ∑ i, ∑ j, e i j := by rw [Finset.mul_sum]
  have hdenom : ∑ i, ∑ j, (w i + w j) =
      2 * Fintype.card I * ∑ i, w i := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    rw [Finset.mul_sum]
    rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Nat.cast_id]
    rw [mul_assoc]
    omega
  have hstrict : 4 * Fintype.card I * ∑ i, ∑ j, e i j <
      ∑ i, ∑ j, (w i + w j) := by
    calc
      4 * Fintype.card I * ∑ i, ∑ j, e i j =
          ∑ i, ∑ j, (4 * Fintype.card I * e i j) := by
        simp_rw [Finset.mul_sum]
      _ < ∑ i, ∑ j, (w i + w j) := by
        apply Finset.sum_lt_sum
        · intro i _
          apply Finset.sum_le_sum
          intro j _
          exact (hnone i j).le
        · classical
          inhabit I
          refine ⟨default, Finset.mem_univ _, ?_⟩
          apply Finset.sum_lt_sum
          · intro j _
            exact (hnone default j).le
          · exact ⟨default, Finset.mem_univ _, hnone default default⟩
  rw [hdenom] at hstrict
  have hreverse : 2 * Fintype.card I * ∑ i, w i ≤
      4 * Fintype.card I * ∑ i, ∑ j, e i j := by
    calc
      2 * Fintype.card I * ∑ i, w i ≤
          2 * Fintype.card I * (2 * ∑ i, ∑ j, e i j) := by gcongr
      _ = 4 * Fintype.card I * ∑ i, ∑ j, e i j := by ring
  omega

noncomputable def degreeBinCount {W : Type*} [Fintype W] : ℕ :=
  Nat.log 2 (Fintype.card W) + 1

noncomputable def degreeBin {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i : Fin (degreeBinCount (W := W))) : Finset W :=
  Finset.univ.filter fun x ↦ 0 < A.degree x ∧ Nat.log 2 (A.degree x) = i.val

lemma mem_degreeBin {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i : Fin (degreeBinCount (W := W))) (x : W) :
    x ∈ degreeBin A i ↔ 0 < A.degree x ∧ Nat.log 2 (A.degree x) = i.val := by
  simp [degreeBin]

def degreeBinIndex {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (x : W) :
    Fin (degreeBinCount (W := W)) :=
  ⟨Nat.log 2 (A.degree x), by
    dsimp [degreeBinCount]
    have hdeg := A.degree_lt_card_verts x
    have hlog := Nat.log_mono_right (b := 2) hdeg.le
    omega⟩

lemma mem_degreeBinIndex {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (x : W) (hx : 0 < A.degree x) :
    x ∈ degreeBin A (degreeBinIndex A x) := by
  rw [mem_degreeBin]
  exact ⟨hx, rfl⟩

lemma sum_degreeBins_eq_sum_degrees
    {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] :
    ∑ i : Fin (degreeBinCount (W := W)),
        ∑ x ∈ degreeBin A i, A.degree x =
      ∑ x : W, A.degree x := by
  classical
  calc
    (∑ i : Fin (degreeBinCount (W := W)),
        ∑ x ∈ degreeBin A i, A.degree x) =
        ∑ i : Fin (degreeBinCount (W := W)),
          ∑ x ∈ (Finset.univ : Finset W) with degreeBinIndex A x = i,
            A.degree x := by
      apply Finset.sum_congr rfl
      intro i _
      rw [degreeBin, Finset.sum_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : 0 < A.degree x
      · by_cases hi : Nat.log 2 (A.degree x) = i.val
        · have hfin : degreeBinIndex A x = i := Fin.ext hi
          simp [hx, hi, hfin]
        · have hfin : degreeBinIndex A x ≠ i := by
            intro h
            exact hi (congrArg Fin.val h)
          simp [hx, hi, hfin]
      · have hz : A.degree x = 0 := Nat.eq_zero_of_not_pos hx
        simp [hz]
    _ = ∑ x : W, A.degree x :=
      Finset.sum_fiberwise (Finset.univ : Finset W)
        (degreeBinIndex A) (fun x ↦ A.degree x)

abbrev BinNeighbor {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (x : W) (j : Fin (degreeBinCount (W := W))) :=
  {y : ↑(degreeBin A j) // A.Adj x y.1}

noncomputable def cellCount {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i j : Fin (degreeBinCount (W := W))) : ℕ :=
  ∑ x : ↑(degreeBin A i), Fintype.card (BinNeighbor A x.1 j)

noncomputable def cellEdgeSigmaSwap {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i j : Fin (degreeBinCount (W := W))) :
    (Σ x : ↑(degreeBin A i), BinNeighbor A x.1 j) ≃
      (Σ y : ↑(degreeBin A j), BinNeighbor A y.1 i) where
  toFun p := ⟨p.2.1, ⟨p.1, p.2.2.symm⟩⟩
  invFun p := ⟨p.2.1, ⟨p.1, p.2.2.symm⟩⟩
  left_inv p := by apply Sigma.ext rfl; rfl
  right_inv p := by apply Sigma.ext rfl; rfl

lemma cellCount_symm {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i j : Fin (degreeBinCount (W := W))) :
    cellCount A i j = cellCount A j i := by
  simp only [cellCount, ← Fintype.card_sigma]
  exact Fintype.card_congr (cellEdgeSigmaSwap A i j)

abbrev NeighborBinFiber {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (x : W) (j : Fin (degreeBinCount (W := W))) :=
  {y : A.neighborSet x // degreeBinIndex A y.1 = j}

noncomputable def binNeighborEquivFiber {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (x : W) (j : Fin (degreeBinCount (W := W))) :
    BinNeighbor A x j ≃ NeighborBinFiber A x j where
  toFun y := ⟨⟨y.1.1, y.2⟩, by
    apply Fin.ext
    exact ((mem_degreeBin A j y.1.1).mp y.1.2).2⟩
  invFun y := by
    have hypos : 0 < A.degree y.1.1 := by
      have : x ∈ A.neighborFinset y.1.1 :=
        (A.mem_neighborFinset y.1.1 x).mpr y.1.2.symm
      exact Finset.card_pos.mpr ⟨x, this⟩
    have hybin : y.1.1 ∈ degreeBin A j := by
      rw [mem_degreeBin]
      exact ⟨hypos, congrArg Fin.val y.2⟩
    exact ⟨⟨y.1.1, hybin⟩, y.1.2⟩
  left_inv y := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; apply Subtype.ext; rfl

lemma sum_cellCount_row {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i : Fin (degreeBinCount (W := W))) :
    ∑ j, cellCount A i j = ∑ x ∈ degreeBin A i, A.degree x := by
  simp only [cellCount]
  rw [Finset.sum_comm]
  calc
    ∑ x : ↑(degreeBin A i), ∑ j,
        Fintype.card (BinNeighbor A x.1 j) =
        ∑ x : ↑(degreeBin A i), ∑ j,
          Fintype.card (NeighborBinFiber A x.1 j) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro j _
      exact Fintype.card_congr (binNeighborEquivFiber A x.1 j)
    _ = ∑ x : ↑(degreeBin A i), A.degree x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Fintype.card_sigma]
      rw [Fintype.card_congr (Equiv.sigmaFiberEquiv
        (fun y : A.neighborSet x.1 ↦ degreeBinIndex A y.1))]
      exact SimpleGraph.card_neighborSet_eq_degree A x.1
    _ = ∑ x ∈ degreeBin A i, A.degree x :=
      Finset.sum_coe_sort (degreeBin A i) (fun x ↦ A.degree x)

lemma degree_bounds_of_mem_bin {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i : Fin (degreeBinCount (W := W))) {x : W} (hx : x ∈ degreeBin A i) :
    2 ^ i.val ≤ A.degree x ∧ A.degree x < 2 ^ (i.val + 1) := by
  rw [mem_degreeBin] at hx
  have hspec := (Nat.log_eq_iff (b := 2) (m := i.val) (n := A.degree x)
    (Or.inr ⟨Nat.one_lt_two, hx.1.ne'⟩)).mp hx.2
  exact hspec

lemma binWeight_le_two_row {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i : Fin (degreeBinCount (W := W))) :
    (degreeBin A i).card * 2 ^ (i.val + 1) ≤ 2 * ∑ j, cellCount A i j := by
  rw [sum_cellCount_row]
  calc
    (degreeBin A i).card * 2 ^ (i.val + 1) =
        ∑ _x ∈ degreeBin A i, 2 * 2 ^ i.val := by
      rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, pow_succ]
      ring
    _ ≤ ∑ x ∈ degreeBin A i, 2 * A.degree x := by
      apply Finset.sum_le_sum
      intro x hx
      exact Nat.mul_le_mul_left 2 (degree_bounds_of_mem_bin A i hx).1
    _ = 2 * ∑ x ∈ degreeBin A i, A.degree x := by
      rw [Finset.mul_sum]

lemma exists_degree_cell {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] :
    ∃ i j : Fin (degreeBinCount (W := W)),
      (degreeBin A i).card * 2 ^ (i.val + 1) +
        (degreeBin A j).card * 2 ^ (j.val + 1) ≤
      4 * degreeBinCount (W := W) * cellCount A i j := by
  let : Nonempty (Fin (degreeBinCount (W := W))) :=
    ⟨⟨0, by dsimp [degreeBinCount]; omega⟩⟩
  simpa using exists_balanced_cell
    (fun i ↦ (degreeBin A i).card * 2 ^ (i.val + 1)) (cellCount A)
      (cellCount_symm A) (binWeight_le_two_row A)

end Erdos113Regular
