import ErdosProblems.Erdos113.ActiveBins
import ErdosProblems.Erdos113.Pruning
import ErdosProblems.Erdos113.BipartiteGraph

open scoped BigOperators

namespace Erdos113CellPruning

noncomputable section

open Erdos113Regular Erdos113ActiveBins Erdos113BipartiteGraph

abbrev BinVertex {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i : Fin (degreeBinCount (W := W))) := ↑(degreeBin A i)

noncomputable def cellEdges {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i j : Fin (degreeBinCount (W := W))) :
    Finset (BinVertex A i × BinVertex A j) :=
  Finset.univ.filter fun p ↦ A.Adj p.1.1 p.2.1

@[simp] lemma mem_cellEdges {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i j : Fin (degreeBinCount (W := W)))
    (p : BinVertex A i × BinVertex A j) :
    p ∈ cellEdges A i j ↔ A.Adj p.1.1 p.2.1 := by
  simp [cellEdges]

noncomputable def cellEdgesEquivSigma {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i j : Fin (degreeBinCount (W := W))) :
    ↑(cellEdges A i j) ≃ (Σ x : BinVertex A i, BinNeighbor A x.1 j) where
  toFun p := ⟨p.1.1, ⟨p.1.2, (mem_cellEdges A i j p.1).mp p.2⟩⟩
  invFun p := ⟨(p.1, p.2.1), (mem_cellEdges A i j _).mpr p.2.2⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by rfl

lemma card_cellEdges {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i j : Fin (degreeBinCount (W := W))) :
    (cellEdges A i j).card = cellCount A i j := by
  rw [← Fintype.card_coe]
  rw [show cellCount A i j = Fintype.card
      (Σ x : BinVertex A i, BinNeighbor A x.1 j) by
    simp only [cellCount, Fintype.card_sigma]]
  exact Fintype.card_congr (cellEdgesEquivSigma A i j)

noncomputable def cellThreshold (cap L : ℕ) : ℕ :=
  ⌈(cap : ℝ) / (16 * L : ℕ)⌉₊

lemma cellThreshold_pos {cap L : ℕ} (hcap : 0 < cap) (hL : 0 < L) :
    0 < cellThreshold cap L := by
  rw [cellThreshold, Nat.ceil_pos]
  positivity

lemma cast_cellThreshold_sub_one_le {cap L : ℕ} (hcap : 0 < cap)
    (hL : 0 < L) :
    ((cellThreshold cap L - 1 : ℕ) : ℝ) ≤ (cap : ℝ) / (16 * L : ℕ) := by
  have htpos : 0 < cellThreshold cap L := cellThreshold_pos hcap hL
  have hlt := Nat.ceil_lt_add_one
    (show 0 ≤ (cap : ℝ) / (16 * L : ℕ) by positivity)
  change (cellThreshold cap L : ℝ) < (cap : ℝ) / (16 * L : ℕ) + 1 at hlt
  rw [Nat.cast_sub (by omega : 1 ≤ cellThreshold cap L), Nat.cast_one]
  linarith

lemma cap_div_le_cast_cellThreshold {cap L : ℕ} :
    (cap : ℝ) / (16 * L : ℕ) ≤ (cellThreshold cap L : ℝ) := by
  exact Nat.le_ceil _

theorem exists_pruned_cell {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (hedge : ∃ x y, A.Adj x y) :
    ∃ (i j : Fin (degreeBinCount (W := W)))
      (D : Finset (BinVertex A i × BinVertex A j)),
      D ⊆ cellEdges A i j ∧ D.Nonempty ∧
      A.edgeFinset.card ≤
        2 * (degreeBinCount (W := W)) ^ 2 * D.card ∧
      (∀ x : BinVertex A i,
        (D ∩ leftFiber (cellEdges A i j) x).Nonempty →
          cellThreshold (2 ^ (i.val + 1)) (degreeBinCount (W := W)) ≤
            (leftFiber D x).card) ∧
      (∀ y : BinVertex A j,
        (D ∩ rightFiber (cellEdges A i j) y).Nonempty →
          cellThreshold (2 ^ (j.val + 1)) (degreeBinCount (W := W)) ≤
            (rightFiber D y).card) := by
  classical
  obtain ⟨i, j, hcellpos, hcellDense, hweight⟩ :=
    exists_dense_active_degree_cell A hedge
  let C := cellEdges A i j
  let L := degreeBinCount (W := W)
  let tL := cellThreshold (2 ^ (i.val + 1)) L
  let tR := cellThreshold (2 ^ (j.val + 1)) L
  let fiber : (BinVertex A i ⊕ BinVertex A j) →
      Finset (BinVertex A i × BinVertex A j) :=
    Sum.elim (leftFiber C) (rightFiber C)
  let threshold : (BinVertex A i ⊕ BinVertex A j) → ℕ :=
    Sum.elim (fun _ ↦ tL) (fun _ ↦ tR)
  obtain ⟨D, hDsub, hDcard, hDstab⟩ :=
    Erdos113Pruning.exists_pruned_indexed C Finset.univ fiber threshold
  have hLpos : 0 < L := by dsimp [L, degreeBinCount]; omega
  have hcost : ((∑ k : BinVertex A i ⊕ BinVertex A j,
      (threshold k - 1) : ℕ) : ℝ) ≤ (C.card : ℝ) / 4 := by
    have htL := cast_cellThreshold_sub_one_le (cap := 2 ^ (i.val + 1)) (L := L)
      (pow_pos (by omega) _) hLpos
    have htR := cast_cellThreshold_sub_one_le (cap := 2 ^ (j.val + 1)) (L := L)
      (pow_pos (by omega) _) hLpos
    have hfirst : ((∑ k : BinVertex A i ⊕ BinVertex A j,
        (threshold k - 1) : ℕ) : ℝ) ≤
        ((degreeBin A i).card * 2 ^ (i.val + 1) +
          (degreeBin A j).card * 2 ^ (j.val + 1) : ℕ) / (16 * L : ℕ) := by
      simp only [Fintype.sum_sum_type, threshold, tL, tR, Sum.elim_inl,
        Sum.elim_inr, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_mul]
      have hi : ((degreeBin A i).card : ℝ) * (tL - 1 : ℕ) ≤
          ((degreeBin A i).card : ℝ) *
            ((2 ^ (i.val + 1) : ℕ) : ℝ) / (16 * L : ℕ) := by
        calc
          ((degreeBin A i).card : ℝ) * (tL - 1 : ℕ) ≤
              ((degreeBin A i).card : ℝ) *
                (((2 ^ (i.val + 1) : ℕ) : ℝ) / (16 * L : ℕ)) := by gcongr
          _ = _ := by ring
      have hj : ((degreeBin A j).card : ℝ) * (tR - 1 : ℕ) ≤
          ((degreeBin A j).card : ℝ) *
            ((2 ^ (j.val + 1) : ℕ) : ℝ) / (16 * L : ℕ) := by
        calc
          ((degreeBin A j).card : ℝ) * (tR - 1 : ℕ) ≤
              ((degreeBin A j).card : ℝ) *
                (((2 ^ (j.val + 1) : ℕ) : ℝ) / (16 * L : ℕ)) := by gcongr
          _ = _ := by ring
      push_cast
      calc
        ((degreeBin A i).card : ℝ) * (tL - 1 : ℕ) +
            ((degreeBin A j).card : ℝ) * (tR - 1 : ℕ) ≤
            ((degreeBin A i).card : ℝ) * (2 ^ (i.val + 1) : ℕ) /
                (16 * L : ℕ) +
              ((degreeBin A j).card : ℝ) * (2 ^ (j.val + 1) : ℕ) /
                (16 * L : ℕ) := add_le_add hi hj
        _ = (((degreeBin A i).card : ℝ) * (2 ^ (i.val + 1) : ℕ) +
              ((degreeBin A j).card : ℝ) * (2 ^ (j.val + 1) : ℕ)) /
              (16 * L : ℕ) := by ring
        _ = (((degreeBin A i).card : ℝ) * (2 : ℝ) ^ (i.val + 1) +
              ((degreeBin A j).card : ℝ) * (2 : ℝ) ^ (j.val + 1)) /
              (16 * (L : ℝ)) := by norm_num
    have hweightR :
        (((degreeBin A i).card * 2 ^ (i.val + 1) +
          (degreeBin A j).card * 2 ^ (j.val + 1) : ℕ) : ℝ) ≤
          4 * L * (C.card : ℝ) := by
      exact_mod_cast (show
        (degreeBin A i).card * 2 ^ (i.val + 1) +
            (degreeBin A j).card * 2 ^ (j.val + 1) ≤
          4 * L * C.card by
        simpa [L, C, card_cellEdges A i j] using hweight)
    calc
      ((∑ k : BinVertex A i ⊕ BinVertex A j,
          (threshold k - 1) : ℕ) : ℝ) ≤
          ((degreeBin A i).card * 2 ^ (i.val + 1) +
            (degreeBin A j).card * 2 ^ (j.val + 1) : ℕ) /
              (16 * L : ℕ) := hfirst
      _ ≤ (C.card : ℝ) / 4 := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < (16 * L : ℕ))).2
        calc
          (((degreeBin A i).card * 2 ^ (i.val + 1) +
            (degreeBin A j).card * 2 ^ (j.val + 1) : ℕ) : ℝ) ≤
              4 * L * (C.card : ℝ) := hweightR
          _ = (C.card : ℝ) / 4 * ((16 * L : ℕ) : ℝ) := by
            push_cast
            ring
  have hCpos : 0 < C.card := by
    simpa [C, card_cellEdges A i j] using hcellpos
  have hDnonempty : D.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hDEmpty
    have hDzero : D.card = 0 := by simp [hDEmpty]
    have hcardR : (C.card : ℝ) ≤
        ((∑ k : BinVertex A i ⊕ BinVertex A j,
          (threshold k - 1) : ℕ) : ℝ) := by
      exact_mod_cast (by simpa [hDzero] using hDcard)
    have hCposR : (0 : ℝ) < C.card := by exact_mod_cast hCpos
    nlinarith
  have hCDreal : (C.card : ℝ) ≤ 2 * (D.card : ℝ) := by
    have hDcardR : (C.card : ℝ) ≤
        (D.card : ℝ) +
          ((∑ k : BinVertex A i ⊕ BinVertex A j,
            (threshold k - 1) : ℕ) : ℝ) := by
      exact_mod_cast hDcard
    nlinarith
  have hCD : C.card ≤ 2 * D.card := by exact_mod_cast hCDreal
  have hDenseD : A.edgeFinset.card ≤
      2 * (degreeBinCount (W := W)) ^ 2 * D.card := by
    calc
      A.edgeFinset.card ≤
          (degreeBinCount (W := W)) ^ 2 * cellCount A i j := hcellDense
      _ = (degreeBinCount (W := W)) ^ 2 * C.card := by
        change (degreeBinCount (W := W)) ^ 2 * cellCount A i j =
          (degreeBinCount (W := W)) ^ 2 * (cellEdges A i j).card
        rw [card_cellEdges]
      _ ≤ (degreeBinCount (W := W)) ^ 2 * (2 * D.card) :=
        Nat.mul_le_mul_left _ hCD
      _ = 2 * (degreeBinCount (W := W)) ^ 2 * D.card := by ring
  have hleft (x : BinVertex A i) :
      D ∩ leftFiber C x = leftFiber D x := by
    ext p
    simp only [Finset.mem_inter, mem_leftFiber]
    constructor
    · exact fun hp ↦ ⟨hp.1, hp.2.2⟩
    · exact fun hp ↦ ⟨hp.1, hDsub hp.1, hp.2⟩
  have hright (y : BinVertex A j) :
      D ∩ rightFiber C y = rightFiber D y := by
    ext p
    simp only [Finset.mem_inter, mem_rightFiber]
    constructor
    · exact fun hp ↦ ⟨hp.1, hp.2.2⟩
    · exact fun hp ↦ ⟨hp.1, hDsub hp.1, hp.2⟩
  refine ⟨i, j, D, hDsub, hDnonempty, hDenseD, ?_, ?_⟩
  · intro x hx
    have hs := hDstab (Sum.inl x) (Finset.mem_univ _) hx
    change tL ≤ (D ∩ leftFiber C x).card at hs
    rw [hleft x] at hs
    simpa [threshold, tL, fiber, L] using hs
  · intro y hy
    have hs := hDstab (Sum.inr y) (Finset.mem_univ _) hy
    change tR ≤ (D ∩ rightFiber C y).card at hs
    rw [hright y] at hs
    simpa [threshold, tR, fiber, L] using hs

lemma card_leftFiber_le_degree {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i j : Fin (degreeBinCount (W := W)))
    (D : Finset (BinVertex A i × BinVertex A j))
    (hD : D ⊆ cellEdges A i j) (x : BinVertex A i) :
    (leftFiber D x).card ≤ A.degree x.1 := by
  let f : ↑(leftFiber D x) → A.neighborSet x.1 := fun p ↦
    ⟨p.1.2.1, by
      have hp := (mem_leftFiber D x p.1).mp p.2
      have hadj := (mem_cellEdges A i j p.1).mp (hD hp.1)
      simpa [hp.2] using hadj⟩
  have hf : Function.Injective f := by
    intro p q hpq
    have hpqW := congrArg Subtype.val hpq
    change p.1.2.1 = q.1.2.1 at hpqW
    apply Subtype.ext
    apply Prod.ext
    · exact ((mem_leftFiber D x p.1).mp p.2).2.trans
        ((mem_leftFiber D x q.1).mp q.2).2.symm
    · apply Subtype.ext
      exact hpqW
  rw [← Fintype.card_coe, ← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_le_of_injective f hf

lemma card_rightFiber_le_degree {W : Type*} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj]
    (i j : Fin (degreeBinCount (W := W)))
    (D : Finset (BinVertex A i × BinVertex A j))
    (hD : D ⊆ cellEdges A i j) (y : BinVertex A j) :
    (rightFiber D y).card ≤ A.degree y.1 := by
  let f : ↑(rightFiber D y) → A.neighborSet y.1 := fun p ↦
    ⟨p.1.1.1, by
      have hp := (mem_rightFiber D y p.1).mp p.2
      have hadj := (mem_cellEdges A i j p.1).mp (hD hp.1)
      simpa [hp.2] using hadj.symm⟩
  have hf : Function.Injective f := by
    intro p q hpq
    have hpqW := congrArg Subtype.val hpq
    change p.1.1.1 = q.1.1.1 at hpqW
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact hpqW
    · exact ((mem_rightFiber D y p.1).mp p.2).2.trans
        ((mem_rightFiber D y q.1).mp q.2).2.symm
  rw [← Fintype.card_coe, ← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_le_of_injective f hf



end

end Erdos113CellPruning
