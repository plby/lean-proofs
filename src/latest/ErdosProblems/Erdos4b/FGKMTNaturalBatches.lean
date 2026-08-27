/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTLabelRestriction

/-! # Natural-stage edge families for a finite categorical partition -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

variable {I Ω α : Type*} [Fintype I] [Fintype Ω] [DecidableEq α] {m : ℕ}

def numberedBatchLabels (a : I → Option (Fin m)) (j : ℕ) : Finset I :=
  if h : j < m then batchLabels a ⟨j, h⟩ else ∅

theorem numberedBatchLabels_of_lt (a : I → Option (Fin m)) {j : ℕ} (hj : j < m) :
    numberedBatchLabels a j = batchLabels a ⟨j, hj⟩ := dif_pos hj

theorem numberedBatchLabels_of_le (a : I → Option (Fin m)) {j : ℕ} (hj : m ≤ j) :
    numberedBatchLabels a j = ∅ := dif_neg (Nat.not_lt.mpr hj)

theorem numberedBatchLabels_disjoint (a : I → Option (Fin m)) {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (numberedBatchLabels a j) (numberedBatchLabels a k) := by
  by_cases hj : j < m
  · rw [numberedBatchLabels_of_lt a hj]
    by_cases hk : k < m
    · rw [numberedBatchLabels_of_lt a hk]
      exact batchLabels_disjoint a (fun h => hjk (congrArg Fin.val h))
    · rw [numberedBatchLabels_of_le a (Nat.le_of_not_gt hk)]
      exact Finset.disjoint_empty_right _
  · rw [numberedBatchLabels_of_le a (Nat.le_of_not_gt hj)]
    exact Finset.disjoint_empty_left _

theorem numberedBatchLabels_card_le (a : I → Option (Fin m)) (j : ℕ) :
    (numberedBatchLabels a j).card ≤ Fintype.card I := Finset.card_le_univ _

def numberedBatchFamily (F : FiniteEdgeFamily I Ω α) (a : I → Option (Fin m)) (j : ℕ) :
    FiniteEdgeFamily (numberedBatchLabels a j) Ω α :=
  F.restrictLabels (numberedBatchLabels a j)

theorem numberedBatchFamily_vertices (F : FiniteEdgeFamily I Ω α)
    (a : I → Option (Fin m)) (j : ℕ) : (F.numberedBatchFamily a j).vertices = F.vertices := rfl

theorem numberedBatchFamily_rank (F : FiniteEdgeFamily I Ω α)
    (a : I → Option (Fin m)) (j : ℕ) : (F.numberedBatchFamily a j).rank = F.rank := rfl

theorem numberedBatchFamily_vertexMass (F : FiniteEdgeFamily I Ω α)
    (a : I → Option (Fin m)) (j : ℕ) (i : numberedBatchLabels a j) (v : α) :
    (F.numberedBatchFamily a j).vertexMass i v = F.vertexMass i.val v := rfl

theorem numberedBatchFamily_codegree_le (F : FiniteEdgeFamily I Ω α)
    (a : I → Option (Fin m)) (j : ℕ) (v w : α) :
    (F.numberedBatchFamily a j).codegree v w ≤ F.codegree v w :=
  F.restrictLabels_codegree_le _ v w

end

end Erdos4b.FGKMT.FiniteEdgeFamily
