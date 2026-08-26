import Mathlib

/-! # Finite greedy bucketing (Lemma 3.4 of the selected source) -/

namespace Erdos856b

open scoped BigOperators

variable {α : Type*}

theorem exists_weight_subset {S : Finset α} {w : α → ℝ} {z δ : ℝ}
    (hz : 0 < z) (hw : ∀ x ∈ S, w x < δ) (hS : z ≤ ∑ x ∈ S, w x) :
    ∃ T : Finset α, T ⊆ S ∧ z ≤ ∑ x ∈ T, w x ∧ (∑ x ∈ T, w x) < z + δ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at hS; linarith
  | @insert x S hx ih =>
    by_cases htail : z ≤ ∑ y ∈ S, w y
    · obtain ⟨T, hT, hlo, hhi⟩ := ih (fun y hy => hw y (Finset.mem_insert_of_mem hy)) htail
      exact ⟨T, hT.trans (Finset.subset_insert _ _), hlo, hhi⟩
    · refine ⟨insert x S, Finset.Subset.refl _, hS, ?_⟩
      rw [Finset.sum_insert hx]
      have hxδ := hw x (Finset.mem_insert_self _ _)
      linarith

/-- Disjoint groups with prescribed lower mass and controlled overshoot. -/
theorem exists_weight_buckets (t : ℕ) {S : Finset α} {w : α → ℝ} {z δ : ℝ}
    (hz : 0 < z) (hδ : 0 < δ) (hw : ∀ x ∈ S, w x < δ)
    (hS : t * (z + δ) ≤ ∑ x ∈ S, w x) :
    ∃ B : Fin t → Finset α,
      (∀ i, B i ⊆ S) ∧ (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      ∀ i, z ≤ ∑ x ∈ B i, w x ∧ (∑ x ∈ B i, w x) < z + δ := by
  classical
  induction t generalizing S with
  | zero => exact ⟨Fin.elim0, by simp, by simp, by simp⟩
  | succ t ih =>
    have hstart : z ≤ ∑ x ∈ S, w x := by
      have ht : (0 : ℝ) ≤ t := by positivity
      push_cast at hS
      nlinarith
    obtain ⟨T, hTS, hTlo, hThi⟩ := exists_weight_subset hz hw hstart
    have hremaining : t * (z + δ) ≤ ∑ x ∈ S \ T, w x := by
      have hsum := Finset.sum_sdiff hTS (f := w)
      push_cast at hS
      linarith
    obtain ⟨B, hBS, hBB, hBw⟩ := ih (fun x hx => hw x (Finset.mem_sdiff.mp hx).1) hremaining
    refine ⟨Fin.cons T B, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases hTS (fun j => ?_) i
      exact (hBS j).trans Finset.sdiff_subset
    · intro i j hij
      refine Fin.cases (fun j hij => ?_) (fun i j hij => ?_) i j hij
      · refine Fin.cases (fun h => (h rfl).elim) (fun j _ => ?_) j hij
        simp only [Fin.cons_zero, Fin.cons_succ]
        exact Finset.disjoint_left.mpr (fun x hxT hxB =>
          (Finset.mem_sdiff.mp (hBS j hxB)).2 hxT)
      · refine Fin.cases (fun _ => ?_) (fun j h => ?_) j hij
        · simp only [Fin.cons_succ, Fin.cons_zero]
          exact Finset.disjoint_left.mpr (fun x hxB hxT =>
            (Finset.mem_sdiff.mp (hBS i hxB)).2 hxT)
        · simpa only [Fin.cons_succ] using hBB i j (fun h' => h (congrArg Fin.succ h'))
    · intro i
      exact Fin.cases ⟨hTlo, hThi⟩ hBw i

end Erdos856b
