/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTScalarReindex

/-! # Nonnegative upper reindexing without a complete prime universe -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem sum_unit_assignments_le_sum_Icc {α : Type*} [Fintype α] [DecidableEq α]
    {p : α → ℕ} (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (B : ℕ) (F : ℕ → ℝ) (hF0 : ∀ n, 0 ≤ F n)
    (hFB : ∀ n, F n ≠ 0 → n ≤ B) :
    (∑ a : α → Option Unit, F (assignmentPrimeProduct p a)) ≤
      ∑ n ∈ Finset.Icc 0 B, F n := by
  classical
  let S := Finset.univ.filter (fun a : α → Option Unit => F (assignmentPrimeProduct p a) ≠ 0)
  have hS : S.image (assignmentPrimeProduct p) ⊆ Finset.Icc 0 B := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hFB _ (Finset.mem_filter.mp ha).2⟩
  calc
    _ = ∑ a ∈ S, F (assignmentPrimeProduct p a) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a _ha
      by_cases hz : F (assignmentPrimeProduct p a) = 0 <;> simp [hz]
    _ = ∑ n ∈ S.image (assignmentPrimeProduct p), F n :=
      (Finset.sum_image (fun a _ha b _hb hab =>
        assignmentPrimeProduct_unit_injective hp hinj hab)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hS (fun n _hn _hnot => hF0 n)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sum_unit_assignments_le_sum_Icc
