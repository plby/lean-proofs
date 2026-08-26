/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A telescoping product estimate for characteristic-function comparisons.
Formal proof: Codex.
-/
import Mathlib

namespace Erdos521

open scoped BigOperators

theorem norm_prod_le_one {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) : ‖∏ i ∈ s, f i‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one (fun _ _ ↦ norm_nonneg _) hf

theorem norm_prod_sub_prod_le_sum {ι : Type*} (s : Finset ι) (f g : ι → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hfs : ∀ j ∈ s, ‖f j‖ ≤ 1 := fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)
    have hgs : ∀ j ∈ s, ‖g j‖ ≤ 1 := fun j hj ↦ hg j (Finset.mem_insert_of_mem hj)
    have hdiff := ih hfs hgs
    have hfprod := norm_prod_le_one s f hfs
    have hgi := hg i (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    calc
      ‖f i * (∏ j ∈ s, f j) - g i * ∏ j ∈ s, g j‖ =
          ‖(f i - g i) * (∏ j ∈ s, f j) + g i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j)‖ := by
        congr 1
        ring
      _ ≤ ‖f i - g i‖ * ‖∏ j ∈ s, f j‖ +
          ‖g i‖ * ‖(∏ j ∈ s, f j) - ∏ j ∈ s, g j‖ := by
        simpa only [norm_mul] using norm_add_le
          ((f i - g i) * (∏ j ∈ s, f j)) (g i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j))
      _ ≤ _ := add_le_add (mul_le_of_le_one_right (norm_nonneg _) hfprod)
        ((mul_le_of_le_one_left (norm_nonneg _) hgi).trans hdiff)

end Erdos521
