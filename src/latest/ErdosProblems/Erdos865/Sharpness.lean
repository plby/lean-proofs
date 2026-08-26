/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Licensed under the Apache License, Version 2.0; see LICENSE.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 865.
Informal authors: Ricky Cipollini and GPT-5.5 Pro.
Formal proof: Aristotle; submitted by Ricky Cipollini.
Source: https://www.erdosproblems.com/865#post-7378
https://github.com/mrricky22/erdos-865-lean/tree/54bfae36c1b0384737bc23b18180bdf001816c5d
Original toolchain: Lean/Mathlib 4.28.0.
Original Mathlib commit: 8f9d9cff6bd728b17a24e163c9402775d9e6a365.
This is the complete July formalization, with the coarse theorem replaced by induction.
-/
import ErdosProblems.Erdos865.Defs

set_option linter.mathlibStandardSet false

namespace Erdos865

/-- The sharpness construction `A = [M, 2M] ∪ [4M, 8M]`. -/
def sharpSet (M : ℕ) : Finset ℕ := Finset.Icc M (2 * M) ∪ Finset.Icc (4 * M) (8 * M)

/-- The construction sits inside `[1, 8M]` (for `M ≥ 1`). -/
theorem sharpSet_subset {M : ℕ} (hM : 1 ≤ M) : sharpSet M ⊆ Finset.Icc 1 (8 * M) :=
  Finset.union_subset (Finset.Icc_subset_Icc (by linarith) (by linarith))
    (Finset.Icc_subset_Icc (by linarith) (by linarith))

/-- The construction has `5M + 2` elements. -/
theorem sharpSet_card {M : ℕ} (hM : 1 ≤ M) : (sharpSet M).card = 5 * M + 2 := by
  have hdisj : Disjoint (Finset.Icc M (2 * M)) (Finset.Icc (4 * M) (8 * M)) :=
    Finset.disjoint_left.mpr fun x hx₁ hx₂ => by
      simp only [Finset.mem_Icc] at hx₁ hx₂; omega
  rw [sharpSet, Finset.card_union_of_disjoint hdisj, Nat.card_Icc, Nat.card_Icc]
  omega

/-- The construction is triple-free. -/
theorem sharpSet_tripleFree (M : ℕ) : IsTripleFree (sharpSet M) := by
  intro h;
  obtain ⟨ a, ha, b, hb, c, hc, hab, hac, hbc, hab', hac', hbc' ⟩ := h;
  unfold sharpSet at *;
  grind

/-- Sharpness: for `N = 8M` with `M ≥ 1` there is a triple-free subset of `[1,N]`
of size `5M + 2`, i.e. with `8 * card = 5 * N + 16`. -/
theorem sharpness {M : ℕ} (hM : 1 ≤ M) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 (8 * M) ∧ IsTripleFree A ∧
      8 * A.card = 5 * (8 * M) + 16 := by
  refine ⟨sharpSet M, sharpSet_subset hM, sharpSet_tripleFree M, ?_⟩
  rw [sharpSet_card hM]; ring

end Erdos865
