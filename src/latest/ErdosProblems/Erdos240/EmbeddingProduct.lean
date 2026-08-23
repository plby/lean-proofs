/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Analysis.Complex.Norm

/-!
# Lower bounds from products over embeddings

These elementary lemmas isolate the last step in a norm-based Liouville
argument.  If a product has absolute value at least one and every factor other
than a distinguished one is at most `H`, then the distinguished factor is at
least the reciprocal of the corresponding power of `H`.
-/

namespace Erdos240.EmbeddingProduct

open scoped BigOperators

/-- The basic estimate when the product has already been split into a
distinguished nonnegative factor and the product of all remaining factors. -/
theorem one_div_pow_card_erase_le_of_one_le_mul_prod
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (i : ι)
    (f : ι → ℝ) (H : ℝ)
    (hH : 1 ≤ H) (hfi : 0 ≤ f i)
    (hf : ∀ j ∈ s.erase i, 0 ≤ f j)
    (hbound : ∀ j ∈ s.erase i, f j ≤ H)
    (hprod : 1 ≤ f i * ∏ j ∈ s.erase i, f j) :
    1 / H ^ (s.erase i).card ≤ f i := by
  have hrest : (∏ j ∈ s.erase i, f j) ≤ H ^ (s.erase i).card := by
    calc
      (∏ j ∈ s.erase i, f j) ≤ ∏ _j ∈ s.erase i, H :=
        Finset.prod_le_prod hf hbound
      _ = H ^ (s.erase i).card := by simp
  have hmul : 1 ≤ f i * H ^ (s.erase i).card :=
    hprod.trans (mul_le_mul_of_nonneg_left hrest hfi)
  exact (div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one hH) _)).2 hmul

/-- Finset form of the basic estimate.  The membership hypothesis permits the
full product to be split by erasing the distinguished index. -/
theorem one_div_pow_card_erase_le_of_one_le_prod
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (i : ι)
    (f : ι → ℝ) (H : ℝ) (hi : i ∈ s)
    (hH : 1 ≤ H) (hf : ∀ j ∈ s, 0 ≤ f j)
    (hbound : ∀ j ∈ s.erase i, f j ≤ H)
    (hprod : 1 ≤ ∏ j ∈ s, f j) :
    1 / H ^ (s.erase i).card ≤ f i := by
  apply one_div_pow_card_erase_le_of_one_le_mul_prod s i f H hH (hf i hi)
  · intro j hj
    exact hf j (Finset.mem_of_mem_erase hj)
  · exact hbound
  · rw [Finset.mul_prod_erase s f hi]
    exact hprod

/-- Complex-norm version for a finite set of indices.  Only the factors other
than `i` need upper bounds. -/
theorem one_div_pow_card_erase_le_norm_of_one_le_norm_prod
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (i : ι)
    (z : ι → ℂ) (H : ℝ) (hi : i ∈ s)
    (hH : 1 ≤ H)
    (hbound : ∀ j ∈ s.erase i, ‖z j‖ ≤ H)
    (hprod : 1 ≤ ‖∏ j ∈ s, z j‖) :
    1 / H ^ (s.erase i).card ≤ ‖z i‖ := by
  apply one_div_pow_card_erase_le_of_one_le_prod
      s i (fun j ↦ ‖z j‖) H hi hH
  · intro j _
    exact norm_nonneg _
  · exact hbound
  · simpa only [Complex.norm_prod] using hprod

/-- Fintype form with the exceptional index stated explicitly.  For a family
of cardinality `d`, the exponent is `d - 1`. -/
theorem one_div_pow_card_sub_one_le_norm_of_one_le_norm_fintypeProd
    {ι : Type*} [Fintype ι] (i : ι) (z : ι → ℂ) (H : ℝ)
    (hH : 1 ≤ H)
    (hbound : ∀ j, j ≠ i → ‖z j‖ ≤ H)
    (hprod : 1 ≤ ‖∏ j, z j‖) :
    1 / H ^ (Fintype.card ι - 1) ≤ ‖z i‖ := by
  classical
  have h := one_div_pow_card_erase_le_norm_of_one_le_norm_prod
    (Finset.univ : Finset ι) i z H (Finset.mem_univ i) hH
    (fun j hj ↦ hbound j (Finset.mem_erase.mp hj).1) hprod
  simpa using h

/-- Convenient Fintype corollary when the same height bound is known for
every factor.  In fact, the conclusion then holds for every choice of the
distinguished index. -/
theorem one_div_pow_card_sub_one_le_norm_of_forall_le
    {ι : Type*} [Fintype ι] (i : ι) (z : ι → ℂ) (H : ℝ)
    (hH : 1 ≤ H) (hbound : ∀ j, ‖z j‖ ≤ H)
    (hprod : 1 ≤ ‖∏ j, z j‖) :
    1 / H ^ (Fintype.card ι - 1) ≤ ‖z i‖ :=
  one_div_pow_card_sub_one_le_norm_of_one_le_norm_fintypeProd
    i z H hH (fun j _ ↦ hbound j) hprod

end Erdos240.EmbeddingProduct

#print axioms Erdos240.EmbeddingProduct.one_div_pow_card_erase_le_norm_of_one_le_norm_prod
#print axioms Erdos240.EmbeddingProduct.one_div_pow_card_sub_one_le_norm_of_forall_le
