import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-! A reciprocal-square tail with an explicit lower cutoff. -/

open scoped BigOperators

namespace Erdos4.FGKMT

theorem finite_reciprocal_square_tail {K : ℕ} (hK : 0 < K) (S : Finset ℕ)
    (hS : ∀ n ∈ S, K < n) :
    (∑ n ∈ S, ((n : ℝ) ^ 2)⁻¹) ≤ (K : ℝ)⁻¹ := by
  let N := max K (S.sup id)
  have hsub : S ⊆ Finset.Ioc K N := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨hS n hn, (Finset.le_sup (f := id) hn).trans (le_max_right _ _)⟩
  calc
    _ ≤ ∑ n ∈ Finset.Ioc K N, ((n : ℝ) ^ 2)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
    _ ≤ (K : ℝ)⁻¹ - (N : ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub hK.ne' (le_max_left _ _)
    _ ≤ _ := sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg N))

theorem finite_shifted_reciprocal_square_tail {K : ℕ} (hK : 2 ≤ K) (S : Finset ℕ)
    (hS : ∀ n ∈ S, K < n) :
    (∑ n ∈ S, (((n : ℝ) - 1)⁻¹) ^ 2) ≤ (((K - 1 : ℕ) : ℝ))⁻¹ := by
  have hinj : Set.InjOn (fun n => n - 1) S := by
    intro n hn m hm heq
    have hnn := hS n hn
    have hmm := hS m hm
    change n - 1 = m - 1 at heq
    omega
  have hshift : (∑ n ∈ S, (((n : ℝ) - 1)⁻¹) ^ 2) =
      ∑ n ∈ S.image (fun n : ℕ => (n - 1 : ℕ)), ((n : ℝ) ^ 2)⁻¹ := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro n hn
    have hn1 : 1 ≤ n := by have hh := hS n hn; omega
    rw [Nat.cast_sub hn1, Nat.cast_one, inv_pow]
  rw [hshift]
  apply finite_reciprocal_square_tail (by omega : 0 < K - 1)
  intro n hn
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
  have hh := hS m hm
  omega

end Erdos4.FGKMT
