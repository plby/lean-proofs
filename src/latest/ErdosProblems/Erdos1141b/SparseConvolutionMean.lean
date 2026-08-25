import ErdosProblems.Erdos1141b.ConvolutionSupport
import ErdosProblems.Erdos1141b.ElementaryBounds
import ErdosProblems.Erdos1141b.BurgessParameters

/-!
# Sparse support gives a small convolution mean
-/

open scoped BigOperators

namespace Erdos1141b

theorem exists_sparse_convolution_mean_cutoff :
    ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
      ∀ X : ℕ, (M : ℝ) ^ (31 / 64 : ℝ) / 2 ≤ (X : ℝ) →
        (X : ℝ) ≤ (M : ℝ) ^ (31 / 64 : ℝ) →
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      (∀ p : ℕ, p.Prime → p ≤ X → ¬p ∣ M → χ (p : ZMod q) = -1) →
      ‖∑ n ∈ Finset.Icc 1 X, χ.zetaMul n‖ ≤
        (X : ℝ) * (M : ℝ) ^ (-1 / 1024 : ℝ) := by
  have hevent : ∀ᶠ M : ℕ in Filter.atTop,
      1 ≤ M ∧ 2 ≤ (M : ℝ) ^ (231 / 1024 : ℝ) ∧
      ∀ n : ℕ, n ≠ 0 → n ≤ M → (n.divisors.card : ℝ) ≤ (M : ℝ) ^ (1 / 128 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 1,
      eventually_const_le_rpow 2 (231 / 1024) (by norm_num),
      eventually_divisors_card_le_rpow_uniform 256 (by norm_num)] with M h1 h2 h3
    exact ⟨h1, h2, by norm_num at h3; exact h3⟩
  obtain ⟨M0, hcut⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨M0, ?_⟩
  intro M hM X hXlo hXhi q χ hprimes
  obtain ⟨hM1, h2, hdiv⟩ := hcut M hM
  have hM0 : M ≠ 0 := by omega
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM1
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hXM : X ≤ M := by
    have h := hXhi.trans (Real.rpow_le_rpow_of_exponent_le hMone (by norm_num : (31 / 64 : ℝ) ≤ 1))
    simpa only [Real.rpow_one, Nat.cast_le] using h
  have hsqrt : (Nat.sqrt X : ℝ) ≤ (M : ℝ) ^ (31 / 128 : ℝ) := by
    calc
      _ ≤ Real.sqrt (X : ℝ) := Real.nat_sqrt_le_real_sqrt
      _ ≤ Real.sqrt ((M : ℝ) ^ (31 / 64 : ℝ)) := Real.sqrt_le_sqrt hXhi
      _ = _ := by rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hMr.le]; norm_num
  calc
    _ ≤ (M.divisors.card : ℝ) * Nat.sqrt X * (M : ℝ) ^ (1 / 128 : ℝ) :=
      norm_zetaMul_prefix_le_of_no_split_prime χ hM0 _ (by positivity)
        (fun n hn hnX ↦ hdiv n hn.ne' (hnX.trans hXM)) hprimes
    _ ≤ (M : ℝ) ^ (1 / 128 : ℝ) * (M : ℝ) ^ (31 / 128 : ℝ) *
        (M : ℝ) ^ (1 / 128 : ℝ) := by
      gcongr
      exact hdiv M hM0 le_rfl
    _ = (M : ℝ) ^ (33 / 128 : ℝ) := by
      rw [← Real.rpow_add hMr, ← Real.rpow_add hMr]; norm_num
    _ ≤ ((M : ℝ) ^ (231 / 1024 : ℝ) / 2) * (M : ℝ) ^ (33 / 128 : ℝ) := by
      have h := mul_le_mul_of_nonneg_right h2 (by positivity : 0 ≤ (M : ℝ) ^ (33 / 128 : ℝ))
      nlinarith
    _ = ((M : ℝ) ^ (31 / 64 : ℝ) / 2) * (M : ℝ) ^ (-1 / 1024 : ℝ) := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← Real.rpow_add hMr, ← Real.rpow_add hMr]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_right hXlo (by positivity)

end Erdos1141b
