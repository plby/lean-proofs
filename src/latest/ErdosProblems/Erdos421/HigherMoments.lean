import ErdosProblems.Erdos421.DivisorMoments
import ErdosProblems.Erdos421.LargeValues

/-! # Higher moments of finite Dirichlet polynomials -/

namespace Erdos421

open MeasureTheory

theorem SupportedThrough.exponentialSum_norm_pow {f : ArithmeticFunction ℂ} {N : ℕ}
    (hN : SupportedThrough f N) (k : ℕ) (t : ℝ) :
    ‖exponentialSum (Finset.Icc 1 (N ^ k)) (f ^ k : ArithmeticFunction ℂ)
      (fun n ↦ Real.log n) t‖ ^ 2 =
      ‖exponentialSum (Finset.Icc 1 N) f (fun n ↦ Real.log n) t‖ ^ (2 * k) := by
  rw [hN.exponentialSum_pow, norm_pow, ← pow_mul, Nat.mul_comm k 2]

theorem finite_dirichlet_higher_mean_bound (f : ArithmeticFunction ℂ) {N : ℕ}
    (hN : SupportedThrough f N) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, n ≠ 0 → ‖f n‖ ≤ C) (k : ℕ) {A B : ℝ} (hAB : A ≤ B) :
    (∫ t in A..B,
      ‖exponentialSum (Finset.Icc 1 N) f (fun n ↦ Real.log n) t‖ ^ (2 * k)) ≤
      (B - A + 4 * (N ^ k : ℕ) * (1 + Real.log (N ^ k : ℕ))) *
        (C ^ (2 * k) * (N ^ k : ℕ) * (1 + Real.log (N ^ k : ℕ)) ^ (k ^ 2)) := by
  have hmean := dirichlet_mean_square_bound (Finset.Icc 1 (N ^ k))
    (f ^ k : ArithmeticFunction ℂ) (N := N ^ k)
    (fun n hn ↦ Finset.mem_Icc.mp hn) A B
  simp_rw [hN.exponentialSum_norm_pow] at hmean
  refine hmean.trans (mul_le_mul_of_nonneg_left (convolution_pow_energy_bound f hC hf k _) ?_)
  have hlog := Real.log_natCast_nonneg (N ^ k)
  have hsize : (0 : ℝ) ≤ (N ^ k : ℕ) := Nat.cast_nonneg _
  nlinarith

theorem finite_dirichlet_higher_sample_bound (f : ArithmeticFunction ℂ) {N : ℕ}
    (hN : SupportedThrough f N) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, n ≠ 0 → ‖f n‖ ≤ C) (k : ℕ)
    (S : Finset ℕ) (t : ℕ → ℝ) {A B : ℝ}
    (hAB : A ≤ B) (ht : ∀ i ∈ S, A ≤ t i ∧ t i ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|) :
    (∑ i ∈ S, ‖exponentialSum (Finset.Icc 1 N) f (fun n ↦ Real.log n) (t i)‖ ^ (2 * k)) ≤
      (2 + (Real.log (N ^ k : ℕ)) ^ 2) *
        (B + 1 - A + 4 * (N ^ k : ℕ) * (1 + Real.log (N ^ k : ℕ))) *
        (C ^ (2 * k) * (N ^ k : ℕ) * (1 + Real.log (N ^ k : ℕ)) ^ (k ^ 2)) := by
  have hsample := dirichlet_separated_square_sum_le (Finset.Icc 1 (N ^ k)) S
    (f ^ k : ArithmeticFunction ℂ) t (N := N ^ k)
    (fun n hn ↦ Finset.mem_Icc.mp hn) hAB ht hsep
  simp_rw [hN.exponentialSum_norm_pow] at hsample
  refine hsample.trans (mul_le_mul_of_nonneg_left (convolution_pow_energy_bound f hC hf k _) ?_)
  have hlog := Real.log_natCast_nonneg (N ^ k)
  have hsize : (0 : ℝ) ≤ (N ^ k : ℕ) := Nat.cast_nonneg _
  apply mul_nonneg (by positivity)
  nlinarith

theorem finite_dirichlet_higher_large_values_bound (f : ArithmeticFunction ℂ) {N : ℕ}
    (hN : SupportedThrough f N) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, n ≠ 0 → ‖f n‖ ≤ C) (k : ℕ)
    (S : Finset ℕ) (t : ℕ → ℝ) {A B V : ℝ}
    (hAB : A ≤ B) (ht : ∀ i ∈ S, A ≤ t i ∧ t i ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|)
    (hV : 0 ≤ V)
    (hlarge : ∀ i ∈ S, V ≤ ‖exponentialSum (Finset.Icc 1 N) f (fun n ↦ Real.log n) (t i)‖) :
    S.card * V ^ (2 * k) ≤
      (2 + (Real.log (N ^ k : ℕ)) ^ 2) *
        (B + 1 - A + 4 * (N ^ k : ℕ) * (1 + Real.log (N ^ k : ℕ))) *
        (C ^ (2 * k) * (N ^ k : ℕ) * (1 + Real.log (N ^ k : ℕ)) ^ (k ^ 2)) := by
  calc
    _ = ∑ _i ∈ S, V ^ (2 * k) := by simp
    _ ≤ ∑ i ∈ S,
        ‖exponentialSum (Finset.Icc 1 N) f (fun n ↦ Real.log n) (t i)‖ ^ (2 * k) :=
      Finset.sum_le_sum (fun i hi ↦ pow_le_pow_left₀ hV (hlarge i hi) _)
    _ ≤ _ := finite_dirichlet_higher_sample_bound f hN hC hf k S t hAB ht hsep

end Erdos421
