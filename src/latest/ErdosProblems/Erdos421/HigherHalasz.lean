import ErdosProblems.Erdos421.FiniteHalasz
import ErdosProblems.Erdos421.HigherMoments

/-! # Applying the Halász estimate to convolution powers -/

namespace Erdos421

theorem SupportedThrough.exponentialSum_Ico_eq {f : ArithmeticFunction ℂ} {N B : ℕ}
    (hN : SupportedThrough f N) (hNB : N < B) (t : ℝ) :
    exponentialSum (Finset.Ico 1 B) f (fun n ↦ Real.log n) t =
      exponentialSum (Finset.Icc 1 N) f (fun n ↦ Real.log n) t := by
  apply sum_Ico_eq_sum_Icc_of_support _ _ hNB
  intro n hn
  rw [hN n hn, zero_mul]

theorem finite_dirichlet_higher_halasz_bound (f : ArithmeticFunction ℂ) {N : ℕ}
    (hN : SupportedThrough f N) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n, n ≠ 0 → ‖f n‖ ≤ C) (k : ℕ) {K : ℕ}
    (hK : 0 < K) (hNK : N ^ k < 2 ^ K)
    (S : Finset ℕ) (t : ℕ → ℝ) {A B V : ℝ}
    (hAB : A ≤ B) (ht : ∀ i ∈ S, A ≤ t i ∧ t i ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|)
    (hV : 0 < V)
    (hlarge : ∀ i ∈ S, V ≤ ‖exponentialSum (Finset.Icc 1 N) f (fun n ↦ Real.log n) (t i)‖) :
    let G := C ^ (2 * k) * (N ^ k : ℕ) * (1 + Real.log (N ^ k : ℕ)) ^ (k ^ 2)
    (S.card : ℝ) ≤ 10240 * K * (2 ^ K : ℕ) * Real.log ((2 ^ K : ℕ) + 2 : ℝ) *
      (G / (V ^ k / K) ^ 2 + 1280 ^ 2 * G ^ 3 * (B - A) / (V ^ k / K) ^ 6) := by
  dsimp only
  apply finite_dirichlet_halasz_energy_bound hK S (f ^ k : ArithmeticFunction ℂ) t
    hAB ht hsep (pow_pos hV k)
  · intro i hi
    rw [(hN.pow k).exponentialSum_Ico_eq hNK, hN.exponentialSum_pow, norm_pow]
    exact pow_le_pow_left₀ hV.le (hlarge i hi) k
  · rw [sum_Ico_eq_sum_Icc_of_support (fun n ↦ ‖(f ^ k : ArithmeticFunction ℂ) n‖ ^ 2)
      (fun n hn ↦ by rw [hN.pow k n hn]; simp) hNK]
    exact convolution_pow_energy_bound f hC hf k (N ^ k)

end Erdos421
