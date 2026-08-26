import ErdosProblems.Erdos421.Halasz

/-! # Dyadic decompositions of finite Dirichlet polynomials -/

namespace Erdos421

theorem sum_dyadic_blocks {R : Type*} [AddCommMonoid R] (f : ℕ → R) (K : ℕ) :
    (∑ j ∈ Finset.range K, ∑ n ∈ Finset.range (2 ^ j), f (2 ^ j + n)) =
      ∑ n ∈ Finset.Ico 1 (2 ^ K), f n := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    have hsplit := Finset.sum_Ico_consecutive f
      (show 1 ≤ 2 ^ K from one_le_pow₀ (by norm_num)) (show 2 ^ K ≤ 2 ^ (K + 1) by
        rw [pow_succ]
        omega)
    rw [← hsplit, Finset.sum_Ico_eq_sum_range f (2 ^ K) (2 ^ (K + 1))]
    have hlen : 2 ^ (K + 1) - 2 ^ K = 2 ^ K := by rw [pow_succ]; omega
    rw [hlen]

theorem exponentialSum_dyadic_blocks (c : ℕ → ℂ) (K : ℕ) (t : ℝ) :
    exponentialSum (Finset.Ico 1 (2 ^ K)) c (fun n ↦ Real.log n) t =
      ∑ j ∈ Finset.range K,
        dirichletBlock (2 ^ j) (2 ^ j) (fun n ↦ c (2 ^ j + n)) t := by
  exact (sum_dyadic_blocks (fun n ↦ c n * oscillatoryPhase (Real.log n) t) K).symm

theorem dyadic_coefficientEnergy_le (c : ℕ → ℂ) {j K : ℕ} (hj : j < K) :
    coefficientEnergy (2 ^ j) (fun n ↦ c (2 ^ j + n)) ≤
      ∑ n ∈ Finset.Ico 1 (2 ^ K), ‖c n‖ ^ 2 := by
  rw [← sum_dyadic_blocks]
  exact Finset.single_le_sum (fun i _ ↦ coefficientEnergy_nonneg (2 ^ i) (fun n ↦ c (2 ^ i + n)))
    (Finset.mem_range.mpr hj)

theorem exists_large_dyadic_block (c : ℕ → ℂ) {K : ℕ} (hK : 0 < K)
    {V t : ℝ} (hlarge : V ≤ ‖exponentialSum (Finset.Ico 1 (2 ^ K)) c (fun n ↦ Real.log n) t‖) :
    ∃ j < K, V / K ≤ ‖dirichletBlock (2 ^ j) (2 ^ j) (fun n ↦ c (2 ^ j + n)) t‖ := by
  rw [exponentialSum_dyadic_blocks] at hlarge
  have hsum : (∑ _j ∈ Finset.range K, V / (K : ℝ)) ≤
      ∑ j ∈ Finset.range K, ‖dirichletBlock (2 ^ j) (2 ^ j) (fun n ↦ c (2 ^ j + n)) t‖ := by
    have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_div_cancel₀ V hK0] using hlarge.trans (norm_sum_le _ _)
  obtain ⟨j, hj, hbig⟩ := Finset.exists_le_of_sum_le ⟨0, Finset.mem_range.mpr hK⟩ hsum
  exact ⟨j, Finset.mem_range.mp hj, hbig⟩

end Erdos421
