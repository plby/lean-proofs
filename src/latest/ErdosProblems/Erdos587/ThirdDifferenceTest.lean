import ErdosProblems.Erdos587.SecondDerivativeTest
import ErdosProblems.Erdos587.FiniteDifferences
import ErdosProblems.Erdos587.IntervalDifferencing

/-! Short-shift correlations controlled by positive third differences. -/

open scoped BigOperators ComplexConjugate

namespace Erdos587

lemma norm_phase_sum_neg (f : ℕ → ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, phase (-f n)‖ = ‖∑ n ∈ Finset.range N, phase (f n)‖ := by
  simp_rw [phase_neg]
  rw [← map_sum, Complex.norm_conj]

theorem norm_phase_sum_le_negative_second_difference (f : ℕ → ℝ) (N : ℕ) {lam C : ℝ}
    (hlam : 0 < lam) (hC : 1 ≤ C)
    (hlo : ∀ n, n + 1 < N → -(C * lam) ≤ phaseIncrement (phaseIncrement f) n)
    (hhi : ∀ n, n + 1 < N → phaseIncrement (phaseIncrement f) n ≤ -lam) :
    ‖∑ n ∈ Finset.range N, phase (f n)‖ ≤
      10 * C * ((N : ℝ) * Real.sqrt lam + (Real.sqrt lam)⁻¹) := by
  rw [← norm_phase_sum_neg f N]
  apply norm_phase_sum_le_second_difference (fun n => -f n) N hlam hC
  · intro n hn
    change lam ≤ phaseIncrement (phaseIncrement (fun n => -f n)) n
    rw [phaseIncrement_twice_neg]
    linarith [hhi n hn]
  · intro n hn
    change phaseIncrement (phaseIncrement (fun n => -f n)) n ≤ C * lam
    rw [phaseIncrement_twice_neg]
    linarith [hlo n hn]

theorem norm_phase_correlation_le_of_third_difference (f : ℕ → ℝ) (N : ℕ) {r : ℕ}
    (hr : 0 < r) {lam C : ℝ} (hlam : 0 < lam) (hC : 1 ≤ C)
    (hlo : ∀ n, n + 2 < N → lam ≤ phaseIncrement (phaseIncrement (phaseIncrement f)) n)
    (hhi : ∀ n, n + 2 < N → phaseIncrement (phaseIncrement (phaseIncrement f)) n ≤ C * lam) :
    ‖∑ n ∈ Finset.range (N - r), phase (f (n + r)) * conj (phase (f n))‖ ≤
      10 * C * (((N - r : ℕ) : ℝ) * Real.sqrt ((r : ℝ) * lam) +
        (Real.sqrt ((r : ℝ) * lam))⁻¹) := by
  simp_rw [← phase_sub]
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hb := correlation_second_difference_bounds f N r hlo hhi
  exact norm_phase_sum_le_second_difference (fun n => f (n + r) - f n) (N - r)
    (mul_pos hrR hlam) hC (fun n hn => (hb n hn).1) (fun n hn => (hb n hn).2)

lemma sum_inverse_sqrt_succ_le (K : ℕ) :
    (∑ n ∈ Finset.range K, (Real.sqrt ((n : ℝ) + 1))⁻¹) ≤ 2 * Real.sqrt K := by
  have hterm (n : ℕ) : (Real.sqrt ((n : ℝ) + 1))⁻¹ ≤
      2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hs : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hmono : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    rw [← one_div]
    apply (div_le_iff₀ hs).mpr
    have hsq₀ := Real.sq_sqrt hn
    have hsq₁ := Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity)
    nlinarith [sq_nonneg (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ))]
  calc
    _ ≤ ∑ n ∈ Finset.range K, 2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) :=
      Finset.sum_le_sum (fun n hn => hterm n)
    _ = 2 * Real.sqrt K := by
      induction K with
      | zero => simp
      | succ K ih =>
        rw [Finset.sum_range_succ, ih, Nat.cast_add, Nat.cast_one]
        ring

lemma sum_sqrt_succ_le (K : ℕ) :
    (∑ n ∈ Finset.range K, Real.sqrt ((n : ℝ) + 1)) ≤ (K : ℝ) * Real.sqrt K := by
  calc
    _ ≤ ∑ n ∈ Finset.range K, Real.sqrt K := by
      apply Finset.sum_le_sum
      intro n hn
      apply Real.sqrt_le_sqrt
      have hh : n + 1 ≤ K := by have := Finset.mem_range.mp hn; omega
      exact_mod_cast hh
    _ = _ := by simp

theorem sum_phase_correlations_le_of_third_difference (f : ℕ → ℝ) (N K : ℕ) {lam C : ℝ}
    (hlam : 0 < lam) (hC : 1 ≤ C)
    (hlo : ∀ n, n + 2 < N → lam ≤ phaseIncrement (phaseIncrement (phaseIncrement f)) n)
    (hhi : ∀ n, n + 2 < N → phaseIncrement (phaseIncrement (phaseIncrement f)) n ≤ C * lam) :
    (∑ r ∈ Finset.range K, ‖∑ n ∈ Finset.range (N - (r + 1)),
      phase (f (n + (r + 1))) * conj (phase (f n))‖) ≤
      10 * C * ((N : ℝ) * Real.sqrt lam * K * Real.sqrt K + 2 * Real.sqrt K / Real.sqrt lam) := by
  have hC0 : 0 ≤ C := by linarith
  have hpoint (r : ℕ) :
      ‖∑ n ∈ Finset.range (N - (r + 1)), phase (f (n + (r + 1))) * conj (phase (f n))‖ ≤
        10 * C * ((N : ℝ) * Real.sqrt lam * Real.sqrt ((r : ℝ) + 1) +
          (Real.sqrt lam)⁻¹ * (Real.sqrt ((r : ℝ) + 1))⁻¹) := by
    have hh := norm_phase_correlation_le_of_third_difference f N (Nat.succ_pos r) hlam hC hlo hhi
    have hNM : ((N - (r + 1) : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N (r + 1)
    simp only [Nat.cast_succ, Real.sqrt_mul (show 0 ≤ (r : ℝ) + 1 by positivity)] at hh
    calc
      _ ≤ 10 * C * (((N - (r + 1) : ℕ) : ℝ) *
          (Real.sqrt ((r : ℝ) + 1) * Real.sqrt lam) +
          (Real.sqrt ((r : ℝ) + 1) * Real.sqrt lam)⁻¹) := hh
      _ ≤ 10 * C * ((N : ℝ) * (Real.sqrt ((r : ℝ) + 1) * Real.sqrt lam) +
          (Real.sqrt ((r : ℝ) + 1) * Real.sqrt lam)⁻¹) := by gcongr
      _ = _ := by rw [mul_inv]; ring
  calc
    _ ≤ ∑ r ∈ Finset.range K, 10 * C * ((N : ℝ) * Real.sqrt lam * Real.sqrt ((r : ℝ) + 1) +
        (Real.sqrt lam)⁻¹ * (Real.sqrt ((r : ℝ) + 1))⁻¹) :=
      Finset.sum_le_sum (fun r hr => hpoint r)
    _ = 10 * C * ((N : ℝ) * Real.sqrt lam * (∑ r ∈ Finset.range K, Real.sqrt ((r : ℝ) + 1)) +
        (Real.sqrt lam)⁻¹ * ∑ r ∈ Finset.range K, (Real.sqrt ((r : ℝ) + 1))⁻¹) := by
      simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc]
    _ ≤ 10 * C * ((N : ℝ) * Real.sqrt lam * ((K : ℝ) * Real.sqrt K) +
        (Real.sqrt lam)⁻¹ * (2 * Real.sqrt K)) := by
      gcongr
      · exact sum_sqrt_succ_le K
      · exact sum_inverse_sqrt_succ_le K
    _ = _ := by ring

theorem short_shift_third_difference_bound (f : ℕ → ℝ) {N K : ℕ}
    (hK : 0 < K) (hKN : K ≤ N) {lam C : ℝ} (hlam : 0 < lam) (hC : 1 ≤ C)
    (hlo : ∀ n, n + 2 < N → lam ≤ phaseIncrement (phaseIncrement (phaseIncrement f)) n)
    (hhi : ∀ n, n + 2 < N → phaseIncrement (phaseIncrement (phaseIncrement f)) n ≤ C * lam) :
    ‖∑ n ∈ Finset.range N, phase (f n)‖ ^ 2 ≤
      2 * (N : ℝ) ^ 2 / K + 40 * C * (N : ℝ) ^ 2 * Real.sqrt lam * Real.sqrt K +
        80 * C * N / (Real.sqrt lam * Real.sqrt K) := by
  have hN : 0 < N := hK.trans_le hKN
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hrootK : 0 < Real.sqrt (K : ℝ) := Real.sqrt_pos.mpr hKR
  have hweyl := interval_short_shift_differencing (fun n => phase (f n)) hN hKN
    (fun n hn => (norm_phase _).le)
  have hcorr := sum_phase_correlations_le_of_third_difference f N K hlam hC hlo hhi
  simp only [Nat.add_assoc] at hweyl
  have hbase : (K : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, phase (f n)‖ ^ 2 ≤
      2 * N * ((K : ℝ) * N + 2 * K *
        (10 * C * ((N : ℝ) * Real.sqrt lam * K * Real.sqrt K + 2 * Real.sqrt K / Real.sqrt lam))) := by
    apply hweyl.trans
    gcongr
  have hrootquot : Real.sqrt (K : ℝ) / K = 1 / Real.sqrt (K : ℝ) := by
    field_simp
    nlinarith [Real.sq_sqrt hKR.le]
  calc
    _ ≤ (2 * N * ((K : ℝ) * N + 2 * K *
        (10 * C * ((N : ℝ) * Real.sqrt lam * K * Real.sqrt K +
          2 * Real.sqrt K / Real.sqrt lam)))) / (K : ℝ) ^ 2 := by
      apply (le_div_iff₀ (pow_pos hKR 2)).mpr
      simpa only [mul_comm] using hbase
    _ = 2 * (N : ℝ) ^ 2 / K + 40 * C * (N : ℝ) ^ 2 * Real.sqrt lam * Real.sqrt K +
        80 * C * N / Real.sqrt lam * (Real.sqrt (K : ℝ) / K) := by
      field_simp
      ring
    _ = _ := by rw [hrootquot]; ring

end Erdos587
