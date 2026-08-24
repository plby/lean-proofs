import ErdosProblems.Erdos587.ThirdDifferenceTest

/-! Optimize the short-shift length in the middle third-difference range. -/

open scoped BigOperators

namespace Erdos587

lemma third_difference_cutoff {n lam : ℝ} (hn : 1 ≤ n) (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) (hlamlo : n ^ (-(3 / 2 : ℝ)) ≤ lam) :
    1 ≤ lam ^ (-(1 / 3 : ℝ)) ∧ lam ^ (-(1 / 3 : ℝ)) ≤ Real.sqrt n := by
  refine ⟨Real.one_le_rpow_of_pos_of_le_one_of_nonpos hlam hlam1 (by norm_num), ?_⟩
  have hnpos : 0 < n := by linarith
  calc
    _ ≤ (n ^ (-(3 / 2 : ℝ))) ^ (-(1 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hnpos _) hlamlo (by norm_num)
    _ = Real.sqrt n := by
      rw [← Real.rpow_mul hnpos.le, Real.sqrt_eq_rpow]
      congr 1
      norm_num

theorem norm_phase_sum_le_middle_third_difference (f : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {lam C : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hlamlo : (N : ℝ) ^ (-(3 / 2 : ℝ)) ≤ lam) (hC : 1 ≤ C)
    (hlo : ∀ n, n + 2 < N → lam ≤ phaseIncrement (phaseIncrement (phaseIncrement f)) n)
    (hhi : ∀ n, n + 2 < N → phaseIncrement (phaseIncrement (phaseIncrement f)) n ≤ C * lam) :
    ‖∑ n ∈ Finset.range N, phase (f n)‖ ≤ 100 * C * N * lam ^ (1 / 6 : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hCpos : 0 < C := by linarith
  let X : ℝ := lam ^ (-(1 / 3 : ℝ))
  let P : ℝ := lam ^ (1 / 3 : ℝ)
  let Q : ℝ := lam ^ (1 / 6 : ℝ)
  obtain ⟨hX1, hXN⟩ := third_difference_cutoff hN1 hlam hlam1 hlamlo
  have hXpos : 0 < X := Real.rpow_pos_of_pos hlam _
  have hPpos : 0 < P := Real.rpow_pos_of_pos hlam _
  have hQpos : 0 < Q := Real.rpow_pos_of_pos hlam _
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  let K := Nat.ceil X
  have hXK : X ≤ (K : ℝ) := Nat.le_ceil X
  have hK : 0 < K := Nat.ceil_pos.mpr hXpos
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hKN : K ≤ N := by
    apply Nat.ceil_le.mpr
    exact hXN.trans (Real.sqrt_le_iff.mpr ⟨hNR.le, by nlinarith⟩)
  have hKX : (K : ℝ) ≤ 2 * X := by
    have hh := Nat.ceil_lt_add_one hXpos.le
    change (K : ℝ) < X + 1 at hh
    change 1 ≤ X at hX1
    linarith
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXpos
  have hsK : 0 < Real.sqrt (K : ℝ) := Real.sqrt_pos.mpr hKR
  have hsXK : Real.sqrt X ≤ Real.sqrt (K : ℝ) := Real.sqrt_le_sqrt hXK
  have hsKX : Real.sqrt (K : ℝ) ≤ 2 * Real.sqrt X := by
    apply Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hXpos.le]
  have hXP : X * P = 1 := by
    dsimp [X, P]
    rw [← Real.rpow_add hlam]
    norm_num
  have hXinv : 1 / X = P := (div_eq_iff hXpos.ne').mpr (by simpa only [mul_comm] using hXP.symm)
  have hsXP : Real.sqrt lam * Real.sqrt X = P := by
    dsimp [X, P]
    simp only [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hlam.le, ← Real.rpow_add hlam]
    congr 1
    norm_num
  have hQsq : Q ^ 2 = P := by
    dsimp [Q, P]
    rw [← Real.rpow_mul_natCast hlam.le]
    congr 1
    norm_num
  have hPinv : 1 ≤ (N : ℝ) * P ^ 2 := by
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hNR.le _) hlamlo
      (by norm_num : (0 : ℝ) ≤ 2 / 3)
    rw [← Real.rpow_mul hNR.le] at hh
    norm_num at hh
    have hP2 : P ^ 2 = lam ^ (2 / 3 : ℝ) := by
      dsimp [P]
      rw [← Real.rpow_mul_natCast hlam.le]
      congr 1
      norm_num
    rw [← hP2] at hh
    have hh' := mul_le_mul_of_nonneg_left hh hNR.le
    simpa only [Real.rpow_neg_one, mul_inv_cancel₀ hNR.ne'] using hh'
  have hNoverP : (N : ℝ) / P ≤ (N : ℝ) ^ 2 * P := by
    apply (div_le_iff₀ hPpos).mpr
    have hh := mul_le_mul_of_nonneg_left hPinv hNR.le
    nlinarith
  have hterm₁ : 2 * (N : ℝ) ^ 2 / K ≤ 2 * (N : ℝ) ^ 2 * P := by
    calc
      _ ≤ 2 * (N : ℝ) ^ 2 / X := div_le_div_of_nonneg_left (by positivity) hXpos hXK
      _ = (2 * (N : ℝ) ^ 2) * (1 / X) := by ring
      _ = _ := by rw [hXinv]
  have hterm₂ : 40 * C * (N : ℝ) ^ 2 * Real.sqrt lam * Real.sqrt K ≤
      80 * C * (N : ℝ) ^ 2 * P := by
    calc
      _ ≤ 40 * C * (N : ℝ) ^ 2 * Real.sqrt lam * (2 * Real.sqrt X) :=
        mul_le_mul_of_nonneg_left hsKX (by positivity)
      _ = 80 * C * (N : ℝ) ^ 2 * (Real.sqrt lam * Real.sqrt X) := by ring
      _ = _ := by rw [hsXP]
  have hterm₃ : 80 * C * N / (Real.sqrt lam * Real.sqrt K) ≤ 80 * C * (N : ℝ) ^ 2 * P := by
    have hden : P ≤ Real.sqrt lam * Real.sqrt K := by
      rw [← hsXP]
      exact mul_le_mul_of_nonneg_left hsXK hs.le
    calc
      _ ≤ 80 * C * N / P := div_le_div_of_nonneg_left (by positivity) hPpos hden
      _ = (80 * C) * ((N : ℝ) / P) := by ring
      _ ≤ (80 * C) * ((N : ℝ) ^ 2 * P) := mul_le_mul_of_nonneg_left hNoverP (by positivity)
      _ = _ := by ring
  have hshort := short_shift_third_difference_bound f hK hKN hlam hC hlo hhi
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 100 * C * N * Q)).mp
  calc
    _ ≤ 2 * (N : ℝ) ^ 2 / K + 40 * C * (N : ℝ) ^ 2 * Real.sqrt lam * Real.sqrt K +
        80 * C * N / (Real.sqrt lam * Real.sqrt K) := hshort
    _ ≤ 2 * (N : ℝ) ^ 2 * P + 80 * C * (N : ℝ) ^ 2 * P + 80 * C * (N : ℝ) ^ 2 * P :=
      add_le_add (add_le_add hterm₁ hterm₂) hterm₃
    _ = (2 + 160 * C) * ((N : ℝ) ^ 2 * P) := by ring
    _ ≤ (10000 * C ^ 2) * ((N : ℝ) ^ 2 * P) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith [sq_nonneg (C - 1)]
    _ = (100 * C * N * Q) ^ 2 := by rw [mul_pow, hQsq]; ring

end Erdos587
