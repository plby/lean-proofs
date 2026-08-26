import ErdosProblems.Erdos421.TimeSubdivision

/-! # An explicit Halász large-value estimate -/

namespace Erdos421

theorem dirichletPhaseVector_norm_sq (M N : ℕ) (t : ℝ) :
    ‖dirichletPhaseVector M N t‖ ^ 2 = N := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ n : Fin N, ‖oscillatoryPhase (Real.log (M + n : ℕ)) (-t)‖ ^ 2) = N
  simp

theorem dirichletBlock_norm_sq_le (M N : ℕ) (c : ℕ → ℂ) (t : ℝ) :
    ‖dirichletBlock M N c t‖ ^ 2 ≤ N * coefficientEnergy N c := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (dirichletPhaseVector M N t) (coefficientVector N c)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [dirichletPhaseVector_inner_coefficient, mul_pow,
    dirichletPhaseVector_norm_sq, coefficientVector_norm_sq] at hsq
  exact hsq

/-- The coefficient-uniform Halász estimate, with every analytic input proved.
The logarithmic factor is displayed at the selected time-window scale. -/
theorem dirichletBlock_halasz_bound {M N : ℕ} (hM : 0 < M) (hN : N ≤ M)
    (S : Finset ℕ) (c : ℕ → ℂ) (t : ℕ → ℝ) {A B V : ℝ}
    (hAB : A ≤ B) (ht : ∀ i ∈ S, A ≤ t i ∧ t i ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|)
    (hV : 0 < V) (hlarge : ∀ i ∈ S, V ≤ ‖dirichletBlock M N c (t i)‖) :
    (S.card : ℝ) ≤
      5120 * M * Real.log ((V ^ 2 / (1280 * coefficientEnergy N c)) ^ 2 + 2) *
        (coefficientEnergy N c / V ^ 2 +
          1280 ^ 2 * (coefficientEnergy N c) ^ 3 * (B - A) / V ^ 6) := by
  let G := coefficientEnergy N c
  have hGnonneg : 0 ≤ G := coefficientEnergy_nonneg N c
  by_cases hGzero : G = 0
  · have hS : S = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨i, hi⟩
      have hbound := dirichletBlock_norm_sq_le M N c (t i)
      change ‖dirichletBlock M N c (t i)‖ ^ 2 ≤ N * G at hbound
      rw [hGzero, mul_zero] at hbound
      have hv := hlarge i hi
      nlinarith [norm_nonneg (dirichletBlock M N c (t i))]
    change (S.card : ℝ) ≤ 5120 * M * Real.log ((V ^ 2 / (1280 * G)) ^ 2 + 2) *
      (G / V ^ 2 + 1280 ^ 2 * G ^ 3 * (B - A) / V ^ 6)
    simp [hS, hGzero]
  · have hG : 0 < G := lt_of_le_of_ne hGnonneg (Ne.symm hGzero)
    let U := (V ^ 2 / (1280 * G)) ^ 2
    have hU : 0 < U := by dsimp only [U]; positivity
    have hsqrt : Real.sqrt U = V ^ 2 / (1280 * G) := Real.sqrt_sq (by positivity)
    have hwindow : 1280 * Real.sqrt U * coefficientEnergy N c ≤ V ^ 2 := by
      rw [hsqrt]
      change 1280 * (V ^ 2 / (1280 * G)) * G ≤ V ^ 2
      have heq : 1280 * (V ^ 2 / (1280 * G)) * G = V ^ 2 := by field_simp
      exact heq.le
    have h := dirichletBlock_large_values_subdivided hM hN S c t hAB hU ht hsep hV.le hlarge hwindow
    let L := Real.log (U + 2)
    have heq : (((B - A) / U + 1) * (5120 * M * L * G)) / V ^ 2 =
        5120 * M * L * (G / V ^ 2 + 1280 ^ 2 * G ^ 3 * (B - A) / V ^ 6) := by
      dsimp only [U]
      field_simp
      ring
    calc
      (S.card : ℝ) ≤ (((B - A) / U + 1) * (5120 * M * L * G)) / V ^ 2 :=
        (le_div_iff₀ (sq_pos_of_pos hV)).mpr h
      _ = _ := heq

/-- The usual length-dependent logarithmic factor in the Halász bound. -/
theorem dirichletBlock_halasz_log_bound {M N : ℕ} (hM : 0 < M) (hN : N ≤ M)
    (S : Finset ℕ) (c : ℕ → ℂ) (t : ℕ → ℝ) {A B V : ℝ}
    (hAB : A ≤ B) (ht : ∀ i ∈ S, A ≤ t i ∧ t i ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|)
    (hV : 0 < V) (hlarge : ∀ i ∈ S, V ≤ ‖dirichletBlock M N c (t i)‖) :
    (S.card : ℝ) ≤ 10240 * M * Real.log (M + 2 : ℝ) *
      (coefficientEnergy N c / V ^ 2 +
        1280 ^ 2 * (coefficientEnergy N c) ^ 3 * (B - A) / V ^ 6) := by
  let G := coefficientEnergy N c
  let Q := G / V ^ 2 + 1280 ^ 2 * G ^ 3 * (B - A) / V ^ 6
  have hG : 0 ≤ G := coefficientEnergy_nonneg N c
  have hM' : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hQ : 0 ≤ Q := by
    have hT := sub_nonneg.mpr hAB
    dsimp only [Q]
    positivity
  have hlogM : 0 ≤ Real.log (M + 2 : ℝ) := Real.log_nonneg (by linarith)
  change (S.card : ℝ) ≤ 10240 * M * Real.log (M + 2 : ℝ) * Q
  by_cases hS : S.Nonempty
  · obtain ⟨i, hi⟩ := hS
    have hv := hlarge i hi
    have hnorm := dirichletBlock_norm_sq_le M N c (t i)
    have hNM : (N : ℝ) ≤ M := by exact_mod_cast hN
    have hNG := mul_le_mul_of_nonneg_right hNM hG
    have hVG : V ^ 2 ≤ (M : ℝ) * G := by
      change ‖dirichletBlock M N c (t i)‖ ^ 2 ≤ N * G at hnorm
      nlinarith [norm_nonneg (dirichletBlock M N c (t i))]
    have hGp : 0 < G := by
      by_contra hnot
      have heq : G = 0 := le_antisymm (le_of_not_gt hnot) hG
      rw [heq, mul_zero] at hVG
      nlinarith
    have hratio : V ^ 2 / (1280 * G) ≤ M := by
      apply (div_le_iff₀ (by positivity : 0 < 1280 * G)).mpr
      nlinarith
    have hratpos : 0 ≤ V ^ 2 / (1280 * G) := by positivity
    have hsquare := pow_le_pow_left₀ hratpos hratio 2
    have hins : (V ^ 2 / (1280 * G)) ^ 2 + 2 ≤ (M + 2 : ℝ) ^ 2 := by nlinarith
    have hlog : Real.log ((V ^ 2 / (1280 * G)) ^ 2 + 2) ≤
        2 * Real.log (M + 2 : ℝ) := by
      have h := Real.log_le_log (by positivity) hins
      simpa only [Real.log_pow, Nat.cast_ofNat] using h
    have h := dirichletBlock_halasz_bound hM hN S c t hAB ht hsep hV hlarge
    change (S.card : ℝ) ≤ 5120 * M * Real.log ((V ^ 2 / (1280 * G)) ^ 2 + 2) * Q at h
    calc
      _ ≤ 5120 * M * Real.log ((V ^ 2 / (1280 * G)) ^ 2 + 2) * Q := h
      _ ≤ 5120 * M * (2 * Real.log (M + 2 : ℝ)) * Q :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by positivity)) hQ
      _ = _ := by ring
  · have heq := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [heq, Finset.card_empty, Nat.cast_zero]
    positivity

end Erdos421
