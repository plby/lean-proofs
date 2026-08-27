import ErdosProblems.Erdos587.HooleyNearbySeries

/-! # High-frequency nearby blocks with the seventh-half log-log power -/

open scoped BigOperators SchwartzMap

namespace Erdos587

lemma delta_reciprocal_prefactor_scale_le {R v : ℕ} (hR : 0 < R) {K L : ℝ}
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hscale : K * v ≤ 4 * R * L) :
    Real.sqrt ((v : ℝ) / R) * R * Real.sqrt K ≤ 2 * R * Real.sqrt L := by
  have hRR : 0 < (R : ℝ) := by exact_mod_cast hR
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  calc
    (Real.sqrt ((v : ℝ) / R) * R * Real.sqrt K) ^ 2 = (R : ℝ) * (K * v) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hK]
      field_simp
    _ ≤ (R : ℝ) * (4 * R * L) := mul_le_mul_of_nonneg_left hscale hRR.le
    _ = (2 * R * Real.sqrt L) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hL]
      ring

lemma delta_nearby_block_scale_bound {R v : ℕ} (hR : 0 < R)
    {K L C M F : ℝ} (hK : 1 ≤ K) (hL : 0 ≤ L) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hF : 1 ≤ F) (hscale : K * v ≤ 4 * R * L) :
    Real.sqrt ((v : ℝ) / R) *
        (2 * (C * R * Real.sqrt K * F) + 2 * R * M) ≤
      4 * (C + M) * R * Real.sqrt L * F := by
  have hKroot : 1 ≤ Real.sqrt K := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hK
  have hKF : 1 ≤ Real.sqrt K * F := one_le_mul_of_one_le_of_one_le hKroot hF
  have hMterm : 2 * (R : ℝ) * M ≤ 2 * R * M * (Real.sqrt K * F) :=
    le_mul_of_one_le_right (by positivity) hKF
  have hbracket : 2 * (C * R * Real.sqrt K * F) + 2 * R * M ≤
      2 * (C + M) * R * Real.sqrt K * F := by nlinarith [hMterm]
  calc
    _ ≤ Real.sqrt ((v : ℝ) / R) * (2 * (C + M) * R * Real.sqrt K * F) :=
      mul_le_mul_of_nonneg_left hbracket (Real.sqrt_nonneg _)
    _ = (2 * (C + M) * F) * (Real.sqrt ((v : ℝ) / R) * R * Real.sqrt K) := by ring
    _ ≤ (2 * (C + M) * F) * (2 * R * Real.sqrt L) :=
      mul_le_mul_of_nonneg_left
        (delta_reciprocal_prefactor_scale_le hR (by linarith) hL hscale) (by positivity)
    _ = _ := by ring

theorem exists_delta_nearby_high_frequency_block_mean (f : 𝓢(ℝ, ℂ))
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v q R X : ℕ, 0 < v → 0 < q → 0 < R →
      q.Coprime v → 2 ≤ X → q ≤ X →
      ∀ K : ℝ, 1 ≤ K → 2 * K ≤ X → K < q →
      (v : ℝ) * K + 16 * q * R ≤ X → 2 * K * (X : ℝ) ^ κ ≤ R →
      ∀ (D : Finset ℕ) (inv : ℕ → ℤ), (∀ r ∈ D, R ≤ r ∧ r ≤ 2 * R) →
      (∀ r ∈ D, (r : ℤ) ∣ (q : ℤ) * inv r - 1) →
      ∀ L : ℝ, 0 < L → (∀ r ∈ D, 1 ≤ ((r : ℝ) / (q * v)) * L ^ 2) →
      (∀ r ∈ D, 1 / 2 ≤ ((v : ℝ) / (r * L)) * K ∧
        ((v : ℝ) / (r * L)) * K ≤ 2) → K * v ≤ 4 * R * L →
      ∀ (b : ℤ) (B : ℕ → ℤ), (q : ℤ) ∣ b * v + 1 →
      (∀ r ∈ D, (q : ℤ) ∣ (r : ℤ) * b * B r - 1) →
      (∑ r ∈ D, ‖nearbyQuadraticRemainder f q r v b L‖) ≤
        C * R * Real.sqrt L * (max 1 (Real.log (Real.log (X : ℝ)))) ^ (7 / 2 : ℝ) := by
  obtain ⟨C, hC, hseries⟩ := exists_delta_nearby_reciprocal_series_mean f hκ
  obtain ⟨M, hM, hprofile⟩ := exists_uniform_fresnelProfile_derivative_bound f 0 0
  refine ⟨4 * (C + M) + 1, by positivity, ?_⟩
  intro v q R X hv hq hR hcop hX hqX K hK hKX hqa hvalue hsep D inv hD hinv L hL
    hP hscale hKL b B hbv hB
  have hzero : ∀ r ∈ D, ‖fresnelProfile f (((r : ℝ) / (q * v)) * L ^ 2) 0‖ ≤ M := by
    intro r hr
    simpa only [pow_zero, one_mul, iteratedDeriv_zero] using hprofile _ (hP r hr) 0
  have h₀ := hseries v q R X hv hq hR hcop hX hqX K hK hKX hqa hvalue hsep
    D inv hD hinv L hL hP hscale 0 (Or.inl rfl)
  have h₁ := hseries v q R X hv hq hR hcop hX hqX K hK hKX hqa hvalue hsep
    D inv hD hinv L hL hP hscale 1 (Or.inr rfl)
  have hbase := sum_nearbyQuadraticRemainder_le_of_series_means f hq hv hR D hD hL
    b B inv hB hbv hinv hM hzero h₀ h₁
  have hF : 1 ≤ (max 1 (Real.log (Real.log (X : ℝ)))) ^ (7 / 2 : ℝ) :=
    Real.one_le_rpow (le_max_left _ _) (by norm_num)
  apply hbase.trans
  apply (delta_nearby_block_scale_bound hR hK hL.le hC.le hM hF hKL).trans
  gcongr
  linarith

end Erdos587
