import ErdosProblems.Erdos587.NearbyReciprocity
import ErdosProblems.Erdos587.FresnelSeries

/-!
# High-frequency blocks in the nearby rational mean

Exact centered Poisson reciprocity is combined with the full Fresnel-weighted
reciprocal mean. All modulus and scale hypotheses are explicit.
-/

open scoped BigOperators SchwartzMap

namespace Erdos587

lemma nearbyReciprocalSeries_eq_reciprocal_phase (f : 𝓢(ℝ, ℂ)) (q r v : ℕ)
    (L : ℝ) (inv : ℕ → ℤ) (e : ℤ) :
    nearbyReciprocalSeries f q r v L (inv r) e =
      ∑' n : ℤ, fresnelProfile f (((r : ℝ) / (q * v)) * L ^ 2)
        (((v : ℝ) / (r * L)) * e / 2 + ((v : ℝ) / (r * L)) * n) *
        phase (-reciprocalQuadraticFrequency 1 v 1 inv r * (n : ℝ) ^ 2 +
          (-reciprocalQuadraticFrequency 1 v 1 inv r * e) * n) := by
  unfold nearbyReciprocalSeries
  apply tsum_congr
  intro n
  apply congrArg₂ (· * ·)
  · congr 1
    ring
  · congr 1
    simp only [reciprocalQuadraticFrequency, one_mul]
    push_cast
    ring

theorem exists_nearby_reciprocal_series_mean_bound (j : ℕ) (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (v q R K : ℕ), 0 < v → 3 ≤ K → K ≤ R → 16 * K < q → q.Coprime v →
        64 * (q * R + v * K + 1) ≤ (R / K) ^ (4 ^ j) →
        ∀ (D : Finset ℕ) (inv : ℕ → ℤ),
          (∀ r ∈ D, 0 < r ∧ r ≤ 2 * R) →
          (∀ r ∈ D, (r : ℤ) ∣ (q : ℤ) * inv r - 1) →
          ∀ L : ℝ, 0 < L →
            (∀ r ∈ D, 1 ≤ ((r : ℝ) / (q * v)) * L ^ 2) →
            (∀ r ∈ D, 1 / 2 ≤ ((v : ℝ) / (r * L)) * K ∧
              ((v : ℝ) / (r * L)) * K ≤ 2) →
            ∀ e : ℤ, (e = 0 ∨ e = 1) →
            (∑ r ∈ D, ‖nearbyReciprocalSeries f q r v L (inv r) e‖) ≤
              C * R * Real.sqrt K * Real.log (35 * (R : ℝ)) ^ O := by
  obtain ⟨C, hC, O, hO, hseries⟩ := exists_reciprocal_fresnel_series_bound j f
  refine ⟨C, hC, O, hO, ?_⟩
  intro v q R K hv hK hKR hq hcop hroot D inv hD hinv L hL hA hscale e he
  have hδ (r : ℕ) (hr : r ∈ D) : 0 < (v : ℝ) / (r * L) := by
    have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
    have hrR : 0 < (r : ℝ) := by exact_mod_cast (hD r hr).1
    positivity
  have hu (r : ℕ) (hr : r ∈ D) : |((v : ℝ) / (r * L)) * e / 2| ≤ 1 := by
    have hδle : (v : ℝ) / (r * L) ≤ 2 := by
      have hKK : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
      nlinarith [hδ r hr, (hscale r hr).2]
    rcases he with rfl | rfl
    · simp
    · simp only [Int.cast_one, mul_one, abs_div, abs_of_pos (hδ r hr),
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
  simp_rw [nearbyReciprocalSeries_eq_reciprocal_phase]
  apply hseries 1 v q 1 R K (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hK hKR hq hcop hroot D inv hD
  · simpa only [one_mul] using hinv
  · exact hA
  · exact hu
  · exact hδ
  · exact hscale

lemma reciprocal_prefactor_scale_le {R K v : ℕ} (hR : 0 < R) {L : ℝ} (hL : 0 ≤ L)
    (hscale : (K : ℝ) * v ≤ 4 * R * L) :
    Real.sqrt ((v : ℝ) / R) * R * Real.sqrt K ≤ 2 * R * Real.sqrt L := by
  have hRR : 0 < (R : ℝ) := by exact_mod_cast hR
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  calc
    (Real.sqrt ((v : ℝ) / R) * R * Real.sqrt K) ^ 2 = (R : ℝ) * (K * v) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (Nat.cast_nonneg K)]
      field_simp
    _ ≤ (R : ℝ) * (4 * R * L) := mul_le_mul_of_nonneg_left hscale hRR.le
    _ = (2 * R * Real.sqrt L) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hL]
      ring

lemma nearby_block_scale_bound {R K v : ℕ} (hR : 0 < R) (hK : 1 ≤ K)
    {L C M F : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C) (hM : 0 ≤ M) (hF : 1 ≤ F)
    (hscale : (K : ℝ) * v ≤ 4 * R * L) :
    Real.sqrt ((v : ℝ) / R) *
        (2 * (C * R * Real.sqrt K * F) + 2 * R * M) ≤
      4 * (C + M) * R * Real.sqrt L * F := by
  have hKroot : 1 ≤ Real.sqrt K := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ K by exact_mod_cast hK)
    simpa only [Real.sqrt_one] using h
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
      mul_le_mul_of_nonneg_left (reciprocal_prefactor_scale_le hR hL hscale) (by positivity)
    _ = _ := by ring

lemma sum_nearbyQuadraticRemainder_le_of_series_means (f : 𝓢(ℝ, ℂ)) {q v R : ℕ}
    (hq : 0 < q) (hv : 0 < v) (hR : 0 < R) (D : Finset ℕ)
    (hD : ∀ r ∈ D, R ≤ r ∧ r ≤ 2 * R) {L : ℝ} (hL : 0 < L)
    (b : ℤ) (B inv : ℕ → ℤ) (hB : ∀ r ∈ D, (q : ℤ) ∣ (r : ℤ) * b * B r - 1)
    (hbv : (q : ℤ) ∣ b * (v : ℤ) + 1)
    (hinv : ∀ r ∈ D, (r : ℤ) ∣ (q : ℤ) * inv r - 1)
    {S M : ℝ} (hM : 0 ≤ M)
    (hzero : ∀ r ∈ D, ‖fresnelProfile f (((r : ℝ) / (q * v)) * L ^ 2) 0‖ ≤ M)
    (hseries₀ : (∑ r ∈ D, ‖nearbyReciprocalSeries f q r v L (inv r) 0‖) ≤ S)
    (hseries₁ : (∑ r ∈ D, ‖nearbyReciprocalSeries f q r v L (inv r) 1‖) ≤ S) :
    (∑ r ∈ D, ‖nearbyQuadraticRemainder f q r v b L‖) ≤
      Real.sqrt ((v : ℝ) / R) * (2 * S + 2 * R * M) := by
  have hRreal : 0 < (R : ℝ) := by exact_mod_cast hR
  have hcard : D.card ≤ 2 * R := by
    have hsub : D ⊆ Finset.Icc 1 (2 * R) := by
      intro r hr
      exact Finset.mem_Icc.mpr ⟨hR.trans_le (hD r hr).1, (hD r hr).2⟩
    simpa using Finset.card_le_card hsub
  have hsumzero : (∑ r ∈ D, ‖fresnelProfile f (((r : ℝ) / (q * v)) * L ^ 2) 0‖) ≤
      2 * R * M := by
    apply (Finset.sum_le_sum hzero).trans
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM
  calc
    _ ≤ ∑ r ∈ D, Real.sqrt ((v : ℝ) / R) *
        (‖nearbyReciprocalSeries f q r v L (inv r) 0‖ +
          ‖nearbyReciprocalSeries f q r v L (inv r) 1‖ +
          ‖fresnelProfile f (((r : ℝ) / (q * v)) * L ^ 2) 0‖) := by
      apply Finset.sum_le_sum
      intro r hr
      apply (norm_nearbyQuadraticRemainder_le f hq (hR.trans_le (hD r hr).1) hv hL
        b (B r) (inv r) (hB r hr) hbv (hinv r hr)).trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply Real.sqrt_le_sqrt
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg v) hRreal
        (by exact_mod_cast (hD r hr).1)
    _ = Real.sqrt ((v : ℝ) / R) *
        ((∑ r ∈ D, ‖nearbyReciprocalSeries f q r v L (inv r) 0‖) +
          (∑ r ∈ D, ‖nearbyReciprocalSeries f q r v L (inv r) 1‖) +
          (∑ r ∈ D, ‖fresnelProfile f (((r : ℝ) / (q * v)) * L ^ 2) 0‖)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ Real.sqrt ((v : ℝ) / R) * (2 * S + 2 * R * M) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      linarith

/-- A full high-frequency denominator block has mean error
`R * sqrt L * log(35*R)^O`. The reciprocal counting margin, profile scale,
and Fourier block width are all explicit; no main term is hidden in the error. -/
theorem exists_nearby_high_frequency_block_bound (j : ℕ) (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (v q R K : ℕ), 0 < v → 3 ≤ K → K ≤ R → 16 * K < q → q.Coprime v →
        64 * (q * R + v * K + 1) ≤ (R / K) ^ (4 ^ j) →
        ∀ (D : Finset ℕ) (inv : ℕ → ℤ),
          (∀ r ∈ D, R ≤ r ∧ r ≤ 2 * R) →
          (∀ r ∈ D, (r : ℤ) ∣ (q : ℤ) * inv r - 1) →
          ∀ L : ℝ, 0 < L →
            (∀ r ∈ D, 1 ≤ ((r : ℝ) / (q * v)) * L ^ 2) →
            (∀ r ∈ D, 1 / 2 ≤ ((v : ℝ) / (r * L)) * K ∧
              ((v : ℝ) / (r * L)) * K ≤ 2) →
            (K : ℝ) * v ≤ 4 * R * L →
            ∀ (b : ℤ) (B : ℕ → ℤ), (q : ℤ) ∣ b * (v : ℤ) + 1 →
              (∀ r ∈ D, (q : ℤ) ∣ (r : ℤ) * b * B r - 1) →
              (∑ r ∈ D, ‖nearbyQuadraticRemainder f q r v b L‖) ≤
                C * R * Real.sqrt L * Real.log (35 * (R : ℝ)) ^ O := by
  obtain ⟨C, hC, O, hO, hseries⟩ := exists_nearby_reciprocal_series_mean_bound j f
  obtain ⟨M, hM, hprofile⟩ := exists_uniform_fresnelProfile_derivative_bound f 0 0
  refine ⟨4 * (C + M) + 1, by positivity, O, hO, ?_⟩
  intro v q R K hv hK hKR hq hcop hroot D inv hD hinv L hL hA hscale hKL b B hbv hB
  have hR : 0 < R := by omega
  have hqpos : 0 < q := by omega
  have hDpos : ∀ r ∈ D, 0 < r ∧ r ≤ 2 * R := by
    intro r hr
    exact ⟨hR.trans_le (hD r hr).1, (hD r hr).2⟩
  have hzero : ∀ r ∈ D, ‖fresnelProfile f (((r : ℝ) / (q * v)) * L ^ 2) 0‖ ≤ M := by
    intro r hr
    simpa only [pow_zero, one_mul, iteratedDeriv_zero] using
      hprofile _ (hA r hr) 0
  have h₀ := hseries v q R K hv hK hKR hq hcop hroot D inv hDpos hinv
    L hL hA hscale 0 (Or.inl rfl)
  have h₁ := hseries v q R K hv hK hKR hq hcop hroot D inv hDpos hinv
    L hL hA hscale 1 (Or.inr rfl)
  have hbase := sum_nearbyQuadraticRemainder_le_of_series_means f hqpos hv hR D hD hL
    b B inv hB hbv hinv hM hzero h₀ h₁
  have hlog : 1 ≤ Real.log (35 * (R : ℝ)) := by
    apply (one_le_log_nat_of_three_le hK).trans
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < K))
    have hKR' : (K : ℝ) ≤ R := by exact_mod_cast hKR
    have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    linarith
  have hF : 1 ≤ Real.log (35 * (R : ℝ)) ^ O := one_le_pow₀ hlog
  apply hbase.trans
  apply (nearby_block_scale_bound hR (by omega : 1 ≤ K) hL.le hC.le hM hF hKL).trans
  gcongr
  linarith

end Erdos587
