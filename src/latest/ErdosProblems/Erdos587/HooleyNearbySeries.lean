import ErdosProblems.Erdos587.HooleyFresnelClosedMean
import ErdosProblems.Erdos587.HooleyCauchy
import ErdosProblems.Erdos587.NearbyMean

/-! # Log-log means for the two reciprocal parity series -/

open scoped BigOperators SchwartzMap

namespace Erdos587

theorem exists_delta_nearby_reciprocal_series_sq_mean (f : 𝓢(ℝ, ℂ))
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v q R X : ℕ, 0 < v → 0 < q → 0 < R →
      q.Coprime v → 2 ≤ X → q ≤ X →
      ∀ K : ℝ, 1 ≤ K → 2 * K ≤ X → K < q →
      (v : ℝ) * K + 16 * q * R ≤ X → 2 * K * (X : ℝ) ^ κ ≤ R →
      ∀ (D : Finset ℕ) (inv : ℕ → ℤ), (∀ r ∈ D, R ≤ r ∧ r ≤ 2 * R) →
      (∀ r ∈ D, (r : ℤ) ∣ (q : ℤ) * inv r - 1) →
      ∀ L : ℝ, 0 < L → (∀ r ∈ D, 1 ≤ ((r : ℝ) / (q * v)) * L ^ 2) →
      (∀ r ∈ D, 1 / 2 ≤ ((v : ℝ) / (r * L)) * K ∧
        ((v : ℝ) / (r * L)) * K ≤ 2) →
      ∀ e : ℤ, (e = 0 ∨ e = 1) →
      (∑ r ∈ D, ‖nearbyReciprocalSeries f q r v L (inv r) e‖ ^ 2) ≤
        C * R * K * (max 1 (Real.log (Real.log (X : ℝ)))) ^ 7 := by
  obtain ⟨C, hC, hmean⟩ := exists_delta_fresnel_reciprocal_closed_sq_mean
    (Bornology.isVonNBounded_singleton (𝕜 := ℝ) f) 1 1 (by norm_num) (by norm_num) hκ
  refine ⟨C, hC, ?_⟩
  intro v q R X hv hq hR hcop hX hqX K hK hKX hqa hvalue hsep D inv hD hinv L hL
    hP hscale e he
  have hδ (r : ℕ) (hr : r ∈ D) : 0 < (v : ℝ) / (r * L) := by
    have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
    have hrR : 0 < (r : ℝ) := by exact_mod_cast (hR.trans_le (hD r hr).1)
    positivity
  have hu (r : ℕ) (hr : r ∈ D) : |((v : ℝ) / (r * L)) * e / 2| ≤ 1 := by
    have hδle : (v : ℝ) / (r * L) ≤ 2 := by
      nlinarith [hδ r hr, (hscale r hr).2]
    rcases he with rfl | rfl
    · simp
    · simp only [Int.cast_one, mul_one, abs_div, abs_of_pos (hδ r hr),
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
  have hrel (r : ℕ) (hr : r ∈ D) :
      ((1 * r : ℕ) : ℤ) ∣ (q : ℤ) * ((v : ℤ) * inv r) - (1 : ℤ) * v := by
    have hh := dvd_mul_of_dvd_right (hinv r hr) (v : ℤ)
    simpa only [one_mul, mul_sub, mul_one, mul_left_comm] using hh
  have hh := hmean q v X hq hcop hX hqX (fun r => (v : ℤ) * inv r) K R hK
    (by exact_mod_cast hR) hKX (by simpa only [Nat.cast_one, one_mul] using hqa)
    (by simpa only [Nat.cast_one, one_mul, mul_one] using hvalue) hsep D
    (by intro r hr; exact_mod_cast hD r hr) hrel (fun _ => f)
    (fun r => ((r : ℝ) / (q * v)) * L ^ 2)
    (fun r => ((v : ℝ) / (r * L)) * e / 2) (fun r => (v : ℝ) / (r * L))
    (fun r => -reciprocalQuadraticFrequency 1 v 1 inv r * e)
    (fun _ _ => Set.mem_singleton f) hP hu hscale
  simpa only [nearbyReciprocalSeries_eq_reciprocal_phase, reciprocalQuadraticFrequency,
    Nat.cast_one, one_mul, Int.cast_mul, Int.cast_natCast] using hh

theorem exists_delta_nearby_reciprocal_series_mean (f : 𝓢(ℝ, ℂ))
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v q R X : ℕ, 0 < v → 0 < q → 0 < R →
      q.Coprime v → 2 ≤ X → q ≤ X →
      ∀ K : ℝ, 1 ≤ K → 2 * K ≤ X → K < q →
      (v : ℝ) * K + 16 * q * R ≤ X → 2 * K * (X : ℝ) ^ κ ≤ R →
      ∀ (D : Finset ℕ) (inv : ℕ → ℤ), (∀ r ∈ D, R ≤ r ∧ r ≤ 2 * R) →
      (∀ r ∈ D, (r : ℤ) ∣ (q : ℤ) * inv r - 1) →
      ∀ L : ℝ, 0 < L → (∀ r ∈ D, 1 ≤ ((r : ℝ) / (q * v)) * L ^ 2) →
      (∀ r ∈ D, 1 / 2 ≤ ((v : ℝ) / (r * L)) * K ∧
        ((v : ℝ) / (r * L)) * K ≤ 2) →
      ∀ e : ℤ, (e = 0 ∨ e = 1) →
      (∑ r ∈ D, ‖nearbyReciprocalSeries f q r v L (inv r) e‖) ≤
        C * R * Real.sqrt K * (max 1 (Real.log (Real.log (X : ℝ)))) ^ (7 / 2 : ℝ) := by
  obtain ⟨C, hC, hmean⟩ := exists_delta_nearby_reciprocal_series_sq_mean f hκ
  refine ⟨C + 1, by positivity, ?_⟩
  intro v q R X hv hq hR hcop hX hqX K hK hKX hqa hvalue hsep D inv hD hinv L hL
    hP hscale e he
  have hh := hmean v q R X hv hq hR hcop hX hqX K hK hKX hqa hvalue hsep
    D inv hD hinv L hL hP hscale e he
  have hcard : (D.card : ℝ) ≤ 2 * R := by
    have hsub : D ⊆ Finset.Icc 1 (2 * R) := by
      intro r hr
      exact Finset.mem_Icc.mpr ⟨hR.trans_le (hD r hr).1, (hD r hr).2⟩
    have ht := Finset.card_le_card hsub
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at ht
    exact_mod_cast ht
  exact delta_sum_norm_le_of_seventh_power D
    (fun r => nearbyReciprocalSeries f q r v L (inv r) e) hC.le (Nat.cast_nonneg R)
    (by linarith) (by positivity) hcard hh

end Erdos587
