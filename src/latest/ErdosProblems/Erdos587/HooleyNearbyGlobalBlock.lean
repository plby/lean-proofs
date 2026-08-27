import ErdosProblems.Erdos587.HooleyNearbyParameters

/-! # Uniform log-log bounds in every nearby gcd block -/

open scoped BigOperators SchwartzMap

namespace Erdos587

theorem exists_delta_nearby_high_block_global_mean (f : 𝓢(ℝ, ℂ))
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a u v M M₀ X : ℕ,
      0 < u → 0 < v → a.Coprime u → u.Coprime v → u ∣ a * v + 1 →
      2 ≤ X → u ≤ X → ∀ L : ℝ, 0 < L → (u : ℝ) * v / L ^ 2 < M₀ + 1 →
      4 * L * (X : ℝ) ^ κ ≤ v → 4 * (M : ℝ) * L ≤ u * v →
      (4 * L + 16 * u) * M ≤ X →
      ∀ d ∈ u.divisors, ∀ R : ℕ, 0 < R →
      (∑ r ∈ nearbyHighBlock (u / d) v M M₀ d R L,
        ‖nearbyQuadraticRemainder f u (d * r) v (a : ℤ) L‖) ≤
        C * R * Real.sqrt L * (max 1 (Real.log (Real.log (X : ℝ)))) ^ (7 / 2 : ℝ) := by
  obtain ⟨C, hC, hblock⟩ := exists_delta_nearby_high_frequency_block_mean f hκ
  refine ⟨C, hC, ?_⟩
  intro a u v M M₀ X hu hv ha huv hav hX huX L hL hcutoff hsep hglobal hsize d hd R hR
  classical
  let q := u / d
  let D := nearbyHighBlock q v M M₀ d R L
  change (∑ r ∈ D, ‖nearbyQuadraticRemainder f u (d * r) v (a : ℤ) L‖) ≤ _
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdvd : d ∣ u := (Nat.mem_divisors.mp hd).1
  have hq : 0 < q := Nat.div_pos (Nat.le_of_dvd hu hdvd) hdpos
  have hdq : d * q = u := Nat.mul_div_cancel' hdvd
  have hqdiv : q ∣ u := ⟨d, by simpa only [mul_comm] using hdq.symm⟩
  by_cases hD : D.Nonempty
  · obtain ⟨r₀, hr₀⟩ := hD
    obtain ⟨⟨hRr₀, hr₀R⟩, _, _, hupper₀, hwide₀⟩ :=
      (mem_nearbyHighBlock q v M M₀ d R r₀ L).mp hr₀
    have hwidth := large_dual_width_implies_block_width hv hL hr₀R hwide₀
    have hdR : d * R ≤ M := (Nat.mul_le_mul_left d hRr₀).trans hupper₀
    obtain ⟨hK, hKX, hKq, hvalue, hpower, hKL⟩ :=
      delta_nearby_global_block_parameters hdpos hq hv hR hdq hdR hL hwidth hsep hglobal hsize
    have hDv (r : ℕ) (hr : r ∈ D) := (mem_nearbyHighBlock q v M M₀ d R r L).mp hr
    have hDr : ∀ r ∈ D, R ≤ r ∧ r ≤ 2 * R := fun r hr => (hDv r hr).1
    have hqv : q.Coprime v := Nat.Coprime.of_dvd_left hqdiv huv
    have haq : a.Coprime q := Nat.Coprime.of_dvd_right hqdiv ha
    have hinv : ∀ r ∈ D, (r : ℤ) ∣ (q : ℤ) * Nat.gcdA q r - 1 := by
      intro r hr
      exact gcdA_inverse_congruence (hDv r hr).2.1.symm
    have hB : ∀ r ∈ D, (q : ℤ) ∣ (r : ℤ) * a * Nat.gcdA (r * a) q - 1 := by
      intro r hr
      have hh := gcdA_inverse_congruence ((hDv r hr).2.1.mul_left haq)
      simpa only [Nat.cast_mul] using hh
    have hbv : (q : ℤ) ∣ (a : ℤ) * v + 1 := by exact_mod_cast hqdiv.trans hav
    have hA : ∀ r ∈ D, 1 ≤ ((r : ℝ) / (q * v)) * L ^ 2 := by
      intro r hr
      exact high_profile_parameter_ge_one hdpos hq hv hL hdq hcutoff (hDv r hr).2.2.1
    have hscale : ∀ r ∈ D,
        1 / 2 ≤ ((v : ℝ) / (r * L)) * (2 * R * L / v) ∧
          ((v : ℝ) / (r * L)) * (2 * R * L / v) ≤ 2 := by
      intro r hr
      exact delta_nearby_profile_scale hR hv hL (hDr r hr).1 (hDr r hr).2
    have hh := hblock v q R X hv hq hR hqv hX ((Nat.div_le_self u d).trans huX)
      (2 * R * L / v) hK hKX hKq hvalue hpower
      D (fun r => Nat.gcdA q r) hDr hinv L hL hA hscale hKL (a : ℤ)
      (fun r => Nat.gcdA (r * a) q) hbv hB
    have heq (r : ℕ) : nearbyQuadraticRemainder f u (d * r) v (a : ℤ) L =
        nearbyQuadraticRemainder f q r v (a : ℤ) L := by
      rw [← hdq]
      exact nearbyQuadraticRemainder_mul f hdpos hq r v (a : ℤ) L
    simp_rw [heq]
    exact hh
  · rw [Finset.not_nonempty_iff_eq_empty.mp hD, Finset.sum_empty]
    positivity

end Erdos587
