import ErdosProblems.Erdos587.HooleyCenteredPowerMean

/-!
# The centered quadratic mean at an arbitrary fixed power separation

The dyadic scale and integer progression parameter are eliminated. The
constant is uniform over a bounded Schwartz family and depends only on
that family and the fixed positive separation exponent.
-/

open scoped BigOperators FourierTransform SchwartzMap

namespace Erdos587

theorem exists_delta_smooth_centered_mean {W : Set 𝓢(ℝ, ℂ)}
    (hW : Bornology.IsVonNBounded ℝ W) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a M q X : ℕ, 1 ≤ M → 0 < q → q.Coprime a →
      ∀ K : ℝ, 1 ≤ K → 2 * (M : ℝ) * K ≤ X →
      (q : ℝ) * (X : ℝ) ^ κ ≤ (M : ℝ) * K →
      ∀ f : ℕ → 𝓢(ℝ, ℂ), (∀ m ∈ Finset.Icc 1 M, f m ∈ W) →
      (∑ m ∈ Finset.Icc 1 M, ‖deltaSmoothCenteredQuadratic (f m) K q (a * m)‖ ^ 2) ≤
        C * M * K * (max 1 (Real.log (Real.log (X : ℝ)))) ^ 7 := by
  obtain ⟨r, hrlarge⟩ := exists_nat_gt (3 / κ)
  have hrR : (0 : ℝ) < r := lt_trans (by positivity : 0 < 3 / κ) hrlarge
  have hr : 0 < r := by exact_mod_cast hrR
  have hexponent : 3 / (r : ℝ) ≤ κ := by
    apply (div_le_iff₀ hrR).mpr
    have h := (div_lt_iff₀ hκ).mp hrlarge
    nlinarith
  obtain ⟨C, hC, hmean⟩ := exists_delta_smooth_centered_power_mean hW r hr
  refine ⟨2 * C, by positivity, ?_⟩
  intro a M q X hM hq hcop K hK hX hsep f hf
  obtain ⟨D, hKD, hDK⟩ := exists_delta_dyadic_scale hK
  let N := M * 2 ^ D
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMK1 : 1 ≤ (M : ℝ) * K := by nlinarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hNlo : (M : ℝ) * K ≤ N := by
    have h := mul_le_mul_of_nonneg_left hKD hM0
    simpa only [N, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h
  have hNhi : (N : ℝ) ≤ 2 * M * K := by
    have h := mul_le_mul_of_nonneg_left hDK hM0
    simp only [N, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    nlinarith
  have hNX : N ≤ X := by exact_mod_cast hNhi.trans hX
  have hpower : (N : ℝ) ^ (3 / (r : ℝ)) ≤ (X : ℝ) ^ κ := by
    calc
      _ ≤ (X : ℝ) ^ (3 / (r : ℝ)) :=
        Real.rpow_le_rpow (Nat.cast_nonneg N) (by exact_mod_cast hNX) (by positivity)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hX1 hexponent
  have hsepN : (q : ℝ) * (N : ℝ) ^ (3 / (r : ℝ)) ≤ N := by
    exact (mul_le_mul_of_nonneg_left hpower (Nat.cast_nonneg q)).trans (hsep.trans hNlo)
  have h := hmean a M q D hM hq hcop hsepN K hK hKD f hf
  have hlog : (max 1 (Real.log (Real.log (N : ℝ)))) ^ 7 ≤
      (max 1 (Real.log (Real.log (X : ℝ)))) ^ 7 :=
    pow_le_pow_left₀ (by positivity) (delta_loglog_nat_mono hNX) 7
  calc
    _ ≤ C * (N : ℝ) * (max 1 (Real.log (Real.log (N : ℝ)))) ^ 7 := h
    _ ≤ C * (N : ℝ) * (max 1 (Real.log (Real.log (X : ℝ)))) ^ 7 :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ C * (2 * M * K) * (max 1 (Real.log (Real.log (X : ℝ)))) ^ 7 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNhi hC.le) (by positivity)
    _ = _ := by ring

end Erdos587
