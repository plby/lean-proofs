import ErdosProblems.Erdos587.HooleySmallDenominator
import ErdosProblems.Erdos587.CenteredQuadratic

/-! # Exact reduction of the smooth quadratic mean and centered error -/

open scoped FourierTransform SchwartzMap

namespace Erdos587

lemma delta_smooth_mean_mul (f : 𝓢(ℝ, ℂ)) (K : ℝ) {d q : ℕ}
    (hd : 0 < d) (hq : 0 < q) (a : ℤ) :
    deltaSmoothQuadraticMean f K (d * q) ((d : ℤ) * a) =
      deltaSmoothQuadraticMean f K q a := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [deltaSmoothQuadraticMean, deltaSmoothQuadraticMean, completeQuadraticGaussSum_mul hd hq]
  push_cast
  field_simp

lemma delta_smooth_centered_mul (f : 𝓢(ℝ, ℂ)) (K : ℝ) {d q : ℕ}
    (hd : 0 < d) (hq : 0 < q) (a : ℤ) :
    deltaSmoothCenteredQuadratic f K (d * q) ((d : ℤ) * a) =
      deltaSmoothCenteredQuadratic f K q a := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [deltaSmoothCenteredQuadratic, deltaSmoothCenteredQuadratic, delta_smooth_mean_mul f K hd hq]
  congr 2
  push_cast
  field_simp

theorem delta_smooth_quadratic_reduction (f : 𝓢(ℝ, ℂ)) (K : ℝ) {q : ℕ}
    (hq : 0 < q) (a : ℕ) :
    let d := a.gcd q
    let Q := q / d
    let A := a / d
    0 < Q ∧ IsUnit (A : ZMod Q) ∧
      deltaSmoothQuadraticMean f K q a = deltaSmoothQuadraticMean f K Q A ∧
      deltaSmoothCenteredQuadratic f K q a = deltaSmoothCenteredQuadratic f K Q A := by
  let d := a.gcd q
  let A := a / d
  let Q := q / d
  have hd : 0 < d := Nat.gcd_pos_of_pos_right a hq
  have hQ : 0 < Q := Nat.div_pos (Nat.gcd_le_right a hq) hd
  have hA : A.Coprime Q := Nat.coprime_div_gcd_div_gcd hd
  have hqa : d * Q = q := Nat.mul_div_cancel' (Nat.gcd_dvd_right a q)
  have haa : d * A = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a q)
  refine ⟨hQ, (ZMod.isUnit_iff_coprime A Q).mpr hA, ?_, ?_⟩
  · change deltaSmoothQuadraticMean f K q a = deltaSmoothQuadraticMean f K Q A
    calc
      _ = deltaSmoothQuadraticMean f K (d * Q) ((d : ℤ) * A) := by
        rw [hqa, ← Nat.cast_mul, haa]
      _ = _ := delta_smooth_mean_mul f K hd hQ A
  · change deltaSmoothCenteredQuadratic f K q a = deltaSmoothCenteredQuadratic f K Q A
    calc
      _ = deltaSmoothCenteredQuadratic f K (d * Q) ((d : ℤ) * A) := by
        rw [hqa, ← Nat.cast_mul, haa]
      _ = _ := delta_smooth_centered_mul f K hd hQ A

theorem exists_delta_small_reduced_denominator_centered_sq_bound {W : Set 𝓢(ℝ, ℂ)}
    (hW : Bornology.IsVonNBounded ℝ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ W, ∀ a q : ℕ, 0 < q → q.Coprime a →
      ∀ (m : ℕ) (K : ℝ), 0 < K → (q / q.gcd m : ℕ) ≤ K →
      ‖deltaSmoothCenteredQuadratic f K q (a * m)‖ ^ 2 ≤ C * K := by
  obtain ⟨C, hC, hbound⟩ := exists_delta_small_denominator_centered_sq_bound hW
  refine ⟨C, hC, ?_⟩
  intro f hf a q hq hcop m K hK hden
  obtain ⟨hQ, hA, hmean, hcenter⟩ := delta_smooth_quadratic_reduction f K hq (a * m)
  rw [← Nat.cast_mul, hcenter]
  apply hbound f hf _ hQ _ (by simpa only [Int.cast_natCast] using hA) K hK
  simpa only [hcop.symm.gcd_mul_left_cancel m, Nat.gcd_comm m q] using hden

theorem exists_delta_large_reduced_denominator_zero_mode_sq_bound {W : Set 𝓢(ℝ, ℂ)}
    (hW : Bornology.IsVonNBounded ℝ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ W, ∀ a q : ℕ, 0 < q → q.Coprime a →
      ∀ (m : ℕ) (K : ℝ), 0 < K → K ≤ (q / q.gcd m : ℕ) →
      ‖deltaSmoothQuadraticMean f K q (a * m)‖ ^ 2 ≤ C * K := by
  obtain ⟨C, hC, hbound⟩ := exists_delta_large_denominator_zero_mode_sq_bound hW
  refine ⟨C, hC, ?_⟩
  intro f hf a q hq hcop m K hK hden
  obtain ⟨hQ, hA, hmean, hcenter⟩ := delta_smooth_quadratic_reduction f K hq (a * m)
  rw [← Nat.cast_mul, hmean]
  apply hbound f hf _ hQ _ (by simpa only [Int.cast_natCast] using hA) K hK
  simpa only [hcop.symm.gcd_mul_left_cancel m, Nat.gcd_comm m q] using hden

end Erdos587
