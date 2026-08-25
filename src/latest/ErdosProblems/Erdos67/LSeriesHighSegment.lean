import ErdosProblems.Erdos67.LSeriesLowCutoff

/-! # Absolute control of a bounded-ratio high segment -/

open scoped BigOperators

namespace Erdos67.LSeriesHighSegment

noncomputable section

/-- Absolute convergence bounds a finite character L-series segment by its
harmonic mass. -/
theorem norm_sum_Ioc_character_LSeries_term_le_harmonic_sub
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t sigma : ℝ)
    {K H : ℕ} (hKH : K ≤ H) (hsigma : 1 ≤ sigma) :
    ‖∑ n ∈ Finset.Ioc K H,
        LSeries.term (fun m : ℕ ↦ chi m)
          ((sigma : ℂ) + Complex.I * (t : ℂ)) n‖ ≤
      (harmonic H : ℝ) - harmonic K := by
  have hsum : (∑ n ∈ Finset.Ioc K H, ((n : ℝ) : ℝ)⁻¹) =
      (harmonic H : ℝ) - harmonic K := by
    have hunion : Finset.Icc 1 K ∪ Finset.Ioc K H = Finset.Icc 1 H := by
      ext n
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    have hdis : Disjoint (Finset.Icc 1 K) (Finset.Ioc K H) := by
      refine Finset.disjoint_left.2 ?_
      intro n hn₁ hn₂
      simp only [Finset.mem_Icc] at hn₁
      simp only [Finset.mem_Ioc] at hn₂
      omega
    have hadd :
        (∑ n ∈ Finset.Icc 1 K, ((n : ℝ) : ℝ)⁻¹) +
          ∑ n ∈ Finset.Ioc K H, ((n : ℝ) : ℝ)⁻¹ =
        ∑ n ∈ Finset.Icc 1 H, ((n : ℝ) : ℝ)⁻¹ := by
      rw [← Finset.sum_union hdis, hunion]
    rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    linarith
  calc
    ‖∑ n ∈ Finset.Ioc K H,
        LSeries.term (fun m : ℕ ↦ chi m)
          ((sigma : ℂ) + Complex.I * (t : ℂ)) n‖ ≤
        ∑ n ∈ Finset.Ioc K H,
          ‖LSeries.term (fun m : ℕ ↦ chi m)
            ((sigma : ℂ) + Complex.I * (t : ℂ)) n‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ioc K H, ((n : ℝ) : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := by
        have := (Finset.mem_Ioc.mp hn).1
        omega
      rw [LSeries.norm_term_eq, if_neg hnpos.ne']
      have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      have hre : (((sigma : ℂ) + Complex.I * (t : ℂ)).re) = sigma := by simp
      rw [hre]
      have hpow : (n : ℝ) ^ sigma ≥ n := by
        have := Real.rpow_le_rpow_of_exponent_le hnOne hsigma
        simpa only [Real.rpow_one] using this
      calc
        ‖chi n‖ / (n : ℝ) ^ sigma ≤ 1 / (n : ℝ) ^ sigma := by
          gcongr
          exact chi.norm_le_one n
        _ ≤ 1 / n := by
          exact one_div_le_one_div_of_le (by positivity) hpow
        _ = ((n : ℝ) : ℝ)⁻¹ := one_div _
    _ = (harmonic H : ℝ) - harmonic K := hsum

/-- If the endpoints differ by at most a fixed multiplicative factor, the
whole high segment costs only an absolute constant. -/
theorem norm_sum_Ioc_character_LSeries_term_le_one_add_log
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t sigma : ℝ)
    {K H C : ℕ} (hKH : K ≤ H) (hC : 0 < C)
    (hH : 0 < H) (hHC : H ≤ C * (K + 1)) (hsigma : 1 ≤ sigma) :
    ‖∑ n ∈ Finset.Ioc K H,
        LSeries.term (fun m : ℕ ↦ chi m)
          ((sigma : ℂ) + Complex.I * (t : ℂ)) n‖ ≤
      1 + Real.log C := by
  have hraw := norm_sum_Ioc_character_LSeries_term_le_harmonic_sub
    chi t sigma hKH hsigma
  have hupper := harmonic_le_one_add_log H
  have hlower := log_add_one_le_harmonic K
  have hKpos : (0 : ℝ) < K + 1 := by positivity
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  have hHpos : (0 : ℝ) < C * (K + 1) := mul_pos hCpos hKpos
  have hlog : Real.log H ≤ Real.log C + Real.log (K + 1) := by
    calc
      Real.log H ≤ Real.log (C * (K + 1)) :=
        Real.log_le_log (by exact_mod_cast hH) (by exact_mod_cast hHC)
      _ = Real.log C + Real.log (K + 1) := by
        rw [Real.log_mul hCpos.ne' hKpos.ne']
  calc
    ‖∑ n ∈ Finset.Ioc K H,
        LSeries.term (fun m : ℕ ↦ chi m)
          ((sigma : ℂ) + Complex.I * (t : ℂ)) n‖ ≤
        (harmonic H : ℝ) - harmonic K := hraw
    _ ≤ (1 + Real.log H) - Real.log (K + 1) := by
      apply sub_le_sub hupper
      simpa only [Nat.cast_add, Nat.cast_one] using hlower
    _ ≤ 1 + Real.log C := by linarith

end

end Erdos67.LSeriesHighSegment
