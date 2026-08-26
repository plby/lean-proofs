import ErdosProblems.Erdos421.SmoothedPerron
import ErdosProblems.Erdos421.ZetaLogDerivativePositivity

/-! # The smoothed Perron formula for the actual von Mangoldt coefficients -/

namespace Erdos421

open Complex MeasureTheory

theorem triangularMellin_tsum_eq_finite (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    (∑' n : ℕ, LSeries.term a (t * I) n * triangularMellinWeight ((n : ℝ) / x)) =
      ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
        LSeries.term a (t * I) n * ((1 - (n : ℝ) / x : ℝ) : ℂ) := by
  classical
  have hzero : ∀ n : ℕ, n ∉ Finset.range (⌊x⌋₊ + 1) →
      LSeries.term a (t * I) n * triangularMellinWeight ((n : ℝ) / x) = 0 := by
    intro n hn
    have hn' : ⌊x⌋₊ < n := by
      simp only [Finset.mem_range, not_lt] at hn
      omega
    have hxn : x < (n : ℝ) := (Nat.floor_lt hx.le).mp hn'
    have hratio : 1 < (n : ℝ) / x := (one_lt_div hx).mpr hxn
    have hnot : (n : ℝ) / x ∉ Set.Ioc (0 : ℝ) 1 := by
      intro hm
      linarith [hm.2]
    simp only [triangularMellinWeight, Set.indicator_of_notMem hnot, mul_zero]
  rw [tsum_eq_sum hzero]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hn0 : n = 0
  · simp only [hn0, LSeries.term_zero, zero_mul]
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hnx : (n : ℝ) ≤ x :=
    (Nat.cast_le.mpr (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn)).trans
      (Nat.floor_le hx.le)
  have hmem : (n : ℝ) / x ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨div_pos hnR hx, (div_le_one hx).mpr hnx⟩
  simp only [triangularMellinWeight, Set.indicator_of_mem hmem, ofReal_sub, ofReal_one]

noncomputable def smoothedVonMangoldtSum (x t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
    LSeries.term (fun m ↦ (ArithmeticFunction.vonMangoldt m : ℂ)) (t * I) n *
      ((1 - (n : ℝ) / x : ℝ) : ℂ)

/-- A finite prime-power weighted sum equals an integral of the actual zeta
logarithmic derivative. No prime-distribution estimate is assumed. -/
theorem smoothedVonMangoldtSum_eq_integral {x σ : ℝ} (hx : 0 < x) (hσ : 1 < σ) (t : ℝ) :
    smoothedVonMangoldtSum x t = -(1 / (2 * Real.pi) : ℝ) • (∫ y : ℝ,
      (x : ℂ) ^ ((σ : ℂ) + y * I) * perronKernel ((σ : ℂ) + y * I) *
        logDeriv riemannZeta ((σ : ℂ) + (t + y : ℝ) * I)) := by
  have ha := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (σ : ℂ)) (by simpa only [ofReal_re] using hσ)
  have h := smoothedPerron_formula hx (by linarith : 1 / 2 ≤ σ) ha t
  rw [triangularMellin_tsum_eq_finite _ hx t] at h
  have hpoint : ∀ y : ℝ,
      LSeries (fun m ↦ (ArithmeticFunction.vonMangoldt m : ℂ))
        ((σ : ℂ) + (t + y : ℝ) * I) =
      -logDeriv riemannZeta ((σ : ℂ) + (t + y : ℝ) * I) := by
    intro y
    simpa only [logDeriv_apply, neg_div] using
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
        (s := (σ : ℂ) + (t + y : ℝ) * I) (by simpa using hσ)
  simp_rw [hpoint, mul_neg] at h
  rw [integral_neg] at h
  change _ = smoothedVonMangoldtSum x t at h
  simpa only [neg_smul, smul_neg] using h.symm

end Erdos421
