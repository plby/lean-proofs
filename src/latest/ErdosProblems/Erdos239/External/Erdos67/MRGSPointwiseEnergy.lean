import ErdosProblems.Erdos239.External.Erdos67.MRHalaszNearMediumEnergy

/-!
# Square-energy consequence of the Granville--Soundararajan pointwise bound

This file packages the elementary integration step needed after the source
estimate of the shape

`‖F(t)‖ ≤ K exp (-M / 2) / (1 + |t - c|) + D`.

The analytic production of that pointwise estimate is deliberately kept
separate.  In particular, the exponential saving is not attributed to any
individual Euler factor.
-/

open MeasureTheory

namespace Erdos67

noncomputable section

/-- A source-form GS pointwise estimate has square energy bounded by the
Archimedean error plus the square of its uniform remainder. -/
theorem symmetric_intervalIntegral_normSq_le_gsPointwise_add
    {F : ℝ → ℂ} (hF : Continuous F) {c T M A K D : ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hAM : A ≤ M)
    (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hpoint : ∀ t ∈ Set.Icc (-T) T,
      ‖F t‖ ≤ K * Real.exp (-(1 / 2 : ℝ) * M) *
          (1 + |t - c|)⁻¹ + D) :
    (∫ t in -T..T, Complex.normSq (F t)) ≤
      64 * K ^ 2 * (A + 1) * Real.exp (-(1 / 2 : ℝ) * A) +
        4 * T * D ^ 2 := by
  let K₀ : ℝ := K * Real.exp (-(1 / 2 : ℝ) * M)
  have hM : 0 ≤ M := hA.trans hAM
  have hK₀ : 0 ≤ K₀ := by
    dsimp only [K₀]
    positivity
  have hcentral : ∀ t ∈ Set.Icc (-T) T,
      |t - c| ≤ halaszCentralRadius 0 →
        ‖F t‖ ≤ K₀ * (0 + 1) * Real.exp (-0) + D := by
    intro t ht _htc
    have hden : 1 ≤ 1 + |t - c| := by
      linarith [abs_nonneg (t - c)]
    have hinv : (1 + |t - c|)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ hden
    calc
      ‖F t‖ ≤ K * Real.exp (-(1 / 2 : ℝ) * M) *
          (1 + |t - c|)⁻¹ + D := hpoint t ht
      _ ≤ K₀ * 1 + D := by
        dsimp only [K₀]
        gcongr
      _ = K₀ * (0 + 1) * Real.exp (-0) + D := by norm_num
  have hside : ∀ t ∈ Set.Icc (-T) T,
      halaszCentralRadius 0 ≤ |t - c| →
        ‖F t‖ ≤ K₀ * |t - c|⁻¹ + D := by
    intro t ht htc
    have htc' : 1 ≤ |t - c| := by
      simpa [halaszCentralRadius] using htc
    have htpos : 0 < |t - c| := lt_of_lt_of_le zero_lt_one htc'
    have hden : |t - c| ≤ 1 + |t - c| := by linarith
    have hinv : (1 + |t - c|)⁻¹ ≤ |t - c|⁻¹ :=
      inv_anti₀ htpos hden
    calc
      ‖F t‖ ≤ K * Real.exp (-(1 / 2 : ℝ) * M) *
          (1 + |t - c|)⁻¹ + D := hpoint t ht
      _ ≤ K₀ * |t - c|⁻¹ + D := by
        dsimp only [K₀]
        gcongr
  have hbase := symmetric_intervalIntegral_normSq_le_archimedeanError_add_of_local
    (F := F) hF (c := c) (T := T) (M := 0) (A := 0) (K := K₀) (D := D)
    hT (by norm_num) (by norm_num) hK₀ hD hcentral hside
  have hexpSq : (Real.exp (-(1 / 2 : ℝ) * M)) ^ 2 = Real.exp (-M) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsmall : Real.exp (-M) ≤ (M + 1) * Real.exp (-M) := by
    have he : 0 < Real.exp (-M) := Real.exp_pos _
    nlinarith
  have hdecay : Real.exp (-M) ≤
      2 * (A + 1) * Real.exp (-(1 / 2 : ℝ) * A) :=
    hsmall.trans (halaszError_le_two_mul_archimedeanError hA hAM)
  have hscale : 0 ≤ 32 * K ^ 2 := by positivity
  calc
    (∫ t in -T..T, Complex.normSq (F t)) ≤
        32 * K₀ ^ 2 * (0 + 1) * Real.exp (-(1 / 2 : ℝ) * 0) +
          4 * T * D ^ 2 := hbase
    _ = 32 * K ^ 2 * Real.exp (-M) + 4 * T * D ^ 2 := by
      dsimp only [K₀]
      rw [mul_pow, hexpSq]
      norm_num
      ring
    _ ≤ 32 * K ^ 2 *
          (2 * (A + 1) * Real.exp (-(1 / 2 : ℝ) * A)) +
          4 * T * D ^ 2 := by
      gcongr
    _ = 64 * K ^ 2 * (A + 1) *
          Real.exp (-(1 / 2 : ℝ) * A) + 4 * T * D ^ 2 := by ring

end

end Erdos67
