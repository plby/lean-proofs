import ErdosProblems.Erdos239.External.Erdos67.MRLemma14

/-!
# The moving-window identity in the Matomäki--Radziwiłł Lemma 14

The high-frequency part of the source proof does not estimate the two
Perron endpoints separately.  It first averages a common moving endpoint
over `w ∈ [h,3h]`.  Subtracting the two averages cancels that moving endpoint
exactly and recovers the original endpoint difference.  This file isolates
that algebraic identity in a form that can be reused before the subsequent
change of variables and logarithmic Plancherel estimate.
-/

open scoped Interval

namespace Erdos67.MRLemma14Smoothing

noncomputable section

/-- Integrable form of the moving-endpoint identity.  Only integrability on
the averaging interval is needed; this is convenient for complex powers,
whose base is only known to be positive on the interval in applications. -/
theorem movingEndpoint_average_sub_average_of_intervalIntegrable
    (G : ℝ → ℂ)
    {h : ℝ} (hh : 0 < h)
    (hG : IntervalIntegrable G MeasureTheory.volume h (3 * h))
    (z₀ z₁ : ℂ) :
    (((2 * h : ℝ) : ℂ))⁻¹ *
        ((∫ w in h..3 * h, (G w - z₀)) -
          ∫ w in h..3 * h, (G w - z₁)) =
      z₁ - z₀ := by
  have h0 : (((2 * h : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hh.ne')
  have hsub₀ : IntervalIntegrable (fun w ↦ G w - z₀) MeasureTheory.volume h (3 * h) :=
    hG.sub intervalIntegrable_const
  have hsub₁ : IntervalIntegrable (fun w ↦ G w - z₁) MeasureTheory.volume h (3 * h) :=
    hG.sub intervalIntegrable_const
  rw [← intervalIntegral.integral_sub hsub₀ hsub₁]
  have hintegrand :
      (fun w ↦ (G w - z₀) - (G w - z₁)) = fun _w ↦ z₁ - z₀ := by
    funext w
    ring
  rw [hintegrand, intervalIntegral.integral_const]
  simp only [Complex.real_smul]
  have hlength : 3 * h - h = 2 * h := by ring
  rw [hlength]
  rw [← mul_assoc, inv_mul_cancel₀ h0, one_mul]

/-- Averaging two differences with a common moving endpoint over `[h,3h]`
recovers the fixed endpoint difference.  This is the exact smoothing
identity used in the high-frequency part of MR Lemma 14. -/
theorem movingEndpoint_average_sub_average
    (G : ℝ → ℂ) (hG : Continuous G) (z₀ z₁ : ℂ)
    {h : ℝ} (hh : 0 < h) :
    (((2 * h : ℝ) : ℂ))⁻¹ *
        ((∫ w in h..3 * h, (G w - z₀)) -
          ∫ w in h..3 * h, (G w - z₁)) =
      z₁ - z₀ := by
  exact movingEndpoint_average_sub_average_of_intervalIntegrable
    G hh (hG.intervalIntegrable _ _) z₀ z₁

/-- Equivalent source spelling with the two averaged integrals divided by
the window length. -/
theorem sub_average_movingEndpoint_eq
    (G : ℝ → ℂ) (hG : Continuous G) (z₀ z₁ : ℂ)
    {h : ℝ} (hh : 0 < h) :
    z₁ - z₀ =
      (((2 * h : ℝ) : ℂ))⁻¹ *
        ((∫ w in h..3 * h, (G w - z₀)) -
          ∫ w in h..3 * h, (G w - z₁)) := by
  symm
  exact movingEndpoint_average_sub_average G hG z₀ z₁ hh

end

end Erdos67.MRLemma14Smoothing
