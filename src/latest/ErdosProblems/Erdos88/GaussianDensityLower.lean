import ErdosProblems.Erdos88.GaussianRobustRank

/-!
# Lower bounds from Gaussian density comparison

This file records the deterministic final step in the many-small-coordinates
case of KSSS Theorem 5.2.  A uniform comparison with the standard normal
density gives, on every fixed compact interval, a positive density lower
bound, a density-ratio bound, and a small-ball lower bound.  These are the
exact inputs used by the reverse relative Esseen inequality.
-/

open MeasureTheory ProbabilityTheory Set

namespace Erdos88.GaussianQuadratic

lemma standardNormalDensity_pos (u : ℝ) :
    0 < standardNormalDensity u := by
  unfold standardNormalDensity
  positivity

lemma standardNormalDensity_nonneg (u : ℝ) :
    0 ≤ standardNormalDensity u :=
  (standardNormalDensity_pos u).le

lemma standardNormalDensity_le_one (u : ℝ) :
    standardNormalDensity u ≤ 1 := by
  unfold standardNormalDensity
  have hexp : Real.exp (-u ^ 2 / 2) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg u])
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.one_le_sqrt]
    nlinarith [Real.two_le_pi]
  exact (div_le_one (by positivity : 0 < Real.sqrt (2 * Real.pi))).2
    (hexp.trans hsqrt)

/-- On `[-M,M]`, the standard normal density is bounded below by its value
at the right endpoint. -/
lemma standardNormalDensity_le_of_abs_le
    {M u : ℝ} (hM : 0 ≤ M) (hu : |u| ≤ M) :
    standardNormalDensity M ≤ standardNormalDensity u := by
  unfold standardNormalDensity
  have huSq : u ^ 2 ≤ M ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg u) hM).2 hu
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact Real.exp_le_exp.mpr (by linarith)

private lemma abs_le_of_mem_centered_Icc
    {x r M y : ℝ} (hr : 0 ≤ r) (hM : |x| + r ≤ M)
    (hy : y ∈ Set.Icc (x - r) (x + r)) :
    |y| ≤ M := by
  rw [abs_le]
  constructor
  · have hx : -|x| ≤ x := neg_abs_le x
    linarith [hy.1]
  · have hx : x ≤ |x| := le_abs_self x
    linarith [hy.2]

/-- A uniform density comparison with the standard normal gives a positive
lower bound throughout a prescribed compact interval. -/
lemma density_lower_of_uniform_standardNormal_close
    {p : ℝ → ℝ} {delta M u : ℝ}
    (hM : 0 ≤ M)
    (hclose : ∀ v : ℝ, |p v - standardNormalDensity v| ≤ delta)
    (hu : |u| ≤ M) :
    standardNormalDensity M - delta ≤ p u := by
  have hnormal := standardNormalDensity_le_of_abs_le hM hu
  have herror := (abs_le.mp (hclose u)).1
  linarith

/-- The corresponding global upper bound. -/
lemma density_upper_of_uniform_standardNormal_close
    {p : ℝ → ℝ} {delta u : ℝ}
    (hclose : ∀ v : ℝ, |p v - standardNormalDensity v| ≤ delta) :
    p u ≤ 1 + delta := by
  have herror := (abs_le.mp (hclose u)).2
  linarith [standardNormalDensity_le_one u]

/-- If the density error is at most half the compact normal-density lower
bound, then the comparison density has ratio at most `4 / φ(M)` on every
window contained in `[-M,M]`. -/
theorem densityRatioOn_of_uniform_standardNormal_close
    {p : ℝ → ℝ} {delta M x eps R : ℝ}
    (hdelta : 0 ≤ delta) (hdeltaOne : delta ≤ 1)
    (hM : 0 ≤ M)
    (hsmall : 2 * delta ≤ standardNormalDensity M)
    (heps : 0 ≤ eps) (hR : 0 ≤ R)
    (hwindow : |x| + R * eps ≤ M)
    (hclose : ∀ v : ℝ, |p v - standardNormalDensity v| ≤ delta) :
    Erdos88.Esseen.DensityRatioOn p x eps R
      (4 / standardNormalDensity M) := by
  intro y z
  have hradius : 0 ≤ R * eps := mul_nonneg hR heps
  have hyAbs : |y.1| ≤ M :=
    abs_le_of_mem_centered_Icc hradius hwindow y.2
  have hzAbs : |z.1| ≤ M :=
    abs_le_of_mem_centered_Icc hradius hwindow z.2
  have hyUpper : p y.1 ≤ 2 := by
    exact (density_upper_of_uniform_standardNormal_close hclose).trans
      (by linarith)
  have hzLower : standardNormalDensity M / 2 ≤ p z.1 := by
    have hz := density_lower_of_uniform_standardNormal_close hM hclose hzAbs
    linarith
  have hmPos : 0 < standardNormalDensity M := standardNormalDensity_pos M
  calc
    p y.1 ≤ 2 := hyUpper
    _ = (4 / standardNormalDensity M) *
        (standardNormalDensity M / 2) := by
      field_simp [hmPos.ne']
      ring
    _ ≤ (4 / standardNormalDensity M) * p z.1 := by
      exact mul_le_mul_of_nonneg_left hzLower (by positivity)

lemma one_le_four_div_standardNormalDensity (M : ℝ) :
    1 ≤ 4 / standardNormalDensity M := by
  have hmPos := standardNormalDensity_pos M
  apply (le_div_iff₀ hmPos).2
  linarith [standardNormalDensity_le_one M]

/-- Integrating the compact density lower bound gives the exact normalized
small-ball lower bound used in the lower half of Claim 12.1. -/
theorem smallBall_ge_of_uniform_standardNormal_close
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {p : ℝ → ℝ} (hdens : Erdos88.Esseen.HasContinuousDensity mu p)
    {delta M eps x : ℝ}
    (hM : 0 ≤ M) (heps : 0 < eps)
    (hwindow : |x| + eps ≤ M)
    (hclose : ∀ v : ℝ, |p v - standardNormalDensity v| ≤ delta) :
    2 * eps * (standardNormalDensity M - delta) ≤
      Erdos88.Esseen.smallBall mu eps x := by
  have hlower : ∀ y ∈ Set.Icc (x - eps) (x + eps),
      standardNormalDensity M - delta ≤ p y := by
    intro y hy
    apply density_lower_of_uniform_standardNormal_close hM hclose
    exact abs_le_of_mem_centered_Icc heps.le hwindow hy
  rw [hdens.smallBall_eq_integral eps x heps.le]
  calc
    2 * eps * (standardNormalDensity M - delta) =
        ∫ _y in (x - eps)..(x + eps),
          (standardNormalDensity M - delta) := by
      rw [intervalIntegral.integral_const]
      ring
    _ ≤ ∫ y in (x - eps)..(x + eps), p y := by
      apply intervalIntegral.integral_mono_on (by linarith)
        (intervalIntegrable_const) (hdens.intervalIntegrable _ _)
      exact hlower

/-- The same comparison gives a uniform concentration upper bound. -/
theorem concentration_le_of_uniform_standardNormal_close
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    {p : ℝ → ℝ} (hdens : Erdos88.Esseen.HasContinuousDensity mu p)
    {delta eps : ℝ} (hdelta : 0 ≤ delta) (heps : 0 < eps)
    (hclose : ∀ v : ℝ, |p v - standardNormalDensity v| ≤ delta) :
    Erdos88.Esseen.concentration mu eps ≤ 2 * eps * (1 + delta) := by
  apply csSup_le (Set.range_nonempty _)
  intro mass hmass
  rcases hmass with ⟨x, rfl⟩
  change Erdos88.Esseen.smallBall mu eps x ≤ _
  rw [hdens.smallBall_eq_integral eps x heps.le]
  calc
    (∫ y in (x - eps)..(x + eps), p y) ≤
        ∫ _y in (x - eps)..(x + eps), (1 + delta) := by
      apply intervalIntegral.integral_mono_on (by linarith)
        (hdens.intervalIntegrable _ _) intervalIntegrable_const
      intro y _hy
      exact density_upper_of_uniform_standardNormal_close hclose
    _ = 2 * eps * (1 + delta) := by
      rw [intervalIntegral.integral_const]
      ring

/-- Complete reverse-Esseen transfer in the many-small-coordinates case.
The reference law only needs a continuous density uniformly close to the
standard normal.  All density positivity, ratio, small-ball, and
concentration inputs are discharged here. -/
theorem smallBall_ge_of_uniform_standardNormal_close_and_fourierError
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {p : ℝ → ℝ} (hdens : Erdos88.Esseen.HasContinuousDensity nu p)
    {delta M eps x R E : ℝ}
    (hdelta : 0 ≤ delta) (hdeltaOne : delta ≤ 1)
    (hM : 0 ≤ M) (heps : 0 < eps) (hR : 4 ≤ R)
    (hwindow : |x| + R * eps ≤ M)
    (hsmall : 2 * delta ≤ standardNormalDensity M)
    (hclose : ∀ v : ℝ, |p v - standardNormalDensity v| ≤ delta)
    (hfourier : Erdos88.Esseen.fourierError mu nu eps ≤ E) :
    (1 / 8 : ℝ) * (2 * eps * (standardNormalDensity M - delta)) -
        Erdos88.Esseen.relativeEsseenConstant *
          ((2 * eps * (1 + delta)) / R + eps * E) ≤
      Erdos88.Esseen.smallBall mu
        ((10000 * (4 / standardNormalDensity M)) * eps) x := by
  let K : ℝ := 4 / standardNormalDensity M
  have hK : 1 ≤ K := by
    simpa only [K] using one_le_four_div_standardNormalDensity M
  have hratio : Erdos88.Esseen.DensityRatioOn p x eps R K := by
    apply densityRatioOn_of_uniform_standardNormal_close
      hdelta hdeltaOne hM hsmall heps.le
        (le_trans (by norm_num) hR) hwindow hclose
  have hlower := smallBall_ge_of_uniform_standardNormal_close
    nu hdens hM heps
      (show |x| + eps ≤ M by
        have hReps : eps ≤ R * eps := by
          nlinarith [mul_nonneg (le_trans (by norm_num) hR) heps.le]
        linarith)
      hclose
  have hconc := concentration_le_of_uniform_standardNormal_close
    nu hdens hdelta heps hclose
  have hrelative := Erdos88.Esseen.relative_esseen_6_3
    mu nu hdens heps hK hR hratio
  have hnoise :
      Erdos88.Esseen.concentration nu eps / R +
          eps * Erdos88.Esseen.fourierError mu nu eps ≤
        (2 * eps * (1 + delta)) / R + eps * E := by
    exact add_le_add
      ((div_le_div_iff_of_pos_right (by linarith : 0 < R)).2 hconc)
      (mul_le_mul_of_nonneg_left hfourier heps.le)
  have hCnoise := mul_le_mul_of_nonneg_left hnoise
    Erdos88.Esseen.relativeEsseenConstant_nonneg
  change _ ≤ Erdos88.Esseen.smallBall mu ((10000 * K) * eps) x
  linarith

end Erdos88.GaussianQuadratic
