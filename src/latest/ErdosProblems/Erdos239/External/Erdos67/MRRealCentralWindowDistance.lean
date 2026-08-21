import ErdosProblems.Erdos239.External.Erdos67.MRRealTwistDistanceZetaTwoSided
import ErdosProblems.Erdos239.External.Erdos67.MRRealPrefixMovingCutoff
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Real pretentious distance on the central Perron window

This is the shrinking-frequency bridge needed by the fixed-high A.10
contour.  It combines the real opposite-twist inequality away from the zeta
pole with a reverse finite-Euler comparison inside the pole window.
-/

open Filter Set Topology
open scoped BigOperators ComplexConjugate LSeries.notation

namespace Erdos67

noncomputable section

open TruncatedEulerLSeries

/-- Uniform two-sided control of the pole-removed zeta factor near one. -/
theorem exists_near_one_riemannZetaOne_norm_bounds :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s : ℂ, ‖s - 1‖ < delta →
      (1 / 2 : ℝ) ≤ ‖riemannZeta₁ s‖ ∧ ‖riemannZeta₁ s‖ ≤ 2 := by
  have hcont : ContinuousAt riemannZeta₁ (1 : ℂ) :=
    differentiable_riemannZeta₁.continuous.continuousAt
  have htend : Tendsto (fun s : ℂ ↦ ‖riemannZeta₁ s‖)
      (𝓝 (1 : ℂ)) (𝓝 (1 : ℝ)) := by
    have hnorm := hcont.norm
    change Tendsto (fun s : ℂ ↦ ‖riemannZeta₁ s‖)
      (𝓝 (1 : ℂ)) (𝓝 ‖riemannZeta₁ (1 : ℂ)‖) at hnorm
    simpa using hnorm
  have htarget : Set.Ioo (1 / 2 : ℝ) 2 ∈ 𝓝 (1 : ℝ) :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  have hevent := htend.eventually htarget
  rw [Metric.eventually_nhds_iff] at hevent
  obtain ⟨delta, hdelta, hbound⟩ := hevent
  refine ⟨delta, hdelta, ?_⟩
  intro s hs
  have hmem := hbound (y := s) (by simpa [dist_eq_norm] using hs)
  exact ⟨hmem.1.le, hmem.2.le⟩

/-- Zeta is uniformly bounded on a compact vertical annulus separated from
its pole. -/
theorem exists_uniform_norm_riemannZeta_compact_away_zero
    (r V : ℝ) (hr : 0 < r) (hrV : r ≤ V) :
    ∃ C : ℝ, 0 < C ∧
      ∀ sigma t : ℝ, 1 ≤ sigma → sigma ≤ 2 →
        r ≤ |t| → |t| ≤ V →
        ‖riemannZeta ((sigma : ℂ) + Complex.I * (t : ℂ))‖ ≤ C := by
  let T : Set ℝ := Set.Icc (-V) (-r) ∪ Set.Icc r V
  let K : Set (ℝ × ℝ) := Set.Icc (1 : ℝ) 2 ×ˢ T
  let z : ℝ × ℝ → ℂ := fun x ↦
    (x.1 : ℂ) + Complex.I * (x.2 : ℂ)
  let F : ℝ × ℝ → ℝ := fun x ↦ ‖riemannZeta (z x)‖
  have hT : IsCompact T := isCompact_Icc.union isCompact_Icc
  have hK : IsCompact K := isCompact_Icc.prod hT
  have hKne : K.Nonempty := by
    refine ⟨(1, r), ?_⟩
    exact ⟨⟨le_rfl, by norm_num⟩, Or.inr ⟨le_rfl, hrV⟩⟩
  have hz_ne : ∀ x ∈ K, z x ≠ 1 := by
    intro x hx heq
    have him := congrArg Complex.im heq
    simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_re, one_mul,
      zero_add, Complex.one_im] at him
    rcases hx.2 with hxneg | hxpos
    · linarith [hxneg.2, hr]
    · linarith [hxpos.1, hr]
  have hF : ContinuousOn F K := by
    intro x hx
    have hzcont : ContinuousAt z x := by
      dsimp only [z]
      fun_prop
    have hzetacont : ContinuousAt riemannZeta (z x) :=
      (differentiableAt_riemannZeta (hz_ne x hx)).continuousAt
    exact (hzetacont.norm.comp hzcont).continuousWithinAt
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hKne hF
  refine ⟨F x + 1, by dsimp only [F]; positivity, ?_⟩
  intro sigma t hsigma1 hsigma2 htr htV
  have htT : t ∈ T := by
    by_cases ht : 0 ≤ t
    · right
      rw [abs_of_nonneg ht] at htr htV
      exact ⟨htr, htV⟩
    · left
      have ht' : t ≤ 0 := le_of_not_ge ht
      rw [abs_of_nonpos ht'] at htr htV
      constructor <;> linarith
  have hst : (sigma, t) ∈ K := ⟨⟨hsigma1, hsigma2⟩, htT⟩
  exact (hmax hst).trans (le_add_of_nonneg_right zero_le_one)

/-- Upper pole envelope expressed using `riemannZeta₁`. -/
theorem norm_riemannZeta_polynomialHeight_le_two_div_abs
    {Y : ℕ} (hY : 2 ≤ Y) {v delta : ℝ}
    (hnear : ‖polynomialHeightEulerPoint Y v - 1‖ < delta)
    (hdelta : ∀ s : ℂ, ‖s - 1‖ < delta → ‖riemannZeta₁ s‖ ≤ 2)
    (hv : 0 < |v|) :
    ‖riemannZeta (polynomialHeightEulerPoint Y v)‖ ≤ 2 / |v| := by
  let s := polynomialHeightEulerPoint Y v
  have hs : s ≠ 1 := by
    intro hs1
    have hre := congrArg Complex.re hs1
    rw [TruncatedEulerLSeries.polynomialHeightEulerPoint_re] at hre
    have hlog : 0 < Real.log (Y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
    simp only [Complex.one_re] at hre
    linarith [inv_pos.mpr hlog]
  have him : |v| ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    have himEq : (s - 1).im = v := by
      dsimp only [s, polynomialHeightEulerPoint]
      simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.I_re, Complex.ofReal_re, zero_mul,
        Complex.I_im, one_mul, zero_add, Complex.one_im, sub_zero]
    simpa only [himEq] using h
  rw [riemannZeta_eq_inv_sub_mul hs, norm_mul, norm_inv]
  have hz := hdelta s (by simpa only [s] using hnear)
  exact (mul_le_mul (inv_anti₀ hv him) hz (norm_nonneg _) (by positivity)).trans_eq
    (by field_simp)

/-- Lower pole envelope expressed using `riemannZeta₁`. -/
theorem one_div_two_mul_invlog_add_abs_le_norm_riemannZeta_polynomialHeight
    {Y : ℕ} (hY : 2 ≤ Y) {v delta : ℝ}
    (hnear : ‖polynomialHeightEulerPoint Y v - 1‖ < delta)
    (hdelta : ∀ s : ℂ, ‖s - 1‖ < delta →
      (1 / 2 : ℝ) ≤ ‖riemannZeta₁ s‖) :
    (1 / 2 : ℝ) / ((Real.log (Y : ℝ))⁻¹ + |v|) ≤
      ‖riemannZeta (polynomialHeightEulerPoint Y v)‖ := by
  let s := polynomialHeightEulerPoint Y v
  have hlog : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hs : s ≠ 1 := by
    intro hs1
    have hre := congrArg Complex.re hs1
    rw [TruncatedEulerLSeries.polynomialHeightEulerPoint_re] at hre
    simp only [Complex.one_re] at hre
    linarith [inv_pos.mpr hlog]
  have hnormUpper : ‖s - 1‖ ≤ (Real.log (Y : ℝ))⁻¹ + |v| := by
    have heq : s - 1 = (((Real.log (Y : ℝ))⁻¹ : ℝ) : ℂ) +
        Complex.I * (v : ℂ) := by
      apply Complex.ext <;> simp [s, polynomialHeightEulerPoint]
    rw [heq]
    calc
      ‖(((Real.log (Y : ℝ))⁻¹ : ℝ) : ℂ) + Complex.I * (v : ℂ)‖ ≤
          ‖(((Real.log (Y : ℝ))⁻¹ : ℝ) : ℂ)‖ +
            ‖Complex.I * (v : ℂ)‖ := norm_add_le _ _
      _ = (Real.log (Y : ℝ))⁻¹ + |v| := by
        rw [Complex.norm_real, Real.norm_of_nonneg (inv_pos.mpr hlog).le,
          norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hdenPos : 0 < (Real.log (Y : ℝ))⁻¹ + |v| := by positivity
  rw [riemannZeta_eq_inv_sub_mul hs, norm_mul, norm_inv]
  have hz := hdelta s (by simpa only [s] using hnear)
  have hinv := inv_anti₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs)) hnormUpper
  calc
    (1 / 2 : ℝ) / ((Real.log (Y : ℝ))⁻¹ + |v|) =
        ((Real.log (Y : ℝ))⁻¹ + |v|)⁻¹ * (1 / 2 : ℝ) := by ring
    _ ≤ ‖s - 1‖⁻¹ * ‖riemannZeta₁ s‖ :=
      mul_le_mul hinv hz (by positivity) (by positivity)

/-- Elementary radius bound for the shifted Euler point. -/
theorem norm_polynomialHeightEulerPoint_sub_one_le
    {Y : ℕ} (hY : 2 ≤ Y) (v : ℝ) :
    ‖polynomialHeightEulerPoint Y v - 1‖ ≤
      (Real.log (Y : ℝ))⁻¹ + |v| := by
  have hlog : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have heq : polynomialHeightEulerPoint Y v - 1 =
      (((Real.log (Y : ℝ))⁻¹ : ℝ) : ℂ) + Complex.I * (v : ℂ) := by
    apply Complex.ext <;> simp [polynomialHeightEulerPoint]
  rw [heq]
  calc
    ‖(((Real.log (Y : ℝ))⁻¹ : ℝ) : ℂ) + Complex.I * (v : ℂ)‖ ≤
        ‖(((Real.log (Y : ℝ))⁻¹ : ℝ) : ℂ)‖ +
          ‖Complex.I * (v : ℂ)‖ := norm_add_le _ _
    _ = (Real.log (Y : ℝ))⁻¹ + |v| := by
      rw [Complex.norm_real, Real.norm_of_nonneg (inv_pos.mpr hlog).le,
        norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- The shrinking radius used to divide the pole and opposite-twist
regimes.  Its exponent leaves a strict margin on both sides. -/
def realCentralPoleRadius (Y : ℕ) : ℝ :=
  (Real.log (Y : ℝ)) ^ (-(23 / 32 : ℝ))

/-- A retained large zero-frequency distance forces uniform
nonpretentiousness throughout the fixed-high A.10 Perron window.  The proof
is independent of the remote minimizing twist: real symmetry handles the
frequencies outside the shrinking pole radius, while the reverse Euler
comparison and the large zero-distance assumption handle the pole radius. -/
theorem eventually_real_centralWindow_nonpretentious_of_large_zero :
    ∀ᶠ Y : ℕ in atTop, ∀ (f : ℕ → ℂ),
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, ‖f n‖ ≤ 1) →
      (23 / 32 : ℝ) * Real.log (Real.log (Y : ℝ)) <
        pretentiousDistSq f (archimedeanTwist 0) Y →
      ∀ t : ℝ, |t| ≤ (Real.log (Y : ℝ)) ^ (2 : ℕ) →
        (realPrefixMovingThreshold Y : ℝ) ≤
          pretentiousDistSq f (archimedeanTwist t) Y := by
  obtain ⟨delta₀, hdelta₀, hpole₀⟩ :=
    exists_near_one_riemannZetaOne_norm_bounds
  let delta : ℝ := min delta₀ 1
  have hdelta : 0 < delta := lt_min hdelta₀ zero_lt_one
  have hdeltaOne : delta ≤ 1 := min_le_right _ _
  have hpole : ∀ s : ℂ, ‖s - 1‖ < delta →
      (1 / 2 : ℝ) ≤ ‖riemannZeta₁ s‖ ∧ ‖riemannZeta₁ s‖ ≤ 2 := by
    intro s hs
    exact hpole₀ s (hs.trans_le (min_le_left _ _))
  obtain ⟨C, hC, hcompact⟩ :=
    exists_uniform_norm_riemannZeta_compact_away_zero
      (delta / 2) 2 (by positivity) (by linarith)
  let alpha : ℝ := 23 / 32
  let E : ℝ := oppositeTwistEulerLoss
  let K : ℝ := PrimeEstimates.mertensBound +
    TruncatedEulerLSeries.shiftedEulerTailConstant +
    2 * polynomialHeightPrimePowerRemainderBound +
    polynomialHeightWeightRemovalBound
  have hloglog : Tendsto
      (fun Y : ℕ ↦ Real.log (Real.log (Y : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlog : Tendsto (fun Y : ℕ ↦ Real.log (Y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hrho : Tendsto realCentralPoleRadius atTop (𝓝 0) := by
    have hbase := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 23 / 32)
    change Tendsto
      (fun Y : ℕ ↦ (Real.log (Y : ℝ)) ^ (-(23 / 32 : ℝ))) atTop (𝓝 0)
    exact hbase.comp hlog
  have hrhoSmall : ∀ᶠ Y : ℕ in atTop,
      realCentralPoleRadius Y < delta / 2 :=
    ((tendsto_order.1 hrho).2 _ (by positivity)).mono fun _ h ↦ h
  have hEabsorb : ∀ᶠ Y : ℕ in atTop,
      E ≤ (1 / 32 : ℝ) * Real.log (Real.log (Y : ℝ)) := by
    have h := hloglog.eventually (eventually_ge_atTop (32 * E))
    filter_upwards [h] with Y hY
    linarith
  have hcompactAbsorb : ∀ᶠ Y : ℕ in atTop,
      Real.log C + E ≤
        (3 / 4 : ℝ) * Real.log (Real.log (Y : ℝ)) := by
    have h := hloglog.eventually
      (eventually_ge_atTop ((4 / 3 : ℝ) * (Real.log C + E)))
    filter_upwards [h] with Y hY
    linarith
  have hKabsorb : ∀ᶠ Y : ℕ in atTop,
      K - Real.log (1 / 4 : ℝ) ≤
        (1 / 64 : ℝ) * Real.log (Real.log (Y : ℝ)) := by
    have h := hloglog.eventually
      (eventually_ge_atTop (64 * (K - Real.log (1 / 4 : ℝ))))
    filter_upwards [h] with Y hY
    linarith
  filter_upwards [hrhoSmall, hEabsorb, hcompactAbsorb, hKabsorb,
      eventually_quarter_log_log_le_oppositeTwistDistSq_polylog,
      eventually_ge_atTop 4,
      hlog.eventually (eventually_ge_atTop 1)] with
      Y hrhoSmallY hEY hcompactY hKY hpoly hY hlogYOne
  intro f hreal hbound hzero t htWindow
  have hlogY : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hloglogY : 0 ≤ Real.log (Real.log (Y : ℝ)) :=
    Real.log_nonneg hlogYOne
  have hthreshold : (realPrefixMovingThreshold Y : ℝ) ≤
      (1 / 16 : ℝ) * Real.log (Real.log (Y : ℝ)) :=
    realPrefixMovingThreshold_cast_le (by omega)
  apply hthreshold.trans
  by_cases htLarge : 1 < |t|
  · have htPoly : |t| ≤ (Real.log (Y : ℝ)) ^ (4 : ℕ) := by
      have hsqOne : 1 ≤ (Real.log (Y : ℝ)) ^ (2 : ℕ) := by
        exact one_le_pow₀ hlogYOne
      calc
        |t| ≤ (Real.log (Y : ℝ)) ^ (2 : ℕ) := htWindow
        _ ≤ ((Real.log (Y : ℝ)) ^ (2 : ℕ)) ^ (2 : ℕ) := by
          nlinarith [sq_nonneg ((Real.log (Y : ℝ)) ^ (2 : ℕ) - 1)]
        _ = (Real.log (Y : ℝ)) ^ (4 : ℕ) := by ring
    have hopposite := hpoly t htLarge htPoly
    have hrealSep :=
      one_fourth_mul_le_pretentiousDistSq_of_real_of_twist_separation
        hreal (fun n hn ↦ hbound n) hopposite
    linarith
  · have htOne : |t| ≤ 1 := le_of_not_gt htLarge
    let rho : ℝ := realCentralPoleRadius Y
    change rho < delta / 2 at hrhoSmallY
    have hrhoPos : 0 < rho := by
      dsimp only [rho, realCentralPoleRadius]
      exact Real.rpow_pos_of_pos hlogY _
    have halpha : alpha = 23 / 32 := rfl
    have hrhoInv : rho⁻¹ = (Real.log (Y : ℝ)) ^ alpha := by
      dsimp only [rho, realCentralPoleRadius, alpha]
      rw [Real.rpow_neg hlogY.le, inv_inv]
    have hinvLogRho : (Real.log (Y : ℝ))⁻¹ ≤ rho := by
      have hpow : (Real.log (Y : ℝ)) ^ alpha ≤ Real.log (Y : ℝ) := by
        calc
          (Real.log (Y : ℝ)) ^ alpha ≤
              (Real.log (Y : ℝ)) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hlogYOne (by
              dsimp only [alpha]
              norm_num)
          _ = Real.log (Y : ℝ) := Real.rpow_one _
      have hinv := inv_anti₀ (Real.rpow_pos_of_pos hlogY alpha) hpow
      rw [← hrhoInv] at hinv
      simpa only [inv_inv] using hinv
    by_cases htTiny : |t| ≤ rho
    · have hpointNear :
          ‖polynomialHeightEulerPoint Y (-t) - 1‖ < delta := by
        calc
          ‖polynomialHeightEulerPoint Y (-t) - 1‖ ≤
              (Real.log (Y : ℝ))⁻¹ + |-t| :=
            norm_polynomialHeightEulerPoint_sub_one_le (by omega) (-t)
          _ ≤ rho + rho := by
            rw [abs_neg]
            exact add_le_add hinvLogRho htTiny
          _ < delta := by linarith
      have hzetaLower :=
        one_div_two_mul_invlog_add_abs_le_norm_riemannZeta_polynomialHeight
          (by omega : 2 ≤ Y) hpointNear (fun s hs ↦ (hpole s hs).1)
      have hden : (Real.log (Y : ℝ))⁻¹ + |-t| ≤ 2 * rho := by
        rw [abs_neg]
        calc
          (Real.log (Y : ℝ))⁻¹ + |t| ≤ rho + rho :=
            add_le_add hinvLogRho htTiny
          _ = 2 * rho := by ring
      have hquarterPos : 0 < (1 / 4 : ℝ) * rho⁻¹ := by positivity
      have hzetaQuarter : (1 / 4 : ℝ) * rho⁻¹ ≤
          ‖riemannZeta (polynomialHeightEulerPoint Y (-t))‖ := by
        calc
          (1 / 4 : ℝ) * rho⁻¹ = (1 / 2 : ℝ) / (2 * rho) := by
            field_simp
            norm_num
          _ ≤ (1 / 2 : ℝ) /
              ((Real.log (Y : ℝ))⁻¹ + |-t|) := by
            exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
          _ ≤ ‖riemannZeta (polynomialHeightEulerPoint Y (-t))‖ :=
            hzetaLower
      have hlogLower := Real.log_le_log hquarterPos hzetaQuarter
      have hlogQuarter :
          Real.log ((1 / 4 : ℝ) * rho⁻¹) =
            Real.log (1 / 4 : ℝ) +
              alpha * Real.log (Real.log (Y : ℝ)) := by
        rw [hrhoInv, Real.log_mul (by norm_num) (ne_of_gt
          (Real.rpow_pos_of_pos hlogY alpha)), Real.log_rpow hlogY]
      rw [hlogQuarter] at hlogLower
      have htwist := pretentiousDistSq_twist_zero_le_loglog_sub_log_zeta_add
        hY t
      dsimp only [K] at hKY
      have htwistUpper :
          pretentiousDistSq (archimedeanTwist t) (archimedeanTwist 0) Y ≤
            (19 / 64 : ℝ) * Real.log (Real.log (Y : ℝ)) := by
        dsimp only [alpha] at hlogLower
        linarith
      by_contra hdist
      have hdist' : pretentiousDistSq f (archimedeanTwist t) Y <
          (1 / 16 : ℝ) * Real.log (Real.log (Y : ℝ)) :=
        lt_of_not_ge hdist
      have htriangle := pretentiousDistSq_triangle_sq_left_unit
        (x := Y) (f := archimedeanTwist t) (g := f)
        (h := archimedeanTwist 0)
        (fun p hp ↦ norm_archimedeanTwist hp.pos t)
        (fun p hp ↦ hbound p)
        (fun p hp ↦ (norm_archimedeanTwist hp.pos 0).le)
      rw [pretentiousDistSq_symm (archimedeanTwist t) f Y] at htriangle
      linarith
    · have htRho : rho < |t| := lt_of_not_ge htTiny
      let v : ℝ := -2 * t
      have hvabs : |v| = 2 * |t| := by
        dsimp only [v]
        rw [abs_mul]
        norm_num
      have hvPos : 0 < |v| := by rw [hvabs]; linarith
      have hvUpper : |v| ≤ 2 := by rw [hvabs]; linarith
      by_cases hpointNear :
          ‖polynomialHeightEulerPoint Y v - 1‖ < delta
      · have hzetaUpper := norm_riemannZeta_polynomialHeight_le_two_div_abs
          (by omega : 2 ≤ Y) hpointNear (fun s hs ↦ (hpole s hs).2) hvPos
        have hinv : |t|⁻¹ ≤ rho⁻¹ := inv_anti₀ hrhoPos htRho.le
        have hzetaPow :
            ‖riemannZeta (polynomialHeightEulerPoint Y v)‖ ≤
              (Real.log (Y : ℝ)) ^ alpha := by
          calc
            ‖riemannZeta (polynomialHeightEulerPoint Y v)‖ ≤ 2 / |v| :=
              hzetaUpper
            _ = |t|⁻¹ := by
              rw [hvabs]
              field_simp
            _ ≤ rho⁻¹ := hinv
            _ = (Real.log (Y : ℝ)) ^ alpha := hrhoInv
        have hzetaNe : riemannZeta (polynomialHeightEulerPoint Y v) ≠ 0 := by
          rw [← LSeries_dirichletCharacter_one_eq_riemannZeta
            (one_lt_polynomialHeightEulerPoint_re (by omega) v)]
          exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re
            (1 : DirichletCharacter ℂ 1)
              (one_lt_polynomialHeightEulerPoint_re (by omega) v)
        have hlogNorm := Real.log_le_log (norm_pos_iff.mpr hzetaNe) hzetaPow
        rw [Real.log_rpow hlogY] at hlogNorm
        have hsep := one_fourth_log_log_sub_log_norm_riemannZeta_sub_loss_le_realDistSq
          hreal (fun n hn ↦ hbound n) hY t
        dsimp only [v, alpha, E] at hlogNorm hsep hEY
        linarith
      · have hvLower : delta / 2 ≤ |v| := by
          by_contra hv
          have hv' : |v| < delta / 2 := lt_of_not_ge hv
          have hnorm := norm_polynomialHeightEulerPoint_sub_one_le
            (by omega : 2 ≤ Y) v
          have : ‖polynomialHeightEulerPoint Y v - 1‖ < delta := by
            calc
              ‖polynomialHeightEulerPoint Y v - 1‖ ≤
                  (Real.log (Y : ℝ))⁻¹ + |v| := hnorm
              _ < rho + delta / 2 := by linarith
              _ < delta := by linarith
          exact hpointNear this
        have hsigma1 : 1 ≤ 1 + (Real.log (Y : ℝ))⁻¹ :=
          le_add_of_nonneg_right (inv_pos.mpr hlogY).le
        have hsigma2 : 1 + (Real.log (Y : ℝ))⁻¹ ≤ 2 := by
          have := inv_le_one₀ hlogY |>.2 hlogYOne
          linarith
        have hzetaC := hcompact
          (1 + (Real.log (Y : ℝ))⁻¹) v hsigma1 hsigma2 hvLower hvUpper
        have hzetaNe : riemannZeta (polynomialHeightEulerPoint Y v) ≠ 0 := by
          rw [← LSeries_dirichletCharacter_one_eq_riemannZeta
            (one_lt_polynomialHeightEulerPoint_re (by omega) v)]
          exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re
            (1 : DirichletCharacter ℂ 1)
              (one_lt_polynomialHeightEulerPoint_re (by omega) v)
        have hpoint :
            (((1 + (Real.log (Y : ℝ))⁻¹ : ℝ) : ℂ) +
              Complex.I * (v : ℂ)) = polynomialHeightEulerPoint Y v := rfl
        rw [hpoint] at hzetaC
        have hlogNorm := Real.log_le_log (norm_pos_iff.mpr hzetaNe) hzetaC
        have hsep := one_fourth_log_log_sub_log_norm_riemannZeta_sub_loss_le_realDistSq
          hreal (fun n hn ↦ hbound n) hY t
        dsimp only [v, E] at hsep hcompactY
        linarith

/-- The moving real threshold is monotone once both endpoints lie beyond the
double-log domain used in its definition. -/
theorem realPrefixMovingThreshold_mono
    {X Z : ℕ} (hX : 3 ≤ X) (hXZ : X ≤ Z) :
    realPrefixMovingThreshold X ≤ realPrefixMovingThreshold Z := by
  unfold realPrefixMovingThreshold
  apply Nat.floor_mono
  apply max_le_max_left
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.strictMonoOn_log.monotoneOn
  · exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  · exact Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
  · apply Real.strictMonoOn_log.monotoneOn
    · simp only [Set.mem_Ioi]
      exact_mod_cast (show 0 < X by omega)
    · simp only [Set.mem_Ioi]
      exact_mod_cast (show 0 < Z by omega)
    · exact_mod_cast hXZ

/-- Source-scale form for the real-prefix dichotomy.  A large zero distance
at `3X` supplies the local fixed-high A.10 distance hypothesis uniformly at
every prefix cutoff `Z ∈ [X,3X]`. -/
theorem eventually_real_centralWindow_at_prefix_of_large_zero_three_mul :
    ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ),
      (∀ n, 0 < n → conj (f n) = f n) →
      (∀ n, ‖f n‖ ≤ 1) →
      (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) <
        pretentiousDistSq f (archimedeanTwist 0) (3 * X) →
      ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
      ∀ t : ℝ, |t| ≤ (Real.log (Z : ℝ)) ^ (2 : ℕ) →
        (realPrefixMovingThreshold X : ℝ) ≤
          pretentiousDistSq f (archimedeanTwist t) Z := by
  obtain ⟨C, hC, htail⟩ :=
    MRHalaszDistanceTail.exists_uniform_pretentiousDistSq_tail_le
  obtain ⟨Y₀, hcentral⟩ :=
    (eventually_atTop.1 eventually_real_centralWindow_nonpretentious_of_large_zero)
  have hloglog : Tendsto
      (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (max 4 Y₀),
      hloglog.eventually (eventually_gt_atTop 55),
      hlog.eventually (eventually_ge_atTop (2 * (Real.log 3 + C)))] with
      X hXY₀ hloglogX hlogXlarge
  intro f hreal hbound hzero Z hXZ hZX t ht
  have hX : 4 ≤ X := le_max_left 4 Y₀ |>.trans hXY₀
  have hZY₀ : Y₀ ≤ Z := (le_max_right 4 Y₀).trans (hXY₀.trans hXZ)
  have hZ : 4 ≤ Z := hX.trans hXZ
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogZ : 0 < Real.log (Z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
  have hloglogCompare :
      Real.log (Real.log (Z : ℝ)) ≤
        Real.log (Real.log (X : ℝ)) + 1 := by
    have hXcast : (3 : ℝ) ≤ X := by exact_mod_cast (show 3 ≤ X by omega)
    have hZXsq : (Z : ℝ) ≤ (X : ℝ) ^ (2 : ℕ) := by
      have hZXcast : (Z : ℝ) ≤ 3 * X := by exact_mod_cast hZX
      nlinarith
    have hlogZX : Real.log (Z : ℝ) ≤ 2 * Real.log (X : ℝ) := by
      calc
        Real.log (Z : ℝ) ≤ Real.log ((X : ℝ) ^ (2 : ℕ)) :=
          Real.strictMonoOn_log.monotoneOn
            (by simp only [Set.mem_Ioi]; exact_mod_cast (show 0 < Z by omega))
            (by simp only [Set.mem_Ioi]; positivity) hZXsq
        _ = 2 * Real.log (X : ℝ) := by rw [Real.log_pow]; norm_num
    calc
      Real.log (Real.log (Z : ℝ)) ≤
          Real.log (2 * Real.log (X : ℝ)) :=
        Real.strictMonoOn_log.monotoneOn hlogZ (mul_pos (by norm_num) hlogX) hlogZX
      _ = Real.log 2 + Real.log (Real.log (X : ℝ)) := by
        rw [Real.log_mul (by norm_num) hlogX.ne']
      _ ≤ Real.log (Real.log (X : ℝ)) + 1 := by
        linarith [Real.log_two_lt_d9]
  have htailOne :
      pretentiousDistSq f (archimedeanTwist 0) (3 * X) -
          pretentiousDistSq f (archimedeanTwist 0) Z ≤ 1 := by
    by_cases hEq : Z = 3 * X
    · subst Z
      simp
    · have hstrict : Z < 3 * X := lt_of_le_of_ne hZX hEq
      have hraw := htail (f := f) (g := archimedeanTwist 0)
        (x := Z) (y := 3 * X) (by omega : 2 ≤ Z) hstrict
        (fun p _hp ↦ hbound p)
        (fun p hp ↦ (norm_archimedeanTwist hp.pos 0).le)
      have hratioPos : 0 < ((3 * X : ℕ) : ℝ) / ((Z : ℝ) + 1) := by
        positivity
      have hratio : ((3 * X : ℕ) : ℝ) / ((Z : ℝ) + 1) ≤ 3 := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < (Z : ℝ) + 1)).2
        have hcast : (X : ℝ) ≤ Z := by exact_mod_cast hXZ
        push_cast
        linarith
      have hlogRatio :
          Real.log (((3 * X : ℕ) : ℝ) / ((Z : ℝ) + 1)) ≤ Real.log 3 :=
        Real.strictMonoOn_log.monotoneOn hratioPos (by norm_num) hratio
      have hlogMono : Real.log (X : ℝ) ≤ Real.log ((Z : ℝ) + 1) := by
        apply Real.strictMonoOn_log.monotoneOn
          (by simp only [Set.mem_Ioi]; positivity)
          (by simp only [Set.mem_Ioi]; positivity)
        exact_mod_cast (show X ≤ Z + 1 by omega)
      have hdenPos : 0 < Real.log ((Z : ℝ) + 1) :=
        Real.log_pos (by exact_mod_cast (show 1 < Z + 1 by omega))
      have hone :
          2 * (Real.log (((3 * X : ℕ) : ℝ) / ((Z : ℝ) + 1)) + C) /
              Real.log ((Z : ℝ) + 1) ≤ 1 := by
        apply (div_le_iff₀ hdenPos).2
        calc
          2 * (Real.log (((3 * X : ℕ) : ℝ) / ((Z : ℝ) + 1)) + C) ≤
              2 * (Real.log 3 + C) := by linarith
          _ ≤ Real.log (X : ℝ) := hlogXlarge
          _ ≤ Real.log ((Z : ℝ) + 1) := hlogMono
          _ = 1 * Real.log ((Z : ℝ) + 1) := by ring
      exact hraw.trans hone
  have hlocalZero :
      (23 / 32 : ℝ) * Real.log (Real.log (Z : ℝ)) <
        pretentiousDistSq f (archimedeanTwist 0) Z := by
    linarith
  have hdist := hcentral Z hZY₀ f hreal hbound hlocalZero t ht
  have hmonoCast : (realPrefixMovingThreshold X : ℝ) ≤
      (realPrefixMovingThreshold Z : ℝ) := by
    exact_mod_cast realPrefixMovingThreshold_mono (by omega : 3 ≤ X) hXZ
  exact hmonoCast.trans hdist

end

end Erdos67

#print axioms Erdos67.exists_near_one_riemannZetaOne_norm_bounds
#print axioms Erdos67.norm_riemannZeta_polynomialHeight_le_two_div_abs
#print axioms Erdos67.one_div_two_mul_invlog_add_abs_le_norm_riemannZeta_polynomialHeight
#print axioms Erdos67.eventually_real_centralWindow_nonpretentious_of_large_zero
#print axioms Erdos67.eventually_real_centralWindow_at_prefix_of_large_zero_three_mul
