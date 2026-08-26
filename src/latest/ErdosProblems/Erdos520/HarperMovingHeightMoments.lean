import ErdosProblems.Erdos520.HarperCentralBandMoments

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Set Function Filter Finset MeasureTheory Topology
open scoped BigOperators

noncomputable section

namespace Erdos
namespace Problem520

/-!
# Scheduled moments on growing noncentral windows

The strong-PNT oscillation error contains a factor proportional to the
height cutoff `M`.  Since scheduled endpoints are squared from one block to
the next, shifting the first block by `clog 2 (M+1)` absorbs this factor.
All thresholds below are consequently an absolute constant plus this
explicit logarithmic shift; none depends on a fixed vertical window.
-/

/-- The factor `M` in the PNT error is cancelled by one logarithmic shift
against the square of the scheduled geometric scale. -/
theorem harperScheduledMovingHeight_geometric_cancellation
    (M J j : ℕ) (hshift : J + Nat.clog 2 (M + 1) ≤ j) :
    (3 + 2 * (M : ℝ)) * (1 / 2 : ℝ) ^ (2 * j) ≤
      5 * (1 / 2 : ℝ) ^ (2 * J) := by
  let s : ℕ := Nat.clog 2 (M + 1)
  have hMnat : M + 1 ≤ 2 ^ s := by
    simpa only [s] using! Nat.le_pow_clog (by norm_num) (M + 1)
  have hM : (M : ℝ) + 1 ≤ (2 : ℝ) ^ s := by
    exact_mod_cast hMnat
  have honePow : (1 : ℝ) ≤ (2 : ℝ) ^ s := one_le_pow₀ (by norm_num)
  have hcoeff : 3 + 2 * (M : ℝ) ≤ 5 * (2 : ℝ) ^ s := by
    nlinarith
  have hsj : J + s ≤ j := by simpa only [s] using! hshift
  have hpow : (1 / 2 : ℝ) ^ (2 * j) ≤
      (1 / 2 : ℝ) ^ (2 * (J + s)) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hcancel :
      (2 : ℝ) ^ s * (1 / 2 : ℝ) ^ (2 * (J + s)) =
        (1 / 2 : ℝ) ^ (2 * J) * (1 / 2 : ℝ) ^ s := by
    rw [show 2 * (J + s) = 2 * J + 2 * s by omega, pow_add]
    rw [show 2 * s = s + s by omega, pow_add]
    calc
      (2 : ℝ) ^ s *
          ((1 / 2 : ℝ) ^ (2 * J) *
            ((1 / 2 : ℝ) ^ s * (1 / 2 : ℝ) ^ s)) =
          (1 / 2 : ℝ) ^ (2 * J) *
            (((2 : ℝ) ^ s * (1 / 2 : ℝ) ^ s) *
              (1 / 2 : ℝ) ^ s) := by ring
      _ = (1 / 2 : ℝ) ^ (2 * J) *
            (((2 : ℝ) * (1 / 2 : ℝ)) ^ s *
              (1 / 2 : ℝ) ^ s) := by rw [mul_pow]
      _ = (1 / 2 : ℝ) ^ (2 * J) * (1 / 2 : ℝ) ^ s := by
        norm_num
  have hcancelLe :
      (2 : ℝ) ^ s * (1 / 2 : ℝ) ^ (2 * (J + s)) ≤
        (1 / 2 : ℝ) ^ (2 * J) := by
    rw [hcancel]
    exact mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num))
  calc
    (3 + 2 * (M : ℝ)) * (1 / 2 : ℝ) ^ (2 * j) ≤
        (5 * (2 : ℝ) ^ s) * (1 / 2 : ℝ) ^ (2 * j) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ ≤ (5 * (2 : ℝ) ^ s) *
        (1 / 2 : ℝ) ^ (2 * (J + s)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 5 * ((2 : ℝ) ^ s *
        (1 / 2 : ℝ) ^ (2 * (J + s))) := by ring
    _ ≤ 5 * (1 / 2 : ℝ) ^ (2 * J) :=
      mul_le_mul_of_nonneg_left hcancelLe (by norm_num)

/-- A single choice of the strong-PNT constants controls every natural
height window.  Only the explicit envelope still records `M`. -/
theorem exists_harperScheduledMovingHeightOscillationBounds :
    ∃ c > 0, ∃ C > 0, ∃ J : ℕ,
      ∀ M j y : ℕ, J ≤ j →
        harperBlockEndpoint (j + 1) ≤ y →
          ∀ tau : ℝ, 2 ≤ |tau| → |tau| ≤ 2 * M →
            |harperScheduledOscillationMass y j tau| ≤
              harperScheduledOscillationEnvelope M c C j := by
  obtain ⟨c, hc, C, hC, J, hraw⟩ :=
    exists_mediumPNT_harperScheduledPrimeOscillation_bound
  refine ⟨c, hc, C, hC, J, ?_⟩
  intro M j y hj hy tau htauLower htauUpper
  have htau : tau ≠ 0 := by
    have : 0 < |tau| := lt_of_lt_of_le (by norm_num) htauLower
    exact abs_pos.mp this
  have hbase := hraw j hj y hy tau htau
  let delta : ℝ := harperScheduledThetaEnvelope c C j
  let ell : ℝ := invLog (harperBlockEndpoint j)
  have hdelta : 0 ≤ delta := by
    dsimp [delta]
    exact harperScheduledThetaEnvelope_nonneg hC.le j
  have hell0 : 0 ≤ ell := by
    dsimp [ell]
    exact (invLog_harperBlockEndpoint_pos j).le
  have hell1 : ell ≤ 1 := by
    dsimp [ell]
    exact invLog_harperBlockEndpoint_le_one j
  have hratio :
      ((harperBlockEndpoint (j + 1) : ℝ) /
          harperBlockEndpoint j) = (harperBlockEndpoint j : ℝ) := by
    rw [harperBlockEndpoint_succ]
    push_cast
    have hAne : (harperBlockEndpoint j : ℝ) ≠ 0 := by
      exact_mod_cast (harperBlockEndpoint_pos j).ne'
    field_simp
  have hlogCancel :
      Real.log ((harperBlockEndpoint (j + 1) : ℝ) /
          harperBlockEndpoint j) * ell = 1 := by
    rw [hratio]
    dsimp [ell, invLog]
    exact mul_inv_cancel₀
      (Real.log_pos (by
        exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 16)
          (harperBlockEndpoint_ge_sixteen j))).ne'
  have htauDiv : 2 / |tau| ≤ 1 := by
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) htauLower)).2
    linarith
  change |harperScheduledOscillationMass y j tau| ≤ _
  calc
    |harperScheduledOscillationMass y j tau| ≤
        (2 / |tau| + 2 * delta +
          delta * (1 + |tau|) *
            Real.log ((harperBlockEndpoint (j + 1) : ℝ) /
              harperBlockEndpoint j)) * ell := by
      simpa only [harperScheduledOscillationMass, delta, ell,
        harperScheduledThetaEnvelope] using! hbase
    _ = (2 / |tau|) * ell + 2 * delta * ell +
        delta * (1 + |tau|) *
          (Real.log ((harperBlockEndpoint (j + 1) : ℝ) /
            harperBlockEndpoint j) * ell) := by ring
    _ = (2 / |tau|) * ell + 2 * delta * ell +
        delta * (1 + |tau|) := by rw [hlogCancel, mul_one]
    _ ≤ ell + 2 * delta + delta * (1 + 2 * (M : ℝ)) := by
      have hfirst : (2 / |tau|) * ell ≤ ell := by
        simpa only [one_mul] using!
          mul_le_mul_of_nonneg_right htauDiv hell0
      have hsecond : 2 * delta * ell ≤ 2 * delta := by nlinarith
      have hthird : delta * (1 + |tau|) ≤
          delta * (1 + 2 * (M : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hdelta
      linarith
    _ = harperScheduledOscillationEnvelope M c C j := by
      dsimp [ell, delta, harperScheduledOscillationEnvelope]
      ring

/-- The PNT envelope is uniformly bounded after the logarithmic height
shift. -/
theorem harperScheduledOscillationEnvelope_le_clog_shift
    {c C : ℝ} (hC : 0 ≤ C) {M J j : ℕ}
    (hshift : J + Nat.clog 2 (M + 1) ≤ j)
    (htheta : harperScheduledThetaEnvelope c C j ≤
      (C + 1) * invLog (harperBlockEndpoint j) ^ 2) :
    harperScheduledOscillationEnvelope M c C j ≤
      (1 / 2 : ℝ) ^ J +
        5 * (C + 1) * (1 / 2 : ℝ) ^ (2 * J) := by
  have hJj : J ≤ j := by omega
  have hell := invLog_harperBlockEndpoint_le_geometric j
  have hpowJ : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ J :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hJj
  have hellJ : invLog (harperBlockEndpoint j) ≤
      (1 / 2 : ℝ) ^ J := hell.trans hpowJ
  have hell0 := (invLog_harperBlockEndpoint_pos j).le
  have hellSq : invLog (harperBlockEndpoint j) ^ 2 ≤
      (1 / 2 : ℝ) ^ (2 * j) := by
    calc
      invLog (harperBlockEndpoint j) ^ 2 ≤
          ((1 / 2 : ℝ) ^ j) ^ 2 := by gcongr
      _ = (1 / 2 : ℝ) ^ (2 * j) := by
        rw [← pow_mul]
        congr 1
        omega
  have htheta' : harperScheduledThetaEnvelope c C j ≤
      (C + 1) * (1 / 2 : ℝ) ^ (2 * j) :=
    htheta.trans (mul_le_mul_of_nonneg_left hellSq (by linarith))
  have hcancel :=
    harperScheduledMovingHeight_geometric_cancellation M J j hshift
  calc
    harperScheduledOscillationEnvelope M c C j =
        invLog (harperBlockEndpoint j) +
          (3 + 2 * (M : ℝ)) *
            harperScheduledThetaEnvelope c C j := rfl
    _ ≤ (1 / 2 : ℝ) ^ J +
        (3 + 2 * (M : ℝ)) *
          ((C + 1) * (1 / 2 : ℝ) ^ (2 * j)) := by gcongr
    _ = (1 / 2 : ℝ) ^ J +
        (C + 1) *
          ((3 + 2 * (M : ℝ)) * (1 / 2 : ℝ) ^ (2 * j)) := by ring
    _ ≤ (1 / 2 : ℝ) ^ J +
        (C + 1) * (5 * (1 / 2 : ℝ) ^ (2 * J)) := by
      gcongr
    _ = (1 / 2 : ℝ) ^ J +
        5 * (C + 1) * (1 / 2 : ℝ) ^ (2 * J) := by ring

/-- Uniform `10^-3` second-harmonic cancellation for every growing natural
height window after an absolute plus logarithmic block shift. -/
theorem exists_harperScheduledMovingHeightOscillation_le_milli :
    ∃ J : ℕ, ∀ M j y : ℕ,
      J + Nat.clog 2 (M + 1) ≤ j →
        harperBlockEndpoint (j + 1) ≤ y →
          ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
            |harperScheduledOscillationMass y j (2 * t)| ≤
              (1 / 1000 : ℝ) := by
  obtain ⟨c, hc, C, hC, Josc, hosc⟩ :=
    exists_harperScheduledMovingHeightOscillationBounds
  obtain ⟨Jtheta, htheta⟩ := Filter.eventually_atTop.1
    (eventually_harperScheduledThetaEnvelope_le_invLog_sq hc hC.le)
  have hq : Tendsto (fun J : ℕ ↦ (1 / 2 : ℝ) ^ J)
      atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hq2 : Tendsto (fun J : ℕ ↦ (1 / 2 : ℝ) ^ (2 * J))
      atTop (𝓝 0) := by
    convert! hq.pow 2 using 1
    · funext J
      rw [show 2 * J = J * 2 by omega, pow_mul]
    · norm_num
  have hsmallTendsto : Tendsto
      (fun J : ℕ ↦ (1 / 2 : ℝ) ^ J +
        5 * (C + 1) * (1 / 2 : ℝ) ^ (2 * J))
      atTop (𝓝 0) := by
    convert! hq.add
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ 5 * (C + 1))
        atTop (𝓝 (5 * (C + 1)))).mul hq2) using 1 <;> norm_num
  have hsmallEventually : ∀ᶠ J : ℕ in atTop,
      (1 / 2 : ℝ) ^ J +
        5 * (C + 1) * (1 / 2 : ℝ) ^ (2 * J) <
          (1 / 1000 : ℝ) :=
    (tendsto_order.mp hsmallTendsto).2 (1 / 1000 : ℝ) (by norm_num)
  obtain ⟨Jsmall, hsmall⟩ := Filter.eventually_atTop.1 hsmallEventually
  let J := max Josc (max Jtheta Jsmall)
  refine ⟨J, ?_⟩
  intro M j y hj hy t htLower htUpper
  have hjOsc : Josc ≤ j := by omega
  have hjTheta : Jtheta ≤ j := by omega
  have hshiftSmall : Jsmall + Nat.clog 2 (M + 1) ≤ j := by omega
  have hraw := hosc M j y hjOsc hy (2 * t) (by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith) (by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left htUpper (by norm_num))
  have henvelope := harperScheduledOscillationEnvelope_le_clog_shift
    hC.le hshiftSmall (htheta j hjTheta)
  exact hraw.trans (henvelope.trans (hsmall Jsmall le_rfl).le)

/-- Sharp diagonal variance bounds with an absolute plus logarithmic
threshold, uniform in the growing height cutoff. -/
theorem exists_harperScheduledMovingHeightDiagonalVariance_third_threeEighths :
    ∃ J : ℕ, ∀ M j y : ℕ,
      J + Nat.clog 2 (M + 1) ≤ j →
        harperBlockEndpoint (j + 1) ≤ y →
          ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
            (1 / 3 : ℝ) <
                harperLinearBlockVariance y
                  (harperScheduledPrimeBlock y j) t t ∧
              harperLinearBlockVariance y
                (harperScheduledPrimeBlock y j) t t < 3 / 8 := by
  obtain ⟨Jmass, hmass⟩ :=
    exists_eventually_harperScheduledPrimeBlock_inv_close_log_two
      (by norm_num : (0 : ℝ) < 1 / 1000)
  obtain ⟨Josc, hosc⟩ :=
    exists_harperScheduledMovingHeightOscillation_le_milli
  obtain ⟨Jloss, hloss⟩ :=
    exists_eventually_harperScheduledVarianceBiasLoss_lt
      (by norm_num : (0 : ℝ) < 1 / 1000)
  refine ⟨max Jmass (max Josc Jloss), ?_⟩
  intro M j y hj hy t htLower htUpper
  have hjmass : Jmass ≤ j := by omega
  have hjosc : Josc + Nat.clog 2 (M + 1) ≤ j := by omega
  have hjloss : Jloss ≤ j := by omega
  let reciprocalMass : ℝ :=
    ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹
  let oscillatoryMass : ℝ :=
    ∑ p ∈ harperScheduledPrimeBlock y j,
      Real.cos ((2 * t) * Real.log (p.1 : ℝ)) / p.1
  let biasLoss : ℝ := harperScheduledVarianceBiasLoss y j t
  have hmassj : |reciprocalMass - Real.log 2| < (1 / 1000 : ℝ) :=
    hmass j hjmass y hy
  have hoscj : |oscillatoryMass| ≤ (1 / 1000 : ℝ) := by
    simpa only [oscillatoryMass, harperScheduledOscillationMass] using!
      hosc M j y hjosc hy t htLower htUpper
  have hlossj : biasLoss < (1 / 1000 : ℝ) :=
    hloss j hjloss y hy t
  have hlossNonneg : 0 ≤ biasLoss :=
    harperScheduledVarianceBiasLoss_nonneg y j t
  have hvarianceIdentity :
      harperLinearBlockVariance y
          (harperScheduledPrimeBlock y j) t t =
        (1 / 2 : ℝ) * (reciprocalMass + oscillatoryMass) - biasLoss := by
    rw [harperScheduledDiagonalVariance_eq_cosineMass_sub_biasLoss,
      sum_harperScheduledPrimeBlock_cos_sq_div]
  rw [hvarianceIdentity]
  have hmassLower := neg_lt_of_abs_lt hmassj
  have hmassUpper := lt_of_abs_lt hmassj
  have hoscLower := neg_le_of_abs_le hoscj
  have hoscUpper := le_of_abs_le hoscj
  constructor <;> nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Sharp diagonal quadratic-drift bounds with a logarithmic height shift. -/
theorem exists_harperScheduledMovingHeightDiagonalMainMean_half_one :
    ∃ J : ℕ, ∀ M j y : ℕ,
      J + Nat.clog 2 (M + 1) ≤ j →
        harperBlockEndpoint (j + 1) ≤ y →
          ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
            (1 / 2 : ℝ) <
                harperLogMainBlockMean y
                  (harperScheduledPrimeBlock y j) t t ∧
              harperLogMainBlockMean y
                (harperScheduledPrimeBlock y j) t t < 1 := by
  obtain ⟨Jmass, hmass⟩ :=
    exists_eventually_harperScheduledPrimeBlock_inv_close_log_two
      (by norm_num : (0 : ℝ) < 1 / 1000)
  obtain ⟨Josc, hosc⟩ :=
    exists_harperScheduledMovingHeightOscillation_le_milli
  obtain ⟨Jcorrection, hcorrection⟩ :=
    exists_eventually_harperScheduledDiagonalCorrection_lt
      (by norm_num : (0 : ℝ) < 1 / 1000)
  refine ⟨max Jmass (max Josc Jcorrection), ?_⟩
  intro M j y hj hy t htLower htUpper
  have hjmass : Jmass ≤ j := by omega
  have hjosc : Josc + Nat.clog 2 (M + 1) ≤ j := by omega
  have hjcorrection : Jcorrection ≤ j := by omega
  let reciprocalMass : ℝ :=
    ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹
  let oscillatoryMass : ℝ :=
    ∑ p ∈ harperScheduledPrimeBlock y j,
      Real.cos ((2 * t) * Real.log (p.1 : ℝ)) / p.1
  let correction : ℝ := harperScheduledDiagonalCorrection y j t
  have hmassj : |reciprocalMass - Real.log 2| < (1 / 1000 : ℝ) :=
    hmass j hjmass y hy
  have hoscj : |oscillatoryMass| ≤ (1 / 1000 : ℝ) := by
    simpa only [oscillatoryMass, harperScheduledOscillationMass] using!
      hosc M j y hjosc hy t htLower htUpper
  have hcorrectionj : correction < (1 / 1000 : ℝ) :=
    hcorrection j hjcorrection y hy t
  have hcorrectionNonneg : 0 ≤ correction :=
    harperScheduledDiagonalCorrection_nonneg y j t
  have hmeanIdentity :
      harperLogMainBlockMean y
          (harperScheduledPrimeBlock y j) t t =
        reciprocalMass + (1 / 2 : ℝ) * oscillatoryMass - correction := by
    simpa only [reciprocalMass, oscillatoryMass, correction,
      harperScheduledDiagonalCorrection] using!
        harperScheduledDiagonalMainMean_eq y j t
  rw [hmeanIdentity]
  have hmassLower := neg_lt_of_abs_lt hmassj
  have hmassUpper := lt_of_abs_lt hmassj
  have hoscLower := neg_le_of_abs_le hoscj
  have hoscUpper := le_of_abs_le hoscj
  constructor <;> nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Supplied-scale stability of the variance on moving height windows.  This
is the interface consumed by refined checkpoint meshes. -/
theorem exists_harperScheduledMovingHeightVariancePerturbation :
    ∃ J : ℕ, ∀ M j y : ℕ,
      J + Nat.clog 2 (M + 1) ≤ j →
        harperBlockEndpoint (j + 1) ≤ y →
          ∀ t u delta : ℝ, 0 ≤ delta →
            |u - t| * Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤ delta →
              |harperLinearBlockVariance y
                    (harperScheduledPrimeBlock y j) t u -
                harperLinearBlockVariance y
                    (harperScheduledPrimeBlock y j) t t| ≤ 3 * delta := by
  obtain ⟨Jmass, hJmass⟩ :=
    exists_eventually_harperScheduledPrimeBlock_inv_bounds
  refine ⟨Jmass, ?_⟩
  intro M j y hj hy t u delta hdelta hscale
  exact abs_harperScheduledLinearBlockVariance_sub_diagonal_le_three_mul
    y j t u delta hdelta (hJmass j (by omega) y hy).2 hscale

/-- Supplied-scale stability of the quadratic logarithmic drift on moving
height windows. -/
theorem exists_harperScheduledMovingHeightMainMeanPerturbation :
    ∃ J : ℕ, ∀ M j y : ℕ,
      J + Nat.clog 2 (M + 1) ≤ j →
        harperBlockEndpoint (j + 1) ≤ y →
          ∀ t u delta : ℝ, 0 ≤ delta →
            |u - t| * Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤ delta →
              |harperLogMainBlockMean y
                    (harperScheduledPrimeBlock y j) t u -
                harperLogMainBlockMean y
                    (harperScheduledPrimeBlock y j) t t| ≤
                  (9 / 2 : ℝ) * delta := by
  obtain ⟨Jmass, hJmass⟩ :=
    exists_eventually_harperScheduledPrimeBlock_inv_bounds
  refine ⟨Jmass, ?_⟩
  intro M j y hj hy t u delta hdelta hscale
  exact abs_harperScheduledLogMainBlockMean_sub_diagonal_le_nine_halves_mul
    y j t u delta hdelta (hJmass j (by omega) y hy).2 hscale

/-- A reciprocal-log checkpoint displacement preserves the standard
off-diagonal variance window for every growing height cutoff. -/
theorem exists_harperScheduledMovingHeightOffDiagonalVariance_quarter_half :
    ∃ J : ℕ, ∀ M j y : ℕ,
      J + Nat.clog 2 (M + 1) ≤ j →
        harperBlockEndpoint (j + 1) ≤ y →
          ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : ℝ,
            |u - t| * Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤
                (1 / 64 : ℝ) →
              (1 / 4 : ℝ) <
                  harperLinearBlockVariance y
                    (harperScheduledPrimeBlock y j) t u ∧
                harperLinearBlockVariance y
                  (harperScheduledPrimeBlock y j) t u < 1 / 2 := by
  obtain ⟨Jmass, hJmass⟩ :=
    exists_eventually_harperScheduledPrimeBlock_inv_bounds
  obtain ⟨Jdiag, hJdiag⟩ :=
    exists_harperScheduledMovingHeightDiagonalVariance_third_threeEighths
  refine ⟨max Jmass Jdiag, ?_⟩
  intro M j y hj hy t htLower htUpper u hscale
  have hdiag := hJdiag M j y (by omega) hy t htLower htUpper
  have hclose :=
    abs_harperScheduledLinearBlockVariance_sub_diagonal_le_three_mul
      y j t u (1 / 64 : ℝ) (by norm_num)
        (hJmass j (by omega) y hy).2 hscale
  have hlower := neg_le_of_abs_le hclose
  have hupper := le_of_abs_le hclose
  constructor <;> nlinarith

/-- The same checkpoint displacement preserves the standard positive drift
window for every growing height cutoff. -/
theorem exists_harperScheduledMovingHeightOffDiagonalMainMean_threeEighths_nineEighths :
    ∃ J : ℕ, ∀ M j y : ℕ,
      J + Nat.clog 2 (M + 1) ≤ j →
        harperBlockEndpoint (j + 1) ≤ y →
          ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : ℝ,
            |u - t| * Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤
                (1 / 64 : ℝ) →
              (3 / 8 : ℝ) <
                  harperLogMainBlockMean y
                    (harperScheduledPrimeBlock y j) t u ∧
                harperLogMainBlockMean y
                  (harperScheduledPrimeBlock y j) t u < 9 / 8 := by
  obtain ⟨Jmass, hJmass⟩ :=
    exists_eventually_harperScheduledPrimeBlock_inv_bounds
  obtain ⟨Jdiag, hJdiag⟩ :=
    exists_harperScheduledMovingHeightDiagonalMainMean_half_one
  refine ⟨max Jmass Jdiag, ?_⟩
  intro M j y hj hy t htLower htUpper u hscale
  have hdiag := hJdiag M j y (by omega) hy t htLower htUpper
  have hclose :=
    abs_harperScheduledLogMainBlockMean_sub_diagonal_le_nine_halves_mul
      y j t u (1 / 64 : ℝ) (by norm_num)
        (hJmass j (by omega) y hy).2 hscale
  have hlower := neg_le_of_abs_le hclose
  have hupper := le_of_abs_le hclose
  constructor <;> nlinarith

/-- Uniform off-diagonal variance and drift windows with an explicit
`clog` height shift. -/
theorem exists_harperScheduledMovingHeightOffDiagonalMoment_bounds :
    ∃ J : ℕ, ∀ M j y : ℕ,
      J + Nat.clog 2 (M + 1) ≤ j →
        harperBlockEndpoint (j + 1) ≤ y →
          ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : ℝ,
            |u - t| * Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤
                (1 / 64 : ℝ) →
              ((1 / 4 : ℝ) <
                  harperLinearBlockVariance y
                    (harperScheduledPrimeBlock y j) t u ∧
                harperLinearBlockVariance y
                  (harperScheduledPrimeBlock y j) t u < 1 / 2) ∧
              ((3 / 8 : ℝ) <
                  harperLogMainBlockMean y
                    (harperScheduledPrimeBlock y j) t u ∧
                harperLogMainBlockMean y
                  (harperScheduledPrimeBlock y j) t u < 9 / 8) := by
  obtain ⟨Jvar, hJvar⟩ :=
    exists_harperScheduledMovingHeightOffDiagonalVariance_quarter_half
  obtain ⟨Jmean, hJmean⟩ :=
    exists_harperScheduledMovingHeightOffDiagonalMainMean_threeEighths_nineEighths
  refine ⟨max Jvar Jmean, ?_⟩
  intro M j y hj hy t htLower htUpper u hscale
  exact ⟨
    hJvar M j y (by omega) hy t htLower htUpper u hscale,
    hJmean M j y (by omega) hy t htLower htUpper u hscale⟩

end Problem520
end Erdos
