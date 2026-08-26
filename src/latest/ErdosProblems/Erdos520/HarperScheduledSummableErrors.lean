import ErdosProblems.Erdos520.HarperInverseEulerMoment
import ErdosProblems.Erdos520.HarperFairEulerProduct
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Set Function Filter Finset MeasureTheory ProbabilityTheory Topology
open scoped BigOperators

noncomputable section

namespace Erdos
namespace Problem520

/-!
# Summable arithmetic errors on Harper's scheduled blocks

The scheduled endpoints grow by exact squaring.  Consequently the strong-PNT
errors are not merely `o(1)` block by block: their total over every later
prefix is finite, and the remaining tail tends to zero with the starting
block.  This is the quantitative form needed to prevent an `O(n)` loss when
the number of blocks varies.
-/

/-! ## Geometric scale identities -/

theorem log_harperBlockEndpoint_eq (j : ℕ) :
    Real.log (harperBlockEndpoint j : ℝ) =
      (16 : ℝ) * (2 : ℝ) ^ j * Real.log 2 := by
  unfold harperBlockEndpoint
  push_cast
  rw [Real.log_pow]
  norm_cast

theorem invLog_harperBlockEndpoint_eq (j : ℕ) :
    invLog (harperBlockEndpoint j) =
      ((16 : ℝ) * Real.log 2)⁻¹ * ((1 : ℝ) / 2) ^ j := by
  rw [invLog, log_harperBlockEndpoint_eq]
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [div_pow]
  field_simp
  ring

theorem summable_invLog_harperBlockEndpoint :
    Summable (fun j : ℕ ↦ invLog (harperBlockEndpoint j)) := by
  have h := summable_geometric_two.mul_left
    (((16 : ℝ) * Real.log 2)⁻¹)
  simpa only [invLog_harperBlockEndpoint_eq] using! h

theorem summable_invLog_harperBlockEndpoint_sq :
    Summable (fun j : ℕ ↦ invLog (harperBlockEndpoint j) ^ 2) := by
  have hgeom : Summable (fun j : ℕ ↦ ((1 / 4 : ℝ) ^ j)) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have h := hgeom.mul_left (((16 : ℝ) * Real.log 2)⁻¹ ^ 2)
  apply h.congr
  intro j
  rw [invLog_harperBlockEndpoint_eq]
  ring_nf
  rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num,
    ← pow_mul, Nat.mul_comm 2 j]

theorem invLog_harperBlockEndpoint_pos (j : ℕ) :
    0 < invLog (harperBlockEndpoint j) := by
  apply invLog_pos
  exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 16)
    (harperBlockEndpoint_ge_sixteen j)

theorem one_le_log_harperBlockEndpoint (j : ℕ) :
    (1 : ℝ) ≤ Real.log (harperBlockEndpoint j : ℝ) := by
  have hlog16 : (1 : ℝ) ≤ Real.log 16 := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 4)
    have hlog4 : Real.log 4 ≥ 1 := by
      have hexp : Real.exp 1 ≤ 4 := by
        exact (Real.exp_one_lt_d9.trans (by norm_num : (2.7182818286 : ℝ) < 4)).le
      exact (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 4)).2 hexp
    have hlogmono : Real.log 4 ≤ Real.log 16 :=
      Real.log_le_log (by norm_num) (by norm_num)
    linarith
  have hendpoint : (16 : ℝ) ≤ harperBlockEndpoint j := by
    exact_mod_cast harperBlockEndpoint_ge_sixteen j
  exact hlog16.trans (Real.log_le_log (by norm_num) hendpoint)

theorem invLog_harperBlockEndpoint_le_one (j : ℕ) :
    invLog (harperBlockEndpoint j) ≤ 1 := by
  have hlog := one_le_log_harperBlockEndpoint j
  unfold invLog
  exact (inv_le_one₀ (lt_of_lt_of_le (by norm_num) hlog)).2 hlog

/-! ## The strong-PNT envelope is summable -/

noncomputable def harperScheduledThetaEnvelope
    (c C : ℝ) (j : ℕ) : ℝ :=
  mediumThetaBlockDelta c C
    (harperBlockEndpoint j) (harperBlockEndpoint (j + 1))

noncomputable def harperScheduledOscillationEnvelope
    (M : ℕ) (c C : ℝ) (j : ℕ) : ℝ :=
  invLog (harperBlockEndpoint j) +
    (3 + 2 * (M : ℝ)) * harperScheduledThetaEnvelope c C j

noncomputable def harperScheduledReciprocalEnvelope
    (c C : ℝ) (j : ℕ) : ℝ :=
  4 * harperScheduledThetaEnvelope c C j

noncomputable def harperScheduledSquareEnvelope (j : ℕ) : ℝ :=
  (3 / 2 : ℝ) * (harperBlockEndpoint j : ℝ)⁻¹

theorem harperScheduledThetaEnvelope_nonneg
    {c C : ℝ} (hC : 0 ≤ C) (j : ℕ) :
    0 ≤ harperScheduledThetaEnvelope c C j := by
  rw [harperScheduledThetaEnvelope, harperBlockEndpoint_succ,
    mediumThetaBlockDelta_square_eq]
  positivity

theorem harperScheduledOscillationEnvelope_nonneg
    (M : ℕ) {c C : ℝ} (hC : 0 ≤ C) (j : ℕ) :
    0 ≤ harperScheduledOscillationEnvelope M c C j := by
  unfold harperScheduledOscillationEnvelope
  exact add_nonneg (invLog_harperBlockEndpoint_pos j).le
    (mul_nonneg (by positivity)
      (harperScheduledThetaEnvelope_nonneg hC j))

theorem harperScheduledReciprocalEnvelope_nonneg
    {c C : ℝ} (hC : 0 ≤ C) (j : ℕ) :
    0 ≤ harperScheduledReciprocalEnvelope c C j := by
  unfold harperScheduledReciprocalEnvelope
  exact mul_nonneg (by norm_num)
    (harperScheduledThetaEnvelope_nonneg hC j)

theorem harperScheduledSquareEnvelope_nonneg (j : ℕ) :
    0 ≤ harperScheduledSquareEnvelope j := by
  unfold harperScheduledSquareEnvelope
  positivity

private theorem rpow_one_tenth_neg_twenty
    (L : ℝ) (hL : 0 < L) :
    (L ^ ((1 : ℝ) / 10)) ^ (-20 : ℝ) = (L⁻¹) ^ 2 := by
  rw [← Real.rpow_mul hL.le]
  norm_num

private theorem eventually_exp_medium_le_inv_log_sq
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) ≤
        (Real.log x)⁻¹ ^ 2 := by
  have hscale : Tendsto
      (fun x : ℝ ↦ Real.log x ^ ((1 : ℝ) / 10))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
      Real.tendsto_log_atTop
  have hsmall := hscale.eventually
    (isLittleO_exp_neg_mul_rpow_atTop hc (-20)).eventuallyLE
  filter_upwards [hsmall,
      Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx hlog
  have hlogpos : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hlog
  rw [Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.norm_of_nonneg (Real.rpow_nonneg
      (Real.rpow_nonneg hlogpos.le _) _)] at hx
  rw [rpow_one_tenth_neg_twenty (Real.log x) hlogpos] at hx
  exact hx

private theorem eventually_four_log_div_sqrt_le_inv_log_sq :
    ∀ᶠ x : ℝ in atTop,
      4 * Real.log x / Real.sqrt x ≤ (Real.log x)⁻¹ ^ 2 := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (3 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).bound
      (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [hsmall, Real.tendsto_log_atTop.eventually_ge_atTop 1,
      eventually_gt_atTop (0 : ℝ)] with x hx hlog hx0
  have hlogpos : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hlog
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlogpos.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hx
  rw [Real.sqrt_eq_rpow]
  have hsqrtpos : 0 < x ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hx0 _
  have hx' : Real.log x ^ (3 : ℕ) ≤
      (1 / 4 : ℝ) * x ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast]
    exact hx
  have hcube : 4 * Real.log x ^ 3 ≤ x ^ ((1 : ℝ) / 2) := by
    calc
      4 * Real.log x ^ 3 ≤
          4 * ((1 / 4 : ℝ) * x ^ ((1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hx' (by norm_num)
      _ = x ^ ((1 : ℝ) / 2) := by ring
  apply (div_le_iff₀ hsqrtpos).2
  have hinvSq : (Real.log x)⁻¹ ^ 2 * x ^ ((1 : ℝ) / 2) =
      x ^ ((1 : ℝ) / 2) / Real.log x ^ 2 := by
    field_simp
  rw [hinvSq]
  apply (le_div_iff₀ (sq_pos_of_pos hlogpos)).2
  calc
    4 * Real.log x * Real.log x ^ 2 = 4 * Real.log x ^ 3 := by ring
    _ ≤ x ^ ((1 : ℝ) / 2) := hcube

theorem eventually_harperScheduledThetaEnvelope_le_invLog_sq
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) :
    ∀ᶠ j : ℕ in atTop,
      harperScheduledThetaEnvelope c C j ≤
        (C + 1) * invLog (harperBlockEndpoint j) ^ 2 := by
  have hend : Tendsto (fun j : ℕ ↦ (harperBlockEndpoint j : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      strictMono_harperBlockEndpoint.tendsto_atTop
  have hexp := hend.eventually (eventually_exp_medium_le_inv_log_sq hc)
  have hsqrt := hend.eventually eventually_four_log_div_sqrt_le_inv_log_sq
  filter_upwards [hexp, hsqrt] with j hexpJ hsqrtJ
  rw [harperScheduledThetaEnvelope, harperBlockEndpoint_succ,
    mediumThetaBlockDelta_square_eq]
  unfold invLog
  calc
    C * Real.exp
          (-c * Real.log (harperBlockEndpoint j : ℝ) ^ ((1 : ℝ) / 10)) +
        4 * Real.log (harperBlockEndpoint j : ℝ) /
          Real.sqrt (harperBlockEndpoint j : ℝ) ≤
        C * (Real.log (harperBlockEndpoint j : ℝ))⁻¹ ^ 2 +
          (Real.log (harperBlockEndpoint j : ℝ))⁻¹ ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hexpJ hC) hsqrtJ
    _ = (C + 1) * (Real.log (harperBlockEndpoint j : ℝ))⁻¹ ^ 2 := by
      ring

theorem summable_harperScheduledThetaEnvelope
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) :
    Summable (harperScheduledThetaEnvelope c C) := by
  apply Summable.of_norm_bounded_eventually_nat
    ((summable_invLog_harperBlockEndpoint_sq.mul_left (C + 1)))
  filter_upwards [eventually_harperScheduledThetaEnvelope_le_invLog_sq hc hC]
    with j hj
  rw [Real.norm_eq_abs, abs_of_nonneg
    (harperScheduledThetaEnvelope_nonneg hC j)]
  exact hj

theorem summable_harperScheduledOscillationEnvelope
    (M : ℕ) {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) :
    Summable (harperScheduledOscillationEnvelope M c C) := by
  exact summable_invLog_harperBlockEndpoint.add
    ((summable_harperScheduledThetaEnvelope hc hC).mul_left
      (3 + 2 * (M : ℝ)))

theorem summable_harperScheduledReciprocalEnvelope
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) :
    Summable (harperScheduledReciprocalEnvelope c C) := by
  exact (summable_harperScheduledThetaEnvelope hc hC).mul_left 4

theorem summable_inv_harperBlockEndpoint :
    Summable (fun j : ℕ ↦ (harperBlockEndpoint j : ℝ)⁻¹) := by
  apply summable_of_ratio_norm_eventually_le
    (show (1 / 16 : ℝ) < 1 by norm_num)
  filter_upwards [] with j
  have hApos : (0 : ℝ) < harperBlockEndpoint j := by
    exact_mod_cast harperBlockEndpoint_pos j
  have hA16 : (16 : ℝ) ≤ harperBlockEndpoint j := by
    exact_mod_cast harperBlockEndpoint_ge_sixteen j
  rw [harperBlockEndpoint_succ]
  push_cast
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hApos)),
    abs_of_pos (inv_pos.mpr hApos)]
  have hmul : (16 : ℝ) * harperBlockEndpoint j ≤
      (harperBlockEndpoint j : ℝ) ^ 2 := by nlinarith
  calc
    ((harperBlockEndpoint j : ℝ) ^ 2)⁻¹ ≤
        ((16 : ℝ) * harperBlockEndpoint j)⁻¹ :=
      inv_anti₀ (mul_pos (by norm_num) hApos) hmul
    _ = (1 / 16 : ℝ) * (harperBlockEndpoint j : ℝ)⁻¹ := by
      field_simp

theorem summable_harperScheduledSquareEnvelope :
    Summable harperScheduledSquareEnvelope := by
  exact summable_inv_harperBlockEndpoint.mul_left (3 / 2 : ℝ)

/-! ## Tails and finite prefixes -/

noncomputable def harperScheduledErrorTail
    (e : ℕ → ℝ) (start : ℕ) : ℝ :=
  ∑' k : ℕ, e (k + start)

theorem tendsto_harperScheduledErrorTail_zero (e : ℕ → ℝ) :
    Tendsto (harperScheduledErrorTail e) atTop (nhds 0) := by
  simpa only [harperScheduledErrorTail] using! tendsto_sum_nat_add e

theorem sum_fin_le_harperScheduledErrorTail
    {e : ℕ → ℝ} (he0 : ∀ j, 0 ≤ e j) (he : Summable e)
    (start n : ℕ) :
    (∑ i : Fin n, e (start + (i : ℕ))) ≤
      harperScheduledErrorTail e start := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ e (start + k)) n]
  have hshift : Summable (fun k : ℕ ↦ e (k + start)) :=
    (summable_nat_add_iff start).2 he
  have hle := hshift.sum_le_tsum (Finset.range n)
    (fun k _hk ↦ he0 (k + start))
  simpa only [harperScheduledErrorTail, add_comm] using! hle

theorem harperScheduledErrorTail_le_tsum
    {e : ℕ → ℝ} (he0 : ∀ j, 0 ≤ e j) (he : Summable e)
    (start : ℕ) :
    harperScheduledErrorTail e start ≤ ∑' j : ℕ, e j := by
  have hsplit := he.sum_add_tsum_nat_add start
  have hpartial : 0 ≤ ∑ j ∈ Finset.range start, e j :=
    Finset.sum_nonneg fun j _hj ↦ he0 j
  unfold harperScheduledErrorTail
  linarith

/-! ## Uniform blockwise consequences of the strong PNT -/

noncomputable def harperScheduledReciprocalMass (y j : ℕ) : ℝ :=
  ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹

noncomputable def harperScheduledOscillationMass
    (y j : ℕ) (tau : ℝ) : ℝ :=
  ∑ p ∈ harperScheduledPrimeBlock y j,
    Real.cos (tau * Real.log (p.1 : ℝ)) / p.1

noncomputable def harperScheduledSquareMass (y j : ℕ) : ℝ :=
  ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹ ^ 2

/-- One choice of the constants in the vendored strong PNT controls all
three scheduled error sequences.  The envelopes are independent of the
ambient cutoff `y` and of the frequency inside the fixed window. -/
theorem exists_harperScheduledSummableBlockErrorBounds (M : ℕ) :
    ∃ c > 0, ∃ C > 0, ∃ J : ℕ,
      ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
        harperBlockEndpoint (j + 1) ≤ y →
          |harperScheduledReciprocalMass y j - Real.log 2| ≤
              harperScheduledReciprocalEnvelope c C j ∧
            (∀ tau : ℝ, 2 ≤ |tau| → |tau| ≤ 2 * M →
              |harperScheduledOscillationMass y j tau| ≤
                harperScheduledOscillationEnvelope M c C j) ∧
            harperScheduledSquareMass y j ≤
              harperScheduledSquareEnvelope j := by
  obtain ⟨c, hc, C, hC, X₀, hX₀two, htheta⟩ := exists_mediumThetaError
  obtain ⟨Jmass, hJmass⟩ :=
    exists_eventually_harperScheduledPrimeBlock_inv_bounds
  have hend : Tendsto (fun j : ℕ ↦ (harperBlockEndpoint j : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      strictMono_harperBlockEndpoint.tendsto_atTop
  obtain ⟨Jpnt, hJpnt⟩ := Filter.eventually_atTop.1
    (hend.eventually_ge_atTop X₀)
  refine ⟨c, hc, C, hC, max Jmass Jpnt, ?_⟩
  intro j hj y hy
  have hjMass : Jmass ≤ j := (le_max_left Jmass Jpnt).trans hj
  have hjPnt : Jpnt ≤ j := (le_max_right Jmass Jpnt).trans hj
  let A : ℕ := harperBlockEndpoint j
  let B : ℕ := harperBlockEndpoint (j + 1)
  let delta : ℝ := harperScheduledThetaEnvelope c C j
  let ell : ℝ := invLog (harperBlockEndpoint j)
  have hA2 : 2 ≤ A := by
    dsimp [A]
    have := harperBlockEndpoint_ge_sixteen j
    omega
  have hAB : A ≤ B := by
    dsimp [A, B]
    exact monotone_harperBlockEndpoint (by omega)
  have hX₀A : X₀ ≤ (A : ℝ) := by
    exact hJpnt j hjPnt
  have hdelta : 0 ≤ delta := by
    dsimp [delta]
    exact harperScheduledThetaEnvelope_nonneg hC.le j
  have herror : ∀ x ∈ Set.Icc (A : ℝ) B,
      |thetaError x| ≤ delta * x := by
    intro x hx
    exact thetaError_le_mediumThetaBlockDelta hc hC.le htheta
      hA2 hAB hX₀A hx
  have hmassBounds := hJmass j hjMass y hy
  have hmass :
      |harperScheduledReciprocalMass y j - Real.log 2| ≤
        harperScheduledReciprocalEnvelope c C j := by
    rw [harperScheduledReciprocalMass,
      sum_harperScheduledPrimeBlock_inv_eq_freshReciprocalSum hy,
      harperBlockEndpoint_succ]
    exact abs_freshReciprocalSum_square_sub_log_two_le_of_thetaError
      hA2 (one_le_log_harperBlockEndpoint j) hdelta (by
        simpa only [A, B, delta, harperBlockEndpoint_succ] using! herror)
  refine ⟨hmass, ?_, ?_⟩
  · intro tau htauLower htauUpper
    have htau : tau ≠ 0 := by
      have : 0 < |tau| := lt_of_lt_of_le (by norm_num) htauLower
      exact abs_pos.mp this
    have hraw := abs_primeOscillation_le_of_thetaError
      hA2 hAB htau hdelta herror
    rw [harperScheduledOscillationMass,
      sum_harperScheduledPrimeBlock_cos_div_eq hy tau]
    simp only [oscKernel] at hraw
    have hratio : ((B : ℝ) / A) = (A : ℝ) := by
      dsimp [A, B]
      rw [harperBlockEndpoint_succ]
      push_cast
      have hAne : (harperBlockEndpoint j : ℝ) ≠ 0 := by positivity
      field_simp
    have hlogCancel : Real.log ((B : ℝ) / A) * ell = 1 := by
      rw [hratio]
      dsimp [ell, A, invLog]
      exact mul_inv_cancel₀
        (Real.log_pos (by
          exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 16)
            (harperBlockEndpoint_ge_sixteen j))).ne'
    have htauDiv : 2 / |tau| ≤ 1 := by
      apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) htauLower)).2
      linarith
    have hell0 : 0 ≤ ell := (invLog_harperBlockEndpoint_pos j).le
    have hell1 : ell ≤ 1 := invLog_harperBlockEndpoint_le_one j
    calc
      |∑ p ∈ (Finset.Ioc A B).filter Nat.Prime,
          Real.cos (tau * Real.log (p : ℝ)) / p| ≤
          (2 / |tau| + 2 * delta +
            delta * (1 + |tau|) * Real.log ((B : ℝ) / A)) * ell := by
        simpa only [ell] using! hraw
      _ = (2 / |tau|) * ell + 2 * delta * ell +
          delta * (1 + |tau|) *
            (Real.log ((B : ℝ) / A) * ell) := by ring
      _ = (2 / |tau|) * ell + 2 * delta * ell +
          delta * (1 + |tau|) := by rw [hlogCancel, mul_one]
      _ ≤ ell + 2 * delta + delta * (1 + 2 * (M : ℝ)) := by
        have hfirst : (2 / |tau|) * ell ≤ ell := by
          simpa only [one_mul] using!
            mul_le_mul_of_nonneg_right htauDiv hell0
        have hsecond : 2 * delta * ell ≤ 2 * delta := by
          nlinarith
        have hthird : delta * (1 + |tau|) ≤
            delta * (1 + 2 * (M : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) hdelta
        linarith
      _ = harperScheduledOscillationEnvelope M c C j := by
        dsimp [ell, delta, harperScheduledOscillationEnvelope]
        ring
  · dsimp [harperScheduledSquareMass, harperScheduledSquareEnvelope]
    calc
      (∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹ ^ 2) ≤
          (harperBlockEndpoint j : ℝ)⁻¹ *
            ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹ :=
        sum_harperScheduledPrimeBlock_inv_sq_le y j
      _ ≤ (harperBlockEndpoint j : ℝ)⁻¹ * (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hmassBounds.2 (by positivity)
      _ = (3 / 2 : ℝ) * (harperBlockEndpoint j : ℝ)⁻¹ := by ring

/-! ## Uniform cumulative prefix and range bounds -/

/-- All three accumulated errors are controlled by tails independent of the
path length.  The first inequality is the matching cumulative logarithmic
drift estimate. -/
theorem exists_harperScheduledCumulativeErrorBounds (M : ℕ) :
    ∃ c > 0, ∃ C > 0, ∃ J : ℕ,
      ∀ start n y : ℕ, J ≤ start →
        harperBlockEndpoint (start + n) ≤ y →
          ∀ u : Fin n → ℝ,
            (∀ i, 1 ≤ |u i|) → (∀ i, |u i| ≤ M) →
              |(∑ i : Fin n,
                  harperScheduledReciprocalMass y (start + (i : ℕ))) -
                    (n : ℝ) * Real.log 2| ≤
                harperScheduledErrorTail
                  (harperScheduledReciprocalEnvelope c C) start ∧
              (∑ i : Fin n,
                  |harperScheduledOscillationMass y (start + (i : ℕ))
                    (2 * u i)|) ≤
                harperScheduledErrorTail
                  (harperScheduledOscillationEnvelope M c C) start ∧
              (∑ i : Fin n,
                  harperScheduledSquareMass y (start + (i : ℕ))) ≤
                harperScheduledErrorTail harperScheduledSquareEnvelope start := by
  obtain ⟨c, hc, C, hC, J, hblock⟩ :=
    exists_harperScheduledSummableBlockErrorBounds M
  refine ⟨c, hc, C, hC, J, ?_⟩
  intro start n y hstart hy u huLower huUpper
  have hyi : ∀ i : Fin n,
      harperBlockEndpoint (start + (i : ℕ) + 1) ≤ y := by
    intro i
    have hindex : start + (i : ℕ) + 1 ≤ start + n := by omega
    exact (monotone_harperBlockEndpoint hindex).trans hy
  have hji : ∀ i : Fin n, J ≤ start + (i : ℕ) := by
    intro i
    omega
  have hpoint : ∀ i : Fin n,
      |harperScheduledReciprocalMass y (start + (i : ℕ)) - Real.log 2| ≤
          harperScheduledReciprocalEnvelope c C (start + (i : ℕ)) ∧
        |harperScheduledOscillationMass y (start + (i : ℕ)) (2 * u i)| ≤
          harperScheduledOscillationEnvelope M c C (start + (i : ℕ)) ∧
        harperScheduledSquareMass y (start + (i : ℕ)) ≤
          harperScheduledSquareEnvelope (start + (i : ℕ)) := by
    intro i
    have hb := hblock (start + (i : ℕ)) (hji i) y (hyi i)
    have habsTwo : |2 * u i| = 2 * |u i| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hlower : 2 ≤ |2 * u i| := by rw [habsTwo]; linarith [huLower i]
    have hupper : |2 * u i| ≤ 2 * M := by
      rw [habsTwo]
      exact mul_le_mul_of_nonneg_left (huUpper i) (by norm_num)
    exact ⟨hb.1, hb.2.1 (2 * u i) hlower hupper, hb.2.2⟩
  have hmassSum :
      (∑ i : Fin n,
        |harperScheduledReciprocalMass y (start + (i : ℕ)) - Real.log 2|) ≤
        harperScheduledErrorTail
          (harperScheduledReciprocalEnvelope c C) start := by
    calc
      (∑ i : Fin n,
        |harperScheduledReciprocalMass y (start + (i : ℕ)) - Real.log 2|) ≤
          ∑ i : Fin n,
            harperScheduledReciprocalEnvelope c C (start + (i : ℕ)) :=
        Finset.sum_le_sum fun i _hi ↦ (hpoint i).1
      _ ≤ harperScheduledErrorTail
          (harperScheduledReciprocalEnvelope c C) start :=
        sum_fin_le_harperScheduledErrorTail
          (harperScheduledReciprocalEnvelope_nonneg hC.le)
          (summable_harperScheduledReciprocalEnvelope hc hC.le) start n
  have hmassIdentity :
      (∑ i : Fin n,
          harperScheduledReciprocalMass y (start + (i : ℕ))) -
          (n : ℝ) * Real.log 2 =
        ∑ i : Fin n,
          (harperScheduledReciprocalMass y (start + (i : ℕ)) -
            Real.log 2) := by
    rw [Finset.sum_sub_distrib]
    simp
  have hmassFinal :
      |(∑ i : Fin n,
          harperScheduledReciprocalMass y (start + (i : ℕ))) -
          (n : ℝ) * Real.log 2| ≤
        harperScheduledErrorTail
          (harperScheduledReciprocalEnvelope c C) start := by
    rw [hmassIdentity]
    exact (Finset.abs_sum_le_sum_abs _ _).trans hmassSum
  refine ⟨hmassFinal, ?_, ?_⟩
  · calc
      (∑ i : Fin n,
          |harperScheduledOscillationMass y (start + (i : ℕ)) (2 * u i)|) ≤
          ∑ i : Fin n,
            harperScheduledOscillationEnvelope M c C (start + (i : ℕ)) :=
        Finset.sum_le_sum fun i _hi ↦ (hpoint i).2.1
      _ ≤ harperScheduledErrorTail
          (harperScheduledOscillationEnvelope M c C) start :=
        sum_fin_le_harperScheduledErrorTail
          (harperScheduledOscillationEnvelope_nonneg M hC.le)
          (summable_harperScheduledOscillationEnvelope M hc hC.le) start n
  · calc
      (∑ i : Fin n,
          harperScheduledSquareMass y (start + (i : ℕ))) ≤
          ∑ i : Fin n,
            harperScheduledSquareEnvelope (start + (i : ℕ)) :=
        Finset.sum_le_sum fun i _hi ↦ (hpoint i).2.2
      _ ≤ harperScheduledErrorTail harperScheduledSquareEnvelope start :=
        sum_fin_le_harperScheduledErrorTail
          harperScheduledSquareEnvelope_nonneg
          summable_harperScheduledSquareEnvelope start n

/-! ## The full varying-height inverse product -/

/-- Inverse Euler energy on a finite prime set, allowing a different height
at every prime coordinate. -/
noncomputable def harperVaryingInverseEulerProduct
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (u : HarperPrimeIndex y → ℝ) (eta : HarperPrimeCube y) : ℝ :=
  ∏ p ∈ S, (harperCoordinateFactor p.1 (u p) (eta p))⁻¹

theorem integral_harperVaryingInverseEulerProduct
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (u : HarperPrimeIndex y → ℝ) :
    ∫ eta, harperVaryingInverseEulerProduct y S u eta
        ∂harperFairCubeLaw y =
      ∏ p ∈ S, harperInverseEulerPrimeMoment p.1 (u p) := by
  let g : HarperPrimeIndex y → Bool → ℝ := fun p b ↦
    if p ∈ S then (harperCoordinateFactor p.1 (u p) b)⁻¹ else 1
  have hfactor := integral_prod_harperFairCubeLaw y g
  have hleft : (fun eta ↦ ∏ p : HarperPrimeIndex y, g p (eta p)) =
      harperVaryingInverseEulerProduct y S u := by
    funext eta
    simp only [g, Finset.prod_ite_mem, Finset.univ_inter]
    rfl
  have hright : (∏ p : HarperPrimeIndex y, ∫ b, g p b ∂coin) =
      ∏ p ∈ S, harperInverseEulerPrimeMoment p.1 (u p) := by
    calc
      (∏ p : HarperPrimeIndex y, ∫ b, g p b ∂coin) =
          ∏ p : HarperPrimeIndex y,
            if p ∈ S then harperInverseEulerPrimeMoment p.1 (u p) else 1 := by
        apply Finset.prod_congr rfl
        intro p _hp
        by_cases hpS : p ∈ S
        · simp only [g, if_pos hpS]
          rfl
        · simp only [g, if_neg hpS]
          rw [integral_coin_bool]
          norm_num
      _ = ∏ p ∈ S, harperInverseEulerPrimeMoment p.1 (u p) :=
        Fintype.prod_ite_mem S _
  rw [hleft, hright] at hfactor
  exact hfactor

theorem integral_harperVaryingInverseEulerProduct_le_exp
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (h4 : ∀ p ∈ S, 4 ≤ p.1) (u : HarperPrimeIndex y → ℝ) :
    (∫ eta, harperVaryingInverseEulerProduct y S u eta
        ∂harperFairCubeLaw y) ≤
      Real.exp (∑ p ∈ S, harperInverseEulerPrimeExponent p.1 (u p)) := by
  rw [integral_harperVaryingInverseEulerProduct]
  calc
    (∏ p ∈ S, harperInverseEulerPrimeMoment p.1 (u p)) ≤
        ∏ p ∈ S, Real.exp (harperInverseEulerPrimeExponent p.1 (u p)) := by
      apply Finset.prod_le_prod
      · intro p hpS
        exact (harperInverseEulerPrimeMoment_pos
          (Nat.prime_of_mem_primesBelow p.property) (u p)).le
      · intro p hpS
        exact harperInverseEulerPrimeMoment_le_exp
          (Nat.prime_of_mem_primesBelow p.property) (h4 p hpS) (u p)
    _ = Real.exp
        (∑ p ∈ S, harperInverseEulerPrimeExponent p.1 (u p)) := by
      rw [Real.exp_sum]

/-- Product of consecutive inverse blocks evaluated at independently chosen
heights. -/
noncomputable def harperScheduledVaryingInverseEulerProduct
    (y start n : ℕ) (u : Fin n → ℝ)
    (eta : HarperPrimeCube y) : ℝ :=
  ∏ i : Fin n,
    harperInverseEulerBlockProduct y
      (harperScheduledPrimeBlock y (start + (i : ℕ))) (u i) eta

noncomputable def harperScheduledVaryingInverseExponent
    (y start n : ℕ) (u : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ p ∈ harperScheduledPrimeBlock y (start + (i : ℕ)),
    harperInverseEulerPrimeExponent p.1 (u i)

theorem harperScheduledVaryingInverseEulerProduct_eq_rangeFrom
    (y start n : ℕ) (u : Fin n → ℝ) (eta : HarperPrimeCube y) :
    harperScheduledVaryingInverseEulerProduct y start n u eta =
      harperVaryingInverseEulerProduct y
        (harperScheduledPrimeRangeFrom y start n)
        (harperScheduledPrimeHeight y start n u) eta := by
  unfold harperScheduledVaryingInverseEulerProduct
    harperInverseEulerBlockProduct harperVaryingInverseEulerProduct
    harperScheduledPrimeRangeFrom
  rw [Finset.prod_biUnion
    (pairwiseDisjoint_harperScheduledPrimeBlock_add y start n)]
  rw [Finset.prod_range]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro p hp
  rw [harperScheduledPrimeHeight_eq y start n u i hp]

theorem integral_harperScheduledVaryingInverseEulerProduct_le_exp
    (y start n : ℕ) (u : Fin n → ℝ) :
    (∫ eta, harperScheduledVaryingInverseEulerProduct y start n u eta
        ∂harperFairCubeLaw y) ≤
      Real.exp (harperScheduledVaryingInverseExponent y start n u) := by
  have h4 : ∀ p ∈ harperScheduledPrimeRangeFrom y start n, 4 ≤ p.1 := by
    intro p hp
    rw [harperScheduledPrimeRangeFrom] at hp
    simp only [Finset.mem_biUnion, Finset.mem_range] at hp
    obtain ⟨j, hj, hpj⟩ := hp
    exact four_le_prime_of_mem_harperScheduledPrimeBlock hpj
  calc
    (∫ eta, harperScheduledVaryingInverseEulerProduct y start n u eta
        ∂harperFairCubeLaw y) =
        ∫ eta, harperVaryingInverseEulerProduct y
          (harperScheduledPrimeRangeFrom y start n)
          (harperScheduledPrimeHeight y start n u) eta
          ∂harperFairCubeLaw y := by
      apply integral_congr_ae
      exact ae_of_all _ fun eta ↦
        harperScheduledVaryingInverseEulerProduct_eq_rangeFrom
          y start n u eta
    _ ≤ Real.exp
        (∑ p ∈ harperScheduledPrimeRangeFrom y start n,
          harperInverseEulerPrimeExponent p.1
            (harperScheduledPrimeHeight y start n u p)) :=
      integral_harperVaryingInverseEulerProduct_le_exp y
        (harperScheduledPrimeRangeFrom y start n) h4
        (harperScheduledPrimeHeight y start n u)
    _ = Real.exp (harperScheduledVaryingInverseExponent y start n u) := by
      congr 1
      unfold harperScheduledVaryingInverseExponent
        harperScheduledPrimeRangeFrom
      rw [Finset.sum_biUnion
        (pairwiseDisjoint_harperScheduledPrimeBlock_add y start n)]
      rw [Finset.sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro p hp
      rw [harperScheduledPrimeHeight_eq y start n u i hp]

private theorem le_log_one_add_add_sq {x : ℝ} (hx : 0 ≤ x) :
    x ≤ Real.log (1 + x) + x ^ 2 := by
  have hlog := Real.le_log_one_add_of_nonneg hx
  have hden : 0 < x + 2 := by linarith
  have hid : x - 2 * x / (x + 2) = x ^ 2 / (x + 2) := by
    field_simp
    ring
  have hquad : x ≤ 2 * x / (x + 2) + x ^ 2 := by
    have hdiv : x ^ 2 / (x + 2) ≤ x ^ 2 := by
      apply (div_le_iff₀ hden).2
      nlinarith [sq_nonneg x]
    have hdiff : x - 2 * x / (x + 2) ≤ x ^ 2 := hid.trans_le hdiv
    linarith
  apply hquad.trans
  linarith

theorem sum_harperScheduledInverseExponent_le_log_osc_square
    (y j : ℕ) (u : ℝ) :
    (∑ p ∈ harperScheduledPrimeBlock y j,
        harperInverseEulerPrimeExponent p.1 u) ≤
      (∑ p ∈ harperScheduledPrimeBlock y j,
        Real.log (1 + (p.1 : ℝ)⁻¹)) +
      2 * |harperScheduledOscillationMass y j (2 * u)| +
      17 * harperScheduledSquareMass y j := by
  have hmassLog : harperScheduledReciprocalMass y j ≤
      (∑ p ∈ harperScheduledPrimeBlock y j,
        Real.log (1 + (p.1 : ℝ)⁻¹)) +
        harperScheduledSquareMass y j := by
    unfold harperScheduledReciprocalMass harperScheduledSquareMass
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun p _hp ↦
      le_log_one_add_add_sq (by positivity)
  have hosc : harperScheduledOscillationMass y j (2 * u) ≤
      |harperScheduledOscillationMass y j (2 * u)| :=
    le_abs_self _
  have hsquare : 0 ≤ harperScheduledSquareMass y j := by
    unfold harperScheduledSquareMass
    positivity
  rw [sum_harperInverseEulerPrimeExponent_eq]
  change harperScheduledReciprocalMass y j +
      2 * harperScheduledOscillationMass y j (2 * u) +
      16 * harperScheduledSquareMass y j ≤ _
  linarith

theorem harperScheduledVaryingInverseExponent_le_log_osc_square
    (y start n : ℕ) (u : Fin n → ℝ) :
    harperScheduledVaryingInverseExponent y start n u ≤
      (∑ p ∈ harperScheduledPrimeRangeFrom y start n,
        Real.log (1 + (p.1 : ℝ)⁻¹)) +
      2 * (∑ i : Fin n,
        |harperScheduledOscillationMass y (start + (i : ℕ)) (2 * u i)|) +
      17 * (∑ i : Fin n,
        harperScheduledSquareMass y (start + (i : ℕ))) := by
  have hblocks :
      harperScheduledVaryingInverseExponent y start n u ≤
        ∑ i : Fin n,
          ((∑ p ∈ harperScheduledPrimeBlock y (start + (i : ℕ)),
              Real.log (1 + (p.1 : ℝ)⁻¹)) +
            2 * |harperScheduledOscillationMass y
              (start + (i : ℕ)) (2 * u i)| +
            17 * harperScheduledSquareMass y (start + (i : ℕ))) := by
    unfold harperScheduledVaryingInverseExponent
    exact Finset.sum_le_sum fun i _hi ↦
      sum_harperScheduledInverseExponent_le_log_osc_square
        y (start + (i : ℕ)) (u i)
  have hlogs :
      (∑ i : Fin n,
        ∑ p ∈ harperScheduledPrimeBlock y (start + (i : ℕ)),
          Real.log (1 + (p.1 : ℝ)⁻¹)) =
        ∑ p ∈ harperScheduledPrimeRangeFrom y start n,
          Real.log (1 + (p.1 : ℝ)⁻¹) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun k : ℕ ↦ ∑ p ∈ harperScheduledPrimeBlock y (start + k),
        Real.log (1 + (p.1 : ℝ)⁻¹)) n]
    have h := Finset.sum_biUnion
      (f := fun p : HarperPrimeIndex y ↦
        Real.log (1 + (p.1 : ℝ)⁻¹))
      (pairwiseDisjoint_harperScheduledPrimeBlock_add y start n)
    simpa only [harperScheduledPrimeRangeFrom] using! h.symm
  calc
    harperScheduledVaryingInverseExponent y start n u ≤ _ := hblocks
    _ = (∑ i : Fin n,
          ∑ p ∈ harperScheduledPrimeBlock y (start + (i : ℕ)),
            Real.log (1 + (p.1 : ℝ)⁻¹)) +
        2 * (∑ i : Fin n,
          |harperScheduledOscillationMass y (start + (i : ℕ)) (2 * u i)|) +
        17 * (∑ i : Fin n,
          harperScheduledSquareMass y (start + (i : ℕ))) := by
      simp only [Finset.sum_add_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ = _ := by rw [hlogs]

/-- The expectation of the complete varying-height inverse product differs
from the fair Euler first moment by one summable tail, rather than by a
constant per block. -/
theorem exists_harperScheduledVaryingInverseEulerProduct_tail_bound
    (M : ℕ) :
    ∃ c > 0, ∃ C > 0, ∃ J : ℕ,
      ∀ start n y : ℕ, J ≤ start →
        harperBlockEndpoint (start + n) ≤ y →
          ∀ u : Fin n → ℝ,
            (∀ i, 1 ≤ |u i|) → (∀ i, |u i| ≤ M) →
              (∫ eta,
                  harperScheduledVaryingInverseEulerProduct
                    y start n u eta ∂harperFairCubeLaw y) ≤
                Real.exp
                    (2 * harperScheduledErrorTail
                        (harperScheduledOscillationEnvelope M c C) start +
                      17 * harperScheduledErrorTail
                        harperScheduledSquareEnvelope start) *
                  ∏ p ∈ harperScheduledPrimeRangeFrom y start n,
                    (1 + (p.1 : ℝ)⁻¹) := by
  obtain ⟨c, hc, C, hC, J, hcum⟩ :=
    exists_harperScheduledCumulativeErrorBounds M
  refine ⟨c, hc, C, hC, J, ?_⟩
  intro start n y hstart hy u huLower huUpper
  have herr := hcum start n y hstart hy u huLower huUpper
  have hexponent :=
    harperScheduledVaryingInverseExponent_le_log_osc_square
      y start n u
  have hexponentTail :
      harperScheduledVaryingInverseExponent y start n u ≤
        (∑ p ∈ harperScheduledPrimeRangeFrom y start n,
          Real.log (1 + (p.1 : ℝ)⁻¹)) +
          (2 * harperScheduledErrorTail
              (harperScheduledOscillationEnvelope M c C) start +
            17 * harperScheduledErrorTail
              harperScheduledSquareEnvelope start) := by
    calc
      harperScheduledVaryingInverseExponent y start n u ≤
          (∑ p ∈ harperScheduledPrimeRangeFrom y start n,
            Real.log (1 + (p.1 : ℝ)⁻¹)) +
          2 * (∑ i : Fin n,
            |harperScheduledOscillationMass y
              (start + (i : ℕ)) (2 * u i)|) +
          17 * (∑ i : Fin n,
            harperScheduledSquareMass y (start + (i : ℕ))) := hexponent
      _ ≤ (∑ p ∈ harperScheduledPrimeRangeFrom y start n,
            Real.log (1 + (p.1 : ℝ)⁻¹)) +
          (2 * harperScheduledErrorTail
              (harperScheduledOscillationEnvelope M c C) start +
            17 * harperScheduledErrorTail
              harperScheduledSquareEnvelope start) := by
        have hosc := herr.2.1
        have hsquare := herr.2.2
        nlinarith
  have hprodexp :
      Real.exp (∑ p ∈ harperScheduledPrimeRangeFrom y start n,
          Real.log (1 + (p.1 : ℝ)⁻¹)) =
        ∏ p ∈ harperScheduledPrimeRangeFrom y start n,
          (1 + (p.1 : ℝ)⁻¹) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro p _hp
    rw [Real.exp_log]
    positivity
  calc
    (∫ eta,
        harperScheduledVaryingInverseEulerProduct y start n u eta
          ∂harperFairCubeLaw y) ≤
        Real.exp (harperScheduledVaryingInverseExponent y start n u) :=
      integral_harperScheduledVaryingInverseEulerProduct_le_exp
        y start n u
    _ ≤ Real.exp
        ((∑ p ∈ harperScheduledPrimeRangeFrom y start n,
            Real.log (1 + (p.1 : ℝ)⁻¹)) +
          (2 * harperScheduledErrorTail
              (harperScheduledOscillationEnvelope M c C) start +
            17 * harperScheduledErrorTail
              harperScheduledSquareEnvelope start)) :=
      Real.exp_le_exp.mpr hexponentTail
    _ = Real.exp
          (2 * harperScheduledErrorTail
              (harperScheduledOscillationEnvelope M c C) start +
            17 * harperScheduledErrorTail
              harperScheduledSquareEnvelope start) *
        ∏ p ∈ harperScheduledPrimeRangeFrom y start n,
          (1 + (p.1 : ℝ)⁻¹) := by
      rw [Real.exp_add, hprodexp]
      ring

theorem tendsto_harperScheduledInverseEulerPrefactor_one
    (M : ℕ) (c C : ℝ) :
    Tendsto
      (fun start : ℕ ↦
        Real.exp
          (2 * harperScheduledErrorTail
              (harperScheduledOscillationEnvelope M c C) start +
            17 * harperScheduledErrorTail
              harperScheduledSquareEnvelope start))
      atTop (nhds 1) := by
  have hosc := tendsto_harperScheduledErrorTail_zero
    (harperScheduledOscillationEnvelope M c C)
  have hsquare := tendsto_harperScheduledErrorTail_zero
    harperScheduledSquareEnvelope
  have hsum : Tendsto
      (fun start : ℕ ↦
        2 * harperScheduledErrorTail
            (harperScheduledOscillationEnvelope M c C) start +
          17 * harperScheduledErrorTail
            harperScheduledSquareEnvelope start)
      atTop (nhds 0) := by
    convert! (tendsto_const_nhds.mul hosc).add
      (tendsto_const_nhds.mul hsquare) using 1
    all_goals norm_num
  simpa using! (Real.continuous_exp.tendsto 0).comp hsum

/-- A literal path-length-independent constant form of the same bound. -/
theorem exists_harperScheduledVaryingInverseEulerProduct_constant_bound
    (M : ℕ) :
    ∃ K ≥ 0, ∃ J : ℕ,
      ∀ start n y : ℕ, J ≤ start →
        harperBlockEndpoint (start + n) ≤ y →
          ∀ u : Fin n → ℝ,
            (∀ i, 1 ≤ |u i|) → (∀ i, |u i| ≤ M) →
              (∫ eta,
                  harperScheduledVaryingInverseEulerProduct
                    y start n u eta ∂harperFairCubeLaw y) ≤
                Real.exp K *
                  ∏ p ∈ harperScheduledPrimeRangeFrom y start n,
                    (1 + (p.1 : ℝ)⁻¹) := by
  obtain ⟨c, hc, C, hC, J, htail⟩ :=
    exists_harperScheduledVaryingInverseEulerProduct_tail_bound M
  let K : ℝ :=
    2 * (∑' j : ℕ, harperScheduledOscillationEnvelope M c C j) +
      17 * (∑' j : ℕ, harperScheduledSquareEnvelope j)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact add_nonneg
      (mul_nonneg (by norm_num)
        (tsum_nonneg (harperScheduledOscillationEnvelope_nonneg M hC.le)))
      (mul_nonneg (by norm_num)
        (tsum_nonneg harperScheduledSquareEnvelope_nonneg))
  refine ⟨K, hK, J, ?_⟩
  intro start n y hstart hy u huLower huUpper
  have hbase := htail start n y hstart hy u huLower huUpper
  have hoscTail := harperScheduledErrorTail_le_tsum
    (harperScheduledOscillationEnvelope_nonneg M hC.le)
    (summable_harperScheduledOscillationEnvelope M hc hC.le) start
  have hsquareTail := harperScheduledErrorTail_le_tsum
    harperScheduledSquareEnvelope_nonneg
    summable_harperScheduledSquareEnvelope start
  have herror :
      2 * harperScheduledErrorTail
          (harperScheduledOscillationEnvelope M c C) start +
        17 * harperScheduledErrorTail harperScheduledSquareEnvelope start ≤ K := by
    dsimp [K]
    nlinarith
  exact hbase.trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr herror) (by positivity))

/-! ## Dyadic central bands

For the central part of Harper's argument the height is not bounded away
from zero.  On the `d`-th band it has size about `2⁻ᵈ`.  The Abel boundary
term therefore costs `2ᵈ / log Y_j`; shifting the first block by `d` makes
that cost a uniformly summable geometric tail.
-/

noncomputable def harperScheduledDyadicOscillationEnvelope
    (d : ℕ) (c C : ℝ) (j : ℕ) : ℝ :=
  4 * (2 : ℝ) ^ d * invLog (harperBlockEndpoint j) +
    7 * harperScheduledThetaEnvelope c C j

theorem harperScheduledDyadicOscillationEnvelope_nonneg
    (d : ℕ) {c C : ℝ} (hC : 0 ≤ C) (j : ℕ) :
    0 ≤ harperScheduledDyadicOscillationEnvelope d c C j := by
  unfold harperScheduledDyadicOscillationEnvelope
  exact add_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (by positivity))
      (invLog_harperBlockEndpoint_pos j).le)
    (mul_nonneg (by norm_num)
      (harperScheduledThetaEnvelope_nonneg hC j))

theorem summable_harperScheduledDyadicOscillationEnvelope
    (d : ℕ) {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) :
    Summable (harperScheduledDyadicOscillationEnvelope d c C) := by
  exact (summable_invLog_harperBlockEndpoint.mul_left
      (4 * (2 : ℝ) ^ d)).add
    ((summable_harperScheduledThetaEnvelope hc hC).mul_left 7)

theorem invLog_harperBlockEndpoint_succ_le_dyadic
    {d j : ℕ} (hdj : d + 3 ≤ j) :
    invLog (harperBlockEndpoint (j + 1)) ≤
      (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ d := by
  let q : ℝ := 1 / 2
  let a : ℝ := ((16 : ℝ) * Real.log 2)⁻¹
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have ha1 : a ≤ 1 := by
    simpa only [a, invLog_harperBlockEndpoint_eq, pow_zero, mul_one] using!
      invLog_harperBlockEndpoint_le_one 0
  have hq0 : 0 ≤ q := by norm_num [q]
  have hq1 : q ≤ 1 := by norm_num [q]
  have hshift : d + 3 ≤ j + 1 := by omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hshift
  have hpow : q ^ (j + 1) ≤ q ^ (d + 3) := by
    rw [hk, pow_add]
    simpa only [mul_one] using!
      mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1) (pow_nonneg hq0 _)
  rw [invLog_harperBlockEndpoint_eq]
  change a * q ^ (j + 1) ≤ (1 / 8 : ℝ) * q ^ d
  calc
    a * q ^ (j + 1) ≤ 1 * q ^ (j + 1) :=
      mul_le_mul_of_nonneg_right ha1 (pow_nonneg hq0 _)
    _ ≤ q ^ (d + 3) := by simpa using! hpow
    _ = (1 / 8 : ℝ) * q ^ d := by
      rw [show d + 3 = d + 3 by rfl, pow_add]
      norm_num [q]
      ring

/-- Strong-PNT cancellation on a shrinking dyadic band, stable under one
local reciprocal-log mesh displacement. -/
theorem exists_harperScheduledDyadicOscillationBounds :
    ∃ c > 0, ∃ C > 0, ∃ J : ℕ,
      ∀ d j y : ℕ, J + d ≤ j →
        harperBlockEndpoint (j + 1) ≤ y →
          ∀ t u : ℝ,
            (1 / 2 : ℝ) ^ (d + 1) < |t| → |t| ≤ 1 →
              |u - t| *
                  Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤ 1 →
                |harperScheduledOscillationMass y j (2 * u)| ≤
                  harperScheduledDyadicOscillationEnvelope d c C j := by
  obtain ⟨c, hc, C, hC, Jraw, hraw⟩ :=
    exists_mediumPNT_harperScheduledPrimeOscillation_bound
  let J := max Jraw 3
  refine ⟨c, hc, C, hC, J, ?_⟩
  intro d j y hj hy t u htLower htUpper hmesh
  have hjRaw : Jraw ≤ j := by
    have : Jraw ≤ J := le_max_left _ _
    omega
  have hjd : d + 3 ≤ j := by
    have : 3 ≤ J := le_max_right _ _
    omega
  let delta : ℝ := harperScheduledThetaEnvelope c C j
  let ell : ℝ := invLog (harperBlockEndpoint j)
  have hdelta : 0 ≤ delta := by
    dsimp [delta]
    exact harperScheduledThetaEnvelope_nonneg hC.le j
  have hell0 : 0 ≤ ell := (invLog_harperBlockEndpoint_pos j).le
  have hell1 : ell ≤ 1 := invLog_harperBlockEndpoint_le_one j
  have hlogSucc : 0 < Real.log (harperBlockEndpoint (j + 1) : ℝ) :=
    Real.log_pos (by
      exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 16)
        (harperBlockEndpoint_ge_sixteen (j + 1)))
  have hdisp : |u - t| ≤
      invLog (harperBlockEndpoint (j + 1)) := by
    unfold invLog
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hlogSucc).2 (by simpa using! hmesh)
  have hscale := invLog_harperBlockEndpoint_succ_le_dyadic hjd
  have hdispDyadic : |u - t| ≤
      (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ d := hdisp.trans hscale
  have hqpos : 0 < (1 / 2 : ℝ) ^ d := by positivity
  have hreverse := abs_sub_abs_le_abs_sub t u
  rw [abs_sub_comm t u] at hreverse
  have htLower' : (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ d < |t| := by
    rw [pow_succ] at htLower
    simpa [mul_comm] using! htLower
  have huLower : (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ d < |u| := by
    linarith
  have huPos : 0 < |u| := lt_of_lt_of_le (mul_pos (by norm_num) hqpos) huLower.le
  have hquarterInv :
      ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ d)⁻¹ =
        4 * (2 : ℝ) ^ d := by
    rw [one_div_pow]
    field_simp
  have huInv : |u|⁻¹ ≤ 4 * (2 : ℝ) ^ d := by
    calc
      |u|⁻¹ ≤ ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ d)⁻¹ :=
        inv_anti₀ (mul_pos (by norm_num) hqpos) huLower.le
      _ = 4 * (2 : ℝ) ^ d := hquarterInv
  have hboundary : 2 / |2 * u| ≤ 4 * (2 : ℝ) ^ d := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      2 / (2 * |u|) = |u|⁻¹ := by field_simp
      _ ≤ 4 * (2 : ℝ) ^ d := huInv
  have hqle : (1 / 2 : ℝ) ^ d ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have huUpper : |u| ≤ 2 := by
    have hutriangle : |u| ≤ |u - t| + |t| := by
      calc
        |u| = |(u - t) + t| := by ring_nf
        _ ≤ |u - t| + |t| := abs_add_le _ _
    linarith
  have htauUpper : |2 * u| ≤ 4 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have htau : 2 * u ≠ 0 := by
    intro hzero
    have : u = 0 := by linarith
    rw [this, abs_zero] at huPos
    exact lt_irrefl 0 huPos
  have hbase := hraw j hjRaw y hy (2 * u) htau
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
  change |harperScheduledOscillationMass y j (2 * u)| ≤ _
  calc
    |harperScheduledOscillationMass y j (2 * u)| ≤
        (2 / |2 * u| + 2 * delta +
          delta * (1 + |2 * u|) *
            Real.log ((harperBlockEndpoint (j + 1) : ℝ) /
              harperBlockEndpoint j)) * ell := by
      simpa only [harperScheduledOscillationMass, delta, ell,
        harperScheduledThetaEnvelope] using! hbase
    _ = (2 / |2 * u|) * ell + 2 * delta * ell +
        delta * (1 + |2 * u|) *
          (Real.log ((harperBlockEndpoint (j + 1) : ℝ) /
            harperBlockEndpoint j) * ell) := by ring
    _ = (2 / |2 * u|) * ell + 2 * delta * ell +
        delta * (1 + |2 * u|) := by rw [hlogCancel, mul_one]
    _ ≤ (4 * (2 : ℝ) ^ d) * ell + 2 * delta + 5 * delta := by
      have hfirst := mul_le_mul_of_nonneg_right hboundary hell0
      have hsecond : 2 * delta * ell ≤ 2 * delta := by nlinarith
      have hthird : delta * (1 + |2 * u|) ≤ 5 * delta := by
        nlinarith
      linarith
    _ = harperScheduledDyadicOscillationEnvelope d c C j := by
      dsimp [ell, delta, harperScheduledDyadicOscillationEnvelope]
      ring

/-- Frequency-free part of the cumulative arithmetic estimate. -/
theorem exists_harperScheduledCumulativeReciprocalSquareBounds :
    ∃ c > 0, ∃ C > 0, ∃ J : ℕ,
      ∀ start n y : ℕ, J ≤ start →
        harperBlockEndpoint (start + n) ≤ y →
          |(∑ i : Fin n,
              harperScheduledReciprocalMass y (start + (i : ℕ))) -
                (n : ℝ) * Real.log 2| ≤
            harperScheduledErrorTail
              (harperScheduledReciprocalEnvelope c C) start ∧
          (∑ i : Fin n,
              harperScheduledSquareMass y (start + (i : ℕ))) ≤
            harperScheduledErrorTail harperScheduledSquareEnvelope start := by
  obtain ⟨c, hc, C, hC, J, hcum⟩ :=
    exists_harperScheduledCumulativeErrorBounds 1
  refine ⟨c, hc, C, hC, J, ?_⟩
  intro start n y hstart hy
  let u : Fin n → ℝ := fun _ ↦ 1
  have h := hcum start n y hstart hy u
    (fun _ ↦ by simp [u]) (fun _ ↦ by simp [u])
  exact ⟨h.1, h.2.2⟩

/-- Cumulative dyadic-band bounds.  The start shift is `J + d`, while every
right-hand side is a single tail independent of the prefix length `n`. -/
theorem exists_harperScheduledDyadicCumulativeErrorBounds :
    ∃ c₀ > 0, ∃ C₀ > 0, ∃ c > 0, ∃ C > 0, ∃ J : ℕ,
      ∀ d start n y : ℕ, J + d ≤ start →
        harperBlockEndpoint (start + n) ≤ y →
          ∀ t u : Fin n → ℝ,
            (∀ i, (1 / 2 : ℝ) ^ (d + 1) < |t i|) →
            (∀ i, |t i| ≤ 1) →
            (∀ i, |u i - t i| *
              Real.log (harperBlockEndpoint
                (start + (i : ℕ) + 1) : ℝ) ≤ 1) →
              |(∑ i : Fin n,
                  harperScheduledReciprocalMass y (start + (i : ℕ))) -
                    (n : ℝ) * Real.log 2| ≤
                harperScheduledErrorTail
                  (harperScheduledReciprocalEnvelope c₀ C₀) start ∧
              (∑ i : Fin n,
                  |harperScheduledOscillationMass y
                    (start + (i : ℕ)) (2 * u i)|) ≤
                harperScheduledErrorTail
                  (harperScheduledDyadicOscillationEnvelope d c C) start ∧
              (∑ i : Fin n,
                  harperScheduledSquareMass y (start + (i : ℕ))) ≤
                harperScheduledErrorTail harperScheduledSquareEnvelope start := by
  obtain ⟨c₀, hc₀, C₀, hC₀, J₀, hbase⟩ :=
    exists_harperScheduledCumulativeReciprocalSquareBounds
  obtain ⟨c, hc, C, hC, Josc, hosc⟩ :=
    exists_harperScheduledDyadicOscillationBounds
  let J := max J₀ Josc
  refine ⟨c₀, hc₀, C₀, hC₀, c, hc, C, hC, J, ?_⟩
  intro d start n y hstart hy t u htLower htUpper hmesh
  have hstart₀ : J₀ ≤ start := by
    have : J₀ ≤ J := le_max_left _ _
    omega
  have hstartOsc : Josc + d ≤ start := by
    have : Josc ≤ J := le_max_right _ _
    omega
  have hbase' := hbase start n y hstart₀ hy
  have hyi : ∀ i : Fin n,
      harperBlockEndpoint (start + (i : ℕ) + 1) ≤ y := by
    intro i
    have hindex : start + (i : ℕ) + 1 ≤ start + n := by omega
    exact (monotone_harperBlockEndpoint hindex).trans hy
  have hpoint : ∀ i : Fin n,
      |harperScheduledOscillationMass y
        (start + (i : ℕ)) (2 * u i)| ≤
          harperScheduledDyadicOscillationEnvelope d c C
            (start + (i : ℕ)) := by
    intro i
    apply hosc d (start + (i : ℕ)) y (by omega) (hyi i)
      (t i) (u i) (htLower i) (htUpper i)
    exact hmesh i
  refine ⟨hbase'.1, ?_, hbase'.2⟩
  calc
    (∑ i : Fin n,
        |harperScheduledOscillationMass y
          (start + (i : ℕ)) (2 * u i)|) ≤
        ∑ i : Fin n,
          harperScheduledDyadicOscillationEnvelope d c C
            (start + (i : ℕ)) :=
      Finset.sum_le_sum fun i _hi ↦ hpoint i
    _ ≤ harperScheduledErrorTail
        (harperScheduledDyadicOscillationEnvelope d c C) start :=
      sum_fin_le_harperScheduledErrorTail
        (harperScheduledDyadicOscillationEnvelope_nonneg d hC.le)
        (summable_harperScheduledDyadicOscillationEnvelope d hc hC.le)
        start n

/-- Complete inverse-product estimate on the shrinking central band. -/
theorem exists_harperScheduledDyadicVaryingInverseEulerProduct_tail_bound :
    ∃ c > 0, ∃ C > 0, ∃ J : ℕ,
      ∀ d start n y : ℕ, J + d ≤ start →
        harperBlockEndpoint (start + n) ≤ y →
          ∀ t u : Fin n → ℝ,
            (∀ i, (1 / 2 : ℝ) ^ (d + 1) < |t i|) →
            (∀ i, |t i| ≤ 1) →
            (∀ i, |u i - t i| *
              Real.log (harperBlockEndpoint
                (start + (i : ℕ) + 1) : ℝ) ≤ 1) →
              (∫ eta,
                  harperScheduledVaryingInverseEulerProduct
                    y start n u eta ∂harperFairCubeLaw y) ≤
                Real.exp
                    (2 * harperScheduledErrorTail
                        (harperScheduledDyadicOscillationEnvelope d c C) start +
                      17 * harperScheduledErrorTail
                        harperScheduledSquareEnvelope start) *
                  ∏ p ∈ harperScheduledPrimeRangeFrom y start n,
                    (1 + (p.1 : ℝ)⁻¹) := by
  obtain ⟨c₀, hc₀, C₀, hC₀, c, hc, C, hC, J, hcum⟩ :=
    exists_harperScheduledDyadicCumulativeErrorBounds
  refine ⟨c, hc, C, hC, J, ?_⟩
  intro d start n y hstart hy t u htLower htUpper hmesh
  have herr := hcum d start n y hstart hy t u htLower htUpper hmesh
  have hexponent :=
    harperScheduledVaryingInverseExponent_le_log_osc_square
      y start n u
  have hexponentTail :
      harperScheduledVaryingInverseExponent y start n u ≤
        (∑ p ∈ harperScheduledPrimeRangeFrom y start n,
          Real.log (1 + (p.1 : ℝ)⁻¹)) +
          (2 * harperScheduledErrorTail
              (harperScheduledDyadicOscillationEnvelope d c C) start +
            17 * harperScheduledErrorTail
              harperScheduledSquareEnvelope start) := by
    calc
      harperScheduledVaryingInverseExponent y start n u ≤
          (∑ p ∈ harperScheduledPrimeRangeFrom y start n,
            Real.log (1 + (p.1 : ℝ)⁻¹)) +
          2 * (∑ i : Fin n,
            |harperScheduledOscillationMass y
              (start + (i : ℕ)) (2 * u i)|) +
          17 * (∑ i : Fin n,
            harperScheduledSquareMass y (start + (i : ℕ))) := hexponent
      _ ≤ (∑ p ∈ harperScheduledPrimeRangeFrom y start n,
            Real.log (1 + (p.1 : ℝ)⁻¹)) +
          (2 * harperScheduledErrorTail
              (harperScheduledDyadicOscillationEnvelope d c C) start +
            17 * harperScheduledErrorTail
              harperScheduledSquareEnvelope start) := by
        nlinarith [herr.2.1, herr.2.2]
  have hprodexp :
      Real.exp (∑ p ∈ harperScheduledPrimeRangeFrom y start n,
          Real.log (1 + (p.1 : ℝ)⁻¹)) =
        ∏ p ∈ harperScheduledPrimeRangeFrom y start n,
          (1 + (p.1 : ℝ)⁻¹) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro p _hp
    rw [Real.exp_log]
    positivity
  calc
    (∫ eta,
        harperScheduledVaryingInverseEulerProduct y start n u eta
          ∂harperFairCubeLaw y) ≤
        Real.exp (harperScheduledVaryingInverseExponent y start n u) :=
      integral_harperScheduledVaryingInverseEulerProduct_le_exp
        y start n u
    _ ≤ Real.exp
        ((∑ p ∈ harperScheduledPrimeRangeFrom y start n,
            Real.log (1 + (p.1 : ℝ)⁻¹)) +
          (2 * harperScheduledErrorTail
              (harperScheduledDyadicOscillationEnvelope d c C) start +
            17 * harperScheduledErrorTail
              harperScheduledSquareEnvelope start)) :=
      Real.exp_le_exp.mpr hexponentTail
    _ = Real.exp
          (2 * harperScheduledErrorTail
              (harperScheduledDyadicOscillationEnvelope d c C) start +
            17 * harperScheduledErrorTail
              harperScheduledSquareEnvelope start) *
        ∏ p ∈ harperScheduledPrimeRangeFrom y start n,
          (1 + (p.1 : ℝ)⁻¹) := by
      rw [Real.exp_add, hprodexp]
      ring

theorem invLog_harperBlockEndpoint_le_geometric (j : ℕ) :
    invLog (harperBlockEndpoint j) ≤ (1 / 2 : ℝ) ^ j := by
  have ha : ((16 : ℝ) * Real.log 2)⁻¹ ≤ 1 := by
    simpa only [invLog_harperBlockEndpoint_eq, pow_zero, mul_one] using!
      invLog_harperBlockEndpoint_le_one 0
  rw [invLog_harperBlockEndpoint_eq]
  simpa only [one_mul] using! mul_le_mul_of_nonneg_right ha
    (show 0 ≤ (1 / 2 : ℝ) ^ j by positivity)

/-- Explicit `O(2^(d-j))` form of the dyadic Abel boundary term. -/
theorem harperScheduledDyadicBoundary_le_geometric
    {d j : ℕ} (hdj : d ≤ j) :
    4 * (2 : ℝ) ^ d * invLog (harperBlockEndpoint j) ≤
      4 * (1 / 2 : ℝ) ^ (j - d) := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hdj
  have hell := invLog_harperBlockEndpoint_le_geometric j
  have hcancel : (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ d = 1 := by
    rw [one_div_pow]
    field_simp
  calc
    4 * (2 : ℝ) ^ d * invLog (harperBlockEndpoint j) ≤
        4 * (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ j :=
      mul_le_mul_of_nonneg_left hell (by positivity)
    _ = 4 * (1 / 2 : ℝ) ^ r := by
      rw [hr, pow_add]
      calc
        4 * (2 : ℝ) ^ d *
            ((1 / 2 : ℝ) ^ d * (1 / 2 : ℝ) ^ r) =
            4 * ((2 : ℝ) ^ d * (1 / 2 : ℝ) ^ d) *
              (1 / 2 : ℝ) ^ r := by ring
        _ = 4 * (1 / 2 : ℝ) ^ r := by rw [hcancel]; ring
    _ = 4 * (1 / 2 : ℝ) ^ (j - d) := by rw [hr]; simp

/-- After the `d`-block shift, the entire dangerous dyadic boundary tail is
bounded by the universal number `8`. -/
theorem harperScheduledDyadicBoundaryTail_le_eight
    {d start : ℕ} (hds : d ≤ start) :
    harperScheduledErrorTail
        (fun j : ℕ ↦
          4 * (2 : ℝ) ^ d * invLog (harperBlockEndpoint j)) start ≤ 8 := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hds
  have hterm : ∀ k : ℕ,
      4 * (2 : ℝ) ^ d *
          invLog (harperBlockEndpoint (k + start)) ≤
        4 * (1 / 2 : ℝ) ^ k := by
    intro k
    have hell := invLog_harperBlockEndpoint_le_geometric (k + start)
    have hcancel : (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ d = 1 := by
      rw [one_div_pow]
      field_simp
    have hqr : (1 / 2 : ℝ) ^ r ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    calc
      4 * (2 : ℝ) ^ d *
          invLog (harperBlockEndpoint (k + start)) ≤
          4 * (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ (k + start) :=
        mul_le_mul_of_nonneg_left hell (by positivity)
      _ = 4 * (1 / 2 : ℝ) ^ k * (1 / 2 : ℝ) ^ r := by
        rw [hr]
        rw [show k + (d + r) = k + d + r by omega, pow_add, pow_add]
        calc
          4 * (2 : ℝ) ^ d *
              ((1 / 2 : ℝ) ^ k * (1 / 2 : ℝ) ^ d *
                (1 / 2 : ℝ) ^ r) =
              4 * (1 / 2 : ℝ) ^ k *
                ((2 : ℝ) ^ d * (1 / 2 : ℝ) ^ d) *
                  (1 / 2 : ℝ) ^ r := by ring
          _ = 4 * (1 / 2 : ℝ) ^ k * (1 / 2 : ℝ) ^ r := by
            rw [hcancel]
            ring
      _ ≤ 4 * (1 / 2 : ℝ) ^ k * 1 :=
        mul_le_mul_of_nonneg_left hqr (by positivity)
      _ = 4 * (1 / 2 : ℝ) ^ k := by ring
  have hleft : Summable (fun k : ℕ ↦
      4 * (2 : ℝ) ^ d * invLog (harperBlockEndpoint (k + start))) := by
    have hbase := summable_invLog_harperBlockEndpoint.mul_left
      (4 * (2 : ℝ) ^ d)
    exact (summable_nat_add_iff start).2 hbase
  have hright : Summable (fun k : ℕ ↦ 4 * (1 / 2 : ℝ) ^ k) :=
    summable_geometric_two.mul_left 4
  calc
    harperScheduledErrorTail
        (fun j : ℕ ↦
          4 * (2 : ℝ) ^ d * invLog (harperBlockEndpoint j)) start =
        ∑' k : ℕ,
          4 * (2 : ℝ) ^ d * invLog (harperBlockEndpoint (k + start)) := rfl
    _ ≤ ∑' k : ℕ, 4 * (1 / 2 : ℝ) ^ k :=
      hleft.tsum_le_tsum hterm hright
    _ = 8 := by
      rw [summable_geometric_two.tsum_mul_left, tsum_geometric_two]
      norm_num

theorem harperScheduledDyadicOscillationTail_le
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    {d start : ℕ} (hds : d ≤ start) :
    harperScheduledErrorTail
        (harperScheduledDyadicOscillationEnvelope d c C) start ≤
      8 + 7 * (∑' j : ℕ, harperScheduledThetaEnvelope c C j) := by
  let b : ℕ → ℝ := fun j ↦
    4 * (2 : ℝ) ^ d * invLog (harperBlockEndpoint j)
  let delta : ℕ → ℝ := harperScheduledThetaEnvelope c C
  have hb : Summable b := by
    exact summable_invLog_harperBlockEndpoint.mul_left (4 * (2 : ℝ) ^ d)
  have hd : Summable delta := summable_harperScheduledThetaEnvelope hc hC
  have hbShift : Summable (fun k : ℕ ↦ b (k + start)) :=
    (summable_nat_add_iff start).2 hb
  have hdShift : Summable (fun k : ℕ ↦ delta (k + start)) :=
    (summable_nat_add_iff start).2 hd
  have hsplit :
      harperScheduledErrorTail
          (harperScheduledDyadicOscillationEnvelope d c C) start =
        harperScheduledErrorTail b start +
          7 * harperScheduledErrorTail delta start := by
    unfold harperScheduledErrorTail
    rw [show (fun k : ℕ ↦
        harperScheduledDyadicOscillationEnvelope d c C (k + start)) =
      (fun k : ℕ ↦ b (k + start) + 7 * delta (k + start)) by rfl]
    rw [hbShift.tsum_add (hdShift.mul_left 7), hdShift.tsum_mul_left]
  rw [hsplit]
  have hbTail : harperScheduledErrorTail b start ≤ 8 := by
    exact harperScheduledDyadicBoundaryTail_le_eight hds
  have hdTail : harperScheduledErrorTail delta start ≤ ∑' j : ℕ, delta j :=
    harperScheduledErrorTail_le_tsum
      (harperScheduledThetaEnvelope_nonneg hC) hd start
  nlinarith

/-- Uniform in both the dyadic depth and the prefix length. -/
theorem exists_harperScheduledDyadicVaryingInverseEulerProduct_constant_bound :
    ∃ K ≥ 0, ∃ J : ℕ,
      ∀ d start n y : ℕ, J + d ≤ start →
        harperBlockEndpoint (start + n) ≤ y →
          ∀ t u : Fin n → ℝ,
            (∀ i, (1 / 2 : ℝ) ^ (d + 1) < |t i|) →
            (∀ i, |t i| ≤ 1) →
            (∀ i, |u i - t i| *
              Real.log (harperBlockEndpoint
                (start + (i : ℕ) + 1) : ℝ) ≤ 1) →
              (∫ eta,
                  harperScheduledVaryingInverseEulerProduct
                    y start n u eta ∂harperFairCubeLaw y) ≤
                Real.exp K *
                  ∏ p ∈ harperScheduledPrimeRangeFrom y start n,
                    (1 + (p.1 : ℝ)⁻¹) := by
  obtain ⟨c, hc, C, hC, J, htail⟩ :=
    exists_harperScheduledDyadicVaryingInverseEulerProduct_tail_bound
  let K : ℝ :=
    2 * (8 + 7 * (∑' j : ℕ, harperScheduledThetaEnvelope c C j)) +
      17 * (∑' j : ℕ, harperScheduledSquareEnvelope j)
  have hK : 0 ≤ K := by
    dsimp [K]
    have hthetaT : 0 ≤ ∑' j : ℕ, harperScheduledThetaEnvelope c C j :=
      tsum_nonneg (harperScheduledThetaEnvelope_nonneg hC.le)
    have hsquareT : 0 ≤ ∑' j : ℕ, harperScheduledSquareEnvelope j :=
      tsum_nonneg harperScheduledSquareEnvelope_nonneg
    nlinarith
  refine ⟨K, hK, J, ?_⟩
  intro d start n y hstart hy t u htLower htUpper hmesh
  have hbase := htail d start n y hstart hy t u htLower htUpper hmesh
  have hds : d ≤ start := by omega
  have hoscTail := harperScheduledDyadicOscillationTail_le hc hC.le hds
  have hsquareTail := harperScheduledErrorTail_le_tsum
    harperScheduledSquareEnvelope_nonneg
    summable_harperScheduledSquareEnvelope start
  have herror :
      2 * harperScheduledErrorTail
          (harperScheduledDyadicOscillationEnvelope d c C) start +
        17 * harperScheduledErrorTail harperScheduledSquareEnvelope start ≤ K := by
    dsimp [K]
    nlinarith
  exact hbase.trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr herror) (by positivity))

end Problem520
end Erdos
