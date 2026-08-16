import ErdosProblems.Erdos6.LargeOuterMoment
import BoundedGaps.Maynard.MaynardS2CoordinateFiberAbel
import BoundedGaps.Maynard.MaynardS2CoordinateFiberWirsingLogarithmic
import BoundedGaps.Maynard.MaynardS2CoordinateFiberOuterWeight

/-!
# A globally continuous `C¹` extension of the scalar fiber profile

On the nonnegative half-line this is exactly the rational factor occurring in
the large Maynard candidate.  The tangent-line extension on the negative side
makes the endpoint `0` differentiable, which is convenient for Abel summation.
-/

namespace Erdos6.Maynard

open Filter MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

def largeFiberSlope : ℝ := largeA * largeK

def largeFiberProfile (x : ℝ) : ℝ :=
  if x ≤ 0 then 1 - largeFiberSlope * x
  else (1 + largeFiberSlope * max x 0)⁻¹

theorem largeFiberSlope_pos : 0 < largeFiberSlope :=
  mul_pos largeA_pos (by exact_mod_cast largeK_pos)

theorem continuous_largeFiberProfile : Continuous largeFiberProfile := by
  unfold largeFiberProfile
  apply Continuous.if_le
  · fun_prop
  · apply Continuous.inv₀
    · fun_prop
    · intro x
      have hx : 0 ≤ largeFiberSlope * max x 0 :=
        mul_nonneg largeFiberSlope_pos.le (le_max_right _ _)
      linarith
  · exact continuous_id
  · exact continuous_const
  · intro x hx
    subst x
    norm_num

theorem largeFiberProfile_eq_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    largeFiberProfile x = (1 + largeFiberSlope * x)⁻¹ := by
  unfold largeFiberProfile
  by_cases h0 : x = 0
  · subst x
    simp
  · rw [if_neg (not_le.mpr (lt_of_le_of_ne hx (Ne.symm h0)))]
    simp [max_eq_left hx]

theorem largeFiberProfile_eq_largeG {x : ℝ} (hx : 0 ≤ x) :
    largeFiberProfile x = largeG (largeK * x) := by
  rw [largeFiberProfile_eq_of_nonneg hx]
  unfold largeFiberSlope largeG
  congr 2
  ring

theorem largeFiberProfile_zero : largeFiberProfile 0 = 1 := by
  simp [largeFiberProfile]

theorem hasDerivAt_largeFiberProfile_of_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt largeFiberProfile
      (-largeFiberSlope / (1 + largeFiberSlope * x) ^ 2) x := by
  have hden : 1 + largeFiberSlope * x ≠ 0 := by
    have := largeFiberSlope_pos
    nlinarith
  have hraw : HasDerivAt (fun z : ℝ => (1 + largeFiberSlope * z)⁻¹)
      (-largeFiberSlope / (1 + largeFiberSlope * x) ^ 2) x := by
    have hc : HasDerivAt (fun z : ℝ => 1 + largeFiberSlope * z)
        largeFiberSlope x := by
      simpa only [mul_one] using
        ((hasDerivAt_const_mul (x := x) largeFiberSlope).const_add (1 : ℝ))
    exact hc.inv hden
  apply hraw.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with z hz
  rw [largeFiberProfile_eq_of_nonneg hz.le]

theorem hasDerivAt_largeFiberProfile_of_neg {x : ℝ} (hx : x < 0) :
    HasDerivAt largeFiberProfile (-largeFiberSlope) x := by
  have hraw : HasDerivAt (fun z : ℝ => 1 - largeFiberSlope * z)
      (-largeFiberSlope) x := by
    simpa only [mul_one] using
      ((hasDerivAt_const_mul (x := x) largeFiberSlope).const_sub (1 : ℝ))
  apply hraw.congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds hx] with z hz
  simp [largeFiberProfile, hz.le]

theorem slope_largeFiberProfile_zero_of_neg {x : ℝ} (hx : x < 0) :
    slope largeFiberProfile 0 x = -largeFiberSlope := by
  simp [slope, largeFiberProfile_zero, largeFiberProfile, hx.le]
  field_simp [hx.ne]

theorem slope_largeFiberProfile_zero_of_pos {x : ℝ} (hx : 0 < x) :
    slope largeFiberProfile 0 x =
      -largeFiberSlope / (1 + largeFiberSlope * x) := by
  have hslope : slope largeFiberProfile 0 x =
      x⁻¹ * (largeFiberProfile x - largeFiberProfile 0) := by
    simp [slope]
  rw [hslope]
  rw [largeFiberProfile_zero, largeFiberProfile_eq_of_nonneg hx.le]
  have hden : 1 + largeFiberSlope * x ≠ 0 := by
    have := largeFiberSlope_pos
    nlinarith
  have hdiff : (1 + largeFiberSlope * x)⁻¹ - 1 =
      -(largeFiberSlope * x) / (1 + largeFiberSlope * x) := by
    field_simp [hden]
    ring
  rw [hdiff]
  field_simp [hx.ne', hden]

theorem hasDerivAt_largeFiberProfile_zero :
    HasDerivAt largeFiberProfile (-largeFiberSlope) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · exact tendsto_nhdsWithin_congr
      (fun x hx => (slope_largeFiberProfile_zero_of_neg hx).symm)
      tendsto_const_nhds
  · have hlim : Tendsto
        (fun x : ℝ => -largeFiberSlope / (1 + largeFiberSlope * x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (-largeFiberSlope)) := by
      have hcont : ContinuousAt
          (fun x : ℝ => -largeFiberSlope / (1 + largeFiberSlope * x)) 0 := by
        apply ContinuousAt.div₀
        · exact continuousAt_const
        · fun_prop
        · norm_num
      have ht := hcont.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
      simpa only [mul_zero, add_zero, div_one] using ht
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (slope_largeFiberProfile_zero_of_pos hx).symm

theorem hasDerivAt_largeFiberProfile {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt largeFiberProfile
      (-largeFiberSlope / (1 + largeFiberSlope * x) ^ 2) x := by
  rcases hx.eq_or_lt with rfl | hx
  · simpa using hasDerivAt_largeFiberProfile_zero
  · exact hasDerivAt_largeFiberProfile_of_pos hx

theorem deriv_largeFiberProfile {x : ℝ} (hx : 0 ≤ x) :
    deriv largeFiberProfile x =
      -largeFiberSlope / (1 + largeFiberSlope * x) ^ 2 :=
  (hasDerivAt_largeFiberProfile hx).deriv

theorem largeFiberProfile_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ largeFiberProfile x := by
  rw [largeFiberProfile_eq_of_nonneg hx]
  apply inv_nonneg.mpr
  exact add_nonneg zero_le_one
    (mul_nonneg largeFiberSlope_pos.le hx)

theorem largeFiberProfile_le_one {x : ℝ} (hx : 0 ≤ x) :
    largeFiberProfile x ≤ 1 := by
  rw [largeFiberProfile_eq_of_nonneg hx]
  apply inv_le_one_of_one_le₀
  exact le_add_of_nonneg_right
    (mul_nonneg largeFiberSlope_pos.le hx)

def largeFiberCompositeDeriv (R : ℕ) (t : ℝ) : ℝ :=
  (-largeFiberSlope /
      (1 + largeFiberSlope * (Real.log t / Real.log R)) ^ 2) *
    (t⁻¹ / Real.log R)

theorem hasDerivAt_largeFiberProfile_comp_log
    {R : ℕ} {t : ℝ} (hR : 1 < R) (ht : 1 ≤ t) :
    HasDerivAt
      (largeFiberProfile ∘ (fun z : ℝ => Real.log z / Real.log R))
      (largeFiberCompositeDeriv R t) t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hlogR : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hx : 0 ≤ Real.log t / Real.log R :=
    div_nonneg (Real.log_nonneg ht) hlogR.le
  have hp := (hasDerivAt_largeFiberProfile hx).comp t
    ((Real.hasDerivAt_log ht0.ne').div_const (Real.log R))
  unfold largeFiberCompositeDeriv
  exact hp

theorem deriv_largeFiberProfile_comp_log
    {R : ℕ} {t : ℝ} (hR : 1 < R) (ht : 1 ≤ t) :
    deriv (fun z : ℝ => largeFiberProfile
      (Real.log z / Real.log R)) t = largeFiberCompositeDeriv R t :=
  (hasDerivAt_largeFiberProfile_comp_log hR ht).deriv

theorem largeFiberCompositeDeriv_nonpos
    {R : ℕ} {t : ℝ} (hR : 1 < R) (ht : 1 ≤ t) :
    largeFiberCompositeDeriv R t ≤ 0 := by
  unfold largeFiberCompositeDeriv
  apply mul_nonpos_of_nonpos_of_nonneg
  · apply div_nonpos_of_nonpos_of_nonneg
    · exact neg_nonpos.mpr largeFiberSlope_pos.le
    · exact sq_nonneg _
  · exact div_nonneg (inv_nonneg.mpr (zero_le_one.trans ht))
      (Real.log_pos (by exact_mod_cast hR)).le

theorem continuousOn_largeFiberCompositeDeriv
    {R : ℕ} (hR : 1 < R) {Q : ℕ} :
    ContinuousOn (largeFiberCompositeDeriv R)
      (Set.Icc (1 : ℝ) Q) := by
  have hlogR : Real.log (R : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hR)).ne'
  unfold largeFiberCompositeDeriv
  have hlog : ContinuousOn (fun t : ℝ => Real.log t / Real.log R)
      (Set.Icc (1 : ℝ) Q) :=
    (continuousOn_id.log (fun t ht =>
      (zero_lt_one.trans_le ht.1).ne')).div_const _
  have hden : ContinuousOn (fun t : ℝ =>
      (1 + largeFiberSlope * (Real.log t / Real.log R)) ^ 2)
      (Set.Icc (1 : ℝ) Q) :=
    (continuousOn_const.add (continuousOn_const.mul hlog)).pow 2
  have hfrac : ContinuousOn (fun t : ℝ =>
      -largeFiberSlope /
        (1 + largeFiberSlope * (Real.log t / Real.log R)) ^ 2)
      (Set.Icc (1 : ℝ) Q) := by
    apply continuousOn_const.div hden
    intro t ht
    have hx : 0 ≤ Real.log t / Real.log R :=
      div_nonneg (Real.log_nonneg ht.1)
        (Real.log_pos (by exact_mod_cast hR)).le
    have hbase : 0 < 1 + largeFiberSlope *
        (Real.log t / Real.log R) := by
      nlinarith [largeFiberSlope_pos]
    exact pow_ne_zero 2 hbase.ne'
  have hinv : ContinuousOn (fun t : ℝ => t⁻¹ / Real.log R)
      (Set.Icc (1 : ℝ) Q) := by
    apply (continuousOn_id.inv₀ (fun t ht =>
      (zero_lt_one.trans_le ht.1).ne')).div_const
  exact hfrac.mul hinv

theorem intervalIntegrable_largeFiberCompositeDeriv
    {R Q : ℕ} (hR : 1 < R) (hQ : 1 ≤ Q) :
    IntervalIntegrable (largeFiberCompositeDeriv R) volume 1 Q :=
  by
    have hc : ContinuousOn (largeFiberCompositeDeriv R)
        (Set.uIcc (1 : ℝ) Q) := by
      rw [Set.uIcc_of_le (by exact_mod_cast hQ)]
      exact continuousOn_largeFiberCompositeDeriv hR
    exact hc.intervalIntegrable

theorem intervalIntegrable_deriv_largeFiber_comp_log
    {R Q : ℕ} (hR : 1 < R) (hQ : 1 ≤ Q) :
    IntervalIntegrable
      (deriv (fun z : ℝ => largeFiberProfile
        (Real.log z / Real.log R))) volume 1 Q := by
  have hQreal : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hc := intervalIntegrable_largeFiberCompositeDeriv hR hQ
  exact hc.congr fun t ht => by
    have ht' := Set.uIoc_subset_uIcc ht
    rw [Set.uIcc_of_le hQreal] at ht'
    exact (deriv_largeFiberProfile_comp_log hR ht'.1).symm

theorem integrableOn_deriv_largeFiber_comp_log_Icc
    {R Q : ℕ} (hR : 1 < R) :
    IntegrableOn
      (deriv (fun z : ℝ => largeFiberProfile (Real.log z / Real.log R)))
      (Set.Icc (1 : ℝ) Q) := by
  have heq : ∀ t ∈ Set.Icc (1 : ℝ) Q,
      deriv (fun z : ℝ => largeFiberProfile (Real.log z / Real.log R)) t =
        largeFiberCompositeDeriv R t := by
    intro t ht
    exact deriv_largeFiberProfile_comp_log hR ht.1
  exact ((continuousOn_largeFiberCompositeDeriv hR).integrableOn_Icc).congr
    (ae_restrict_mem measurableSet_Icc |>.mono fun t ht => (heq t ht).symm)

theorem integrableOn_abs_deriv_largeFiber_comp_log_Ioc
    {R Q : ℕ} (hR : 1 < R) :
    IntegrableOn
      (fun t => |deriv (fun z : ℝ => largeFiberProfile
        (Real.log z / Real.log R)) t|)
      (Set.Ioc (1 : ℝ) Q) := by
  have h : IntegrableOn
      (fun t => |deriv (fun z : ℝ => largeFiberProfile
        (Real.log z / Real.log R)) t|)
      (Set.Icc (1 : ℝ) Q) :=
    (integrableOn_deriv_largeFiber_comp_log_Icc (Q := Q) hR).abs
  exact h.mono_set Set.Ioc_subset_Icc_self

theorem integrableOn_deriv_mul_log_largeFiber_comp_log
    (S : ℝ) {R Q : ℕ} (hR : 1 < R) :
    IntegrableOn
      (fun t => deriv (fun z : ℝ => largeFiberProfile
          (Real.log z / Real.log R)) t * (S * Real.log t))
      (Set.Ioc (1 : ℝ) Q) := by
  have hcont : ContinuousOn
      (fun t : ℝ => largeFiberCompositeDeriv R t *
        (S * Real.log t)) (Set.Icc (1 : ℝ) Q) :=
    (continuousOn_largeFiberCompositeDeriv hR).mul
      (continuousOn_const.mul
        (continuousOn_id.log (fun t ht =>
          (zero_lt_one.trans_le ht.1).ne')))
  have hint : IntegrableOn
      (fun t : ℝ => largeFiberCompositeDeriv R t *
        (S * Real.log t)) (Set.Ioc (1 : ℝ) Q) :=
    (hcont.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  apply hint.congr
  exact (ae_restrict_mem measurableSet_Ioc).mono fun t ht => by
    change largeFiberCompositeDeriv R t * (S * Real.log t) =
      deriv (fun z : ℝ => largeFiberProfile
        (Real.log z / Real.log R)) t * (S * Real.log t)
    rw [deriv_largeFiberProfile_comp_log hR ht.1.le]

theorem integral_abs_deriv_largeFiber_comp_log_le_one
    {R Q : ℕ} (hR : 1 < R) (hQ : 1 ≤ Q) :
    (∫ t in Set.Ioc (1 : ℝ) Q,
      |deriv (fun z : ℝ => largeFiberProfile
        (Real.log z / Real.log R)) t|) ≤ 1 := by
  let f : ℝ → ℝ := fun z =>
    largeFiberProfile (Real.log z / Real.log R)
  have hQreal : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hdiff : ∀ t ∈ Set.uIcc (1 : ℝ) Q,
      DifferentiableAt ℝ f t := by
    intro t ht
    rw [Set.uIcc_of_le hQreal] at ht
    exact (hasDerivAt_largeFiberProfile_comp_log hR ht.1).differentiableAt
  have hint : IntervalIntegrable (deriv f) volume 1 Q :=
    intervalIntegrable_deriv_largeFiber_comp_log hR hQ
  have hfund : (∫ t in (1 : ℝ)..Q, deriv f t) = f Q - f 1 :=
    intervalIntegral.integral_deriv_eq_sub hdiff hint
  rw [← intervalIntegral.integral_of_le hQreal]
  calc
    (∫ t in (1 : ℝ)..Q, |deriv f t|) =
        ∫ t in (1 : ℝ)..Q, -deriv f t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hQreal] at ht
      change |deriv f t| = -deriv f t
      rw [abs_of_nonpos]
      rw [deriv_largeFiberProfile_comp_log hR ht.1]
      exact largeFiberCompositeDeriv_nonpos hR ht.1
    _ = -(f Q - f 1) := by
      rw [intervalIntegral.integral_neg, hfund]
    _ = 1 - largeFiberProfile (Real.log Q / Real.log R) := by
      simp [f, largeFiberProfile_zero]
    _ ≤ 1 := by
      apply sub_le_self
      apply largeFiberProfile_nonneg
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hQ))
        (Real.log_pos (by exact_mod_cast hR)).le

end

end Erdos6.Maynard
