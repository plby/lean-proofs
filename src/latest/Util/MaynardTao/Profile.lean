/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos48.External.Erdos4.Base
import BoundedGaps.Maynard.MaynardS2CoordinateFiberAbel
import BoundedGaps.Maynard.MaynardS2CoordinateFiberWirsingLogarithmic

/-!
# A parameterized inverse-affine fiber profile

The fixed large-tuple development uses the same profile with one frozen
slope.  For Maynard--Tao the slope is `A * K`, so we keep the elementary
calculus argument parameterized.
-/

namespace MaynardTao

open Filter MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

def inverseAffineProfile (lam x : ℝ) : ℝ :=
  if x ≤ 0 then 1 - lam * x
  else (1 + lam * max x 0)⁻¹

theorem continuous_inverseAffineProfile {lam : ℝ} (hlam : 0 < lam) :
    Continuous (inverseAffineProfile lam) := by
  unfold inverseAffineProfile
  apply Continuous.if_le
  · fun_prop
  · apply Continuous.inv₀
    · fun_prop
    · intro x
      have hx : 0 ≤ lam * max x 0 :=
        mul_nonneg hlam.le (le_max_right _ _)
      linarith
  · exact continuous_id
  · exact continuous_const
  · intro x hx
    subst x
    norm_num

theorem inverseAffineProfile_eq_of_nonneg {lam x : ℝ} (hx : 0 ≤ x) :
    inverseAffineProfile lam x = (1 + lam * x)⁻¹ := by
  unfold inverseAffineProfile
  by_cases h0 : x = 0
  · subst x
    simp
  · rw [if_neg (not_le.mpr (lt_of_le_of_ne hx (Ne.symm h0)))]
    simp [max_eq_left hx]

theorem inverseAffineProfile_eq_factor {K : ℕ} {A x : ℝ}
    (hx : 0 ≤ x) :
    inverseAffineProfile (A * (K : ℝ)) x =
      Erdos4.VariableMaynard.factor A ((K : ℝ) * x) := by
  rw [inverseAffineProfile_eq_of_nonneg hx]
  unfold Erdos4.VariableMaynard.factor
  congr 2
  ring

theorem inverseAffineProfile_zero (lam : ℝ) :
    inverseAffineProfile lam 0 = 1 := by
  simp [inverseAffineProfile]

theorem hasDerivAt_inverseAffineProfile_of_pos {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) :
    HasDerivAt (inverseAffineProfile lam)
      (-lam / (1 + lam * x) ^ 2) x := by
  have hden : 1 + lam * x ≠ 0 := by
    nlinarith
  have hraw : HasDerivAt (fun z : ℝ => (1 + lam * z)⁻¹)
      (-lam / (1 + lam * x) ^ 2) x := by
    have hc : HasDerivAt (fun z : ℝ => 1 + lam * z) lam x := by
      simpa only [mul_one] using
        ((hasDerivAt_const_mul (x := x) lam).const_add (1 : ℝ))
    exact hc.inv hden
  apply hraw.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with z hz
  rw [inverseAffineProfile_eq_of_nonneg hz.le]

theorem hasDerivAt_inverseAffineProfile_of_neg {lam x : ℝ}
    (hx : x < 0) :
    HasDerivAt (inverseAffineProfile lam) (-lam) x := by
  have hraw : HasDerivAt (fun z : ℝ => 1 - lam * z) (-lam) x := by
    simpa only [mul_one] using
      ((hasDerivAt_const_mul (x := x) lam).const_sub (1 : ℝ))
  apply hraw.congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds hx] with z hz
  simp [inverseAffineProfile, hz.le]

theorem slope_inverseAffineProfile_zero_of_neg {lam x : ℝ} (hx : x < 0) :
    slope (inverseAffineProfile lam) 0 x = -lam := by
  simp [slope, inverseAffineProfile_zero, inverseAffineProfile, hx.le]
  field_simp [hx.ne]

theorem slope_inverseAffineProfile_zero_of_pos {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) :
    slope (inverseAffineProfile lam) 0 x =
      -lam / (1 + lam * x) := by
  have hslope : slope (inverseAffineProfile lam) 0 x =
      x⁻¹ * (inverseAffineProfile lam x - inverseAffineProfile lam 0) := by
    simp [slope]
  rw [hslope, inverseAffineProfile_zero,
    inverseAffineProfile_eq_of_nonneg hx.le]
  have hden : 1 + lam * x ≠ 0 := by
    nlinarith
  have hdiff : (1 + lam * x)⁻¹ - 1 =
      -(lam * x) / (1 + lam * x) := by
    field_simp [hden]
    ring
  rw [hdiff]
  field_simp [hx.ne', hden]

theorem hasDerivAt_inverseAffineProfile_zero {lam : ℝ} (hlam : 0 < lam) :
    HasDerivAt (inverseAffineProfile lam) (-lam) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · exact tendsto_nhdsWithin_congr
      (fun x hx => (slope_inverseAffineProfile_zero_of_neg hx).symm)
      tendsto_const_nhds
  · have hlim : Tendsto
        (fun x : ℝ => -lam / (1 + lam * x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (-lam)) := by
      have hcont : ContinuousAt
          (fun x : ℝ => -lam / (1 + lam * x)) 0 := by
        apply ContinuousAt.div₀
        · exact continuousAt_const
        · fun_prop
        · norm_num
      have ht := hcont.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
      simpa only [mul_zero, add_zero, div_one] using ht
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (slope_inverseAffineProfile_zero_of_pos hlam hx).symm

theorem hasDerivAt_inverseAffineProfile {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 ≤ x) :
    HasDerivAt (inverseAffineProfile lam)
      (-lam / (1 + lam * x) ^ 2) x := by
  rcases hx.eq_or_lt with rfl | hx
  · simpa using hasDerivAt_inverseAffineProfile_zero hlam
  · exact hasDerivAt_inverseAffineProfile_of_pos hlam hx

theorem deriv_inverseAffineProfile {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 ≤ x) :
    deriv (inverseAffineProfile lam) x =
      -lam / (1 + lam * x) ^ 2 :=
  (hasDerivAt_inverseAffineProfile hlam hx).deriv

theorem inverseAffineProfile_nonneg {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 ≤ x) :
    0 ≤ inverseAffineProfile lam x := by
  rw [inverseAffineProfile_eq_of_nonneg hx]
  apply inv_nonneg.mpr
  exact add_nonneg zero_le_one (mul_nonneg hlam.le hx)

theorem inverseAffineProfile_le_one {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 ≤ x) :
    inverseAffineProfile lam x ≤ 1 := by
  rw [inverseAffineProfile_eq_of_nonneg hx]
  apply inv_le_one_of_one_le₀
  exact le_add_of_nonneg_right (mul_nonneg hlam.le hx)

def inverseAffineCompositeDeriv (lam : ℝ) (R : ℕ) (t : ℝ) : ℝ :=
  (-lam / (1 + lam * (Real.log t / Real.log R)) ^ 2) *
    (t⁻¹ / Real.log R)

theorem hasDerivAt_inverseAffineProfile_comp_log
    {lam : ℝ} (hlam : 0 < lam)
    {R : ℕ} {t : ℝ} (hR : 1 < R) (ht : 1 ≤ t) :
    HasDerivAt
      (inverseAffineProfile lam ∘
        (fun z : ℝ => Real.log z / Real.log R))
      (inverseAffineCompositeDeriv lam R t) t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hlogR : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hx : 0 ≤ Real.log t / Real.log R :=
    div_nonneg (Real.log_nonneg ht) hlogR.le
  have hp := (hasDerivAt_inverseAffineProfile hlam hx).comp t
    ((Real.hasDerivAt_log ht0.ne').div_const (Real.log R))
  unfold inverseAffineCompositeDeriv
  exact hp

theorem deriv_inverseAffineProfile_comp_log
    {lam : ℝ} (hlam : 0 < lam)
    {R : ℕ} {t : ℝ} (hR : 1 < R) (ht : 1 ≤ t) :
    deriv (fun z : ℝ => inverseAffineProfile lam
      (Real.log z / Real.log R)) t =
      inverseAffineCompositeDeriv lam R t :=
  (hasDerivAt_inverseAffineProfile_comp_log hlam hR ht).deriv

theorem inverseAffineCompositeDeriv_nonpos
    {lam : ℝ} (hlam : 0 < lam)
    {R : ℕ} {t : ℝ} (hR : 1 < R) (ht : 1 ≤ t) :
    inverseAffineCompositeDeriv lam R t ≤ 0 := by
  unfold inverseAffineCompositeDeriv
  apply mul_nonpos_of_nonpos_of_nonneg
  · apply div_nonpos_of_nonpos_of_nonneg
    · exact neg_nonpos.mpr hlam.le
    · exact sq_nonneg _
  · exact div_nonneg (inv_nonneg.mpr (zero_le_one.trans ht))
      (Real.log_pos (by exact_mod_cast hR)).le

theorem continuousOn_inverseAffineCompositeDeriv
    {lam : ℝ} (hlam : 0 < lam)
    {R : ℕ} (hR : 1 < R) {Q : ℕ} :
    ContinuousOn (inverseAffineCompositeDeriv lam R)
      (Set.Icc (1 : ℝ) Q) := by
  have hlogR : Real.log (R : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hR)).ne'
  unfold inverseAffineCompositeDeriv
  have hlog : ContinuousOn (fun t : ℝ => Real.log t / Real.log R)
      (Set.Icc (1 : ℝ) Q) :=
    (continuousOn_id.log (fun t ht =>
      (zero_lt_one.trans_le ht.1).ne')).div_const _
  have hden : ContinuousOn (fun t : ℝ =>
      (1 + lam * (Real.log t / Real.log R)) ^ 2)
      (Set.Icc (1 : ℝ) Q) :=
    (continuousOn_const.add (continuousOn_const.mul hlog)).pow 2
  have hfrac : ContinuousOn (fun t : ℝ =>
      -lam / (1 + lam * (Real.log t / Real.log R)) ^ 2)
      (Set.Icc (1 : ℝ) Q) := by
    apply continuousOn_const.div hden
    intro t ht
    have hx : 0 ≤ Real.log t / Real.log R :=
      div_nonneg (Real.log_nonneg ht.1)
        (Real.log_pos (by exact_mod_cast hR)).le
    have hbase : 0 < 1 + lam * (Real.log t / Real.log R) := by
      nlinarith
    exact pow_ne_zero 2 hbase.ne'
  have hinv : ContinuousOn (fun t : ℝ => t⁻¹ / Real.log R)
      (Set.Icc (1 : ℝ) Q) := by
    apply (continuousOn_id.inv₀ (fun t ht =>
      (zero_lt_one.trans_le ht.1).ne')).div_const
  exact hfrac.mul hinv

theorem intervalIntegrable_inverseAffineCompositeDeriv
    {lam : ℝ} (hlam : 0 < lam)
    {R Q : ℕ} (hR : 1 < R) (hQ : 1 ≤ Q) :
    IntervalIntegrable (inverseAffineCompositeDeriv lam R) volume 1 Q := by
  have hc : ContinuousOn (inverseAffineCompositeDeriv lam R)
      (Set.uIcc (1 : ℝ) Q) := by
    rw [Set.uIcc_of_le (by exact_mod_cast hQ)]
    exact continuousOn_inverseAffineCompositeDeriv hlam hR
  exact hc.intervalIntegrable

theorem intervalIntegrable_deriv_inverseAffine_comp_log
    {lam : ℝ} (hlam : 0 < lam)
    {R Q : ℕ} (hR : 1 < R) (hQ : 1 ≤ Q) :
    IntervalIntegrable
      (deriv (fun z : ℝ => inverseAffineProfile lam
        (Real.log z / Real.log R))) volume 1 Q := by
  have hQreal : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hc := intervalIntegrable_inverseAffineCompositeDeriv hlam hR hQ
  exact hc.congr fun t ht => by
    have ht' := Set.uIoc_subset_uIcc ht
    rw [Set.uIcc_of_le hQreal] at ht'
    exact (deriv_inverseAffineProfile_comp_log hlam hR ht'.1).symm

theorem integrableOn_deriv_inverseAffine_comp_log_Icc
    {lam : ℝ} (hlam : 0 < lam)
    {R Q : ℕ} (hR : 1 < R) :
    IntegrableOn
      (deriv (fun z : ℝ => inverseAffineProfile lam
        (Real.log z / Real.log R)))
      (Set.Icc (1 : ℝ) Q) := by
  have heq : ∀ t ∈ Set.Icc (1 : ℝ) Q,
      deriv (fun z : ℝ => inverseAffineProfile lam
          (Real.log z / Real.log R)) t =
        inverseAffineCompositeDeriv lam R t := by
    intro t ht
    exact deriv_inverseAffineProfile_comp_log hlam hR ht.1
  exact ((continuousOn_inverseAffineCompositeDeriv hlam hR).integrableOn_Icc).congr
    (ae_restrict_mem measurableSet_Icc |>.mono fun t ht => (heq t ht).symm)

theorem integrableOn_abs_deriv_inverseAffine_comp_log_Ioc
    {lam : ℝ} (hlam : 0 < lam)
    {R Q : ℕ} (hR : 1 < R) :
    IntegrableOn
      (fun t => |deriv (fun z : ℝ => inverseAffineProfile lam
        (Real.log z / Real.log R)) t|)
      (Set.Ioc (1 : ℝ) Q) := by
  have h : IntegrableOn
      (fun t => |deriv (fun z : ℝ => inverseAffineProfile lam
        (Real.log z / Real.log R)) t|)
      (Set.Icc (1 : ℝ) Q) :=
    (integrableOn_deriv_inverseAffine_comp_log_Icc hlam (Q := Q) hR).abs
  exact h.mono_set Set.Ioc_subset_Icc_self

theorem integrableOn_deriv_mul_log_inverseAffine_comp_log
    (S : ℝ) {lam : ℝ} (hlam : 0 < lam)
    {R Q : ℕ} (hR : 1 < R) :
    IntegrableOn
      (fun t => deriv (fun z : ℝ => inverseAffineProfile lam
          (Real.log z / Real.log R)) t * (S * Real.log t))
      (Set.Ioc (1 : ℝ) Q) := by
  have hcont : ContinuousOn
      (fun t : ℝ => inverseAffineCompositeDeriv lam R t *
        (S * Real.log t)) (Set.Icc (1 : ℝ) Q) :=
    (continuousOn_inverseAffineCompositeDeriv hlam hR).mul
      (continuousOn_const.mul
        (continuousOn_id.log (fun t ht =>
          (zero_lt_one.trans_le ht.1).ne')))
  have hint : IntegrableOn
      (fun t : ℝ => inverseAffineCompositeDeriv lam R t *
        (S * Real.log t)) (Set.Ioc (1 : ℝ) Q) :=
    (hcont.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  apply hint.congr
  exact (ae_restrict_mem measurableSet_Ioc).mono fun t ht => by
    change inverseAffineCompositeDeriv lam R t * (S * Real.log t) =
      deriv (fun z : ℝ => inverseAffineProfile lam
        (Real.log z / Real.log R)) t * (S * Real.log t)
    rw [deriv_inverseAffineProfile_comp_log hlam hR ht.1.le]

theorem integral_abs_deriv_inverseAffine_comp_log_le_one
    {lam : ℝ} (hlam : 0 < lam)
    {R Q : ℕ} (hR : 1 < R) (hQ : 1 ≤ Q) :
    (∫ t in Set.Ioc (1 : ℝ) Q,
      |deriv (fun z : ℝ => inverseAffineProfile lam
        (Real.log z / Real.log R)) t|) ≤ 1 := by
  let f : ℝ → ℝ := fun z =>
    inverseAffineProfile lam (Real.log z / Real.log R)
  have hQreal : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hdiff : ∀ t ∈ Set.uIcc (1 : ℝ) Q,
      DifferentiableAt ℝ f t := by
    intro t ht
    rw [Set.uIcc_of_le hQreal] at ht
    exact (hasDerivAt_inverseAffineProfile_comp_log hlam hR ht.1).differentiableAt
  have hint : IntervalIntegrable (deriv f) volume 1 Q :=
    intervalIntegrable_deriv_inverseAffine_comp_log hlam hR hQ
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
      rw [deriv_inverseAffineProfile_comp_log hlam hR ht.1]
      exact inverseAffineCompositeDeriv_nonpos hlam hR ht.1
    _ = -(f Q - f 1) := by
      rw [intervalIntegral.integral_neg, hfund]
    _ = 1 - inverseAffineProfile lam (Real.log Q / Real.log R) := by
      simp [f, inverseAffineProfile_zero]
    _ ≤ 1 := by
      apply sub_le_self
      apply inverseAffineProfile_nonneg hlam
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hQ))
        (Real.log_pos (by exact_mod_cast hR)).le

end

end MaynardTao
