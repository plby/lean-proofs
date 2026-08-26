import ErdosProblems.Erdos4b.Base

namespace Erdos4b

open Filter MeasureTheory Set
open scoped ArithmeticFunction.Moebius BigOperators Interval

noncomputable section

/-! A parameterized version of the scalar profile used in the coordinate
fiber.  The tangent continuation to the negative half-line is only there to
make the profile globally continuous and differentiable at zero; all divisor
arguments lie on the nonnegative half-line. -/

def variableFiberProfile (s x : ℝ) : ℝ :=
  if x ≤ 0 then 1 - s * x else (1 + s * max x 0)⁻¹

theorem continuous_variableFiberProfile {s : ℝ} (hs : 0 < s) :
    Continuous (variableFiberProfile s) := by
  unfold variableFiberProfile
  apply Continuous.if_le
  · fun_prop
  · apply Continuous.inv₀
    · fun_prop
    · intro x
      have hx : 0 ≤ s * max x 0 :=
        mul_nonneg hs.le (le_max_right _ _)
      linarith
  · exact continuous_id
  · exact continuous_const
  · intro x hx
    subst x
    norm_num

theorem variableFiberProfile_eq_of_nonneg {s x : ℝ} (hx : 0 ≤ x) :
    variableFiberProfile s x = (1 + s * x)⁻¹ := by
  unfold variableFiberProfile
  by_cases h0 : x = 0
  · subst x
    simp
  · rw [if_neg (not_le.mpr (lt_of_le_of_ne hx (Ne.symm h0)))]
    simp [max_eq_left hx]

@[simp] theorem variableFiberProfile_zero (s : ℝ) :
    variableFiberProfile s 0 = 1 := by
  simp [variableFiberProfile]

theorem hasDerivAt_variableFiberProfile_of_pos {s x : ℝ}
    (hs : 0 < s) (hx : 0 < x) :
    HasDerivAt (variableFiberProfile s)
      (-s / (1 + s * x) ^ 2) x := by
  have hden : 1 + s * x ≠ 0 := by nlinarith
  have hraw : HasDerivAt (fun z : ℝ => (1 + s * z)⁻¹)
      (-s / (1 + s * x) ^ 2) x := by
    have hc : HasDerivAt (fun z : ℝ => 1 + s * z) s x := by
      simpa only [mul_one] using
        ((hasDerivAt_const_mul (x := x) s).const_add (1 : ℝ))
    exact hc.inv hden
  apply hraw.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with z hz
  rw [variableFiberProfile_eq_of_nonneg hz.le]

theorem hasDerivAt_variableFiberProfile_of_neg {s x : ℝ}
    (hx : x < 0) :
    HasDerivAt (variableFiberProfile s) (-s) x := by
  have hraw : HasDerivAt (fun z : ℝ => 1 - s * z) (-s) x := by
    simpa only [mul_one] using
      ((hasDerivAt_const_mul (x := x) s).const_sub (1 : ℝ))
  apply hraw.congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds hx] with z hz
  simp [variableFiberProfile, hz.le]

theorem slope_variableFiberProfile_zero_of_neg {s x : ℝ} (hx : x < 0) :
    slope (variableFiberProfile s) 0 x = -s := by
  simp [slope, variableFiberProfile, hx.le]
  field_simp [hx.ne]

theorem slope_variableFiberProfile_zero_of_pos {s x : ℝ}
    (hs : 0 < s) (hx : 0 < x) :
    slope (variableFiberProfile s) 0 x = -s / (1 + s * x) := by
  have hslope : slope (variableFiberProfile s) 0 x =
      x⁻¹ * (variableFiberProfile s x - variableFiberProfile s 0) := by
    simp [slope]
  rw [hslope, variableFiberProfile_zero,
    variableFiberProfile_eq_of_nonneg hx.le]
  have hden : 1 + s * x ≠ 0 := by nlinarith
  have hdiff : (1 + s * x)⁻¹ - 1 = -(s * x) / (1 + s * x) := by
    field_simp [hden]
    ring
  rw [hdiff]
  field_simp [hx.ne', hden]

theorem hasDerivAt_variableFiberProfile_zero {s : ℝ} (hs : 0 < s) :
    HasDerivAt (variableFiberProfile s) (-s) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · exact tendsto_nhdsWithin_congr
      (fun x hx => (slope_variableFiberProfile_zero_of_neg hx).symm)
      tendsto_const_nhds
  · have hlim : Tendsto (fun x : ℝ => -s / (1 + s * x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (-s)) := by
      have hcont : ContinuousAt (fun x : ℝ => -s / (1 + s * x)) 0 := by
        apply ContinuousAt.div₀
        · exact continuousAt_const
        · fun_prop
        · norm_num
      have ht := hcont.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
      simpa only [mul_zero, add_zero, div_one] using ht
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (slope_variableFiberProfile_zero_of_pos hs hx).symm

theorem hasDerivAt_variableFiberProfile {s x : ℝ}
    (hs : 0 < s) (hx : 0 ≤ x) :
    HasDerivAt (variableFiberProfile s)
      (-s / (1 + s * x) ^ 2) x := by
  rcases hx.eq_or_lt with rfl | hx
  · simpa using hasDerivAt_variableFiberProfile_zero hs
  · exact hasDerivAt_variableFiberProfile_of_pos hs hx

theorem deriv_variableFiberProfile {s x : ℝ}
    (hs : 0 < s) (hx : 0 ≤ x) :
    deriv (variableFiberProfile s) x = -s / (1 + s * x) ^ 2 :=
  (hasDerivAt_variableFiberProfile hs hx).deriv

theorem variableFiberProfile_nonneg {s x : ℝ}
    (hs : 0 < s) (hx : 0 ≤ x) :
    0 ≤ variableFiberProfile s x := by
  rw [variableFiberProfile_eq_of_nonneg hx]
  apply inv_nonneg.mpr
  exact add_nonneg zero_le_one (mul_nonneg hs.le hx)

theorem variableFiberProfile_le_one {s x : ℝ}
    (hs : 0 < s) (hx : 0 ≤ x) :
    variableFiberProfile s x ≤ 1 := by
  rw [variableFiberProfile_eq_of_nonneg hx]
  apply inv_le_one_of_one_le₀
  exact le_add_of_nonneg_right (mul_nonneg hs.le hx)

def variableFiberCompositeDeriv (s : ℝ) (R : ℕ) (t : ℝ) : ℝ :=
  (-s / (1 + s * (Real.log t / Real.log R)) ^ 2) *
    (t⁻¹ / Real.log R)

theorem hasDerivAt_variableFiberProfile_comp_log
    {s : ℝ} (hs : 0 < s) {R : ℕ} {t : ℝ}
    (hR : 1 < R) (ht : 1 ≤ t) :
    HasDerivAt
      (variableFiberProfile s ∘ (fun z : ℝ => Real.log z / Real.log R))
      (variableFiberCompositeDeriv s R t) t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hlogR : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hx : 0 ≤ Real.log t / Real.log R :=
    div_nonneg (Real.log_nonneg ht) hlogR.le
  have hp := (hasDerivAt_variableFiberProfile hs hx).comp t
    ((Real.hasDerivAt_log ht0.ne').div_const (Real.log R))
  unfold variableFiberCompositeDeriv
  exact hp

theorem deriv_variableFiberProfile_comp_log
    {s : ℝ} (hs : 0 < s) {R : ℕ} {t : ℝ}
    (hR : 1 < R) (ht : 1 ≤ t) :
    deriv (fun z : ℝ => variableFiberProfile s
      (Real.log z / Real.log R)) t = variableFiberCompositeDeriv s R t :=
  (hasDerivAt_variableFiberProfile_comp_log hs hR ht).deriv

theorem variableFiberCompositeDeriv_nonpos
    {s : ℝ} (hs : 0 < s) {R : ℕ} {t : ℝ}
    (hR : 1 < R) (ht : 1 ≤ t) :
    variableFiberCompositeDeriv s R t ≤ 0 := by
  unfold variableFiberCompositeDeriv
  apply mul_nonpos_of_nonpos_of_nonneg
  · apply div_nonpos_of_nonpos_of_nonneg
    · exact neg_nonpos.mpr hs.le
    · exact sq_nonneg _
  · exact div_nonneg (inv_nonneg.mpr (zero_le_one.trans ht))
      (Real.log_pos (by exact_mod_cast hR)).le

theorem continuousOn_variableFiberCompositeDeriv
    {s : ℝ} (hs : 0 < s) {R : ℕ} (hR : 1 < R) {Q : ℕ} :
    ContinuousOn (variableFiberCompositeDeriv s R)
      (Set.Icc (1 : ℝ) Q) := by
  have hlogR : Real.log (R : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hR)).ne'
  unfold variableFiberCompositeDeriv
  have hlog : ContinuousOn (fun t : ℝ => Real.log t / Real.log R)
      (Set.Icc (1 : ℝ) Q) :=
    (continuousOn_id.log (fun t ht =>
      (zero_lt_one.trans_le ht.1).ne')).div_const _
  have hden : ContinuousOn (fun t : ℝ =>
      (1 + s * (Real.log t / Real.log R)) ^ 2)
      (Set.Icc (1 : ℝ) Q) :=
    (continuousOn_const.add (continuousOn_const.mul hlog)).pow 2
  have hfrac : ContinuousOn (fun t : ℝ =>
      -s / (1 + s * (Real.log t / Real.log R)) ^ 2)
      (Set.Icc (1 : ℝ) Q) := by
    apply continuousOn_const.div hden
    intro t ht
    have hx : 0 ≤ Real.log t / Real.log R :=
      div_nonneg (Real.log_nonneg ht.1)
        (Real.log_pos (by exact_mod_cast hR)).le
    have hbase : 0 < 1 + s * (Real.log t / Real.log R) := by
      nlinarith
    exact pow_ne_zero 2 hbase.ne'
  have hinv : ContinuousOn (fun t : ℝ => t⁻¹ / Real.log R)
      (Set.Icc (1 : ℝ) Q) := by
    apply (continuousOn_id.inv₀ (fun t ht =>
      (zero_lt_one.trans_le ht.1).ne')).div_const
  exact hfrac.mul hinv

theorem intervalIntegrable_variableFiberCompositeDeriv
    {s : ℝ} (hs : 0 < s) {R Q : ℕ} (hR : 1 < R) (hQ : 1 ≤ Q) :
    IntervalIntegrable (variableFiberCompositeDeriv s R) volume 1 Q := by
  have hc : ContinuousOn (variableFiberCompositeDeriv s R)
      (Set.uIcc (1 : ℝ) Q) := by
    rw [Set.uIcc_of_le (by exact_mod_cast hQ)]
    exact continuousOn_variableFiberCompositeDeriv hs hR
  exact hc.intervalIntegrable

theorem intervalIntegrable_deriv_variableFiber_comp_log
    {s : ℝ} (hs : 0 < s) {R Q : ℕ} (hR : 1 < R) (hQ : 1 ≤ Q) :
    IntervalIntegrable
      (deriv (fun z : ℝ => variableFiberProfile s
        (Real.log z / Real.log R))) volume 1 Q := by
  have hQreal : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hc := intervalIntegrable_variableFiberCompositeDeriv hs hR hQ
  exact hc.congr fun t ht => by
    have ht' := Set.uIoc_subset_uIcc ht
    rw [Set.uIcc_of_le hQreal] at ht'
    exact (deriv_variableFiberProfile_comp_log hs hR ht'.1).symm

theorem integrableOn_deriv_variableFiber_comp_log_Icc
    {s : ℝ} (hs : 0 < s) {R Q : ℕ} (hR : 1 < R) :
    IntegrableOn
      (deriv (fun z : ℝ => variableFiberProfile s
        (Real.log z / Real.log R))) (Set.Icc (1 : ℝ) Q) := by
  have heq : ∀ t ∈ Set.Icc (1 : ℝ) Q,
      deriv (fun z : ℝ => variableFiberProfile s
        (Real.log z / Real.log R)) t =
        variableFiberCompositeDeriv s R t := by
    intro t ht
    exact deriv_variableFiberProfile_comp_log hs hR ht.1
  exact ((continuousOn_variableFiberCompositeDeriv hs hR).integrableOn_Icc).congr
    (ae_restrict_mem measurableSet_Icc |>.mono fun t ht => (heq t ht).symm)

theorem integrableOn_abs_deriv_variableFiber_comp_log_Ioc
    {s : ℝ} (hs : 0 < s) {R Q : ℕ} (hR : 1 < R) :
    IntegrableOn
      (fun t => |deriv (fun z : ℝ => variableFiberProfile s
        (Real.log z / Real.log R)) t|) (Set.Ioc (1 : ℝ) Q) := by
  have h : IntegrableOn
      (fun t => |deriv (fun z : ℝ => variableFiberProfile s
        (Real.log z / Real.log R)) t|) (Set.Icc (1 : ℝ) Q) :=
    (integrableOn_deriv_variableFiber_comp_log_Icc
      (Q := Q) hs hR).abs
  exact h.mono_set Set.Ioc_subset_Icc_self

theorem integrableOn_deriv_mul_log_variableFiber_comp_log
    {s : ℝ} (hs : 0 < s) (S : ℝ) {R Q : ℕ} (hR : 1 < R) :
    IntegrableOn
      (fun t => deriv (fun z : ℝ => variableFiberProfile s
          (Real.log z / Real.log R)) t * (S * Real.log t))
      (Set.Ioc (1 : ℝ) Q) := by
  have hcont : ContinuousOn
      (fun t : ℝ => variableFiberCompositeDeriv s R t *
        (S * Real.log t)) (Set.Icc (1 : ℝ) Q) :=
    (continuousOn_variableFiberCompositeDeriv hs hR).mul
      (continuousOn_const.mul
        (continuousOn_id.log (fun t ht =>
          (zero_lt_one.trans_le ht.1).ne')))
  have hint : IntegrableOn
      (fun t : ℝ => variableFiberCompositeDeriv s R t *
        (S * Real.log t)) (Set.Ioc (1 : ℝ) Q) :=
    (hcont.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  apply hint.congr
  exact (ae_restrict_mem measurableSet_Ioc).mono fun t ht => by
    change variableFiberCompositeDeriv s R t * (S * Real.log t) =
      deriv (fun z : ℝ => variableFiberProfile s
        (Real.log z / Real.log R)) t * (S * Real.log t)
    rw [deriv_variableFiberProfile_comp_log hs hR ht.1.le]

theorem integral_abs_deriv_variableFiber_comp_log_le_one
    {s : ℝ} (hs : 0 < s) {R Q : ℕ} (hR : 1 < R) (hQ : 1 ≤ Q) :
    (∫ t in Set.Ioc (1 : ℝ) Q,
      |deriv (fun z : ℝ => variableFiberProfile s
        (Real.log z / Real.log R)) t|) ≤ 1 := by
  let f : ℝ → ℝ := fun z =>
    variableFiberProfile s (Real.log z / Real.log R)
  have hQreal : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hdiff : ∀ t ∈ Set.uIcc (1 : ℝ) Q,
      DifferentiableAt ℝ f t := by
    intro t ht
    rw [Set.uIcc_of_le hQreal] at ht
    exact (hasDerivAt_variableFiberProfile_comp_log hs hR ht.1).differentiableAt
  have hint : IntervalIntegrable (deriv f) volume 1 Q :=
    intervalIntegrable_deriv_variableFiber_comp_log hs hR hQ
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
      rw [deriv_variableFiberProfile_comp_log hs hR ht.1]
      exact variableFiberCompositeDeriv_nonpos hs hR ht.1
    _ = -(f Q - f 1) := by
      rw [intervalIntegral.integral_neg, hfund]
    _ = 1 - variableFiberProfile s (Real.log Q / Real.log R) := by
      simp [f]
    _ ≤ 1 := by
      apply sub_le_self
      apply variableFiberProfile_nonneg hs
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hQ))
        (Real.log_pos (by exact_mod_cast hR)).le

theorem variableFiberProfile_eq_factor
    {K : ℕ} {A x : ℝ} (hx : 0 ≤ x) :
    variableFiberProfile (A * (K : ℝ)) x =
      VariableMaynard.factor A ((K : ℝ) * x) := by
  rw [variableFiberProfile_eq_of_nonneg hx]
  unfold VariableMaynard.factor
  congr 2
  ring

noncomputable def variableCoordinateOuterProfile
    (K : ℕ) (A : ℝ) (R : ℕ) (m : ↑(primorialShifts K))
    (r : ↑(primorialShifts K) → ℕ) : ℝ :=
  ∏ h ∈ (Finset.univ : Finset ↑(primorialShifts K)).erase m,
    variableFiberProfile (A * (K : ℝ))
      (Real.log (r h) / Real.log R)

theorem primorialShiftsCandidate_update_eq_outer_mul_profile
    {K R W : ℕ} {A : ℝ} (hK : 0 < K) (hA : 0 < A)
    (m : ↑(primorialShifts K)) {r : ↑(primorialShifts K) → ℕ}
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple
      (primorialShifts K) R W r)
    (hrm : r m = 1) (hR : 1 < R) {u : ℕ}
    (hu : u ∈ BoundedGaps.Maynard.maynardS2CoordinateFiberSupport
      (primorialShifts K) R W m r) :
    primorialShiftsCandidate K A
        (Function.update (fun h => Real.log (r h) / Real.log R) m
          (Real.log u / Real.log R)) =
      variableCoordinateOuterProfile K A R m r *
        variableFiberProfile (A * (K : ℝ))
          (Real.log u / Real.log R) := by
  let d := Function.update r m u
  have hdMem : d ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport
      (primorialShifts K) R W :=
    Erdos6.Maynard.update_mem_support_of_mem_coordinateFiber m hr hrm hu
  have hsimplex := Erdos6.Maynard.normalizedLog_mem_finiteSimplex_of_mem_support
    hR hdMem
  have hpoint :
      BoundedGaps.Maynard.normalizedDivisorLogTuple (primorialShifts K) R d =
        Function.update (fun h => Real.log (r h) / Real.log R) m
          (Real.log u / Real.log R) := by
    funext h
    by_cases hh : h = m
    · subst h
      simp [d, BoundedGaps.Maynard.normalizedDivisorLogTuple]
    · simp [d, BoundedGaps.Maynard.normalizedDivisorLogTuple, hh]
  rw [← hpoint,
    ← primorialShiftsContinuousProduct_eq_candidate_of_mem_simplex hsimplex]
  unfold primorialShiftsContinuousProduct
  rw [← Finset.mul_prod_erase (Finset.univ :
    Finset ↑(primorialShifts K))
      (fun h => variableContinuousFactor A
        ((K : ℝ) * BoundedGaps.Maynard.normalizedDivisorLogTuple
          (primorialShifts K) R d h)) (Finset.mem_univ m)]
  have hm : BoundedGaps.Maynard.normalizedDivisorLogTuple
      (primorialShifts K) R d m = Real.log u / Real.log R := by
    simp [d, BoundedGaps.Maynard.normalizedDivisorLogTuple]
  rw [hm]
  have hux : 0 ≤ Real.log u / Real.log R := by
    have huPos : 0 < u :=
      ((BoundedGaps.Maynard.mem_maynardS2CoordinateFiberSupport_iff
        m hrm).mp hu).2.1
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast huPos))
      (Real.log_pos (by exact_mod_cast hR)).le
  rw [variableContinuousFactor_eq_factor
    (mul_nonneg (Nat.cast_nonneg _) hux),
    ← variableFiberProfile_eq_factor hux]
  have hprod :
      (∏ h ∈ (Finset.univ : Finset ↑(primorialShifts K)).erase m,
        variableContinuousFactor A
          ((K : ℝ) * BoundedGaps.Maynard.normalizedDivisorLogTuple
            (primorialShifts K) R d h)) =
      variableCoordinateOuterProfile K A R m r := by
    unfold variableCoordinateOuterProfile
    apply Finset.prod_congr rfl
    intro h hh
    have hne : h ≠ m := (Finset.mem_erase.mp hh).1
    have hdh := (BoundedGaps.Maynard.mem_maynardDivisorTupleBox_iff.mp
      (BoundedGaps.Maynard.mem_maynardDivisorTupleSupport_iff.mp hdMem).1) h
    have hrhPos : 0 < r h := by
      have : 1 ≤ d h := hdh.1
      have : 0 < d h := Nat.zero_lt_one.trans_le this
      simpa [d, hne] using this
    have hx : 0 ≤ Real.log (r h) / Real.log R :=
      div_nonneg (Real.log_nonneg (by exact_mod_cast hrhPos))
        (Real.log_pos (by exact_mod_cast hR)).le
    have hlogEq : BoundedGaps.Maynard.normalizedDivisorLogTuple
        (primorialShifts K) R d h = Real.log (r h) / Real.log R := by
      simp [BoundedGaps.Maynard.normalizedDivisorLogTuple, d, hne]
    rw [hlogEq]
    rw [variableContinuousFactor_eq_factor
      (mul_nonneg (Nat.cast_nonneg _) hx),
      variableFiberProfile_eq_factor hx]
  rw [hprod]
  ring

noncomputable def variableFiberScalarSum
    (K : ℕ) (A : ℝ) (R W : ℕ) (m : ↑(primorialShifts K))
    (r : ↑(primorialShifts K) → ℕ) : ℝ :=
  ∑ u ∈ BoundedGaps.Maynard.maynardS2CoordinateFiberSupport
      (primorialShifts K) R W m r,
    ((ArithmeticFunction.moebius u : ℝ) ^ 2 / Nat.totient u) *
      variableFiberProfile (A * (K : ℝ))
        (Real.log u / Real.log R)

noncomputable def variableFiberEndpointIntegral
    (K : ℕ) (A : ℝ) (R : ℕ) (m : ↑(primorialShifts K))
    (r : ↑(primorialShifts K) → ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..
      (Real.log (BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
        (BoundedGaps.Maynard.maynardS2OffCoordinateProduct
          (primorialShifts K) m r)) / Real.log R),
    variableFiberProfile (A * (K : ℝ)) x

theorem primorialShiftsCoordinateFiberSum_eq_outer_mul_scalarSum
    {K R W : ℕ} {A : ℝ} (hK : 0 < K) (hA : 0 < A)
    (m : ↑(primorialShifts K)) {r : ↑(primorialShifts K) → ℕ}
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple
      (primorialShifts K) R W r)
    (hrm : r m = 1) (hR : 1 < R) :
    BoundedGaps.Maynard.maynardS2CoordinateFiberSum (primorialShifts K) R W
        (BoundedGaps.Maynard.maynardYValue (primorialShifts K) R W
          (primorialShiftsCandidate K A)) m r =
      variableCoordinateOuterProfile K A R m r *
        variableFiberScalarSum K A R W m r := by
  rw [BoundedGaps.Maynard.maynardS2CoordinateFiberSum_maynardYValue_eq_sourceSum
    m hr hrm]
  unfold variableFiberScalarSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [primorialShiftsCandidate_update_eq_outer_mul_profile
    hK hA m hr hrm hR hu]
  ring

theorem exists_uniform_variableFiberAbel_bound
    (s : ℝ) (hs : 0 < s) :
    ∃ K₀ C₀ : ℝ, 0 < K₀ ∧ 0 ≤ C₀ ∧
      ∀ {K D R : ℕ} (m : ↑(primorialShifts K))
          (r : ↑(primorialShifts K) → ℕ),
        0 < K →
        BoundedGaps.Maynard.IsMaynardDivisorTuple
            (primorialShifts K) R (primorial D) r →
        1 ≤ D → 2 ≤ Real.log R →
        1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
          (BoundedGaps.Maynard.maynardS2OffCoordinateProduct
            (primorialShifts K) m r) →
        |variableFiberScalarSum K (s / (K : ℝ)) R (primorial D) m r -
          BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r *
            Real.log R *
              variableFiberEndpointIntegral K (s / (K : ℝ)) R m r| ≤
          2 * Erdos6.Maynard.largeFiberAbelEnvelope K₀ C₀ D R m r := by
  obtain ⟨K₀, C₀, hK₀, hC₀, hcum⟩ :=
    BoundedGaps.Maynard.exists_uniform_abs_abelCumulative_maynardS2CoordinateFiberCoefficient_sub_density_log_le_logarithmic
  refine ⟨K₀, C₀, hK₀, hC₀, ?_⟩
  intro K D R m r hK hr hD hlogR hQ
  let Q := BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
    (BoundedGaps.Maynard.maynardS2OffCoordinateProduct
      (primorialShifts K) m r)
  let S := BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r
  let E := Erdos6.Maynard.largeFiberAbelEnvelope K₀ C₀ D R m r
  have hR : 1 < R := by
    by_contra hnot
    have hRle : (R : ℝ) ≤ 1 := by exact_mod_cast (le_of_not_gt hnot)
    have hlogNonpos := Real.log_nonpos (by positivity : (0 : ℝ) ≤ R) hRle
    linarith
  have hE : 0 ≤ E :=
    Erdos6.Maynard.largeFiberAbelEnvelope_nonneg hK₀ hC₀ hD hlogR m r hr
  have hQone : 1 ≤ Q := by omega
  have hG : Continuous (variableFiberProfile s) :=
    continuous_variableFiberProfile hs
  have hfDeriv : ∀ x ∈ Set.Icc (1 : ℝ) Q,
      HasDerivAt
        (fun t => variableFiberProfile s (Real.log t / Real.log R))
        (deriv (fun t => variableFiberProfile s
          (Real.log t / Real.log R)) x) x := by
    intro x hx
    exact (hasDerivAt_variableFiberProfile_comp_log hs hR hx.1).differentiableAt.hasDerivAt
  have hfDerivInt : IntervalIntegrable
      (deriv (fun t : ℝ => variableFiberProfile s
        (Real.log t / Real.log R))) volume 1 Q :=
    intervalIntegrable_deriv_variableFiber_comp_log hs hR hQone
  have hfInt : IntegrableOn
      (deriv (fun t : ℝ => variableFiberProfile s
        (Real.log t / Real.log R))) (Set.Icc (1 : ℝ) Q) :=
    integrableOn_deriv_variableFiber_comp_log_Icc hs hR
  have hfNormInt : IntegrableOn
      (fun t => |deriv (fun z : ℝ => variableFiberProfile s
        (Real.log z / Real.log R)) t|) (Set.Ioc (1 : ℝ) Q) :=
    integrableOn_abs_deriv_variableFiber_comp_log_Ioc hs hR
  have hmainInt : IntegrableOn
      (fun t => deriv (fun z : ℝ => variableFiberProfile s
          (Real.log z / Real.log R)) t * (S * Real.log t))
      (Set.Ioc (1 : ℝ) Q) :=
    integrableOn_deriv_mul_log_variableFiber_comp_log hs S hR
  have happrox : ∀ t ∈ Set.Icc (1 : ℝ) Q,
      |BoundedGaps.Maynard.abelCumulative
          (BoundedGaps.Maynard.maynardS2CoordinateFiberCoefficient
            (primorialShifts K) (primorial D) m r) t -
        S * Real.log t| ≤ E := by
    intro t ht
    exact hcum m r hr hlogR ht.1
  have hvariation :
      (∫ t in Set.Ioc (1 : ℝ) Q,
        |deriv (fun z : ℝ => variableFiberProfile s
          (Real.log z / Real.log R)) t|) ≤ 1 :=
    integral_abs_deriv_variableFiber_comp_log_le_one hs hR hQone
  have hbase :=
    BoundedGaps.Maynard.abs_maynardS2CoordinateFiberWeightedSum_sub_twoScaleNormalizedLogIntegral_le
      m hr hQ hR hE hG hfDeriv hfDerivInt hfInt hfNormInt hmainInt
        happrox hvariation
  have hx : 0 ≤ Real.log Q / Real.log R :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hQone))
      (Real.log_pos (by exact_mod_cast hR)).le
  have hendNonneg : 0 ≤ variableFiberProfile s
      (Real.log Q / Real.log R) := variableFiberProfile_nonneg hs hx
  have hendLe : variableFiberProfile s
      (Real.log Q / Real.log R) ≤ 1 := variableFiberProfile_le_one hs hx
  have hendAbs : |variableFiberProfile s
      (Real.log Q / Real.log R)| ≤ 1 := by
    rw [abs_of_nonneg hendNonneg]
    exact hendLe
  have hfactor : E *
      (|variableFiberProfile s (Real.log Q / Real.log R)| + 1) ≤
        2 * E := by nlinarith
  have hslope : (s / (K : ℝ)) * (K : ℝ) = s := by
    have hKcast : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
    field_simp
  simpa [variableFiberScalarSum, variableFiberEndpointIntegral,
    hslope, Q, S, E] using hbase.trans hfactor

noncomputable def variableOuterCutoff (x : ℝ) : ℝ :=
  min 1 (max 0 (3 - 4 * x))

theorem continuous_variableOuterCutoff : Continuous variableOuterCutoff := by
  unfold variableOuterCutoff
  fun_prop

theorem variableOuterCutoff_nonneg (x : ℝ) :
    0 ≤ variableOuterCutoff x := by
  unfold variableOuterCutoff
  exact le_min (by norm_num) (le_max_left _ _)

theorem variableOuterCutoff_le_one (x : ℝ) :
    variableOuterCutoff x ≤ 1 := by
  unfold variableOuterCutoff
  exact min_le_left _ _

theorem variableOuterCutoff_eq_one {x : ℝ} (hx : x ≤ 1 / 2) :
    variableOuterCutoff x = 1 := by
  unfold variableOuterCutoff
  have h : 1 ≤ 3 - 4 * x := by linarith
  rw [max_eq_right ((by norm_num : (0 : ℝ) ≤ 1).trans h), min_eq_left h]

theorem variableOuterCutoff_eq_zero {x : ℝ} (hx : 3 / 4 ≤ x) :
    variableOuterCutoff x = 0 := by
  unfold variableOuterCutoff
  have h : 3 - 4 * x ≤ 0 := by linarith
  rw [max_eq_left h]
  norm_num

theorem variableOuterCutoff_mul_quarter_le_complement
    {x eps q : ℝ} (heps : eps ≤ 1 / 4) (hq0 : 0 ≤ q)
    (hq : 1 - x - eps ≤ q) :
    variableOuterCutoff x * (1 / 4) ≤ q := by
  by_cases hx : x ≤ 1 / 2
  · rw [variableOuterCutoff_eq_one hx]
    linarith
  · by_cases hx' : 3 / 4 ≤ x
    · rw [variableOuterCutoff_eq_zero hx']
      simpa using hq0
    · have hxlo : 1 / 2 < x := lt_of_not_ge hx
      have hxhi : x < 3 / 4 := lt_of_not_ge hx'
      have hcut : variableOuterCutoff x = 3 - 4 * x := by
        unfold variableOuterCutoff
        have h0 : 0 ≤ 3 - 4 * x := by linarith
        have h1 : 3 - 4 * x ≤ 1 := by linarith
        rw [max_eq_right h0, min_eq_right h1]
      rw [hcut]
      linarith

noncomputable def variableQuarterMass (K : ℕ) (A : ℝ) : ℝ :=
  Real.log (1 + A * (K : ℝ) * (1 / 4 : ℝ)) /
    (A * (K : ℝ))

theorem variableQuarterMass_pos
    {K : ℕ} {A : ℝ} (hK : 0 < K) (hA : 0 < A) :
    0 < variableQuarterMass K A := by
  unfold variableQuarterMass
  have hterm : 0 < A * (K : ℝ) * (1 / 4 : ℝ) := by positivity
  exact div_pos (Real.log_pos (by linarith)) (by positivity)

theorem integral_variableFiberProfile_interval
    {K : ℕ} {A B : ℝ} (hK : 0 < K) (hA : 0 < A)
    (hB : 0 ≤ B) :
    (∫ x : ℝ in (0 : ℝ)..B,
      variableFiberProfile (A * (K : ℝ)) x) =
      Real.log (1 + A * (K : ℝ) * B) / (A * (K : ℝ)) := by
  calc
    (∫ x : ℝ in (0 : ℝ)..B,
        variableFiberProfile (A * (K : ℝ)) x) =
        ∫ x : ℝ in (0 : ℝ)..B,
          VariableMaynard.factor A ((K : ℝ) * x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx0 : 0 ≤ x := by
        rw [Set.uIcc_of_le hB] at hx
        exact hx.1
      exact variableFiberProfile_eq_factor hx0
    _ = _ := VariableMaynard.integral_factor_interval hK hA hB

theorem cutoff_mul_variableQuarterMass_le_fiberIntegral
    {K : ℕ} {A c q : ℝ} (hK : 0 < K) (hA : 0 < A)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hq : c * (1 / 4) ≤ q) :
    c * variableQuarterMass K A ≤
      ∫ x : ℝ in (0 : ℝ)..q,
        variableFiberProfile (A * (K : ℝ)) x := by
  have hq0 : 0 ≤ q :=
    (mul_nonneg hc0 (by norm_num : (0 : ℝ) ≤ 1 / 4)).trans hq
  let s : ℝ := A * (K : ℝ)
  have hs : 0 < s := by dsimp [s]; positivity
  have hx : 0 ≤ s * (1 / 4 : ℝ) := by positivity
  have hconc := Erdos6.Maynard.mul_log_one_add_le_log_one_add_mul
    hc0 hc1 hx
  have harg : 1 + c * (s * (1 / 4 : ℝ)) ≤ 1 + s * q := by
    nlinarith
  have hargPos : 0 < 1 + c * (s * (1 / 4 : ℝ)) := by positivity
  have hlogMono :
      Real.log (1 + c * (s * (1 / 4 : ℝ))) ≤
        Real.log (1 + s * q) :=
    Real.strictMonoOn_log.monotoneOn hargPos
      (show 1 + s * q ∈ Set.Ioi (0 : ℝ) from Set.mem_Ioi.mpr (by positivity))
      harg
  rw [integral_variableFiberProfile_interval hK hA hq0]
  unfold variableQuarterMass
  change c * (Real.log (1 + s * (1 / 4 : ℝ)) / s) ≤ _
  calc
    c * (Real.log (1 + s * (1 / 4 : ℝ)) / s) =
        (c * Real.log (1 + s * (1 / 4 : ℝ))) / s := by ring
    _ ≤ Real.log (1 + s * q) / s :=
      div_le_div_of_nonneg_right (hconc.trans hlogMono) hs.le
    _ = _ := by rfl

theorem variableCoordinateOuterProfile_nonneg_le_one
    {K R W : ℕ} {A : ℝ} (hA : 0 < A)
    (m : ↑(primorialShifts K)) {r : ↑(primorialShifts K) → ℕ}
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple
      (primorialShifts K) R W r) (hR : 1 < R) :
    0 ≤ variableCoordinateOuterProfile K A R m r ∧
      variableCoordinateOuterProfile K A R m r ≤ 1 := by
  have hbox := hr.mem_maynardDivisorTupleBox
  have hcoord : ∀ h : ↑(primorialShifts K),
      Real.log (r h) / Real.log R ∈ Set.Icc (0 : ℝ) 1 :=
    fun h => BoundedGaps.Maynard.normalizedDivisorLogTuple_mem_Icc_of_mem_maynardDivisorTupleBox
      hR hbox h
  have hs : 0 < A * (K : ℝ) := by
    have hK : 0 < K := by
      rw [← card_primorialShifts K]
      exact Finset.card_pos.mpr ⟨m.1, m.2⟩
    positivity
  unfold variableCoordinateOuterProfile
  constructor
  · exact Finset.prod_nonneg fun h hh =>
      variableFiberProfile_nonneg hs (hcoord h).1
  · calc
      (∏ h ∈ (Finset.univ : Finset ↑(primorialShifts K)).erase m,
          variableFiberProfile (A * (K : ℝ))
            (Real.log (r h) / Real.log R)) ≤
          ∏ _h ∈ (Finset.univ : Finset ↑(primorialShifts K)).erase m,
            (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro h hh
          exact variableFiberProfile_nonneg hs (hcoord h).1
        · intro h hh
          exact variableFiberProfile_le_one hs (hcoord h).1
      _ = 1 := by simp

theorem variableFiberEndpointIntegral_bounds
    {K R W : ℕ} {A : ℝ} (hK : 0 < K) (hA : 0 < A)
    (m : ↑(primorialShifts K)) {r : ↑(primorialShifts K) → ℕ}
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple
      (primorialShifts K) R W r) (hR : 1 < R)
    (hQ : 1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
      (BoundedGaps.Maynard.maynardS2OffCoordinateProduct
        (primorialShifts K) m r))
    (hlog3 : Real.log 3 / Real.log R ≤ (1 : ℝ) / 4) :
    variableOuterCutoff
        (Real.log (BoundedGaps.Maynard.maynardS2OffCoordinateProduct
          (primorialShifts K) m r) / Real.log R) *
        variableQuarterMass K A ≤
      variableFiberEndpointIntegral K A R m r ∧
      variableFiberEndpointIntegral K A R m r ≤ 1 := by
  let P := BoundedGaps.Maynard.maynardS2OffCoordinateProduct
    (primorialShifts K) m r
  let Q := BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R P
  let q := Real.log Q / Real.log R
  let x := Real.log P / Real.log R
  let c := variableOuterCutoff x
  have hP : 0 < P :=
    BoundedGaps.Maynard.maynardS2OffCoordinateProduct_pos m r hr
  have hQnat : 1 < Q := by simpa [Q, P] using hQ
  have hQpos : 0 < Q := Nat.zero_lt_of_lt hQnat
  have hlogR : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hq0 : 0 ≤ q :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hQpos)) hlogR.le
  have hendpoint := Erdos6.Maynard.coordinateFiberEndpoint_ratio_ge_complement_sub
    m hr hR hQ
  have hqLower : 1 - x - Real.log 3 / Real.log R ≤ q := by
    simpa [P, Q, q, x] using hendpoint
  have hc0 : 0 ≤ c := variableOuterCutoff_nonneg x
  have hc1 : c ≤ 1 := variableOuterCutoff_le_one x
  have hcq : c * (1 / 4) ≤ q :=
    variableOuterCutoff_mul_quarter_le_complement hlog3 hq0 hqLower
  have hlower := cutoff_mul_variableQuarterMass_le_fiberIntegral
    hK hA hc0 hc1 hcq
  have hQP : Q * P < R := by
    have hle : Q * P ≤ R - 1 := by
      unfold Q BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint
      simpa [Nat.mul_comm] using Nat.mul_div_le (R - 1) P
    omega
  have hQltR : Q < R := by
    have hQleQP : Q ≤ Q * P := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left Q hP
    exact hQleQP.trans_lt hQP
  have hlogQle : Real.log Q ≤ Real.log R :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by exact_mod_cast hQpos))
      (Set.mem_Ioi.mpr (by exact_mod_cast Nat.zero_lt_of_lt hR))
      (by exact_mod_cast hQltR.le)
  have hq1 : q ≤ 1 := (div_le_one hlogR).2 hlogQle
  have hintFormula := integral_variableFiberProfile_interval hK hA hq0
  have hs : 0 < A * (K : ℝ) := by positivity
  have harg : 0 < 1 + (A * (K : ℝ)) * q := by positivity
  have hlogBound : Real.log (1 + (A * (K : ℝ)) * q) ≤
      (A * (K : ℝ)) * q := by
    have := Real.log_le_sub_one_of_pos harg
    linarith
  have hupper :
      (∫ z : ℝ in (0 : ℝ)..q,
        variableFiberProfile (A * (K : ℝ)) z) ≤ 1 := by
    rw [hintFormula]
    calc
      Real.log (1 + A * (K : ℝ) * q) / (A * (K : ℝ)) ≤
          ((A * (K : ℝ)) * q) / (A * (K : ℝ)) :=
        div_le_div_of_nonneg_right hlogBound hs.le
      _ = q := by field_simp [hs.ne']
      _ ≤ 1 := hq1
  simpa [variableFiberEndpointIntegral, P, Q, q, x, c] using
    And.intro hlower hupper

theorem variableOuterCutoff_eq_zero_of_bad_endpoint
    {K R W : ℕ} (m : ↑(primorialShifts K))
    {r : ↑(primorialShifts K) → ℕ}
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple
      (primorialShifts K) R W r) (hR : 1 < R)
    (hbad : ¬1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
      (BoundedGaps.Maynard.maynardS2OffCoordinateProduct
        (primorialShifts K) m r))
    (hlog2 : Real.log 2 / Real.log R ≤ (1 : ℝ) / 4) :
    variableOuterCutoff
      (Real.log (BoundedGaps.Maynard.maynardS2OffCoordinateProduct
        (primorialShifts K) m r) / Real.log R) = 0 := by
  let P := BoundedGaps.Maynard.maynardS2OffCoordinateProduct
    (primorialShifts K) m r
  let Q := BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R P
  have hP : 0 < P :=
    BoundedGaps.Maynard.maynardS2OffCoordinateProduct_pos m r hr
  have hbad' : ¬1 < Q := by simpa [Q, P] using hbad
  have hQle : Q ≤ 1 := le_of_not_gt hbad'
  have hRsub : R - 1 < (Q + 1) * P := by
    unfold Q BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint
    exact (Nat.div_lt_iff_lt_mul hP).mp
      (Nat.lt_succ_self ((R - 1) / P))
  have hRle : R ≤ 2 * P := by
    have hmul : (Q + 1) * P ≤ 2 * P :=
      Nat.mul_le_mul_right P (by omega)
    omega
  have hlogR : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hPReal : (0 : ℝ) < P := by exact_mod_cast hP
  have h2PReal : (0 : ℝ) < 2 * P := by positivity
  have hRReal : (0 : ℝ) < R := by exact_mod_cast Nat.zero_lt_of_lt hR
  have hRleReal : (R : ℝ) ≤ (2 : ℝ) * P := by exact_mod_cast hRle
  have hlogMul : Real.log R ≤ Real.log 2 + Real.log P := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hRReal) (Set.mem_Ioi.mpr h2PReal) hRleReal
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by exact_mod_cast hP.ne')] at hmono
    exact hmono
  have hcomp : 1 - Real.log P / Real.log R ≤
      Real.log 2 / Real.log R := by
    calc
      1 - Real.log P / Real.log R =
          (Real.log R - Real.log P) / Real.log R := by
        field_simp [hlogR.ne']
      _ ≤ Real.log 2 / Real.log R :=
        div_le_div_of_nonneg_right (by linarith) hlogR.le
  apply variableOuterCutoff_eq_zero
  linarith

theorem variableCoordinateFiberSum_sq_lower
    {K D R : ℕ} {A K₀ C₀ : ℝ}
    (hK : 0 < K) (hA : 0 < A) (hK₀ : 0 < K₀) (hC₀ : 0 ≤ C₀)
    (hAbel : ∀ (m : ↑(primorialShifts K))
        (r : ↑(primorialShifts K) → ℕ),
      BoundedGaps.Maynard.IsMaynardDivisorTuple
          (primorialShifts K) R (primorial D) r →
      1 ≤ D → 2 ≤ Real.log R →
      1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
        (BoundedGaps.Maynard.maynardS2OffCoordinateProduct
          (primorialShifts K) m r) →
      |variableFiberScalarSum K A R (primorial D) m r -
        BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r *
          Real.log R * variableFiberEndpointIntegral K A R m r| ≤
        2 * Erdos6.Maynard.largeFiberAbelEnvelope K₀ C₀ D R m r)
    (m : ↑(primorialShifts K)) {r : ↑(primorialShifts K) → ℕ}
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple
      (primorialShifts K) R (primorial D) r)
    (hrm : r m = 1) (hD : 1 ≤ D) (hlogR : 2 ≤ Real.log R)
    (hQ : 1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
      (BoundedGaps.Maynard.maynardS2OffCoordinateProduct
        (primorialShifts K) m r))
    (hlog3 : Real.log 3 / Real.log R ≤ (1 : ℝ) / 4) :
    let O := variableCoordinateOuterProfile K A R m r
    let S := BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r
    let L := Real.log R
    let c := variableOuterCutoff
      (Real.log (BoundedGaps.Maynard.maynardS2OffCoordinateProduct
        (primorialShifts K) m r) / Real.log R)
    let eta := Erdos6.Maynard.largeFiberRelativeError K₀ C₀ D R
    ((O * S * L) * (c * variableQuarterMass K A)) ^ 2 -
        (O * S * L) ^ 2 * (2 * eta + eta ^ 2) ≤
      BoundedGaps.Maynard.maynardS2CoordinateFiberSum
        (primorialShifts K) R (primorial D)
        (BoundedGaps.Maynard.maynardYValue (primorialShifts K) R
          (primorial D) (primorialShiftsCandidate K A)) m r ^ 2 := by
  dsimp only
  let O := variableCoordinateOuterProfile K A R m r
  let S := BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r
  let L := Real.log R
  let I := variableFiberEndpointIntegral K A R m r
  let c := variableOuterCutoff
    (Real.log (BoundedGaps.Maynard.maynardS2OffCoordinateProduct
      (primorialShifts K) m r) / Real.log R)
  let eta := Erdos6.Maynard.largeFiberRelativeError K₀ C₀ D R
  let x := variableFiberScalarSum K A R (primorial D) m r
  let z := BoundedGaps.Maynard.maynardS2CoordinateFiberSum
    (primorialShifts K) R (primorial D)
    (BoundedGaps.Maynard.maynardYValue (primorialShifts K) R
      (primorial D) (primorialShiftsCandidate K A)) m r
  let scale := O * S * L
  let y := scale * I
  let b := scale * (c * variableQuarterMass K A)
  have hR : 1 < R := by
    by_contra hn
    have hRle : (R : ℝ) ≤ 1 := by exact_mod_cast le_of_not_gt hn
    have hnonpos := Real.log_nonpos (by positivity : (0 : ℝ) ≤ R) hRle
    linarith
  have hO := variableCoordinateOuterProfile_nonneg_le_one hA m hr hR
  have hS : 0 < S :=
    BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries_pos m r hr
  have hL : 0 < L := by dsimp [L]; linarith
  have hscale : 0 ≤ scale := by
    dsimp [scale]
    exact mul_nonneg (mul_nonneg hO.1 hS.le) hL.le
  have hI := variableFiberEndpointIntegral_bounds hK hA m hr hR hQ hlog3
  have hI0 : 0 ≤ I := by
    have hc0 := variableOuterCutoff_nonneg
      (Real.log (BoundedGaps.Maynard.maynardS2OffCoordinateProduct
        (primorialShifts K) m r) / Real.log R)
    have hm0 := variableQuarterMass_pos hK hA
    exact (mul_nonneg hc0 hm0.le).trans hI.1
  have hI1 : I ≤ 1 := hI.2
  have heta : 0 ≤ eta :=
    Erdos6.Maynard.largeFiberRelativeError_nonneg hK₀ hC₀ hD hlogR
  have hz : z = O * x := by
    dsimp [z, O, x]
    exact primorialShiftsCoordinateFiberSum_eq_outer_mul_scalarSum
      hK hA m hr hrm hR
  have hxerr := hAbel m r hr hD hlogR hQ
  have henv : 2 * Erdos6.Maynard.largeFiberAbelEnvelope K₀ C₀ D R m r =
      S * L * eta := by
    simpa [S, L, eta] using
      Erdos6.Maynard.two_largeFiberAbelEnvelope_eq_relative
        (K := K₀) (C := C₀) m r hL.ne'
  have herr : |z - y| ≤ scale * eta := by
    rw [hz]
    have heq : O * x - y = O * (x - S * L * I) := by
      dsimp [y, scale]
      ring
    rw [heq, abs_mul, abs_of_nonneg hO.1]
    calc
      O * |x - S * L * I| ≤
          O * (2 * Erdos6.Maynard.largeFiberAbelEnvelope K₀ C₀ D R m r) :=
        mul_le_mul_of_nonneg_left (by simpa [x, S, L, I] using hxerr) hO.1
      _ = scale * eta := by rw [henv]; dsimp [scale]; ring
  have hc0 : 0 ≤ c := by dsimp [c]; apply variableOuterCutoff_nonneg
  have hm0 := variableQuarterMass_pos hK hA
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hby : b ≤ y := by
    dsimp [b, y]
    exact mul_le_mul_of_nonneg_left hI.1 hscale
  have hyScale : y ≤ scale := by
    dsimp [y]
    nlinarith
  exact Erdos6.Maynard.sq_ge_baseline_sq_sub_error
    hscale heta hb0 hby hyScale herr

noncomputable def variableCoordinateFiberSquareDiagonal
    (K : ℕ) (A alpha : ℝ) (N : ℕ)
    (m : ↑(primorialShifts K)) : ℝ :=
  ∑ r ∈ (BoundedGaps.Maynard.maynardDivisorTupleSupport
      (primorialShifts K) (Erdos6.Maynard.maynardRadius alpha N)
      (Erdos6.Maynard.maynardModulus N)).filter (fun r => r m = 1),
    BoundedGaps.Maynard.maynardS2CoordinateFiberSum (primorialShifts K)
        (Erdos6.Maynard.maynardRadius alpha N)
        (Erdos6.Maynard.maynardModulus N)
        (BoundedGaps.Maynard.maynardYValue (primorialShifts K)
          (Erdos6.Maynard.maynardRadius alpha N)
          (Erdos6.Maynard.maynardModulus N)
          (primorialShiftsCandidate K A)) m r ^ 2 /
      ∏ h : ↑(primorialShifts K),
        (BoundedGaps.Maynard.maynardS2G (r h) : ℝ)

noncomputable def variableOuterContinuousDensity
    (K : ℕ) (A : ℝ) {ι : Type*} [Fintype ι]
    (t : ι → ℝ) : ℝ :=
  ∏ i, variableContinuousFactor A ((K : ℝ) * t i) ^ 2

noncomputable def variableOuterSquaredIntegrand
    (K : ℕ) (A : ℝ) {ι : Type*} [Fintype ι]
    (t : ι → ℝ) : ℝ :=
  variableOuterCutoff (VariableMaynard.coordinateSum t) ^ 2 *
    variableOuterContinuousDensity K A t

theorem continuous_variableOuterContinuousDensity
    {K : ℕ} {A : ℝ} (hA : 0 < A) (ι : Type*) [Fintype ι] :
    Continuous (variableOuterContinuousDensity K A : (ι → ℝ) → ℝ) := by
  unfold variableOuterContinuousDensity
  apply continuous_finsetProd
  intro i hi
  exact (continuous_variableContinuousFactor hA).comp
    (continuous_const.mul (continuous_apply i)) |>.pow 2

theorem continuous_variableOuterSquaredIntegrand
    {K : ℕ} {A : ℝ} (hA : 0 < A) (ι : Type*) [Fintype ι] :
    Continuous (variableOuterSquaredIntegrand K A : (ι → ℝ) → ℝ) := by
  unfold variableOuterSquaredIntegrand
  exact ((continuous_variableOuterCutoff.comp
    (by
      change Continuous (fun t : ι → ℝ => ∑ i : ι, t i)
      fun_prop)).pow 2).mul
    (continuous_variableOuterContinuousDensity hA ι)

theorem variableOuterContinuousDensity_bounds
    {K : ℕ} {A : ℝ} (hA : 0 < A)
    {ι : Type*} [Fintype ι] (t : ι → ℝ)
    (ht : t ∈ BoundedGaps.Maynard.maynardCubeOf ι) :
    0 ≤ variableOuterContinuousDensity K A t ∧
      variableOuterContinuousDensity K A t ≤ 1 := by
  unfold variableOuterContinuousDensity
  constructor
  · exact Finset.prod_nonneg fun i hi => sq_nonneg _
  · calc
      (∏ i : ι, variableContinuousFactor A ((K : ℝ) * t i) ^ 2) ≤
          ∏ _i : ι, (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro i hi
          exact sq_nonneg _
        · intro i hi
          have hx : 0 ≤ (K : ℝ) * t i :=
            mul_nonneg (Nat.cast_nonneg _) (ht i (Set.mem_univ i)).1
          rw [variableContinuousFactor_eq_factor hx]
          exact pow_le_one₀ (VariableMaynard.factor_nonneg hA hx)
            (VariableMaynard.factor_le_one hA hx)
      _ = 1 := Finset.prod_const_one

theorem variableOuterSquaredIntegrand_bounds
    {K : ℕ} {A : ℝ} (hA : 0 < A)
    {ι : Type*} [Fintype ι] (t : ι → ℝ)
    (ht : t ∈ BoundedGaps.Maynard.maynardCubeOf ι) :
    0 ≤ variableOuterSquaredIntegrand K A t ∧
      variableOuterSquaredIntegrand K A t ≤ 1 := by
  have hd := variableOuterContinuousDensity_bounds (K := K) hA t ht
  have hc0 := variableOuterCutoff_nonneg (VariableMaynard.coordinateSum t)
  have hc1 := variableOuterCutoff_le_one (VariableMaynard.coordinateSum t)
  unfold variableOuterSquaredIntegrand
  constructor
  · exact mul_nonneg (sq_nonneg _) hd.1
  · have hcsq : variableOuterCutoff (VariableMaynard.coordinateSum t) ^ 2 ≤ 1 :=
      pow_le_one₀ hc0 hc1
    nlinarith [mul_le_mul hcsq hd.2 hd.1 (by norm_num : (0 : ℝ) ≤ 1)]

theorem variableFiberProfile_eq_continuousFactor
    {K : ℕ} {A x : ℝ} (hx : 0 ≤ x) :
    variableFiberProfile (A * (K : ℝ)) x =
      variableContinuousFactor A ((K : ℝ) * x) := by
  rw [variableFiberProfile_eq_factor hx,
    variableContinuousFactor_eq_factor
      (mul_nonneg (Nat.cast_nonneg _) hx)]

theorem tupleOffFaceExtension_variableOuterProfile_sq
    {K R W : ℕ} {A : ℝ} (hA : 0 < A)
    (m : ↑(primorialShifts K))
    (u : Erdos6.Maynard.tupleOffFace (primorialShifts K) m → ℕ)
    (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport
      (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) R W)
    (hR : 1 < R) :
    variableCoordinateOuterProfile K A R m
        (Erdos6.Maynard.tupleOffFaceExtension m u) ^ 2 =
      variableOuterContinuousDensity K A
        (fun h : Erdos6.Maynard.tupleOffFace (primorialShifts K) m =>
          Real.log (u h) / Real.log R) := by
  have hbox :=
    (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hu).mem_maynardDivisorTupleBox
  have hcoord : ∀ h : Erdos6.Maynard.tupleOffFace (primorialShifts K) m,
      0 ≤ Real.log (u h) / Real.log R := fun h =>
    (BoundedGaps.Maynard.normalizedDivisorLogTuple_mem_Icc_of_mem_maynardDivisorTupleBox
      hR hbox h).1
  have hprod : variableCoordinateOuterProfile K A R m
      (Erdos6.Maynard.tupleOffFaceExtension m u) =
      ∏ h : Erdos6.Maynard.tupleOffFace (primorialShifts K) m,
        variableFiberProfile (A * (K : ℝ))
          (Real.log (u h) / Real.log R) := by
    unfold variableCoordinateOuterProfile
    rw [Erdos6.Maynard.prod_subtype_erase_eq_offFace]
    apply Finset.prod_congr rfl
    intro h hh
    have hhmem : h.1 ∈ (primorialShifts K).erase m.1 := by
      simpa [Erdos6.Maynard.tupleOffFace] using h.2
    let hfull : ↑(primorialShifts K) :=
      ⟨h.1, (Finset.mem_erase.mp hhmem).2⟩
    have hne : hfull ≠ m := by
      intro heq
      exact (Finset.mem_erase.mp hhmem).1
        (by simpa [hfull] using
          congrArg (fun z : ↑(primorialShifts K) => z.1) heq)
    have hext : Erdos6.Maynard.tupleOffFaceExtension m u hfull = u h := by
      rw [Erdos6.Maynard.tupleOffFaceExtension_off m u hfull hne]
    simpa [hfull, Erdos6.Maynard.tupleOffFace] using congrArg
      (fun n : ℕ => variableFiberProfile (A * (K : ℝ))
        (Real.log n / Real.log R)) hext
  rw [hprod]
  unfold variableOuterContinuousDensity
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro h hh
  rw [variableFiberProfile_eq_continuousFactor (hcoord h)]

theorem variableFiberArithmeticScale_eq_outer
    {K D R : ℕ} {A : ℝ} (hA : 0 < A)
    (m : ↑(primorialShifts K))
    (u : Erdos6.Maynard.tupleOffFace (primorialShifts K) m → ℕ)
    (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport
      (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) R (primorial D))
    (hR : 1 < R) :
    let r := Erdos6.Maynard.tupleOffFaceExtension m u
    let O := variableCoordinateOuterProfile K A R m r
    let S := BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r
    let L := Real.log R
    (O * S * L) ^ 2 /
        ∏ h : ↑(primorialShifts K),
          (BoundedGaps.Maynard.maynardS2G (r h) : ℝ) =
      BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 * L ^ 2 *
        (BoundedGaps.Maynard.outerTupleWeight
          (Erdos6.Maynard.tupleOffFace (primorialShifts K) m)
          (primorial D) u *
        variableOuterContinuousDensity K A
          (fun h : Erdos6.Maynard.tupleOffFace (primorialShifts K) m =>
            Real.log (u h) / Real.log R)) := by
  dsimp only
  let r := Erdos6.Maynard.tupleOffFaceExtension m u
  have hr : BoundedGaps.Maynard.IsMaynardDivisorTuple
      (primorialShifts K) R (primorial D) r :=
    (Erdos6.Maynard.isMaynardDivisorTuple_extension_iff
      R (primorial D) m u).mpr
      (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hu)
  have hrm : r m = 1 := Erdos6.Maynard.tupleOffFaceExtension_at m u
  have hseries :=
    BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries_sq_div_gProduct_eq_outerSquarefree
      m r hr hrm
  have houter := Erdos6.Maynard.tupleOffFaceExtension_outerWeight m u hu
  have hdensity := tupleOffFaceExtension_variableOuterProfile_sq hA m u hu hR
  rw [show (variableCoordinateOuterProfile K A R m r *
      BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r *
      Real.log R) ^ 2 /
      ∏ h : ↑(primorialShifts K),
        (BoundedGaps.Maynard.maynardS2G (r h) : ℝ) =
      variableCoordinateOuterProfile K A R m r ^ 2 * Real.log R ^ 2 *
        (BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r ^ 2 /
          ∏ h : ↑(primorialShifts K),
            (BoundedGaps.Maynard.maynardS2G (r h) : ℝ)) by ring]
  rw [hseries, houter, hdensity]
  ring

theorem variableOffFace_logProduct_eq_coordinateSum
    {H : Finset ℕ} {R W : ℕ} (m : H)
    (u : Erdos6.Maynard.tupleOffFace H m → ℕ)
    (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport
      (Erdos6.Maynard.tupleOffFace H m) R W) (hR : 1 < R) :
    Real.log (BoundedGaps.Maynard.maynardS2OffCoordinateProduct H m
        (Erdos6.Maynard.tupleOffFaceExtension m u)) / Real.log R =
      VariableMaynard.coordinateSum
        (fun h : Erdos6.Maynard.tupleOffFace H m =>
          Real.log (u h) / Real.log R) := by
  simpa [VariableMaynard.coordinateSum, Erdos6.Maynard.largeCoordinateSum]
    using Erdos6.Maynard.tupleOffFace_logProduct_eq_coordinateSum m u hu hR

theorem variableCoordinateFiberTerm_lower
    {K D R : ℕ} {A K₀ C₀ : ℝ}
    (hK : 0 < K) (hA : 0 < A) (hK₀ : 0 < K₀) (hC₀ : 0 ≤ C₀)
    (hAbel : ∀ (m : ↑(primorialShifts K))
        (r : ↑(primorialShifts K) → ℕ),
      BoundedGaps.Maynard.IsMaynardDivisorTuple
          (primorialShifts K) R (primorial D) r →
      1 ≤ D → 2 ≤ Real.log R →
      1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
        (BoundedGaps.Maynard.maynardS2OffCoordinateProduct
          (primorialShifts K) m r) →
      |variableFiberScalarSum K A R (primorial D) m r -
        BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r *
          Real.log R * variableFiberEndpointIntegral K A R m r| ≤
        2 * Erdos6.Maynard.largeFiberAbelEnvelope K₀ C₀ D R m r)
    (m : ↑(primorialShifts K))
    (u : Erdos6.Maynard.tupleOffFace (primorialShifts K) m → ℕ)
    (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport
      (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) R (primorial D))
    (hD : 2 ≤ D) (hlogR : 2 ≤ Real.log R)
    (hlog2 : Real.log 2 / Real.log R ≤ (1 : ℝ) / 4)
    (hlog3 : Real.log 3 / Real.log R ≤ (1 : ℝ) / 4) :
    let r := Erdos6.Maynard.tupleOffFaceExtension m u
    let point := fun h : Erdos6.Maynard.tupleOffFace
        (primorialShifts K) m => Real.log (u h) / Real.log R
    let eta := Erdos6.Maynard.largeFiberRelativeError K₀ C₀ D R
    BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 * Real.log R ^ 2 *
        (BoundedGaps.Maynard.outerTupleWeight
          (Erdos6.Maynard.tupleOffFace (primorialShifts K) m)
          (primorial D) u *
        (variableQuarterMass K A ^ 2 *
            variableOuterSquaredIntegrand K A point -
          (2 * eta + eta ^ 2) *
            variableOuterContinuousDensity K A point)) ≤
      BoundedGaps.Maynard.maynardS2CoordinateFiberSum
          (primorialShifts K) R (primorial D)
          (BoundedGaps.Maynard.maynardYValue (primorialShifts K) R
            (primorial D) (primorialShiftsCandidate K A)) m r ^ 2 /
        ∏ h : ↑(primorialShifts K),
          (BoundedGaps.Maynard.maynardS2G (r h) : ℝ) := by
  dsimp only
  let r := Erdos6.Maynard.tupleOffFaceExtension m u
  let point := fun h : Erdos6.Maynard.tupleOffFace
      (primorialShifts K) m => Real.log (u h) / Real.log R
  let eta := Erdos6.Maynard.largeFiberRelativeError K₀ C₀ D R
  let O := variableCoordinateOuterProfile K A R m r
  let S := BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r
  let L := Real.log R
  let c := variableOuterCutoff
    (Real.log (BoundedGaps.Maynard.maynardS2OffCoordinateProduct
      (primorialShifts K) m r) / Real.log R)
  let g := ∏ h : ↑(primorialShifts K),
    (BoundedGaps.Maynard.maynardS2G (r h) : ℝ)
  have hR : 1 < R := by
    by_contra hn
    have hRle : (R : ℝ) ≤ 1 := by exact_mod_cast le_of_not_gt hn
    have hnonpos := Real.log_nonpos (by positivity : (0 : ℝ) ≤ R) hRle
    linarith
  have hr : BoundedGaps.Maynard.IsMaynardDivisorTuple
      (primorialShifts K) R (primorial D) r :=
    (Erdos6.Maynard.isMaynardDivisorTuple_extension_iff
      R (primorial D) m u).mpr
      (BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hu)
  have hrm : r m = 1 := Erdos6.Maynard.tupleOffFaceExtension_at m u
  have hg : 0 < g := by
    dsimp [g]
    exact BoundedGaps.Maynard.maynardS2G_product_pos_of_supported hD hr
  have hscale := variableFiberArithmeticScale_eq_outer hA m u hu hR
  have hcut : c = variableOuterCutoff (VariableMaynard.coordinateSum point) := by
    dsimp [c, point, r]
    rw [variableOffFace_logProduct_eq_coordinateSum m u hu hR]
  have hdensity : O ^ 2 = variableOuterContinuousDensity K A point := by
    dsimp [O, point, r]
    exact tupleOffFaceExtension_variableOuterProfile_sq hA m u hu hR
  by_cases hQ : 1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
      (BoundedGaps.Maynard.maynardS2OffCoordinateProduct
        (primorialShifts K) m r)
  · have hraw := variableCoordinateFiberSum_sq_lower hK hA hK₀ hC₀
      hAbel m hr hrm (by omega) hlogR hQ hlog3
    have hdiv := (div_le_div_iff_of_pos_right hg).mpr hraw
    change (((O * S * L) * (c * variableQuarterMass K A)) ^ 2 -
      (O * S * L) ^ 2 * (2 * eta + eta ^ 2)) / g ≤ _ at hdiv
    rw [sub_div] at hdiv
    have houter :
        (O * S * L) ^ 2 / g =
          BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 * L ^ 2 *
            (BoundedGaps.Maynard.outerTupleWeight
              (Erdos6.Maynard.tupleOffFace (primorialShifts K) m)
              (primorial D) u *
              variableOuterContinuousDensity K A point) := by
      simpa [O, S, L, g, r, point] using hscale
    rw [show ((O * S * L) * (c * variableQuarterMass K A)) ^ 2 / g =
        ((O * S * L) ^ 2 / g) *
          (c ^ 2 * variableQuarterMass K A ^ 2) by ring,
      show ((O * S * L) ^ 2 * (2 * eta + eta ^ 2)) / g =
        ((O * S * L) ^ 2 / g) * (2 * eta + eta ^ 2) by ring,
      houter] at hdiv
    rw [hcut] at hdiv
    change BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 * L ^ 2 *
        (BoundedGaps.Maynard.outerTupleWeight
          (Erdos6.Maynard.tupleOffFace (primorialShifts K) m)
          (primorial D) u *
        (variableQuarterMass K A ^ 2 *
            variableOuterSquaredIntegrand K A point -
          (2 * eta + eta ^ 2) *
            variableOuterContinuousDensity K A point)) ≤
      BoundedGaps.Maynard.maynardS2CoordinateFiberSum
          (primorialShifts K) R (primorial D)
          (BoundedGaps.Maynard.maynardYValue (primorialShifts K) R
            (primorial D) (primorialShiftsCandidate K A)) m r ^ 2 / g
    calc
      _ = BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 * L ^ 2 *
              (BoundedGaps.Maynard.outerTupleWeight
                (Erdos6.Maynard.tupleOffFace (primorialShifts K) m)
                (primorial D) u *
                variableOuterContinuousDensity K A point) *
              (variableOuterCutoff (VariableMaynard.coordinateSum point) ^ 2 *
                variableQuarterMass K A ^ 2) -
            BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 * L ^ 2 *
              (BoundedGaps.Maynard.outerTupleWeight
                (Erdos6.Maynard.tupleOffFace (primorialShifts K) m)
                (primorial D) u *
                variableOuterContinuousDensity K A point) *
              (2 * eta + eta ^ 2) := by
          unfold variableOuterSquaredIntegrand
          ring
      _ ≤ _ := hdiv
  · have hc : c = 0 :=
      variableOuterCutoff_eq_zero_of_bad_endpoint m hr hR hQ hlog2
    have hsq0 : 0 ≤
        BoundedGaps.Maynard.maynardS2CoordinateFiberSum
          (primorialShifts K) R (primorial D)
          (BoundedGaps.Maynard.maynardYValue (primorialShifts K) R
            (primorial D) (primorialShiftsCandidate K A)) m r ^ 2 / g :=
      div_nonneg (sq_nonneg _) hg.le
    have hweight : 0 ≤ BoundedGaps.Maynard.outerTupleWeight
        (Erdos6.Maynard.tupleOffFace (primorialShifts K) m)
        (primorial D) u := Erdos6.Maynard.outerTupleWeight_nonneg _ _ _
    have heta : 0 ≤ eta :=
      Erdos6.Maynard.largeFiberRelativeError_nonneg hK₀ hC₀ (by omega) hlogR
    have herr0 : 0 ≤ 2 * eta + eta ^ 2 := by nlinarith [sq_nonneg eta]
    have hd0 : 0 ≤ variableOuterContinuousDensity K A point := by
      rw [← hdensity]
      exact sq_nonneg _
    have hs0 : 0 ≤ BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 :=
      sq_nonneg _
    have hL0 : 0 ≤ L ^ 2 := sq_nonneg _
    rw [hcut] at hc
    unfold variableOuterSquaredIntegrand
    rw [hc]
    norm_num
    have hnonpos := (mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg hs0 hL0) hweight)
      (neg_nonpos.mpr (mul_nonneg herr0 hd0))).trans hsq0
    simpa [L, g, eta, point, r, mul_assoc, mul_left_comm, mul_comm] using hnonpos

theorem variableCoordinateFiberSquareDiagonal_lower
    {K : ℕ} {A K₀ C₀ : ℝ}
    (hK : 0 < K) (hA : 0 < A) (hK₀ : 0 < K₀) (hC₀ : 0 ≤ C₀)
    (hAbel : ∀ {D R : ℕ} (m : ↑(primorialShifts K))
        (r : ↑(primorialShifts K) → ℕ),
      BoundedGaps.Maynard.IsMaynardDivisorTuple
          (primorialShifts K) R (primorial D) r →
      1 ≤ D → 2 ≤ Real.log R →
      1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
        (BoundedGaps.Maynard.maynardS2OffCoordinateProduct
          (primorialShifts K) m r) →
      |variableFiberScalarSum K A R (primorial D) m r -
        BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r *
          Real.log R * variableFiberEndpointIntegral K A R m r| ≤
        2 * Erdos6.Maynard.largeFiberAbelEnvelope K₀ C₀ D R m r)
    {alpha : ℝ} {N : ℕ} (m : ↑(primorialShifts K))
    (hD : 2 ≤ BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (hlogR : 2 ≤ Real.log
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N))
    (hlog2 : Real.log 2 / Real.log
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) ≤ (1 : ℝ) / 4)
    (hlog3 : Real.log 3 / Real.log
      (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) ≤ (1 : ℝ) / 4) :
    let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
    let R := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N
    let eta := Erdos6.Maynard.largeFiberRelativeError K₀ C₀ D R
    BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 * Real.log R ^ 2 *
        (variableQuarterMass K A ^ 2 *
            Erdos6.Maynard.tupleOuterMaynardWeightedMoment
              (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) alpha
              (variableOuterSquaredIntegrand K A) N -
          (2 * eta + eta ^ 2) *
            Erdos6.Maynard.tupleOuterMaynardWeightedMoment
              (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) alpha
              (variableOuterContinuousDensity K A) N) ≤
      variableCoordinateFiberSquareDiagonal K A alpha N m := by
  dsimp only
  let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let R := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N
  let eta := Erdos6.Maynard.largeFiberRelativeError K₀ C₀ D R
  let P := BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 *
    Real.log R ^ 2
  let S := BoundedGaps.Maynard.maynardDivisorTupleSupport
    (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) R (primorial D)
  have hpoint : ∀ u : Erdos6.Maynard.tupleOffFace
      (primorialShifts K) m → ℕ,
      Erdos6.Maynard.tupleNormalizedLogPoint
          (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) alpha N u =
        fun h : Erdos6.Maynard.tupleOffFace (primorialShifts K) m =>
          Real.log (u h) / Real.log R := by
    intro u
    rfl
  have hsum :
      ∑ u ∈ S,
        P * (BoundedGaps.Maynard.outerTupleWeight
          (Erdos6.Maynard.tupleOffFace (primorialShifts K) m)
          (primorial D) u *
        (variableQuarterMass K A ^ 2 *
            variableOuterSquaredIntegrand K A
              (Erdos6.Maynard.tupleNormalizedLogPoint
                (Erdos6.Maynard.tupleOffFace (primorialShifts K) m)
                alpha N u) -
          (2 * eta + eta ^ 2) *
            variableOuterContinuousDensity K A
              (Erdos6.Maynard.tupleNormalizedLogPoint
                (Erdos6.Maynard.tupleOffFace (primorialShifts K) m)
                alpha N u))) ≤
      ∑ u ∈ S,
        BoundedGaps.Maynard.maynardS2CoordinateFiberSum
            (primorialShifts K) R (primorial D)
            (BoundedGaps.Maynard.maynardYValue (primorialShifts K) R
              (primorial D) (primorialShiftsCandidate K A)) m
              (Erdos6.Maynard.tupleOffFaceExtension m u) ^ 2 /
          ∏ h : ↑(primorialShifts K),
            (BoundedGaps.Maynard.maynardS2G
              (Erdos6.Maynard.tupleOffFaceExtension m u h) : ℝ) := by
    apply Finset.sum_le_sum
    intro u hu
    have ht := variableCoordinateFiberTerm_lower hK hA hK₀ hC₀
      (fun m r => hAbel m r) m u hu hD hlogR hlog2 hlog3
    simpa [P, D, R, eta, hpoint u] using ht
  have hreindex := Erdos6.Maynard.sum_coordinateOneSupport_eq_offFace
    R (primorial D) m
    (fun r =>
      BoundedGaps.Maynard.maynardS2CoordinateFiberSum
          (primorialShifts K) R (primorial D)
          (BoundedGaps.Maynard.maynardYValue (primorialShifts K) R
            (primorial D) (primorialShiftsCandidate K A)) m r ^ 2 /
        ∏ h : ↑(primorialShifts K),
          (BoundedGaps.Maynard.maynardS2G (r h) : ℝ))
  have hright :
      (∑ u ∈ S,
        BoundedGaps.Maynard.maynardS2CoordinateFiberSum
            (primorialShifts K) R (primorial D)
            (BoundedGaps.Maynard.maynardYValue (primorialShifts K) R
              (primorial D) (primorialShiftsCandidate K A)) m
              (Erdos6.Maynard.tupleOffFaceExtension m u) ^ 2 /
          ∏ h : ↑(primorialShifts K),
            (BoundedGaps.Maynard.maynardS2G
              (Erdos6.Maynard.tupleOffFaceExtension m u h) : ℝ)) =
        variableCoordinateFiberSquareDiagonal K A alpha N m := by
    unfold variableCoordinateFiberSquareDiagonal
    simpa [S, D, R, Erdos6.Maynard.maynardModulus,
      BoundedGaps.Maynard.engelsmaMaynardModulus] using hreindex.symm
  rw [hright] at hsum
  have hleft :
      (∑ u ∈ S,
        P * (BoundedGaps.Maynard.outerTupleWeight
          (Erdos6.Maynard.tupleOffFace (primorialShifts K) m)
          (primorial D) u *
        (variableQuarterMass K A ^ 2 *
            variableOuterSquaredIntegrand K A
              (Erdos6.Maynard.tupleNormalizedLogPoint
                (Erdos6.Maynard.tupleOffFace (primorialShifts K) m)
                alpha N u) -
          (2 * eta + eta ^ 2) *
            variableOuterContinuousDensity K A
              (Erdos6.Maynard.tupleNormalizedLogPoint
                (Erdos6.Maynard.tupleOffFace (primorialShifts K) m)
                alpha N u)))) =
      P * (variableQuarterMass K A ^ 2 *
          Erdos6.Maynard.tupleOuterMaynardWeightedMoment
            (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) alpha
            (variableOuterSquaredIntegrand K A) N -
        (2 * eta + eta ^ 2) *
          Erdos6.Maynard.tupleOuterMaynardWeightedMoment
            (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) alpha
            (variableOuterContinuousDensity K A) N) := by
    unfold Erdos6.Maynard.tupleOuterMaynardWeightedMoment
    dsimp [S, D, R]
    simp only [BoundedGaps.Maynard.engelsmaMaynardModulus]
    simp only [mul_sub, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    ring
  rw [hleft] at hsum
  simpa [P, D, R, eta] using hsum

theorem fintype_card_tupleOffFace_primorialShifts
    {K : ℕ} (m : ↑(primorialShifts K)) :
    Fintype.card (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) =
      K - 1 := by
  rw [Fintype.card_coe]
  unfold Erdos6.Maynard.tupleOffFace
  rw [Finset.card_erase_of_mem m.2, card_primorialShifts]

theorem variableOuterContinuousDensity_eq_productDensity
    {K : ℕ} {A : ℝ} {ι : Type*} [Fintype ι] (t : ι → ℝ)
    (ht : t ∈ BoundedGaps.Maynard.maynardCubeOf ι) :
    variableOuterContinuousDensity K A t =
      VariableMaynard.productDensity K A t := by
  unfold variableOuterContinuousDensity VariableMaynard.productDensity
    VariableMaynard.squareDensity
  apply Finset.prod_congr rfl
  intro i hi
  have hx : 0 ≤ (K : ℝ) * t i :=
    mul_nonneg (Nat.cast_nonneg _) (ht i (Set.mem_univ i)).1
  rw [variableContinuousFactor_eq_factor hx]

theorem variableOuterSquaredIntegrand_eq_productDensity_of_good
    {K : ℕ} {A : ℝ} {ι : Type*} [Fintype ι]
    {t : ι → ℝ} (ht : t ∈ VariableMaynard.goodRegion ι) :
    variableOuterSquaredIntegrand K A t =
      VariableMaynard.productDensity K A t := by
  unfold variableOuterSquaredIntegrand
  rw [variableOuterCutoff_eq_one ht.2,
    variableOuterContinuousDensity_eq_productDensity _ ht.1]
  norm_num

theorem variableGoodRegion_subset_finiteSimplex
    (H : Finset ℕ) :
    VariableMaynard.goodRegion H ⊆
      BoundedGaps.Maynard.finiteSimplexOf H := by
  intro t ht
  refine ⟨ht.1, ?_⟩
  exact ht.2.trans (by norm_num)

theorem variableGood_productDensity_integral_gt_half
    {K : ℕ} {A : ℝ} (hK2 : 2 ≤ K) (hA : 0 < A)
    (hmoment : VariableMaynard.firstMoment K A <
      (1 / (4 * (K : ℝ))) * VariableMaynard.baseMass K A)
    (ι : Type*) [Fintype ι] (hcard : Fintype.card ι = K - 1) :
    (1 / 2 : ℝ) * VariableMaynard.baseMass K A ^ (K - 1) <
      ∫ t : ι → ℝ in VariableMaynard.goodRegion ι,
        VariableMaynard.productDensity K A t := by
  have hbound := VariableMaynard.badRegion_productDensity_integral_le
    (K := K) (A := A) (by omega : 0 < K) hA ι
  rw [hcard] at hbound
  have hbad := hbound.trans_lt
    (VariableMaynard.weighted_bad_bound_lt_half hK2
      (VariableMaynard.baseMass_pos (by omega) hA) hmoment)
  have hsubset := VariableMaynard.goodRegion_subset_cube ι
  have hsplit := setIntegral_sdiff
    (VariableMaynard.goodRegion_measurable ι)
    (VariableMaynard.productDensity_integrableOn_cube K A hA ι) hsubset
  have htotal := VariableMaynard.integral_product_squareDensity_cube
    (K := K) (A := A) (by omega : 0 < K) hA ι
  change (∫ t : ι → ℝ in BoundedGaps.Maynard.maynardCubeOf ι,
    VariableMaynard.productDensity K A t) = _ at htotal
  rw [hcard] at htotal
  rw [htotal] at hsplit
  have hbase : 0 < VariableMaynard.baseMass K A :=
    VariableMaynard.baseMass_pos (by omega) hA
  have hpow : 0 < VariableMaynard.baseMass K A ^ (K - 1) :=
    pow_pos hbase _
  linarith

theorem integral_variableOuterSquaredIntegrand_gt_half
    {K : ℕ} {A : ℝ} (hK2 : 2 ≤ K) (hA : 0 < A)
    (hmoment : VariableMaynard.firstMoment K A <
      (1 / (4 * (K : ℝ))) * VariableMaynard.baseMass K A)
    (H : Finset ℕ) (hcard : Fintype.card H = K - 1) :
    (1 / 2 : ℝ) * VariableMaynard.baseMass K A ^ (K - 1) <
      ∫ t : H → ℝ in BoundedGaps.Maynard.finiteSimplexOf H,
        variableOuterSquaredIntegrand K A t := by
  have hgood := variableGood_productDensity_integral_gt_half
    hK2 hA hmoment H hcard
  have heq :
      (∫ t : H → ℝ in VariableMaynard.goodRegion H,
        variableOuterSquaredIntegrand K A t) =
      ∫ t : H → ℝ in VariableMaynard.goodRegion H,
        VariableMaynard.productDensity K A t := by
    apply setIntegral_congr_fun (VariableMaynard.goodRegion_measurable H)
    intro t ht
    exact variableOuterSquaredIntegrand_eq_productDensity_of_good ht
  have hint : IntegrableOn
      (variableOuterSquaredIntegrand K A : (H → ℝ) → ℝ)
      (BoundedGaps.Maynard.finiteSimplexOf H) :=
    (continuous_variableOuterSquaredIntegrand hA H).continuousOn.integrableOn_compact
      (BoundedGaps.Maynard.isCompact_finiteSimplexOf H)
  have hmono :
      (∫ t : H → ℝ in VariableMaynard.goodRegion H,
        variableOuterSquaredIntegrand K A t) ≤
      ∫ t : H → ℝ in BoundedGaps.Maynard.finiteSimplexOf H,
        variableOuterSquaredIntegrand K A t := by
    apply setIntegral_mono_set hint
    · exact (ae_restrict_mem
        (BoundedGaps.Maynard.isCompact_finiteSimplexOf H).measurableSet).mono
          (fun t ht => (variableOuterSquaredIntegrand_bounds hA t ht.1).1)
    · exact Filter.Eventually.of_forall fun t ht =>
        variableGoodRegion_subset_finiteSimplex H ht
  rw [heq] at hmono
  exact hgood.trans_le hmono

theorem tendsto_normalizedVariableOuterSquaredMoment
    {K : ℕ} (hK2 : 2 ≤ K) {A alpha : ℝ}
    (hA : 0 < A) (halpha : 0 < alpha)
    (m : ↑(primorialShifts K)) :
    Tendsto (fun N : ℕ =>
      Erdos6.Maynard.normalizedTupleOuterMaynardWeightedMoment
        (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) alpha
        (variableOuterSquaredIntegrand K A) N) atTop
      (nhds (∫ t in BoundedGaps.Maynard.finiteSimplexOf
          (Erdos6.Maynard.tupleOffFace (primorialShifts K) m),
        variableOuterSquaredIntegrand K A t)) := by
  have hcard := fintype_card_tupleOffFace_primorialShifts m
  have h0card : 0 < Fintype.card
      (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) := by
    rw [hcard]
    omega
  let h0 : Erdos6.Maynard.tupleOffFace (primorialShifts K) m :=
    Classical.choice (Fintype.card_pos_iff.mp h0card)
  exact Erdos6.Maynard.tendsto_normalizedTupleOuterMaynardWeightedMoment
    h0 halpha (continuous_variableOuterSquaredIntegrand hA _)
      (fun x hx => variableOuterSquaredIntegrand_bounds hA x hx.1)

theorem tendsto_normalizedVariableOuterDensityMoment
    {K : ℕ} (hK2 : 2 ≤ K) {A alpha : ℝ}
    (hA : 0 < A) (halpha : 0 < alpha)
    (m : ↑(primorialShifts K)) :
    Tendsto (fun N : ℕ =>
      Erdos6.Maynard.normalizedTupleOuterMaynardWeightedMoment
        (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) alpha
        (variableOuterContinuousDensity K A) N) atTop
      (nhds (∫ t in BoundedGaps.Maynard.finiteSimplexOf
          (Erdos6.Maynard.tupleOffFace (primorialShifts K) m),
        variableOuterContinuousDensity K A t)) := by
  have hcard := fintype_card_tupleOffFace_primorialShifts m
  have h0card : 0 < Fintype.card
      (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) := by
    rw [hcard]
    omega
  let h0 : Erdos6.Maynard.tupleOffFace (primorialShifts K) m :=
    Classical.choice (Fintype.card_pos_iff.mp h0card)
  exact Erdos6.Maynard.tendsto_normalizedTupleOuterMaynardWeightedMoment
    h0 halpha (continuous_variableOuterContinuousDensity hA _)
      (fun x hx => variableOuterContinuousDensity_bounds
        (K := K) hA x hx.1)

noncomputable def variableFiberLowerCoefficient
    (K : ℕ) (A : ℝ) : ℝ :=
  variableQuarterMass K A ^ 2 *
    ((1 : ℝ) / 2 * VariableMaynard.baseMass K A ^ (K - 1))

theorem variableFiberLowerCoefficient_pos
    {K : ℕ} {A : ℝ} (hK : 0 < K) (hA : 0 < A) :
    0 < variableFiberLowerCoefficient K A := by
  unfold variableFiberLowerCoefficient
  exact mul_pos (sq_pos_of_pos (variableQuarterMass_pos hK hA))
    (mul_pos (by norm_num)
      (pow_pos (VariableMaynard.baseMass_pos hK hA) _))

theorem exists_uniform_variableFiberAbel_bound_KA
    {K : ℕ} {A : ℝ} (hK : 0 < K) (hA : 0 < A) :
    ∃ K₀ C₀ : ℝ, 0 < K₀ ∧ 0 ≤ C₀ ∧
      ∀ {D R : ℕ} (m : ↑(primorialShifts K))
          (r : ↑(primorialShifts K) → ℕ),
        BoundedGaps.Maynard.IsMaynardDivisorTuple
            (primorialShifts K) R (primorial D) r →
        1 ≤ D → 2 ≤ Real.log R →
        1 < BoundedGaps.Maynard.maynardS2CoordinateFiberEndpoint R
          (BoundedGaps.Maynard.maynardS2OffCoordinateProduct
            (primorialShifts K) m r) →
        |variableFiberScalarSum K A R (primorial D) m r -
          BoundedGaps.Maynard.maynardS2CoordinateFiberSingularSeries D m r *
            Real.log R * variableFiberEndpointIntegral K A R m r| ≤
          2 * Erdos6.Maynard.largeFiberAbelEnvelope K₀ C₀ D R m r := by
  have hs : 0 < A * (K : ℝ) := by positivity
  obtain ⟨K₀, C₀, hK₀, hC₀, hbound⟩ :=
    exists_uniform_variableFiberAbel_bound (A * (K : ℝ)) hs
  refine ⟨K₀, C₀, hK₀, hC₀, ?_⟩
  intro D R m r hr hD hlogR hQ
  have hKcast : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
  have hdiv : A * (K : ℝ) / (K : ℝ) = A := by field_simp
  simpa [hdiv] using hbound m r hK hr hD hlogR hQ

theorem eventually_variableCoordinateFiberSquareDiagonal_normalized_gt
    {K : ℕ} (hK2 : 2 ≤ K) {A alpha : ℝ}
    (hA : 0 < A)
    (hmoment : VariableMaynard.firstMoment K A <
      (1 / (4 * (K : ℝ))) * VariableMaynard.baseMass K A)
    (halpha : 0 < alpha) (m : ↑(primorialShifts K)) :
    ∀ᶠ N : ℕ in atTop,
      variableFiberLowerCoefficient K A <
        variableCoordinateFiberSquareDiagonal K A alpha N m /
          (BoundedGaps.Maynard.preSieveSingularSeries
              (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
            Real.log (Erdos6.Maynard.maynardRadius alpha N) ^ 2 *
            Erdos6.Maynard.tupleNaturalScale
              (Erdos6.Maynard.tupleOffFace (primorialShifts K) m)
              alpha N) := by
  obtain ⟨K₀, C₀, hK₀, hC₀, hAbel⟩ :=
    exists_uniform_variableFiberAbel_bound_KA (by omega : 0 < K) hA
  let eta : ℕ → ℝ := fun N => Erdos6.Maynard.largeFiberRelativeError K₀ C₀
    (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
  let MA : ℕ → ℝ := fun N =>
    Erdos6.Maynard.normalizedTupleOuterMaynardWeightedMoment
      (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) alpha
      (variableOuterSquaredIntegrand K A) N
  let MB : ℕ → ℝ := fun N =>
    Erdos6.Maynard.normalizedTupleOuterMaynardWeightedMoment
      (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) alpha
      (variableOuterContinuousDensity K A) N
  let IA := ∫ t in BoundedGaps.Maynard.finiteSimplexOf
      (Erdos6.Maynard.tupleOffFace (primorialShifts K) m),
    variableOuterSquaredIntegrand K A t
  let IB := ∫ t in BoundedGaps.Maynard.finiteSimplexOf
      (Erdos6.Maynard.tupleOffFace (primorialShifts K) m),
    variableOuterContinuousDensity K A t
  have heta : Tendsto eta atTop (nhds 0) := by
    simpa [eta] using Erdos6.Maynard.tendsto_largeFiberRelativeError_zero
      halpha K₀ C₀
  have hMA : Tendsto MA atTop (nhds IA) := by
    simpa [MA, IA] using
      tendsto_normalizedVariableOuterSquaredMoment hK2 hA halpha m
  have hMB : Tendsto MB atTop (nhds IB) := by
    simpa [MB, IB] using
      tendsto_normalizedVariableOuterDensityMoment hK2 hA halpha m
  have herr : Tendsto (fun N : ℕ => (2 * eta N + eta N ^ 2) * MB N)
      atTop (nhds 0) := by
    have he : Tendsto (fun N : ℕ => 2 * eta N + eta N ^ 2)
        atTop (nhds 0) := by
      convert (heta.const_mul 2).add (heta.pow 2) using 1 <;> norm_num
    simpa using he.mul hMB
  have hbracket : Tendsto (fun N : ℕ =>
      variableQuarterMass K A ^ 2 * MA N -
        (2 * eta N + eta N ^ 2) * MB N)
      atTop (nhds (variableQuarterMass K A ^ 2 * IA)) := by
    simpa using (hMA.const_mul (variableQuarterMass K A ^ 2)).sub herr
  have hlimit : variableFiberLowerCoefficient K A <
      variableQuarterMass K A ^ 2 * IA := by
    unfold variableFiberLowerCoefficient IA
    exact mul_lt_mul_of_pos_left
      (integral_variableOuterSquaredIntegrand_gt_half hK2 hA hmoment _
        (fintype_card_tupleOffFace_primorialShifts m))
      (sq_pos_of_pos (variableQuarterMass_pos (by omega) hA))
  have hbracketEventually := hbracket.eventually (eventually_gt_nhds hlimit)
  have hconditions := Erdos6.Maynard.eventually_largeFiber_conditions halpha
  have houterScale := Erdos6.Maynard.eventually_tupleNaturalScale_pos
    (H := Erdos6.Maynard.tupleOffFace (primorialShifts K) m) halpha
  filter_upwards [hbracketEventually, hconditions, houterScale] with
      N hbracketN hcond hscale
  let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let R := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N
  let P := BoundedGaps.Maynard.preSieveSingularSeries D ^ 2 *
    Real.log R ^ 2
  have hP : 0 < P := by
    dsimp [P]
    have hS := BoundedGaps.Maynard.preSieveSingularSeries_pos D
    have hL : 0 < Real.log R := by linarith [hcond.2.1]
    exact mul_pos (sq_pos_of_pos hS) (sq_pos_of_pos hL)
  have hfinite := variableCoordinateFiberSquareDiagonal_lower
    (by omega : 0 < K) hA hK₀ hC₀ hAbel m hcond.1 hcond.2.1
      (hcond.2.2.1.trans (by norm_num))
      (hcond.2.2.2.trans (by norm_num))
  have hdiv := div_le_div_of_nonneg_right hfinite
    (mul_nonneg hP.le hscale.le)
  have heq :
      P * (variableQuarterMass K A ^ 2 *
            Erdos6.Maynard.tupleOuterMaynardWeightedMoment
              (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) alpha
              (variableOuterSquaredIntegrand K A) N -
          (2 * eta N + eta N ^ 2) *
            Erdos6.Maynard.tupleOuterMaynardWeightedMoment
              (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) alpha
              (variableOuterContinuousDensity K A) N) /
          (P * Erdos6.Maynard.tupleNaturalScale
            (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) alpha N) =
        variableQuarterMass K A ^ 2 * MA N -
          (2 * eta N + eta N ^ 2) * MB N := by
    dsimp [MA, MB]
    unfold Erdos6.Maynard.normalizedTupleOuterMaynardWeightedMoment
    field_simp [hP.ne', hscale.ne']
  change P * (variableQuarterMass K A ^ 2 *
            Erdos6.Maynard.tupleOuterMaynardWeightedMoment
              (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) alpha
              (variableOuterSquaredIntegrand K A) N -
          (2 * eta N + eta N ^ 2) *
            Erdos6.Maynard.tupleOuterMaynardWeightedMoment
              (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) alpha
              (variableOuterContinuousDensity K A) N) /
          (P * Erdos6.Maynard.tupleNaturalScale
            (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) alpha N) ≤
        variableCoordinateFiberSquareDiagonal K A alpha N m /
          (P * Erdos6.Maynard.tupleNaturalScale
            (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) alpha N)
      at hdiv
  rw [heq] at hdiv
  exact hbracketN.trans_le (by
    simpa [D, R, P, eta] using hdiv)

theorem abs_tupleCoordinateOneYDiagonal_sub_variableFiberDiagonal_le
    {K N : ℕ} {A alpha : ℝ} (hA : 0 < A)
    (m : ↑(primorialShifts K))
    (hD : 0 < BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (hWL : (Erdos6.Maynard.maynardModulus N : ℝ) ≤
      1 + Real.log (Erdos6.Maynard.maynardRadius alpha N)) :
    |Erdos6.Maynard.tupleCoordinateOneYDiagonal
          (primorialShifts K) alpha (primorialShiftsCandidate K A) N m -
        variableCoordinateFiberSquareDiagonal K A alpha N m| ≤
      Erdos6.Maynard.tupleCoordinateOneSquarePerturbation
        (primorialShifts K) alpha N m := by
  let H := primorialShifts K
  let R := Erdos6.Maynard.maynardRadius alpha N
  let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let W := primorial D
  let y := BoundedGaps.Maynard.maynardYValue H R W
    (primorialShiftsCandidate K A)
  have hy : BoundedGaps.Maynard.IsSupportedMaynardY H R W y :=
    BoundedGaps.Maynard.isSupportedMaynardY_maynardYValue _ _ _ _
  have hyBound : ∀ r, |y r| ≤ (1 : ℝ) := by
    intro r
    exact BoundedGaps.Maynard.abs_maynardYValue_le H R W
      (primorialShiftsCandidate K A) (by norm_num)
      (primorialShiftsCandidate_abs_le_one hA) r
  have hD' : 0 < D := by simpa [D] using hD
  have hWL' : (W : ℝ) ≤ 1 + Real.log R := by
    simpa [W, R, D, Erdos6.Maynard.maynardModulus,
      BoundedGaps.Maynard.engelsmaMaynardModulus] using hWL
  have hsum := Erdos6.Maynard.abs_tupleRestrictedYSum_sub_fiberSum_le
    hy m hD' hWL' (B := (1 : ℝ)) (by norm_num) hyBound
  rw [Erdos6.Maynard.tupleCoordinateOneYDiagonal_eq_explicit]
  unfold variableCoordinateFiberSquareDiagonal
    Erdos6.Maynard.tupleCoordinateOneSquarePerturbation
  simpa only [H, R, D, W, y, Erdos6.Maynard.maynardRadius,
    Erdos6.Maynard.maynardModulus,
    BoundedGaps.Maynard.engelsmaMaynardModulus] using hsum

theorem eventually_variableCoordinateOneYDiagonal_normalized_gt
    {K : ℕ} (hK2 : 2 ≤ K) {A alpha c : ℝ}
    (hA : 0 < A)
    (hmoment : VariableMaynard.firstMoment K A <
      (1 / (4 * (K : ℝ))) * VariableMaynard.baseMass K A)
    (halpha : 0 < alpha) (m : ↑(primorialShifts K))
    (hc : c < variableFiberLowerCoefficient K A) :
    ∀ᶠ N : ℕ in atTop,
      c < Erdos6.Maynard.tupleCoordinateOneYDiagonal
          (primorialShifts K) alpha (primorialShiftsCandidate K A) N m /
        (BoundedGaps.Maynard.preSieveSingularSeries
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
          Real.log (Erdos6.Maynard.maynardRadius alpha N) ^ 2 *
          Erdos6.Maynard.tupleNaturalScale
            (Erdos6.Maynard.tupleOffFace (primorialShifts K) m)
            alpha N) := by
  let scale : ℕ → ℝ := fun N =>
    BoundedGaps.Maynard.preSieveSingularSeries
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
      Real.log (Erdos6.Maynard.maynardRadius alpha N) ^ 2 *
      Erdos6.Maynard.tupleNaturalScale
        (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) alpha N
  have hfiber := eventually_variableCoordinateFiberSquareDiagonal_normalized_gt
    hK2 hA hmoment halpha m
  have hpert :=
    Erdos6.Maynard.tendsto_normalizedTupleCoordinateOneSquarePerturbation_zero
      (H := primorialShifts K) halpha m
  have hgap : 0 < variableFiberLowerCoefficient K A - c := sub_pos.mpr hc
  have hpertSmall : ∀ᶠ N : ℕ in atTop,
      Erdos6.Maynard.tupleCoordinateOneSquarePerturbation
          (primorialShifts K) alpha N m / scale N <
        variableFiberLowerCoefficient K A - c := by
    have he := hpert.eventually (eventually_lt_nhds hgap)
    simpa [scale] using he
  have hcond :=
    BoundedGaps.Maynard.eventually_engelsmaMaynardCrossBound_conditions halpha
  have hRone :=
    BoundedGaps.Maynard.eventually_one_lt_engelsmaMaynardRadius halpha
  have houter := Erdos6.Maynard.eventually_tupleNaturalScale_pos
    (H := Erdos6.Maynard.tupleOffFace (primorialShifts K) m) halpha
  filter_upwards [hfiber, hpertSmall, hcond, hRone, houter] with
      N hfiberN hpertN hcondN hRoneN houterN
  have hlog : 0 < Real.log (Erdos6.Maynard.maynardRadius alpha N) :=
    Real.log_pos (by exact_mod_cast hRoneN)
  have hpre : 0 < BoundedGaps.Maynard.preSieveSingularSeries
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) :=
    BoundedGaps.Maynard.preSieveSingularSeries_pos _
  have hscale : 0 < scale N := by
    dsimp [scale]
    exact mul_pos (mul_pos (sq_pos_of_pos hpre) (sq_pos_of_pos hlog)) houterN
  have hbridge :=
    abs_tupleCoordinateOneYDiagonal_sub_variableFiberDiagonal_le
      hA m hcondN.2.1 hcondN.2.2
  have hlower :
      variableCoordinateFiberSquareDiagonal K A alpha N m -
          Erdos6.Maynard.tupleCoordinateOneSquarePerturbation
            (primorialShifts K) alpha N m ≤
        Erdos6.Maynard.tupleCoordinateOneYDiagonal
          (primorialShifts K) alpha (primorialShiftsCandidate K A) N m := by
    have hn := neg_le_of_abs_le hbridge
    linarith
  have hdiv := div_le_div_of_nonneg_right hlower hscale.le
  have hfiberN' : variableFiberLowerCoefficient K A <
      variableCoordinateFiberSquareDiagonal K A alpha N m / scale N := by
    simpa [scale] using hfiberN
  have htarget : c <
      Erdos6.Maynard.tupleCoordinateOneYDiagonal
          (primorialShifts K) alpha (primorialShiftsCandidate K A) N m /
        scale N := by
    rw [sub_div] at hdiv
    linarith
  simpa [scale] using htarget

theorem abs_tupleRestrictedY_le_transformEnvelope_of_abs_le_one
    {H : Finset ℕ} {alpha : ℝ} {N : ℕ}
    (F : (H → ℝ) → ℝ) (hF : ∀ t, |F t| ≤ 1)
    (m : H) {r : H → ℕ}
    (hD : 0 < BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (hWL : (Erdos6.Maynard.maynardModulus N : ℝ) ≤
      1 + Real.log (Erdos6.Maynard.maynardRadius alpha N))
    (hr : BoundedGaps.Maynard.IsMaynardDivisorTuple H
      (Erdos6.Maynard.maynardRadius alpha N)
      (Erdos6.Maynard.maynardModulus N) r)
    (hrm : r m = 1) :
    |BoundedGaps.Maynard.maynardS2RestrictedYFromCoefficients H
        (BoundedGaps.Maynard.maynardDivisorTupleSupport H
          (Erdos6.Maynard.maynardRadius alpha N)
          (Erdos6.Maynard.maynardModulus N))
        (BoundedGaps.Maynard.maynardCoefficientFromY H
          (Erdos6.Maynard.maynardRadius alpha N)
          (Erdos6.Maynard.maynardModulus N)
          (BoundedGaps.Maynard.maynardYValue H
            (Erdos6.Maynard.maynardRadius alpha N)
            (Erdos6.Maynard.maynardModulus N) F)) m r| ≤
      Erdos6.Maynard.tupleRestrictedTransformEnvelope H alpha N m := by
  have h := BoundedGaps.Maynard.abs_maynardS2RestrictedY_le_log
    (BoundedGaps.Maynard.isSupportedMaynardY_maynardYValue H
      (Erdos6.Maynard.maynardRadius alpha N)
      (Erdos6.Maynard.maynardModulus N) F)
    m hD hWL hr hrm (show (0 : ℝ) ≤ 1 by norm_num)
    (fun u => BoundedGaps.Maynard.abs_maynardYValue_le H
      (Erdos6.Maynard.maynardRadius alpha N)
      (Erdos6.Maynard.maynardModulus N) F
      (by norm_num) hF u)
  simpa [Erdos6.Maynard.tupleRestrictedTransformEnvelope,
    Erdos6.Maynard.maynardModulus,
    BoundedGaps.Maynard.engelsmaMaynardModulus] using h

theorem abs_tupleRestrictedCross_le_explicit_of_abs_le_one
    {H : Finset ℕ} {alpha : ℝ} {N : ℕ}
    (F : (H → ℝ) → ℝ) (hF : ∀ t, |F t| ≤ 1)
    (m : H)
    (hR : 1 < Erdos6.Maynard.maynardRadius alpha N)
    (hD : 2 ≤ BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    (hWL : (Erdos6.Maynard.maynardModulus N : ℝ) ≤
      1 + Real.log (Erdos6.Maynard.maynardRadius alpha N)) :
    |Erdos6.Maynard.tupleRestrictedCross H alpha F N m| ≤
      Erdos6.Maynard.tupleRestrictedTransformEnvelope H alpha N m ^ 2 *
        ((32 * Real.exp 32 /
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1) : ℝ)) *
          ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
          (Real.exp 32) ^
            ((BoundedGaps.Maynard.offDiagonalPairs H).card - 1)) *
        (BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeMean
          (Erdos6.Maynard.maynardModulus N)
          (Erdos6.Maynard.maynardRadius alpha N)) ^
            (Finset.univ.erase m).card := by
  let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let R := Erdos6.Maynard.maynardRadius alpha N
  let W := Erdos6.Maynard.maynardModulus N
  let y := BoundedGaps.Maynard.maynardYValue H R W F
  let E := Erdos6.Maynard.tupleRestrictedTransformEnvelope H alpha N m
  let T := BoundedGaps.Maynard.roughS2CrossTupleReciprocalGSquareTail H D R
  let M := BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeMean W R
  have hcoeff : Erdos6.Maynard.tupleMaynardCoefficient H alpha F N =
      BoundedGaps.Maynard.maynardCoefficientFromY H R W y := by
    funext d
    exact BoundedGaps.Maynard.maynardCoefficient_eq_fromYValue _ _ _ _ d
  have hbase : |Erdos6.Maynard.tupleRestrictedCross H alpha F N m| ≤
      E ^ 2 * T *
        BoundedGaps.Maynard.restrictedS2CommonReciprocalGMass H W R m := by
    unfold Erdos6.Maynard.tupleRestrictedCross
    rw [hcoeff]
    apply BoundedGaps.Maynard.abs_incompatibleRestrictedS2_le_crossTail_mul_commonMass
      hR hD (Erdos6.Maynard.tupleRestrictedTransformEnvelope_nonneg
        (Nat.zero_lt_of_lt hD) hWL)
    intro r hr hrm
    exact abs_tupleRestrictedY_le_transformEnvelope_of_abs_le_one
      F hF m (Nat.zero_lt_of_lt hD) hWL hr hrm
  have htail0 : 0 ≤ T := by
    unfold T BoundedGaps.Maynard.roughS2CrossTupleReciprocalGSquareTail
    exact Finset.sum_nonneg fun s hs => by
      unfold BoundedGaps.Maynard.roughS2CrossTupleReciprocalGSquareWeight
      exact Finset.prod_nonneg fun x hx =>
        Finset.prod_nonneg fun p hp =>
          BoundedGaps.Maynard.maynardS2CrossPrimeSquareWeight_nonneg p
  have hM0 : 0 ≤ M := by
    unfold M BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeMean
    exact Finset.sum_nonneg fun n hn =>
      Erdos6.Maynard.tupleReciprocalGSquarefreeAF_nonneg _ n
  have hmass := BoundedGaps.Maynard.restrictedS2CommonReciprocalGMass_le
    (H := H) (W := W) (R := R) (m := m)
  have htail := BoundedGaps.Maynard.roughS2CrossTupleReciprocalGSquareTail_le
    (H := H) (Q := R) hD
  calc
    _ ≤ E ^ 2 * T *
        BoundedGaps.Maynard.restrictedS2CommonReciprocalGMass H W R m := hbase
    _ ≤ E ^ 2 * T * M ^ (Finset.univ.erase m).card :=
      mul_le_mul_of_nonneg_left hmass (mul_nonneg (sq_nonneg _) htail0)
    _ ≤ E ^ 2 *
        ((32 * Real.exp 32 / (D : ℝ)) *
          ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
          (Real.exp 32) ^
            ((BoundedGaps.Maynard.offDiagonalPairs H).card - 1)) *
          M ^ (Finset.univ.erase m).card :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left htail (sq_nonneg _))
        (pow_nonneg hM0 _)
    _ = _ := by rfl

theorem tendsto_normalizedTupleRestrictedCross_zero_of_abs_le_one
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    (F : (H → ℝ) → ℝ) (hF : ∀ t, |F t| ≤ 1) (m : H) :
    Tendsto (fun N : ℕ =>
      Erdos6.Maynard.tupleRestrictedCross H alpha F N m /
        (BoundedGaps.Maynard.preSieveSingularSeries
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
          Real.log (Erdos6.Maynard.maynardRadius alpha N) ^ 2 *
          Erdos6.Maynard.tupleNaturalScale
            (Erdos6.Maynard.tupleOffFace H m) alpha N))
      atTop (nhds 0) := by
  let D : ℕ → ℕ := fun N =>
    BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let R : ℕ → ℕ := fun N => Erdos6.Maynard.maynardRadius alpha N
  let L : ℕ → ℝ := fun N => Real.log (R N)
  let S : ℕ → ℝ := fun N =>
    BoundedGaps.Maynard.preSieveSingularSeries (D N)
  let Q : ℕ → ℝ := fun N => S N * L N
  let M : ℕ → ℝ := fun N =>
    BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeMean
      (Erdos6.Maynard.maynardModulus N) (R N)
  let k := (Finset.univ.erase m).card
  let Aenv : ℕ → ℝ := fun N =>
    8 / (D N : ℝ) + (8 * Real.exp 8 / (D N : ℝ)) *
      (1 + 8 * Real.exp 8 / (D N : ℝ)) ^ (k - 1)
  let E : ℕ → ℝ := fun N =>
    Erdos6.Maynard.tupleRestrictedTransformEnvelope H alpha N m
  let Tail : ℕ → ℝ := fun N =>
    (32 * Real.exp 32 / (D N : ℝ)) *
      ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
      (Real.exp 32) ^
        ((BoundedGaps.Maynard.offDiagonalPairs H).card - 1)
  let Ctail : ℝ := 32 * Real.exp 32 *
    ((BoundedGaps.Maynard.offDiagonalPairs H).card : ℝ) *
    (Real.exp 32) ^
      ((BoundedGaps.Maynard.offDiagonalPairs H).card - 1)
  let Cenv : ℝ := 16 * (1 + (k : ℝ))
  have hDtop : Tendsto (fun N => (D N : ℝ)) atTop atTop := by
    dsimp [D]
    exact tendsto_natCast_atTop_atTop.comp
      BoundedGaps.Maynard.tendsto_shifted_tripleLogCutoff
  have hinvD : Tendsto (fun N => (1 : ℝ) / D N) atTop (nhds 0) := by
    simpa [one_div] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
        atTop (nhds 1)).div_atTop hDtop)
  have hterm : Tendsto (fun N => 8 * Real.exp 8 / D N)
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hinvD.const_mul (8 * Real.exp 8)
  have hpow : Tendsto (fun N =>
      (1 + 8 * Real.exp 8 / D N) ^ (k - 1)) atTop (nhds 1) := by
    simpa [add_comm] using (hterm.add_const 1).pow (k - 1)
  have hAenv : Tendsto Aenv atTop (nhds 0) := by
    have hfirst : Tendsto (fun N => (8 : ℝ) / D N)
        atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using hinvD.const_mul 8
    have hsecond := hterm.mul hpow
    simpa [Aenv] using hfirst.add hsecond
  have hAsmall : ∀ᶠ N : ℕ in atTop,
      0 ≤ Aenv N ∧ Aenv N ≤ 1 := by
    filter_upwards [hAenv.eventually
      (Metric.ball_mem_nhds (0 : ℝ) one_pos),
      hDtop.eventually (eventually_gt_atTop 0)] with N hN hDN
    have h0 : 0 ≤ Aenv N := by dsimp [Aenv]; positivity
    exact ⟨h0, le_of_lt (by
      simpa [Real.dist_eq, abs_of_nonneg h0] using hN)⟩
  have hLtop : Tendsto L atTop atTop := by
    simpa [L, R, Erdos6.Maynard.maynardRadius] using
      BoundedGaps.Maynard.tendsto_log_engelsmaMaynardRadius_atTop halpha
  have hLratio : ∀ᶠ N : ℕ in atTop,
      0 ≤ (1 + L N) / L N ∧ (1 + L N) / L N ≤ 2 := by
    filter_upwards [hLtop.eventually (eventually_ge_atTop (1 : ℝ))] with N hN
    have hp : 0 < L N := lt_of_lt_of_le zero_lt_one hN
    exact ⟨div_nonneg (by linarith) hp.le,
      (div_le_iff₀ hp).2 (by linarith)⟩
  have hS : ∀ᶠ N : ℕ in atTop, 0 < S N ∧ S N ≤ 1 := by
    filter_upwards [] with N
    exact ⟨BoundedGaps.Maynard.preSieveSingularSeries_pos _,
      BoundedGaps.Maynard.preSieveSingularSeries_le_one _⟩
  have hQ : ∀ᶠ N : ℕ in atTop, 0 < Q N := by
    filter_upwards [hS,
      hLtop.eventually (eventually_gt_atTop 0)] with N hSN hLN
    exact mul_pos hSN.1 hLN
  have hLpos : ∀ᶠ N : ℕ in atTop, 0 < L N :=
    hLtop.eventually (eventually_gt_atTop 0)
  have hmean : Tendsto (fun N => M N / Q N) atTop (nhds 1) := by
    simpa [M, Q, S, L, D, R, Erdos6.Maynard.maynardModulus,
      BoundedGaps.Maynard.engelsmaMaynardModulus] using
      BoundedGaps.Maynard.tendsto_engelsmaReciprocalGSquarefreeMean_div_leadingTerm_one
        halpha
  have hmeanPow : Tendsto (fun N => M N ^ k / Q N ^ k)
      atTop (nhds 1) := by simpa [div_pow] using hmean.pow k
  have hmassLe : ∀ᶠ N : ℕ in atTop, M N ^ k / Q N ^ k ≤ 2 := by
    filter_upwards [hmeanPow.eventually
      (Metric.ball_mem_nhds (1 : ℝ) one_pos)] with N hN
    have hd : |M N ^ k / Q N ^ k - 1| < 1 := by
      simpa [Real.dist_eq] using hN
    linarith [le_abs_self (M N ^ k / Q N ^ k - 1)]
  have hcond :=
    BoundedGaps.Maynard.eventually_engelsmaMaynardCrossBound_conditions halpha
  have hRone :=
    BoundedGaps.Maynard.eventually_one_lt_engelsmaMaynardRadius halpha
  have hD2 : ∀ᶠ N : ℕ in atTop, 2 ≤ D N := by
    obtain ⟨N₀, hN₀⟩ := BoundedGaps.Maynard.exists_tripleLogCutoff_ge 2
    filter_upwards [eventually_ge_atTop (N₀ + 1)] with N hN
    exact hN₀ (N - 1) (by omega)
  have henv : ∀ᶠ N : ℕ in atTop,
      0 ≤ E N / Q N ∧ E N / Q N ≤ Cenv := by
    filter_upwards [hcond, hD2, hLratio, hAsmall, hS,
      hLtop.eventually (eventually_gt_atTop 0)] with
      N hCN hD2N hLR hAN hSN hLN
    have hEdivL : E N / L N =
        8 * S N * ((1 + L N) / L N) * (1 + (k : ℝ) * Aenv N) := by
      dsimp [E, L, S, Aenv, D, R, k]
      unfold Erdos6.Maynard.tupleRestrictedTransformEnvelope
      simp only [Erdos6.Maynard.maynardModulus,
        BoundedGaps.Maynard.engelsmaMaynardModulus,
        Finset.univ_eq_attach]
      rw [BoundedGaps.Maynard.preSieveSingularSeries_eq_totient_div]
      field_simp [hLN.ne']
    have hEdiv : E N / Q N =
        8 * ((1 + L N) / L N) * (1 + (k : ℝ) * Aenv N) := by
      calc
        E N / Q N = (E N / L N) / S N := by
          dsimp [Q]
          field_simp [hLN.ne', hSN.1.ne']
        _ = (8 * S N * ((1 + L N) / L N) *
            (1 + (k : ℝ) * Aenv N)) / S N := by rw [hEdivL]
        _ = 8 * ((1 + L N) / L N) *
            (1 + (k : ℝ) * Aenv N) := by field_simp [hSN.1.ne']
    have hfac0 : 0 ≤ 1 + (k : ℝ) * Aenv N := by positivity
    have hfacLe : 1 + (k : ℝ) * Aenv N ≤ 1 + (k : ℝ) := by
      simpa [add_comm] using add_le_add_left
        (mul_le_mul_of_nonneg_left hAN.2 (Nat.cast_nonneg k)) 1
    rw [hEdiv]
    constructor
    · positivity
    · calc
        8 * ((1 + L N) / L N) * (1 + (k : ℝ) * Aenv N) ≤
            8 * 2 * (1 + (k : ℝ) * Aenv N) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hLR.2 (by norm_num)) hfac0
        _ ≤ 8 * 2 * (1 + (k : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hfacLe (by norm_num)
        _ = Cenv := by dsimp [Cenv]; ring
  have htail : Tendsto Tail atTop (nhds 0) := by
    have h := hinvD.const_mul Ctail
    simpa [Tail, Ctail, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using h
  have hzero : Tendsto (fun N => (2 * Cenv ^ 2) * Tail N)
      atTop (nhds 0) := by
    simpa using htail.const_mul (2 * Cenv ^ 2)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ hzero
  filter_upwards [hcond, hRone, hD2, henv, hmassLe, hQ, hLpos] with
      N hCN hRoneN hD2N hEN hMN hQN hLN
  have hcorr' := abs_tupleRestrictedCross_le_explicit_of_abs_le_one
    F hF m hRoneN hD2N hCN.2.2
  have hM0 : 0 ≤ M N := by
    unfold M BoundedGaps.Maynard.maynardS2ReciprocalGSquarefreeMean
    exact Finset.sum_nonneg fun n hn =>
      Erdos6.Maynard.tupleReciprocalGSquarefreeAF_nonneg _ n
  have hTail0 : 0 ≤ Tail N := by dsimp [Tail]; positivity
  have hden : 0 < Q N ^ (k + 2) := pow_pos hQN _
  have hcard : Fintype.card (Erdos6.Maynard.tupleOffFace H m) = k := by
    calc
      Fintype.card (Erdos6.Maynard.tupleOffFace H m) =
          (Erdos6.Maynard.tupleOffFace H m).card := Fintype.card_coe _
      _ = H.card - 1 := by
        unfold Erdos6.Maynard.tupleOffFace
        rw [Finset.card_erase_of_mem m.2]
      _ = k := by
        dsimp [k]
        rw [Finset.card_erase_of_mem (Finset.mem_attach H m),
          Finset.card_attach]
  have houterEq : Erdos6.Maynard.tupleNaturalScale
      (Erdos6.Maynard.tupleOffFace H m) alpha N = Q N ^ k := by
    unfold Erdos6.Maynard.tupleNaturalScale
    rw [hcard]
  have hscaleEq :
      BoundedGaps.Maynard.preSieveSingularSeries (D N) ^ 2 * L N ^ 2 *
          Erdos6.Maynard.tupleNaturalScale
            (Erdos6.Maynard.tupleOffFace H m) alpha N =
        Q N ^ (k + 2) := by
    rw [houterEq]
    dsimp [Q]
    rw [pow_add]
    ring
  rw [show BoundedGaps.Maynard.preSieveSingularSeries
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
        Real.log (Erdos6.Maynard.maynardRadius alpha N) ^ 2 *
          Erdos6.Maynard.tupleNaturalScale
            (Erdos6.Maynard.tupleOffFace H m) alpha N =
        Q N ^ (k + 2) by simpa [D, L, R] using hscaleEq,
      abs_div, abs_of_pos hden]
  calc
    |Erdos6.Maynard.tupleRestrictedCross H alpha F N m| /
          Q N ^ (k + 2) ≤
        E N ^ 2 * Tail N * M N ^ k / Q N ^ (k + 2) :=
      div_le_div_of_nonneg_right (by
        simpa [E, Tail, M, D, R, k] using hcorr') hden.le
    _ = (E N / Q N) ^ 2 * Tail N * (M N ^ k / Q N ^ k) := by
      field_simp [hQN.ne']
      ring
    _ ≤ Cenv ^ 2 * Tail N * (M N ^ k / Q N ^ k) := by
      have hs := pow_le_pow_left₀ hEN.1 hEN.2 2
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hs hTail0)
        (div_nonneg (pow_nonneg hM0 _) (pow_nonneg hQN.le _))
    _ ≤ Cenv ^ 2 * Tail N * 2 := by
      exact mul_le_mul_of_nonneg_left hMN
        (mul_nonneg (sq_nonneg _) hTail0)
    _ = (2 * Cenv ^ 2) * Tail N := by ring

theorem eventually_variableTupleRestrictedGKernel_normalized_gt
    {K : ℕ} (hK2 : 2 ≤ K) {A alpha c : ℝ}
    (hA : 0 < A)
    (hmoment : VariableMaynard.firstMoment K A <
      (1 / (4 * (K : ℝ))) * VariableMaynard.baseMass K A)
    (halpha : 0 < alpha) (m : ↑(primorialShifts K))
    (hc : c < variableFiberLowerCoefficient K A) :
    ∀ᶠ N : ℕ in atTop,
      c < Erdos6.Maynard.tupleRestrictedGKernel
          (primorialShifts K) alpha (primorialShiftsCandidate K A) N m /
        (BoundedGaps.Maynard.preSieveSingularSeries
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
          Real.log (Erdos6.Maynard.maynardRadius alpha N) ^ 2 *
          Erdos6.Maynard.tupleNaturalScale
            (Erdos6.Maynard.tupleOffFace (primorialShifts K) m)
            alpha N) := by
  let scale : ℕ → ℝ := fun N =>
    BoundedGaps.Maynard.preSieveSingularSeries
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
      Real.log (Erdos6.Maynard.maynardRadius alpha N) ^ 2 *
      Erdos6.Maynard.tupleNaturalScale
        (Erdos6.Maynard.tupleOffFace (primorialShifts K) m) alpha N
  let mid := (c + variableFiberLowerCoefficient K A) / 2
  let eps := (variableFiberLowerCoefficient K A - c) / 2
  have hmid : mid < variableFiberLowerCoefficient K A := by
    dsimp [mid]
    linarith
  have heps : 0 < eps := by dsimp [eps]; linarith
  have hy := eventually_variableCoordinateOneYDiagonal_normalized_gt
    hK2 hA hmoment halpha m hmid
  have hcross := tendsto_normalizedTupleRestrictedCross_zero_of_abs_le_one
    halpha (primorialShiftsCandidate K A)
      (primorialShiftsCandidate_abs_le_one hA) m
  have hcrossSmall : ∀ᶠ N : ℕ in atTop,
      |Erdos6.Maynard.tupleRestrictedCross (primorialShifts K) alpha
          (primorialShiftsCandidate K A) N m / scale N| < eps := by
    have h := hcross.eventually (Metric.ball_mem_nhds (0 : ℝ) heps)
    simpa only [Real.dist_eq, sub_zero, scale] using h
  filter_upwards [hy, hcrossSmall] with N hyN hcrossN
  have hidentity := Erdos6.Maynard.tupleRestrictedGKernel_eq_quadratic_sub_cross
    (primorialShifts K) alpha (primorialShiftsCandidate K A) N m
  rw [Erdos6.Maynard.tupleRestrictedQuadratic_eq_yDiagonal,
    Erdos6.Maynard.tupleRestrictedYDiagonal_eq_coordinateOne] at hidentity
  have hcrossUpper :
      Erdos6.Maynard.tupleRestrictedCross (primorialShifts K) alpha
          (primorialShiftsCandidate K A) N m / scale N < eps :=
    (le_abs_self _).trans_lt hcrossN
  have htarget : c <
      Erdos6.Maynard.tupleRestrictedGKernel
          (primorialShifts K) alpha (primorialShiftsCandidate K A) N m /
        scale N := by
    rw [hidentity, sub_div]
    dsimp [mid, eps] at hyN hcrossUpper
    linarith
  simpa [scale] using htarget

theorem tupleRestrictedTotientKernel_eq_GKernel_variable
    (H : Finset ℕ) (alpha : ℝ) (F : (H → ℝ) → ℝ)
    (N : ℕ) (m : H) :
    Erdos6.Maynard.tupleRestrictedTotientKernel H alpha F N m =
      Erdos6.Maynard.tupleRestrictedGKernel H alpha F N m := by
  unfold Erdos6.Maynard.tupleRestrictedTotientKernel
    Erdos6.Maynard.tupleRestrictedGKernel
  apply BoundedGaps.Maynard.compatibleDivisorPairRestrictedTotientKernel_eq_commonDivisorS2TupleSum
  intro d hd
  exact Erdos6.Maynard.tupleMaynardS2SupportProof H alpha N d hd

theorem eventually_pinnedRestrictedArithmeticKernel_normalized_gt_variable
    {K : ℕ} (hK2 : 2 ≤ K) {A alpha c : ℝ}
    (hA : 0 < A)
    (hmoment : VariableMaynard.firstMoment K A <
      (1 / (4 * (K : ℝ))) * VariableMaynard.baseMass K A)
    (halpha : 0 < alpha) (h : ↑(primorialShifts K))
    (hc : c < variableFiberLowerCoefficient K A) :
    ∀ᶠ N : ℕ in atTop,
      c < pinnedRestrictedArithmeticKernel K A alpha N h /
        (BoundedGaps.Maynard.preSieveSingularSeries
            (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
          Real.log (Erdos6.Maynard.maynardRadius alpha N) ^ 2 *
          Erdos6.Maynard.tupleNaturalScale
            (Erdos6.Maynard.tupleOffFace (primorialShifts K) h)
            alpha N) := by
  have hmain := eventually_variableTupleRestrictedGKernel_normalized_gt
    hK2 hA hmoment halpha h hc
  filter_upwards [hmain] with N hN
  rw [pinnedRestrictedArithmeticKernel_eq_tuple,
    tupleRestrictedTotientKernel_eq_GKernel_variable]
  exact hN

noncomputable def variablePinnedKernelScale
    (K : ℕ) (alpha : ℝ) (N : ℕ) : ℝ :=
  BoundedGaps.Maynard.preSieveSingularSeries
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
    Real.log (Erdos6.Maynard.maynardRadius alpha N) ^ 2 *
    (BoundedGaps.Maynard.preSieveSingularSeries
        (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) *
      Real.log (Erdos6.Maynard.maynardRadius alpha N)) ^ (K - 1)

theorem tupleOffFace_naturalScale_primorialShifts
    {K : ℕ} (h : ↑(primorialShifts K)) (alpha : ℝ) (N : ℕ) :
    Erdos6.Maynard.tupleNaturalScale
        (Erdos6.Maynard.tupleOffFace (primorialShifts K) h) alpha N =
      (BoundedGaps.Maynard.preSieveSingularSeries
          (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) *
        Real.log (Erdos6.Maynard.maynardRadius alpha N)) ^ (K - 1) := by
  unfold Erdos6.Maynard.tupleNaturalScale
  rw [fintype_card_tupleOffFace_primorialShifts h]

theorem eventually_sum_pinnedRestrictedArithmeticKernel_gt_variable
    {K : ℕ} (hK2 : 2 ≤ K) {A alpha c : ℝ}
    (hA : 0 < A)
    (hmoment : VariableMaynard.firstMoment K A <
      (1 / (4 * (K : ℝ))) * VariableMaynard.baseMass K A)
    (halpha : 0 < alpha) (hc : 0 < c)
    (hcLower : c < variableFiberLowerCoefficient K A) :
    ∀ᶠ N : ℕ in atTop,
      (K : ℝ) * c * variablePinnedKernelScale K alpha N <
        ∑ h : ↑(primorialShifts K),
          pinnedRestrictedArithmeticKernel K A alpha N h := by
  have hall : ∀ᶠ N : ℕ in atTop, ∀ h : ↑(primorialShifts K),
      c < pinnedRestrictedArithmeticKernel K A alpha N h /
        variablePinnedKernelScale K alpha N := by
    have hall' := (Finset.univ : Finset ↑(primorialShifts K)).eventually_all.mpr
      (fun h _ => eventually_pinnedRestrictedArithmeticKernel_normalized_gt_variable
        hK2 hA hmoment halpha h hcLower)
    filter_upwards [hall'] with N hN
    intro h
    simpa [variablePinnedKernelScale,
      tupleOffFace_naturalScale_primorialShifts] using hN h
  have hscale : ∀ᶠ N : ℕ in atTop,
      0 < variablePinnedKernelScale K alpha N := by
    filter_upwards [
      BoundedGaps.Maynard.eventually_one_lt_engelsmaMaynardRadius halpha]
      with N hR
    unfold variablePinnedKernelScale
    have hS := BoundedGaps.Maynard.preSieveSingularSeries_pos
      (BoundedGaps.Maynard.tripleLogCutoff (N - 1))
    have hL : 0 < Real.log (Erdos6.Maynard.maynardRadius alpha N) :=
      Real.log_pos (by exact_mod_cast hR)
    positivity
  filter_upwards [hall, hscale] with N hallN hscaleN
  have hterm : ∀ h : ↑(primorialShifts K),
      c * variablePinnedKernelScale K alpha N <
        pinnedRestrictedArithmeticKernel K A alpha N h := by
    intro h
    exact (lt_div_iff₀ hscaleN).mp (hallN h)
  have huniv : (Finset.univ : Finset ↑(primorialShifts K)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact Fintype.card_pos_iff.mp (by
      rw [Fintype.card_coe, card_primorialShifts]
      omega)
  calc
    (K : ℝ) * c * variablePinnedKernelScale K alpha N =
        ∑ _h : ↑(primorialShifts K),
          c * variablePinnedKernelScale K alpha N := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_coe, card_primorialShifts]
      ring
    _ < _ := Finset.sum_lt_sum_of_nonempty huniv (fun h _ => hterm h)

theorem explicit_variableKernelRatio_lower_log
    {K : ℕ} {A : ℝ} (hK : 0 < K) (hA : 0 < A) :
    Real.log (1 + A * (K : ℝ) * (1 / 4 : ℝ)) ^ 2 / (2 * A) <
      ((K : ℝ) / 2) * variableQuarterMass K A ^ 2 /
        VariableMaynard.baseMass K A := by
  have hKR : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hterm : 0 < A * (K : ℝ) * (1 / 4 : ℝ) := by positivity
  have harg : 1 < 1 + A * (K : ℝ) * (1 / 4 : ℝ) := by linarith
  have hlog : 0 < Real.log (1 + A * (K : ℝ) * (1 / 4 : ℝ)) :=
    Real.log_pos harg
  let L := Real.log (1 + A * (K : ℝ) * (1 / 4 : ℝ))
  have hden : 0 < 2 * A ^ 2 * (K : ℝ) := by positivity
  calc
    L ^ 2 / (2 * A) = L ^ 2 * (A * (K : ℝ)) /
        (2 * A ^ 2 * (K : ℝ)) := by
      field_simp [hA.ne', hKR.ne']
    _ < L ^ 2 * (1 + A * (K : ℝ)) /
        (2 * A ^ 2 * (K : ℝ)) := by
      apply (div_lt_div_iff₀ hden hden).2
      have : 0 < L ^ 2 := sq_pos_of_pos hlog
      nlinarith
    _ = ((K : ℝ) / 2) * variableQuarterMass K A ^ 2 /
        VariableMaynard.baseMass K A := by
      unfold variableQuarterMass VariableMaynard.baseMass L
      field_simp [hA.ne', hKR.ne']

theorem parameter_quarter_log_lower {r : ℕ} (hr : 8 ≤ r) :
    (2 / 3 : ℝ) * (r : ℝ) <
      Real.log (1 + VariableMaynard.parameterA r *
        (VariableMaynard.parameterK r : ℝ) * (1 / 4 : ℝ)) := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hKpos : (0 : ℝ) < VariableMaynard.parameterK r := by
    exact_mod_cast VariableMaynard.parameterK_pos r
  have hKlog : Real.log (VariableMaynard.parameterK r : ℝ) =
      (r : ℝ) * Real.log 2 := by
    unfold VariableMaynard.parameterK
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have harg : (VariableMaynard.parameterK r : ℝ) <
      1 + VariableMaynard.parameterA r *
        (VariableMaynard.parameterK r : ℝ) * (1 / 4 : ℝ) := by
    unfold VariableMaynard.parameterA
    have hrone : (1 : ℝ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
    nlinarith
  have hargpos : 0 < 1 + VariableMaynard.parameterA r *
      (VariableMaynard.parameterK r : ℝ) * (1 / 4 : ℝ) :=
    hKpos.trans harg
  have hmono := Real.strictMonoOn_log hKpos hargpos harg
  rw [hKlog] at hmono
  have hlogTwo : (2 / 3 : ℝ) < Real.log 2 :=
    (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  nlinarith

theorem variableFiberCoefficient_ratio_ge
    {K : ℕ} {A : ℝ} (hK : 0 < K) (hA : 0 < A) :
    ((K : ℝ) / 2) * variableQuarterMass K A ^ 2 /
        VariableMaynard.baseMass K A ≤
      ((K : ℝ) * variableFiberLowerCoefficient K A) /
        BoundedGaps.Maynard.maynardI K (VariableMaynard.candidate K A) := by
  let I := BoundedGaps.Maynard.maynardI K (VariableMaynard.candidate K A)
  let B := VariableMaynard.baseMass K A
  let M := variableQuarterMass K A
  have hI : 0 < I := VariableMaynard.maynardI_candidate_pos hK hA
  have hB : 0 < B := VariableMaynard.baseMass_pos hK hA
  have hIle : I ≤ B ^ K := by
    simpa [I, B] using VariableMaynard.maynardI_candidate_le hK hA
  have hL : 0 ≤ (K : ℝ) * variableFiberLowerCoefficient K A :=
    mul_nonneg (Nat.cast_nonneg _)
      (variableFiberLowerCoefficient_pos hK hA).le
  have heq :
      ((K : ℝ) * variableFiberLowerCoefficient K A) / B ^ K =
        ((K : ℝ) / 2) * M ^ 2 / B := by
    unfold variableFiberLowerCoefficient
    have hpow : B ^ K = B ^ (K - 1) * B := by
      have hexp : K = (K - 1) + 1 := by omega
      calc
        B ^ K = B ^ ((K - 1) + 1) := congrArg (fun n : ℕ => B ^ n) hexp
        _ = B ^ (K - 1) * B := pow_succ _ _
    rw [hpow]
    field_simp [hB.ne']
    ring
  rw [← heq]
  exact div_le_div_of_nonneg_left hL hI hIle

theorem parameter_variableFiberCoefficient_ratio_gt
    {r : ℕ} (hr : 8 ≤ r) :
    (r : ℝ) / 72 <
      ((VariableMaynard.parameterK r : ℝ) *
          variableFiberLowerCoefficient (VariableMaynard.parameterK r)
            (VariableMaynard.parameterA r)) /
        BoundedGaps.Maynard.maynardI (VariableMaynard.parameterK r)
          (VariableMaynard.candidate (VariableMaynard.parameterK r)
            (VariableMaynard.parameterA r)) := by
  have hrN : 0 < r := by omega
  have hrR : (0 : ℝ) < r := by exact_mod_cast hrN
  have hA : 0 < VariableMaynard.parameterA r :=
    VariableMaynard.parameterA_pos hrN
  have hK := VariableMaynard.parameterK_pos r
  have hexplicit := explicit_variableKernelRatio_lower_log hK hA
  have hloglower := parameter_quarter_log_lower hr
  have hsq : ((2 / 3 : ℝ) * (r : ℝ)) ^ 2 <
      Real.log (1 + VariableMaynard.parameterA r *
        (VariableMaynard.parameterK r : ℝ) * (1 / 4 : ℝ)) ^ 2 := by
    have : 0 < (2 / 3 : ℝ) * (r : ℝ) := by positivity
    nlinarith
  have hlower : (r : ℝ) / 72 <
      Real.log (1 + VariableMaynard.parameterA r *
          (VariableMaynard.parameterK r : ℝ) * (1 / 4 : ℝ)) ^ 2 /
        (2 * VariableMaynard.parameterA r) := by
    unfold VariableMaynard.parameterA
    have hden : 0 < 2 * (16 * (r : ℝ)) := by positivity
    rw [lt_div_iff₀ hden]
    calc
      (r : ℝ) / 72 * (2 * (16 * (r : ℝ))) =
          ((2 / 3 : ℝ) * (r : ℝ)) ^ 2 := by ring
      _ < _ := hsq
  exact hlower.trans (hexplicit.trans_le
    (variableFiberCoefficient_ratio_ge hK hA))

theorem allowedPreSieveResidues_card_le_totient (W m : ℕ) :
    (allowedPreSieveResidues W m).card ≤ Nat.totient W := by
  rw [← BoundedGaps.Maynard.card_coprimeResidues W]
  apply Finset.card_le_card
  intro v hv
  have hvData := Finset.mem_filter.mp hv
  have hvI := Finset.mem_Ico.mp hvData.1
  have hcopPoly := hvData.2
  have hvdvd : v ∣ preSievePolynomial m v := by
    unfold preSievePolynomial
    exact dvd_mul_right _ _
  have hcop : v.Coprime W := Nat.Coprime.of_dvd_left hvdvd hcopPoly
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hvI.2, hcop⟩

theorem eventually_scaledTrivialCompanionNormalizationMass_le_sharp
    {K : ℕ} (hK : 0 < K) {A alpha : ℝ}
    (hA : 0 < A) (halpha : 0 < alpha) (halphaQuarter : alpha < 1 / 4) :
    ∀ᶠ N : ℕ in atTop, ∀ m q : ℕ,
      0 < m → q.Prime →
      BoundedGaps.Maynard.engelsmaMaynardRadius alpha N ≤ q →
      scaledTrivialCompanionNormalizationMass K A alpha
          (fun _ => m) (fun _ => q) N ≤
        3 * (Nat.totient (BoundedGaps.Maynard.engelsmaMaynardModulus N) : ℝ) *
          BoundedGaps.Maynard.maynardI K (VariableMaynard.candidate K A) *
          Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N := by
  let I := BoundedGaps.Maynard.maynardI K
    (VariableMaynard.candidate K A)
  have hI : 0 < I := VariableMaynard.maynardI_candidate_pos hK hA
  have hfirst : ∀ᶠ N : ℕ in atTop,
      0 < normalizedFirstCompatibleQuadratic K A alpha N ∧
      normalizedFirstCompatibleQuadratic K A alpha N < 2 * I := by
    have ht := tendsto_normalizedFirstCompatibleQuadratic hK hA halpha
    exact ht.eventually (Ioo_mem_nhds (by simpa [I] using hI)
      (by dsimp [I]; nlinarith [hI]))
  have herrlim := tendsto_trivialCompanionErrorEnvelope_div_scale_zero
    (primorialShifts K) halpha (by norm_num : (0 : ℝ) ≤ 1)
      halphaQuarter
  have herrsmall : ∀ᶠ N : ℕ in atTop,
      trivialCompanionErrorEnvelope (primorialShifts K) alpha 1 N /
          Erdos6.Maynard.tupleMaynardScale
            (primorialShifts K) alpha N < I :=
    (tendsto_order.1 herrlim).2 I hI
  obtain ⟨N₀, hN₀⟩ :=
    BoundedGaps.Maynard.exists_tripleLogCutoff_ge 2
  filter_upwards [hfirst, herrsmall,
    Erdos6.Maynard.eventually_tupleMaynardScale_pos
      (H := primorialShifts K) halpha,
    Erdos6.Maynard.eventually_tupleMaynard_coverage (primorialShifts K),
    eventually_ge_atTop (N₀ + 1)] with
      N hfirstN herrsmallN hscale hcover hN
  intro m q hm hq hRq
  let D := BoundedGaps.Maynard.tripleLogCutoff (N - 1)
  let W := BoundedGaps.Maynard.engelsmaMaynardModulus N
  let Q := BoundedGaps.Maynard.compatibleDivisorPairTotientExpandedSum
        (primorialShifts K)
        (separatedFirstSupport (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) D)
        (separatedFirstCoefficient (primorialShifts K)
          (BoundedGaps.Maynard.engelsmaMaynardRadius alpha N) D
          (primorialShiftsCandidate K A))
  let E := scaledTrivialCompanionNormalizationError K A alpha
    (fun _ => m) (fun _ => q) N
  have hD : 2 ≤ D := hN₀ (N - 1) (by omega)
  have hmass : scaledTrivialCompanionNormalizationMass K A alpha
      (fun _ => m) (fun _ => q) N =
      (N : ℝ) * preSieveDensity D m * Q + E := by
    unfold scaledTrivialCompanionNormalizationMass
    dsimp [E, scaledTrivialCompanionNormalizationError, D, W, Q]
    simpa [BoundedGaps.Maynard.engelsmaMaynardModulus] using
      (preSievedScaledTrivialCompanionWeightSum_eq_main_add_error
        (H := primorialShifts K)
        (RD := BoundedGaps.Maynard.engelsmaMaynardRadius alpha N)
        (w := D) (m := m) (q := q) (T := N)
        hD hm hq hcover hRq (primorialShiftsCandidate K A))
  have hEbound : |E| ≤
      trivialCompanionErrorEnvelope (primorialShifts K) alpha 1 N := by
    dsimp [E, scaledTrivialCompanionNormalizationError, D, W]
    exact scaledTrivialCompanionNormalizationError_abs_le_envelope
      (H := primorialShifts K) (alpha := alpha) (B := 1)
      (N := N) (m := m) (q := q) (T := N)
      (F := primorialShiftsCandidate K A)
      (by norm_num) (primorialShiftsCandidate_abs_le_one hA)
      hm hq hD hcover hRq
  have hmainnorm :
      ((N : ℝ) * preSieveDensity D m * Q) /
          Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N =
        ((allowedPreSieveResidues W m).card : ℝ) *
          normalizedFirstCompatibleQuadratic K A alpha N := by
    simpa [D, W, Q] using
      (normalized_trivialCompanion_main_eq_card_mul
        (K := K) (N := N) (m := m) (A := A) (alpha := alpha)
        hD hm hscale.ne')
  have hcardNat := allowedPreSieveResidues_card_le_totient W m
  have hcard : ((allowedPreSieveResidues W m).card : ℝ) ≤
      Nat.totient W := by exact_mod_cast hcardNat
  have hphi0 : (0 : ℝ) ≤ Nat.totient W := Nat.cast_nonneg _
  have hmainDiv :
      ((N : ℝ) * preSieveDensity D m * Q) /
          Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N ≤
        (Nat.totient W : ℝ) * (2 * I) := by
    rw [hmainnorm]
    exact (mul_le_mul_of_nonneg_right hcard hfirstN.1.le).trans
      (mul_le_mul_of_nonneg_left hfirstN.2.le hphi0)
  have hmain : (N : ℝ) * preSieveDensity D m * Q ≤
      (Nat.totient W : ℝ) * (2 * I) *
        Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N :=
    (div_le_iff₀ hscale).mp hmainDiv
  have hE : E ≤ I *
      Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N := by
    calc
      E ≤ |E| := le_abs_self E
      _ ≤ trivialCompanionErrorEnvelope (primorialShifts K) alpha 1 N :=
        hEbound
      _ ≤ I * Erdos6.Maynard.tupleMaynardScale
          (primorialShifts K) alpha N :=
        ((div_lt_iff₀ hscale).mp herrsmallN).le
  have hWpos : 0 < W := by
    dsimp [W]
    exact primorial_pos _
  have hphiOne : (1 : ℝ) ≤ Nat.totient W := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (Nat.totient_pos.mpr hWpos).ne')
  rw [hmass]
  calc
    (N : ℝ) * preSieveDensity D m * Q + E ≤
        (Nat.totient W : ℝ) * (2 * I) *
            Erdos6.Maynard.tupleMaynardScale (primorialShifts K) alpha N +
          I * Erdos6.Maynard.tupleMaynardScale
            (primorialShifts K) alpha N := add_le_add hmain hE
    _ ≤ 3 * (Nat.totient W : ℝ) * I *
          Erdos6.Maynard.tupleMaynardScale
            (primorialShifts K) alpha N := by
      have hIscale : 0 ≤ I * Erdos6.Maynard.tupleMaynardScale
          (primorialShifts K) alpha N := mul_nonneg hI.le hscale.le
      nlinarith
    _ = _ := by rfl

end

end Erdos4b
