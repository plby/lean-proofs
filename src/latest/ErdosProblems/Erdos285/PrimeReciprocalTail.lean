/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos285.PositiveReservoir

/-!
# The prime reciprocal tail above the smoothness cutoff

This file completes the analytic estimate needed by the positive-reservoir
argument.  The reciprocal mass of the primes between `x^(2/5)` and a fixed
positive multiple of `x` tends to `log (5/2)`.  For the reservoir construction
we only need the strict, uniform upper bound `49/50`.
-/

open Filter Finset Real Asymptotics
open scoped BigOperators Topology

namespace Erdos285.PositiveReservoir

noncomputable section

/-- The natural floor of `x^(2/5)` tends to infinity. -/
lemma smoothCutoff_tendsto_atTop : Tendsto smoothCutoff atTop atTop := by
  apply tendsto_nat_floor_atTop.comp
  apply (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
  exact tendsto_natCast_atTop_atTop

/-- The logarithm of the smoothness cutoff is asymptotic to `(2/5) log x`. -/
lemma log_smoothCutoff_div_log_tendsto_two_fifths :
    Tendsto
      (fun x : ℕ ↦ Real.log (smoothCutoff x : ℝ) / Real.log (x : ℝ))
      atTop (nhds (2 / 5 : ℝ)) := by
  let scale : ℕ → ℝ := fun x ↦ (x : ℝ) ^ (2 / 5 : ℝ)
  let ratio : ℕ → ℝ := fun x ↦ (smoothCutoff x : ℝ) / scale x
  have hscale : Tendsto scale atTop atTop := by
    dsimp [scale]
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
      tendsto_natCast_atTop_atTop
  have hratio : Tendsto ratio atTop (nhds 1) := by
    change Tendsto ((fun y : ℝ ↦ (⌊y⌋₊ : ℝ) / y) ∘ scale) atTop (nhds 1)
    exact tendsto_nat_floor_div_atTop.comp hscale
  have hlogratio : Tendsto (fun x ↦ Real.log (ratio x)) atTop (nhds 0) := by
    change Tendsto (Real.log ∘ ratio) atTop (nhds 0)
    simpa using (Real.continuousAt_log one_ne_zero).tendsto.comp hratio
  have hlogratio_div : Tendsto
      (fun x : ℕ ↦ Real.log (ratio x) / Real.log (x : ℝ))
      atTop (nhds 0) :=
    hlogratio.div_atTop tendsto_log_coe_at_top
  have hmain : Tendsto
      (fun x : ℕ ↦
        Real.log (ratio x) / Real.log (x : ℝ) + (2 / 5 : ℝ))
      atTop (nhds (2 / 5 : ℝ)) := by
    simpa using hlogratio_div.add_const (2 / 5 : ℝ)
  apply hmain.congr'
  filter_upwards
    [eventually_gt_atTop (1 : ℕ),
      hscale.eventually (eventually_gt_atTop (0 : ℝ)),
      hratio.eventually (Ioi_mem_nhds zero_lt_one)] with x hx hscalePos hratioPos
  have hxpos : (0 : ℝ) < x := by positivity
  have hlogx : Real.log (x : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hx)).ne'
  have hscaleNe : scale x ≠ 0 := hscalePos.ne'
  have hratioNe : ratio x ≠ 0 := hratioPos.ne'
  have hcutoff : (smoothCutoff x : ℝ) = ratio x * scale x := by
    dsimp [ratio]
    exact (div_mul_cancel₀ _ hscaleNe).symm
  rw [hcutoff, Real.log_mul hratioNe hscaleNe]
  dsimp [scale]
  rw [Real.log_rpow hxpos]
  field_simp

/-- The logarithm of `floor (αx)` is asymptotic to `log x` for fixed
positive `α`. -/
lemma log_floor_mul_div_log_tendsto_one (α : ℝ) (hα : 0 < α) :
    Tendsto
      (fun x : ℕ ↦ Real.log (⌊α * (x : ℝ)⌋₊ : ℝ) / Real.log (x : ℝ))
      atTop (nhds 1) := by
  let scale : ℕ → ℝ := fun x ↦ α * (x : ℝ)
  let ratio : ℕ → ℝ := fun x ↦ (⌊scale x⌋₊ : ℝ) / scale x
  have hscale : Tendsto scale atTop atTop := by
    exact tendsto_natCast_atTop_atTop.const_mul_atTop hα
  have hratio : Tendsto ratio atTop (nhds 1) := by
    change Tendsto ((fun y : ℝ ↦ (⌊y⌋₊ : ℝ) / y) ∘ scale) atTop (nhds 1)
    exact tendsto_nat_floor_div_atTop.comp hscale
  have hlogratio : Tendsto (fun x ↦ Real.log (ratio x)) atTop (nhds 0) := by
    change Tendsto (Real.log ∘ ratio) atTop (nhds 0)
    simpa using (Real.continuousAt_log one_ne_zero).tendsto.comp hratio
  have hlogratio_div : Tendsto
      (fun x : ℕ ↦ Real.log (ratio x) / Real.log (x : ℝ))
      atTop (nhds 0) :=
    hlogratio.div_atTop tendsto_log_coe_at_top
  have hconst_div : Tendsto
      (fun x : ℕ ↦ Real.log α / Real.log (x : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_coe_at_top
  have hmain : Tendsto
      (fun x : ℕ ↦
        Real.log (ratio x) / Real.log (x : ℝ) +
          Real.log α / Real.log (x : ℝ) + 1)
      atTop (nhds 1) := by
    simpa using (hlogratio_div.add hconst_div).add_const 1
  apply hmain.congr'
  filter_upwards
    [eventually_gt_atTop (1 : ℕ),
      hscale.eventually (eventually_gt_atTop (0 : ℝ)),
      hratio.eventually (Ioi_mem_nhds zero_lt_one)] with x hx hscalePos hratioPos
  have hxpos : (0 : ℝ) < x := by positivity
  have hlogx : Real.log (x : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hx)).ne'
  have hscaleNe : scale x ≠ 0 := hscalePos.ne'
  have hratioNe : ratio x ≠ 0 := hratioPos.ne'
  have hfloor : (⌊α * (x : ℝ)⌋₊ : ℝ) = ratio x * scale x := by
    dsimp [ratio, scale]
    exact (div_mul_cancel₀ _ (mul_ne_zero hα.ne' hxpos.ne')).symm
  rw [hfloor, Real.log_mul hratioNe hscaleNe]
  dsimp [scale]
  rw [Real.log_mul hα.ne' hxpos.ne']
  field_simp
  ring

/-- The logarithmic interval length in the Abel majorant tends to
`log (5/2)`. -/
lemma loglog_floor_mul_sub_loglog_smoothCutoff_tendsto (α : ℝ) (hα : 0 < α) :
    Tendsto
      (fun x : ℕ ↦
        Real.log (Real.log (⌊α * (x : ℝ)⌋₊ : ℝ)) -
          Real.log (Real.log (smoothCutoff x : ℝ)))
      atTop (nhds (Real.log (5 / 2 : ℝ))) := by
  have hnum := log_floor_mul_div_log_tendsto_one α hα
  have hden := log_smoothCutoff_div_log_tendsto_two_fifths
  have hquot : Tendsto
      (fun x : ℕ ↦
        (Real.log (⌊α * (x : ℝ)⌋₊ : ℝ) / Real.log (x : ℝ)) /
          (Real.log (smoothCutoff x : ℝ) / Real.log (x : ℝ)))
      atTop (nhds ((1 : ℝ) / (2 / 5 : ℝ))) :=
    hnum.div hden (by norm_num)
  have hquot' : Tendsto
      (fun x : ℕ ↦
        Real.log (⌊α * (x : ℝ)⌋₊ : ℝ) /
          Real.log (smoothCutoff x : ℝ))
      atTop (nhds (5 / 2 : ℝ)) := by
    rw [show (5 / 2 : ℝ) = (1 : ℝ) / (2 / 5 : ℝ) by norm_num]
    apply hquot.congr'
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with x hx
    have hlogx : Real.log (x : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hx)).ne'
    field_simp
  have hlogquot : Tendsto
      (fun x : ℕ ↦ Real.log
        (Real.log (⌊α * (x : ℝ)⌋₊ : ℝ) /
          Real.log (smoothCutoff x : ℝ)))
      atTop (nhds (Real.log (5 / 2 : ℝ))) :=
    (Real.continuousAt_log (by norm_num : (5 / 2 : ℝ) ≠ 0)).tendsto.comp hquot'
  apply hlogquot.congr'
  have hlogA : Tendsto (fun x : ℕ ↦ Real.log (smoothCutoff x : ℝ))
      atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp smoothCutoff_tendsto_atTop)
  have hfloorTop : Tendsto (fun x : ℕ ↦ ⌊α * (x : ℝ)⌋₊) atTop atTop := by
    apply tendsto_nat_floor_atTop.comp
    exact tendsto_natCast_atTop_atTop.const_mul_atTop hα
  have hlogB : Tendsto (fun x : ℕ ↦ Real.log (⌊α * (x : ℝ)⌋₊ : ℝ))
      atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hfloorTop)
  filter_upwards
    [hlogA.eventually (eventually_gt_atTop (0 : ℝ)),
      hlogB.eventually (eventually_gt_atTop (0 : ℝ))] with x hA hB
  rw [Real.log_div hB.ne' hA.ne']

private lemma log_five_halves_lt_nineteen_twentieths :
    Real.log (5 / 2 : ℝ) < 19 / 20 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 5 / 2)]
  calc
    (5 / 2 : ℝ) < ∑ i ∈ range 4, (19 / 20 : ℝ) ^ i / (i.factorial : ℝ) := by
      norm_num
    _ ≤ Real.exp (19 / 20 : ℝ) := Real.sum_le_exp_of_nonneg (by norm_num) 4

/-- The Abel-summation upper bound for the reciprocal prime interval tends to
`(101/100) log (5/2)`. -/
lemma primeReciprocalInterval_majorant_tendsto (α : ℝ) (hα : 0 < α) :
    Tendsto
      (fun x : ℕ ↦
        (101 / 100 : ℝ) / Real.log (⌊α * (x : ℝ)⌋₊ : ℝ) +
          (101 / 100 : ℝ) *
            (Real.log (Real.log (⌊α * (x : ℝ)⌋₊ : ℝ)) -
              Real.log (Real.log (smoothCutoff x : ℝ))))
      atTop (nhds ((101 / 100 : ℝ) * Real.log (5 / 2 : ℝ))) := by
  have hfloorTop : Tendsto (fun x : ℕ ↦ ⌊α * (x : ℝ)⌋₊) atTop atTop := by
    apply tendsto_nat_floor_atTop.comp
    exact tendsto_natCast_atTop_atTop.const_mul_atTop hα
  have hlogTop : Tendsto
      (fun x : ℕ ↦ Real.log (⌊α * (x : ℝ)⌋₊ : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hfloorTop)
  have hfirst : Tendsto
      (fun x : ℕ ↦ (101 / 100 : ℝ) /
        Real.log (⌊α * (x : ℝ)⌋₊ : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hlogTop
  have hsecond :=
    (loglog_floor_mul_sub_loglog_smoothCutoff_tendsto α hα).const_mul (101 / 100 : ℝ)
  simpa using hfirst.add hsecond

/-- For every fixed positive `α`, the reciprocal mass of the primes in
`(floor(x^(2/5)), floor(αx)]` is eventually strictly below `49/50`. -/
theorem eventually_primeReciprocalInterval_smoothCutoff_lt (α : ℝ) (hα : 0 < α) :
    ∀ᶠ x : ℕ in atTop,
      primeReciprocalInterval (smoothCutoff x) ⌊α * (x : ℝ)⌋₊ < (49 / 50 : ℝ) := by
  have hlimit : (101 / 100 : ℝ) * Real.log (5 / 2 : ℝ) < 49 / 50 := by
    nlinarith [log_five_halves_lt_nineteen_twentieths]
  have hmajor := (primeReciprocalInterval_majorant_tendsto α hα).eventually
    (Iio_mem_nhds hlimit)
  have hcutoffTwo : ∀ᶠ x : ℕ in atTop, 2 ≤ smoothCutoff x :=
    smoothCutoff_tendsto_atTop.eventually (eventually_ge_atTop 2)
  have hfloorTop : Tendsto (fun x : ℕ ↦ ⌊α * (x : ℝ)⌋₊) atTop atTop := by
    apply tendsto_nat_floor_atTop.comp
    exact tendsto_natCast_atTop_atTop.const_mul_atTop hα
  have hcutoffLe : ∀ᶠ x : ℕ in atTop, smoothCutoff x ≤ ⌊α * (x : ℝ)⌋₊ := by
    have hneg : Tendsto (fun x : ℕ ↦ (x : ℝ) ^ (-(3 / 5 : ℝ)))
        atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 5)).comp
        tendsto_natCast_atTop_atTop
    have hsmall := hneg.eventually (Iio_mem_nhds hα)
    filter_upwards [hsmall, eventually_gt_atTop (0 : ℕ)] with x hxsmall hx
    apply Nat.floor_mono
    have hxpos : (0 : ℝ) < x := by positivity
    have hratio : (x : ℝ) ^ (2 / 5 : ℝ) / x =
        (x : ℝ) ^ (-(3 / 5 : ℝ)) := by
      calc
        (x : ℝ) ^ (2 / 5 : ℝ) / x =
            (x : ℝ) ^ ((2 / 5 : ℝ) - 1) := by
          symm
          simpa using Real.rpow_sub hxpos (2 / 5 : ℝ) 1
        _ = (x : ℝ) ^ (-(3 / 5 : ℝ)) := by norm_num
    rw [← div_le_iff₀ hxpos]
    rw [hratio]
    exact hxsmall.le
  have hpnt := eventually_primeCounting_upper
  rw [eventually_atTop] at hpnt
  obtain ⟨T, hT⟩ := hpnt
  have hcutoffT : ∀ᶠ x : ℕ in atTop, T ≤ (smoothCutoff x : ℝ) := by
    have hcastTop : Tendsto (fun x : ℕ ↦ (smoothCutoff x : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp smoothCutoff_tendsto_atTop
    exact hcastTop.eventually (eventually_ge_atTop T)
  filter_upwards [hmajor, hcutoffTwo, hcutoffLe, hcutoffT] with x hmaj ha hab hTcut
  refine (primeReciprocalInterval_le (smoothCutoff x) ⌊α * (x : ℝ)⌋₊ ha hab ?_).trans_lt hmaj
  intro t ht
  exact hT t (hTcut.trans ht.1)

end

end Erdos285.PositiveReservoir
