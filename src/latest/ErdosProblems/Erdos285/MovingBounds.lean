/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos285.Proposition4
import ErdosProblems.Erdos285.Proposition6Asymptotic
import ErdosProblems.Erdos285.RoughCounts

/-!
# Moving-parameter estimates for Martin's Proposition 6

The final construction takes the lower endpoint
`exp (-1) + 1 / sqrt (log x)`, rather than a fixed endpoint.  Consequently
the initial residual tends to zero and the fixed-parameter margin theorem in
`Proposition6Asymptotic` does not apply directly.  This file proves the
quantitative moving estimates used by the final Proposition 6 invocation.
-/

namespace Erdos285

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

open RoughCounts

/-! ## The elimination budget -/

/-- The actual recursion budget, summed over every possible measure up to the
main cutoff, is eventually covered by the explicit deletion budget. -/
theorem eventually_totalEliminationBudget_mainCutoff_le :
    ∀ᶠ x : ℕ in atTop,
      totalEliminationBudget x (mainCutoffNat x) ≤ proposition6DeletionBudget x := by
  have hQtop : Tendsto mainCutoffNat atTop atTop := mainCutoffNat_spec.2.1
  have hlogtop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    tendsto_log_coe_at_top
  filter_upwards [eventually_ge_atTop 3,
    hQtop.eventually (eventually_ge_atTop 1),
    hlogtop.eventually (eventually_ge_atTop 1)] with x hx hQ hlog
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hlog0 : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hlog
  have hQcut : (mainCutoffNat x : ℝ) ≤
      (x : ℝ) / Real.log (x : ℝ) ^ 30 := by
    rw [← show proposition6MainCutoff x =
      (x : ℝ) / Real.log (x : ℝ) ^ 30 by rfl, mainCutoffNat_eq]
    exact Nat.floor_le (proposition6MainCutoff_nonneg x)
  have hsum : (totalEliminationBudget x (mainCutoffNat x) : ℝ) ≤
      600 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
    rw [totalEliminationBudget, Nat.cast_sum]
    calc
      ∑ q ∈ range (mainCutoffNat x + 1),
          (Erdos285.Lemma12.martinBlockBound x q : ℝ) ≤
          ∑ q ∈ range (mainCutoffNat x + 1),
            200 * ((x : ℝ) / q) ^ ((2 : ℝ) / 3) *
              Real.log (x : ℝ) ^ 3 := by
        apply Finset.sum_le_sum
        intro q hq
        exact Erdos285.Lemma12.martinBlockBound_cast_le hx1
      _ = ∑ q ∈ Icc 1 (mainCutoffNat x),
            200 * ((x : ℝ) / q) ^ ((2 : ℝ) / 3) *
              Real.log (x : ℝ) ^ 3 := by
        rw [show range (mainCutoffNat x + 1) = insert 0 (Icc 1 (mainCutoffNat x)) by
          ext q
          simp
          omega]
        simp
      _ = 200 * (x : ℝ) ^ ((2 : ℝ) / 3) *
            Real.log (x : ℝ) ^ 3 *
              (∑ q ∈ Icc 1 (mainCutoffNat x),
                (q : ℝ) ^ (-(2 : ℝ) / 3)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        have hqpos : (0 : ℝ) < q := by
          have : 1 ≤ q := (Finset.mem_Icc.mp hq).1
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one this)
        rw [div_rpow_two_thirds hx0 hqpos]
        ring
      _ ≤ 200 * (x : ℝ) ^ ((2 : ℝ) / 3) *
            Real.log (x : ℝ) ^ 3 *
              (3 * (mainCutoffNat x : ℝ) ^ ((1 : ℝ) / 3)) := by
        gcongr
        exact sum_Icc_rpow_neg_two_thirds_le _ hQ
      _ ≤ 200 * (x : ℝ) ^ ((2 : ℝ) / 3) *
            Real.log (x : ℝ) ^ 3 *
              (3 * ((x : ℝ) / Real.log (x : ℝ) ^ 30) ^
                ((1 : ℝ) / 3)) := by
        gcongr
      _ = 600 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
        calc
          200 * (x : ℝ) ^ ((2 : ℝ) / 3) * Real.log (x : ℝ) ^ 3 *
                (3 * ((x : ℝ) / Real.log (x : ℝ) ^ 30) ^
                  ((1 : ℝ) / 3)) =
              600 * ((x : ℝ) ^ ((2 : ℝ) / 3) *
                ((x : ℝ) / Real.log (x : ℝ) ^ 30) ^ ((1 : ℝ) / 3) *
                Real.log (x : ℝ) ^ 3) := by ring
          _ = 600 * ((x : ℝ) / Real.log (x : ℝ) ^ 7) := by
            rw [deletion_rpow_identity (by positivity) hlog0]
          _ = 600 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by ring
  have htarget : (totalEliminationBudget x (mainCutoffNat x) : ℝ) ≤
      1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
    calc
      (totalEliminationBudget x (mainCutoffNat x) : ℝ) ≤
          600 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := hsum
      _ ≤ 1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
        have hr : 0 ≤ (x : ℝ) / Real.log (x : ℝ) ^ 7 := by positivity
        calc
          600 * (x : ℝ) / Real.log (x : ℝ) ^ 7 =
              600 * ((x : ℝ) / Real.log (x : ℝ) ^ 7) := by ring
          _ ≤ 1000 * ((x : ℝ) / Real.log (x : ℝ) ^ 7) :=
            mul_le_mul_of_nonneg_right (by norm_num) hr
          _ = 1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by ring
  have hceil : 1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 ≤
      (proposition6DeletionBudget x : ℝ) := Nat.le_ceil _
  exact_mod_cast htarget.trans hceil

/-! ## Moving terminal intervals -/

private def movingEndpoint (x : ℕ) : ℕ :=
  ⌊Proposition4.martinLowerRatio x * (x : ℝ)⌋₊

lemma movingEndpoint_ratio_tendsto :
    Tendsto (fun x : ℕ ↦ (movingEndpoint x : ℝ) / (x : ℝ)) atTop
      (nhds (Real.exp (-1))) := by
  simpa [movingEndpoint] using Proposition4.martinLowerEndpoint_floor_ratio_tendsto

lemma movingEndpoint_tendsto_atTop : Tendsto movingEndpoint atTop atTop := by
  have hbase : Tendsto
      (fun x : ℕ ↦ ⌊oneLowerRatio * (x : ℝ)⌋₊) atTop atTop :=
    floorOneEndpoint_tendsto_atTop
  apply tendsto_atTop.2
  intro b
  filter_upwards [hbase.eventually (eventually_ge_atTop b),
    Proposition4.eventually_martinLowerRatio_bounds] with x hb halpha
  exact hb.trans (Nat.floor_mono
    (mul_le_mul_of_nonneg_right halpha.1.le (Nat.cast_nonneg x)))

lemma movingFullInitialInterval_reciprocalMass_tendsto_one :
    Tendsto
      (fun x : ℕ ↦ reciprocalMass
        (fullInitialIntervalAt (Proposition4.martinLowerRatio x) x))
      atTop (nhds 1) := by
  have herrorX := Real.tendsto_harmonic_sub_log
  have herrorA := Real.tendsto_harmonic_sub_log.comp movingEndpoint_tendsto_atTop
  have herror : Tendsto
      (fun x : ℕ ↦
        (((harmonic x : ℚ) : ℝ) - Real.log (x : ℝ)) -
        (((harmonic (movingEndpoint x) : ℚ) : ℝ) -
          Real.log (movingEndpoint x : ℝ)))
      atTop (nhds 0) := by
    simpa using herrorX.sub herrorA
  have hlogratio : Tendsto
      (fun x : ℕ ↦ Real.log ((movingEndpoint x : ℝ) / (x : ℝ)))
      atTop (nhds (-1)) := by
    have h := (Real.continuousAt_log (Real.exp_ne_zero (-1))).tendsto.comp
      movingEndpoint_ratio_tendsto
    simpa [Function.comp_def] using h
  have hlogdiff : Tendsto
      (fun x : ℕ ↦ Real.log (x : ℝ) - Real.log (movingEndpoint x : ℝ))
      atTop (nhds 1) := by
    have h : Tendsto
        (fun x : ℕ ↦ -Real.log ((movingEndpoint x : ℝ) / (x : ℝ)))
        atTop (nhds 1) := by simpa using hlogratio.neg
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ),
      movingEndpoint_tendsto_atTop.eventually (eventually_gt_atTop 0)]
        with x hx hA
    rw [Real.log_div (by positivity) (by positivity)]
    ring
  have htotal := herror.add hlogdiff
  have htotal' : Tendsto
      (fun x : ℕ ↦ ((harmonic x : ℚ) : ℝ) -
        ((harmonic (movingEndpoint x) : ℚ) : ℝ)) atTop (nhds 1) := by
    convert htotal using 1 <;> norm_num
    funext x
    ring
  apply htotal'.congr'
  filter_upwards [Proposition4.eventually_martinLowerRatio_bounds,
    eventually_gt_atTop (0 : ℕ)] with x halpha hx
  have hAle : movingEndpoint x ≤ x := by
    have hreal : (movingEndpoint x : ℝ) ≤ (x : ℝ) :=
      (Nat.floor_le (mul_nonneg
        ((Real.exp_pos (-1)).trans halpha.1).le (Nat.cast_nonneg x))).trans
        (mul_le_of_le_one_left (Nat.cast_nonneg x) halpha.2.le)
    exact_mod_cast hreal
  symm
  simpa [movingEndpoint, fullInitialIntervalAt] using
    reciprocalMass_Ioc_eq_harmonic_sub hAle

lemma movingInitialRoughPart_reciprocalMass_tendsto_zero :
    Tendsto
      (fun x : ℕ ↦ reciprocalMass
        (initialRoughPartAt (Proposition4.martinLowerRatio x) x))
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun x ↦ reciprocalMass_nonneg _
  · filter_upwards [Proposition4.eventually_martinLowerRatio_bounds]
      with x halpha
    apply reciprocalMass_mono (B := initialRoughPart x)
    intro n hn
    rw [initialRoughPartAt, mem_roughNumbersIn] at hn
    rw [initialRoughPart, mem_roughNumbersIn]
    refine ⟨?_, hn.2.1, hn.2.2⟩
    have hmul : oneLowerRatio * (x : ℝ) ≤
        Proposition4.martinLowerRatio x * (x : ℝ) := by
      exact mul_le_mul_of_nonneg_right halpha.1.le (Nat.cast_nonneg x)
    have hfloor : ⌊oneLowerRatio * (x : ℝ)⌋₊ ≤
        ⌊Proposition4.martinLowerRatio x * (x : ℝ)⌋₊ :=
      Nat.floor_mono hmul
    omega
  · exact initialRoughPart_reciprocalMass_tendsto_zero

lemma movingInitialBlock_reciprocalMass_tendsto_one :
    Tendsto
      (fun x : ℕ ↦ reciprocalMass
        (initialBlockAt (Proposition4.martinLowerRatio x) x))
      atTop (nhds 1) := by
  have h := movingFullInitialInterval_reciprocalMass_tendsto_one.sub
    movingInitialRoughPart_reciprocalMass_tendsto_zero
  have h' : Tendsto
      (fun x : ℕ ↦
        reciprocalMass (fullInitialIntervalAt (Proposition4.martinLowerRatio x) x) -
          reciprocalMass (initialRoughPartAt (Proposition4.martinLowerRatio x) x))
      atTop (nhds 1) := by simpa using h
  apply h'.congr'
  filter_upwards with x
  rw [initialBlockAt_eq_sdiff,
    reciprocalMass_sdiff (initialRoughPartAt_subset_full _ _)]

lemma movingInitialResidual_tendsto_zero :
    Tendsto
      (fun x : ℕ ↦
        (initialResidual (1 : ℚ) (Proposition4.martinLowerRatio x) x
          (proposition6MainCutoff x) : ℝ))
      atTop (nhds 0) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop
    (nhds 1)).sub movingInitialBlock_reciprocalMass_tendsto_one
  simpa [initialResidual, initialBlockAt, ratCast_recSum_eq_reciprocalMass] using h

/-! ## Quantitative positive lower margin -/

lemma log_one_add_lower {t : ℝ} (ht0 : 0 ≤ t) :
    t / (1 + t) ≤ Real.log (1 + t) := by
  have hpos : 0 < 1 + t := by linarith
  have hinv : 0 < (1 + t)⁻¹ := inv_pos.mpr hpos
  have h := Real.log_le_sub_one_of_pos hinv
  rw [Real.log_inv] at h
  have hne : 1 + t ≠ 0 := hpos.ne'
  field_simp at h ⊢
  nlinarith

lemma eventually_moving_full_residual_ge_margin_quarter :
    ∀ᶠ x : ℕ in atTop,
      Proposition4.martinMargin x / 4 ≤
        1 - reciprocalMass
          (fullInitialIntervalAt (Proposition4.martinLowerRatio x) x) := by
  have hmargin0 := Proposition4.martinMargin_tendsto_zero
  have hmargintop := Proposition4.martinMargin_mul_t_tendsto_atTop
  filter_upwards [Proposition4.eventually_martinLowerRatio_bounds,
    Proposition4.martinMargin_pos,
    hmargin0.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    hmargintop.eventually (eventually_ge_atTop 2),
    eventually_ge_atTop 3] with x halpha hmpos hmle hmx hx
  let a := movingEndpoint x
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hapos : 0 < a := by
    have hax : (1 : ℝ) ≤ Proposition4.martinMargin x * (x : ℝ) := by
      linarith
    have hbase : 0 ≤ Real.exp (-1) * (x : ℝ) := by positivity
    have hscale : (1 : ℝ) ≤
        Proposition4.martinLowerRatio x * (x : ℝ) := by
      rw [Proposition4.martinLowerRatio]
      nlinarith
    have : 1 ≤ a := by
      change 1 ≤ movingEndpoint x
      rw [movingEndpoint, Nat.one_le_floor_iff]
      exact hscale
    omega
  have hale : a ≤ x := by
    have hreal : (a : ℝ) ≤ (x : ℝ) := by
      dsimp [a, movingEndpoint]
      exact (Nat.floor_le (mul_nonneg
        ((Real.exp_pos (-1)).trans halpha.1).le (Nat.cast_nonneg x))).trans
        (mul_le_of_le_one_left (Nat.cast_nonneg x) halpha.2.le)
    exact_mod_cast hreal
  have heuler :
      ((harmonic x : ℚ) : ℝ) - Real.log (x : ℝ) ≤
        ((harmonic a : ℚ) : ℝ) - Real.log (a : ℝ) := by
    simpa [Real.eulerMascheroniSeq', (show x ≠ 0 by omega),
      (show a ≠ 0 by omega)] using
      Real.strictAnti_eulerMascheroniSeq'.antitone hale
  have hmass : reciprocalMass
      (fullInitialIntervalAt (Proposition4.martinLowerRatio x) x) =
      ((harmonic x : ℚ) : ℝ) - ((harmonic a : ℚ) : ℝ) := by
    simpa [a, movingEndpoint, fullInitialIntervalAt] using
      reciprocalMass_Ioc_eq_harmonic_sub hale
  have hafloor : Proposition4.martinLowerRatio x * (x : ℝ) - 1 ≤
      (a : ℝ) := by
    dsimp [a, movingEndpoint]
    have h := (Nat.lt_floor_add_one
      (Proposition4.martinLowerRatio x * (x : ℝ))).le
    linarith
  have haRatio : Real.exp (-1) + Proposition4.martinMargin x / 2 ≤
      (a : ℝ) / (x : ℝ) := by
    rw [Proposition4.martinLowerRatio] at hafloor
    rw [le_div_iff₀ hxpos]
    have hhalf : (1 : ℝ) ≤ Proposition4.martinMargin x * (x : ℝ) / 2 := by
      linarith
    nlinarith
  have haRatioPos : 0 < (a : ℝ) / (x : ℝ) := div_pos (by exact_mod_cast hapos) hxpos
  have hlogRatio : Real.log (Real.exp (-1) + Proposition4.martinMargin x / 2) ≤
      Real.log ((a : ℝ) / (x : ℝ)) :=
    Real.log_le_log (by positivity) haRatio
  let t : ℝ := Real.exp 1 * Proposition4.martinMargin x / 2
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ Real.exp 1 / 2 := by
    dsimp [t]
    exact div_le_div_of_nonneg_right
      (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hmle.le (Real.exp_pos (1 : ℝ)).le)
      (by norm_num)
  have htDiv : Proposition4.martinMargin x / 4 ≤ t / (1 + t) := by
    have hden : 1 + t ≤ Real.exp 1 := by
      dsimp [t]
      have hexp2 : (2 : ℝ) ≤ Real.exp 1 := by
        linarith [Real.exp_one_gt_d9]
      nlinarith
    have htEq : t = Real.exp 1 * Proposition4.martinMargin x / 2 := rfl
    rw [htEq]
    have htpos : 0 < 1 + t := by dsimp [t]; positivity
    apply (le_div_iff₀ htpos).2
    calc
      Proposition4.martinMargin x / 4 * (1 + t) ≤
          Proposition4.martinMargin x / 4 * Real.exp 1 :=
        mul_le_mul_of_nonneg_left hden (div_nonneg hmpos.le (by norm_num))
      _ ≤ Real.exp 1 * Proposition4.martinMargin x / 2 := by
        nlinarith [Real.exp_pos (1 : ℝ), hmpos]
  have hlogLower : Proposition4.martinMargin x / 4 ≤ Real.log (1 + t) :=
    htDiv.trans (log_one_add_lower ht0)
  have hfactor : Real.exp (-1) + Proposition4.martinMargin x / 2 =
      Real.exp (-1) * (1 + t) := by
    dsimp [t]
    have hexp : Real.exp (-1) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]
      norm_num
    calc
      Real.exp (-1) + Proposition4.martinMargin x / 2 =
          Real.exp (-1) +
            (Real.exp (-1) * Real.exp 1) * Proposition4.martinMargin x / 2 := by
        rw [hexp, one_mul]
      _ = Real.exp (-1) *
          (1 + Real.exp 1 * Proposition4.martinMargin x / 2) := by ring
  have hlogGap : Proposition4.martinMargin x / 4 ≤
      1 + Real.log ((a : ℝ) / (x : ℝ)) := by
    calc
      Proposition4.martinMargin x / 4 ≤ Real.log (1 + t) := hlogLower
      _ = 1 + Real.log (Real.exp (-1) + Proposition4.martinMargin x / 2) := by
        rw [hfactor, Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp]
        ring
      _ ≤ 1 + Real.log ((a : ℝ) / (x : ℝ)) := by linarith
  rw [hmass]
  have haRne : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hapos)
  rw [Real.log_div haRne hxpos.ne'] at hlogGap
  have htail : ((harmonic x : ℚ) : ℝ) - ((harmonic a : ℚ) : ℝ) ≤
      Real.log (x : ℝ) - Real.log (a : ℝ) := by linarith
  linarith

/-! ## The moving errors are smaller than the positive margin -/

lemma eventually_moving_budget_ratio_le_log_pow :
    ∀ᶠ x : ℕ in atTop,
      (proposition6DeletionBudget x : ℝ) /
          (Real.exp (-1) * (x : ℝ)) ≤
        (1001 / Real.exp (-1)) * (Real.log (x : ℝ) ^ 7)⁻¹ := by
  have hscale : Tendsto
      (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ) ^ 7) atTop atTop := by
    have h := (UnitFractions.tendsto_mul_add_div_pow_log_at_top
      (1 : ℝ) 0 7 zero_lt_one).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using h
  filter_upwards [hscale.eventually (eventually_ge_atTop 1), eventually_ge_atTop 3]
      with x hscale1 hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hceil : (proposition6DeletionBudget x : ℝ) ≤
      1001 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by
    calc
      (proposition6DeletionBudget x : ℝ) ≤
          1000 * (x : ℝ) / Real.log (x : ℝ) ^ 7 + 1 :=
        (Nat.ceil_lt_add_one (by positivity)).le
      _ = 1000 * ((x : ℝ) / Real.log (x : ℝ) ^ 7) + 1 := by ring
      _ ≤ 1000 * ((x : ℝ) / Real.log (x : ℝ) ^ 7) +
          ((x : ℝ) / Real.log (x : ℝ) ^ 7) := by
        exact add_le_add (le_refl _) hscale1
      _ = 1001 * (x : ℝ) / Real.log (x : ℝ) ^ 7 := by ring
  calc
    (proposition6DeletionBudget x : ℝ) /
        (Real.exp (-1) * (x : ℝ)) ≤
      (1001 * (x : ℝ) / Real.log (x : ℝ) ^ 7) /
        (Real.exp (-1) * (x : ℝ)) := by
      exact div_le_div_of_nonneg_right hceil (by positivity)
    _ = (1001 / Real.exp (-1)) * (Real.log (x : ℝ) ^ 7)⁻¹ := by
      field_simp

lemma moving_errors_div_margin_tendsto_zero :
    Tendsto
      (fun x : ℕ ↦
        ((Real.log (x : ℝ))⁻¹ +
          4 * ((proposition6DeletionBudget x : ℝ) /
            (Real.exp (-1) * (x : ℝ)))) /
          Proposition4.martinMargin x)
      atTop (nhds 0) := by
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    tendsto_log_coe_at_top
  have hfirst : Tendsto
      (fun x : ℕ ↦ (Real.sqrt (Real.log (x : ℝ)))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hlogTop)
  have hsecond : Tendsto
      (fun x : ℕ ↦ (1001 / Real.exp (-1)) *
        Real.log (x : ℝ) ^ (-(13 : ℝ) / 2)) atTop (nhds 0) := by
    have hpow := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 13 / 2)).comp hlogTop
    convert hpow.const_mul (1001 / Real.exp (-1)) using 1 <;> norm_num
  have hupper := hfirst.add (hsecond.const_mul 4)
  apply squeeze_zero' (g := fun x : ℕ ↦
    (Real.sqrt (Real.log (x : ℝ)))⁻¹ +
      4 * ((1001 / Real.exp (-1)) *
        Real.log (x : ℝ) ^ (-(13 : ℝ) / 2)))
  · filter_upwards [eventually_ge_atTop 3,
      Proposition4.eventually_martinLowerRatio_bounds,
      Proposition4.martinMargin_pos] with x hx halpha hm
    have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    have halphapos : 0 < Proposition4.martinLowerRatio x :=
      (Real.exp_pos _).trans halpha.1
    have hlognonneg : 0 ≤ Real.log (x : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
    exact div_nonneg
      (add_nonneg (inv_nonneg.mpr hlognonneg)
        (mul_nonneg (by norm_num) (div_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (Real.exp_pos (-1)).le hxpos.le)))) hm.le
  · filter_upwards [eventually_moving_budget_ratio_le_log_pow,
      eventually_ge_atTop 3, Proposition4.martinMargin_pos]
      with x hbudget hx hm
    have hlog : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    have hsqrt : 0 < Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_pos.2 hlog
    have hmargin : Proposition4.martinMargin x =
        (Real.sqrt (Real.log (x : ℝ)))⁻¹ := rfl
    have hbudget' := mul_le_mul_of_nonneg_left hbudget (by norm_num : (0 : ℝ) ≤ 4)
    have hpowid : (Real.log (x : ℝ) ^ 7)⁻¹ *
        Real.sqrt (Real.log (x : ℝ)) =
        Real.log (x : ℝ) ^ (-(13 : ℝ) / 2) := by
      rw [← Real.rpow_natCast (Real.log (x : ℝ)) 7,
        ← Real.rpow_neg hlog.le, Real.sqrt_eq_rpow]
      rw [← Real.rpow_add hlog]
      norm_num
    rw [hmargin, div_inv_eq_mul, add_mul]
    have hfirstId : (Real.log (x : ℝ))⁻¹ *
        Real.sqrt (Real.log (x : ℝ)) =
        (Real.sqrt (Real.log (x : ℝ)))⁻¹ := by
      field_simp [hsqrt.ne', hlog.ne']
      rw [Real.sq_sqrt hlog.le]
    have hbmul := mul_le_mul_of_nonneg_right hbudget' hsqrt.le
    calc
      (Real.log (x : ℝ))⁻¹ * Real.sqrt (Real.log (x : ℝ)) +
          (4 * ((proposition6DeletionBudget x : ℝ) /
            (Real.exp (-1) * (x : ℝ)))) *
            Real.sqrt (Real.log (x : ℝ)) ≤
        (Real.sqrt (Real.log (x : ℝ)))⁻¹ +
          (4 * ((1001 / Real.exp (-1)) * (Real.log (x : ℝ) ^ 7)⁻¹)) *
            Real.sqrt (Real.log (x : ℝ)) := by
              rw [hfirstId]
              simpa [add_comm] using
                add_le_add_left hbmul (Real.sqrt (Real.log (x : ℝ)))⁻¹
      _ = (Real.sqrt (Real.log (x : ℝ)))⁻¹ +
          4 * ((1001 / Real.exp (-1)) *
            Real.log (x : ℝ) ^ (-(13 : ℝ) / 2)) := by
              rw [← hpowid]
              ring
  · simpa using hupper

theorem eventually_moving_initial_residual_margins :
    ∀ᶠ x : ℕ in atTop,
      (Real.log (x : ℝ))⁻¹ +
          4 * ((proposition6DeletionBudget x : ℝ) /
            (Real.exp (-1) * (x : ℝ))) <
        (initialResidual (1 : ℚ) (Proposition4.martinLowerRatio x) x
          (proposition6MainCutoff x) : ℝ) ∧
      (initialResidual (1 : ℚ) (Proposition4.martinLowerRatio x) x
          (proposition6MainCutoff x) : ℝ) +
          (proposition6DeletionBudget x : ℝ) /
            (Proposition4.martinLowerRatio x * (x : ℝ)) < 1 := by
  have hnormalized := moving_errors_div_margin_tendsto_zero.eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  have hbudgetZero : Tendsto
      (fun x : ℕ ↦ (proposition6DeletionBudget x : ℝ) /
        (Proposition4.martinLowerRatio x * (x : ℝ))) atTop (nhds 0) := by
    have hupper : Tendsto
        (fun x : ℕ ↦ (1001 / Real.exp (-1)) *
          (Real.log (x : ℝ) ^ 7)⁻¹) atTop (nhds 0) := by
      have htop := (tendsto_pow_atTop (by norm_num : (7 : ℕ) ≠ 0)).comp
        tendsto_log_coe_at_top
      simpa using (tendsto_inv_atTop_zero.comp htop).const_mul
        (1001 / Real.exp (-1))
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop 1,
        Proposition4.eventually_martinLowerRatio_bounds] with x hx ha
      have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
      have hapos : 0 < Proposition4.martinLowerRatio x :=
        (Real.exp_pos _).trans ha.1
      exact div_nonneg (Nat.cast_nonneg _)
        (mul_nonneg hapos.le hxpos.le)
    · filter_upwards [eventually_moving_budget_ratio_le_log_pow,
        Proposition4.eventually_martinLowerRatio_bounds,
        eventually_ge_atTop 1] with x hfixed halpha hx
      have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
      have hden : Real.exp (-1) * (x : ℝ) ≤
          Proposition4.martinLowerRatio x * (x : ℝ) :=
        mul_le_mul_of_nonneg_right halpha.1.le hxpos.le
      exact (div_le_div_of_nonneg_left (Nat.cast_nonneg _)
        (mul_pos (Real.exp_pos _) hxpos) hden).trans hfixed
    · exact hupper
  have hsum : Tendsto
      (fun x : ℕ ↦
        (initialResidual (1 : ℚ) (Proposition4.martinLowerRatio x) x
          (proposition6MainCutoff x) : ℝ) +
        (proposition6DeletionBudget x : ℝ) /
          (Proposition4.martinLowerRatio x * (x : ℝ)))
      atTop (nhds 0) := by
    simpa using movingInitialResidual_tendsto_zero.add hbudgetZero
  have hupper := hsum.eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [eventually_moving_full_residual_ge_margin_quarter,
    hnormalized, hupper, Proposition4.martinMargin_pos]
      with x hfull hnorm hup hm
  constructor
  · have herr : (Real.log (x : ℝ))⁻¹ +
        4 * ((proposition6DeletionBudget x : ℝ) /
          (Real.exp (-1) * (x : ℝ))) <
        Proposition4.martinMargin x / 4 := by
      rw [div_lt_iff₀ hm] at hnorm
      nlinarith
    have hsmoothLeFull : reciprocalMass
        (initialBlockAt (Proposition4.martinLowerRatio x) x) ≤
        reciprocalMass
          (fullInitialIntervalAt (Proposition4.martinLowerRatio x) x) := by
      exact reciprocalMass_mono (by
        rw [initialBlockAt_eq_sdiff]
        exact Finset.sdiff_subset)
    have hres : Proposition4.martinMargin x / 4 ≤
        (initialResidual (1 : ℚ) (Proposition4.martinLowerRatio x) x
          (proposition6MainCutoff x) : ℝ) := by
      rw [initialResidual]
      rw [Rat.cast_sub, Rat.cast_one]
      rw [ratCast_recSum_eq_reciprocalMass]
      change Proposition4.martinMargin x / 4 ≤
        1 - reciprocalMass (initialBlockAt (Proposition4.martinLowerRatio x) x)
      linarith
    exact herr.trans_le hres
  · exact hup

/-! ## Final bundled form -/

/-- The three moving estimates consumed by the final Proposition 6
constructor.  The lower error is stated with the fixed lower bound
`exp (-1)`, while the upper error retains the sharper moving denominator. -/
theorem eventually_moving_proposition6_bounds :
    ∀ᶠ x : ℕ in atTop,
      (Real.log (x : ℝ))⁻¹ +
          4 * ((proposition6DeletionBudget x : ℝ) /
            (Real.exp (-1) * (x : ℝ))) <
        (initialResidual (1 : ℚ) (Proposition4.martinLowerRatio x) x
          (proposition6MainCutoff x) : ℝ) ∧
      (initialResidual (1 : ℚ) (Proposition4.martinLowerRatio x) x
          (proposition6MainCutoff x) : ℝ) +
          (proposition6DeletionBudget x : ℝ) /
            (Proposition4.martinLowerRatio x * (x : ℝ)) < 1 ∧
      totalEliminationBudget x ⌊proposition6MainCutoff x⌋₊ ≤
        proposition6DeletionBudget x := by
  filter_upwards [eventually_moving_initial_residual_margins,
    eventually_totalEliminationBudget_mainCutoff_le] with x hmargins hbudget
  simpa [mainCutoffNat_eq] using ⟨hmargins.1, hmargins.2, hbudget⟩

end

end Erdos285

#print axioms Erdos285.eventually_moving_proposition6_bounds
