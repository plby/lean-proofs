import ErdosProblems.Erdos67.LogBandSelector
import ErdosProblems.Erdos67.LogBandDecay
import ErdosProblems.Erdos67.ResidueLogPhaseBounds

/-! # Uniform epsilon bound for a fixed finite set of logarithmic bands -/

open scoped BigOperators
open Filter

namespace Erdos67.ResidueFixedDepthEpsilon

noncomputable section

open Erdos1149
open Erdos67.LogPhaseSum
open Erdos67.LogPhaseHigherDerivative
open Erdos67.ResidueLogPhase
open Erdos67.ResidueLogPhaseBounds
open Erdos67.LogBandCoverage
open Erdos67.LogBandSelector
open Erdos67.LogBandDecay
open Erdos67.LogWeylParameters

theorem norm_residueClassSum_natLogTwist_le_length
    {q A M : ℕ} [NeZero q] (c : ZMod q) (t : ℝ) (hA : 0 < A) :
    ‖LSeriesLogPhaseBridge.residueClassSum (Finset.Icc A M) c
        (fun n ↦ natLogTwist n t)‖ ≤ residueIntervalLength A M c := by
  rw [norm_residueClassSum_natLogTwist_eq_positiveShifted c t hA]
  calc
    ‖∑ j ∈ Finset.range (residueIntervalLength A M c),
        HigherDerivative.phase
          (shiftedLogPhase (positiveLogCoefficient t)
            ((firstResidueAtOrAbove A c : ℝ) / q) j)‖ ≤
        ∑ j ∈ Finset.range (residueIntervalLength A M c),
          ‖HigherDerivative.phase
            (shiftedLogPhase (positiveLogCoefficient t)
              ((firstResidueAtOrAbove A c : ℝ) / q) j)‖ := norm_sum_le _ _
    _ = residueIntervalLength A M c := by simp

private theorem eventually_lagBudget_le_mul {η : ℝ} (hη : 0 < η) :
    ∀ᶠ X : ℕ in atTop,
      (rOneLagBudget X : ℝ) ≤ η * X := by
  have htR : Tendsto (fun x : ℝ ↦ x ^ (-(15 / 16 : ℝ))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have ht : Tendsto
      (fun X : ℕ ↦ 2 * (X : ℝ) ^ (-(15 / 16 : ℝ))) atTop (nhds 0) := by
    simpa using (htR.comp tendsto_natCast_atTop_atTop).const_mul 2
  have hsmall : ∀ᶠ X : ℕ in atTop,
      2 * (X : ℝ) ^ (-(15 / 16 : ℝ)) ≤ η :=
    ((tendsto_order.1 ht).2 _ hη).mono fun _ h ↦ h.le
  filter_upwards [eventually_ge_atTop (1 : ℕ), hsmall] with X hX hsmallX
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hceil : (rOneLagBudget X : ℝ) ≤
      2 * (X : ℝ) ^ (1 / 16 : ℝ) := by
    unfold rOneLagBudget
    exact AnalyticParameters.natCeil_le_two_mul
      (Real.one_le_rpow hXR (by norm_num))
  have hsplit : 2 * (X : ℝ) ^ (1 / 16 : ℝ) =
      (2 * (X : ℝ) ^ (-(15 / 16 : ℝ))) * X := by
    have hXpos : 0 < (X : ℝ) := zero_lt_one.trans_le hXR
    have hxid : (X : ℝ) ^ (1 / 16 : ℝ) =
        (X : ℝ) ^ (-(15 / 16 : ℝ)) * X := by
      calc
        (X : ℝ) ^ (1 / 16 : ℝ) =
            (X : ℝ) ^ (-(15 / 16 : ℝ) + 1) := by norm_num
        _ = (X : ℝ) ^ (-(15 / 16 : ℝ)) * (X : ℝ) ^ (1 : ℝ) :=
          Real.rpow_add hXpos _ _
        _ = (X : ℝ) ^ (-(15 / 16 : ℝ)) * X := by
          rw [Real.rpow_one]
    rw [hxid, mul_assoc]
  calc
    (rOneLagBudget X : ℝ) ≤ 2 * (X : ℝ) ^ (1 / 16 : ℝ) := hceil
    _ = (2 * (X : ℝ) ^ (-(15 / 16 : ℝ))) * X := hsplit
    _ ≤ η * X := mul_le_mul_of_nonneg_right hsmallX (by positivity)

/-- After fixing a finite maximum depth, every sufficiently large dyadic
residue prefix in the height range `[U, X^(R+1))` has arbitrarily small
linear norm.  The final `+1` is solely the closed-interval endpoint. -/
theorem exists_residuePrefix_epsilon_threshold
    (R : ℕ) (hR : 2 ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ {q A M : ℕ} [NeZero q] (c : ZMod q) {t : ℝ},
      0 < A → M ≤ 2 * A → t ≠ 0 →
      X₀ ≤ firstResidueAtOrAbove A c / q →
      (firstResidueAtOrAbove A c : ℝ) / q ≤ positiveLogCoefficient t →
      positiveLogCoefficient t <
        ((firstResidueAtOrAbove A c / q : ℕ) : ℝ) ^ (R + 1) →
      ‖LSeriesLogPhaseBridge.residueClassSum (Finset.Icc A M) c
          (fun n ↦ natLogTwist n t)‖ ≤
        ε * ((firstResidueAtOrAbove A c : ℝ) / q) + 1 := by
  obtain ⟨Xdecay, hdecay⟩ :=
    exists_finiteBandDecay_threshold R (half_pos hε)
  obtain ⟨Xfixed, hfixed⟩ := exists_residue_fixedDepthRange_threshold R
  obtain ⟨Xlag, hlag⟩ := eventually_atTop.1
    (eventually_lagBudget_le_mul hε)
  obtain ⟨Xselect, hselect⟩ := eventually_atTop.1
    (eventually_fixedDepth_selector R hR)
  refine ⟨max 1 (max Xdecay (max Xfixed (max Xlag Xselect))), ?_⟩
  intro q A M _ c t hA hM ht hscale hUa hupper
  let X : ℕ := firstResidueAtOrAbove A c / q
  let U : ℝ := (firstResidueAtOrAbove A c : ℝ) / q
  let a : ℝ := positiveLogCoefficient t
  let P : ℕ := residueIntervalLength A M c
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hXone : 1 ≤ X :=
    (Nat.le_max_left 1 _).trans hscale
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hXone
  have hXpos : 0 < (X : ℝ) := zero_lt_one.trans_le hXR
  have hU : 0 < U := by
    dsimp only [U]
    have hn₀ := firstResidueAtOrAbove_pos c hA
    positivity
  have ha : 0 < a := by
    dsimp only [a]
    exact positiveLogCoefficient_pos ht
  have hXU : (X : ℝ) ≤ U := by
    dsimp only [X, U]
    exact Nat.cast_div_le
  have hUlt : U < (X : ℝ) + 1 := by
    have hnat : firstResidueAtOrAbove A c <
        q * (firstResidueAtOrAbove A c / q + 1) := by
      simpa only [mul_comm] using
        Nat.lt_mul_div_succ (firstResidueAtOrAbove A c) hq
    apply (div_lt_iff₀ (by exact_mod_cast hq : (0 : ℝ) < q)).2
    exact_mod_cast (by simpa only [X, mul_comm] using hnat)
  have hUX : U ≤ 2 * X := by linarith
  have hdecayX : finiteBandDecay R X ≤ ε / 2 :=
    hdecay X ((Nat.le_max_left Xdecay _).trans
      ((Nat.le_max_right 1 (max Xdecay (max Xfixed (max Xlag Xselect)))).trans
        hscale))
  have hfixedX : Xfixed ≤ X :=
    (Nat.le_max_left Xfixed (max Xlag Xselect)).trans
      ((Nat.le_max_right Xdecay (max Xfixed (max Xlag Xselect))).trans
        ((Nat.le_max_right 1 (max Xdecay (max Xfixed (max Xlag Xselect)))).trans
          hscale))
  have hlagX : (rOneLagBudget X : ℝ) ≤ ε * X :=
    hlag X ((Nat.le_max_left Xlag Xselect).trans
      ((Nat.le_max_right Xfixed (max Xlag Xselect)).trans
        ((Nat.le_max_right Xdecay (max Xfixed (max Xlag Xselect))).trans
          ((Nat.le_max_right 1 (max Xdecay (max Xfixed (max Xlag Xselect)))).trans
            hscale))))
  have hselectX := hselect X
    ((Nat.le_max_right Xlag Xselect).trans
      ((Nat.le_max_right Xfixed (max Xlag Xselect)).trans
        ((Nat.le_max_right Xdecay (max Xfixed (max Xlag Xselect))).trans
          ((Nat.le_max_right 1 (max Xdecay (max Xfixed (max Xlag Xselect)))).trans
            hscale)))) (a := a) (U := U)
  by_cases hPzero : P = 0
  · have htriv := norm_residueClassSum_natLogTwist_le_length (M := M) c t hA
    have hzero : residueIntervalLength A M c = 0 := by
      simpa only [P] using hPzero
    have hnorm : ‖LSeriesLogPhaseBridge.residueClassSum (Finset.Icc A M) c
        (fun n ↦ natLogTwist n t)‖ ≤ 0 := by
      simpa only [hzero, Nat.cast_zero] using htriv
    have hrhs : 0 ≤ ε * U + 1 := by positivity
    exact hnorm.trans (by simpa only [U] using hrhs)
  by_cases hPlong : rOneLagBudget X + 1 ≤ P
  · have hsel := hselectX ha hXU hUX
        (by simpa only [U, a] using hUa)
        (by simpa only [X, a] using hupper)
    rcases hsel with hsecond | ⟨r, hrmem, hrband, hrupper⟩
    · have hb := norm_residueClassSum_natLogTwist_le_rOnePower
        c hA hM (by simpa only [X] using hXone)
        (by simpa only [X, P] using hPlong)
        (by simpa only [U, a] using hUa)
        (by simpa only [X, U, a] using hsecond)
      have hfirst : 18 * (X : ℝ) ^ (63 / 64 : ℝ) ≤
          2 * finiteBandDecay R X * X := by
        have hsplit : (X : ℝ) ^ (63 / 64 : ℝ) =
            (X : ℝ) ^ (-1 / 64 : ℝ) * X := by
          calc
            (X : ℝ) ^ (63 / 64 : ℝ) =
                (X : ℝ) ^ ((-1 / 64 : ℝ) + 1) := by norm_num
            _ = (X : ℝ) ^ (-1 / 64 : ℝ) * (X : ℝ) ^ (1 : ℝ) :=
              Real.rpow_add hXpos _ _
            _ = (X : ℝ) ^ (-1 / 64 : ℝ) * X := by rw [Real.rpow_one]
        rw [hsplit]
        have hpart : 9 * (X : ℝ) ^ (-1 / 64 : ℝ) ≤
            finiteBandDecay R X := by
          unfold finiteBandDecay
          exact le_add_of_nonneg_right (Finset.sum_nonneg fun r hr ↦
            mul_nonneg (realStartBandConstant_nonneg r)
              (Real.rpow_nonneg (Nat.cast_nonneg X) _))
        nlinarith [mul_le_mul_of_nonneg_right hpart (show 0 ≤ (X : ℝ) by positivity)]
      calc
        ‖LSeriesLogPhaseBridge.residueClassSum (Finset.Icc A M) c
            (fun n ↦ natLogTwist n t)‖ ≤
            18 * (X : ℝ) ^ (63 / 64 : ℝ) + 1 := by
          simpa only [X] using hb
        _ ≤ 2 * finiteBandDecay R X * X + 1 := by linarith
        _ ≤ ε * U + 1 := by
          have : 2 * finiteBandDecay R X ≤ ε := by linarith
          nlinarith [mul_le_mul_of_nonneg_right this (show 0 ≤ (X : ℝ) by positivity)]
    · have hPpos : 0 < residueIntervalLength A M c := by
        simpa only [P] using Nat.pos_of_ne_zero hPzero
      have hb := hfixed c r hrmem hA hM ht hPpos
        (by simpa only [X] using hfixedX)
        (by simpa only [X, a] using hrband)
        (by simpa only [X, a] using hrupper)
      let C := realStartBandConstant r
      have hterm : C * (X : ℝ) ^ (-savingExponent r) ≤
          finiteBandDecay R X := by
        unfold finiteBandDecay
        have hsingle : C * (X : ℝ) ^ (-savingExponent r) ≤
            ∑ i ∈ Finset.Icc 2 R,
              realStartBandConstant i * (X : ℝ) ^ (-savingExponent i) := by
          simpa only [C] using
            (Finset.single_le_sum
              (fun i (_ : i ∈ Finset.Icc 2 R) ↦
                mul_nonneg (realStartBandConstant_nonneg i)
                  (Real.rpow_nonneg (Nat.cast_nonneg X)
                    (-savingExponent i))) hrmem)
        exact hsingle.trans (le_add_of_nonneg_left (by positivity))
      have hsplit : C * (X : ℝ) ^ (1 - savingExponent r) =
          (C * (X : ℝ) ^ (-savingExponent r)) * X := by
        have hxid : (X : ℝ) ^ (1 - savingExponent r) =
            (X : ℝ) ^ (-savingExponent r) * X := by
          calc
            (X : ℝ) ^ (1 - savingExponent r) =
                (X : ℝ) ^ (-savingExponent r + 1) := by ring_nf
            _ = (X : ℝ) ^ (-savingExponent r) * (X : ℝ) ^ (1 : ℝ) :=
              Real.rpow_add hXpos _ _
            _ = (X : ℝ) ^ (-savingExponent r) * X := by rw [Real.rpow_one]
        rw [hxid, mul_assoc]
      have hmain : C * (X : ℝ) ^ (1 - savingExponent r) ≤
          finiteBandDecay R X * X := by
        rw [hsplit]
        exact mul_le_mul_of_nonneg_right hterm (by positivity)
      calc
        ‖LSeriesLogPhaseBridge.residueClassSum (Finset.Icc A M) c
            (fun n ↦ natLogTwist n t)‖ ≤
            C * (X : ℝ) ^ (1 - savingExponent r) + 1 := by
          simpa only [X, C, realStartBandConstant] using hb
        _ ≤ finiteBandDecay R X * X + 1 := by linarith
        _ ≤ ε * U + 1 := by
          have hdε : finiteBandDecay R X ≤ ε := hdecayX.trans (by linarith)
          have hm := mul_le_mul_of_nonneg_right hdε (show 0 ≤ (X : ℝ) by positivity)
          nlinarith
  · have hPsmall : P ≤ rOneLagBudget X := by omega
    have htriv := norm_residueClassSum_natLogTwist_le_length (M := M) c t hA
    calc
      ‖LSeriesLogPhaseBridge.residueClassSum (Finset.Icc A M) c
          (fun n ↦ natLogTwist n t)‖ ≤ P := by simpa only [P] using htriv
      _ ≤ rOneLagBudget X := by exact_mod_cast hPsmall
      _ ≤ ε * X := hlagX
      _ ≤ ε * U + 1 := by
        have := mul_le_mul_of_nonneg_left hXU hε.le
        linarith

/-- The normalized form used by dyadic Abel summation.  At a larger uniform
threshold the single closed-interval endpoint is absorbed into the requested
multiple of the integer comparison scale. -/
theorem exists_residuePrefix_mul_comparison_threshold
    (R : ℕ) (hR : 2 ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ {q A M : ℕ} [NeZero q] (c : ZMod q) {t : ℝ},
      0 < A → M ≤ 2 * A → t ≠ 0 →
      X₀ ≤ firstResidueAtOrAbove A c / q →
      (firstResidueAtOrAbove A c : ℝ) / q ≤ positiveLogCoefficient t →
      positiveLogCoefficient t <
        ((firstResidueAtOrAbove A c / q : ℕ) : ℝ) ^ (R + 1) →
      ‖LSeriesLogPhaseBridge.residueClassSum (Finset.Icc A M) c
          (fun n ↦ natLogTwist n t)‖ ≤
        ε * (firstResidueAtOrAbove A c / q : ℕ) := by
  obtain ⟨Xbase, hbase⟩ :=
    exists_residuePrefix_epsilon_threshold R hR (show 0 < ε / 4 by positivity)
  obtain ⟨Xend : ℕ, hXend⟩ := exists_nat_ge (2 / ε)
  refine ⟨max 1 (max Xbase Xend), ?_⟩
  intro q A M _ c t hA hM ht hscale hUa hupper
  let X : ℕ := firstResidueAtOrAbove A c / q
  let U : ℝ := (firstResidueAtOrAbove A c : ℝ) / q
  have hXbase : Xbase ≤ X :=
    (Nat.le_max_left Xbase Xend).trans
      ((Nat.le_max_right 1 (max Xbase Xend)).trans hscale)
  have hbound := hbase c hA hM ht
    (by simpa only [X] using hXbase) hUa hupper
  have hXone : 1 ≤ X :=
    (Nat.le_max_left 1 _).trans hscale
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hXone
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hUlt : U < (X : ℝ) + 1 := by
    have hnat : firstResidueAtOrAbove A c <
        q * (firstResidueAtOrAbove A c / q + 1) := by
      simpa only [mul_comm] using
        Nat.lt_mul_div_succ (firstResidueAtOrAbove A c) hq
    apply (div_lt_iff₀ (by exact_mod_cast hq : (0 : ℝ) < q)).2
    exact_mod_cast (by simpa only [X, mul_comm] using hnat)
  have hUtwo : U ≤ 2 * X := by linarith
  have hXendX : Xend ≤ X :=
    (Nat.le_max_right Xbase Xend).trans
      ((Nat.le_max_right 1 (max Xbase Xend)).trans hscale)
  have htwo : (2 / ε : ℝ) ≤ X :=
    hXend.trans (by exact_mod_cast hXendX)
  have hone : (1 : ℝ) ≤ (ε / 2) * X := by
    calc
      (1 : ℝ) = (ε / 2) * (2 / ε) := by field_simp
      _ ≤ (ε / 2) * X :=
        mul_le_mul_of_nonneg_left htwo (by positivity)
  have hmain : (ε / 4) * U ≤ (ε / 2) * X := by
    nlinarith
  calc
    ‖LSeriesLogPhaseBridge.residueClassSum (Finset.Icc A M) c
        (fun n ↦ natLogTwist n t)‖ ≤ (ε / 4) * U + 1 := by
      simpa only [U] using hbound
    _ ≤ ε * X := by nlinarith
    _ = ε * (firstResidueAtOrAbove A c / q : ℕ) := by rfl

end

end Erdos67.ResidueFixedDepthEpsilon
