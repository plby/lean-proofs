import ErdosProblems.Erdos239.External.Erdos67.ResidueLogPhase
import ErdosProblems.Erdos239.External.Erdos67.LogSecondDerivativeReal
import ErdosProblems.Erdos239.External.Erdos67.LogControlledWeyl
import ErdosProblems.Erdos239.External.Erdos67.LogBandCoverage

/-!
# Real-start bounds after residue-class decomposition

This file packages the elementary geometry of a residue class in a closed
dyadic interval and applies the real-start second-derivative estimate.
-/

open scoped BigOperators

namespace Erdos67.ResidueLogPhaseBounds

noncomputable section

open Erdos1149
open Erdos67.LSeriesLogPhaseBridge
open Erdos67.LogPhaseSum
open Erdos67.LogPhaseHigherDerivative
open Erdos67.ResidueLogPhase
open Erdos67.LogSecondDerivativeReal
open Erdos67.LogControlledWeyl
open Erdos67.LogWeylParameters
open Erdos67.LogBandCoverage

/-- In a closed dyadic interval `[A,M]`, `M ≤ 2A`, the number of selected
members of one residue class is at most its normalized real starting point
plus one. -/
theorem residueIntervalLength_le_start_div_add_one
    {q A M : ℕ} [NeZero q] (c : ZMod q) (hM : M ≤ 2 * A) :
    ((residueIntervalLength A M c : ℕ) : ℝ) ≤
      (firstResidueAtOrAbove A c : ℝ) / q + 1 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  unfold residueIntervalLength
  split_ifs with hn₀M
  · have hAn₀ : A ≤ firstResidueAtOrAbove A c :=
      le_firstResidueAtOrAbove c
    have hdiff : M - firstResidueAtOrAbove A c ≤
        firstResidueAtOrAbove A c := by omega
    have hdiv : (M - firstResidueAtOrAbove A c) / q ≤
        firstResidueAtOrAbove A c / q :=
      Nat.div_le_div_right hdiff
    calc
      ((((M - firstResidueAtOrAbove A c) / q + 1 : ℕ) : ℝ)) ≤
          ((firstResidueAtOrAbove A c / q + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.add_le_add_right hdiv 1
      _ = ((firstResidueAtOrAbove A c / q : ℕ) : ℝ) + 1 := by
        norm_num only [Nat.cast_add, Nat.cast_one]
      _ ≤ (firstResidueAtOrAbove A c : ℝ) / q + 1 := by
        gcongr
        exact Nat.cast_div_le
  · have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    norm_num
    positivity

/-- Natural-number form of the closed-endpoint correction: after deleting
one possible final term, the residue prefix has length at most `⌊U⌋`. -/
theorem residueIntervalLength_sub_one_le_start_div
    {q A M : ℕ} [NeZero q] (c : ZMod q) (hM : M ≤ 2 * A) :
    residueIntervalLength A M c - 1 ≤
      firstResidueAtOrAbove A c / q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hPU := residueIntervalLength_le_start_div_add_one c hM
  have hUlt : (firstResidueAtOrAbove A c : ℝ) / q <
      ((firstResidueAtOrAbove A c / q : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ (by exact_mod_cast hq : (0 : ℝ) < q)).2
    have hnat : firstResidueAtOrAbove A c <
        q * (firstResidueAtOrAbove A c / q + 1) :=
      Nat.lt_mul_div_succ _ hq
    push_cast
    exact_mod_cast (show firstResidueAtOrAbove A c <
        (firstResidueAtOrAbove A c / q + 1) * q by
      simpa only [mul_comm] using hnat)
  have hPlt : (residueIntervalLength A M c : ℝ) <
      ((firstResidueAtOrAbove A c / q : ℕ) : ℝ) + 2 := by
    linarith
  have hPltNat : residueIntervalLength A M c <
      firstResidueAtOrAbove A c / q + 2 := by exact_mod_cast hPlt
  have hPle : residueIntervalLength A M c ≤
      firstResidueAtOrAbove A c / q + 1 := by
    exact Nat.le_of_lt_succ (by
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hPltNat)
  simpa using Nat.sub_le_sub_right hPle 1

/-- The separated `r=1` estimate, already expressed as the residue-class
sum which is consumed by the Abel-summation bridge. -/
theorem norm_residueClassSum_natLogTwist_le_secondDerivative
    {q A M H : ℕ} [NeZero q] (c : ZMod q) {t : ℝ}
    (hA : 0 < A) (hM : M ≤ 2 * A)
    (hH : 0 < H) (hHP : H + 1 ≤ residueIntervalLength A M c)
    (hUa : (firstResidueAtOrAbove A c : ℝ) / q ≤
      positiveLogCoefficient t)
    (hscale : 8 * (H : ℝ) * positiveLogCoefficient t ≤
      ((firstResidueAtOrAbove A c : ℝ) / q) ^ 2) :
    ‖residueClassSum (Finset.Icc A M) c
        (fun n ↦ natLogTwist n t)‖ ≤
      ((firstResidueAtOrAbove A c : ℝ) / q) *
        Real.sqrt (38 * (1 + Real.log (H : ℝ)) / (H : ℝ)) + 1 := by
  let U : ℝ := (firstResidueAtOrAbove A c : ℝ) / q
  let P : ℕ := residueIntervalLength A M c
  let a : ℝ := positiveLogCoefficient t
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hn₀ : 0 < firstResidueAtOrAbove A c :=
    firstResidueAtOrAbove_pos c hA
  have hU : 0 < U := by
    dsimp only [U]
    positivity
  have ha : 0 < a := by
    have ht : t ≠ 0 := by
      intro ht
      subst t
      simp only [positiveLogCoefficient, abs_zero, zero_div] at hUa
      have hUraw : 0 < (firstResidueAtOrAbove A c : ℝ) / q := by
        simpa only [U] using hU
      linarith
    exact positiveLogCoefficient_pos ht
  have hPU : (P : ℝ) ≤ U + 1 := by
    exact residueIntervalLength_le_start_div_add_one c hM
  have hbound := norm_realLogBlock_le_sqrt_add_one
    (a := a) (U := U) (P := P) (H := H)
    hH (by simpa only [P] using hHP) ha hU hPU
    (by simpa only [U, a] using hUa)
    (by simpa only [U, a] using hscale)
  rw [norm_residueClassSum_natLogTwist_eq c t hA,
    norm_sum_normalizedLogArgument_eq_positive]
  simpa only [realBlockPhase, U, P, a] using hbound

/-- Fixed-depth (`r ≥ 2`) residue-class bound at the natural comparison
scale `X = ⌊U⌋ = n₀ / q`.  A closed dyadic interval can contain one more
selected point than this scale; removing that final point makes the prefix
length at most `X`, and its norm costs exactly one when restored. -/
theorem norm_residueClassSum_natLogTwist_le_fixedDepth
    {q A M r : ℕ} [NeZero q] (c : ZMod q) {t : ℝ}
    (hA : 0 < A) (hM : M ≤ 2 * A) (ht : t ≠ 0)
    (hr : 2 ≤ r)
    (hX : 1 ≤ firstResidueAtOrAbove A c / q)
    (hP : 0 < residueIntervalLength A M c)
    (hboundary :
      ((firstResidueAtOrAbove A c / q : ℕ) : ℝ) ^ r ≤
          positiveLogCoefficient t ∨
        rawStepScale r (firstResidueAtOrAbove A c / q)
            (positiveLogCoefficient t) ≤
          ((firstResidueAtOrAbove A c / q : ℕ) : ℝ) ^ (3 / 4 : ℝ))
    (hupper : positiveLogCoefficient t <
      ((firstResidueAtOrAbove A c / q : ℕ) : ℝ) ^ (r + 1))
    (hlarge : IsLargeLogWeylScale r
      (firstResidueAtOrAbove A c / q))
    (hwindow :
      ((residueIntervalLength A M c - 1 : ℕ) : ℝ) +
          (depth r : ℝ) *
            shiftCount r (firstResidueAtOrAbove A c / q) *
            stepSize r (firstResidueAtOrAbove A c / q)
              (positiveLogCoefficient t) + 1 ≤
        2 * ((firstResidueAtOrAbove A c : ℝ) / q)) :
    ‖residueClassSum (Finset.Icc A M) c
        (fun n ↦ natLogTwist n t)‖ ≤
      AnalyticParameters.envelopeConstant 10
          ((2 : ℝ) ^ (depth r + 1) * terminalConstant r) (depth r) *
        ((firstResidueAtOrAbove A c / q : ℕ) : ℝ) ^
          (1 - savingExponent r) + 1 := by
  let n₀ := firstResidueAtOrAbove A c
  let U : ℝ := (n₀ : ℝ) / q
  let X : ℕ := n₀ / q
  let P : ℕ := residueIntervalLength A M c
  let a : ℝ := positiveLogCoefficient t
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hn₀ : 0 < n₀ := by
    dsimp only [n₀]
    exact firstResidueAtOrAbove_pos c hA
  have hU : 0 < U := by dsimp only [U]; positivity
  have ha : 0 < a := by
    dsimp only [a]
    exact positiveLogCoefficient_pos ht
  have hXU : (X : ℝ) ≤ U := by
    dsimp only [X, U]
    exact Nat.cast_div_le
  have hUlt : U < (X : ℝ) + 1 := by
    have hnat : n₀ < q * (n₀ / q + 1) := by
      simpa only [mul_comm] using Nat.lt_mul_div_succ n₀ hq
    apply (div_lt_iff₀ (by exact_mod_cast hq : (0 : ℝ) < q)).2
    push_cast
    exact_mod_cast (show n₀ < (X + 1) * q by
      simpa only [X, mul_comm] using hnat)
  have hUX : U ≤ 2 * X := by
    have hXR : (1 : ℝ) ≤ X := by
      exact_mod_cast (show 1 ≤ X by simpa only [X, n₀] using hX)
    linarith
  have hPU : (P : ℝ) ≤ U + 1 := by
    dsimp only [P, U, n₀]
    exact residueIntervalLength_le_start_div_add_one c hM
  obtain ⟨P', hPeq⟩ := Nat.exists_eq_succ_of_ne_zero
    (show P ≠ 0 from (by simpa only [P] using hP.ne'))
  have hP'X : P' ≤ X := by
    have hP'U : (P' : ℝ) ≤ U := by
      rw [hPeq] at hPU
      push_cast at hPU
      linarith
    have hP'lt : (P' : ℝ) < (X : ℝ) + 1 := hP'U.trans_lt hUlt
    have hP'ltNat : P' < X + 1 := by exact_mod_cast hP'lt
    omega
  have hmain :=
    norm_sum_shiftedLogPhase_realStart_le_of_lower_or_rawStepScale_le
      (r := r) (X := X) (P := P') (a := a) (U := U)
      hr (by simpa only [X, n₀] using hX) hP'X ha hXU hUX
      (by simpa only [X, n₀, a] using hboundary)
      (by simpa only [X, n₀, a] using hupper)
      (by simpa only [X, n₀] using hlarge)
      (by
        have hPsub : P - 1 = P' := by omega
        simpa only [P, X, U, n₀, a, hPsub] using hwindow)
  rw [norm_residueClassSum_natLogTwist_eq_positiveShifted c t hA]
  change ‖∑ j ∈ Finset.range P,
      HigherDerivative.phase (shiftedLogPhase a U j)‖ ≤ _
  rw [hPeq, Finset.sum_range_succ]
  calc
    ‖(∑ j ∈ Finset.range P',
          HigherDerivative.phase (shiftedLogPhase a U j)) +
        HigherDerivative.phase (shiftedLogPhase a U P')‖ ≤
        ‖∑ j ∈ Finset.range P',
          HigherDerivative.phase (shiftedLogPhase a U j)‖ +
          ‖HigherDerivative.phase (shiftedLogPhase a U P')‖ :=
      norm_add_le _ _
    _ ≤ AnalyticParameters.envelopeConstant 10
          ((2 : ℝ) ^ (depth r + 1) * terminalConstant r) (depth r) *
        (X : ℝ) ^ (1 - savingExponent r) + 1 := by
      rw [HigherDerivative.norm_phase]
      gcongr
    _ = _ := by rfl

/-- A single comparison-scale threshold discharges the largeness and
translation-window hypotheses in every fixed depth `2 ≤ r ≤ R`. -/
theorem exists_residue_fixedDepthRange_threshold (R : ℕ) :
    ∃ X₀ : ℕ, ∀ {q A M : ℕ} [NeZero q] (c : ZMod q) {t : ℝ} (r : ℕ),
      r ∈ Finset.Icc 2 R →
      0 < A → M ≤ 2 * A → t ≠ 0 →
      0 < residueIntervalLength A M c →
      X₀ ≤ firstResidueAtOrAbove A c / q →
      (((firstResidueAtOrAbove A c / q : ℕ) : ℝ) ^ r ≤
          positiveLogCoefficient t ∨
        rawStepScale r (firstResidueAtOrAbove A c / q)
            (positiveLogCoefficient t) ≤
          ((firstResidueAtOrAbove A c / q : ℕ) : ℝ) ^ (3 / 4 : ℝ)) →
      positiveLogCoefficient t <
        ((firstResidueAtOrAbove A c / q : ℕ) : ℝ) ^ (r + 1) →
      ‖residueClassSum (Finset.Icc A M) c
          (fun n ↦ natLogTwist n t)‖ ≤
        AnalyticParameters.envelopeConstant 10
            ((2 : ℝ) ^ (depth r + 1) * terminalConstant r) (depth r) *
          ((firstResidueAtOrAbove A c / q : ℕ) : ℝ) ^
            (1 - savingExponent r) + 1 := by
  have heach : ∀ r ∈ Finset.Icc 2 R,
      ∀ᶠ X : ℕ in Filter.atTop,
        1 ≤ X ∧ IsLargeLogWeylScale r X ∧
          (depth r : ℝ) * (X : ℝ) ^ (3 / 4 : ℝ) + 1 ≤ X := by
    intro r hrmem
    obtain ⟨Xwindow, hwindow⟩ := exists_window_threshold (depth r)
    filter_upwards [Filter.eventually_ge_atTop (max 1 Xwindow),
      eventually_isLargeLogWeylScale r] with X hX hlarge
    exact ⟨(Nat.le_max_left 1 Xwindow).trans hX, hlarge,
      hwindow X ((Nat.le_max_right 1 Xwindow).trans hX)⟩
  have hall : ∀ᶠ X : ℕ in Filter.atTop, ∀ r ∈ Finset.Icc 2 R,
      1 ≤ X ∧ IsLargeLogWeylScale r X ∧
        (depth r : ℝ) * (X : ℝ) ^ (3 / 4 : ℝ) + 1 ≤ X :=
    (Finset.eventually_all (Finset.Icc 2 R)).2 heach
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.1 hall
  refine ⟨X₀, ?_⟩
  intro q A M _ c t r hrmem hA hM ht hP hscale hboundary hupper
  let X : ℕ := firstResidueAtOrAbove A c / q
  have hdata := hX₀ X (by simpa only [X] using hscale) r hrmem
  have hXone : 1 ≤ X := hdata.1
  have hlarge : IsLargeLogWeylScale r X := hdata.2.1
  have hwindowBase :
      (depth r : ℝ) * (X : ℝ) ^ (3 / 4 : ℝ) + 1 ≤ X := hdata.2.2
  have ha : 0 < positiveLogCoefficient t := positiveLogCoefficient_pos ht
  have hp := parameters_of_lower_or_rawStepScale_le
    (Finset.mem_Icc.mp hrmem).1 hXone ha
    (by simpa only [X] using hboundary)
    (by simpa only [X] using hupper) hlarge
  dsimp only at hp
  have hKd : (shiftCount r X : ℝ) *
      stepSize r X (positiveLogCoefficient t) ≤
        (X : ℝ) ^ (3 / 4 : ℝ) := hp.2.2.2.2.2.2.2.1
  have hPsub : residueIntervalLength A M c - 1 ≤ X := by
    simpa only [X] using residueIntervalLength_sub_one_le_start_div c hM
  have hPcast : ((residueIntervalLength A M c - 1 : ℕ) : ℝ) ≤ X := by
    exact_mod_cast hPsub
  have hshift : (depth r : ℝ) *
      ((shiftCount r X : ℝ) * stepSize r X (positiveLogCoefficient t)) ≤
        (depth r : ℝ) * (X : ℝ) ^ (3 / 4 : ℝ) := by
    exact mul_le_mul_of_nonneg_left hKd (by positivity)
  have hXU : (X : ℝ) ≤
      (firstResidueAtOrAbove A c : ℝ) / q := by
    dsimp only [X]
    exact Nat.cast_div_le
  have hfullWindow :
      ((residueIntervalLength A M c - 1 : ℕ) : ℝ) +
          (depth r : ℝ) * shiftCount r X *
            stepSize r X (positiveLogCoefficient t) + 1 ≤
        2 * ((firstResidueAtOrAbove A c : ℝ) / q) := by
    calc
      ((residueIntervalLength A M c - 1 : ℕ) : ℝ) +
          (depth r : ℝ) * shiftCount r X *
            stepSize r X (positiveLogCoefficient t) + 1 ≤
          (X : ℝ) +
            ((depth r : ℝ) * (X : ℝ) ^ (3 / 4 : ℝ) + 1) := by
        nlinarith
      _ ≤ (X : ℝ) + X := by
        linarith
      _ ≤ 2 * ((firstResidueAtOrAbove A c : ℝ) / q) := by
        nlinarith
  exact norm_residueClassSum_natLogTwist_le_fixedDepth
    c hA hM ht (Finset.mem_Icc.mp hrmem).1
    (by simpa only [X] using hXone) hP
    (by simpa only [X] using hboundary)
    (by simpa only [X] using hupper)
    (by simpa only [X] using hlarge)
    (by simpa only [X] using hfullWindow)

/-- Canonical power-saving form of the separated `r=1` residue-class
estimate.  Here the natural comparison scale is `X = ⌊U⌋`; the closed
interval endpoint still costs only the final `+1`. -/
theorem norm_residueClassSum_natLogTwist_le_rOnePower
    {q A M : ℕ} [NeZero q] (c : ZMod q) {t : ℝ}
    (hA : 0 < A) (hM : M ≤ 2 * A)
    (hX : 1 ≤ firstResidueAtOrAbove A c / q)
    (hP : rOneLagBudget (firstResidueAtOrAbove A c / q) + 1 ≤
      residueIntervalLength A M c)
    (hUa : (firstResidueAtOrAbove A c : ℝ) / q ≤
      positiveLogCoefficient t)
    (hscale : 8 *
        (rOneLagBudget (firstResidueAtOrAbove A c / q) : ℝ) *
          positiveLogCoefficient t ≤
        ((firstResidueAtOrAbove A c : ℝ) / q) ^ 2) :
    ‖residueClassSum (Finset.Icc A M) c
        (fun n ↦ natLogTwist n t)‖ ≤
      18 * ((firstResidueAtOrAbove A c / q : ℕ) : ℝ) ^
        (63 / 64 : ℝ) + 1 := by
  let X : ℕ := firstResidueAtOrAbove A c / q
  let U : ℝ := (firstResidueAtOrAbove A c : ℝ) / q
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hXR : (1 : ℝ) ≤ X := by
    exact_mod_cast (show 1 ≤ X by simpa only [X] using hX)
  have hXpos : (0 : ℝ) < X := zero_lt_one.trans_le hXR
  have hUlt : U < (X : ℝ) + 1 := by
    have hnat : firstResidueAtOrAbove A c <
        q * (firstResidueAtOrAbove A c / q + 1) := by
      simpa only [mul_comm] using
        Nat.lt_mul_div_succ (firstResidueAtOrAbove A c) hq
    apply (div_lt_iff₀ (by exact_mod_cast hq : (0 : ℝ) < q)).2
    push_cast
    exact_mod_cast (by simpa only [X, mul_comm] using hnat)
  have hUX : U ≤ 2 * X := by linarith
  have hraw := norm_residueClassSum_natLogTwist_le_secondDerivative
    c hA hM (rOneLagBudget_pos (by omega))
    (by simpa only [X] using hP) hUa hscale
  have hcoeff := rOneLagBudget_sqrt_le_power
    (show 1 ≤ X by simpa only [X] using hX)
  have hpowProduct : (X : ℝ) * (X : ℝ) ^ (-1 / 64 : ℝ) =
      (X : ℝ) ^ (63 / 64 : ℝ) := by
    nth_rewrite 1 [← Real.rpow_one (X : ℝ)]
    rw [← Real.rpow_add hXpos]
    norm_num
  calc
    ‖residueClassSum (Finset.Icc A M) c
        (fun n ↦ natLogTwist n t)‖ ≤
      U * Real.sqrt
        (38 * (1 + Real.log (rOneLagBudget X : ℝ)) /
          (rOneLagBudget X : ℝ)) + 1 := by
        simpa only [X, U] using hraw
    _ ≤ (2 * X) * (9 * (X : ℝ) ^ (-1 / 64 : ℝ)) + 1 := by
      gcongr
    _ = 18 * (X : ℝ) ^ (63 / 64 : ℝ) + 1 := by
      rw [← hpowProduct]
      ring
    _ = 18 * ((firstResidueAtOrAbove A c / q : ℕ) : ℝ) ^
        (63 / 64 : ℝ) + 1 := by rfl

end

end Erdos67.ResidueLogPhaseBounds
