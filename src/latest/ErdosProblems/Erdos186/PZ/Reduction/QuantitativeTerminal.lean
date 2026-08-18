/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.FirstCrossingControl
import ErdosProblems.Erdos186.PZ.Reduction.FirstCrossingAbsorption
import ErdosProblems.Erdos186.PZ.Reduction.InitialNoDimensionIncrease
import ErdosProblems.Erdos186.PZ.Reduction.GuardShrinkAbsorption

/-!
# Quantitative population-guarded terminal state
-/

namespace Erdos186.PZ.Reduction

open Erdos186.Irreducible

noncomputable section

variable {beta eta : ℝ} {C : HigherDimensionalContext beta eta}
  {selector : BoundedCFPSelector C} {delta gamma : ℝ}

/-- The first-crossing contradiction gives a uniform bound for total upward
rank jump in every population-guarded trace. -/
theorem exists_guarded_upwardJump_threshold
    (D0 J : ℕ) (beta0 tau sigma initialCost : ℝ)
    (hsigma : 0 ≤ sigma) (ha : 0 < tau * sigma)
    (hgap : beta0 < (tau * sigma) * (J + 1 : ℕ))
    (hstrong : selector.UsesScaleExponent sigma)
    (hinitialCost : 0 < initialCost) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ {delta gamma : ℝ},
      0 ≤ delta → 0 ≤ gamma → gamma ≤ 1 →
      ∀ (m : ℕ) (initial : CoordinateReplacementState selector),
        threshold ≤ m → initial.selected.dimension ≤ D0 →
        (initial.selected.progression.volume : ℝ) ≤
          initialCost * Real.rpow (m : ℝ) beta0 →
        ∀ {length : ℕ},
          (Tg : RelationTrace
            (GuardedCoordinateReplacement selector delta gamma
              (Real.rpow (m : ℝ) tau)) initial length) →
          coordinateUpwardJump Tg.forgetPopulationGuard length ≤ J := by
  let Q := D0 + J
  let R := max Q (rankBoundSum C Q)
  let Ucap := J + rankBoundSum C Q
  let changeCap := D0 + 2 * Ucap
  let cost := uniformStepCost R (scaleDenSum C Q)
  have hcost : 0 < cost :=
    lt_of_lt_of_le zero_lt_one (one_le_uniformStepCost (scaleDenSum_pos C Q))
  obtain ⟨threshold, hthreshold, habsorb⟩ :=
    exists_firstCrossingAbsorption_threshold cost initialCost beta0
      (tau * sigma) changeCap J hcost hinitialCost hgap
  refine ⟨threshold, hthreshold, ?_⟩
  intro delta gamma hdelta0 hgamma0 hgamma1 m initial hm hinitialRank
    hinitialVolume length Tg
  have hmpos : 0 < m := by omega
  by_contra hnot
  have hcross : J < coordinateUpwardJump Tg.forgetPopulationGuard length :=
    Nat.lt_of_not_ge hnot
  obtain ⟨i, hilength, hpre, hcrossi⟩ :=
    Tg.forgetPopulationGuard.exists_first_coordinateUpwardJump_gt hcross
  let Tg' : RelationTrace
      (GuardedCoordinateReplacement selector delta gamma
        (Real.rpow (m : ℝ) tau)) initial (i + 1) := {
    state := Tg.state
    state_zero := Tg.state_zero
    valid := fun j hj ↦ Tg.valid j (hj.trans_le (by omega)) }
  let T := Tg'.forgetPopulationGuard
  have hjumpT : ∀ n, coordinateUpwardJump T n =
      coordinateUpwardJump Tg.forgetPopulationGuard n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [RelationTrace.coordinateUpwardJump_succ, ih]
        rfl
  have hpreT : coordinateUpwardJump T i ≤ J := by
    rw [hjumpT]
    exact hpre
  have hcrossiT : J < coordinateUpwardJump T (i + 1) := by
    rw [hjumpT]
    exact hcrossi
  let p := quantitativeMoveParameters C delta gamma m (tau * sigma) R Q
    hdelta0 hgamma0 hgamma1 hmpos ha.le
  let H : CoordinateTraceControl p T :=
    guardedTraceControl_first_crossing_uniform Tg'
    hdelta0 hgamma0 hgamma1 hmpos hsigma ha.le hstrong hinitialRank hpreT
  have hUeq : upwardJump H.toMoveTrace (i + 1) =
      coordinateUpwardJump T (i + 1) :=
    (T.coordinateUpwardJump_eq_upwardJump H (i + 1)).symm
  have hzeroRank : (T.state 0).selected.dimension =
      initial.selected.dimension := by
    exact congrArg (fun S : CoordinateReplacementState selector ↦
      S.selected.dimension) T.state_zero
  have hcurrent : (T.state i).selected.dimension ≤ Q := by
    calc
      (T.state i).selected.dimension ≤
          (T.state 0).selected.dimension + J :=
        T.selected_dimension_le_of_upwardJump_le (le_refl i) hpreT
      _ = initial.selected.dimension + J := by rw [hzeroRank]
      _ ≤ D0 + J := Nat.add_le_add_right hinitialRank J
  have hnextAmbient : (T.state (i + 1)).ambientDimension ≤ Q := by
    rw [T.ambientDimension_succ (show i < i + 1 by omega)]
    exact hcurrent
  have hnextRank : (T.state (i + 1)).selected.dimension ≤
      rankBoundSum C Q :=
    (T.state (i + 1)).selected_dimension_le.trans
      (rankBound_le_rankBoundSum C hnextAmbient)
  have hUcap : coordinateUpwardJump T (i + 1) ≤ Ucap := by
    simp only [coordinateUpwardJump]
    dsimp [Ucap]
    omega
  have hchange : kindCount H.toMoveTrace .up (i + 1) +
      kindCount H.toMoveTrace .down (i + 1) ≤ changeCap := by
    have hraw := changingMoveCount_le_of_upwardJump_le H.toMoveTrace
      (le_refl (i + 1)) (by simpa [hUeq] using hUcap)
    dsimp [changeCap]
    rw [CoordinateTraceControl.toMoveTrace_dimension, hzeroRank] at hraw
    exact hraw.trans (by dsimp [Ucap]; omega)
  have hone := one_le_uniform_product H.toMoveTrace
    (show i + 1 ≤ i + 1 by rfl)
  have hcostPow : p.cost ^
      (kindCount H.toMoveTrace .up (i + 1) +
        kindCount H.toMoveTrace .down (i + 1)) ≤ cost ^ changeCap := by
    change cost ^ _ ≤ cost ^ changeCap
    exact pow_le_pow_right₀ (one_le_uniformStepCost (scaleDenSum_pos C Q)) hchange
  have hgammaPow : p.shrinkFactor ^
      kindCount H.toMoveTrace .shrink (i + 1) ≤ 1 := by
    change gamma ^ _ ≤ 1
    exact pow_le_one₀ hgamma0 hgamma1
  have hupPow : p.upBase ^
      upwardJump H.toMoveTrace (i + 1) ≤
        (Real.rpow (m : ℝ) (-(tau * sigma))) ^ (J + 1) := by
    dsimp [p, quantitativeMoveParameters]
    change (Real.rpow (m : ℝ) (-(tau * sigma))) ^
        upwardJump H.toMoveTrace (i + 1) ≤ _
    rw [hUeq]
    apply pow_le_pow_of_le_one
    · exact Real.rpow_nonneg (by positivity) _
    · exact Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast hmpos) (by linarith)
    · omega
  have hzeroVolume : (T.state 0).selected.progression.volume =
      initial.selected.progression.volume := by
    exact congrArg (fun S : CoordinateReplacementState selector ↦
      S.selected.progression.volume) T.state_zero
  have hcostGamma :
      p.cost ^ (kindCount H.toMoveTrace .up (i + 1) +
          kindCount H.toMoveTrace .down (i + 1)) *
        p.shrinkFactor ^ kindCount H.toMoveTrace .shrink (i + 1) ≤
          cost ^ changeCap := by
    calc
      _ ≤ p.cost ^ (kindCount H.toMoveTrace .up (i + 1) +
            kindCount H.toMoveTrace .down (i + 1)) * 1 := by gcongr
      _ ≤ cost ^ changeCap := by simpa using hcostPow
  have hupper :
      p.cost ^
          (kindCount H.toMoveTrace .up (i + 1) +
            kindCount H.toMoveTrace .down (i + 1)) *
        p.shrinkFactor ^
          kindCount H.toMoveTrace .shrink (i + 1) *
        p.upBase ^ upwardJump H.toMoveTrace (i + 1) *
          (H.toMoveTrace.state 0).gapSize ≤
      cost ^ changeCap *
        (Real.rpow (m : ℝ) (-(tau * sigma))) ^ (J + 1) *
          (initialCost * Real.rpow (m : ℝ) beta0) := by
    change _ * _ * _ * ((T.state 0).selected.progression.volume : ℝ) ≤ _
    rw [hzeroVolume]
    calc
      _ ≤ cost ^ changeCap * p.upBase ^
          upwardJump H.toMoveTrace (i + 1) *
            (initial.selected.progression.volume : ℝ) := by
              gcongr
              exact pow_nonneg p.upBase_nonneg _
      _ ≤ cost ^ changeCap *
          (Real.rpow (m : ℝ) (-(tau * sigma))) ^ (J + 1) *
            (initial.selected.progression.volume : ℝ) := by gcongr
      _ ≤ cost ^ changeCap *
          (Real.rpow (m : ℝ) (-(tau * sigma))) ^ (J + 1) *
            (initialCost * Real.rpow (m : ℝ) beta0) := by
              gcongr
              exact mul_nonneg (pow_nonneg hcost.le _)
                (pow_nonneg (Real.rpow_nonneg (by positivity) _) _)
  have habs := habsorb m hm
  linarith [hone.trans hupper]

/-- When `gamma < 1`, the bounded-upward-jump estimate gives a finite
guarded terminal trace.  The bound may depend on the concrete input size;
only the upward-jump and rank bounds are uniform. -/
theorem exists_quantitative_guarded_terminal_of_gamma_lt_one
    {m : ℕ} {tau sigma : ℝ} {D0 J : ℕ}
    (initial : CoordinateReplacementState selector)
    (hdelta0 : 0 ≤ delta) (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma < 1) (hm : 0 < m)
    (hsigma : 0 ≤ sigma) (ha : 0 ≤ tau * sigma)
    (hstrong : selector.UsesScaleExponent sigma)
    (hinitialRank : initial.selected.dimension ≤ D0)
    (hinitialPopulation : Real.rpow (m : ℝ) tau <
      (initial.points.card : ℝ))
    (hjumpAll : ∀ {length : ℕ},
      (Tg : RelationTrace
        (GuardedCoordinateReplacement selector delta gamma
          (Real.rpow (m : ℝ) tau)) initial length) →
      coordinateUpwardJump Tg.forgetPopulationGuard length ≤ J) :
    ∃ length : ℕ, ∃ Tg : RelationTrace
        (GuardedCoordinateReplacement selector delta gamma
          (Real.rpow (m : ℝ) tau)) initial length,
      (∀ U, ¬ GuardedCoordinateReplacement selector delta gamma
        (Real.rpow (m : ℝ) tau) (Tg.state length) U) ∧
      coordinateUpwardJump Tg.forgetPopulationGuard length ≤ J ∧
      (Tg.state length).selected.dimension ≤ D0 + J ∧
      Real.rpow (m : ℝ) tau < ((Tg.state length).points.card : ℝ) := by
  let R := initial.selected.dimension + J
  let p := quantitativeMoveParameters C delta gamma m (tau * sigma) R R
    hdelta0 hgamma0 hgamma1.le hm ha
  have hpCost : 0 < p.cost :=
    lt_of_lt_of_le zero_lt_one p.one_le_cost
  have hvol0 : 0 < (initial.selected.progression.volume : ℝ) := by
    have h := initial.toIterationState.one_le_gapSize
    change 1 ≤ (initial.selected.progression.volume : ℝ) at h
    linarith
  let fixed : ℝ := p.cost ^ (initial.selected.dimension + 2 * J) *
    (initial.selected.progression.volume : ℝ)
  have hfixed : 0 < fixed := mul_pos (pow_pos hpCost _) hvol0
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := fixed⁻¹) (y := gamma)
    (inv_pos.mpr hfixed) hgamma1
  have hgammaSucc : gamma ^ (n + 1) ≤ gamma ^ n := by
    exact pow_le_pow_of_le_one hgamma0 hgamma1.le (by omega)
  have hbudget : p.cost ^ (initial.selected.dimension + 2 * J) *
      p.shrinkFactor ^ (n + 1) *
        (initial.selected.progression.volume : ℝ) < 1 := by
    change p.cost ^ (initial.selected.dimension + 2 * J) *
      gamma ^ (n + 1) * (initial.selected.progression.volume : ℝ) < 1
    have hmul : fixed * gamma ^ n < 1 := by
      calc
        fixed * gamma ^ n < fixed * fixed⁻¹ :=
          mul_lt_mul_of_pos_left hn hfixed
        _ = 1 := mul_inv_cancel₀ hfixed.ne'
    calc
      p.cost ^ (initial.selected.dimension + 2 * J) *
          gamma ^ (n + 1) * (initial.selected.progression.volume : ℝ) =
        fixed * gamma ^ (n + 1) := by simp [fixed]; ring
      _ ≤ fixed * gamma ^ n := mul_le_mul_of_nonneg_left hgammaSucc hfixed.le
      _ < 1 := hmul
  have traceBound : ∀ {length : ℕ},
      RelationTrace
        (GuardedCoordinateReplacement selector delta gamma
          (Real.rpow (m : ℝ) tau)) initial length →
        length ≤ initial.selected.dimension + 2 * J + n := by
    intro length Tg
    let T := Tg.forgetPopulationGuard
    have hj := hjumpAll Tg
    let H := guardedTraceControl_of_jump_le Tg hdelta0 hgamma0 hgamma1.le
      hm hsigma ha hstrong hj
    have hjMove : upwardJump H.toMoveTrace length ≤ J := by
      rw [← T.coordinateUpwardJump_eq_upwardJump H]
      exact hj
    have hzeroRank : (T.state 0).selected.dimension =
        initial.selected.dimension := congrArg
      (fun S : CoordinateReplacementState selector ↦ S.selected.dimension)
      T.state_zero
    have hzeroVolume : (T.state 0).selected.progression.volume =
        initial.selected.progression.volume := congrArg
      (fun S : CoordinateReplacementState selector ↦
        S.selected.progression.volume) T.state_zero
    have hb : p.cost ^ ((H.toMoveTrace.state 0).dimension + 2 * J) *
        p.shrinkFactor ^ (n + 1) * (H.toMoveTrace.state 0).gapSize < 1 := by
      change p.cost ^ ((T.state 0).selected.dimension + 2 * J) *
        p.shrinkFactor ^ (n + 1) *
          ((T.state 0).selected.progression.volume : ℝ) < 1
      simpa [hzeroRank, hzeroVolume] using hbudget
    have hl := length_le_of_upwardJump_and_budget H.toMoveTrace hjMove hb
    change length ≤ (T.state 0).selected.dimension + 2 * J + n at hl
    rw [hzeroRank] at hl
    exact hl
  obtain ⟨S, hreach, hterminal⟩ := exists_guardedTerminal_of_trace_bound
    selector delta gamma (Real.rpow (m : ℝ) tau) initial
      (initial.selected.dimension + 2 * J + n) traceBound
  obtain ⟨length, Tg, hend⟩ := RelationTrace.exists_of_reflTransGen hreach
  have hj := hjumpAll Tg
  have hzeroRank : (Tg.forgetPopulationGuard.state 0).selected.dimension =
      initial.selected.dimension := congrArg
    (fun V : CoordinateReplacementState selector ↦ V.selected.dimension)
    Tg.forgetPopulationGuard.state_zero
  have hrank := Tg.forgetPopulationGuard.selected_dimension_le_initial_add_upwardJump
    length
  have hfinalRank : (Tg.state length).selected.dimension ≤ D0 + J := by
    rw [hzeroRank] at hrank
    exact hrank.trans (Nat.add_le_add hinitialRank hj)
  have hpopulation : Real.rpow (m : ℝ) tau <
      ((Tg.state length).points.card : ℝ) := by
    by_cases hzero : length = 0
    · subst length
      have hpoints : (Tg.state 0).points.card = initial.points.card :=
        congrArg (fun V : CoordinateReplacementState selector ↦ V.points.card)
          Tg.state_zero
      simpa [hpoints] using hinitialPopulation
    · exact Tg.state_card_gt_cutoff (Nat.pos_of_ne_zero hzero) le_rfl
  refine ⟨length, Tg, ?_, hj, hfinalRank, hpopulation⟩
  intro U hstep
  apply hterminal U
  simpa [hend] using hstep

/-- The guarded terminal cannot stop because the next dense failure crosses
the population cutoff.  This is the quantitative stopping argument in
Lemma 10. -/
theorem irreducible_of_quantitative_guarded_terminal
    {m L K D0 J : ℕ} {beta0 tau sigma initialCost : ℝ}
    (initial : CoordinateReplacementState selector)
    (Tg : RelationTrace
      (GuardedCoordinateReplacement selector delta gamma
        (Real.rpow (m : ℝ) tau)) initial L)
    (hterminal : ∀ U, ¬ GuardedCoordinateReplacement selector delta gamma
      (Real.rpow (m : ℝ) tau) (Tg.state L) U)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hgamma0 : 0 < gamma) (hgammaDelta : gamma ≤ delta ^ K)
    (hgammaLower : Real.rpow (m : ℝ) (-(1 / 3 : ℝ)) ≤ gamma)
    (hm : 2 ≤ m) (hsigma : 0 ≤ sigma) (ha : 0 ≤ tau * sigma)
    (hstrong : selector.UsesScaleExponent sigma)
    (hinitialCard : initial.points.card = m)
    (hinitialRank : initial.selected.dimension ≤ D0)
    (hinitialVolume : (initial.selected.progression.volume : ℝ) ≤
      initialCost * Real.rpow (m : ℝ) beta0)
    (hjump : coordinateUpwardJump Tg.forgetPopulationGuard L ≤ J)
    (habsorb :
      let p := quantitativeMoveParameters C delta gamma m (tau * sigma)
        (D0 + J) (D0 + J) hdelta0.le hgamma0.le
          (by
            have h := hgammaDelta.trans (pow_le_one₀ hdelta0.le hdelta1)
            simpa using h) (by omega) ha
      p.cost ^ (D0 + 2 * J) * initialCost *
        Real.rpow (m : ℝ)
          (beta0 - (K : ℝ) * (1 - tau) +
            (((D0 + 2 * J) + 1 : ℕ) : ℝ) / 3) < 1) :
    (Tg.state L).Irreducible delta gamma := by
  have hgamma1 : gamma ≤ 1 :=
    by
      have h := hgammaDelta.trans (pow_le_one₀ hdelta0.le hdelta1)
      simpa using h
  let T := Tg.forgetPopulationGuard
  let p := quantitativeMoveParameters C delta gamma m (tau * sigma)
    (D0 + J) (D0 + J) hdelta0.le hgamma0.le hgamma1 (by omega) ha
  let H : CoordinateTraceControl p T :=
    guardedTraceControl_of_jump_le_uniform Tg hdelta0.le hgamma0.le hgamma1
      (by omega) hsigma ha hstrong hinitialRank hjump
  by_contra hirr
  obtain ⟨U, hstep⟩ :=
    (not_stateIrreducible_iff_exists_replacement selector delta gamma
      (Tg.state L)).mp hirr
  have hbelow : (U.points.card : ℝ) ≤ Real.rpow (m : ℝ) tau := by
    by_contra habove
    apply hterminal U
    exact ⟨hstep, lt_of_not_ge habove⟩
  have hretention := T.coordinate_retention_pow_mul_card_le hdelta0.le
    (show L ≤ L by rfl)
  have hzeroCard : (T.state 0).points.card = m := by
    rw [T.state_zero]
    exact hinitialCard
  have hendPoints : T.state L = Tg.state L := rfl
  have hguard : delta ^ (L + 1) * (m : ℝ) ≤
      Real.rpow (m : ℝ) tau := by
    calc
      delta ^ (L + 1) * (m : ℝ) =
          delta * (delta ^ L * (m : ℝ)) := by rw [pow_succ]; ring
      _ ≤ delta * ((T.state L).points.card : ℝ) := by
        gcongr
        simpa [hzeroCard] using hretention
      _ ≤ (U.points.card : ℝ) := by
        rw [hendPoints]
        exact hstep.dense
      _ ≤ Real.rpow (m : ℝ) tau := hbelow
  let changes := kindCount H.toMoveTrace .up L +
    kindCount H.toMoveTrace .down L
  let shrinks := kindCount H.toMoveTrace .shrink L
  have hlength : L = changes + shrinks := by
    simpa [changes, shrinks] using length_eq_sum_kindCount H.toMoveTrace L
  have hUmove : upwardJump H.toMoveTrace L ≤ J := by
    rw [← T.coordinateUpwardJump_eq_upwardJump H]
    exact hjump
  have hchanges : changes ≤ D0 + 2 * J := by
    have hraw := changingMoveCount_le_of_upwardJump_le H.toMoveTrace
      (le_refl L) hUmove
    have hzeroRank : (T.state 0).selected.dimension =
        initial.selected.dimension := congrArg
      (fun V : CoordinateReplacementState selector ↦ V.selected.dimension)
      T.state_zero
    calc
      changes ≤ (T.state 0).selected.dimension + 2 * J := hraw
      _ = initial.selected.dimension + 2 * J := by rw [hzeroRank]
      _ ≤ D0 + 2 * J := Nat.add_le_add_right hinitialRank (2 * J)
  have hshrink := guarded_shrink_power_bound m L changes shrinks K
    (D0 + 2 * J) delta gamma tau beta0 hdelta0 hdelta1 hgamma0
      hgammaDelta hgammaLower hguard hlength hchanges hm
  have hvolume := gapSize_le_uniform_product H.toMoveTrace (le_refl L)
  change ((T.state L).selected.progression.volume : ℝ) ≤ _ at hvolume
  rw [CoordinateTraceControl.toMoveTrace_gapSize] at hvolume
  have hzeroVolume : (T.state 0).selected.progression.volume =
      initial.selected.progression.volume := congrArg
    (fun V : CoordinateReplacementState selector ↦
      V.selected.progression.volume) T.state_zero
  have hupOne : p.upBase ^ upwardJump H.toMoveTrace L ≤ 1 :=
    pow_le_one₀ p.upBase_nonneg p.upBase_le_one
  have hcostPower : p.cost ^ changes ≤ p.cost ^ (D0 + 2 * J) :=
    pow_le_pow_right₀ p.one_le_cost hchanges
  have hinitialCost0 : 0 ≤ initialCost := by
    by_contra hn
    have hc : initialCost < 0 := lt_of_not_ge hn
    have hrp : 0 < Real.rpow (m : ℝ) beta0 :=
      Real.rpow_pos_of_pos (by positivity) _
    have hneg : initialCost * Real.rpow (m : ℝ) beta0 < 0 :=
      mul_neg_of_neg_of_pos hc hrp
    have hone := initial.toIterationState.one_le_gapSize
    change 1 ≤ (initial.selected.progression.volume : ℝ) at hone
    linarith
  have hvolumeUpper : ((T.state L).selected.progression.volume : ℝ) ≤
      (p.cost ^ (D0 + 2 * J) * initialCost) *
        (gamma ^ shrinks * Real.rpow (m : ℝ) beta0) := by
    calc
      _ ≤ p.cost ^ changes * gamma ^ shrinks *
          p.upBase ^ upwardJump H.toMoveTrace L *
            ((T.state 0).selected.progression.volume : ℝ) := by
        simpa [changes, shrinks, p, quantitativeMoveParameters] using hvolume
      _ ≤ p.cost ^ (D0 + 2 * J) * gamma ^ shrinks *
          p.upBase ^ upwardJump H.toMoveTrace L *
            ((T.state 0).selected.progression.volume : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg p.upBase_nonneg _)
        exact mul_le_mul_of_nonneg_right hcostPower (pow_nonneg hgamma0.le _)
      _ ≤ p.cost ^ (D0 + 2 * J) * gamma ^ shrinks * 1 *
          ((T.state 0).selected.progression.volume : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        apply mul_le_mul_of_nonneg_left hupOne
        exact mul_nonneg (pow_nonneg p.cost_nonneg _)
          (pow_nonneg hgamma0.le _)
      _ ≤ p.cost ^ (D0 + 2 * J) * gamma ^ shrinks * 1 *
          (initialCost * Real.rpow (m : ℝ) beta0) := by
        rw [hzeroVolume]
        apply mul_le_mul_of_nonneg_left hinitialVolume
        exact mul_nonneg
          (mul_nonneg (pow_nonneg p.cost_nonneg _) (pow_nonneg hgamma0.le _))
          zero_le_one
      _ = (p.cost ^ (D0 + 2 * J) * initialCost) *
          (gamma ^ shrinks * Real.rpow (m : ℝ) beta0) := by ring
  have hfinal : ((T.state L).selected.progression.volume : ℝ) < 1 := by
    calc
      _ ≤ (p.cost ^ (D0 + 2 * J) * initialCost) *
          (gamma ^ shrinks * Real.rpow (m : ℝ) beta0) := hvolumeUpper
      _ ≤ (p.cost ^ (D0 + 2 * J) * initialCost) *
          Real.rpow (m : ℝ)
            (beta0 - (K : ℝ) * (1 - tau) +
              (((D0 + 2 * J) + 1 : ℕ) : ℝ) / 3) := by
        gcongr
        exact mul_nonneg (pow_nonneg p.cost_nonneg _) hinitialCost0
      _ < 1 := habsorb
  have hone : (1 : ℝ) ≤ ((T.state L).selected.progression.volume : ℝ) :=
    (T.state L).toIterationState.one_le_gapSize
  linarith

end

end Erdos186.PZ.Reduction
