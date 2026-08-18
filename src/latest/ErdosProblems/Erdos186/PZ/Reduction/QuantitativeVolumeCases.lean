/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.EqualRankAbsorption
import ErdosProblems.Erdos186.PZ.Reduction.TraceAdapter
import ErdosProblems.Erdos186.PZ.Reduction.QuantitativeRanks

/-!
# Collected terminal GAP bounds in the three rank cases

This file performs the final numerical bookkeeping after the replacement
trace has been constructed.  The initial state is allowed both a coarse
box bound and the sharper Lemma-6 bound above the input rank.
-/

namespace Erdos186.PZ.Reduction

open Erdos186.Irreducible

noncomputable section

variable {beta eta : ℝ} {C : HigherDimensionalContext beta eta}
  {selector : BoundedCFPSelector C} {delta gamma : ℝ}

/-- Natural powers of the rank-saving base are the corresponding real
power with multiplied exponent. -/
theorem rpow_neg_pow_nat {m q : ℕ} {a : ℝ} (hm : 0 < m) :
    (Real.rpow (m : ℝ) (-a)) ^ q =
      Real.rpow (m : ℝ) (-a * (q : ℝ)) := by
  have hmreal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnat := Real.rpow_natCast (Real.rpow (m : ℝ) (-a)) q
  have hmul : Real.rpow (m : ℝ) (-a * (q : ℝ)) =
      Real.rpow (Real.rpow (m : ℝ) (-a)) (q : ℝ) :=
    Real.rpow_mul hmreal.le (-a) (q : ℝ)
  exact hnat.symm.trans hmul.symm

/-- A controlled trace with bounded upward jump satisfies all three terminal
rank estimates.  The returned constant is the fixed changing-move loss
times the fixed initial-box loss. -/
theorem quantitative_terminal_volume_cases
    {initial : CoordinateReplacementState selector} {L ell D0 J K m : ℕ}
    {a initialCost boxSize : ℝ}
    (T : RelationTrace (CoordinateReplacement selector delta gamma) initial L)
    (p : MoveParameters) (H : CoordinateTraceControl p T)
    (hcost : 1 ≤ p.cost)
    (hshrink : p.shrinkFactor = gamma)
    (hup : p.upBase = Real.rpow (m : ℝ) (-a))
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (hgamma0 : 0 < gamma) (hgammaDelta : gamma ≤ delta ^ K)
    (hgammaLower : Real.rpow (m : ℝ) (-(1 / 3 : ℝ)) ≤ gamma)
    (hm : 2 ≤ m) (ha : (2 / 3 : ℝ) ≤ a)
    (hinitialCost0 : 0 ≤ initialCost) (hbox0 : 0 ≤ boxSize)
    (hinitialCard : initial.points.card = m)
    (hinitialRank : initial.selected.dimension ≤ D0)
    (hinitialCoarse : (initial.selected.progression.volume : ℝ) ≤
      initialCost * boxSize)
    (hinitialHigh : ell < initial.selected.dimension →
      (initial.selected.progression.volume : ℝ) ≤
        initialCost *
          (Real.rpow (m : ℝ) (-a)) ^
            (initial.selected.dimension - ell) * boxSize)
    (hjump : coordinateUpwardJump T L ≤ J) :
    let constant := p.cost ^ (D0 + 2 * J) * initialCost
    (((T.state L).selected.progression.volume : ℝ) ≤ constant * boxSize) ∧
    (ell < (T.state L).selected.dimension →
      ((T.state L).selected.progression.volume : ℝ) ≤
        constant * Real.rpow (m : ℝ)
          (-a * (((T.state L).selected.dimension - ell : ℕ) : ℝ)) * boxSize) ∧
    ((T.state L).selected.dimension = ell →
      ((T.state L).selected.progression.volume : ℝ) ≤
        constant *
          (((T.state L).points.card : ℝ) / (m : ℝ)) ^ K * boxSize) ∧
    ((T.state L).selected.dimension < ell →
      ((T.state L).selected.progression.volume : ℝ) ≤
        constant * boxSize) := by
  have hmpos : 0 < m := by omega
  have hgamma1 : gamma ≤ 1 := by
    have h := hgammaDelta.trans (pow_le_one₀ hdelta0.le hdelta1)
    simpa using h
  have hzeroRank : (T.state 0).selected.dimension =
      initial.selected.dimension := congrArg
    (fun V : CoordinateReplacementState selector ↦ V.selected.dimension)
    T.state_zero
  have hzeroCard : (T.state 0).points.card = m := by
    rw [T.state_zero]
    exact hinitialCard
  have hzeroVolume : (T.state 0).selected.progression.volume =
      initial.selected.progression.volume := congrArg
    (fun V : CoordinateReplacementState selector ↦
      V.selected.progression.volume) T.state_zero
  let changes := kindCount H.toMoveTrace .up L +
    kindCount H.toMoveTrace .down L
  let shrinks := kindCount H.toMoveTrace .shrink L
  let up := upwardJump H.toMoveTrace L
  let down := downwardJump H.toMoveTrace L
  have hupJump : up = coordinateUpwardJump T L := by
    dsimp [up]
    exact (T.coordinateUpwardJump_eq_upwardJump H L).symm
  have hupBound : up ≤ J := hupJump.le.trans hjump
  have hchanges : changes ≤ D0 + 2 * J := by
    have hraw := changingMoveCount_le_of_upwardJump_le H.toMoveTrace
      (le_refl L) hupBound
    calc
      changes ≤ (H.toMoveTrace.state 0).dimension + 2 * J := hraw
      _ = initial.selected.dimension + 2 * J := by
        rw [CoordinateTraceControl.toMoveTrace_dimension, hzeroRank]
      _ ≤ D0 + 2 * J := Nat.add_le_add_right hinitialRank _
  have hcostPower : p.cost ^ changes ≤ p.cost ^ (D0 + 2 * J) :=
    pow_le_pow_right₀ hcost hchanges
  have hgammaPower : gamma ^ shrinks ≤ 1 :=
    pow_le_one₀ hgamma0.le hgamma1
  have hupBaseNonneg : 0 ≤ Real.rpow (m : ℝ) (-a) :=
    Real.rpow_nonneg (by positivity) _
  have hupBaseOne : Real.rpow (m : ℝ) (-a) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast (show 1 ≤ m by omega)
    · linarith
  have hupPower : (Real.rpow (m : ℝ) (-a)) ^ up ≤ 1 :=
    pow_le_one₀ hupBaseNonneg hupBaseOne
  have hvolume := gapSize_le_uniform_product H.toMoveTrace (le_refl L)
  change ((T.state L).selected.progression.volume : ℝ) ≤ _ at hvolume
  rw [CoordinateTraceControl.toMoveTrace_gapSize, hshrink, hup] at hvolume
  have hvolumeInitial : ((T.state L).selected.progression.volume : ℝ) ≤
      p.cost ^ changes * gamma ^ shrinks *
        (Real.rpow (m : ℝ) (-a)) ^ up *
          (initial.selected.progression.volume : ℝ) := by
    simpa [hzeroVolume] using hvolume
  have hvolumeCost : ((T.state L).selected.progression.volume : ℝ) ≤
      p.cost ^ (D0 + 2 * J) * gamma ^ shrinks *
        (Real.rpow (m : ℝ) (-a)) ^ up *
          (initial.selected.progression.volume : ℝ) := by
    calc
      _ ≤ p.cost ^ changes * gamma ^ shrinks *
          (Real.rpow (m : ℝ) (-a)) ^ up *
            (initial.selected.progression.volume : ℝ) := hvolumeInitial
      _ ≤ p.cost ^ (D0 + 2 * J) * gamma ^ shrinks *
          (Real.rpow (m : ℝ) (-a)) ^ up *
            (initial.selected.progression.volume : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hupBaseNonneg _)
        exact mul_le_mul_of_nonneg_right hcostPower (pow_nonneg hgamma0.le _)
  have hvolumeNoShrink : ((T.state L).selected.progression.volume : ℝ) ≤
      p.cost ^ (D0 + 2 * J) * 1 *
        (Real.rpow (m : ℝ) (-a)) ^ up *
          (initial.selected.progression.volume : ℝ) := by
    calc
      _ ≤ p.cost ^ (D0 + 2 * J) * gamma ^ shrinks *
          (Real.rpow (m : ℝ) (-a)) ^ up *
            (initial.selected.progression.volume : ℝ) := hvolumeCost
      _ ≤ p.cost ^ (D0 + 2 * J) * 1 *
          (Real.rpow (m : ℝ) (-a)) ^ up *
            (initial.selected.progression.volume : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hupBaseNonneg _)
        exact mul_le_mul_of_nonneg_left hgammaPower
          (pow_nonneg p.cost_nonneg _)
  have hinitialUnified :
      (initial.selected.progression.volume : ℝ) ≤
        initialCost * (Real.rpow (m : ℝ) (-a)) ^
          (initial.selected.dimension - ell) * boxSize := by
    by_cases hr : ell < initial.selected.dimension
    · exact hinitialHigh hr
    · have hz : initial.selected.dimension - ell = 0 := by omega
      simpa [hz] using hinitialCoarse
  have hvolumeCoarse : ((T.state L).selected.progression.volume : ℝ) ≤
      (p.cost ^ (D0 + 2 * J) * initialCost) * boxSize := by
    calc
      _ ≤ p.cost ^ (D0 + 2 * J) * 1 *
          (Real.rpow (m : ℝ) (-a)) ^ up *
            (initial.selected.progression.volume : ℝ) := hvolumeNoShrink
      _ ≤ p.cost ^ (D0 + 2 * J) * 1 * 1 *
          (initial.selected.progression.volume : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        exact mul_le_mul_of_nonneg_left hupPower
          (mul_nonneg (pow_nonneg p.cost_nonneg _) zero_le_one)
      _ ≤ p.cost ^ (D0 + 2 * J) * 1 * 1 *
          (initialCost * boxSize) := by
        exact mul_le_mul_of_nonneg_left hinitialCoarse
          (mul_nonneg (mul_nonneg (pow_nonneg p.cost_nonneg _) zero_le_one)
            zero_le_one)
      _ = (p.cost ^ (D0 + 2 * J) * initialCost) * boxSize := by ring
  dsimp only
  refine ⟨hvolumeCoarse, ?_, ?_, ?_⟩
  · intro hfinalHigh
    have hbalance := dimension_balance H.toMoveTrace (le_refl L)
    change (T.state 0).selected.dimension + up =
      (T.state L).selected.dimension + down at hbalance
    have hexponent : (T.state L).selected.dimension - ell ≤
        up + (initial.selected.dimension - ell) := by
      rw [hzeroRank] at hbalance
      omega
    calc
      ((T.state L).selected.progression.volume : ℝ) ≤
          p.cost ^ (D0 + 2 * J) * 1 *
            (Real.rpow (m : ℝ) (-a)) ^ up *
              (initial.selected.progression.volume : ℝ) := hvolumeNoShrink
      _ ≤ p.cost ^ (D0 + 2 * J) * 1 *
          (Real.rpow (m : ℝ) (-a)) ^ up *
            (initialCost * (Real.rpow (m : ℝ) (-a)) ^
              (initial.selected.dimension - ell) * boxSize) := by
        exact mul_le_mul_of_nonneg_left hinitialUnified
          (mul_nonneg
            (mul_nonneg (pow_nonneg p.cost_nonneg _) zero_le_one)
            (pow_nonneg hupBaseNonneg _))
      _ = (p.cost ^ (D0 + 2 * J) * initialCost) *
          (Real.rpow (m : ℝ) (-a)) ^
            (up + (initial.selected.dimension - ell)) * boxSize := by
        rw [pow_add]
        ring
      _ ≤ (p.cost ^ (D0 + 2 * J) * initialCost) *
          (Real.rpow (m : ℝ) (-a)) ^
            ((T.state L).selected.dimension - ell) * boxSize := by
        apply mul_le_mul_of_nonneg_right _ hbox0
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hupBaseNonneg hupBaseOne hexponent)
          (mul_nonneg (pow_nonneg p.cost_nonneg _) hinitialCost0)
      _ = (p.cost ^ (D0 + 2 * J) * initialCost) *
          Real.rpow (m : ℝ)
            (-a * (((T.state L).selected.dimension - ell : ℕ) : ℝ)) *
              boxSize := by rw [rpow_neg_pow_nat hmpos]
  · intro hfinalEqual
    have hlength : L = changes + shrinks := by
      simpa [changes, shrinks] using length_eq_sum_kindCount H.toMoveTrace L
    have hbalance := dimension_balance H.toMoveTrace (le_refl L)
    change (T.state 0).selected.dimension + up =
      (T.state L).selected.dimension + down at hbalance
    rw [hzeroRank, hfinalEqual] at hbalance
    let q := up + (initial.selected.dimension - ell)
    have hdownQ : down ≤ q := by dsimp [q]; omega
    have hupQ : up ≤ q := by dsimp [q]; omega
    have hchangeRaw : changes ≤ up + down := by
      have hu := upCount_le_upwardJump H.toMoveTrace (le_refl L)
      have hd := downCount_le_downwardJump H.toMoveTrace (le_refl L)
      dsimp [changes, up, down]
      omega
    have hchangesQ : changes ≤ 2 * q := by omega
    have hret := retention_pow_mul_le_population H.toMoveTrace (le_refl L)
    change p.retention ^ L * ((T.state 0).points.card : ℝ) ≤
      ((T.state L).points.card : ℝ) at hret
    rw [H.retention_eq, hzeroCard] at hret
    have hequalScalar := equalRank_shrink_up_bound m L changes shrinks q K
      ((T.state L).points.card : ℝ) delta gamma a hdelta0 hgamma0
      hgammaDelta hgammaLower hret hlength hchangesQ hm ha
    calc
      ((T.state L).selected.progression.volume : ℝ) ≤
          p.cost ^ (D0 + 2 * J) * gamma ^ shrinks *
            (Real.rpow (m : ℝ) (-a)) ^ up *
              (initial.selected.progression.volume : ℝ) := hvolumeCost
      _ ≤ p.cost ^ (D0 + 2 * J) * gamma ^ shrinks *
          (Real.rpow (m : ℝ) (-a)) ^ up *
            (initialCost * (Real.rpow (m : ℝ) (-a)) ^
              (initial.selected.dimension - ell) * boxSize) := by
        exact mul_le_mul_of_nonneg_left hinitialUnified
          (mul_nonneg
            (mul_nonneg (pow_nonneg p.cost_nonneg _)
              (pow_nonneg hgamma0.le _)) (pow_nonneg hupBaseNonneg _))
      _ = (p.cost ^ (D0 + 2 * J) * initialCost) *
          (gamma ^ shrinks * (Real.rpow (m : ℝ) (-a)) ^ q) *
            boxSize := by
        dsimp [q]
        rw [pow_add]
        ring
      _ ≤ (p.cost ^ (D0 + 2 * J) * initialCost) *
          (((T.state L).points.card : ℝ) / (m : ℝ)) ^ K * boxSize := by
        apply mul_le_mul_of_nonneg_right _ hbox0
        exact mul_le_mul_of_nonneg_left hequalScalar
          (mul_nonneg (pow_nonneg p.cost_nonneg _) hinitialCost0)
  · intro _hfinalLow
    exact hvolumeCoarse

end

end Erdos186.PZ.Reduction
