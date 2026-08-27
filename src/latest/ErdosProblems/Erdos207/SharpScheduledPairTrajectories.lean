/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AvailabilityLowerTrajectory
import ErdosProblems.Erdos207.TimedFullyScheduledAggregatePairBand

/-!
# Pair trajectories using the actual scheduled envelopes

The earlier linear trajectories used the terminal pair floor and therefore
lost the cubic scaling in a long initial phase.  Here the drift rates use the
four envelopes at the current clock value: lower/upper availability and
lower/upper live-pair degree.
-/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

/-- Conservative deletion rate for the upper pair trajectory. -/
def sharpScheduledPairUpperRate (M d u : ℕ) : ℝ :=
  (M : ℝ)⁻¹ * (d : ℝ) * ((3 * d - 2 - u : ℕ) : ℝ)

/-- Conservative deletion rate for the lower pair trajectory, using the
aggregate pair-star incidence cutoff. -/
def sharpScheduledPairLowerRate (D u Kinc : ℕ) : ℝ :=
  ((D - u : ℕ) : ℝ)⁻¹ * (((u : ℝ) * (2 * u : ℕ)) + Kinc)

lemma sharpScheduledPairUpperRate_nonneg (M d u : ℕ) :
    0 ≤ sharpScheduledPairUpperRate M d u := by
  unfold sharpScheduledPairUpperRate
  positivity

lemma sharpScheduledPairLowerRate_nonneg (D u Kinc : ℕ) :
    0 ≤ sharpScheduledPairLowerRate D u Kinc := by
  unfold sharpScheduledPairLowerRate
  positivity

/-- Monotonicity of the sharp survival-masked lower rate under a smaller
availability denominator and a larger pair cap. -/
lemma sharpScheduledPairLowerRate_mono
    {D Dmin u umax Kinc : ℕ}
    (hD : Dmin ≤ D) (hu : u ≤ umax) (hgap : umax < Dmin) :
    sharpScheduledPairLowerRate D u Kinc ≤
      sharpScheduledPairLowerRate Dmin umax Kinc := by
  have hdenNat : Dmin - umax ≤ D - u := by omega
  have hdenPos : 0 < Dmin - umax := Nat.sub_pos_of_lt hgap
  have hdenPos' : 0 < D - u := hdenPos.trans_le hdenNat
  have hinv : (((D - u : ℕ) : ℝ))⁻¹ ≤
      (((Dmin - umax : ℕ) : ℝ))⁻¹ := by
    apply (inv_le_inv₀ (by exact_mod_cast hdenPos')
      (by exact_mod_cast hdenPos)).mpr
    exact_mod_cast hdenNat
  have hnum : ((u : ℝ) * (2 * u : ℕ)) + Kinc ≤
      ((umax : ℝ) * (2 * umax : ℕ)) + Kinc := by
    gcongr
  unfold sharpScheduledPairLowerRate
  exact mul_le_mul hinv hnum (by positivity) (by positivity)

/-- Upper target obtained by integrating the scheduled conservative rates. -/
def sharpScheduledPairUpperTarget
    {V : Type*} [Fintype V] [DecidableEq V]
    (S₀ : GreedyStateOn V) (Mschedule dschedule uschedule : ℕ → ℕ)
    (P : PairOn V) (i : ℕ) : ℝ :=
  fixedPairAvailableCountReal S₀ P.1 S₀ -
    ∑ j ∈ range i,
      sharpScheduledPairUpperRate
        (Mschedule j) (dschedule j) (uschedule j)

/-- Lower target obtained by integrating the scheduled aggregate rates. -/
def sharpScheduledPairLowerTarget
    {V : Type*} [Fintype V] [DecidableEq V]
    (S₀ : GreedyStateOn V) (Dschedule uschedule : ℕ → ℕ) (Kinc : ℕ)
    (P : PairOn V) (i : ℕ) : ℝ :=
  fixedPairAvailableCountReal S₀ P.1 S₀ -
    ∑ j ∈ range i,
      sharpScheduledPairLowerRate (Dschedule j) (uschedule j) Kinc

@[simp]
lemma sharpScheduledPairUpperTarget_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (S₀ : GreedyStateOn V) (M d u : ℕ → ℕ) (P : PairOn V) :
    sharpScheduledPairUpperTarget S₀ M d u P 0 =
      fixedPairAvailableCountReal S₀ P.1 S₀ := by
  simp [sharpScheduledPairUpperTarget]

@[simp]
lemma sharpScheduledPairLowerTarget_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (S₀ : GreedyStateOn V) (D u : ℕ → ℕ) (Kinc : ℕ) (P : PairOn V) :
    sharpScheduledPairLowerTarget S₀ D u Kinc P 0 =
      fixedPairAvailableCountReal S₀ P.1 S₀ := by
  simp [sharpScheduledPairLowerTarget]

lemma sharpScheduledPairUpperTarget_succ_sub
    {V : Type*} [Fintype V] [DecidableEq V]
    (S₀ : GreedyStateOn V) (M d u : ℕ → ℕ) (P : PairOn V) (i : ℕ) :
    sharpScheduledPairUpperTarget S₀ M d u P (i + 1) -
        sharpScheduledPairUpperTarget S₀ M d u P i =
      -sharpScheduledPairUpperRate (M i) (d i) (u i) := by
  simp [sharpScheduledPairUpperTarget, sum_range_succ]

lemma sharpScheduledPairLowerTarget_succ_sub
    {V : Type*} [Fintype V] [DecidableEq V]
    (S₀ : GreedyStateOn V) (D u : ℕ → ℕ) (Kinc : ℕ)
    (P : PairOn V) (i : ℕ) :
    sharpScheduledPairLowerTarget S₀ D u Kinc P (i + 1) -
        sharpScheduledPairLowerTarget S₀ D u Kinc P i =
      -sharpScheduledPairLowerRate (D i) (u i) Kinc := by
  simp [sharpScheduledPairLowerTarget, sum_range_succ]

/-- The scheduled upper rate is no larger than the forced deletion rate of
any currently live pair. -/
theorem sharpScheduledPairUpperRate_le_current
    {V : Type*} [Fintype V] [DecidableEq V]
    {S : GreedyStateOn V} {P : PairOn V} {M d u : ℕ}
    (hnonempty : S.available.Nonempty)
    (hM : S.available.card ≤ M)
    (hfloor : HasAvailablePairFloor d S)
    (_hupper : HasAvailablePairCutoff u S)
    (halive : PairAlive P.1 S) :
    sharpScheduledPairUpperRate M d u ≤
      (S.available.card : ℝ)⁻¹ *
        ((availableTrianglesContainingPair S P.1).card : ℝ) *
          ((3 * d - 2 - u : ℕ) : ℝ) := by
  have hApos : 0 < S.available.card := card_pos.mpr hnonempty
  have hMpos : 0 < M := hApos.trans_le hM
  have hinv : (M : ℝ)⁻¹ ≤ (S.available.card : ℝ)⁻¹ := by
    apply (inv_le_inv₀ (by exact_mod_cast hMpos) (by exact_mod_cast hApos)).mpr
    exact_mod_cast hM
  have hpair : d ≤ (availableTrianglesContainingPair S P.1).card :=
    hfloor P.1 P.2 halive
  unfold sharpScheduledPairUpperRate
  gcongr

/-- Uniform scheduled variance budget for the upper martingale. -/
def sharpScheduledPairUpperVariance
    (D u Kpair Kglobal : ℕ) (r : ℝ) : ℝ :=
  2 * ((D : ℝ)⁻¹ * (u : ℝ) *
      (((3 + Kpair : ℕ) : ℝ) * ((3 * u + Kglobal : ℕ) : ℝ))) +
    2 * r ^ 2

/-- Uniform scheduled variance budget for the aggregate lower martingale. -/
def sharpScheduledPairLowerVariance
    (D u Kpair Kinc : ℕ) (r : ℝ) : ℝ :=
  2 * ((D : ℝ)⁻¹ *
      (((3 + Kpair : ℕ) : ℝ) *
        ((u : ℝ) * (3 * u : ℕ) + Kinc))) +
    2 * r ^ 2

theorem sharpScheduledPairUpperVariance_current_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {S : GreedyStateOn V} {P : PairOn V}
    {D u Kpair Kglobal : ℕ} (r : ℝ)
    (hDpos : 0 < D) (hD : D ≤ S.available.card)
    (hupper : HasAvailablePairCutoff u S) :
    2 * ((S.available.card : ℝ)⁻¹ *
          (((availableTrianglesContainingPair S P.1).card : ℝ) *
            (((3 + Kpair : ℕ) : ℝ) *
              ((3 * u + Kglobal : ℕ) : ℝ)))) +
        2 * r ^ 2 ≤
      sharpScheduledPairUpperVariance D u Kpair Kglobal r := by
  have hApos : 0 < S.available.card := hDpos.trans_le hD
  have hinv : (S.available.card : ℝ)⁻¹ ≤ (D : ℝ)⁻¹ := by
    apply (inv_le_inv₀ (by exact_mod_cast hApos) (by exact_mod_cast hDpos)).mpr
    exact_mod_cast hD
  have hpair : (availableTrianglesContainingPair S P.1).card ≤ u :=
    hupper P.1 P.2
  have hpairReal :
      ((availableTrianglesContainingPair S P.1).card : ℝ) ≤ (u : ℝ) := by
    exact_mod_cast hpair
  have hmain :
      (S.available.card : ℝ)⁻¹ *
          ((availableTrianglesContainingPair S P.1).card : ℝ) ≤
        (D : ℝ)⁻¹ * (u : ℝ) :=
    mul_le_mul hinv hpairReal (by positivity) (by positivity)
  unfold sharpScheduledPairUpperVariance
  calc
    2 * ((S.available.card : ℝ)⁻¹ *
          (((availableTrianglesContainingPair S P.1).card : ℝ) *
            (((3 + Kpair : ℕ) : ℝ) *
              ((3 * u + Kglobal : ℕ) : ℝ)))) + 2 * r ^ 2 =
        2 * (((S.available.card : ℝ)⁻¹ *
            ((availableTrianglesContainingPair S P.1).card : ℝ)) *
              (((3 + Kpair : ℕ) : ℝ) *
                ((3 * u + Kglobal : ℕ) : ℝ))) + 2 * r ^ 2 := by ring
    _ ≤ 2 * (((D : ℝ)⁻¹ * (u : ℝ)) *
              (((3 + Kpair : ℕ) : ℝ) *
                ((3 * u + Kglobal : ℕ) : ℝ))) + 2 * r ^ 2 := by
      gcongr
    _ = 2 * ((D : ℝ)⁻¹ * (u : ℝ) *
        (((3 + Kpair : ℕ) : ℝ) *
          ((3 * u + Kglobal : ℕ) : ℝ))) + 2 * r ^ 2 := by ring

theorem sharpScheduledPairLowerVariance_current_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {S : GreedyStateOn V} {P : PairOn V}
    {D u Kpair Kinc : ℕ} (r : ℝ)
    (hDpos : 0 < D) (hD : D ≤ S.available.card)
    (hupper : HasAvailablePairCutoff u S) :
    2 * ((S.available.card : ℝ)⁻¹ *
          (((3 + Kpair : ℕ) : ℝ) *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (3 * u : ℕ) + Kinc))) +
        2 * r ^ 2 ≤
      sharpScheduledPairLowerVariance D u Kpair Kinc r := by
  have hApos : 0 < S.available.card := hDpos.trans_le hD
  have hinv : (S.available.card : ℝ)⁻¹ ≤ (D : ℝ)⁻¹ := by
    apply (inv_le_inv₀ (by exact_mod_cast hApos) (by exact_mod_cast hDpos)).mpr
    exact_mod_cast hD
  have hpair : (availableTrianglesContainingPair S P.1).card ≤ u :=
    hupper P.1 P.2
  unfold sharpScheduledPairLowerVariance
  have hinside :
      (((3 + Kpair : ℕ) : ℝ) *
        (((availableTrianglesContainingPair S P.1).card : ℝ) *
          ((3 * u : ℕ) : ℝ) + (Kinc : ℝ))) ≤
      (((3 + Kpair : ℕ) : ℝ) *
        ((u : ℝ) * ((3 * u : ℕ) : ℝ) + (Kinc : ℝ))) := by
    gcongr
  have hmain :
      (S.available.card : ℝ)⁻¹ *
          (((3 + Kpair : ℕ) : ℝ) *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              ((3 * u : ℕ) : ℝ) + (Kinc : ℝ))) ≤
        (D : ℝ)⁻¹ *
          (((3 + Kpair : ℕ) : ℝ) *
            ((u : ℝ) * ((3 * u : ℕ) : ℝ) + (Kinc : ℝ))) :=
    mul_le_mul hinv hinside (by positivity) (by positivity)
  exact add_le_add (mul_le_mul_of_nonneg_left hmain (by norm_num)) le_rfl

end

end Erdos207
