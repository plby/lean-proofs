/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyDeletionIncidence
import ErdosProblems.Erdos207.FiniteStoppedKernel

/-!
# Concentration of global availability from aggregate deletion incidences

The global availability loss is centered by its aggregate conditional
first-moment bound, rather than by the maximum possible one-step loss.  A
maximum pair degree and a maximum two-away degree are still used for the
jump and variance terms, while the drift uses only the single total
two-away-incidence cutoff.
-/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

/-- Conditional loss rate supplied by a pair-degree cutoff `Δ`, a total
two-away cutoff `I`, and an availability floor `D`. -/
def averageAvailabilityLossRate (Δ I D : ℕ) : ℝ :=
  (3 * Δ : ℕ) + (I : ℝ) / D

/-- The timed process is active while the two pointwise cutoffs, the one
aggregate cutoff, and the global availability floor all hold. -/
def timedAverageAvailabilityActive
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Δ K I D : ℕ)
    (_i : ℕ) (S : GreedyStateOn V) : Prop :=
  HasAvailablePairCutoff Δ S ∧
    HasTwoAwayCutoff F K S ∧
    totalAvailableTwoAwayIncidences F S ≤ I ∧
    D ≤ S.available.card

/-- Centered accumulated availability loss. -/
def averageAvailabilityDeficit
    {V : Type*} [Fintype V] [DecidableEq V]
    (rate : ℝ) (i : ℕ) (S : GreedyStateOn V) : ℝ :=
  -((S.available.card : ℕ) : ℝ) - (i : ℝ) * rate

/-- The normalized aggregate incidence envelope is at most the advertised
average loss rate throughout the active region. -/
lemma availableIncidenceEnvelope_le_averageRate
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {Δ I D : ℕ}
    (htotal : totalAvailableTwoAwayIncidences F S ≤ I)
    (hD : 0 < D) (hfloor : D ≤ S.available.card) :
    (S.available.card : ℝ)⁻¹ *
        ((S.available.card * (3 * Δ) +
          totalAvailableTwoAwayIncidences F S : ℕ) : ℝ) ≤
      averageAvailabilityLossRate Δ I D := by
  have htotalReal :
      (totalAvailableTwoAwayIncidences F S : ℝ) ≤ (I : ℝ) := by
    exact_mod_cast htotal
  have hfloorReal : (D : ℝ) ≤ (S.available.card : ℝ) := by
    exact_mod_cast hfloor
  have hDReal : (0 : ℝ) < D := by exact_mod_cast hD
  have hAReal : (0 : ℝ) < S.available.card :=
    hDReal.trans_le hfloorReal
  have hfrac :
      (totalAvailableTwoAwayIncidences F S : ℝ) /
          (S.available.card : ℝ) ≤
        (I : ℝ) / D := by
    gcongr
  rw [show ((S.available.card * (3 * Δ) +
      totalAvailableTwoAwayIncidences F S : ℕ) : ℝ) =
    (S.available.card : ℝ) * (3 * Δ : ℕ) +
      (totalAvailableTwoAwayIncidences F S : ℝ) by norm_cast]
  rw [inv_mul_eq_div]
  field_simp [hAReal.ne']
  rw [averageAvailabilityLossRate]
  field_simp [hDReal.ne'] at hfrac ⊢
  nlinarith

/-- Aggregate incidence accounting gives the advertised conditional mean
loss rate. -/
theorem greedyKernel_expectationReal_availabilityLoss_le_averageRate
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {Δ I D : ℕ}
    (hInv : GreedyInvariant F S) (hpair : HasAvailablePairCutoff Δ S)
    (htotal : totalAvailableTwoAwayIncidences F S ≤ I)
    (hD : 0 < D) (hfloor : D ≤ S.available.card) :
    (greedyKernel F S).expectationReal (fun S' ↦
        (S.available.card : ℝ) - (S'.available.card : ℝ)) ≤
      averageAvailabilityLossRate Δ I D := by
  have hA : S.available.Nonempty := by
    rw [← card_pos]
    exact hD.trans_le hfloor
  have hinc :=
    greedyKernel_expectationReal_availableCount_increment_ge_incidence
      hInv hpair hA
  let inc : GreedyStateOn V → ℝ := fun S' ↦
    greedyAvailableCountReal (univ : TripleSystemOn V) S' -
      greedyAvailableCountReal (univ : TripleSystemOn V) S
  have hcount (R : GreedyStateOn V) :
      greedyAvailableCountReal (univ : TripleSystemOn V) R =
        (R.available.card : ℝ) := by
    simp [greedyAvailableCountReal, greedyAvailableIn]
  have hloss :
      (greedyKernel F S).expectationReal (fun S' ↦
          (S.available.card : ℝ) - (S'.available.card : ℝ)) =
        -(greedyKernel F S).expectationReal inc := by
    have hfun : (fun S' : GreedyStateOn V ↦
        (S.available.card : ℝ) - (S'.available.card : ℝ)) =
        (fun S' ↦ 0 - inc S') := by
      funext S'
      simp only [inc, hcount]
      ring
    rw [hfun, FiniteLaw.expectationReal_sub,
      FiniteLaw.expectationReal_zero, zero_sub]
  have henvelope := availableIncidenceEnvelope_le_averageRate
    (Δ := Δ) htotal hD hfloor
  rw [hloss]
  have hinc' :
      -((S.available.card : ℝ)⁻¹) *
          ((S.available.card * (3 * Δ) +
            totalAvailableTwoAwayIncidences F S : ℕ) : ℝ) ≤
        (greedyKernel F S).expectationReal inc := by
    simpa only [inc] using hinc
  nlinarith

/-- Under the two pointwise cutoffs, a supported greedy successor has
centered availability-loss jump at most `3Δ+K`. -/
theorem averageAvailabilityDeficit_jump_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S S' : GreedyStateOn V}
    {Δ K I D i : ℕ}
    (hInv : GreedyInvariant F S)
    (hactive : timedAverageAvailabilityActive F Δ K I D i S)
    (hmass : 0 < (greedyKernel F S).mass S') :
    averageAvailabilityDeficit (averageAvailabilityLossRate Δ I D)
        (i + 1) S' -
      averageAvailabilityDeficit (averageAvailabilityLossRate Δ I D)
        i S ≤ (3 * Δ + K : ℕ) := by
  have hrNonneg : 0 ≤ averageAvailabilityLossRate Δ I D := by
    unfold averageAvailabilityLossRate
    positivity
  rcases greedyKernel_supported_step_or_self F S S' hmass with
    rfl | ⟨T, hT, rfl⟩
  · simp only [averageAvailabilityDeficit]
    push_cast
    nlinarith
  · have hpartition := greedyDeletedIn_card_add_step_card
      F (univ : TripleSystemOn V) S T
    rw [greedyAvailableIn_univ, greedyAvailableIn_univ] at hpartition
    have hdeleted := card_greedyDeleted_available_le_pairCutoff
      hInv hactive.1 hactive.2.1 hT
    have hpartitionReal :
        ((greedyDeletedIn F (univ : TripleSystemOn V) S T).card : ℝ) +
          ((greedyStep F S T).available.card : ℝ) =
            (S.available.card : ℝ) := by
      exact_mod_cast hpartition
    have hdeletedReal :
        ((greedyDeletedIn F (univ : TripleSystemOn V) S T).card : ℝ) ≤
          (3 * Δ + K : ℕ) := by
      exact_mod_cast hdeleted
    have heq :
        averageAvailabilityDeficit (averageAvailabilityLossRate Δ I D)
            (i + 1) (greedyStep F S T) -
          averageAvailabilityDeficit (averageAvailabilityLossRate Δ I D)
            i S =
          (S.available.card : ℝ) -
            ((greedyStep F S T).available.card : ℝ) -
              averageAvailabilityLossRate Δ I D := by
      simp only [averageAvailabilityDeficit]
      push_cast
      ring
    rw [heq]
    nlinarith

/-- The centered global-availability deficit has nonpositive conditional
drift throughout the active region. -/
theorem greedyKernel_expectationReal_averageAvailabilityDeficit_increment_le_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {Δ K I D i : ℕ}
    (hInv : GreedyInvariant F S)
    (hD : 0 < D)
    (hactive : timedAverageAvailabilityActive F Δ K I D i S) :
    (greedyKernel F S).expectationReal (fun S' ↦
        averageAvailabilityDeficit (averageAvailabilityLossRate Δ I D)
            (i + 1) S' -
          averageAvailabilityDeficit (averageAvailabilityLossRate Δ I D)
            i S) ≤ 0 := by
  let rate := averageAvailabilityLossRate Δ I D
  have hloss := greedyKernel_expectationReal_availabilityLoss_le_averageRate
    hInv hactive.1 hactive.2.2.1 hD hactive.2.2.2
  have hfun : (fun S' : GreedyStateOn V ↦
      averageAvailabilityDeficit rate (i + 1) S' -
        averageAvailabilityDeficit rate i S) =
      (fun S' ↦
        ((S.available.card : ℝ) - (S'.available.card : ℝ)) - rate) := by
    funext S'
    simp only [averageAvailabilityDeficit]
    push_cast
    ring
  rw [hfun, FiniteLaw.expectationReal_sub,
    FiniteLaw.expectationReal_const]
  exact sub_nonpos.mpr hloss

/-- Conditional second moment of the centered deficit. -/
theorem greedyKernel_expectationReal_averageAvailabilityDeficit_sqIncrement_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {Δ K I D i : ℕ}
    (hInv : GreedyInvariant F S)
    (hD : 0 < D)
    (hactive : timedAverageAvailabilityActive F Δ K I D i S) :
    (greedyKernel F S).expectationReal (fun S' ↦
        (averageAvailabilityDeficit (averageAvailabilityLossRate Δ I D)
            (i + 1) S' -
          averageAvailabilityDeficit (averageAvailabilityLossRate Δ I D)
            i S) ^ 2) ≤
      2 * ((3 * Δ + K : ℕ) : ℝ) *
          averageAvailabilityLossRate Δ I D +
        2 * (averageAvailabilityLossRate Δ I D) ^ 2 := by
  let rate := averageAvailabilityLossRate Δ I D
  let inc : GreedyStateOn V → ℝ := fun S' ↦
    greedyAvailableCountReal (univ : TripleSystemOn V) S' -
      greedyAvailableCountReal (univ : TripleSystemOn V) S
  have hA : S.available.Nonempty := by
    rw [← card_pos]
    exact hD.trans_le hactive.2.2.2
  have hincSq :=
    greedyKernel_expectationReal_availableCount_sqIncrement_le_incidence
      hInv hactive.1 hactive.2.1 hA
  have henvelope :
      (S.available.card : ℝ)⁻¹ *
          ((S.available.card * (3 * Δ) +
            totalAvailableTwoAwayIncidences F S : ℕ) : ℝ) ≤ rate := by
    exact availableIncidenceEnvelope_le_averageRate
      (Δ := Δ) hactive.2.2.1 hD hactive.2.2.2
  have hincSq' :
      (greedyKernel F S).expectationReal (fun S' ↦ (inc S') ^ 2) ≤
        ((3 * Δ + K : ℕ) : ℝ) * rate := by
    have hcoef : (0 : ℝ) ≤ ((3 * Δ + K : ℕ) : ℝ) := by positivity
    calc
      (greedyKernel F S).expectationReal (fun S' ↦ (inc S') ^ 2) ≤
          ((3 * Δ + K : ℕ) : ℝ) *
            ((S.available.card : ℝ)⁻¹ *
              ((S.available.card * (3 * Δ) +
                totalAvailableTwoAwayIncidences F S : ℕ) : ℝ)) := by
        simpa only [inc, mul_assoc] using hincSq
      _ ≤ ((3 * Δ + K : ℕ) : ℝ) * rate :=
        mul_le_mul_of_nonneg_left henvelope hcoef
  have hpoint : ∀ S',
      (averageAvailabilityDeficit rate (i + 1) S' -
        averageAvailabilityDeficit rate i S) ^ 2 ≤
          2 * (inc S') ^ 2 + 2 * rate ^ 2 := by
    intro S'
    have hcount (R : GreedyStateOn V) :
        greedyAvailableCountReal (univ : TripleSystemOn V) R =
          (R.available.card : ℝ) := by
      simp [greedyAvailableCountReal, greedyAvailableIn]
    have heq :
        averageAvailabilityDeficit rate (i + 1) S' -
            averageAvailabilityDeficit rate i S = -inc S' - rate := by
      simp only [averageAvailabilityDeficit, inc, hcount]
      push_cast
      ring
    rw [heq]
    nlinarith [sq_nonneg (inc S' - rate)]
  calc
    (greedyKernel F S).expectationReal (fun S' ↦
        (averageAvailabilityDeficit rate (i + 1) S' -
          averageAvailabilityDeficit rate i S) ^ 2) ≤
      (greedyKernel F S).expectationReal (fun S' ↦
        2 * (inc S') ^ 2 + 2 * rate ^ 2) :=
      FiniteLaw.expectationReal_mono _ hpoint
    _ = 2 * (greedyKernel F S).expectationReal
          (fun S' ↦ (inc S') ^ 2) + 2 * rate ^ 2 := by
      rw [FiniteLaw.expectationReal_add,
        FiniteLaw.expectationReal_const_mul,
        FiniteLaw.expectationReal_const]
    _ ≤ 2 * (((3 * Δ + K : ℕ) : ℝ) * rate) +
        2 * rate ^ 2 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hincSq' (by norm_num)) le_rfl
    _ = _ := by ring

/-- Exponential lower-tail estimate for global availability under the
aggregate-incidence stopped law. -/
theorem probability_timedAverageAvailability_deficit_ge_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V)
    (Δ K I D : ℕ) (theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀) (hD : 0 < D)
    (hvariance :
      2 * ((3 * Δ + K : ℕ) : ℝ) *
          averageAvailabilityLossRate Δ I D +
        2 * (averageAvailabilityLossRate Δ I D) ^ 2 ≤ v)
    (htheta : 0 < theta)
    (hthetaJump : theta * ((3 * Δ + K : ℕ) : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    let active := timedAverageAvailabilityActive F Δ K I D
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    ((L.probability (fun z ↦
      a ≤ averageAvailabilityDeficit (averageAvailabilityLossRate Δ I D)
          z.1.1 z.2 -
        averageAvailabilityDeficit (averageAvailabilityLossRate Δ I D)
          0 S₀) : ℝ)) ≤
      Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v) := by
  classical
  dsimp only
  apply FiniteLaw.probability_timedStoppedProcess_deviation_ge_le_exp
    (P := fun S ↦ GreedyInvariant F S)
    n (fun _ ↦ greedyKernel F)
      (timedAverageAvailabilityActive F Δ K I D)
      (averageAvailabilityDeficit (averageAvailabilityLossRate Δ I D))
      S₀ theta (3 * Δ + K : ℕ) a v hInv₀ htheta (by positivity)
      hthetaJump hv
  · intro _i _hi S hS
    intro S' hmass
    rcases greedyKernel_supported_step_or_self F S S' hmass with
      rfl | ⟨T, hT, rfl⟩
    · exact hS
    · exact hS.step hT
  · intro i _hi S hS hactive S' hmass _hS'
    exact averageAvailabilityDeficit_jump_le hS hactive hmass
  · intro i _hi S hS hactive
    exact
      greedyKernel_expectationReal_averageAvailabilityDeficit_increment_le_zero
        hS hD hactive
  · intro i _hi S hS hactive
    exact
      (greedyKernel_expectationReal_averageAvailabilityDeficit_sqIncrement_le
        hS hD hactive).trans hvariance

end

end Erdos207
