/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TimedPairBandPhase

/-!
# Positive-mass success witness for a timed pair-band phase

The phase extractor is often followed by several independent support
invariants.  This version retains the positive-mass timed terminal state, so
all of those invariants can be evaluated on the same successful trajectory.
-/

namespace Erdos207

noncomputable section

/-- If premature stopping and two-away failure have total probability below
one, the common timed law has a positive-mass state at the horizon with the
two-away cutoff intact. -/
theorem exists_timedPairBand_success_with_mass_of_failure_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V)
    (K Delta delta : ℕ) (D : ℕ → ℕ) (epsilonPair epsilonTwo : ℝ)
    (hpair :
      let active := timedPairBandActive F K Delta delta D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      (L.probability
        (fun z ↦ z.1.1 ≠ n ∧ HasTwoAwayCutoff F K z.2) : ℝ) ≤ epsilonPair)
    (htwo :
      let active := timedPairBandActive F K Delta delta D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      (L.probability
        (fun z ↦ ¬ HasTwoAwayCutoff F K z.2) : ℝ) ≤ epsilonTwo)
    (hsmall : epsilonPair + epsilonTwo < 1) :
    let active := timedPairBandActive F K Delta delta D
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    ∃ z, z.1.1 = n ∧ HasTwoAwayCutoff F K z.2 ∧ 0 < L.mass z := by
  classical
  dsimp only
  let active := timedPairBandActive F K Delta delta D
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let earlyWithCutoff : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ z.1.1 ≠ n ∧ HasTwoAwayCutoff F K z.2
  let cutoffFailure : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ ¬ HasTwoAwayCutoff F K z.2
  let failure : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ z.1.1 ≠ n ∨ ¬ HasTwoAwayCutoff F K z.2
  let success : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ z.1.1 = n ∧ HasTwoAwayCutoff F K z.2
  have hfailureSubset : ∀ z, failure z →
      earlyWithCutoff z ∨ cutoffFailure z := by
    intro z hz
    by_cases hcut : HasTwoAwayCutoff F K z.2
    · exact Or.inl ⟨hz.resolve_right (not_not_intro hcut), hcut⟩
    · exact Or.inr hcut
  have hmono := L.probability_mono hfailureSubset
  have hor := L.probability_or_le earlyWithCutoff cutoffFailure
  have hmonoReal : (L.probability failure : ℝ) ≤
      (L.probability (fun z ↦
        earlyWithCutoff z ∨ cutoffFailure z) : ℝ) := by
    exact_mod_cast hmono
  have horReal :
      (L.probability (fun z ↦
        earlyWithCutoff z ∨ cutoffFailure z) : ℝ) ≤
        (L.probability earlyWithCutoff : ℝ) +
          (L.probability cutoffFailure : ℝ) := by
    exact_mod_cast hor
  have hfailure : (L.probability failure : ℝ) < 1 := by
    calc
      (L.probability failure : ℝ) ≤
          (L.probability (fun z ↦
            earlyWithCutoff z ∨ cutoffFailure z) : ℝ) := hmonoReal
      _ ≤ (L.probability earlyWithCutoff : ℝ) +
          (L.probability cutoffFailure : ℝ) := horReal
      _ ≤ epsilonPair + epsilonTwo := add_le_add
        (by simpa [L, active, earlyWithCutoff] using hpair)
        (by simpa [L, active, cutoffFailure] using htwo)
      _ < 1 := hsmall
  have hsuccessNot : (fun z ↦ ¬ failure z) = success := by
    funext z
    apply propext
    simp [failure, success]
  have hsuccessReal : 0 < (L.probability success : ℝ) := by
    rw [← hsuccessNot, L.probability_not]
    rw [NNReal.coe_sub (L.probability_le_one failure)]
    norm_num only [NNReal.coe_one]
    exact sub_pos.mpr hfailure
  have hsuccess : 0 < L.probability success := by
    exact_mod_cast hsuccessReal
  obtain ⟨z, hz, hmass⟩ :=
    L.exists_of_probability_pos_with_mass hsuccess
  exact ⟨z, hz.1, hz.2, hmass⟩

end

end Erdos207
