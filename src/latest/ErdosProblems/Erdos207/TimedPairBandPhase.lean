/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TimedPairBandBootstrap
import ErdosProblems.Erdos207.TimedPairBandTwoCutoffs
import ErdosProblems.Erdos207.TimedStoppedTwoAway
import ErdosProblems.Erdos207.CoverDownProbability

/-!
# Positive-probability extraction for a full pair-band phase

The pair-band bootstrap controls premature stopping conditional on the
two-away cutoff.  The A2 moment argument controls failure of that cutoff on
the same timed law.  If the two error bounds sum to less than one, a
positive-mass outcome reaches the horizon, retains the cutoff, preserves the
global availability floor, and has made exactly one insertion per clock step.
-/

namespace Erdos207

noncomputable section

/-- Abstract final union-bound step for the common timed law. -/
theorem exists_timedPairBand_full_phase_of_failure_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V)
    (K Δ δ : ℕ) (D : ℕ → ℕ) (εpair εtwo : ℝ)
    (hInv₀ : GreedyInvariant F S₀)
    {Q : GreedyStateOn V → Prop} (hQ₀ : Q S₀)
    (hQK : ∀ i, i < n → ∀ S, Q S →
      (greedyKernel F S).SupportedOn Q)
    (hfloor₀ : D 0 ≤ S₀.available.card)
    (hdecrease : ∀ i, i < n → D (i + 1) + (3 * Δ + K) ≤ D i)
    (hpair :
      let active := timedPairBandActive F K Δ δ D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      (L.probability
        (fun z ↦ z.1.1 ≠ n ∧ HasTwoAwayCutoff F K z.2) : ℝ) ≤ εpair)
    (htwo :
      let active := timedPairBandActive F K Δ δ D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      (L.probability
        (fun z ↦ ¬ HasTwoAwayCutoff F K z.2) : ℝ) ≤ εtwo)
    (hsmall : εpair + εtwo < 1) :
    ∃ S : GreedyStateOn V,
      Q S ∧ GreedyInvariant F S ∧ HasTwoAwayCutoff F K S ∧
        D n ≤ S.available.card ∧
        S.chosen.card = S₀.chosen.card + n := by
  classical
  let active := timedPairBandActive F K Δ δ D
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
      (L.probability (fun z ↦ earlyWithCutoff z ∨ cutoffFailure z) : ℝ) := by
    exact_mod_cast hmono
  have horReal :
      (L.probability (fun z ↦ earlyWithCutoff z ∨ cutoffFailure z) : ℝ) ≤
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
      _ ≤ εpair + εtwo := add_le_add (by simpa [L, active,
        earlyWithCutoff] using hpair) (by simpa [L, active,
          cutoffFailure] using htwo)
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
  obtain ⟨z, hzsuccess, hmass⟩ :=
    L.exists_of_probability_pos_with_mass hsuccess
  have hprogress := timedPairBandProcessLaw_supported_progress
    hInv₀ hfloor₀ hdecrease z hmass
  have hQsupport : L.SupportedOn (fun z ↦ Q z.2) :=
    FiniteLaw.timedStoppedProcessLaw_supported n
      (fun _ ↦ greedyKernel F) active S₀ hQ₀ hQK
  exact ⟨z.2, hQsupport z hmass, hprogress.1.1, hzsuccess.2,
    by simpa [hzsuccess.1] using hprogress.2.1,
    by simpa [hzsuccess.1] using hprogress.2.2⟩

/-- Final union bound for a timed phase with separate pair-local and global
two-away cutoffs. -/
theorem exists_timedPairBandTwoCutoffs_full_phase_of_failure_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V)
    (Kpair Kglobal Δ δ : ℕ) (D : ℕ → ℕ)
    (εband εpairTwo εglobalTwo : ℝ)
    (hInv₀ : GreedyInvariant F S₀)
    {Q : GreedyStateOn V → Prop}
    (hQsupport :
      let active := timedPairBandActiveTwoCutoffs
        F Kpair Kglobal Δ δ D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      L.SupportedOn (fun z ↦ Q z.2))
    (hfloor₀ : D 0 ≤ S₀.available.card)
    (hdecrease : ∀ i, i < n →
      D (i + 1) + (3 * Δ + Kglobal) ≤ D i)
    (hband :
      let active := timedPairBandActiveTwoCutoffs
        F Kpair Kglobal Δ δ D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      (L.probability (fun z ↦ z.1.1 ≠ n ∧
        HasPairTwoAwayCutoff F Kpair z.2 ∧
        HasTwoAwayCutoff F Kglobal z.2) : ℝ) ≤ εband)
    (hpairTwo :
      let active := timedPairBandActiveTwoCutoffs
        F Kpair Kglobal Δ δ D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      (L.probability
        (fun z ↦ ¬ HasPairTwoAwayCutoff F Kpair z.2) : ℝ) ≤ εpairTwo)
    (hglobalTwo :
      let active := timedPairBandActiveTwoCutoffs
        F Kpair Kglobal Δ δ D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      (L.probability
        (fun z ↦ ¬ HasTwoAwayCutoff F Kglobal z.2) : ℝ) ≤ εglobalTwo)
    (hsmall : εband + εpairTwo + εglobalTwo < 1) :
    ∃ S : GreedyStateOn V,
      Q S ∧ GreedyInvariant F S ∧
        HasPairTwoAwayCutoff F Kpair S ∧
        HasTwoAwayCutoff F Kglobal S ∧
        D n ≤ S.available.card ∧
        S.chosen.card = S₀.chosen.card + n := by
  classical
  let active := timedPairBandActiveTwoCutoffs F Kpair Kglobal Δ δ D
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let early : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ z.1.1 ≠ n ∧ HasPairTwoAwayCutoff F Kpair z.2 ∧
      HasTwoAwayCutoff F Kglobal z.2
  let pairFailure : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ ¬ HasPairTwoAwayCutoff F Kpair z.2
  let globalFailure : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ ¬ HasTwoAwayCutoff F Kglobal z.2
  let failure : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ z.1.1 ≠ n ∨ ¬ HasPairTwoAwayCutoff F Kpair z.2 ∨
      ¬ HasTwoAwayCutoff F Kglobal z.2
  let success : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ z.1.1 = n ∧ HasPairTwoAwayCutoff F Kpair z.2 ∧
      HasTwoAwayCutoff F Kglobal z.2
  have hfailureSubset : ∀ z, failure z →
      (early z ∨ pairFailure z) ∨ globalFailure z := by
    intro z hz
    by_cases hp : HasPairTwoAwayCutoff F Kpair z.2
    · by_cases hg : HasTwoAwayCutoff F Kglobal z.2
      · exact Or.inl (Or.inl ⟨hz.resolve_right
          (fun h ↦ h.elim (fun hnp ↦ hnp hp) (fun hng ↦ hng hg)), hp, hg⟩
          )
      · exact Or.inr hg
    · exact Or.inl (Or.inr hp)
  have hmono := L.probability_mono hfailureSubset
  have hor₁ := L.probability_or_le early pairFailure
  have hor₂ := L.probability_or_le
    (fun z ↦ early z ∨ pairFailure z) globalFailure
  have hmonoReal : (L.probability failure : ℝ) ≤
      (L.probability
        (fun z ↦ (early z ∨ pairFailure z) ∨ globalFailure z) : ℝ) := by
    exact_mod_cast hmono
  have hor₁Real :
      (L.probability (fun z ↦ early z ∨ pairFailure z) : ℝ) ≤
        (L.probability early : ℝ) + (L.probability pairFailure : ℝ) := by
    exact_mod_cast hor₁
  have hor₂Real :
      (L.probability (fun z ↦ (early z ∨ pairFailure z) ∨ globalFailure z) : ℝ) ≤
        (L.probability (fun z ↦ early z ∨ pairFailure z) : ℝ) +
          (L.probability globalFailure : ℝ) := by
    exact_mod_cast hor₂
  have hfailure : (L.probability failure : ℝ) < 1 := by
    calc
      (L.probability failure : ℝ) ≤
          (L.probability (fun z ↦
            (early z ∨ pairFailure z) ∨ globalFailure z) : ℝ) := hmonoReal
      _ ≤ (L.probability (fun z ↦ early z ∨ pairFailure z) : ℝ) +
          (L.probability globalFailure : ℝ) := hor₂Real
      _ ≤ (L.probability early : ℝ) + (L.probability pairFailure : ℝ) +
          (L.probability globalFailure : ℝ) :=
        add_le_add hor₁Real le_rfl
      _ ≤ εband + εpairTwo + εglobalTwo := by
        exact add_le_add
          (add_le_add
            (by simpa [L, active, early] using hband)
            (by simpa [L, active, pairFailure] using hpairTwo))
          (by simpa [L, active, globalFailure] using hglobalTwo)
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
  obtain ⟨z, hzsuccess, hmass⟩ :=
    L.exists_of_probability_pos_with_mass hsuccess
  have hprogress := timedPairBandTwoCutoffsProcessLaw_supported_progress
    hInv₀ hfloor₀ hdecrease z hmass
  exact ⟨z.2, hQsupport z hmass, hprogress.1.1, hzsuccess.2.1,
    hzsuccess.2.2, by simpa [hzsuccess.1] using hprogress.2.1,
    by simpa [hzsuccess.1] using hprogress.2.2⟩

end

end Erdos207
