/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TimedPairBandBootstrap

/-!
# Timed pair-band bootstrap with separate local and global cutoffs

The global two-away cutoff controls the total number of triangles deleted in
one greedy step.  The smaller pair-local cutoff controls the jump of a
surviving pair star.  Keeping these parameters separate is essential for the
numerical KSSS regime.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Timed active region with separate pair-local and global two-away
cutoffs and a deterministic global availability schedule. -/
def timedPairBandActiveTwoCutoffs
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Kpair Kglobal Δ δ : ℕ) (D : ℕ → ℕ)
    (i : ℕ) (S : GreedyStateOn V) : Prop :=
  pairBandActiveTwoCutoffs F Kpair Kglobal Δ δ i S ∧
    D i ≤ S.available.card

/-- One active transition preserves the greedy invariant and advances the
global availability schedule; only the global cutoff enters the decrement. -/
theorem timedPairBandTwoCutoffsKernel_supported_invariant_availability
    {V : Type*} [Fintype V] [DecidableEq V]
    {n : ℕ} {F : ForbiddenFamilyOn V} {Kpair Kglobal Δ δ : ℕ}
    {D : ℕ → ℕ} {S₀ : GreedyStateOn V}
    (hdecrease : ∀ i, i < n → D (i + 1) + (3 * Δ + Kglobal) ≤ D i)
    (z : FiniteLaw.TimedState (GreedyStateOn V) n)
    (hz : PairTrajectoryInvariant F S₀ z.2 ∧ D z.1.1 ≤ z.2.available.card) :
    (FiniteLaw.timedStoppedKernel n (fun _ ↦ greedyKernel F)
      (timedPairBandActiveTwoCutoffs F Kpair Kglobal Δ δ D) z).SupportedOn
      (fun z' ↦ PairTrajectoryInvariant F S₀ z'.2 ∧
        D z'.1.1 ≤ z'.2.available.card) := by
  classical
  unfold FiniteLaw.timedStoppedKernel
  split_ifs with hactive
  · have hstep := greedyKernel_supported_step_of_nonempty F z.2
      hactive.2.1.1
    have hdec := hdecrease z.1.1 hactive.1
    refine hstep.map (fun S' ↦
      (FiniteLaw.advanceTime z.1 hactive.1, S')) ?_
    intro S' hS'
    obtain ⟨T, hT, rfl⟩ := hS'
    refine ⟨?_, ?_⟩
    · exact ⟨hz.1.1.step hT,
        (greedyStep_available_subset F z.2 T).trans hz.1.2⟩
    · simp only [FiniteLaw.advanceTime_val]
      have hcard := greedyStep_available_card_le_add_pairEnvelope
        hz.1.1 hactive.2.1.2.1 hactive.2.1.2.2.2.1 hT
      omega
  · exact FiniteLaw.supportedOn_pure _ hz

/-- The stopped law retains its greedy invariant and scheduled availability
floor on every positive-mass outcome. -/
theorem timedPairBandTwoCutoffsProcessLaw_supported_invariant_availability
    {V : Type*} [Fintype V] [DecidableEq V]
    {n : ℕ} {F : ForbiddenFamilyOn V} {Kpair Kglobal Δ δ : ℕ}
    {D : ℕ → ℕ} {S₀ : GreedyStateOn V}
    (hInv₀ : GreedyInvariant F S₀) (hfloor₀ : D 0 ≤ S₀.available.card)
    (hdecrease : ∀ i, i < n → D (i + 1) + (3 * Δ + Kglobal) ≤ D i) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
      (timedPairBandActiveTwoCutoffs F Kpair Kglobal Δ δ D) S₀).SupportedOn
      (fun z ↦ PairTrajectoryInvariant F S₀ z.2 ∧
        D z.1.1 ≤ z.2.available.card) := by
  apply (FiniteLaw.supportedOn_pure
    (fun z : FiniteLaw.TimedState (GreedyStateOn V) n ↦
      PairTrajectoryInvariant F S₀ z.2 ∧ D z.1.1 ≤ z.2.available.card)
    ⟨pairTrajectoryInvariant_initial hInv₀, hfloor₀⟩).evolveKernels
  intro _i z hz
  exact timedPairBandTwoCutoffsKernel_supported_invariant_availability
    hdecrease z hz

/-- Premature stopping while both cutoffs survive is contained in the
simultaneous pair-deviation event. -/
theorem probability_timedPairBandTwoCutoffs_not_horizon_and_cutoffs_le_deviation
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V)
    (qUpper qLower : PairOn V → ℕ → ℝ)
    (Kpair Kglobal Δ δ : ℕ) (D : ℕ → ℕ) (a : ℝ)
    (hInv₀ : GreedyInvariant F S₀)
    (hDpositive : ∀ i, i ≤ n → 0 < D i)
    (hfloor₀ : D 0 ≤ S₀.available.card)
    (hdecrease : ∀ i, i < n → D (i + 1) + (3 * Δ + Kglobal) ≤ D i)
    (hcap : ∀ P : PairOn V, ∀ i, i ≤ n →
      qUpper P i +
          (fixedPairAvailableCountReal S₀ P.1 S₀ - qUpper P 0) + a ≤
        ((Δ + 1 : ℕ) : ℝ))
    (htargetFloor : ∀ P : PairOn V, ∀ i, i ≤ n → PairAlive P.1 S₀ →
      (δ : ℝ) ≤ qLower P i +
          (fixedPairAvailableCountReal S₀ P.1 S₀ - qLower P 0) - a) :
    let active := timedPairBandActiveTwoCutoffs F Kpair Kglobal Δ δ D
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    L.probability (fun z ↦ z.1.1 ≠ n ∧
      HasPairTwoAwayCutoff F Kpair z.2 ∧ HasTwoAwayCutoff F Kglobal z.2) ≤
      L.probability (fun z ↦ ∃ P : PairOn V,
        (PairAlive P.1 z.2 ∧
          a ≤ fixedPairUpperDeviation (qUpper P) S₀ P.1 z.1.1 z.2 -
            fixedPairUpperDeviation (qUpper P) S₀ P.1 0 S₀) ∨
        (PairAlive P.1 z.2 ∧
          a ≤ fixedPairLowerDeviation (qLower P) S₀ P.1 z.1.1 z.2 -
            fixedPairLowerDeviation (qLower P) S₀ P.1 0 S₀)) := by
  classical
  dsimp only
  let active := timedPairBandActiveTwoCutoffs F Kpair Kglobal Δ δ D
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  have hstate : L.SupportedOn (fun z ↦
      PairTrajectoryInvariant F S₀ z.2 ∧
        D z.1.1 ≤ z.2.available.card) :=
    timedPairBandTwoCutoffsProcessLaw_supported_invariant_availability
      hInv₀ hfloor₀ hdecrease
  have hterminal : L.SupportedOn
      (fun z ↦ z.1.1 = n ∨ ¬ active z.1.1 z.2) :=
    FiniteLaw.timedStoppedProcessLaw_supported_terminal n
      (fun _ ↦ greedyKernel F) active S₀
  have hsupport : L.SupportedOn (fun z ↦
      (PairTrajectoryInvariant F S₀ z.2 ∧
        D z.1.1 ≤ z.2.available.card) ∧
      (z.1.1 = n ∨ ¬ active z.1.1 z.2)) := by
    intro z hmass
    exact ⟨hstate z hmass, hterminal z hmass⟩
  apply L.probability_mono_of_supported hsupport
  intro z hzSupport hzPremature
  have hnotActive : ¬ active z.1.1 z.2 :=
    hzSupport.2.resolve_left hzPremature.1
  by_contra hnoDeviation
  have htime : z.1.1 ≤ n := by omega
  have havailable : z.2.available.Nonempty := by
    rw [← card_pos]
    exact (hDpositive z.1.1 htime).trans_le hzSupport.1.2
  have hupperDev : ∀ P : PairOn V, PairAlive P.1 z.2 →
      fixedPairUpperDeviation (qUpper P) S₀ P.1 z.1.1 z.2 -
        fixedPairUpperDeviation (qUpper P) S₀ P.1 0 S₀ < a := by
    intro P halive
    exact lt_of_not_ge (fun hbad ↦ hnoDeviation ⟨P, Or.inl ⟨halive, hbad⟩⟩)
  have hlowerDev : ∀ P : PairOn V, PairAlive P.1 z.2 →
      fixedPairLowerDeviation (qLower P) S₀ P.1 z.1.1 z.2 -
        fixedPairLowerDeviation (qLower P) S₀ P.1 0 S₀ < a := by
    intro P halive
    exact lt_of_not_ge (fun hbad ↦ hnoDeviation ⟨P, Or.inr ⟨halive, hbad⟩⟩)
  apply hnotActive
  refine ⟨?_, hzSupport.1.2⟩
  exact pairBandActiveTwoCutoffs_of_deviations_lt qUpper qLower z.1.1
    Kpair Kglobal Δ δ a hzSupport.1.1.2 havailable hzPremature.2.1
    hzPremature.2.2 (fun P ↦ hcap P z.1.1 htime)
    (fun P halive ↦ htargetFloor P z.1.1 htime halive)
    hupperDev hlowerDev

/-- Exponential form of the timed two-cutoff premature-stopping estimate. -/
theorem probability_timedPairBandTwoCutoffs_not_horizon_and_cutoffs_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V)
    (qUpper qLower : PairOn V → ℕ → ℝ)
    (Kpair Kglobal Δ δ JUpper : ℕ) (D : ℕ → ℕ) (theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀) (hδ : 1 ≤ δ)
    (hsmall : 3 + Kpair < δ)
    (hDpositive : ∀ i, i ≤ n → 0 < D i)
    (hfloor₀ : D 0 ≤ S₀.available.card)
    (hdecrease : ∀ i, i < n → D (i + 1) + (3 * Δ + Kglobal) ≤ D i)
    (hcap : ∀ P : PairOn V, ∀ i, i ≤ n →
      qUpper P i +
          (fixedPairAvailableCountReal S₀ P.1 S₀ - qUpper P 0) + a ≤
        ((Δ + 1 : ℕ) : ℝ))
    (htargetFloor : ∀ P : PairOn V, ∀ i, i ≤ n → PairAlive P.1 S₀ →
      (δ : ℝ) ≤ qLower P i +
          (fixedPairAvailableCountReal S₀ P.1 S₀ - qLower P 0) - a)
    (hqUpperLowerBound : ∀ P : PairOn V, ∀ i, i < n →
      -(JUpper : ℝ) ≤ qUpper P (i + 1) - qUpper P i)
    (hqUpperNoninc : ∀ P : PairOn V, ∀ i, i < n →
      qUpper P (i + 1) - qUpper P i ≤ 0)
    (hqLowerDeath : ∀ P : PairOn V, ∀ i, i < n →
      -(δ : ℝ) ≤ qLower P (i + 1) - qLower P i)
    (hqLowerNoninc : ∀ P : PairOn V, ∀ i, i < n →
      qLower P (i + 1) - qLower P i ≤ 0)
    (hqUpperDrift : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S →
      timedPairBandActiveTwoCutoffs F Kpair Kglobal Δ δ D i S →
        PairAlive P.1 S →
        -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (3 * δ - 2 - Δ : ℕ)) ≤
          qUpper P (i + 1) - qUpper P i)
    (hqLowerDrift : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S →
      timedPairBandActiveTwoCutoffs F Kpair Kglobal Δ δ D i S →
        PairAlive P.1 S →
        qLower P (i + 1) - qLower P i ≤
          -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (3 * Δ + Kglobal : ℕ)))
    (hvarianceUpper : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S →
      timedPairBandActiveTwoCutoffs F Kpair Kglobal Δ δ D i S →
        PairAlive P.1 S →
        2 * ((S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (((3 + Kpair : ℕ) : ℝ) *
                ((3 * Δ + Kglobal : ℕ) : ℝ)))) +
            2 * (qUpper P (i + 1) - qUpper P i) ^ 2 ≤ v)
    (hvarianceLower : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S →
      timedPairBandActiveTwoCutoffs F Kpair Kglobal Δ δ D i S →
        PairAlive P.1 S →
        2 * ((S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (((3 + Kpair : ℕ) : ℝ) *
                ((3 * Δ + Kglobal : ℕ) : ℝ)))) +
            2 * (qLower P (i + 1) - qLower P i) ^ 2 ≤ v)
    (htheta : 0 < theta)
    (hthetaUpper : theta * (JUpper : ℝ) ≤ 1)
    (hthetaLower : theta * ((3 + Kpair : ℕ) : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    let active := timedPairBandActiveTwoCutoffs F Kpair Kglobal Δ δ D
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    (L.probability (fun z ↦ z.1.1 ≠ n ∧
      HasPairTwoAwayCutoff F Kpair z.2 ∧ HasTwoAwayCutoff F Kglobal z.2) : ℝ) ≤
      (Fintype.card (PairOn V) : ℝ) *
        (2 * Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v)) := by
  classical
  dsimp only
  let active := timedPairBandActiveTwoCutoffs F Kpair Kglobal Δ δ D
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let bad : FiniteLaw.TimedState (GreedyStateOn V) n → Prop := fun z ↦
    ∃ P : PairOn V,
      (PairAlive P.1 z.2 ∧
        a ≤ fixedPairUpperDeviation (qUpper P) S₀ P.1 z.1.1 z.2 -
          fixedPairUpperDeviation (qUpper P) S₀ P.1 0 S₀) ∨
      (PairAlive P.1 z.2 ∧
        a ≤ fixedPairLowerDeviation (qLower P) S₀ P.1 z.1.1 z.2 -
          fixedPairLowerDeviation (qLower P) S₀ P.1 0 S₀)
  have hbootstrap :=
    probability_timedPairBandTwoCutoffs_not_horizon_and_cutoffs_le_deviation
      n F S₀ qUpper qLower Kpair Kglobal Δ δ D a hInv₀ hDpositive
      hfloor₀ hdecrease hcap htargetFloor
  have hbootstrapReal :
      (L.probability (fun z ↦ z.1.1 ≠ n ∧
        HasPairTwoAwayCutoff F Kpair z.2 ∧ HasTwoAwayCutoff F Kglobal z.2) : ℝ) ≤
        (L.probability bad : ℝ) := by
    exact_mod_cast hbootstrap
  refine hbootstrapReal.trans ?_
  exact probability_timedStoppedGreedy_exists_pair_deviation_ge_le_of_pairCutoff
    n F active S₀ qUpper qLower Δ δ Kpair Kglobal JUpper theta a v hInv₀
    (fun _i _hi _S _hS hactive ↦ hactive.1.1)
    (fun _i _hi _S _hS hactive ↦ hactive.1.2.1)
    (fun _i _hi _S _hS hactive ↦ hactive.1.2.2.1)
    (fun _i _hi _S _hS hactive ↦ hactive.1.2.2.2.1)
    (fun _i _hi _S _hS hactive ↦ hactive.1.2.2.2.2)
    hδ hsmall hqUpperLowerBound hqUpperNoninc hqLowerDeath
    hqLowerNoninc hqUpperDrift hqLowerDrift hvarianceUpper
    hvarianceLower htheta hthetaUpper hthetaLower hv

/-- The stopping clock counts successful insertions in the two-cutoff
process. -/
theorem timedPairBandTwoCutoffsProcessLaw_supported_progress
    {V : Type*} [Fintype V] [DecidableEq V]
    {n : ℕ} {F : ForbiddenFamilyOn V} {Kpair Kglobal Δ δ : ℕ}
    {D : ℕ → ℕ} {S₀ : GreedyStateOn V}
    (hInv₀ : GreedyInvariant F S₀) (hfloor₀ : D 0 ≤ S₀.available.card)
    (hdecrease : ∀ i, i < n → D (i + 1) + (3 * Δ + Kglobal) ≤ D i) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
      (timedPairBandActiveTwoCutoffs F Kpair Kglobal Δ δ D) S₀).SupportedOn
      (fun z ↦ PairTrajectoryInvariant F S₀ z.2 ∧
        D z.1.1 ≤ z.2.available.card ∧
        z.2.chosen.card = S₀.chosen.card + z.1.1) := by
  apply (FiniteLaw.supportedOn_pure
    (fun z : FiniteLaw.TimedState (GreedyStateOn V) n ↦
      PairTrajectoryInvariant F S₀ z.2 ∧
        D z.1.1 ≤ z.2.available.card ∧
        z.2.chosen.card = S₀.chosen.card + z.1.1)
    ⟨pairTrajectoryInvariant_initial hInv₀, hfloor₀, by simp⟩).evolveKernels
  intro _i z hz
  classical
  unfold FiniteLaw.timedStoppedKernel
  split_ifs with hactive
  · have hstep := greedyKernel_supported_step_of_nonempty F z.2
      hactive.2.1.1
    have hdec := hdecrease z.1.1 hactive.1
    refine hstep.map (fun S' ↦
      (FiniteLaw.advanceTime z.1 hactive.1, S')) ?_
    intro S' hS'
    obtain ⟨T, hT, rfl⟩ := hS'
    have hTnot : T ∉ z.2.chosen := (hz.1.1.2.2 T hT).1
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨hz.1.1.step hT,
        (greedyStep_available_subset F z.2 T).trans hz.1.2⟩
    · simp only [FiniteLaw.advanceTime_val]
      have hcard := greedyStep_available_card_le_add_pairEnvelope
        hz.1.1 hactive.2.1.2.1 hactive.2.1.2.2.2.1 hT
      omega
    · rw [greedyStep_chosen_card F z.2 T hTnot, hz.2.2]
      simp only [FiniteLaw.advanceTime_val]
      omega
  · exact FiniteLaw.supportedOn_pure _ hz

end

end Erdos207
