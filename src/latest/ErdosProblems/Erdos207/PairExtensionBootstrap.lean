/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SimultaneousPairExtensionConcentration

/-!
# Bootstrap from pair-extension concentration to process progress

The stopped differential-equation argument must rule out stopping at the
pair-codegree boundary.  Strict upper and lower deviation inequalities imply
the corresponding integral pair-codegree cutoffs.  Combined with the generic
first-passage certificate, this converts the simultaneous concentration bound
into a bound on premature stopping, conditional only on the separately
controlled two-away cutoff.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Active region for the pair-band stopped greedy process. -/
def pairBandActive
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (K Δ δ : ℕ)
    (_i : ℕ) (S : GreedyStateOn V) : Prop :=
  S.available.Nonempty ∧
    HasAvailablePairCutoff Δ S ∧
    HasTwoAwayCutoff F K S ∧
    HasAvailablePairFloor δ S

/-- A strict upper-deviation inequality and a real target cap imply the
integral upper codegree bound for one pair. -/
theorem card_availablePair_le_of_upperDeviation_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {S₀ S : GreedyStateOn V} {P : PairOn V}
    {q : ℕ → ℝ} {i Δ : ℕ} {a : ℝ}
    (hsub : S.available ⊆ S₀.available)
    (hcap : q i +
        (fixedPairAvailableCountReal S₀ P.1 S₀ - q 0) + a ≤
      ((Δ + 1 : ℕ) : ℝ))
    (hdev : fixedPairUpperDeviation q S₀ P.1 i S -
        fixedPairUpperDeviation q S₀ P.1 0 S₀ < a) :
    (availableTrianglesContainingPair S P.1).card ≤ Δ := by
  have hlt : fixedPairAvailableCountReal S₀ P.1 S <
      ((Δ + 1 : ℕ) : ℝ) := by
    simp only [fixedPairUpperDeviation] at hdev
    linarith
  rw [fixedPairAvailableCountReal_eq_current hsub] at hlt
  have hnat : (availableTrianglesContainingPair S P.1).card < Δ + 1 := by
    exact_mod_cast hlt
  omega

/-- A strict lower-deviation inequality and a real target floor imply the
integral lower codegree bound for one pair. -/
theorem card_availablePair_ge_of_lowerDeviation_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {S₀ S : GreedyStateOn V} {P : PairOn V}
    {q : ℕ → ℝ} {i δ : ℕ} {a : ℝ}
    (hsub : S.available ⊆ S₀.available)
    (hfloor : (δ : ℝ) ≤ q i +
        (fixedPairAvailableCountReal S₀ P.1 S₀ - q 0) - a)
    (hdev : fixedPairLowerDeviation q S₀ P.1 i S -
        fixedPairLowerDeviation q S₀ P.1 0 S₀ < a) :
    δ ≤ (availableTrianglesContainingPair S P.1).card := by
  have hlt : (δ : ℝ) < fixedPairAvailableCountReal S₀ P.1 S := by
    simp only [fixedPairLowerDeviation] at hdev
    linarith
  rw [fixedPairAvailableCountReal_eq_current hsub] at hlt
  exact_mod_cast hlt.le

/-- Uniform upper deviations imply the active-region pair cutoff. -/
theorem hasAvailablePairCutoff_of_upperDeviations_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {S₀ S : GreedyStateOn V} (q : PairOn V → ℕ → ℝ)
    (i Δ : ℕ) (a : ℝ) (hsub : S.available ⊆ S₀.available)
    (hcap : ∀ P : PairOn V, q P i +
        (fixedPairAvailableCountReal S₀ P.1 S₀ - q P 0) + a ≤
      ((Δ + 1 : ℕ) : ℝ))
    (hdev : ∀ P : PairOn V,
      PairAlive P.1 S →
      fixedPairUpperDeviation (q P) S₀ P.1 i S -
        fixedPairUpperDeviation (q P) S₀ P.1 0 S₀ < a) :
    HasAvailablePairCutoff Δ S := by
  intro P hP
  by_cases halive : PairAlive P S
  · exact card_availablePair_le_of_upperDeviation_lt hsub
      (hcap ⟨P, hP⟩) (hdev ⟨P, hP⟩ halive)
  · have hempty : availableTrianglesContainingPair S P = ∅ :=
      not_nonempty_iff_eq_empty.mp halive
    simp [hempty]

/-- Uniform lower deviations imply the active-region pair floor. -/
theorem hasAvailablePairFloor_of_lowerDeviations_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {S₀ S : GreedyStateOn V} (q : PairOn V → ℕ → ℝ)
    (i δ : ℕ) (a : ℝ) (hsub : S.available ⊆ S₀.available)
    (hfloor : ∀ P : PairOn V, PairAlive P.1 S₀ →
      (δ : ℝ) ≤ q P i +
        (fixedPairAvailableCountReal S₀ P.1 S₀ - q P 0) - a)
    (hdev : ∀ P : PairOn V,
      PairAlive P.1 S →
      fixedPairLowerDeviation (q P) S₀ P.1 i S -
        fixedPairLowerDeviation (q P) S₀ P.1 0 S₀ < a) :
    HasAvailablePairFloor δ S := by
  intro P hP hnonempty
  exact card_availablePair_ge_of_lowerDeviation_lt hsub
    (hfloor ⟨P, hP⟩ (PairAlive.of_available_subset hsub hnonempty))
    (hdev ⟨P, hP⟩ hnonempty)

/-- If at least one vertex pair exists and its lower envelope remains
positive, the uniform lower-deviation event also guarantees that some
triangle is available. -/
theorem available_nonempty_of_lowerDeviations_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {S₀ S : GreedyStateOn V} (P₀ : PairOn V)
    (q : PairOn V → ℕ → ℝ) (i δ : ℕ) (a : ℝ)
    (hδ : 1 ≤ δ) (hsub : S.available ⊆ S₀.available)
    (hfloor : ∀ P : PairOn V, (δ : ℝ) ≤ q P i +
        (fixedPairAvailableCountReal S₀ P.1 S₀ - q P 0) - a)
    (hdev : ∀ P : PairOn V,
      fixedPairLowerDeviation (q P) S₀ P.1 i S -
        fixedPairLowerDeviation (q P) S₀ P.1 0 S₀ < a) :
    S.available.Nonempty := by
  have hlower := card_availablePair_ge_of_lowerDeviation_lt hsub
    (hfloor P₀) (hdev P₀)
  have hcard : 0 < (availableTrianglesContainingPair S P₀.1).card := by
    omega
  obtain ⟨T, hT⟩ := card_pos.mp hcard
  exact ⟨T, (mem_availableTrianglesContainingPair_iff.mp hT).1⟩

/-- Pair deviations below their windows, together with the independently
supplied two-away cutoff, put the state back inside the full active region. -/
theorem pairBandActive_of_deviations_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    (qUpper qLower : PairOn V → ℕ → ℝ)
    (i K Δ δ : ℕ) (a : ℝ)
    (hsub : S.available ⊆ S₀.available)
    (havailable : S.available.Nonempty)
    (htwo : HasTwoAwayCutoff F K S)
    (hcap : ∀ P : PairOn V, qUpper P i +
        (fixedPairAvailableCountReal S₀ P.1 S₀ - qUpper P 0) + a ≤
      ((Δ + 1 : ℕ) : ℝ))
    (hfloor : ∀ P : PairOn V, PairAlive P.1 S₀ →
      (δ : ℝ) ≤ qLower P i +
        (fixedPairAvailableCountReal S₀ P.1 S₀ - qLower P 0) - a)
    (hupperDev : ∀ P : PairOn V,
      PairAlive P.1 S →
      fixedPairUpperDeviation (qUpper P) S₀ P.1 i S -
        fixedPairUpperDeviation (qUpper P) S₀ P.1 0 S₀ < a)
    (hlowerDev : ∀ P : PairOn V,
      PairAlive P.1 S →
      fixedPairLowerDeviation (qLower P) S₀ P.1 i S -
        fixedPairLowerDeviation (qLower P) S₀ P.1 0 S₀ < a) :
    pairBandActive F K Δ δ i S := by
  exact ⟨havailable,
    hasAvailablePairCutoff_of_upperDeviations_lt qUpper i Δ a
      hsub hcap hupperDev,
    htwo,
    hasAvailablePairFloor_of_lowerDeviations_lt qLower i δ a
      hsub hfloor hlowerDev⟩

/-- On terminal support, premature stopping while the two-away cutoff still
holds can only occur if at least one pair has crossed one of its two
deviation windows. -/
theorem probability_pairBand_not_horizon_and_twoAway_le_deviation
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V)
    (qUpper qLower : PairOn V → ℕ → ℝ)
    (K Δ δ : ℕ) (a : ℝ)
    (hInv₀ : GreedyInvariant F S₀)
    (hcap : ∀ P : PairOn V, ∀ i, i ≤ n →
      qUpper P i +
          (fixedPairAvailableCountReal S₀ P.1 S₀ - qUpper P 0) + a ≤
        ((Δ + 1 : ℕ) : ℝ))
    (hfloor : ∀ P : PairOn V, ∀ i, i ≤ n → PairAlive P.1 S₀ →
      (δ : ℝ) ≤ qLower P i +
          (fixedPairAvailableCountReal S₀ P.1 S₀ - qLower P 0) - a) :
    let active := pairBandActive F K Δ δ
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    L.probability (fun z ↦ z.1.1 ≠ n ∧
      HasTwoAwayCutoff F K z.2 ∧ z.2.available.Nonempty) ≤
      L.probability (fun z ↦ ∃ P : PairOn V,
        (PairAlive P.1 z.2 ∧
          a ≤ fixedPairUpperDeviation (qUpper P) S₀ P.1 z.1.1 z.2 -
            fixedPairUpperDeviation (qUpper P) S₀ P.1 0 S₀) ∨
        (PairAlive P.1 z.2 ∧
          a ≤ fixedPairLowerDeviation (qLower P) S₀ P.1 z.1.1 z.2 -
            fixedPairLowerDeviation (qLower P) S₀ P.1 0 S₀)) := by
  classical
  dsimp only
  let active := pairBandActive F K Δ δ
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  have hinv : L.SupportedOn
      (fun z ↦ PairTrajectoryInvariant F S₀ z.2) := by
    exact FiniteLaw.timedStoppedProcessLaw_supported n
      (fun _ ↦ greedyKernel F) active S₀
      (pairTrajectoryInvariant_initial hInv₀)
      (fun _i _hi S hS ↦ greedyKernel_supported_pairTrajectoryInvariant hS)
  have hterminal : L.SupportedOn
      (fun z ↦ z.1.1 = n ∨ ¬ active z.1.1 z.2) := by
    exact FiniteLaw.timedStoppedProcessLaw_supported_terminal n
      (fun _ ↦ greedyKernel F) active S₀
  have hsupport : L.SupportedOn (fun z ↦
      PairTrajectoryInvariant F S₀ z.2 ∧
        (z.1.1 = n ∨ ¬ active z.1.1 z.2)) := by
    intro z hmass
    exact ⟨hinv z hmass, hterminal z hmass⟩
  apply L.probability_mono_of_supported hsupport
  intro z hzSupport hzPremature
  have hzInv := hzSupport.1
  have hnotActive : ¬ active z.1.1 z.2 :=
    hzSupport.2.resolve_left hzPremature.1
  by_contra hnoDeviation
  have htime : z.1.1 ≤ n := by omega
  have hupperDev : ∀ P : PairOn V,
      PairAlive P.1 z.2 →
      fixedPairUpperDeviation (qUpper P) S₀ P.1 z.1.1 z.2 -
        fixedPairUpperDeviation (qUpper P) S₀ P.1 0 S₀ < a := by
    intro P halive
    exact lt_of_not_ge (fun hbad ↦ hnoDeviation ⟨P, Or.inl ⟨halive, hbad⟩⟩)
  have hlowerDev : ∀ P : PairOn V,
      PairAlive P.1 z.2 →
      fixedPairLowerDeviation (qLower P) S₀ P.1 z.1.1 z.2 -
        fixedPairLowerDeviation (qLower P) S₀ P.1 0 S₀ < a := by
    intro P halive
    exact lt_of_not_ge (fun hbad ↦ hnoDeviation ⟨P, Or.inr ⟨halive, hbad⟩⟩)
  apply hnotActive
  exact pairBandActive_of_deviations_lt qUpper qLower z.1.1
    K Δ δ a hzInv.2 hzPremature.2.2 hzPremature.2.1
    (fun P ↦ hcap P z.1.1 htime)
    (fun P halive ↦ hfloor P z.1.1 htime halive) hupperDev hlowerDev

/-- The complete pair-band bootstrap: the probability of stopping before the
horizon while the two-away cutoff remains valid is bounded by the simultaneous
two-sided exponential tail over all vertex pairs. -/
theorem probability_pairBand_not_horizon_and_twoAway_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V)
    (qUpper qLower : PairOn V → ℕ → ℝ)
    (K Δ δ JUpper : ℕ) (theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀) (hδ : 1 ≤ δ)
    (hsmall : 3 + K < δ)
    (hcap : ∀ P : PairOn V, ∀ i, i ≤ n →
      qUpper P i +
          (fixedPairAvailableCountReal S₀ P.1 S₀ - qUpper P 0) + a ≤
        ((Δ + 1 : ℕ) : ℝ))
    (htargetFloor : ∀ P : PairOn V, ∀ i, i ≤ n → PairAlive P.1 S₀ →
      (δ : ℝ) ≤ qLower P i +
          (fixedPairAvailableCountReal S₀ P.1 S₀ - qLower P 0) - a)
    (hqUpperLowerBound : ∀ P : PairOn V, ∀ i, i < n →
      -(JUpper : ℝ) ≤
        qUpper P (i + 1) - qUpper P i)
    (hqUpperNoninc : ∀ P : PairOn V, ∀ i, i < n →
      qUpper P (i + 1) - qUpper P i ≤ 0)
    (hqLowerDeath : ∀ P : PairOn V, ∀ i, i < n →
      -(δ : ℝ) ≤
        qLower P (i + 1) - qLower P i)
    (hqLowerNoninc : ∀ P : PairOn V, ∀ i, i < n →
      qLower P (i + 1) - qLower P i ≤ 0)
    (hqUpperDrift : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → pairBandActive F K Δ δ i S →
        PairAlive P.1 S →
        -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (3 * δ - 2 - Δ : ℕ)) ≤
          qUpper P (i + 1) - qUpper P i)
    (hqLowerDrift : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → pairBandActive F K Δ δ i S →
        PairAlive P.1 S →
        qLower P (i + 1) - qLower P i ≤
          -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (3 * Δ + K : ℕ)))
    (hvarianceUpper : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → pairBandActive F K Δ δ i S →
        PairAlive P.1 S →
        2 * ((S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (((3 + K : ℕ) : ℝ) * ((3 * Δ + K : ℕ) : ℝ)))) +
            2 * (qUpper P (i + 1) - qUpper P i) ^ 2 ≤ v)
    (hvarianceLower : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S → pairBandActive F K Δ δ i S →
        PairAlive P.1 S →
        2 * ((S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (((3 + K : ℕ) : ℝ) * ((3 * Δ + K : ℕ) : ℝ)))) +
            2 * (qLower P (i + 1) - qLower P i) ^ 2 ≤ v)
    (htheta : 0 < theta)
    (hthetaUpper : theta * (JUpper : ℝ) ≤ 1)
    (hthetaLower : theta * ((3 + K : ℕ) : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    let active := pairBandActive F K Δ δ
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    (L.probability (fun z ↦ z.1.1 ≠ n ∧
      HasTwoAwayCutoff F K z.2 ∧ z.2.available.Nonempty) : ℝ) ≤
      (Fintype.card (PairOn V) : ℝ) *
        (2 * Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v)) := by
  classical
  dsimp only
  let active := pairBandActive F K Δ δ
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
  have hbootstrap := probability_pairBand_not_horizon_and_twoAway_le_deviation
    n F S₀ qUpper qLower K Δ δ a hInv₀ hcap htargetFloor
  have hbootstrapReal :
      (L.probability
        (fun z ↦ z.1.1 ≠ n ∧ HasTwoAwayCutoff F K z.2 ∧
          z.2.available.Nonempty) : ℝ) ≤
        (L.probability bad : ℝ) := by
    exact_mod_cast hbootstrap
  refine hbootstrapReal.trans ?_
  exact probability_timedStoppedGreedy_exists_pair_deviation_ge_le_of_pairCutoff
    n F active S₀ qUpper qLower Δ δ K K JUpper theta a v hInv₀
    (fun _i _hi _S _hS hactive ↦ hactive.1)
    (fun _i _hi _S _hS hactive ↦ hactive.2.1)
    (fun _i _hi _S _hS hactive ↦ hactive.2.2.1.hasPairTwoAwayCutoff)
    (fun _i _hi _S _hS hactive ↦ hactive.2.2.1)
    (fun _i _hi _S _hS hactive ↦ hactive.2.2.2)
    hδ hsmall hqUpperLowerBound hqUpperNoninc hqLowerDeath
    hqLowerNoninc hqUpperDrift hqLowerDrift hvarianceUpper
    hvarianceLower htheta hthetaUpper hthetaLower hv

/-- Active region with separate pair-local and global two-away cutoffs. -/
def pairBandActiveTwoCutoffs
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Kpair Kglobal Δ δ : ℕ)
    (_i : ℕ) (S : GreedyStateOn V) : Prop :=
  S.available.Nonempty ∧
    HasAvailablePairCutoff Δ S ∧
    HasPairTwoAwayCutoff F Kpair S ∧
    HasTwoAwayCutoff F Kglobal S ∧
    HasAvailablePairFloor δ S

/-- Pair deviations below their windows, together with both two-away
cutoffs, put a state back inside the two-cutoff active region. -/
theorem pairBandActiveTwoCutoffs_of_deviations_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    (qUpper qLower : PairOn V → ℕ → ℝ)
    (i Kpair Kglobal Δ δ : ℕ) (a : ℝ)
    (hsub : S.available ⊆ S₀.available)
    (havailable : S.available.Nonempty)
    (hpairTwo : HasPairTwoAwayCutoff F Kpair S)
    (htwo : HasTwoAwayCutoff F Kglobal S)
    (hcap : ∀ P : PairOn V, qUpper P i +
        (fixedPairAvailableCountReal S₀ P.1 S₀ - qUpper P 0) + a ≤
      ((Δ + 1 : ℕ) : ℝ))
    (hfloor : ∀ P : PairOn V, PairAlive P.1 S₀ →
      (δ : ℝ) ≤ qLower P i +
        (fixedPairAvailableCountReal S₀ P.1 S₀ - qLower P 0) - a)
    (hupperDev : ∀ P : PairOn V,
      PairAlive P.1 S →
      fixedPairUpperDeviation (qUpper P) S₀ P.1 i S -
        fixedPairUpperDeviation (qUpper P) S₀ P.1 0 S₀ < a)
    (hlowerDev : ∀ P : PairOn V,
      PairAlive P.1 S →
      fixedPairLowerDeviation (qLower P) S₀ P.1 i S -
        fixedPairLowerDeviation (qLower P) S₀ P.1 0 S₀ < a) :
    pairBandActiveTwoCutoffs F Kpair Kglobal Δ δ i S := by
  exact ⟨havailable,
    hasAvailablePairCutoff_of_upperDeviations_lt qUpper i Δ a
      hsub hcap hupperDev,
    hpairTwo, htwo,
    hasAvailablePairFloor_of_lowerDeviations_lt qLower i δ a
      hsub hfloor hlowerDev⟩

/-- On terminal support for the two-cutoff process, a premature stop while
both cutoffs still hold can only be caused by a pair deviation. -/
theorem probability_pairBandTwoCutoffs_not_horizon_and_cutoffs_le_deviation
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V)
    (qUpper qLower : PairOn V → ℕ → ℝ)
    (Kpair Kglobal Δ δ : ℕ) (a : ℝ)
    (hInv₀ : GreedyInvariant F S₀)
    (hcap : ∀ P : PairOn V, ∀ i, i ≤ n →
      qUpper P i +
          (fixedPairAvailableCountReal S₀ P.1 S₀ - qUpper P 0) + a ≤
        ((Δ + 1 : ℕ) : ℝ))
    (hfloor : ∀ P : PairOn V, ∀ i, i ≤ n → PairAlive P.1 S₀ →
      (δ : ℝ) ≤ qLower P i +
          (fixedPairAvailableCountReal S₀ P.1 S₀ - qLower P 0) - a) :
    let active := pairBandActiveTwoCutoffs F Kpair Kglobal Δ δ
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    L.probability (fun z ↦ z.1.1 ≠ n ∧
      HasPairTwoAwayCutoff F Kpair z.2 ∧
      HasTwoAwayCutoff F Kglobal z.2 ∧ z.2.available.Nonempty) ≤
      L.probability (fun z ↦ ∃ P : PairOn V,
        (PairAlive P.1 z.2 ∧
          a ≤ fixedPairUpperDeviation (qUpper P) S₀ P.1 z.1.1 z.2 -
            fixedPairUpperDeviation (qUpper P) S₀ P.1 0 S₀) ∨
        (PairAlive P.1 z.2 ∧
          a ≤ fixedPairLowerDeviation (qLower P) S₀ P.1 z.1.1 z.2 -
            fixedPairLowerDeviation (qLower P) S₀ P.1 0 S₀)) := by
  classical
  dsimp only
  let active := pairBandActiveTwoCutoffs F Kpair Kglobal Δ δ
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  have hinv : L.SupportedOn
      (fun z ↦ PairTrajectoryInvariant F S₀ z.2) := by
    exact FiniteLaw.timedStoppedProcessLaw_supported n
      (fun _ ↦ greedyKernel F) active S₀
      (pairTrajectoryInvariant_initial hInv₀)
      (fun _i _hi S hS ↦ greedyKernel_supported_pairTrajectoryInvariant hS)
  have hterminal : L.SupportedOn
      (fun z ↦ z.1.1 = n ∨ ¬ active z.1.1 z.2) := by
    exact FiniteLaw.timedStoppedProcessLaw_supported_terminal n
      (fun _ ↦ greedyKernel F) active S₀
  have hsupport : L.SupportedOn (fun z ↦
      PairTrajectoryInvariant F S₀ z.2 ∧
        (z.1.1 = n ∨ ¬ active z.1.1 z.2)) := by
    intro z hmass
    exact ⟨hinv z hmass, hterminal z hmass⟩
  apply L.probability_mono_of_supported hsupport
  intro z hzSupport hzPremature
  have hzInv := hzSupport.1
  have hnotActive : ¬ active z.1.1 z.2 :=
    hzSupport.2.resolve_left hzPremature.1
  by_contra hnoDeviation
  have htime : z.1.1 ≤ n := by omega
  have hupperDev : ∀ P : PairOn V,
      PairAlive P.1 z.2 →
      fixedPairUpperDeviation (qUpper P) S₀ P.1 z.1.1 z.2 -
        fixedPairUpperDeviation (qUpper P) S₀ P.1 0 S₀ < a := by
    intro P halive
    exact lt_of_not_ge (fun hbad ↦ hnoDeviation ⟨P, Or.inl ⟨halive, hbad⟩⟩)
  have hlowerDev : ∀ P : PairOn V,
      PairAlive P.1 z.2 →
      fixedPairLowerDeviation (qLower P) S₀ P.1 z.1.1 z.2 -
        fixedPairLowerDeviation (qLower P) S₀ P.1 0 S₀ < a := by
    intro P halive
    exact lt_of_not_ge (fun hbad ↦ hnoDeviation ⟨P, Or.inr ⟨halive, hbad⟩⟩)
  apply hnotActive
  exact pairBandActiveTwoCutoffs_of_deviations_lt qUpper qLower z.1.1
    Kpair Kglobal Δ δ a hzInv.2 hzPremature.2.2.2 hzPremature.2.1
    hzPremature.2.2.1 (fun P ↦ hcap P z.1.1 htime)
    (fun P halive ↦ hfloor P z.1.1 htime halive) hupperDev hlowerDev

/-- Complete two-cutoff pair-band bootstrap. -/
theorem probability_pairBandTwoCutoffs_not_horizon_and_cutoffs_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V)
    (qUpper qLower : PairOn V → ℕ → ℝ)
    (Kpair Kglobal Δ δ JUpper : ℕ) (theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀) (hδ : 1 ≤ δ)
    (hsmall : 3 + Kpair < δ)
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
        pairBandActiveTwoCutoffs F Kpair Kglobal Δ δ i S →
        PairAlive P.1 S →
        -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (3 * δ - 2 - Δ : ℕ)) ≤
          qUpper P (i + 1) - qUpper P i)
    (hqLowerDrift : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S →
        pairBandActiveTwoCutoffs F Kpair Kglobal Δ δ i S →
        PairAlive P.1 S →
        qLower P (i + 1) - qLower P i ≤
          -(S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (3 * Δ + Kglobal : ℕ)))
    (hvarianceUpper : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S →
        pairBandActiveTwoCutoffs F Kpair Kglobal Δ δ i S →
        PairAlive P.1 S →
        2 * ((S.available.card : ℝ)⁻¹ *
            (((availableTrianglesContainingPair S P.1).card : ℝ) *
              (((3 + Kpair : ℕ) : ℝ) *
                ((3 * Δ + Kglobal : ℕ) : ℝ)))) +
            2 * (qUpper P (i + 1) - qUpper P i) ^ 2 ≤ v)
    (hvarianceLower : ∀ P : PairOn V, ∀ i, i < n → ∀ S,
      PairTrajectoryInvariant F S₀ S →
        pairBandActiveTwoCutoffs F Kpair Kglobal Δ δ i S →
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
    let active := pairBandActiveTwoCutoffs F Kpair Kglobal Δ δ
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    (L.probability (fun z ↦ z.1.1 ≠ n ∧
      HasPairTwoAwayCutoff F Kpair z.2 ∧
      HasTwoAwayCutoff F Kglobal z.2 ∧ z.2.available.Nonempty) : ℝ) ≤
      (Fintype.card (PairOn V) : ℝ) *
        (2 * Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v)) := by
  classical
  dsimp only
  let active := pairBandActiveTwoCutoffs F Kpair Kglobal Δ δ
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
    probability_pairBandTwoCutoffs_not_horizon_and_cutoffs_le_deviation
      n F S₀ qUpper qLower Kpair Kglobal Δ δ a hInv₀ hcap htargetFloor
  have hbootstrapReal :
      (L.probability (fun z ↦ z.1.1 ≠ n ∧
        HasPairTwoAwayCutoff F Kpair z.2 ∧
        HasTwoAwayCutoff F Kglobal z.2 ∧ z.2.available.Nonempty) : ℝ) ≤
        (L.probability bad : ℝ) := by
    exact_mod_cast hbootstrap
  refine hbootstrapReal.trans ?_
  exact probability_timedStoppedGreedy_exists_pair_deviation_ge_le_of_pairCutoff
    n F active S₀ qUpper qLower Δ δ Kpair Kglobal JUpper theta a v hInv₀
    (fun _i _hi _S _hS hactive ↦ hactive.1)
    (fun _i _hi _S _hS hactive ↦ hactive.2.1)
    (fun _i _hi _S _hS hactive ↦ hactive.2.2.1)
    (fun _i _hi _S _hS hactive ↦ hactive.2.2.2.1)
    (fun _i _hi _S _hS hactive ↦ hactive.2.2.2.2)
    hδ hsmall hqUpperLowerBound hqUpperNoninc hqLowerDeath
    hqLowerNoninc hqUpperDrift hqLowerDrift hvarianceUpper
    hvarianceLower htheta hthetaUpper hthetaLower hv

end

end Erdos207
