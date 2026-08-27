/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LinearPairTrajectories
import ErdosProblems.Erdos207.TimedStoppedPairTwoAway

/-!
# A decreasing availability schedule

One greedy phase uses the deterministic natural-valued floor
`D₀ - i L`, where the one-step loss allowance is `L = 3Δ + K`.  A single
buffer inequality at the horizon supplies positivity, the terminal floor,
the pathwise decrease condition, and the cumulative reciprocal bound needed
by the two-away moment estimate.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

def linearAvailabilitySchedule (D₀ L n i : ℕ) : ℕ :=
  D₀ - min i n * L

@[simp]
theorem linearAvailabilitySchedule_zero (D₀ L n : ℕ) :
    linearAvailabilitySchedule D₀ L n 0 = D₀ := by
  simp [linearAvailabilitySchedule]

theorem linearAvailabilitySchedule_min
    {D₀ L Dmin n i : ℕ}
    (hbuffer : n * L + Dmin ≤ D₀) :
    Dmin ≤ linearAvailabilitySchedule D₀ L n i := by
  have himul : min i n * L ≤ n * L :=
    Nat.mul_le_mul_right L (min_le_right i n)
  unfold linearAvailabilitySchedule
  omega

theorem linearAvailabilitySchedule_pos
    {D₀ L Dmin n i : ℕ}
    (hDmin : 0 < Dmin) (hbuffer : n * L + Dmin ≤ D₀) :
    0 < linearAvailabilitySchedule D₀ L n i :=
  hDmin.trans_le (linearAvailabilitySchedule_min hbuffer)

theorem linearAvailabilitySchedule_decrease
    {D₀ L Dmin n i : ℕ}
    (hbuffer : n * L + Dmin ≤ D₀) (hi : i < n) :
    linearAvailabilitySchedule D₀ L n (i + 1) + L ≤
      linearAvailabilitySchedule D₀ L n i := by
  have hi' : i + 1 ≤ n := by omega
  have himul : (i + 1) * L ≤ n * L := Nat.mul_le_mul_right L hi'
  have hstep : (i + 1) * L = i * L + L := by
    rw [Nat.add_mul]
    simp
  unfold linearAvailabilitySchedule
  rw [min_eq_left hi.le, min_eq_left hi']
  omega

theorem sum_range_linearAvailabilitySchedule_inv_le
    {D₀ L Dmin n : ℕ}
    (hDmin : 0 < Dmin) (hbuffer : n * L + Dmin ≤ D₀) :
    (∑ i ∈ range n,
        (linearAvailabilitySchedule D₀ L n i : ℝ≥0)⁻¹) ≤
      (n : ℝ≥0) * (Dmin : ℝ≥0)⁻¹ := by
  calc
    (∑ i ∈ range n,
        (linearAvailabilitySchedule D₀ L n i : ℝ≥0)⁻¹) ≤
        ∑ _i ∈ range n, (Dmin : ℝ≥0)⁻¹ := by
      apply sum_le_sum
      intro i hi
      have hmin := linearAvailabilitySchedule_min (i := i) hbuffer
      have hDpos : (0 : ℝ≥0) <
          (linearAvailabilitySchedule D₀ L n i : ℝ≥0) := by
        exact_mod_cast hDmin.trans_le hmin
      have hminReal : (Dmin : ℝ≥0) ≤
          (linearAvailabilitySchedule D₀ L n i : ℝ≥0) := by
        exact_mod_cast hmin
      exact (inv_le_inv₀ hDpos (by exact_mod_cast hDmin)).mpr hminReal
    _ = (n : ℝ≥0) * (Dmin : ℝ≥0)⁻¹ := by simp

theorem sum_range_linearAvailabilitySchedule_inv_le_card
    {V : Type*} [Fintype V]
    {D₀ L Dmin n : ℕ}
    (hDmin : 0 < Dmin) (hbuffer : n * L + Dmin ≤ D₀)
    (hratio : (n : ℝ≥0) * (Dmin : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹) :
    (∑ i ∈ range n,
        (linearAvailabilitySchedule D₀ L n i : ℝ≥0)⁻¹) ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹ :=
  (sum_range_linearAvailabilitySchedule_inv_le hDmin hbuffer).trans hratio

/-- The explicit pair-tail theorem with the clipped linear availability
schedule.  Its floor is `Dmin` at and after the horizon, while every active
step has the exact loss allowance `3Δ+K` reserved. -/
theorem probability_linearScheduledPairBand_not_horizon_and_twoAway_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V)
    (K Δ δ JUpper Dmin D₀ : ℕ) (theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀) (hδ : 1 ≤ δ)
    (hsmallPair : 3 + K < δ)
    (hDminPos : 0 < Dmin)
    (hbuffer : n * (3 * Δ + K) + Dmin ≤ D₀)
    (hfloor₀ : D₀ ≤ S₀.available.card)
    (hinitialCap : ∀ P : PairOn V,
      fixedPairAvailableCountReal S₀ P.1 S₀ + a ≤
        ((Δ + 1 : ℕ) : ℝ))
    (hfinalFloor : ∀ P : PairOn V, PairAlive P.1 S₀ →
      (δ : ℝ) + a + (n : ℝ) * pairLowerLinearRate Δ K Dmin ≤
        fixedPairAvailableCountReal S₀ P.1 S₀)
    (hupperJump : pairUpperLinearRate S₀ δ Δ ≤ (JUpper : ℝ))
    (hlowerDeath : pairLowerLinearRate Δ K Dmin ≤ (δ : ℝ))
    (hvarianceUpper :
      linearPairVarianceBudget Δ K Dmin (pairUpperLinearRate S₀ δ Δ) ≤ v)
    (hvarianceLower :
      linearPairVarianceBudget Δ K Dmin
        (pairLowerLinearRate Δ K Dmin) ≤ v)
    (htheta : 0 < theta)
    (hthetaUpper : theta * (JUpper : ℝ) ≤ 1)
    (hthetaLower : theta * ((3 + K : ℕ) : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    let D := linearAvailabilitySchedule D₀ (3 * Δ + K) n
    let active := timedPairBandActive F K Δ δ D
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    (L.probability (fun z ↦ z.1.1 ≠ n ∧ HasTwoAwayCutoff F K z.2) : ℝ) ≤
      (Fintype.card (PairOn V) : ℝ) *
        (2 * Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v)) := by
  dsimp only
  apply probability_timedPairBand_linear_not_horizon_and_twoAway_le_exp
    n F S₀ K Δ δ JUpper Dmin
      (linearAvailabilitySchedule D₀ (3 * Δ + K) n)
      theta a v hInv₀ hδ hsmallPair
  · intro i _hi
    exact linearAvailabilitySchedule_pos hDminPos hbuffer
  · exact hDminPos
  · intro i _hi
    exact linearAvailabilitySchedule_min hbuffer
  · simpa using hfloor₀
  · intro i hi
    exact linearAvailabilitySchedule_decrease hbuffer hi
  · exact hinitialCap
  · exact hfinalFloor
  · exact hupperJump
  · exact hlowerDeath
  · exact hvarianceUpper
  · exact hvarianceLower
  · exact htheta
  · exact hthetaUpper
  · exact hthetaLower
  · exact hv

/-- A complete positive-probability absorber-greedy phase with the explicit
linear pair targets and clipped linear availability schedule. -/
theorem exists_linearScheduledAbsorberGreedy_phase
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M n s K Δ δ JUpper Dmin D₀ : ℕ}
    {H : SimpleGraph V} {X : Finset V} {B A : TripleSystemOn V}
    (S₀ : GreedyStateOn V)
    (hS₀ : S₀ = absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q B) A)
    (theta a v : ℝ)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hδ : 1 ≤ δ) (hsmallPair : 3 + K < δ)
    (hDminPos : 0 < Dmin)
    (hbuffer : n * (3 * Δ + K) + Dmin ≤ D₀)
    (hfloor₀ : D₀ ≤ S₀.available.card)
    (hinitialCap : ∀ P : PairOn V,
      fixedPairAvailableCountReal S₀ P.1 S₀ + a ≤
        ((Δ + 1 : ℕ) : ℝ))
    (hfinalFloor : ∀ P : PairOn V, PairAlive P.1 S₀ →
      (δ : ℝ) + a + (n : ℝ) * pairLowerLinearRate Δ K Dmin ≤
        fixedPairAvailableCountReal S₀ P.1 S₀)
    (hupperJump : pairUpperLinearRate S₀ δ Δ ≤ (JUpper : ℝ))
    (hlowerDeath : pairLowerLinearRate Δ K Dmin ≤ (δ : ℝ))
    (hvarianceUpper :
      linearPairVarianceBudget Δ K Dmin (pairUpperLinearRate S₀ δ Δ) ≤ v)
    (hvarianceLower :
      linearPairVarianceBudget Δ K Dmin
        (pairLowerLinearRate Δ K Dmin) ≤ v)
    (htheta : 0 < theta)
    (hthetaUpper : theta * (JUpper : ℝ) ≤ 1)
    (hthetaLower : theta * ((3 + K : ℕ) : ℝ) ≤ 1)
    (hv : 0 ≤ v)
    (hratio : (n : ℝ≥0) * (Dmin : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hsmall :
      (Fintype.card (PairOn V) : ℝ) *
          (2 * Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v)) +
        (((Fintype.card (TripleOn V) : ℝ≥0) *
          envelopeTwoAwayTail q M s H X B K : ℝ≥0) : ℝ) < 1) :
    ∃ S : GreedyStateOn V,
      AbsorberGreedyInvariant
          (absorberErdosForbiddenConfigurationsOn q B) A S ∧
        HasTwoAwayCutoff
          (absorberErdosForbiddenConfigurationsOn q B) K S ∧
        linearAvailabilitySchedule D₀ (3 * Δ + K) n n ≤
          S.available.card ∧
        S.chosen.card = n := by
  subst S₀
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let D := linearAvailabilitySchedule D₀ (3 * Δ + K) n
  let active := timedPairBandActive F K Δ δ D
  let εpair : ℝ := (Fintype.card (PairOn V) : ℝ) *
    (2 * Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v))
  let εtwoNN : ℝ≥0 := (Fintype.card (TripleOn V) : ℝ≥0) *
    envelopeTwoAwayTail q M s H X B K
  let εtwo : ℝ := (εtwoNN : ℝ)
  have hInvAbs : AbsorberGreedyInvariant F A S₀ := by
    exact absorberGreedyInitialState_invariant F A fun C hC ↦
      absorberErdosForbidden_nonempty hC
  have hpair :
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      (L.probability
        (fun z ↦ z.1.1 ≠ n ∧ HasTwoAwayCutoff F K z.2) : ℝ) ≤ εpair := by
    dsimp only
    simpa only [F, S₀, D, active, εpair] using
      (probability_linearScheduledPairBand_not_horizon_and_twoAway_le_exp
        n F S₀ K Δ δ JUpper Dmin D₀ theta a v hInvAbs.1 hδ hsmallPair
        hDminPos hbuffer hfloor₀ hinitialCap hfinalFloor hupperJump
        hlowerDeath hvarianceUpper hvarianceLower htheta hthetaUpper
        hthetaLower hv)
  have htwoNN :
      (FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀).probability
          (fun z ↦ ¬ HasTwoAwayCutoff F K z.2) ≤ εtwoNN := by
    simpa only [F, S₀, εtwoNN] using
      (timedStoppedAbsorberGreedy_probability_not_twoAwayCutoff_le
        (K := K) (s := s) active hA2 hDminPos
        (fun i S hactive ↦
          (linearAvailabilitySchedule_min (i := i) hbuffer).trans hactive.2)
        hratio)
  have htwo :
      ((FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀).probability
          (fun z ↦ ¬ HasTwoAwayCutoff F K z.2) : ℝ) ≤ εtwo := by
    exact_mod_cast htwoNN
  have hsmall' : εpair + εtwo < 1 := by
    simpa only [εpair, εtwo, εtwoNN] using hsmall
  obtain ⟨S, hSAbs, _hSInv, hScut, hSfloor, hScard⟩ :=
    exists_timedPairBand_full_phase_of_failure_bounds
      n F S₀ K Δ δ D εpair εtwo hInvAbs.1 hInvAbs
      (fun _i _hi _S hS ↦ absorberGreedyKernel_supported hS)
      (by simpa [D] using hfloor₀)
      (fun i hi ↦ by
        simpa only [D] using linearAvailabilitySchedule_decrease hbuffer hi)
      hpair htwo hsmall'
  exact ⟨S, hSAbs, hScut, hSfloor,
    by simpa [S₀, absorberGreedyInitialState] using hScard⟩

/-! ## Separate pair-local and global cutoffs -/

/-- The explicit linear pair-band estimate with distinct local and global
two-away cutoffs.  Only the global cutoff enters the availability schedule.
-/
theorem probability_linearScheduledPairBandTwoCutoffs_not_horizon_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (S₀ : GreedyStateOn V)
    (Kpair Kglobal Δ δ JUpper Dmin D₀ : ℕ) (theta a v : ℝ)
    (hInv₀ : GreedyInvariant F S₀) (hδ : 1 ≤ δ)
    (hsmallPair : 3 + Kpair < δ)
    (hDminPos : 0 < Dmin)
    (hbuffer : n * (3 * Δ + Kglobal) + Dmin ≤ D₀)
    (hfloor₀ : D₀ ≤ S₀.available.card)
    (hinitialCap : ∀ P : PairOn V,
      fixedPairAvailableCountReal S₀ P.1 S₀ + a ≤
        ((Δ + 1 : ℕ) : ℝ))
    (hfinalFloor : ∀ P : PairOn V, PairAlive P.1 S₀ →
      (δ : ℝ) + a +
          (n : ℝ) * pairLowerLinearRate Δ Kglobal Dmin ≤
        fixedPairAvailableCountReal S₀ P.1 S₀)
    (hupperJump : pairUpperLinearRate S₀ δ Δ ≤ (JUpper : ℝ))
    (hlowerDeath : pairLowerLinearRate Δ Kglobal Dmin ≤ (δ : ℝ))
    (hvarianceUpper :
      linearPairVarianceBudgetTwoCutoffs Δ Kpair Kglobal Dmin
        (pairUpperLinearRate S₀ δ Δ) ≤ v)
    (hvarianceLower :
      linearPairVarianceBudgetTwoCutoffs Δ Kpair Kglobal Dmin
        (pairLowerLinearRate Δ Kglobal Dmin) ≤ v)
    (htheta : 0 < theta)
    (hthetaUpper : theta * (JUpper : ℝ) ≤ 1)
    (hthetaLower : theta * ((3 + Kpair : ℕ) : ℝ) ≤ 1)
    (hv : 0 ≤ v) :
    let D := linearAvailabilitySchedule D₀ (3 * Δ + Kglobal) n
    let active := timedPairBandActiveTwoCutoffs
      F Kpair Kglobal Δ δ D
    let L := FiniteLaw.timedStoppedProcessLaw n
      (fun _ ↦ greedyKernel F) active S₀
    (L.probability (fun z ↦ z.1.1 ≠ n ∧
      HasPairTwoAwayCutoff F Kpair z.2 ∧
      HasTwoAwayCutoff F Kglobal z.2) : ℝ) ≤
      (Fintype.card (PairOn V) : ℝ) *
        (2 * Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v)) := by
  dsimp only
  apply probability_timedPairBand_linearTwoCutoffs_not_horizon_and_cutoffs_le_exp
    n F S₀ Kpair Kglobal Δ δ JUpper Dmin
      (linearAvailabilitySchedule D₀ (3 * Δ + Kglobal) n)
      theta a v hInv₀ hδ hsmallPair
  · intro i _hi
    exact linearAvailabilitySchedule_pos hDminPos hbuffer
  · exact hDminPos
  · intro i _hi
    exact linearAvailabilitySchedule_min hbuffer
  · simpa using hfloor₀
  · intro i hi
    exact linearAvailabilitySchedule_decrease hbuffer hi
  · exact hinitialCap
  · exact hfinalFloor
  · exact hupperJump
  · exact hlowerDeath
  · exact hvarianceUpper
  · exact hvarianceLower
  · exact htheta
  · exact hthetaUpper
  · exact hthetaLower
  · exact hv

/-- Positive-probability extraction for the scheduled absorber-greedy phase
with separate pair-local and global cutoffs. -/
theorem exists_linearScheduledAbsorberGreedy_phaseTwoCutoffs_of_supported
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M n sPair sGlobal Kpair Kglobal Δ δ JUpper Dmin D₀ : ℕ}
    {H : SimpleGraph V} {X : Finset V} {B A : TripleSystemOn V}
    (S₀ : GreedyStateOn V)
    (hS₀ : S₀ = absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q B) A)
    (theta a v : ℝ)
    (hA2 : HasAbsorberLocalization q M H X B)
    {Q : GreedyStateOn V → Prop}
    (hQsupport :
      let F := absorberErdosForbiddenConfigurationsOn q B
      let D := linearAvailabilitySchedule D₀ (3 * Δ + Kglobal) n
      let active := timedPairBandActiveTwoCutoffs
        F Kpair Kglobal Δ δ D
      let L := FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀
      L.SupportedOn (fun z ↦ Q z.2))
    (hδ : 1 ≤ δ) (hsmallPair : 3 + Kpair < δ)
    (hDminPos : 0 < Dmin)
    (hbuffer : n * (3 * Δ + Kglobal) + Dmin ≤ D₀)
    (hfloor₀ : D₀ ≤ S₀.available.card)
    (hinitialCap : ∀ P : PairOn V,
      fixedPairAvailableCountReal S₀ P.1 S₀ + a ≤
        ((Δ + 1 : ℕ) : ℝ))
    (hfinalFloor : ∀ P : PairOn V, PairAlive P.1 S₀ →
      (δ : ℝ) + a +
          (n : ℝ) * pairLowerLinearRate Δ Kglobal Dmin ≤
        fixedPairAvailableCountReal S₀ P.1 S₀)
    (hupperJump : pairUpperLinearRate S₀ δ Δ ≤ (JUpper : ℝ))
    (hlowerDeath : pairLowerLinearRate Δ Kglobal Dmin ≤ (δ : ℝ))
    (hvarianceUpper :
      linearPairVarianceBudgetTwoCutoffs Δ Kpair Kglobal Dmin
        (pairUpperLinearRate S₀ δ Δ) ≤ v)
    (hvarianceLower :
      linearPairVarianceBudgetTwoCutoffs Δ Kpair Kglobal Dmin
        (pairLowerLinearRate Δ Kglobal Dmin) ≤ v)
    (htheta : 0 < theta)
    (hthetaUpper : theta * (JUpper : ℝ) ≤ 1)
    (hthetaLower : theta * ((3 + Kpair : ℕ) : ℝ) ≤ 1)
    (hv : 0 ≤ v)
    (hratio : (n : ℝ≥0) * (Dmin : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hsmall :
      (Fintype.card (PairOn V) : ℝ) *
          (2 * Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v)) +
        (((Fintype.card (TripleOn V) : ℝ≥0) *
          (Fintype.card (PairOn V) : ℝ≥0) *
          pairTwoAwayTail q sPair Kpair
            (pairTwoAwayThreatExtensionCoefficient q B : ℕ) : ℝ≥0) : ℝ) +
        (((Fintype.card (TripleOn V) : ℝ≥0) *
          envelopeTwoAwayTail q M sGlobal H X B Kglobal : ℝ≥0) : ℝ) < 1) :
    ∃ S : GreedyStateOn V,
      Q S ∧
        GreedyInvariant (absorberErdosForbiddenConfigurationsOn q B) S ∧
        HasPairTwoAwayCutoff
          (absorberErdosForbiddenConfigurationsOn q B) Kpair S ∧
        HasTwoAwayCutoff
          (absorberErdosForbiddenConfigurationsOn q B) Kglobal S ∧
        linearAvailabilitySchedule D₀ (3 * Δ + Kglobal) n n ≤
          S.available.card ∧
        S.chosen.card = n := by
  subst S₀
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let D := linearAvailabilitySchedule D₀ (3 * Δ + Kglobal) n
  let active := timedPairBandActiveTwoCutoffs F Kpair Kglobal Δ δ D
  let εband : ℝ := (Fintype.card (PairOn V) : ℝ) *
    (2 * Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v))
  let εpairNN : ℝ≥0 := (Fintype.card (TripleOn V) : ℝ≥0) *
    (Fintype.card (PairOn V) : ℝ≥0) *
      pairTwoAwayTail q sPair Kpair
        (pairTwoAwayThreatExtensionCoefficient q B : ℕ)
  let εglobalNN : ℝ≥0 := (Fintype.card (TripleOn V) : ℝ≥0) *
    envelopeTwoAwayTail q M sGlobal H X B Kglobal
  let εpair : ℝ := (εpairNN : ℝ)
  let εglobal : ℝ := (εglobalNN : ℝ)
  have hQsupport' :
      (FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀).SupportedOn
          (fun z ↦ Q z.2) := by
    simpa only [F, S₀, D, active] using hQsupport
  have hInvAbs : AbsorberGreedyInvariant F A S₀ := by
    exact absorberGreedyInitialState_invariant F A fun C hC ↦
      absorberErdosForbidden_nonempty hC
  have hbandReal :
      ((FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀).probability
        (fun z ↦ z.1.1 ≠ n ∧ HasPairTwoAwayCutoff F Kpair z.2 ∧
          HasTwoAwayCutoff F Kglobal z.2) : ℝ) ≤ εband := by
    simpa only [F, S₀, D, active, εband] using
      (probability_linearScheduledPairBandTwoCutoffs_not_horizon_le_exp
        n F S₀ Kpair Kglobal Δ δ JUpper Dmin D₀ theta a v
        hInvAbs.1 hδ hsmallPair hDminPos hbuffer hfloor₀ hinitialCap
        hfinalFloor hupperJump hlowerDeath hvarianceUpper hvarianceLower
        htheta hthetaUpper hthetaLower hv)
  have hpairNN :
      (FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀).probability
        (fun z ↦ ¬ HasPairTwoAwayCutoff F Kpair z.2) ≤ εpairNN := by
    simpa only [F, S₀, εpairNN] using
      (timedStoppedAbsorberGreedy_probability_not_pairTwoAwayCutoff_le_local
        (K := Kpair) (s := sPair) active hDminPos
        (fun i S hactive ↦
          (linearAvailabilitySchedule_min (i := i) hbuffer).trans hactive.2)
        hratio)
  have hglobalNN :
      (FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀).probability
        (fun z ↦ ¬ HasTwoAwayCutoff F Kglobal z.2) ≤ εglobalNN := by
    simpa only [F, S₀, εglobalNN] using
      (timedStoppedAbsorberGreedy_probability_not_twoAwayCutoff_le
        (K := Kglobal) (s := sGlobal) active hA2 hDminPos
        (fun i S hactive ↦
          (linearAvailabilitySchedule_min (i := i) hbuffer).trans hactive.2)
        hratio)
  have hpairReal :
      ((FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀).probability
        (fun z ↦ ¬ HasPairTwoAwayCutoff F Kpair z.2) : ℝ) ≤ εpair := by
    exact_mod_cast hpairNN
  have hglobalReal :
      ((FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀).probability
        (fun z ↦ ¬ HasTwoAwayCutoff F Kglobal z.2) : ℝ) ≤ εglobal := by
    exact_mod_cast hglobalNN
  have hsmall' : εband + εpair + εglobal < 1 := by
    simpa only [εband, εpair, εglobal, εpairNN, εglobalNN] using hsmall
  obtain ⟨S, hSQ, hSInv, hSpair, hSglobal, hSfloor, hScard⟩ :=
    exists_timedPairBandTwoCutoffs_full_phase_of_failure_bounds
      n F S₀ Kpair Kglobal Δ δ D εband εpair εglobal
      hInvAbs.1 hQsupport'
      (by simpa [D] using hfloor₀)
      (fun i hi ↦ by
        simpa only [D] using linearAvailabilitySchedule_decrease hbuffer hi)
      hbandReal hpairReal hglobalReal hsmall'
  exact ⟨S, hSQ, hSInv, hSpair, hSglobal, hSfloor,
    by simpa [S₀, absorberGreedyInitialState] using hScard⟩

/-- Specialization of the supported phase theorem to the full absorber
greedy invariant. -/
theorem exists_linearScheduledAbsorberGreedy_phaseTwoCutoffs
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M n sPair sGlobal Kpair Kglobal Δ δ JUpper Dmin D₀ : ℕ}
    {H : SimpleGraph V} {X : Finset V} {B A : TripleSystemOn V}
    (S₀ : GreedyStateOn V)
    (hS₀ : S₀ = absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q B) A)
    (theta a v : ℝ)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hδ : 1 ≤ δ) (hsmallPair : 3 + Kpair < δ)
    (hDminPos : 0 < Dmin)
    (hbuffer : n * (3 * Δ + Kglobal) + Dmin ≤ D₀)
    (hfloor₀ : D₀ ≤ S₀.available.card)
    (hinitialCap : ∀ P : PairOn V,
      fixedPairAvailableCountReal S₀ P.1 S₀ + a ≤
        ((Δ + 1 : ℕ) : ℝ))
    (hfinalFloor : ∀ P : PairOn V, PairAlive P.1 S₀ →
      (δ : ℝ) + a +
          (n : ℝ) * pairLowerLinearRate Δ Kglobal Dmin ≤
        fixedPairAvailableCountReal S₀ P.1 S₀)
    (hupperJump : pairUpperLinearRate S₀ δ Δ ≤ (JUpper : ℝ))
    (hlowerDeath : pairLowerLinearRate Δ Kglobal Dmin ≤ (δ : ℝ))
    (hvarianceUpper :
      linearPairVarianceBudgetTwoCutoffs Δ Kpair Kglobal Dmin
        (pairUpperLinearRate S₀ δ Δ) ≤ v)
    (hvarianceLower :
      linearPairVarianceBudgetTwoCutoffs Δ Kpair Kglobal Dmin
        (pairLowerLinearRate Δ Kglobal Dmin) ≤ v)
    (htheta : 0 < theta)
    (hthetaUpper : theta * (JUpper : ℝ) ≤ 1)
    (hthetaLower : theta * ((3 + Kpair : ℕ) : ℝ) ≤ 1)
    (hv : 0 ≤ v)
    (hratio : (n : ℝ≥0) * (Dmin : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hsmall :
      (Fintype.card (PairOn V) : ℝ) *
          (2 * Real.exp (-theta * a + theta ^ 2 * (n : ℝ) * v)) +
        (((Fintype.card (TripleOn V) : ℝ≥0) *
          (Fintype.card (PairOn V) : ℝ≥0) *
          pairTwoAwayTail q sPair Kpair
            (pairTwoAwayThreatExtensionCoefficient q B : ℕ) : ℝ≥0) : ℝ) +
        (((Fintype.card (TripleOn V) : ℝ≥0) *
          envelopeTwoAwayTail q M sGlobal H X B Kglobal : ℝ≥0) : ℝ) < 1) :
    ∃ S : GreedyStateOn V,
      AbsorberGreedyInvariant
          (absorberErdosForbiddenConfigurationsOn q B) A S ∧
        HasPairTwoAwayCutoff
          (absorberErdosForbiddenConfigurationsOn q B) Kpair S ∧
        HasTwoAwayCutoff
          (absorberErdosForbiddenConfigurationsOn q B) Kglobal S ∧
        linearAvailabilitySchedule D₀ (3 * Δ + Kglobal) n n ≤
          S.available.card ∧
        S.chosen.card = n := by
  have hInvAbs : AbsorberGreedyInvariant
      (absorberErdosForbiddenConfigurationsOn q B) A S₀ := by
    rw [hS₀]
    exact absorberGreedyInitialState_invariant _ _ fun C hC ↦
      absorberErdosForbidden_nonempty hC
  let F := absorberErdosForbiddenConfigurationsOn q B
  let D := linearAvailabilitySchedule D₀ (3 * Δ + Kglobal) n
  let active := timedPairBandActiveTwoCutoffs
    F Kpair Kglobal Δ δ D
  have hInvSupport :
      (FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀).SupportedOn
          (fun z ↦ AbsorberGreedyInvariant F A z.2) := by
    exact FiniteLaw.timedStoppedProcessLaw_supported n
      (fun _ ↦ greedyKernel F) active S₀ hInvAbs
      (fun _i _hi _S hS ↦ absorberGreedyKernel_supported hS)
  obtain ⟨S, hSAbs, _hSInv, hSpair, hSglobal, hSfloor, hScard⟩ :=
    exists_linearScheduledAbsorberGreedy_phaseTwoCutoffs_of_supported
      S₀ hS₀ theta a v hA2 (by
        simpa only [F, D, active] using hInvSupport)
      hδ hsmallPair hDminPos hbuffer hfloor₀ hinitialCap hfinalFloor
      hupperJump hlowerDeath hvarianceUpper hvarianceLower htheta
      hthetaUpper hthetaLower hv hratio hsmall
  exact ⟨S, hSAbs, hSpair, hSglobal, hSfloor, hScard⟩

end

end Erdos207
