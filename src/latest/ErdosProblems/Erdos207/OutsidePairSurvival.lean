/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialPairAvailability
import ErdosProblems.Erdos207.AlivePairJump
import ErdosProblems.Erdos207.TimedPairBandSuccess
import ErdosProblems.Erdos207.LinearAvailabilitySchedule

/-!
# Survival of uncovered outside pairs

The lower pair band is useful for cover-down only after one records which
pairs it protects.  A pair outside the fixed absorber graph and outside the
flexible square is initially alive once the padded absorber is sufficiently
small.  During a pair-band step, the strict inequality `3 + K < delta`
implies that such a pair can become dead only when the selected triangle
covers it.  Consequently every pair which is still in the leave remains
alive throughout the phase.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Every uncovered pair outside `H` and outside the complete graph on `X`
still has a legal available extension. -/
def OutsideLeavePairsAlive
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (S : GreedyStateOn V) : Prop :=
  ∀ u v : V, ¬ H.Adj u v → ¬ (u ∈ X ∧ v ∈ X) →
    (leaveGraph S.chosen).Adj u v → PairAlive {u, v} S

/-- The supported-loss estimate makes every eligible pair alive in the
initial constrained-greedy state. -/
theorem outsideLeavePairsAlive_initial
    {V : Type*} [Fintype V] [DecidableEq V]
    {q C : Nat} {H : SimpleGraph V} [DecidableRel H.Adj]
    {X : Finset V} {B : TripleSystemOn V}
    (hbank : BankPairsSupported H X B)
    (hdegree : ∀ x, H.degree x ≤ C)
    (hsupport : (verticesOn B).card ≤ C)
    (hlarge : 3 * C + 3 ≤ Fintype.card V) :
    OutsideLeavePairsAlive H X
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outsideAvailableTriangles H B)) := by
  intro u v huvH huvX huvLeave
  have huv : u ≠ v := huvLeave.ne
  have hlocal := card_sub_two_le_initialPairStar_add_three_mul
    (q := q) hbank hdegree hsupport huv huvH
  apply card_pos.mp
  omega

/-- A leave edge after a greedy step was already a leave edge before it. -/
lemma leaveGraph_greedyStep_adj_old
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T : TripleOn V}
    {u v : V}
    (h : (leaveGraph (greedyStep F S T).chosen).Adj u v) :
    (leaveGraph S.chosen).Adj u v := by
  rw [leaveGraph_adj] at h ⊢
  refine ⟨h.1, ?_⟩
  rintro ⟨U, hUS, huU, hvU, huv⟩
  apply h.2
  exact ⟨U, by simpa [greedyStep] using (mem_insert_of_mem hUS),
    huU, hvU, huv⟩

/-- If a pair is left uncovered after selecting `T`, then `T` did not
contain that pair. -/
lemma not_pair_subset_selected_of_leaveGraph_greedyStep
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T : TripleOn V}
    {u v : V}
    (h : (leaveGraph (greedyStep F S T).chosen).Adj u v) :
    ¬ ({u, v} : Finset V) ⊆ T.1 := by
  intro hsub
  have huT : u ∈ T.1 := hsub (by simp)
  have hvT : v ∈ T.1 := hsub (by simp)
  have hchosen : T ∈ (greedyStep F S T).chosen := by
    simp [greedyStep]
  have hcovered : (coveredGraph (greedyStep F S T).chosen).Adj u v :=
    coveredGraph_adj.mpr ⟨T, hchosen, huT, hvT, h.ne⟩
  exact (leaveGraph_adj.mp h).2
    (coveredGraph_adj.mp hcovered)

/-- The outside-pair survival invariant is preserved by every active
pair-band transition. -/
theorem OutsideLeavePairsAlive.greedyStep
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {H : SimpleGraph V} {X : Finset V}
    {S : GreedyStateOn V} {T : TripleOn V} {K delta : ℕ}
    (houtside : OutsideLeavePairsAlive H X S)
    (hS : GreedyInvariant F S) (hT : T ∈ S.available)
    (htwo : HasTwoAwayCutoff F K S)
    (hfloor : HasAvailablePairFloor delta S)
    (hsmall : 3 + K < delta) :
    OutsideLeavePairsAlive H X (Erdos207.greedyStep F S T) := by
  intro u v huvH huvX huvLeave
  have huv : u ≠ v := huvLeave.ne
  have hold : PairAlive ({u, v} : Finset V) S :=
    houtside u v huvH huvX (leaveGraph_greedyStep_adj_old huvLeave)
  have hpairCard : ({u, v} : Finset V).card = 2 := by
    simp [huv]
  have hpairFloor : delta ≤
      (availableTrianglesContainingPair S {u, v}).card :=
    hfloor {u, v} hpairCard hold
  exact pairAlive_greedyStep_of_not_subset_of_floor
    hpairCard hS hT htwo hpairFloor hsmall
      (not_pair_subset_selected_of_leaveGraph_greedyStep huvLeave)

/-- The ordinary greedy kernel preserves outside-pair survival while the
pair floor and two-away cutoff hold. -/
theorem greedyKernel_supported_outsideLeavePairsAlive
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {H : SimpleGraph V} {X : Finset V}
    {S : GreedyStateOn V} {K delta : ℕ}
    (houtside : OutsideLeavePairsAlive H X S)
    (hS : GreedyInvariant F S)
    (htwo : HasTwoAwayCutoff F K S)
    (hfloor : HasAvailablePairFloor delta S)
    (hsmall : 3 + K < delta) :
    (greedyKernel F S).SupportedOn (OutsideLeavePairsAlive H X) := by
  intro S' hmass
  rcases greedyKernel_supported_step_or_self F S S' hmass with
    rfl | ⟨T, hT, rfl⟩
  · exact houtside
  · exact houtside.greedyStep hS hT htwo hfloor hsmall

/-- The timed pair-band law preserves outside-pair survival.  In the active
branch the strict pair floor supplies the deterministic step lemma; in the
stopped branch the state is unchanged. -/
theorem timedPairBandProcessLaw_supported_outsideLeavePairsAlive
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (H : SimpleGraph V) (X : Finset V)
    (S₀ : GreedyStateOn V) (K Delta delta : ℕ) (D : ℕ → ℕ)
    (hInv₀ : GreedyInvariant F S₀)
    (houtside₀ : OutsideLeavePairsAlive H X S₀)
    (hsmall : 3 + K < delta) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
      (timedPairBandActive F K Delta delta D) S₀).SupportedOn
        (fun z ↦ OutsideLeavePairsAlive H X z.2) := by
  let z₀ : FiniteLaw.TimedState (GreedyStateOn V) n :=
    (⟨0, by omega⟩, S₀)
  have hsupport :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedPairBandActive F K Delta delta D) S₀).SupportedOn
          (fun z ↦ GreedyInvariant F z.2 ∧
            OutsideLeavePairsAlive H X z.2) := by
    apply (FiniteLaw.supportedOn_pure
    (fun z : FiniteLaw.TimedState (GreedyStateOn V) n ↦
      GreedyInvariant F z.2 ∧ OutsideLeavePairsAlive H X z.2)
      ⟨hInv₀, houtside₀⟩).evolveKernels
    intro _i z hz
    classical
    unfold FiniteLaw.timedStoppedKernel
    split_ifs with hactive
    · have hout := greedyKernel_supported_outsideLeavePairsAlive
        hz.2 hz.1 hactive.2.1.2.2.1 hactive.2.1.2.2.2 hsmall
      have hboth : (greedyKernel F z.2).SupportedOn
          (fun S' ↦ GreedyInvariant F S' ∧
            OutsideLeavePairsAlive H X S') := by
        intro S' hmass
        exact ⟨greedyKernel_supported hz.1 S' hmass, hout S' hmass⟩
      exact hboth.map
        (fun S' ↦ (FiniteLaw.advanceTime z.1 hactive.1, S'))
        (fun _S' hS' ↦ hS')
    · exact FiniteLaw.supportedOn_pure _ hz
  intro z hmass
  exact (hsupport z hmass).2

/-! ## Separate pair-local and global cutoffs -/

/-- Pair-local cutoff version of outside-pair survival for one greedy step. -/
theorem OutsideLeavePairsAlive.greedyStep_of_pairCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {H : SimpleGraph V} {X : Finset V}
    {S : GreedyStateOn V} {T : TripleOn V} {Kpair delta : ℕ}
    (houtside : OutsideLeavePairsAlive H X S)
    (hS : GreedyInvariant F S) (hT : T ∈ S.available)
    (htwo : HasPairTwoAwayCutoff F Kpair S)
    (hfloor : HasAvailablePairFloor delta S)
    (hsmall : 3 + Kpair < delta) :
    OutsideLeavePairsAlive H X (Erdos207.greedyStep F S T) := by
  intro u v huvH huvX huvLeave
  have huv : u ≠ v := huvLeave.ne
  have hold : PairAlive ({u, v} : Finset V) S :=
    houtside u v huvH huvX (leaveGraph_greedyStep_adj_old huvLeave)
  have hpairCard : ({u, v} : Finset V).card = 2 := by simp [huv]
  have hpairFloor : delta ≤
      (availableTrianglesContainingPair S {u, v}).card :=
    hfloor {u, v} hpairCard hold
  exact pairAlive_greedyStep_of_not_subset_of_floor_of_pairCutoff
    hpairCard hS hT htwo hpairFloor hsmall
      (not_pair_subset_selected_of_leaveGraph_greedyStep huvLeave)

theorem greedyKernel_supported_outsideLeavePairsAlive_of_pairCutoff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {H : SimpleGraph V} {X : Finset V}
    {S : GreedyStateOn V} {Kpair delta : ℕ}
    (houtside : OutsideLeavePairsAlive H X S)
    (hS : GreedyInvariant F S)
    (htwo : HasPairTwoAwayCutoff F Kpair S)
    (hfloor : HasAvailablePairFloor delta S)
    (hsmall : 3 + Kpair < delta) :
    (greedyKernel F S).SupportedOn (OutsideLeavePairsAlive H X) := by
  intro S' hmass
  rcases greedyKernel_supported_step_or_self F S S' hmass with
    rfl | ⟨T, hT, rfl⟩
  · exact houtside
  · exact houtside.greedyStep_of_pairCutoff hS hT htwo hfloor hsmall

/-- The two-cutoff timed law preserves all outside leave pairs. -/
theorem timedPairBandTwoCutoffsProcessLaw_supported_outsideLeavePairsAlive
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (H : SimpleGraph V) (X : Finset V)
    (S₀ : GreedyStateOn V) (Kpair Kglobal Delta delta : ℕ)
    (D : ℕ → ℕ)
    (hInv₀ : GreedyInvariant F S₀)
    (houtside₀ : OutsideLeavePairsAlive H X S₀)
    (hsmall : 3 + Kpair < delta) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
      (timedPairBandActiveTwoCutoffs F Kpair Kglobal Delta delta D) S₀).SupportedOn
        (fun z ↦ OutsideLeavePairsAlive H X z.2) := by
  have hsupport :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedPairBandActiveTwoCutoffs F Kpair Kglobal Delta delta D) S₀).SupportedOn
          (fun z ↦ GreedyInvariant F z.2 ∧
            OutsideLeavePairsAlive H X z.2) := by
    apply (FiniteLaw.supportedOn_pure
      (fun z : FiniteLaw.TimedState (GreedyStateOn V) n ↦
        GreedyInvariant F z.2 ∧ OutsideLeavePairsAlive H X z.2)
        ⟨hInv₀, houtside₀⟩).evolveKernels
    intro _i z hz
    classical
    unfold FiniteLaw.timedStoppedKernel
    split_ifs with hactive
    · have hout := greedyKernel_supported_outsideLeavePairsAlive_of_pairCutoff
        hz.2 hz.1 hactive.2.1.2.2.1 hactive.2.1.2.2.2.2 hsmall
      have hboth : (greedyKernel F z.2).SupportedOn
          (fun S' ↦ GreedyInvariant F S' ∧ OutsideLeavePairsAlive H X S') := by
        intro S' hmass
        exact ⟨greedyKernel_supported hz.1 S' hmass, hout S' hmass⟩
      exact hboth.map
        (fun S' ↦ (FiniteLaw.advanceTime z.1 hactive.1, S'))
        (fun _S' hS' ↦ hS')
    · exact FiniteLaw.supportedOn_pure _ hz
  intro z hmass
  exact (hsupport z hmass).2

/-- The explicit scheduled absorber phase, strengthened with the statement
that every surviving outside leave pair still has a legal extension.  The
positive-mass timed witness is shared by all four support conclusions. -/
theorem exists_linearScheduledAbsorberGreedy_phase_with_outsidePairSurvival
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M n s K Delta delta JUpper Dmin D₀ C : ℕ}
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {X : Finset V} {B A : TripleSystemOn V}
    (S₀ : GreedyStateOn V)
    (hS₀ : S₀ = absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q B) A)
    (hA : A = outsideAvailableTriangles H B)
    (theta a variance : ℝ)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hbank : BankPairsSupported H X B)
    (hdegree : ∀ x, H.degree x ≤ C)
    (hsupport : (verticesOn B).card ≤ C)
    (hlarge : 3 * C + 3 ≤ Fintype.card V)
    (hdelta : 1 ≤ delta) (hsmallPair : 3 + K < delta)
    (hDminPos : 0 < Dmin)
    (hbuffer : n * (3 * Delta + K) + Dmin ≤ D₀)
    (hfloor₀ : D₀ ≤ S₀.available.card)
    (hinitialCap : ∀ P : PairOn V,
      fixedPairAvailableCountReal S₀ P.1 S₀ + a ≤
        ((Delta + 1 : ℕ) : ℝ))
    (hfinalFloor : ∀ P : PairOn V, PairAlive P.1 S₀ →
      (delta : ℝ) + a +
          (n : ℝ) * pairLowerLinearRate Delta K Dmin ≤
        fixedPairAvailableCountReal S₀ P.1 S₀)
    (hupperJump : pairUpperLinearRate S₀ delta Delta ≤ (JUpper : ℝ))
    (hlowerDeath : pairLowerLinearRate Delta K Dmin ≤ (delta : ℝ))
    (hvarianceUpper :
      linearPairVarianceBudget Delta K Dmin
        (pairUpperLinearRate S₀ delta Delta) ≤ variance)
    (hvarianceLower :
      linearPairVarianceBudget Delta K Dmin
        (pairLowerLinearRate Delta K Dmin) ≤ variance)
    (htheta : 0 < theta)
    (hthetaUpper : theta * (JUpper : ℝ) ≤ 1)
    (hthetaLower : theta * ((3 + K : ℕ) : ℝ) ≤ 1)
    (hvariance : 0 ≤ variance)
    (hratio : (n : ℝ≥0) * (Dmin : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hsmall :
      (Fintype.card (PairOn V) : ℝ) *
          (2 * Real.exp
            (-theta * a + theta ^ 2 * (n : ℝ) * variance)) +
        (((Fintype.card (TripleOn V) : ℝ≥0) *
          envelopeTwoAwayTail q M s H X B K : ℝ≥0) : ℝ) < 1) :
    ∃ S : GreedyStateOn V,
      AbsorberGreedyInvariant
          (absorberErdosForbiddenConfigurationsOn q B) A S ∧
        OutsideLeavePairsAlive H X S ∧
        HasTwoAwayCutoff
          (absorberErdosForbiddenConfigurationsOn q B) K S ∧
        linearAvailabilitySchedule D₀ (3 * Delta + K) n n ≤
          S.available.card ∧
        S.chosen.card = n := by
  subst S₀
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let D := linearAvailabilitySchedule D₀ (3 * Delta + K) n
  let active := timedPairBandActive F K Delta delta D
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let epsilonPair : ℝ := (Fintype.card (PairOn V) : ℝ) *
    (2 * Real.exp
      (-theta * a + theta ^ 2 * (n : ℝ) * variance))
  let epsilonTwoNN : ℝ≥0 := (Fintype.card (TripleOn V) : ℝ≥0) *
    envelopeTwoAwayTail q M s H X B K
  let epsilonTwo : ℝ := (epsilonTwoNN : ℝ)
  have hInvAbs : AbsorberGreedyInvariant F A S₀ := by
    exact absorberGreedyInitialState_invariant F A fun E hE ↦
      absorberErdosForbidden_nonempty hE
  have hpair :
      (L.probability
        (fun z ↦ z.1.1 ≠ n ∧ HasTwoAwayCutoff F K z.2) : ℝ) ≤
        epsilonPair := by
    simpa only [L, F, S₀, D, active, epsilonPair] using
      (probability_linearScheduledPairBand_not_horizon_and_twoAway_le_exp
        n F S₀ K Delta delta JUpper Dmin D₀ theta a variance
        hInvAbs.1 hdelta hsmallPair hDminPos hbuffer hfloor₀ hinitialCap
        hfinalFloor hupperJump hlowerDeath hvarianceUpper hvarianceLower
        htheta hthetaUpper hthetaLower hvariance)
  have htwoNN : L.probability
      (fun z ↦ ¬ HasTwoAwayCutoff F K z.2) ≤ epsilonTwoNN := by
    simpa only [L, F, S₀, D, active, epsilonTwoNN] using
      (timedStoppedAbsorberGreedy_probability_not_twoAwayCutoff_le
        (K := K) (s := s) active hA2 hDminPos
        (fun i S hactive ↦
          (linearAvailabilitySchedule_min (i := i) hbuffer).trans
            hactive.2)
        hratio)
  have htwo : (L.probability
      (fun z ↦ ¬ HasTwoAwayCutoff F K z.2) : ℝ) ≤ epsilonTwo := by
    exact_mod_cast htwoNN
  have hsmall' : epsilonPair + epsilonTwo < 1 := by
    simpa only [epsilonPair, epsilonTwo, epsilonTwoNN] using hsmall
  obtain ⟨z, hztime, hzcut, hzmass⟩ :=
    exists_timedPairBand_success_with_mass_of_failure_bounds
      n F S₀ K Delta delta D epsilonPair epsilonTwo hpair htwo hsmall'
  have hprogress := timedPairBandProcessLaw_supported_progress
    hInvAbs.1 (by simpa [D] using hfloor₀)
      (fun i hi ↦ by
        simpa only [D] using linearAvailabilitySchedule_decrease hbuffer hi)
      z hzmass
  have houtside₀ : OutsideLeavePairsAlive H X S₀ := by
    change OutsideLeavePairsAlive H X
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A)
    rw [hA]
    exact
      (outsideLeavePairsAlive_initial (q := q) hbank hdegree hsupport hlarge)
  have houtsideSupport :=
    timedPairBandProcessLaw_supported_outsideLeavePairsAlive
      n F H X S₀ K Delta delta D hInvAbs.1 houtside₀ hsmallPair
  have hAbsSupport : L.SupportedOn
      (fun z ↦ AbsorberGreedyInvariant F A z.2) := by
    exact FiniteLaw.timedStoppedProcessLaw_supported n
      (fun _ ↦ greedyKernel F) active S₀ hInvAbs
      (fun _i _hi S hS ↦ absorberGreedyKernel_supported hS)
  refine ⟨z.2, hAbsSupport z hzmass, houtsideSupport z hzmass,
    hzcut, ?_, ?_⟩
  · simpa only [D, hztime] using hprogress.2.1
  · simpa [S₀, absorberGreedyInitialState, hztime] using hprogress.2.2

/-! ## Scheduled phase with separate pair-local and global cutoffs -/

/-- The explicit scheduled two-cutoff absorber phase, strengthened by
survival of every outside pair which remains in the leave.  Both invariants
are supported by the very same timed stopped law, so positive-probability
extraction preserves them simultaneously. -/
theorem exists_linearScheduledAbsorberGreedy_phaseTwoCutoffs_with_outsidePairSurvival
    {V : Type*} [Fintype V] [DecidableEq V]
    {q M n sPair sGlobal Kpair Kglobal Delta delta JUpper Dmin D₀ C : ℕ}
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {X : Finset V} {B A : TripleSystemOn V}
    (S₀ : GreedyStateOn V)
    (hS₀ : S₀ = absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q B) A)
    (hA : A = outsideAvailableTriangles H B)
    (theta a variance : ℝ)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hbank : BankPairsSupported H X B)
    (hdegree : ∀ x, H.degree x ≤ C)
    (hsupport : (verticesOn B).card ≤ C)
    (hlarge : 3 * C + 3 ≤ Fintype.card V)
    (hdelta : 1 ≤ delta) (hsmallPair : 3 + Kpair < delta)
    (hDminPos : 0 < Dmin)
    (hbuffer : n * (3 * Delta + Kglobal) + Dmin ≤ D₀)
    (hfloor₀ : D₀ ≤ S₀.available.card)
    (hinitialCap : ∀ P : PairOn V,
      fixedPairAvailableCountReal S₀ P.1 S₀ + a ≤
        ((Delta + 1 : ℕ) : ℝ))
    (hfinalFloor : ∀ P : PairOn V, PairAlive P.1 S₀ →
      (delta : ℝ) + a +
          (n : ℝ) * pairLowerLinearRate Delta Kglobal Dmin ≤
        fixedPairAvailableCountReal S₀ P.1 S₀)
    (hupperJump : pairUpperLinearRate S₀ delta Delta ≤ (JUpper : ℝ))
    (hlowerDeath :
      pairLowerLinearRate Delta Kglobal Dmin ≤ (delta : ℝ))
    (hvarianceUpper :
      linearPairVarianceBudgetTwoCutoffs Delta Kpair Kglobal Dmin
        (pairUpperLinearRate S₀ delta Delta) ≤ variance)
    (hvarianceLower :
      linearPairVarianceBudgetTwoCutoffs Delta Kpair Kglobal Dmin
        (pairLowerLinearRate Delta Kglobal Dmin) ≤ variance)
    (htheta : 0 < theta)
    (hthetaUpper : theta * (JUpper : ℝ) ≤ 1)
    (hthetaLower : theta * ((3 + Kpair : ℕ) : ℝ) ≤ 1)
    (hvariance : 0 ≤ variance)
    (hratio : (n : ℝ≥0) * (Dmin : ℝ≥0)⁻¹ ≤
      (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hsmall :
      (Fintype.card (PairOn V) : ℝ) *
          (2 * Real.exp
            (-theta * a + theta ^ 2 * (n : ℝ) * variance)) +
        (((Fintype.card (TripleOn V) : ℝ≥0) *
          (Fintype.card (PairOn V) : ℝ≥0) *
          pairTwoAwayTail q sPair Kpair
            (pairTwoAwayThreatExtensionCoefficient q B : ℕ) : ℝ≥0) : ℝ) +
        (((Fintype.card (TripleOn V) : ℝ≥0) *
          envelopeTwoAwayTail q M sGlobal H X B Kglobal : ℝ≥0) : ℝ) < 1) :
    ∃ S : GreedyStateOn V,
      AbsorberGreedyInvariant
          (absorberErdosForbiddenConfigurationsOn q B) A S ∧
        OutsideLeavePairsAlive H X S ∧
        HasPairTwoAwayCutoff
          (absorberErdosForbiddenConfigurationsOn q B) Kpair S ∧
        HasTwoAwayCutoff
          (absorberErdosForbiddenConfigurationsOn q B) Kglobal S ∧
        linearAvailabilitySchedule D₀ (3 * Delta + Kglobal) n n ≤
          S.available.card ∧
        S.chosen.card = n := by
  subst S₀
  let F := absorberErdosForbiddenConfigurationsOn q B
  let S₀ := absorberGreedyInitialState F A
  let D := linearAvailabilitySchedule D₀ (3 * Delta + Kglobal) n
  let active := timedPairBandActiveTwoCutoffs
    F Kpair Kglobal Delta delta D
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  have hInvAbs : AbsorberGreedyInvariant F A S₀ := by
    exact absorberGreedyInitialState_invariant F A fun E hE ↦
      absorberErdosForbidden_nonempty hE
  have houtside₀ : OutsideLeavePairsAlive H X S₀ := by
    change OutsideLeavePairsAlive H X
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B) A)
    rw [hA]
    exact outsideLeavePairsAlive_initial
      (q := q) hbank hdegree hsupport hlarge
  have hAbsSupport : L.SupportedOn
      (fun z ↦ AbsorberGreedyInvariant F A z.2) := by
    exact FiniteLaw.timedStoppedProcessLaw_supported n
      (fun _ ↦ greedyKernel F) active S₀ hInvAbs
      (fun _i _hi _S hS ↦ absorberGreedyKernel_supported hS)
  have houtsideSupport : L.SupportedOn
      (fun z ↦ OutsideLeavePairsAlive H X z.2) := by
    simpa only [L] using
      (timedPairBandTwoCutoffsProcessLaw_supported_outsideLeavePairsAlive
        n F H X S₀ Kpair Kglobal Delta delta D
        hInvAbs.1 houtside₀ hsmallPair)
  have hBothSupport : L.SupportedOn
      (fun z ↦ AbsorberGreedyInvariant F A z.2 ∧
        OutsideLeavePairsAlive H X z.2) := by
    intro z hz
    exact ⟨hAbsSupport z hz, houtsideSupport z hz⟩
  obtain ⟨S, hSboth, _hSInv, hSpair, hSglobal, hSfloor, hScard⟩ :=
    exists_linearScheduledAbsorberGreedy_phaseTwoCutoffs_of_supported
      S₀ rfl theta a variance hA2 (Q := fun S ↦
        AbsorberGreedyInvariant F A S ∧ OutsideLeavePairsAlive H X S)
      (by simpa only [L, F, D, active] using hBothSupport)
      hdelta hsmallPair hDminPos hbuffer hfloor₀ hinitialCap
      hfinalFloor hupperJump hlowerDeath hvarianceUpper hvarianceLower
      htheta hthetaUpper hthetaLower hvariance hratio hsmall
  exact ⟨S, hSboth.1, hSboth.2, hSpair, hSglobal,
    hSfloor, hScard⟩

end

end Erdos207
