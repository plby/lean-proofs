/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ConditionedPreliminaryGreedyJointLaw

/-!
# A totalized conditioned preliminary kernel

The preliminary stopped process is conditioned on reaching its terminal
active region.  At old states where this event has positive mass we use the
conditioned law; elsewhere we use a deterministic fallback.  Probability and
structural conclusions are therefore stated on the positive-mass support of
the old master law.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The relative preliminary state starts from an existing selected packing
and exposes exactly the ambient family supplied by the master stage. -/
def relativePreliminaryInitialState
    {V : Type*} [Fintype V] [DecidableEq V]
    (P A : TripleSystemOn V) : GreedyStateOn V :=
  { chosen := P, available := A }

@[simp] lemma relativePreliminaryInitialState_chosen
    {V : Type*} [Fintype V] [DecidableEq V]
    (P A : TripleSystemOn V) :
    (relativePreliminaryInitialState P A).chosen = P := rfl

@[simp] lemma relativePreliminaryInitialState_available
    {V : Type*} [Fintype V] [DecidableEq V]
    (P A : TripleSystemOn V) :
    (relativePreliminaryInitialState P A).available = A := rfl

/-- Besides the ordinary invariant, a relative greedy trajectory only adds
members of the initial available family. -/
def RelativeGreedyTrajectory
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S₀ S : GreedyStateOn V) : Prop :=
  GreedyInvariant F S ∧
    S.available ⊆ S₀.available ∧
    S₀.chosen ⊆ S.chosen ∧
    S.chosen ⊆ S₀.chosen ∪ S₀.available

lemma relativeGreedyTrajectory_initial
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ : GreedyStateOn V}
    (hS₀ : GreedyInvariant F S₀) :
    RelativeGreedyTrajectory F S₀ S₀ := by
  exact ⟨hS₀, Subset.rfl, Subset.rfl, subset_union_left⟩

lemma greedyKernel_supported_relativeGreedyTrajectory
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    (hS : RelativeGreedyTrajectory F S₀ S) :
    (greedyKernel F S).SupportedOn (RelativeGreedyTrajectory F S₀) := by
  intro S' hmass
  have hInv' := greedyKernel_supported hS.1 S' hmass
  rcases greedyKernel_supported_step_or_self F S S' hmass with
    rfl | ⟨T, hT, rfl⟩
  · exact hS
  · refine ⟨hInv', (greedyStep_available_subset F S T).trans hS.2.1,
      hS.2.2.1.trans (subset_insert T S.chosen), ?_⟩
    intro U hU
    rw [greedyStep, mem_insert] at hU
    rcases hU with rfl | hUS
    · exact mem_union_right _ (hS.2.1 hT)
    · exact hS.2.2.2 hUS

/-- The whole stopped preliminary process retains the relative trajectory
certificate, independently of which stopping predicate is used. -/
theorem timedStoppedGreedyProcess_supported_relativeGreedyTrajectory
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop) (S₀ : GreedyStateOn V)
    (hS₀ : GreedyInvariant F S₀) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
      active S₀).SupportedOn
        (fun z ↦ RelativeGreedyTrajectory F S₀ z.2) := by
  apply FiniteLaw.timedStoppedProcessLaw_supported n
    (fun _ ↦ greedyKernel F) active S₀
    (relativeGreedyTrajectory_initial hS₀)
  intro _j _hj S hS
  exact greedyKernel_supported_relativeGreedyTrajectory hS

lemma RelativeGreedyTrajectory.added_subset_available
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    (h : RelativeGreedyTrajectory F S₀ S) :
    S.chosen \ S₀.chosen ⊆ S₀.available := by
  intro T hT
  have hTU := h.2.2.2 (mem_sdiff.mp hT).1
  exact (mem_union.mp hTU).resolve_left (mem_sdiff.mp hT).2

lemma RelativeGreedyTrajectory.initial_union_added
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    (h : RelativeGreedyTrajectory F S₀ S) :
    S₀.chosen ∪ (S.chosen \ S₀.chosen) = S.chosen := by
  exact union_sdiff_of_subset h.2.2.1

/-- The new part of a relative trajectory extends an old disjoint split to
the packing represented by its terminal chosen family. -/
lemma RelativeGreedyTrajectory.structural_newPart
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S₀ S : GreedyStateOn V}
    {I D A : TripleSystemOn V}
    (h : RelativeGreedyTrajectory F S₀ S)
    (hchosen : S₀.chosen = I ∪ D) (havailable : S₀.available = A)
    (hID : Disjoint I D) :
    S.chosen \ S₀.chosen ⊆ A ∧
      Disjoint I (D ∪ (S.chosen \ S₀.chosen)) ∧
      IsPackingOn (I ∪ (D ∪ (S.chosen \ S₀.chosen))) := by
  have hnew : S.chosen \ S₀.chosen ⊆ A := by
    simpa only [havailable] using h.added_subset_available
  have hInew : Disjoint I (S.chosen \ S₀.chosen) := by
    rw [Finset.disjoint_left]
    intro T hTI hTnew
    exact (mem_sdiff.mp hTnew).2
      (hchosen.symm ▸ mem_union_left D hTI)
  have hdisj : Disjoint I (D ∪ (S.chosen \ S₀.chosen)) := by
    rw [disjoint_union_right]
    exact ⟨hID, hInew⟩
  have hunion : I ∪ (D ∪ (S.chosen \ S₀.chosen)) = S.chosen := by
    rw [← union_assoc, ← hchosen]
    exact h.initial_union_added
  exact ⟨hnew, hdisj, hunion.symm ▸ h.1.1⟩

/-- Positivity of the terminal active event is the exact readiness condition
for the conditioned preliminary kernel. -/
def RelativePreliminaryReady
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (Kpair Kglobal Kinc Delta delta I D : ℕ)
    (S₀ : GreedyStateOn V) : Prop :=
  let active := timedAggregateAveragePairBandActive
    F Kpair Kglobal Kinc Delta delta I D
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  0 < L.probability (fun z ↦ active z.1.1 z.2)

/-- Use the genuine conditioned law at ready states and a deterministic
fallback elsewhere. -/
def supportedConditionedRelativePreliminaryKernel
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (Kpair Kglobal Kinc Delta delta I D : ℕ)
    (S₀ : GreedyStateOn V) :
    FiniteLaw (FiniteLaw.TimedState (GreedyStateOn V) n) := by
  classical
  let active := timedAggregateAveragePairBandActive
    F Kpair Kglobal Kinc Delta delta I D
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  if h : RelativePreliminaryReady n F
      Kpair Kglobal Kinc Delta delta I D S₀ then
    exact L.conditionOn (fun z ↦ active z.1.1 z.2) h
  else
    exact FiniteLaw.pure (⟨0, by omega⟩, S₀)

/-- At a ready state the totalized kernel is supported on terminal activity. -/
theorem supportedConditionedRelativePreliminaryKernel_supported_active
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (Kpair Kglobal Kinc Delta delta I D : ℕ)
    (S₀ : GreedyStateOn V)
    (hready : RelativePreliminaryReady n F
      Kpair Kglobal Kinc Delta delta I D S₀) :
    (supportedConditionedRelativePreliminaryKernel n F
      Kpair Kglobal Kinc Delta delta I D S₀).SupportedOn
        (fun z ↦ timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta I D z.1.1 z.2) := by
  classical
  rw [supportedConditionedRelativePreliminaryKernel, dif_pos hready]
  exact FiniteLaw.conditionOn_supported _ _ hready

/-- Conditioning does not discard the relative structural trajectory. -/
theorem supportedConditionedRelativePreliminaryKernel_supported_trajectory
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (Kpair Kglobal Kinc Delta delta I D : ℕ)
    (S₀ : GreedyStateOn V) (hS₀ : GreedyInvariant F S₀)
    (hready : RelativePreliminaryReady n F
      Kpair Kglobal Kinc Delta delta I D S₀) :
    (supportedConditionedRelativePreliminaryKernel n F
      Kpair Kglobal Kinc Delta delta I D S₀).SupportedOn
        (fun z ↦ RelativeGreedyTrajectory F S₀ z.2) := by
  classical
  let active := timedAggregateAveragePairBandActive
    F Kpair Kglobal Kinc Delta delta I D
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  have htrajectory : L.SupportedOn
      (fun z ↦ RelativeGreedyTrajectory F S₀ z.2) :=
    timedStoppedGreedyProcess_supported_relativeGreedyTrajectory
      n F active S₀ hS₀
  rw [supportedConditionedRelativePreliminaryKernel, dif_pos hready]
  exact htrajectory.conditionOn hready

/-- The totalized preliminary kernel can add at most one triangle per clock
step.  This bound is retained by the active conditioning, and is also true
for the deterministic fallback (which adds no triangle). -/
theorem supportedConditionedRelativePreliminaryKernel_supported_added_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (Kpair Kglobal Kinc Delta delta I D : ℕ)
    (S₀ : GreedyStateOn V) (hS₀ : GreedyInvariant F S₀) :
    (supportedConditionedRelativePreliminaryKernel n F
      Kpair Kglobal Kinc Delta delta I D S₀).SupportedOn
        (fun z ↦ (z.2.chosen \ S₀.chosen).card ≤ n) := by
  classical
  let active := timedAggregateAveragePairBandActive
    F Kpair Kglobal Kinc Delta delta I D
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  by_cases hready : RelativePreliminaryReady n F
      Kpair Kglobal Kinc Delta delta I D S₀
  · have hcard : L.SupportedOn
        (fun z ↦ z.2.chosen.card = S₀.chosen.card + z.1.1) := by
      simpa only [L, active] using
        timedAggregateAveragePairBandProcessLaw_supported_chosen_card
          (n := n) (Kpair := Kpair) (Kglobal := Kglobal)
          (Kinc := Kinc) (Delta := Delta) (delta := delta)
          (I := I) (D := D) hS₀
    have htrajectory : L.SupportedOn
        (fun z ↦ RelativeGreedyTrajectory F S₀ z.2) :=
      timedStoppedGreedyProcess_supported_relativeGreedyTrajectory
        n F active S₀ hS₀
    rw [supportedConditionedRelativePreliminaryKernel, dif_pos hready]
    intro z hz
    have hzcard := hcard.conditionOn hready z hz
    have hztraj := htrajectory.conditionOn hready z hz
    rw [card_sdiff_of_subset hztraj.2.2.1, hzcard]
    simpa using z.1.2
  · rw [supportedConditionedRelativePreliminaryKernel, dif_neg hready]
    intro z hz
    have hz' := FiniteLaw.supportedOn_pure
      (fun z : FiniteLaw.TimedState (GreedyStateOn V) n ↦
        (z.2.chosen \ S₀.chosen).card ≤ n) (by simp) z hz
    exact hz'

/-- The explicit inactivity estimate gives readiness and the pure product
law for newly selected triples and residual crossing edges. -/
theorem supportedConditionedRelativePreliminaryKernel_productLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (H G : SimpleGraph V) (X : Finset V)
    (Kpair Kglobal Kinc Delta delta I D M k : ℕ)
    (hD : 0 < D) (hkM : k ≤ M) (h3k : 3 * k ≤ delta)
    (alpha eta epsilon : ℝ≥0) (S₀ : GreedyStateOn V)
    (hInv₀ : GreedyInvariant F S₀)
    (houtside₀ : OutsideLeavePairsAlive H X S₀)
    (hHG : Disjoint H G)
    (hGleave : G ≤ leaveGraph S₀.chosen)
    (hsmall : 3 + Kpair < delta)
    (hactive₀ : timedAggregateAveragePairBandActive
      F Kpair Kglobal Kinc Delta delta I D 0 S₀)
    (hupper : ∀ j S,
      timedAggregateAveragePairBandActive
        F Kpair Kglobal Kinc Delta delta I D j S →
      S.available.card ≤ M)
    (hselected : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ alpha)
    (hsurvived : ∀ Q : TripleSystemOn V,
      ((((M - k : ℕ) : ℝ≥0) * (M : ℝ≥0)⁻¹) ^
        (n - Q.card)) ≤ eta)
    (hinactive :
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F)
        (timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta I D) S₀).probability
        (fun z ↦ ¬ timedAggregateAveragePairBandActive
          F Kpair Kglobal Kinc Delta delta I D z.1.1 z.2) ≤ epsilon)
    (hepsilon : epsilon < 1) :
    RelativePreliminaryReady n F
        Kpair Kglobal Kinc Delta delta I D S₀ ∧
      ∀ Q : TripleSystemOn V, ∀ E : Finset (Sym2 V),
        (supportedConditionedRelativePreliminaryKernel n F
          Kpair Kglobal Kinc Delta delta I D S₀).probability
            (fun z ↦ Q ⊆ z.2.chosen \ S₀.chosen ∧
              E ⊆ preliminaryResidualCrossingEdges G X z.2.chosen) ≤
          (alpha / (1 - epsilon)) ^ Q.card *
            (eta / (1 - epsilon)) ^ E.card := by
  let active := timedAggregateAveragePairBandActive
    F Kpair Kglobal Kinc Delta delta I D
  let L := FiniteLaw.timedStoppedProcessLaw n
    (fun _ ↦ greedyKernel F) active S₀
  let Good : FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ active z.1.1 z.2
  have hlower : 1 - epsilon ≤ L.probability Good := by
    rw [L.probability_not Good] at hinactive
    calc
      1 - epsilon ≤ 1 - (1 - L.probability Good) :=
        tsub_le_tsub_left hinactive 1
      _ = L.probability Good :=
        tsub_tsub_cancel_of_le (L.probability_le_one Good)
  have hready : RelativePreliminaryReady n F
      Kpair Kglobal Kinc Delta delta I D S₀ :=
    (tsub_pos_iff_lt.mpr hepsilon).trans_le hlower
  refine ⟨hready, ?_⟩
  intro Q E
  have hraw :=
    conditionedTimedAggregateAveragePairBand_probability_newSelected_residual_le
      n F H G X Kpair Kglobal Kinc Delta delta I D M k hD hkM h3k
      alpha eta S₀ hInv₀ houtside₀ hHG hGleave hsmall hactive₀
      hupper hselected hsurvived hready Q E
  have hden : 0 < 1 - epsilon := tsub_pos_iff_lt.mpr hepsilon
  have halpha : alpha / L.probability Good ≤ alpha / (1 - epsilon) := by
    exact div_le_div_of_nonneg_left zero_le hden hlower
  have heta : eta / L.probability Good ≤ eta / (1 - epsilon) := by
    exact div_le_div_of_nonneg_left zero_le hden hlower
  rw [supportedConditionedRelativePreliminaryKernel, dif_pos hready]
  calc
    (L.conditionOn Good hready).probability
        (fun z ↦ Q ⊆ z.2.chosen \ S₀.chosen ∧
          E ⊆ preliminaryResidualCrossingEdges G X z.2.chosen) ≤
        (alpha / L.probability Good) ^ Q.card *
          (eta / L.probability Good) ^ E.card := by
      simpa only [L, Good, active] using hraw
    _ ≤ (alpha / (1 - epsilon)) ^ Q.card *
        (eta / (1 - epsilon)) ^ E.card := by
      gcongr

end

end Erdos207
