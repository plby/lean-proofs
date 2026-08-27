/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyDeletionBound
import ErdosProblems.Erdos207.InhomogeneousJointInclusion
import ErdosProblems.Erdos207.StoppedGreedyJointInclusion

/-!
# A greedy process stopped at a deterministic availability envelope

The threshold used by a long greedy trajectory is naturally time dependent.
At time `i` we run the ordinary constrained-greedy transition only while the
two-away deletion cutoff holds and at least `D i` triangles remain.  This file
proves both the resulting inhomogeneous joint-inclusion estimate and the
pathwise preservation of the scheduled availability floor.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- At time `i`, freeze unless both the two-away cutoff and the scheduled
availability floor hold. -/
def envelopeStoppedGreedyKernel
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (K : ℕ) (D : ℕ → ℕ)
    (i : ℕ) (S : GreedyStateOn V) : FiniteLaw (GreedyStateOn V) := by
  classical
  exact if HasTwoAwayCutoff F K S ∧ D i ≤ S.available.card then
      greedyKernel F S
    else
      FiniteLaw.pure S

/-- Law after the first `fuel` envelope-stopped transitions. -/
def envelopeStoppedGreedyProcessLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (K : ℕ) (D : ℕ → ℕ)
    (fuel : ℕ) (S : GreedyStateOn V) : FiniteLaw (GreedyStateOn V) :=
  FiniteLaw.evolveKernels (envelopeStoppedGreedyKernel F K D) fuel
    (FiniteLaw.pure S)

/-- With nonempty availability, every supported successor is an actual
greedy step (the frozen alternative cannot occur). -/
theorem greedyKernel_supported_step_of_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (hA : S.available.Nonempty) :
    FiniteLaw.SupportedOn
      (fun S' ↦ ∃ T ∈ S.available, S' = greedyStep F S T)
      (greedyKernel F S) := by
  classical
  unfold greedyKernel
  simp only [hA, ↓reduceDIte]
  let hne : Nonempty S.available :=
    ⟨⟨hA.choose, hA.choose_spec⟩⟩
  let next : S.available → GreedyStateOn V :=
    fun T ↦ greedyStep F S T.1
  exact (FiniteLaw.uniform_supported (fun _ : S.available ↦ True)
    (fun _ ↦ trivial)).map next fun T _ ↦ ⟨T.1, T.2, rfl⟩

lemma greedyStep_chosen_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T : TripleOn V)
    (hT : T ∉ S.chosen) :
    (greedyStep F S T).chosen.card = S.chosen.card + 1 := by
  simp [greedyStep, hT]

/-- Time-dependent freezing preserves the monotone single-insertion
property of the ordinary greedy kernel. -/
theorem envelopeStoppedGreedyKernel_monotone_singleInsertion
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (K : ℕ) (D : ℕ → ℕ) (i : ℕ) :
    IsMonotoneSingleInsertionKernel (envelopeStoppedGreedyKernel F K D i)
      (fun S : GreedyStateOn V ↦ S.chosen) := by
  classical
  intro S
  unfold envelopeStoppedGreedyKernel
  split_ifs with hactive
  · exact greedyKernel_monotone_singleInsertion F S
  · exact FiniteLaw.supportedOn_pure _ ⟨Subset.rfl, by simp⟩

/-- The one-point hazard at time `i` is at most the reciprocal scheduled
availability, whether the kernel is active or frozen. -/
theorem envelopeStoppedGreedyKernel_probability_new_triangle_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (K : ℕ) (D : ℕ → ℕ)
    (i : ℕ) (hD : 0 < D i) (S : GreedyStateOn V) (T : TripleOn V)
    (hTnot : T ∉ S.chosen) :
    (envelopeStoppedGreedyKernel F K D i S).probability
        (fun S' ↦ T ∈ S'.chosen) ≤ (D i : ℝ≥0)⁻¹ := by
  classical
  unfold envelopeStoppedGreedyKernel
  split_ifs with hactive
  · exact greedyKernel_probability_new_triangle_le
      F S T (D i) hD hactive.2 hTnot
  · rw [FiniteLaw.probability_pure]
    simp [hTnot]

/-- Every envelope-stopped transition preserves the greedy invariant. -/
theorem envelopeStoppedGreedyKernel_supported_invariant
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {K : ℕ} {D : ℕ → ℕ}
    {i : ℕ} {S : GreedyStateOn V} (hInv : GreedyInvariant F S) :
    FiniteLaw.SupportedOn (GreedyInvariant F)
      (envelopeStoppedGreedyKernel F K D i S) := by
  classical
  unfold envelopeStoppedGreedyKernel
  split_ifs with hactive
  · exact greedyKernel_supported hInv
  · exact FiniteLaw.supportedOn_pure _ hInv

/-- If the next scheduled floor plus the deletion envelope is at most the
current floor, then one transition preserves both the invariant and the next
floor.  On a cutoff failure the process freezes, so the conclusion remains
valid. -/
theorem envelopeStoppedGreedyKernel_supported_nextEnvelope
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {K : ℕ} {D : ℕ → ℕ}
    {i : ℕ} {S : GreedyStateOn V}
    (hInv : GreedyInvariant F S) (hfloor : D i ≤ S.available.card)
    (hdecrease : D (i + 1) + (3 * Fintype.card V + K) ≤ D i) :
    FiniteLaw.SupportedOn
      (fun S' ↦ GreedyInvariant F S' ∧
        D (i + 1) ≤ S'.available.card)
      (envelopeStoppedGreedyKernel F K D i S) := by
  classical
  have hnext_le : D (i + 1) ≤ D i := by omega
  unfold envelopeStoppedGreedyKernel
  split_ifs with hactive
  · have hsupport := greedyKernel_supported_step_or_self F S
    intro S' hmass
    rcases hsupport S' hmass with rfl | ⟨T, hT, rfl⟩
    · exact ⟨hInv, hnext_le.trans hfloor⟩
    · refine ⟨hInv.step hT, ?_⟩
      have hstep := greedyStep_available_card_le_add_envelope
        hInv hactive.1 hT
      omega
  · exact FiniteLaw.supportedOn_pure _ ⟨hInv, hnext_le.trans hfloor⟩

/-- The invariant and the deterministic availability schedule hold on the
entire positive-mass support of the stopped process. -/
theorem envelopeStoppedGreedyProcessLaw_supported
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {K : ℕ} {D : ℕ → ℕ}
    {S : GreedyStateOn V} (hInv : GreedyInvariant F S)
    (hfloor : D 0 ≤ S.available.card)
    (hdecrease : ∀ i,
      D (i + 1) + (3 * Fintype.card V + K) ≤ D i) :
    ∀ fuel,
      FiniteLaw.SupportedOn
        (fun S' ↦ GreedyInvariant F S' ∧
          D fuel ≤ S'.available.card)
        (envelopeStoppedGreedyProcessLaw F K D fuel S) := by
  intro fuel
  induction fuel with
  | zero =>
      exact FiniteLaw.supportedOn_pure _ ⟨hInv, hfloor⟩
  | succ fuel ih =>
      change FiniteLaw.SupportedOn _
        (FiniteLaw.bind
          (envelopeStoppedGreedyProcessLaw F K D fuel S)
          (envelopeStoppedGreedyKernel F K D fuel))
      exact ih.bind _ fun S' hS' ↦
        envelopeStoppedGreedyKernel_supported_nextEnvelope
          hS'.1 hS'.2 (hdecrease fuel)

/-- Absorber containment and exact availability are preserved together with
the scheduled floor. -/
theorem envelopeStoppedGreedyKernel_supported_absorberNextEnvelope
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V}
    {K : ℕ} {D : ℕ → ℕ} {i : ℕ} {S : GreedyStateOn V}
    (hInv : AbsorberGreedyInvariant F A S)
    (hfloor : D i ≤ S.available.card)
    (hdecrease : D (i + 1) + (3 * Fintype.card V + K) ≤ D i) :
    FiniteLaw.SupportedOn
      (fun S' ↦ AbsorberGreedyInvariant F A S' ∧
        D (i + 1) ≤ S'.available.card)
      (envelopeStoppedGreedyKernel F K D i S) := by
  classical
  have hnext_le : D (i + 1) ≤ D i := by omega
  unfold envelopeStoppedGreedyKernel
  split_ifs with hactive
  · have hsupport := greedyKernel_supported_step_or_self F S
    intro S' hmass
    rcases hsupport S' hmass with rfl | ⟨T, hT, rfl⟩
    · exact ⟨hInv, hnext_le.trans hfloor⟩
    · refine ⟨hInv.step hT, ?_⟩
      have hstep := greedyStep_available_card_le_add_envelope
        hInv.1 hactive.1 hT
      omega
  · exact FiniteLaw.supportedOn_pure _ ⟨hInv, hnext_le.trans hfloor⟩

theorem envelopeStoppedAbsorberGreedyProcessLaw_supported
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V}
    {K : ℕ} {D : ℕ → ℕ} {S : GreedyStateOn V}
    (hInv : AbsorberGreedyInvariant F A S)
    (hfloor : D 0 ≤ S.available.card)
    (hdecrease : ∀ i,
      D (i + 1) + (3 * Fintype.card V + K) ≤ D i) :
    ∀ fuel,
      FiniteLaw.SupportedOn
        (fun S' ↦ AbsorberGreedyInvariant F A S' ∧
          D fuel ≤ S'.available.card)
        (envelopeStoppedGreedyProcessLaw F K D fuel S) := by
  intro fuel
  induction fuel with
  | zero =>
      exact FiniteLaw.supportedOn_pure _ ⟨hInv, hfloor⟩
  | succ fuel ih =>
      change FiniteLaw.SupportedOn _
        (FiniteLaw.bind
          (envelopeStoppedGreedyProcessLaw F K D fuel S)
          (envelopeStoppedGreedyKernel F K D fuel))
      exact ih.bind _ fun S' hS' ↦
        envelopeStoppedGreedyKernel_supported_absorberNextEnvelope
          hS'.1 hS'.2 (hdecrease fuel)

/-- A terminal state on which the cutoff still holds has performed every
scheduled insertion.  A cutoff failure is absorbing, and therefore is the
only alternative in the support invariant. -/
theorem envelopeStoppedAbsorberGreedyProcessLaw_supported_progress
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V}
    {K : ℕ} {D : ℕ → ℕ} {S₀ : GreedyStateOn V}
    (hInv : AbsorberGreedyInvariant F A S₀)
    (hfloor : D 0 ≤ S₀.available.card) (hD : ∀ i, 0 < D i)
    (hdecrease : ∀ i,
      D (i + 1) + (3 * Fintype.card V + K) ≤ D i) :
    ∀ fuel,
      FiniteLaw.SupportedOn
        (fun S ↦ AbsorberGreedyInvariant F A S ∧
          D fuel ≤ S.available.card ∧
          (¬ HasTwoAwayCutoff F K S ∨
            S.chosen.card = S₀.chosen.card + fuel))
        (envelopeStoppedGreedyProcessLaw F K D fuel S₀) := by
  intro fuel
  induction fuel with
  | zero =>
      exact FiniteLaw.supportedOn_pure _
        ⟨hInv, hfloor, Or.inr (by omega)⟩
  | succ fuel ih =>
      change FiniteLaw.SupportedOn _
        (FiniteLaw.bind
          (envelopeStoppedGreedyProcessLaw F K D fuel S₀)
          (envelopeStoppedGreedyKernel F K D fuel))
      refine ih.bind (envelopeStoppedGreedyKernel F K D fuel) ?_
      intro S hS
      have hdec := hdecrease fuel
      have hnext_le : D (fuel + 1) ≤ D fuel := by
        omega
      unfold envelopeStoppedGreedyKernel
      split_ifs with hactive
      · have hnonempty : S.available.Nonempty := by
          rw [← card_pos]
          exact (hD fuel).trans_le hS.2.1
        have hsteps := greedyKernel_supported_step_of_nonempty F S hnonempty
        intro S' hmass
        obtain ⟨T, hT, rfl⟩ := hsteps S' hmass
        have hTnot : T ∉ S.chosen := (hS.1.1.2.2 T hT).1
        have hcardS : S.chosen.card = S₀.chosen.card + fuel := by
          rcases hS.2.2 with hbad | hcard
          · exact (hbad hactive.1).elim
          · exact hcard
        have hstepfloor := greedyStep_available_card_le_add_envelope
          hS.1.1 hactive.1 hT
        refine ⟨hS.1.step hT, ?_, Or.inr ?_⟩
        · omega
        · rw [greedyStep_chosen_card F S T hTnot, hcardS]
          omega
      · have hbad : ¬ HasTwoAwayCutoff F K S := by
          intro hcut
          exact hactive ⟨hcut, hS.2.1⟩
        exact FiniteLaw.supportedOn_pure _
          ⟨hS.1, hnext_le.trans hS.2.1, Or.inl hbad⟩

/-- Joint inclusion under the envelope-stopped process.  The only price for
the varying threshold is the sum of its reciprocal point hazards. -/
theorem envelopeStoppedGreedyProcess_probability_subset_chosen_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (K : ℕ) (D : ℕ → ℕ)
    (hD : ∀ i, 0 < D i) (fuel : ℕ) (S : GreedyStateOn V)
    (U : TripleSystemOn V) (hdisjoint : Disjoint U S.chosen) :
    (envelopeStoppedGreedyProcessLaw F K D fuel S).probability
        (fun S' ↦ U ⊆ S'.chosen) ≤
      (U.card.factorial : ℝ≥0) *
        ((∑ i ∈ range fuel, (D i : ℝ≥0)⁻¹) ^ U.card) := by
  exact evolveKernels_probability_subset_le
    (envelopeStoppedGreedyKernel F K D)
    (fun S : GreedyStateOn V ↦ S.chosen)
    (fun i ↦ (D i : ℝ≥0)⁻¹)
    (envelopeStoppedGreedyKernel_monotone_singleInsertion F K D)
    (fun i S T hT ↦
      envelopeStoppedGreedyKernel_probability_new_triangle_le
        F K D i (hD i) S T hT)
    S U hdisjoint fuel

/-- Weighted form of the inhomogeneous joint-inclusion estimate. -/
theorem envelopeStoppedGreedyProcess_probability_subset_chosen_le_weight
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (K : ℕ) (D : ℕ → ℕ)
    (hD : ∀ i, 0 < D i) (fuel m : ℕ) (p : ℝ≥0)
    (hratio : (∑ i ∈ range fuel, (D i : ℝ≥0)⁻¹) ≤ p)
    (S : GreedyStateOn V) (U : TripleSystemOn V)
    (hdisjoint : Disjoint U S.chosen) (hcard : U.card ≤ m) :
    (envelopeStoppedGreedyProcessLaw F K D fuel S).probability
        (fun S' ↦ U ⊆ S'.chosen) ≤
      (m.factorial : ℝ≥0) * setWeight (constantTripleWeight p) U := by
  rw [setWeight_constantTripleWeight]
  calc
    (envelopeStoppedGreedyProcessLaw F K D fuel S).probability
        (fun S' ↦ U ⊆ S'.chosen) ≤
      (U.card.factorial : ℝ≥0) *
        ((∑ i ∈ range fuel, (D i : ℝ≥0)⁻¹) ^ U.card) :=
      envelopeStoppedGreedyProcess_probability_subset_chosen_le
        F K D hD fuel S U hdisjoint
    _ ≤ (m.factorial : ℝ≥0) * p ^ U.card := by
      apply mul_le_mul
      · exact_mod_cast Nat.factorial_le hcard
      · exact pow_le_pow_left' hratio U.card
      · exact bot_le
      · exact bot_le

end

end Erdos207
