/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyOneStepProbability
import ErdosProblems.Erdos207.KernelJointInclusion
import ErdosProblems.Erdos207.UniformExtensionWeight

/-!
# Joint inclusion for a stopped constrained-greedy process

The process is frozen as soon as fewer than `D` legal triangles remain.
Before that time each specified new triangle has conditional probability at
most `D⁻¹`.  The abstract single-insertion theorem then supplies the required
joint inclusion estimate without an independence assumption.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Freeze the constrained-greedy kernel below the availability threshold
`D`. -/
def stoppedGreedyKernel
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (D : ℕ) (S : GreedyStateOn V) :
    FiniteLaw (GreedyStateOn V) :=
  if D ≤ S.available.card then greedyKernel F S else FiniteLaw.pure S

/-- Law of the threshold-stopped process after a fixed number of steps. -/
def stoppedGreedyProcessLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (D fuel : ℕ) (S : GreedyStateOn V) :
    FiniteLaw (GreedyStateOn V) :=
  FiniteLaw.iterateKernel (stoppedGreedyKernel F D) fuel
    (FiniteLaw.pure S)

/-- One ordinary greedy step enlarges the chosen family by at most one
triangle. -/
theorem greedyKernel_monotone_singleInsertion
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) :
    IsMonotoneSingleInsertionKernel (greedyKernel F)
      (fun S : GreedyStateOn V ↦ S.chosen) := by
  classical
  intro S
  unfold greedyKernel
  split_ifs with hnonempty
  · let hne : Nonempty S.available :=
      ⟨⟨hnonempty.choose, hnonempty.choose_spec⟩⟩
    let next : S.available → GreedyStateOn V :=
      fun T ↦ greedyStep F S T.1
    have hu : FiniteLaw.SupportedOn (fun _ : S.available ↦ True)
        (@FiniteLaw.uniform S.available _ hne) :=
      FiniteLaw.uniform_supported _ fun _ ↦ trivial
    have hmap : FiniteLaw.SupportedOn
        (fun S' : GreedyStateOn V ↦ S.chosen ⊆ S'.chosen ∧
          (S'.chosen \ S.chosen).card ≤ 1)
        (FiniteLaw.map next (@FiniteLaw.uniform S.available _ hne)) := by
      refine hu.map next ?_
      intro T _hT
      constructor
      · exact subset_insert T.1 S.chosen
      · by_cases hmem : T.1 ∈ S.chosen
        · simp [next, greedyStep, hmem]
        · simp [next, greedyStep, hmem]
    exact hmap
  · exact FiniteLaw.supportedOn_pure _ ⟨Subset.rfl, by simp⟩

/-- Freezing a single-insertion kernel preserves the same structural
property. -/
theorem stoppedGreedyKernel_monotone_singleInsertion
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (D : ℕ) :
    IsMonotoneSingleInsertionKernel (stoppedGreedyKernel F D)
      (fun S : GreedyStateOn V ↦ S.chosen) := by
  classical
  intro S
  unfold stoppedGreedyKernel
  split_ifs with hactive
  · exact greedyKernel_monotone_singleInsertion F S
  · exact FiniteLaw.supportedOn_pure _ ⟨Subset.rfl, by simp⟩

/-- Freezing the absorber-constrained kernel preserves the full greedy
invariant, just as an ordinary greedy step does. -/
theorem stoppedAbsorberGreedyKernel_supported
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V} {D : ℕ}
    {S : GreedyStateOn V}
    (hS : AbsorberGreedyInvariant F A S) :
    FiniteLaw.SupportedOn (AbsorberGreedyInvariant F A)
      (stoppedGreedyKernel F D S) := by
  classical
  unfold stoppedGreedyKernel
  split_ifs with hactive
  · exact absorberGreedyKernel_supported hS
  · exact FiniteLaw.supportedOn_pure _ hS

/-- Every positive-mass trajectory of the threshold-stopped process retains
the absorber greedy invariant. -/
theorem stoppedAbsorberGreedyProcessLaw_supported
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V} {D fuel : ℕ}
    {S : GreedyStateOn V}
    (hS : AbsorberGreedyInvariant F A S) :
    FiniteLaw.SupportedOn (AbsorberGreedyInvariant F A)
      (stoppedGreedyProcessLaw F D fuel S) := by
  classical
  apply FiniteLaw.SupportedOn.iterateKernel
    (FiniteLaw.supportedOn_pure _ hS) (stoppedGreedyKernel F D)
  intro S' hS'
  exact stoppedAbsorberGreedyKernel_supported hS'

/-- Specialization of stopped-process support to the canonical empty
initial packing for the absorber forbidden family. -/
theorem stoppedAbsorberGreedyInitialProcessLaw_supported
    {V : Type*} [Fintype V] [DecidableEq V]
    (q D fuel : ℕ) (B A : TripleSystemOn V) :
    FiniteLaw.SupportedOn
      (AbsorberGreedyInvariant
        (absorberErdosForbiddenConfigurationsOn q B) A)
      (stoppedGreedyProcessLaw
        (absorberErdosForbiddenConfigurationsOn q B) D fuel
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B) A)) := by
  apply stoppedAbsorberGreedyProcessLaw_supported
  exact absorberGreedyInitialState_invariant _ _ fun S hS ↦
    absorberErdosForbidden_nonempty hS

/-- Above a positive stopping threshold, the one-point conditional
probability is at most the reciprocal threshold. -/
theorem stoppedGreedyKernel_probability_new_triangle_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (D : ℕ) (hD : 0 < D)
    (S : GreedyStateOn V) (T : TripleOn V) (hTnot : T ∉ S.chosen) :
    (stoppedGreedyKernel F D S).probability
        (fun S' ↦ T ∈ S'.chosen) ≤ (D : ℝ≥0)⁻¹ := by
  classical
  unfold stoppedGreedyKernel
  split_ifs with hactive
  · exact greedyKernel_probability_new_triangle_le
      F S T D hD hactive hTnot
  · rw [FiniteLaw.probability_pure]
    simp [hTnot]

/-- Joint-inclusion estimate for the concrete threshold-stopped constrained
greedy process. -/
theorem stoppedGreedyProcess_probability_subset_chosen_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (D fuel : ℕ) (hD : 0 < D)
    (S : GreedyStateOn V) (U : TripleSystemOn V)
    (hdisjoint : Disjoint U S.chosen) :
    (stoppedGreedyProcessLaw F D fuel S).probability
        (fun S' ↦ U ⊆ S'.chosen) ≤
      (U.card.factorial : ℝ≥0) *
        (((fuel : ℝ≥0) * (D : ℝ≥0)⁻¹) ^ U.card) := by
  exact iterateKernel_probability_subset_le
    (stoppedGreedyKernel F D) (fun S : GreedyStateOn V ↦ S.chosen)
    (D : ℝ≥0)⁻¹
    (stoppedGreedyKernel_monotone_singleInsertion F D)
    (fun S T hT ↦
      stoppedGreedyKernel_probability_new_triangle_le F D hD S T hT)
    S U hdisjoint fuel

/-- If the cumulative stopped-process one-point scale is at most a prescribed
constant weight `p`, then every family of at most `m` triangles satisfies the
uniform joint-inclusion hypothesis used by the KSSS moment lemma. -/
theorem stoppedGreedyProcess_probability_subset_chosen_le_weight
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (D fuel m : ℕ) (hD : 0 < D)
    (p : ℝ≥0) (hratio : (fuel : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ p)
    (S : GreedyStateOn V) (U : TripleSystemOn V)
    (hdisjoint : Disjoint U S.chosen) (hcard : U.card ≤ m) :
    (stoppedGreedyProcessLaw F D fuel S).probability
        (fun S' ↦ U ⊆ S'.chosen) ≤
      (m.factorial : ℝ≥0) * setWeight (constantTripleWeight p) U := by
  rw [setWeight_constantTripleWeight]
  calc
    (stoppedGreedyProcessLaw F D fuel S).probability
        (fun S' ↦ U ⊆ S'.chosen) ≤
      (U.card.factorial : ℝ≥0) *
        (((fuel : ℝ≥0) * (D : ℝ≥0)⁻¹) ^ U.card) :=
      stoppedGreedyProcess_probability_subset_chosen_le
        F D fuel hD S U hdisjoint
    _ ≤ (m.factorial : ℝ≥0) * p ^ U.card := by
      apply mul_le_mul
      · exact_mod_cast Nat.factorial_le hcard
      · exact pow_le_pow_left' hratio U.card
      · exact bot_le
      · exact bot_le

end

end Erdos207
