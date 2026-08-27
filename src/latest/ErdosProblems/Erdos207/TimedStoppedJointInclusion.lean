/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteStoppedKernel
import ErdosProblems.Erdos207.InhomogeneousJointInclusion
import ErdosProblems.Erdos207.GreedyOneStepProbability
import ErdosProblems.Erdos207.UniformExtensionWeight
import ErdosProblems.Erdos207.StoppedGreedyJointInclusion

/-!
# Joint inclusion for a timed stopped greedy law

If every active state retains at least `D` available triangles, adjoining the
stopping clock does not change the monotone one-insertion property or the
one-point hazard bound.  Hence the terminal timed law satisfies the same
factorial joint-inclusion estimate as the ordinary stopped greedy process.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- A timed stopped greedy transition inserts at most one triangle. -/
theorem timedStoppedGreedyKernel_monotone_singleInsertion
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop) :
    IsMonotoneSingleInsertionKernel
      (fun z : FiniteLaw.TimedState (GreedyStateOn V) n ↦
        FiniteLaw.timedStoppedKernel n (fun _ ↦ greedyKernel F) active z)
      (fun z ↦ z.2.chosen) := by
  classical
  intro z
  change FiniteLaw.SupportedOn _
    (FiniteLaw.timedStoppedKernel n (fun _ ↦ greedyKernel F) active z)
  unfold FiniteLaw.timedStoppedKernel
  split_ifs with hactive
  · exact (greedyKernel_monotone_singleInsertion F z.2).map
      (fun S' ↦ (FiniteLaw.advanceTime z.1 hactive.1, S'))
      (fun S' hS' ↦ hS')
  · exact FiniteLaw.supportedOn_pure _ ⟨Subset.rfl, by simp⟩

/-- A uniform active-region availability floor gives a uniform point hazard
bound for the timed transition. -/
theorem timedStoppedGreedyKernel_probability_new_triangle_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (hD : 0 < D)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (z : FiniteLaw.TimedState (GreedyStateOn V) n) (T : TripleOn V)
    (hTnot : T ∉ z.2.chosen) :
    (FiniteLaw.timedStoppedKernel n (fun _ ↦ greedyKernel F) active z).probability
        (fun z' ↦ T ∈ z'.2.chosen) ≤ (D : ℝ≥0)⁻¹ := by
  classical
  unfold FiniteLaw.timedStoppedKernel
  split_ifs with hactive
  · rw [FiniteLaw.probability_map]
    exact greedyKernel_probability_new_triangle_le F z.2 T D hD
      (hfloor z.1.1 z.2 hactive.2) hTnot
  · rw [FiniteLaw.probability_pure]
    simp [hTnot]

/-- Factorial joint-inclusion estimate for the terminal timed law. -/
theorem timedStoppedGreedyProcess_probability_subset_chosen_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (hD : 0 < D)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (S₀ : GreedyStateOn V) (U : TripleSystemOn V)
    (hdisjoint : Disjoint U S₀.chosen) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
        (fun z ↦ U ⊆ z.2.chosen) ≤
      (U.card.factorial : ℝ≥0) *
        (((n : ℝ≥0) * (D : ℝ≥0)⁻¹) ^ U.card) := by
  let z₀ : FiniteLaw.TimedState (GreedyStateOn V) n :=
    (⟨0, by omega⟩, S₀)
  have hjoint := evolveKernels_probability_subset_le
    (fun _i z ↦ FiniteLaw.timedStoppedKernel n
      (fun _ ↦ greedyKernel F) active z)
    (fun z : FiniteLaw.TimedState (GreedyStateOn V) n ↦ z.2.chosen)
    (fun _i ↦ (D : ℝ≥0)⁻¹)
    (fun _i ↦ timedStoppedGreedyKernel_monotone_singleInsertion n F active)
    (fun _i z T hT ↦
      timedStoppedGreedyKernel_probability_new_triangle_le
        n F active D hD hfloor z T hT)
    z₀ U hdisjoint n
  simpa [FiniteLaw.timedStoppedProcessLaw, z₀] using hjoint

/-- Joint-inclusion estimate compared with a prescribed constant triangle
weight. -/
theorem timedStoppedGreedyProcess_probability_subset_chosen_le_weight
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (D m : ℕ) (p : ℝ≥0) (hD : 0 < D)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ p)
    (S₀ : GreedyStateOn V) (U : TripleSystemOn V)
    (hdisjoint : Disjoint U S₀.chosen) (hcard : U.card ≤ m) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
        (fun z ↦ U ⊆ z.2.chosen) ≤
      (m.factorial : ℝ≥0) * setWeight (constantTripleWeight p) U := by
  rw [setWeight_constantTripleWeight]
  calc
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
        (fun z ↦ U ⊆ z.2.chosen) ≤
      (U.card.factorial : ℝ≥0) *
        (((n : ℝ≥0) * (D : ℝ≥0)⁻¹) ^ U.card) :=
      timedStoppedGreedyProcess_probability_subset_chosen_le
        n F active D hD hfloor S₀ U hdisjoint
    _ ≤ (m.factorial : ℝ≥0) * p ^ U.card := by
      apply mul_le_mul
      · exact_mod_cast Nat.factorial_le hcard
      · exact pow_le_pow_left' hratio U.card
      · exact bot_le
      · exact bot_le

end

end Erdos207
