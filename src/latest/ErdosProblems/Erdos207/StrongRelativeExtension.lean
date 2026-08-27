/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.StrongWellDistributedUnion
import ErdosProblems.Erdos207.RelativeExtensionFromJoint

/-!
# Relative extension bounds from strong well-distributedness

The joint-inclusion consequence of strong well-distributedness is inserted
into the relative-extension binomial expansion.  A finite union bound over
all roots actually occurring inside a configuration then selects one outcome
with a uniform relative extension bound.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Expected relative extension weight for `initial ∪ later` under a
strongly well-distributed master law. -/
theorem IsStronglyWellDistributed.expected_relativeExtensionWeight_le
    {Ω V I : Type*} [Fintype Ω] [Fintype V] [Fintype I]
    [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {initial later : Ω → TripleSystemOn V}
    {p C b : ℝ≥0}
    (h : IsStronglyWellDistributed L W stage initial later p C b)
    (d : ℕ) (hC : 1 ≤ C)
    (F : I → TripleSystemOn V) (hcard : ∀ i, (F i).card ≤ d)
    (hb : ∀ S : TripleSystemOn V, S.card ≤ d →
      b ≤ setWeight (masterUnionTriangleWeight W stage p) S)
    (sigma : TripleOn V → ℝ≥0) (A : TripleSystemOn V) :
    L.expectation (fun ω ↦
      extensionWeight
        (fun i ↦ F i \ (initial ω ∪ later ω)) sigma A) ≤
      (2 * (2 * C) ^ d) *
        extensionWeight F
          (fun T ↦ masterUnionTriangleWeight W stage p T + sigma T) A := by
  apply expected_relativeExtensionWeight_le_of_joint
    L (fun ω ↦ initial ω ∪ later ω) F
      (masterUnionTriangleWeight W stage p) sigma
      (2 * (2 * C) ^ d) d hcard
  intro S hSd
  exact h.probability_subset_union_le_product hC S hSd (hb S hSd)

/-- A scalar union bound selects one master-law outcome for which every
relative extension root obeys the same cutoff. -/
theorem IsStronglyWellDistributed.exists_relativeExtensionBound
    {Ω V I : Type*} [Fintype Ω] [Fintype V] [Fintype I]
    [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {initial later : Ω → TripleSystemOn V}
    {p C b : ℝ≥0}
    (h : IsStronglyWellDistributed L W stage initial later p C b)
    (d : ℕ) (hC : 1 ≤ C)
    (F : I → TripleSystemOn V) (hcard : ∀ i, (F i).card ≤ d)
    (hb : ∀ S : TripleSystemOn V, S.card ≤ d →
      b ≤ setWeight (masterUnionTriangleWeight W stage p) S)
    (sigma : TripleOn V → ℝ≥0) (kappa kappaOut : ℝ≥0)
    (hkappa : HasExtensionBound F
      (fun T ↦ masterUnionTriangleWeight W stage p T + sigma T) kappa)
    (hkappaOut : 0 < kappaOut)
    (hsmall : (configurationRoots F).card *
      (((2 * (2 * C) ^ d) * kappa) / kappaOut) < 1) :
    ∃ ω : Ω,
      HasExtensionBound
        (fun i ↦ F i \ (initial ω ∪ later ω)) sigma kappaOut := by
  let Bad : TripleSystemOn V → Ω → Prop := fun A ω ↦
    kappaOut ≤ extensionWeight
      (fun i ↦ F i \ (initial ω ∪ later ω)) sigma A
  have hprob : ∀ A : TripleSystemOn V,
      L.probability (Bad A) ≤
        ((2 * (2 * C) ^ d) * kappa) / kappaOut := by
    intro A
    apply (L.probability_le_expectation_div
      (fun ω ↦ extensionWeight
        (fun i ↦ F i \ (initial ω ∪ later ω)) sigma A)
      hkappaOut).trans
    exact (div_le_div_iff_of_pos_right hkappaOut).2 <|
      (h.expected_relativeExtensionWeight_le d hC F hcard hb sigma A).trans
        (mul_le_mul_of_nonneg_left (hkappa A) zero_le)
  have hsum : ∑ A ∈ configurationRoots F, L.probability (Bad A) < 1 := by
    calc
      ∑ A ∈ configurationRoots F, L.probability (Bad A) ≤
          ∑ _A ∈ configurationRoots F,
            ((2 * (2 * C) ^ d) * kappa) / kappaOut := by
        exact sum_le_sum fun A _hA ↦ hprob A
      _ = (configurationRoots F).card *
          (((2 * (2 * C) ^ d) * kappa) / kappaOut) := by simp
      _ < 1 := hsmall
  obtain ⟨ω, hω⟩ := L.exists_avoiding_of_sum_probability_lt_one
    (configurationRoots F) Bad hsum
  refine ⟨ω, ?_⟩
  intro A
  by_cases hA : A ∈ configurationRoots F
  · exact le_of_lt (lt_of_not_ge (hω A hA))
  · rw [extensionWeight_eq_zero_of_not_mem_configurationRoots
      (fun i ↦ F i \ (initial ω ∪ later ω)) sigma]
    · exact zero_le
    · intro hroot
      obtain ⟨i, hi⟩ := mem_configurationRoots_iff.mp hroot
      exact hA (mem_configurationRoots_iff.mpr
        ⟨i, hi.trans sdiff_subset⟩)

end

end Erdos207
