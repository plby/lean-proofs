/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyRootedConfigurationWeight

/-! # The first KSSS crude-statistic moment bound at uniform weight -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem greedyRootedConfigurationClass_moment_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (S : Ω → GreedyStateOn V)
    (F J : ForbiddenFamilyOn V) (R : TripleSystemOn V)
    (c m n B s : ℕ) (C : ℝ≥0)
    (hS : L.SupportedOn (fun ω ↦ GreedyInvariant F (S ω)))
    (hcard : ∀ E ∈ J, E.card = m) (hR : R.card = 2)
    (hc : c + 3 ≤ m) (hn : 1 ≤ n)
    (hcount : ∀ Q : TripleSystemOn V, 2 ≤ Q.card → Q.card < m →
      (familyExtensions J Q).card ≤ B * n ^ (m - Q.card - 1))
    (hjoint : ∀ T : TripleSystemOn V, T.card ≤ s * c →
      L.probability (fun ω ↦ T ⊆ (S ω).chosen) ≤ C * ((n : ℝ≥0)⁻¹) ^ T.card) :
    L.expectation (fun ω ↦ ((greedyRootedConfigurationClass J (S ω) R c).card : ℝ≥0) ^ s) ≤
      C * (((2 : ℝ≥0) ^ (s * c) *
        ((2 : ℝ≥0) ^ m * B * (n : ℝ≥0) ^ (m - c - 3))) ^ s) := by
  let z := m - c - R.card
  let rem := fun u : OmittedFamilyIndex J R z ↦ omittedFamilyRemainder u
  have hremcard : ∀ u, (rem u).card ≤ c := by
    intro u
    rw [omittedFamilyRemainder_card hcard u, hR]
    dsimp only [z]
    omega
  have hkappa : HasExtensionBound rem (fun _ ↦ (n : ℝ≥0)⁻¹)
      ((2 : ℝ≥0) ^ m * B * (n : ℝ≥0) ^ (m - c - 3)) := by
    have hz : 1 ≤ z := by dsimp only [z]; omega
    have hexp : z - 1 = m - c - 3 := by dsimp only [z]; omega
    simpa only [hexp] using omittedFamily_hasExtensionBound J R z m n B
      hcard hR hz hn hcount
  have hdom :
      L.expectation (fun ω ↦ ((greedyRootedConfigurationClass J (S ω) R c).card : ℝ≥0) ^ s) ≤
        L.expectation (fun ω ↦ (selectedCount rem (S ω).chosen) ^ s) := by
    unfold FiniteLaw.expectation
    apply sum_le_sum
    intro ω _
    by_cases hmass : 0 < L.mass ω
    · have hpoint := greedyRootedConfigurationClass_card_le_selectedCount R c m
        (hS ω hmass) hcard
      have hpoint' : ((greedyRootedConfigurationClass J (S ω) R c).card : ℝ≥0) ≤
          selectedCount rem (S ω).chosen := by
        exact hpoint
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left' hpoint' s) zero_le
    · have hzero : L.mass ω = 0 := le_antisymm (le_of_not_gt hmass) zero_le
      simp [hzero]
  refine hdom.trans (configurationMomentBound L rem (fun ω ↦ (S ω).chosen)
    (fun _ ↦ (n : ℝ≥0)⁻¹) C _ hremcard hkappa ?_)
  intro T hT
  simpa only [setWeight, prod_const] using hjoint T hT

end

end Erdos207
