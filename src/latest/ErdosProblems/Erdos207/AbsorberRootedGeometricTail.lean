/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TimedStoppedBoundedMomentTail
import ErdosProblems.Erdos207.AbsorberRootedMoment

/-! # Growing-moment tail for the first rooted crude statistic -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem timedStoppedAbsorber_rooted_geometricTail
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (D : ℕ) (S₀ : GreedyStateOn V) (B R : TripleSystemOn V)
    (q j c s : ℕ) (w K : ℝ≥0)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hR : R.card = 2) (hc : c + 5 ≤ j) (hD : 0 < D) (hw : 1 ≤ w) (hK : 0 < K)
    (hfloor : ∀ i S, active i S → D ≤ S.available.card)
    (hratio : (n : ℝ≥0) * (D : ℝ≥0)⁻¹ ≤ w * (Fintype.card V + 1 : ℝ≥0)⁻¹)
    (hcut : 2 * (w ^ c * ((boundedIntersectionMomentCoefficient c s : ℝ≥0) *
      ((2 : ℝ≥0) ^ (j - 2) * pairExactBankExtensionCoefficient q B *
        (Fintype.card V + 1 : ℝ≥0) ^ (j - c - 5)))) ≤ K) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ K ≤ ((greedyRootedConfigurationClass
        (absorberInducedConfigurationsOn q j B) z.2 R c).card : ℝ≥0)) ≤ (1 / 2 : ℝ≥0) ^ s := by
  let J := absorberInducedConfigurationsOn q j B
  let z := j - 2 - c - R.card
  let rem := fun u : OmittedFamilyIndex J R z ↦ omittedFamilyRemainder u
  have hcard : ∀ u, (rem u).card ≤ c := by
    intro u
    rw [omittedFamilyRemainder_card absorberInducedConfigurationsOn_fixed_card u, hR]
    dsimp only [z]
    omega
  have hcount : ∀ Q : TripleSystemOn V, 2 ≤ Q.card → Q.card < j - 2 →
      (familyExtensions J Q).card ≤ pairExactBankExtensionCoefficient q B *
        (Fintype.card V + 1) ^ (j - 2 - Q.card - 1) := by
    intro Q hQ hQsmall
    have he : j - 2 - Q.card - 1 = j - Q.card - 3 := by omega
    rw [he]
    exact card_familyExtensions_absorberInduced_le_strong q j B Q hQ hQsmall
  have hκ : HasExtensionBound rem (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹)
      ((2 : ℝ≥0) ^ (j - 2) * pairExactBankExtensionCoefficient q B *
        (Fintype.card V + 1 : ℝ≥0) ^ (j - c - 5)) := by
    have hz : 1 ≤ z := by dsimp only [z]; omega
    have he : z - 1 = j - c - 5 := by dsimp only [z]; omega
    simpa only [he, Nat.cast_add, Nat.cast_one] using
      omittedFamily_hasExtensionBound J R z (j - 2) (Fintype.card V + 1)
        (pairExactBankExtensionCoefficient q B) absorberInducedConfigurationsOn_fixed_card
        hR hz (by omega) hcount
  exact timedStoppedGreedy_dominatedConfigurationTail n F active D S₀ rem
    (fun S ↦ ((greedyRootedConfigurationClass J S R c).card : ℝ≥0)) c s
    (Fintype.card V + 1 : ℝ≥0)⁻¹ w
    ((2 : ℝ≥0) ^ (j - 2) * pairExactBankExtensionCoefficient q B *
      (Fintype.card V + 1 : ℝ≥0) ^ (j - c - 5)) K
    hInv₀ hchosen₀ hD hw hK hfloor hratio
    (fun S hS ↦ greedyRootedConfigurationClass_card_le_selectedCount R c (j - 2) hS
      absorberInducedConfigurationsOn_fixed_card) hcard hκ hcut

end

end Erdos207
