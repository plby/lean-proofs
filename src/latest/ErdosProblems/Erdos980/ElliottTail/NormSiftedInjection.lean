/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos980.ElliottTail.RayNormPrimeSieve

/-!
# Injecting finite surviving fibres into a norm-sifted mass

This file isolates the elementary final bridge used by each odd-prime
correction fibre.  An injective family of candidates, each of unit weight
and avoiding every selected sieve prime in its conductor norm, contributes
at least its cardinality to the literal norm-sifted mass.
-/

open scoped BigOperators NumberField

noncomputable section

namespace Erdos980.ElliottTail.NormSiftedInjection

open RayNormPrimeSieve

/-- A unit-weight injective surviving family contributes its full
cardinality to `normSiftedMass`. -/
theorem card_le_normSiftedMass_of_injection
    {K A σ : Type*} [Field K] [NumberField K]
    [DecidableEq A] [DecidableEq σ]
    (D : Data K A) (S : Finset σ) (enc : σ → A)
    (hinj : Set.InjOn enc S)
    (hmem : ∀ s ∈ S, enc s ∈ D.candidates)
    (hweight : ∀ s ∈ S, D.weight (enc s) = 1)
    (hsurvive : ∀ s ∈ S, ∀ q ∈ D.sievePrimes,
      ¬q ∣ D.conductorNorm (enc s)) :
    (S.card : ℝ) ≤ normSiftedMass D := by
  classical
  let g : A → ℝ := fun a ↦
    if ∀ q ∈ D.sievePrimes, ¬q ∣ D.conductorNorm a
    then D.weight a else 0
  have himageCard : (S.image enc).card = S.card :=
    Finset.card_image_iff.mpr hinj
  have himage : S.image enc ⊆ D.candidates := by
    intro a ha
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ha
    exact hmem s hs
  have hg_one : ∀ a ∈ S.image enc, g a = 1 := by
    intro a ha
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ha
    dsimp only [g]
    rw [if_pos (hsurvive s hs), hweight s hs]
  have hg_nonneg : ∀ a ∈ D.candidates, a ∉ S.image enc → 0 ≤ g a := by
    intro a ha _
    dsimp only [g]
    split_ifs
    · exact D.weight_nonneg a ha
    · exact le_rfl
  calc
    (S.card : ℝ) = ((S.image enc).card : ℝ) := by rw [himageCard]
    _ = ∑ a ∈ S.image enc, g a := by
      calc
        ((S.image enc).card : ℝ) =
            ∑ _a ∈ S.image enc, (1 : ℝ) := by simp
        _ = ∑ a ∈ S.image enc, g a := by
          apply Finset.sum_congr rfl
          intro a ha
          exact (hg_one a ha).symm
    _ ≤ ∑ a ∈ D.candidates, g a :=
      Finset.sum_le_sum_of_subset_of_nonneg himage hg_nonneg
    _ = normSiftedMass D := rfl

end Erdos980.ElliottTail.NormSiftedInjection
