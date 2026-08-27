/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedRootedBlocker
import ErdosProblems.Erdos207.RootedThreatWeight

/-!
# Rooted threat weights localized to a third-vertex set

The internal cover of an outside pair `uv` only tests triangles whose third
vertex belongs to the next vortex level.  The witness family in this file
records that restriction before applying the generic configuration-moment
lemma.  This prevents the irrelevant ambient choices of a missing third
vertex from entering the obstruction count.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- A rooted threat witness whose designated missing triangle has a third
vertex in `U`. -/
abbrev LocalizedRootedThreatWitness
    (V : Type*) [DecidableEq V] (F : ForbiddenFamilyOn V)
    (u v : V) (U : Finset V) :=
  {z : RootedThreatWitness V F u v //
    ∃ w ∈ (z.1.2 : Finset V), w ∈ U ∧ w ≠ u ∧ w ≠ v}

noncomputable instance instFintypeLocalizedRootedThreatWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (u v : V) (U : Finset V) :
    Fintype (LocalizedRootedThreatWitness V F u v U) := by
  classical
  exact Fintype.ofFinite _

/-- The already-selected part of a localized witness. -/
def localizedRootedThreatRemainder
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V}
    {u v : V} {U : Finset V}
    (z : LocalizedRootedThreatWitness V F u v U) : TripleSystemOn V :=
  rootedThreatRemainder z.1

/-- Localized witnesses whose remainders have already been selected. -/
noncomputable def activeLocalizedRootedThreatWitnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (u v : V) (U : Finset V) :
    Finset (LocalizedRootedThreatWitness V F u v U) := by
  classical
  exact univ.filter fun z ↦ localizedRootedThreatRemainder z ⊆ P

@[simp]
lemma mem_activeLocalizedRootedThreatWitnesses_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P : TripleSystemOn V}
    {u v : V} {U : Finset V}
    {z : LocalizedRootedThreatWitness V F u v U} :
    z ∈ activeLocalizedRootedThreatWitnesses F P u v U ↔
      localizedRootedThreatRemainder z ⊆ P := by
  classical
  simp [activeLocalizedRootedThreatWitnesses]

/-- Forgetting the designated triangle maps localized active witnesses onto
the localized active configuration family. -/
lemma image_activeLocalizedRootedThreatWitnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (u v : V) (U : Finset V) :
    (activeLocalizedRootedThreatWitnesses F P u v U).image
        (fun z ↦ z.1.1.1) =
      rootedActiveForbiddenConfigurationsIn F P u v U := by
  classical
  ext C
  constructor
  · intro hC
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hC
    have hrem := mem_activeLocalizedRootedThreatWitnesses_iff.mp hz
    exact mem_rootedActiveForbiddenConfigurationsIn_iff.mpr
      ⟨z.1.2.1, z.1.1.2, z.1.2.2.1,
        z.1.2.2.2.1, z.1.2.2.2.2, z.2, hrem⟩
  · intro hC
    obtain ⟨hCF, T, hTC, huT, hvT, hthird, hrem⟩ :=
      mem_rootedActiveForbiddenConfigurationsIn_iff.mp hC
    let z : RootedThreatWitness V F u v :=
      ⟨(C, T), hCF, hTC, huT, hvT⟩
    let zU : LocalizedRootedThreatWitness V F u v U := ⟨z, hthird⟩
    apply mem_image.mpr
    refine ⟨zU, mem_activeLocalizedRootedThreatWitnesses_iff.mpr ?_, rfl⟩
    change C.erase T ⊆ P
    exact hrem

lemma card_rootedActiveForbiddenConfigurationsIn_le_witnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P : TripleSystemOn V}
    {u v : V} {U : Finset V} :
    (rootedActiveForbiddenConfigurationsIn F P u v U).card ≤
      (activeLocalizedRootedThreatWitnesses F P u v U).card := by
  rw [← image_activeLocalizedRootedThreatWitnesses]
  exact card_image_le

/-- The generic selected-count of localized remainders is exactly the number
of active localized witnesses. -/
lemma selectedCount_localizedRootedThreatRemainder
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (u v : V) (U : Finset V) :
    selectedCount
        (fun z : LocalizedRootedThreatWitness V F u v U ↦
          localizedRootedThreatRemainder z) P =
      (activeLocalizedRootedThreatWitnesses F P u v U).card := by
  classical
  unfold selectedCount activeLocalizedRootedThreatWitnesses
  simp only [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter]
  apply Finset.sum_congr rfl
  intro z _hz
  by_cases h : localizedRootedThreatRemainder z ⊆ P <;> simp [h]

/-- Pointwise domination of the localized active-configuration count by its
witness selected-count. -/
lemma rootedActiveIn_count_le_selectedCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (u v : V) (U : Finset V) :
    ((rootedActiveForbiddenConfigurationsIn F P u v U).card : ℝ≥0) ≤
      selectedCount
        (fun z : LocalizedRootedThreatWitness V F u v U ↦
          localizedRootedThreatRemainder z) P := by
  rw [selectedCount_localizedRootedThreatRemainder]
  exact_mod_cast
    card_rootedActiveForbiddenConfigurationsIn_le_witnesses

/-- Every localized rooted remainder inherits the usual `k-1` cardinality
bound. -/
lemma card_localizedRootedThreatRemainder_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {u v : V} {U : Finset V} {k : ℕ}
    (hcard : ∀ C ∈ F, C.card ≤ k)
    (z : LocalizedRootedThreatWitness V F u v U) :
    (localizedRootedThreatRemainder z).card ≤ k - 1 :=
  card_rootedThreatRemainder_le hcard z.1

/-- Generic moment estimate for the localized rooted count.  The new
combinatorial input is an extension bound for the localized witness family. -/
theorem rootedActiveInMomentBound
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (R : Ω → TripleSystemOn V)
    (F : ForbiddenFamilyOn V) (u v : V) (U : Finset V)
    (π : TripleOn V → ℝ≥0) (C κ : ℝ≥0) {k s : ℕ}
    (hcard : ∀ S ∈ F, S.card ≤ k)
    (hκ : HasExtensionBound
      (fun z : LocalizedRootedThreatWitness V F u v U ↦
        localizedRootedThreatRemainder z) π κ)
    (hjoint : ∀ T : TripleSystemOn V, T.card ≤ s * (k - 1) →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ C * setWeight π T) :
    L.expectation (fun ω ↦
      ((rootedActiveForbiddenConfigurationsIn F (R ω) u v U).card :
        ℝ≥0) ^ s) ≤
      C * (((2 : ℝ≥0) ^ (s * (k - 1)) * κ) ^ s) := by
  calc
    L.expectation (fun ω ↦
        ((rootedActiveForbiddenConfigurationsIn F (R ω) u v U).card :
          ℝ≥0) ^ s) ≤
        L.expectation (fun ω ↦
          (selectedCount
            (fun z : LocalizedRootedThreatWitness V F u v U ↦
              localizedRootedThreatRemainder z) (R ω)) ^ s) := by
      apply FiniteLaw.expectation_mono
      intro ω
      exact pow_le_pow_left' (rootedActiveIn_count_le_selectedCount
        F (R ω) u v U) s
    _ ≤ C * (((2 : ℝ≥0) ^ (s * (k - 1)) * κ) ^ s) := by
      apply configurationMomentBound L
        (fun z : LocalizedRootedThreatWitness V F u v U ↦
          localizedRootedThreatRemainder z) R π C κ
      · exact card_localizedRootedThreatRemainder_le hcard
      · exact hκ
      · exact hjoint

/-- The localized first moment only needs the extension weight above the
empty planted root. -/
theorem rootedActiveInExpectationBound_of_empty
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (R : Ω → TripleSystemOn V)
    (F : ForbiddenFamilyOn V) (u v : V) (U : Finset V)
    (π : TripleOn V → ℝ≥0) (C κ : ℝ≥0) {k : ℕ}
    (hcard : ∀ S ∈ F, S.card ≤ k)
    (hκ : extensionWeight
      (fun z : LocalizedRootedThreatWitness V F u v U ↦
        localizedRootedThreatRemainder z)
      π (∅ : TripleSystemOn V) ≤ κ)
    (hjoint : ∀ T : TripleSystemOn V, T.card ≤ k - 1 →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ C * setWeight π T) :
    L.expectation (fun ω ↦
      ((rootedActiveForbiddenConfigurationsIn F (R ω) u v U).card :
        ℝ≥0)) ≤ C * κ := by
  calc
    L.expectation (fun ω ↦
        ((rootedActiveForbiddenConfigurationsIn F (R ω) u v U).card :
          ℝ≥0)) ≤
        L.expectation (fun ω ↦ selectedCount
          (fun z : LocalizedRootedThreatWitness V F u v U ↦
            localizedRootedThreatRemainder z) (R ω)) := by
      apply FiniteLaw.expectation_mono
      intro ω
      exact rootedActiveIn_count_le_selectedCount F (R ω) u v U
    _ ≤ C * κ := by
      exact expectation_selectedCount_le_of_empty_extensionWeight L
        (fun z : LocalizedRootedThreatWitness V F u v U ↦
          localizedRootedThreatRemainder z)
        R π C κ (card_localizedRootedThreatRemainder_le hcard) hκ hjoint

/-- Markov's inequality for the localized empty-root first moment. -/
theorem rootedActiveIn_probability_ge_le_of_empty
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (R : Ω → TripleSystemOn V)
    (F : ForbiddenFamilyOn V) (u v : V) (U : Finset V)
    (π : TripleOn V → ℝ≥0) (C κ a : ℝ≥0) {k : ℕ}
    (ha : 0 < a)
    (hcard : ∀ S ∈ F, S.card ≤ k)
    (hκ : extensionWeight
      (fun z : LocalizedRootedThreatWitness V F u v U ↦
        localizedRootedThreatRemainder z)
      π (∅ : TripleSystemOn V) ≤ κ)
    (hjoint : ∀ T : TripleSystemOn V, T.card ≤ k - 1 →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ C * setWeight π T) :
    L.probability (fun ω ↦
      a ≤ (rootedActiveForbiddenConfigurationsIn F (R ω) u v U).card) ≤
      (C * κ) / a := by
  have hmarkov := L.probability_le_expectation_div
    (fun ω ↦
      ((rootedActiveForbiddenConfigurationsIn F (R ω) u v U).card :
        ℝ≥0)) ha
  exact hmarkov.trans ((div_le_div_iff_of_pos_right ha).2
    (rootedActiveInExpectationBound_of_empty L R F u v U π C κ
      hcard hκ hjoint))

/-- Markov consequence of the localized rooted moment estimate. -/
theorem rootedActiveIn_probability_ge_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (R : Ω → TripleSystemOn V)
    (F : ForbiddenFamilyOn V) (u v : V) (U : Finset V)
    (π : TripleOn V → ℝ≥0) (C κ a : ℝ≥0) {k s : ℕ}
    (ha : 0 < a)
    (hcard : ∀ S ∈ F, S.card ≤ k)
    (hκ : HasExtensionBound
      (fun z : LocalizedRootedThreatWitness V F u v U ↦
        localizedRootedThreatRemainder z) π κ)
    (hjoint : ∀ T : TripleSystemOn V, T.card ≤ s * (k - 1) →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ C * setWeight π T) :
    L.probability (fun ω ↦
      a ≤ (rootedActiveForbiddenConfigurationsIn F (R ω) u v U).card) ≤
      (C * (((2 : ℝ≥0) ^ (s * (k - 1)) * κ) ^ s)) / a ^ s := by
  have hmono : L.probability (fun ω ↦
      a ≤ (rootedActiveForbiddenConfigurationsIn F (R ω) u v U).card) ≤
      L.probability (fun ω ↦
        a ^ s ≤
          ((rootedActiveForbiddenConfigurationsIn F (R ω) u v U).card :
            ℝ≥0) ^ s) := by
    apply L.probability_mono
    intro ω hω
    exact pow_le_pow_left' hω s
  refine hmono.trans ?_
  have hmarkov := L.probability_le_expectation_div
    (fun ω ↦
      ((rootedActiveForbiddenConfigurationsIn F (R ω) u v U).card :
        ℝ≥0) ^ s) (pow_pos ha s)
  exact hmarkov.trans ((div_le_div_iff_of_pos_right (pow_pos ha s)).2
    (rootedActiveInMomentBound L R F u v U π C κ hcard hκ hjoint))

end

end Erdos207
