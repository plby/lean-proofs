/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ForbiddenCompletionCount
import ErdosProblems.Erdos207.WeightSystem

/-!
# Rooted threat families as weight systems

For a fixed pair `uv`, a threat witness is a forbidden configuration together
with a designated missing triangle through `uv`.  Its remainder is the set of
triangles that must already have been selected.  Thus the number of rooted
active configurations is bounded by a `selectedCount`, putting it directly
in the scope of the KSSS moment lemma formalized in `WeightSystem`.
-/

namespace Erdos207

open Finset
open scoped NNReal

/-- A forbidden configuration with a designated triangle through `uv`. -/
abbrev RootedThreatWitness
    (V : Type*) [DecidableEq V] (F : ForbiddenFamilyOn V) (u v : V) :=
  {z : TripleSystemOn V × TripleOn V //
    z.1 ∈ F ∧ z.2 ∈ z.1 ∧ u ∈ z.2.1 ∧ v ∈ z.2.1}

noncomputable instance instFintypeRootedThreatWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (u v : V) :
    Fintype (RootedThreatWitness V F u v) := by
  classical
  exact Fintype.ofFinite _

/-- The already-selected part of a rooted threat witness. -/
def rootedThreatRemainder
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V} {u v : V}
    (z : RootedThreatWitness V F u v) : TripleSystemOn V :=
  z.1.1.erase z.1.2

/-- Rooted witnesses whose remainder is contained in the chosen family. -/
noncomputable def activeRootedThreatWitnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V) (u v : V) :
    Finset (RootedThreatWitness V F u v) := by
  classical
  exact univ.filter fun z ↦ rootedThreatRemainder z ⊆ P

@[simp]
lemma mem_activeRootedThreatWitnesses_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P : TripleSystemOn V} {u v : V}
    {z : RootedThreatWitness V F u v} :
    z ∈ activeRootedThreatWitnesses F P u v ↔
      rootedThreatRemainder z ⊆ P := by
  classical
  simp [activeRootedThreatWitnesses]

/-- Forgetting the designated missing triangle maps the active witness family
onto the rooted active configuration family. -/
lemma image_activeRootedThreatWitnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V) (u v : V) :
    (activeRootedThreatWitnesses F P u v).image (fun z ↦ z.1.1) =
      rootedActiveForbiddenConfigurations F P u v := by
  classical
  ext S
  constructor
  · intro hS
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hS
    have hrem := mem_activeRootedThreatWitnesses_iff.mp hz
    exact mem_rootedActiveForbiddenConfigurations_iff.mpr
      ⟨z.2.1, z.1.2, z.2.2.1, z.2.2.2.1, z.2.2.2.2, hrem⟩
  · intro hS
    obtain ⟨hSF, T, hTS, huT, hvT, hrem⟩ :=
      mem_rootedActiveForbiddenConfigurations_iff.mp hS
    let z : RootedThreatWitness V F u v :=
      ⟨(S, T), hSF, hTS, huT, hvT⟩
    apply mem_image.mpr
    exact ⟨z, mem_activeRootedThreatWitnesses_iff.mpr hrem, rfl⟩

lemma card_rootedActiveForbiddenConfigurations_le_witnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P : TripleSystemOn V} {u v : V} :
    (rootedActiveForbiddenConfigurations F P u v).card ≤
      (activeRootedThreatWitnesses F P u v).card := by
  rw [← image_activeRootedThreatWitnesses]
  exact card_image_le

/-- The weight-system count of selected remainders is exactly the cardinality
of active rooted witnesses. -/
lemma selectedCount_rootedThreatRemainder
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V) (u v : V) :
    selectedCount
      (fun z : RootedThreatWitness V F u v ↦ rootedThreatRemainder z) P =
      (activeRootedThreatWitnesses F P u v).card := by
  classical
  unfold selectedCount activeRootedThreatWitnesses
  simp only [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter]
  apply Finset.sum_congr rfl
  intro z _hz
  by_cases h : rootedThreatRemainder z ⊆ P <;> simp [h]

/-- Pointwise domination of rooted active configurations by their weighted
witness count. -/
lemma rootedActive_count_le_selectedCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V) (u v : V) :
    ((rootedActiveForbiddenConfigurations F P u v).card : ℝ≥0) ≤
      selectedCount
        (fun z : RootedThreatWitness V F u v ↦ rootedThreatRemainder z) P := by
  rw [selectedCount_rootedThreatRemainder]
  exact_mod_cast
    card_rootedActiveForbiddenConfigurations_le_witnesses

/-- If forbidden configurations have at most `k` triangles, every rooted
threat remainder has at most `k-1` triangles. -/
lemma card_rootedThreatRemainder_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {u v : V} {k : ℕ}
    (hcard : ∀ S ∈ F, S.card ≤ k)
    (z : RootedThreatWitness V F u v) :
    (rootedThreatRemainder z).card ≤ k - 1 := by
  rw [rootedThreatRemainder, card_erase_of_mem z.2.2.1]
  have := hcard z.1.1 z.2.1
  omega

/-- Moment estimate for the number of rooted active forbidden
configurations.  All probabilistic information is isolated in `hjoint`, and
all combinatorial well-spreadness information in the extension bound `hκ`. -/
theorem rootedActiveMomentBound
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (R : Ω → TripleSystemOn V)
    (F : ForbiddenFamilyOn V) (u v : V)
    (π : TripleOn V → ℝ≥0) (C κ : ℝ≥0) {k s : ℕ}
    (hcard : ∀ S ∈ F, S.card ≤ k)
    (hκ : HasExtensionBound
      (fun z : RootedThreatWitness V F u v ↦ rootedThreatRemainder z)
      π κ)
    (hjoint : ∀ T : TripleSystemOn V, T.card ≤ s * (k - 1) →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ C * setWeight π T) :
    L.expectation (fun ω ↦
      ((rootedActiveForbiddenConfigurations F (R ω) u v).card : ℝ≥0) ^ s) ≤
      C * (((2 : ℝ≥0) ^ (s * (k - 1)) * κ) ^ s) := by
  calc
    L.expectation (fun ω ↦
        ((rootedActiveForbiddenConfigurations F (R ω) u v).card : ℝ≥0) ^ s) ≤
        L.expectation (fun ω ↦
          (selectedCount
            (fun z : RootedThreatWitness V F u v ↦ rootedThreatRemainder z)
            (R ω)) ^ s) := by
      apply FiniteLaw.expectation_mono
      intro ω
      exact pow_le_pow_left' (rootedActive_count_le_selectedCount
        F (R ω) u v) s
    _ ≤ C * (((2 : ℝ≥0) ^ (s * (k - 1)) * κ) ^ s) := by
      apply configurationMomentBound L
        (fun z : RootedThreatWitness V F u v ↦ rootedThreatRemainder z)
        R π C κ
      · exact card_rootedThreatRemainder_le hcard
      · exact hκ
      · exact hjoint

/-- First-moment rooted-threat estimate using only the empty-root extension
weight.  This is the density-sensitive form needed in the vortex induction:
the much coarser extension bound above arbitrary roots is unnecessary for a
single Markov moment. -/
theorem rootedActiveExpectationBound_of_empty
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (R : Ω → TripleSystemOn V)
    (F : ForbiddenFamilyOn V) (u v : V)
    (π : TripleOn V → ℝ≥0) (C κ : ℝ≥0) {k : ℕ}
    (hcard : ∀ S ∈ F, S.card ≤ k)
    (hκ : extensionWeight
      (fun z : RootedThreatWitness V F u v ↦ rootedThreatRemainder z)
      π (∅ : TripleSystemOn V) ≤ κ)
    (hjoint : ∀ T : TripleSystemOn V, T.card ≤ k - 1 →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ C * setWeight π T) :
    L.expectation (fun ω ↦
      ((rootedActiveForbiddenConfigurations F (R ω) u v).card : ℝ≥0)) ≤
      C * κ := by
  calc
    L.expectation (fun ω ↦
        ((rootedActiveForbiddenConfigurations F (R ω) u v).card : ℝ≥0)) ≤
        L.expectation (fun ω ↦
          selectedCount
            (fun z : RootedThreatWitness V F u v ↦ rootedThreatRemainder z)
            (R ω)) := by
      apply FiniteLaw.expectation_mono
      intro ω
      exact rootedActive_count_le_selectedCount F (R ω) u v
    _ ≤ C * κ := by
      exact expectation_selectedCount_le_of_empty_extensionWeight L
        (fun z : RootedThreatWitness V F u v ↦ rootedThreatRemainder z)
        R π C κ (card_rootedThreatRemainder_le hcard) hκ hjoint

/-- Markov consequence of the empty-root first-moment estimate. -/
theorem rootedActive_probability_ge_le_of_empty
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (R : Ω → TripleSystemOn V)
    (F : ForbiddenFamilyOn V) (u v : V)
    (π : TripleOn V → ℝ≥0) (C κ a : ℝ≥0) {k : ℕ}
    (ha : 0 < a)
    (hcard : ∀ S ∈ F, S.card ≤ k)
    (hκ : extensionWeight
      (fun z : RootedThreatWitness V F u v ↦ rootedThreatRemainder z)
      π (∅ : TripleSystemOn V) ≤ κ)
    (hjoint : ∀ T : TripleSystemOn V, T.card ≤ k - 1 →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ C * setWeight π T) :
    L.probability (fun ω ↦
      a ≤ (rootedActiveForbiddenConfigurations F (R ω) u v).card) ≤
      (C * κ) / a := by
  have hmarkov := L.probability_le_expectation_div
    (fun ω ↦
      ((rootedActiveForbiddenConfigurations F (R ω) u v).card : ℝ≥0)) ha
  exact hmarkov.trans ((div_le_div_iff_of_pos_right ha).2
    (rootedActiveExpectationBound_of_empty L R F u v π C κ hcard hκ hjoint))

/-- Markov consequence of `rootedActiveMomentBound`. -/
theorem rootedActive_probability_ge_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (R : Ω → TripleSystemOn V)
    (F : ForbiddenFamilyOn V) (u v : V)
    (π : TripleOn V → ℝ≥0) (C κ a : ℝ≥0) {k s : ℕ}
    (ha : 0 < a)
    (hcard : ∀ S ∈ F, S.card ≤ k)
    (hκ : HasExtensionBound
      (fun z : RootedThreatWitness V F u v ↦ rootedThreatRemainder z)
      π κ)
    (hjoint : ∀ T : TripleSystemOn V, T.card ≤ s * (k - 1) →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ C * setWeight π T) :
    L.probability (fun ω ↦
      a ≤ (rootedActiveForbiddenConfigurations F (R ω) u v).card) ≤
      (C * (((2 : ℝ≥0) ^ (s * (k - 1)) * κ) ^ s)) / a ^ s := by
  have hmono : L.probability (fun ω ↦
      a ≤ (rootedActiveForbiddenConfigurations F (R ω) u v).card) ≤
      L.probability (fun ω ↦
        a ^ s ≤
          ((rootedActiveForbiddenConfigurations F (R ω) u v).card : ℝ≥0) ^ s) := by
    apply L.probability_mono
    intro ω hω
    exact pow_le_pow_left' hω s
  refine hmono.trans ?_
  have hmarkov := L.probability_le_expectation_div
    (fun ω ↦
      ((rootedActiveForbiddenConfigurations F (R ω) u v).card : ℝ≥0) ^ s)
    (pow_pos ha s)
  exact hmarkov.trans ((div_le_div_iff_of_pos_right (pow_pos ha s)).2
    (rootedActiveMomentBound L R F u v π C κ hcard hκ hjoint))

end Erdos207
