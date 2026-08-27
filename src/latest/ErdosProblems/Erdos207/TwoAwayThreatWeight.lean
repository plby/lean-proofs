/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyDeletionObstruction
import ErdosProblems.Erdos207.WeightSystem

/-!
# Two-away forbidden configurations as a weight system

Fixing a triangle `U`, a witness consists of a forbidden configuration and
a distinct second missing triangle `T`, both contained in that
configuration.  The remainder must already be selected.  This is exactly
the second deletion class isolated in `GreedyDeletionObstruction`.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- A forbidden configuration with two designated distinct missing
triangles, one of which is the fixed triangle `U`. -/
abbrev TwoAwayThreatWitness
    (V : Type*) [DecidableEq V] (F : ForbiddenFamilyOn V)
    (U : TripleOn V) :=
  {z : TripleSystemOn V × TripleOn V //
    z.1 ∈ F ∧ z.2 ∈ z.1 ∧ U ∈ z.1 ∧ z.2 ≠ U}

noncomputable instance instFintypeTwoAwayThreatWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (U : TripleOn V) :
    Fintype (TwoAwayThreatWitness V F U) := by
  classical
  exact Fintype.ofFinite _

/-- The part of a two-away witness which must already be selected. -/
def twoAwayThreatRemainder
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V}
    {U : TripleOn V} (z : TwoAwayThreatWitness V F U) :
    TripleSystemOn V :=
  (z.1.1.erase z.1.2).erase U

/-- Active two-away witnesses over a selected family. -/
def activeTwoAwayThreatWitnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V) (U : TripleOn V) :
    Finset (TwoAwayThreatWitness V F U) :=
  (univ : Finset (TwoAwayThreatWitness V F U)).filter fun z ↦
    twoAwayThreatRemainder z ⊆ P

@[simp]
lemma mem_activeTwoAwayThreatWitnesses_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P : TripleSystemOn V} {U : TripleOn V}
    {z : TwoAwayThreatWitness V F U} :
    z ∈ activeTwoAwayThreatWitnesses F P U ↔
      twoAwayThreatRemainder z ⊆ P := by
  classical
  simp [activeTwoAwayThreatWitnesses]

/-- Forgetting the forbidden configuration maps active witnesses onto the
two-away deletion family. -/
lemma image_activeTwoAwayThreatWitnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V) (U : TripleOn V) :
    (activeTwoAwayThreatWitnesses F P U).image (fun z ↦ z.1.2) =
      twoAwayForbiddenTriangles F P U := by
  classical
  ext T
  constructor
  · intro hT
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hT
    exact mem_twoAwayForbiddenTriangles_iff.mpr
      ⟨z.2.2.2.2, z.1.1, z.2.1, z.2.2.1, z.2.2.2.1,
        mem_activeTwoAwayThreatWitnesses_iff.mp hz⟩
  · intro hT
    obtain ⟨hTU, C, hCF, hTC, hUC, hrem⟩ :=
      mem_twoAwayForbiddenTriangles_iff.mp hT
    let z : TwoAwayThreatWitness V F U :=
      ⟨(C, T), hCF, hTC, hUC, hTU⟩
    exact mem_image.mpr
      ⟨z, mem_activeTwoAwayThreatWitnesses_iff.mpr hrem, rfl⟩

lemma card_twoAwayForbiddenTriangles_le_witnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P : TripleSystemOn V} {U : TripleOn V} :
    (twoAwayForbiddenTriangles F P U).card ≤
      (activeTwoAwayThreatWitnesses F P U).card := by
  rw [← image_activeTwoAwayThreatWitnesses]
  exact card_image_le

/-- The weight-system count is the exact number of active two-away
witnesses. -/
lemma selectedCount_twoAwayThreatRemainder
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V) (U : TripleOn V) :
    selectedCount
      (fun z : TwoAwayThreatWitness V F U ↦ twoAwayThreatRemainder z) P =
      ((activeTwoAwayThreatWitnesses F P U).card : ℝ≥0) := by
  classical
  unfold selectedCount activeTwoAwayThreatWitnesses
  simp only [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter]
  apply Finset.sum_congr rfl
  intro z _hz
  by_cases h : twoAwayThreatRemainder z ⊆ P <;> simp [h]

/-- The actual two-away deletion count is dominated by its witness count. -/
lemma twoAwayForbidden_count_le_selectedCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V) (U : TripleOn V) :
    ((twoAwayForbiddenTriangles F P U).card : ℝ≥0) ≤
      selectedCount
        (fun z : TwoAwayThreatWitness V F U ↦ twoAwayThreatRemainder z) P := by
  rw [selectedCount_twoAwayThreatRemainder]
  exact_mod_cast card_twoAwayForbiddenTriangles_le_witnesses

/-- Two distinct designated members reduce the remainder size by two. -/
lemma card_twoAwayThreatRemainder_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {U : TripleOn V} {k : ℕ}
    (hcard : ∀ C ∈ F, C.card ≤ k)
    (z : TwoAwayThreatWitness V F U) :
    (twoAwayThreatRemainder z).card ≤ k - 2 := by
  have hUerase : U ∈ z.1.1.erase z.1.2 :=
    mem_erase.mpr ⟨z.2.2.2.2.symm, z.2.2.2.1⟩
  rw [twoAwayThreatRemainder, card_erase_of_mem hUerase,
    card_erase_of_mem z.2.2.1]
  have hzcard := hcard z.1.1 z.2.1
  omega

/-- Moment estimate for one fixed selected triangle's two-away deletion
count.  Probabilistic and combinatorial inputs remain explicitly separated. -/
theorem twoAwayForbiddenMomentBound
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (R : Ω → TripleSystemOn V)
    (F : ForbiddenFamilyOn V) (U : TripleOn V)
    (π : TripleOn V → ℝ≥0) (C κ : ℝ≥0) {k s : ℕ}
    (hcard : ∀ A ∈ F, A.card ≤ k)
    (hκ : HasExtensionBound
      (fun z : TwoAwayThreatWitness V F U ↦ twoAwayThreatRemainder z)
      π κ)
    (hjoint : ∀ T : TripleSystemOn V, T.card ≤ s * (k - 2) →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ C * setWeight π T) :
    L.expectation (fun ω ↦
      ((twoAwayForbiddenTriangles F (R ω) U).card : ℝ≥0) ^ s) ≤
      C * (((2 : ℝ≥0) ^ (s * (k - 2)) * κ) ^ s) := by
  calc
    L.expectation (fun ω ↦
        ((twoAwayForbiddenTriangles F (R ω) U).card : ℝ≥0) ^ s) ≤
      L.expectation (fun ω ↦
        (selectedCount
          (fun z : TwoAwayThreatWitness V F U ↦ twoAwayThreatRemainder z)
          (R ω)) ^ s) := by
        apply FiniteLaw.expectation_mono
        intro ω
        exact pow_le_pow_left'
          (twoAwayForbidden_count_le_selectedCount F (R ω) U) s
    _ ≤ C * (((2 : ℝ≥0) ^ (s * (k - 2)) * κ) ^ s) := by
      apply configurationMomentBound L
        (fun z : TwoAwayThreatWitness V F U ↦ twoAwayThreatRemainder z)
        R π C κ
      · exact card_twoAwayThreatRemainder_le hcard
      · exact hκ
      · exact hjoint

end

end Erdos207
