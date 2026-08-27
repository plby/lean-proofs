/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedRootedThreatWeight
import ErdosProblems.Erdos207.RootedThreatExtraction

/-!
# Simultaneous extraction of localized rooted caps

Only the scheduled outside pairs are charged, and each pair is charged only
for missing third vertices in its actual internal-cover candidate set.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Uniform cap on the active configurations rooted at every ordered pair,
counting only missing third vertices in `U`. -/
def RootedActiveCapsGoodIn
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (U : Finset V) (r : ℕ) : Prop :=
  ∀ u v : V, u ≠ v →
    (rootedActiveForbiddenConfigurationsIn F P u v U).card ≤ r

/-- A cap on a larger third-vertex set implies the corresponding cap on a
smaller set. -/
lemma RootedActiveCapsGoodIn.mono
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P : TripleSystemOn V}
    {U U' : Finset V} {r : ℕ}
    (hcap : RootedActiveCapsGoodIn F P U' r) (hUU' : U ⊆ U') :
    RootedActiveCapsGoodIn F P U r := by
  intro u v huv
  exact (card_le_card
    (rootedActiveForbiddenConfigurationsIn_mono hUU')).trans
      (hcap u v huv)

/-- A cap on the whole next vortex controls every scheduled extension set
contained in it. -/
lemma RootedActiveCapsGoodIn.scheduled
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P : TripleSystemOn V}
    {U : Finset V} {r : ℕ}
    (hcap : RootedActiveCapsGoodIn F P U r)
    (E : Finset (Sym2 V)) (S : Sym2 V → Finset V)
    (hne : ∀ e ∈ E, e.out.1 ≠ e.out.2)
    (hS : ∀ e ∈ E, S e ⊆ U) :
    ∀ e ∈ E,
      (rootedActiveForbiddenConfigurationsIn
        F P e.out.1 e.out.2 (S e)).card ≤ r := by
  intro e he
  exact (card_le_card
    (rootedActiveForbiddenConfigurationsIn_mono (hS e he))).trans
      (hcap e.out.1 e.out.2 (hne e he))

/-- Union bound converting a per-pair localized tail into a simultaneous
cap over all ordered distinct pairs. -/
theorem probability_not_rootedActiveCapsGoodIn_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (R : Ω → TripleSystemOn V)
    (F : ForbiddenFamilyOn V) (U : Finset V)
    (r : ℕ) (epsilon : ℝ≥0)
    (hprob : ∀ e : DistinctPair V,
      L.probability (fun ω ↦
        (r + 1 : ℝ≥0) ≤
          (rootedActiveForbiddenConfigurationsIn
            F (R ω) e.1.1 e.1.2 U).card) ≤ epsilon) :
    L.probability (fun ω ↦
      ¬ RootedActiveCapsGoodIn F (R ω) U r) ≤
        (Fintype.card (DistinctPair V) : ℝ≥0) * epsilon := by
  let Bad : DistinctPair V → Ω → Prop := fun e ω ↦
    (r + 1 : ℝ≥0) ≤
      (rootedActiveForbiddenConfigurationsIn
        F (R ω) e.1.1 e.1.2 U).card
  calc
    L.probability (fun ω ↦
        ¬ RootedActiveCapsGoodIn F (R ω) U r) ≤
        L.probability (fun ω ↦ ∃ e : DistinctPair V, Bad e ω) := by
      apply L.probability_mono
      intro ω hbad
      unfold RootedActiveCapsGoodIn at hbad
      push Not at hbad
      obtain ⟨u, v, huv, hlarge⟩ := hbad
      let e : DistinctPair V := ⟨(u, v), huv⟩
      refine ⟨e, ?_⟩
      dsimp only [Bad, e]
      exact_mod_cast (Nat.add_one_le_iff.mpr hlarge)
    _ ≤ ∑ e : DistinctPair V, L.probability (Bad e) := by
      simpa using L.probability_exists_le
        (univ : Finset (DistinctPair V)) Bad
    _ ≤ ∑ _e : DistinctPair V, epsilon := by
      apply sum_le_sum
      intro e _he
      exact hprob e
    _ = (Fintype.card (DistinctPair V) : ℝ≥0) * epsilon := by simp

/-- Moment-plus-union-bound estimate for the common fixed-vortex localized
cap event. -/
theorem probability_not_rootedActiveCapsGoodIn_le_of_moment
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (R : Ω → TripleSystemOn V)
    (F : ForbiddenFamilyOn V) (U : Finset V)
    (π : TripleOn V → ℝ≥0) (C κ : ℝ≥0)
    (r : ℕ) {k s : ℕ}
    (hcard : ∀ T ∈ F, T.card ≤ k)
    (hκ : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : LocalizedRootedThreatWitness V F e.1.1 e.1.2 U ↦
          localizedRootedThreatRemainder z) π κ)
    (hjoint : ∀ T : TripleSystemOn V, T.card ≤ s * (k - 1) →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ C * setWeight π T) :
    L.probability (fun ω ↦
      ¬ RootedActiveCapsGoodIn F (R ω) U r) ≤
      (Fintype.card (DistinctPair V) : ℝ≥0) *
        ((C * (((2 : ℝ≥0) ^ (s * (k - 1)) * κ) ^ s)) /
          (r + 1 : ℝ≥0) ^ s) := by
  apply probability_not_rootedActiveCapsGoodIn_le L R F U r
  intro e
  exact rootedActiveIn_probability_ge_le L R F e.1.1 e.1.2 U
    π C κ (r + 1) (by positivity) hcard (hκ e) hjoint

/-- First-moment version of the localized uniform-cap union bound.  It only
requires the witness extension sum above the empty planted root. -/
theorem probability_not_rootedActiveCapsGoodIn_le_of_firstMoment
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (R : Ω → TripleSystemOn V)
    (F : ForbiddenFamilyOn V) (U : Finset V)
    (π : TripleOn V → ℝ≥0) (C κ : ℝ≥0)
    (r : ℕ) {k : ℕ}
    (hcard : ∀ T ∈ F, T.card ≤ k)
    (hκ : ∀ e : DistinctPair V,
      extensionWeight
        (fun z : LocalizedRootedThreatWitness V F e.1.1 e.1.2 U ↦
          localizedRootedThreatRemainder z)
        π (∅ : TripleSystemOn V) ≤ κ)
    (hjoint : ∀ T : TripleSystemOn V, T.card ≤ k - 1 →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ C * setWeight π T) :
    L.probability (fun ω ↦
      ¬ RootedActiveCapsGoodIn F (R ω) U r) ≤
      (Fintype.card (DistinctPair V) : ℝ≥0) *
        ((C * κ) / (r + 1 : ℝ≥0)) := by
  apply probability_not_rootedActiveCapsGoodIn_le L R F U r
  intro e
  exact rootedActiveIn_probability_ge_le_of_empty L R F e.1.1 e.1.2 U
    π C κ (r + 1) (by positivity) hcard (hκ e) hjoint

/-- Uniform localized cap over a finite scheduled family of ordered pairs. -/
def LocalizedRootedActiveCapsGood
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V)
    (E : Finset (DistinctPair V))
    (S : DistinctPair V → Finset V) (r : ℕ) : Prop :=
  ∀ e ∈ E,
    (rootedActiveForbiddenConfigurationsIn
      F P e.1.1 e.1.2 (S e)).card ≤ r

/-- Union bound for a finite scheduled family of localized rooted caps. -/
theorem probability_not_localizedRootedActiveCapsGood_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (R : Ω → TripleSystemOn V)
    (F : ForbiddenFamilyOn V) (E : Finset (DistinctPair V))
    (S : DistinctPair V → Finset V) (r : ℕ) (epsilon : ℝ≥0)
    (hprob : ∀ e ∈ E,
      L.probability (fun ω ↦
        (r + 1 : ℝ≥0) ≤
          (rootedActiveForbiddenConfigurationsIn
            F (R ω) e.1.1 e.1.2 (S e)).card) ≤ epsilon) :
    L.probability (fun ω ↦
      ¬ LocalizedRootedActiveCapsGood F (R ω) E S r) ≤
        (E.card : ℝ≥0) * epsilon := by
  let Bad : DistinctPair V → Ω → Prop := fun e ω ↦
    (r + 1 : ℝ≥0) ≤
      (rootedActiveForbiddenConfigurationsIn
        F (R ω) e.1.1 e.1.2 (S e)).card
  calc
    L.probability (fun ω ↦
        ¬ LocalizedRootedActiveCapsGood F (R ω) E S r) ≤
        L.probability (fun ω ↦ ∃ e ∈ E, Bad e ω) := by
      apply L.probability_mono
      intro ω hbad
      unfold LocalizedRootedActiveCapsGood at hbad
      push_neg at hbad
      obtain ⟨e, heE, hlarge⟩ := hbad
      refine ⟨e, heE, ?_⟩
      dsimp only [Bad]
      exact_mod_cast (Nat.add_one_le_iff.mpr hlarge)
    _ ≤ ∑ e ∈ E, L.probability (Bad e) := by
      simpa using L.probability_exists_le E Bad
    _ ≤ ∑ _e ∈ E, epsilon := by
      apply sum_le_sum
      intro e he
      exact hprob e he
    _ = (E.card : ℝ≥0) * epsilon := by simp

/-- Moment-plus-union-bound estimate for the localized cap event. -/
theorem probability_not_localizedRootedActiveCapsGood_le_of_moment
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (R : Ω → TripleSystemOn V)
    (F : ForbiddenFamilyOn V) (E : Finset (DistinctPair V))
    (S : DistinctPair V → Finset V)
    (π : TripleOn V → ℝ≥0) (C κ : ℝ≥0)
    (r : ℕ) {k s : ℕ}
    (hcard : ∀ T ∈ F, T.card ≤ k)
    (hκ : ∀ e ∈ E,
      HasExtensionBound
        (fun z : LocalizedRootedThreatWitness V F e.1.1 e.1.2 (S e) ↦
          localizedRootedThreatRemainder z) π κ)
    (hjoint : ∀ T : TripleSystemOn V, T.card ≤ s * (k - 1) →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ C * setWeight π T) :
    L.probability (fun ω ↦
      ¬ LocalizedRootedActiveCapsGood F (R ω) E S r) ≤
      (E.card : ℝ≥0) *
        ((C * (((2 : ℝ≥0) ^ (s * (k - 1)) * κ) ^ s)) /
          (r + 1 : ℝ≥0) ^ s) := by
  apply probability_not_localizedRootedActiveCapsGood_le
    L R F E S r
  intro e he
  exact rootedActiveIn_probability_ge_le L R F e.1.1 e.1.2 (S e)
    π C κ (r + 1) (by positivity) hcard (hκ e he) hjoint

end

end Erdos207
