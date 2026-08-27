/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RootedThreatWeight

/-!
# Simultaneous extraction of rooted threat bounds

The fixed-pair moment estimate is converted by a finite union bound into one
outcome controlling every ordered pair.  Ordered pairs are used only as a
convenient finite index type; the threat family itself is symmetric in the
two endpoints.
-/

namespace Erdos207

open Finset
open scoped NNReal

/-- Ordered pairs of distinct vertices. -/
abbrev DistinctPair (V : Type*) [DecidableEq V] :=
  {p : V × V // p.1 ≠ p.2}

/-- Uniform cap on active forbidden configurations rooted at an ordered
pair. -/
def RootedActiveCapsGood
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P : TripleSystemOn V) (r : Nat) : Prop :=
  ∀ u v : V, u ≠ v →
    (rootedActiveForbiddenConfigurations F P u v).card ≤ r

/-- A union bound converts per-pair upper tails into failure probability
for the common natural-number rooted cap. -/
theorem probability_not_rootedActiveCapsGood_le
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Omega) (R : Omega -> TripleSystemOn V)
    (F : ForbiddenFamilyOn V) (r : Nat) (epsilon : NNReal)
    (hprob : ∀ e : DistinctPair V,
      L.probability (fun omega =>
        (r + 1 : NNReal) <=
          (rootedActiveForbiddenConfigurations F (R omega)
            e.1.1 e.1.2).card) <= epsilon) :
    L.probability (fun omega =>
      ¬ RootedActiveCapsGood F (R omega) r) <=
        (Fintype.card (DistinctPair V) : NNReal) * epsilon := by
  let Bad : DistinctPair V -> Omega -> Prop := fun e omega =>
    (r + 1 : NNReal) <=
      (rootedActiveForbiddenConfigurations F (R omega)
        e.1.1 e.1.2).card
  calc
    L.probability (fun omega =>
        ¬ RootedActiveCapsGood F (R omega) r) <=
        L.probability (fun omega => Exists fun e : DistinctPair V =>
          Bad e omega) := by
      apply L.probability_mono
      intro omega hbad
      unfold RootedActiveCapsGood at hbad
      push Not at hbad
      obtain ⟨u, v, huv, hlarge⟩ := hbad
      let e : DistinctPair V := ⟨(u, v), huv⟩
      refine ⟨e, ?_⟩
      dsimp only [Bad, e]
      exact_mod_cast (Nat.add_one_le_iff.mpr hlarge)
    _ <= ∑ e : DistinctPair V, L.probability (Bad e) := by
      simpa using L.probability_exists_le
        (univ : Finset (DistinctPair V)) Bad
    _ <= ∑ _e : DistinctPair V, epsilon := by
      apply sum_le_sum
      intro e he
      exact hprob e
    _ = (Fintype.card (DistinctPair V) : NNReal) * epsilon := by simp

/-- Complete moment-plus-union-bound estimate for failure of a uniform
natural-number rooted cap. -/
theorem probability_not_rootedActiveCapsGood_le_of_moment
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Omega) (R : Omega -> TripleSystemOn V)
    (F : ForbiddenFamilyOn V)
    (pi : TripleOn V -> NNReal) (C kappa : NNReal)
    (r : Nat) {k s : Nat}
    (hcard : ∀ S ∈ F, S.card ≤ k)
    (hkappa : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 =>
          rootedThreatRemainder z) pi kappa)
    (hjoint : ∀ T : TripleSystemOn V, T.card ≤ s * (k - 1) →
      L.probability (fun omega => T ⊆ R omega) ≤ C * setWeight pi T) :
    L.probability (fun omega =>
      ¬ RootedActiveCapsGood F (R omega) r) <=
      (Fintype.card (DistinctPair V) : NNReal) *
        ((C * (((2 : NNReal) ^ (s * (k - 1)) * kappa) ^ s)) /
          (r + 1 : NNReal) ^ s) := by
  apply probability_not_rootedActiveCapsGood_le L R F r
  intro e
  exact rootedActive_probability_ge_le L R F e.1.1 e.1.2
    pi C kappa (r + 1) (by positivity) hcard (hkappa e) hjoint

/-- The simultaneous rooted-cap failure estimate obtained from the sharp
first moment.  Only the empty-root extension weight is required for each
ordered vertex pair. -/
theorem probability_not_rootedActiveCapsGood_le_of_firstMoment
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Omega) (R : Omega → TripleSystemOn V)
    (F : ForbiddenFamilyOn V)
    (pi : TripleOn V → ℝ≥0) (C kappa : ℝ≥0)
    (r : ℕ) {k : ℕ}
    (hcard : ∀ S ∈ F, S.card ≤ k)
    (hkappa : ∀ e : DistinctPair V,
      extensionWeight
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 ↦
          rootedThreatRemainder z) pi (∅ : TripleSystemOn V) ≤ kappa)
    (hjoint : ∀ T : TripleSystemOn V, T.card ≤ k - 1 →
      L.probability (fun omega ↦ T ⊆ R omega) ≤ C * setWeight pi T) :
    L.probability (fun omega ↦
      ¬ RootedActiveCapsGood F (R omega) r) ≤
      (Fintype.card (DistinctPair V) : ℝ≥0) *
        ((C * kappa) / (r + 1 : ℝ≥0)) := by
  apply probability_not_rootedActiveCapsGood_le L R F r
  intro e
  exact rootedActive_probability_ge_le_of_empty L R F e.1.1 e.1.2
    pi C kappa (r + 1) (by positivity) hcard (hkappa e) hjoint

/-- A uniform probability bound for every rooted pair yields one outcome
where every rooted active count is below the common threshold. -/
theorem exists_all_rootedActive_lt_of_probability_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (R : Ω → TripleSystemOn V)
    (F : ForbiddenFamilyOn V) (a ε : ℝ≥0)
    (hprob : ∀ e : DistinctPair V,
      L.probability (fun ω ↦
        a ≤ (rootedActiveForbiddenConfigurations
          F (R ω) e.1.1 e.1.2).card) ≤ ε)
    (hsmall : (Fintype.card (DistinctPair V) : ℝ≥0) * ε < 1) :
    ∃ ω, ∀ e : DistinctPair V,
      ((rootedActiveForbiddenConfigurations
        F (R ω) e.1.1 e.1.2).card : ℝ≥0) < a := by
  let bad : DistinctPair V → Ω → Prop := fun e ω ↦
    a ≤ (rootedActiveForbiddenConfigurations
      F (R ω) e.1.1 e.1.2).card
  have hsum : ∑ e : DistinctPair V, L.probability (bad e) < 1 := by
    calc
      ∑ e : DistinctPair V, L.probability (bad e) ≤
          ∑ _e : DistinctPair V, ε := by
        apply sum_le_sum
        intro e _he
        exact hprob e
      _ = (Fintype.card (DistinctPair V) : ℝ≥0) * ε := by simp
      _ < 1 := hsmall
  obtain ⟨ω, hω⟩ := L.exists_avoiding_of_sum_probability_lt_one
    (univ : Finset (DistinctPair V)) bad (by simpa using hsum)
  refine ⟨ω, ?_⟩
  intro e
  exact lt_of_not_ge (hω e (mem_univ e))

/-- Complete finite moment-plus-union-bound extraction theorem. -/
theorem exists_all_rootedActive_lt_of_moment
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Ω) (R : Ω → TripleSystemOn V)
    (F : ForbiddenFamilyOn V)
    (π : TripleOn V → ℝ≥0) (C κ a : ℝ≥0) {k s : ℕ}
    (ha : 0 < a)
    (hcard : ∀ S ∈ F, S.card ≤ k)
    (hκ : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 ↦
          rootedThreatRemainder z) π κ)
    (hjoint : ∀ T : TripleSystemOn V, T.card ≤ s * (k - 1) →
      L.probability (fun ω ↦ T ⊆ R ω) ≤ C * setWeight π T)
    (hsmall : (Fintype.card (DistinctPair V) : ℝ≥0) *
      ((C * (((2 : ℝ≥0) ^ (s * (k - 1)) * κ) ^ s)) / a ^ s) < 1) :
    ∃ ω, ∀ e : DistinctPair V,
      ((rootedActiveForbiddenConfigurations
        F (R ω) e.1.1 e.1.2).card : ℝ≥0) < a := by
  apply exists_all_rootedActive_lt_of_probability_le L R F a
    ((C * (((2 : ℝ≥0) ^ (s * (k - 1)) * κ) ^ s)) / a ^ s)
  · intro e
    exact rootedActive_probability_ge_le L R F e.1.1 e.1.2
      π C κ a ha hcard (hκ e) hjoint
  · exact hsmall

end Erdos207
