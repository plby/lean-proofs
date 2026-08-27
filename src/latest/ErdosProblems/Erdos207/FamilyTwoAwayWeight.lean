/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TwoAwayThreatWeight
import ErdosProblems.Erdos207.UniformExtensionWeight

/-!
# Removing two designated members from a fixed-size family

This file is the finite counting bridge for two-away threats.  If a
fixed-size family of configurations has extension weight `K` after one
member `U` is prescribed, then designating and removing one further member
costs at most the family size and one inverse point weight.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- A member of `G` containing `U`, together with a distinct second
designated member. -/
structure FamilyTwoAwayWitness
    {V : Type*} [DecidableEq V]
    (G : ForbiddenFamilyOn V) (U : TripleOn V) where
  family : TripleSystemOn V
  family_mem : family ∈ G
  fixed_mem : U ∈ family
  missing : TripleOn V
  missing_mem : missing ∈ family
  missing_ne : missing ≠ U

instance instFiniteFamilyTwoAwayWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : ForbiddenFamilyOn V) (U : TripleOn V) :
    Finite (FamilyTwoAwayWitness G U) :=
  Finite.of_injective
    (fun z : FamilyTwoAwayWitness G U ↦ (z.family, z.missing)) (by
      intro z w h
      cases z
      cases w
      simp_all)

noncomputable instance instFintypeFamilyTwoAwayWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : ForbiddenFamilyOn V) (U : TripleOn V) :
    Fintype (FamilyTwoAwayWitness G U) := Fintype.ofFinite _

/-- Remove both designated members. -/
def familyTwoAwayRemainder
    {V : Type*} [DecidableEq V]
    {G : ForbiddenFamilyOn V} {U : TripleOn V}
    (z : FamilyTwoAwayWitness G U) : TripleSystemOn V :=
  (z.family.erase z.missing).erase U

lemma familyTwoAwayRemainder_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : ForbiddenFamilyOn V} {U : TripleOn V} {m : ℕ}
    (hcard : ∀ S ∈ G, S.card = m)
    (z : FamilyTwoAwayWitness G U) :
    (familyTwoAwayRemainder z).card = m - 2 := by
  have hUerase : U ∈ z.family.erase z.missing :=
    mem_erase.mpr ⟨z.missing_ne.symm, z.fixed_mem⟩
  rw [familyTwoAwayRemainder, card_erase_of_mem hUerase,
    card_erase_of_mem z.missing_mem, hcard z.family z.family_mem]
  omega

/-- Witnesses whose two-away remainder contains the further root `H`. -/
abbrev ActiveFamilyTwoAwayWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : ForbiddenFamilyOn V) (U : TripleOn V) (H : TripleSystemOn V) :=
  {z : FamilyTwoAwayWitness G U // H ⊆ familyTwoAwayRemainder z}

/-- An active witness remembers a member of `G` containing `insert U H`
and one of that member's triangles. -/
def activeFamilyTwoAwayEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : ForbiddenFamilyOn V) (U : TripleOn V) (H : TripleSystemOn V) :
    ActiveFamilyTwoAwayWitness G U H ↪
      Σ S : familyExtensions G (insert U H), S.1 := by
  classical
  refine
    { toFun := fun z ↦ ⟨
        ⟨z.1.family, mem_familyExtensions_iff.mpr
          ⟨z.1.family_mem, ?_⟩⟩,
        ⟨z.1.missing, z.1.missing_mem⟩⟩
      inj' := ?_ }
  · intro T hT
    rw [mem_insert] at hT
    rcases hT with rfl | hTH
    · exact z.1.fixed_mem
    · exact mem_of_mem_erase
        (mem_of_mem_erase (z.2 hTH))
  · intro z w hzw
    have hfamily : z.1.family = w.1.family :=
      congrArg (fun x ↦ x.1.1) hzw
    have hmissing : z.1.missing = w.1.missing :=
      congrArg (fun x ↦ x.2.1) hzw
    apply Subtype.ext
    cases z with
    | mk z hz =>
      cases w with
      | mk w hw =>
        cases z
        cases w
        simp_all

/-- Active witness multiplicity is at most `m` times the number of family
extensions containing the enlarged root. -/
lemma card_activeFamilyTwoAwayWitness_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : ForbiddenFamilyOn V} {U : TripleOn V}
    (H : TripleSystemOn V) {m : ℕ}
    (hcard : ∀ S ∈ G, S.card = m) :
    Fintype.card (ActiveFamilyTwoAwayWitness G U H) ≤
      (familyExtensions G (insert U H)).card * m := by
  calc
    Fintype.card (ActiveFamilyTwoAwayWitness G U H) ≤
        Fintype.card (Σ S : familyExtensions G (insert U H), S.1) :=
      Fintype.card_le_of_embedding (activeFamilyTwoAwayEmbedding G U H)
    _ = ∑ S : familyExtensions G (insert U H), S.1.card := by simp
    _ = ∑ _S : familyExtensions G (insert U H), m := by
      apply sum_congr rfl
      intro S _hS
      exact hcard S.1 (mem_familyExtensions_iff.mp S.2).1
    _ = (familyExtensions G (insert U H)).card * m := by simp

/-- Exact constant-weight formula for the indexed two-away witness family. -/
lemma extensionWeight_familyTwoAway_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : ForbiddenFamilyOn V} {U : TripleOn V} {m : ℕ}
    (hcard : ∀ S ∈ G, S.card = m)
    (p : ℝ≥0) (H : TripleSystemOn V) :
    extensionWeight
        (fun z : FamilyTwoAwayWitness G U ↦ familyTwoAwayRemainder z)
        (constantTripleWeight p) H =
      (Fintype.card (ActiveFamilyTwoAwayWitness G U H) : ℝ≥0) *
        p ^ (m - 2 - H.card) := by
  classical
  unfold extensionWeight
  calc
    (∑ z : FamilyTwoAwayWitness G U,
        if H ⊆ familyTwoAwayRemainder z then
          setWeight (constantTripleWeight p)
            (familyTwoAwayRemainder z \ H) else 0) =
      ∑ z : FamilyTwoAwayWitness G U,
        if H ⊆ familyTwoAwayRemainder z then
          p ^ (m - 2 - H.card) else 0 := by
        apply sum_congr rfl
        intro z _hz
        by_cases hH : H ⊆ familyTwoAwayRemainder z
        · rw [if_pos hH, if_pos hH,
            setWeight_constantTripleWeight,
            card_sdiff_of_subset hH,
            familyTwoAwayRemainder_card hcard]
        · simp [hH]
    _ = (Fintype.card (ActiveFamilyTwoAwayWitness G U H) : ℝ≥0) *
        p ^ (m - 2 - H.card) := by
      rw [Fintype.card_subtype]
      rw [← Finset.sum_filter]
      simp

/-- At inverse ambient weight, deleting the second designated member costs
at most `m (|V|+1)` relative to prescribing the first one. -/
theorem extensionWeight_familyTwoAway_le_enlargedRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : ForbiddenFamilyOn V} {U : TripleOn V} {m : ℕ}
    (hcard : ∀ S ∈ G, S.card = m) (H : TripleSystemOn V) :
    extensionWeight
        (fun z : FamilyTwoAwayWitness G U ↦ familyTwoAwayRemainder z)
        (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹)) H ≤
      (m * (Fintype.card V + 1) : ℕ) *
        extensionWeight (fun S : G ↦ S.1)
          (constantTripleWeight ((Fintype.card V + 1 : ℝ≥0)⁻¹))
          (insert U H) := by
  classical
  rw [extensionWeight_familyTwoAway_eq hcard]
  change _ ≤ ((m * (Fintype.card V + 1) : ℕ) : ℝ≥0) *
    extensionWeight (fun S : G ↦ S.1)
      (fun _ ↦ (Fintype.card V + 1 : ℝ≥0)⁻¹) (insert U H)
  rw [extensionWeight_constant_eq G m hcard
    ((Fintype.card V + 1 : ℝ≥0)⁻¹) (insert U H)]
  let N : ℝ≥0 := (Fintype.card V : ℝ≥0) + 1
  let p : ℝ≥0 := N⁻¹
  change (Fintype.card (ActiveFamilyTwoAwayWitness G U H) : ℝ≥0) *
      p ^ (m - 2 - H.card) ≤
    ((m * (Fintype.card V + 1) : ℕ) : ℝ≥0) *
      (((familyExtensions G (insert U H)).card : ℝ≥0) *
        p ^ (m - (insert U H).card))
  by_cases hactive : IsEmpty (ActiveFamilyTwoAwayWitness G U H)
  · have hzero : Fintype.card (ActiveFamilyTwoAwayWitness G U H) = 0 :=
      Fintype.card_eq_zero
    simp [hzero]
  · letI : Nonempty (ActiveFamilyTwoAwayWitness G U H) := not_isEmpty_iff.mp hactive
    let z : ActiveFamilyTwoAwayWitness G U H := Classical.choice inferInstance
    have hUnotH : U ∉ H := by
      intro hUH
      have hUrem := z.2 hUH
      exact (mem_erase.mp hUrem).1 rfl
    have hHcard : H.card + 2 ≤ m := by
      have hsubcard := card_le_card z.2
      rw [familyTwoAwayRemainder_card hcard z.1] at hsubcard
      have hm : 1 < z.1.family.card :=
        Finset.one_lt_card.mpr
          ⟨U, z.1.fixed_mem, z.1.missing, z.1.missing_mem,
            z.1.missing_ne.symm⟩
      rw [hcard z.1.family z.1.family_mem] at hm
      omega
    have hinsert : (insert U H).card = H.card + 1 :=
      card_insert_of_notMem hUnotH
    have hpow :
        N * p ^ (m - (insert U H).card) =
          p ^ (m - 2 - H.card) := by
      rw [hinsert]
      have hexp : m - (H.card + 1) = (m - 2 - H.card) + 1 := by omega
      rw [hexp, pow_succ]
      calc
        N * (p ^ (m - 2 - H.card) * p) =
            p ^ (m - 2 - H.card) * (N * p) := by ring
        _ = p ^ (m - 2 - H.card) := by
          have hN : N ≠ 0 := by dsimp [N]; positivity
          rw [show N * p = 1 by simp [p, hN], mul_one]
    have hactiveCard := card_activeFamilyTwoAwayWitness_le
      (G := G) (U := U) H hcard
    have hcast :
        (Fintype.card (ActiveFamilyTwoAwayWitness G U H) : ℝ≥0) ≤
          ((familyExtensions G (insert U H)).card * m : ℕ) := by
      exact_mod_cast hactiveCard
    calc
      (Fintype.card (ActiveFamilyTwoAwayWitness G U H) : ℝ≥0) *
          p ^ (m - 2 - H.card) ≤
        (((familyExtensions G (insert U H)).card * m : ℕ) : ℝ≥0) *
          p ^ (m - 2 - H.card) := by
            simpa only [mul_comm] using
              mul_le_mul_right hcast (p ^ (m - 2 - H.card))
      _ = ((m * (Fintype.card V + 1) : ℕ) : ℝ≥0) *
          (((familyExtensions G (insert U H)).card : ℝ≥0) *
            p ^ (m - (insert U H).card)) := by
        simp only [N, p, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hpow ⊢
        rw [← hpow]
        ring

end

end Erdos207
