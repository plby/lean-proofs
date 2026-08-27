/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ThreatExtensionCrude

/-!
# Rooted-threat moments relative to an initial packing

For a stage beginning from `P0`, only the part of a rooted threat remainder
outside `P0` must be supplied by the new random family.  This relative
remainder is the correct configuration map for applying B4 to a later stage.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Rooted activity is monotone in the selected family. -/
lemma rootedActiveForbiddenConfigurations_mono
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P P' : TripleSystemOn V} {u v : V}
    (hPP' : P ⊆ P') :
    rootedActiveForbiddenConfigurations F P u v ⊆
      rootedActiveForbiddenConfigurations F P' u v := by
  intro C hC
  obtain ⟨hCF, T, hTC, huT, hvT, hrem⟩ :=
    mem_rootedActiveForbiddenConfigurations_iff.mp hC
  exact mem_rootedActiveForbiddenConfigurations_iff.mpr
    ⟨hCF, T, hTC, huT, hvT, hrem.trans hPP'⟩

lemma rootedActiveForbiddenConfigurations_card_mono
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P P' : TripleSystemOn V} {u v : V}
    (hPP' : P ⊆ P') :
    (rootedActiveForbiddenConfigurations F P u v).card <=
      (rootedActiveForbiddenConfigurations F P' u v).card :=
  card_le_card (rootedActiveForbiddenConfigurations_mono hPP')

/-- The part of a rooted threat remainder which is not already present in the
initial packing. -/
def relativeRootedThreatRemainder
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V} {u v : V}
    (P0 : TripleSystemOn V) (z : RootedThreatWitness V F u v) :
    TripleSystemOn V :=
  rootedThreatRemainder z \ P0

lemma relativeRootedThreatRemainder_subset_iff
    {V : Type*} [DecidableEq V] {F : ForbiddenFamilyOn V} {u v : V}
    (P0 R : TripleSystemOn V) (z : RootedThreatWitness V F u v) :
    relativeRootedThreatRemainder P0 z ⊆ R ↔
      rootedThreatRemainder z ⊆ P0 ∪ R := by
  constructor
  · intro h T hT
    by_cases hTP0 : T ∈ P0
    · exact mem_union_left R hTP0
    · exact mem_union_right P0 (h (mem_sdiff.mpr ⟨hT, hTP0⟩))
  · intro h T hT
    obtain ⟨hTrem, hTnotP0⟩ := mem_sdiff.mp hT
    exact (mem_union.mp (h hTrem)).resolve_left hTnotP0

/-- Relative remainders selected from `R` are exactly the rooted witnesses
active over the enlarged packing `P0 ∪ R`. -/
lemma selectedCount_relativeRootedThreatRemainder
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P0 R : TripleSystemOn V) (u v : V) :
    selectedCount
      (fun z : RootedThreatWitness V F u v =>
        relativeRootedThreatRemainder P0 z) R =
      (activeRootedThreatWitnesses F (P0 ∪ R) u v).card := by
  classical
  unfold selectedCount activeRootedThreatWitnesses
  simp only [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_filter]
  apply sum_congr rfl
  intro z _hz
  by_cases hrel : relativeRootedThreatRemainder P0 z ⊆ R
  · have horig : rootedThreatRemainder z ⊆ P0 ∪ R :=
      (relativeRootedThreatRemainder_subset_iff P0 R z).mp hrel
    simp [hrel, horig]
  · have horig : ¬ rootedThreatRemainder z ⊆ P0 ∪ R := fun hz =>
      hrel ((relativeRootedThreatRemainder_subset_iff P0 R z).mpr hz)
    simp [hrel, horig]

/-- Pointwise domination of rooted active configurations after adjoining a
random relative family. -/
lemma rootedActive_union_count_le_relativeSelectedCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P0 R : TripleSystemOn V) (u v : V) :
    ((rootedActiveForbiddenConfigurations F (P0 ∪ R) u v).card : NNReal) <=
      selectedCount
        (fun z : RootedThreatWitness V F u v =>
          relativeRootedThreatRemainder P0 z) R := by
  rw [selectedCount_relativeRootedThreatRemainder]
  exact_mod_cast card_rootedActiveForbiddenConfigurations_le_witnesses

/-- A relative rooted remainder is no larger than the original rooted
remainder. -/
lemma card_relativeRootedThreatRemainder_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {u v : V} {P0 : TripleSystemOn V} {k : Nat}
    (hcard : ∀ C ∈ F, C.card <= k)
    (z : RootedThreatWitness V F u v) :
    (relativeRootedThreatRemainder P0 z).card <= k - 1 := by
  exact (card_le_card (sdiff_subset)).trans
    (card_rootedThreatRemainder_le hcard z)

/-- Baseline relative extension bound obtained solely from the number of
rooted witnesses. -/
theorem relativeRootedThreatRemainder_hasExtensionBound_crude
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P0 : TripleSystemOn V) (u v : V)
    (pi : TripleOn V -> NNReal) (k : Nat)
    (hcard : ∀ C ∈ F, C.card <= k) (hpi : ∀ T, pi T <= 1) :
    HasExtensionBound
      (fun z : RootedThreatWitness V F u v =>
        relativeRootedThreatRemainder P0 z)
      pi (F.card * k) := by
  intro A
  unfold extensionWeight
  calc
    ∑ z : RootedThreatWitness V F u v,
        (if A ⊆ relativeRootedThreatRemainder P0 z then
          setWeight pi (relativeRootedThreatRemainder P0 z \ A) else 0) <=
        ∑ _z : RootedThreatWitness V F u v, (1 : NNReal) := by
      apply sum_le_sum
      intro z _hz
      split_ifs
      · exact setWeight_le_one pi hpi _
      · exact zero_le
    _ = (Fintype.card (RootedThreatWitness V F u v) : NNReal) := by simp
    _ <= (F.card * k : NNReal) := by
      exact_mod_cast card_rootedThreatWitness_le F u v k hcard

/-- Moment estimate for rooted threats active after adjoining a random family
to a fixed initial packing. -/
theorem relativeRootedActiveMomentBound
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Omega) (R : Omega -> TripleSystemOn V)
    (F : ForbiddenFamilyOn V) (P0 : TripleSystemOn V) (u v : V)
    (pi : TripleOn V -> NNReal) (C kappa : NNReal) {k s : Nat}
    (hcard : ∀ S ∈ F, S.card <= k)
    (hkappa : HasExtensionBound
      (fun z : RootedThreatWitness V F u v =>
        relativeRootedThreatRemainder P0 z) pi kappa)
    (hjoint : ∀ T : TripleSystemOn V, T.card <= s * (k - 1) ->
      L.probability (fun omega => T ⊆ R omega) <=
        C * setWeight pi T) :
    L.expectation (fun omega =>
      ((rootedActiveForbiddenConfigurations F (P0 ∪ R omega) u v).card :
        NNReal) ^ s) <=
      C * (((2 : NNReal) ^ (s * (k - 1)) * kappa) ^ s) := by
  calc
    L.expectation (fun omega =>
        ((rootedActiveForbiddenConfigurations F (P0 ∪ R omega) u v).card :
          NNReal) ^ s) <=
        L.expectation (fun omega =>
          (selectedCount
            (fun z : RootedThreatWitness V F u v =>
              relativeRootedThreatRemainder P0 z)
            (R omega)) ^ s) := by
      apply L.expectation_mono
      intro omega
      exact pow_le_pow_left'
        (rootedActive_union_count_le_relativeSelectedCount
          F P0 (R omega) u v) s
    _ <= C * (((2 : NNReal) ^ (s * (k - 1)) * kappa) ^ s) := by
      apply configurationMomentBound L
        (fun z : RootedThreatWitness V F u v =>
          relativeRootedThreatRemainder P0 z)
        R pi C kappa
      · exact card_relativeRootedThreatRemainder_le hcard
      · exact hkappa
      · exact hjoint

/-- Markov tail bound for the relative rooted-active count. -/
theorem relativeRootedActive_probability_ge_le
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    (L : FiniteLaw Omega) (R : Omega -> TripleSystemOn V)
    (F : ForbiddenFamilyOn V) (P0 : TripleSystemOn V) (u v : V)
    (pi : TripleOn V -> NNReal) (C kappa a : NNReal) {k s : Nat}
    (ha : 0 < a)
    (hcard : ∀ S ∈ F, S.card <= k)
    (hkappa : HasExtensionBound
      (fun z : RootedThreatWitness V F u v =>
        relativeRootedThreatRemainder P0 z) pi kappa)
    (hjoint : ∀ T : TripleSystemOn V, T.card <= s * (k - 1) ->
      L.probability (fun omega => T ⊆ R omega) <=
        C * setWeight pi T) :
    L.probability (fun omega =>
      a <= (rootedActiveForbiddenConfigurations
        F (P0 ∪ R omega) u v).card) <=
      (C * (((2 : NNReal) ^ (s * (k - 1)) * kappa) ^ s)) / a ^ s := by
  have hmono : L.probability (fun omega =>
      a <= (rootedActiveForbiddenConfigurations
        F (P0 ∪ R omega) u v).card) <=
      L.probability (fun omega =>
        a ^ s <=
          ((rootedActiveForbiddenConfigurations
            F (P0 ∪ R omega) u v).card : NNReal) ^ s) := by
    apply L.probability_mono
    intro omega homega
    exact pow_le_pow_left' homega s
  refine hmono.trans ?_
  have hmarkov := L.probability_le_expectation_div
    (fun omega =>
      ((rootedActiveForbiddenConfigurations
        F (P0 ∪ R omega) u v).card : NNReal) ^ s)
    (pow_pos ha s)
  exact hmarkov.trans ((div_le_div_iff_of_pos_right (pow_pos ha s)).2
    (relativeRootedActiveMomentBound
      L R F P0 u v pi C kappa hcard hkappa hjoint))

end

end Erdos207
