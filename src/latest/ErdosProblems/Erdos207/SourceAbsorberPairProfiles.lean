/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceDerivedProfiles
import ErdosProblems.Erdos207.SourceGenuinePairProfiles

/-! # Source WS2: separating derived and genuine profiled pairs -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem card_profiledDistinctPairs_fst_filter_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F D : ForbiddenFamilyOn V) (T T' : TripleOn V) (t : VortexProfile ell) :
    ((W.profiledDistinctEqualRemainderPairs F T T' t).filter fun p ↦ p.1 ∈ D).card ≤
      (W.profiledExtensions D {T} t).card := by
  apply card_le_card_of_injOn (fun p ↦ p.1)
  · intro p hp
    obtain ⟨hp, hpD⟩ := mem_filter.mp hp
    obtain ⟨_, _, _, hT, _, _, ht⟩ := (W.mem_profiledDistinctEqualRemainderPairs_iff _ _ _ _ _).mp hp
    exact (W.mem_profiledExtensions_iff _ _ _ _).mpr
      ⟨hpD, singleton_subset_iff.mpr hT, by simpa only [sdiff_singleton_eq_erase] using ht⟩
  · intro p hp p' hp' heq
    exact distinctEqualRemainderPairs_fst_injOn F T T'
      (mem_filter.mp (mem_filter.mp hp).1).1
      (mem_filter.mp (mem_filter.mp hp').1).1 heq

theorem card_profiledDistinctPairs_snd_filter_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F D : ForbiddenFamilyOn V) (T T' : TripleOn V) (t : VortexProfile ell) :
    ((W.profiledDistinctEqualRemainderPairs F T T' t).filter fun p ↦ p.2 ∈ D).card ≤
      (W.profiledExtensions D {T'} t).card := by
  apply card_le_card_of_injOn (fun p ↦ p.2)
  · intro p hp
    obtain ⟨hp, hpD⟩ := mem_filter.mp hp
    obtain ⟨_, _, _, _, hT', hrem, ht⟩ := (W.mem_profiledDistinctEqualRemainderPairs_iff _ _ _ _ _).mp hp
    apply (W.mem_profiledExtensions_iff _ _ _ _).mpr
    refine ⟨hpD, singleton_subset_iff.mpr hT', ?_⟩
    simpa only [sdiff_singleton_eq_erase, hrem] using ht
  · intro p hp p' hp' heq
    change p.2 = p'.2 at heq
    obtain ⟨_, _, _, hT, _, hrem, _⟩ :=
      (W.mem_profiledDistinctEqualRemainderPairs_iff _ _ _ _ _).mp (mem_filter.mp hp).1
    obtain ⟨_, _, _, hT2, _, hrem2, _⟩ :=
      (W.mem_profiledDistinctEqualRemainderPairs_iff _ _ _ _ _).mp (mem_filter.mp hp').1
    apply Prod.ext _ heq
    calc
      p.1 = insert T (p.1.erase T) := (insert_erase hT).symm
      _ = insert T (p'.1.erase T) := by rw [hrem, heq, ← hrem2]
      _ = p'.1 := insert_erase hT2

theorem card_profiledDistinctPairs_le_split
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F D : ForbiddenFamilyOn V) (T T' : TripleOn V) (t : VortexProfile ell) :
    (W.profiledDistinctEqualRemainderPairs F T T' t).card ≤
      (W.profiledExtensions D {T} t).card + (W.profiledExtensions D {T'} t).card +
        (W.profiledDistinctEqualRemainderPairs (F \ D) T T' t).card := by
  let P := W.profiledDistinctEqualRemainderPairs F T T' t
  have hsub : P ⊆ (P.filter fun p ↦ p.1 ∈ D) ∪ (P.filter fun p ↦ p.2 ∈ D) ∪
      W.profiledDistinctEqualRemainderPairs (F \ D) T T' t := by
    intro p hp
    by_cases hfirst : p.1 ∈ D
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hp, hfirst⟩))
    by_cases hsecond : p.2 ∈ D
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hp, hsecond⟩))
    apply mem_union_right
    obtain ⟨hF, hF', hrest⟩ := (W.mem_profiledDistinctEqualRemainderPairs_iff _ _ _ _ _).mp hp
    exact (W.mem_profiledDistinctEqualRemainderPairs_iff _ _ _ _ _).mpr
      ⟨mem_sdiff.mpr ⟨hF, hfirst⟩, mem_sdiff.mpr ⟨hF', hsecond⟩, hrest⟩
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  exact Nat.add_le_add_right ((card_union_le _ _).trans
    (Nat.add_le_add (card_profiledDistinctPairs_fst_filter_le W F D T T' t)
      (card_profiledDistinctPairs_snd_filter_le W F D T T' t))) _

theorem card_profiledDistinctPairs_induced_nonderived_source_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell q j : ℕ}
    (W : Vortex V ell) (B : TripleSystemOn V) (T T' : TripleOn V) (t : VortexProfile ell)
    (hj : 4 ≤ j) (hterminal : 0 < W.terminalSize) :
    ((W.profiledDistinctEqualRemainderPairs
      (absorberInducedConfigurationsOn q j B \ derivedAbsorberConfigurations q j B) T T' t).card : ℝ≥0) ≤
        (exactBankVortexCoefficient j ell : ℝ≥0) * W.sourceProfileScale (j - 4) t := by
  have hpure : ∀ E ∈ absorberInducedConfigurationsOn q j B \ derivedAbsorberConfigurations q j B,
      5 ≤ j ∧ IsErdosConfigOn j E := by
    intro E hE
    exact genuine_of_induced_not_derived (by omega) (mem_sdiff.mp hE).1 (mem_sdiff.mp hE).2
  by_cases hj5 : 5 ≤ j
  · exact card_genuine_profiledDistinctPairs_source_le W T T' t (fun E hE ↦ (hpure E hE).2) hj5 hterminal
  · have hempty : absorberInducedConfigurationsOn q j B \ derivedAbsorberConfigurations q j B = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro E hE
      exact hj5 (hpure E hE).1
    simp [hempty, Vortex.profiledDistinctEqualRemainderPairs, distinctEqualRemainderPairs]

theorem card_profiledDistinctPairs_absorber_source_le_of_derived_bound
    {V : Type*} [Fintype V] [DecidableEq V] {ell q j : ℕ}
    (W : Vortex V ell) (B : TripleSystemOn V) (T T' : TripleOn V) (t : VortexProfile ell)
    (a : ℝ≥0) (hj : 4 ≤ j) (hterminal : 0 < W.terminalSize)
    (hderived : ∀ S : TripleOn V,
      ((W.profiledExtensions (derivedAbsorberConfigurations q j B) {S} t).card : ℝ≥0) ≤
        a * W.sourceProfileScale (j - 4) t) :
    ((W.profiledDistinctEqualRemainderPairs (absorberInducedConfigurationsOn q j B) T T' t).card : ℝ≥0) ≤
      (2 * a + exactBankVortexCoefficient j ell) * W.sourceProfileScale (j - 4) t := by
  have hsplit : ((W.profiledDistinctEqualRemainderPairs (absorberInducedConfigurationsOn q j B) T T' t).card : ℝ≥0) ≤
      (W.profiledExtensions (derivedAbsorberConfigurations q j B) {T} t).card +
      (W.profiledExtensions (derivedAbsorberConfigurations q j B) {T'} t).card +
      (W.profiledDistinctEqualRemainderPairs
        (absorberInducedConfigurationsOn q j B \ derivedAbsorberConfigurations q j B) T T' t).card := by
    exact_mod_cast card_profiledDistinctPairs_le_split W (absorberInducedConfigurationsOn q j B)
      (derivedAbsorberConfigurations q j B) T T' t
  apply hsplit.trans
  calc
    _ ≤ a * W.sourceProfileScale (j - 4) t + a * W.sourceProfileScale (j - 4) t +
        exactBankVortexCoefficient j ell * W.sourceProfileScale (j - 4) t :=
      add_le_add (add_le_add (hderived T) (hderived T'))
        (card_profiledDistinctPairs_induced_nonderived_source_le W B T T' t hj hterminal)
    _ = _ := by ring

theorem card_profiledDistinctPairs_absorber_source_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell q j : ℕ}
    (W : Vortex V ell) (B : TripleSystemOn V) (T T' : TripleOn V) (t : VortexProfile ell)
    (hj : 4 ≤ j) (hterminal : 0 < W.terminalSize) :
    ((W.profiledDistinctEqualRemainderPairs (absorberInducedConfigurationsOn q j B) T T' t).card : ℝ≥0) ≤
      (2 * ((subsetsUpToCard B q).card * (exactBankVortexOrderCoefficient q ell : ℝ≥0)) +
        exactBankVortexCoefficient j ell) * W.sourceProfileScale (j - 4) t := by
  exact card_profiledDistinctPairs_absorber_source_le_of_derived_bound W B T T' t _ hj hterminal
    (fun S ↦ card_profiledExtensions_derived_singleton_source_le W B S t hj hterminal)

theorem card_profiledDistinctPairs_absorber_source_le_localized
    {V : Type*} [Fintype V] [DecidableEq V] {m q M j : ℕ}
    (W : Vortex V (m + 1)) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (T T' : TripleOn V) (t : VortexProfile (m + 1)) (z : ℝ≥0)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hsep : ∀ x ∈ graphSupportFinset H, x ∉ X → x ∉ W.U 1)
    (hj : 4 ≤ j) (hjq : j ≤ q)
    (hterminal : 0 < W.terminalSize) (hroot : 0 < (W.U 0).card)
    (hbank : ((subsetsUpToCard B q).card : ℝ≥0) * W.terminalSize ≤ (W.U 0).card * z) :
    ((W.profiledDistinctEqualRemainderPairs (absorberInducedConfigurationsOn q j B) T T' t).card : ℝ≥0) ≤
      (2 * (((2 : ℝ≥0) ^ M + z) * exactBankVortexOrderCoefficient q (m + 1)) +
        exactBankVortexCoefficient j (m + 1)) * W.sourceProfileScale (j - 4) t := by
  exact card_profiledDistinctPairs_absorber_source_le_of_derived_bound W B T T' t _ hj hterminal
    (fun S ↦ card_profiledExtensions_derived_singleton_source_le_localized W H X B S t z
      hA2 hsep hj hjq hterminal hroot hbank)

end

end Erdos207
