/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.NondegenerateHammockClosure

/-!
# Bounded extensions retaining a nondegenerate hammock seed

Extend the seed by Zorn. A large maximal extension can be truncated while
retaining the seed, because the union of two kappa-small families is still
kappa-small for infinite kappa. This supplies the actual selector needed
by a coherent filtered tracker, without a stage-coherence assumption here.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint

open DirectedPath Alternating

universe u

variable {V : Type u}

theorem exists_nondegenerateHammockMaximalUpTo_superset
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (u₀ : V) (e : AltEnd V)
    (kappa : Cardinal.{u}) (hkappa : aleph0 ≤ kappa)
    {K : Set (AltPath Gamma.graph)}
    (hK : NondegenerateHammock Gamma Y u₀ e K) (hKcard : #K ≤ kappa) :
    ∃ H : Set (AltPath Gamma.graph), K ⊆ H ∧
      NondegenerateHammockMaximalUpTo Gamma Y u₀ e kappa H := by
  obtain ⟨M, hKM, hMmax⟩ :=
    exists_maximal_nondegenerateHammock_superset Gamma Y u₀ e hK
  by_cases hMcard : #M ≤ kappa
  · exact ⟨M, hKM, maximalUpTo_of_maximal hMmax.1 hMmax hMcard⟩
  · have hsuccM : succ kappa ≤ #M := succ_le_of_lt (lt_of_not_ge hMcard)
    obtain ⟨s, hs⟩ := Cardinal.le_mk_iff_exists_set.mp
      ((le_succ kappa).trans hsuccM)
    obtain ⟨t, ht⟩ := Cardinal.le_mk_iff_exists_set.mp hsuccM
    let T : Set (AltPath Gamma.graph) := Subtype.val '' s
    let U : Set (AltPath Gamma.graph) := Subtype.val '' t
    let H : Set (AltPath Gamma.graph) := K ∪ T
    have hTM : T ⊆ M := by
      rintro Q ⟨q, _, rfl⟩
      exact q.2
    have hUM : U ⊆ M := by
      rintro Q ⟨q, _, rfl⟩
      exact q.2
    have hTcard : #T = kappa :=
      (Cardinal.mk_image_eq_of_injOn Subtype.val s Set.injOn_subtype_val).trans hs
    have hUcard : #U = succ kappa :=
      (Cardinal.mk_image_eq_of_injOn Subtype.val t Set.injOn_subtype_val).trans ht
    have hHM : H ⊆ M := Set.union_subset hKM hTM
    have hHupper : #H ≤ kappa :=
      (Cardinal.mk_union_le K T).trans
        (Cardinal.add_le_of_le hkappa hKcard hTcard.le)
    have hHlower : kappa ≤ #H := by
      rw [← hTcard]
      exact Cardinal.mk_subtype_mono Set.subset_union_right
    exact ⟨H, Set.subset_union_left,
      maximalUpTo_of_large (hMmax.1.subset hHM)
        (le_antisymm hHupper hHlower) (hMmax.1.subset hUM) hUcard⟩

noncomputable def seededNondegenerateHammockExtension
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (kappa : Cardinal.{u})
    (u₀ : V) (e : AltEnd V) (K : Set (AltPath Gamma.graph)) :
    Set (AltPath Gamma.graph) := by
  classical
  exact if h : aleph0 ≤ kappa ∧
      NondegenerateHammock Gamma Y u₀ e K ∧ #K ≤ kappa then
    Classical.choose
      (exists_nondegenerateHammockMaximalUpTo_superset Gamma Y u₀ e kappa
        h.1 h.2.1 h.2.2)
  else ∅

theorem seededNondegenerateHammockExtension_spec
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (kappa : Cardinal.{u})
    (u₀ : V) (e : AltEnd V) (K : Set (AltPath Gamma.graph))
    (hkappa : aleph0 ≤ kappa)
    (hK : NondegenerateHammock Gamma Y u₀ e K) (hKcard : #K ≤ kappa) :
    K ⊆ seededNondegenerateHammockExtension Gamma Y kappa u₀ e K ∧
      NondegenerateHammockMaximalUpTo Gamma Y u₀ e kappa
        (seededNondegenerateHammockExtension Gamma Y kappa u₀ e K) := by
  rw [seededNondegenerateHammockExtension, dif_pos ⟨hkappa, hK, hKcard⟩]
  exact Classical.choose_spec
    (exists_nondegenerateHammockMaximalUpTo_superset Gamma Y u₀ e kappa
      hkappa hK hKcard)

theorem seededNondegenerateHammockExtension_card_le
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (kappa : Cardinal.{u})
    (u₀ : V) (e : AltEnd V) (K : Set (AltPath Gamma.graph))
    (hkappa : aleph0 ≤ kappa) :
    #(seededNondegenerateHammockExtension Gamma Y kappa u₀ e K) ≤ kappa := by
  by_cases hvalid : NondegenerateHammock Gamma Y u₀ e K ∧ #K ≤ kappa
  · exact (seededNondegenerateHammockExtension_spec Gamma Y kappa u₀ e K
      hkappa hvalid.1 hvalid.2).2.card_le
  · rw [seededNondegenerateHammockExtension, dif_neg]
    · simp
    · intro h
      exact hvalid h.2

#print axioms exists_nondegenerateHammockMaximalUpTo_superset
#print axioms seededNondegenerateHammockExtension_spec
#print axioms seededNondegenerateHammockExtension_card_le

end Erdos599.Blueprint
