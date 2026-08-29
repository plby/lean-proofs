/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.NondegenerateHammockClosure

/-!
# Seeded nondegenerate hammocks with a genuine path filter

The same-stage roof condition must be part of the selected family, not a
conclusion inferred from the preliminary `IsSafe` predicate. This module
constructs maximal-up-to families satisfying an arbitrary additional path
predicate; the intended application uses containment in the current roof.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {u₀ : V} {e : AltEnd V}

def FilteredNondegenerateHammock
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (u₀ : V) (e : AltEnd V)
    (P : AltPath Gamma.graph → Prop) (H : Set (AltPath Gamma.graph)) : Prop :=
  NondegenerateHammock Gamma Y u₀ e H ∧ ∀ Q ∈ H, P Q

theorem FilteredNondegenerateHammock.subset
    {P : AltPath Gamma.graph → Prop} {H K : Set (AltPath Gamma.graph)}
    (hH : FilteredNondegenerateHammock Gamma Y u₀ e P H) (hKH : K ⊆ H) :
    FilteredNondegenerateHammock Gamma Y u₀ e P K :=
  ⟨hH.1.subset hKH, fun Q hQ ↦ hH.2 Q (hKH hQ)⟩

theorem FilteredNondegenerateHammock.insert
    {P : AltPath Gamma.graph → Prop} {H : Set (AltPath Gamma.graph)}
    {Q : AltPath Gamma.graph}
    (hH : FilteredNondegenerateHammock Gamma Y u₀ e P H)
    (hsafe : IsSafe Y Q) (hstart : Q.initial = u₀) (hend : HasEnd Q e)
    (hnondeg : ¬IsDegenerate Y Q e) (hP : P Q)
    (hdisj : ∀ R ∈ H,
      Disjoint (hammockInterior u₀ e Q) (hammockInterior u₀ e R)) :
    FilteredNondegenerateHammock Gamma Y u₀ e P (insert Q H) := by
  refine ⟨hH.1.insert hsafe hstart hend hnondeg hdisj, ?_⟩
  intro R hR
  rcases hR with rfl | hR
  · exact hP
  · exact hH.2 R hR

theorem exists_maximal_filteredNondegenerateHammock_superset
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (u₀ : V) (e : AltEnd V)
    (P : AltPath Gamma.graph → Prop) {K : Set (AltPath Gamma.graph)}
    (hK : FilteredNondegenerateHammock Gamma Y u₀ e P K) :
    ∃ H : Set (AltPath Gamma.graph), K ⊆ H ∧
      Maximal (fun L ↦ FilteredNondegenerateHammock Gamma Y u₀ e P L) H := by
  apply zorn_subset_nonempty
    {L | FilteredNondegenerateHammock Gamma Y u₀ e P L}
  · intro c hcsub hc _hcne
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun L hL ↦ Set.subset_sUnion_of_mem hL⟩
    · exact nondegenerateHammock_sUnion_of_chain
        (fun H hH ↦ (hcsub hH).1) hc
    · intro Q hQ
      obtain ⟨H, hHc, hQH⟩ := Set.mem_sUnion.1 hQ
      exact (hcsub hHc).2 Q hQH
  · exact hK

def FilteredNondegenerateHammockMaximalUpTo
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (u₀ : V) (e : AltEnd V)
    (P : AltPath Gamma.graph → Prop) (rho : Cardinal.{u})
    (H : Set (AltPath Gamma.graph)) : Prop :=
  MaximalUpTo {L | FilteredNondegenerateHammock Gamma Y u₀ e P L} rho H

theorem FilteredNondegenerateHammockMaximalUpTo.isFilteredNondegenerateHammock
    {P : AltPath Gamma.graph → Prop} {rho : Cardinal.{u}}
    {H : Set (AltPath Gamma.graph)}
    (hH : FilteredNondegenerateHammockMaximalUpTo Gamma Y u₀ e P rho H) :
    FilteredNondegenerateHammock Gamma Y u₀ e P H := MaximalUpTo.mem hH

theorem FilteredNondegenerateHammockMaximalUpTo.card_le
    {P : AltPath Gamma.graph → Prop} {rho : Cardinal.{u}}
    {H : Set (AltPath Gamma.graph)}
    (hH : FilteredNondegenerateHammockMaximalUpTo Gamma Y u₀ e P rho H) :
    #H ≤ rho := MaximalUpTo.card_le hH

theorem exists_filteredNondegenerateHammockMaximalUpTo_superset
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (u₀ : V) (e : AltEnd V)
    (P : AltPath Gamma.graph → Prop) (kappa : Cardinal.{u})
    (hkappa : aleph0 ≤ kappa) {K : Set (AltPath Gamma.graph)}
    (hK : FilteredNondegenerateHammock Gamma Y u₀ e P K) (hKcard : #K ≤ kappa) :
    ∃ H : Set (AltPath Gamma.graph), K ⊆ H ∧
      FilteredNondegenerateHammockMaximalUpTo Gamma Y u₀ e P kappa H := by
  obtain ⟨M, hKM, hMmax⟩ :=
    exists_maximal_filteredNondegenerateHammock_superset Gamma Y u₀ e P hK
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

noncomputable def seededFilteredNondegenerateHammockExtension
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (kappa : Cardinal.{u})
    (u₀ : V) (e : AltEnd V) (P : AltPath Gamma.graph → Prop)
    (K : Set (AltPath Gamma.graph)) : Set (AltPath Gamma.graph) := by
  classical
  exact if h : aleph0 ≤ kappa ∧
      FilteredNondegenerateHammock Gamma Y u₀ e P K ∧ #K ≤ kappa then
    Classical.choose
      (exists_filteredNondegenerateHammockMaximalUpTo_superset Gamma Y u₀ e P kappa
        h.1 h.2.1 h.2.2)
  else ∅

theorem seededFilteredNondegenerateHammockExtension_spec
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (kappa : Cardinal.{u})
    (u₀ : V) (e : AltEnd V) (P : AltPath Gamma.graph → Prop)
    (K : Set (AltPath Gamma.graph)) (hkappa : aleph0 ≤ kappa)
    (hK : FilteredNondegenerateHammock Gamma Y u₀ e P K) (hKcard : #K ≤ kappa) :
    K ⊆ seededFilteredNondegenerateHammockExtension Gamma Y kappa u₀ e P K ∧
      FilteredNondegenerateHammockMaximalUpTo Gamma Y u₀ e P kappa
        (seededFilteredNondegenerateHammockExtension Gamma Y kappa u₀ e P K) := by
  rw [seededFilteredNondegenerateHammockExtension, dif_pos ⟨hkappa, hK, hKcard⟩]
  exact Classical.choose_spec
    (exists_filteredNondegenerateHammockMaximalUpTo_superset Gamma Y u₀ e P kappa
      hkappa hK hKcard)

theorem seededFilteredNondegenerateHammockExtension_card_le
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (kappa : Cardinal.{u})
    (u₀ : V) (e : AltEnd V) (P : AltPath Gamma.graph → Prop)
    (K : Set (AltPath Gamma.graph)) (hkappa : aleph0 ≤ kappa) :
    #(seededFilteredNondegenerateHammockExtension Gamma Y kappa u₀ e P K)
      ≤ kappa := by
  by_cases hvalid : FilteredNondegenerateHammock Gamma Y u₀ e P K ∧ #K ≤ kappa
  · exact (seededFilteredNondegenerateHammockExtension_spec
      Gamma Y kappa u₀ e P K hkappa hvalid.1 hvalid.2).2.card_le
  · rw [seededFilteredNondegenerateHammockExtension, dif_neg]
    · simp
    · intro h
      exact hvalid h.2

#print axioms exists_filteredNondegenerateHammockMaximalUpTo_superset
#print axioms seededFilteredNondegenerateHammockExtension_spec
#print axioms seededFilteredNondegenerateHammockExtension_card_le

end Erdos599.Blueprint
