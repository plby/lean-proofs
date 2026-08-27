/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkUnderlyingFamily

/-! # Multiplicity-preserving three-mark codes for the source link moment -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

abbrev SourceLinkMarking (V : Type*) [DecidableEq V] :=
  TripleOn V × (TripleSystemOn V × TripleSystemOn V × TripleSystemOn V)

def SourceLinkMarking.root {V : Type*} [DecidableEq V] (x : SourceLinkMarking V) := x.1
def SourceLinkMarking.initial {V : Type*} [DecidableEq V] (x : SourceLinkMarking V) := x.2.1
def SourceLinkMarking.later {V : Type*} [DecidableEq V] (x : SourceLinkMarking V) := x.2.2.1
def SourceLinkMarking.candidate {V : Type*} [DecidableEq V] (x : SourceLinkMarking V) := x.2.2.2

def SourceLinkMarking.system
    {V : Type*} [DecidableEq V] (x : SourceLinkMarking V) : TripleSystemOn V :=
  x.initial ∪ x.later ∪ x.candidate

abbrev SourceLinkTriangleCoordinate (V : Type*) [DecidableEq V] := TripleOn V ⊕ (TripleOn V ⊕ TripleOn V)

abbrev SourceLinkCoordinate (V : Type*) [DecidableEq V] := SourceLinkTriangleCoordinate V ⊕ Sym2 V

def SourceLinkMarking.triangleCoordinates
    {V : Type*} [DecidableEq V] (x : SourceLinkMarking V) :
    Finset (SourceLinkTriangleCoordinate V) :=
  x.initial.disjSum (x.later.disjSum x.candidate)

def SourceLinkMarking.edgeCoordinates
    {V : Type*} [DecidableEq V] (x : SourceLinkMarking V) (e : Sym2 V) : Finset (Sym2 V) :=
  (x.candidate.biUnion tripleEdgeFinset).erase e

def SourceLinkMarking.coordinates
    {V : Type*} [DecidableEq V] (x : SourceLinkMarking V) (e : Sym2 V) :
    Finset (SourceLinkCoordinate V) :=
  x.triangleCoordinates.disjSum (x.edgeCoordinates e)

def IsSourceLinkMarking
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (e : Sym2 V)
    (A : TripleSystemOn V) (x : SourceLinkMarking V) : Prop :=
  x.system ∈ sourceLinkUnderlyingFamily W F e ∅ ∧
  Disjoint x.initial x.later ∧ Disjoint (x.initial ∪ x.later) x.candidate ∧
  x.root ∈ x.candidate ∧ e ∈ tripleEdgeFinset x.root ∧
  W.level x.root = Fin.last ell ∧ x.candidate ⊆ A ∧
  (x.later ∪ x.candidate.erase x.root).Nonempty

def sourceLinkMarkings
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (e : Sym2 V)
    (A : TripleSystemOn V) : Finset (SourceLinkMarking V) := by
  classical
  exact univ.filter (IsSourceLinkMarking W F e A)

def sourceLinkUnderlyingRoot
    {V : Type*} [DecidableEq V] (H : Finset (SourceLinkCoordinate V)) : TripleSystemOn V :=
  H.toLeft.toLeft ∪ H.toLeft.toRight.toLeft ∪ H.toLeft.toRight.toRight

theorem SourceLinkMarking.root_mem_system
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V}
    {A : TripleSystemOn V} {x : SourceLinkMarking V} (hx : IsSourceLinkMarking W F e A x) :
    x.root ∈ x.system := mem_union_right _ hx.2.2.2.1

theorem SourceLinkMarking.candidate_eq_sdiff
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V}
    {A : TripleSystemOn V} {x : SourceLinkMarking V} (hx : IsSourceLinkMarking W F e A x) :
    x.candidate = x.system \ (x.initial ∪ x.later) := by
  apply Finset.ext
  intro T
  have hd := disjoint_left.mp hx.2.2.1
  simp only [system, mem_sdiff, mem_union]
  constructor
  · intro hT
    exact ⟨Or.inr hT, fun hT' ↦ hd (mem_union.mpr hT') hT⟩
  · intro hT
    exact hT.1.resolve_left hT.2

theorem sourceLinkMarking_rooted_system_mem
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V}
    {A : TripleSystemOn V} {x : SourceLinkMarking V}
    (hx : IsSourceLinkMarking W F e A x) {H : Finset (SourceLinkCoordinate V)}
    (hH : H ⊆ x.coordinates e) :
    x.system ∈ familyExtensions (sourceLinkUnderlyingFamily W F e H.toRight)
      (sourceLinkUnderlyingRoot H) := by
  have hparts := subset_disjSum.mp hH
  have htri : H.toLeft.toLeft ⊆ x.initial ∧ H.toLeft.toRight ⊆ x.later.disjSum x.candidate :=
    subset_disjSum.mp hparts.1
  have htri' := subset_disjSum.mp htri.2
  have hm := sourceLinkUnderlyingFamily_data hx.1
  apply mem_familyExtensions_iff.mpr
  constructor
  · apply mem_filter.mpr
    refine ⟨hm.1, hm.2.1, ?_⟩
    intro f hf
    obtain ⟨T, hT, hfT⟩ := mem_biUnion.mp (mem_erase.mp (hparts.2 hf)).2
    exact mem_biUnion.mpr ⟨T, mem_union_right _ hT, hfT⟩
  · exact union_subset (union_subset (htri.1.trans (subset_union_left.trans subset_union_left))
      (htri'.1.trans (subset_union_right.trans subset_union_left)))
      (htri'.2.trans subset_union_right)

theorem card_sourceLinkMarkings_system_fiber_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V} {A : TripleSystemOn V}
    (hpack : ∀ E ∈ F, IsPackingOn E) (E : TripleSystemOn V) :
    ((sourceLinkMarkings W F e A).filter (fun x ↦ x.system = E)).card ≤ 4 ^ E.card := by
  classical
  calc
    _ ≤ (E.powerset ×ˢ E.powerset).card := by
      apply card_le_card_of_injOn (f := fun x : SourceLinkMarking V ↦ (x.initial, x.later))
      · intro x hx
        have heq := (mem_filter.mp hx).2
        apply mem_product.mpr
        constructor
        · exact mem_powerset.mpr (heq ▸ (subset_union_left.trans subset_union_left))
        · exact mem_powerset.mpr (heq ▸ (subset_union_right.trans subset_union_left))
      · intro x hx x' hx' hxx'
        have hd : IsSourceLinkMarking W F e A x := (mem_filter.mp (mem_filter.mp hx).1).2
        have hd' : IsSourceLinkMarking W F e A x' := (mem_filter.mp (mem_filter.mp hx').1).2
        have heq : x.system = x'.system := (mem_filter.mp hx).2.trans (mem_filter.mp hx').2.symm
        have hi : x.initial = x'.initial :=
          congrArg (fun u : TripleSystemOn V × TripleSystemOn V ↦ u.1) hxx'
        have hl : x.later = x'.later :=
          congrArg (fun u : TripleSystemOn V × TripleSystemOn V ↦ u.2) hxx'
        have hc : x.candidate = x'.candidate := by
          rw [SourceLinkMarking.candidate_eq_sdiff hd, SourceLinkMarking.candidate_eq_sdiff hd', heq, hi, hl]
        have hr : x.root = x'.root :=
          (hpack x.system (sourceLinkUnderlyingFamily_data hd.1).1).eq_of_common_graph_edge
            (SourceLinkMarking.root_mem_system hd) (heq.symm ▸ SourceLinkMarking.root_mem_system hd')
            hd.2.2.2.2.1 hd'.2.2.2.2.1
        exact Prod.ext hr (Prod.ext hi (Prod.ext hl hc))
    _ = _ := by simp only [card_product, card_powerset, ← mul_pow]; norm_num

end

end Erdos207
