/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFragmentWarp
import ErdosProblems.Erdos599.GroundingConcreteControls

/-!
# The carrier used by the Assertion 8.20 first-hit construction

A usable hanging fragment consists of the surviving fragment together with
the represented parent edge immediately preceding it.  Its auxiliary
carrier contains the old vertices of the fragment and the edge gadgets of
both the fragment and its predecessor.  Taking the first hit of the union of
these carriers is what makes the later predecessor splices compatible.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingFragmentCarrier

open DirectedPath
open PopularGroundingBridge

universe u

variable {V I : Type u} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type u) :=
  PopularAuxiliary.Input Gamma I

abbrev LV (L : Input Gamma I) :=
  PopularAuxiliary.Input.LambdaVertex V I

/-- A cut-preceded hanging fragment which omits the current request vertex. -/
structure Piece (L : Input Gamma I) {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (r : Request L S.cut) where
  fragment : L.Fragment
  fragment_mem : fragment ∈ GroundingCut.fragments L S.cut
  hanging : fragment.IsHanging
  predecessor : V × V
  predecessor_mem_cut : predecessor ∈ GroundingCut.CE L S.cut
  predecessor_mem_parent : predecessor ∈ fragment.parent.edgeSet
  predecessor_head : predecessor.2 = fragment.path.initial
  avoids_request : requestVertex r ∉ fragment.path.support

/-- The complete auxiliary trace used by the predecessor splice. -/
def Piece.carrier {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U} {r : Request L S.cut}
    (W : Piece L S r) : Set (LV L) :=
  PopularAuxiliary.Input.LambdaVertex.old '' W.fragment.path.support ∪
    (fun e : V × V ↦
      PopularAuxiliary.Input.LambdaVertex.edge e.1 e.2) ''
      insert W.predecessor W.fragment.path.edgeSet

/-- The union of all usable hanging-fragment carriers for one request. -/
def carrier {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (r : Request L S.cut) : Set (LV L) :=
  ⋃ W : Piece L S r, W.carrier

/-- Every piece carrier lies in the full trace of its parent ladder path. -/
theorem Piece.carrier_subset_ladderTrace
    {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U} {r : Request L S.cut}
    (W : Piece L S r) :
    W.carrier ⊆ PopularSwitching.ladderTrace L W.fragment.parent := by
  intro z hz
  rcases hz with hz | hz
  · rcases hz with ⟨x, hx, rfl⟩
    exact Or.inl ⟨x, W.fragment.support_subset hx, rfl⟩
  · rcases hz with ⟨e, he, rfl⟩
    apply Or.inr
    refine ⟨e, ?_, rfl⟩
    rcases Set.mem_insert_iff.mp he with rfl | he
    · exact W.predecessor_mem_parent
    · exact W.fragment.edges_subset he

/-- A piece carrier avoids the apex of its request fan. -/
theorem Piece.carrier_disjoint_requestAuxVertex
    {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U} {r : Request L S.cut}
    (W : Piece L S r) :
    Disjoint W.carrier {requestAuxVertex r} := by
  rw [Set.disjoint_left]
  intro z hz hzApex
  have hzEq : z = requestAuxVertex r := Set.mem_singleton_iff.mp hzApex
  rcases hz with hz | hz
  · exact Set.disjoint_left.1
      (GroundingConcreteControls.oldImage_fragment_disjoint_requestAuxVertex
        W.avoids_request) hz hzApex
  · rcases hz with ⟨e, he, rfl⟩
    cases r with
    | inl x => cases hzEq
    | inr d =>
        have hed : e = d.1 := by
          exact Prod.ext
            (PopularAuxiliary.Input.LambdaVertex.edge.inj hzEq).1
            (PopularAuxiliary.Input.LambdaVertex.edge.inj hzEq).2
        have hdFamily : d.1 ∈ L.familyEdges :=
          PopularGroundingBridge.edgeRequest_mem_familyEdges S d
        have hdCE : d.1 ∈ GroundingCut.CE L S.cut := by
          exact ⟨d.2, hdFamily⟩
        rcases Set.mem_insert_iff.mp he with he | he
        · subst e
          apply W.avoids_request
          change d.1.2 ∈ W.fragment.path.support
          rw [he, W.predecessor_head]
          exact W.fragment.path.initial_mem_support
        · exact Set.disjoint_left.1 W.fragment_mem.1 he
            (hed ▸ hdCE)

/-- Consequently the union of all piece carriers avoids the request apex. -/
theorem carrier_disjoint_requestAuxVertex
    {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (r : Request L S.cut) :
    Disjoint (carrier S r) {requestAuxVertex r} := by
  rw [Set.disjoint_left]
  intro z hz hzApex
  obtain ⟨W, hzW⟩ := Set.mem_iUnion.mp hz
  exact Set.disjoint_left.1 W.carrier_disjoint_requestAuxVertex hzW hzApex

/-- A literal collision supplies a contact with the global piece carrier. -/
theorem collision_meets_carrier
    {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (r : Request L S.cut)
    {p : FinitePath L.lambda.graph}
    (hp : GroundingConcreteControls.hangingFragmentCollision
      L S.cut r p) :
    p.walk.Meets (carrier S r) := by
  rcases hp with ⟨P, hP, hhang, hpred, hapex, x, hxP, hxp⟩
  rcases hpred with ⟨s, hsCut, hsParent, hsHead⟩
  let W : Piece L S r :=
    { fragment := P
      fragment_mem := hP
      hanging := hhang
      predecessor := s
      predecessor_mem_cut := hsCut
      predecessor_mem_parent := hsParent
      predecessor_head := hsHead
      avoids_request := hapex }
  refine ⟨.old x, hxp, ?_⟩
  apply Set.mem_iUnion.2
  refine ⟨W, Or.inl ?_⟩
  exact ⟨x, hxP, rfl⟩

/-- Membership in the global carrier selects a concrete piece containing
that vertex. -/
theorem exists_piece_of_mem_carrier
    {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U} {r : Request L S.cut}
    {z : LV L} (hz : z ∈ carrier S r) :
    ∃ W : Piece L S r, z ∈ W.carrier := by
  exact Set.mem_iUnion.mp hz

/-- Every carrier vertex has a finite auxiliary continuation to the
represented predecessor in the cut. -/
theorem Piece.exists_path_to_cut
    {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U} {r : Request L S.cut}
    (W : Piece L S r) {z : LV L} (hz : z ∈ W.carrier) :
    ∃ q : FinitePath L.lambda.graph,
      q.start = z ∧ q.finish ∈ S.cut ∧ q.support ⊆ W.carrier := by
  rcases hz with hz | hz
  · rcases hz with ⟨x, hx, rfl⟩
    obtain ⟨q, hqStart, hqFinish, hqSupport⟩ :=
      GroundingFragmentWarp.exists_path_to_cutPredecessor
        L S.cut W.fragment_mem W.predecessor_mem_cut
        W.predecessor_mem_parent W.predecessor_head hx
    refine ⟨q, hqStart, ?_, ?_⟩
    · rw [hqFinish]
      exact W.predecessor_mem_cut.1
    · intro z hz
      rcases hqSupport hz with hz | hz
      · apply Or.inl
        rcases Set.mem_singleton_iff.mp hz with rfl
        exact ⟨x, hx, rfl⟩
      · exact Or.inr hz
  · rcases hz with ⟨e, he, rfl⟩
    rcases Set.mem_insert_iff.mp he with rfl | he
    · let q : FinitePath L.lambda.graph :=
        FinitePath.trivial L.lambda.graph
          (.edge W.predecessor.1 W.predecessor.2)
      refine ⟨q, ?_, ?_, ?_⟩
      · simp [q]
      · change PopularAuxiliary.Input.LambdaVertex.edge
          W.predecessor.1 W.predecessor.2 ∈ S.cut
        exact W.predecessor_mem_cut.1
      · intro z hz
        have hz' : z =
            PopularAuxiliary.Input.LambdaVertex.edge
              W.predecessor.1 W.predecessor.2 := by
          simpa [q] using hz
        subst z
        exact Or.inr ⟨W.predecessor, Set.mem_insert _ _, rfl⟩
    · obtain ⟨q, hqStart, hqFinish, hqSupport⟩ :=
        GroundingFragmentWarp.exists_edge_path_to_cutPredecessor
          L S.cut W.fragment_mem W.predecessor_mem_cut
          W.predecessor_mem_parent W.predecessor_head he
      refine ⟨q, hqStart, ?_, ?_⟩
      · rw [hqFinish]
        exact W.predecessor_mem_cut.1
      · intro z hz
        exact Or.inr (hqSupport hz)

/-- The union of all carriers with a fixed parent is countable and avoids
the request apex.  This is the countable fiber used in stationary thinning. -/
def parentCarrier {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (r : Request L S.cut)
    (Y : Gamma.DPath) : Set (LV L) :=
  {z | ∃ W : Piece L S r, W.fragment.parent = Y ∧ z ∈ W.carrier}

theorem parentCarrier_subset_ladderTrace
    {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (r : Request L S.cut)
    (Y : Gamma.DPath) :
    parentCarrier S r Y ⊆ PopularSwitching.ladderTrace L Y := by
  rintro z ⟨W, hWY, hzW⟩
  rw [← hWY]
  exact W.carrier_subset_ladderTrace hzW

theorem parentCarrier_countable
    {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (r : Request L S.cut)
    (Y : Gamma.DPath) : (parentCarrier S r Y).Countable :=
  (PopularSwitching.ladderTrace_countable L Y).mono
    (parentCarrier_subset_ladderTrace S r Y)

theorem parentCarrier_disjoint_requestAuxVertex
    {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (r : Request L S.cut)
    (Y : Gamma.DPath) :
    Disjoint (parentCarrier S r Y) {requestAuxVertex r} := by
  rw [Set.disjoint_left]
  rintro z ⟨W, _hWY, hzW⟩ hzApex
  exact Set.disjoint_left.1 W.carrier_disjoint_requestAuxVertex hzW hzApex

/-- Full auxiliary traces of distinct members of the limiting ladder warp
are disjoint.  This lower-level copy keeps the Assertion 8.20 construction
independent of the downstream simultaneous decoder for Assertion 8.22. -/
theorem ladderTrace_disjoint_of_ne
    (L : Input Gamma I) {Y Z : Gamma.DPath}
    (hY : Y ∈ L.ladder.paths) (hZ : Z ∈ L.ladder.paths)
    (hYZ : Y ≠ Z) :
    Disjoint (PopularSwitching.ladderTrace L Y)
      (PopularSwitching.ladderTrace L Z) := by
  rw [Set.disjoint_left]
  intro x hxY hxZ
  simp only [PopularSwitching.ladderTrace, Set.mem_union,
    Set.mem_image] at hxY hxZ
  rcases hxY with ⟨a, ha, rfl⟩ | ⟨e, he, rfl⟩
  · rcases hxZ with ⟨b, hb, hab⟩ | ⟨f, hf, hbad⟩
    · cases hab
      exact hYZ (Alternating.DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint
        hY hZ ha hb)
    · cases hbad
  · rcases hxZ with ⟨b, hb, hbad⟩ | ⟨f, hf, hef⟩
    · cases hbad
    · have hfst : e.1 = f.1 := by
        exact (PopularAuxiliary.Input.LambdaVertex.edge.inj hef).1.symm
      exact hYZ (Alternating.DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint
        hY hZ (Y.edgeSet_subset_support_prod he).1
          (hfst ▸ (Z.edgeSet_subset_support_prod hf).1))

/-- Carriers of pieces with different parent ladder paths are disjoint. -/
theorem Piece.carrier_disjoint_of_parent_ne
    {L : Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U} {r : Request L S.cut}
    (W Z : Piece L S r) (hparent : W.fragment.parent ≠ Z.fragment.parent) :
    Disjoint W.carrier Z.carrier :=
  (ladderTrace_disjoint_of_ne L W.fragment.parent_mem Z.fragment.parent_mem
    hparent).mono W.carrier_subset_ladderTrace Z.carrier_subset_ladderTrace

end GroundingFragmentCarrier
end Erdos599
