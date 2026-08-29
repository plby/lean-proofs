/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeFixedAssignment
import ErdosProblems.Erdos599.FracturedCanonicalBoundary

/-!
# Internal-edge purity for the actual canonical duplicated families

The duplicated ambient graph contains many noncanonical edges. We use only
the three actual edge forms of the canonical paths. Their port incidence,
together with downstairs subdivision incidence, proves the internal-edge
property needed by the fixed-original Hall construction.
-/

namespace Erdos599.Alternating.FracturedCanonicalInternalReference

open Set DirectedPath FracturedDuplication FracturedCanonicalFiniteLift
open FracturedCanonicalReferenceLift ColouredSafeInternalReferenceHall
open Blueprint.LinkageBlueprint.FracturedCanonicalBoundary

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- The three consecutive-vertex forms in a canonical expanded path. -/
inductive CanonicalStep (D : Digraph V) : Vertex V → Vertex V → Prop
  | proper {x y : V} (adj : D.Adj x y) : CanonicalStep D (outgoing x) (incoming y)
  | incomingPlain (x : V) : CanonicalStep D (incoming x) (plain x)
  | plainOutgoing (x : V) : CanonicalStep D (plain x) (outgoing x)

namespace CanonicalStep

theorem into_incoming {D : Digraph V} {a : Vertex V} {y : V}
    (h : CanonicalStep D a (incoming y)) :
    ∃ x, a = outgoing x ∧ D.Adj x y := by
  cases h with
  | proper hadj => exact ⟨_, rfl, hadj⟩

theorem from_outgoing {D : Digraph V} {b : Vertex V} {x : V}
    (h : CanonicalStep D (outgoing x) b) :
    ∃ y, b = incoming y ∧ D.Adj x y := by
  cases h with
  | proper hadj => exact ⟨_, rfl, hadj⟩

theorem into_plain {D : Digraph V} {a : Vertex V} {x : V}
    (h : CanonicalStep D a (plain x)) : a = incoming x := by
  cases h
  rfl

theorem from_plain {D : Digraph V} {b : Vertex V} {x : V}
    (h : CanonicalStep D (plain x) b) : b = outgoing x := by
  cases h
  rfl

end CanonicalStep

theorem canonicalConsWalk_edges (Z : FracturedWarp Gamma) :
    ∀ {x y z : V} (h : Gamma.graph.Adj x y) (q : Walk Gamma.graph y z)
      {a b : Vertex V}, (a, b) ∈ (canonicalConsWalk Z h q).edgeSet →
        CanonicalStep Gamma.graph a b := by
  intro x y z h q
  induction q generalizing x with
  | nil =>
      intro a b he
      simp only [canonicalConsWalk, Walk.edgeSet_cons, Walk.edgeSet_nil,
        Set.union_empty, Set.mem_singleton_iff] at he
      cases he
      exact .proper h
  | @cons y w z hnext q ih =>
      intro a b he
      simp only [canonicalConsWalk, Walk.edgeSet_cons, Set.mem_union,
        Set.mem_singleton_iff] at he
      rcases he with he | he | he | he
      · cases he
        exact .proper h
      · cases he
        exact .incomingPlain y
      · cases he
        exact .plainOutgoing y
      · exact ih hnext he

theorem canonicalActiveLift_edges (Z : FracturedWarp Gamma)
    {a b : Vertex V} (he : (a, b) ∈ familyEdges (canonicalActiveLift Z)) :
    CanonicalStep Gamma.graph a b := by
  simp only [familyEdges, Set.mem_iUnion] at he
  obtain ⟨P, ⟨p, _hp, hpne, rfl⟩, heP⟩ := he
  have hsub : (lift Z p hpne).walk.edgeSet ⊆
      (canonicalConsWalk Z (firstConsData p hpne).first
        (firstConsData p hpne).tail).edgeSet := by
    apply Walk.edgeSet_subset_of_support_prefix
    rw [canonicalConsWalk_support_eq_lift Z p hpne]
  exact canonicalConsWalk_edges Z _ _ (hsub heP)

theorem liftedReferencePaths_edges (Z : FracturedWarp Gamma)
    {Y : Set Gamma.DPath} {a b : Vertex V}
    (he : (a, b) ∈ familyEdges (liftedReferencePaths Z Y)) :
    CanonicalStep Gamma.graph a b := by
  simp only [familyEdges, Set.mem_iUnion] at he
  obtain ⟨P, ⟨p, _hp, rfl⟩, he⟩ := he
  change (a, b) ∈ (referenceLiftFinitePath Z p).edgeSet at he
  classical
  by_cases hp : p.start = p.finish
  · rw [referenceLiftFinitePath, dif_pos hp] at he
    exact (Set.notMem_empty _ he).elim
  · rw [referenceLiftFinitePath, dif_neg hp] at he
    exact canonicalConsWalk_edges Z _ _ he

/-- A relation-level local-incidence argument, applied only to actual
canonical family edges, not to every duplicated ambient edge. -/
theorem internalReferenceEdges_of_canonicalSteps
    {D : Digraph V} {Delta : DWeb (Vertex V)} {W Y : Set Delta.DPath}
    (hsub : Blueprint.HasHereditarySubdivisionIncidence D)
    (hY : Delta.IsWarp Y) (hYfin : Delta.HasFiniteCharacter Y)
    (hWstep : ∀ {a b}, (a, b) ∈ familyEdges W → CanonicalStep D a b)
    (hYstep : ∀ {a b}, (a, b) ∈ familyEdges Y → CanonicalStep D a b) :
    InternalReferenceEdges W Y := by
  intro a b he ha hb hbI haT
  have hin : HasIncoming (familyEdges Y) b := by
    by_contra hnot
    apply hbI
    rw [initialSet_eq_vertexSet_diff_hasIncoming hY hYfin]
    exact ⟨hb, hnot⟩
  have hout : HasOutgoing (familyEdges Y) a := by
    by_contra hnot
    apply haT
    rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing hY hYfin]
    exact ⟨ha, hnot⟩
  cases hWstep he with
  | @proper x y hxy =>
      rcases hsub hxy with ⟨_hne, hpred | hsucc⟩
      · obtain ⟨w, _hwx, _hwy, hpred, _hother⟩ := hpred
        obtain ⟨c, hc⟩ := hin
        obtain ⟨z, hcz, hzy⟩ := (hYstep hc).into_incoming
        have hcEq : c = outgoing x := hcz.trans (congrArg outgoing (hpred hzy))
        exact hcEq ▸ hc
      · obtain ⟨w, _hwx, _hwy, hsucc, _hother⟩ := hsucc
        obtain ⟨c, hc⟩ := hout
        obtain ⟨z, hcz, hxz⟩ := (hYstep hc).from_outgoing
        have hcEq : c = incoming y := hcz.trans (congrArg incoming (hsucc hxz))
        exact hcEq ▸ hc
  | incomingPlain x =>
      obtain ⟨c, hc⟩ := hin
      exact (hYstep hc).into_plain ▸ hc
  | plainOutgoing x =>
      obtain ⟨c, hc⟩ := hout
      exact (hYstep hc).from_plain ▸ hc

/-- The actual peeled canonical family satisfies the internal-edge property.
No no-junction or source-boundary assertion is needed for this local lemma. -/
theorem canonical_internalReferenceEdges
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hsub : Blueprint.HasHereditarySubdivisionIncidence Gamma.graph)
    (hY : Gamma.IsWarp Y) :
    InternalReferenceEdges (canonicalActiveLift Z) (canonicalPeeledReferenceLift Z Y) :=
  internalReferenceEdges_of_canonicalSteps hsub
    (liftedReferencePaths_isWarp Z
      (Blueprint.LinkageBlueprint.FracturedAssignmentPeel.activeReference_isWarp Z hY))
    (liftedReferencePaths_hasFiniteCharacter Z _)
    (canonicalActiveLift_edges Z) (liftedReferencePaths_edges Z)

/-- The actual canonical pair now receives a simultaneous fixed-forward
assignment. Its boundary and no-junction inputs are the existing geometric
conditions, not an assumed assignment or a new incidence hypothesis. -/
theorem exists_canonicalFixedSafeAssignment
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (hsub : Blueprint.HasHereditarySubdivisionIncidence Gamma.graph)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths)
    (hnoJunction : NoJunctionOnReference Z
      (Blueprint.LinkageBlueprint.FracturedAssignmentPeel.activeReference Z Y)) :
    Nonempty (ColouredSafeFixedAssignment.FixedSafeAssignment
      (canonicalActiveLift Z) (canonicalPeeledReferenceLift Z Y)) := by
  have geometry := canonicalDichotomyGeometry Z hboundary hY hZfinite hYfinite
    hsource hnoJunction
  exact ColouredSafeFixedAssignment.exists_fixedSafeAssignment
    geometry.forward_isWarp geometry.reference_isWarp
    geometry.forward_finite geometry.reference_finite geometry.source_subset
    geometry.boundary_aligned.2 (canonical_internalReferenceEdges Z hsub hY)

#print axioms canonicalActiveLift_edges
#print axioms liftedReferencePaths_edges
#print axioms internalReferenceEdges_of_canonicalSteps
#print axioms canonical_internalReferenceEdges
#print axioms exists_canonicalFixedSafeAssignment

end Erdos599.Alternating.FracturedCanonicalInternalReference
