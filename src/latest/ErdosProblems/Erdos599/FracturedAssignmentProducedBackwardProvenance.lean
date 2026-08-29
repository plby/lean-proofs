/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedProjectionCompiler

/-!
# Backward-owner provenance retained by the fractured assignment compiler

The finite and infinite projection compilers already construct indexed,
unique backward-owner certificates, but `AssignedPathProjection` and
`BracketFracturedAssignment` forget them.  This file keeps the existing APIs
unchanged and adds a stronger produced certificate.  Its provenance is
derived from the actual finite run compression and infinite traversal
compiler; it is not an extra provider premise.
-/

noncomputable section

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace FracturedAssignmentPeel

open Set DirectedPath _root_.Erdos599.Alternating
open Alternating.FracturedDuplication

universe u v

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}

/-- An assigned path together with some concrete indexing of all its links
and unique reference owners for the backward links. -/
structure HasIndexedBackwardProvenance
    (Q : AltPath Gamma.graph) (Y : Set Gamma.DPath) where
  Index : Type u
  certificate : Q.IndexedBackwardProvenance Y Index

namespace HasIndexedBackwardProvenance

variable {Q : AltPath Gamma.graph} {Y Y' : Set Gamma.DPath}

/-- Package an existing indexed certificate. -/
def ofCertificate {I : Type u}
    (P : Q.IndexedBackwardProvenance Y I) :
    HasIndexedBackwardProvenance Q Y :=
  ⟨I, P⟩

/-- Reference-family monotonicity does not change the indexed owners. -/
def mono (P : HasIndexedBackwardProvenance Q Y) (hYY' : Y ⊆ Y') :
    HasIndexedBackwardProvenance Q Y' :=
  ⟨P.Index, {
    link := P.certificate.link
    links_eq_range := P.certificate.links_eq_range
    owner := P.certificate.owner
    owner_mem := fun i hd => hYY' (P.certificate.owner_mem i hd)
    isSubpath := P.certificate.isSubpath
    owner_unique := P.certificate.owner_unique }⟩

/-- The reinserted singleton holes have the empty link indexing. -/
def trivial (x : V) (Y : Set Gamma.DPath) :
    HasIndexedBackwardProvenance (.trivial x) Y :=
  ⟨ULift.{u, 0} Empty, {
    link := fun i => Empty.elim i.down
    links_eq_range := by
      symm
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro l
      rintro ⟨i, rfl⟩
      exact Empty.elim i.down
    owner := fun i => Empty.elim i.down
    owner_mem := fun i => Empty.elim i.down
    isSubpath := fun i => Empty.elim i.down
    owner_unique := fun i => Empty.elim i.down }⟩

/-- Lift the canonical natural-number indexing of an infinite compression
into the vertex universe used by the uniform produced certificate. -/
def ofNatCertificate
    (P : Q.IndexedBackwardProvenance Y Nat) :
    HasIndexedBackwardProvenance Q Y :=
  ⟨ULift.{u, 0} Nat, {
    link := fun i => P.link i.down
    links_eq_range := by
      rw [P.links_eq_range]
      ext l
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨ULift.up i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i.down, rfl⟩
    owner := fun i hd => P.owner i.down hd
    owner_mem := fun i hd => P.owner_mem i.down hd
    isSubpath := fun i hd => P.isSubpath i.down hd
    owner_unique := fun i j hi hj howner =>
      P.owner_unique i.down j.down hi hj howner }⟩

end HasIndexedBackwardProvenance

/-- The existing per-source projected path plus the owner certificate which
the concrete branch compiler used to prove its safety. -/
structure ProducedAssignedPathProjection
    (Z : FracturedWarp Gamma)
    (upstairs : AltPath (web Gamma Z).graph) (source : V) where
  base : AssignedPathProjection (Y := Y) Z upstairs source
  backward : HasIndexedBackwardProvenance base.path Y

namespace InfiniteTraversalBlocks

variable {Z : FracturedWarp Gamma}
variable {Q : AltPath (web Gamma Z).graph} {M : Type v}

/-- The indexed certificate constructed inside `compile`, exposed without
changing the existing `Projection` structure. -/
noncomputable def compile_indexedBackwardProvenance
    (T : InfiniteTraversalBlocks (Y := Y) Z Q M)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.edgeWarp) :
    (T.compile hY hZfinite).path.IndexedBackwardProvenance
      (activeReference Z Y) Nat := by
  let B := T.blocks
  let P := T.provenance
  have hactiveY : Gamma.IsWarp (activeReference Z Y) :=
    activeReference_isWarp Z hY
  let W : InfiniteRunWalk Gamma.graph :=
    P.infiniteRunWalk Z.edgeWarp_isWarp hactiveY
      T.vertex_finite T.carrier_finite
  change (AltPath.infinite W.toInfiniteTrace).IndexedBackwardProvenance
    (activeReference Z Y) Nat
  exact P.infiniteIndexedBackwardProvenance Z.edgeWarp_isWarp hactiveY
    T.vertex_finite T.carrier_finite

end InfiniteTraversalBlocks

/-- The actual finite selected branch with its finite compressed-run owner
index retained. -/
noncomputable def selectedFiniteProjection_produced
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (B : BracketSimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)))
    (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y})
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQselected : B.assigned (toLiftedSource Z hYfinite z) = .finite Q) :
    ProducedAssignedPathProjection (Y := Y) Z
      (B.assigned (toLiftedSource Z hYfinite z)) z.1 := by
  let base := selectedFiniteProjection Z hboundary hY hZfinite hYfinite
    B z Q hQselected
  refine ⟨base, ?_⟩
  have hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.finite Q) := by
    have h := B.bracket_safe (toLiftedSource Z hYfinite z)
    rw [hQselected] at h
    exact h
  have hlast : Q.lastLink.direction = .forward :=
    selected_finite_last_direction_forward Z hYfinite B z Q hQselected
  have P := finiteTraceCompression_indexedBackwardProvenance
    Z Q hQ hY hlast
  change HasIndexedBackwardProvenance
    (finiteTraceCompression Z Q).path Y
  exact (HasIndexedBackwardProvenance.ofCertificate P).mono
    (activeReference_subset Z Y)

/-- The actual infinite selected branch with the omega run indexing retained. -/
noncomputable def selectedInfiniteProjection_produced
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hZedgeFinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (B : BracketSimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)))
    (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y})
    (R : InfiniteTrace (web Gamma Z).graph)
    (hR : B.assigned (toLiftedSource Z hYfinite z) = .infinite R) :
    ProducedAssignedPathProjection (Y := Y) Z
      (B.assigned (toLiftedSource Z hYfinite z)) z.1 := by
  have hbracket : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.infinite R) := by
    have h := B.bracket_safe (toLiftedSource Z hYfinite z)
    rw [hR] at h
    exact h
  have hinitial : project (AltPath.infinite R).initial ∉
      Gamma.vertexSet Y := by
    have h := selected_project_initial_outside Z hboundary hYfinite B z
    rw [hR] at h
    exact h
  let T := InfiniteTraversalFrontend.infiniteTraversalBlocks Z R hbracket
    hZfinite hZedgeFinite hYfinite hinitial
  have hinitialEq : project R.initial = z.1 := by
    have h := selected_project_initial Z hYfinite B z
    rw [hR] at h
    exact h
  rw [hR]
  let base := T.assignedPathProjection hY hZedgeFinite
    hinitialEq hinitial
  refine ⟨base, ?_⟩
  change HasIndexedBackwardProvenance (T.compile hY hZedgeFinite).path Y
  exact (HasIndexedBackwardProvenance.ofNatCertificate
    (T.compile_indexedBackwardProvenance hY hZedgeFinite)).mono
      (activeReference_subset Z Y)

/-- Case split on the selected lifted path, retaining the actual certificate
from either concrete projection branch. -/
noncomputable def producedProjectionsOfFiniteAndInfiniteBranches
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hZedgeFinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (B : BracketSimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y))) :
    forall z : {x // x ∈ Gamma.initialSet (activePaths Z) \
        Gamma.initialSet Y},
      ProducedAssignedPathProjection (Y := Y) Z
        (B.assigned (toLiftedSource Z hYfinite z)) z.1 := by
  intro z
  generalize hselected : B.assigned (toLiftedSource Z hYfinite z) = Q
  cases Q with
  | trivial w =>
      exact False.elim (assigned_ne_trivial Z hYfinite B z w hselected)
  | finite Q =>
      rw [← hselected]
      exact selectedFiniteProjection_produced Z hboundary hY hZedgeFinite
        hYfinite B z Q hselected
  | infinite R =>
      rw [← hselected]
      exact selectedInfiniteProjection_produced Z hboundary hY hZfinite
        hZedgeFinite hYfinite B z R hselected

/-- Final assignment certificate retaining actual indexed backward owners for
every assigned trace, including the empty certificate at reinserted singleton
holes. -/
structure ProducedBracketFracturedAssignment
    (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath) where
  bracket : BracketFracturedAssignment Z Y
  backward : forall z,
    HasIndexedBackwardProvenance (bracket.assignment.assigned z) Y

/-- Strong final assembly from the actual finite and infinite branch
compilers. -/
noncomputable def producedBracketFracturedAssignmentOfCompiler
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hZedgeFinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (B : BracketSimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y))) :
    ProducedBracketFracturedAssignment Z Y := by
  let P := producedProjectionsOfFiniteAndInfiniteBranches Z hboundary hY
    hZfinite hZedgeFinite hYfinite B
  let Pbase := fun z => (P z).base
  let bracket := bracketAssignmentOfActiveLiftedProjections Z hboundary hY
    hZfinite hYfinite B Pbase
  refine ⟨bracket, ?_⟩
  intro z
  change HasIndexedBackwardProvenance
    ((combineActiveAssignment Z hboundary hY hZfinite
      (activeAssignmentOfProjections Z hYfinite B Pbase)).assigned z) Y
  simp only [combineActiveAssignment]
  split
  · exact HasIndexedBackwardProvenance.trivial z.1 Y
  · exact (P _).backward

/-- Existence of the stronger, provenance-preserving assignment is an output
of the existing compiler hypotheses. -/
theorem exists_producedBracketFracturedAssignment
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hZedgeFinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths) :
    Nonempty (ProducedBracketFracturedAssignment Z Y) := by
  obtain ⟨B⟩ := exists_activeLiftedBracketAssignment Z hboundary hY
    hZfinite hYfinite hinitial
  exact ⟨producedBracketFracturedAssignmentOfCompiler Z hboundary hY
    hZfinite hZedgeFinite hYfinite B⟩

#print axioms InfiniteTraversalBlocks.compile_indexedBackwardProvenance
#print axioms selectedFiniteProjection_produced
#print axioms selectedInfiniteProjection_produced
#print axioms producedBracketFracturedAssignmentOfCompiler
#print axioms exists_producedBracketFracturedAssignment

end FracturedAssignmentPeel
end LinkageBlueprint
end Blueprint
end Erdos599
