/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ArbitraryReferenceProducedBackwardProvenance

/-!
# Run-walk realizations retained by the fractured assignment compiler

The fractured projection compilers construct their nontrivial output by
compressing a concrete finite or infinite run walk.  The ordinary assignment
and the backward-owner certificate deliberately forget that construction.
This file adds a certificate which retains it, without changing any of the
existing assignment APIs.

The zero-edge finite branch and the singleton holes reinserted after active
projection are recorded as literal trivial paths.  Every other finite branch
is the exact trace of `projectedFiniteTraceInput`, and every infinite branch
is the exact trace of the run walk constructed by the infinite provenance
compiler.  Thus downstream contact segmentation can work with the ordered
runs actually used by the proof rather than an abstract alternating path.
-/

noncomputable section

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace FracturedAssignmentPeel

open Set DirectedPath _root_.Erdos599.Alternating
open Alternating.FracturedDuplication
open PopularAuxiliary.Input

universe u v

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}

/-- An alternating path together with the exact concrete run-walk shape from
which it was compiled.  The equality is retained explicitly so consumers can
transport ordered-run constructions without unfolding the compiler. -/
inductive HasRunWalkRealization (Q : AltPath Gamma.graph) : Type u
  | trivial (x : V) (path_eq : Q = .trivial x)
  | finite (W : FiniteRunWalk Gamma.graph)
      (path_eq : Q = .finite W.toFiniteTrace)
  | infinite (W : InfiniteRunWalk Gamma.graph)
      (path_eq : Q = .infinite W.toInfiniteTrace)

namespace HasRunWalkRealization

/-- The canonical realization of a literal trivial path. -/
def ofTrivial (x : V) :
    HasRunWalkRealization (Gamma := Gamma) (.trivial x) :=
  .trivial x rfl

end HasRunWalkRealization

/-- The existing concrete projection and its exact run-walk realization. -/
structure TraversalProducedAssignedPathProjection
    (Z : FracturedWarp Gamma)
    (upstairs : AltPath (web Gamma Z).graph) (source : V) where
  produced : ProducedAssignedPathProjection (Y := Y) Z upstairs source
  realization : HasRunWalkRealization produced.base.path

namespace InfiniteTraversalBlocks

variable {Z : FracturedWarp Gamma}
variable {Q : AltPath (web Gamma Z).graph} {M : Type v}

/-- Expose the exact infinite run walk used by `compile`. -/
noncomputable def compile_runWalkRealization
    (T : InfiniteTraversalBlocks (Y := Y) Z Q M)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.edgeWarp) :
    HasRunWalkRealization (T.compile hY hZfinite).path := by
  let P := T.provenance
  let W : InfiniteRunWalk Gamma.graph :=
    P.infiniteRunWalk Z.edgeWarp_isWarp (activeReference_isWarp Z hY)
      T.vertex_finite T.carrier_finite
  exact .infinite W (by rfl)

end InfiniteTraversalBlocks

/-- The actual finite selected branch, retaining both indexed backward
owners and its exact finite run walk (or the genuine zero-edge trivial
result). -/
noncomputable def selectedFiniteProjection_traversalProduced
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
    TraversalProducedAssignedPathProjection (Y := Y) Z
      (B.assigned (toLiftedSource Z hYfinite z)) z.1 := by
  let produced := selectedFiniteProjection_produced Z hboundary hY
    hZfinite hYfinite B z Q hQselected
  refine ⟨produced, ?_⟩
  change HasRunWalkRealization (finiteTraceCompression Z Q).path
  let E := (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute
  by_cases hnil : E.steps = []
  · exact .trivial (project Q.initial) (by
      simp [finiteTraceCompression, ErasedSignedRoute.compressionOfValid,
        E, hnil])
  · exact HasRunWalkRealization.finite
      (projectedFiniteTraceInput Z Q hnil).toFiniteRunWalk
      (finiteTraceCompression_path_eq_of_steps_ne_nil Z Q hnil)

/-- The actual infinite selected branch, retaining both indexed backward
owners and the exact omega run walk used by the infinite compiler. -/
noncomputable def selectedInfiniteProjection_traversalProduced
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
    TraversalProducedAssignedPathProjection (Y := Y) Z
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
  let produced : ProducedAssignedPathProjection (Y := Y) Z
      (.infinite R) z.1 := ⟨base,
    (HasIndexedBackwardProvenance.ofNatCertificate
      (T.compile_indexedBackwardProvenance hY hZedgeFinite)).mono
        (activeReference_subset Z Y)⟩
  refine ⟨produced, ?_⟩
  change HasRunWalkRealization (T.compile hY hZedgeFinite).path
  exact T.compile_runWalkRealization hY hZedgeFinite

/-- Case split on the path selected upstairs, retaining the concrete
realization produced by the corresponding finite or infinite compiler. -/
noncomputable def traversalProducedProjectionsOfFiniteAndInfiniteBranches
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
      TraversalProducedAssignedPathProjection (Y := Y) Z
        (B.assigned (toLiftedSource Z hYfinite z)) z.1 := by
  intro z
  generalize hselected : B.assigned (toLiftedSource Z hYfinite z) = Q
  cases Q with
  | trivial w =>
      exact False.elim (assigned_ne_trivial Z hYfinite B z w hselected)
  | finite Q =>
      rw [← hselected]
      exact selectedFiniteProjection_traversalProduced Z hboundary hY
        hZedgeFinite hYfinite B z Q hselected
  | infinite R =>
      rw [← hselected]
      exact selectedInfiniteProjection_traversalProduced Z hboundary hY
        hZfinite hZedgeFinite hYfinite B z R hselected

/-- The provenance-preserving fractured assignment enriched with an exact
run-walk realization of every assigned path. -/
structure TraversalProducedBracketFracturedAssignment
    (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath) where
  produced : ProducedBracketFracturedAssignment Z Y
  realization : forall z,
    HasRunWalkRealization (produced.bracket.assignment.assigned z)

/-- Assemble the enriched certificate from the actual finite and infinite
branch compilers.  Singleton holes omitted from active projection are
reinserted with their literal trivial realization. -/
noncomputable def traversalProducedBracketFracturedAssignmentOfCompiler
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hZedgeFinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (B : BracketSimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y))) :
    TraversalProducedBracketFracturedAssignment Z Y := by
  let P := traversalProducedProjectionsOfFiniteAndInfiniteBranches Z
    hboundary hY hZfinite hZedgeFinite hYfinite B
  let Pbase := fun z => (P z).produced.base
  let bracket := bracketAssignmentOfActiveLiftedProjections Z hboundary hY
    hZfinite hYfinite B Pbase
  let produced : ProducedBracketFracturedAssignment Z Y := ⟨bracket, by
    intro z
    change HasIndexedBackwardProvenance
      ((combineActiveAssignment Z hboundary hY hZfinite
        (activeAssignmentOfProjections Z hYfinite B Pbase)).assigned z) Y
    simp only [combineActiveAssignment]
    split
    · exact HasIndexedBackwardProvenance.trivial z.1 Y
    · exact (P _).produced.backward⟩
  refine ⟨produced, ?_⟩
  intro z
  change HasRunWalkRealization
    ((combineActiveAssignment Z hboundary hY hZfinite
      (activeAssignmentOfProjections Z hYfinite B Pbase)).assigned z)
  simp only [combineActiveAssignment]
  split
  · exact HasRunWalkRealization.ofTrivial z.1
  · exact (P _).realization

/-- Existence of the enriched certificate follows from the same compiler
hypotheses as the ordinary fractured assignment. -/
theorem exists_traversalProducedBracketFracturedAssignment
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hZedgeFinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths) :
    Nonempty (TraversalProducedBracketFracturedAssignment Z Y) := by
  obtain ⟨B⟩ := exists_activeLiftedBracketAssignment Z hboundary hY
    hZfinite hYfinite hinitial
  exact ⟨traversalProducedBracketFracturedAssignmentOfCompiler Z
    hboundary hY hZfinite hZedgeFinite hYfinite B⟩

namespace TraversalProducedBracketFracturedAssignment

/-- Reindex to the full arbitrary-reference source domain.  Finite-proxy
promotion changes only owner certificates, so every run-walk realization is
literally unchanged. -/
noncomputable def liftFiniteProxy
    {F : FracturedWarp Gamma}
    (hboundary : BoundaryAligned F.paths Y)
    (hY : Gamma.IsWarp Y)
    (B : TraversalProducedBracketFracturedAssignment F
      (finiteProxyReference Y)) :
    TraversalProducedBracketFracturedAssignment F Y where
  produced := B.produced.liftFiniteProxy hboundary hY
  realization z := by
    change HasRunWalkRealization
      (B.produced.bracket.assignment.assigned (toFiniteProxySource z))
    exact B.realization (toFiniteProxySource z)

end TraversalProducedBracketFracturedAssignment

/-- Arbitrary-reference form of the exact traversal-producing compiler. -/
theorem exists_traversalProducedBracketFracturedAssignment_anyReference
    (F : FracturedWarp Gamma)
    (hboundary : BoundaryAligned F.paths Y)
    (hY : Gamma.IsWarp Y)
    (hFfinite : Gamma.HasFiniteCharacter F.paths)
    (hFedgeFinite : Gamma.HasFiniteCharacter F.edgeWarp)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet F.paths) :
    Nonempty (TraversalProducedBracketFracturedAssignment F Y) := by
  have hinitialProxy :
      Gamma.initialSet (finiteProxyReference Y) ⊆
        Gamma.initialSet F.paths := by
    rwa [initialSet_finiteProxyReference]
  obtain ⟨B⟩ := exists_traversalProducedBracketFracturedAssignment F
    (_root_.Erdos599.Blueprint.LinkageBlueprint.BoundaryAligned.finiteProxyReference
      hboundary)
    (finiteProxyReference_isWarp hY) hFfinite hFedgeFinite
    (finiteProxyReference_hasFiniteCharacter Y) hinitialProxy
  exact ⟨B.liftFiniteProxy hboundary hY⟩

namespace OutsideFracturedWarp

variable {W : Set Gamma.DPath} {X : Set V}

/-- Cut-facing arbitrary-reference form of the exact traversal-producing
compiler. -/
theorem exists_traversalProducedBracketFracturedAssignment_anyReference
    (F : OutsideFracturedWarp W X)
    (hboundary : BoundaryAligned F.holes.paths Y)
    (hY : Gamma.IsWarp Y)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet F.holes.paths) :
    Nonempty (TraversalProducedBracketFracturedAssignment F.holes Y) :=
  FracturedAssignmentPeel.exists_traversalProducedBracketFracturedAssignment_anyReference
    F.holes hboundary hY F.finiteCharacter F.edgeWarpFiniteCharacter hinitial

end OutsideFracturedWarp

#print axioms InfiniteTraversalBlocks.compile_runWalkRealization
#print axioms selectedFiniteProjection_traversalProduced
#print axioms selectedInfiniteProjection_traversalProduced
#print axioms traversalProducedBracketFracturedAssignmentOfCompiler
#print axioms exists_traversalProducedBracketFracturedAssignment
#print axioms TraversalProducedBracketFracturedAssignment.liftFiniteProxy
#print axioms exists_traversalProducedBracketFracturedAssignment_anyReference
#print axioms OutsideFracturedWarp.exists_traversalProducedBracketFracturedAssignment_anyReference

end FracturedAssignmentPeel
end LinkageBlueprint
end Blueprint
end Erdos599
