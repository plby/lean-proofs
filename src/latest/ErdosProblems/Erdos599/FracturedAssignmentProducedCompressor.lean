/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedAssignmentProducedRunWalk

/-!
# Compressor inputs retained by the fractured assignment compiler

A `FiniteRunWalk` or `InfiniteRunWalk` remembers the maximal runs but forgets
the raw chronological vertex stream from which those runs were compressed.
Contact segmentation needs that stronger data.  This file therefore retains
the actual `RunCompressor.FiniteInput` or `RunCompressor.InfiniteInput` used by
the finite and infinite projection branches, together with the exact equality
to the assigned alternating path.

No ordering is reconstructed from the weaker `ProjectedRun.support_eq`
certificate: the input stored here is definitionally the one built by the
verified projection compiler.
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

/-- An assigned alternating path together with the exact chronological
compressor input that produced it.  The trivial constructor records the two
genuine no-edge branches. -/
inductive HasCompressorRealization (Q : AltPath Gamma.graph) : Type u
  | trivial (x : V) (path_eq : Q = .trivial x)
  | finite (S : RunCompressor.FiniteInput Gamma.graph)
      (path_eq : Q = .finite S.toFiniteRunWalk.toFiniteTrace)
  | infinite (S : RunCompressor.InfiniteInput Gamma.graph)
      (changes : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
      (path_eq : Q = .infinite (S.toInfiniteRunWalk changes).toInfiniteTrace)

namespace HasCompressorRealization

def ofTrivial (x : V) :
    HasCompressorRealization (Gamma := Gamma) (.trivial x) :=
  .trivial x rfl

/-- Forget only the raw compressor input while retaining its compiled run
walk. -/
def toRunWalk {Q : AltPath Gamma.graph}
    (h : HasCompressorRealization Q) : HasRunWalkRealization Q := by
  cases h with
  | trivial x hQ => exact .trivial x hQ
  | finite S hQ => exact .finite S.toFiniteRunWalk hQ
  | infinite S hchange hQ => exact .infinite (S.toInfiniteRunWalk hchange) hQ

end HasCompressorRealization

namespace InfiniteTraversalBlocks

variable {Z : FracturedWarp Gamma}
variable {Q : AltPath (web Gamma Z).graph} {M : Type v}

/-- Expose the raw loop-erased stream and change certificate used by the
infinite compiler, before maximal-run compression. -/
noncomputable def compile_compressorRealization
    (T : InfiniteTraversalBlocks (Y := Y) Z Q M)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.edgeWarp) :
    HasCompressorRealization (T.compile hY hZfinite).path := by
  let P := T.provenance
  let hactiveY : Gamma.IsWarp (activeReference Z Y) :=
    activeReference_isWarp Z hY
  let S : RunCompressor.InfiniteInput Gamma.graph :=
    P.loopErasedInput T.vertex_finite
  let hchange : ∀ n, ∃ m, n < m ∧
      S.colour m ≠ S.colour n :=
    P.loopErasedInput_changes Z.edgeWarp_isWarp hactiveY
      T.vertex_finite T.carrier_finite
  exact .infinite S hchange (by rfl)

end InfiniteTraversalBlocks

/-- One selected projection with all old provenance plus its actual raw
compressor input. -/
structure CompressorProducedAssignedPathProjection
    (Z : FracturedWarp Gamma)
    (upstairs : AltPath (web Gamma Z).graph) (source : V) where
  traversal : TraversalProducedAssignedPathProjection
    (Y := Y) Z upstairs source
  compressor : HasCompressorRealization traversal.produced.base.path

/-- The actual finite selected branch, retaining its chronological finite
input in the nonempty branch. -/
noncomputable def selectedFiniteProjection_compressorProduced
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
    CompressorProducedAssignedPathProjection (Y := Y) Z
      (B.assigned (toLiftedSource Z hYfinite z)) z.1 := by
  let traversal := selectedFiniteProjection_traversalProduced Z hboundary hY
    hZfinite hYfinite B z Q hQselected
  refine ⟨traversal, ?_⟩
  change HasCompressorRealization (finiteTraceCompression Z Q).path
  let E := (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute
  by_cases hnil : E.steps = []
  · exact .trivial (project Q.initial) (by
      simp [finiteTraceCompression, ErasedSignedRoute.compressionOfValid,
        E, hnil])
  · exact .finite (projectedFiniteTraceInput Z Q hnil)
      (finiteTraceCompression_path_eq_of_steps_ne_nil Z Q hnil)

/-- The actual infinite selected branch, retaining the loop-erased
`InfiniteInput` and its unbounded-colour-change proof. -/
noncomputable def selectedInfiniteProjection_compressorProduced
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
    CompressorProducedAssignedPathProjection (Y := Y) Z
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
  let selectedBase := T.assignedPathProjection hY hZedgeFinite
    hinitialEq hinitial
  let base : AssignedPathProjection (Y := Y) Z
      (B.assigned (toLiftedSource Z hYfinite z)) z.1 := {
    path := selectedBase.path
    starts_at := selectedBase.starts_at
    bracket_safe := selectedBase.bracket_safe
    safe := selectedBase.safe
    leaving := selectedBase.leaving
    maximal := selectedBase.maximal
    terminal_lift := by
      intro v hv
      have hnone := (T.compile hY hZedgeFinite).path.isInfinite_iff_terminal?_eq_none.mp
        (T.compile hY hZedgeFinite).infinite
      change (T.compile hY hZedgeFinite).path.terminal? = some v at hv
      rw [hnone] at hv
      contradiction }
  let produced : ProducedAssignedPathProjection (Y := Y) Z
      (B.assigned (toLiftedSource Z hYfinite z)) z.1 := ⟨base,
    (HasIndexedBackwardProvenance.ofNatCertificate
      (T.compile_indexedBackwardProvenance hY hZedgeFinite)).mono
        (activeReference_subset Z Y)⟩
  let traversal : TraversalProducedAssignedPathProjection (Y := Y) Z
      (B.assigned (toLiftedSource Z hYfinite z)) z.1 :=
    ⟨produced, T.compile_runWalkRealization hY hZedgeFinite⟩
  exact ⟨traversal, T.compile_compressorRealization hY hZedgeFinite⟩

/-- Project an explicitly selected upstairs path.  The output index remains
the original assigned path, so the selector has usable computation laws
without dependent rewriting through the assignment field. -/
noncomputable def compressorProducedProjectionOfSelectedPath
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hZedgeFinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (B : BracketSimultaneousAssignment
      (activeLiftedPaths Z) (liftedReference Z (activeReference Z Y)))
    (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y})
    (selected : {Q : AltPath (web Gamma Z).graph //
      B.assigned (toLiftedSource Z hYfinite z) = Q}) :
    CompressorProducedAssignedPathProjection (Y := Y) Z
      (B.assigned (toLiftedSource Z hYfinite z)) z.1 := by
  obtain ⟨Q, hselected⟩ := selected
  cases Q with
  | trivial w =>
      exact False.elim (assigned_ne_trivial Z hYfinite B z w hselected)
  | finite Q =>
      exact selectedFiniteProjection_compressorProduced Z hboundary hY
        hZedgeFinite hYfinite B z Q hselected
  | infinite R =>
      exact selectedInfiniteProjection_compressorProduced Z hboundary hY
        hZfinite hZedgeFinite hYfinite B z R hselected

/-- Case split on the selected upstairs path, now preserving the actual
finite or infinite compressor input. -/
noncomputable def compressorProducedProjectionsOfFiniteAndInfiniteBranches
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
      CompressorProducedAssignedPathProjection (Y := Y) Z
        (B.assigned (toLiftedSource Z hYfinite z)) z.1 := by
  intro z
  exact compressorProducedProjectionOfSelectedPath Z hboundary hY hZfinite
    hZedgeFinite hYfinite B z
      ⟨B.assigned (toLiftedSource Z hYfinite z), rfl⟩

theorem compressorProducedProjections_eq_selectedFinite
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hZedgeFinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (B : BracketSimultaneousAssignment
      (activeLiftedPaths Z) (liftedReference Z (activeReference Z Y)))
    (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y})
    (Q : FiniteTrace (web Gamma Z).graph)
    (hselected : B.assigned (toLiftedSource Z hYfinite z) = .finite Q) :
    compressorProducedProjectionsOfFiniteAndInfiniteBranches Z hboundary hY
        hZfinite hZedgeFinite hYfinite B z =
      selectedFiniteProjection_compressorProduced Z hboundary hY hZedgeFinite
        hYfinite B z Q hselected := by
  unfold compressorProducedProjectionsOfFiniteAndInfiniteBranches
  have hSigma :
      (⟨B.assigned (toLiftedSource Z hYfinite z), rfl⟩ :
        {R : AltPath (web Gamma Z).graph //
          B.assigned (toLiftedSource Z hYfinite z) = R}) =
      ⟨.finite Q, hselected⟩ := by
    apply Subtype.ext
    exact hselected
  rw [hSigma]
  rfl

theorem compressorProducedProjections_eq_selectedInfinite
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hZedgeFinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (B : BracketSimultaneousAssignment
      (activeLiftedPaths Z) (liftedReference Z (activeReference Z Y)))
    (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y})
    (R : InfiniteTrace (web Gamma Z).graph)
    (hselected : B.assigned (toLiftedSource Z hYfinite z) = .infinite R) :
    compressorProducedProjectionsOfFiniteAndInfiniteBranches Z hboundary hY
        hZfinite hZedgeFinite hYfinite B z =
      selectedInfiniteProjection_compressorProduced Z hboundary hY hZfinite
        hZedgeFinite hYfinite B z R hselected := by
  unfold compressorProducedProjectionsOfFiniteAndInfiniteBranches
  have hSigma :
      (⟨B.assigned (toLiftedSource Z hYfinite z), rfl⟩ :
        {Q : AltPath (web Gamma Z).graph //
          B.assigned (toLiftedSource Z hYfinite z) = Q}) =
      ⟨.infinite R, hselected⟩ := by
    apply Subtype.ext
    exact hselected
  rw [hSigma]
  rfl

/-- The provenance-preserving fractured assignment enriched with the actual
raw compressor input of every assigned path. -/
structure CompressorProducedBracketFracturedAssignment
    (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath) where
  traversal : TraversalProducedBracketFracturedAssignment Z Y
  compressor : forall z,
    HasCompressorRealization
      (traversal.produced.bracket.assignment.assigned z)

/-- Assemble the compressor-enriched certificate from the actual branch
compilers. -/
noncomputable def compressorProducedBracketFracturedAssignmentOfCompiler
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hZedgeFinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (B : BracketSimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y))) :
    CompressorProducedBracketFracturedAssignment Z Y := by
  let P := compressorProducedProjectionsOfFiniteAndInfiniteBranches Z
    hboundary hY hZfinite hZedgeFinite hYfinite B
  let Pbase := fun z => (P z).traversal.produced.base
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
    · exact (P _).traversal.produced.backward⟩
  let traversal : TraversalProducedBracketFracturedAssignment Z Y :=
    ⟨produced, by
      intro z
      change HasRunWalkRealization
        ((combineActiveAssignment Z hboundary hY hZfinite
          (activeAssignmentOfProjections Z hYfinite B Pbase)).assigned z)
      simp only [combineActiveAssignment]
      split
      · exact HasRunWalkRealization.ofTrivial z.1
      · exact (P _).traversal.realization⟩
  refine ⟨traversal, ?_⟩
  intro z
  change HasCompressorRealization
    ((combineActiveAssignment Z hboundary hY hZfinite
      (activeAssignmentOfProjections Z hYfinite B Pbase)).assigned z)
  simp only [combineActiveAssignment]
  split
  · exact HasCompressorRealization.ofTrivial z.1
  · exact (P _).compressor

/-- Existence under the same hypotheses as the existing produced
assignment. -/
theorem exists_compressorProducedBracketFracturedAssignment
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hZedgeFinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths) :
    Nonempty (CompressorProducedBracketFracturedAssignment Z Y) := by
  obtain ⟨B⟩ := exists_activeLiftedBracketAssignment Z hboundary hY
    hZfinite hYfinite hinitial
  exact ⟨compressorProducedBracketFracturedAssignmentOfCompiler Z
    hboundary hY hZfinite hZedgeFinite hYfinite B⟩

namespace CompressorProducedBracketFracturedAssignment

/-- Finite-proxy promotion changes owner certificates only, hence leaves the
stored chronological compressor input literally unchanged. -/
noncomputable def liftFiniteProxy
    {F : FracturedWarp Gamma}
    (hboundary : BoundaryAligned F.paths Y)
    (hY : Gamma.IsWarp Y)
    (B : CompressorProducedBracketFracturedAssignment F
      (finiteProxyReference Y)) :
    CompressorProducedBracketFracturedAssignment F Y where
  traversal := B.traversal.liftFiniteProxy hboundary hY
  compressor z := by
    change HasCompressorRealization
      (B.traversal.produced.bracket.assignment.assigned
        (toFiniteProxySource z))
    exact B.compressor (toFiniteProxySource z)

end CompressorProducedBracketFracturedAssignment

/-- Arbitrary-reference form of the compressor-input-producing compiler. -/
theorem exists_compressorProducedBracketFracturedAssignment_anyReference
    (F : FracturedWarp Gamma)
    (hboundary : BoundaryAligned F.paths Y)
    (hY : Gamma.IsWarp Y)
    (hFfinite : Gamma.HasFiniteCharacter F.paths)
    (hFedgeFinite : Gamma.HasFiniteCharacter F.edgeWarp)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet F.paths) :
    Nonempty (CompressorProducedBracketFracturedAssignment F Y) := by
  have hinitialProxy :
      Gamma.initialSet (finiteProxyReference Y) ⊆
        Gamma.initialSet F.paths := by
    rwa [initialSet_finiteProxyReference]
  obtain ⟨B⟩ := exists_compressorProducedBracketFracturedAssignment F
    (_root_.Erdos599.Blueprint.LinkageBlueprint.BoundaryAligned.finiteProxyReference
      hboundary)
    (finiteProxyReference_isWarp hY) hFfinite hFedgeFinite
    (finiteProxyReference_hasFiniteCharacter Y) hinitialProxy
  exact ⟨B.liftFiniteProxy hboundary hY⟩

namespace OutsideFracturedWarp

variable {W : Set Gamma.DPath} {X : Set V}

/-- Cut-facing arbitrary-reference form retaining actual compressor input. -/
theorem exists_compressorProducedBracketFracturedAssignment_anyReference
    (F : OutsideFracturedWarp W X)
    (hboundary : BoundaryAligned F.holes.paths Y)
    (hY : Gamma.IsWarp Y)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet F.holes.paths) :
    Nonempty (CompressorProducedBracketFracturedAssignment F.holes Y) :=
  FracturedAssignmentPeel.exists_compressorProducedBracketFracturedAssignment_anyReference
    F.holes hboundary hY F.finiteCharacter F.edgeWarpFiniteCharacter hinitial

end OutsideFracturedWarp

#print axioms InfiniteTraversalBlocks.compile_compressorRealization
#print axioms selectedFiniteProjection_compressorProduced
#print axioms selectedInfiniteProjection_compressorProduced
#print axioms compressorProducedBracketFracturedAssignmentOfCompiler
#print axioms exists_compressorProducedBracketFracturedAssignment
#print axioms CompressorProducedBracketFracturedAssignment.liftFiniteProxy
#print axioms exists_compressorProducedBracketFracturedAssignment_anyReference
#print axioms OutsideFracturedWarp.exists_compressorProducedBracketFracturedAssignment_anyReference

end FracturedAssignmentPeel
end LinkageBlueprint
end Blueprint
end Erdos599
