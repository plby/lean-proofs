/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCompressedFreshSplice
import ErdosProblems.Erdos599.MovingAdvance931Compiler

/-!
# A source-faithful moving-slice occurrence request for Assertion 9.31

The scheduled endpoint belongs to the old slice, while the resulting
relation is roofed and stable at the new slice.  The older occurrence request
used one set for both roles, forcing the false side condition that the old
endpoint also lie on the new frontier.  This module separates those indices.

The relation compiler returns the actual classified whole-family occurrence
relation.  Freshness is not another opaque output: it is extracted as the
set difference by the current edge set, using the concrete no-incoming-old
incidence certificate.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Output of the occurrence-level inside/outside relation construction.
The target path is the one selected by the old-slice scheduled closure. -/
structure MovingOccurrenceWholeFamilyOutput
    (ancestor current : LinkageBlueprint Gamma Y kappa)
    {Zf : FracturedWarp Gamma}
    (assignment : CompressedFracturedAssignment Zf Y)
    (z : V) (Tnew Z persistent B : Set V)
    (targetPath : FinitePath Gamma.graph) where
  relation : CompressedWholeFamilyAdvanceSpliceRelation
    ancestor current assignment z Tnew Z persistent B
  no_incoming_old : ∀ {x y : V}, x ∈ current.vertexSet →
    (y, x) ∈ relation.splice.edge \ current.edgeSet → False
  target_path_eq : relation.splice.target_path = targetPath

namespace MovingOccurrenceWholeFamilyOutput

variable {ancestor current : LinkageBlueprint Gamma Y kappa}
variable {Zf : FracturedWarp Gamma}
variable {A : CompressedFracturedAssignment Zf Y}
variable {z : V} {Tnew Z persistent B : Set V}
variable {targetPath : FinitePath Gamma.graph}

/-- Compile the literal whole-family output to the endpoint-provenance fresh
attachment, without changing its underlying relation. -/
def toCompressedFresh
    (O : MovingOccurrenceWholeFamilyOutput ancestor current A z Tnew Z
      persistent B targetPath)
    (hinfinite : ∀ s, A.outcome s = none →
      IsPopular Gamma Y persistent kappa s.1) :
    CompressedFreshAdvanceSpliceRelation
      ancestor current A z Tnew Z persistent B :=
  O.relation.toCompressedFreshOfNoIncomingOld hinfinite O.no_incoming_old

theorem compressedFresh_target_path
    (O : MovingOccurrenceWholeFamilyOutput ancestor current A z Tnew Z
      persistent B targetPath)
    (hinfinite : ∀ s, A.outcome s = none →
      IsPopular Gamma Y persistent kappa s.1) :
    (O.toCompressedFresh hinfinite).attachment.target_path = targetPath :=
  O.target_path_eq

end MovingOccurrenceWholeFamilyOutput

/-- The moving-slice occurrence request.

`Told` occurs only in the scheduled target-path closure.  `Tnew` occurs only
in the compiled relation boundary.  The split assignment is kept in its
duplicated occurrence web and classified through the genuine projected
Claim-2 context. -/
structure MovingOccurrenceAdvance931Request
    (ancestor current : LinkageBlueprint Gamma Y kappa)
    (z : V) (Told Tnew Z persistent B : Set V) where
  before : Set V
  innerRoof : Set V
  outerRoof : Set V
  seed : Set V
  extraPaths : Set Gamma.DPath
  Preserves : FinitePath Gamma.graph → Prop
  closure : ScheduledClosureRequestWithExtraPaths Gamma Y extraPaths kappa z
    before innerRoof outerRoof Told B seed Preserves
  endpoint_mem_old : z ∈ Told
  fractured : FracturedWarp Gamma
  reference_finite : Gamma.HasFiniteCharacter Y
  duplicated : FracturedDuplication.DuplicatedFracturedAssignment fractured Y
  finite_endpoints : ∀ s v,
    (CompressedFracturedAssignment.ofDuplicated duplicated
      reference_finite).outcome s = some v →
      IsImaginaryEdge Gamma Y kappa s.1 v
  infinite_sources : ∀ s,
    (CompressedFracturedAssignment.ofDuplicated duplicated
      reference_finite).outcome s = none →
      IsPopular Gamma Y persistent kappa s.1
  target_path : FinitePath Gamma.graph
  target_path_start : target_path.start = z
  target_path_finish : target_path.finish ∈ B
  target_path_closed : target_path.support ⊆ closure.closureSet
  target_path_preserves : Preserves target_path
  auxiliary : DWeb V
  /-- The actual auxiliary is obtained from the ambient web by quotient,
  essential-part, deletion, and retargeting operations.  Hence every edge
  selected by cardinal induction is still an ambient real edge. -/
  auxiliary_edge_ambient : ∀ {x y : V}, auxiliary.graph.Adj x y →
    Gamma.graph.Adj x y
  auxiliary_unhindered : auxiliary.IsUnhindered
  source_card : #auxiliary.source ≤ kappa
  compile : ∀ L : Set auxiliary.DPath,
    CardinalInduction.IsLinkageBetween
      auxiliary auxiliary.source auxiliary.target L →
      Nonempty (MovingOccurrenceWholeFamilyOutput ancestor current
        (CompressedFracturedAssignment.ofDuplicated duplicated
          reference_finite) z Tnew Z persistent B target_path)

namespace MovingOccurrenceAdvance931Request

/-- Construct the moving request from a scheduled closure at the old slice
and the genuine occurrence projection/classification context. -/
noncomputable def ofScheduledClosureProjection
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {Told Tnew Z persistent B : Set V}
    {before innerRoof outerRoof seed : Set V}
    {extraPaths : Set Gamma.DPath}
    {Preserves : FinitePath Gamma.graph → Prop}
    (C : ScheduledClosureRequestWithExtraPaths Gamma Y extraPaths kappa z
      before innerRoof outerRoof Told B seed Preserves)
    (hzOld : z ∈ Told)
    (fractured : FracturedWarp Gamma)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (duplicated :
      FracturedDuplication.DuplicatedFracturedAssignment fractured Y)
    (projection : CompressedFracturedAssignment.ProjectionClosureContext
      duplicated hYfinite C.closureSet before innerRoof outerRoof)
    (auxiliary : DWeb V)
    (auxiliary_edge_ambient : ∀ {x y : V}, auxiliary.graph.Adj x y →
      Gamma.graph.Adj x y)
    (auxiliary_unhindered : auxiliary.IsUnhindered)
    (source_card : #auxiliary.source ≤ kappa)
    (compile : ∀ (p : FinitePath Gamma.graph),
      p.start = z → p.finish ∈ B → p.support ⊆ C.closureSet →
      Preserves p →
      ∀ L : Set auxiliary.DPath,
        CardinalInduction.IsLinkageBetween
          auxiliary auxiliary.source auxiliary.target L →
        Nonempty (MovingOccurrenceWholeFamilyOutput ancestor current
          (CompressedFracturedAssignment.ofDuplicated duplicated hYfinite)
          z Tnew Z persistent B p)) :
    MovingOccurrenceAdvance931Request
      ancestor current z Told Tnew Z persistent B := by
  let hclassified :=
    CompressedFracturedAssignment.classify_of_projectionClosureContext
      (persistent := persistent) duplicated hYfinite C.hammock_closed projection
  let hp := C.toScheduledClosureRequest.exists_scheduled_target_path hzOld
  let p := hp.choose
  exact {
    before := before
    innerRoof := innerRoof
    outerRoof := outerRoof
    seed := seed
    extraPaths := extraPaths
    Preserves := Preserves
    closure := C
    endpoint_mem_old := hzOld
    fractured := fractured
    reference_finite := hYfinite
    duplicated := duplicated
    finite_endpoints := hclassified.1
    infinite_sources := hclassified.2
    target_path := p
    target_path_start := hp.choose_spec.1
    target_path_finish := hp.choose_spec.2.1
    target_path_closed := hp.choose_spec.2.2.1
    target_path_preserves := hp.choose_spec.2.2.2
    auxiliary := auxiliary
    auxiliary_edge_ambient := auxiliary_edge_ambient
    auxiliary_unhindered := auxiliary_unhindered
    source_card := source_card
    compile := compile p hp.choose_spec.1 hp.choose_spec.2.1
      hp.choose_spec.2.2.1 hp.choose_spec.2.2.2 }

/-- Solve the auxiliary linkage and compile the honest occurrence output to
a fully predecessor-preserving moving Assertion 9.31 step. -/
theorem exists_fullyPredecessorPreservingMovingAdvance931
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    {ancestor current : LinkageBlueprint Gamma Y kappa}
    {z : V} {Told Tnew Z persistent B : Set V}
    (R : MovingOccurrenceAdvance931Request ancestor current z Told Tnew Z
      persistent B) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      MovingAdvance931 ancestor current U z Told Tnew Z persistent B ∧
        current.NoNewPredecessorsTo U := by
  obtain ⟨L, hL⟩ := CardinalInduction.isLinkable_of_source_mk_le_current
    hlower hext R.auxiliary R.auxiliary_unhindered R.source_card
  let O := (R.compile L hL).some
  exact (O.toCompressedFresh R.infinite_sources).attachment
    |>.exists_fullyPredecessorPreservingMovingAdvance931 R.endpoint_mem_old

#print axioms MovingOccurrenceWholeFamilyOutput.toCompressedFresh
#print axioms ofScheduledClosureProjection
#print axioms exists_fullyPredecessorPreservingMovingAdvance931

end MovingOccurrenceAdvance931Request
end Erdos599.Blueprint.LinkageBlueprint
