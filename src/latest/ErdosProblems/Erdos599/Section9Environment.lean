/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayTerminalDomain
import ErdosProblems.Erdos599.TerminalOutsideSplice

/-!
# Reachable-state environment for the Section 9 scheduler

The terminal scheduler must not assume a stable-successor compiler on every
abstract linkage blueprint.  Its reachable states instead carry the actual
9.30 continuation and scheduled-closure 9.31 request for each real terminal.
This file packages the reusable source geometry which produces those local
certificates and proves that certification is closed under both compiled
successors and stable limits.

The full-edge predecessor clause is retained across intermediate stages.
It is strictly stronger than the real-edge clause: imaginary edges are still
present before the final all-real limit.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u v

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- A coupled 9.30 replacement with the full-edge transition invariant
needed before the final all-real limit.  The existing
`CoupledHammockReplacement` supplies all Assertion 9.30 conclusions; this
wrapper records the additional provenance of edges entering old vertices. -/
structure FullyPredecessorPreservingCoupledHammockReplacement
    (W cut current : LinkageBlueprint Gamma Y kappa)
    (u z : V) (T : Set V) where
  replacement : CoupledHammockReplacement W cut current u z T
  no_new_predecessors : W.NoNewPredecessorsTo current

/-- Appending a genuinely fresh real path by the paper's `diamond`
operation cannot create an edge entering an old blueprint vertex.  This is
the local full-predecessor fact needed when the coupled 9.30 replacement is
realized by a concrete fresh splice. -/
theorem noNewPredecessorsTo_diamond
    (W : LinkageBlueprint Gamma Y kappa)
    (q : FinitePath (imaginaryGraph Gamma Y kappa))
    (hq : (.inl q : Path _) ∈ W.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = q.finish)
    (hfresh : W.vertexSet ∩ P.support ⊆ {q.finish}) :
    W.NoNewPredecessorsTo (W.diamond q hq P hstart hfresh) := by
  intro x y hx hxy
  rw [edgeSet_diamond W q hq P hstart hfresh] at hxy
  rcases hxy with hxy | hxy
  · exact hxy
  · have hxP : x ∈ P.support :=
      (P.edgeSet_subset_support_prod hxy).2
    have hxeq : x = q.finish := Set.mem_singleton_iff.mp
      (hfresh ⟨hx, hxP⟩)
    have hxin : (y, P.start) ∈ P.edgeSet := by
      simpa only [hstart, hxeq] using hxy
    exact False.elim
      (Alternating.FinitePath.no_incoming_edge_at_start P y hxin)

/-- The exact 9.30 cut only deletes an imaginary edge, so every cut edge is
already an edge of the ancestor. -/
theorem IsCutAt.noNewPredecessorsTo_cut
    {W cut : LinkageBlueprint Gamma Y kappa} {u : V}
    (hcut : W.IsCutAt cut u) : W.NoNewPredecessorsTo cut := by
  intro _x _y _hx hxy
  exact hcut.ordinaryExtends_original.2 hxy

/-- Package a concrete coupled replacement realized by a fresh `diamond`.
The predecessor proof is derived from the exact cut and fresh path; it is
not an additional geometric premise. -/
def FullyPredecessorPreservingCoupledHammockReplacement.ofDiamond
    {W cut : LinkageBlueprint Gamma Y kappa} {u z : V} {T : Set V}
    (hcut : W.IsCutAt cut u)
    (q : FinitePath (imaginaryGraph Gamma Y kappa))
    (hq : (.inl q : Path _) ∈ cut.paths)
    (P : FinitePath Gamma.graph) (hstart : P.start = q.finish)
    (hfresh : cut.vertexSet ∩ P.support ⊆ {q.finish})
    (R : CoupledHammockReplacement W cut
      (cut.diamond q hq P hstart hfresh) u z T) :
    FullyPredecessorPreservingCoupledHammockReplacement W cut
      (cut.diamond q hq P hstart hfresh) u z T where
  replacement := R
  no_new_predecessors := NoNewPredecessorsTo.trans
    hcut.noNewPredecessorsTo_cut
    (noNewPredecessorsTo_diamond cut q hq P hstart hfresh)
    (by
      rcases hcut with ⟨_, rfl⟩ | ⟨v, hv⟩
      · exact Subset.rfl
      · intro x hx
        simpa only [hv.vertices_eq] using hx)

/-- Full-predecessor form of the terminal-outside-slice coupled replacement
compiler. -/
def FullyPredecessorPreservingTerminalOutsideHammockReplacementCompiler
    (T Z persistent : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V)
      (Q : AltPath Gamma.graph),
    W.IsLinkageBlueprint T Z persistent →
      persistent ⊆ T →
      u ∈ W.realPart.terminals →
      u ∈ W.terminalSet → u ∉ T →
      IsSafe Y Q → Q.initial = u → Q.IsInfinite →
      Disjoint (Q.vertexSet \ {u}) W.vertexSet →
      ∃ (current : LinkageBlueprint Gamma Y kappa) (z : V),
        Nonempty (FullyPredecessorPreservingCoupledHammockReplacement
          W W current u z T)

/-- Full-predecessor form of the imaginary-successor coupled replacement
compiler. -/
def FullyPredecessorPreservingImaginarySuccessorHammockReplacementCompiler
    (T Z persistent : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u v : V)
      (Q : AltPath Gamma.graph),
    W.IsLinkageBlueprint T Z persistent →
      persistent ⊆ T →
      u ∈ W.realPart.terminals →
      (u, v) ∈ W.edgeSet →
      IsImaginaryEdge Gamma Y kappa u v →
      IsSafe Y Q → Q.initial = u → HasEnd Q (.vertex v) →
      Disjoint (hammockInterior u (.vertex v) Q) W.vertexSet →
      ∃ (cut current : LinkageBlueprint Gamma Y kappa) (z : V),
        W.IsImaginaryEdgeDeletionAt cut u v ∧
          Nonempty (FullyPredecessorPreservingCoupledHammockReplacement
            W cut current u z T)

/-- Forget the full-predecessor provenance and recover the existing
terminal-outside coupled-replacement interface. -/
theorem FullyPredecessorPreservingTerminalOutsideHammockReplacementCompiler.toCoupled
    {T Z persistent : Set V}
    (h : FullyPredecessorPreservingTerminalOutsideHammockReplacementCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent) :
    TerminalOutsideHammockReplacementCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent := by
  intro W u Q hW hpersistent hu huterm huT hsafe hinitial hinfinite hdisjoint
  obtain ⟨current, z, R⟩ := h W u Q hW hpersistent hu huterm huT
    hsafe hinitial hinfinite hdisjoint
  exact ⟨current, z, R.map
    FullyPredecessorPreservingCoupledHammockReplacement.replacement⟩

/-- Forget the full-predecessor provenance and recover the existing
imaginary-successor coupled-replacement interface. -/
theorem FullyPredecessorPreservingImaginarySuccessorHammockReplacementCompiler.toCoupled
    {T Z persistent : Set V}
    (h : FullyPredecessorPreservingImaginarySuccessorHammockReplacementCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent) :
    ImaginarySuccessorHammockReplacementCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent := by
  intro W u v Q hW hpersistent hu huv himaginary hsafe hinitial hend hdisjoint
  obtain ⟨cut, current, z, hcut, R⟩ := h W u v Q hW hpersistent hu huv
    himaginary hsafe hinitial hend hdisjoint
  exact ⟨cut, current, z, hcut, R.map
    FullyPredecessorPreservingCoupledHammockReplacement.replacement⟩

/-- Assertion 9.30 on its published all-real-terminal domain, retaining
predecessor preservation for the complete blueprint edge relation. -/
def AllRealTerminalFullyPredecessorPreservingContinuation930Compiler
    (T Z persistent B : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint T Z persistent → persistent ⊆ T →
      u ∈ W.realPart.terminals →
        ∃ (cut current : LinkageBlueprint Gamma Y kappa) (z : V),
          Continuation930 W cut current u z T B ∧
            W.NoNewPredecessorsTo current

/-- The two concrete coupled-replacement branches construct the
all-real-terminal 9.30 certificate, including its full-edge predecessor
invariant. -/
theorem allRealTerminalFullyPredecessorPreservingContinuation930Compiler_of_coupledHammockReplacement
    {T Z persistent B : Set V}
    (hkappa : aleph0 ≤ kappa)
    (hterminal :
      FullyPredecessorPreservingTerminalOutsideHammockReplacementCompiler
        (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent)
    (himaginary :
      FullyPredecessorPreservingImaginarySuccessorHammockReplacementCompiler
        (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent) :
    AllRealTerminalFullyPredecessorPreservingContinuation930Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B := by
  intro W u hW hpersistent hu
  have hWvertices : #W.vertexSet ≤ kappa :=
    W.mk_vertexSet_le_of_mk_paths_le hkappa hW.card_paths
  rcases real_terminal_is_terminal_or_has_imaginary_edge_mem hu with
      huterm | ⟨v, huv, himag⟩
  · by_cases huT : u ∈ T
    · exact ⟨W, W, u,
        continuation930_of_terminal_mem_slice hu huterm huT,
        NoNewPredecessorsTo.refl W⟩
    · have hhammock :
          HasHammockCard Gamma Y u .infinity (succ kappa) :=
        terminal_outside_slice_has_infinite_hammock
          hW hpersistent huterm huT
      obtain ⟨Q, hQsafe, hQinitial, hQinfinite, hQdisjoint⟩ :=
        exists_safe_infinite_hammock_path_avoiding hhammock hWvertices
      obtain ⟨current, z, hreplacement⟩ :=
        hterminal W u Q hW hpersistent hu huterm huT hQsafe hQinitial
          hQinfinite hQdisjoint
      exact ⟨W, current, z,
        hreplacement.some.replacement.continuation930,
        hreplacement.some.no_new_predecessors⟩
  · obtain ⟨Q, hQsafe, hQinitial, hQend, hQdisjoint⟩ :=
      exists_hammock_path_disjoint_of_mk_le himag hWvertices
    obtain ⟨cut, current, z, _hcut, hreplacement⟩ :=
      himaginary W u v Q hW hpersistent hu huv himag hQsafe hQinitial
        hQend hQdisjoint
    exact ⟨cut, current, z,
      hreplacement.some.replacement.continuation930,
      hreplacement.some.no_new_predecessors⟩

/-- A linkage blueprint together with the concrete Section 9 geometry for
every real terminal which the fair scheduler is allowed to select. -/
structure CertifiedStable934State
    (W : LinkageBlueprint Gamma Y kappa)
    (T Z persistent B : Set V) : Prop where
  isBlueprint : W.IsLinkageBlueprint T Z persistent
  stable : W.Stable T persistent
  transition : ∀ (u : V), u ∈ W.realPart.terminals →
    Nonempty (CertifiedStable934Transition W u T Z persistent B)

/-- The reusable Section 9 data.  It is an intermediate construction
package, not a public premise of the half-way clause: the scheduler consumes
only `CertifiedStable934State`s reachable from its certified seed.

The `request` field is indexed by the concrete 9.30 continuation.  It does
not assert a scheduled request for an arbitrary assignment domain and hence
does not reintroduce the invalid universal scheduled-request API. -/
structure Section9Environment
    (T Z persistent B : Set V) : Prop where
  infinite_cardinal : aleph0 ≤ kappa
  normalized : Gamma.IsNormalized
  reference_warp : Gamma.IsWarp Y
  reference_finite : Gamma.HasFiniteCharacter Y
  simultaneous_assignment : FracturedSimultaneousAssignmentStatement Gamma
  lower_induction : CardinalInduction.UniversalCardinalInductionBelow V kappa
  extension_induction : CardinalInduction.UniversalExtensionClauseAt V kappa
  persistent_subset_slice : persistent ⊆ T
  terminal_replacement :
    FullyPredecessorPreservingTerminalOutsideHammockReplacementCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent
  imaginary_replacement :
    FullyPredecessorPreservingImaginarySuccessorHammockReplacementCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent
  request : ∀ (W cut current : LinkageBlueprint Gamma Y kappa)
      (u z : V),
    W.IsLinkageBlueprint T Z persistent →
      Continuation930 W cut current u z T B →
        Nonempty (ClosureAdaptedAdvance931AuxiliaryLinkageRequest
          W current z T Z persistent B)

/-- Re-run the Section 9 construction at one real terminal of a certified
blueprint.  There is no `u ∈ T` premise: the concrete 9.30 continuation
performs the source proof's full case split and supplies an endpoint in `T`. -/
theorem Section9Environment.certifiedTransition
    {T Z persistent B : Set V}
    (E : Section9Environment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    {W : LinkageBlueprint Gamma Y kappa} {u : V}
    (hW : W.IsLinkageBlueprint T Z persistent)
    (hu : u ∈ W.realPart.terminals) :
    Nonempty (CertifiedStable934Transition W u T Z persistent B) := by
  let hcontinuation :=
    allRealTerminalFullyPredecessorPreservingContinuation930Compiler_of_coupledHammockReplacement
      (B := B) E.infinite_cardinal E.terminal_replacement
        E.imaginary_replacement
  obtain ⟨cut, current, z, hcontinuation, hnoNew⟩ :=
    hcontinuation W u hW E.persistent_subset_slice hu
  let R := (E.request W cut current u z hW hcontinuation).some
  exact ⟨{
    cut := cut
    current := current
    endpoint := z
    continuation := hcontinuation
    no_new_predecessors := hnoNew
    request := R }⟩

/-- Any blueprint satisfying the two scheduler invariants is certified by
reapplying the concrete Section 9 environment. -/
theorem Section9Environment.certify
    {T Z persistent B : Set V}
    (E : Section9Environment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (W : LinkageBlueprint Gamma Y kappa)
    (hW : W.IsLinkageBlueprint T Z persistent)
    (hstable : W.Stable T persistent) :
    CertifiedStable934State W T Z persistent B where
  isBlueprint := hW
  stable := hstable
  transition := fun _ hu ↦ E.certifiedTransition hW hu

/-- Compile the concrete transition stored at a certified state. -/
theorem CertifiedStable934State.compiledSuccessor
    {T Z persistent B : Set V}
    (E : Section9Environment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    {W : LinkageBlueprint Gamma Y kappa}
    (S : CertifiedStable934State W T Z persistent B)
    (u : V) (hu : u ∈ W.realPart.terminals) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      FullyPredecessorPreservingStable934 W U u T Z persistent B ∧
        CertifiedStable934State U T Z persistent B := by
  let C := (S.transition u hu).some
  obtain ⟨U, hU⟩ := C.compile E.lower_induction E.extension_induction
    E.normalized E.reference_warp E.reference_finite
    E.simultaneous_assignment
  exact ⟨U, hU, E.certify U hU.conclusion.1 hU.conclusion.2.1⟩

/-- A stable limit produced by Assertion 9.33 is immediately a certified
state for the next scheduler block.  No limit-specific scheduled request is
postulated: the same concrete Section 9 environment is reapplied to the
limit blueprint. -/
theorem Section9Environment.certifyStableLimit
    {I : Type v} {T Z persistent B : Set V}
    (E : Section9Environment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (stage : I → LinkageBlueprint Gamma Y kappa)
    (limit : LinkageBlueprint Gamma Y kappa)
    (hlimit : StableLimitConclusion stage limit T Z persistent B) :
    CertifiedStable934State limit T Z persistent B :=
  E.certify limit hlimit.1 hlimit.2.1

/-- A certified scheduler state whose local 9.31 transactions retain the
split-occurrence assignment.  This is the sound replacement for
`CertifiedStable934State` when fractured connector occurrences cannot be
contracted to safe alternating paths in the original web. -/
structure OccurrenceCertifiedStable934State
    (W : LinkageBlueprint Gamma Y kappa)
    (T Z persistent B : Set V) : Prop where
  isBlueprint : W.IsLinkageBlueprint T Z persistent
  stable : W.Stable T persistent
  transition : ∀ (u : V), u ∈ W.realPart.terminals →
    Nonempty (OccurrenceCertifiedStable934Transition W u T Z persistent B)

/-- Reusable Section 9 data with an occurrence-aware 9.31 request.

There is deliberately no normalization or projected simultaneous-assignment
field.  The request constructor must derive its endpoint classifications
from the duplicated-web assignment attached to the concrete continuation. -/
structure OccurrenceSection9Environment
    (T Z persistent B : Set V) : Prop where
  infinite_cardinal : aleph0 ≤ kappa
  lower_induction : CardinalInduction.UniversalCardinalInductionBelow V kappa
  extension_induction : CardinalInduction.UniversalExtensionClauseAt V kappa
  persistent_subset_slice : persistent ⊆ T
  terminal_replacement :
    FullyPredecessorPreservingTerminalOutsideHammockReplacementCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent
  imaginary_replacement :
    FullyPredecessorPreservingImaginarySuccessorHammockReplacementCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent
  request : ∀ (W cut current : LinkageBlueprint Gamma Y kappa)
      (u z : V),
    W.IsLinkageBlueprint T Z persistent →
      Continuation930 W cut current u z T B →
        Nonempty (OccurrenceClosureAdaptedAdvance931AuxiliaryLinkageRequest
          W current z T Z persistent B)

/-- Re-run the occurrence-aware Section 9 construction at one real terminal. -/
theorem OccurrenceSection9Environment.certifiedTransition
    {T Z persistent B : Set V}
    (E : OccurrenceSection9Environment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    {W : LinkageBlueprint Gamma Y kappa} {u : V}
    (hW : W.IsLinkageBlueprint T Z persistent)
    (hu : u ∈ W.realPart.terminals) :
    Nonempty (OccurrenceCertifiedStable934Transition
      W u T Z persistent B) := by
  let hcontinuation :=
    allRealTerminalFullyPredecessorPreservingContinuation930Compiler_of_coupledHammockReplacement
      (B := B) E.infinite_cardinal E.terminal_replacement
        E.imaginary_replacement
  obtain ⟨cut, current, z, hcontinuation, hnoNew⟩ :=
    hcontinuation W u hW E.persistent_subset_slice hu
  let R := (E.request W cut current u z hW hcontinuation).some
  exact ⟨{
    cut := cut
    current := current
    endpoint := z
    continuation := hcontinuation
    no_new_predecessors := hnoNew
    request := R }⟩

/-- Certify any stable linkage blueprint by reapplying the concrete
occurrence-aware Section 9 geometry. -/
theorem OccurrenceSection9Environment.certify
    {T Z persistent B : Set V}
    (E : OccurrenceSection9Environment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (W : LinkageBlueprint Gamma Y kappa)
    (hW : W.IsLinkageBlueprint T Z persistent)
    (hstable : W.Stable T persistent) :
    OccurrenceCertifiedStable934State W T Z persistent B where
  isBlueprint := hW
  stable := hstable
  transition := fun _ hu ↦ E.certifiedTransition hW hu

/-- Compile the occurrence-aware transition stored at a certified state. -/
theorem OccurrenceCertifiedStable934State.compiledSuccessor
    {T Z persistent B : Set V}
    (E : OccurrenceSection9Environment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    {W : LinkageBlueprint Gamma Y kappa}
    (S : OccurrenceCertifiedStable934State W T Z persistent B)
    (u : V) (hu : u ∈ W.realPart.terminals) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      FullyPredecessorPreservingStable934 W U u T Z persistent B ∧
        OccurrenceCertifiedStable934State U T Z persistent B := by
  let C := (S.transition u hu).some
  obtain ⟨U, hU⟩ := C.compile E.lower_induction E.extension_induction
  exact ⟨U, hU, E.certify U hU.conclusion.1 hU.conclusion.2.1⟩

/-- Stable 9.33 limits are occurrence-certified by reapplying the same
concrete continuation-indexed request constructor. -/
theorem OccurrenceSection9Environment.certifyStableLimit
    {I : Type v} {T Z persistent B : Set V}
    (E : OccurrenceSection9Environment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (stage : I → LinkageBlueprint Gamma Y kappa)
    (limit : LinkageBlueprint Gamma Y kappa)
    (hlimit : StableLimitConclusion stage limit T Z persistent B) :
    OccurrenceCertifiedStable934State limit T Z persistent B :=
  E.certify limit hlimit.1 hlimit.2.1

/-- Certified state for the source-faithful, `RealExtends`-only scheduler.
Its transitions remember the concrete 9.30 continuation and occurrence-aware
9.31 request, but make no predecessor claim about the 9.30 replacement. -/
structure SourceOccurrenceCertifiedStable934State
    (W : LinkageBlueprint Gamma Y kappa)
    (T Z persistent B : Set V) : Prop where
  isBlueprint : W.IsLinkageBlueprint T Z persistent
  stable : W.Stable T persistent
  transition : ∀ (u : V), u ∈ W.realPart.terminals →
    Nonempty (SourceOccurrenceCertifiedStable934Transition
      W u T Z persistent B)

/-- The honest all-real-terminal Section 9 environment.  The two 9.30
compilers are the ordinary coupled-replacement interfaces from the source
proof; full predecessor preservation remains a property of the fresh 9.31
attachment and is not imposed on the composite transition. -/
structure SourceOccurrenceSection9Environment
    (T Z persistent B : Set V) : Prop where
  infinite_cardinal : aleph0 ≤ kappa
  lower_induction : CardinalInduction.UniversalCardinalInductionBelow V kappa
  extension_induction : CardinalInduction.UniversalExtensionClauseAt V kappa
  persistent_subset_slice : persistent ⊆ T
  terminal_replacement :
    TerminalOutsideHammockReplacementCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent
  imaginary_replacement :
    ImaginarySuccessorHammockReplacementCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent
  request : ∀ (W cut current : LinkageBlueprint Gamma Y kappa)
      (u z : V),
    W.IsLinkageBlueprint T Z persistent →
      Continuation930 W cut current u z T B →
        Nonempty (OccurrenceClosureAdaptedAdvance931AuxiliaryLinkageRequest
          W current z T Z persistent B)

/-- Re-run the ordinary coupled 9.30 construction and attach its concrete
occurrence-aware 9.31 transaction. -/
theorem SourceOccurrenceSection9Environment.certifiedTransition
    {T Z persistent B : Set V}
    (E : SourceOccurrenceSection9Environment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    {W : LinkageBlueprint Gamma Y kappa} {u : V}
    (hW : W.IsLinkageBlueprint T Z persistent)
    (hu : u ∈ W.realPart.terminals) :
    Nonempty (SourceOccurrenceCertifiedStable934Transition
      W u T Z persistent B) := by
  let hcontinuation :=
    allRealTerminalContinuation930Compiler_of_coupledHammockReplacement
      (B := B) E.infinite_cardinal E.terminal_replacement
        E.imaginary_replacement
  obtain ⟨cut, current, z, hcontinuation⟩ :=
    hcontinuation W u hW E.persistent_subset_slice hu
  let R := (E.request W cut current u z hW hcontinuation).some
  exact ⟨{
    cut := cut
    current := current
    endpoint := z
    continuation := hcontinuation
    request := R }⟩

/-- Certify any stable reachable blueprint by re-running the source
continuation-indexed geometry. -/
theorem SourceOccurrenceSection9Environment.certify
    {T Z persistent B : Set V}
    (E : SourceOccurrenceSection9Environment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (W : LinkageBlueprint Gamma Y kappa)
    (hW : W.IsLinkageBlueprint T Z persistent)
    (hstable : W.Stable T persistent) :
    SourceOccurrenceCertifiedStable934State W T Z persistent B where
  isBlueprint := hW
  stable := hstable
  transition := fun _ hu ↦ E.certifiedTransition hW hu

/-- Compile a certified source transition and certify the resulting stable
successor. -/
theorem SourceOccurrenceCertifiedStable934State.compiledSuccessor
    {T Z persistent B : Set V}
    (E : SourceOccurrenceSection9Environment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    {W : LinkageBlueprint Gamma Y kappa}
    (S : SourceOccurrenceCertifiedStable934State W T Z persistent B)
    (u : V) (hu : u ∈ W.realPart.terminals) :
    ∃ U : LinkageBlueprint Gamma Y kappa,
      StableExtensionConclusion W U u T Z persistent B ∧
        SourceOccurrenceCertifiedStable934State U T Z persistent B := by
  let C := (S.transition u hu).some
  obtain ⟨U, hU⟩ := C.compile E.lower_induction E.extension_induction
  exact ⟨U, hU, E.certify U hU.1 hU.2.1⟩

/-- Stable 9.33 limits are source-occurrence-certified by reapplying the
same concrete continuation-indexed request constructor. -/
theorem SourceOccurrenceSection9Environment.certifyStableLimit
    {I : Type v} {T Z persistent B : Set V}
    (E : SourceOccurrenceSection9Environment
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (stage : I → LinkageBlueprint Gamma Y kappa)
    (limit : LinkageBlueprint Gamma Y kappa)
    (hlimit : StableLimitConclusion stage limit T Z persistent B) :
    SourceOccurrenceCertifiedStable934State limit T Z persistent B :=
  E.certify limit hlimit.1 hlimit.2.1

/-- Package the ordinary coupled replacements and concrete occurrence
request into the source-faithful environment. -/
theorem exists_sourceOccurrenceSection9Environment
    {T Z persistent B : Set V}
    (hkappa : aleph0 ≤ kappa)
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    (hpersistent : persistent ⊆ T)
    (hterminal : TerminalOutsideHammockReplacementCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent)
    (himaginary : ImaginarySuccessorHammockReplacementCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent)
    (hrequest : ∀ (W cut current : LinkageBlueprint Gamma Y kappa)
        (u z : V),
      W.IsLinkageBlueprint T Z persistent →
        Continuation930 W cut current u z T B →
          Nonempty (OccurrenceClosureAdaptedAdvance931AuxiliaryLinkageRequest
            W current z T Z persistent B)) :
    Nonempty (SourceOccurrenceSection9Environment
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B) :=
  ⟨{
    infinite_cardinal := hkappa
    lower_induction := hlower
    extension_induction := hext
    persistent_subset_slice := hpersistent
    terminal_replacement := hterminal
    imaginary_replacement := himaginary
    request := hrequest }⟩

/-- Package the concrete occurrence-aware inputs.  This constructor is an
internal integration seam; the final half-way theorem must discharge the
continuation-indexed request using the global closure/fracture geometry. -/
theorem exists_occurrenceSection9Environment
    {T Z persistent B : Set V}
    (hkappa : aleph0 ≤ kappa)
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    (hpersistent : persistent ⊆ T)
    (hterminal :
      FullyPredecessorPreservingTerminalOutsideHammockReplacementCompiler
        (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent)
    (himaginary :
      FullyPredecessorPreservingImaginarySuccessorHammockReplacementCompiler
        (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent)
    (hrequest : ∀ (W cut current : LinkageBlueprint Gamma Y kappa)
        (u z : V),
      W.IsLinkageBlueprint T Z persistent →
        Continuation930 W cut current u z T B →
          Nonempty (OccurrenceClosureAdaptedAdvance931AuxiliaryLinkageRequest
            W current z T Z persistent B)) :
    Nonempty (OccurrenceSection9Environment
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B) :=
  ⟨{
    infinite_cardinal := hkappa
    lower_induction := hlower
    extension_induction := hext
    persistent_subset_slice := hpersistent
    terminal_replacement := hterminal
    imaginary_replacement := himaginary
    request := hrequest }⟩

/-- Constructor exposing the exact global inputs still needed to build the
reachable-state environment.  Downstream scheduler theorems should consume
the resulting certified seed/system, not add this package as a new public
premise of `halfwayClauseStep`. -/
theorem exists_section9Environment
    {T Z persistent B : Set V}
    (hkappa : aleph0 ≤ kappa)
    (hGamma : Gamma.IsNormalized)
    (hYwarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hassignment : FracturedSimultaneousAssignmentStatement Gamma)
    (hlower : CardinalInduction.UniversalCardinalInductionBelow V kappa)
    (hext : CardinalInduction.UniversalExtensionClauseAt V kappa)
    (hpersistent : persistent ⊆ T)
    (hterminal :
      FullyPredecessorPreservingTerminalOutsideHammockReplacementCompiler
        (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent)
    (himaginary :
      FullyPredecessorPreservingImaginarySuccessorHammockReplacementCompiler
        (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent)
    (hrequest : ∀ (W cut current : LinkageBlueprint Gamma Y kappa)
        (u z : V),
      W.IsLinkageBlueprint T Z persistent →
        Continuation930 W cut current u z T B →
          Nonempty (ClosureAdaptedAdvance931AuxiliaryLinkageRequest
            W current z T Z persistent B)) :
    Nonempty (Section9Environment
      (Gamma := Gamma) (Y := Y) (kappa := kappa)
      T Z persistent B) :=
  ⟨{
    infinite_cardinal := hkappa
    normalized := hGamma
    reference_warp := hYwarp
    reference_finite := hYfinite
    simultaneous_assignment := hassignment
    lower_induction := hlower
    extension_induction := hext
    persistent_subset_slice := hpersistent
    terminal_replacement := hterminal
    imaginary_replacement := himaginary
    request := hrequest }⟩

end LinkageBlueprint
end Blueprint
end Erdos599
