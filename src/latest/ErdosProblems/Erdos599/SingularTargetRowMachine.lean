/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularExtension
import ErdosProblems.Erdos599.SingularBoundarySplit
import ErdosProblems.Erdos599.SingularPendingDecomposition
import ErdosProblems.Erdos599.SingularQuotientReentry
import ErdosProblems.Erdos599.SingularTargetLinkTransfer

/-!
# The concrete singular target-row machine

This module constructs the private-state machine used in Assertion 9.17.
The elementary lemmas in the first section discharge the exact source and
cardinal bookkeeping for one simultaneous competitor-closing step.  The
geometric state records the separating stop-over, quotient unhinderedness,
and finite-character continuation data which are needed to choose the next
row without making a successor choice for an arbitrary row.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularTargetRowMachine

open SingularExtension SingularMatrix SingularBoundarySplit
  SingularPendingDecomposition SingularContinuation SliceSpliceSource

universe u

variable {V : Type u}

/-! ## The split geometric state

The target row itself need not be terminal-clean: a component which has
already reached the target can cross a later stop-over before its terminal.
Only the still-pending components are used in the next quotient star.  The
following record is therefore the invariant which can actually be iterated.
It deliberately keeps the ordinary row fields outside the record: those are
already carried by `TargetRowStage`.
-/

/-- Geometric data for a target row after completed target components have
been split off.  The clean and boundary pending pieces are the exact pieces
from `SingularPendingDecomposition`; no cleanliness assertion is made about
the completed part. -/
structure SplitStopover (G : DWeb V) (W : Set G.DPath) where
  boundary : Set V
  separator : IsSeparatorFrom G G.source boundary
  minimal : IsTrimmedSeparator G boundary
  quotient_unhindered : (G.quotient boundary).IsUnhindered
  terminal_subset : G.terminalFrontier W ⊆ boundary
  clean_pending_roof :
    G.vertexSet (cleanPendingPart G W boundary) ⊆ G.roof boundary
  clean_pending_terminalClean :
    TerminalCleanAt G (cleanPendingPart G W boundary) boundary
  /-- A pending component which starts on the boundary has no old edge to
  preserve.  This is the exact condition under which its initial vertex may
  be used directly as a quotient request. -/
  boundary_pending_trivial :
    ∀ p ∈ boundaryPendingPart G W boundary,
      p = G.trivialPath p.initial

namespace SplitStopover

/-- Every separating half-way stop-over supplies the geometric split
certificate.  Only the outside pending components are asserted to be
roofed and terminal-clean; boundary-starting components remain explicitly
outside that assertion. -/
def ofSeparatingHalfwayStopover
    {G : DWeb V} {W : Set G.DPath} {D : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (htrivial : ∀ p ∈ boundaryPendingPart G W D,
      p = G.trivialPath p.initial) : SplitStopover G W where
  boundary := D
  separator := hD.separator
  minimal := hD.stopover.minimal
  quotient_unhindered := hD.quotient_unhindered
  terminal_subset := hD.linkage.terminalFrontier_subset
  clean_pending_roof := by
    rintro x ⟨p, hp, hxp⟩
    exact outsidePart_vertexSet_subset_roof hD.linkage hD.separator
      ⟨p, ⟨hp.1.1, hp.2⟩, hxp⟩
  clean_pending_terminalClean := cleanPendingPart_terminalClean hD.linkage
  boundary_pending_trivial := htrivial

theorem quotient_source_eq {G : DWeb V} {W : Set G.DPath}
    (S : SplitStopover G W) :
    (G.quotient S.boundary).source = S.boundary :=
  quotient_source_eq_stopover G S.separator S.minimal

theorem pendingRequests_subset_quotientSource
    {G : DWeb V} {W : Set G.DPath}
    (S : SplitStopover G W)
    (hW : IsLinkageBetween G G.source S.boundary W) :
    pendingRequests G W S.boundary ⊆
      (G.quotient S.boundary).source := by
  rw [S.quotient_source_eq]
  exact pendingRequests_subset hW

end SplitStopover

/-- Every source introduced by a competitor step is still an ambient source,
provided all participating path families have ambient-source initials. -/
theorem nextTargetSources_subset_source
    {I : Type u} {G : DWeb V} {fixed : Set G.DPath}
    (hfixed : G.initialSet fixed ⊆ G.source)
    (S : TargetRowStage G I)
    (hsources : ∀ i, S.sources i ⊆ G.source) (i : I) :
    nextTargetSources G fixed S i ⊆ G.source := by
  rintro x (hx | hx)
  · exact hsources i hx
  · obtain ⟨a, _ha, p, hpAll, _hpa, q, hqAll, hqx, _hpq⟩ := hx
    rcases hqAll with hqFixed | hqRows
    · apply hfixed
      exact ⟨q, hqFixed, hqx⟩
    · obtain ⟨j, hqj⟩ := Set.mem_iUnion.1 hqRows
      rw [← S.initialSet j]
      exact ⟨q, hqj, hqx⟩

/-- One simultaneous competitor step has cardinality at most the scale of
its column. -/
theorem mk_nextTargetSources_le
    {I : Type u} {G : DWeb V} {fixed : Set G.DPath}
    (hfixed : G.IsWarp fixed) (S : TargetRowStage G I)
    {rho : Cardinal.{u}} (hrho : aleph0 ≤ rho)
    (hI : #I ≤ rho) (i : I) (hsource : #(S.sources i) ≤ rho) :
    #(nextTargetSources G fixed S i) ≤ rho := by
  unfold nextTargetSources DWeb.competitorStep
  refine (Cardinal.mk_union_le _ _).trans ?_
  exact Cardinal.add_le_of_le hrho hsource
    (G.mk_competitorClosure_fixed_iUnion_le fixed S.paths (S.sources i)
      hfixed S.isWarp hrho hI hsource)

/-- Since the competitor operation is inflationary, an exact-size source
row remains of exactly that size after one bounded step. -/
theorem mk_nextTargetSources_eq
    {I : Type u} {G : DWeb V} {fixed : Set G.DPath}
    (hfixed : G.IsWarp fixed) (S : TargetRowStage G I)
    {rho : Cardinal.{u}} (hrho : aleph0 ≤ rho)
    (hI : #I ≤ rho) (i : I) (hexact : #(S.sources i) = rho) :
    #(nextTargetSources G fixed S i) = rho := by
  apply le_antisymm
  · exact mk_nextTargetSources_le hfixed S hrho hI i hexact.le
  · rw [← hexact]
    apply Cardinal.mk_le_mk_of_subset
    exact fun _ hx ↦ Or.inl hx

/-! The cardinal change-of-coordinates at an old terminal does not require
the old row to be a linkage to one common stop-over.  Warpness, finite
character, and full initial coverage are the exact hypotheses.  This weaker
form is needed after completed target components have been split from the
clean pending row. -/

theorem exists_path_to_requestedFrontier_of_structural
    {G : DWeb V} {W : Set G.DPath} {A : Set V}
    (hfinite : G.HasFiniteCharacter W)
    (hinitial : G.initialSet W = G.source)
    (hA : A ⊆ G.source) {a : V} (ha : a ∈ A) :
    ∃ p ∈ initialRestriction G W A,
      p.initial = a ∧
      ∃ t : requestedFrontier G W A, G.terminal? p = some t.1 := by
  have haInitial : a ∈ G.initialSet W := hinitial.symm ▸ hA ha
  obtain ⟨p, hpW, hpInitial⟩ := haInitial
  obtain ⟨f, rfl⟩ := hfinite hpW
  have hfA : DirectedPath.Path.initial (Sum.inl f : G.DPath) ∈ A :=
    hpInitial ▸ ha
  let t : requestedFrontier G W A :=
    ⟨f.finish, ⟨.inl f, ⟨hpW, hfA⟩, rfl⟩⟩
  exact ⟨.inl f, ⟨hpW, hfA⟩, hpInitial, t, rfl⟩

theorem requestedInitial_surjective_of_structural
    {G : DWeb V} {W : Set G.DPath} {A : Set V}
    (hwarp : G.IsWarp W)
    (hfinite : G.HasFiniteCharacter W)
    (hinitial : G.initialSet W = G.source)
    (hA : A ⊆ G.source) :
    Function.Surjective (requestedInitial G W A) := by
  rintro ⟨a, ha⟩
  obtain ⟨p, hp, hpInitial, t, hpTerminal⟩ :=
    exists_path_to_requestedFrontier_of_structural hfinite hinitial hA ha
  have hpath : requestedPath G W A t = p := by
    by_contra hne
    have hdis := hwarp
      (requestedPath_spec G W A t).1.1 hp.1 hne
    exact Set.disjoint_left.1 hdis
      (G.terminal_mem_support (requestedPath_spec G W A t).2)
      (G.terminal_mem_support hpTerminal)
  refine ⟨t, ?_⟩
  apply Subtype.ext
  change (requestedPath G W A t).initial = a
  exact (congrArg (fun q : G.DPath ↦ q.initial) hpath).trans hpInitial

theorem mk_requestedFrontier_eq_of_structural
    {G : DWeb V} {W : Set G.DPath} {A : Set V}
    (hwarp : G.IsWarp W)
    (hfinite : G.HasFiniteCharacter W)
    (hinitial : G.initialSet W = G.source)
    (hA : A ⊆ G.source) :
    #(requestedFrontier G W A) = #A := by
  apply le_antisymm
  · exact mk_requestedFrontier_le hwarp
  · exact Cardinal.mk_le_of_surjective
      (requestedInitial_surjective_of_structural
        hwarp hfinite hinitial hA)

/-- The requested old terminals form a legitimate source row in the
quotient by a separating trimmed stop-over. -/
theorem requestedFrontier_subset_quotientSource
    {G : DWeb V} {W : Set G.DPath} {D A : Set V}
    (hD : IsSeparatingHalfwayStopover G W D) :
    requestedFrontier G W A ⊆ (G.quotient D).source := by
  intro x hx
  rw [hD.quotient_source_eq]
  exact hD.linkage.terminalFrontier_subset
    ⟨hx.choose, hx.choose_spec.1.1, hx.choose_spec.2⟩

/-- The lower induction hypothesis supplies the exact quotient half-way row
requested by one competitor-closed column.  The request has the same
cardinality as the old source row because a finite full linkage has exactly
one terminal component for each requested initial vertex. -/
theorem exists_quotientHalfwayForNext
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {G : DWeb V} {fixed : Set G.DPath}
    (hfixedWarp : G.IsWarp fixed)
    (hfixedInitial : G.initialSet fixed ⊆ G.source)
    (S : TargetRowStage G (Index kappa))
    (hsource : ∀ i,
      S.sources i ⊆ G.source ∧
        #(S.sources i) = scale kappa hkappa hsingular i)
    (D : Index kappa → Set V)
    (hD : ∀ i, IsSeparatingHalfwayStopover G (S.paths i) (D i))
    (i : Index kappa) :
    let T := nextTargetSources G fixed S i
    let A := requestedFrontier G (S.paths i) T
    ∃ U : Set (G.quotient (D i)).DPath,
      IsHalfwayLinkageOfAltitude (G.quotient (D i)) A
        (scale kappa hkappa hsingular i) U := by
  dsimp only
  let rho := scale kappa hkappa hsingular i
  have hrho : aleph0 ≤ rho := scale_infinite kappa hkappa hsingular i
  have hI : #(Index kappa) ≤ rho :=
    scale_index_le kappa hkappa hsingular i
  have hTcard : #(nextTargetSources G fixed S i) = rho :=
    mk_nextTargetSources_eq hfixedWarp S hrho hI i (hsource i).2
  have hTsub : nextTargetSources G fixed S i ⊆ G.source := by
    exact nextTargetSources_subset_source hfixedInitial S
      (fun j ↦ (hsource j).1) i
  have hAcard :
      #(requestedFrontier G (S.paths i)
          (nextTargetSources G fixed S i)) = rho := by
    rw [mk_requestedFrontier_eq (hD i).linkage hTsub, hTcard]
  have hAsub : requestedFrontier G (S.paths i)
      (nextTargetSources G fixed S i) ⊆ (G.quotient (D i)).source :=
    requestedFrontier_subset_quotientSource (hD i)
  have hlowerRho := hlower rho
    (scale_below kappa hkappa hsingular i)
      (G.quotient (D i)) (hD i).quotient_unhindered
  exact hlowerRho.halfway hrho _ hAsub hAcard

/-- Split-row form of `exists_quotientHalfwayForNext`.  Completed target
components may make the whole row fail endpoint cleanliness, so this version
uses only the structural row fields and the split stop-over's terminal and
quotient-source certificates. -/
theorem exists_quotientHalfwayForNext_split
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {G : DWeb V} {fixed : Set G.DPath}
    (hfixedWarp : G.IsWarp fixed)
    (hfixedInitial : G.initialSet fixed ⊆ G.source)
    (S : TargetRowStage G (Index kappa))
    (hsource : ∀ i,
      S.sources i ⊆ G.source ∧
        #(S.sources i) = scale kappa hkappa hsingular i)
    (D : ∀ i, SplitStopover G (S.paths i))
    (i : Index kappa) :
    let T := nextTargetSources G fixed S i
    let A := requestedFrontier G (S.paths i) T
    ∃ U : Set (G.quotient (D i).boundary).DPath,
      IsHalfwayLinkageOfAltitude (G.quotient (D i).boundary) A
        (scale kappa hkappa hsingular i) U := by
  dsimp only
  let rho := scale kappa hkappa hsingular i
  have hrho : aleph0 ≤ rho := scale_infinite kappa hkappa hsingular i
  have hI : #(Index kappa) ≤ rho :=
    scale_index_le kappa hkappa hsingular i
  have hTcard : #(nextTargetSources G fixed S i) = rho :=
    mk_nextTargetSources_eq hfixedWarp S hrho hI i (hsource i).2
  have hTsub : nextTargetSources G fixed S i ⊆ G.source :=
    nextTargetSources_subset_source hfixedInitial S
      (fun j ↦ (hsource j).1) i
  have hAcard :
      #(requestedFrontier G (S.paths i)
          (nextTargetSources G fixed S i)) = rho := by
    rw [mk_requestedFrontier_eq_of_structural
      (S.isWarp i) (S.finiteCharacter i) (S.initialSet i) hTsub,
      hTcard]
  have hAsub : requestedFrontier G (S.paths i)
      (nextTargetSources G fixed S i) ⊆
      (G.quotient (D i).boundary).source := by
    rw [(D i).quotient_source_eq]
    rintro x ⟨p, hp, hpx⟩
    exact (D i).terminal_subset ⟨p, hp.1, hpx⟩
  have hlowerRho := hlower rho
    (scale_below kappa hkappa hsingular i)
      (G.quotient (D i).boundary) (D i).quotient_unhindered
  exact hlowerRho.halfway hrho _ hAsub hAcard

/-! ## Iterating a sound split successor

The remaining geometry is isolated in one transition predicate.  Once a
successor supplies both its displayed row and the next split certificate,
the private-state `TargetRowMachine` is a direct choice recursion. -/

/-- A simultaneous target row together with its per-column completed/pending
stop-over certificates. -/
structure SplitTargetRowStage (G : DWeb V) (I : Type u) where
  row : TargetRowStage G I
  split : ∀ i, SplitStopover G (row.paths i)

/-- The exact one-step output required from the completed/pending re-entry
construction. -/
def SplitTargetRowSuccessorRule {I : Type u} (G : DWeb V)
    (fixed : Set G.DPath) : Prop :=
  ∀ S : SplitTargetRowStage G I,
    ∃ T : SplitTargetRowStage G I,
      T.row.sources = nextTargetSources G fixed S.row ∧
      ∀ i, G.ForwardExtension (S.row.paths i) (T.row.paths i)

noncomputable def nextSplitTargetRowStage {I : Type u} (G : DWeb V)
    (fixed : Set G.DPath)
    (hstep : SplitTargetRowSuccessorRule (I := I) G fixed)
    (S : SplitTargetRowStage G I) : SplitTargetRowStage G I :=
  Classical.choose (hstep S)

theorem nextSplitTargetRowStage_sources {I : Type u} (G : DWeb V)
    (fixed : Set G.DPath)
    (hstep : SplitTargetRowSuccessorRule (I := I) G fixed)
    (S : SplitTargetRowStage G I) :
    (nextSplitTargetRowStage G fixed hstep S).row.sources =
      nextTargetSources G fixed S.row :=
  (Classical.choose_spec (hstep S)).1

theorem forward_nextSplitTargetRowStage {I : Type u} (G : DWeb V)
    (fixed : Set G.DPath)
    (hstep : SplitTargetRowSuccessorRule (I := I) G fixed)
    (S : SplitTargetRowStage G I) (i : I) :
    G.ForwardExtension (S.row.paths i)
      ((nextSplitTargetRowStage G fixed hstep S).row.paths i) :=
  (Classical.choose_spec (hstep S)).2 i

/-- Package a genuine split successor as the private-state machine consumed
by the singular matrix. -/
noncomputable def targetRowMachineOfSplitSuccessor
    {I : Type u} {G : DWeb V} {fixed : Set G.DPath}
    {initialSources : I → Set V}
    (S0 : SplitTargetRowStage G I)
    (hS0 : S0.row.sources = initialSources)
    (hstep : SplitTargetRowSuccessorRule (I := I) G fixed) :
    TargetRowMachine G fixed initialSources where
  State := SplitTargetRowStage G I
  row S := S.row
  initial := S0
  next S := nextSplitTargetRowStage G fixed hstep S
  sources_initial := hS0
  sources_next S := nextSplitTargetRowStage_sources G fixed hstep S
  forward_next S i := forward_nextSplitTargetRowStage G fixed hstep S i

end SingularTargetRowMachine
end CardinalInduction
end Erdos599
