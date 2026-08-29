/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularTargetRowMachine
import ErdosProblems.Erdos599.SingularCompletedPendingMerge

/-!
# Re-entering a singular row through its pending terminal frontier

The target row used in Assertion 9.17 need not be terminal-clean at its
stop-over: a still-pending member may start in the stop-over and end at a
different point of it.  This module records the sound replacement for the
over-strong terminal-clean continuation interface.

The quotient family is first restricted to components whose initials are
old terminals.  If such a lifted component meets an old member, quotient
geometry says that the meeting point is its initial vertex.  That vertex is
the terminal of some old member; warpness then identifies that member with
the one being continued.  Thus the source-star is compatible without a
terminal-clean hypothesis on the whole old row.

This also explains why a boundary-starting pending member cannot in general
be continued using only a quotient request at its *initial* vertex: forward
extension needs a quotient component at its terminal.  The iterable request
therefore contains the complete selected terminal frontier.  Boundary
initials may be requested in addition for target bookkeeping, but cannot
replace these terminal requests.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularPendingReentry

open DirectedPath SingularContinuation SingularBoundarySplit
  SingularPendingDecomposition SingularTargetRowMachine SliceSpliceSource
  SingularQuotientReentry SingularCompletedPendingMerge

universe u

variable {V : Type u}

/-! ## Boundary-starting members of a clean finite row are trivial -/

private theorem walk_eq_nil_of_isPath_same_ends
    {G : DWeb V} {x : V} (w : DirectedPath.Walk G.graph x x)
    (hw : w.IsPath) : w = .nil := by
  cases w with
  | nil => rfl
  | @cons _ y _ h q =>
      exact False.elim ((List.nodup_cons.mp hw).1 q.end_mem_support)

private theorem finitePath_eq_trivial_of_start_eq_finish
    {G : DWeb V} (p : DirectedPath.FinitePath G.graph)
    (h : p.start = p.finish) :
    p = DirectedPath.FinitePath.trivial G.graph p.start := by
  rcases p with ⟨start, finish, walk, isPath⟩
  dsimp at h ⊢
  subst finish
  have hw : walk = .nil := walk_eq_nil_of_isPath_same_ends walk isPath
  subst walk
  rfl

/-- If a finite-character family is terminal-clean at `E`, then any one of
its members whose initial vertex already lies in `E` is the length-zero
path at that vertex.  Indeed terminal-cleanliness identifies the terminal
with the initial, and simplicity rules out a nonempty closed finite path. -/
theorem eq_trivialPath_of_mem_of_initial_mem_of_terminalCleanAt
    {G : DWeb V} {C : Set G.DPath} {E : Set V}
    (hfinite : G.HasFiniteCharacter C)
    (hclean : TerminalCleanAt G C E)
    {p : G.DPath} (hpC : p ∈ C) (hpInitial : p.initial ∈ E) :
    p = G.trivialPath p.initial := by
  obtain ⟨f, rfl⟩ := hfinite hpC
  have hterminal : G.terminal? (.inl f : G.DPath) = some f.start :=
    hclean (.inl f) hpC f.start f.start_mem_support hpInitial
  have hfinish : f.start = f.finish := by
    exact (Option.some.inj hterminal).symm
  have hf := finitePath_eq_trivial_of_start_eq_finish f hfinish
  change (Sum.inl f : G.DPath) =
    Sum.inl (DirectedPath.FinitePath.trivial G.graph f.start)
  exact congrArg (fun g : DirectedPath.FinitePath G.graph ↦
    (Sum.inl g : G.DPath)) hf

/-- Hence every boundary-starting pending member of a globally clean finite
row is trivial.  No linkage hypothesis is needed. -/
theorem boundaryPendingPart_eq_trivialPath_of_terminalCleanAt
    {G : DWeb V} {C : Set G.DPath} {E : Set V}
    (hfinite : G.HasFiniteCharacter C)
    (hclean : TerminalCleanAt G C E)
    {p : G.DPath} (hp : p ∈ boundaryPendingPart G C E) :
    p = G.trivialPath p.initial := by
  exact eq_trivialPath_of_mem_of_initial_mem_of_terminalCleanAt
    hfinite hclean hp.1.1 hp.2.2

/-- The boundary-trivial invariant survives `completedPendingMerge` when
its clean fallback row is terminal-clean: every pending member of the merge
comes from that clean row. -/
theorem boundaryPendingPart_completedPendingMerge_eq_trivialPath
    {G : DWeb V} {C T : Set G.DPath} {E : Set V}
    (hCfinite : G.HasFiniteCharacter C)
    (hCclean : TerminalCleanAt G C E)
    {p : G.DPath}
    (hp : p ∈ boundaryPendingPart G (completedPendingMerge G C T) E) :
    p = G.trivialPath p.initial := by
  apply eq_trivialPath_of_mem_of_initial_mem_of_terminalCleanAt
    hCfinite hCclean
  · exact pendingPart_completedPendingMerge_subset G C T hp.1
  · exact hp.2.2

/-- Every path with initial vertex `a` extends the trivial path at `a`. -/
theorem extends_trivialPath_of_initial_eq
    (G : DWeb V) {a : V} {q : G.DPath} (hq : q.initial = a) :
    G.Extends (G.trivialPath a) q := by
  rcases q with f | r
  · change [a] <+: f.walk.support
    rw [List.singleton_prefix_iff_head?_eq_some,
      List.head?_eq_some_head f.walk.support_ne_nil, f.walk.head_support]
    exact congrArg some hq
  · change (DirectedPath.FinitePath.trivial G.graph a).IsInitialSegmentOf r
    intro n hn
    simp only [DirectedPath.FinitePath.trivial_walk] at hn ⊢
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hn)
    subst n
    change r.initial = a at hq
    exact hq.symm

/-- Replacing a family of trivial paths by any family with exactly the same
initial set is an honest forward extension. -/
theorem forwardExtension_of_trivial_of_initialSet_eq
    (G : DWeb V) {W R : Set G.DPath}
    (htrivial : ∀ p ∈ W, p = G.trivialPath p.initial)
    (hinitial : G.initialSet R = G.initialSet W) :
    G.ForwardExtension W R := by
  constructor
  · intro p hpW
    have hpInitial : p.initial ∈ G.initialSet R := by
      rw [hinitial]
      exact ⟨p, hpW, rfl⟩
    obtain ⟨q, hqR, hqp⟩ := hpInitial
    refine ⟨q, hqR, ?_⟩
    rw [htrivial p hpW]
    exact extends_trivialPath_of_initial_eq G hqp
  · intro q hqR
    have hqInitial : q.initial ∈ G.initialSet W := by
      rw [← hinitial]
      exact ⟨q, hqR, rfl⟩
    obtain ⟨p, hpW, hpq⟩ := hqInitial
    refine ⟨p, hpW, ?_⟩
    rw [htrivial p hpW]
    exact extends_trivialPath_of_initial_eq G hpq.symm

/-- Forward extension is componentwise stable under binary unions. -/
theorem forwardExtension_union
    (G : DWeb V) {W₁ W₂ R₁ R₂ : Set G.DPath}
    (h₁ : G.ForwardExtension W₁ R₁)
    (h₂ : G.ForwardExtension W₂ R₂) :
    G.ForwardExtension (W₁ ∪ W₂) (R₁ ∪ R₂) := by
  constructor
  · intro p hp
    rcases hp with hp₁ | hp₂
    · obtain ⟨q, hq, hpq⟩ := h₁.1 p hp₁
      exact ⟨q, Or.inl hq, hpq⟩
    · obtain ⟨q, hq, hpq⟩ := h₂.1 p hp₂
      exact ⟨q, Or.inr hq, hpq⟩
  · intro q hq
    rcases hq with hq₁ | hq₂
    · obtain ⟨p, hp, hpq⟩ := h₁.2 q hq₁
      exact ⟨p, Or.inl hp, hpq⟩
    · obtain ⟨p, hp, hpq⟩ := h₂.2 q hq₂
      exact ⟨p, Or.inr hp, hpq⟩

/-- A trivial boundary-starting family is supported in the boundary and
hence in its roof. -/
theorem boundaryPendingPart_vertexSet_subset_roof_of_trivial
    (G : DWeb V) {W : Set G.DPath} {C : Set V}
    (htrivial : ∀ p ∈ boundaryPendingPart G W C,
      p = G.trivialPath p.initial) :
    G.vertexSet (boundaryPendingPart G W C) ⊆ G.roof C := by
  rintro x ⟨p, hp, hxp⟩
  have hpEq := htrivial p hp
  rw [hpEq, G.support_trivialPath] at hxp
  apply G.subset_roof C
  exact hxp ▸ hp.2.2

/-- Boundary-starting pending components which are trivial are themselves
terminal-clean at the boundary. -/
theorem boundaryPendingPart_terminalClean_of_trivial
    (G : DWeb V) {W : Set G.DPath} {C : Set V}
    (htrivial : ∀ p ∈ boundaryPendingPart G W C,
      p = G.trivialPath p.initial) :
    TerminalCleanAt G (boundaryPendingPart G W C) C := by
  intro p hp x hxp _hxC
  have hpEq := htrivial p hp
  rw [hpEq, G.support_trivialPath] at hxp
  rw [hpEq, G.terminal?_trivialPath]
  exact congrArg some hxp.symm

/-- For a family of trivial paths, terminal frontier and initial set agree. -/
theorem terminalFrontier_boundaryPendingPart_eq_initialSet_of_trivial
    (G : DWeb V) {W : Set G.DPath} {C : Set V}
    (htrivial : ∀ p ∈ boundaryPendingPart G W C,
      p = G.trivialPath p.initial) :
    G.terminalFrontier (boundaryPendingPart G W C) =
      G.initialSet (boundaryPendingPart G W C) := by
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    refine ⟨p, hp, ?_⟩
    have hpEq := htrivial p hp
    rw [hpEq] at hpx ⊢
    exact Option.some.inj hpx
  · rintro ⟨p, hp, hpx⟩
    refine ⟨p, hp, ?_⟩
    have hpEq := htrivial p hp
    rw [hpEq] at hpx ⊢
    exact congrArg some hpx

/-- The clean/boundary split only requires all represented initials to be
ambient sources.  This version applies to a selected-source restriction of
a full row. -/
theorem clean_union_boundary_of_initialSet_subset
    {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (hsource : G.initialSet W ⊆ G.source) :
    cleanPendingPart G W C ∪ boundaryPendingPart G W C =
      SingularExtension.pendingPart G W := by
  apply Set.Subset.antisymm
  · exact Set.union_subset (fun _ hp ↦ hp.1) (fun _ hp ↦ hp.1)
  · intro p hp
    have hpSource : p.initial ∈ G.source :=
      hsource ⟨p, hp.1, rfl⟩
    by_cases hpC : p.initial ∈ C
    · exact Or.inr ⟨hp, hpSource, hpC⟩
    · exact Or.inl ⟨hp, hpSource, hpC⟩

/-- Pending parts are monotone under restriction of the underlying path
family. -/
theorem pendingPart_mono
    (G : DWeb V) {W₁ W₂ : Set G.DPath} (hW : W₁ ⊆ W₂) :
    SingularExtension.pendingPart G W₁ ⊆
      SingularExtension.pendingPart G W₂ := by
  intro p hp
  refine ⟨hW hp.1, ?_⟩
  intro hpCompleted
  exact hp.2 ⟨hp.1, hpCompleted.2⟩

/-- Boundary-pending parts are monotone under restriction of the underlying
path family. -/
theorem boundaryPendingPart_mono
    (G : DWeb V) {W₁ W₂ : Set G.DPath} {C : Set V}
    (hW : W₁ ⊆ W₂) :
    boundaryPendingPart G W₁ C ⊆ boundaryPendingPart G W₂ C := by
  intro p hp
  refine ⟨⟨hW hp.1.1, ?_⟩, hp.2⟩
  intro hpCompleted
  exact hp.1.2 ⟨hp.1.1, hpCompleted.2⟩

theorem cleanPendingPart_mono
    (G : DWeb V) {W₁ W₂ : Set G.DPath} {C : Set V}
    (hW : W₁ ⊆ W₂) :
    cleanPendingPart G W₁ C ⊆ cleanPendingPart G W₂ C := by
  intro p hp
  refine ⟨⟨hW hp.1.1, ?_⟩, hp.2⟩
  intro hpCompleted
  exact hp.1.2 ⟨hp.1.1, hpCompleted.2⟩

/-- Boundary triviality therefore passes to every selected-source
restriction of a displayed row. -/
theorem boundaryPendingPart_trivial_mono
    (G : DWeb V) {W₁ W₂ : Set G.DPath} {C : Set V}
    (hW : W₁ ⊆ W₂)
    (htrivial : ∀ p ∈ boundaryPendingPart G W₂ C,
      p = G.trivialPath p.initial) :
    ∀ p ∈ boundaryPendingPart G W₁ C,
      p = G.trivialPath p.initial := by
  intro p hp
  exact htrivial p (boundaryPendingPart_mono G hW hp)

/-- Under the boundary-trivial invariant the whole pending part, unlike the
completed part, is roofed by the current split boundary. -/
theorem pendingPart_vertexSet_subset_roof_of_split
    {G : DWeb V} {W : Set G.DPath} (S : SplitStopover G W)
    (hfull : G.initialSet W = G.source)
    (htrivial : ∀ p ∈ boundaryPendingPart G W S.boundary,
      p = G.trivialPath p.initial) :
    G.vertexSet (SingularExtension.pendingPart G W) ⊆
      G.roof S.boundary := by
  rw [← clean_union_boundary hfull, G.vertexSet_union]
  exact Set.union_subset S.clean_pending_roof
    (boundaryPendingPart_vertexSet_subset_roof_of_trivial G htrivial)

/-- Selected-source form of pending roof containment. -/
theorem pendingPart_vertexSet_subset_roof_of_split_selected
    {G : DWeb V} {W : Set G.DPath} (S : SplitStopover G W)
    (hsource : G.initialSet W ⊆ G.source)
    (htrivial : ∀ p ∈ boundaryPendingPart G W S.boundary,
      p = G.trivialPath p.initial) :
    G.vertexSet (SingularExtension.pendingPart G W) ⊆
      G.roof S.boundary := by
  rw [← clean_union_boundary_of_initialSet_subset hsource,
    G.vertexSet_union]
  exact Set.union_subset S.clean_pending_roof
    (boundaryPendingPart_vertexSet_subset_roof_of_trivial G htrivial)

/-- A selected subfamily of a split row inherits the pending roof bound
and boundary-trivial invariant from the whole row. -/
theorem pendingPart_selected_vertexSet_subset_roof_of_split
    {G : DWeb V} {W₁ W₂ : Set G.DPath} (S : SplitStopover G W₂)
    (hW : W₁ ⊆ W₂)
    (hsource : G.initialSet W₁ ⊆ G.source)
    (htrivial : ∀ p ∈ boundaryPendingPart G W₂ S.boundary,
      p = G.trivialPath p.initial) :
    G.vertexSet (SingularExtension.pendingPart G W₁) ⊆
      G.roof S.boundary := by
  rw [← clean_union_boundary_of_initialSet_subset hsource,
    G.vertexSet_union]
  refine Set.union_subset ?_ ?_
  · rintro x ⟨p, hp, hxp⟩
    exact S.clean_pending_roof
      ⟨p, cleanPendingPart_mono G hW hp, hxp⟩
  · exact boundaryPendingPart_vertexSet_subset_roof_of_trivial G
      (boundaryPendingPart_trivial_mono G hW htrivial)

/-- The whole pending part of a selected split row is terminal-clean.  The
outside piece has the recorded clean certificate, while the boundary piece
is trivial.  Completed paths remain deliberately outside this statement. -/
theorem pendingPart_selected_terminalClean_of_split
    {G : DWeb V} {W₁ W₂ : Set G.DPath} (S : SplitStopover G W₂)
    (hW : W₁ ⊆ W₂)
    (hsource : G.initialSet W₁ ⊆ G.source) :
    TerminalCleanAt G (SingularExtension.pendingPart G W₁) S.boundary := by
  rw [← clean_union_boundary_of_initialSet_subset hsource]
  intro p hp
  rcases hp with hpClean | hpBoundary
  · exact S.clean_pending_terminalClean p
      (cleanPendingPart_mono G hW hpClean)
  · exact boundaryPendingPart_terminalClean_of_trivial G
      (boundaryPendingPart_trivial_mono G hW
        S.boundary_pending_trivial) p hpBoundary

/-- Under the same invariant the exact pending-request set is literally the
terminal frontier of the whole pending part.  Thus boundary initials can be
fed to the same source-star as clean pending terminals. -/
theorem pendingRequests_eq_terminalFrontier_pendingPart_of_trivial
    {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (hfull : G.initialSet W = G.source)
    (htrivial : ∀ p ∈ boundaryPendingPart G W C,
      p = G.trivialPath p.initial) :
    pendingRequests G W C =
      G.terminalFrontier (SingularExtension.pendingPart G W) := by
  unfold pendingRequests
  rw [← clean_union_boundary hfull, G.terminalFrontier_union,
    terminalFrontier_boundaryPendingPart_eq_initialSet_of_trivial G htrivial]

/-- Selected-source form of the request/frontier identity. -/
theorem pendingRequests_eq_terminalFrontier_pendingPart_of_trivial_selected
    {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (hsource : G.initialSet W ⊆ G.source)
    (htrivial : ∀ p ∈ boundaryPendingPart G W C,
      p = G.trivialPath p.initial) :
    pendingRequests G W C =
      G.terminalFrontier (SingularExtension.pendingPart G W) := by
  unfold pendingRequests
  rw [← clean_union_boundary_of_initialSet_subset hsource,
    G.terminalFrontier_union,
    terminalFrontier_boundaryPendingPart_eq_initialSet_of_trivial G htrivial]

/-! ## The exact pending-request auxiliary web -/

/-- The lower-cardinal half-way clause is applied after restricting the
quotient source to the genuine pending requests.  The graph and target are
unchanged; only the distinguished source set is reduced. -/
def pendingAuxiliaryWeb (G : DWeb V) (W : Set G.DPath) (C : Set V) :
    DWeb V :=
  (G.quotient C).sourceSubweb (pendingRequests G W C)

@[simp] theorem pendingAuxiliaryWeb_graph
    (G : DWeb V) (W : Set G.DPath) (C : Set V) :
    (pendingAuxiliaryWeb G W C).graph = (G.quotient C).graph :=
  rfl

@[simp] theorem pendingAuxiliaryWeb_source
    (G : DWeb V) (W : Set G.DPath) (C : Set V) :
    (pendingAuxiliaryWeb G W C).source = pendingRequests G W C :=
  rfl

@[simp] theorem pendingAuxiliaryWeb_target
    (G : DWeb V) (W : Set G.DPath) (C : Set V) :
    (pendingAuxiliaryWeb G W C).target = (G.quotient C).target :=
  rfl

/-- Unhinderedness descends to the exact pending-request source subweb.
Normalization supplies the no-incoming-source hypothesis in the quotient. -/
theorem pendingAuxiliaryWeb_isUnhindered
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {C : Set V}
    (hquotient : (G.quotient C).IsUnhindered)
    (hrequest : pendingRequests G W C ⊆ (G.quotient C).source) :
    (pendingAuxiliaryWeb G W C).IsUnhindered := by
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  exact hquotient.sourceSubweb (G.quotient C)
    (DWeb.NoEdgeEnters.quotient G hNoEnter) hrequest

/-- Apply the universal lower induction hypothesis in the exact auxiliary
web.  This theorem intentionally returns a half-way linkage in the source
subweb: its initial set is definitionally `pendingRequests`, not the whole
quotient source. -/
theorem exists_pendingAuxiliaryHalfway_of_lower
    {kappa mu : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa) (hmuInfinite : aleph0 ≤ mu)
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {C : Set V}
    (hquotient : (G.quotient C).IsUnhindered)
    (hrequest : pendingRequests G W C ⊆ (G.quotient C).source)
    (hcard : #(pendingRequests G W C) = mu) :
    ∃ U : Set (pendingAuxiliaryWeb G W C).DPath,
      IsHalfwayLinkageOfAltitude (pendingAuxiliaryWeb G W C)
        (pendingRequests G W C) mu U := by
  have haux : (pendingAuxiliaryWeb G W C).IsUnhindered :=
    pendingAuxiliaryWeb_isUnhindered hNorm hquotient hrequest
  exact (hlower mu hmu (pendingAuxiliaryWeb G W C) haux).halfway
    hmuInfinite (pendingRequests G W C) (by simp) hcard

/-- Forgetting the restricted source does not change the path graph, warp
property, finite character, or target links of an auxiliary witness. -/
theorem pendingAuxiliaryHalfway_quotientPayload
    {G : DWeb V} {W : Set G.DPath} {C : Set V}
    {mu : Cardinal.{u}}
    {U : Set (pendingAuxiliaryWeb G W C).DPath}
    (hU : IsHalfwayLinkageOfAltitude (pendingAuxiliaryWeb G W C)
      (pendingRequests G W C) mu U) :
    (G.quotient C).IsWarp U ∧
      (G.quotient C).HasFiniteCharacter U ∧
      (G.quotient C).initialSet U = pendingRequests G W C ∧
      LinksToTarget (G.quotient C) U (pendingRequests G W C) := by
  obtain ⟨E, hE⟩ := hU.1
  exact ⟨hE.linkage.isWarp, hE.linkage.finiteCharacter,
    hE.linkage.initialSet_eq, hU.2.1⟩

/-! ## The frozen-deletion pending auxiliary web -/

/-- To make freezing sound, choose the lower-cardinal quotient family only
after deleting a vertex set containing the frozen family. -/
def deletedPendingAuxiliaryWeb
    (G : DWeb V) (W : Set G.DPath) (C Q : Set V) : DWeb V :=
  ((G.delete Q).quotient C).sourceSubweb (pendingRequests G W C)

@[simp] theorem deletedPendingAuxiliaryWeb_graph
    (G : DWeb V) (W : Set G.DPath) (C Q : Set V) :
    (deletedPendingAuxiliaryWeb G W C Q).graph =
      ((G.delete Q).quotient C).graph := rfl

@[simp] theorem deletedPendingAuxiliaryWeb_source
    (G : DWeb V) (W : Set G.DPath) (C Q : Set V) :
    (deletedPendingAuxiliaryWeb G W C Q).source =
      pendingRequests G W C := rfl

@[simp] theorem deletedPendingAuxiliaryWeb_target
    (G : DWeb V) (W : Set G.DPath) (C Q : Set V) :
    (deletedPendingAuxiliaryWeb G W C Q).target =
      ((G.delete Q).quotient C).target := rfl

theorem deletedPendingAuxiliaryWeb_isUnhindered
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {C Q : Set V}
    (hbase : ((G.delete Q).quotient C).IsUnhindered)
    (hrequest : pendingRequests G W C ⊆
      ((G.delete Q).quotient C).source) :
    (deletedPendingAuxiliaryWeb G W C Q).IsUnhindered := by
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  exact hbase.sourceSubweb ((G.delete Q).quotient C)
    (DWeb.NoEdgeEnters.quotient (G.delete Q) hNoEnter.delete) hrequest

/-- Apply the lower induction hypothesis in the quotient after the frozen
deletion.  The deleted-quotient unhinderedness premise is explicit: unlike
cross-disjointness, it is not a consequence of ordinary competitor closure. -/
theorem exists_deletedPendingAuxiliaryHalfway_of_lower
    {kappa mu : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa) (hmuInfinite : aleph0 ≤ mu)
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {C Q : Set V}
    (hbase : ((G.delete Q).quotient C).IsUnhindered)
    (hrequest : pendingRequests G W C ⊆
      ((G.delete Q).quotient C).source)
    (hcard : #(pendingRequests G W C) = mu) :
    ∃ U : Set (deletedPendingAuxiliaryWeb G W C Q).DPath,
      IsHalfwayLinkageOfAltitude (deletedPendingAuxiliaryWeb G W C Q)
        (pendingRequests G W C) mu U := by
  have haux := deletedPendingAuxiliaryWeb_isUnhindered
    hNorm hbase hrequest
  exact (hlower mu hmu (deletedPendingAuxiliaryWeb G W C Q) haux).halfway
    hmuInfinite (pendingRequests G W C) (by simp) hcard

/-- Apply the lower induction hypothesis from the weakest residual safety
certificate actually used by the frozen-pending construction.  Requiring
the whole deleted quotient to be unhindered is a convenient sufficient
condition (see `exists_deletedPendingAuxiliaryHalfway_of_lower`), but the
successor only needs the source subweb on the pending requests.  This is
the future-safe invariant that a row-state construction should preserve. -/
theorem exists_deletedPendingAuxiliaryHalfway_of_lower_of_auxiliary
    {kappa mu : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa) (hmuInfinite : aleph0 ≤ mu)
    {G : DWeb V} {W : Set G.DPath} {C Q : Set V}
    (haux : (deletedPendingAuxiliaryWeb G W C Q).IsUnhindered)
    (hcard : #(pendingRequests G W C) = mu) :
    ∃ U : Set (deletedPendingAuxiliaryWeb G W C Q).DPath,
      IsHalfwayLinkageOfAltitude (deletedPendingAuxiliaryWeb G W C Q)
        (pendingRequests G W C) mu U := by
  exact (hlower mu hmu (deletedPendingAuxiliaryWeb G W C Q) haux).halfway
    hmuInfinite (pendingRequests G W C) (by simp) hcard

/-- The exact future-safety certificate consumed by one frozen-pending
successor.  It deliberately refers only to the requested source subweb:
vertices of the deleted quotient which are irrelevant to this column do
not have to remain unhindered. -/
structure DeletedPendingSafety
    (G : DWeb V) (W : Set G.DPath) (C Q : Set V)
    (mu : Cardinal.{u}) : Prop where
  requests_source : pendingRequests G W C ⊆
    ((G.delete Q).quotient C).source
  residual_unhindered :
    (deletedPendingAuxiliaryWeb G W C Q).IsUnhindered
  requests_card : #(pendingRequests G W C) = mu

/-- The previously used whole-deleted-quotient invariant is a sufficient
way to construct the sharper request-subweb safety certificate. -/
theorem DeletedPendingSafety.of_deletedQuotient
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {C Q : Set V} {mu : Cardinal.{u}}
    (hbase : ((G.delete Q).quotient C).IsUnhindered)
    (hrequest : pendingRequests G W C ⊆
      ((G.delete Q).quotient C).source)
    (hcard : #(pendingRequests G W C) = mu) :
    DeletedPendingSafety G W C Q mu where
  requests_source := hrequest
  residual_unhindered :=
    deletedPendingAuxiliaryWeb_isUnhindered hNorm hbase hrequest
  requests_card := hcard

/-- A future-safety certificate supplies the lower half-way witness without
the stronger whole-deleted-quotient hypothesis. -/
theorem DeletedPendingSafety.exists_halfway_of_lower
    {kappa mu : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa) (hmuInfinite : aleph0 ≤ mu)
    {G : DWeb V} {W : Set G.DPath} {C Q : Set V}
    (hsafe : DeletedPendingSafety G W C Q mu) :
    ∃ U : Set (deletedPendingAuxiliaryWeb G W C Q).DPath,
      IsHalfwayLinkageOfAltitude (deletedPendingAuxiliaryWeb G W C Q)
        (pendingRequests G W C) mu U := by
  exact exists_deletedPendingAuxiliaryHalfway_of_lower_of_auxiliary
    hlower hmu hmuInfinite hsafe.residual_unhindered hsafe.requests_card

/-- The extension half of the lower induction links the entire residual
request web at every smaller cardinal, including finite cardinals.  A full
linkage is a half-way linkage at its own altitude, so the frozen-pending
splice does not actually require the request cardinal to be infinite. -/
theorem DeletedPendingSafety.exists_halfway_of_lower_extension
    {kappa mu : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa)
    {G : DWeb V} {W : Set G.DPath} {C Q : Set V}
    (hsafe : DeletedPendingSafety G W C Q mu) :
    ∃ U : Set (deletedPendingAuxiliaryWeb G W C Q).DPath,
      IsHalfwayLinkageOfAltitude (deletedPendingAuxiliaryWeb G W C Q)
        (pendingRequests G W C)
        (altitude (deletedPendingAuxiliaryWeb G W C Q) U) U := by
  let H := deletedPendingAuxiliaryWeb G W C Q
  have hsourceCard : #H.source = mu := by
    simpa only [H, deletedPendingAuxiliaryWeb_source] using
      hsafe.requests_card
  have hCI := hlower mu hmu H hsafe.residual_unhindered
  have hext : ExtensionClauseAt H #H.source := by
    rw [hsourceCard]
    exact hCI.extension
  obtain ⟨U, hU⟩ := linkable_of_extension_at_source_card H hext
  refine ⟨U, fullLinkage_isHalfwayLinkage hU, ?_, le_rfl⟩
  exact fullLinkage_linksToTarget hU (by
    change pendingRequests G W C ⊆ pendingRequests G W C
    exact Set.Subset.rfl)

/-- Forget the distinguished restricted source of the deleted pending
auxiliary web.  Its path graph is definitionally the deleted quotient. -/
def forgetDeletedPendingAuxiliaryFamily
    (G : DWeb V) (W : Set G.DPath) (C Q : Set V)
    (U : Set (deletedPendingAuxiliaryWeb G W C Q).DPath) :
    Set ((G.delete Q).quotient C).DPath := U

/-- Transport a lower witness out of the frozen deletion and into the
ordinary quotient.  It retains its warp, finite-character, source, and
target-link data; its ambient lift is disjoint from the deleted set. -/
theorem deletedPendingAuxiliaryHalfway_quotientPayload
    {G : DWeb V} {W : Set G.DPath} {C Q : Set V}
    {mu : Cardinal.{u}}
    {U : Set (deletedPendingAuxiliaryWeb G W C Q).DPath}
    (hrequest : pendingRequests G W C ⊆
      ((G.delete Q).quotient C).source)
    (hU : IsHalfwayLinkageOfAltitude
      (deletedPendingAuxiliaryWeb G W C Q)
      (pendingRequests G W C) mu U) :
    let U₀ := forgetDeletedPendingAuxiliaryFamily G W C Q U
    let R := SingularExtension.deletedQuotientFamily G C Q U₀
    (G.quotient C).IsWarp R ∧
      (G.quotient C).HasFiniteCharacter R ∧
      (G.quotient C).initialSet R = pendingRequests G W C ∧
      LinksToTarget (G.quotient C) R (pendingRequests G W C) ∧
      Disjoint
        (G.vertexSet (liftedQuotientFamily G C R)) Q := by
  dsimp only
  obtain ⟨E, hE⟩ := hU.1
  let U₀ := forgetDeletedPendingAuxiliaryFamily G W C Q U
  have hU₀warp : ((G.delete Q).quotient C).IsWarp U₀ := by
    change (deletedPendingAuxiliaryWeb G W C Q).IsWarp U
    exact hE.linkage.isWarp
  have hU₀finite : ((G.delete Q).quotient C).HasFiniteCharacter U₀ := by
    change (deletedPendingAuxiliaryWeb G W C Q).HasFiniteCharacter U
    exact hE.linkage.finiteCharacter
  have hU₀initial : ((G.delete Q).quotient C).initialSet U₀ =
      pendingRequests G W C := by
    change (deletedPendingAuxiliaryWeb G W C Q).initialSet U =
      pendingRequests G W C
    exact hE.linkage.initialSet_eq
  have hU₀links : LinksToTarget ((G.delete Q).quotient C) U₀
      (pendingRequests G W C) := by
    change LinksToTarget (deletedPendingAuxiliaryWeb G W C Q) U
      (pendingRequests G W C)
    exact hU.2.1
  have hstart : ((G.delete Q).quotient C).initialSet U₀ ⊆
      ((G.delete Q).quotient C).source := by
    rw [hU₀initial]
    exact hrequest
  refine ⟨SingularExtension.deletedQuotientFamily_isWarp
      hU₀warp,
    SingularExtension.deletedQuotientFamily_hasFiniteCharacter
      hU₀finite,
    ?_,
    SingularExtension.linksToTarget_deletedQuotientFamily hU₀links,
    SingularExtension.lift_deletedQuotientFamily_vertexSet_disjoint hstart⟩
  rw [SingularExtension.deletedQuotientFamily_initialSet,
    hU₀initial]

/-! ## The terminal-frontier compatibility lemma -/

/-- A lifted quotient family starting only at terminals of an old warp is
source-star compatible with that warp.  No terminal-clean assertion is
needed, even when an old member starts in the quotient boundary. -/
theorem starCompatible_liftQuotientFamily_of_frontier
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    {U : Set (G.quotient C).DPath}
    (hUstart : (G.quotient C).initialSet U ⊆ G.terminalFrontier W) :
    G.StarCompatible W (liftedQuotientFamily G C U) := by
  intro p hpW q hqU x hxp hxq
  obtain ⟨q₀, hq₀U, rfl⟩ := hqU
  have hxRoof : x ∈ G.roof C := hroof ⟨p, hpW, hxp⟩
  have hxClass := G.quotientPath_support_initial_or_avoids C q₀ (by
    simpa only [G.support_liftQuotientPath] using hxq)
  have hxInitial : x = q₀.initial := by
    rcases hxClass with hx | hxAvoid
    · exact hx
    · exfalso
      by_cases hxEssential : x ∈ G.essential C
      · exact hxAvoid.2 (htrim ▸ hxEssential)
      · exact hxAvoid.1 ⟨hxRoof, hxEssential⟩
  have hqInitial : q₀.initial ∈ (G.quotient C).initialSet U :=
    ⟨q₀, hq₀U, rfl⟩
  obtain ⟨r, hrW, hrTerminal⟩ := hUstart hqInitial
  have hpr : p = r := by
    by_contra hne
    exact Set.disjoint_left.1 (hW hpW hrW hne) hxp
      (G.terminal_mem_support (hxInitial ▸ hrTerminal))
  subst r
  exact ⟨by simpa only [hxInitial] using hrTerminal,
    by simpa only [G.initial_liftQuotientPath] using hxInitial.symm⟩

/-- Continue an arbitrary roofed warp through quotient paths selected at
its terminal frontier. -/
noncomputable def frontierContinuation
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (U : Set (G.quotient C).DPath)
    (hUstart : (G.quotient C).initialSet U ⊆ G.terminalFrontier W) :
    Set G.DPath :=
  G.star (starCompatible_liftQuotientFamily_of_frontier
    G hW hroof htrim hUstart)

theorem frontierContinuation_isWarp
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    {U : Set (G.quotient C).DPath}
    (hU : (G.quotient C).IsWarp U)
    (hUstart : (G.quotient C).initialSet U ⊆ G.terminalFrontier W) :
    G.IsWarp (frontierContinuation G hW hroof htrim U hUstart) := by
  apply G.isWarp_star hW (DWeb.IsWarp.liftQuotientFamily G hU)

theorem forwardExtension_frontierContinuation
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (U : Set (G.quotient C).DPath)
    (hUstart : (G.quotient C).initialSet U ⊆ G.terminalFrontier W) :
    G.ForwardExtension W
      (frontierContinuation G hW hroof htrim U hUstart) := by
  exact G.forwardExtension_star
    (starCompatible_liftQuotientFamily_of_frontier
      G hW hroof htrim hUstart)

theorem initialSet_frontierContinuation
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (U : Set (G.quotient C).DPath)
    (hUstart : (G.quotient C).initialSet U ⊆ G.terminalFrontier W) :
    G.initialSet (frontierContinuation G hW hroof htrim U hUstart) =
      G.initialSet W := by
  exact (G.initialSet_eq_of_forwardExtension
    (forwardExtension_frontierContinuation
      G hW hroof htrim U hUstart)).symm

/-- Appending to a finite old member along a finite quotient lift again
produces a finite member. -/
private theorem appendFinite_finite_of_finite
    {D : Digraph V} (p : DirectedPath.FinitePath D)
    (q : DirectedPath.Path D) (hstart : q.initial = p.finish)
    (hinter : p.support ∩ q.support ⊆ {p.finish})
    (hq : ∃ g : DirectedPath.FinitePath D, q = .inl g) :
    ∃ g : DirectedPath.FinitePath D,
      DirectedPath.Path.appendFinite p q hstart hinter = .inl g := by
  rcases q with q | r
  · exact ⟨p.appendFinite q hstart hinter, rfl⟩
  · obtain ⟨g, hg⟩ := hq
    cases hg

theorem frontierContinuation_finiteCharacter
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hWfinite : G.HasFiniteCharacter W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    {U : Set (G.quotient C).DPath}
    (hUfinite : (G.quotient C).HasFiniteCharacter U)
    (hUstart : (G.quotient C).initialSet U ⊆ G.terminalFrontier W) :
    G.HasFiniteCharacter
      (frontierContinuation G hW hroof htrim U hUstart) := by
  let L := liftedQuotientFamily G C U
  let hc : G.StarCompatible W L :=
    starCompatible_liftQuotientFamily_of_frontier
      G hW hroof htrim hUstart
  have hLfinite : G.HasFiniteCharacter L := by
    rintro q ⟨q₀, hq₀U, rfl⟩
    obtain ⟨g, rfl⟩ := hUfinite hq₀U
    let g' : DirectedPath.FinitePath G.graph :=
      g.lift (fun {_ _} h => G.quotient_adj_imp h)
    exact ⟨g', rfl⟩
  rintro r ⟨p, rfl⟩
  rcases p with ⟨p, hpW⟩
  obtain ⟨f, rfl⟩ := hWfinite hpW
  simp only [DWeb.starPath]
  split
  next hmatch =>
    exact appendFinite_finite_of_finite f (Classical.choose hmatch) _ _
      (hLfinite (Classical.choose_spec hmatch).1)
  next _ => exact ⟨f, rfl⟩

/-- Every old terminal is represented by a lifted quotient member when the
restricted quotient family has exactly the old frontier as its initial set. -/
theorem exists_liftedQuotientPath_from_frontier
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    {U : Set (G.quotient C).DPath}
    (hcover : G.terminalFrontier W ⊆
      (G.quotient C).initialSet U)
    {f : DirectedPath.FinitePath G.graph}
    (hfW : (Sum.inl f : G.DPath) ∈ W) :
    ∃ q ∈ liftedQuotientFamily G C U, q.initial = f.finish := by
  have hfInitial : f.finish ∈ (G.quotient C).initialSet U :=
    hcover ⟨.inl f, hfW, rfl⟩
  obtain ⟨q₀, hq₀U, hq₀init⟩ := hfInitial
  refine ⟨G.liftQuotientPath C q₀, ⟨q₀, hq₀U, rfl⟩, ?_⟩
  simpa only [G.initial_liftQuotientPath] using hq₀init

/-- Once every old terminal is consumed, every new terminal is a terminal
of the selected quotient family. -/
theorem terminalFrontier_frontierContinuation_subset
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hWfinite : G.HasFiniteCharacter W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    {U : Set (G.quotient C).DPath}
    (hUstart : (G.quotient C).initialSet U ⊆ G.terminalFrontier W)
    (hcover : G.terminalFrontier W ⊆
      (G.quotient C).initialSet U) :
    G.terminalFrontier
        (frontierContinuation G hW hroof htrim U hUstart) ⊆
      (G.quotient C).terminalFrontier U := by
  let L := liftedQuotientFamily G C U
  let hc : G.StarCompatible W L :=
    starCompatible_liftQuotientFamily_of_frontier
      G hW hroof htrim hUstart
  rintro z ⟨r, ⟨p, rfl⟩, hrz⟩
  rcases p with ⟨p, hpW⟩
  obtain ⟨f, rfl⟩ := hWfinite hpW
  have hmatch : ∃ q ∈ L, q.initial = f.finish :=
    exists_liftedQuotientPath_from_frontier G hcover hpW
  simp only [DWeb.starPath] at hrz
  rw [dif_pos hmatch] at hrz
  let q := Classical.choose hmatch
  have hqL : q ∈ L := (Classical.choose_spec hmatch).1
  have hqstart : q.initial = f.finish := (Classical.choose_spec hmatch).2
  have hinter : f.support ∩ q.support ⊆ {f.finish} := by
    intro x hx
    have hx' := hc (.inl f) hpW q hqL x hx.1 hx.2
    exact Set.mem_singleton_iff.2 (Option.some.inj hx'.1).symm
  have hqTerminal : G.terminal? q = some z := by
    have hterm := DirectedPath.Path.terminal?_appendFinite
      f q hqstart hinter
    change DirectedPath.Path.terminal? q = some z
    rw [← hterm]
    dsimp only [q]
    exact hrz
  rw [← G.terminalFrontier_liftQuotientFamily C U]
  exact ⟨q, hqL, hqTerminal⟩

/-- Target links in the quotient compose with old finite members through
the frontier continuation.  This is the target-row analogue of the
terminal-frontier and forward-extension lemmas above. -/
theorem linksToTarget_frontierContinuation
    {G : DWeb V} (hNorm : G.IsNormalized)
    {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hWfinite : G.HasFiniteCharacter W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    {U : Set (G.quotient C).DPath}
    (hUwarp : (G.quotient C).IsWarp U)
    (hUfinite : (G.quotient C).HasFiniteCharacter U)
    (hUinitial : (G.quotient C).initialSet U = G.terminalFrontier W)
    {A B : Set V}
    (hA : A ⊆ G.terminalFrontier W)
    (hB : B ⊆ G.source)
    (hroute : RoutesTerminals G W B A)
    (hlinks : LinksToTarget (G.quotient C) U A) :
    LinksToTarget G
      (frontierContinuation G hW hroof htrim U hUinitial.le) B := by
  intro b hb
  obtain ⟨f, hfW, hfStart, hfFinishA⟩ := hroute b hb
  obtain ⟨p, hpU, q, hpq, hpure, before, after, hsupport,
    t, htTarget, htAfter⟩ := hlinks f.finish hfFinishA
  have hpq' : p = (Sum.inl q : (G.quotient C).DPath) := hpq
  subst p
  have hfinishQ : f.finish ∈ q.support := by
    have hsingleton : f.finish ∈ ({f.finish} : Set V) :=
      Set.mem_singleton f.finish
    rw [← hpure] at hsingleton
    exact hsingleton.1
  have hfinishInitial : f.finish ∈
      (G.quotient C).initialSet U := by
    rw [hUinitial]
    exact hA hfFinishA
  obtain ⟨q₀, hq₀U, hq₀Initial⟩ := hfinishInitial
  have hq₀eq : q₀ = (Sum.inl q : (G.quotient C).DPath) := by
    by_contra hne
    exact Set.disjoint_left.1 (hUwarp hq₀U hpU hne)
      (hq₀Initial.symm ▸ q₀.initial_mem_support) hfinishQ
  subst q₀
  have hqStart : q.start = f.finish := hq₀Initial
  let L := liftedQuotientFamily G C U
  have hcompat : G.StarCompatible W L :=
    starCompatible_liftQuotientFamily_of_frontier
      G hW hroof htrim hUinitial.le
  let qLift : G.DPath := G.liftQuotientPath C (.inl q)
  have hqLiftL : qLift ∈ L := ⟨.inl q, hpU, rfl⟩
  have hqLiftInitial : qLift.initial = f.finish := by
    change q.start = f.finish
    exact hqStart
  have hmatch : ∃ r ∈ L, r.initial = f.finish :=
    ⟨qLift, hqLiftL, hqLiftInitial⟩
  let chosen : G.DPath := Classical.choose hmatch
  have hchosenL : chosen ∈ L := (Classical.choose_spec hmatch).1
  have hchosenInitial : chosen.initial = f.finish :=
    (Classical.choose_spec hmatch).2
  have hLwarp : G.IsWarp L :=
    DWeb.IsWarp.liftQuotientFamily G hUwarp
  have hchosenEq : chosen = qLift := by
    by_contra hne
    exact Set.disjoint_left.1 (hLwarp hchosenL hqLiftL hne)
      (hchosenInitial.symm ▸ chosen.initial_mem_support)
      (hqLiftInitial.symm ▸ qLift.initial_mem_support)
  let rStar : G.DPath := G.starPath hcompat ⟨.inl f, hfW⟩
  have hrMem : rStar ∈
      frontierContinuation G hW hroof htrim U hUinitial.le :=
    ⟨⟨.inl f, hfW⟩, rfl⟩
  have htQ : t ∈ q.support := by
    change t ∈ q.walk.support
    rw [hsupport]
    exact List.mem_append_right before htAfter
  have htLift : t ∈ qLift.support := by
    dsimp only [qLift]
    rw [G.support_liftQuotientPath]
    exact htQ
  have htChosen : t ∈ chosen.support := hchosenEq ▸ htLift
  have htStar : t ∈ rStar.support := by
    dsimp only [rStar]
    simp only [DWeb.starPath]
    split
    next hmatch' =>
      let chosen' : G.DPath := Classical.choose hmatch'
      have hchosen'L : chosen' ∈ L :=
        (Classical.choose_spec hmatch').1
      have hchosen'Initial : chosen'.initial = f.finish :=
        (Classical.choose_spec hmatch').2
      have hchosen'Eq : chosen' = qLift := by
        by_contra hne
        exact Set.disjoint_left.1 (hLwarp hchosen'L hqLiftL hne)
          (hchosen'Initial.symm ▸ chosen'.initial_mem_support)
          (hqLiftInitial.symm ▸ qLift.initial_mem_support)
      have htChosen' : t ∈ chosen'.support := hchosen'Eq ▸ htLift
      have hinter : f.support ∩ chosen'.support ⊆ {f.finish} := by
        intro x hx
        have hx' := hcompat (.inl f) hfW chosen' hchosen'L x hx.1 hx.2
        exact Set.mem_singleton_iff.2 (Option.some.inj hx'.1).symm
      rw [DirectedPath.Path.support_appendFinite f chosen'
        hchosen'Initial hinter]
      exact Or.inr htChosen'
    next hnone =>
      exact (hnone hmatch).elim
  have hContinuedFinite : G.HasFiniteCharacter
      (frontierContinuation G hW hroof htrim U hUinitial.le) :=
    frontierContinuation_finiteCharacter G hW hWfinite hroof htrim
      hUfinite hUinitial.le
  obtain ⟨g, hrg⟩ := hContinuedFinite hrMem
  have hgMem : (Sum.inl g : G.DPath) ∈
      frontierContinuation G hW hroof htrim U hUinitial.le :=
    hrg ▸ hrMem
  have htG : t ∈ g.support := by
    rw [hrg] at htStar
    exact htStar
  have hgStart : g.start = b := by
    have hstart := G.initial_starPath hcompat
      ⟨(.inl f : G.DPath), hfW⟩
    dsimp only [rStar] at hrg
    rw [hrg] at hstart
    exact hstart.trans hfStart
  have htFinish : t = g.finish :=
    hNorm.eq_finish_of_mem_walk g.walk htG htTarget
  have hgSourcePure : g.support ∩ B = {b} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxg, hxB⟩
      exact Set.mem_singleton_iff.2
        ((hNorm.eq_start_of_mem_walk g.walk hxg (hB hxB)).trans hgStart)
    · intro x hx
      have hxb : x = b := Set.mem_singleton_iff.1 hx
      subst x
      refine ⟨?_, hb⟩
      exact hgStart ▸ g.start_mem_support
  refine ⟨.inl g, hgMem, g, rfl, hgSourcePure, ?_⟩
  refine ⟨[], g.walk.support.tail, ?_, g.finish, ?_, ?_⟩
  · simp only [List.nil_append]
    calc
      g.walk.support =
          g.walk.support.head g.walk.support_ne_nil ::
            g.walk.support.tail :=
        (g.walk.support.cons_head_tail g.walk.support_ne_nil).symm
      _ = b :: g.walk.support.tail := by
        congr 1
        rw [g.walk.head_support]
        exact hgStart
  · exact htFinish ▸ htTarget
  · have hcons : b :: g.walk.support.tail = g.walk.support := by
      have hhead :
          g.walk.support.head g.walk.support_ne_nil = b :=
        g.walk.head_support.trans hgStart
      calc
        b :: g.walk.support.tail =
            g.walk.support.head g.walk.support_ne_nil ::
              g.walk.support.tail :=
          congrArg (fun x ↦ x :: g.walk.support.tail) hhead.symm
        _ = g.walk.support :=
          g.walk.support.cons_head_tail g.walk.support_ne_nil
    change g.finish ∈ b :: g.walk.support.tail
    rw [hcons]
    exact g.finish_mem_support

/-- A finite family routes each represented initial vertex to the terminal
of its own component. -/
theorem routesTerminals_initialSet_terminalFrontier
    {G : DWeb V} {W : Set G.DPath}
    (hfinite : G.HasFiniteCharacter W) :
    RoutesTerminals G W (G.initialSet W) (G.terminalFrontier W) := by
  intro b hb
  obtain ⟨p, hpW, hpb⟩ := hb
  obtain ⟨f, rfl⟩ := hfinite hpW
  refine ⟨f, hpW, hpb, ?_⟩
  exact ⟨.inl f, hpW, rfl⟩

/-- The exact selected-pending continuation furnished by a lower half-way
witness in `pendingAuxiliaryWeb`.  This is the iterable part of the split
successor: it uses only the selected pending subfamily, inherits its roof
bound and boundary-triviality from the full split row, and produces an
ambient forward extension carrying all quotient target links. -/
theorem exists_selectedPendingContinuation_of_auxiliaryHalfway
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W₁ W₂ : Set G.DPath} (S : SplitStopover G W₂)
    (hsub : W₁ ⊆ W₂)
    (hWwarp : G.IsWarp W₂)
    (hWfinite : G.HasFiniteCharacter W₂)
    (hsource : G.initialSet W₁ ⊆ G.source)
    (htrivial : ∀ p ∈ boundaryPendingPart G W₂ S.boundary,
      p = G.trivialPath p.initial)
    {mu : Cardinal.{u}}
    {U : Set (pendingAuxiliaryWeb G W₁ S.boundary).DPath}
    (hU : IsHalfwayLinkageOfAltitude
      (pendingAuxiliaryWeb G W₁ S.boundary)
      (pendingRequests G W₁ S.boundary) mu U) :
    ∃ R : Set G.DPath,
      G.IsWarp R ∧
      G.HasFiniteCharacter R ∧
      G.ForwardExtension (SingularExtension.pendingPart G W₁) R ∧
      G.initialSet R =
        G.initialSet (SingularExtension.pendingPart G W₁) ∧
      LinksToTarget G R
        (G.initialSet (SingularExtension.pendingPart G W₁)) ∧
      G.terminalFrontier R ⊆
        (G.quotient S.boundary).terminalFrontier U := by
  let P := SingularExtension.pendingPart G W₁
  have hPtrivial : ∀ p ∈ boundaryPendingPart G W₁ S.boundary,
      p = G.trivialPath p.initial :=
    boundaryPendingPart_trivial_mono G hsub htrivial
  have hrequest : pendingRequests G W₁ S.boundary =
      G.terminalFrontier P :=
    pendingRequests_eq_terminalFrontier_pendingPart_of_trivial_selected
      hsource hPtrivial
  have hPwarp : G.IsWarp P := by
    intro p hp q hq hpq
    exact hWwarp (hsub hp.1) (hsub hq.1) hpq
  have hPfinite : G.HasFiniteCharacter P := by
    intro p hp
    exact hWfinite (hsub hp.1)
  have hProof : G.vertexSet P ⊆ G.roof S.boundary :=
    pendingPart_selected_vertexSet_subset_roof_of_split
      S hsub hsource htrivial
  have hPsource : G.initialSet P ⊆ G.source := by
    rintro x ⟨p, hp, hpx⟩
    exact hsource ⟨p, hp.1, hpx⟩
  obtain ⟨hUwarp, hUfinite, hUinitialRequest, hUlinksRequest⟩ :=
    pendingAuxiliaryHalfway_quotientPayload hU
  have hUinitial : (G.quotient S.boundary).initialSet U =
      G.terminalFrontier P := hUinitialRequest.trans hrequest
  have hUlinks : LinksToTarget (G.quotient S.boundary) U
      (G.terminalFrontier P) := by
    simpa only [hrequest] using hUlinksRequest
  let R := frontierContinuation G hPwarp hProof S.minimal U hUinitial.le
  refine ⟨R,
    frontierContinuation_isWarp G hPwarp hProof S.minimal
      hUwarp hUinitial.le,
    frontierContinuation_finiteCharacter G hPwarp hPfinite hProof
      S.minimal hUfinite hUinitial.le,
    forwardExtension_frontierContinuation G hPwarp hProof S.minimal
      U hUinitial.le,
    initialSet_frontierContinuation G hPwarp hProof S.minimal
      U hUinitial.le,
    ?_,
    terminalFrontier_frontierContinuation_subset G hPwarp hPfinite
      hProof S.minimal hUinitial.le hUinitial.ge⟩
  exact linksToTarget_frontierContinuation hNorm hPwarp hPfinite hProof
    S.minimal hUwarp hUfinite hUinitial Set.Subset.rfl hPsource
    (routesTerminals_initialSet_terminalFrontier hPfinite) hUlinks

/-! ## Freezing components outside the continued subwarp -/

/-- Adjoin a verbatim frozen family to a frontier continuation. -/
noncomputable def frozenFrontierContinuation
    (G : DWeb V) (F : Set G.DPath) {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (U : Set (G.quotient C).DPath)
    (hUstart : (G.quotient C).initialSet U ⊆ G.terminalFrontier W) :
    Set G.DPath :=
  F ∪ frontierContinuation G hW hroof htrim U hUstart

theorem forwardExtension_frozenFrontierContinuation
    (G : DWeb V) (F : Set G.DPath) {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (U : Set (G.quotient C).DPath)
    (hUstart : (G.quotient C).initialSet U ⊆ G.terminalFrontier W) :
    G.ForwardExtension (F ∪ W)
      (frozenFrontierContinuation G F hW hroof htrim U hUstart) := by
  exact forwardExtension_union_frozen G
    (forwardExtension_frontierContinuation
      G hW hroof htrim U hUstart)

theorem frozenFrontierContinuation_isWarp
    (G : DWeb V) {F : Set G.DPath} {C : Set V} {W : Set G.DPath}
    (hF : G.IsWarp F) (hW : G.IsWarp W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    {U : Set (G.quotient C).DPath}
    (hU : (G.quotient C).IsWarp U)
    (hUstart : (G.quotient C).initialSet U ⊆ G.terminalFrontier W)
    (hcross : Disjoint (G.vertexSet F)
      (G.vertexSet
        (frontierContinuation G hW hroof htrim U hUstart))) :
    G.IsWarp
      (frozenFrontierContinuation G F hW hroof htrim U hUstart) := by
  exact isWarp_union_of_disjoint_vertexSet G hF
    (frontierContinuation_isWarp
      G hW hroof htrim hU hUstart) hcross

theorem frozenFrontierContinuation_finiteCharacter
    (G : DWeb V) {F : Set G.DPath} {C : Set V} {W : Set G.DPath}
    (hFfinite : G.HasFiniteCharacter F)
    (hW : G.IsWarp W)
    (hWfinite : G.HasFiniteCharacter W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    {U : Set (G.quotient C).DPath}
    (hUfinite : (G.quotient C).HasFiniteCharacter U)
    (hUstart : (G.quotient C).initialSet U ⊆ G.terminalFrontier W) :
    G.HasFiniteCharacter
      (frozenFrontierContinuation G F hW hroof htrim U hUstart) := by
  exact finiteCharacter_union G hFfinite
    (frontierContinuation_finiteCharacter
      G hW hWfinite hroof htrim hUfinite hUstart)

/-- A second old pending family need not be included in the deleted set.
If it is roofed and terminal-clean at the current boundary, then a quotient
continuation of a vertex-disjoint pending family cannot cross it.  Indeed,
quotient support can meet the old roof only at its initial vertex; source-
star compatibility makes that vertex the terminal of the old component,
while the request condition makes it the terminal of a component in the
continued family, contradicting their old vertex-disjointness. -/
theorem disjoint_roofedClean_frontierContinuation
    (G : DWeb V) {F P : Set G.DPath} {C : Set V}
    (hFP : Disjoint (G.vertexSet F) (G.vertexSet P))
    (hFroof : G.vertexSet F ⊆ G.roof C)
    (hFclean : TerminalCleanAt G F C)
    (hPwarp : G.IsWarp P)
    (hProof : G.vertexSet P ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    {U : Set (G.quotient C).DPath}
    (hUstart : (G.quotient C).initialSet U ⊆
      G.terminalFrontier P)
    (hPterminal : G.terminalFrontier P ⊆ C) :
    Disjoint (G.vertexSet F)
      (G.vertexSet (frontierContinuation G hPwarp hProof htrim
        U hUstart)) := by
  let L := liftedQuotientFamily G C U
  let hc : G.StarCompatible P L :=
    starCompatible_liftQuotientFamily_of_frontier
      G hPwarp hProof htrim hUstart
  have hUstartC : (G.quotient C).initialSet U ⊆ C :=
    hUstart.trans hPterminal
  let hcF : G.StarCompatible F L :=
    starCompatible_liftQuotientFamily_of_roof
      G hFroof htrim hFclean hUstartC
  apply Set.disjoint_left.2
  intro x hxF hxContinuation
  have hxStar : x ∈ G.vertexSet (G.star hc) := hxContinuation
  rcases vertexSet_star_subset_union hc hxStar with hxP | hxL
  · exact Set.disjoint_left.1 hFP hxF hxP
  · obtain ⟨f, hfF, hxf⟩ := hxF
    obtain ⟨q, hqL, hxq⟩ := hxL
    have hglue := hcF f hfF q hqL x hxf hxq
    obtain ⟨q₀, hq₀U, rfl⟩ := hqL
    have hq₀Initial : q₀.initial ∈ (G.quotient C).initialSet U :=
      ⟨q₀, hq₀U, rfl⟩
    obtain ⟨p, hpP, hpTerminal⟩ := hUstart hq₀Initial
    apply Set.disjoint_left.1 hFP ⟨f, hfF, hxf⟩
    refine ⟨p, hpP, ?_⟩
    have hq₀x : q₀.initial = x := by
      simpa only [G.initial_liftQuotientPath] using hglue.2
    exact hq₀x ▸ G.terminal_mem_support hpTerminal

/-- Choosing the quotient family after deleting `Q` discharges the frozen
cross-disjointness obligation.  The old pending part is disjoint from the
frozen part, while the new quotient part avoids `Q` by construction. -/
theorem disjoint_frozen_frontierContinuation_deletedQuotientFamily
    (G : DWeb V) {F P : Set G.DPath} {C Q : Set V}
    (hFP : Disjoint (G.vertexSet F) (G.vertexSet P))
    (hFQ : G.vertexSet F ⊆ Q)
    (hPwarp : G.IsWarp P)
    (hProof : G.vertexSet P ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    {U : Set ((G.delete Q).quotient C).DPath}
    (hstart : ((G.delete Q).quotient C).initialSet U ⊆
      ((G.delete Q).quotient C).source)
    (hRstart : (G.quotient C).initialSet
        (SingularExtension.deletedQuotientFamily G C Q U) ⊆
      G.terminalFrontier P) :
    Disjoint (G.vertexSet F)
      (G.vertexSet (frontierContinuation G hPwarp hProof htrim
        (SingularExtension.deletedQuotientFamily G C Q U) hRstart)) := by
  let R := SingularExtension.deletedQuotientFamily G C Q U
  let L := liftedQuotientFamily G C R
  let hc : G.StarCompatible P L :=
    starCompatible_liftQuotientFamily_of_frontier
      G hPwarp hProof htrim hRstart
  have hLQ : Disjoint (G.vertexSet L) Q :=
    SingularExtension.lift_deletedQuotientFamily_vertexSet_disjoint hstart
  apply Set.disjoint_left.2
  intro x hxF hxContinuation
  have hxStar : x ∈ G.vertexSet (G.star hc) := by
    exact hxContinuation
  rcases vertexSet_star_subset_union hc hxStar with hxP | hxL
  · exact Set.disjoint_left.1 hFP hxF hxP
  · exact Set.disjoint_left.1 hLQ hxL (hFQ hxF)

theorem terminalFrontier_frozenFrontierContinuation_subset
    (G : DWeb V) {F : Set G.DPath} {C : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (hWfinite : G.HasFiniteCharacter W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    {U : Set (G.quotient C).DPath}
    (hUstart : (G.quotient C).initialSet U ⊆ G.terminalFrontier W)
    (hcover : G.terminalFrontier W ⊆
      (G.quotient C).initialSet U) :
    G.terminalFrontier
        (frozenFrontierContinuation G F hW hroof htrim U hUstart) ⊆
      G.terminalFrontier F ∪ (G.quotient C).terminalFrontier U := by
  rintro z ⟨p, hp, hpz⟩
  rcases hp with hpF | hpNew
  · exact Or.inl ⟨p, hpF, hpz⟩
  · exact Or.inr
      (terminalFrontier_frontierContinuation_subset
        G hW hWfinite hroof htrim hUstart hcover ⟨p, hpNew, hpz⟩)

/-- Bundled structural output for one safe frozen/frontier continuation.
The cross-disjointness premise is deliberately explicit: it is exactly the
safe-deletion or competitor-avoidance fact which the row machine must
construct before invoking the lower half-way clause. -/
theorem frozenFrontierContinuation_structural
    (G : DWeb V) {F : Set G.DPath} {C : Set V} {W : Set G.DPath}
    (hF : G.IsWarp F) (hW : G.IsWarp W)
    (hFfinite : G.HasFiniteCharacter F)
    (hWfinite : G.HasFiniteCharacter W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    {U : Set (G.quotient C).DPath}
    (hU : (G.quotient C).IsWarp U)
    (hUfinite : (G.quotient C).HasFiniteCharacter U)
    (hUinitial : (G.quotient C).initialSet U = G.terminalFrontier W)
    (hcross : Disjoint (G.vertexSet F)
      (G.vertexSet
        (frontierContinuation G hW hroof htrim U hUinitial.le))) :
    G.IsWarp
        (frozenFrontierContinuation G F hW hroof htrim U hUinitial.le) ∧
      G.HasFiniteCharacter
        (frozenFrontierContinuation G F hW hroof htrim U hUinitial.le) ∧
      G.ForwardExtension (F ∪ W)
        (frozenFrontierContinuation G F hW hroof htrim U hUinitial.le) ∧
      G.initialSet
        (frozenFrontierContinuation G F hW hroof htrim U hUinitial.le) =
        G.initialSet (F ∪ W) := by
  have hforward := forwardExtension_frozenFrontierContinuation
    G F hW hroof htrim U hUinitial.le
  exact ⟨frozenFrontierContinuation_isWarp
      G hF hW hroof htrim hU hUinitial.le hcross,
    frozenFrontierContinuation_finiteCharacter
      G hFfinite hW hWfinite hroof htrim hUfinite hUinitial.le,
    hforward,
    (G.initialSet_eq_of_forwardExtension hforward).symm⟩

/-- Complete frozen/selected-pending re-entry through a lower half-way
witness chosen after a safe frozen deletion.  This theorem makes the exact
extra safety premise visible through `hrequest` and the type of `hU`; the
preceding lower-induction theorem supplies such an `hU` once the deleted
quotient is known to be unhindered. -/
theorem exists_frozenSelectedPendingContinuation_of_deletedAuxiliaryHalfway
    {G : DWeb V} (hNorm : G.IsNormalized)
    {F W₁ W₂ : Set G.DPath} (S : SplitStopover G W₂)
    (hFsub : F ⊆ W₂) (hsub : W₁ ⊆ W₂)
    (hdecomp : F ∪ SingularExtension.pendingPart G W₁ = W₂)
    (hfamilyDisjoint : Disjoint F (SingularExtension.pendingPart G W₁))
    (hWwarp : G.IsWarp W₂)
    (hWfinite : G.HasFiniteCharacter W₂)
    (hsource : G.initialSet W₁ ⊆ G.source)
    {Q : Set V} (hFQ : G.vertexSet F ⊆ Q)
    (hrequest : pendingRequests G W₁ S.boundary ⊆
      ((G.delete Q).quotient S.boundary).source)
    {mu : Cardinal.{u}}
    {U : Set (deletedPendingAuxiliaryWeb
      G W₁ S.boundary Q).DPath}
    (hU : IsHalfwayLinkageOfAltitude
      (deletedPendingAuxiliaryWeb G W₁ S.boundary Q)
      (pendingRequests G W₁ S.boundary) mu U) :
    ∃ T : Set G.DPath,
      G.IsWarp T ∧
      G.HasFiniteCharacter T ∧
      G.ForwardExtension W₂ T ∧
      G.initialSet T = G.initialSet W₂ ∧
      LinksToTarget G T
        (G.initialSet (SingularExtension.pendingPart G W₁)) ∧
      G.terminalFrontier T ⊆
        G.terminalFrontier F ∪
          (G.quotient S.boundary).terminalFrontier
            (SingularExtension.deletedQuotientFamily G S.boundary Q
              (forgetDeletedPendingAuxiliaryFamily
                G W₁ S.boundary Q U)) := by
  let P := SingularExtension.pendingPart G W₁
  let U₀ := forgetDeletedPendingAuxiliaryFamily G W₁ S.boundary Q U
  let R := SingularExtension.deletedQuotientFamily G S.boundary Q U₀
  have hPtrivial : ∀ p ∈ boundaryPendingPart G W₁ S.boundary,
      p = G.trivialPath p.initial :=
    boundaryPendingPart_trivial_mono G hsub S.boundary_pending_trivial
  have hrequestFront : pendingRequests G W₁ S.boundary =
      G.terminalFrontier P :=
    pendingRequests_eq_terminalFrontier_pendingPart_of_trivial_selected
      hsource hPtrivial
  have hPwarp : G.IsWarp P := by
    intro p hp q hq hpq
    exact hWwarp (hsub hp.1) (hsub hq.1) hpq
  have hPfinite : G.HasFiniteCharacter P := by
    intro p hp
    exact hWfinite (hsub hp.1)
  have hFwarp : G.IsWarp F := by
    intro p hp q hq hpq
    exact hWwarp (hFsub hp) (hFsub hq) hpq
  have hFfinite : G.HasFiniteCharacter F := by
    intro p hp
    exact hWfinite (hFsub hp)
  have hProof : G.vertexSet P ⊆ G.roof S.boundary :=
    pendingPart_selected_vertexSet_subset_roof_of_split
      S hsub hsource S.boundary_pending_trivial
  have hFPvertex : Disjoint (G.vertexSet F) (G.vertexSet P) := by
    apply Set.disjoint_left.2
    intro x hxF hxP
    obtain ⟨p, hpF, hxp⟩ := hxF
    obtain ⟨q, hqP, hxq⟩ := hxP
    have hpq : p ≠ q := by
      intro heq
      subst q
      exact Set.disjoint_left.1 hfamilyDisjoint hpF hqP
    exact Set.disjoint_left.1
      (hWwarp (hFsub hpF) (hsub hqP.1) hpq) hxp hxq
  obtain ⟨hRwarp, hRfinite, hRinitialRequest, hRlinksRequest, _hRQ⟩ :=
    deletedPendingAuxiliaryHalfway_quotientPayload hrequest hU
  have hRinitial : (G.quotient S.boundary).initialSet R =
      G.terminalFrontier P := hRinitialRequest.trans hrequestFront
  have hRlinks : LinksToTarget (G.quotient S.boundary) R
      (G.terminalFrontier P) := by
    simpa only [hrequestFront] using hRlinksRequest
  have hU₀initial : ((G.delete Q).quotient S.boundary).initialSet U₀ =
      pendingRequests G W₁ S.boundary := by
    rw [← SingularExtension.deletedQuotientFamily_initialSet]
    exact hRinitialRequest
  have hU₀start : ((G.delete Q).quotient S.boundary).initialSet U₀ ⊆
      ((G.delete Q).quotient S.boundary).source := by
    rw [hU₀initial]
    exact hrequest
  have hcross : Disjoint (G.vertexSet F)
      (G.vertexSet (frontierContinuation G hPwarp hProof S.minimal
        R hRinitial.le)) :=
    disjoint_frozen_frontierContinuation_deletedQuotientFamily
      G hFPvertex hFQ hPwarp hProof S.minimal hU₀start hRinitial.le
  let T := frozenFrontierContinuation G F hPwarp hProof S.minimal
    R hRinitial.le
  have hstruct := frozenFrontierContinuation_structural G
    hFwarp hPwarp hFfinite hPfinite hProof S.minimal
    hRwarp hRfinite hRinitial hcross
  have hPsource : G.initialSet P ⊆ G.source := by
    rintro x ⟨p, hp, hpx⟩
    exact hsource ⟨p, hp.1, hpx⟩
  have hRambientLinks : LinksToTarget G
      (frontierContinuation G hPwarp hProof S.minimal R hRinitial.le)
      (G.initialSet P) :=
    linksToTarget_frontierContinuation hNorm hPwarp hPfinite hProof
      S.minimal hRwarp hRfinite hRinitial Set.Subset.rfl hPsource
      (routesTerminals_initialSet_terminalFrontier hPfinite) hRlinks
  refine ⟨T, hstruct.1, hstruct.2.1, ?_, ?_, ?_, ?_⟩
  · rw [← hdecomp]
    exact hstruct.2.2.1
  · rw [hstruct.2.2.2, hdecomp]
  · intro b hb
    obtain ⟨p, hp, hrest⟩ := hRambientLinks b hb
    exact ⟨p, Or.inr hp, hrest⟩
  · exact terminalFrontier_frozenFrontierContinuation_subset
      G hPwarp hPfinite hProof S.minimal hRinitial.le hRinitial.ge

/-- Complete one forward frozen-pending continuation directly from the
future-safe residual certificate.  This is the construction-facing form of
`exists_frozenSelectedPendingContinuation_of_deletedAuxiliaryHalfway`: the
lower-cardinal invocation and the deleted quotient transport are both
internal, and no unhinderedness assertion about the whole deleted quotient
is required. -/
theorem exists_frozenSelectedPendingContinuation_of_safety
    {kappa mu : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa)
    {G : DWeb V} (hNorm : G.IsNormalized)
    {F W₁ W₂ : Set G.DPath} (S : SplitStopover G W₂)
    (hFsub : F ⊆ W₂) (hsub : W₁ ⊆ W₂)
    (hdecomp : F ∪ SingularExtension.pendingPart G W₁ = W₂)
    (hfamilyDisjoint : Disjoint F (SingularExtension.pendingPart G W₁))
    (hWwarp : G.IsWarp W₂)
    (hWfinite : G.HasFiniteCharacter W₂)
    (hsource : G.initialSet W₁ ⊆ G.source)
    {Q : Set V} (hFQ : G.vertexSet F ⊆ Q)
    (hsafe : DeletedPendingSafety G W₁ S.boundary Q mu) :
    ∃ (U : Set (deletedPendingAuxiliaryWeb
        G W₁ S.boundary Q).DPath) (T : Set G.DPath),
      IsHalfwayLinkageOfAltitude
          (deletedPendingAuxiliaryWeb G W₁ S.boundary Q)
          (pendingRequests G W₁ S.boundary)
          (altitude (deletedPendingAuxiliaryWeb G W₁ S.boundary Q) U) U ∧
      G.IsWarp T ∧
      G.HasFiniteCharacter T ∧
      G.ForwardExtension W₂ T ∧
      G.initialSet T = G.initialSet W₂ ∧
      LinksToTarget G T
        (G.initialSet (SingularExtension.pendingPart G W₁)) ∧
      G.terminalFrontier T ⊆
        G.terminalFrontier F ∪
          (G.quotient S.boundary).terminalFrontier
            (SingularExtension.deletedQuotientFamily G S.boundary Q
              (forgetDeletedPendingAuxiliaryFamily
                G W₁ S.boundary Q U)) := by
  obtain ⟨U, hU⟩ :=
    hsafe.exists_halfway_of_lower_extension hlower hmu
  obtain ⟨T, hT⟩ :=
    exists_frozenSelectedPendingContinuation_of_deletedAuxiliaryHalfway
    hNorm S hFsub hsub hdecomp hfamilyDisjoint hWwarp hWfinite hsource hFQ
      hsafe.requests_source hU
  exact ⟨U, T, hU, hT⟩

/-- The concrete three-piece successor needed by a target row.  Only the
completed part is protected by the future-safe deleted set.  Pending paths
outside the selected subfamily are kept verbatim: their roof and terminal-
clean certificates make them automatically disjoint from the new quotient
continuation. -/
theorem exists_threePieceSelectedPendingContinuation_of_safety
    {kappa mu : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hmu : mu < kappa)
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W₁ W₂ : Set G.DPath} (S : SplitStopover G W₂)
    (hsub : W₁ ⊆ W₂)
    (hWwarp : G.IsWarp W₂)
    (hWfinite : G.HasFiniteCharacter W₂)
    (hWsource : G.initialSet W₂ ⊆ G.source)
    {Q : Set V}
    (hcompletedQ :
      G.vertexSet (SingularExtension.completedPart G W₂) ⊆ Q)
    (hsafe : DeletedPendingSafety G W₁ S.boundary Q mu) :
    ∃ (U : Set (deletedPendingAuxiliaryWeb
        G W₁ S.boundary Q).DPath) (T : Set G.DPath),
      IsHalfwayLinkageOfAltitude
          (deletedPendingAuxiliaryWeb G W₁ S.boundary Q)
          (pendingRequests G W₁ S.boundary)
          (altitude (deletedPendingAuxiliaryWeb G W₁ S.boundary Q) U) U ∧
      G.IsWarp T ∧
      G.HasFiniteCharacter T ∧
      G.ForwardExtension W₂ T ∧
      G.initialSet T = G.initialSet W₂ ∧
      LinksToTarget G T
        (G.initialSet (SingularExtension.pendingPart G W₁)) ∧
      G.terminalFrontier T ⊆
        G.terminalFrontier
            (SingularExtension.completedPart G W₂ ∪
              (SingularExtension.pendingPart G W₂ \
                SingularExtension.pendingPart G W₁)) ∪
          (G.quotient S.boundary).terminalFrontier
            (SingularExtension.deletedQuotientFamily G S.boundary Q
              (forgetDeletedPendingAuxiliaryFamily
                G W₁ S.boundary Q U)) := by
  let P := SingularExtension.pendingPart G W₁
  let R := SingularExtension.pendingPart G W₂ \ P
  let F := SingularExtension.completedPart G W₂
  let K := F ∪ R
  obtain ⟨U, hU⟩ :=
    hsafe.exists_halfway_of_lower_extension hlower hmu
  let U₀ := forgetDeletedPendingAuxiliaryFamily G W₁ S.boundary Q U
  let L := SingularExtension.deletedQuotientFamily G S.boundary Q U₀
  have hsource₁ : G.initialSet W₁ ⊆ G.source := by
    rintro x ⟨p, hp, hpx⟩
    exact hWsource ⟨p, hsub hp, hpx⟩
  have hPsub : P ⊆ SingularExtension.pendingPart G W₂ :=
    pendingPart_mono G hsub
  have hPsubW : P ⊆ W₂ := by
    intro p hp
    exact hsub hp.1
  have hRsubW : R ⊆ W₂ := by
    intro p hp
    exact hp.1.1
  have hFsubW : F ⊆ W₂ := by
    intro p hp
    exact hp.1
  have hKsubW : K ⊆ W₂ := Set.union_subset hFsubW hRsubW
  have hdecomp : K ∪ P = W₂ := by
    apply Set.Subset.antisymm
    · exact Set.union_subset hKsubW (hPsub.trans fun _ hp ↦ hp.1)
    · intro p hpW
      by_cases hpCompleted : p ∈ F
      · exact Or.inl (Or.inl hpCompleted)
      · have hpPending : p ∈ SingularExtension.pendingPart G W₂ :=
          ⟨hpW, hpCompleted⟩
        by_cases hpP : p ∈ P
        · exact Or.inr hpP
        · exact Or.inl (Or.inr ⟨hpPending, hpP⟩)
  have hPwarp : G.IsWarp P := by
    intro p hp q hq hpq
    exact hWwarp (hPsubW hp) (hPsubW hq) hpq
  have hPfinite : G.HasFiniteCharacter P := by
    intro p hp
    exact hWfinite (hPsubW hp)
  have hKwarp : G.IsWarp K := by
    intro p hp q hq hpq
    exact hWwarp (hKsubW hp) (hKsubW hq) hpq
  have hKfinite : G.HasFiniteCharacter K := by
    intro p hp
    exact hWfinite (hKsubW hp)
  have hProof : G.vertexSet P ⊆ G.roof S.boundary :=
    pendingPart_selected_vertexSet_subset_roof_of_split
      S hsub hsource₁ S.boundary_pending_trivial
  have hPendingRoof :
      G.vertexSet (SingularExtension.pendingPart G W₂) ⊆
        G.roof S.boundary :=
    pendingPart_selected_vertexSet_subset_roof_of_split
      S Set.Subset.rfl hWsource S.boundary_pending_trivial
  have hRroof : G.vertexSet R ⊆ G.roof S.boundary := by
    rintro x ⟨p, hpR, hxp⟩
    exact hPendingRoof ⟨p, hpR.1, hxp⟩
  have hPendingClean : TerminalCleanAt G
      (SingularExtension.pendingPart G W₂) S.boundary :=
    pendingPart_selected_terminalClean_of_split
      S Set.Subset.rfl hWsource
  have hRclean : TerminalCleanAt G R S.boundary := by
    intro p hp
    exact hPendingClean p hp.1
  have hPterminal : G.terminalFrontier P ⊆ S.boundary := by
    rintro x ⟨p, hpP, hpx⟩
    exact S.terminal_subset ⟨p, hPsubW hpP, hpx⟩
  have hFPvertex : Disjoint (G.vertexSet F) (G.vertexSet P) := by
    apply Set.disjoint_left.2
    rintro x ⟨f, hfF, hxf⟩ ⟨p, hpP, hxp⟩
    have hfp : f ≠ p := by
      intro hfp
      subst p
      exact hpP.2 ⟨hpP.1, hfF.2⟩
    exact Set.disjoint_left.1
      (hWwarp (hFsubW hfF) (hPsubW hpP) hfp) hxf hxp
  have hRPvertex : Disjoint (G.vertexSet R) (G.vertexSet P) := by
    apply Set.disjoint_left.2
    rintro x ⟨r, hrR, hxr⟩ ⟨p, hpP, hxp⟩
    have hrp : r ≠ p := by
      intro hrp
      subst p
      exact hrR.2 hpP
    exact Set.disjoint_left.1
      (hWwarp (hRsubW hrR) (hPsubW hpP) hrp) hxr hxp
  have hPtrivial : ∀ p ∈ boundaryPendingPart G W₁ S.boundary,
      p = G.trivialPath p.initial :=
    boundaryPendingPart_trivial_mono G hsub
      S.boundary_pending_trivial
  have hrequestFront : pendingRequests G W₁ S.boundary =
      G.terminalFrontier P :=
    pendingRequests_eq_terminalFrontier_pendingPart_of_trivial_selected
      hsource₁ hPtrivial
  obtain ⟨hLwarp, hLfinite, hLinitialRequest, hLlinksRequest, _hLQ⟩ :=
    deletedPendingAuxiliaryHalfway_quotientPayload
      hsafe.requests_source hU
  have hLinitial : (G.quotient S.boundary).initialSet L =
      G.terminalFrontier P := hLinitialRequest.trans hrequestFront
  have hLlinks : LinksToTarget (G.quotient S.boundary) L
      (G.terminalFrontier P) := by
    simpa only [hrequestFront] using hLlinksRequest
  have hU₀initial : ((G.delete Q).quotient S.boundary).initialSet U₀ =
      pendingRequests G W₁ S.boundary := by
    rw [← SingularExtension.deletedQuotientFamily_initialSet]
    exact hLinitialRequest
  have hU₀start : ((G.delete Q).quotient S.boundary).initialSet U₀ ⊆
      ((G.delete Q).quotient S.boundary).source := by
    rw [hU₀initial]
    exact hsafe.requests_source
  have hcrossF : Disjoint (G.vertexSet F)
      (G.vertexSet (frontierContinuation G hPwarp hProof S.minimal
        L hLinitial.le)) :=
    disjoint_frozen_frontierContinuation_deletedQuotientFamily
      G hFPvertex hcompletedQ hPwarp hProof S.minimal
        hU₀start hLinitial.le
  have hcrossR : Disjoint (G.vertexSet R)
      (G.vertexSet (frontierContinuation G hPwarp hProof S.minimal
        L hLinitial.le)) :=
    disjoint_roofedClean_frontierContinuation
      G hRPvertex hRroof hRclean hPwarp hProof S.minimal
        hLinitial.le hPterminal
  have hcrossK : Disjoint (G.vertexSet K)
      (G.vertexSet (frontierContinuation G hPwarp hProof S.minimal
        L hLinitial.le)) := by
    rw [G.vertexSet_union]
    exact Set.disjoint_union_left.mpr ⟨hcrossF, hcrossR⟩
  let T := frozenFrontierContinuation G K hPwarp hProof S.minimal
    L hLinitial.le
  have hstruct := frozenFrontierContinuation_structural G
    hKwarp hPwarp hKfinite hPfinite hProof S.minimal
      hLwarp hLfinite hLinitial hcrossK
  have hPsource : G.initialSet P ⊆ G.source := by
    rintro x ⟨p, hp, hpx⟩
    exact hsource₁ ⟨p, hp.1, hpx⟩
  have hLambientLinks : LinksToTarget G
      (frontierContinuation G hPwarp hProof S.minimal L hLinitial.le)
      (G.initialSet P) :=
    linksToTarget_frontierContinuation hNorm hPwarp hPfinite hProof
      S.minimal hLwarp hLfinite hLinitial Set.Subset.rfl hPsource
      (routesTerminals_initialSet_terminalFrontier hPfinite) hLlinks
  refine ⟨U, T, hU, hstruct.1, hstruct.2.1, ?_, ?_, ?_, ?_⟩
  · rw [← hdecomp]
    exact hstruct.2.2.1
  · rw [hstruct.2.2.2, hdecomp]
  · intro b hb
    obtain ⟨p, hp, hrest⟩ := hLambientLinks b hb
    exact ⟨p, Or.inr hp, hrest⟩
  · exact terminalFrontier_frozenFrontierContinuation_subset
      G hPwarp hPfinite hProof S.minimal hLinitial.le hLinitial.ge

/-! ## The exact restricted quotient family -/

/-- Keep precisely the quotient components whose initial vertices lie in a
specified request set. -/
def quotientInitialRestriction
    (G : DWeb V) (C : Set V) (U : Set (G.quotient C).DPath)
    (A : Set V) : Set (G.quotient C).DPath :=
  initialRestriction (G.quotient C) U A

@[simp] theorem mem_quotientInitialRestriction
    {G : DWeb V} {C A : Set V} {U : Set (G.quotient C).DPath}
    {q : (G.quotient C).DPath} :
    q ∈ quotientInitialRestriction G C U A ↔ q ∈ U ∧ q.initial ∈ A :=
  Iff.rfl

theorem quotientInitialRestriction_isWarp
    {G : DWeb V} {C A : Set V} {U : Set (G.quotient C).DPath}
    (hU : (G.quotient C).IsWarp U) :
    (G.quotient C).IsWarp (quotientInitialRestriction G C U A) := by
  intro p hp q hq hpq
  exact hU hp.1 hq.1 hpq

theorem quotientInitialRestriction_finiteCharacter
    {G : DWeb V} {C A : Set V} {U : Set (G.quotient C).DPath}
    (hU : (G.quotient C).HasFiniteCharacter U) :
    (G.quotient C).HasFiniteCharacter
      (quotientInitialRestriction G C U A) := by
  intro p hp
  exact hU hp.1

theorem initialSet_quotientInitialRestriction_subset
    (G : DWeb V) (C : Set V) (U : Set (G.quotient C).DPath)
    (A : Set V) :
    (G.quotient C).initialSet (quotientInitialRestriction G C U A) ⊆ A := by
  rintro x ⟨q, hq, rfl⟩
  exact hq.2

/-- Restriction has exactly `A` as its initial set whenever the original
family covers every vertex of `A`. -/
theorem initialSet_quotientInitialRestriction_eq_of_subset
    (G : DWeb V) (C : Set V) (U : Set (G.quotient C).DPath)
    (A : Set V) (hA : A ⊆ (G.quotient C).initialSet U) :
    (G.quotient C).initialSet (quotientInitialRestriction G C U A) = A := by
  apply Set.Subset.antisymm
  · exact initialSet_quotientInitialRestriction_subset G C U A
  · intro x hxA
    obtain ⟨q, hqU, hqx⟩ := hA hxA
    exact ⟨q, ⟨hqU, hqx ▸ hxA⟩, hqx⟩

/-- Quotient paths selected at the initials of a boundary-trivial pending
family directly replace that family by forward extensions. -/
theorem forwardExtension_boundaryPending_liftQuotientRestriction
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    {U : Set (G.quotient C).DPath}
    (htrivial : ∀ p ∈ boundaryPendingPart G W C,
      p = G.trivialPath p.initial)
    (hcover : G.initialSet (boundaryPendingPart G W C) ⊆
      (G.quotient C).initialSet U) :
    G.ForwardExtension (boundaryPendingPart G W C)
      (liftedQuotientFamily G C
        (quotientInitialRestriction G C U
          (G.initialSet (boundaryPendingPart G W C)))) := by
  apply forwardExtension_of_trivial_of_initialSet_eq G htrivial
  rw [G.initialSet_liftQuotientFamily,
    initialSet_quotientInitialRestriction_eq_of_subset G C U _ hcover]

/-- Terminal cleanliness and finite character discharge the boundary-
trivial premise of the direct quotient replacement. -/
theorem forwardExtension_boundaryPending_liftQuotientRestriction_of_clean
    (G : DWeb V) {C : Set V} {W : Set G.DPath}
    {U : Set (G.quotient C).DPath}
    (hfinite : G.HasFiniteCharacter W)
    (hclean : TerminalCleanAt G W C)
    (hcover : G.initialSet (boundaryPendingPart G W C) ⊆
      (G.quotient C).initialSet U) :
    G.ForwardExtension (boundaryPendingPart G W C)
      (liftedQuotientFamily G C
        (quotientInitialRestriction G C U
          (G.initialSet (boundaryPendingPart G W C)))) := by
  apply forwardExtension_boundaryPending_liftQuotientRestriction G
  · exact fun p hp ↦
      boundaryPendingPart_eq_trivialPath_of_terminalCleanAt hfinite hclean hp
  · exact hcover

/-- A full-source quotient linkage covers every requested terminal, hence
restriction to those starts has exactly that initial set. -/
theorem initialSet_quotientInitialRestriction_eq
    {G : DWeb V} {C A E : Set V}
    {U : Set (G.quotient C).DPath}
    (hU : IsLinkageBetween (G.quotient C) (G.quotient C).source E U)
    (hA : A ⊆ (G.quotient C).source) :
    (G.quotient C).initialSet (quotientInitialRestriction G C U A) = A := by
  apply Set.Subset.antisymm
  · exact initialSet_quotientInitialRestriction_subset G C U A
  · intro x hxA
    have hxInitial : x ∈ (G.quotient C).initialSet U := by
      rw [hU.initialSet_eq]
      exact hA hxA
    obtain ⟨q, hqU, hqx⟩ := hxInitial
    exact ⟨q, ⟨hqU, hqx ▸ hxA⟩, hqx⟩

/-- Restricting a full quotient half-way linkage to selected terminal starts
provides the exact family needed by `frontierContinuation`. -/
theorem restrictedHalfway_initialSet_eq_frontier
    {G : DWeb V} {C A : Set V} {kappa : Cardinal.{u}}
    {U : Set (G.quotient C).DPath}
    (hU : IsHalfwayLinkageOfAltitude (G.quotient C) A kappa U)
    (hA : A ⊆ (G.quotient C).source) :
    (G.quotient C).initialSet (quotientInitialRestriction G C U A) = A := by
  obtain ⟨E, hE⟩ := hU.1
  exact initialSet_quotientInitialRestriction_eq hE.linkage hA

end SingularPendingReentry
end CardinalInduction
end Erdos599
