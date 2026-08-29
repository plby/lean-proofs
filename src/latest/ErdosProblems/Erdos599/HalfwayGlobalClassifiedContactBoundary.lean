/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayGlobalClassifiedContactAggregation
import ErdosProblems.Erdos599.GroundingFiniteAlternatingRoot

/-!
# Endpoint-specific boundary of a reclassified contact piece

The coarse global classification says that one endpoint of every omitted
shortcut lies on the limiting reference.  For an actual bracket-alternating
piece, its backward links lie on the selected reference as well.  This extra
literal fact upgrades the coarse disjunction to the endpoint needed by the
boundary calculation: a terminal with no retained incoming forward edge is
on the limiting reference, and dually an initial with no retained outgoing
forward edge is on the limiting reference.

These are direct lemmas about one concrete piece.  They do not introduce an
environment record or assert that arbitrary classified segmentation data was
constructed by the Section 9 splitter.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder Alternating

universe u v

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {X : Set V} {kappa : Cardinal.{u}}

private theorem eq_of_reflTransGen_of_noIncoming
    {E : Set (V × V)} {a b : V}
    (h : Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b)
    (hno : ¬ ∃ x, (x, b) ∈ E) : a = b := by
  rcases Relation.ReflTransGen.cases_tail h with hab | ⟨x, _hax, hxb⟩
  · exact hab.symm
  · exact False.elim (hno ⟨x, hxb⟩)

namespace ClassifiedFiniteContactPiece

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {Q : AltPath Gamma.graph} {u v : V}

private theorem selectedReference_mem_limitWarp
    {x : V} (R : ClosedReferenceOwner C.selectedReference X x) :
    x ∈ Gamma.vertexSet C.ladder.limitWarp := by
  let R' := (C.limitingReferenceEndpointOwner_of_selected R.mem R.contains).some
  exact ⟨R'.path, R'.mem, R'.contains⟩

private theorem limitingOwner_mem
    {x : V} (R : ClubStageGeometry.LimitingReferenceEndpointOwner C x) :
    x ∈ Gamma.vertexSet C.ladder.limitWarp :=
  ⟨R.path, R.mem, R.contains⟩

/-- If the shortcut of a concrete bracket-alternating finite piece is
deleted by limiting-reference reclassification, a terminal which receives
no literal forward edge is a limiting-reference vertex. -/
theorem terminal_mem_limitWarp_of_omittedShortcut_of_noIncoming
    (P : ClassifiedFiniteContactPiece
      (Y := C.selectedReference) (kappa := kappa) Q X u v)
    (hback : BackwardLinksOn C.selectedReference P.path)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (hlocal : (u, v) ∈ P.shortcutEdges)
    (hglobal : (u, v) ∉ P.limitingShortcutEdges hSafeRoof)
    (hno : ¬ ∃ x, (x, v) ∈ P.path.directionEdges .forward) :
    v ∈ Gamma.vertexSet C.ladder.limitWarp := by
  have hcovered :=
    (P.covered_of_not_mem_limitingShortcut hSafeRoof hlocal hglobal).1
  rcases hcovered with hRu | hRv
  · obtain ⟨Ru⟩ := hRu
    cases hpath : P.path with
    | trivial w =>
        have hwu : w = u := by
          have := P.starts_at
          rw [hpath] at this
          exact this
        have hwv : w = v := by
          have := P.ends_at
          rw [hpath] at this
          exact Option.some.inj this
        have huv : u = v := hwu.symm.trans hwv
        exact ⟨Ru.path, Ru.mem, by simpa only [huv] using Ru.contains⟩
    | finite T =>
        have hbackT : BackwardLinksOn C.selectedReference (.finite T) := by
          simpa only [hpath] using hback
        have hterminal : T.terminal = v := by
          have := P.ends_at
          rw [hpath] at this
          exact Option.some.inj this
        have hinitial : T.initial = u := by
          have := P.starts_at
          rw [hpath] at this
          exact this
        have hnoT : ¬ ∃ x,
            (x, T.terminal) ∈ (AltPath.finite T).directionEdges .forward := by
          simpa only [hterminal, hpath] using hno
        rcases T.initial_or_backwardOwner_reaches_terminal hbackT
            (Set.Subset.rfl) with hreach |
            ⟨l, _hl, _hldir, parent, hparent, hsub, hreach⟩
        · have heq : T.initial = T.terminal :=
            eq_of_reflTransGen_of_noIncoming hreach hnoT
          have huv : u = v := hinitial.symm.trans (heq.trans hterminal)
          exact ⟨Ru.path, Ru.mem, by simpa only [huv] using Ru.contains⟩
        · have heq : l.path.start = T.terminal :=
            eq_of_reflTransGen_of_noIncoming hreach hnoT
          have hvParent : v ∈ parent.support := by
            rw [← hterminal, ← heq]
            exact hsub.1 l.path.start_mem_support
          let R := (C.limitingReferenceEndpointOwner_of_selected
            hparent hvParent).some
          exact ⟨R.path, R.mem, R.contains⟩
    | infinite T =>
        have := P.ends_at
        rw [hpath] at this
        simp at this
  · obtain ⟨Rv⟩ := hRv
    exact ⟨Rv.path, Rv.mem, Rv.contains⟩

/-- Sink-side counterpart.  If the terminal rather than the initial is the
covered endpoint, the first link is either backward (so the initial lies on
its selected-reference owner) or forward (contradicting the absence of a
retained outgoing edge). -/
theorem initial_mem_limitWarp_of_omittedShortcut_of_noOutgoing
    (P : ClassifiedFiniteContactPiece
      (Y := C.selectedReference) (kappa := kappa) Q X u v)
    (hback : BackwardLinksOn C.selectedReference P.path)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (hlocal : (u, v) ∈ P.shortcutEdges)
    (hglobal : (u, v) ∉ P.limitingShortcutEdges hSafeRoof)
    (hno : ¬ ∃ y, (u, y) ∈ P.path.directionEdges .forward) :
    u ∈ Gamma.vertexSet C.ladder.limitWarp := by
  have hcovered :=
    (P.covered_of_not_mem_limitingShortcut hSafeRoof hlocal hglobal).1
  rcases hcovered with hRu | hRv
  · obtain ⟨Ru⟩ := hRu
    exact ⟨Ru.path, Ru.mem, Ru.contains⟩
  · obtain ⟨Rv⟩ := hRv
    cases hpath : P.path with
    | trivial w =>
        have hwu : w = u := by
          have := P.starts_at
          rw [hpath] at this
          exact this
        have hwv : w = v := by
          have := P.ends_at
          rw [hpath] at this
          exact Option.some.inj this
        have huv : u = v := hwu.symm.trans hwv
        exact ⟨Rv.path, Rv.mem, by simpa only [huv] using Rv.contains⟩
    | finite T =>
        have hbackT : BackwardLinksOn C.selectedReference (.finite T) := by
          simpa only [hpath] using hback
        have hinitial : T.initial = u := by
          have := P.starts_at
          rw [hpath] at this
          exact this
        cases hdir : T.firstLink.direction with
        | backward =>
            obtain ⟨parent, hparent, hsub⟩ :=
              hbackT T.firstLink T.firstLink_mem_links hdir
            have huParent : u ∈ parent.support := by
              have hfinish : T.firstLink.path.finish = u := by
                calc
                  T.firstLink.path.finish = T.firstLink.entry := by
                    simp [Link.entry, hdir]
                  _ = T.initial := rfl
                  _ = u := hinitial
              rw [← hfinish]
              exact hsub.1 T.firstLink.path.finish_mem_support
            let R := (C.limitingReferenceEndpointOwner_of_selected
              hparent huParent).some
            exact ⟨R.path, R.mem, R.contains⟩
        | forward =>
            exfalso
            obtain ⟨y, huy⟩ :=
              T.firstLink.path.walk.exists_outgoing_edge_of_mem_of_ne_finish
                T.firstLink.path.start_mem_support T.firstLink.nontrivial
            apply hno
            refine ⟨y, ?_⟩
            have hstart : T.firstLink.path.start = u := by
              calc
                T.firstLink.path.start = T.firstLink.entry := by
                  simp [Link.entry, hdir]
                _ = T.initial := rfl
                _ = u := hinitial
            rw [hpath, ← hstart]
            simp only [AltPath.directionEdges, Set.mem_iUnion]
            exact ⟨T.firstLink, T.firstLink_mem_links, hdir, huy⟩
    | infinite T =>
        have := P.ends_at
        rw [hpath] at this
        simp at this

end ClassifiedFiniteContactPiece

namespace ClassifiedContactChain

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {Q : AltPath Gamma.graph} {I J : Type v}

/-- Endpoint-specific root accounting for one classified contact chain. -/
theorem omittedShortcut_head_mem_limitWarp_of_noIncomingOriginalForward
    (K : ClassifiedContactChain
      (Y := C.selectedReference) (kappa := kappa) Q X I J)
    (hback : ∀ i, BackwardLinksOn C.selectedReference (K.piece i).path)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    {a b : V} (hab : (a, b) ∈ K.shortcutEdges)
    (hnot : (a, b) ∉ K.limitingShortcutEdges hSafeRoof)
    (hno : ¬ ∃ x, (x, b) ∈ Q.directionEdges .forward) :
    b ∈ Gamma.vertexSet C.ladder.limitWarp := by
  simp only [shortcutEdges, Set.mem_iUnion] at hab
  obtain ⟨i, hab⟩ := hab
  have hpair := (K.piece i).mem_shortcutEdges_eq hab
  have ha : a = K.point (K.source i) := congrArg Prod.fst hpair
  have hb : b = K.point (K.target i) := congrArg Prod.snd hpair
  subst a
  subst b
  have hnotPiece :
      (K.point (K.source i), K.point (K.target i)) ∉
        (K.piece i).limitingShortcutEdges hSafeRoof := by
    intro h
    apply hnot
    exact Set.mem_iUnion.2 ⟨i, h⟩
  apply (K.piece i).terminal_mem_limitWarp_of_omittedShortcut_of_noIncoming
    (hback i) hSafeRoof hab hnotPiece
  rintro ⟨x, hx⟩
  exact hno ⟨x, (K.piece i).forwardEdges_subset_original hx⟩

/-- Endpoint-specific sink accounting for one classified contact chain. -/
theorem omittedShortcut_tail_mem_limitWarp_of_noOutgoingOriginalForward
    (K : ClassifiedContactChain
      (Y := C.selectedReference) (kappa := kappa) Q X I J)
    (hback : ∀ i, BackwardLinksOn C.selectedReference (K.piece i).path)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    {a b : V} (hab : (a, b) ∈ K.shortcutEdges)
    (hnot : (a, b) ∉ K.limitingShortcutEdges hSafeRoof)
    (hno : ¬ ∃ y, (a, y) ∈ Q.directionEdges .forward) :
    a ∈ Gamma.vertexSet C.ladder.limitWarp := by
  simp only [shortcutEdges, Set.mem_iUnion] at hab
  obtain ⟨i, hab⟩ := hab
  have hpair := (K.piece i).mem_shortcutEdges_eq hab
  have ha : a = K.point (K.source i) := congrArg Prod.fst hpair
  have hb : b = K.point (K.target i) := congrArg Prod.snd hpair
  subst a
  subst b
  have hnotPiece :
      (K.point (K.source i), K.point (K.target i)) ∉
        (K.piece i).limitingShortcutEdges hSafeRoof := by
    intro h
    apply hnot
    exact Set.mem_iUnion.2 ⟨i, h⟩
  apply (K.piece i).initial_mem_limitWarp_of_omittedShortcut_of_noOutgoing
    (hback i) hSafeRoof hab hnotPiece
  rintro ⟨y, hy⟩
  exact hno ⟨y, (K.piece i).forwardEdges_subset_original hy⟩

end ClassifiedContactChain

namespace ClassifiedContactSegmentation

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {Q : AltPath Gamma.graph} {persistent : Set V}

/-- The literal bracket fact needed for endpoint-specific boundary
accounting.  Infinite tails create no shortcut, so only finite pieces occur
in this predicate. -/
def FinitePiecesBackwardLinksOn
    (S : ClassifiedContactSegmentation
      (Y := C.selectedReference) (kappa := kappa) Q X persistent) : Prop :=
  match S with
  | .finite T => ∀ i, BackwardLinksOn C.selectedReference (T.piece i).path
  | .eventually T =>
      ∀ i, BackwardLinksOn C.selectedReference (T.piece i).path
  | .omega T => ∀ i, BackwardLinksOn C.selectedReference (T.piece i).path

theorem omittedShortcut_head_mem_limitWarp_of_noIncomingOriginalForward
    (S : ClassifiedContactSegmentation
      (Y := C.selectedReference) (kappa := kappa) Q X persistent)
    (hback : S.FinitePiecesBackwardLinksOn)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    {a b : V} (hab : (a, b) ∈ S.shortcutEdges)
    (hnot : (a, b) ∉ S.limitingShortcutEdges hSafeRoof)
    (hno : ¬ ∃ x, (x, b) ∈ Q.directionEdges .forward) :
    b ∈ Gamma.vertexSet C.ladder.limitWarp := by
  cases S with
  | finite T =>
      exact T.toChain.omittedShortcut_head_mem_limitWarp_of_noIncomingOriginalForward
        hback hSafeRoof hab hnot hno
  | eventually T =>
      exact T.toChain.omittedShortcut_head_mem_limitWarp_of_noIncomingOriginalForward
        hback hSafeRoof hab hnot hno
  | omega T =>
      exact T.toChain.omittedShortcut_head_mem_limitWarp_of_noIncomingOriginalForward
        hback hSafeRoof hab hnot hno

theorem omittedShortcut_tail_mem_limitWarp_of_noOutgoingOriginalForward
    (S : ClassifiedContactSegmentation
      (Y := C.selectedReference) (kappa := kappa) Q X persistent)
    (hback : S.FinitePiecesBackwardLinksOn)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    {a b : V} (hab : (a, b) ∈ S.shortcutEdges)
    (hnot : (a, b) ∉ S.limitingShortcutEdges hSafeRoof)
    (hno : ¬ ∃ y, (a, y) ∈ Q.directionEdges .forward) :
    a ∈ Gamma.vertexSet C.ladder.limitWarp := by
  cases S with
  | finite T =>
      exact T.toChain.omittedShortcut_tail_mem_limitWarp_of_noOutgoingOriginalForward
        hback hSafeRoof hab hnot hno
  | eventually T =>
      exact T.toChain.omittedShortcut_tail_mem_limitWarp_of_noOutgoingOriginalForward
        hback hSafeRoof hab hnot hno
  | omega T =>
      exact T.toChain.omittedShortcut_tail_mem_limitWarp_of_noOutgoingOriginalForward
        hback hSafeRoof hab hnot hno

end ClassifiedContactSegmentation

namespace GroupedClassifiedContactSegmentedAssignment

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {Z : Set Gamma.DPath}
variable {A : SimultaneousAssignment Z C.selectedReference}
variable {persistent : Set V} {G : Type v}

theorem omittedShortcut_head_mem_limitWarp_of_noIncomingAssignedForward
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hback : ∀ s, (S.segmentation s).FinitePiecesBackwardLinksOn)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    {a b : V} (hab : (a, b) ∈ S.edge)
    (hnot : (a, b) ∉ S.limitingShortcutEdges hSafeRoof)
    (hno : ¬ ∃ x, (x, b) ∈ S.assignedForwardEdges) :
    b ∈ Gamma.vertexSet C.ladder.limitWarp := by
  simp only [edge, Set.mem_iUnion] at hab
  obtain ⟨s, hab⟩ := hab
  have hnotS : (a, b) ∉
      (S.segmentation s).limitingShortcutEdges hSafeRoof := by
    intro h
    apply hnot
    exact Set.mem_iUnion.2 ⟨s, h⟩
  apply (S.segmentation s)
    |>.omittedShortcut_head_mem_limitWarp_of_noIncomingOriginalForward
      (hback s) hSafeRoof hab hnotS
  rintro ⟨x, hx⟩
  apply hno
  exact ⟨x, Set.mem_iUnion.2 ⟨s, hx⟩⟩

theorem omittedShortcut_tail_mem_limitWarp_of_noOutgoingAssignedForward
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hback : ∀ s, (S.segmentation s).FinitePiecesBackwardLinksOn)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    {a b : V} (hab : (a, b) ∈ S.edge)
    (hnot : (a, b) ∉ S.limitingShortcutEdges hSafeRoof)
    (hno : ¬ ∃ y, (a, y) ∈ S.assignedForwardEdges) :
    a ∈ Gamma.vertexSet C.ladder.limitWarp := by
  simp only [edge, Set.mem_iUnion] at hab
  obtain ⟨s, hab⟩ := hab
  have hnotS : (a, b) ∉
      (S.segmentation s).limitingShortcutEdges hSafeRoof := by
    intro h
    apply hnot
    exact Set.mem_iUnion.2 ⟨s, h⟩
  apply (S.segmentation s)
    |>.omittedShortcut_tail_mem_limitWarp_of_noOutgoingOriginalForward
      (hback s) hSafeRoof hab hnotS
  rintro ⟨y, hy⟩
  apply hno
  exact ⟨y, Set.mem_iUnion.2 ⟨s, hy⟩⟩

/-- Exact useful root accounting once the concrete bracket producer retains
its backward-link certificates.  A genuinely new root lies on the limiting
reference, rather than merely being adjacent to a covered endpoint. -/
theorem limitingRoots_subset_localRoots_union_limitWarp
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hback : ∀ s, (S.segmentation s).FinitePiecesBackwardLinksOn)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (carrier : Set V) :
    {x | x ∈ carrier ∧ ¬ ∃ y, (y, x) ∈ S.limitingEdge hSafeRoof} ⊆
      {x | x ∈ carrier ∧ ¬ ∃ y, (y, x) ∈ S.localEdge} ∪
      (carrier ∩ Gamma.vertexSet C.ladder.limitWarp) := by
  intro x hx
  by_cases hold : ∃ y, (y, x) ∈ S.localEdge
  · right
    obtain ⟨y, hyx⟩ := hold
    rcases hyx with hyx | hyx
    · exact False.elim (hx.2 ⟨y, Or.inl hyx⟩)
    · have hnot : (y, x) ∉ S.limitingShortcutEdges hSafeRoof := by
        intro h
        exact hx.2 ⟨y, Or.inr h⟩
      have hnoForward : ¬ ∃ z, (z, x) ∈ S.assignedForwardEdges := by
        rintro ⟨z, hzx⟩
        exact hx.2 ⟨z, Or.inl hzx⟩
      exact ⟨hx.1,
        S.omittedShortcut_head_mem_limitWarp_of_noIncomingAssignedForward
          hback hSafeRoof hyx hnot hnoForward⟩
  · exact Or.inl ⟨hx.1, hold⟩

/-- Sink counterpart of
`limitingRoots_subset_localRoots_union_limitWarp`. -/
theorem limitingSinks_subset_localSinks_union_limitWarp
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hback : ∀ s, (S.segmentation s).FinitePiecesBackwardLinksOn)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (carrier : Set V) :
    {x | x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ S.limitingEdge hSafeRoof} ⊆
      {x | x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ S.localEdge} ∪
      (carrier ∩ Gamma.vertexSet C.ladder.limitWarp) := by
  intro x hx
  by_cases hold : ∃ y, (x, y) ∈ S.localEdge
  · right
    obtain ⟨y, hxy⟩ := hold
    rcases hxy with hxy | hxy
    · exact False.elim (hx.2 ⟨y, Or.inl hxy⟩)
    · have hnot : (x, y) ∉ S.limitingShortcutEdges hSafeRoof := by
        intro h
        exact hx.2 ⟨y, Or.inr h⟩
      have hnoForward : ¬ ∃ z, (x, z) ∈ S.assignedForwardEdges := by
        rintro ⟨z, hxz⟩
        exact hx.2 ⟨z, Or.inl hxz⟩
      exact ⟨hx.1,
        S.omittedShortcut_tail_mem_limitWarp_of_noOutgoingAssignedForward
          hback hSafeRoof hxy hnot hnoForward⟩
  · exact Or.inl ⟨hx.1, hold⟩

/-- The root accounting is stable under adjoining the same already-realized
inside relation to both the local and globally reclassified contact
relations.  This is the form used by a literal cut-splice successor. -/
theorem union_limitingRoots_subset_union_localRoots_union_limitWarp
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hback : ∀ s, (S.segmentation s).FinitePiecesBackwardLinksOn)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (inside : Set (V × V)) (carrier : Set V) :
    {x | x ∈ carrier ∧
      ¬ ∃ y, (y, x) ∈ inside ∪ S.limitingEdge hSafeRoof} ⊆
      {x | x ∈ carrier ∧ ¬ ∃ y, (y, x) ∈ inside ∪ S.localEdge} ∪
      (carrier ∩ Gamma.vertexSet C.ladder.limitWarp) := by
  intro x hx
  have hxLimiting :
      x ∈ {x | x ∈ carrier ∧
        ¬ ∃ y, (y, x) ∈ S.limitingEdge hSafeRoof} := by
    refine ⟨hx.1, ?_⟩
    rintro ⟨y, hyx⟩
    exact hx.2 ⟨y, Or.inr hyx⟩
  rcases S.limitingRoots_subset_localRoots_union_limitWarp
      hback hSafeRoof carrier hxLimiting with hlocal | href
  · apply Or.inl
    refine ⟨hlocal.1, ?_⟩
    rintro ⟨y, hyx⟩
    rcases hyx with hyx | hyx
    · exact hx.2 ⟨y, Or.inl hyx⟩
    · exact hlocal.2 ⟨y, hyx⟩
  · exact Or.inr href

/-- Sink counterpart of
`union_limitingRoots_subset_union_localRoots_union_limitWarp`. -/
theorem union_limitingSinks_subset_union_localSinks_union_limitWarp
    (S : GroupedClassifiedContactSegmentedAssignment
      (kappa := kappa) A X persistent G)
    (hback : ∀ s, (S.segmentation s).FinitePiecesBackwardLinksOn)
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (inside : Set (V × V)) (carrier : Set V) :
    {x | x ∈ carrier ∧
      ¬ ∃ y, (x, y) ∈ inside ∪ S.limitingEdge hSafeRoof} ⊆
      {x | x ∈ carrier ∧ ¬ ∃ y, (x, y) ∈ inside ∪ S.localEdge} ∪
      (carrier ∩ Gamma.vertexSet C.ladder.limitWarp) := by
  intro x hx
  have hxLimiting :
      x ∈ {x | x ∈ carrier ∧
        ¬ ∃ y, (x, y) ∈ S.limitingEdge hSafeRoof} := by
    refine ⟨hx.1, ?_⟩
    rintro ⟨y, hxy⟩
    exact hx.2 ⟨y, Or.inr hxy⟩
  rcases S.limitingSinks_subset_localSinks_union_limitWarp
      hback hSafeRoof carrier hxLimiting with hlocal | href
  · apply Or.inl
    refine ⟨hlocal.1, ?_⟩
    rintro ⟨y, hxy⟩
    rcases hxy with hxy | hxy
    · exact hx.2 ⟨y, Or.inl hxy⟩
    · exact hlocal.2 ⟨y, hxy⟩
  · exact Or.inr href

end GroupedClassifiedContactSegmentedAssignment

#print axioms ClassifiedFiniteContactPiece.terminal_mem_limitWarp_of_omittedShortcut_of_noIncoming
#print axioms ClassifiedFiniteContactPiece.initial_mem_limitWarp_of_omittedShortcut_of_noOutgoing
#print axioms GroupedClassifiedContactSegmentedAssignment.limitingRoots_subset_localRoots_union_limitWarp
#print axioms GroupedClassifiedContactSegmentedAssignment.limitingSinks_subset_localSinks_union_limitWarp
#print axioms GroupedClassifiedContactSegmentedAssignment.union_limitingRoots_subset_union_localRoots_union_limitWarp
#print axioms GroupedClassifiedContactSegmentedAssignment.union_limitingSinks_subset_union_localSinks_union_limitWarp

end Erdos599.Blueprint.LinkageBlueprint
