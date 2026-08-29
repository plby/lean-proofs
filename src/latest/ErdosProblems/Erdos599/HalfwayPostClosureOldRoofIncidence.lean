/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureActualSegmentation
import ErdosProblems.Erdos599.HalfwayOldStageSourceDiamond

/-!
# Old-roof incidence of the actual post-closure transaction

Every literal forward edge retained from the post-closure assignment is an
edge of the captured old-to-new interval row.  Such an edge cannot enter the
old roof.  At a finite compressor contact the same assertion holds even when
the preceding traversal coordinate might a priori have been backward:
backward links avoid the closed set, while the contact belongs to it, so the
preceding coordinate is forward.

These are occurrence-level facts.  They do not assume a grouping of contact
pieces and therefore remain available to the eventual occurrence-indexed
aggregation used by Assertion 9.31.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

namespace Alternating.RunCompressor.FiniteInput

open DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

/-- If the head, rather than the tail, of a raw traversal coordinate belongs
to a set avoided by all backward links, that coordinate is forward. -/
theorem colour_eq_forward_of_next_vertex_mem
    (S : FiniteInput D) (X : Set V)
    (hbackwardOff : ∀ l ∈ (AltPath.finite
        S.toFiniteRunWalk.toFiniteTrace).links,
      l.direction = .backward → Disjoint l.path.support X)
    (k : Fin S.lastEdge) (hkX : S.vertex (k.1 + 1) ∈ X) :
    S.colour k = .forward := by
  cases hcolour : S.colour k with
  | forward => rfl
  | backward =>
      have hraw := S.rawEdge_mem_directionEdges k
      rw [hcolour] at hraw
      simp only [AltPath.directionEdges, Set.mem_iUnion] at hraw
      obtain ⟨l, hl, hdir, he⟩ := hraw
      have hkSupport : S.vertex (k.1 + 1) ∈ l.path.support := by
        have hend := (l.path.edgeSet_subset_support_prod he).1
        simpa only [rawEdge, hcolour] using hend
      exact False.elim
        (Set.disjoint_left.1 (hbackwardOff l hl hdir) hkSupport hkX)

end Alternating.RunCompressor.FiniteInput

namespace Alternating.RunCompressor.InfiniteInput

open DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

/-- Infinite-compressor counterpart of
`FiniteInput.colour_eq_forward_of_next_vertex_mem`. -/
theorem colour_eq_forward_of_next_vertex_mem
    (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (X : Set V)
    (hbackwardOff : ∀ l ∈ (AltPath.infinite
        (S.toInfiniteRunWalk hchange).toInfiniteTrace).links,
      l.direction = .backward → Disjoint l.path.support X)
    (n : Nat) (hnX : S.vertex (n + 1) ∈ X) :
    S.colour n = .forward := by
  cases hcolour : S.colour n with
  | forward => rfl
  | backward =>
      have hraw := S.rawEdge_mem_directionEdges hchange n
      rw [hcolour] at hraw
      simp only [AltPath.directionEdges, Set.mem_iUnion] at hraw
      obtain ⟨l, hl, hdir, he⟩ := hraw
      have hnSupport : S.vertex (n + 1) ∈ l.path.support := by
        have hend := (l.path.edgeSet_subset_support_prod he).1
        simpa only [rawEdge, hcolour] using hend
      exact False.elim
        (Set.disjoint_left.1 (hbackwardOff l hl hdir) hnSupport hnX)

end Alternating.RunCompressor.InfiniteInput

namespace Blueprint.LinkageBlueprint

open DirectedPath Ladder
open _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

namespace ClosedClassifiedContactSegmentation

/-- The head of a shortcut is never the initial contact.  This follows from
the strict successor index in each of the finite, eventual, and omega
contact-chain shapes, independently of how the pieces were classified. -/
theorem shortcut_head_ne_initial
    {X persistent : Set V} {Q : AltPath Gamma.graph}
    (S : ClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X persistent)
    {x y : V} (hxy : (x, y) ∈ S.shortcutEdges) :
    y ≠ Q.initial := by
  cases S with
  | finite D =>
      obtain ⟨i, hpair⟩ := D.toChain.mem_shortcutEdges_eq hxy
      have hy : y = D.point i.succ := congrArg Prod.snd hpair
      intro hyInitial
      have hpoints : D.point i.succ =
          D.point ⟨0, Nat.zero_lt_succ _⟩ :=
        hy.symm.trans (hyInitial.trans D.initial_eq.symm)
      have hindices := D.point_injective hpoints
      have hvals := congrArg Fin.val hindices
      simp at hvals
  | eventually D =>
      obtain ⟨i, hpair⟩ := D.toChain.mem_shortcutEdges_eq hxy
      have hy : y = D.point i.succ := congrArg Prod.snd hpair
      intro hyInitial
      have hpoints : D.point i.succ =
          D.point ⟨0, Nat.zero_lt_succ _⟩ :=
        hy.symm.trans (hyInitial.trans D.initial_eq.symm)
      have hindices := D.point_injective hpoints
      have hvals := congrArg Fin.val hindices
      simp at hvals
  | omega D =>
      obtain ⟨i, hpair⟩ := D.toChain.mem_shortcutEdges_eq hxy
      have hy : y = D.point (i + 1) := by
        have hy' := congrArg Prod.snd hpair
        change y = D.point (Nat.succ i) at hy'
        simpa only [Nat.succ_eq_add_one] using hy'
      intro hyInitial
      have hpoints : D.point (i + 1) = D.point 0 :=
        hy.symm.trans (hyInitial.trans D.initial_eq.symm)
      have hindices := D.point_injective hpoints
      omega

end ClosedClassifiedContactSegmentation

namespace PostClosureIntervalTransaction

/-- No edge of the actual captured interval row enters the roof of its old
frontier.  A row vertex in that roof is an old-frontier initial, and a warp
has no family edge entering one of its initials. -/
theorem intervalFamilyEdge_head_not_mem_currentRoof
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure)
    {x y : V} (hxy : (x, y) ∈ familyEdges T.interval.ambientInterval) :
    y ∉ Gamma.roof C.newSlice := by
  intro hyRoof
  have hyVertex : y ∈ Gamma.vertexSet T.interval.ambientInterval := by
    simp only [familyEdges, Set.mem_iUnion] at hxy
    obtain ⟨p, hp, hxyp⟩ := hxy
    exact ⟨p, hp, (p.edgeSet_subset_support_prod hxyp).2⟩
  have hyOldSlice : y ∈ Rlimit.capturedGeometry.oldSlice := by
    rw [← T.interval.ambientInterval_vertexSet_inter_oldRoof]
    exact ⟨hyVertex, by
      simpa only [DynamicMoving931GlobalClosure.capturedGeometry_oldSlice]
        using hyRoof⟩
  have hyInitial : y ∈ Gamma.initialSet T.interval.ambientInterval := by
    rw [T.interval.ambientInterval_linkage.initialSet_eq]
    exact hyOldSlice
  exact isWarp_noIncoming_familyEdges_of_mem_initialSet
    T.interval.ambientInterval_linkage.isWarp hyInitial ⟨x, hxy⟩

end PostClosureIntervalTransaction

namespace PostClosureProducedAssignment

/-- Every literal forward edge of an actual assigned route has its head
outside the old roof. -/
theorem assigned_forwardEdge_head_not_mem_currentRoof
    (A : PostClosureProducedAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    {x y : V}
    (hxy : (x, y) ∈
      (A.assignment.produced.bracket.assignment.assigned s).directionEdges
        .forward) :
    y ∉ Gamma.roof C.newSlice := by
  simp only [AltPath.directionEdges, Set.mem_iUnion] at hxy
  obtain ⟨l, hl, hdir, hxyl⟩ := hxy
  apply T.intervalFamilyEdge_head_not_mem_currentRoof
  exact A.assigned_forwardLink_edges_subset_intervalFamily s l hl hdir hxyl

end PostClosureProducedAssignment

namespace PostClosureCompressorAssignment

/-- The raw edge immediately preceding a closed-set vertex of an actual
finite compressed assignment is a literal forward edge of the interval
row. -/
theorem finite_incomingRawEdge_mem_intervalFamily
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    (S : RunCompressor.FiniteInput Gamma.graph)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .finite S.toFiniteRunWalk.toFiniteTrace)
    (k : Fin S.lastEdge)
    (hkX : S.vertex (k.1 + 1) ∈ Rlimit.closedSet) :
    (S.vertex k.1, S.vertex (k.1 + 1)) ∈
      familyEdges T.interval.ambientInterval := by
  have hbackwardOff : ∀ l ∈ (AltPath.finite
      S.toFiniteRunWalk.toFiniteTrace).links,
      l.direction = .backward → Disjoint l.path.support Rlimit.closedSet := by
    intro l hl hdir
    apply A.toPostClosureProducedAssignment.assigned_backwardLink_disjoint_closedSet
      s l
    · rw [hS]
      exact hl
    · exact hdir
  have hcolour : S.colour k = .forward :=
    S.colour_eq_forward_of_next_vertex_mem Rlimit.closedSet hbackwardOff k hkX
  have hraw := S.rawEdge_mem_directionEdges k
  rw [hcolour] at hraw
  simp only [AltPath.directionEdges, Set.mem_iUnion] at hraw
  obtain ⟨l, hl, hdir, he⟩ := hraw
  have hrow := A.toPostClosureProducedAssignment
    |>.assigned_forwardLink_edges_subset_intervalFamily s l
      (by rw [hS]; exact hl) hdir he
  simpa only [RunCompressor.FiniteInput.rawEdge, hcolour] using hrow

/-- Every noninitial finite break point has a literal incoming interval-row
edge, provided that break point belongs to the closing set. -/
theorem finite_breakPoint_hasIncoming_intervalFamily
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    (S : RunCompressor.FiniteInput Gamma.graph)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .finite S.toFiniteRunWalk.toFiniteTrace)
    (i : Fin (S.finiteWalk.breakCount Rlimit.closedSet))
    (hvX : S.finiteWalk.breakPoint Rlimit.closedSet i.succ ∈
      Rlimit.closedSet) :
    ∃ x, (x, S.finiteWalk.breakPoint Rlimit.closedSet i.succ) ∈
      familyEdges T.interval.ambientInterval := by
  let b := S.finiteWalk.breakPosition Rlimit.closedSet i.succ
  have hab := S.breakPosition_lt_succ Rlimit.closedSet i
  have hbpos : 0 < b := by
    dsimp [b]
    omega
  have hble : b ≤ S.lastEdge := by
    dsimp [b]
    rw [← S.finiteWalk_finalPosition]
    exact S.finiteWalk.breakPosition_le_final Rlimit.closedSet i.succ
  let k : Fin S.lastEdge := ⟨b - 1, by omega⟩
  have hkb : k.1 + 1 = b := by
    dsimp [k]
    omega
  dsimp [b] at hkb
  have hkX : S.vertex (k.1 + 1) ∈ Rlimit.closedSet := by
    rw [hkb]
    exact hvX
  refine ⟨S.vertex k.1, ?_⟩
  have hedge := A.finite_incomingRawEdge_mem_intervalFamily s S hS k hkX
  change (S.vertex k.1,
    S.vertex (S.finiteWalk.breakPosition Rlimit.closedSet i.succ)) ∈
      familyEdges T.interval.ambientInterval
  rw [← hkb]
  exact hedge

/-- Consequently every target of a finite contact interval lies outside the
old roof.  This is the shortcut-head incidence fact needed by the concrete
9.31 relation assembler. -/
theorem finite_breakPoint_target_not_mem_currentRoof
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    (S : RunCompressor.FiniteInput Gamma.graph)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .finite S.toFiniteRunWalk.toFiniteTrace)
    (i : Fin (S.finiteWalk.breakCount Rlimit.closedSet))
    (hvX : S.finiteWalk.breakPoint Rlimit.closedSet i.succ ∈
      Rlimit.closedSet) :
    S.finiteWalk.breakPoint Rlimit.closedSet i.succ ∉
      Gamma.roof C.newSlice := by
  obtain ⟨x, hx⟩ :=
    A.finite_breakPoint_hasIncoming_intervalFamily s S hS i hvX
  exact T.intervalFamilyEdge_head_not_mem_currentRoof hx

/-- Coordinate-free finite form.  Every noninitial vertex of the actual
assigned trace which belongs to the closing set has a preceding raw
coordinate; that coordinate is forward and therefore prevents the vertex
from lying in the old roof. -/
theorem finite_vertex_not_mem_currentRoof_of_mem_closedSet_of_ne_initial
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    (S : RunCompressor.FiniteInput Gamma.graph)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .finite S.toFiniteRunWalk.toFiniteTrace)
    {x : V}
    (hxTrace : x ∈
      (AltPath.finite S.toFiniteRunWalk.toFiniteTrace).vertexSet)
    (hxX : x ∈ Rlimit.closedSet)
    (hxInitial : x ≠
      (AltPath.finite S.toFiniteRunWalk.toFiniteTrace).initial) :
    x ∉ Gamma.roof C.newSlice := by
  let n := S.toFiniteRunWalk.vertexPosition x hxTrace
  have hnle : n ≤ S.lastEdge := by
    have hnle' := S.toFiniteRunWalk.vertexPosition_le_final x hxTrace
    rw [S.finiteWalk_finalPosition] at hnle'
    exact hnle'
  have hvn : S.vertex n = x := by
    exact S.toFiniteRunWalk.vertex_vertexPosition x hxTrace
  have hnpos : 0 < n := by
    by_contra hnpos
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnpos
    apply hxInitial
    calc
      x = S.vertex n := hvn.symm
      _ = S.vertex 0 := congrArg S.vertex hnzero
      _ = (AltPath.finite
          S.toFiniteRunWalk.toFiniteTrace).initial :=
        S.toFiniteRunWalk.toFiniteTrace_initial.symm
  let k : Fin S.lastEdge := ⟨n - 1, by omega⟩
  have hkn : k.1 + 1 = n := by
    dsimp [k]
    omega
  have hkX : S.vertex (k.1 + 1) ∈ Rlimit.closedSet := by
    rw [hkn, hvn]
    exact hxX
  have hedge := A.finite_incomingRawEdge_mem_intervalFamily s S hS k hkX
  apply T.intervalFamilyEdge_head_not_mem_currentRoof
  simpa only [hkn, hvn] using hedge

/-- Any shortcut contributed by a mixed piece whose endpoints are the
actual consecutive finite break points has its head outside the old roof.
No equation identifying the piece's internal path is needed: shortcut
membership already identifies its endpoint pair. -/
theorem finite_contactPiece_shortcut_head_not_mem_currentRoof
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    (S : RunCompressor.FiniteInput Gamma.graph)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .finite S.toFiniteRunWalk.toFiniteTrace)
    (i : Fin (S.finiteWalk.breakCount Rlimit.closedSet))
    (hvX : S.finiteWalk.breakPoint Rlimit.closedSet i.succ ∈
      Rlimit.closedSet)
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := C.ladder.limitWarp) (kappa := kappa)
      (.finite S.toFiniteRunWalk.toFiniteTrace) Rlimit.closedSet
      (S.finiteWalk.breakPoint Rlimit.closedSet i.castSucc)
      (S.finiteWalk.breakPoint Rlimit.closedSet i.succ))
    {x y : V} (hxy : (x, y) ∈ P.shortcutEdges) :
    y ∉ Gamma.roof C.newSlice := by
  have hpair := P.mem_shortcutEdges_eq hxy
  have hy : y = S.finiteWalk.breakPoint Rlimit.closedSet i.succ :=
    congrArg Prod.snd hpair
  rw [hy]
  exact A.finite_breakPoint_target_not_mem_currentRoof s S hS i hvX

/-- Infinite-compressor counterpart: a raw coordinate whose next vertex is
closed is a literal forward interval-row edge. -/
theorem infinite_incomingRawEdge_mem_intervalFamily
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
    (n : Nat) (hnX : S.vertex (n + 1) ∈ Rlimit.closedSet) :
    (S.vertex n, S.vertex (n + 1)) ∈
      familyEdges T.interval.ambientInterval := by
  have hbackwardOff : ∀ l ∈ (AltPath.infinite
      (S.toInfiniteRunWalk hchange).toInfiniteTrace).links,
      l.direction = .backward → Disjoint l.path.support Rlimit.closedSet := by
    intro l hl hdir
    apply A.toPostClosureProducedAssignment.assigned_backwardLink_disjoint_closedSet
      s l
    · rw [hS]
      exact hl
    · exact hdir
  have hcolour : S.colour n = .forward :=
    S.colour_eq_forward_of_next_vertex_mem hchange Rlimit.closedSet
      hbackwardOff n hnX
  have hraw := S.rawEdge_mem_directionEdges hchange n
  rw [hcolour] at hraw
  simp only [AltPath.directionEdges, Set.mem_iUnion] at hraw
  obtain ⟨l, hl, hdir, he⟩ := hraw
  have hrow := A.toPostClosureProducedAssignment
    |>.assigned_forwardLink_edges_subset_intervalFamily s l
      (by rw [hS]; exact hl) hdir he
  simpa only [RunCompressor.InfiniteInput.rawEdge, hcolour] using hrow

/-- The target of every bounded contact interval in an actual infinite
compressor lies outside the old roof. -/
theorem infinite_contact_target_not_mem_currentRoof
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
    (a b : Nat) (hab : a < b)
    (hbX : S.vertex b ∈ Rlimit.closedSet) :
    S.vertex b ∉ Gamma.roof C.newSlice := by
  let n := b - 1
  have hnb : n + 1 = b := by
    dsimp [n]
    omega
  have hnX : S.vertex (n + 1) ∈ Rlimit.closedSet := by
    rw [hnb]
    exact hbX
  have hedge := A.infinite_incomingRawEdge_mem_intervalFamily
    s S hchange hS n hnX
  exact T.intervalFamilyEdge_head_not_mem_currentRoof (by
    simpa only [hnb] using hedge)

/-- Coordinate-free infinite form of the preceding old-roof exclusion. -/
theorem infinite_vertex_not_mem_currentRoof_of_mem_closedSet_of_ne_initial
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
    {x : V}
    (hxTrace : x ∈ (AltPath.infinite
      (S.toInfiniteRunWalk hchange).toInfiniteTrace).vertexSet)
    (hxX : x ∈ Rlimit.closedSet)
    (hxInitial : x ≠ (AltPath.infinite
      (S.toInfiniteRunWalk hchange).toInfiniteTrace).initial) :
    x ∉ Gamma.roof C.newSlice := by
  change x ∈ (S.toInfiniteRunWalk hchange).toInfiniteTrace.vertexSet at hxTrace
  rw [S.toInfiniteTrace_vertexSet hchange] at hxTrace
  obtain ⟨n, rfl⟩ := hxTrace
  have hnpos : 0 < n := by
    by_contra hnpos
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnpos
    apply hxInitial
    rw [hnzero]
    exact (S.toInfiniteRunWalk hchange).toInfiniteTrace_initial.symm
  let k := n - 1
  have hkn : k + 1 = n := by
    dsimp [k]
    omega
  have hkX : S.vertex (k + 1) ∈ Rlimit.closedSet := by
    rw [hkn]
    exact hxX
  have hedge := A.infinite_incomingRawEdge_mem_intervalFamily
    s S hchange hS k hkX
  apply T.intervalFamilyEdge_head_not_mem_currentRoof
  simpa only [hkn] using hedge

/-- Branch-independent actual-assignment form.  The only data an aggregate
contact segmentation must retain are that its target is a closed vertex and
is not the first contact. -/
theorem assigned_vertex_not_mem_currentRoof_of_mem_closedSet_of_ne_initial
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    {x : V}
    (hxTrace : x ∈
      (A.assignment.produced.bracket.assignment.assigned s).vertexSet)
    (hxX : x ∈ Rlimit.closedSet)
    (hxInitial : x ≠
      (A.assignment.produced.bracket.assignment.assigned s).initial) :
    x ∉ Gamma.roof C.newSlice := by
  cases A.compressor s with
  | trivial w hQ =>
      have hxw : x = w := by
        rw [hQ] at hxTrace
        simpa [AltPath.vertexSet] using hxTrace
      exact False.elim (hxInitial (by rw [hQ, hxw]; rfl))
  | finite S hQ =>
      apply A.finite_vertex_not_mem_currentRoof_of_mem_closedSet_of_ne_initial
        s S hQ
      · rwa [← hQ]
      · exact hxX
      · rwa [← hQ]

  | infinite S hchange hQ =>
      apply A.infinite_vertex_not_mem_currentRoof_of_mem_closedSet_of_ne_initial
        s S hchange hQ
      · rwa [← hQ]
      · exact hxX
      · rwa [← hQ]

/-- A complete contact segmentation with its actual contact-closedness
certificate contributes no shortcut whose head lies in the old roof. -/
theorem segmentation_shortcut_head_not_mem_currentRoof
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    (S : ClosedClassifiedContactSegmentation
      (Y := C.ladder.limitWarp) (kappa := kappa)
      (A.assignment.produced.bracket.assignment.assigned s)
      Rlimit.closedSet C.persistent)
    (hcontacts : S.contactSet ⊆ Rlimit.closedSet)
    {x y : V} (hxy : (x, y) ∈ S.shortcutEdges) :
    y ∉ Gamma.roof C.newSlice := by
  apply A.assigned_vertex_not_mem_currentRoof_of_mem_closedSet_of_ne_initial s
  · exact S.contactSet_subset_vertexSet (S.endpoints_mem_contactSet hxy).2
  · exact hcontacts (S.endpoints_mem_contactSet hxy).2
  · exact S.shortcut_head_ne_initial hxy

/-- The complete retained relation of one actual segmented route has no
edge entering the old roof.  Literal retained edges use the forward-row
incidence theorem; compressed edges use the preceding shortcut theorem. -/
theorem segmentation_retainedEdge_head_not_mem_currentRoof
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    (S : ClosedClassifiedContactSegmentation
      (Y := C.ladder.limitWarp) (kappa := kappa)
      (A.assignment.produced.bracket.assignment.assigned s)
      Rlimit.closedSet C.persistent)
    (hcontacts : S.contactSet ⊆ Rlimit.closedSet)
    {x y : V} (hxy : (x, y) ∈ S.retainedEdges) :
    y ∉ Gamma.roof C.newSlice := by
  rcases S.retainedEdges_subset_originalForward_union_shortcut hxy with
      hforward | hshortcut
  · exact A.toPostClosureProducedAssignment
      |>.assigned_forwardEdge_head_not_mem_currentRoof s hforward
  · exact A.segmentation_shortcut_head_not_mem_currentRoof
      s S hcontacts hshortcut

/-- Unconditional specialization to the canonical actual segmentation
chosen by the post-closure compiler. -/
theorem actualSegmentation_retainedEdge_head_not_mem_currentRoof
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    {x y : V}
    (hxy : (x, y) ∈
      (A.actualClosedClassifiedContactSegmentation s).retainedEdges) :
    y ∉ Gamma.roof C.newSlice := by
  exact A.segmentation_retainedEdge_head_not_mem_currentRoof s
    (A.actualClosedClassifiedContactSegmentation s)
    (A.actualClosedClassifiedContactSegmentation_contactSet_subset s) hxy

/-- The complete outside relation retained by the actual post-closure
compiler, before any cross-source grouping or orientation is imposed.  This
is an occurrence-indexed union: distinct fractured sources are not silently
identified. -/
def actualSegmentedRetainedEdges
    (A : PostClosureCompressorAssignment T) : Set (V × V) :=
  ⋃ s, (A.actualClosedClassifiedContactSegmentation s).retainedEdges

/-- No edge in the occurrence-indexed union of actual retained outside
relations enters the old roof. -/
theorem actualSegmentedRetainedEdge_head_not_mem_currentRoof
    (A : PostClosureCompressorAssignment T)
    {x y : V} (hxy : (x, y) ∈ A.actualSegmentedRetainedEdges) :
    y ∉ Gamma.roof C.newSlice := by
  simp only [actualSegmentedRetainedEdges, Set.mem_iUnion] at hxy
  obtain ⟨s, hxy⟩ := hxy
  exact A.actualSegmentation_retainedEdge_head_not_mem_currentRoof s hxy

/-- Every occurrence-indexed retained outside edge belongs to the global
imaginary graph.  Literal forward edges use the original graph summand;
shortcuts use their classification certificate. -/
theorem actualSegmentedRetainedEdges_subset_imaginaryGraph
    (A : PostClosureCompressorAssignment T) :
    A.actualSegmentedRetainedEdges ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} := by
  intro e he
  simp only [actualSegmentedRetainedEdges, Set.mem_iUnion] at he
  obtain ⟨s, he⟩ := he
  let S := A.actualClosedClassifiedContactSegmentation s
  rcases S.retainedEdges_subset_originalForward_union_shortcut he with
    hforward | hshortcut
  · simp only [AltPath.directionEdges, Set.mem_iUnion] at hforward
    obtain ⟨l, _hl, _hdir, hel⟩ := hforward
    exact original_adj_imaginaryGraph (l.path.edgeSet_subset_adj hel)
  · exact S.shortcutEdges_subset_imaginaryGraph hshortcut

/-- The literal edge set contributed by the actual post-closure geometry:
the inside restriction `W[X]`, together with every occurrence-indexed
retained outside route.  This is only an edge set; it does not assert the
still-pending cross-source bi-uniqueness or splice boundary fields. -/
def actualPostClosureFreshEdges
    (A : PostClosureCompressorAssignment T) : Set (V × V) :=
  sourceInsideEdges T.interval.ambientInterval Rlimit.closedSet ∪
    A.actualSegmentedRetainedEdges

/-- Every actual inside or retained-outside edge has head outside the old
roof.  The inside branch is a literal interval-row edge, while the outside
branch is the occurrence-indexed theorem above. -/
theorem actualPostClosureFreshEdge_head_not_mem_currentRoof
    (A : PostClosureCompressorAssignment T)
    {x y : V} (hxy : (x, y) ∈ A.actualPostClosureFreshEdges) :
    y ∉ Gamma.roof C.newSlice := by
  rcases hxy with hinside | houtside
  · exact T.intervalFamilyEdge_head_not_mem_currentRoof hinside.1
  · exact A.actualSegmentedRetainedEdge_head_not_mem_currentRoof houtside

/-- The full literal actual post-closure edge set belongs to the global
imaginary graph. -/
theorem actualPostClosureFreshEdges_subset_imaginaryGraph
    (A : PostClosureCompressorAssignment T) :
    A.actualPostClosureFreshEdges ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} := by
  intro e he
  rcases he with hinside | houtside
  · exact original_adj_imaginaryGraph
      (familyEdges_subset_adj T.interval.ambientInterval hinside.1)
  · exact A.actualSegmentedRetainedEdges_subset_imaginaryGraph houtside

/-- Consequently the concrete post-closure fresh relation has no edge
entering the carrier of any current blueprint satisfying the actual old-slice
roof condition. -/
theorem actualPostClosureFreshEdges_noIncoming_current
    (A : PostClosureCompressorAssignment T)
    {currentClosed : Set V}
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent) :
    ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈ A.actualPostClosureFreshEdges → False := by
  intro x y hx hxy
  exact (A.actualPostClosureFreshEdge_head_not_mem_currentRoof hxy)
    (hcurrent.vertices_roofed hx)

/-- Adjoining the concrete fresh edge set to the current edge relation
creates no new predecessor of any current vertex. -/
theorem current_union_actualPostClosureFreshEdges_noNewIncoming
    (A : PostClosureCompressorAssignment T)
    {currentClosed : Set V}
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent) :
    ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈ current.edgeSet ∪ A.actualPostClosureFreshEdges →
        (y, x) ∈ current.edgeSet := by
  intro x y hx hxy
  rcases hxy with hcurrentEdge | hfresh
  · exact hcurrentEdge
  · exact False.elim
      (A.actualPostClosureFreshEdges_noIncoming_current current hcurrent hx hfresh)

/-- In particular, every current initial remains a root after adjoining the
actual post-closure fresh relation. -/
theorem currentInitial_noIncoming_current_union_actualPostClosureFreshEdges
    (A : PostClosureCompressorAssignment T)
    {currentClosed : Set V}
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    {x : V} (hx : x ∈ current.initialSet) :
    ¬ ∃ y, (y, x) ∈ current.edgeSet ∪ A.actualPostClosureFreshEdges := by
  have hxVertex : x ∈ current.vertexSet := by
    obtain ⟨p, hp, hpInitial⟩ := hx
    exact ⟨p, hp, hpInitial.symm ▸ p.initial_mem_support⟩
  have hnoOld : ¬ ∃ y, (y, x) ∈ current.edgeSet :=
    isWarp_noIncoming_familyEdges_of_mem_initialSet current.isWarp hx
  rintro ⟨y, hyx⟩
  exact hnoOld ⟨y,
    A.current_union_actualPostClosureFreshEdges_noNewIncoming
      current hcurrent hxVertex hyx⟩

/-- Shortcut-head form for a bounded actual infinite-compressor contact
piece. -/
theorem infinite_contactPiece_shortcut_head_not_mem_currentRoof
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference
        Rlimit.closedSet)})
    (S : RunCompressor.InfiniteInput Gamma.graph)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (hS : A.assignment.produced.bracket.assignment.assigned s =
      .infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
    (a b : Nat) (hab : a < b)
    (hbX : S.vertex b ∈ Rlimit.closedSet)
    (P : ClassifiedOrClosedFiniteContactPiece
      (Y := C.ladder.limitWarp) (kappa := kappa)
      (.infinite (S.toInfiniteRunWalk hchange).toInfiniteTrace)
      Rlimit.closedSet (S.vertex a) (S.vertex b))
    {x y : V} (hxy : (x, y) ∈ P.shortcutEdges) :
    y ∉ Gamma.roof C.newSlice := by
  have hpair := P.mem_shortcutEdges_eq hxy
  have hy : y = S.vertex b := congrArg Prod.snd hpair
  rw [hy]
  exact A.infinite_contact_target_not_mem_currentRoof
    s S hchange hS a b hab hbX

end PostClosureCompressorAssignment

end Blueprint.LinkageBlueprint
end Erdos599

#print axioms Erdos599.Alternating.RunCompressor.FiniteInput.colour_eq_forward_of_next_vertex_mem
#print axioms Erdos599.Alternating.RunCompressor.InfiniteInput.colour_eq_forward_of_next_vertex_mem
#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureIntervalTransaction.intervalFamilyEdge_head_not_mem_currentRoof
#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureProducedAssignment.assigned_forwardEdge_head_not_mem_currentRoof
#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment.finite_breakPoint_target_not_mem_currentRoof
#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment.infinite_contact_target_not_mem_currentRoof
#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment.actualSegmentedRetainedEdge_head_not_mem_currentRoof
#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment.actualPostClosureFreshEdges_subset_imaginaryGraph
#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment.actualPostClosureFreshEdge_head_not_mem_currentRoof
#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment.actualPostClosureFreshEdges_noIncoming_current
#print axioms Erdos599.Blueprint.LinkageBlueprint.PostClosureCompressorAssignment.currentInitial_noIncoming_current_union_actualPostClosureFreshEdges
