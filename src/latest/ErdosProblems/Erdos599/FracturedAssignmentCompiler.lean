/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedDuplication
import ErdosProblems.Erdos599.SafeAlternatingDichotomy
import ErdosProblems.Erdos599.SimultaneousAssignmentGlobal

/-!
# Compiling fractured assignments in the occurrence-split web

This module completes the normalization reduction for Remark 4.20.  The
fractured family is first made honest by `endpointLiftedPaths`; singleton
members traverse their whole role fibre.  Endpoint purity then lets the
reference warp pass through the same normalization without truncation.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace FracturedDuplication

theorem initialSet_normalizedEndpointLiftedPaths
    (Z : FracturedWarp Gamma)
    (hfinite : Gamma.HasFiniteCharacter Z.paths) :
    (endpointWeb Gamma Z).normalized.initialSet
        (normalizedEndpointLiftedPaths Z) =
      sourceCopy Z '' Gamma.initialSet Z.paths := by
  ext z
  constructor
  · rintro ⟨P, ⟨p, hp, rfl⟩, hP⟩
    refine ⟨p.start, ⟨(.inl p : Gamma.DPath), hp, rfl⟩, ?_⟩
    exact (start_normalizedEndpointLiftFinitePath Z p hp).symm.trans hP
  · rintro ⟨x, ⟨p, hp, hpx⟩, rfl⟩
    rcases hfinite hp with ⟨q, rfl⟩
    refine ⟨(.inl (normalizedEndpointLiftFinitePath Z q hp) :
        (endpointWeb Gamma Z).normalized.DPath), ⟨q, hp, rfl⟩, ?_⟩
    change q.start = x at hpx
    exact (start_normalizedEndpointLiftFinitePath Z q hp).trans
      (congrArg (sourceCopy Z) hpx)

theorem terminalFrontier_normalizedEndpointLiftedPaths
    (Z : FracturedWarp Gamma)
    (hfinite : Gamma.HasFiniteCharacter Z.paths) :
    (endpointWeb Gamma Z).normalized.terminalFrontier
        (normalizedEndpointLiftedPaths Z) =
      terminalCopy Z '' Gamma.terminalFrontier Z.paths := by
  ext z
  constructor
  · rintro ⟨P, ⟨p, hp, rfl⟩, hP⟩
    refine ⟨p.finish, ⟨(.inl p : Gamma.DPath), hp, rfl⟩, ?_⟩
    change some (normalizedEndpointLiftFinitePath Z p hp).finish = some z at hP
    exact (finish_normalizedEndpointLiftFinitePath Z p hp).symm.trans
      (Option.some.inj hP)
  · rintro ⟨x, ⟨p, hp, hpx⟩, rfl⟩
    rcases hfinite hp with ⟨q, rfl⟩
    refine ⟨(.inl (normalizedEndpointLiftFinitePath Z q hp) :
        (endpointWeb Gamma Z).normalized.DPath), ⟨q, hp, rfl⟩, ?_⟩
    change some (normalizedEndpointLiftFinitePath Z q hp).finish =
      some (terminalCopy Z x)
    change some q.finish = some x at hpx
    rw [finish_normalizedEndpointLiftFinitePath, Option.some.inj hpx]

theorem normalizedEndpointLiftedPaths_source
    (Z : FracturedWarp Gamma) :
    (endpointWeb Gamma Z).normalized.initialSet
        (normalizedEndpointLiftedPaths Z) ⊆
      (endpointWeb Gamma Z).normalized.source := by
  rintro z ⟨P, ⟨p, hp, rfl⟩, hinit⟩
  change z ∈ (web Gamma Z).initialSet (endpointLiftedPaths Z)
  refine ⟨(.inl (endpointLiftFinitePath Z p) : (web Gamma Z).DPath),
    endpointLiftFinitePath_mem_endpointLiftedPaths Z hp, ?_⟩
  change (endpointLiftFinitePath Z p).start = z
  change (normalizedEndpointLiftFinitePath Z p hp).start = z at hinit
  simpa only [start_endpointLiftFinitePath,
    start_normalizedEndpointLiftFinitePath] using hinit

theorem normalizedEndpointLiftedPaths_target
    (Z : FracturedWarp Gamma) :
    (endpointWeb Gamma Z).normalized.terminalFrontier
        (normalizedEndpointLiftedPaths Z) ⊆
      (endpointWeb Gamma Z).normalized.target := by
  rintro z ⟨P, ⟨p, hp, rfl⟩, hterm⟩
  change z ∈ (web Gamma Z).terminalFrontier (endpointLiftedPaths Z)
  refine ⟨(.inl (endpointLiftFinitePath Z p) : (web Gamma Z).DPath),
    endpointLiftFinitePath_mem_endpointLiftedPaths Z hp, ?_⟩
  change some (endpointLiftFinitePath Z p).finish = some z
  change some (normalizedEndpointLiftFinitePath Z p hp).finish = some z at hterm
  simpa using hterm

theorem project_mem_support_expandFinitePath (Z : FracturedWarp Gamma)
    (p : FinitePath Gamma.graph) {z : Vertex V}
    (hz : z ∈ (expandFinitePath Z p).support) : project z ∈ p.support := by
  rw [support_expandFinitePath] at hz
  rcases hz with ⟨x, hxp, hzx⟩
  simpa only [mem_vertexBlock_project Z hzx] using hxp

/-- Endpoint purity makes an expanded reference member use only edges of the
normalized endpoint web.  Its support and both endpoints are unchanged. -/
noncomputable def normalizedReferenceFinitePath
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (p : FinitePath Gamma.graph) (hpY : (.inl p : Gamma.DPath) ∈ Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hY : Gamma.IsWarp Y)
    (huncovered : UncoveredSourcesOutsideReference Z Y)
    (hterminal : TerminalContactPure Z Y) :
    FinitePath (endpointWeb Gamma Z).normalized.graph := by
  let q := expandFinitePath Z p
  let hs : ∀ {z}, z ∈ q.walk.support.tail →
      z ∉ (endpointWeb Gamma Z).source := by
    intro z hz hzsource
    rw [endpointWeb, initialSet_endpointLiftedPaths Z hZfinite] at hzsource
    rcases hzsource with ⟨a, haZ, rfl⟩
    have haSupport : a ∈ p.support :=
      project_mem_support_expandFinitePath Z p (List.mem_of_mem_tail hz)
    have haVertex : a ∈ Gamma.vertexSet Y :=
      ⟨(.inl p : Gamma.DPath), hpY, haSupport⟩
    have haInitial : a ∈ Gamma.initialSet Y := by
      by_contra haNotInitial
      exact huncovered ⟨haZ, haNotInitial⟩ haVertex
    have haStart : a = p.start := by
      simpa using finite_support_inter_initialSet_of_isWarp hY hpY
        ⟨haSupport, haInitial⟩
    have hzStart : sourceCopy Z a = q.start := by
      simpa [q, haStart]
    rw [hzStart] at hz
    exact DWeb.walk_start_not_mem_tail2 q.walk q.isPath hz
  let ht : ∀ {z}, z ∈ q.walk.support.dropLast →
      z ∉ (endpointWeb Gamma Z).target := by
    intro z hz hztarget
    rw [endpointWeb, terminalFrontier_endpointLiftedPaths Z hZfinite] at hztarget
    rcases hztarget with ⟨b, hbZ, rfl⟩
    have hbSupport : b ∈ p.support :=
      project_mem_support_expandFinitePath Z p (List.mem_of_mem_dropLast hz)
    have hbVertex : b ∈ Gamma.vertexSet Y :=
      ⟨(.inl p : Gamma.DPath), hpY, hbSupport⟩
    have hbTerminal : b ∈ Gamma.terminalFrontier Y :=
      hterminal ⟨hbZ, hbVertex⟩
    have hbFinish : b = p.finish := by
      simpa using DWeb.IsWarp.finite_support_inter_terminalFrontier
        Gamma hY hpY ⟨hbSupport, hbTerminal⟩
    have hzFinish : terminalCopy Z b = q.finish := by
      simpa [q, hbFinish]
    rw [hzFinish] at hz
    exact DWeb.walk_finish_not_mem_dropLast2 q.walk q.isPath hz
  exact normalizeExactFinitePath (endpointWeb Gamma Z) q hs ht

@[simp] theorem support_normalizedReferenceFinitePath
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (p : FinitePath Gamma.graph) (hpY : (.inl p : Gamma.DPath) ∈ Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hY : Gamma.IsWarp Y)
    (huncovered : UncoveredSourcesOutsideReference Z Y)
    (hterminal : TerminalContactPure Z Y) :
    (normalizedReferenceFinitePath Z p hpY hZfinite hY huncovered hterminal).support =
      (expandFinitePath Z p).support := by
  unfold normalizedReferenceFinitePath
  apply support_normalizeExactFinitePath

@[simp] theorem start_normalizedReferenceFinitePath
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (p : FinitePath Gamma.graph) (hpY : (.inl p : Gamma.DPath) ∈ Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hY : Gamma.IsWarp Y)
    (huncovered : UncoveredSourcesOutsideReference Z Y)
    (hterminal : TerminalContactPure Z Y) :
    (normalizedReferenceFinitePath Z p hpY hZfinite hY huncovered hterminal).start =
      sourceCopy Z p.start := rfl

@[simp] theorem finish_normalizedReferenceFinitePath
    (Z : FracturedWarp Gamma) {Y : Set Gamma.DPath}
    (p : FinitePath Gamma.graph) (hpY : (.inl p : Gamma.DPath) ∈ Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hY : Gamma.IsWarp Y)
    (huncovered : UncoveredSourcesOutsideReference Z Y)
    (hterminal : TerminalContactPure Z Y) :
    (normalizedReferenceFinitePath Z p hpY hZfinite hY huncovered hterminal).finish =
      terminalCopy Z p.finish := rfl

/-- The reference warp transported, without truncation, to the normalized
endpoint split web. -/
noncomputable def normalizedLiftedReference
    (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hY : Gamma.IsWarp Y)
    (huncovered : UncoveredSourcesOutsideReference Z Y)
    (hterminal : TerminalContactPure Z Y) :
    Set (endpointWeb Gamma Z).normalized.DPath :=
  {P | ∃ (p : FinitePath Gamma.graph) (hp : (.inl p : Gamma.DPath) ∈ Y),
      P = .inl (normalizedReferenceFinitePath Z p hp hZfinite hY
        huncovered hterminal)}

theorem normalizedLiftedReference_hasFiniteCharacter
    (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hY : Gamma.IsWarp Y)
    (huncovered : UncoveredSourcesOutsideReference Z Y)
    (hterminal : TerminalContactPure Z Y) :
    (endpointWeb Gamma Z).normalized.HasFiniteCharacter
      (normalizedLiftedReference Z Y hZfinite hY huncovered hterminal) := by
  rintro P ⟨p, hp, rfl⟩
  exact ⟨normalizedReferenceFinitePath Z p hp hZfinite hY
    huncovered hterminal, rfl⟩

theorem normalizedLiftedReference_isWarp
    (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hY : Gamma.IsWarp Y)
    (huncovered : UncoveredSourcesOutsideReference Z Y)
    (hterminal : TerminalContactPure Z Y) :
    (endpointWeb Gamma Z).normalized.IsWarp
      (normalizedLiftedReference Z Y hZfinite hY huncovered hterminal) := by
  rintro P ⟨p, hp, rfl⟩ Q ⟨q, hq, rfl⟩ hPQ
  change Disjoint
    (normalizedReferenceFinitePath Z p hp hZfinite hY
      huncovered hterminal).support
    (normalizedReferenceFinitePath Z q hq hZfinite hY
      huncovered hterminal).support
  rw [support_normalizedReferenceFinitePath,
    support_normalizedReferenceFinitePath]
  apply liftedReference_isWarp Z hY
    (show (.inl (expandFinitePath Z p) : (web Gamma Z).DPath) ∈
      liftedReference Z Y from ⟨p, hp, rfl⟩)
    (show (.inl (expandFinitePath Z q) : (web Gamma Z).DPath) ∈
      liftedReference Z Y from ⟨q, hq, rfl⟩)
  intro heq
  have heq' : expandFinitePath Z p = expandFinitePath Z q := Sum.inl.inj heq
  apply hPQ
  congr 1
  unfold normalizedReferenceFinitePath
  apply normalizeExactFinitePath_congr
  exact heq'

theorem initialSet_normalizedLiftedReference
    (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hY : Gamma.IsWarp Y)
    (huncovered : UncoveredSourcesOutsideReference Z Y)
    (hterminal : TerminalContactPure Z Y) :
    (endpointWeb Gamma Z).normalized.initialSet
        (normalizedLiftedReference Z Y hZfinite hY huncovered hterminal) =
      sourceCopy Z '' Gamma.initialSet Y := by
  ext z
  constructor
  · rintro ⟨P, ⟨p, hp, rfl⟩, hP⟩
    refine ⟨p.start, ⟨(.inl p : Gamma.DPath), hp, rfl⟩, ?_⟩
    exact (start_normalizedReferenceFinitePath Z p hp hZfinite hY
      huncovered hterminal).symm.trans hP
  · rintro ⟨x, ⟨p, hp, hpx⟩, rfl⟩
    rcases hYfinite hp with ⟨q, rfl⟩
    refine ⟨(.inl (normalizedReferenceFinitePath Z q hp hZfinite hY
        huncovered hterminal) : (endpointWeb Gamma Z).normalized.DPath),
      ⟨q, hp, rfl⟩, ?_⟩
    change q.start = x at hpx
    exact (start_normalizedReferenceFinitePath Z q hp hZfinite hY
      huncovered hterminal).trans (congrArg (sourceCopy Z) hpx)

theorem vertexSet_normalizedLiftedReference
    (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hY : Gamma.IsWarp Y)
    (huncovered : UncoveredSourcesOutsideReference Z Y)
    (hterminal : TerminalContactPure Z Y) :
    (endpointWeb Gamma Z).normalized.vertexSet
        (normalizedLiftedReference Z Y hZfinite hY huncovered hterminal) =
      {z | ∃ x ∈ Gamma.vertexSet Y, z ∈ vertexBlock Z x} := by
  ext z
  constructor
  · rintro ⟨P, ⟨p, hp, rfl⟩, hz⟩
    change z ∈ (normalizedReferenceFinitePath Z p hp hZfinite hY
      huncovered hterminal).support at hz
    rw [support_normalizedReferenceFinitePath,
      support_expandFinitePath] at hz
    rcases hz with ⟨x, hxp, hzx⟩
    exact ⟨x, ⟨(.inl p : Gamma.DPath), hp, hxp⟩, hzx⟩
  · rintro ⟨x, ⟨P, hP, hxP⟩, hzx⟩
    rcases hYfinite hP with ⟨p, rfl⟩
    refine ⟨(.inl (normalizedReferenceFinitePath Z p hP hZfinite hY
        huncovered hterminal) : (endpointWeb Gamma Z).normalized.DPath),
      ⟨p, hP, rfl⟩, ?_⟩
    change z ∈ (normalizedReferenceFinitePath Z p hP hZfinite hY
      huncovered hterminal).support
    rw [support_normalizedReferenceFinitePath,
      support_expandFinitePath]
    exact ⟨x, hxP, hzx⟩

theorem project_not_mem_vertexSet_normalizedLiftedReference
    (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hY : Gamma.IsWarp Y)
    (huncovered : UncoveredSourcesOutsideReference Z Y)
    (hterminal : TerminalContactPure Z Y) {z : Vertex V}
    (hz : z ∉ (endpointWeb Gamma Z).normalized.vertexSet
      (normalizedLiftedReference Z Y hZfinite hY huncovered hterminal)) :
    project z ∉ Gamma.vertexSet Y := by
  intro hxY
  apply hz
  rw [vertexSet_normalizedLiftedReference Z Y hZfinite hYfinite hY
    huncovered hterminal]
  refine ⟨project z, hxY, ?_⟩
  rcases z with ⟨x, r⟩
  rcases r <;> simp [project, vertexBlock, plain, incoming, outgoing]

/-! ## Lifting normalized alternating traces -/

def liftNormalizedLink (Delta : DWeb V)
    (l : Link Delta.normalized.graph) : Link Delta.graph where
  path := Delta.liftNormalizedFinitePath l.path
  direction := l.direction
  nontrivial := l.nontrivial

@[simp] theorem direction_liftNormalizedLink (Delta : DWeb V)
    (l : Link Delta.normalized.graph) :
    (liftNormalizedLink Delta l).direction = l.direction := rfl

@[simp] theorem start_liftNormalizedLinkPath (Delta : DWeb V)
    (l : Link Delta.normalized.graph) :
    (liftNormalizedLink Delta l).path.start = l.path.start := rfl

@[simp] theorem finish_liftNormalizedLinkPath (Delta : DWeb V)
    (l : Link Delta.normalized.graph) :
    (liftNormalizedLink Delta l).path.finish = l.path.finish := rfl

@[simp] theorem entry_liftNormalizedLink (Delta : DWeb V)
    (l : Link Delta.normalized.graph) :
    (liftNormalizedLink Delta l).entry = l.entry := by
  cases l.direction <;> rfl

@[simp] theorem exit_liftNormalizedLink (Delta : DWeb V)
    (l : Link Delta.normalized.graph) :
    (liftNormalizedLink Delta l).exit = l.exit := by
  cases l.direction <;> rfl

@[simp] theorem support_liftNormalizedLink (Delta : DWeb V)
    (l : Link Delta.normalized.graph) :
    (liftNormalizedLink Delta l).path.support = l.path.support :=
  Delta.support_liftNormalizedFinitePath l.path

theorem compatibleInOrder_liftNormalizedLink (Delta : DWeb V)
    (adjacent : Prop) (l r : Link Delta.normalized.graph)
    (h : CompatibleInOrder adjacent l r) :
    CompatibleInOrder adjacent (liftNormalizedLink Delta l)
      (liftNormalizedLink Delta r) := by
  cases hl : l.direction <;> cases hr : r.direction <;>
    simpa [CompatibleInOrder, Link.entry, Link.exit, Link.interior,
      Link.endpoints, hl, hr] using h

def liftNormalizedFiniteTrace (Delta : DWeb V)
    (Q : FiniteTrace Delta.normalized.graph) : FiniteTrace Delta.graph where
  lastIndex := Q.lastIndex
  link i := liftNormalizedLink Delta (Q.link i)
  joins i := by simpa using Q.joins i
  alternates i := Q.alternates i
  compatible i j hij :=
    compatibleInOrder_liftNormalizedLink Delta _ _ _ (Q.compatible i j hij)

def liftNormalizedInfiniteTrace (Delta : DWeb V)
    (Q : InfiniteTrace Delta.normalized.graph) : InfiniteTrace Delta.graph where
  link i := liftNormalizedLink Delta (Q.link i)
  joins i := by simpa using Q.joins i
  alternates i := Q.alternates i
  compatible i j hij :=
    compatibleInOrder_liftNormalizedLink Delta _ _ _ (Q.compatible i j hij)

def liftNormalizedAltPath (Delta : DWeb V) :
    AltPath Delta.normalized.graph → AltPath Delta.graph
  | .trivial v => .trivial v
  | .finite Q => .finite (liftNormalizedFiniteTrace Delta Q)
  | .infinite Q => .infinite (liftNormalizedInfiniteTrace Delta Q)

@[simp] theorem initial_liftNormalizedAltPath (Delta : DWeb V)
    (Q : AltPath Delta.normalized.graph) :
    (liftNormalizedAltPath Delta Q).initial = Q.initial := by
  rcases Q with Q | Q | Q
  · rfl
  · change (liftNormalizedLink Delta Q.firstLink).entry = Q.firstLink.entry
    exact entry_liftNormalizedLink Delta Q.firstLink
  · change (liftNormalizedLink Delta (Q.link 0)).entry = (Q.link 0).entry
    exact entry_liftNormalizedLink Delta (Q.link 0)

@[simp] theorem terminal?_liftNormalizedAltPath (Delta : DWeb V)
    (Q : AltPath Delta.normalized.graph) :
    (liftNormalizedAltPath Delta Q).terminal? = Q.terminal? := by
  rcases Q with Q | Q | Q
  · rfl
  · change some (liftNormalizedLink Delta Q.lastLink).exit =
      some Q.lastLink.exit
    rw [exit_liftNormalizedLink]
  · rfl

@[simp] theorem isInfinite_liftNormalizedAltPath (Delta : DWeb V)
    (Q : AltPath Delta.normalized.graph) :
    (liftNormalizedAltPath Delta Q).IsInfinite ↔ Q.IsInfinite := by
  cases Q <;> simp [liftNormalizedAltPath, AltPath.IsInfinite]

/-! ## The normalized split assignment compiler -/

def normalizedAssignmentSource
    (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hY : Gamma.IsWarp Y)
    (huncovered : UncoveredSourcesOutsideReference Z Y)
    (hterminal : TerminalContactPure Z Y)
    (s : AssignmentSource Z Y) :
    {z : Vertex V // z ∈
      (endpointWeb Gamma Z).normalized.initialSet
          (normalizedEndpointLiftedPaths Z) \
        (endpointWeb Gamma Z).normalized.initialSet
          (normalizedLiftedReference Z Y hZfinite hY huncovered hterminal)} := by
  refine ⟨sourceCopy Z s.1, ?_, ?_⟩
  · rw [initialSet_normalizedEndpointLiftedPaths Z hZfinite]
    exact ⟨s.1, s.2.1, rfl⟩
  · rw [initialSet_normalizedLiftedReference Z Y hZfinite hYfinite hY
      huncovered hterminal]
    rintro ⟨x, hxY, hxs⟩
    apply s.2.2
    have : x = s.1 := sourceCopy_injective Z hxs
    simpa [this] using hxY

@[simp] theorem project_normalizedAssignmentSource
    (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hY : Gamma.IsWarp Y)
    (huncovered : UncoveredSourcesOutsideReference Z Y)
    (hterminal : TerminalContactPure Z Y)
    (s : AssignmentSource Z Y) :
    project (normalizedAssignmentSource Z Y hZfinite hYfinite hY
      huncovered hterminal s).1 = s.1 := rfl

/-- The unconditional normalized simultaneous-assignment theorem, applied to
the endpoint-pure occurrence split, yields the truthful fractured compiler. -/
theorem exists_duplicatedFracturedAssignment_of_normalized
    (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths)
    (huncovered : UncoveredSourcesOutsideReference Z Y)
    (hterminal : TerminalContactPure Z Y) :
    Nonempty (DuplicatedFracturedAssignment Z Y) := by
  let Delta := endpointWeb Gamma Z
  let ZN := normalizedEndpointLiftedPaths Z
  let YN := normalizedLiftedReference Z Y hZfinite hY huncovered hterminal
  have hordinary : SimultaneousAssignmentStatement Delta.normalized :=
    simultaneousAssignment_of_safeAlternatingDichotomy_global
      (safeAlternatingDichotomyStatement Delta.normalized)
  have hinit : Delta.normalized.initialSet YN ⊆
      Delta.normalized.initialSet ZN := by
    dsimp only [Delta, ZN, YN]
    rw [initialSet_normalizedLiftedReference Z Y hZfinite hYfinite hY
      huncovered hterminal,
      initialSet_normalizedEndpointLiftedPaths Z hZfinite]
    exact Set.image_mono hinitial
  let A := (hordinary Delta.normalized_isNormalized ZN YN
    (normalizedEndpointLiftedPaths_source Z)
    (normalizedEndpointLiftedPaths_target Z)
    (normalizedEndpointLiftedPaths_isWarp Z)
    (normalizedLiftedReference_isWarp Z Y hZfinite hY huncovered hterminal)
    (normalizedEndpointLiftedPaths_hasFiniteCharacter Z)
    (normalizedLiftedReference_hasFiniteCharacter Z Y hZfinite hY
      huncovered hterminal) hinit).some
  refine ⟨{
    splitPath := fun s ↦ liftNormalizedAltPath Delta
      (A.assigned (normalizedAssignmentSource Z Y hZfinite hYfinite hY
        huncovered hterminal s))
    projected_start := ?_
    projected_finite_terminal := ?_
    projected_finite_terminals_injective := ?_ }⟩
  · intro s
    change project (liftNormalizedAltPath Delta
      (A.assigned (normalizedAssignmentSource Z Y hZfinite hYfinite hY
        huncovered hterminal s))).initial = s.1
    rw [initial_liftNormalizedAltPath, A.starts_at]
    rfl
  · intro s z hterm
    change (liftNormalizedAltPath Delta
      (A.assigned (normalizedAssignmentSource Z Y hZfinite hYfinite hY
        huncovered hterminal s))).terminal? = some z at hterm
    have hterm' :
        (A.assigned (normalizedAssignmentSource Z Y hZfinite hYfinite hY
          huncovered hterminal s)).terminal? = some z := by
      rw [terminal?_liftNormalizedAltPath] at hterm
      exact hterm
    have hz := A.finite_terminal_mem
      (normalizedAssignmentSource Z Y hZfinite hYfinite hY
        huncovered hterminal s) hterm'
    have hzFrontier : project z ∈ Gamma.terminalFrontier Z.paths := by
      rw [terminalFrontier_normalizedEndpointLiftedPaths Z hZfinite] at hz
      rcases hz.1 with ⟨v, hv, hvz⟩
      have : v = project z := by
        simpa only [project_terminalCopy] using congrArg project hvz
      exact this ▸ hv
    exact ⟨hzFrontier,
      project_not_mem_vertexSet_normalizedLiftedReference Z Y hZfinite
        hYfinite hY huncovered hterminal hz.2⟩
  · intro s₁ s₂ z₁ z₂ hterm₁ hterm₂ hproject
    change (liftNormalizedAltPath Delta
      (A.assigned (normalizedAssignmentSource Z Y hZfinite hYfinite hY
        huncovered hterminal s₁))).terminal? = some z₁ at hterm₁
    change (liftNormalizedAltPath Delta
      (A.assigned (normalizedAssignmentSource Z Y hZfinite hYfinite hY
        huncovered hterminal s₂))).terminal? = some z₂ at hterm₂
    have hterm₁' :
        (A.assigned (normalizedAssignmentSource Z Y hZfinite hYfinite hY
          huncovered hterminal s₁)).terminal? = some z₁ := by
      rw [terminal?_liftNormalizedAltPath] at hterm₁
      exact hterm₁
    have hterm₂' :
        (A.assigned (normalizedAssignmentSource Z Y hZfinite hYfinite hY
          huncovered hterminal s₂)).terminal? = some z₂ := by
      rw [terminal?_liftNormalizedAltPath] at hterm₂
      exact hterm₂
    have hm₁ := A.finite_terminal_mem
      (normalizedAssignmentSource Z Y hZfinite hYfinite hY
        huncovered hterminal s₁) hterm₁'
    have hm₂ := A.finite_terminal_mem
      (normalizedAssignmentSource Z Y hZfinite hYfinite hY
        huncovered hterminal s₂) hterm₂'
    rw [terminalFrontier_normalizedEndpointLiftedPaths Z hZfinite] at hm₁ hm₂
    rcases hm₁.1 with ⟨v₁, hv₁, hvz₁⟩
    rcases hm₂.1 with ⟨v₂, hv₂, hvz₂⟩
    have hv : v₁ = v₂ := by
      simpa only [project_terminalCopy] using
        (congrArg project hvz₁).trans
          (hproject.trans (congrArg project hvz₂).symm)
    have hz : z₁ = z₂ := by
      rw [← hvz₁, ← hvz₂, hv]
    have hterm₂'' :
        (A.assigned (normalizedAssignmentSource Z Y hZfinite hYfinite hY
          huncovered hterminal s₂)).terminal? = some z₁ :=
      hterm₂'.trans (congrArg Option.some hz.symm)
    have hs := A.finite_terminals_injective
      (z₁ := normalizedAssignmentSource Z Y hZfinite hYfinite hY
        huncovered hterminal s₁)
      (z₂ := normalizedAssignmentSource Z Y hZfinite hYfinite hY
        huncovered hterminal s₂)
      (v := z₁) hterm₁' hterm₂''
    exact Subtype.ext (sourceCopy_injective Z (congrArg Subtype.val hs))

/-- Public endpoint-pure form of Remark 4.20. -/
theorem duplicatedFracturedAssignmentStatement :
    DuplicatedFracturedAssignmentStatement Gamma := by
  intro Z Y hY hZfinite hYfinite hinitial huncovered hterminal
  exact exists_duplicatedFracturedAssignment_of_normalized Z Y hY hZfinite
    hYfinite hinitial huncovered hterminal

end FracturedDuplication
end Alternating
end Erdos599
