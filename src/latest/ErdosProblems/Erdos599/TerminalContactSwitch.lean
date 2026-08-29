/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaAlternating
import ErdosProblems.Erdos599.ReducingBoundary

/-!
# Switching at an initial endpoint of the reference warp

The Section 8 decoder may finish by one forward link at an initial vertex of
the reference warp.  This is the one endpoint configuration deliberately
excluded by `Alternating.IsSwitchingAlternating`: the final contact is meant
to merge into the old component, rather than start a further backward link.

This file proves the exact finite switching theorem for that configuration.
The additional endpoint hypotheses are necessary.  The old initial vertex
must be non-isolated (recorded below by an old outgoing edge), and no inserted
forward edge may leave it.  Under those assumptions the usual symmetric-
difference relation is locally biunique, has a finite cyclowarp realization,
and has the same two-frontier deletion law as an ordinary reducing switch.
-/

noncomputable section

open Set

namespace Erdos599
namespace Alternating

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Switching-ready terminal-relaxed alternation.  The only forward contact
with the reference warp which need not be covered by a backward link is the
displayed terminal `u`.  The last field rules out an earlier forward
departure from that same vertex, which would compete with its old outgoing
edge. -/
structure IsTerminalContactSwitching
    (Z : Set Gamma.DPath) (Q : FiniteTrace Gamma.graph) (u : V) : Prop where
  warp : Gamma.IsWarp Z
  backwardLinksOn : BackwardLinksOn Z (.finite Q)
  forwardLinksOff : ForwardLinksOff Z (.finite Q)
  contactsCoveredAtTerminal :
    PopularAuxiliary.Input.ForwardVertexContactsCoveredAtTerminal
      Gamma Z (.finite Q)
  firstForwardInitialOff :
    (AltPath.finite Q).firstDirection? = some .forward →
      Q.initial ∉ Gamma.vertexSet Z
  terminal_eq : Q.terminal = u
  terminal_mem_initialSet : u ∈ Gamma.initialSet Z
  terminal_outgoing_or_isolated :
    HasOutgoing (familyEdges Z) u ∨ u ∈ isolatedVertices Z
  noForwardOutgoingAtTerminal :
    ¬ HasOutgoing ((AltPath.finite Q).directionEdges .forward) u

namespace IsTerminalContactSwitching

theorem of_terminalRelaxed
    {Z : Set Gamma.DPath} {Q : FiniteTrace Gamma.graph} {u : V}
    (hQ : PopularAuxiliary.Input.IsTerminalRelaxedAlternating
      Gamma Z (.finite Q))
    (hterminal : Q.terminal = u)
    (hu : u ∈ Gamma.initialSet Z)
    (huout : HasOutgoing (familyEdges Z) u)
    (hnout : ¬ HasOutgoing
      ((AltPath.finite Q).directionEdges .forward) u) :
    IsTerminalContactSwitching Z Q u where
  warp := hQ.1
  backwardLinksOn := hQ.2.1
  forwardLinksOff := hQ.2.2.1
  contactsCoveredAtTerminal := hQ.2.2.2.1
  firstForwardInitialOff := hQ.2.2.2.2
  terminal_eq := hterminal
  terminal_mem_initialSet := hu
  terminal_outgoing_or_isolated := Or.inl huout
  noForwardOutgoingAtTerminal := hnout

theorem of_terminalRelaxed_isolated
    {Z : Set Gamma.DPath} {Q : FiniteTrace Gamma.graph} {u : V}
    (hQ : PopularAuxiliary.Input.IsTerminalRelaxedAlternating
      Gamma Z (.finite Q))
    (hterminal : Q.terminal = u)
    (hu : u ∈ Gamma.initialSet Z)
    (huisolated : u ∈ isolatedVertices Z)
    (hnout : ¬ HasOutgoing
      ((AltPath.finite Q).directionEdges .forward) u) :
    IsTerminalContactSwitching Z Q u where
  warp := hQ.1
  backwardLinksOn := hQ.2.1
  forwardLinksOff := hQ.2.2.1
  contactsCoveredAtTerminal := hQ.2.2.2.1
  firstForwardInitialOff := hQ.2.2.2.2
  terminal_eq := hterminal
  terminal_mem_initialSet := hu
  terminal_outgoing_or_isolated := Or.inr huisolated
  noForwardOutgoingAtTerminal := hnout

theorem terminal_not_isolated_of_outgoing
    {Z : Set Gamma.DPath} {Q : FiniteTrace Gamma.graph} {u : V}
    (hQ : IsTerminalContactSwitching Z Q u)
    (huout : HasOutgoing (familyEdges Z) u) :
    u ∉ isolatedVertices Z :=
  not_isolated_of_hasOutgoing hQ.warp huout

end IsTerminalContactSwitching

namespace TerminalContactSwitch

private theorem Link.finish_eq_exit_of_forward
    (l : Link Gamma.graph) (h : l.direction = .forward) :
    l.path.finish = l.exit := by simp [Link.exit, h]

private theorem Link.start_eq_entry_of_forward
    (l : Link Gamma.graph) (h : l.direction = .forward) :
    l.path.start = l.entry := by simp [Link.entry, h]

private theorem Link.start_eq_exit_of_backward
    (l : Link Gamma.graph) (h : l.direction = .backward) :
    l.path.start = l.exit := by simp [Link.exit, h]

private theorem Link.finish_eq_entry_of_backward
    (l : Link Gamma.graph) (h : l.direction = .backward) :
    l.path.finish = l.entry := by simp [Link.entry, h]

private theorem link_ne_finish_of_mem_interior
    (l : Link Gamma.graph) {x : V} (hx : x ∈ l.interior) :
    x ≠ l.path.finish := by
  intro h
  apply hx.2
  simp [Link.endpoints, h]

private theorem link_ne_start_of_mem_interior
    (l : Link Gamma.graph) {x : V} (hx : x ∈ l.interior) :
    x ≠ l.path.start := by
  intro h
  apply hx.2
  simp [Link.endpoints, h]

private theorem finiteTrace_joins_of_val_eq_succ
    (Q : FiniteTrace Gamma.graph) {i j : Fin (Q.lastIndex + 1)}
    (hij : j.1 = i.1 + 1) : (Q.link i).exit = (Q.link j).entry := by
  have hi : i.1 < Q.lastIndex := by omega
  let k : Fin Q.lastIndex := ⟨i.1, hi⟩
  have hki : Fin.castSucc k = i := Fin.ext (by rfl)
  have hkj : k.succ = j := Fin.ext (by simpa [k] using hij.symm)
  simpa [hki, hkj] using Q.joins k

private theorem finiteTrace_forwardEdge_mem_directionEdges
    (Q : FiniteTrace Gamma.graph) {i : Fin (Q.lastIndex + 1)}
    (hdi : (Q.link i).direction = .forward) {x y : V}
    (hxy : (x, y) ∈ (Q.link i).path.edgeSet) :
    (x, y) ∈ (AltPath.finite Q).directionEdges .forward := by
  simp only [AltPath.directionEdges, AltPath.links, FiniteTrace.links,
    Set.mem_iUnion, Set.mem_range]
  exact ⟨Q.link i, ⟨i, rfl⟩, hdi, hxy⟩

/-- An initial vertex of an arbitrary path/ray warp has no incoming family
edge.  Unlike the older incidence characterization, this does not require
finite character. -/
private theorem not_hasIncoming_familyEdges_of_mem_initialSet
    {Z : Set Gamma.DPath} (hZ : Gamma.IsWarp Z) {x : V}
    (hx : x ∈ Gamma.initialSet Z) :
    ¬ HasIncoming (familyEdges Z) x := by
  rintro ⟨y, hyx⟩
  rcases hx with ⟨p, hpZ, rfl⟩
  simp only [familyEdges, Set.mem_iUnion] at hyx
  rcases hyx with ⟨q, hqZ, hyxq⟩
  have hxp : p.initial ∈ p.support := p.initial_mem_support
  have hxq : p.initial ∈ q.support :=
    (q.edgeSet_subset_support_prod hyxq).2
  have hpq : p = q :=
    DWeb.IsWarp.eq_of_mem_support hZ hpZ hqZ hxp hxq
  subst q
  rcases p with p | r
  · exact FinitePath.no_incoming_edge_at_start p y hyxq
  · rcases hyxq with ⟨n, hn⟩
    have hzero : n + 1 = 0 := by
      apply r.injective
      exact (congrArg Prod.snd hn).symm
    omega

/-- At a forward source, the competing old outgoing edge is removed.  The
new terminal alternative cannot occur because no forward edge leaves `u`. -/
theorem FiniteTrace.reference_outgoing_mem_edgeSet_at_forward_source
    {Z : Set Gamma.DPath} (Q : FiniteTrace Gamma.graph) {u : V}
    (hQ : IsTerminalContactSwitching Z Q u)
    {i : Fin (Q.lastIndex + 1)}
    (hdi : (Q.link i).direction = .forward) {x y z : V}
    (hxy : (x, y) ∈ (Q.link i).path.edgeSet)
    (hxz : (x, z) ∈ familyEdges Z) :
    (x, z) ∈ Q.edgeSet := by
  have hxi : x ∈ (Q.link i).path.support :=
    (Q.link i).path.edgeSet_subset_support_prod hxy |>.1
  have hxZ : x ∈ Gamma.vertexSet Z := by
    simp only [familyEdges, Set.mem_iUnion] at hxz
    rcases hxz with ⟨p, hpZ, hxp⟩
    exact ⟨p, hpZ, p.edgeSet_subset_support_prod hxp |>.1⟩
  have hxfwd : x ∈ (AltPath.finite Q).directionVertices .forward := by
    simp only [AltPath.directionVertices, AltPath.links,
      FiniteTrace.links, Set.mem_iUnion, Set.mem_range]
    exact ⟨Q.link i, ⟨i, rfl⟩, hdi, hxi⟩
  rcases hQ.contactsCoveredAtTerminal hxfwd hxZ with hxback | hterminal
  · simp only [AltPath.directionVertices, AltPath.links,
      FiniteTrace.links, Set.mem_iUnion, Set.mem_range] at hxback
    rcases hxback with ⟨l, ⟨j, rfl⟩, hdj, hxj⟩
    have hji : j < i := by
      have hne : j ≠ i := by
        intro h
        subst j
        rw [hdi] at hdj
        cases hdj
      rcases lt_or_gt_of_ne hne with hji | hij
      · exact hji
      · have hcompat := Q.compatible i j hij
        simp only [CompatibleInOrder, hdi, hdj] at hcompat
        by_cases hadj : j.1 = i.1 + 1
        · have hxinter : x ∈
              (Q.link i).path.support ∩ (Q.link j).path.support := ⟨hxi, hxj⟩
          rw [hcompat.1 hadj] at hxinter
          have hxexit : x = (Q.link i).exit := by simpa using hxinter
          exact False.elim
            (FinitePath.source_ne_finish_of_mem_edgeSet (Q.link i).path hxy
              (hxexit.trans
                (Link.finish_eq_exit_of_forward (Q.link i) hdi).symm))
        · exact False.elim
            (Set.disjoint_left.1 (hcompat.2 hadj) hxi hxj)
    have hcompat := Q.compatible j i hji
    simp only [CompatibleInOrder, hdj, hdi] at hcompat
    have hx_ne_finish : x ≠ (Q.link j).path.finish := by
      by_cases hadj : i.1 = j.1 + 1
      · rcases hcompat.1 hadj hxj hxi with hxexit | hxint
        · exact fun hxf ↦ (Q.link j).nontrivial
            ((Link.start_eq_exit_of_backward (Q.link j) hdj).trans
              (hxexit.symm.trans hxf))
        · exact link_ne_finish_of_mem_interior (Q.link j) hxint.1
      · exact link_ne_finish_of_mem_interior (Q.link j)
          ((hcompat.2 hadj ⟨hxj, hxi⟩).1)
    rcases FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
      (Q.link j).path hxj hx_ne_finish with ⟨w, hxw⟩
    have hxwZ : (x, w) ∈ familyEdges Z := by
      rcases hQ.backwardLinksOn (Q.link j) ⟨j, rfl⟩ hdj with
        ⟨p, hpZ, hjp⟩
      simp only [familyEdges, Set.mem_iUnion]
      exact ⟨p, hpZ, hjp.2 hxw⟩
    have hwz : w = z := familyEdges_out_unique hQ.warp hxwZ hxz
    subst w
    change (x, z) ∈ ⋃ k, (Q.link k).path.edgeSet
    exact Set.mem_iUnion.2 ⟨j, hxw⟩
  · have hxu : x = u := by
      simpa [AltPath.terminal?, hQ.terminal_eq] using
        (Option.some.inj hterminal).symm
    subst x
    rcases hQ.terminal_outgoing_or_isolated with huout | huisolated
    · exact False.elim (hQ.noForwardOutgoingAtTerminal
        ⟨y, finiteTrace_forwardEdge_mem_directionEdges Q hdi hxy⟩)
    · exact False.elim
        (not_hasOutgoing_of_mem_isolatedVertices hQ.warp huisolated
          ⟨z, hxz⟩)

/-- At a forward target, the competing old incoming edge is removed.  At the
single terminal exception no such edge exists because `u` is an old initial
vertex. -/
theorem FiniteTrace.reference_incoming_mem_edgeSet_at_forward_target
    {Z : Set Gamma.DPath} (Q : FiniteTrace Gamma.graph) {u : V}
    (hQ : IsTerminalContactSwitching Z Q u)
    {i : Fin (Q.lastIndex + 1)}
    (hdi : (Q.link i).direction = .forward) {x y z : V}
    (hxz : (x, z) ∈ (Q.link i).path.edgeSet)
    (hyz : (y, z) ∈ familyEdges Z) :
    (y, z) ∈ Q.edgeSet := by
  have hzi : z ∈ (Q.link i).path.support :=
    (Q.link i).path.edgeSet_subset_support_prod hxz |>.2
  have hzZ : z ∈ Gamma.vertexSet Z := by
    simp only [familyEdges, Set.mem_iUnion] at hyz
    rcases hyz with ⟨p, hpZ, hyp⟩
    exact ⟨p, hpZ, p.edgeSet_subset_support_prod hyp |>.2⟩
  have hzfwd : z ∈ (AltPath.finite Q).directionVertices .forward := by
    simp only [AltPath.directionVertices, AltPath.links,
      FiniteTrace.links, Set.mem_iUnion, Set.mem_range]
    exact ⟨Q.link i, ⟨i, rfl⟩, hdi, hzi⟩
  rcases hQ.contactsCoveredAtTerminal hzfwd hzZ with hzback | hterminal
  · simp only [AltPath.directionVertices, AltPath.links,
      FiniteTrace.links, Set.mem_iUnion, Set.mem_range] at hzback
    rcases hzback with ⟨l, ⟨j, rfl⟩, hdj, hzj⟩
    have hne : i ≠ j := by
      intro h
      subst j
      rw [hdi] at hdj
      cases hdj
    have hz_ne_start : z ≠ (Q.link j).path.start := by
      rcases lt_or_gt_of_ne hne with hij | hji
      · have hcompat := Q.compatible i j hij
        simp only [CompatibleInOrder, hdi, hdj] at hcompat
        by_cases hadj : j.1 = i.1 + 1
        · have hzinter : z ∈
              (Q.link i).path.support ∩ (Q.link j).path.support := ⟨hzi, hzj⟩
          rw [hcompat.1 hadj] at hzinter
          have hzexit : z = (Q.link i).exit := by simpa using hzinter
          have hjoin := finiteTrace_joins_of_val_eq_succ Q hadj
          have hzentry : z = (Q.link j).entry := hzexit.trans hjoin
          intro hzstart
          exact (Q.link j).nontrivial
            (hzstart.symm.trans
              (hzentry.trans
                (Link.finish_eq_entry_of_backward (Q.link j) hdj).symm))
        · exact False.elim
            (Set.disjoint_left.1 (hcompat.2 hadj) hzi hzj)
      · have hcompat := Q.compatible j i hji
        simp only [CompatibleInOrder, hdj, hdi] at hcompat
        by_cases hadj : i.1 = j.1 + 1
        · rcases hcompat.1 hadj hzj hzi with hzexit | hzint
          · have hjoin := finiteTrace_joins_of_val_eq_succ Q hadj
            have hzentry : z = (Q.link i).entry := hzexit.trans hjoin
            exact False.elim
              (FinitePath.target_ne_start_of_mem_edgeSet (Q.link i).path hxz
                (hzentry.trans
                  (Link.start_eq_entry_of_forward (Q.link i) hdi).symm))
          · exact link_ne_start_of_mem_interior (Q.link j) hzint.1
        · exact link_ne_start_of_mem_interior (Q.link j)
            ((hcompat.2 hadj ⟨hzj, hzi⟩).1)
    rcases FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
      (Q.link j).path hzj hz_ne_start with ⟨w, hwz⟩
    have hwzZ : (w, z) ∈ familyEdges Z := by
      rcases hQ.backwardLinksOn (Q.link j) ⟨j, rfl⟩ hdj with
        ⟨p, hpZ, hjp⟩
      simp only [familyEdges, Set.mem_iUnion]
      exact ⟨p, hpZ, hjp.2 hwz⟩
    have hwy : w = y := familyEdges_in_unique hQ.warp hwzZ hyz
    subst w
    change (y, z) ∈ ⋃ k, (Q.link k).path.edgeSet
    exact Set.mem_iUnion.2 ⟨j, hwz⟩
  · have hzu : z = u := by
      simpa [AltPath.terminal?, hQ.terminal_eq] using
        (Option.some.inj hterminal).symm
    subst z
    have huNoIncoming : ¬ HasIncoming (familyEdges Z) u := by
      exact not_hasIncoming_familyEdges_of_mem_initialSet hQ.warp
        hQ.terminal_mem_initialSet
    exact False.elim (huNoIncoming ⟨y, hyz⟩)

theorem FiniteTrace.switchedEdges_out_unique
    {Z : Set Gamma.DPath} (Q : FiniteTrace Gamma.graph) {u : V}
    (hQ : IsTerminalContactSwitching Z Q u) {x y z : V}
    (hxy : (x, y) ∈ switchedEdges Z (.finite Q))
    (hxz : (x, z) ∈ switchedEdges Z (.finite Q)) : y = z := by
  rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
  · exact familyEdges_out_unique hQ.warp hxy.1 hxz.1
  · rcases Q.exists_forward_link_of_mem_edgeSet_not_familyEdges
      hQ.backwardLinksOn hxz.1 hxz.2 with ⟨j, hdj, hxzj⟩
    exact False.elim (hxy.2
      (_root_.Erdos599.Alternating.TerminalContactSwitch.FiniteTrace.reference_outgoing_mem_edgeSet_at_forward_source
        Q hQ hdj hxzj hxy.1))
  · rcases Q.exists_forward_link_of_mem_edgeSet_not_familyEdges
      hQ.backwardLinksOn hxy.1 hxy.2 with ⟨i, hdi, hxyi⟩
    exact False.elim (hxz.2
      (_root_.Erdos599.Alternating.TerminalContactSwitch.FiniteTrace.reference_outgoing_mem_edgeSet_at_forward_source
        Q hQ hdi hxyi hxz.1))
  · rcases Q.exists_forward_link_of_mem_edgeSet_not_familyEdges
      hQ.backwardLinksOn hxy.1 hxy.2 with ⟨i, hdi, hxyi⟩
    rcases Q.exists_forward_link_of_mem_edgeSet_not_familyEdges
      hQ.backwardLinksOn hxz.1 hxz.2 with ⟨j, hdj, hxzj⟩
    exact Q.forward_edges_out_unique hdi hdj hxyi hxzj

theorem FiniteTrace.switchedEdges_in_unique
    {Z : Set Gamma.DPath} (Q : FiniteTrace Gamma.graph) {u : V}
    (hQ : IsTerminalContactSwitching Z Q u)
    {x y z : V}
    (hxz : (x, z) ∈ switchedEdges Z (.finite Q))
    (hyz : (y, z) ∈ switchedEdges Z (.finite Q)) : x = y := by
  rcases hxz with hxz | hxz <;> rcases hyz with hyz | hyz
  · exact familyEdges_in_unique hQ.warp hxz.1 hyz.1
  · rcases Q.exists_forward_link_of_mem_edgeSet_not_familyEdges
      hQ.backwardLinksOn hyz.1 hyz.2 with ⟨j, hdj, hyzj⟩
    exact False.elim (hxz.2
      (_root_.Erdos599.Alternating.TerminalContactSwitch.FiniteTrace.reference_incoming_mem_edgeSet_at_forward_target
        Q hQ hdj hyzj hxz.1))
  · rcases Q.exists_forward_link_of_mem_edgeSet_not_familyEdges
      hQ.backwardLinksOn hxz.1 hxz.2 with ⟨i, hdi, hxzi⟩
    exact False.elim (hyz.2
      (_root_.Erdos599.Alternating.TerminalContactSwitch.FiniteTrace.reference_incoming_mem_edgeSet_at_forward_target
        Q hQ hdi hxzi hyz.1))
  · rcases Q.exists_forward_link_of_mem_edgeSet_not_familyEdges
      hQ.backwardLinksOn hxz.1 hxz.2 with ⟨i, hdi, hxzi⟩
    rcases Q.exists_forward_link_of_mem_edgeSet_not_familyEdges
      hQ.backwardLinksOn hyz.1 hyz.2 with ⟨j, hdj, hyzj⟩
    exact Q.forward_edges_in_unique hdi hdj hxzi hyzj

/-- Terminal-contact switching is still the literal deletion of the used
backward edges followed by insertion of the forward edges. -/
theorem FiniteTrace.switchedEdges_eq_backward_sdiff_union_forward
    {Z : Set Gamma.DPath} (Q : FiniteTrace Gamma.graph) {u : V}
    (hQ : IsTerminalContactSwitching Z Q u) :
    switchedEdges Z (.finite Q) =
      (familyEdges Z \ (AltPath.finite Q).directionEdges .backward) ∪
        (AltPath.finite Q).directionEdges .forward := by
  have hB := hQ.backwardLinksOn.directionEdges_subset_familyEdges
  have hF := hQ.forwardLinksOff.directionEdges_disjoint
  ext e
  have hQE : e ∈ (AltPath.finite Q).edgeSet ↔
      e ∈ (AltPath.finite Q).directionEdges .forward ∨
        e ∈ (AltPath.finite Q).directionEdges .backward := by
    rw [(AltPath.finite Q).edgeSet_eq_directionEdges_union]
    rfl
  constructor
  · rintro (⟨heZ, heQ⟩ | ⟨heQ, heZ⟩)
    · left
      exact ⟨heZ, fun heB ↦ heQ (hQE.2 (Or.inr heB))⟩
    · rcases hQE.1 heQ with heF | heB
      · exact Or.inr heF
      · exact False.elim (heZ (hB heB))
  · rintro (⟨heZ, heB⟩ | heF)
    · left
      exact ⟨heZ, fun heQ ↦ by
        rcases hQE.1 heQ with heF | heB'
        · exact Set.disjoint_left.1 hF heF heZ
        · exact heB heB'⟩
    · right
      refine ⟨hQE.2 (Or.inl heF), ?_⟩
      exact fun heZ ↦ Set.disjoint_left.1 hF heF heZ

/-- The edge-balance calculation for a terminal contact. -/
theorem FiniteTrace.edgeBalance_switched_eq_add_directionBalances
    {Z : Set Gamma.DPath} (Q : FiniteTrace Gamma.graph) {u : V}
    (hQ : IsTerminalContactSwitching Z Q u)
    (x : V) :
    edgeBalance (switchedEdges Z (.finite Q)) x =
      edgeBalance (familyEdges Z) x +
        edgeBalance ((AltPath.finite Q).directionEdges .forward) x -
        edgeBalance ((AltPath.finite Q).directionEdges .backward) x := by
  let E := familyEdges Z
  let B := (AltPath.finite Q).directionEdges .backward
  let F := (AltPath.finite Q).directionEdges .forward
  have hBE : B ⊆ E := hQ.backwardLinksOn.directionEdges_subset_familyEdges
  have hFB : Disjoint (E \ B) F := by
    rw [Set.disjoint_left]
    intro e heEF heF
    exact Set.disjoint_left.1 hQ.forwardLinksOff.directionEdges_disjoint
      heF heEF.1
  have houtE : Relator.RightUnique (fun a b ↦ (a, b) ∈ E) :=
    fun _ _ _ h₁ h₂ ↦ familyEdges_out_unique hQ.warp h₁ h₂
  have hinE : Relator.LeftUnique (fun a b ↦ (a, b) ∈ E) :=
    fun _ _ _ h₁ h₂ ↦ familyEdges_in_unique hQ.warp h₁ h₂
  have houtS : Relator.RightUnique (fun a b ↦ (a, b) ∈ E \ B ∪ F) := by
    rw [← _root_.Erdos599.Alternating.TerminalContactSwitch.FiniteTrace.switchedEdges_eq_backward_sdiff_union_forward Q hQ]
    exact fun _ _ _ h₁ h₂ ↦
      _root_.Erdos599.Alternating.TerminalContactSwitch.FiniteTrace.switchedEdges_out_unique
        (u := u) Q hQ h₁ h₂
  have hinS : Relator.LeftUnique (fun a b ↦ (a, b) ∈ E \ B ∪ F) := by
    rw [← _root_.Erdos599.Alternating.TerminalContactSwitch.FiniteTrace.switchedEdges_eq_backward_sdiff_union_forward Q hQ]
    exact fun _ _ _ h₁ h₂ ↦
      _root_.Erdos599.Alternating.TerminalContactSwitch.FiniteTrace.switchedEdges_in_unique
        (u := u) Q hQ h₁ h₂
  rw [_root_.Erdos599.Alternating.TerminalContactSwitch.FiniteTrace.switchedEdges_eq_backward_sdiff_union_forward Q hQ]
  simpa only [E, B, F] using
    edgeBalance_sdiff_union_eq_add_sub hBE houtE hinE houtS hinS hFB x

/-- The terminal-contact trace has the same signed boundary delta as an
ordinary reducing trace. -/
theorem FiniteTrace.hasTerminalContactBalanceDelta
    {Z : Set Gamma.DPath} (Q : FiniteTrace Gamma.graph) {u : V}
    (hQ : IsTerminalContactSwitching Z Q u)
    (x : V) :
    edgeBalance (switchedEdges Z (.finite Q)) x =
      edgeBalance (familyEdges Z) x + propInt (x = Q.initial) -
        propInt (x = Q.terminal) := by
  rw [_root_.Erdos599.Alternating.TerminalContactSwitch.FiniteTrace.edgeBalance_switched_eq_add_directionBalances Q hQ]
  have hdir := Q.directionBalance_difference_eq_sum_entries x
  have hsum := Q.sum_entry_exit_eq_boundary x
  omega

private theorem not_mem_backwardVertices_of_mem_isolated
    {Z : Set Gamma.DPath} (Q : FiniteTrace Gamma.graph) {u x : V}
    (hQ : IsTerminalContactSwitching Z Q u)
    (hxiso : x ∈ isolatedVertices Z) :
    x ∉ (AltPath.finite Q).directionVertices .backward := by
  intro hxback
  simp only [AltPath.directionVertices, AltPath.links,
    FiniteTrace.links, Set.mem_iUnion, Set.mem_range] at hxback
  rcases hxback with ⟨l, ⟨i, rfl⟩, hdi, hxl⟩
  rcases hQ.backwardLinksOn (Q.link i) ⟨i, rfl⟩ hdi with
    ⟨p, hpZ, hip⟩
  have hxp : x ∈ p.support := hip.1 hxl
  have hp0 : p = Gamma.trivialPath x :=
    DWeb.IsWarp.eq_of_mem_support hQ.warp hpZ hxiso hxp (by simp)
  have hsupp : (Q.link i).path.support ⊆ ({x} : Set V) := by
    rw [← Gamma.support_trivialPath x, ← hp0]
    exact hip.1
  have hstart : (Q.link i).path.start = x := by
    simpa using hsupp (Q.link i).path.start_mem_support
  have hfinish : (Q.link i).path.finish = x := by
    simpa using hsupp (Q.link i).path.finish_mem_support
  exact (Q.link i).nontrivial (hstart.trans hfinish.symm)

private theorem not_mem_vertexSet_of_mem_isolated
    {Z : Set Gamma.DPath} (Q : FiniteTrace Gamma.graph) {u x : V}
    (hQ : IsTerminalContactSwitching Z Q u)
    (hxiso : x ∈ isolatedVertices Z) (hxu : x ≠ u) : x ∉ Q.vertexSet := by
  intro hxQ
  simp only [FiniteTrace.vertexSet, Set.mem_iUnion] at hxQ
  rcases hxQ with ⟨i, hxi⟩
  cases hdi : (Q.link i).direction with
  | backward =>
      apply not_mem_backwardVertices_of_mem_isolated Q hQ hxiso
      simp only [AltPath.directionVertices, AltPath.links,
        FiniteTrace.links, Set.mem_iUnion, Set.mem_range]
      exact ⟨Q.link i, ⟨i, rfl⟩, hdi, hxi⟩
  | forward =>
      have hxfwd : x ∈ (AltPath.finite Q).directionVertices .forward := by
        simp only [AltPath.directionVertices, AltPath.links,
          FiniteTrace.links, Set.mem_iUnion, Set.mem_range]
        exact ⟨Q.link i, ⟨i, rfl⟩, hdi, hxi⟩
      have hxZ : x ∈ Gamma.vertexSet Z :=
        ⟨Gamma.trivialPath x, hxiso, by simp⟩
      rcases hQ.contactsCoveredAtTerminal hxfwd hxZ with hxback | hxt
      · exact not_mem_backwardVertices_of_mem_isolated Q hQ hxiso hxback
      · have heq : x = u := by
          simpa [AltPath.terminal?, hQ.terminal_eq] using
            (Option.some.inj hxt).symm
        exact hxu heq

theorem isolated_not_incident_switched
    {Z : Set Gamma.DPath} (Q : FiniteTrace Gamma.graph) {u x : V}
    (hQ : IsTerminalContactSwitching Z Q u)
    (hxiso : x ∈ isolatedVertices Z) (hxu : x ≠ u) :
    (¬ HasIncoming (switchedEdges Z (.finite Q)) x) ∧
      (¬ HasOutgoing (switchedEdges Z (.finite Q)) x) := by
  constructor
  · rintro ⟨y, hyx⟩
    rcases hyx with hyx | hyx
    · exact not_hasIncoming_of_mem_isolatedVertices hQ.warp hxiso ⟨y, hyx.1⟩
    · have hxQ : x ∈ Q.vertexSet := by
        rcases Q.exists_link_of_mem_edgeSet hyx.1 with ⟨i, hi⟩
        exact Set.mem_iUnion.2 ⟨i,
          (Q.link i).path.edgeSet_subset_support_prod hi |>.2⟩
      exact not_mem_vertexSet_of_mem_isolated Q hQ hxiso hxu hxQ
  · rintro ⟨y, hxy⟩
    rcases hxy with hxy | hxy
    · exact not_hasOutgoing_of_mem_isolatedVertices hQ.warp hxiso ⟨y, hxy.1⟩
    · have hxQ : x ∈ Q.vertexSet := by
        rcases Q.exists_link_of_mem_edgeSet hxy.1 with ⟨i, hi⟩
        exact Set.mem_iUnion.2 ⟨i,
          (Q.link i).path.edgeSet_subset_support_prod hi |>.1⟩
      exact not_mem_vertexSet_of_mem_isolated Q hQ hxiso hxu hxQ

/-- A finite terminal-contact application has an honest finite-character
cyclowarp realization. -/
theorem FiniteTrace.exists_terminalContact_application_cyclowarp
    {Z : Set Gamma.DPath} (Q : FiniteTrace Gamma.graph) {u : V}
    (hQ : IsTerminalContactSwitching Z Q u)
    (hZfin : Gamma.HasFiniteCharacter Z) :
    ∃ C : Cyclowarp Gamma,
      C.edges = (Cyclowarp.application Z (.finite Q)).edges ∧
      C.isolated = isolatedVertices Z \ {u} ∧
      Gamma.HasFiniteCharacter C.pathPart := by
  have hfinite := Q.switched_componentSupports_finite hQ.warp hZfin
  have hI : ∀ x ∈ isolatedVertices Z \ {u}, ∀ y,
      (x, y) ∉ switchedEdges Z (.finite Q) ∧
        (y, x) ∉ switchedEdges Z (.finite Q) := by
    intro x hx y
    have hno := isolated_not_incident_switched Q hQ hx.1 hx.2
    exact ⟨fun hxy ↦ hno.2 ⟨y, hxy⟩, fun hyx ↦ hno.1 ⟨y, hyx⟩⟩
  rcases RelationComponents.exists_cyclowarp_of_finite_componentSupports
      Gamma (switchedEdges Z (.finite Q)) (isolatedVertices Z \ {u})
      (Cyclowarp.application Z (.finite Q)).edges_in_graph
      (fun hxy hxz ↦
        _root_.Erdos599.Alternating.TerminalContactSwitch.FiniteTrace.switchedEdges_out_unique Q hQ hxy hxz)
      (fun hxz hyz ↦
        _root_.Erdos599.Alternating.TerminalContactSwitch.FiniteTrace.switchedEdges_in_unique Q hQ hxz hyz)
      hfinite hI with ⟨C, hCedges, hCisolated, hCfin⟩
  exact ⟨C, by simpa using hCedges, by simpa using hCisolated, hCfin⟩

theorem start_hasIncoming
    {Z : Set Gamma.DPath} (Q : FiniteTrace Gamma.graph) {u v : V}
    (hQ : IsTerminalContactSwitching Z Q u)
    (hv : v ∈ Gamma.terminalFrontier Z) (hQi : Q.initial = v) :
    HasIncoming (familyEdges Z) v := by
  have hdir : Q.firstLink.direction = .backward := by
    cases hd : Q.firstLink.direction with
    | backward => rfl
    | forward =>
        exfalso
        apply hQ.firstForwardInitialOff
        · simp [AltPath.firstDirection?, hd]
        · rw [hQi]
          exact terminalFrontier_subset_vertexSet Z hv
  have hfinish : Q.firstLink.path.finish = v := by
    rw [← hQi]
    change Q.firstLink.path.finish = Q.firstLink.entry
    simp [Link.entry, hdir]
  have hne : Q.firstLink.path.finish ≠ Q.firstLink.path.start :=
    Q.firstLink.nontrivial.symm
  rcases FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
      Q.firstLink.path Q.firstLink.path.finish_mem_support hne with ⟨y, hy⟩
  rcases hQ.backwardLinksOn Q.firstLink Q.firstLink_mem_links hdir with
    ⟨p, hpZ, hpSub⟩
  refine ⟨y, ?_⟩
  simp only [familyEdges, Set.mem_iUnion]
  exact ⟨p, hpZ, hpSub.2 (hfinish ▸ hy)⟩

/-- Exact boundary delta for the path part of a finite terminal-contact
switch.  It deletes the old initial endpoint `u` and the old terminal
endpoint `v`. -/
theorem Cyclowarp.pathPart_frontiers_eq_sdiff_of_finite_terminalContact
    {Z : Set Gamma.DPath} (hZfin : Gamma.HasFiniteCharacter Z)
    (Q : FiniteTrace Gamma.graph) {u v : V}
    (hQ : IsTerminalContactSwitching Z Q u)
    (hv : v ∈ Gamma.terminalFrontier Z) (hQi : Q.initial = v)
    (C : Cyclowarp Gamma)
    (hEdges : C.edges = (Cyclowarp.application Z (.finite Q)).edges)
    (hIso : C.isolated = isolatedVertices Z \ {u})
    (hCfin : Gamma.HasFiniteCharacter C.pathPart) :
    Gamma.initialSet C.pathPart = Gamma.initialSet Z \ {u} ∧
      Gamma.terminalFrontier C.pathPart =
        Gamma.terminalFrontier Z \ {v} := by
  classical
  have hvin := start_hasIncoming Q hQ hv hQi
  have hvniso := not_isolated_of_hasIncoming hQ.warp hvin
  have hvbal : edgeBalance (familyEdges Z) v = -1 :=
    (mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one
      hQ.warp hZfin).1 hv |>.resolve_left hvniso
  have hvu : v ≠ u := by
    intro h
    subst u
    exact (not_hasIncoming_familyEdges_of_mem_initialSet hQ.warp
      hQ.terminal_mem_initialSet) hvin
  have huv : u ≠ v := hvu.symm
  have hbalance : ∀ x,
      edgeBalance C.edges x = edgeBalance (familyEdges Z) x +
        propInt (x = v) - propInt (x = u) := by
    intro x
    rw [hEdges, Cyclowarp.application_edges,
      _root_.Erdos599.Alternating.TerminalContactSwitch.FiniteTrace.hasTerminalContactBalanceDelta Q hQ,
      hQi, hQ.terminal_eq]
  rcases hQ.terminal_outgoing_or_isolated with huout | huisolated
  · have huniso := not_isolated_of_hasOutgoing hQ.warp huout
    have hubal : edgeBalance (familyEdges Z) u = 1 :=
      (mem_initialSet_iff_isolated_or_edgeBalance_eq_one
        hQ.warp hZfin).1 hQ.terminal_mem_initialSet |>.resolve_left huniso
    have hIso' : C.isolated = isolatedVertices Z := by
      rw [hIso]
      ext x
      simp only [Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · exact fun hx ↦ hx.1
      · intro hx
        exact ⟨hx, fun hxu ↦ huniso (hxu ▸ hx)⟩
    constructor
    · ext x
      rw [C.mem_initialSet_pathPart_iff_isolated_or_edgeBalance_eq_one hCfin]
      simp only [Set.mem_sdiff, Set.mem_singleton_iff]
      rw [mem_initialSet_iff_isolated_or_edgeBalance_eq_one hQ.warp hZfin,
        hIso', hbalance]
      by_cases hxv : x = v
      · subst x
        simp [propInt, hvniso, hvbal, hvu]
      · by_cases hxu : x = u
        · subst x
          simp [propInt, huniso, hubal, huv]
        · simp [propInt, hxv, hxu]
    · ext x
      rw [C.mem_terminalFrontier_pathPart_iff_isolated_or_edgeBalance_eq_neg_one
        hCfin]
      simp only [Set.mem_sdiff, Set.mem_singleton_iff]
      rw [mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one
        hQ.warp hZfin, hIso', hbalance]
      by_cases hxv : x = v
      · subst x
        simp [propInt, hvniso, hvbal, hvu]
      · by_cases hxu : x = u
        · subst x
          simp [propInt, huniso, hubal, huv]
        · simp [propInt, hxv, hxu]
  · have huNoIn := not_hasIncoming_of_mem_isolatedVertices hQ.warp huisolated
    have huNoOut := not_hasOutgoing_of_mem_isolatedVertices hQ.warp huisolated
    have hubal : edgeBalance (familyEdges Z) u = 0 := by
      simp [edgeBalance, propInt, huNoIn, huNoOut]
    constructor
    · ext x
      rw [C.mem_initialSet_pathPart_iff_isolated_or_edgeBalance_eq_one hCfin]
      simp only [Set.mem_sdiff, Set.mem_singleton_iff]
      rw [mem_initialSet_iff_isolated_or_edgeBalance_eq_one hQ.warp hZfin,
        hIso, hbalance]
      by_cases hxv : x = v
      · subst x
        simp [propInt, hvniso, hvbal, hvu]
      · by_cases hxu : x = u
        · subst x
          simp [propInt, huisolated, hubal, huv]
        · simp [propInt, hxv, hxu]
    · ext x
      rw [C.mem_terminalFrontier_pathPart_iff_isolated_or_edgeBalance_eq_neg_one
        hCfin]
      simp only [Set.mem_sdiff, Set.mem_singleton_iff]
      rw [mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one
        hQ.warp hZfin, hIso, hbalance]
      by_cases hxv : x = v
      · subst x
        simp [propInt, hvniso, hvbal, hvu]
      · by_cases hxu : x = u
        · subst x
          simp [propInt, huisolated, hubal, huv]
        · simp [propInt, hxv, hxu]

/-- Complete finite terminal-contact switch: the path part of the switched
cyclowarp is an honest finite-character warp and deletes exactly the two
displayed frontier points. -/
theorem exists_terminalContactSwitch
    (Z : Set Gamma.DPath) (Q : FiniteTrace Gamma.graph) (u v : V)
    (hZfin : Gamma.HasFiniteCharacter Z)
    (hQ : IsTerminalContactSwitching Z Q u)
    (hv : v ∈ Gamma.terminalFrontier Z) (hQi : Q.initial = v) :
    ∃ Z' : Set Gamma.DPath,
      Gamma.IsWarp Z' ∧ Gamma.HasFiniteCharacter Z' ∧
        Gamma.initialSet Z' = Gamma.initialSet Z \ {u} ∧
        Gamma.terminalFrontier Z' = Gamma.terminalFrontier Z \ {v} := by
  obtain ⟨C, hEdges, hIso, hCfin⟩ :=
    _root_.Erdos599.Alternating.TerminalContactSwitch.FiniteTrace.exists_terminalContact_application_cyclowarp
      Q hQ hZfin
  have hfrontiers :=
    _root_.Erdos599.Alternating.TerminalContactSwitch.Cyclowarp.pathPart_frontiers_eq_sdiff_of_finite_terminalContact
      hZfin Q hQ hv hQi C hEdges hIso hCfin
  exact ⟨C.pathPart, C.pathPart_isWarp, hCfin,
    hfrontiers.1, hfrontiers.2⟩

end TerminalContactSwitch
end Alternating
end Erdos599

#print axioms Erdos599.Alternating.TerminalContactSwitch.FiniteTrace.switchedEdges_out_unique
#print axioms Erdos599.Alternating.TerminalContactSwitch.FiniteTrace.switchedEdges_in_unique
#print axioms Erdos599.Alternating.TerminalContactSwitch.FiniteTrace.exists_terminalContact_application_cyclowarp
#print axioms Erdos599.Alternating.TerminalContactSwitch.Cyclowarp.pathPart_frontiers_eq_sdiff_of_finite_terminalContact
#print axioms Erdos599.Alternating.TerminalContactSwitch.exists_terminalContactSwitch
