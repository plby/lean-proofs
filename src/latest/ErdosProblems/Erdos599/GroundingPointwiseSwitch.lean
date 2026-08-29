/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaCompressionBridge
import ErdosProblems.Erdos599.ReducingBoundary

/-!
# Pointwise boundary control for a decoded grounding switch

The limiting ladder warp may contain rays, so the finite-character boundary
lemmas used by the finite reducing-switch construction do not apply to it.
This file proves the corresponding edge-balance characterization for an
arbitrary warp of finite paths and rays.  It then records the strongest
pointwise consequence of a realized decoded switch: a nontrivial reducing
route deletes exactly its terminal initial and its initial terminal.

This does not assert that one switch is already a wave.  Other hanging
components may remain; the whole equal-subwarp argument must combine the
compatible switches before applying the wave criterion.
-/

noncomputable section

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

namespace Ray

theorem not_hasIncoming_edgeSet_initial {D : Digraph V} (r : Ray D) :
    ¬ HasIncoming r.edgeSet r.initial := by
  rintro ⟨y, n, h⟩
  have hzero : n + 1 = 0 := by
    apply r.injective
    exact (congrArg Prod.snd h).symm
  omega

theorem hasOutgoing_edgeSet_of_mem_support {D : Digraph V} (r : Ray D)
    {x : V} (hx : x ∈ r.support) : HasOutgoing r.edgeSet x := by
  rcases hx with ⟨n, rfl⟩
  exact ⟨r (n + 1), n, rfl⟩

theorem hasIncoming_edgeSet_of_mem_support_of_ne_initial
    {D : Digraph V} (r : Ray D) {x : V} (hx : x ∈ r.support)
    (hne : x ≠ r.initial) : HasIncoming r.edgeSet x := by
  rcases hx with ⟨n, rfl⟩
  cases n with
  | zero => exact False.elim (hne rfl)
  | succ n =>
      refine ⟨r n, n, ?_⟩
      simp only [Nat.succ_eq_add_one]

end Ray

private theorem Walk.eq_nil_of_isPath_pointwise {D : Digraph V} {x : V}
    (p : Walk D x x) (hp : p.IsPath) : p = .nil := by
  cases p with
  | nil => rfl
  | @cons _ y _ h q =>
      exact False.elim ((List.nodup_cons.mp hp).1 q.end_mem_support)

private theorem FinitePath.eq_trivial_of_start_eq_finish_pointwise
    {D : Digraph V} (p : FinitePath D) (h : p.start = p.finish) :
    p = FinitePath.trivial D p.start := by
  rcases p with ⟨start, finish, walk, isPath⟩
  dsimp at h ⊢
  subst finish
  have hw : walk = .nil := Walk.eq_nil_of_isPath_pointwise walk isPath
  subst walk
  rfl

private theorem noIncoming_familyEdges_at_initial
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W)
    {p : Gamma.DPath} (hp : p ∈ W) :
    ¬ HasIncoming (familyEdges W) p.initial := by
  rintro ⟨y, hy⟩
  simp only [familyEdges, Set.mem_iUnion] at hy
  rcases hy with ⟨q, hq, hyq⟩
  have hpq : p = q :=
    DWeb.IsWarp.eq_of_mem_support hW hp hq p.initial_mem_support
      (q.edgeSet_subset_support_prod hyq).2
  subst q
  rcases p with p | r
  · exact FinitePath.no_incoming_edge_at_start p y hyq
  · exact _root_.Erdos599.Alternating.Ray.not_hasIncoming_edgeSet_initial r
      ⟨y, hyq⟩

/-- An initial vertex of an arbitrary warp has no incoming family edge.
Unlike the older finite-character characterization, this also applies when
the selected component is a ray. -/
theorem not_hasIncoming_familyEdges_of_mem_initialSet_anyWarp
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W)
    {x : V} (hx : x ∈ Gamma.initialSet W) :
    ¬ HasIncoming (familyEdges W) x := by
  rcases hx with ⟨p, hp, rfl⟩
  exact noIncoming_familyEdges_at_initial hW hp

private theorem noOutgoing_familyEdges_at_terminal
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W)
    {p : Gamma.DPath} (hp : p ∈ W) {x : V}
    (hterminal : Gamma.terminal? p = some x) :
    ¬ HasOutgoing (familyEdges W) x := by
  rintro ⟨y, hy⟩
  simp only [familyEdges, Set.mem_iUnion] at hy
  rcases hy with ⟨q, hq, hyq⟩
  have hxp : x ∈ p.support := Gamma.terminal_mem_support hterminal
  have hpq : p = q :=
    DWeb.IsWarp.eq_of_mem_support hW hp hq hxp
      (q.edgeSet_subset_support_prod hyq).1
  subst q
  rcases p with p | r
  · simp only [DWeb.terminal?_finite, Option.some.injEq] at hterminal
    subst x
    exact FinitePath.no_outgoing_edge_at_finish p y hyq
  · simp at hterminal

/-- A finite terminal of an arbitrary warp has no outgoing family edge;
other components of the warp may be rays. -/
theorem not_hasOutgoing_familyEdges_of_mem_terminalFrontier_anyWarp
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W)
    {x : V} (hx : x ∈ Gamma.terminalFrontier W) :
    ¬ HasOutgoing (familyEdges W) x := by
  rcases hx with ⟨p, hp, hterminal⟩
  exact noOutgoing_familyEdges_at_terminal hW hp hterminal

private theorem hasOutgoing_familyEdges_of_nontrivial_finite_start
    {W : Set Gamma.DPath} {p : FinitePath Gamma.graph}
    (hp : (Sum.inl p : Gamma.DPath) ∈ W) (hne : p.start ≠ p.finish) :
    HasOutgoing (familyEdges W) p.start := by
  obtain ⟨y, hy⟩ :=
    _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish p
    p.start_mem_support hne
  exact ⟨y, Set.mem_iUnion.2 ⟨(Sum.inl p : Gamma.DPath),
    Set.mem_iUnion.2 ⟨hp, hy⟩⟩⟩

private theorem hasIncoming_familyEdges_of_nontrivial_finite_finish
    {W : Set Gamma.DPath} {p : FinitePath Gamma.graph}
    (hp : (Sum.inl p : Gamma.DPath) ∈ W) (hne : p.start ≠ p.finish) :
    HasIncoming (familyEdges W) p.finish := by
  obtain ⟨y, hy⟩ :=
    _root_.Erdos599.Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start p
    p.finish_mem_support hne.symm
  exact ⟨y, Set.mem_iUnion.2 ⟨(Sum.inl p : Gamma.DPath),
    Set.mem_iUnion.2 ⟨hp, hy⟩⟩⟩

private theorem hasOutgoing_familyEdges_of_ray_mem
    {W : Set Gamma.DPath} {r : Ray Gamma.graph}
    (hr : (Sum.inr r : Gamma.DPath) ∈ W) {x : V}
    (hx : x ∈ r.support) : HasOutgoing (familyEdges W) x := by
  obtain ⟨y, hxy⟩ :=
    _root_.Erdos599.Alternating.Ray.hasOutgoing_edgeSet_of_mem_support r hx
  exact ⟨y, Set.mem_iUnion.2 ⟨(Sum.inr r : Gamma.DPath),
    Set.mem_iUnion.2 ⟨hr, hxy⟩⟩⟩

private theorem hasIncoming_familyEdges_of_path_mem_of_ne_initial
    {W : Set Gamma.DPath} {p : Gamma.DPath} (hp : p ∈ W)
    {x : V} (hx : x ∈ p.support) (hne : x ≠ p.initial) :
    HasIncoming (familyEdges W) x := by
  rcases p with p | r
  · obtain ⟨y, hy⟩ :=
      _root_.Erdos599.Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start p
      hx hne
    exact ⟨y, Set.mem_iUnion.2 ⟨(Sum.inl p : Gamma.DPath),
      Set.mem_iUnion.2 ⟨hp, hy⟩⟩⟩
  · obtain ⟨y, hy⟩ :=
      _root_.Erdos599.Alternating.Ray.hasIncoming_edgeSet_of_mem_support_of_ne_initial
        r hx hne
    exact ⟨y, Set.mem_iUnion.2 ⟨(Sum.inr r : Gamma.DPath),
      Set.mem_iUnion.2 ⟨hp, hy⟩⟩⟩

/-- Edge balance recognizes the initial set of every warp, including warps
with ray components. -/
theorem mem_initialSet_iff_isolated_or_edgeBalance_eq_one_anyWarp
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W) {x : V} :
    x ∈ Gamma.initialSet W ↔
      x ∈ isolatedVertices W ∨ edgeBalance (familyEdges W) x = 1 := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases p with p | r
    · by_cases htrivial : p.start = p.finish
      · left
        have hp0 :=
          FinitePath.eq_trivial_of_start_eq_finish_pointwise p htrivial
        have hp0' : (Sum.inl p : Gamma.DPath) = Gamma.trivialPath p.start := by
          rw [hp0]
          rfl
        rwa [hp0'] at hp
      · right
        rw [edgeBalance_eq_one_iff]
        exact ⟨hasOutgoing_familyEdges_of_nontrivial_finite_start hp htrivial,
          noIncoming_familyEdges_at_initial hW hp⟩
    · right
      rw [edgeBalance_eq_one_iff]
      exact ⟨hasOutgoing_familyEdges_of_ray_mem hp r.initial_mem_support,
        noIncoming_familyEdges_at_initial hW hp⟩
  · rintro (hiso | hbalance)
    · exact ⟨Gamma.trivialPath x, hiso, by simp⟩
    · rw [edgeBalance_eq_one_iff] at hbalance
      obtain ⟨y, hxy⟩ := hbalance.1
      simp only [familyEdges, Set.mem_iUnion] at hxy
      rcases hxy with ⟨p, hp, hpedge⟩
      have hxp : x ∈ p.support := (p.edgeSet_subset_support_prod hpedge).1
      refine ⟨p, hp, ?_⟩
      by_contra hne
      exact hbalance.2
        (hasIncoming_familyEdges_of_path_mem_of_ne_initial hp hxp
          (fun h ↦ hne h.symm))

/-- Edge balance recognizes the finite terminal frontier of every warp,
even when other components are rays. -/
theorem mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one_anyWarp
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W) {x : V} :
    x ∈ Gamma.terminalFrontier W ↔
      x ∈ isolatedVertices W ∨ edgeBalance (familyEdges W) x = -1 := by
  constructor
  · rintro ⟨p, hp, hterminal⟩
    rcases p with p | r
    · simp only [DWeb.terminal?_finite, Option.some.injEq] at hterminal
      subst x
      by_cases htrivial : p.start = p.finish
      · left
        have hp0 :=
          FinitePath.eq_trivial_of_start_eq_finish_pointwise p htrivial
        have hp0' : (Sum.inl p : Gamma.DPath) = Gamma.trivialPath p.finish := by
          rw [hp0, htrivial]
          rfl
        rwa [hp0'] at hp
      · right
        rw [edgeBalance_eq_neg_one_iff]
        exact ⟨hasIncoming_familyEdges_of_nontrivial_finite_finish hp htrivial,
          noOutgoing_familyEdges_at_terminal hW hp rfl⟩
    · simp at hterminal
  · rintro (hiso | hbalance)
    · exact ⟨Gamma.trivialPath x, hiso, by simp⟩
    · rw [edgeBalance_eq_neg_one_iff] at hbalance
      obtain ⟨y, hyx⟩ := hbalance.1
      simp only [familyEdges, Set.mem_iUnion] at hyx
      rcases hyx with ⟨p, hp, hpedge⟩
      have hxp : x ∈ p.support := (p.edgeSet_subset_support_prod hpedge).2
      rcases p with p | r
      · refine ⟨Sum.inl p, hp, ?_⟩
        simp only [DWeb.terminal?_finite, Option.some.injEq]
        by_contra hne
        obtain ⟨z, hxz⟩ :=
          _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
            p hxp (fun h ↦ hne h.symm)
        apply hbalance.2
        exact ⟨z, Set.mem_iUnion.2 ⟨(Sum.inl p : Gamma.DPath),
          Set.mem_iUnion.2 ⟨hp, hxz⟩⟩⟩
      · exact False.elim (hbalance.2
          (hasOutgoing_familyEdges_of_ray_mem hp hxp))

end Alternating

namespace PopularAuxiliary.Input

open Set DirectedPath Alternating

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}
variable {L : PopularAuxiliary.Input Gamma I}

/-- A realized nontrivial decoded reducing switch has the exact boundary
effect needed by grounding: it deletes the hanging initial endpoint and the
inessential terminal endpoint.  No finite-character assumption is made on
the reference or realized warp. -/
theorem AlternatingCompression.realizedBy_frontiers_of_reducing
    {p : FinitePath L.lambda.graph} {T : L.MicroTrace p}
    (C : L.AlternatingCompression p T)
    (hSwitch : IsSwitchingAlternating L.ladder.paths C.path)
    (hx : T.initial ∈ Gamma.terminalFrontier L.ladder.paths)
    (hy : T.terminal ∈ Gamma.initialSet L.ladder.paths)
    (hxy : T.initial ≠ T.terminal)
    {W : Set Gamma.DPath}
    (hW : (L.decodedSwitchData p).RealizedBy W) :
    Gamma.initialSet W = Gamma.initialSet L.ladder.paths \ {T.terminal} ∧
      Gamma.terminalFrontier W =
        Gamma.terminalFrontier L.ladder.paths \ {T.initial} := by
  have hWapp :
      (Cyclowarp.application L.ladder.paths C.path).RealizedBy W := by
    rw [← C.switchData_eq]
    exact hW
  obtain ⟨Q, hCQ⟩ : ∃ Q : FiniteTrace Gamma.graph,
      C.path = .finite Q := by
    cases hC : C.path with
    | trivial a =>
        have hi : a = T.initial := by
          have hinit := C.initial_eq
          rw [hC] at hinit
          exact hinit
        have ht : a = T.terminal := by
          have hterm := C.terminal_eq
          rw [hC] at hterm
          exact Option.some.inj hterm
        exact False.elim (hxy (hi.symm.trans ht))
    | finite Q => exact ⟨Q, rfl⟩
    | infinite Q =>
        have hterm := C.terminal_eq
        simp [hC] at hterm
  have hSwitchQ : IsSwitchingAlternating L.ladder.paths (.finite Q) := by
    simpa [hCQ] using hSwitch
  have hQi : (AltPath.finite Q).initial = T.initial := by
    rw [← hCQ]
    exact C.initial_eq
  have hQt : (AltPath.finite Q).terminal? = some T.terminal := by
    rw [← hCQ]
    exact C.terminal_eq
  have hxIncoming : HasIncoming
      (Alternating.familyEdges L.ladder.paths) T.initial :=
    Q.reducing_start_hasIncoming hSwitchQ.isAlternating hx hQi
  have hyOutgoing : HasOutgoing
      (Alternating.familyEdges L.ladder.paths) T.terminal :=
    Q.reducing_terminal_hasOutgoing hSwitchQ.isAlternating hy hQt
  have hxnotiso : T.initial ∉ isolatedVertices L.ladder.paths :=
    fun hiso ↦
      (not_hasIncoming_of_mem_isolatedVertices L.ladder.disjoint hiso)
        hxIncoming
  have hynotiso : T.terminal ∉ isolatedVertices L.ladder.paths :=
    fun hiso ↦
      (not_hasOutgoing_of_mem_isolatedVertices L.ladder.disjoint hiso)
        hyOutgoing
  have hxbal : edgeBalance
      (Alternating.familyEdges L.ladder.paths) T.initial = -1 :=
    ((mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one_anyWarp
      L.ladder.disjoint).1 hx).resolve_left hxnotiso
  have hybal : edgeBalance
      (Alternating.familyEdges L.ladder.paths) T.terminal = 1 :=
    ((mem_initialSet_iff_isolated_or_edgeBalance_eq_one_anyWarp
      L.ladder.disjoint).1 hy).resolve_left hynotiso
  have hyx : T.terminal ≠ T.initial := hxy.symm
  have hbalance : ∀ z,
      edgeBalance (Alternating.familyEdges W) z =
        edgeBalance (Alternating.familyEdges L.ladder.paths) z +
          propInt (z = T.initial) - propInt (z = T.terminal) := by
    intro z
    rw [hWapp.2.1, Cyclowarp.application_edges]
    rw [hCQ]
    have hd := Q.hasReducingBalanceDelta hSwitchQ z
    have hi : Q.initial = T.initial := hQi
    have ht : Q.terminal = T.terminal := Option.some.inj hQt
    simpa [hi, ht] using hd
  have hiso : isolatedVertices W = isolatedVertices L.ladder.paths := by
    exact hWapp.2.2
  constructor
  · ext z
    simp only [Set.mem_diff, Set.mem_singleton_iff]
    rw [mem_initialSet_iff_isolated_or_edgeBalance_eq_one_anyWarp hW.1,
      mem_initialSet_iff_isolated_or_edgeBalance_eq_one_anyWarp
        L.ladder.disjoint,
      hiso, hbalance]
    by_cases hzx : z = T.initial
    · subst z
      simp [propInt, hxy, hxnotiso, hxbal]
    · by_cases hzy : z = T.terminal
      · subst z
        simp [propInt, hxy, hyx, hynotiso, hybal]
      · simp [propInt, hzx, hzy]
  · ext z
    simp only [Set.mem_diff, Set.mem_singleton_iff]
    rw [mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one_anyWarp
        hW.1,
      mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one_anyWarp
        L.ladder.disjoint,
      hiso, hbalance]
    by_cases hzx : z = T.initial
    · subst z
      simp [propInt, hxy, hxnotiso, hxbal]
    · by_cases hzy : z = T.terminal
      · subst z
        simp [propInt, hxy, hyx, hynotiso, hybal]
      · simp [propInt, hzx, hzy]

end PopularAuxiliary.Input
end Erdos599
