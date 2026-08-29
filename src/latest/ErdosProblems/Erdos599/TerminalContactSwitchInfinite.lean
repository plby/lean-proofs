/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.TerminalContactSwitch
import ErdosProblems.Erdos599.SafeSwitchingAssembly
import ErdosProblems.Erdos599.PathFilterComponents
import ErdosProblems.Erdos599.RayCompatibleRelationDecomposition

/-!
# Terminal-contact switching for arbitrary path/ray warps

The finite terminal-contact theorem is not enough for the limiting ladder in
Section 8, whose members may be rays.  This file proves the incidence
description of the two frontiers for an arbitrary warp and combines it with
the ray-permitting decomposition of an acyclic locally bi-unique relation.

Directed cycles and reverse directed rays are the exact component
obstructions to the decomposition.  Forward directed rays are retained as
ray members of the resulting warp.
-/

noncomputable section

open Set

namespace Erdos599
namespace Alternating

open DirectedPath RelationDecomposition

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace TerminalContactSwitch

private theorem walk_eq_nil_of_isPath {D : Digraph V} {x : V}
    (p : Walk D x x) (hp : p.IsPath) : p = .nil := by
  cases p with
  | nil => rfl
  | @cons _ y _ h q =>
      exact False.elim ((List.nodup_cons.mp hp).1 q.end_mem_support)

private theorem finitePath_eq_trivial_of_start_eq_finish
    {D : Digraph V} (p : FinitePath D) (h : p.start = p.finish) :
    p = FinitePath.trivial D p.start := by
  rcases p with ⟨start, finish, walk, isPath⟩
  dsimp at h ⊢
  subst finish
  have hw : walk = .nil := walk_eq_nil_of_isPath walk isPath
  subst walk
  rfl

/-- The carrier of an arbitrary warp is its isolated vertices together with
the vertices incident with a family edge.  This includes ray members. -/
theorem vertexSet_eq_isolated_union_incident_anyWarp
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W) :
    Gamma.vertexSet W = isolatedVertices W ∪
      {x | HasIncoming (familyEdges W) x ∨
        HasOutgoing (familyEdges W) x} := by
  ext x
  constructor
  · rintro ⟨p, hpW, hxp⟩
    rcases p with p | r
    · by_cases hends : p.start = p.finish
      · left
        have hp0 := finitePath_eq_trivial_of_start_eq_finish p hends
        have hp0' : (Sum.inl p : Gamma.DPath) =
            Gamma.trivialPath p.start := by
          rw [hp0]
          rfl
        rw [hp0'] at hpW hxp
        have hx : x = p.start := by simpa using hxp
        subst x
        exact hpW
      · by_cases hxstart : x = p.start
        · right
          right
          subst x
          rcases FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
              p p.start_mem_support hends with ⟨y, hy⟩
          exact ⟨y, by
            simp only [familyEdges, Set.mem_iUnion]
            exact ⟨Sum.inl p, hpW, hy⟩⟩
        · right
          left
          rcases FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
              p hxp hxstart with ⟨y, hy⟩
          exact ⟨y, by
            simp only [familyEdges, Set.mem_iUnion]
            exact ⟨Sum.inl p, hpW, hy⟩⟩
    · rcases hxp with ⟨n, rfl⟩
      cases n with
      | zero =>
          right
          right
          exact ⟨r 1, by
            simp only [familyEdges, Set.mem_iUnion]
            exact ⟨Sum.inr r, hpW, ⟨0, rfl⟩⟩⟩
      | succ n =>
          right
          left
          exact ⟨r n, by
            simp only [familyEdges, Set.mem_iUnion]
            exact ⟨Sum.inr r, hpW, ⟨n, rfl⟩⟩⟩
  · rintro (hxiso | hxinc)
    · exact isolatedVertices_subset_vertexSet W hxiso
    · rcases hxinc with ⟨y, hy⟩ | ⟨y, hy⟩
      · simp only [familyEdges, Set.mem_iUnion] at hy
        rcases hy with ⟨p, hpW, hyp⟩
        exact ⟨p, hpW, (p.edgeSet_subset_support_prod hyp).2⟩
      · simp only [familyEdges, Set.mem_iUnion] at hy
        rcases hy with ⟨p, hpW, hyp⟩
        exact ⟨p, hpW, (p.edgeSet_subset_support_prod hyp).1⟩

/-- Initial vertices of an arbitrary path/ray warp are exactly the carrier
vertices without an incoming family edge. -/
theorem initialSet_eq_vertexSet_diff_hasIncoming_anyWarp
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W) :
    Gamma.initialSet W =
      Gamma.vertexSet W \ {x | HasIncoming (familyEdges W) x} := by
  ext x
  constructor
  · rintro ⟨p, hpW, rfl⟩
    refine ⟨⟨p, hpW, p.initial_mem_support⟩, ?_⟩
    rintro ⟨y, hy⟩
    simp only [familyEdges, Set.mem_iUnion] at hy
    rcases hy with ⟨q, hqW, hyq⟩
    have hxq : p.initial ∈ q.support :=
      (q.edgeSet_subset_support_prod hyq).2
    have hpq : p = q :=
      DWeb.IsWarp.eq_of_mem_support hW hpW hqW p.initial_mem_support hxq
    subst q
    rcases p with p | r
    · exact FinitePath.no_incoming_edge_at_start p y hyq
    · rcases hyq with ⟨n, hn⟩
      have hzero : n + 1 = 0 := by
        apply r.injective
        exact (congrArg Prod.snd hn).symm
      omega
  · rintro ⟨⟨p, hpW, hxp⟩, hxno⟩
    refine ⟨p, hpW, ?_⟩
    by_contra hpinitial
    have hne : x ≠ p.initial := fun h ↦ hpinitial h.symm
    rcases p with p | r
    · obtain ⟨y, hyx⟩ :=
        FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
          p hxp hne
      exact hxno ⟨y, by
        simp only [familyEdges, Set.mem_iUnion]
        exact ⟨Sum.inl p, hpW, hyx⟩⟩
    · obtain ⟨n, hn⟩ := hxp
      cases n with
      | zero => exact hne (by simpa [Path.initial, Ray.initial] using hn.symm)
      | succ n =>
          exact hxno ⟨r n, by
            simp only [familyEdges, Set.mem_iUnion]
            exact ⟨Sum.inr r, hpW, ⟨n, by
              exact Prod.ext rfl hn.symm⟩⟩⟩

/-- Finite terminals of an arbitrary path/ray warp are exactly the carrier
vertices without an outgoing family edge. -/
theorem terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W) :
    Gamma.terminalFrontier W =
      Gamma.vertexSet W \ {x | HasOutgoing (familyEdges W) x} := by
  ext x
  constructor
  · intro hx
    refine ⟨⟨hx.choose, hx.choose_spec.1,
      Gamma.terminal_mem_support hx.choose_spec.2⟩, ?_⟩
    rintro ⟨y, hxy⟩
    obtain ⟨p, hpW, hpterm⟩ := hx
    simp only [familyEdges, Set.mem_iUnion] at hxy
    rcases hxy with ⟨q, hqW, hxyq⟩
    have hxp : x ∈ p.support := Gamma.terminal_mem_support hpterm
    have hxq : x ∈ q.support := (q.edgeSet_subset_support_prod hxyq).1
    have hpq : p = q :=
      DWeb.IsWarp.eq_of_mem_support hW hpW hqW hxp hxq
    subst q
    rcases p with p | r
    · have hpfinish : p.finish = x := by
        simpa [DWeb.terminal?, Path.terminal?] using hpterm
      exact FinitePath.no_outgoing_edge_at_finish p y (hpfinish ▸ hxyq)
    · simp [DWeb.terminal?, Path.terminal?] at hpterm
  · rintro ⟨⟨p, hpW, hxp⟩, hxno⟩
    rcases p with p | r
    · have hfinish : x = p.finish := by
        by_contra hne
        obtain ⟨y, hxy⟩ :=
          FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
            p hxp hne
        exact hxno ⟨y, by
          simp only [familyEdges, Set.mem_iUnion]
          exact ⟨Sum.inl p, hpW, hxy⟩⟩
      exact ⟨Sum.inl p, hpW, by
        simp [DWeb.terminal?, Path.terminal?, hfinish]⟩
    · obtain ⟨n, rfl⟩ := hxp
      exact False.elim <| hxno ⟨r (n + 1), by
        simp only [familyEdges, Set.mem_iUnion]
        exact ⟨Sum.inr r, hpW, ⟨n, rfl⟩⟩⟩

theorem mem_initialSet_iff_isolated_or_edgeBalance_eq_one_anyWarp
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W) {x : V} :
    x ∈ Gamma.initialSet W ↔
      x ∈ isolatedVertices W ∨ edgeBalance (familyEdges W) x = 1 := by
  rw [initialSet_eq_vertexSet_diff_hasIncoming_anyWarp hW,
    vertexSet_eq_isolated_union_incident_anyWarp hW]
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq,
    edgeBalance_eq_one_iff]
  constructor
  · rintro ⟨hxiso | hin | hout, hnin⟩
    · exact Or.inl hxiso
    · exact False.elim (hnin hin)
    · exact Or.inr ⟨hout, hnin⟩
  · rintro (hxiso | ⟨hout, hnin⟩)
    · exact ⟨Or.inl hxiso,
        not_hasIncoming_of_mem_isolatedVertices hW hxiso⟩
    · exact ⟨Or.inr (Or.inr hout), hnin⟩

theorem mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one_anyWarp
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W) {x : V} :
    x ∈ Gamma.terminalFrontier W ↔
      x ∈ isolatedVertices W ∨ edgeBalance (familyEdges W) x = -1 := by
  rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp hW,
    vertexSet_eq_isolated_union_incident_anyWarp hW]
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq,
    edgeBalance_eq_neg_one_iff]
  constructor
  · rintro ⟨hxiso | hin | hout, hnout⟩
    · exact Or.inl hxiso
    · exact Or.inr ⟨hin, hnout⟩
    · exact False.elim (hnout hout)
  · rintro (hxiso | ⟨hin, hnout⟩)
    · exact ⟨Or.inl hxiso,
        not_hasOutgoing_of_mem_isolatedVertices hW hxiso⟩
    · exact ⟨Or.inr (Or.inl hin), hnout⟩

/-- Adding finitely many edges to a relation without reverse directed rays
cannot create a reverse directed ray.  Indeed, the edges of a reverse ray
are pairwise distinct, so a tail of the ray avoids the finite perturbation. -/
theorem not_containsReverseDirectedRay_of_subset_union_finite
    {B F E : Set (V × V)}
    (hE : E ⊆ B ∪ F)
    (hB : ¬ ContainsReverseDirectedRay B)
    (hF : F.Finite) :
    ¬ ContainsReverseDirectedRay E := by
  rintro ⟨R, hR⟩
  let edge : ℕ → V × V :=
    fun n ↦ (R.vertex (n + 1), R.vertex n)
  have hedgeInjective : Function.Injective edge := by
    intro i j hij
    apply R.injective
    exact congrArg Prod.snd hij
  have hbadFinite : (edge ⁻¹' F).Finite :=
    Set.Finite.preimage hedgeInjective.injOn hF
  obtain ⟨N, hN⟩ := hbadFinite.bddAbove
  apply hB
  let T : DirectedRay V :=
    { vertex := fun n ↦ R.vertex (N + 1 + n)
      injective := fun _ _ h ↦
        Nat.add_left_cancel (R.injective h) }
  refine ⟨T, ?_⟩
  intro n
  have heE : edge (N + 1 + n) ∈ E := by
    simpa [edge, Nat.add_assoc] using hR (N + 1 + n)
  have heUnion := hE heE
  have heNotF : edge (N + 1 + n) ∉ F := by
    intro heF
    have hle : N + 1 + n ≤ N := hN heF
    omega
  simpa [T, edge, Nat.add_assoc] using heUnion.resolve_right heNotF

/-- A finite terminal-contact modification of an arbitrary warp cannot
create a reverse directed ray.  This removes the reverse-ray premise from
the ray-permitting realization theorem. -/
theorem terminalContact_switchedEdges_not_containsReverseDirectedRay
    (Z : Set Gamma.DPath) (Q : FiniteTrace Gamma.graph) (u : V)
    (hQ : IsTerminalContactSwitching Z Q u) :
    ¬ ContainsReverseDirectedRay (switchedEdges Z (.finite Q)) := by
  apply not_containsReverseDirectedRay_of_subset_union_finite
      (B := familyEdges Z)
      (F := (AltPath.finite Q).directionEdges .forward)
  · rw [FiniteTrace.switchedEdges_eq_backward_sdiff_union_forward Q hQ]
    exact Set.union_subset_union Set.diff_subset Set.Subset.rfl
  · exact
      _root_.Erdos599.PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsReverseDirectedRay
        hQ.warp
  · have hfin : (AltPath.finite Q).edgeSet.Finite := by
      simpa only [AltPath.edgeSet, AltPath.links, FiniteTrace.links] using
        Q.edgeSet_finite
    apply hfin.subset
    rw [(AltPath.finite Q).edgeSet_eq_directionEdges_union]
    exact Set.subset_union_left

/-! ## Discarding cyclic components -/

/-- The union of all directed-cycle edges of a relation. -/
def cyclicEdges (E : Set (V × V)) : Set (V × V) :=
  {e | ∃ C : DirectedCycle V, C.EdgeSet ⊆ E ∧ e ∈ C.EdgeSet}

theorem cyclicEdges_subset (E : Set (V × V)) : cyclicEdges E ⊆ E := by
  rintro e ⟨C, hCE, heC⟩
  exact hCE heC

theorem hasOutgoing_cyclicEdges_iff_hasIncoming
    (E : Set (V × V)) (x : V) :
    HasOutgoing (cyclicEdges E) x ↔ HasIncoming (cyclicEdges E) x := by
  constructor
  · rintro ⟨y, C, hCE, hxyC⟩
    obtain ⟨z, hzxC⟩ := C.hasIncoming_of_mem_edgeSet_source hxyC
    exact ⟨z, C, hCE, hzxC⟩
  · rintro ⟨y, C, hCE, hyxC⟩
    obtain ⟨z, hxzC⟩ := C.hasOutgoing_of_mem_edgeSet_target hyxC
    exact ⟨z, C, hCE, hxzC⟩

theorem hasOutgoing_sdiff_cyclicEdges_iff
    {E : Set (V × V)}
    (hout : Relator.RightUnique (fun x y ↦ (x, y) ∈ E)) (x : V) :
    HasOutgoing (E \ cyclicEdges E) x ↔
      HasOutgoing E x ∧ ¬ HasOutgoing (cyclicEdges E) x := by
  constructor
  · rintro ⟨y, hyE, hyCycle⟩
    refine ⟨⟨y, hyE⟩, ?_⟩
    rintro ⟨z, hzCycle⟩
    have hyz : y = z := hout hyE (cyclicEdges_subset E hzCycle)
    subst z
    exact hyCycle hzCycle
  · rintro ⟨⟨y, hyE⟩, hnoCycle⟩
    exact ⟨y, hyE, fun hyCycle ↦ hnoCycle ⟨y, hyCycle⟩⟩

theorem hasIncoming_sdiff_cyclicEdges_iff
    {E : Set (V × V)}
    (hin : Relator.LeftUnique (fun x y ↦ (x, y) ∈ E)) (x : V) :
    HasIncoming (E \ cyclicEdges E) x ↔
      HasIncoming E x ∧ ¬ HasIncoming (cyclicEdges E) x := by
  constructor
  · rintro ⟨y, hyE, hyCycle⟩
    refine ⟨⟨y, hyE⟩, ?_⟩
    rintro ⟨z, hzCycle⟩
    have hyz : y = z := hin hyE (cyclicEdges_subset E hzCycle)
    subst z
    exact hyCycle hzCycle
  · rintro ⟨⟨y, hyE⟩, hnoCycle⟩
    exact ⟨y, hyE, fun hyCycle ↦ hnoCycle ⟨y, hyCycle⟩⟩

theorem edgeBalance_sdiff_cyclicEdges
    {E : Set (V × V)}
    (hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E)) (x : V) :
    edgeBalance (E \ cyclicEdges E) x = edgeBalance E x := by
  rw [edgeBalance, edgeBalance,
    hasOutgoing_sdiff_cyclicEdges_iff hunique.2,
    hasIncoming_sdiff_cyclicEdges_iff hunique.1]
  have hcycle := hasOutgoing_cyclicEdges_iff_hasIncoming E x
  classical
  by_cases houtC : HasOutgoing (cyclicEdges E) x
  · have hinC : HasIncoming (cyclicEdges E) x := hcycle.mp houtC
    have houtE : HasOutgoing E x := by
      obtain ⟨y, hy⟩ := houtC
      exact ⟨y, cyclicEdges_subset E hy⟩
    have hinE : HasIncoming E x := by
      obtain ⟨y, hy⟩ := hinC
      exact ⟨y, cyclicEdges_subset E hy⟩
    simp [propInt, houtE, hinE, houtC, hinC]
  · have hinC : ¬ HasIncoming (cyclicEdges E) x := by
      exact fun h ↦ houtC (hcycle.mpr h)
    simp [propInt, houtC, hinC]

theorem sdiff_cyclicEdges_not_containsDirectedCycle (E : Set (V × V)) :
    ¬ ContainsDirectedCycle (E \ cyclicEdges E) := by
  rintro ⟨C, hC⟩
  let i : Fin C.length := ⟨0, C.positive⟩
  have he := hC (show (C.vertex i, C.vertex (C.next i)) ∈ C.EdgeSet from
    ⟨i, rfl⟩)
  apply he.2
  exact ⟨C, fun e heC ↦ (hC heC).1, ⟨i, rfl⟩⟩

/-- Any locally bi-unique relation without a reverse ray has a path/ray warp
realization after its directed-cycle components are discarded.  Discarding
those components preserves edge balance and prescribed isolated vertices. -/
theorem exists_warp_realizing_biUnique_up_to_cycles_with_isolated
    (E : Set (V × V)) (I : Set V)
    (hgraph : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E))
    (hReverseRay : ¬ ContainsReverseDirectedRay E)
    (hI : ∀ x ∈ I, ∀ y, (x, y) ∉ E ∧ (y, x) ∉ E) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsWarp W ∧ isolatedVertices W = I ∧
        ∀ x, edgeBalance (familyEdges W) x = edgeBalance E x := by
  let E' := E \ cyclicEdges E
  have hunique' : Relator.BiUnique (fun x y ↦ (x, y) ∈ E') :=
    ⟨fun _ _ _ hx hy ↦ hunique.1 hx.1 hy.1,
      fun _ _ _ hx hy ↦ hunique.2 hx.1 hy.1⟩
  obtain ⟨W, hW, hWE, hWI⟩ :=
    RayCompatibleRelationDecomposition.exists_warp_realizing_biUnique_with_isolated
      Gamma E' I
      (fun _ he ↦ hgraph he.1) hunique'
      (sdiff_cyclicEdges_not_containsDirectedCycle E)
      (fun h ↦ hReverseRay ⟨h.choose, fun n ↦ (h.choose_spec n).1⟩)
      (fun x hx y ↦ ⟨fun h ↦ (hI x hx y).1 h.1,
        fun h ↦ (hI x hx y).2 h.1⟩)
  refine ⟨W, hW, hWI, ?_⟩
  intro x
  rw [hWE]
  exact edgeBalance_sdiff_cyclicEdges hunique x

/-- Unconditional ray-permitting realization of a finite terminal-contact
switch on an arbitrary path/ray warp.  Forward-ray components are retained;
directed-cycle components are discarded, which does not change edge balance
or either frontier. -/
theorem exists_terminalContactSwitch_anyWarp
    (Z : Set Gamma.DPath) (Q : FiniteTrace Gamma.graph) (u v : V)
    (hQ : IsTerminalContactSwitching Z Q u)
    (hv : v ∈ Gamma.terminalFrontier Z) (hQi : Q.initial = v) :
    ∃ Z' : Set Gamma.DPath,
      Gamma.IsWarp Z' ∧
        Gamma.initialSet Z' = Gamma.initialSet Z \ {u} ∧
        Gamma.terminalFrontier Z' = Gamma.terminalFrontier Z \ {v} := by
  classical
  let E := switchedEdges Z (.finite Q)
  let I := isolatedVertices Z \ {u}
  have hI : ∀ x ∈ I, ∀ y, (x, y) ∉ E ∧ (y, x) ∉ E := by
    intro x hx y
    have hno :=
      _root_.Erdos599.Alternating.TerminalContactSwitch.isolated_not_incident_switched
        Q hQ hx.1 hx.2
    exact ⟨fun hxy ↦ hno.2 ⟨y, hxy⟩,
      fun hyx ↦ hno.1 ⟨y, hyx⟩⟩
  have hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E) := by
    exact ⟨
      fun _ _ _ hxz hyz ↦
        _root_.Erdos599.Alternating.TerminalContactSwitch.FiniteTrace.switchedEdges_in_unique
          Q hQ hxz hyz,
      fun _ _ _ hxy hxz ↦
        _root_.Erdos599.Alternating.TerminalContactSwitch.FiniteTrace.switchedEdges_out_unique
          Q hQ hxy hxz⟩
  obtain ⟨Z', hZ', hIso, hEdgesBalance⟩ :=
    exists_warp_realizing_biUnique_up_to_cycles_with_isolated
      (Gamma := Gamma) E I
      (by simpa [E] using
        (Cyclowarp.application Z (.finite Q)).edges_in_graph)
      hunique
      (by simpa [E] using
        terminalContact_switchedEdges_not_containsReverseDirectedRay Z Q u hQ)
      hI
  refine ⟨Z', hZ', ?_⟩
  have hvin := start_hasIncoming Q hQ hv hQi
  have hvniso := not_isolated_of_hasIncoming hQ.warp hvin
  have hvbal : edgeBalance (familyEdges Z) v = -1 :=
    (mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one_anyWarp
      hQ.warp).1 hv |>.resolve_left hvniso
  have hvu : v ≠ u := by
    intro h
    subst u
    have hu := hQ.terminal_mem_initialSet
    rw [initialSet_eq_vertexSet_diff_hasIncoming_anyWarp hQ.warp] at hu
    exact hu.2 hvin
  have huv : u ≠ v := hvu.symm
  have hbalance : ∀ x,
      edgeBalance (familyEdges Z') x = edgeBalance (familyEdges Z) x +
        propInt (x = v) - propInt (x = u) := by
    intro x
    rw [hEdgesBalance]
    change edgeBalance (switchedEdges Z (.finite Q)) x = _
    rw [_root_.Erdos599.Alternating.TerminalContactSwitch.FiniteTrace.hasTerminalContactBalanceDelta
      Q hQ, hQi, hQ.terminal_eq]
  rcases hQ.terminal_outgoing_or_isolated with huout | huisolated
  · have huniso := not_isolated_of_hasOutgoing hQ.warp huout
    have hubal : edgeBalance (familyEdges Z) u = 1 :=
      (mem_initialSet_iff_isolated_or_edgeBalance_eq_one_anyWarp
        hQ.warp).1 hQ.terminal_mem_initialSet |>.resolve_left huniso
    have hIso' : isolatedVertices Z' = isolatedVertices Z := by
      rw [hIso]
      ext x
      simp only [I, Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · exact fun hx ↦ hx.1
      · intro hx
        exact ⟨hx, fun hxu ↦ huniso (hxu ▸ hx)⟩
    constructor
    · ext x
      rw [mem_initialSet_iff_isolated_or_edgeBalance_eq_one_anyWarp hZ']
      simp only [Set.mem_sdiff, Set.mem_singleton_iff]
      rw [mem_initialSet_iff_isolated_or_edgeBalance_eq_one_anyWarp hQ.warp,
        hIso', hbalance]
      by_cases hxv : x = v
      · subst x
        simp [propInt, hvniso, hvbal, hvu]
      · by_cases hxu : x = u
        · subst x
          simp [propInt, huniso, hubal, huv]
        · simp [propInt, hxv, hxu]
    · ext x
      rw [mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one_anyWarp
        hZ']
      simp only [Set.mem_sdiff, Set.mem_singleton_iff]
      rw [mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one_anyWarp
        hQ.warp, hIso', hbalance]
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
      rw [mem_initialSet_iff_isolated_or_edgeBalance_eq_one_anyWarp hZ']
      simp only [Set.mem_sdiff, Set.mem_singleton_iff]
      rw [mem_initialSet_iff_isolated_or_edgeBalance_eq_one_anyWarp hQ.warp,
        hIso, hbalance]
      by_cases hxv : x = v
      · subst x
        simp [I, propInt, hvniso, hvbal, hvu]
      · by_cases hxu : x = u
        · subst x
          simp [I, propInt, huisolated, hubal, huv]
        · simp [I, propInt, hxv, hxu]
    · ext x
      rw [mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one_anyWarp
        hZ']
      simp only [Set.mem_sdiff, Set.mem_singleton_iff]
      rw [mem_terminalFrontier_iff_isolated_or_edgeBalance_eq_neg_one_anyWarp
        hQ.warp, hIso, hbalance]
      by_cases hxv : x = v
      · subst x
        simp [I, propInt, hvniso, hvbal, hvu]
      · by_cases hxu : x = u
        · subst x
          simp [I, propInt, huisolated, hubal, huv]
        · simp [I, propInt, hxv, hxu]

/-- Backwards-compatible acyclic wrapper.  The component premises are no
longer needed: reverse rays are excluded by finite perturbation and directed
cycles are discarded. -/
theorem exists_terminalContactSwitch_of_acyclic
    (Z : Set Gamma.DPath) (Q : FiniteTrace Gamma.graph) (u v : V)
    (hQ : IsTerminalContactSwitching Z Q u)
    (hv : v ∈ Gamma.terminalFrontier Z) (hQi : Q.initial = v)
    (_hcycle : ¬ ContainsDirectedCycle (switchedEdges Z (.finite Q)))
    (_hReverseRay :
      ¬ ContainsReverseDirectedRay (switchedEdges Z (.finite Q))) :
    ∃ Z' : Set Gamma.DPath,
      Gamma.IsWarp Z' ∧
        Gamma.initialSet Z' = Gamma.initialSet Z \ {u} ∧
        Gamma.terminalFrontier Z' = Gamma.terminalFrontier Z \ {v} :=
  exists_terminalContactSwitch_anyWarp Z Q u v hQ hv hQi

/-- Backwards-compatible wrapper retaining the former no-cycle premise. -/
theorem exists_terminalContactSwitch_of_noDirectedCycle
    (Z : Set Gamma.DPath) (Q : FiniteTrace Gamma.graph) (u v : V)
    (hQ : IsTerminalContactSwitching Z Q u)
    (hv : v ∈ Gamma.terminalFrontier Z) (hQi : Q.initial = v)
    (hcycle : ¬ ContainsDirectedCycle (switchedEdges Z (.finite Q))) :
    ∃ Z' : Set Gamma.DPath,
      Gamma.IsWarp Z' ∧
        Gamma.initialSet Z' = Gamma.initialSet Z \ {u} ∧
        Gamma.terminalFrontier Z' = Gamma.terminalFrontier Z \ {v} := by
  exact exists_terminalContactSwitch_anyWarp Z Q u v hQ hv hQi

end TerminalContactSwitch
end Alternating
end Erdos599

#print axioms Erdos599.Alternating.TerminalContactSwitch.exists_terminalContactSwitch_of_acyclic
#print axioms Erdos599.Alternating.TerminalContactSwitch.exists_terminalContactSwitch_of_noDirectedCycle
#print axioms Erdos599.Alternating.TerminalContactSwitch.exists_terminalContactSwitch_anyWarp
