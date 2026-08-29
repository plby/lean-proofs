/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayStageGeometry

/-!
# The concrete inside-fragment union in Assertion 9.31

The outside-fragment simultaneous assignment does not by itself determine
the splice in Assertion 9.31.  The other input is the family of pieces of the
`T_alpha`--`T_beta` linkage which lie inside the closed set.  This file keeps
that family as an actual linkage blueprint, rather than as an arbitrary edge
relation.

From the warp property of the inside family we derive graph containment,
endpoint containment, and bi-uniqueness of its edge union.  The attachment
conditions say exactly that a finite assigned edge leaves a terminal of an
inside fragment and enters an initial of an inside fragment.  They imply the
two cross-incidence conditions automatically.  Similarly, the root and sink
boundary of the full union is derived from the initial/terminal boundary of
the concrete inside family.

The remaining fields of `ConcreteInsideFragmentSplice` are genuinely global
geometry: the construction rank, the strong-edge condition, the old-family
accounting formula, and the distinguished real path.  None of these follows
from the fractured assignment alone.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}

/-! ## Roots and sinks of an actual blueprint -/

/-- A terminal of a blueprint has no outgoing edge in its edge union. -/
theorem no_outgoing_of_mem_terminalSet
    (F : LinkageBlueprint Gamma Y kappa) {x : V}
    (hx : x ∈ F.terminalSet) : ¬ ∃ y, (x, y) ∈ F.edgeSet := by
  rintro ⟨y, hxy⟩
  obtain ⟨p, hpF, hpterm⟩ := hx
  simp only [edgeSet, Set.mem_iUnion] at hxy
  obtain ⟨q, hqF, hxyq⟩ := hxy
  have hxp : x ∈ p.support := by
    rcases p with p | r
    · have hpfinish : p.finish = x := by
        simpa [DWeb.terminal?, DirectedPath.Path.terminal?] using hpterm
      exact hpfinish ▸ p.finish_mem_support
    · simp [DWeb.terminal?, DirectedPath.Path.terminal?] at hpterm
  have hxq : x ∈ q.support :=
    (q.edgeSet_subset_support_prod hxyq).1
  have hpq : p = q :=
    F.path_eq_of_mem_support hpF hqF hxp hxq
  subst q
  rcases p with p | r
  · have hpfinish : p.finish = x := by
      simpa [DWeb.terminal?, DirectedPath.Path.terminal?] using hpterm
    exact Alternating.FinitePath.no_outgoing_edge_at_finish p y
      (hpfinish ▸ hxyq)
  · simp [DWeb.terminal?, DirectedPath.Path.terminal?] at hpterm

/-- An initial of a blueprint has no incoming edge in its edge union. -/
theorem no_incoming_of_mem_initialSet
    (F : LinkageBlueprint Gamma Y kappa) {x : V}
    (hx : x ∈ F.initialSet) : ¬ ∃ y, (y, x) ∈ F.edgeSet := by
  rintro ⟨y, hyx⟩
  obtain ⟨p, hpF, hpinitial⟩ := hx
  simp only [edgeSet, Set.mem_iUnion] at hyx
  obtain ⟨q, hqF, hyxq⟩ := hyx
  have hxp : x ∈ p.support := hpinitial.symm ▸ p.initial_mem_support
  have hxq : x ∈ q.support :=
    (q.edgeSet_subset_support_prod hyxq).2
  have hpq : p = q :=
    F.path_eq_of_mem_support hpF hqF hxp hxq
  subst q
  rcases p with p | r
  · have hpstart : p.start = x := by
      simpa [DirectedPath.Path.initial] using hpinitial
    exact Alternating.FinitePath.no_incoming_edge_at_start p y
      (hpstart ▸ hyxq)
  · obtain ⟨n, hn⟩ := hyxq
    have hzero : n + 1 = 0 := by
      apply r.injective
      calc
        r (n + 1) = x := (congrArg Prod.snd hn).symm
        _ = r.initial := hpinitial.symm
        _ = r 0 := rfl
    omega

/-- The terminal frontier of an actual blueprint is exactly its carrier
vertices with no outgoing inside-fragment edge. -/
theorem terminalSet_eq_no_outgoing
    (F : LinkageBlueprint Gamma Y kappa) :
    F.terminalSet =
      {x | x ∈ F.vertexSet ∧ ¬ ∃ y, (x, y) ∈ F.edgeSet} := by
  ext x
  constructor
  · intro hx
    have hx' := hx
    obtain ⟨p, hpF, hpterm⟩ := hx
    exact ⟨⟨p, hpF, (imaginaryWeb Gamma Y kappa).terminal_mem_support hpterm⟩,
      F.no_outgoing_of_mem_terminalSet hx'⟩
  · rintro ⟨hxcarrier, hnoout⟩
    by_contra hxterm
    exact hnoout (F.exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet
      hxcarrier hxterm)

/-- The initial set of an actual blueprint is exactly its carrier vertices
with no incoming inside-fragment edge. -/
theorem initialSet_eq_no_incoming
    (F : LinkageBlueprint Gamma Y kappa) :
    F.initialSet =
      {x | x ∈ F.vertexSet ∧ ¬ ∃ y, (y, x) ∈ F.edgeSet} := by
  ext x
  constructor
  · intro hx
    have hx' := hx
    obtain ⟨p, hpF, hpinitial⟩ := hx
    exact ⟨⟨p, hpF, hpinitial.symm ▸ p.initial_mem_support⟩,
      F.no_incoming_of_mem_initialSet hx'⟩
  · rintro ⟨hxcarrier, hnoin⟩
    obtain ⟨p, hpF, hxp⟩ := hxcarrier
    refine ⟨p, hpF, ?_⟩
    by_contra hpinitial
    have hne : x ≠ p.initial := by
      intro h
      exact hpinitial h.symm
    rcases p with p | r
    · obtain ⟨y, hy⟩ :=
        Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
          p hxp hne
      exact hnoin ⟨y, Set.mem_iUnion.2 ⟨Sum.inl p,
        Set.mem_iUnion.2 ⟨hpF, hy⟩⟩⟩
    · obtain ⟨n, hn⟩ := hxp
      have hnpos : 0 < n := by
        by_contra hnzero
        have : n = 0 := Nat.eq_zero_of_not_pos hnzero
        exact hne (by simpa [DirectedPath.Path.initial, Ray.initial, this]
          using hn.symm)
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
      exact hnoin ⟨r m, Set.mem_iUnion.2 ⟨Sum.inr r,
        Set.mem_iUnion.2 ⟨hpF, ⟨m, by
          exact Prod.ext rfl hn.symm⟩⟩⟩⟩

/-! ## Concrete inside-fragment data -/

/-- The actual data returned by the inside/outside decomposition of the
`T_alpha`--`T_beta` linkage.

The edge relation and carrier are not fields: they are definitionally the
edge union and vertex set of `insideFamily`.  Endpoint attachment is stated
using its genuine initial and terminal sets. -/
structure ConcreteInsideFragmentSplice
    (C : ClubStageGeometry Gamma Y kappa theta)
    (W : LinkageBlueprint Gamma Y kappa)
    {Zf : FracturedWarp Gamma}
    (A : SimultaneousAssignment Zf.paths Y) (u : V) where
  insideFamily : LinkageBlueprint Gamma Y kappa
  finite_sources_terminal : ∀ s v,
    (A.assigned s).terminal? = some v →
      s.1 ∈ insideFamily.terminalSet
  finite_targets_initial : ∀ s v,
    (A.assigned s).terminal? = some v →
      v ∈ insideFamily.initialSet
  infinite_sources_terminal : assignedInfiniteSources A ⊆
    insideFamily.terminalSet
  terminal_boundary : insideFamily.terminalSet ⊆
    {x | ∃ s : {z // z ∈
      Gamma.initialSet Zf.paths \ Gamma.initialSet Y}, s.1 = x} ∪
      C.newSlice
  carrier_roofed : insideFamily.vertexSet ⊆ C.outerRoof
  covers_source : Gamma.source ⊆
    insideFamily.initialSet ∪
      Gamma.initialSet
        (referencePathsMeeting Y C.newSlice \
          referencePathsMeeting Y insideFamily.vertexSet)
  covered_initial_not_assigned_target :
    Gamma.source ∩ insideFamily.initialSet ⊆
      {x | ¬ ∃ y, (y, x) ∈ assignedFiniteEdges A}
  carrier_closed : insideFamily.vertexSet ⊆ C.closedSet
  card_paths : #insideFamily.paths ≤ kappa
  rank : V → Nat
  inside_rank : ∀ {x y}, (x, y) ∈ insideFamily.edgeSet → rank x < rank y
  assigned_rank : ∀ {x y},
    (x, y) ∈ assignedFiniteEdges A → rank x < rank y
  every_relation_ray_strong :
    ∀ r : Ray (imaginaryGraph Gamma Y kappa),
      r.edgeSet ⊆ insideFamily.edgeSet ∪ assignedFiniteEdges A →
        (strongEdgeIndices r).Infinite
  inside_stable : insideFamily.Stable C.newSlice C.persistent
  old_real_vertices : W.realPart.vertices ⊆ insideFamily.vertexSet
  old_real_edges : W.realPart.edges ⊆
    relationRealEdges (Gamma := Gamma)
      (insideFamily.edgeSet ∪ assignedFiniteEdges A)
  old_vertices_accounted : W.vertexSet ⊆
    (insideFamily.terminalSet ∩ W.terminalSet) ∪
      {x | ∃ y,
        (x, y) ∈ W.familyGraph.edges ∩
          (insideFamily.edgeSet ∪ assignedFiniteEdges A)} ∪
        relationCompletedRealVertices (Gamma := Gamma)
          (insideFamily.edgeSet ∪ assignedFiniteEdges A)
          insideFamily.vertexSet Gamma.target
  preserved_old_terminal_not_assigned_source :
    insideFamily.terminalSet ∩ W.terminalSet ⊆
      {x | ¬ ∃ y, (x, y) ∈ assignedFiniteEdges A}
  target_path : FinitePath Gamma.graph
  target_path_start : target_path.start = u
  target_path_finish : target_path.finish ∈ Gamma.target
  target_path_vertices : target_path.support ⊆ insideFamily.vertexSet
  target_path_edges : target_path.edgeSet ⊆
    relationRealEdges (Gamma := Gamma)
      (insideFamily.edgeSet ∪ assignedFiniteEdges A)
  preserves_other_real_terminals :
    W.realPart.terminals \ {u} ⊆
      relationRealTerminals (Gamma := Gamma)
        (insideFamily.edgeSet ∪ assignedFiniteEdges A)
        insideFamily.vertexSet

namespace ConcreteInsideFragmentSplice

variable {C : ClubStageGeometry Gamma Y kappa theta}
variable {W : LinkageBlueprint Gamma Y kappa}
variable {Zf : FracturedWarp Gamma}
variable {A : SimultaneousAssignment Zf.paths Y} {u : V}

variable (D : ConcreteInsideFragmentSplice C W A u)

private theorem assignment_finite_or_infinite
    (s : {z // z ∈ Gamma.initialSet Zf.paths \ Gamma.initialSet Y}) :
    (∃ v, (A.assigned s).terminal? = some v) ∨ (A.assigned s).IsInfinite := by
  rcases A.maximal s with hinfinite | ⟨v, _hv, hterm⟩
  · exact Or.inr hinfinite
  · exact Or.inl ⟨v, hterm⟩

private theorem infinite_not_finite_source {x : V}
    (hx : x ∈ assignedInfiniteSources A) :
    ¬ ∃ y, (x, y) ∈ assignedFiniteEdges A := by
  rintro ⟨y, s, hfinite, hsx⟩
  obtain ⟨t, htx, hinfinite⟩ := hx
  have hst : s = t := by
    apply Subtype.ext
    exact hsx.trans htx.symm
  subst t
  have hnone : (A.assigned s).terminal? = none :=
    (AltPath.isInfinite_iff_terminal?_eq_none _).1 hinfinite
  rw [hfinite] at hnone
  exact Option.some_ne_none _ hnone

theorem assigned_endpoints {e : V × V}
    (he : e ∈ assignedFiniteEdges A) :
    e.1 ∈ D.insideFamily.vertexSet ∧
      e.2 ∈ D.insideFamily.vertexSet := by
  obtain ⟨s, hterm, hs⟩ := he
  have hsource := D.finite_sources_terminal s _ hterm
  have htarget := D.finite_targets_initial s _ hterm
  rw [D.insideFamily.terminalSet_eq_no_outgoing] at hsource
  rw [D.insideFamily.initialSet_eq_no_incoming] at htarget
  exact ⟨hs ▸ hsource.1, htarget.1⟩

theorem cross_in {x y z : V}
    (hxz : (x, z) ∈ D.insideFamily.edgeSet)
    (hyz : (y, z) ∈ assignedFiniteEdges A) : x = y := by
  obtain ⟨s, hterm, _hsy⟩ := hyz
  exact False.elim <| D.insideFamily.no_incoming_of_mem_initialSet
    (D.finite_targets_initial s z hterm) ⟨x, hxz⟩

theorem cross_out {x y z : V}
    (hxy : (x, y) ∈ D.insideFamily.edgeSet)
    (hxz : (x, z) ∈ assignedFiniteEdges A) : y = z := by
  obtain ⟨s, hterm, hsx⟩ := hxz
  exact False.elim <| D.insideFamily.no_outgoing_of_mem_terminalSet
    (by simpa [hsx] using D.finite_sources_terminal s z hterm) ⟨y, hxy⟩

theorem infinite_sources_sink : assignedInfiniteSources A ⊆
    {x | x ∈ D.insideFamily.vertexSet ∧
      ¬ ∃ y, (x, y) ∈
        D.insideFamily.edgeSet ∪ assignedFiniteEdges A} := by
  intro x hx
  have hxterminal := D.infinite_sources_terminal hx
  have hxterminal' := hxterminal
  rw [D.insideFamily.terminalSet_eq_no_outgoing] at hxterminal'
  refine ⟨hxterminal'.1, ?_⟩
  rintro ⟨y, hy⟩
  rcases hy with hy | hy
  · exact D.insideFamily.no_outgoing_of_mem_terminalSet hxterminal ⟨y, hy⟩
  · exact infinite_not_finite_source (A := A) hx ⟨y, hy⟩

theorem sink_boundary :
    {x | x ∈ D.insideFamily.vertexSet ∧
      ¬ ∃ y, (x, y) ∈
        D.insideFamily.edgeSet ∪ assignedFiniteEdges A} ⊆
      assignedInfiniteSources A ∪ C.newSlice := by
  rintro x ⟨hxcarrier, hxsink⟩
  have hxterminal : x ∈ D.insideFamily.terminalSet := by
    rw [D.insideFamily.terminalSet_eq_no_outgoing]
    exact ⟨hxcarrier, fun h ↦ hxsink ⟨h.choose, Or.inl h.choose_spec⟩⟩
  rcases D.terminal_boundary hxterminal with hxdomain | hxT
  · obtain ⟨s, hsx⟩ := hxdomain
    rcases assignment_finite_or_infinite (A := A) s with hxfinite | hxinfinite
    · obtain ⟨v, hterm⟩ := hxfinite
      exact False.elim <| hxsink ⟨v, Or.inr ⟨s, hterm, hsx⟩⟩
    · exact Or.inl ⟨s, hsx, hxinfinite⟩
  · exact Or.inr hxT

/-- Compile the actual inside-fragment family and its geometric boundary to
the raw union datum consumed by the global replacement theorem. -/
def toClubStageUnionData : ClubStageUnionData C W A u where
  inside := D.insideFamily.edgeSet
  carrier := D.insideFamily.vertexSet
  inside_in_graph := by
    intro e he
    simp only [edgeSet, Set.mem_iUnion] at he
    obtain ⟨p, _hp, hep⟩ := he
    exact p.edgeSet_subset_adj hep
  inside_endpoints := by
    intro e he
    simp only [edgeSet, Set.mem_iUnion] at he
    obtain ⟨p, hpF, hep⟩ := he
    have hend := p.edgeSet_subset_support_prod hep
    exact ⟨⟨p, hpF, hend.1⟩, ⟨p, hpF, hend.2⟩⟩
  assigned_endpoints := fun e he ↦ D.assigned_endpoints he
  inside_biunique := by
    change Relator.BiUnique
      (fun x y ↦ (x, y) ∈
        familyEdges (Γ := imaginaryWeb Gamma Y kappa)
          D.insideFamily.paths)
    exact Alternating.IsWarp.familyEdges_biUnique
      (Γ := imaginaryWeb Gamma Y kappa) D.insideFamily.isWarp
  cross_in := D.cross_in
  cross_out := D.cross_out
  rank := D.rank
  inside_rank := D.inside_rank
  assigned_rank := D.assigned_rank
  infinite_sources_sink := D.infinite_sources_sink
  sink_boundary := D.sink_boundary
  carrier_roofed := D.carrier_roofed
  covers_source := by
    intro x hx
    rcases D.covers_source hx with hxinitial | hxreference
    · apply Or.inl
      have hnoassigned := D.covered_initial_not_assigned_target ⟨hx, hxinitial⟩
      have hnoinside := D.insideFamily.no_incoming_of_mem_initialSet hxinitial
      exact ⟨by
        rw [D.insideFamily.initialSet_eq_no_incoming] at hxinitial
        exact hxinitial.1, fun h ↦ by
          rcases h with ⟨y, hy | hy⟩
          · exact hnoinside ⟨y, hy⟩
          · exact hnoassigned ⟨y, hy⟩⟩
    · exact Or.inr hxreference
  carrier_closed := D.carrier_closed
  card_carrier := D.insideFamily.mk_vertexSet_le_of_mk_paths_le
    C.capacity_infinite D.card_paths
  every_relation_ray_strong := D.every_relation_ray_strong
  stable_boundary := by
    intro x hx
    apply D.inside_stable
    refine ⟨?_, hx.2⟩
    rw [D.insideFamily.terminalSet_eq_no_outgoing]
    exact ⟨hx.1.1, fun h ↦ hx.1.2 ⟨h.choose, Or.inl h.choose_spec⟩⟩
  old_real_vertices := D.old_real_vertices
  old_real_edges := D.old_real_edges
  old_vertices_accounted := by
    intro x hx
    rcases D.old_vertices_accounted hx with (hxterm | hxedge) | hxcomplete
    · apply Or.inl
      apply Or.inl
      refine ⟨?_, hxterm.2⟩
      have hnoassigned := D.preserved_old_terminal_not_assigned_source hxterm
      have hxterminal := hxterm.1
      rw [D.insideFamily.terminalSet_eq_no_outgoing] at hxterminal
      exact ⟨hxterminal.1, fun h ↦ by
        rcases h with ⟨y, hy | hy⟩
        · exact hxterminal.2 ⟨y, hy⟩
        · exact hnoassigned ⟨y, hy⟩⟩
    · exact Or.inl (Or.inr hxedge)
    · exact Or.inr hxcomplete
  target_path := D.target_path
  target_path_start := D.target_path_start
  target_path_finish := D.target_path_finish
  target_path_vertices := D.target_path_vertices
  target_path_edges := D.target_path_edges
  preserves_other_real_terminals := D.preserves_other_real_terminals

end ConcreteInsideFragmentSplice

/-! ## Exact system-level compiler -/

/-- Construction data for every scheduled request, phrased in terms of an
actual inside-fragment path family.  This is strictly below
`ClubStageUnionSystem`: it contains no arbitrary `inside` relation and no
prepackaged `ClubStageUnionData` or `WholeFamilyUnionGeometry`. -/
def ConcreteInsideFragmentSpliceSystem
    (C : ClubStageGeometry Gamma Y kappa theta) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint C.newSlice C.closedSet C.persistent →
      C.persistent ⊆ C.newSlice → u ∈ W.realPart.terminals →
      ∀ (R : ClosedFracturedReplacementRequest
          (Gamma := Gamma) (Y := Y) (kappa := kappa) C.persistent)
        (A : SimultaneousAssignment R.fractured.paths Y),
        Nonempty (ConcreteInsideFragmentSplice C W A u)

/-- The concrete inside/outside linkage decomposition discharges the union
system expected by the checked global replacement transaction. -/
theorem clubStageUnionSystem_of_insideFragmentSplices
    {C : ClubStageGeometry Gamma Y kappa theta}
    (H : ConcreteInsideFragmentSpliceSystem C) :
    ClubStageUnionSystem C := by
  intro W u hW hpersistent hu R A
  exact ⟨(H W u hW hpersistent hu R A).some.toClubStageUnionData⟩

/-- End-to-end Section 9 successor compiler from the retained closure seed
and the concrete inside-fragment path construction. -/
theorem stable934Compiler_of_clubStageInsideFragments
    {C : ClubStageGeometry Gamma Y kappa theta}
    (S : ClubStageSeedSystem C)
    (H : ConcreteInsideFragmentSpliceSystem C) :
    Stable934Compiler (Γ := Gamma) (Y := Y) (κ := kappa)
      C.newSlice C.closedSet C.persistent Gamma.target := by
  exact stable934Compiler_of_clubStageGeometry S
    (clubStageUnionSystem_of_insideFragmentSplices H)

end LinkageBlueprint
end Blueprint
end Erdos599
