/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayCompressedFreshSplice

/-!
# The complete compressed inside union in moving Assertion 9.31

This is the live occurrence-aware replacement for the obsolete
`ClubStageUnionData`/`WholeFamilyUnionGeometry` route.  Its inside object is
an actual linkage family containing the complete joint survivor and the
row-inside pieces.  The occurrence assignment contributes only its classified
finite endpoint edges; no split path is projected or contracted.

Full current-carrier and current-edge containment are explicit construction
facts.  The exact fresh-no-incoming incidence is also retained, so the
resulting whole-family relation immediately compiles to a genuine fresh
attachment.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Concrete complete inside family together with the boundary and
accounting facts of the moving 9.31 construction. -/
structure CompressedCompleteInsideFragmentSplice
    (ancestor current : LinkageBlueprint Gamma Y kappa)
    {Zf : FracturedWarp Gamma}
    (A : CompressedFracturedAssignment Zf Y)
    (z : V) (Tnew Z persistent B : Set V) where
  insideFamily : LinkageBlueprint Gamma Y kappa
  finite_sources_terminal : ∀ s v, A.outcome s = some v →
    s.1 ∈ insideFamily.terminalSet
  finite_targets_initial : ∀ s v, A.outcome s = some v →
    v ∈ insideFamily.initialSet
  infinite_sources_terminal : A.infiniteSources ⊆ insideFamily.terminalSet
  terminal_boundary : insideFamily.terminalSet ⊆ A.infiniteSources ∪ Tnew
  carrier_roofed : insideFamily.vertexSet ⊆ Gamma.roof Tnew
  covers_source : Gamma.source ⊆
    insideFamily.initialSet ∪
      Gamma.initialSet
        (referencePathsMeeting Y Tnew \
          referencePathsMeeting Y insideFamily.vertexSet)
  covered_initial_not_assigned_target :
    Gamma.source ∩ insideFamily.initialSet ⊆
      {x | ¬ ∃ y, (y, x) ∈ A.finiteEdges}
  carrier_closed : insideFamily.vertexSet ⊆ Z
  capacity_infinite : aleph0 ≤ kappa
  card_paths : #insideFamily.paths ≤ kappa
  rank : V → Nat
  inside_rank : ∀ {x y}, (x, y) ∈ insideFamily.edgeSet → rank x < rank y
  assigned_rank : ∀ {x y}, (x, y) ∈ A.finiteEdges → rank x < rank y
  every_relation_ray_strong :
    ∀ r : Ray (imaginaryGraph Gamma Y kappa),
      r.edgeSet ⊆ insideFamily.edgeSet ∪ A.finiteEdges →
        (strongEdgeIndices r).Infinite
  inside_stable : insideFamily.Stable Tnew persistent
  current_vertices : current.vertexSet ⊆ insideFamily.vertexSet
  current_edges : current.edgeSet ⊆ insideFamily.edgeSet ∪ A.finiteEdges
  fresh_no_incoming_old : ∀ {x y : V}, x ∈ current.vertexSet →
    (y, x) ∈ (insideFamily.edgeSet ∪ A.finiteEdges) \ current.edgeSet → False
  old_vertices_accounted : current.vertexSet ⊆
    (({x | x ∈ insideFamily.vertexSet ∧
        ¬ ∃ y, (x, y) ∈ insideFamily.edgeSet ∪ A.finiteEdges} ∩
        current.terminalSet) ∪
      {x | ∃ y, (x, y) ∈ current.familyGraph.edges ∩
        (insideFamily.edgeSet ∪ A.finiteEdges)} ∪
      relationCompletedRealVertices (Gamma := Gamma)
        (insideFamily.edgeSet ∪ A.finiteEdges)
        insideFamily.vertexSet B)
  target_path : FinitePath Gamma.graph
  target_path_start : target_path.start = z
  target_path_finish : target_path.finish ∈ B
  target_path_vertices : target_path.support ⊆ insideFamily.vertexSet
  target_path_edges : target_path.edgeSet ⊆
    relationRealEdges (Gamma := Gamma)
      (insideFamily.edgeSet ∪ A.finiteEdges)
  preserves_other_real_terminals : current.realPart.terminals \ {z} ⊆
    relationRealTerminals (Gamma := Gamma)
      (insideFamily.edgeSet ∪ A.finiteEdges) insideFamily.vertexSet
  persistent_boundary : current.terminalSet ∩ persistent ⊆
    {x | x ∈ insideFamily.vertexSet ∧
      ¬ ∃ y, (x, y) ∈ insideFamily.edgeSet ∪ A.finiteEdges} ∪ {z}
  inherited_boundary : ∀ x, x ∈ ancestor.terminalSet →
    x ∈ current.terminalSet → x ≠ z →
      x ∈ insideFamily.vertexSet ∧
        ¬ ∃ y, (x, y) ∈ insideFamily.edgeSet ∪ A.finiteEdges

namespace CompressedCompleteInsideFragmentSplice

variable {ancestor current : LinkageBlueprint Gamma Y kappa}
variable {Zf : FracturedWarp Gamma}
variable {A : CompressedFracturedAssignment Zf Y}
variable {z : V} {Tnew Z persistent B : Set V}

private theorem no_incoming_of_initial
    (F : LinkageBlueprint Gamma Y kappa) {x : V}
    (hx : x ∈ F.initialSet) : ¬ ∃ y, (y, x) ∈ F.edgeSet := by
  rintro ⟨y, hyx⟩
  obtain ⟨p, hpF, hpinitial⟩ := hx
  simp only [edgeSet, Set.mem_iUnion] at hyx
  obtain ⟨q, hqF, hyxq⟩ := hyx
  have hxp : x ∈ p.support := hpinitial.symm ▸ p.initial_mem_support
  have hxq : x ∈ q.support := (q.edgeSet_subset_support_prod hyxq).2
  have hpq := F.path_eq_of_mem_support hpF hqF hxp hxq
  subst q
  rcases p with p | r
  · have hpstart : p.start = x := by
      simpa [DirectedPath.Path.initial] using hpinitial
    exact FinitePath.no_incoming_edge_at_start p y (hpstart ▸ hyxq)
  · obtain ⟨n, hn⟩ := hyxq
    have hzero : n + 1 = 0 := by
      apply r.injective
      calc
        r (n + 1) = x := (congrArg Prod.snd hn).symm
        _ = r.initial := hpinitial.symm
        _ = r 0 := rfl
    omega

private theorem no_outgoing_of_terminal
    (F : LinkageBlueprint Gamma Y kappa) {x : V}
    (hx : x ∈ F.terminalSet) : ¬ ∃ y, (x, y) ∈ F.edgeSet := by
  rintro ⟨y, hxy⟩
  obtain ⟨p, hpF, hpterminal⟩ := hx
  simp only [edgeSet, Set.mem_iUnion] at hxy
  obtain ⟨q, hqF, hxyq⟩ := hxy
  have hxp : x ∈ p.support :=
    (imaginaryWeb Gamma Y kappa).terminal_mem_support hpterminal
  have hxq : x ∈ q.support := (q.edgeSet_subset_support_prod hxyq).1
  have hpq := F.path_eq_of_mem_support hpF hqF hxp hxq
  subst q
  rcases p with p | r
  · have hpfinish : p.finish = x := by
      simpa [DWeb.terminal?, DirectedPath.Path.terminal?] using hpterminal
    exact FinitePath.no_outgoing_edge_at_finish p y (hpfinish ▸ hxyq)
  · simp [DWeb.terminal?, DirectedPath.Path.terminal?] at hpterminal

private theorem no_directed_cycle_of_rank
    (E : Set (V × V)) (rank : V → Nat)
    (hrank : ∀ {x y}, (x, y) ∈ E → rank x < rank y) :
    ¬ ContainsDirectedCycle E := by
  rintro ⟨C, hC⟩
  let last : Nat := C.length - 1
  have hlast : last < C.length := Nat.sub_lt C.positive (by omega)
  have hnextLast : C.next ⟨last, hlast⟩ =
      (⟨0, C.positive⟩ : Fin C.length) := by
    apply Fin.ext
    have hs : last + 1 = C.length := Nat.sub_add_cancel C.positive
    simp [DirectedCycle.next, hs]
  have hmono : ∀ n, (hn : n < C.length) →
      rank (C.vertex ⟨0, C.positive⟩) ≤ rank (C.vertex ⟨n, hn⟩) := by
    intro n
    induction n with
    | zero => intro _; exact Nat.le_refl _
    | succ n ih =>
        intro hn
        have hn' : n < C.length := Nat.lt_trans (Nat.lt_succ_self n) hn
        have hnext : C.next (⟨n, hn'⟩ : Fin C.length) = ⟨n + 1, hn⟩ := by
          apply Fin.ext
          exact Nat.mod_eq_of_lt hn
        exact (ih hn').trans (Nat.le_of_lt (by
          rw [← hnext]
          exact hrank (hC ⟨⟨n, hn'⟩, rfl⟩)))
  have hback : rank (C.vertex ⟨last, hlast⟩) <
      rank (C.vertex ⟨0, C.positive⟩) := by
    rw [← hnextLast]
    exact hrank (hC ⟨⟨last, hlast⟩, rfl⟩)
  exact (Nat.not_lt_of_ge (hmono last hlast)) hback

private theorem no_reverse_ray_of_rank
    (E : Set (V × V)) (rank : V → Nat)
    (hrank : ∀ {x y}, (x, y) ∈ E → rank x < rank y) :
    ¬ ContainsReverseDirectedRay E := by
  rintro ⟨R, hR⟩
  have hdesc (n : Nat) : rank (R.vertex (n + 1)) < rank (R.vertex n) :=
    hrank (hR n)
  have hbound : ∀ n, rank (R.vertex n) + n ≤ rank (R.vertex 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hs := hdesc n
        omega
  have h := hbound (rank (R.vertex 0) + 1)
  omega

variable (D : CompressedCompleteInsideFragmentSplice
  ancestor current A z Tnew Z persistent B)

theorem finite_endpoints {e : V × V} (he : e ∈ A.finiteEdges) :
    e.1 ∈ D.insideFamily.vertexSet ∧
      e.2 ∈ D.insideFamily.vertexSet := by
  obtain ⟨s, hterm, hs⟩ := he
  have hsource := D.finite_sources_terminal s _ hterm
  have htarget := D.finite_targets_initial s _ hterm
  obtain ⟨p, hp, hpterm⟩ := hsource
  obtain ⟨q, hq, hqinitial⟩ := htarget
  refine ⟨⟨p, hp, ?_⟩, ⟨q, hq, ?_⟩⟩
  · rw [← hs]
    exact (imaginaryWeb Gamma Y kappa).terminal_mem_support hpterm
  · exact hqinitial.symm ▸ q.initial_mem_support

theorem cross_in {x y v : V}
    (hxv : (x, v) ∈ D.insideFamily.edgeSet)
    (hyv : (y, v) ∈ A.finiteEdges) : x = y := by
  obtain ⟨s, hterm, _⟩ := hyv
  exact False.elim <| no_incoming_of_initial D.insideFamily
    (D.finite_targets_initial s v hterm) ⟨x, hxv⟩

theorem cross_out {x y v : V}
    (hxy : (x, y) ∈ D.insideFamily.edgeSet)
    (hxv : (x, v) ∈ A.finiteEdges) : y = v := by
  obtain ⟨s, hterm, hsx⟩ := hxv
  exact False.elim <| no_outgoing_of_terminal D.insideFamily
    (by simpa [hsx] using D.finite_sources_terminal s v hterm) ⟨y, hxy⟩

theorem union_biunique : Relator.BiUnique
    (fun x y ↦ (x, y) ∈ D.insideFamily.edgeSet ∪ A.finiteEdges) := by
  have hinside := Alternating.IsWarp.familyEdges_biUnique D.insideFamily.isWarp
  constructor
  · intro x y v hxv hyv
    rcases hxv with hxv | hxv <;> rcases hyv with hyv | hyv
    · exact hinside.1 hxv hyv
    · exact D.cross_in hxv hyv
    · exact (D.cross_in hyv hxv).symm
    · exact A.finiteEdges_in_unique hxv hyv
  · intro x y v hxy hxv
    rcases hxy with hxy | hxy <;> rcases hxv with hxv | hxv
    · exact hinside.2 hxy hxv
    · exact D.cross_out hxy hxv
    · exact (D.cross_out hxv hxy).symm
    · exact A.finiteEdges_out_unique hxy hxv

theorem union_no_directed_cycle :
    ¬ ContainsDirectedCycle (D.insideFamily.edgeSet ∪ A.finiteEdges) :=
  no_directed_cycle_of_rank _ D.rank (by
    intro x y hxy
    exact hxy.elim D.inside_rank D.assigned_rank)

theorem union_no_reverse_ray :
    ¬ ContainsReverseDirectedRay (D.insideFamily.edgeSet ∪ A.finiteEdges) :=
  no_reverse_ray_of_rank _ D.rank (by
    intro x y hxy
    exact hxy.elim D.inside_rank D.assigned_rank)

theorem infinite_sources_sink : A.infiniteSources ⊆
    {x | x ∈ D.insideFamily.vertexSet ∧
      ¬ ∃ y, (x, y) ∈ D.insideFamily.edgeSet ∪ A.finiteEdges} := by
  intro x hx
  have hxterminal := D.infinite_sources_terminal hx
  have hxcarrier : x ∈ D.insideFamily.vertexSet := by
    obtain ⟨p, hp, hpterm⟩ := hxterminal
    exact ⟨p, hp,
      (imaginaryWeb Gamma Y kappa).terminal_mem_support hpterm⟩
  refine ⟨hxcarrier, ?_⟩
  rintro ⟨y, hxy | hxy⟩
  · exact no_outgoing_of_terminal D.insideFamily hxterminal ⟨y, hxy⟩
  · obtain ⟨s, hsx, hsnone⟩ := hx
    obtain ⟨t, htsome, htx⟩ := hxy
    have hst : s = t := by
      apply Subtype.ext
      exact hsx.trans htx.symm
    subst t
    simp [hsnone] at htsome

theorem sink_boundary :
    {x | x ∈ D.insideFamily.vertexSet ∧
      ¬ ∃ y, (x, y) ∈ D.insideFamily.edgeSet ∪ A.finiteEdges} ⊆
      A.infiniteSources ∪ Tnew := by
  intro x hx
  have hxterminal : x ∈ D.insideFamily.terminalSet := by
    by_contra hxnot
    obtain ⟨y, hxy⟩ :=
      D.insideFamily.exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet
        hx.1 hxnot
    exact hx.2 ⟨y, Or.inl hxy⟩
  exact D.terminal_boundary hxterminal

theorem covers_source_union : Gamma.source ⊆
    {x | x ∈ D.insideFamily.vertexSet ∧
      ¬ ∃ y, (y, x) ∈ D.insideFamily.edgeSet ∪ A.finiteEdges} ∪
      Gamma.initialSet
        (referencePathsMeeting Y Tnew \
          referencePathsMeeting Y D.insideFamily.vertexSet) := by
  intro x hx
  rcases D.covers_source hx with hxinitial | hxreference
  · apply Or.inl
    obtain ⟨p, hp, hpinitial⟩ := hxinitial
    refine ⟨⟨p, hp, hpinitial.symm ▸ p.initial_mem_support⟩, ?_⟩
    rintro ⟨y, hyx | hyx⟩
    · exact no_incoming_of_initial D.insideFamily
        ⟨p, hp, hpinitial⟩ ⟨y, hyx⟩
    · exact D.covered_initial_not_assigned_target
        ⟨hx, ⟨p, hp, hpinitial⟩⟩ ⟨y, hyx⟩
  · exact Or.inr hxreference

theorem stable_boundary :
    {x | x ∈ D.insideFamily.vertexSet ∧
      ¬ ∃ y, (x, y) ∈ D.insideFamily.edgeSet ∪ A.finiteEdges} ∩ Tnew ⊆
      persistent := by
  intro x hx
  apply D.inside_stable
  refine ⟨?_, hx.2⟩
  by_contra hxnot
  obtain ⟨y, hxy⟩ :=
    D.insideFamily.exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet
      hx.1.1 hxnot
  exact hx.1.2 ⟨y, Or.inl hxy⟩

/-- Construct the live compressed whole-family splice relation from the
complete inside linkage and the occurrence endpoint summary. -/
def toCompressedWholeFamilySpliceRelation
    (hfinite : ∀ s v, A.outcome s = some v →
      IsImaginaryEdge Gamma Y kappa s.1 v) :
    CompressedWholeFamilySpliceRelation current A z Tnew Z persistent B where
  edge := D.insideFamily.edgeSet ∪ A.finiteEdges
  carrier := D.insideFamily.vertexSet
  edge_in_graph := by
    intro e he
    rcases he with he | he
    · rcases Set.mem_iUnion.1 he with ⟨p, he⟩
      rcases Set.mem_iUnion.1 he with ⟨hp, hep⟩
      exact p.edgeSet_subset_adj hep
    · exact A.finiteEdges_subset_imaginaryGraph hfinite he
  endpoints_mem := by
    intro e he
    exact he.elim
      (fun he ↦ by
        simp only [edgeSet, Set.mem_iUnion] at he
        obtain ⟨p, hp, hep⟩ := he
        exact ⟨⟨p, hp, (p.edgeSet_subset_support_prod hep).1⟩,
          ⟨p, hp, (p.edgeSet_subset_support_prod hep).2⟩⟩)
      (fun he ↦ D.finite_endpoints he)
  biunique := D.union_biunique
  no_directed_cycle := D.union_no_directed_cycle
  no_reverse_ray := D.union_no_reverse_ray
  assigned_edges := fun _ he ↦ Or.inr he
  infinite_sources_sink := D.infinite_sources_sink
  sink_boundary := D.sink_boundary
  vertices_roofed := D.carrier_roofed
  covers_source := D.covers_source_union
  vertices_closed := D.carrier_closed
  card_carrier := D.insideFamily.mk_vertexSet_le_of_mk_paths_le
    D.capacity_infinite D.card_paths
  every_relation_ray_strong := D.every_relation_ray_strong
  stable_boundary := D.stable_boundary
  old_real_vertices := by
    simpa only [realPart_vertices] using D.current_vertices
  old_real_edges := by
    rintro e he
    exact ⟨D.current_edges he.1, he.2⟩
  old_vertices_accounted := D.old_vertices_accounted
  target_path := D.target_path
  target_path_start := D.target_path_start
  target_path_finish := D.target_path_finish
  target_path_vertices := D.target_path_vertices
  target_path_edges := D.target_path_edges
  preserves_other_real_terminals := D.preserves_other_real_terminals

/-- Add the ancestor/current boundary fields.  Full current retention and
the no-incoming-new incidence are already concrete fields of `D`; the real
predecessor statement follows rather than being separately assumed. -/
def toCompressedWholeFamilyAdvanceSpliceRelation
    (hfinite : ∀ s v, A.outcome s = some v →
      IsImaginaryEdge Gamma Y kappa s.1 v) :
    CompressedWholeFamilyAdvanceSpliceRelation
      ancestor current A z Tnew Z persistent B where
  splice := D.toCompressedWholeFamilySpliceRelation hfinite
  old_vertices := D.current_vertices
  old_edges := D.current_edges
  persistent_boundary := D.persistent_boundary
  inherited_boundary := D.inherited_boundary
  no_new_real_predecessors := by
    intro x y hx hxy
    by_cases hcurrent : (y, x) ∈ current.edgeSet
    · exact ⟨hcurrent, hxy.2⟩
    · exact False.elim <| D.fresh_no_incoming_old
        (by simpa only [realPart_vertices] using hx) ⟨hxy.1, hcurrent⟩

theorem advance_fresh_no_incoming
    (hfinite : ∀ s v, A.outcome s = some v →
      IsImaginaryEdge Gamma Y kappa s.1 v) :
    ∀ {x y : V}, x ∈ current.vertexSet →
      (y, x) ∈
          (D.toCompressedWholeFamilyAdvanceSpliceRelation hfinite).splice.edge \
            current.edgeSet → False :=
  D.fresh_no_incoming_old

#print axioms finite_endpoints
#print axioms union_biunique
#print axioms union_no_directed_cycle
#print axioms toCompressedWholeFamilyAdvanceSpliceRelation

end CompressedCompleteInsideFragmentSplice
end Erdos599.Blueprint.LinkageBlueprint
