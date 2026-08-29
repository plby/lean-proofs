/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Alternating
import ErdosProblems.Erdos599.CountableAssignment
import ErdosProblems.Erdos599.ReducingBoundary

/-!
# Switching along a finite reducing alternating path

This file isolates the update of the auxiliary warp used in the proof of
Aharoni--Berger Theorem 4.12.  The zero-link case needs separate treatment:
source Definition 4.3 retains singleton components under raw application,
whereas a reducing singleton has to be removed from the auxiliary warp.
-/

namespace Erdos599
namespace Alternating
namespace ReducingSwitch

open Set DirectedPath

universe u

variable {V : Type u} {Γ : DWeb V}

private theorem Walk.eq_nil_of_isPath {x : V}
    (p : Walk Γ.graph x x) (hp : p.IsPath) : p = .nil := by
  cases p with
  | nil => rfl
  | @cons _ y _ h q =>
      exact False.elim ((List.nodup_cons.mp hp).1 q.end_mem_support)

private theorem FinitePath.eq_trivial_of_start_eq_finish
    (p : FinitePath Γ.graph) (h : p.start = p.finish) :
    p = FinitePath.trivial Γ.graph p.start := by
  rcases p with ⟨start, finish, walk, isPath⟩
  dsimp at h ⊢
  subst finish
  have hw : walk = .nil := Walk.eq_nil_of_isPath walk isPath
  subst walk
  rfl

private theorem eq_of_mem_of_initial_eq {Z : Set Γ.DPath}
    (hZ : Γ.IsWarp Z) {p q : Γ.DPath} (hp : p ∈ Z) (hq : q ∈ Z)
    (h : p.initial = q.initial) : p = q := by
  by_contra hpq
  exact Set.disjoint_left.1 (hZ hp hq hpq)
    p.initial_mem_support (h ▸ q.initial_mem_support)

private theorem eq_of_mem_of_terminal_eq {Z : Set Γ.DPath}
    (hZ : Γ.IsWarp Z) {p q : Γ.DPath} (hp : p ∈ Z) (hq : q ∈ Z)
    {x : V} (hpterm : Γ.terminal? p = some x)
    (hqterm : Γ.terminal? q = some x) : p = q := by
  by_contra hpq
  exact Set.disjoint_left.1 (hZ hp hq hpq)
    (Γ.terminal_mem_support hpterm) (Γ.terminal_mem_support hqterm)

theorem initialSet_sdiff_singleton {Z : Set Γ.DPath}
    (hZ : Γ.IsWarp Z) {p : Γ.DPath} (hp : p ∈ Z) :
    Γ.initialSet (Z \ {p}) = Γ.initialSet Z \ {p.initial} := by
  ext x
  constructor
  · rintro ⟨q, ⟨hqZ, hqp⟩, rfl⟩
    refine ⟨⟨q, hqZ, rfl⟩, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hqinit
    exact hqp (eq_of_mem_of_initial_eq hZ hqZ hp hqinit)
  · rintro ⟨⟨q, hqZ, hqx⟩, hx⟩
    refine ⟨q, ⟨hqZ, ?_⟩, hqx⟩
    simp only [Set.mem_singleton_iff]
    intro hqp
    subst q
    exact hx hqx.symm

theorem terminalFrontier_sdiff_singleton {Z : Set Γ.DPath}
    (hZ : Γ.IsWarp Z) {p : Γ.DPath} (hp : p ∈ Z) {x : V}
    (hpterm : Γ.terminal? p = some x) :
    Γ.terminalFrontier (Z \ {p}) = Γ.terminalFrontier Z \ {x} := by
  ext y
  constructor
  · rintro ⟨q, ⟨hqZ, hqp⟩, hqterm⟩
    refine ⟨⟨q, hqZ, hqterm⟩, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro hyx
    subst y
    exact hqp (eq_of_mem_of_terminal_eq hZ hqZ hp hqterm hpterm)
  · rintro ⟨⟨q, hqZ, hqterm⟩, hyx⟩
    refine ⟨q, ⟨hqZ, ?_⟩, hqterm⟩
    simp only [Set.mem_singleton_iff]
    intro hqp
    subst q
    have : some x = some y := hpterm.symm.trans hqterm
    exact hyx (Option.some.inj this).symm

theorem exists_delete_common_endpoint
    {Z : Set Γ.DPath} (hZ : Γ.IsWarp Z)
    (hZfin : Γ.HasFiniteCharacter Z) {u : V}
    (huI : u ∈ Γ.initialSet Z) (huT : u ∈ Γ.terminalFrontier Z) :
    ∃ Z' : Set Γ.DPath,
      Γ.IsWarp Z' ∧ Γ.HasFiniteCharacter Z' ∧
        Γ.initialSet Z' = Γ.initialSet Z \ {u} ∧
        Γ.terminalFrontier Z' = Γ.terminalFrontier Z \ {u} ∧
        familyEdges Z' ⊆ familyEdges Z ∧
        Γ.vertexSet Z' ⊆ Γ.vertexSet Z := by
  rcases huI with ⟨p, hpZ, hpinit⟩
  rcases huT with ⟨q, hqZ, hqterm⟩
  have huq : u ∈ q.support := Γ.terminal_mem_support hqterm
  have hup : u ∈ p.support := hpinit ▸ p.initial_mem_support
  have hpq : p = q := DWeb.IsWarp.eq_of_mem_support hZ hpZ hqZ hup huq
  subst q
  rcases hZfin hpZ with ⟨pfin, rfl⟩
  change pfin.start = u at hpinit
  simp only [DWeb.terminal?_finite, Option.some.injEq] at hqterm
  have hends : pfin.start = pfin.finish := hpinit.trans hqterm.symm
  have hptriv := FinitePath.eq_trivial_of_start_eq_finish pfin hends
  have heq : (Sum.inl pfin : Γ.DPath) = Γ.trivialPath u := by
    rw [hptriv]
    change (Sum.inl (FinitePath.trivial Γ.graph pfin.start) : Γ.DPath) =
      Sum.inl (FinitePath.trivial Γ.graph u)
    rw [hpinit]
  have hp0 : Γ.trivialPath u ∈ Z := by
    rw [← heq]
    exact hpZ
  refine ⟨Z \ {Γ.trivialPath u}, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    exact hZ ha.1 hb.1 hab
  · intro a ha
    exact hZfin ha.1
  · apply initialSet_sdiff_singleton hZ
    exact hp0
  · apply terminalFrontier_sdiff_singleton hZ
    · exact hp0
    · simp
  · intro e he
    simp only [familyEdges, Set.mem_iUnion] at he ⊢
    rcases he with ⟨p, hp, hpe⟩
    exact ⟨p, hp.1, hpe⟩
  · rintro x ⟨p, hp, hxp⟩
    exact ⟨p, hp.1, hxp⟩

/-! ## Finite character of a finite switch -/

theorem altPath_edgeSet_subset_vertexSet_prod {D : Digraph V}
    (T : AltPath D) :
    T.edgeSet ⊆ {e | e.1 ∈ T.vertexSet ∧ e.2 ∈ T.vertexSet} := by
  cases T with
  | trivial x => simp
  | finite Q =>
      rintro e he
      simp only [AltPath.edgeSet, FiniteTrace.edgeSet, Set.mem_iUnion] at he
      rcases he with ⟨i, hei⟩
      have hs := (Q.link i).path.edgeSet_subset_support_prod hei
      exact ⟨Set.mem_iUnion.2 ⟨i, hs.1⟩, Set.mem_iUnion.2 ⟨i, hs.2⟩⟩
  | infinite Q =>
      rintro e he
      simp only [AltPath.edgeSet, InfiniteTrace.edgeSet, Set.mem_iUnion] at he
      rcases he with ⟨i, hei⟩
      have hs := (Q.link i).path.edgeSet_subset_support_prod hei
      exact ⟨Set.mem_iUnion.2 ⟨i, hs.1⟩, Set.mem_iUnion.2 ⟨i, hs.2⟩⟩

/-- Any path component of a cyclowarp realizing a finite application to a
finite-character warp is finite.  This is independent of safeness: a ray
could use only finitely many switched edges, after which disjointness traps
it in one finite member of the original warp. -/
theorem Cyclowarp.pathPart_hasFiniteCharacter_of_finite_application
    {Z : Set Γ.DPath} (hZ : Γ.IsWarp Z)
    (hZfin : Γ.HasFiniteCharacter Z) {T : AltPath Γ.graph}
    (hTfin : T.IsFinite) (C : Cyclowarp Γ)
    (hC : C.edges = (Cyclowarp.application Z T).edges) :
    Γ.HasFiniteCharacter C.pathPart := by
  intro p hp
  change p ∈ C.paths at hp
  rcases p with p | r
  · exact ⟨p, rfl⟩
  · exfalso
    have hTCfinite : T.vertexSet.Finite := T.vertexSet_finite_of_isFinite hTfin
    have hindices : {n : ℕ | r n ∈ T.vertexSet}.Finite :=
      Set.Finite.preimage r.injective.injOn hTCfinite
    obtain ⟨B, hB⟩ := hindices.bddAbove
    let N := B + 1
    have hN : ∀ n ≥ N, r n ∉ T.vertexSet := by
      intro n hn hmem
      have hnB : n ≤ B := hB hmem
      omega
    have hedgeZ : ∀ k : ℕ, (r (N + k), r (N + k + 1)) ∈ familyEdges Z := by
      intro k
      have heC : (r (N + k), r (N + k + 1)) ∈ C.edges := by
        change (r (N + k), r (N + k + 1)) ∈
          familyEdges C.paths ∪ ⋃ c ∈ C.cycles, c.EdgeSet
        apply Or.inl
        simp only [familyEdges, Set.mem_iUnion]
        exact ⟨Sum.inr r, hp, ⟨N + k, rfl⟩⟩
      rw [hC, Cyclowarp.application_edges] at heC
      rcases heC with heC | heC
      · exact heC.1
      · have heSupport := altPath_edgeSet_subset_vertexSet_prod T heC.1
        exact False.elim ((hN (N + k) (by omega)) heSupport.1)
    have hedgeExists : ∀ k : ℕ, ∃ p ∈ Z,
        (r (N + k), r (N + k + 1)) ∈ p.edgeSet := by
      intro k
      simp only [familyEdges, Set.mem_iUnion] at hedgeZ
      rcases hedgeZ k with ⟨p, hpZ, hpe⟩
      exact ⟨p, hpZ, hpe⟩
    choose z hzZ hzedge using hedgeExists
    have hzEq : ∀ k : ℕ, z k = z 0 := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
          apply Eq.trans _ ih
          apply DWeb.IsWarp.eq_of_mem_support hZ (hzZ (k + 1)) (hzZ k)
          · exact (z (k + 1)).edgeSet_subset_support_prod (hzedge (k + 1)) |>.1
          · have he := (z k).edgeSet_subset_support_prod (hzedge k)
            simpa only [Nat.add_assoc] using he.2
    have hrange : ∀ k : ℕ, r (N + k) ∈ (z 0).support := by
      intro k
      rw [← hzEq k]
      exact (z k).edgeSet_subset_support_prod (hzedge k) |>.1
    rcases hZfin (hzZ 0) with ⟨q, hq⟩
    have htail : ∀ k : ℕ, r.tail N k ∈ q.support := by
      intro k
      rw [Ray.tail_apply]
      change r (N + k) ∈
        DirectedPath.Path.support (D := Γ.graph) (Sum.inl q)
      rw [← hq]
      exact hrange k
    exact q.support_finite.not_infinite
      (Set.infinite_of_injective_forall_mem (r.tail N).injective htail)

private theorem mem_vertexSet_union_of_mem_familyEdges_union
    {Z Y : Set Γ.DPath} {e : V × V}
    (he : e ∈ familyEdges Z ∪ familyEdges Y) :
    (e.1 ∈ Γ.vertexSet Z ∪ Γ.vertexSet Y) ∧
      (e.2 ∈ Γ.vertexSet Z ∪ Γ.vertexSet Y) := by
  rcases he with heZ | heY
  · simp only [familyEdges, Set.mem_iUnion] at heZ
    rcases heZ with ⟨p, hpZ, hep⟩
    have hs := p.edgeSet_subset_support_prod hep
    exact ⟨Or.inl ⟨p, hpZ, hs.1⟩, Or.inl ⟨p, hpZ, hs.2⟩⟩
  · simp only [familyEdges, Set.mem_iUnion] at heY
    rcases heY with ⟨p, hpY, hep⟩
    have hs := p.edgeSet_subset_support_prod hep
    exact ⟨Or.inr ⟨p, hpY, hs.1⟩, Or.inr ⟨p, hpY, hs.2⟩⟩

/-- The path part of a concrete bracket switch stays in the vertex union of
the two bracket warps.  Edge confinement handles every nontrivial component;
the isolated-data equality handles singleton components. -/
theorem Cyclowarp.pathPart_vertexSet_subset_of_application
    {Z Y : Set Γ.DPath} {T : AltPath Γ.graph}
    (hT : IsBracketAlternating Y Z T) (C : Cyclowarp Γ)
    (hEdges : C.edges = (Cyclowarp.application Z T).edges)
    (hIsolated : C.isolated = (Cyclowarp.application Z T).isolated) :
    Γ.vertexSet C.pathPart ⊆ Γ.vertexSet Z ∪ Γ.vertexSet Y := by
  rintro x ⟨p, hpC, hxp⟩
  have hedgeConf := C.pathPart_edges_subset_familyEdges_union_of_application hT hEdges
  rcases p with p | r
  · by_cases hxstart : x = p.start
    · by_cases hxfinish : x = p.finish
      · have hends : p.start = p.finish := hxstart.symm.trans hxfinish
        have hpEq : (Sum.inl p : Γ.DPath) = Γ.trivialPath p.start := by
          rw [FinitePath.eq_trivial_of_start_eq_finish p hends]
          rfl
        have hiso : p.start ∈ C.isolated := by
          change Γ.trivialPath p.start ∈ C.paths
          rw [← hpEq]
          exact hpC
        rw [hxstart]
        exact Or.inl (C.isolated_subset_vertexSet_of_application hIsolated hiso)
      · rcases
          _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
          p hxp hxfinish
          with ⟨y, hy⟩
        have hyC : (x, y) ∈ familyEdges C.pathPart := by
          simp only [familyEdges, Set.mem_iUnion]
          exact ⟨Sum.inl p, hpC, hy⟩
        exact (mem_vertexSet_union_of_mem_familyEdges_union (hedgeConf hyC)).1
    · rcases _root_.Erdos599.Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
        p hxp hxstart
        with ⟨y, hy⟩
      have hyC : (y, x) ∈ familyEdges C.pathPart := by
        simp only [familyEdges, Set.mem_iUnion]
        exact ⟨Sum.inl p, hpC, hy⟩
      exact (mem_vertexSet_union_of_mem_familyEdges_union (hedgeConf hyC)).2
  · rcases hxp with ⟨n, rfl⟩
    have heC : (r n, r (n + 1)) ∈ familyEdges C.pathPart := by
      simp only [familyEdges, Set.mem_iUnion]
      exact ⟨Sum.inr r, hpC, ⟨n, rfl⟩⟩
    exact (mem_vertexSet_union_of_mem_familyEdges_union (hedgeConf heC)).1

/-! ## The finite reducing switch -/

/-- Switching along a finite reducing `[Y,Z]`-alternating path deletes its
two endpoints from the corresponding frontiers.  The zero-link case is
handled by deleting the common singleton component explicitly; every
nontrivial finite case is the path part of the switched cyclowarp. -/
theorem exists_reducingSwitch
    (Z Y : Set Γ.DPath) (u v : V) (T : AltPath Γ.graph)
    (hZ : Γ.IsWarp Z) (hZfin : Γ.HasFiniteCharacter Z)
    (_hY : Γ.IsWarp Y) (_hYfin : Γ.HasFiniteCharacter Y)
    (huZ : u ∈ Γ.initialSet Z) (_huY : u ∉ Γ.vertexSet Y)
    (hvZ : v ∈ Γ.terminalFrontier Z) (_hvY : v ∉ Γ.vertexSet Y)
    (hT : IsBracketAlternating Y Z T) (hTi : T.initial = v)
    (hTt : T.terminal? = some u) (hTfin : T.IsFinite) :
    ∃ Z' : Set Γ.DPath,
      Γ.IsWarp Z' ∧ Γ.HasFiniteCharacter Z' ∧
      Γ.initialSet Z' = Γ.initialSet Z \ {u} ∧
      Γ.terminalFrontier Z' = Γ.terminalFrontier Z \ {v} ∧
      Γ.vertexSet Z' ⊆ Γ.vertexSet Z ∪ Γ.vertexSet Y := by
  cases T with
  | trivial w =>
      simp only [AltPath.initial_trivial] at hTi
      simp only [AltPath.terminal?_trivial, Option.some.injEq] at hTt
      subst v
      subst u
      obtain ⟨Z', hZ', hZ'fin, hinit, hterm, _, hvertices⟩ :=
        exists_delete_common_endpoint hZ hZfin huZ hvZ
      exact ⟨Z', hZ', hZ'fin, hinit, hterm,
        hvertices.trans Set.subset_union_left⟩
  | finite Q =>
      obtain ⟨C, hEdges, hIsolated, hCfin⟩ :=
        Q.exists_application_cyclowarp hT.1 hZfin
      have hfrontiers :=
        C.pathPart_frontiers_eq_sdiff_of_finite_reducing hZfin Q hT.1
          hvZ hTi huZ hTt hEdges hIsolated hCfin
      exact ⟨C.pathPart, C.pathPart_isWarp, hCfin,
        hfrontiers.1, hfrontiers.2,
        Cyclowarp.pathPart_vertexSet_subset_of_application
          hT C hEdges hIsolated⟩
  | infinite Q => exact False.elim hTfin

/-- Concrete reducing-switch rule consumed by the countable successive-switch
construction. -/
theorem reducingSwitchRule (Γ : DWeb V) : ReducingSwitchRule Γ := by
  intro Z Y u v T hZ hZfin hY hYfin huZ huY hvZ hvY hT hTi hTt hTfin
  exact exists_reducingSwitch Z Y u v T hZ hZfin hY hYfin huZ huY
    hvZ hvY hT hTi hTt hTfin

end ReducingSwitch
end Alternating
end Erdos599
