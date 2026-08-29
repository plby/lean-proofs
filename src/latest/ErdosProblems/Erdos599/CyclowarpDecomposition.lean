/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Alternating
import ErdosProblems.Erdos599.RelationComponents
import Mathlib.Data.Set.Finite.Lattice

/-!
# Finite reducing switches

This file contains the finite, reducing specialization of the cyclowarp
operation from Aharoni--Berger Definition 4.3.  In particular, it records
the endpoint orientation facts which force a nontrivial reducing alternating
path to delete, rather than add, the boundary edges at its two ends.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Γ : DWeb V}

/-! ## Elementary frontier facts -/

theorem initialSet_subset_vertexSet (W : Set Γ.DPath) :
    Γ.initialSet W ⊆ Γ.vertexSet W := by
  rintro x ⟨p, hp, rfl⟩
  exact ⟨p, hp, p.initial_mem_support⟩

theorem terminalFrontier_subset_vertexSet (W : Set Γ.DPath) :
    Γ.terminalFrontier W ⊆ Γ.vertexSet W := by
  rintro x ⟨p, hp, hpx⟩
  exact ⟨p, hp, Γ.terminal_mem_support hpx⟩

/-! ## The two links at a nontrivial reducing path point backwards -/

/-- A nontrivial finite alternating path whose initial vertex lies on the
reference warp cannot start with a forward link. -/
theorem firstDirection_eq_backward_of_initial_mem
    {Z : Set Γ.DPath} {T : AltPath Γ.graph}
    (hT : IsAlternating Z T) (hi : T.initial ∈ Γ.vertexSet Z)
    (hnontrivial : ∀ x, T ≠ .trivial x) :
    T.firstDirection? = some .backward := by
  rcases T with x | Q | Q
  · exact False.elim (hnontrivial x rfl)
  · cases hdir : Q.firstLink.direction with
    | backward => simp [AltPath.firstDirection?, hdir]
    | forward =>
        exfalso
        exact hT.2.2.1 (by simp [AltPath.firstDirection?, hdir]) hi
  · cases hdir : (Q.link 0).direction with
    | backward => simp [AltPath.firstDirection?, hdir]
    | forward =>
        exfalso
        exact hT.2.2.1 (by simp [AltPath.firstDirection?, hdir]) hi

/-- A nontrivial finite alternating path whose terminal vertex lies on the
reference warp cannot finish with a forward link. -/
theorem lastDirection_eq_backward_of_terminal_mem
    {Z : Set Γ.DPath} {T : AltPath Γ.graph} {u : V}
    (hT : IsAlternating Z T) (ht : T.terminal? = some u)
    (hu : u ∈ Γ.vertexSet Z) (hnontrivial : ∀ x, T ≠ .trivial x) :
    T.lastDirection? = some .backward := by
  rcases T with x | Q | Q
  · exact False.elim (hnontrivial x rfl)
  · cases hdir : Q.lastLink.direction with
    | backward => simp [AltPath.lastDirection?, hdir]
    | forward =>
        exfalso
        exact hT.2.2.2 u ht
          (by simp [AltPath.lastDirection?, hdir]) hu
  · simp [AltPath.terminal?] at ht

/-- Endpoint orientation for a nontrivial reducing alternating path. -/
theorem reducing_end_directions
    {Z : Set Γ.DPath} {T : AltPath Γ.graph} {v u : V}
    (hT : IsAlternating Z T)
    (hv : v ∈ Γ.terminalFrontier Z) (hTi : T.initial = v)
    (hu : u ∈ Γ.initialSet Z) (hTt : T.terminal? = some u)
    (hnontrivial : ∀ x, T ≠ .trivial x) :
    T.firstDirection? = some .backward ∧
      T.lastDirection? = some .backward := by
  refine ⟨firstDirection_eq_backward_of_initial_mem hT ?_ hnontrivial,
    lastDirection_eq_backward_of_terminal_mem hT hTt
      (initialSet_subset_vertexSet Z hu) hnontrivial⟩
  rw [hTi]
  exact terminalFrontier_subset_vertexSet Z hv

/-! ## Finiteness of the trace data -/

private theorem walk_edgeSet_finite {a b : V}
    (p : Walk Γ.graph a b) : p.edgeSet.Finite := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
      simpa using Set.Finite.union (Set.finite_singleton (x, y)) ih

theorem FiniteTrace.vertexSet_finite (Q : FiniteTrace Γ.graph) :
    Q.vertexSet.Finite := by
  simp only [FiniteTrace.vertexSet]
  exact finite_iUnion fun i ↦ (Q.link i).path.support_finite

theorem FiniteTrace.edgeSet_finite (Q : FiniteTrace Γ.graph) :
    Q.edgeSet.Finite := by
  simp only [FiniteTrace.edgeSet]
  exact finite_iUnion fun i ↦ walk_edgeSet_finite (Q.link i).path.walk

theorem AltPath.vertexSet_finite_of_isFinite
    (T : AltPath Γ.graph) (hT : T.IsFinite) : T.vertexSet.Finite := by
  cases T with
  | trivial x => simp [AltPath.vertexSet]
  | finite Q => exact Q.vertexSet_finite
  | infinite Q => simp [AltPath.IsFinite] at hT

theorem AltPath.edgeSet_finite_of_isFinite
    (T : AltPath Γ.graph) (hT : T.IsFinite) : T.edgeSet.Finite := by
  cases T with
  | trivial x => simp [AltPath.edgeSet]
  | finite Q => exact Q.edgeSet_finite
  | infinite Q => simp [AltPath.IsFinite] at hT

/-! ## Edge incidence at the ends of a finite path -/

theorem Walk.exists_incoming_edge_of_mem_support_of_ne_start
    {D : Digraph V} {a b x : V} (p : Walk D a b)
    (hx : x ∈ p.support) (hxa : x ≠ a) :
    ∃ y, (y, x) ∈ p.edgeSet := by
  induction p with
  | nil => exact False.elim (hxa (by simpa using hx))
  | @cons a c b e p ih =>
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact False.elim (hxa rfl)
      · by_cases hxc : x = c
        · subst x
          exact ⟨a, by simp⟩
        · rcases ih hx hxc with ⟨y, hy⟩
          exact ⟨y, by simp [hy]⟩

theorem Walk.exists_outgoing_edge_of_mem_support_of_ne_end
    {D : Digraph V} {a b x : V} (p : Walk D a b)
    (hx : x ∈ p.support) (hxb : x ≠ b) :
    ∃ y, (x, y) ∈ p.edgeSet := by
  induction p with
  | nil => exact False.elim (hxb (by simpa using hx))
  | @cons a c b e p ih =>
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨c, by simp⟩
      · rcases ih hx hxb with ⟨y, hy⟩
        exact ⟨y, by simp [hy]⟩

theorem Walk.no_incoming_edge_at_start_of_isPath
    {D : Digraph V} {a b : V} (p : Walk D a b) (hp : p.IsPath) (y : V) :
    (y, a) ∉ p.edgeSet := by
  induction p with
  | nil => simp
  | @cons a c b e p ih =>
      intro he
      simp only [Walk.edgeSet_cons, Set.mem_union,
        Set.mem_singleton_iff] at he
      have hac : a ∉ p.support := (List.nodup_cons.mp hp).1
      rcases he with he | he
      · have hca : c = a := (congrArg Prod.snd he).symm
        exact hac (hca ▸ p.start_mem_support)
      · exact hac (p.edgeSet_subset_support_prod he).2

theorem Walk.no_outgoing_edge_at_end_of_isPath
    {D : Digraph V} {a b : V} (p : Walk D a b) (hp : p.IsPath) (y : V) :
    (b, y) ∉ p.edgeSet := by
  induction p with
  | nil => simp
  | @cons a c b e p ih =>
      intro he
      simp only [Walk.edgeSet_cons, Set.mem_union,
        Set.mem_singleton_iff] at he
      rcases he with he | he
      · have hab : a = b := (congrArg Prod.fst he).symm
        exact (List.nodup_cons.mp hp).1 (hab ▸ p.end_mem_support)
      · exact ih (List.nodup_cons.mp hp).2 he

theorem FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
    {D : Digraph V} (p : FinitePath D) {x : V}
    (hx : x ∈ p.support) (hxa : x ≠ p.start) :
    ∃ y, (y, x) ∈ p.edgeSet :=
  Walk.exists_incoming_edge_of_mem_support_of_ne_start p.walk hx hxa

theorem FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
    {D : Digraph V} (p : FinitePath D) {x : V}
    (hx : x ∈ p.support) (hxb : x ≠ p.finish) :
    ∃ y, (x, y) ∈ p.edgeSet :=
  Walk.exists_outgoing_edge_of_mem_support_of_ne_end p.walk hx hxb

theorem FinitePath.no_incoming_edge_at_start
    {D : Digraph V} (p : FinitePath D) (y : V) :
    (y, p.start) ∉ p.edgeSet :=
  Walk.no_incoming_edge_at_start_of_isPath p.walk p.isPath y

theorem FinitePath.no_outgoing_edge_at_finish
    {D : Digraph V} (p : FinitePath D) (y : V) :
    (p.finish, y) ∉ p.edgeSet :=
  Walk.no_outgoing_edge_at_end_of_isPath p.walk p.isPath y

theorem Walk.edgeSet_out_unique_of_isPath
    {D : Digraph V} {a b : V} (p : Walk D a b) (hp : p.IsPath)
    {x y z : V} (hxy : (x, y) ∈ p.edgeSet)
    (hxz : (x, z) ∈ p.edgeSet) : y = z := by
  induction p with
  | nil => simp at hxy
  | @cons a c b e p ih =>
      simp only [Walk.edgeSet_cons, Set.mem_union,
        Set.mem_singleton_iff] at hxy hxz
      rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
      · exact (congrArg Prod.snd hxy).trans
          (congrArg Prod.snd hxz).symm
      · have hxa : x = a := congrArg Prod.fst hxy
        exact False.elim ((List.nodup_cons.mp hp).1
          (hxa ▸ (p.edgeSet_subset_support_prod hxz).1))
      · have hxa : x = a := congrArg Prod.fst hxz
        exact False.elim ((List.nodup_cons.mp hp).1
          (hxa ▸ (p.edgeSet_subset_support_prod hxy).1))
      · exact ih (List.nodup_cons.mp hp).2 hxy hxz

theorem Walk.edgeSet_in_unique_of_isPath
    {D : Digraph V} {a b : V} (p : Walk D a b) (hp : p.IsPath)
    {x y z : V} (hxz : (x, z) ∈ p.edgeSet)
    (hyz : (y, z) ∈ p.edgeSet) : x = y := by
  induction p with
  | nil => simp at hxz
  | @cons a c b e p ih =>
      simp only [Walk.edgeSet_cons, Set.mem_union,
        Set.mem_singleton_iff] at hxz hyz
      rcases hxz with hxz | hxz <;> rcases hyz with hyz | hyz
      · exact (congrArg Prod.fst hxz).trans
          (congrArg Prod.fst hyz).symm
      · have hzc : z = c := congrArg Prod.snd hxz
        exact False.elim
          (Walk.no_incoming_edge_at_start_of_isPath p
            (List.nodup_cons.mp hp).2 y (hzc ▸ hyz))
      · have hzc : z = c := congrArg Prod.snd hyz
        exact False.elim
          (Walk.no_incoming_edge_at_start_of_isPath p
            (List.nodup_cons.mp hp).2 x (hzc ▸ hxz))
      · exact ih (List.nodup_cons.mp hp).2 hxz hyz

theorem FinitePath.edgeSet_out_unique
    {D : Digraph V} (p : FinitePath D) {x y z : V}
    (hxy : (x, y) ∈ p.edgeSet) (hxz : (x, z) ∈ p.edgeSet) : y = z :=
  Walk.edgeSet_out_unique_of_isPath p.walk p.isPath hxy hxz

theorem FinitePath.edgeSet_in_unique
    {D : Digraph V} (p : FinitePath D) {x y z : V}
    (hxz : (x, z) ∈ p.edgeSet) (hyz : (y, z) ∈ p.edgeSet) : x = y :=
  Walk.edgeSet_in_unique_of_isPath p.walk p.isPath hxz hyz

theorem Ray.edgeSet_out_unique
    {D : Digraph V} (r : Ray D) {x y z : V}
    (hxy : (x, y) ∈ r.edgeSet) (hxz : (x, z) ∈ r.edgeSet) : y = z := by
  rcases hxy with ⟨n, hn⟩
  rcases hxz with ⟨m, hm⟩
  have hnm : n = m := r.injective
    ((congrArg Prod.fst hn).symm.trans (congrArg Prod.fst hm))
  subst m
  exact (congrArg Prod.snd hn).trans (congrArg Prod.snd hm).symm

theorem Ray.edgeSet_in_unique
    {D : Digraph V} (r : Ray D) {x y z : V}
    (hxz : (x, z) ∈ r.edgeSet) (hyz : (y, z) ∈ r.edgeSet) : x = y := by
  rcases hxz with ⟨n, hn⟩
  rcases hyz with ⟨m, hm⟩
  have hsucc : n + 1 = m + 1 := r.injective
    ((congrArg Prod.snd hn).symm.trans (congrArg Prod.snd hm))
  have hnm : n = m := by omega
  subst m
  exact (congrArg Prod.fst hn).trans (congrArg Prod.fst hm).symm

theorem Path.edgeSet_out_unique
    {D : Digraph V} (p : Path D) {x y z : V}
    (hxy : (x, y) ∈ p.edgeSet) (hxz : (x, z) ∈ p.edgeSet) : y = z := by
  rcases p with p | r
  · exact FinitePath.edgeSet_out_unique p hxy hxz
  · exact Ray.edgeSet_out_unique r hxy hxz

theorem Path.edgeSet_in_unique
    {D : Digraph V} (p : Path D) {x y z : V}
    (hxz : (x, z) ∈ p.edgeSet) (hyz : (y, z) ∈ p.edgeSet) : x = y := by
  rcases p with p | r
  · exact FinitePath.edgeSet_in_unique p hxz hyz
  · exact Ray.edgeSet_in_unique r hxz hyz

theorem familyEdges_out_unique {W : Set Γ.DPath}
    (hW : Γ.IsWarp W) {x y z : V}
    (hxy : (x, y) ∈ familyEdges W)
    (hxz : (x, z) ∈ familyEdges W) : y = z := by
  simp only [familyEdges, Set.mem_iUnion] at hxy hxz
  rcases hxy with ⟨p, hpW, hxyp⟩
  rcases hxz with ⟨q, hqW, hxzq⟩
  have hxp : x ∈ p.support := p.edgeSet_subset_support_prod hxyp |>.1
  have hxq : x ∈ q.support := q.edgeSet_subset_support_prod hxzq |>.1
  have hpq := DWeb.IsWarp.eq_of_mem_support hW hpW hqW hxp hxq
  subst q
  exact Path.edgeSet_out_unique p hxyp hxzq

theorem familyEdges_in_unique {W : Set Γ.DPath}
    (hW : Γ.IsWarp W) {x y z : V}
    (hxz : (x, z) ∈ familyEdges W)
    (hyz : (y, z) ∈ familyEdges W) : x = y := by
  simp only [familyEdges, Set.mem_iUnion] at hxz hyz
  rcases hxz with ⟨p, hpW, hxzp⟩
  rcases hyz with ⟨q, hqW, hyzq⟩
  have hzp : z ∈ p.support := p.edgeSet_subset_support_prod hxzp |>.2
  have hzq : z ∈ q.support := q.edgeSet_subset_support_prod hyzq |>.2
  have hpq := DWeb.IsWarp.eq_of_mem_support hW hpW hqW hzp hzq
  subst q
  exact Path.edgeSet_in_unique p hxzp hyzq

/-- A vertex has an incoming edge in an edge relation. -/
def HasIncoming (E : Set (V × V)) (x : V) : Prop :=
  ∃ y, (y, x) ∈ E

/-- A vertex has an outgoing edge in an edge relation. -/
def HasOutgoing (E : Set (V × V)) (x : V) : Prop :=
  ∃ y, (x, y) ∈ E

theorem FinitePath.source_ne_finish_of_mem_edgeSet
    {D : Digraph V} (p : FinitePath D) {x y : V}
    (hxy : (x, y) ∈ p.edgeSet) : x ≠ p.finish := by
  intro h
  subst x
  exact FinitePath.no_outgoing_edge_at_finish p y hxy

theorem FinitePath.target_ne_start_of_mem_edgeSet
    {D : Digraph V} (p : FinitePath D) {x y : V}
    (hxy : (x, y) ∈ p.edgeSet) : y ≠ p.start := by
  intro h
  subst y
  exact FinitePath.no_incoming_edge_at_start p x hxy

theorem FiniteTrace.exists_link_of_mem_edgeSet
    (Q : FiniteTrace Γ.graph) {e : V × V} (he : e ∈ Q.edgeSet) :
    ∃ i, e ∈ (Q.link i).path.edgeSet := by
  simpa only [FiniteTrace.edgeSet, Set.mem_iUnion] using he

theorem FiniteTrace.exists_forward_link_of_mem_edgeSet_not_familyEdges
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hback : BackwardLinksOn Z (.finite Q)) {e : V × V}
    (he : e ∈ Q.edgeSet) (heZ : e ∉ familyEdges Z) :
    ∃ i, (Q.link i).direction = .forward ∧
      e ∈ (Q.link i).path.edgeSet := by
  rcases Q.exists_link_of_mem_edgeSet he with ⟨i, hei⟩
  refine ⟨i, ?_, hei⟩
  cases hdir : (Q.link i).direction with
  | forward => rfl
  | backward =>
      rcases hback (Q.link i) ⟨i, rfl⟩ hdir with ⟨p, hpZ, hip⟩
      apply False.elim
      apply heZ
      simp only [familyEdges, Set.mem_iUnion]
      exact ⟨p, hpZ, hip.2 hei⟩

private theorem FiniteTrace.forward_edges_out_unique_of_lt
    (Q : FiniteTrace Γ.graph) {i j : Fin (Q.lastIndex + 1)}
    (hij : i < j) (hdi : (Q.link i).direction = .forward)
    (hdj : (Q.link j).direction = .forward) {x y z : V}
    (hxy : (x, y) ∈ (Q.link i).path.edgeSet)
    (hxz : (x, z) ∈ (Q.link j).path.edgeSet) : False := by
  have hcompat := Q.compatible i j hij
  simp only [CompatibleInOrder, hdi, hdj] at hcompat
  have hxi : x ∈ (Q.link i).path.support :=
    (Q.link i).path.edgeSet_subset_support_prod hxy |>.1
  have hxj : x ∈ (Q.link j).path.support :=
    (Q.link j).path.edgeSet_subset_support_prod hxz |>.1
  have hifinish : x ≠ (Q.link i).path.finish :=
    FinitePath.source_ne_finish_of_mem_edgeSet (Q.link i).path hxy
  have hjfinish : x ≠ (Q.link j).path.finish :=
    FinitePath.source_ne_finish_of_mem_edgeSet (Q.link j).path hxz
  rcases hcompat hxi hxj with h | h
  · exact hjfinish (by simpa [Link.exit, hdj] using h.2)
  · exact hifinish (by simpa [Link.exit, hdi] using h.1)

private theorem FiniteTrace.forward_edges_in_unique_of_lt
    (Q : FiniteTrace Γ.graph) {i j : Fin (Q.lastIndex + 1)}
    (hij : i < j) (hdi : (Q.link i).direction = .forward)
    (hdj : (Q.link j).direction = .forward) {x y z : V}
    (hxz : (x, z) ∈ (Q.link i).path.edgeSet)
    (hyz : (y, z) ∈ (Q.link j).path.edgeSet) : False := by
  have hcompat := Q.compatible i j hij
  simp only [CompatibleInOrder, hdi, hdj] at hcompat
  have hzi : z ∈ (Q.link i).path.support :=
    (Q.link i).path.edgeSet_subset_support_prod hxz |>.2
  have hzj : z ∈ (Q.link j).path.support :=
    (Q.link j).path.edgeSet_subset_support_prod hyz |>.2
  have histart : z ≠ (Q.link i).path.start :=
    FinitePath.target_ne_start_of_mem_edgeSet (Q.link i).path hxz
  have hjstart : z ≠ (Q.link j).path.start :=
    FinitePath.target_ne_start_of_mem_edgeSet (Q.link j).path hyz
  rcases hcompat hzi hzj with h | h
  · exact histart (by simpa [Link.entry, hdi] using h.1)
  · exact hjstart (by simpa [Link.entry, hdj] using h.2)

theorem FiniteTrace.forward_edges_out_unique
    (Q : FiniteTrace Γ.graph) {i j : Fin (Q.lastIndex + 1)}
    (hdi : (Q.link i).direction = .forward)
    (hdj : (Q.link j).direction = .forward) {x y z : V}
    (hxy : (x, y) ∈ (Q.link i).path.edgeSet)
    (hxz : (x, z) ∈ (Q.link j).path.edgeSet) : y = z := by
  by_cases hij : i = j
  · subst j
    exact FinitePath.edgeSet_out_unique (Q.link i).path hxy hxz
  · rcases lt_or_gt_of_ne hij with hij | hji
    · exact False.elim
        (Q.forward_edges_out_unique_of_lt hij hdi hdj hxy hxz)
    · exact False.elim
        (Q.forward_edges_out_unique_of_lt hji hdj hdi hxz hxy)

theorem FiniteTrace.forward_edges_in_unique
    (Q : FiniteTrace Γ.graph) {i j : Fin (Q.lastIndex + 1)}
    (hdi : (Q.link i).direction = .forward)
    (hdj : (Q.link j).direction = .forward) {x y z : V}
    (hxz : (x, z) ∈ (Q.link i).path.edgeSet)
    (hyz : (y, z) ∈ (Q.link j).path.edgeSet) : x = y := by
  by_cases hij : i = j
  · subst j
    exact FinitePath.edgeSet_in_unique (Q.link i).path hxz hyz
  · rcases lt_or_gt_of_ne hij with hij | hji
    · exact False.elim
        (Q.forward_edges_in_unique_of_lt hij hdi hdj hxz hyz)
    · exact False.elim
        (Q.forward_edges_in_unique_of_lt hji hdj hdi hyz hxz)

private theorem Link.finish_eq_exit_of_forward
    (l : Link Γ.graph) (h : l.direction = .forward) :
    l.path.finish = l.exit := by simp [Link.exit, h]

private theorem Link.start_eq_entry_of_forward
    (l : Link Γ.graph) (h : l.direction = .forward) :
    l.path.start = l.entry := by simp [Link.entry, h]

private theorem Link.start_eq_exit_of_backward
    (l : Link Γ.graph) (h : l.direction = .backward) :
    l.path.start = l.exit := by simp [Link.exit, h]

private theorem Link.finish_eq_entry_of_backward
    (l : Link Γ.graph) (h : l.direction = .backward) :
    l.path.finish = l.entry := by simp [Link.entry, h]

private theorem Link.ne_finish_of_mem_interior
    (l : Link Γ.graph) {x : V} (hx : x ∈ l.interior) :
    x ≠ l.path.finish := by
  intro h
  apply hx.2
  simp [Link.endpoints, h]

private theorem Link.ne_start_of_mem_interior
    (l : Link Γ.graph) {x : V} (hx : x ∈ l.interior) :
    x ≠ l.path.start := by
  intro h
  apply hx.2
  simp [Link.endpoints, h]

private theorem FiniteTrace.joins_of_val_eq_succ
    (Q : FiniteTrace Γ.graph) {i j : Fin (Q.lastIndex + 1)}
    (hij : j.1 = i.1 + 1) : (Q.link i).exit = (Q.link j).entry := by
  have hi : i.1 < Q.lastIndex := by omega
  let k : Fin Q.lastIndex := ⟨i.1, hi⟩
  have hki : Fin.castSucc k = i := Fin.ext (by rfl)
  have hkj : k.succ = j := Fin.ext (by simpa [k] using hij.symm)
  simpa [hki, hkj] using Q.joins k

/-- At the source of a forward trace edge, an outgoing edge of the reference
warp is one of the trace edges.  It is therefore removed when the forward
edge is inserted. -/
theorem FiniteTrace.reference_outgoing_mem_edgeSet_at_forward_source
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hQ : IsSwitchingAlternating Z (.finite Q))
    {i : Fin (Q.lastIndex + 1)}
    (hdi : (Q.link i).direction = .forward) {x y z : V}
    (hxy : (x, y) ∈ (Q.link i).path.edgeSet)
    (hxz : (x, z) ∈ familyEdges Z) :
    (x, z) ∈ Q.edgeSet := by
  have hxi : x ∈ (Q.link i).path.support :=
    (Q.link i).path.edgeSet_subset_support_prod hxy |>.1
  have hxZ : x ∈ Γ.vertexSet Z := by
    have hxz' := hxz
    simp only [familyEdges, Set.mem_iUnion] at hxz'
    rcases hxz' with ⟨p, hpZ, hxp⟩
    exact ⟨p, hpZ, p.edgeSet_subset_support_prod hxp |>.1⟩
  have hxfwd : x ∈ (AltPath.finite Q).directionVertices .forward := by
    simp only [AltPath.directionVertices, AltPath.links,
      FiniteTrace.links, Set.mem_iUnion, Set.mem_range]
    exact ⟨Q.link i, ⟨i, rfl⟩, hdi, hxi⟩
  have hxback : x ∈ (AltPath.finite Q).directionVertices .backward :=
    hQ.2.2 ⟨hxfwd, hxZ⟩
  simp only [AltPath.directionVertices, AltPath.links,
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
            (hxexit.trans (Link.finish_eq_exit_of_forward (Q.link i) hdi).symm))
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
      · exact (Q.link j).ne_finish_of_mem_interior hxint.1
    · exact (Q.link j).ne_finish_of_mem_interior
        ((hcompat.2 hadj ⟨hxj, hxi⟩).1)
  rcases FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
    (Q.link j).path hxj hx_ne_finish with ⟨w, hxw⟩
  have hxwZ : (x, w) ∈ familyEdges Z := by
    rcases hQ.1.2.1 (Q.link j) ⟨j, rfl⟩ hdj with ⟨p, hpZ, hjp⟩
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨p, hpZ, hjp.2 hxw⟩
  have hwz : w = z := familyEdges_out_unique hQ.1.1 hxwZ hxz
  subst w
  change (x, z) ∈ ⋃ k, (Q.link k).path.edgeSet
  exact Set.mem_iUnion.2 ⟨j, hxw⟩

theorem FiniteTrace.switchedEdges_out_unique
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hQ : IsSwitchingAlternating Z (.finite Q)) {x y z : V}
    (hxy : (x, y) ∈ switchedEdges Z (.finite Q))
    (hxz : (x, z) ∈ switchedEdges Z (.finite Q)) : y = z := by
  rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
  · exact familyEdges_out_unique hQ.1.1 hxy.1 hxz.1
  · rcases Q.exists_forward_link_of_mem_edgeSet_not_familyEdges
        hQ.1.2.1 hxz.1 hxz.2 with ⟨j, hdj, hxzj⟩
    exact False.elim (hxy.2
      (Q.reference_outgoing_mem_edgeSet_at_forward_source hQ hdj hxzj hxy.1))
  · rcases Q.exists_forward_link_of_mem_edgeSet_not_familyEdges
        hQ.1.2.1 hxy.1 hxy.2 with ⟨i, hdi, hxyi⟩
    exact False.elim (hxz.2
      (Q.reference_outgoing_mem_edgeSet_at_forward_source hQ hdi hxyi hxz.1))
  · rcases Q.exists_forward_link_of_mem_edgeSet_not_familyEdges
        hQ.1.2.1 hxy.1 hxy.2 with ⟨i, hdi, hxyi⟩
    rcases Q.exists_forward_link_of_mem_edgeSet_not_familyEdges
        hQ.1.2.1 hxz.1 hxz.2 with ⟨j, hdj, hxzj⟩
    exact Q.forward_edges_out_unique hdi hdj hxyi hxzj

/-- At the target of a forward trace edge, an incoming edge of the reference
warp is one of the trace edges. -/
theorem FiniteTrace.reference_incoming_mem_edgeSet_at_forward_target
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hQ : IsSwitchingAlternating Z (.finite Q))
    {i : Fin (Q.lastIndex + 1)}
    (hdi : (Q.link i).direction = .forward) {x y z : V}
    (hxz : (x, z) ∈ (Q.link i).path.edgeSet)
    (hyz : (y, z) ∈ familyEdges Z) :
    (y, z) ∈ Q.edgeSet := by
  have hzi : z ∈ (Q.link i).path.support :=
    (Q.link i).path.edgeSet_subset_support_prod hxz |>.2
  have hzZ : z ∈ Γ.vertexSet Z := by
    have hyz' := hyz
    simp only [familyEdges, Set.mem_iUnion] at hyz'
    rcases hyz' with ⟨p, hpZ, hyp⟩
    exact ⟨p, hpZ, p.edgeSet_subset_support_prod hyp |>.2⟩
  have hzfwd : z ∈ (AltPath.finite Q).directionVertices .forward := by
    simp only [AltPath.directionVertices, AltPath.links,
      FiniteTrace.links, Set.mem_iUnion, Set.mem_range]
    exact ⟨Q.link i, ⟨i, rfl⟩, hdi, hzi⟩
  have hzback : z ∈ (AltPath.finite Q).directionVertices .backward :=
    hQ.2.2 ⟨hzfwd, hzZ⟩
  simp only [AltPath.directionVertices, AltPath.links,
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
        have hjoin := Q.joins_of_val_eq_succ hadj
        have hzentry : z = (Q.link j).entry := hzexit.trans hjoin
        intro hzstart
        exact (Q.link j).nontrivial
          (hzstart.symm.trans
            (hzentry.trans (Link.finish_eq_entry_of_backward (Q.link j) hdj).symm))
      · exact False.elim
          (Set.disjoint_left.1 (hcompat.2 hadj) hzi hzj)
    · have hcompat := Q.compatible j i hji
      simp only [CompatibleInOrder, hdj, hdi] at hcompat
      by_cases hadj : i.1 = j.1 + 1
      · rcases hcompat.1 hadj hzj hzi with hzexit | hzint
        · have hjoin := Q.joins_of_val_eq_succ hadj
          have hzentry : z = (Q.link i).entry := hzexit.trans hjoin
          exact False.elim
            (FinitePath.target_ne_start_of_mem_edgeSet (Q.link i).path hxz
              (hzentry.trans
                (Link.start_eq_entry_of_forward (Q.link i) hdi).symm))
        · exact (Q.link j).ne_start_of_mem_interior hzint.1
      · exact (Q.link j).ne_start_of_mem_interior
          ((hcompat.2 hadj ⟨hzj, hzi⟩).1)
  rcases FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
    (Q.link j).path hzj hz_ne_start with ⟨w, hwz⟩
  have hwzZ : (w, z) ∈ familyEdges Z := by
    rcases hQ.1.2.1 (Q.link j) ⟨j, rfl⟩ hdj with ⟨p, hpZ, hjp⟩
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨p, hpZ, hjp.2 hwz⟩
  have hwy : w = y := familyEdges_in_unique hQ.1.1 hwzZ hyz
  subst w
  change (y, z) ∈ ⋃ k, (Q.link k).path.edgeSet
  exact Set.mem_iUnion.2 ⟨j, hwz⟩

theorem FiniteTrace.switchedEdges_in_unique
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hQ : IsSwitchingAlternating Z (.finite Q)) {x y z : V}
    (hxz : (x, z) ∈ switchedEdges Z (.finite Q))
    (hyz : (y, z) ∈ switchedEdges Z (.finite Q)) : x = y := by
  rcases hxz with hxz | hxz <;> rcases hyz with hyz | hyz
  · exact familyEdges_in_unique hQ.1.1 hxz.1 hyz.1
  · rcases Q.exists_forward_link_of_mem_edgeSet_not_familyEdges
        hQ.1.2.1 hyz.1 hyz.2 with ⟨j, hdj, hyzj⟩
    exact False.elim (hxz.2
      (Q.reference_incoming_mem_edgeSet_at_forward_target hQ hdj hyzj hxz.1))
  · rcases Q.exists_forward_link_of_mem_edgeSet_not_familyEdges
        hQ.1.2.1 hxz.1 hxz.2 with ⟨i, hdi, hxzi⟩
    exact False.elim (hyz.2
      (Q.reference_incoming_mem_edgeSet_at_forward_target hQ hdi hxzi hyz.1))
  · rcases Q.exists_forward_link_of_mem_edgeSet_not_familyEdges
        hQ.1.2.1 hxz.1 hxz.2 with ⟨i, hdi, hxzi⟩
    rcases Q.exists_forward_link_of_mem_edgeSet_not_familyEdges
        hQ.1.2.1 hyz.1 hyz.2 with ⟨j, hdj, hyzj⟩
    exact Q.forward_edges_in_unique hdi hdj hxzi hyzj

/-! ## The finite region affected by a finite trace -/

/-- The support of the unique reference-warp path through `x`, or the empty
set when `x` is not covered by the reference warp. -/
noncomputable def coveredPathSupport
    {Z : Set Γ.DPath} (hZ : Γ.IsWarp Z) (x : V) : Set V :=
  by
    classical
    exact if hx : x ∈ Γ.vertexSet Z then
      (DWeb.IsWarp.pathAt hZ hx).support
    else ∅

theorem coveredPathSupport_finite
    {Z : Set Γ.DPath} (hZ : Γ.IsWarp Z)
    (hZfin : Γ.HasFiniteCharacter Z) (x : V) :
    (coveredPathSupport hZ x).Finite := by
  classical
  simp only [coveredPathSupport]
  split_ifs with hx
  · rcases hZfin (DWeb.IsWarp.pathAt_mem hZ hx) with ⟨p, hp⟩
    rw [hp]
    exact p.support_finite
  · exact Set.finite_empty

theorem coveredPathSupport_eq_of_mem
    {Z : Set Γ.DPath} (hZ : Γ.IsWarp Z) {p : Γ.DPath}
    (hpZ : p ∈ Z) {x : V} (hxp : x ∈ p.support) :
    coveredPathSupport hZ x = p.support := by
  classical
  have hxZ : x ∈ Γ.vertexSet Z := ⟨p, hpZ, hxp⟩
  rw [coveredPathSupport, dif_pos hxZ]
  exact congrArg Path.support
    (DWeb.IsWarp.eq_pathAt_of_mem_support hZ hxZ hpZ hxp).symm

/-- All vertices on the trace, together with the complete reference paths
which the trace touches. -/
noncomputable def FiniteTrace.affectedVertices
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hZ : Γ.IsWarp Z) : Set V :=
  Q.vertexSet ∪ ⋃ x ∈ Q.vertexSet, coveredPathSupport hZ x

theorem FiniteTrace.affectedVertices_finite
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hZ : Γ.IsWarp Z) (hZfin : Γ.HasFiniteCharacter Z) :
    (Q.affectedVertices hZ).Finite := by
  classical
  apply Q.vertexSet_finite.union
  exact Q.vertexSet_finite.biUnion fun x _ ↦
    coveredPathSupport_finite hZ hZfin x

theorem FiniteTrace.vertexSet_subset_affectedVertices
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hZ : Γ.IsWarp Z) :
    Q.vertexSet ⊆ Q.affectedVertices hZ :=
  Set.subset_union_left

private theorem mem_affectedVertices_of_mem_coveredPathSupport
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hZ : Γ.IsWarp Z) {a x : V} (ha : a ∈ Q.vertexSet)
    (hx : x ∈ coveredPathSupport hZ a) :
    x ∈ Q.affectedVertices hZ := by
  right
  simp only [Set.mem_iUnion]
  exact ⟨a, ha, hx⟩

/-- The affected region is closed under either endpoint of every reference
edge. -/
theorem FiniteTrace.affected_of_familyEdge_of_affected_left
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hZ : Γ.IsWarp Z) {x y : V}
    (hxy : (x, y) ∈ familyEdges Z)
    (hx : x ∈ Q.affectedVertices hZ) :
    y ∈ Q.affectedVertices hZ := by
  classical
  simp only [familyEdges, Set.mem_iUnion] at hxy
  rcases hxy with ⟨p, hpZ, hxyp⟩
  have hxp : x ∈ p.support := p.edgeSet_subset_support_prod hxyp |>.1
  have hyp : y ∈ p.support := p.edgeSet_subset_support_prod hxyp |>.2
  rcases hx with hxQ | hxcovered
  · exact mem_affectedVertices_of_mem_coveredPathSupport Q hZ hxQ
      ((coveredPathSupport_eq_of_mem hZ hpZ hxp).symm ▸ hyp)
  · simp only [Set.mem_iUnion] at hxcovered
    rcases hxcovered with ⟨a, haQ, hxa⟩
    by_cases haZ : a ∈ Γ.vertexSet Z
    · rw [coveredPathSupport, dif_pos haZ] at hxa
      have hpath := DWeb.IsWarp.pathAt_mem hZ haZ
      have hpxeq : p = DWeb.IsWarp.pathAt hZ haZ :=
        DWeb.IsWarp.eq_of_mem_support hZ hpZ hpath hxp hxa
      exact mem_affectedVertices_of_mem_coveredPathSupport Q hZ haQ
        (by
          rw [coveredPathSupport, dif_pos haZ, ← hpxeq]
          exact hyp)
    · rw [coveredPathSupport, dif_neg haZ] at hxa
      exact False.elim (by simpa using hxa)

theorem FiniteTrace.affected_of_familyEdge_of_affected_right
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hZ : Γ.IsWarp Z) {x y : V}
    (hxy : (x, y) ∈ familyEdges Z)
    (hy : y ∈ Q.affectedVertices hZ) :
    x ∈ Q.affectedVertices hZ := by
  classical
  simp only [familyEdges, Set.mem_iUnion] at hxy
  rcases hxy with ⟨p, hpZ, hxyp⟩
  have hxp : x ∈ p.support := p.edgeSet_subset_support_prod hxyp |>.1
  have hyp : y ∈ p.support := p.edgeSet_subset_support_prod hxyp |>.2
  rcases hy with hyQ | hycovered
  · exact mem_affectedVertices_of_mem_coveredPathSupport Q hZ hyQ
      ((coveredPathSupport_eq_of_mem hZ hpZ hyp).symm ▸ hxp)
  · simp only [Set.mem_iUnion] at hycovered
    rcases hycovered with ⟨a, haQ, hya⟩
    by_cases haZ : a ∈ Γ.vertexSet Z
    · rw [coveredPathSupport, dif_pos haZ] at hya
      have hpath := DWeb.IsWarp.pathAt_mem hZ haZ
      have hpeq : p = DWeb.IsWarp.pathAt hZ haZ :=
        DWeb.IsWarp.eq_of_mem_support hZ hpZ hpath hyp hya
      exact mem_affectedVertices_of_mem_coveredPathSupport Q hZ haQ
        (by
          rw [coveredPathSupport, dif_pos haZ, ← hpeq]
          exact hxp)
    · rw [coveredPathSupport, dif_neg haZ] at hya
      exact False.elim (by simpa using hya)

theorem FiniteTrace.affected_of_switchedEdge_of_affected_left
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hZ : Γ.IsWarp Z) {x y : V}
    (hxy : (x, y) ∈ switchedEdges Z (.finite Q))
    (hx : x ∈ Q.affectedVertices hZ) :
    y ∈ Q.affectedVertices hZ := by
  rcases hxy with hxy | hxy
  · exact Q.affected_of_familyEdge_of_affected_left hZ hxy.1 hx
  · have hyQ : y ∈ Q.vertexSet := by
      rcases Q.exists_link_of_mem_edgeSet hxy.1 with ⟨i, hi⟩
      exact Set.mem_iUnion.2 ⟨i,
        (Q.link i).path.edgeSet_subset_support_prod hi |>.2⟩
    exact Q.vertexSet_subset_affectedVertices hZ hyQ

theorem FiniteTrace.affected_of_switchedEdge_of_affected_right
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hZ : Γ.IsWarp Z) {x y : V}
    (hxy : (x, y) ∈ switchedEdges Z (.finite Q))
    (hy : y ∈ Q.affectedVertices hZ) :
    x ∈ Q.affectedVertices hZ := by
  rcases hxy with hxy | hxy
  · exact Q.affected_of_familyEdge_of_affected_right hZ hxy.1 hy
  · have hxQ : x ∈ Q.vertexSet := by
      rcases Q.exists_link_of_mem_edgeSet hxy.1 with ⟨i, hi⟩
      exact Set.mem_iUnion.2 ⟨i,
        (Q.link i).path.edgeSet_subset_support_prod hi |>.1⟩
    exact Q.vertexSet_subset_affectedVertices hZ hxQ

/-- A finite set containing the entire weak switched component of `root`. -/
noncomputable def FiniteTrace.componentBound
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hZ : Γ.IsWarp Z) (root : V) : Set V :=
  Q.affectedVertices hZ ∪ coveredPathSupport hZ root ∪ {root}

theorem FiniteTrace.componentBound_finite
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hZ : Γ.IsWarp Z) (hZfin : Γ.HasFiniteCharacter Z)
    (root : V) : (Q.componentBound hZ root).Finite := by
  exact ((Q.affectedVertices_finite hZ hZfin).union
    (coveredPathSupport_finite hZ hZfin root)).union
      (Set.finite_singleton root)

private theorem FiniteTrace.componentBound_of_familyEdge_left
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hZ : Γ.IsWarp Z) (root : V) {x y : V}
    (hxy : (x, y) ∈ familyEdges Z)
    (hx : x ∈ Q.componentBound hZ root) :
    y ∈ Q.componentBound hZ root := by
  classical
  rcases hx with hxAB | hxroot
  · rcases hxAB with hxaff | hxcover
    · exact Or.inl (Or.inl
        (Q.affected_of_familyEdge_of_affected_left hZ hxy hxaff))
    · simp only [familyEdges, Set.mem_iUnion] at hxy
      rcases hxy with ⟨p, hpZ, hxyp⟩
      have hxp : x ∈ p.support := p.edgeSet_subset_support_prod hxyp |>.1
      have hyp : y ∈ p.support := p.edgeSet_subset_support_prod hxyp |>.2
      by_cases hrZ : root ∈ Γ.vertexSet Z
      · left
        right
        rw [coveredPathSupport, dif_pos hrZ] at hxcover ⊢
        have hpath := DWeb.IsWarp.pathAt_mem hZ hrZ
        have hpeq : p = DWeb.IsWarp.pathAt hZ hrZ :=
          DWeb.IsWarp.eq_of_mem_support hZ hpZ hpath hxp hxcover
        rw [← hpeq]
        exact hyp
      · rw [coveredPathSupport, dif_neg hrZ] at hxcover
        exact False.elim (by simpa using hxcover)
  · have hxroot' : x = root := by simpa using hxroot
    subst x
    simp only [familyEdges, Set.mem_iUnion] at hxy
    rcases hxy with ⟨p, hpZ, hrootp⟩
    left
    right
    rw [coveredPathSupport_eq_of_mem hZ hpZ
      (p.edgeSet_subset_support_prod hrootp |>.1)]
    exact p.edgeSet_subset_support_prod hrootp |>.2

private theorem FiniteTrace.componentBound_of_familyEdge_right
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hZ : Γ.IsWarp Z) (root : V) {x y : V}
    (hxy : (x, y) ∈ familyEdges Z)
    (hy : y ∈ Q.componentBound hZ root) :
    x ∈ Q.componentBound hZ root := by
  classical
  rcases hy with hyAB | hyroot
  · rcases hyAB with hyaff | hycover
    · exact Or.inl (Or.inl
        (Q.affected_of_familyEdge_of_affected_right hZ hxy hyaff))
    · simp only [familyEdges, Set.mem_iUnion] at hxy
      rcases hxy with ⟨p, hpZ, hxyp⟩
      have hxp : x ∈ p.support := p.edgeSet_subset_support_prod hxyp |>.1
      have hyp : y ∈ p.support := p.edgeSet_subset_support_prod hxyp |>.2
      by_cases hrZ : root ∈ Γ.vertexSet Z
      · left
        right
        rw [coveredPathSupport, dif_pos hrZ] at hycover ⊢
        have hpath := DWeb.IsWarp.pathAt_mem hZ hrZ
        have hpeq : p = DWeb.IsWarp.pathAt hZ hrZ :=
          DWeb.IsWarp.eq_of_mem_support hZ hpZ hpath hyp hycover
        rw [← hpeq]
        exact hxp
      · rw [coveredPathSupport, dif_neg hrZ] at hycover
        exact False.elim (by simpa using hycover)
  · have hyroot' : y = root := by simpa using hyroot
    subst y
    simp only [familyEdges, Set.mem_iUnion] at hxy
    rcases hxy with ⟨p, hpZ, hproot⟩
    left
    right
    rw [coveredPathSupport_eq_of_mem hZ hpZ
      (p.edgeSet_subset_support_prod hproot |>.2)]
    exact p.edgeSet_subset_support_prod hproot |>.1

theorem FiniteTrace.componentBound_closed
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hZ : Γ.IsWarp Z) (root : V) {x y : V}
    (hstep : (x, y) ∈ switchedEdges Z (.finite Q) ∨
      (y, x) ∈ switchedEdges Z (.finite Q))
    (hx : x ∈ Q.componentBound hZ root) :
    y ∈ Q.componentBound hZ root := by
  rcases hstep with hxy | hyx
  · rcases hxy with hxy | hxy
    · exact Q.componentBound_of_familyEdge_left hZ root hxy.1 hx
    · left
      left
      rcases Q.exists_link_of_mem_edgeSet hxy.1 with ⟨i, hi⟩
      exact Q.vertexSet_subset_affectedVertices hZ
        (Set.mem_iUnion.2 ⟨i,
          (Q.link i).path.edgeSet_subset_support_prod hi |>.2⟩)
  · rcases hyx with hyx | hyx
    · exact Q.componentBound_of_familyEdge_right hZ root hyx.1 hx
    · left
      left
      rcases Q.exists_link_of_mem_edgeSet hyx.1 with ⟨i, hi⟩
      exact Q.vertexSet_subset_affectedVertices hZ
        (Set.mem_iUnion.2 ⟨i,
          (Q.link i).path.edgeSet_subset_support_prod hi |>.1⟩)

/-- Weak connectivity in a directed edge relation. -/
def WeaklyConnectedBy (E : Set (V × V)) (x y : V) : Prop :=
  Relation.ReflTransGen (fun a b ↦ (a, b) ∈ E ∨ (b, a) ∈ E) x y

theorem FiniteTrace.weaklyConnectedBy_switched_subset_componentBound
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hZ : Γ.IsWarp Z) (root : V) :
    {x | WeaklyConnectedBy (switchedEdges Z (.finite Q)) root x} ⊆
      Q.componentBound hZ root := by
  intro x hx
  change Relation.ReflTransGen _ root x at hx
  induction hx with
  | refl => exact Or.inr (by simp)
  | tail hreach hstep ih => exact Q.componentBound_closed hZ root hstep ih

theorem FiniteTrace.weaklyConnectedBy_switched_finite
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hZ : Γ.IsWarp Z) (hZfin : Γ.HasFiniteCharacter Z)
    (root : V) :
    {x | WeaklyConnectedBy (switchedEdges Z (.finite Q)) root x}.Finite :=
  (Q.componentBound_finite hZ hZfin root).subset
    (Q.weaklyConnectedBy_switched_subset_componentBound hZ root)

/-- Every quotient component of the finite switched relation has finite
support.  This is the bridge from the concrete affected-region argument to
the generic locally-biunique relation decomposition. -/
theorem FiniteTrace.switched_componentSupports_finite
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hZ : Γ.IsWarp Z) (hZfin : Γ.HasFiniteCharacter Z) :
    ∀ c : RelationComponents.Component (switchedEdges Z (.finite Q)),
      (RelationComponents.componentSupport (switchedEdges Z (.finite Q)) c).Finite := by
  apply RelationComponents.finite_componentSupports_of_roots
  intro root
  change
    {x | Relation.ReflTransGen
      (fun a b ↦ (a, b) ∈ switchedEdges Z (.finite Q) ∨
        (b, a) ∈ switchedEdges Z (.finite Q)) root x}.Finite
  exact Q.weaklyConnectedBy_switched_finite hZ hZfin root

/-! ## Singleton components are untouched -/

private theorem isolated_no_incoming_family
    {Z : Set Γ.DPath} (hZ : Γ.IsWarp Z) {x : V}
    (hxiso : x ∈ isolatedVertices Z) :
    ¬ HasIncoming (familyEdges Z) x := by
  rintro ⟨y, hy⟩
  simp only [familyEdges, Set.mem_iUnion] at hy
  rcases hy with ⟨p, hpZ, hyp⟩
  have hxp : x ∈ p.support := p.edgeSet_subset_support_prod hyp |>.2
  have hp0 : p = Γ.trivialPath x :=
    DWeb.IsWarp.eq_of_mem_support hZ hpZ hxiso hxp (by simp)
  subst p
  simpa [DWeb.trivialPath, Path.trivial, FinitePath.edgeSet,
    FinitePath.trivial, Walk.edgeSet] using hyp

private theorem isolated_no_outgoing_family
    {Z : Set Γ.DPath} (hZ : Γ.IsWarp Z) {x : V}
    (hxiso : x ∈ isolatedVertices Z) :
    ¬ HasOutgoing (familyEdges Z) x := by
  rintro ⟨y, hy⟩
  simp only [familyEdges, Set.mem_iUnion] at hy
  rcases hy with ⟨p, hpZ, hyp⟩
  have hxp : x ∈ p.support := p.edgeSet_subset_support_prod hyp |>.1
  have hp0 : p = Γ.trivialPath x :=
    DWeb.IsWarp.eq_of_mem_support hZ hpZ hxiso hxp (by simp)
  subst p
  simpa [DWeb.trivialPath, Path.trivial, FinitePath.edgeSet,
    FinitePath.trivial, Walk.edgeSet] using hyp

private theorem FiniteTrace.not_mem_backwardVertices_of_mem_isolated
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hQ : IsSwitchingAlternating Z (.finite Q)) {x : V}
    (hxiso : x ∈ isolatedVertices Z) :
    x ∉ (AltPath.finite Q).directionVertices .backward := by
  intro hxback
  simp only [AltPath.directionVertices, AltPath.links,
    FiniteTrace.links, Set.mem_iUnion, Set.mem_range] at hxback
  rcases hxback with ⟨l, ⟨i, rfl⟩, hdi, hxl⟩
  rcases hQ.1.2.1 (Q.link i) ⟨i, rfl⟩ hdi with ⟨p, hpZ, hip⟩
  have hxp : x ∈ p.support := hip.1 hxl
  have hp0 : p = Γ.trivialPath x :=
    DWeb.IsWarp.eq_of_mem_support hQ.1.1 hpZ hxiso hxp (by simp)
  have hsupp : (Q.link i).path.support ⊆ ({x} : Set V) := by
    rw [← Γ.support_trivialPath x, ← hp0]
    exact hip.1
  have hstart : (Q.link i).path.start = x := by
    simpa using hsupp (Q.link i).path.start_mem_support
  have hfinish : (Q.link i).path.finish = x := by
    simpa using hsupp (Q.link i).path.finish_mem_support
  exact (Q.link i).nontrivial (hstart.trans hfinish.symm)

theorem FiniteTrace.not_mem_vertexSet_of_mem_isolated
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hQ : IsSwitchingAlternating Z (.finite Q)) {x : V}
    (hxiso : x ∈ isolatedVertices Z) :
    x ∉ Q.vertexSet := by
  intro hxQ
  simp only [FiniteTrace.vertexSet, Set.mem_iUnion] at hxQ
  rcases hxQ with ⟨i, hxi⟩
  cases hdi : (Q.link i).direction with
  | backward =>
      apply Q.not_mem_backwardVertices_of_mem_isolated hQ hxiso
      simp only [AltPath.directionVertices, AltPath.links,
        FiniteTrace.links, Set.mem_iUnion, Set.mem_range]
      exact ⟨Q.link i, ⟨i, rfl⟩, hdi, hxi⟩
  | forward =>
      have hxfwd : x ∈ (AltPath.finite Q).directionVertices .forward := by
        simp only [AltPath.directionVertices, AltPath.links,
          FiniteTrace.links, Set.mem_iUnion, Set.mem_range]
        exact ⟨Q.link i, ⟨i, rfl⟩, hdi, hxi⟩
      have hxZ : x ∈ Γ.vertexSet Z := ⟨Γ.trivialPath x, hxiso, by simp⟩
      exact Q.not_mem_backwardVertices_of_mem_isolated hQ hxiso
        (hQ.2.2 ⟨hxfwd, hxZ⟩)

theorem FiniteTrace.isolated_not_incident_switched
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hQ : IsSwitchingAlternating Z (.finite Q)) {x : V}
    (hxiso : x ∈ isolatedVertices Z) :
    (¬ HasIncoming (switchedEdges Z (.finite Q)) x) ∧
      (¬ HasOutgoing (switchedEdges Z (.finite Q)) x) := by
  constructor
  · rintro ⟨y, hyx⟩
    rcases hyx with hyx | hyx
    · exact isolated_no_incoming_family hQ.1.1 hxiso ⟨y, hyx.1⟩
    · have hxQ : x ∈ Q.vertexSet := by
        rcases Q.exists_link_of_mem_edgeSet hyx.1 with ⟨i, hi⟩
        exact Set.mem_iUnion.2 ⟨i,
          (Q.link i).path.edgeSet_subset_support_prod hi |>.2⟩
      exact Q.not_mem_vertexSet_of_mem_isolated hQ hxiso hxQ
  · rintro ⟨y, hxy⟩
    rcases hxy with hxy | hxy
    · exact isolated_no_outgoing_family hQ.1.1 hxiso ⟨y, hxy.1⟩
    · have hxQ : x ∈ Q.vertexSet := by
        rcases Q.exists_link_of_mem_edgeSet hxy.1 with ⟨i, hi⟩
        exact Set.mem_iUnion.2 ⟨i,
          (Q.link i).path.edgeSet_subset_support_prod hi |>.1⟩
      exact Q.not_mem_vertexSet_of_mem_isolated hQ hxiso hxQ

/-! ## The finite cyclowarp decomposition -/

/-- A finite alternating trace on a finite-character warp realizes the raw
application data by a genuine cyclowarp whose path part consists entirely of
finite paths.  Thus deleting the cycle components leaves a finite-character
warp, exactly as in Definition 4.3. -/
theorem FiniteTrace.exists_application_cyclowarp
    {Z : Set Γ.DPath} (Q : FiniteTrace Γ.graph)
    (hQ : IsSwitchingAlternating Z (.finite Q))
    (hZfin : Γ.HasFiniteCharacter Z) :
    ∃ C : Cyclowarp Γ,
      C.edges = (Cyclowarp.application Z (.finite Q)).edges ∧
      C.isolated = (Cyclowarp.application Z (.finite Q)).isolated ∧
      Γ.HasFiniteCharacter C.pathPart := by
  have hfinite := Q.switched_componentSupports_finite hQ.1.1 hZfin
  have hI : ∀ x ∈ isolatedVertices Z, ∀ y,
      (x, y) ∉ switchedEdges Z (.finite Q) ∧
        (y, x) ∉ switchedEdges Z (.finite Q) := by
    intro x hx y
    have hno := Q.isolated_not_incident_switched hQ hx
    exact ⟨fun hxy ↦ hno.2 ⟨y, hxy⟩, fun hyx ↦ hno.1 ⟨y, hyx⟩⟩
  rcases RelationComponents.exists_cyclowarp_of_finite_componentSupports
      Γ (switchedEdges Z (.finite Q)) (isolatedVertices Z)
      (Cyclowarp.application Z (.finite Q)).edges_in_graph
      (fun hxy hxz ↦ Q.switchedEdges_out_unique hQ hxy hxz)
      (fun hxz hyz ↦ Q.switchedEdges_in_unique hQ hxz hyz)
      hfinite hI with ⟨C, hCedges, hCisolated, hCfin⟩
  exact ⟨C, by simpa using hCedges, by simpa using hCisolated, hCfin⟩

theorem initialSet_eq_vertexSet_diff_hasIncoming
    {W : Set Γ.DPath} (hW : Γ.IsWarp W)
    (hWfin : Γ.HasFiniteCharacter W) :
    Γ.initialSet W =
      Γ.vertexSet W \ {x | HasIncoming (familyEdges W) x} := by
  ext x
  constructor
  · rintro ⟨p, hpW, rfl⟩
    refine ⟨⟨p, hpW, p.initial_mem_support⟩, ?_⟩
    rintro ⟨y, hy⟩
    simp only [familyEdges, Set.mem_iUnion] at hy
    rcases hy with ⟨q, hqW, hyq⟩
    have hstartq : p.initial ∈ q.support :=
      q.edgeSet_subset_support_prod hyq |>.2
    have hpq : p = q :=
      DWeb.IsWarp.eq_of_mem_support hW hpW hqW p.initial_mem_support hstartq
    subst q
    rcases hWfin hpW with ⟨pfin, rfl⟩
    exact FinitePath.no_incoming_edge_at_start pfin y hyq
  · rintro ⟨⟨p, hpW, hxp⟩, hxno⟩
    rcases hWfin hpW with ⟨pfin, rfl⟩
    refine ⟨Sum.inl pfin, hpW, ?_⟩
    by_contra hxstart
    rcases FinitePath.exists_incoming_edge_of_mem_support_of_ne_start pfin hxp
      (fun h ↦ hxstart h.symm)
      with ⟨y, hy⟩
    exact hxno ⟨y, by
      simp only [familyEdges, Set.mem_iUnion]
      exact ⟨Sum.inl pfin, hpW, hy⟩⟩

theorem terminalFrontier_eq_vertexSet_diff_hasOutgoing
    {W : Set Γ.DPath} (hW : Γ.IsWarp W)
    (hWfin : Γ.HasFiniteCharacter W) :
    Γ.terminalFrontier W =
      Γ.vertexSet W \ {x | HasOutgoing (familyEdges W) x} := by
  ext x
  constructor
  · rintro ⟨p, hpW, hpx⟩
    refine ⟨⟨p, hpW, Γ.terminal_mem_support hpx⟩, ?_⟩
    rintro ⟨y, hy⟩
    simp only [familyEdges, Set.mem_iUnion] at hy
    rcases hy with ⟨q, hqW, hyq⟩
    have hxq : x ∈ q.support := q.edgeSet_subset_support_prod hyq |>.1
    have hxp : x ∈ p.support := Γ.terminal_mem_support hpx
    have hpq : p = q := DWeb.IsWarp.eq_of_mem_support hW hpW hqW hxp hxq
    subst q
    rcases hWfin hpW with ⟨pfin, rfl⟩
    simp only [DWeb.terminal?_finite, Option.some.injEq] at hpx
    subst x
    exact FinitePath.no_outgoing_edge_at_finish pfin y hyq
  · rintro ⟨⟨p, hpW, hxp⟩, hxno⟩
    rcases hWfin hpW with ⟨pfin, rfl⟩
    refine ⟨Sum.inl pfin, hpW, ?_⟩
    simp only [DWeb.terminal?_finite, Option.some.injEq]
    by_contra hxfinish
    rcases FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish pfin hxp
      (fun h ↦ hxfinish h.symm)
      with ⟨y, hy⟩
    exact hxno ⟨y, by
      simp only [familyEdges, Set.mem_iUnion]
      exact ⟨Sum.inl pfin, hpW, hy⟩⟩

private theorem Walk.eq_nil_of_isPath {D : Digraph V} {x : V}
    (p : Walk D x x) (hp : p.IsPath) : p = .nil := by
  cases p with
  | nil => rfl
  | @cons _ y _ h q =>
      exact False.elim ((List.nodup_cons.mp hp).1 q.end_mem_support)

private theorem FinitePath.eq_trivial_of_start_eq_finish
    {D : Digraph V} (p : FinitePath D) (h : p.start = p.finish) :
    p = FinitePath.trivial D p.start := by
  rcases p with ⟨start, finish, walk, isPath⟩
  dsimp at h ⊢
  subst finish
  have hw : walk = .nil := Walk.eq_nil_of_isPath walk isPath
  subst walk
  rfl

theorem isolatedVertices_subset_vertexSet (W : Set Γ.DPath) :
    isolatedVertices W ⊆ Γ.vertexSet W := by
  intro x hx
  exact ⟨Γ.trivialPath x, hx, by simp⟩

/-- For a finite-character family, the edge relation together with its
explicit singleton components determines its whole vertex set. -/
theorem vertexSet_eq_isolated_union_incident
    {W : Set Γ.DPath} (hWfin : Γ.HasFiniteCharacter W) :
    Γ.vertexSet W = isolatedVertices W ∪
      {x | HasIncoming (familyEdges W) x ∨
        HasOutgoing (familyEdges W) x} := by
  ext x
  constructor
  · rintro ⟨p, hpW, hxp⟩
    rcases hWfin hpW with ⟨pfin, rfl⟩
    by_cases hends : pfin.start = pfin.finish
    · left
      have hp0 := FinitePath.eq_trivial_of_start_eq_finish pfin hends
      have hp0' : (Sum.inl pfin : Γ.DPath) = Γ.trivialPath pfin.start := by
        rw [hp0]
        rfl
      rw [hp0'] at hpW hxp
      have hx : x = pfin.start := by
        simpa using hxp
      subst x
      exact hpW
    · by_cases hxstart : x = pfin.start
      · right
        right
        subst x
        rcases FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish pfin
          pfin.start_mem_support hends with ⟨y, hy⟩
        exact ⟨y, by
          simp only [familyEdges, Set.mem_iUnion]
          exact ⟨Sum.inl pfin, hpW, hy⟩⟩
      · right
        left
        rcases FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
          pfin hxp hxstart
          with ⟨y, hy⟩
        exact ⟨y, by
          simp only [familyEdges, Set.mem_iUnion]
          exact ⟨Sum.inl pfin, hpW, hy⟩⟩
  · rintro (hxiso | hxinc)
    · exact isolatedVertices_subset_vertexSet W hxiso
    · rcases hxinc with ⟨y, hy⟩ | ⟨y, hy⟩
      · simp only [familyEdges, Set.mem_iUnion] at hy
        rcases hy with ⟨p, hpW, hyp⟩
        exact ⟨p, hpW, p.edgeSet_subset_support_prod hyp |>.2⟩
      · simp only [familyEdges, Set.mem_iUnion] at hy
        rcases hy with ⟨p, hpW, hyp⟩
        exact ⟨p, hpW, p.edgeSet_subset_support_prod hyp |>.1⟩

theorem not_hasIncoming_of_mem_isolatedVertices
    {W : Set Γ.DPath} (hW : Γ.IsWarp W) {x : V}
    (hx : x ∈ isolatedVertices W) :
    ¬ HasIncoming (familyEdges W) x := by
  rintro ⟨y, hy⟩
  simp only [familyEdges, Set.mem_iUnion] at hy
  rcases hy with ⟨p, hpW, hyp⟩
  have hxp : x ∈ p.support := p.edgeSet_subset_support_prod hyp |>.2
  have hp0 : p = Γ.trivialPath x :=
    DWeb.IsWarp.eq_of_mem_support hW hpW hx hxp (by simp)
  subst p
  simpa [DWeb.trivialPath, Path.trivial, FinitePath.edgeSet,
    FinitePath.trivial, Walk.edgeSet] using hyp

theorem not_hasOutgoing_of_mem_isolatedVertices
    {W : Set Γ.DPath} (hW : Γ.IsWarp W) {x : V}
    (hx : x ∈ isolatedVertices W) :
    ¬ HasOutgoing (familyEdges W) x := by
  rintro ⟨y, hy⟩
  simp only [familyEdges, Set.mem_iUnion] at hy
  rcases hy with ⟨p, hpW, hyp⟩
  have hxp : x ∈ p.support := p.edgeSet_subset_support_prod hyp |>.1
  have hp0 : p = Γ.trivialPath x :=
    DWeb.IsWarp.eq_of_mem_support hW hpW hx hxp (by simp)
  subst p
  simpa [DWeb.trivialPath, Path.trivial, FinitePath.edgeSet,
    FinitePath.trivial, Walk.edgeSet] using hyp

/-- Initial vertices expressed using only edge incidence and the explicit
singleton-component set. -/
theorem initialSet_eq_isolated_union_outgoing_boundary
    {W : Set Γ.DPath} (hW : Γ.IsWarp W)
    (hWfin : Γ.HasFiniteCharacter W) :
    Γ.initialSet W = isolatedVertices W ∪
      {x | HasOutgoing (familyEdges W) x ∧
        ¬ HasIncoming (familyEdges W) x} := by
  rw [initialSet_eq_vertexSet_diff_hasIncoming hW hWfin,
    vertexSet_eq_isolated_union_incident hWfin]
  ext x
  constructor
  · rintro ⟨hx, hnin⟩
    rcases hx with hxiso | hin | hout
    · exact Or.inl hxiso
    · exact False.elim (hnin hin)
    · exact Or.inr ⟨hout, hnin⟩
  · rintro (hxiso | ⟨hout, hnin⟩)
    · exact ⟨Or.inl hxiso,
        not_hasIncoming_of_mem_isolatedVertices hW hxiso⟩
    · exact ⟨Or.inr (Or.inr hout), hnin⟩

/-- Finite terminals expressed using only edge incidence and the explicit
singleton-component set. -/
theorem terminalFrontier_eq_isolated_union_incoming_boundary
    {W : Set Γ.DPath} (hW : Γ.IsWarp W)
    (hWfin : Γ.HasFiniteCharacter W) :
    Γ.terminalFrontier W = isolatedVertices W ∪
      {x | HasIncoming (familyEdges W) x ∧
        ¬ HasOutgoing (familyEdges W) x} := by
  rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing hW hWfin,
    vertexSet_eq_isolated_union_incident hWfin]
  ext x
  constructor
  · rintro ⟨hx, hnout⟩
    rcases hx with hxiso | hin | hout
    · exact Or.inl hxiso
    · exact Or.inr ⟨hin, hnout⟩
    · exact False.elim (hnout hout)
  · rintro (hxiso | ⟨hin, hnout⟩)
    · exact ⟨Or.inl hxiso,
        not_hasOutgoing_of_mem_isolatedVertices hW hxiso⟩
    · exact ⟨Or.inr (Or.inl hin), hnout⟩

/-- Equality of edge sets and explicitly retained singleton components is
enough to identify the initial frontier of finite-character warps. -/
theorem initialSet_eq_of_edges_isolated_eq
    {W W' : Set Γ.DPath} (hW : Γ.IsWarp W)
    (hW' : Γ.IsWarp W') (hWfin : Γ.HasFiniteCharacter W)
    (hW'fin : Γ.HasFiniteCharacter W')
    (hedges : familyEdges W = familyEdges W')
    (hiso : isolatedVertices W = isolatedVertices W') :
    Γ.initialSet W = Γ.initialSet W' := by
  rw [initialSet_eq_vertexSet_diff_hasIncoming hW hWfin,
    initialSet_eq_vertexSet_diff_hasIncoming hW' hW'fin,
    vertexSet_eq_isolated_union_incident hWfin,
    vertexSet_eq_isolated_union_incident hW'fin, hedges, hiso]

/-- Equality of edge sets and explicitly retained singleton components is
enough to identify the terminal frontier of finite-character warps. -/
theorem terminalFrontier_eq_of_edges_isolated_eq
    {W W' : Set Γ.DPath} (hW : Γ.IsWarp W)
    (hW' : Γ.IsWarp W') (hWfin : Γ.HasFiniteCharacter W)
    (hW'fin : Γ.HasFiniteCharacter W')
    (hedges : familyEdges W = familyEdges W')
    (hiso : isolatedVertices W = isolatedVertices W') :
    Γ.terminalFrontier W = Γ.terminalFrontier W' := by
  rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing hW hWfin,
    terminalFrontier_eq_vertexSet_diff_hasOutgoing hW' hW'fin,
    vertexSet_eq_isolated_union_incident hWfin,
    vertexSet_eq_isolated_union_incident hW'fin, hedges, hiso]

/-! ## Confinement of a bracket switch -/

theorem edgeSet_subset_familyEdges_of_isFragmentOf
    {p : FinitePath Γ.graph} {W : Set Γ.DPath}
    (hp : IsFragmentOf p W) : p.edgeSet ⊆ familyEdges W := by
  rcases hp with ⟨q, hqW, hpq⟩
  intro e he
  simp only [familyEdges, Set.mem_iUnion]
  exact ⟨q, hqW, hpq.2 he⟩

/-- Every edge of a `[U,Z]`-alternating path belongs to one of the two
ambient warps: forward links lie on `U`, and backward links lie on `Z`. -/
theorem AltPath.edgeSet_subset_familyEdges_union_of_isBracketAlternating
    {U Z : Set Γ.DPath} {T : AltPath Γ.graph}
    (hT : IsBracketAlternating U Z T) :
    T.edgeSet ⊆ familyEdges Z ∪ familyEdges U := by
  intro e he
  rw [T.edgeSet_eq_iUnion_links] at he
  simp only [Set.mem_iUnion] at he
  rcases he with ⟨l, hlT, hel⟩
  cases hdir : l.direction with
  | forward =>
      exact Or.inr (edgeSet_subset_familyEdges_of_isFragmentOf
        (hT.2 l hlT hdir) hel)
  | backward =>
      exact Or.inl (edgeSet_subset_familyEdges_of_isFragmentOf
        (hT.1.2.1 l hlT hdir) hel)

/-- The switched edge relation for a bracket alternating path is confined
to the edge union of the two bracket warps. -/
theorem switchedEdges_subset_familyEdges_union_of_isBracketAlternating
    {U Z : Set Γ.DPath} {T : AltPath Γ.graph}
    (hT : IsBracketAlternating U Z T) :
    switchedEdges Z T ⊆ familyEdges Z ∪ familyEdges U := by
  intro e he
  rcases he with he | he
  · exact Or.inl he.1
  · exact T.edgeSet_subset_familyEdges_union_of_isBracketAlternating hT he.1

/-- Any concrete cyclowarp realization of a bracket switch inherits its
edge confinement.  This formulation is convenient for the finite reducing
switch, where cycle components are discarded afterwards. -/
theorem Cyclowarp.edges_subset_familyEdges_union_of_application
    {U Z : Set Γ.DPath} {T : AltPath Γ.graph}
    (hT : IsBracketAlternating U Z T) (C : Cyclowarp Γ)
    (hC : C.edges = (Cyclowarp.application Z T).edges) :
    C.edges ⊆ familyEdges Z ∪ familyEdges U := by
  rw [hC, Cyclowarp.application_edges]
  exact switchedEdges_subset_familyEdges_union_of_isBracketAlternating hT

theorem Cyclowarp.pathPart_edges_subset_familyEdges_union_of_application
    {U Z : Set Γ.DPath} {T : AltPath Γ.graph}
    (hT : IsBracketAlternating U Z T) (C : Cyclowarp Γ)
    (hC : C.edges = (Cyclowarp.application Z T).edges) :
    familyEdges C.pathPart ⊆ familyEdges Z ∪ familyEdges U := by
  have hsub : familyEdges C.pathPart ⊆ C.edges := by
    intro e he
    exact Or.inl he
  exact hsub.trans
    (C.edges_subset_familyEdges_union_of_application hT hC)

theorem Cyclowarp.isolated_subset_vertexSet_of_application
    {Z : Set Γ.DPath} {T : AltPath Γ.graph}
    (C : Cyclowarp Γ)
    (hC : C.isolated = (Cyclowarp.application Z T).isolated) :
    C.isolated ⊆ Γ.vertexSet Z := by
  rw [hC, Cyclowarp.application_isolated]
  exact isolatedVertices_subset_vertexSet Z

end Alternating
end Erdos599
