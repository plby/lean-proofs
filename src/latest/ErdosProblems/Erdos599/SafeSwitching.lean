/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Alternating

/-!
# Safe switching

This file proves Aharoni--Berger Lemma 4.9: applying a safe alternating path
to a finite-character warp has an honest finite-character warp realization.
-/

namespace Erdos599

open Set DirectedPath

universe u

namespace Alternating

variable {V : Type u} {Γ : DWeb V}

/-! ## Incidence of finite path edge sets -/

/-- The initial vertex of a simple walk is never the target of one of its
edges. -/
theorem Walk.start_ne_edge_target {D : Digraph V} {a b : V}
    (p : Walk D a b) (hp : p.IsPath) {e : V × V}
    (he : e ∈ p.edgeSet) : a ≠ e.2 := by
  induction p with
  | nil => simp at he
  | @cons a c b h p ih =>
      simp only [Walk.edgeSet_cons, Set.mem_union,
        Set.mem_singleton_iff] at he
      have ha : a ∉ p.support := (List.nodup_cons.mp hp).1
      rcases he with rfl | he
      · exact fun hac ↦ ha (hac ▸ p.start_mem_support)
      · exact fun hae ↦
          ha (hae ▸ (p.edgeSet_subset_support_prod he).2)

/-- The terminal vertex of a simple walk is never the source of one of its
edges. -/
theorem Walk.finish_ne_edge_source {D : Digraph V} {a b : V}
    (p : Walk D a b) (hp : p.IsPath) {e : V × V}
    (he : e ∈ p.edgeSet) : b ≠ e.1 := by
  induction p with
  | nil => simp at he
  | @cons a c b h p ih =>
      simp only [Walk.edgeSet_cons, Set.mem_union,
        Set.mem_singleton_iff] at he
      rcases he with rfl | he
      · intro hba
        exact (List.nodup_cons.mp hp).1 (hba ▸ p.end_mem_support)
      · exact ih (List.nodup_cons.mp hp).2 he

/-- A simple walk has at most one outgoing edge at every vertex. -/
theorem Walk.edgeSet_rightUnique {D : Digraph V} {a b : V}
    (p : Walk D a b) (hp : p.IsPath) :
    Relator.RightUnique (fun x y ↦ (x, y) ∈ p.edgeSet) := by
  intro x y z hxy hxz
  induction p with
  | nil => simp at hxy
  | @cons a c b h p ih =>
      simp only [Walk.edgeSet_cons, Set.mem_union,
        Set.mem_singleton_iff] at hxy hxz
      rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
      · simpa using congrArg Prod.snd (hxy.trans hxz.symm)
      · have hxa : x = a := congrArg Prod.fst hxy
        exact False.elim ((List.nodup_cons.mp hp).1
          (hxa ▸ (p.edgeSet_subset_support_prod hxz).1))
      · have hxa : x = a := congrArg Prod.fst hxz
        exact False.elim ((List.nodup_cons.mp hp).1
          (hxa ▸ (p.edgeSet_subset_support_prod hxy).1))
      · exact ih (List.nodup_cons.mp hp).2 hxy hxz

/-- A simple walk has at most one incoming edge at every vertex. -/
theorem Walk.edgeSet_leftUnique {D : Digraph V} {a b : V}
    (p : Walk D a b) (hp : p.IsPath) :
    Relator.LeftUnique (fun x y ↦ (x, y) ∈ p.edgeSet) := by
  intro x y z hxz hyz
  induction p with
  | nil => simp at hxz
  | @cons a c b h p ih =>
      simp only [Walk.edgeSet_cons, Set.mem_union,
        Set.mem_singleton_iff] at hxz hyz
      rcases hxz with hxz | hxz <;> rcases hyz with hyz | hyz
      · simpa using congrArg Prod.fst (hxz.trans hyz.symm)
      · have hzc : z = c := congrArg Prod.snd hxz
        exact False.elim (Walk.start_ne_edge_target p
          (List.nodup_cons.mp hp).2 hyz (hzc.symm.trans rfl))
      · have hzc : z = c := congrArg Prod.snd hyz
        exact False.elim (Walk.start_ne_edge_target p
          (List.nodup_cons.mp hp).2 hxz (hzc.symm.trans rfl))
      · exact ih (List.nodup_cons.mp hp).2 hxz hyz

/-- The edge relation of a finite path has indegree and outdegree at most
one. -/
theorem FinitePath.edgeSet_biUnique {D : Digraph V}
    (p : FinitePath D) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ p.edgeSet) :=
  ⟨Walk.edgeSet_leftUnique p.walk p.isPath,
    Walk.edgeSet_rightUnique p.walk p.isPath⟩

/-! ## Incidence of all forward links -/

private theorem compatible_forward_rightUnique {D : Digraph V}
    {l r : Link D} {adjacent : Prop}
    (hl : l.direction = .forward) (hr : r.direction = .forward)
    (hcomp : CompatibleInOrder adjacent l r) {x y z : V}
    (hxy : (x, y) ∈ l.path.edgeSet)
    (hxz : (x, z) ∈ r.path.edgeSet) : False := by
  simp only [CompatibleInOrder, hl, hr] at hcomp
  have hxs := l.path.edgeSet_subset_support_prod hxy
  have hxt := r.path.edgeSet_subset_support_prod hxz
  rcases hcomp hxs.1 hxt.1 with h | h
  · have hfinish : r.path.finish = x := by
      simpa [Link.exit, hr] using h.2.symm
    exact Walk.finish_ne_edge_source r.path.walk r.path.isPath hxz
      (hfinish.trans rfl)
  · have hfinish : l.path.finish = x := by
      simpa [Link.exit, hl] using h.1.symm
    exact Walk.finish_ne_edge_source l.path.walk l.path.isPath hxy
      (hfinish.trans rfl)

private theorem compatible_forward_leftUnique {D : Digraph V}
    {l r : Link D} {adjacent : Prop}
    (hl : l.direction = .forward) (hr : r.direction = .forward)
    (hcomp : CompatibleInOrder adjacent l r) {x y z : V}
    (hxz : (x, z) ∈ l.path.edgeSet)
    (hyz : (y, z) ∈ r.path.edgeSet) : False := by
  simp only [CompatibleInOrder, hl, hr] at hcomp
  have hxs := l.path.edgeSet_subset_support_prod hxz
  have hxt := r.path.edgeSet_subset_support_prod hyz
  rcases hcomp hxs.2 hxt.2 with h | h
  · have hstart : l.path.start = z := by
      simpa [Link.entry, hl] using h.1.symm
    exact Walk.start_ne_edge_target l.path.walk l.path.isPath hxz
      (hstart.trans rfl)
  · have hstart : r.path.start = z := by
      simpa [Link.entry, hr] using h.2.symm
    exact Walk.start_ne_edge_target r.path.walk r.path.isPath hyz
      (hstart.trans rfl)

/-- Forward links of a finite alternating trace have at most one outgoing
edge at each vertex. -/
theorem FiniteTrace.forwardEdges_rightUnique {D : Digraph V}
    (Q : FiniteTrace D) :
    Relator.RightUnique
      (fun x y ↦ (x, y) ∈
        (AltPath.finite Q).directionEdges .forward) := by
  intro x y z hxy hxz
  simp only [AltPath.directionEdges, AltPath.links, FiniteTrace.links,
    Set.mem_iUnion, Set.mem_range] at hxy hxz
  rcases hxy with ⟨l, ⟨i, rfl⟩, hli, hxy⟩
  rcases hxz with ⟨r, ⟨j, rfl⟩, hrj, hxz⟩
  by_cases hij : i = j
  · subst j
    exact (FinitePath.edgeSet_biUnique (Q.link i).path).2 hxy hxz
  · rcases lt_or_gt_of_ne hij with hij | hji
    · exact False.elim (compatible_forward_rightUnique hli hrj
        (Q.compatible i j hij) hxy hxz)
    · exact False.elim (compatible_forward_rightUnique hrj hli
        (Q.compatible j i hji) hxz hxy)

/-- Forward links of a finite alternating trace have at most one incoming
edge at each vertex. -/
theorem FiniteTrace.forwardEdges_leftUnique {D : Digraph V}
    (Q : FiniteTrace D) :
    Relator.LeftUnique
      (fun x y ↦ (x, y) ∈
        (AltPath.finite Q).directionEdges .forward) := by
  intro x y z hxz hyz
  simp only [AltPath.directionEdges, AltPath.links, FiniteTrace.links,
    Set.mem_iUnion, Set.mem_range] at hxz hyz
  rcases hxz with ⟨l, ⟨i, rfl⟩, hli, hxz⟩
  rcases hyz with ⟨r, ⟨j, rfl⟩, hrj, hyz⟩
  by_cases hij : i = j
  · subst j
    exact (FinitePath.edgeSet_biUnique (Q.link i).path).1 hxz hyz
  · rcases lt_or_gt_of_ne hij with hij | hji
    · exact False.elim (compatible_forward_leftUnique hli hrj
        (Q.compatible i j hij) hxz hyz)
    · exact False.elim (compatible_forward_leftUnique hrj hli
        (Q.compatible j i hji) hyz hxz)

/-- Forward links of an infinite alternating trace have at most one outgoing
edge at each vertex. -/
theorem InfiniteTrace.forwardEdges_rightUnique {D : Digraph V}
    (Q : InfiniteTrace D) :
    Relator.RightUnique
      (fun x y ↦ (x, y) ∈
        (AltPath.infinite Q).directionEdges .forward) := by
  intro x y z hxy hxz
  simp only [AltPath.directionEdges, AltPath.links, InfiniteTrace.links,
    Set.mem_iUnion, Set.mem_range] at hxy hxz
  rcases hxy with ⟨l, ⟨i, rfl⟩, hli, hxy⟩
  rcases hxz with ⟨r, ⟨j, rfl⟩, hrj, hxz⟩
  by_cases hij : i = j
  · subst j
    exact (FinitePath.edgeSet_biUnique (Q.link i).path).2 hxy hxz
  · rcases lt_or_gt_of_ne hij with hij | hji
    · exact False.elim (compatible_forward_rightUnique hli hrj
        (Q.compatible i j hij) hxy hxz)
    · exact False.elim (compatible_forward_rightUnique hrj hli
        (Q.compatible j i hji) hxz hxy)

/-- Forward links of an infinite alternating trace have at most one incoming
edge at each vertex. -/
theorem InfiniteTrace.forwardEdges_leftUnique {D : Digraph V}
    (Q : InfiniteTrace D) :
    Relator.LeftUnique
      (fun x y ↦ (x, y) ∈
        (AltPath.infinite Q).directionEdges .forward) := by
  intro x y z hxz hyz
  simp only [AltPath.directionEdges, AltPath.links, InfiniteTrace.links,
    Set.mem_iUnion, Set.mem_range] at hxz hyz
  rcases hxz with ⟨l, ⟨i, rfl⟩, hli, hxz⟩
  rcases hyz with ⟨r, ⟨j, rfl⟩, hrj, hyz⟩
  by_cases hij : i = j
  · subst j
    exact (FinitePath.edgeSet_biUnique (Q.link i).path).1 hxz hyz
  · rcases lt_or_gt_of_ne hij with hij | hji
    · exact False.elim (compatible_forward_leftUnique hli hrj
        (Q.compatible i j hij) hxz hyz)
    · exact False.elim (compatible_forward_leftUnique hrj hli
        (Q.compatible j i hji) hyz hxz)

/-- The union of all forward-link edges of an alternating path has indegree
and outdegree at most one. -/
theorem AltPath.forwardEdges_biUnique {D : Digraph V} (Q : AltPath D) :
    Relator.BiUnique
      (fun x y ↦ (x, y) ∈ Q.directionEdges .forward) := by
  cases Q with
  | trivial v =>
      constructor <;> intro x y z h <;>
        simp [AltPath.directionEdges, AltPath.links] at h
  | finite Q =>
      exact ⟨Q.forwardEdges_leftUnique, Q.forwardEdges_rightUnique⟩
  | infinite Q =>
      exact ⟨Q.forwardEdges_leftUnique, Q.forwardEdges_rightUnique⟩

/-! ## Incidence of warp edge sets -/

/-- The edge relation of a directed ray has indegree and outdegree at most
one. -/
theorem Ray.edgeSet_biUnique {D : Digraph V} (r : Ray D) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ r.edgeSet) := by
  constructor
  · intro a b c hab hcb
    rcases hab with ⟨i, hi⟩
    rcases hcb with ⟨j, hj⟩
    have hs : r (i + 1) = r (j + 1) :=
      (congrArg Prod.snd hi).symm.trans (congrArg Prod.snd hj)
    have hij : i = j := by
      have := r.injective hs
      omega
    calc
      a = r i := congrArg Prod.fst hi
      _ = r j := by rw [hij]
      _ = b := (congrArg Prod.fst hj).symm
  · intro a b c hab hac
    rcases hab with ⟨i, hi⟩
    rcases hac with ⟨j, hj⟩
    have hs : r i = r j :=
      (congrArg Prod.fst hi).symm.trans (congrArg Prod.fst hj)
    have hij : i = j := r.injective hs
    calc
      b = r (i + 1) := congrArg Prod.snd hi
      _ = r (j + 1) := by rw [hij]
      _ = c := (congrArg Prod.snd hj).symm

/-- The edge relation of either kind of directed path has indegree and
outdegree at most one. -/
theorem Path.edgeSet_biUnique {D : Digraph V} (p : Path D) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ p.edgeSet) := by
  rcases p with p | r
  · exact FinitePath.edgeSet_biUnique p
  · exact Ray.edgeSet_biUnique r

/-- The union of the edge sets of a warp has at most one outgoing edge at
each vertex. -/
theorem IsWarp.familyEdges_rightUnique {Y : Set Γ.DPath}
    (hY : Γ.IsWarp Y) :
    Relator.RightUnique (fun x y ↦ (x, y) ∈ familyEdges Y) := by
  intro x y z hxy hxz
  simp only [familyEdges, Set.mem_iUnion] at hxy hxz
  rcases hxy with ⟨p, hpY, hp⟩
  rcases hxz with ⟨q, hqY, hq⟩
  have hxp := (p.edgeSet_subset_support_prod hp).1
  have hxq := (q.edgeSet_subset_support_prod hq).1
  have hpq : p = q :=
    DWeb.IsWarp.eq_of_mem_support hY hpY hqY hxp hxq
  subst q
  exact (Path.edgeSet_biUnique p).2 hp hq

/-- The union of the edge sets of a warp has at most one incoming edge at
each vertex. -/
theorem IsWarp.familyEdges_leftUnique {Y : Set Γ.DPath}
    (hY : Γ.IsWarp Y) :
    Relator.LeftUnique (fun x y ↦ (x, y) ∈ familyEdges Y) := by
  intro x y z hxz hyz
  simp only [familyEdges, Set.mem_iUnion] at hxz hyz
  rcases hxz with ⟨p, hpY, hp⟩
  rcases hyz with ⟨q, hqY, hq⟩
  have hzp := (p.edgeSet_subset_support_prod hp).2
  have hzq := (q.edgeSet_subset_support_prod hq).2
  have hpq : p = q :=
    DWeb.IsWarp.eq_of_mem_support hY hpY hqY hzp hzq
  subst q
  exact (Path.edgeSet_biUnique p).1 hp hq

/-- The full edge relation of a warp is locally bi-unique. -/
theorem IsWarp.familyEdges_biUnique {Y : Set Γ.DPath}
    (hY : Γ.IsWarp Y) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ familyEdges Y) :=
  ⟨IsWarp.familyEdges_leftUnique hY,
    IsWarp.familyEdges_rightUnique hY⟩

/-! ## Edge incidence in finite subpaths -/

theorem Walk.exists_edge_from_of_mem_of_ne_finish {D : Digraph V}
    {a b x : V} (p : Walk D a b) (hx : x ∈ p.support)
    (hxb : x ≠ b) : ∃ y, (x, y) ∈ p.edgeSet := by
  induction p with
  | nil => exact False.elim (hxb (by simpa using hx))
  | @cons a c b h p ih =>
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨c, by simp⟩
      · obtain ⟨y, hy⟩ := ih hx hxb
        exact ⟨y, by simp [hy]⟩

theorem Walk.exists_edge_to_of_mem_of_ne_start {D : Digraph V}
    {a b x : V} (p : Walk D a b) (hx : x ∈ p.support)
    (hxa : x ≠ a) : ∃ y, (y, x) ∈ p.edgeSet := by
  induction p with
  | nil => exact False.elim (hxa (by simpa using hx))
  | @cons a c b h p ih =>
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact False.elim (hxa rfl)
      · by_cases hxc : x = c
        · exact ⟨a, by simp [hxc]⟩
        · obtain ⟨y, hy⟩ := ih hx hxc
          exact ⟨y, by simp [hy]⟩

theorem FinitePath.exists_edge_from_of_mem_of_ne_finish
    {D : Digraph V} (p : FinitePath D) {x : V}
    (hx : x ∈ p.support) (hxf : x ≠ p.finish) :
    ∃ y, (x, y) ∈ p.edgeSet :=
  Walk.exists_edge_from_of_mem_of_ne_finish p.walk hx hxf

theorem FinitePath.exists_edge_to_of_mem_of_ne_start
    {D : Digraph V} (p : FinitePath D) {x : V}
    (hx : x ∈ p.support) (hxs : x ≠ p.start) :
    ∃ y, (y, x) ∈ p.edgeSet :=
  Walk.exists_edge_to_of_mem_of_ne_start p.walk hx hxs

/-- An outgoing edge of a containing path at a nonterminal vertex of a
finite subpath is already an edge of the subpath. -/
theorem FinitePath.outgoing_mem_of_isSubpathOf {D : Digraph V}
    (q : FinitePath D) (p : Path D) {x y : V}
    (hsub : q.IsSubpathOf p) (hxq : x ∈ q.support)
    (hxf : x ≠ q.finish) (hxy : (x, y) ∈ p.edgeSet) :
    (x, y) ∈ q.edgeSet := by
  obtain ⟨z, hxz⟩ :=
    FinitePath.exists_edge_from_of_mem_of_ne_finish q hxq hxf
  have hxzp : (x, z) ∈ p.edgeSet := hsub.2 hxz
  have hyz := (Path.edgeSet_biUnique p).2 hxy hxzp
  simpa [hyz] using hxz

/-- An incoming edge of a containing path at a noninitial vertex of a
finite subpath is already an edge of the subpath. -/
theorem FinitePath.incoming_mem_of_isSubpathOf {D : Digraph V}
    (q : FinitePath D) (p : Path D) {x y : V}
    (hsub : q.IsSubpathOf p) (hxq : x ∈ q.support)
    (hxs : x ≠ q.start) (hyx : (y, x) ∈ p.edgeSet) :
    (y, x) ∈ q.edgeSet := by
  obtain ⟨z, hzx⟩ :=
    FinitePath.exists_edge_to_of_mem_of_ne_start q hxq hxs
  have hzxp : (z, x) ∈ p.edgeSet := hsub.2 hzx
  have hyz := (Path.edgeSet_biUnique p).1 hyx hzxp
  simpa [hyz] using hzx

/-! ## Forward/backward contact incidence -/

theorem forward_before_backward_no_source {D : Digraph V}
    {f b : Link D} {adjacent : Prop}
    (hf : f.direction = .forward) (hb : b.direction = .backward)
    (hcomp : CompatibleInOrder adjacent f b) {x y : V}
    (hxy : (x, y) ∈ f.path.edgeSet)
    (hxb : x ∈ b.path.support) : False := by
  simp only [CompatibleInOrder, hf, hb] at hcomp
  have hxf := (f.path.edgeSet_subset_support_prod hxy).1
  by_cases ha : adjacent
  · have hx : x ∈ f.path.support ∩ b.path.support := ⟨hxf, hxb⟩
    rw [hcomp.1 ha] at hx
    have hxe : x = f.exit := by simpa using hx
    have hfinish : f.path.finish = x := by
      simpa [Link.exit, hf] using hxe.symm
    exact Walk.finish_ne_edge_source f.path.walk f.path.isPath hxy
      (hfinish.trans rfl)
  · exact Set.disjoint_left.1 (hcomp.2 ha) hxf hxb

theorem backward_before_forward_source_ne_entry {D : Digraph V}
    {b f : Link D} {adjacent : Prop}
    (hb : b.direction = .backward) (hf : f.direction = .forward)
    (hcomp : CompatibleInOrder adjacent b f) {x y : V}
    (hxy : (x, y) ∈ f.path.edgeSet)
    (hxb : x ∈ b.path.support) : x ≠ b.entry := by
  simp only [CompatibleInOrder, hb, hf] at hcomp
  have hxf := (f.path.edgeSet_subset_support_prod hxy).1
  have not_entry_of_interior (hx : x ∈ b.interior) :
      x ≠ b.entry := by
    intro h
    exact hx.2 (h ▸ by rw [b.endpoints_eq]; simp)
  by_cases ha : adjacent
  · rcases hcomp.1 ha hxb hxf with h | h
    · exact fun hxe ↦ b.entry_ne_exit (hxe.symm.trans h)
    · exact not_entry_of_interior h.1
  · exact not_entry_of_interior ((hcomp.2 ha ⟨hxb, hxf⟩).1)

theorem forward_before_backward_target_ne_exit {D : Digraph V}
    {f b : Link D} {adjacent : Prop}
    (hf : f.direction = .forward) (hb : b.direction = .backward)
    (hcomp : CompatibleInOrder adjacent f b)
    (hjoin : adjacent → f.exit = b.entry) {x y : V}
    (hyx : (y, x) ∈ f.path.edgeSet)
    (hxb : x ∈ b.path.support) : x ≠ b.exit := by
  simp only [CompatibleInOrder, hf, hb] at hcomp
  have hxf := (f.path.edgeSet_subset_support_prod hyx).2
  by_cases ha : adjacent
  · have hx : x ∈ f.path.support ∩ b.path.support := ⟨hxf, hxb⟩
    rw [hcomp.1 ha] at hx
    have hxe : x = f.exit := by simpa using hx
    have hbe : x = b.entry := hxe.trans (hjoin ha)
    exact fun hxexit ↦ b.entry_ne_exit (hbe.symm.trans hxexit)
  · exact False.elim (Set.disjoint_left.1 (hcomp.2 ha) hxf hxb)

theorem backward_before_forward_target_ne_exit {D : Digraph V}
    {b f : Link D} {adjacent : Prop}
    (hb : b.direction = .backward) (hf : f.direction = .forward)
    (hcomp : CompatibleInOrder adjacent b f)
    (hjoin : adjacent → b.exit = f.entry) {x y : V}
    (hyx : (y, x) ∈ f.path.edgeSet)
    (hxb : x ∈ b.path.support) : x ≠ b.exit := by
  simp only [CompatibleInOrder, hb, hf] at hcomp
  have hxf := (f.path.edgeSet_subset_support_prod hyx).2
  have not_exit_of_interior (hx : x ∈ b.interior) :
      x ≠ b.exit := by
    intro h
    exact hx.2 (h ▸ by rw [b.endpoints_eq]; simp)
  by_cases ha : adjacent
  · rcases hcomp.1 ha hxb hxf with h | h
    · have hxentry : x = f.entry := h.trans (hjoin ha)
      have hstart : f.path.start = x := by
        simpa [Link.entry, hf] using hxentry.symm
      exact False.elim (Walk.start_ne_edge_target f.path.walk
        f.path.isPath hyx (hstart.trans rfl))
    · exact not_exit_of_interior h.1
  · exact not_exit_of_interior ((hcomp.2 ha ⟨hxb, hxf⟩).1)

private theorem FiniteTrace.join_of_adjacent {D : Digraph V}
    (Q : FiniteTrace D) (i j : Fin (Q.lastIndex + 1))
    (h : j.1 = i.1 + 1) :
    (Q.link i).exit = (Q.link j).entry := by
  let k : Fin Q.lastIndex := ⟨i.1, by omega⟩
  have hi : Fin.castSucc k = i := by ext; rfl
  have hj : k.succ = j := by ext; simpa [k] using h.symm
  simpa [hi, hj] using Q.joins k

private theorem FiniteTrace.forward_source_backward_ne_entry
    {D : Digraph V} (Q : FiniteTrace D)
    (fi bi : Fin (Q.lastIndex + 1))
    (hf : (Q.link fi).direction = .forward)
    (hb : (Q.link bi).direction = .backward) {x y : V}
    (hxy : (x, y) ∈ (Q.link fi).path.edgeSet)
    (hxb : x ∈ (Q.link bi).path.support) :
    x ≠ (Q.link bi).entry := by
  have hne : fi ≠ bi := by
    intro h
    subst bi
    simp [hf] at hb
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact False.elim (forward_before_backward_no_source hf hb
      (Q.compatible fi bi hlt) hxy hxb)
  · exact backward_before_forward_source_ne_entry hb hf
      (Q.compatible bi fi hgt) hxy hxb

private theorem FiniteTrace.forward_target_backward_ne_exit
    {D : Digraph V} (Q : FiniteTrace D)
    (fi bi : Fin (Q.lastIndex + 1))
    (hf : (Q.link fi).direction = .forward)
    (hb : (Q.link bi).direction = .backward) {x y : V}
    (hyx : (y, x) ∈ (Q.link fi).path.edgeSet)
    (hxb : x ∈ (Q.link bi).path.support) :
    x ≠ (Q.link bi).exit := by
  have hne : fi ≠ bi := by
    intro h
    subst bi
    simp [hf] at hb
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact forward_before_backward_target_ne_exit hf hb
      (Q.compatible fi bi hlt) (Q.join_of_adjacent fi bi) hyx hxb
  · exact backward_before_forward_target_ne_exit hb hf
      (Q.compatible bi fi hgt) (Q.join_of_adjacent bi fi) hyx hxb

private theorem InfiniteTrace.forward_source_backward_ne_entry
    {D : Digraph V} (Q : InfiniteTrace D) (fi bi : ℕ)
    (hf : (Q.link fi).direction = .forward)
    (hb : (Q.link bi).direction = .backward) {x y : V}
    (hxy : (x, y) ∈ (Q.link fi).path.edgeSet)
    (hxb : x ∈ (Q.link bi).path.support) :
    x ≠ (Q.link bi).entry := by
  have hne : fi ≠ bi := by
    intro h
    subst bi
    simp [hf] at hb
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact False.elim (forward_before_backward_no_source hf hb
      (Q.compatible fi bi hlt) hxy hxb)
  · exact backward_before_forward_source_ne_entry hb hf
      (Q.compatible bi fi hgt) hxy hxb

private theorem InfiniteTrace.forward_target_backward_ne_exit
    {D : Digraph V} (Q : InfiniteTrace D) (fi bi : ℕ)
    (hf : (Q.link fi).direction = .forward)
    (hb : (Q.link bi).direction = .backward) {x y : V}
    (hyx : (y, x) ∈ (Q.link fi).path.edgeSet)
    (hxb : x ∈ (Q.link bi).path.support) :
    x ≠ (Q.link bi).exit := by
  have hne : fi ≠ bi := by
    intro h
    subst bi
    simp [hf] at hb
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact forward_before_backward_target_ne_exit hf hb
      (Q.compatible fi bi hlt)
      (fun ha ↦ by simpa [ha] using Q.joins fi) hyx hxb
  · exact backward_before_forward_target_ne_exit hb hf
      (Q.compatible bi fi hgt)
      (fun ha ↦ by simpa [ha] using Q.joins bi) hyx hxb

/-- At the source of a forward edge, every backward link through that
vertex continues farther in the reference orientation. -/
theorem AltPath.forward_source_backward_ne_entry {D : Digraph V}
    (Q : AltPath D) {x y : V}
    (hxy : (x, y) ∈ Q.directionEdges .forward)
    {b : Link D} (hbQ : b ∈ Q.links)
    (hb : b.direction = .backward) (hxb : x ∈ b.path.support) :
    x ≠ b.entry := by
  cases Q with
  | trivial v => simp [AltPath.directionEdges, AltPath.links] at hxy
  | finite Q =>
      simp only [AltPath.directionEdges, AltPath.links, FiniteTrace.links,
        Set.mem_iUnion, Set.mem_range] at hxy hbQ
      rcases hxy with ⟨f, ⟨fi, rfl⟩, hf, hxy⟩
      rcases hbQ with ⟨bi, rfl⟩
      exact Q.forward_source_backward_ne_entry fi bi hf hb hxy hxb
  | infinite Q =>
      simp only [AltPath.directionEdges, AltPath.links,
        InfiniteTrace.links, Set.mem_iUnion, Set.mem_range] at hxy hbQ
      rcases hxy with ⟨f, ⟨fi, rfl⟩, hf, hxy⟩
      rcases hbQ with ⟨bi, rfl⟩
      exact Q.forward_source_backward_ne_entry fi bi hf hb hxy hxb

/-- At the target of a forward edge, every backward link through that
vertex extends farther backward in the reference orientation. -/
theorem AltPath.forward_target_backward_ne_exit {D : Digraph V}
    (Q : AltPath D) {x y : V}
    (hyx : (y, x) ∈ Q.directionEdges .forward)
    {b : Link D} (hbQ : b ∈ Q.links)
    (hb : b.direction = .backward) (hxb : x ∈ b.path.support) :
    x ≠ b.exit := by
  cases Q with
  | trivial v => simp [AltPath.directionEdges, AltPath.links] at hyx
  | finite Q =>
      simp only [AltPath.directionEdges, AltPath.links, FiniteTrace.links,
        Set.mem_iUnion, Set.mem_range] at hyx hbQ
      rcases hyx with ⟨f, ⟨fi, rfl⟩, hf, hyx⟩
      rcases hbQ with ⟨bi, rfl⟩
      exact Q.forward_target_backward_ne_exit fi bi hf hb hyx hxb
  | infinite Q =>
      simp only [AltPath.directionEdges, AltPath.links,
        InfiniteTrace.links, Set.mem_iUnion, Set.mem_range] at hyx hbQ
      rcases hyx with ⟨f, ⟨fi, rfl⟩, hf, hyx⟩
      rcases hbQ with ⟨bi, rfl⟩
      exact Q.forward_target_backward_ne_exit fi bi hf hb hyx hxb

theorem AltPath.directionEdge_endpoints (Q : AltPath Γ.graph)
    {d : Direction} {e : V × V} (he : e ∈ Q.directionEdges d) :
    e.1 ∈ Q.directionVertices d ∧
      e.2 ∈ Q.directionVertices d := by
  simp only [AltPath.directionEdges, AltPath.directionVertices,
    Set.mem_iUnion] at he ⊢
  rcases he with ⟨l, hlQ, hldir, hel⟩
  have hs := l.path.edgeSet_subset_support_prod hel
  exact ⟨⟨l, hlQ, hldir, hs.1⟩, ⟨l, hlQ, hldir, hs.2⟩⟩

/-- Any reference-warp edge leaving the source of a forward edge is one of
the deleted backward edges. -/
theorem IsSwitchingAlternating.family_outgoing_of_forward_source_is_backward
    {Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (hAlt : IsSwitchingAlternating Y Q) {x y z : V}
    (hF : (x, y) ∈ Q.directionEdges .forward)
    (hY : (x, z) ∈ familyEdges Y) :
    (x, z) ∈ Q.directionEdges .backward := by
  have hxY : x ∈ Γ.vertexSet Y := by
    simp only [familyEdges, Set.mem_iUnion] at hY
    rcases hY with ⟨p, hpY, hp⟩
    exact ⟨p, hpY, (p.edgeSet_subset_support_prod hp).1⟩
  have hxF : x ∈ Q.directionVertices .forward :=
    (Q.directionEdge_endpoints hF).1
  have hxB : x ∈ Q.directionVertices .backward :=
    hAlt.contactsCovered ⟨hxF, hxY⟩
  simp only [AltPath.directionVertices, Set.mem_iUnion] at hxB
  rcases hxB with ⟨b, hbQ, hbdir, hxb⟩
  rcases hAlt.1.2.1 b hbQ hbdir with ⟨p, hpY, hbp⟩
  simp only [familyEdges, Set.mem_iUnion] at hY
  rcases hY with ⟨q, hqY, hxzq⟩
  have hpq : p = q := DWeb.IsWarp.eq_of_mem_support hAlt.1.1 hpY hqY
    (hbp.1 hxb) (q.edgeSet_subset_support_prod hxzq).1
  subst q
  have hxne : x ≠ b.path.finish := by
    simpa [Link.entry, hbdir] using
      Q.forward_source_backward_ne_entry hF hbQ hbdir hxb
  have hxzb : (x, z) ∈ b.path.edgeSet :=
    FinitePath.outgoing_mem_of_isSubpathOf
      b.path p hbp hxb hxne hxzq
  simp only [AltPath.directionEdges, Set.mem_iUnion]
  exact ⟨b, hbQ, hbdir, hxzb⟩

/-- Any reference-warp edge entering the target of a forward edge is one of
the deleted backward edges. -/
theorem IsSwitchingAlternating.family_incoming_of_forward_target_is_backward
    {Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (hAlt : IsSwitchingAlternating Y Q) {x y z : V}
    (hF : (y, x) ∈ Q.directionEdges .forward)
    (hY : (z, x) ∈ familyEdges Y) :
    (z, x) ∈ Q.directionEdges .backward := by
  have hxY : x ∈ Γ.vertexSet Y := by
    simp only [familyEdges, Set.mem_iUnion] at hY
    rcases hY with ⟨p, hpY, hp⟩
    exact ⟨p, hpY, (p.edgeSet_subset_support_prod hp).2⟩
  have hxF : x ∈ Q.directionVertices .forward :=
    (Q.directionEdge_endpoints hF).2
  have hxB : x ∈ Q.directionVertices .backward :=
    hAlt.contactsCovered ⟨hxF, hxY⟩
  simp only [AltPath.directionVertices, Set.mem_iUnion] at hxB
  rcases hxB with ⟨b, hbQ, hbdir, hxb⟩
  rcases hAlt.1.2.1 b hbQ hbdir with ⟨p, hpY, hbp⟩
  simp only [familyEdges, Set.mem_iUnion] at hY
  rcases hY with ⟨q, hqY, hzxq⟩
  have hpq : p = q := DWeb.IsWarp.eq_of_mem_support hAlt.1.1 hpY hqY
    (hbp.1 hxb) (q.edgeSet_subset_support_prod hzxq).2
  subst q
  have hxne : x ≠ b.path.start := by
    simpa [Link.exit, hbdir] using
      Q.forward_target_backward_ne_exit hF hbQ hbdir hxb
  have hzxb : (z, x) ∈ b.path.edgeSet :=
    FinitePath.incoming_mem_of_isSubpathOf
      b.path p hbp hxb hxne hzxq
  simp only [AltPath.directionEdges, Set.mem_iUnion]
  exact ⟨b, hbQ, hbdir, hzxb⟩

/-! ## Normal form of the switched relation -/

/-- Every backward-link edge is an edge of the reference warp. -/
theorem BackwardLinksOn.directionEdges_subset_familyEdges
    {Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (h : BackwardLinksOn Y Q) :
    Q.directionEdges .backward ⊆ familyEdges Y := by
  intro e he
  simp only [AltPath.directionEdges, Set.mem_iUnion] at he
  rcases he with ⟨l, hlQ, hdir, hel⟩
  rcases h l hlQ hdir with ⟨p, hpY, hlp⟩
  simp only [familyEdges, Set.mem_iUnion]
  exact ⟨p, hpY, hlp.2 hel⟩

/-- Switching deletes precisely the backward-link edges and inserts
precisely the forward-link edges. -/
theorem IsSwitchingAlternating.switchedEdges_eq
    {Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (h : IsSwitchingAlternating Y Q) :
    switchedEdges Y Q =
      (familyEdges Y \ Q.directionEdges .backward) ∪
        Q.directionEdges .forward := by
  have hF : Disjoint (Q.directionEdges .forward) (familyEdges Y) :=
    h.forwardLinksOff.directionEdges_disjoint
  have hB : Q.directionEdges .backward ⊆ familyEdges Y :=
    h.1.2.1.directionEdges_subset_familyEdges
  rw [switchedEdges, Q.edgeSet_eq_directionEdges_union]
  ext e
  constructor
  · rintro (⟨heY, heQ⟩ | ⟨heQ, heY⟩)
    · exact Or.inl ⟨heY, fun heB ↦ heQ (Or.inr heB)⟩
    · rcases heQ with heF | heB
      · exact Or.inr heF
      · exact False.elim (heY (hB heB))
  · rintro (⟨heY, heB⟩ | heF)
    · exact Or.inl ⟨heY, fun heQ ↦ heQ.elim
        (fun hqF ↦ Set.disjoint_left.1 hF hqF heY) heB⟩
    · exact Or.inr ⟨Or.inl heF,
        fun heY ↦ Set.disjoint_left.1 hF heF heY⟩

/-- The switched relation has at most one outgoing edge at each vertex. -/
theorem IsSwitchingAlternating.switchedEdges_rightUnique
    {Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (h : IsSwitchingAlternating Y Q) :
    Relator.RightUnique (fun x y ↦ (x, y) ∈ switchedEdges Y Q) := by
  rw [h.switchedEdges_eq]
  intro x y z hxy hxz
  rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
  · exact (IsWarp.familyEdges_rightUnique h.1.1) hxy.1 hxz.1
  · exact False.elim (hxy.2
      (h.family_outgoing_of_forward_source_is_backward hxz hxy.1))
  · exact False.elim (hxz.2
      (h.family_outgoing_of_forward_source_is_backward hxy hxz.1))
  · exact Q.forwardEdges_biUnique.2 hxy hxz

/-- The switched relation has at most one incoming edge at each vertex. -/
theorem IsSwitchingAlternating.switchedEdges_leftUnique
    {Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (h : IsSwitchingAlternating Y Q) :
    Relator.LeftUnique (fun x y ↦ (x, y) ∈ switchedEdges Y Q) := by
  rw [h.switchedEdges_eq]
  intro x y z hxz hyz
  rcases hxz with hxz | hxz <;> rcases hyz with hyz | hyz
  · exact (IsWarp.familyEdges_leftUnique h.1.1) hxz.1 hyz.1
  · exact False.elim (hxz.2
      (h.family_incoming_of_forward_target_is_backward hyz hxz.1))
  · exact False.elim (hyz.2
      (h.family_incoming_of_forward_target_is_backward hxz hyz.1))
  · exact Q.forwardEdges_biUnique.1 hxz hyz

/-- The switched relation is locally bi-unique. -/
theorem IsSwitchingAlternating.switchedEdges_biUnique
    {Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (h : IsSwitchingAlternating Y Q) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ switchedEdges Y Q) :=
  ⟨h.switchedEdges_leftUnique, h.switchedEdges_rightUnique⟩

/-! ## Ordered supports and edge intervals -/

theorem Walk.support_length_eq {D : Digraph V} {a b : V}
    (p : Walk D a b) : p.support.length = p.length + 1 := by
  induction p <;> simp_all [Walk.support, Walk.length]

theorem Walk.getElem_length_eq_end {D : Digraph V} {a b : V}
    (p : Walk D a b) :
    p.support[p.length]'(by rw [Walk.support_length_eq p]; omega) = b := by
  induction p with
  | nil => rfl
  | @cons a c b h p ih =>
      simp only [Walk.length_cons, Walk.support_cons]
      simpa using ih

theorem Walk.mem_edgeSet_iff_exists_getVert {D : Digraph V} {a b : V}
    (p : Walk D a b) (e : V × V) :
    e ∈ p.edgeSet ↔ ∃ i < p.length,
      ∃ hi : i + 1 < p.support.length,
        e = (p.support[i]'(by omega), p.support[i + 1]'hi) := by
  induction p with
  | nil => simp [Walk.edgeSet]
  | @cons a c b h p ih =>
      simp only [Walk.edgeSet_cons, Set.mem_union, Set.mem_singleton_iff,
        Walk.length_cons]
      constructor
      · rintro (rfl | he)
        · refine ⟨0, by omega, ?_, ?_⟩
          · simp only [Walk.support_cons, List.length_cons]
            exact Nat.succ_lt_succ
              (List.length_pos_iff.mpr p.support_ne_nil)
          · apply Prod.ext
            · rfl
            · exact ((List.getElem_zero
                (List.length_pos_iff.mpr p.support_ne_nil)).trans
                  p.head_support).symm
        · rw [ih] at he
          rcases he with ⟨i, hi, hi', rfl⟩
          refine ⟨i + 1, by omega, ?_, ?_⟩
          · simpa using hi'
          · simp
      · rintro ⟨i, hi, hi', rfl⟩
        cases i with
        | zero =>
            apply Or.inl
            apply Prod.ext
            · rfl
            · change p.support[0]'(by
                  exact List.length_pos_iff.mpr p.support_ne_nil) = c
              exact (List.getElem_zero _).trans p.head_support
        | succ i =>
            apply Or.inr
            rw [ih]
            refine ⟨i, by omega, ?_, ?_⟩
            · simpa using hi'
            · simp

theorem Walk.idxOf_target_eq_source_add_one [DecidableEq V]
    {D : Digraph V} {a b : V} (p : Walk D a b) (hp : p.IsPath)
    {x y : V} (hxy : (x, y) ∈ p.edgeSet) :
    p.support.idxOf y = p.support.idxOf x + 1 := by
  classical
  rw [Walk.mem_edgeSet_iff_exists_getVert p] at hxy
  rcases hxy with ⟨i, hi, hi', he⟩
  have hx : x = p.support[i] := congrArg Prod.fst he
  have hy : y = p.support[i + 1] := congrArg Prod.snd he
  subst x
  subst y
  rw [hp.idxOf_getElem, hp.idxOf_getElem]

theorem Walk.idxOf_getVert_eq_start_add [DecidableEq V]
    {D : Digraph V} {a b c d : V}
    (p : Walk D a b) (hp : p.IsPath)
    (q : Walk D c d) (hqE : q.edgeSet ⊆ p.edgeSet) {i : ℕ}
    (hi : i ≤ q.length) :
    p.support.idxOf (q.support[i]'(by
      rw [Walk.support_length_eq q]
      omega)) = p.support.idxOf c + i := by
  induction i with
  | zero =>
      simp only [Nat.add_zero]
      congr 1
      exact (List.getElem_zero
        (List.length_pos_iff.mpr q.support_ne_nil)).trans q.head_support
  | succ i ih =>
      have hi' : i < q.length := by omega
      have hlen := Walk.support_length_eq q
      have hi0 : i < q.support.length := by omega
      have hi1 : i + 1 < q.support.length := by omega
      have heq : (q.support[i]'hi0, q.support[i + 1]'hi1) ∈ q.edgeSet := by
        rw [Walk.mem_edgeSet_iff_exists_getVert q]
        exact ⟨i, hi', hi1, rfl⟩
      rw [Walk.idxOf_target_eq_source_add_one p hp (hqE heq), ih (by omega)]
      omega

/-- The edge positions of a finite subpath form a numerical interval in the
ordered support of the ambient finite path. -/
theorem FinitePath.edgeSet_eq_position_interval [DecidableEq V]
    {D : Digraph V} (p q : FinitePath D)
    (hsub : q.IsSubpathOf (Sum.inl p)) :
    q.edgeSet = {e ∈ p.edgeSet |
      p.walk.support.idxOf q.start ≤ p.walk.support.idxOf e.1 ∧
        p.walk.support.idxOf e.1 < p.walk.support.idxOf q.finish} := by
  classical
  ext e
  constructor
  · intro heq
    have hep := hsub.2 heq
    change e ∈ q.walk.edgeSet at heq
    rw [Walk.mem_edgeSet_iff_exists_getVert q.walk] at heq
    rcases heq with ⟨i, hi, hi', rfl⟩
    refine ⟨hep, ?_, ?_⟩
    · change p.walk.support.idxOf q.start ≤
        p.walk.support.idxOf q.walk.support[i]
      have hiPos := Walk.idxOf_getVert_eq_start_add p.walk p.isPath
          q.walk hsub.2 (i := i) (Nat.le_of_lt hi)
      omega
    · change p.walk.support.idxOf q.walk.support[i] <
        p.walk.support.idxOf q.finish
      have hfinish := Walk.idxOf_getVert_eq_start_add p.walk p.isPath
          q.walk hsub.2 (i := q.walk.length) le_rfl
      have qlast : q.walk.support[q.walk.length]'(by
          rw [Walk.support_length_eq q.walk]
          omega) = q.finish :=
        Walk.getElem_length_eq_end q.walk
      rw [qlast] at hfinish
      have hiPos := Walk.idxOf_getVert_eq_start_add p.walk p.isPath
        q.walk hsub.2 (i := i) (Nat.le_of_lt hi)
      omega
  · rintro ⟨hep, hlo, hhi⟩
    change e ∈ p.walk.edgeSet at hep
    rw [Walk.mem_edgeSet_iff_exists_getVert p.walk] at hep
    rcases hep with ⟨i, hi, hi', rfl⟩
    have hipos : p.walk.support.idxOf (p.walk.support[i]'(by omega)) = i := by
      rw [p.isPath.idxOf_getElem]
    rw [hipos] at hlo hhi
    have hstart := Walk.idxOf_getVert_eq_start_add p.walk p.isPath
      q.walk hsub.2 (i := 0) (Nat.zero_le _)
    simp only [Nat.add_zero] at hstart
    have qfirst : q.walk.support[0]'(by
        exact List.length_pos_iff.mpr q.walk.support_ne_nil) = q.start :=
      (List.getElem_zero _).trans q.walk.head_support
    rw [qfirst] at hstart
    have hfinish := Walk.idxOf_getVert_eq_start_add p.walk p.isPath
      q.walk hsub.2 (i := q.walk.length) le_rfl
    have qlast : q.walk.support[q.walk.length]'(by
        have := Walk.support_length_eq q.walk
        omega) = q.finish :=
      Walk.getElem_length_eq_end q.walk
    rw [qlast] at hfinish
    rw [hfinish] at hhi
    let j := i - p.walk.support.idxOf q.start
    have hj : j < q.walk.length := by omega
    change (p.walk.support[i], p.walk.support[i + 1]) ∈ q.walk.edgeSet
    rw [Walk.mem_edgeSet_iff_exists_getVert q.walk]
    refine ⟨j, hj, ?_⟩
    refine ⟨?_, ?_⟩
    · rw [Walk.support_length_eq q.walk]
      omega
    have hj0 : j < q.walk.support.length := by
      rw [Walk.support_length_eq q.walk]
      omega
    have hj1 : j + 1 < q.walk.support.length := by
      rw [Walk.support_length_eq q.walk]
      omega
    apply Prod.ext
    · apply (List.idxOf_inj (l := p.walk.support)
        (x := p.walk.support[i]) (y := q.walk.support[j]'hj0)
        (List.getElem_mem _)).mp
      have hqpos := Walk.idxOf_getVert_eq_start_add p.walk p.isPath
        q.walk hsub.2 (i := j) (Nat.le_of_lt hj)
      rw [hqpos, hipos]
      dsimp [j]
      omega
    · apply (List.idxOf_inj (l := p.walk.support)
        (x := p.walk.support[i + 1]) (y := q.walk.support[j + 1]'hj1)
        (List.getElem_mem _)).mp
      have hqpos := Walk.idxOf_getVert_eq_start_add p.walk p.isPath
        q.walk hsub.2 (i := j + 1) hj
      have hipos1 :
          p.walk.support.idxOf (p.walk.support[i + 1]'hi') = i + 1 := by
        rw [p.isPath.idxOf_getElem]
      rw [hqpos, hipos1]
      dsimp [j]
      omega

theorem Path.finite_of_isSubpathOf_finite
    {D : Digraph V} {q : Path D} {p : FinitePath D}
    (hsub : q.IsSubpathOf (.inl p)) :
    ∃ r : FinitePath D, q = .inl r := by
  rcases q with r | R
  · exact ⟨r, rfl⟩
  · exfalso
    have hfin : R.support.Finite :=
      p.support_finite.subset hsub.1
    exact hfin.not_infinite
      (Set.infinite_range_of_injective R.injective)

theorem IsEdgeInterval.mem_of_between_positions [DecidableEq V]
    {p : FinitePath Γ.graph} {E : Set (V × V)}
    (hI : IsEdgeInterval E (.inl p))
    {e₁ e e₂ : V × V}
    (he₁ : e₁ ∈ E) (he₂ : e₂ ∈ E) (hep : e ∈ p.edgeSet)
    (h₁ : p.walk.support.idxOf e₁.1 ≤ p.walk.support.idxOf e.1)
    (h₂ : p.walk.support.idxOf e.1 ≤ p.walk.support.idxOf e₂.1) :
    e ∈ E := by
  classical
  rcases hI with rfl | ⟨q, hsub, rfl⟩
  · exact False.elim (by simpa using he₁)
  · obtain ⟨r, rfl⟩ := Path.finite_of_isSubpathOf_finite hsub
    change e₁ ∈ r.edgeSet at he₁
    change e₂ ∈ r.edgeSet at he₂
    change e ∈ r.edgeSet
    rw [FinitePath.edgeSet_eq_position_interval p r hsub] at he₁ he₂ ⊢
    exact ⟨hep, h₁.trans' he₁.2.1, h₂.trans_lt he₂.2.2⟩

theorem IsSwitchingAlternating.exists_backward_edge_to_forward_target
    {Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (hAlt : IsSwitchingAlternating Y Q)
    {p : FinitePath Γ.graph} (hpY : (Sum.inl p : Γ.DPath) ∈ Y)
    {a x : V} (hF : (a, x) ∈ Q.directionEdges .forward)
    (hxp : x ∈ p.support) :
    ∃ z, (z, x) ∈ p.edgeSet ∩ Q.directionEdges .backward := by
  have hxY : x ∈ Γ.vertexSet Y := ⟨.inl p, hpY, hxp⟩
  have hxF := (Q.directionEdge_endpoints hF).2
  have hxB := hAlt.contactsCovered ⟨hxF, hxY⟩
  simp only [AltPath.directionVertices, Set.mem_iUnion] at hxB
  rcases hxB with ⟨b, hbQ, hbdir, hxb⟩
  rcases hAlt.1.2.1 b hbQ hbdir with ⟨q, hqY, hbq⟩
  have hpq : q = .inl p :=
    DWeb.IsWarp.eq_of_mem_support hAlt.1.1 hqY hpY (hbq.1 hxb) hxp
  subst q
  have hxne : x ≠ b.path.start := by
    simpa [Link.exit, hbdir] using
      Q.forward_target_backward_ne_exit hF hbQ hbdir hxb
  obtain ⟨z, hzx⟩ :=
    FinitePath.exists_edge_to_of_mem_of_ne_start b.path hxb hxne
  exact ⟨z, hbq.2 hzx, by
    simp only [AltPath.directionEdges, Set.mem_iUnion]
    exact ⟨b, hbQ, hbdir, hzx⟩⟩

theorem IsSwitchingAlternating.exists_backward_edge_from_forward_source
    {Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (hAlt : IsSwitchingAlternating Y Q)
    {p : FinitePath Γ.graph} (hpY : (Sum.inl p : Γ.DPath) ∈ Y)
    {x b : V} (hF : (x, b) ∈ Q.directionEdges .forward)
    (hxp : x ∈ p.support) :
    ∃ z, (x, z) ∈ p.edgeSet ∩ Q.directionEdges .backward := by
  have hxY : x ∈ Γ.vertexSet Y := ⟨.inl p, hpY, hxp⟩
  have hxF := (Q.directionEdge_endpoints hF).1
  have hxB := hAlt.contactsCovered ⟨hxF, hxY⟩
  simp only [AltPath.directionVertices, Set.mem_iUnion] at hxB
  rcases hxB with ⟨l, hlQ, hldir, hxl⟩
  rcases hAlt.1.2.1 l hlQ hldir with ⟨q, hqY, hlq⟩
  have hpq : q = .inl p :=
    DWeb.IsWarp.eq_of_mem_support hAlt.1.1 hqY hpY (hlq.1 hxl) hxp
  subst q
  have hxne : x ≠ l.path.finish := by
    simpa [Link.entry, hldir] using
      Q.forward_source_backward_ne_entry hF hlQ hldir hxl
  obtain ⟨z, hxz⟩ :=
    FinitePath.exists_edge_from_of_mem_of_ne_finish l.path hxl hxne
  exact ⟨z, hlq.2 hxz, by
    simp only [AltPath.directionEdges, Set.mem_iUnion]
    exact ⟨l, hlQ, hldir, hxz⟩⟩

/-- A safe switch cannot leave a nonempty retained interval of a reference
path between two forward edges. -/
theorem IsSwitchingSafe.no_forward_retainedPath_forward
    {Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (hSafe : IsSwitchingSafe Y Q)
    {p r : FinitePath Γ.graph}
    (hpY : (Sum.inl p : Γ.DPath) ∈ Y)
    (hrp : r.IsSubpathOf (.inl p))
    (hrne : r.start ≠ r.finish)
    (hret : r.edgeSet ⊆
      familyEdges Y \ Q.directionEdges .backward)
    {a b : V}
    (hIn : (a, r.start) ∈ Q.directionEdges .forward)
    (hOut : (r.finish, b) ∈ Q.directionEdges .forward) : False := by
  classical
  letI := Classical.decEq V
  have hAlt : IsSwitchingAlternating Y Q := hSafe.isSwitchingAlternating
  obtain ⟨z, hzP, hzB⟩ :=
    hAlt.exists_backward_edge_to_forward_target hpY hIn
      (hrp.1 r.start_mem_support)
  obtain ⟨w, hwP, hwB⟩ :=
    hAlt.exists_backward_edge_from_forward_source hpY hOut
      (hrp.1 r.finish_mem_support)
  obtain ⟨t, hrt⟩ :=
    FinitePath.exists_edge_from_of_mem_of_ne_finish r
      r.start_mem_support hrne
  have hrtRet := hret hrt
  have hpos :=
    FinitePath.edgeSet_eq_position_interval p r hrp
  have hrtPos : p.walk.support.idxOf r.start ≤
      p.walk.support.idxOf (r.start, t).1 ∧
      p.walk.support.idxOf (r.start, t).1 <
        p.walk.support.idxOf r.finish := by
    rw [hpos] at hrt
    exact hrt.2
  change p.walk.support.idxOf r.start ≤
      p.walk.support.idxOf r.start ∧
      p.walk.support.idxOf r.start <
        p.walk.support.idxOf r.finish at hrtPos
  have hzPos := Walk.idxOf_target_eq_source_add_one
    p.walk p.isPath hzP
  have hwPos := Walk.idxOf_target_eq_source_add_one
    p.walk p.isPath hwP
  have hzI : (z, r.start) ∈
      Q.directionEdges .backward ∩ p.edgeSet := ⟨hzB, hzP⟩
  have hwI : (r.finish, w) ∈
      Q.directionEdges .backward ∩ p.edgeSet := ⟨hwB, hwP⟩
  have hleft : p.walk.support.idxOf (z, r.start).1 ≤
      p.walk.support.idxOf (r.start, t).1 := by
    change p.walk.support.idxOf z ≤ p.walk.support.idxOf r.start
    omega
  have hright : p.walk.support.idxOf (r.start, t).1 ≤
      p.walk.support.idxOf (r.finish, w).1 := by
    change p.walk.support.idxOf r.start ≤
      p.walk.support.idxOf r.finish
    omega
  have hrtI : (r.start, t) ∈
      Q.directionEdges .backward ∩ p.edgeSet :=
    IsEdgeInterval.mem_of_between_positions
      (hSafe.1.2.1 (.inl p) hpY) hzI hwI (hrp.2 hrt)
      hleft hright
  exact hrtRet.2 hrtI.1

/-! ## Reverse rays in the forward-link relation -/

/-- A one-way infinite chain traversing a directed relation backwards. -/
def ContainsReverseDirectedRay (E : Set (V × V)) : Prop :=
  ∃ R : DirectedRay V, ∀ n, (R.vertex (n + 1), R.vertex n) ∈ E

private theorem Link.not_mem_interior_entry {D : Digraph V} (l : Link D) :
    l.entry ∉ l.interior := by
  intro h
  exact h.2 (by rw [l.endpoints_eq]; simp)

private theorem Link.not_mem_interior_exit {D : Digraph V} (l : Link D) :
    l.exit ∉ l.interior := by
  intro h
  exact h.2 (by rw [l.endpoints_eq]; simp)

/-- Consecutive forward edges in an infinite trace cannot move to an earlier
link.  This is the order-theoretic core that excludes backward rays. -/
theorem InfiniteTrace.forward_transition_index_le {D : Digraph V}
    (Q : InfiniteTrace D) {i j : ℕ}
    (hdi : (Q.link i).direction = .forward)
    (hdj : (Q.link j).direction = .forward)
    {a x b : V}
    (ha : (a, x) ∈ (Q.link i).path.edgeSet)
    (hb : (x, b) ∈ (Q.link j).path.edgeSet) : i ≤ j := by
  by_contra hnot
  have hji : j < i := Nat.lt_of_not_ge hnot
  have hcomp := Q.compatible j i hji
  simp only [CompatibleInOrder, hdj, hdi] at hcomp
  have hxi := (Q.link i).path.edgeSet_subset_support_prod ha |>.2
  have hxj := (Q.link j).path.edgeSet_subset_support_prod hb |>.1
  rcases hcomp hxj hxi with hwrong | himpossible
  · have hjzero : j = 0 := by
      by_contra hj
      have hjpos : 0 < j := Nat.pos_of_ne_zero hj
      let k := j - 1
      have hksucc : k + 1 = j := by omega
      have hkdir : (Q.link k).direction = .backward := by
        have halt := Q.alternates k
        rw [hksucc, hdj] at halt
        cases hdir : (Q.link k).direction
        · exact False.elim (halt hdir)
        · rfl
      have hjoin : (Q.link k).exit = (Q.link j).entry := by
        simpa [hksucc] using Q.joins k
      have hxk : x ∈ (Q.link k).path.support := by
        have hx : x = (Q.link k).exit := hwrong.1.trans hjoin.symm
        rw [hx]
        exact (Q.link k).exit_mem_support
      have hki : k < i := by omega
      have hnonadj : i ≠ k + 1 := by omega
      have hkcomp := Q.compatible k i hki
      simp only [CompatibleInOrder, hkdir, hdi] at hkcomp
      have hxint := (hkcomp.2 hnonadj ⟨hxk, hxi⟩).1
      exact (Q.link k).not_mem_interior_exit
        (hjoin.trans hwrong.1.symm ▸ hxint)
    subst j
    have hisuccdir : (Q.link (i + 1)).direction = .backward := by
      have halt := Q.alternates i
      rw [hdi] at halt
      cases hdir : (Q.link (i + 1)).direction
      · exact False.elim (halt hdir.symm)
      · rfl
    have hjoin := Q.joins i
    have hxb : x ∈ (Q.link (i + 1)).path.support := by
      have hx : x = (Q.link (i + 1)).entry := hwrong.2.trans hjoin
      rw [hx]
      exact (Q.link (i + 1)).entry_mem_support
    have hlt : 0 < i + 1 := Nat.zero_lt_succ i
    have hnonadj : i + 1 ≠ 1 := by omega
    have h0comp := Q.compatible 0 (i + 1) hlt
    simp only [CompatibleInOrder, hdj, hisuccdir] at h0comp
    exact Set.disjoint_left.1 (h0comp.2 hnonadj) hxj hxb
  · have histart : (Q.link i).path.start = x := by
      simpa [Link.entry, hdi] using himpossible.2.symm
    exact Walk.start_ne_edge_target (Q.link i).path.walk
      (Q.link i).path.isPath ha (histart.trans rfl)

noncomputable def InfiniteTrace.forwardIndex {D : Digraph V}
    (Q : InfiniteTrace D) (e : V × V)
    (he : e ∈ (AltPath.infinite Q).directionEdges .forward) : ℕ :=
  Classical.choose (show ∃ i, (Q.link i).direction = .forward ∧
      e ∈ (Q.link i).path.edgeSet by
    simp only [AltPath.directionEdges, AltPath.links, InfiniteTrace.links,
      Set.mem_iUnion, Set.mem_range] at he
    rcases he with ⟨l, ⟨i, rfl⟩, hdir, he⟩
    exact ⟨i, hdir, he⟩)

theorem InfiniteTrace.forwardIndex_spec {D : Digraph V}
    (Q : InfiniteTrace D) (e : V × V)
    (he : e ∈ (AltPath.infinite Q).directionEdges .forward) :
    (Q.link (Q.forwardIndex e he)).direction = .forward ∧
      e ∈ (Q.link (Q.forwardIndex e he)).path.edgeSet :=
  Classical.choose_spec (show ∃ i, (Q.link i).direction = .forward ∧
      e ∈ (Q.link i).path.edgeSet by
    simp only [AltPath.directionEdges, AltPath.links, InfiniteTrace.links,
      Set.mem_iUnion, Set.mem_range] at he
    rcases he with ⟨l, ⟨i, rfl⟩, hdir, he⟩
    exact ⟨i, hdir, he⟩)

theorem antitone_nat_eventually_constant (f : ℕ → ℕ)
    (hf : ∀ n, f (n + 1) ≤ f n) :
    ∃ N, ∀ n, f (N + n) = f N := by
  classical
  let m := Nat.find (show ∃ k, k ∈ Set.range f from ⟨f 0, 0, rfl⟩)
  have hm : m ∈ Set.range f := Nat.find_spec
    (show ∃ k, k ∈ Set.range f from ⟨f 0, 0, rfl⟩)
  rcases hm with ⟨N, hN⟩
  refine ⟨N, fun n ↦ ?_⟩
  apply Nat.le_antisymm
  · exact (antitone_nat_of_succ_le hf) (Nat.le_add_right N n)
  · rw [hN]
    exact Nat.find_min'
      (show ∃ k, k ∈ Set.range f from ⟨f 0, 0, rfl⟩) ⟨N + n, rfl⟩

/-- The union of all forward links of an infinite alternating trace has no
backward-directed ray. -/
theorem InfiniteTrace.forwardEdges_not_containsReverseDirectedRay
    {D : Digraph V} (Q : InfiniteTrace D) :
    ¬ ContainsReverseDirectedRay
      ((AltPath.infinite Q).directionEdges .forward) := by
  rintro ⟨R, hR⟩
  let f : ℕ → ℕ := fun n ↦ Q.forwardIndex
    (R.vertex (n + 1), R.vertex n) (hR n)
  have hf : ∀ n, f (n + 1) ≤ f n := by
    intro n
    exact Q.forward_transition_index_le
      (Q.forwardIndex_spec _ (hR (n + 1))).1
      (Q.forwardIndex_spec _ (hR n)).1
      (Q.forwardIndex_spec _ (hR (n + 1))).2
      (Q.forwardIndex_spec _ (hR n)).2
  obtain ⟨N, hN⟩ := antitone_nat_eventually_constant f hf
  let l := Q.link (f N)
  have hmem : ∀ n : ℕ, R.vertex (N + n) ∈ l.path.support := by
    intro n
    cases n with
    | zero =>
        have he := (Q.forwardIndex_spec _ (hR N)).2
        exact (l.path.edgeSet_subset_support_prod he).2
    | succ n =>
        have he := (Q.forwardIndex_spec _ (hR (N + n))).2
        have hidx : f (N + n) = f N := hN n
        change (R.vertex (N + n + 1), R.vertex (N + n)) ∈
          (Q.link (f (N + n))).path.edgeSet at he
        rw [hidx] at he
        change R.vertex (N + (n + 1)) ∈ (Q.link (f N)).path.support
        simpa [Nat.add_assoc] using
          ((Q.link (f N)).path.edgeSet_subset_support_prod he).1
  exact l.path.support_finite.not_infinite
    (Set.infinite_of_injective_forall_mem
      (fun _ _ h ↦ Nat.add_left_cancel (R.injective h)) hmem)

/-! ## Retained singleton components -/

theorem mem_vertexSet_of_mem_isolatedVertices {Y : Set Γ.DPath} {v : V}
    (hv : v ∈ isolatedVertices Y) : v ∈ Γ.vertexSet Y := by
  exact ⟨Γ.trivialPath v, hv, by simp⟩

/-- No backward link can meet a singleton member of the reference warp. -/
theorem BackwardLinksOn.directionVertices_disjoint_isolatedVertices
    {Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (hY : Γ.IsWarp Y) (hback : BackwardLinksOn Y Q) :
    Disjoint (Q.directionVertices .backward) (isolatedVertices Y) := by
  rw [Set.disjoint_left]
  intro v hvQ hviso
  simp only [AltPath.directionVertices, Set.mem_iUnion] at hvQ
  rcases hvQ with ⟨l, hlQ, hldir, hvl⟩
  rcases hback l hlQ hldir with ⟨p, hpY, hlp⟩
  have htrivY : Γ.trivialPath v ∈ Y := hviso
  have hvtriv : v ∈ (Γ.trivialPath v).support := by simp
  have hp : p = Γ.trivialPath v :=
    DWeb.IsWarp.eq_of_mem_support hY hpY htrivY (hlp.1 hvl) hvtriv
  have hentry : l.entry = v := by
    have := hlp.1 l.entry_mem_support
    rw [hp] at this
    simpa using this
  have hexit : l.exit = v := by
    have := hlp.1 l.exit_mem_support
    rw [hp] at this
    simpa using this
  exact l.entry_ne_exit (hentry.trans hexit.symm)

/-- Neither endpoint of an alternating-path edge is an explicitly retained
singleton of the reference warp. -/
theorem IsSwitchingAlternating.altEdge_not_incident_isolated
    {Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (hAlt : IsSwitchingAlternating Y Q) {v : V}
    (hviso : v ∈ isolatedVertices Y) {e : V × V}
    (he : e ∈ Q.edgeSet) : e.1 ≠ v ∧ e.2 ≠ v := by
  have hvY : v ∈ Γ.vertexSet Y :=
    mem_vertexSet_of_mem_isolatedVertices hviso
  have hbackdisj :=
    hAlt.1.2.1.directionVertices_disjoint_isolatedVertices hAlt.1.1
  have hforward :
      Disjoint (Q.directionVertices .forward) (isolatedVertices Y) := by
    rw [Set.disjoint_left]
    intro x hxF hxI
    have hxY : x ∈ Γ.vertexSet Y :=
      mem_vertexSet_of_mem_isolatedVertices hxI
    exact Set.disjoint_left.1 hbackdisj
      (hAlt.contactsCovered ⟨hxF, hxY⟩) hxI
  rw [Q.edgeSet_eq_directionEdges_union] at he
  have endpoint_direction {d : Direction}
      (hed : e ∈ Q.directionEdges d) :
      e.1 ∈ Q.directionVertices d ∧
        e.2 ∈ Q.directionVertices d := by
    simp only [AltPath.directionEdges, AltPath.directionVertices,
      Set.mem_iUnion] at hed ⊢
    rcases hed with ⟨l, hlQ, hldir, hel⟩
    have hs := l.path.edgeSet_subset_support_prod hel
    exact ⟨⟨l, hlQ, hldir, hs.1⟩, ⟨l, hlQ, hldir, hs.2⟩⟩
  rcases he with heF | heB
  · have hs := endpoint_direction heF
    exact ⟨fun h ↦ Set.disjoint_left.1 hforward (h ▸ hs.1) hviso,
      fun h ↦ Set.disjoint_left.1 hforward (h ▸ hs.2) hviso⟩
  · have hs := endpoint_direction heB
    exact ⟨fun h ↦ Set.disjoint_left.1 hbackdisj (h ▸ hs.1) hviso,
      fun h ↦ Set.disjoint_left.1 hbackdisj (h ▸ hs.2) hviso⟩

/-- No reference-warp edge is incident with one of the reference warp's
singleton components. -/
theorem IsWarp.familyEdge_not_incident_isolated
    {Y : Set Γ.DPath} (hY : Γ.IsWarp Y)
    {v : V} (hviso : v ∈ isolatedVertices Y)
    {e : V × V} (he : e ∈ familyEdges Y) :
    e.1 ≠ v ∧ e.2 ≠ v := by
  simp only [familyEdges, Set.mem_iUnion] at he
  rcases he with ⟨p, hpY, hep⟩
  have hs := p.edgeSet_subset_support_prod hep
  have htrivY : Γ.trivialPath v ∈ Y := hviso
  have hvtriv : v ∈ (Γ.trivialPath v).support := by simp
  constructor
  · intro h
    have hp : p = Γ.trivialPath v :=
      DWeb.IsWarp.eq_of_mem_support hY hpY htrivY (h ▸ hs.1) hvtriv
    rw [hp] at hep
    simpa [DWeb.trivialPath, DirectedPath.Path.trivial,
      DirectedPath.FinitePath.trivial, FinitePath.edgeSet] using hep
  · intro h
    have hp : p = Γ.trivialPath v :=
      DWeb.IsWarp.eq_of_mem_support hY hpY htrivY (h ▸ hs.2) hvtriv
    rw [hp] at hep
    simpa [DWeb.trivialPath, DirectedPath.Path.trivial,
      DirectedPath.FinitePath.trivial, FinitePath.edgeSet] using hep

/-- Retained singleton components are disjoint from every switched edge. -/
theorem IsSwitchingSafe.switchedEdge_not_incident_isolated
    {Y : Set Γ.DPath} {Q : AltPath Γ.graph}
    (h : IsSwitchingSafe Y Q) {v : V} (hviso : v ∈ isolatedVertices Y)
    {e : V × V} (he : e ∈ switchedEdges Y Q) :
    e.1 ≠ v ∧ e.2 ≠ v := by
  rcases he with he | he
  · exact IsWarp.familyEdge_not_incident_isolated h.1.1.1 hviso he.1
  · exact IsSwitchingAlternating.altEdge_not_incident_isolated
      h.isSwitchingAlternating hviso he.1

/-! ## Finite paths have neither ray nor cycle edge sets -/

/-- A finite walk uses finitely many directed edges. -/
theorem Walk.edgeSet_finite {D : Digraph V} {a b : V}
    (p : Walk D a b) : p.edgeSet.Finite := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
      simpa using Set.Finite.union (Set.finite_singleton (x, y)) ih

/-- A finite path uses finitely many directed edges. -/
theorem FinitePath.edgeSet_finite {D : Digraph V} (p : FinitePath D) :
    p.edgeSet.Finite :=
  Walk.edgeSet_finite p.walk

/-- Every endpoint of an edge used by a path family belongs to the family's
vertex set. -/
theorem familyEdges_subset_vertexSet_prod (W : Set Γ.DPath) :
    familyEdges W ⊆
      {e | e.1 ∈ Γ.vertexSet W ∧ e.2 ∈ Γ.vertexSet W} := by
  intro e he
  simp only [familyEdges, Set.mem_iUnion] at he
  rcases he with ⟨q, hqW, heq⟩
  have hs := q.edgeSet_subset_support_prod heq
  exact ⟨⟨q, hqW, hs.1⟩, ⟨q, hqW, hs.2⟩⟩

/-- A finite path vertex-disjoint from a family uses no edge of that
family. -/
theorem FinitePath.edgeSet_disjoint_familyEdges_of_support_disjoint
    (p : FinitePath Γ.graph) (W : Set Γ.DPath)
    (hdisj : Disjoint p.support (Γ.vertexSet W)) :
    Disjoint p.edgeSet (familyEdges W) := by
  rw [Set.disjoint_left]
  intro e hep heW
  have hp := p.edgeSet_subset_support_prod hep
  have hW := familyEdges_subset_vertexSet_prod W heW
  exact Set.disjoint_left.1 hdisj hp.1 hW.1

private def cyclePrevious (C : DirectedCycle V) (i : Fin C.length) :
    Fin C.length :=
  if hi : i.1 = 0 then
    ⟨C.length - 1, Nat.sub_lt C.positive (by omega)⟩
  else
    ⟨i.1 - 1, by omega⟩

private theorem DirectedCycle.next_cyclePrevious (C : DirectedCycle V)
    (i : Fin C.length) : C.next (cyclePrevious C i) = i := by
  ext
  simp only [cyclePrevious, next]
  split_ifs with hi
  · rw [hi]
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt C.positive))]
    simp
  · have hipos : 0 < i.1 := Nat.pos_of_ne_zero hi
    rw [Nat.sub_add_cancel hipos]
    exact Nat.mod_eq_of_lt i.2

/-- The edges of a simple finite directed walk cannot contain a directed
cycle.  The proof removes the first edge and inspects the predecessor of a
hypothetical occurrence of that edge on the cycle. -/
theorem Walk.edgeSet_not_containsDirectedCycle {D : Digraph V} :
    ∀ {a b : V} (p : Walk D a b),
      p.IsPath → ¬ ContainsDirectedCycle p.edgeSet := by
  intro a b p
  induction p with
  | nil =>
      intro _ hcycle
      rcases hcycle with ⟨C, hC⟩
      have he := hC ⟨⟨0, C.positive⟩, rfl⟩
      simp at he
  | @cons x y z h p ih =>
      intro hp hcycle
      rcases hcycle with ⟨C, hC⟩
      by_cases htail : C.EdgeSet ⊆ p.edgeSet
      · exact ih (List.nodup_cons.mp hp).2 ⟨C, htail⟩
      · rcases Set.not_subset.mp htail with ⟨e, heC, henot⟩
        have he := hC heC
        simp only [Walk.edgeSet_cons, Set.mem_union,
          Set.mem_singleton_iff] at he
        rcases he with he | he
        · rcases heC with ⟨i, rfl⟩
          have heHead :
              (C.vertex i, C.vertex (C.next i)) = (x, y) := he
          have hx : C.vertex i = x := congrArg Prod.fst heHead
          let j := cyclePrevious C i
          have hejC :
              (C.vertex j, C.vertex (C.next j)) ∈ C.EdgeSet := ⟨j, rfl⟩
          have hej := hC hejC
          simp only [Walk.edgeSet_cons, Set.mem_union,
            Set.mem_singleton_iff] at hej
          have hnext : C.next j = i := C.next_cyclePrevious i
          rcases hej with hej | hej
          · have hyx : y = x := by
              calc
                y = C.vertex (C.next j) := (congrArg Prod.snd hej).symm
                _ = C.vertex i := by rw [hnext]
                _ = x := hx
            exact (List.nodup_cons.mp hp).1 (hyx ▸ p.start_mem_support)
          · have hxin : x ∈ p.support := by
              have hs := p.edgeSet_subset_support_prod hej
              rw [hnext, hx] at hs
              exact hs.2
            exact (List.nodup_cons.mp hp).1 hxin
        · exact henot he

/-- A finite directed path's edge set contains no directed cycle. -/
theorem FinitePath.edgeSet_not_containsDirectedCycle {D : Digraph V}
    (p : FinitePath D) : ¬ ContainsDirectedCycle p.edgeSet :=
  Walk.edgeSet_not_containsDirectedCycle p.walk p.isPath

/-- A finite directed path's edge set contains no one-way infinite directed
path. -/
theorem FinitePath.edgeSet_not_containsDirectedRay {D : Digraph V}
    (p : FinitePath D) : ¬ ContainsDirectedRay p.edgeSet := by
  rintro ⟨R, hR⟩
  have hmem : ∀ n : ℕ, R.vertex n ∈ p.support := by
    intro n
    exact (p.edgeSet_subset_support_prod
      (hR ⟨n, rfl⟩)).1
  exact p.support_finite.not_infinite
    (Set.infinite_of_injective_forall_mem R.injective hmem)

/-- Ray-freeness is inherited by subsets of a finite path edge set. -/
theorem FinitePath.not_containsDirectedRay_of_subset {D : Digraph V}
    (p : FinitePath D) {E : Set (V × V)} (hE : E ⊆ p.edgeSet) :
    ¬ ContainsDirectedRay E := by
  rintro ⟨R, hR⟩
  exact FinitePath.edgeSet_not_containsDirectedRay p ⟨R, hR.trans hE⟩

/-- Cycle-freeness is inherited by subsets of a finite path edge set. -/
theorem FinitePath.not_containsDirectedCycle_of_subset {D : Digraph V}
    (p : FinitePath D) {E : Set (V × V)} (hE : E ⊆ p.edgeSet) :
    ¬ ContainsDirectedCycle E := by
  rintro ⟨C, hC⟩
  exact FinitePath.edgeSet_not_containsDirectedCycle p ⟨C, hC.trans hE⟩

/-! ## Extracting the finite path part of a cyclowarp -/

/-- If an honest cyclowarp realization of raw switch data has no cycle
components and only finite path components, its path part is the required
finite-character warp realization. -/
theorem SwitchData.hasFiniteWarpRealization_of_cyclowarp
    (S : SwitchData Γ) (C : Cyclowarp Γ)
    (hedges : C.edges = S.edges) (hiso : C.isolated = S.isolated)
    (hcycles : C.cycles = ∅)
    (hfinite : Γ.HasFiniteCharacter C.pathPart) :
    S.HasFiniteWarpRealization := by
  refine ⟨C.pathPart, ⟨C.pathPart_isWarp, ?_, ?_⟩, hfinite⟩
  · simpa [Cyclowarp.edges, Cyclowarp.pathPart, hcycles] using hedges
  · simpa [Cyclowarp.isolated, Cyclowarp.pathPart] using hiso

/-- Existential form of
`SwitchData.hasFiniteWarpRealization_of_cyclowarp`. -/
theorem SwitchData.hasFiniteWarpRealization_of_exists_cyclowarp
    (S : SwitchData Γ)
    (hC : ∃ C : Cyclowarp Γ, C.edges = S.edges ∧
      C.isolated = S.isolated ∧ C.cycles = ∅ ∧
        Γ.HasFiniteCharacter C.pathPart) :
    S.HasFiniteWarpRealization := by
  rcases hC with ⟨C, hedges, hiso, hcycles, hfinite⟩
  exact S.hasFiniteWarpRealization_of_cyclowarp C hedges hiso hcycles hfinite

/-! ## The zero-link case -/

/-- Applying the zero-link alternating path changes neither the edge relation
nor the explicitly retained singleton components. -/
theorem Cyclowarp.application_trivial_realizedBy
    (Y : Set Γ.DPath) (v : V) (hY : Γ.IsWarp Y) :
    (Cyclowarp.application Y (.trivial v)).RealizedBy Y := by
  refine ⟨hY, ?_, rfl⟩
  simp [Cyclowarp.application, switchedEdges, familyEdges]

/-- Lemma 4.9 for the zero-link alternating path. -/
theorem Cyclowarp.application_trivial_hasFiniteWarpRealization
    (Y : Set Γ.DPath) (v : V) (hY : Γ.IsWarp Y)
    (hYfin : Γ.HasFiniteCharacter Y) :
    (Cyclowarp.application Y (.trivial v)).HasFiniteWarpRealization :=
  ⟨Y, Cyclowarp.application_trivial_realizedBy Y v hY, hYfin⟩

end Alternating

end Erdos599

namespace Erdos599.Alternating.RelationDecomposition

open Set Function
open Erdos599.DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

/-- A functional directed edge relation, oriented from depth zero toward
larger natural-number depths.  `component` is a canonical root label. -/
structure ForwardOrientation (D : Digraph V) where
  edge : Set (V × V)
  carrier : Set V
  depth : V → ℕ
  component : V → V
  edge_in_graph : edge ⊆ {e | D.Adj e.1 e.2}
  endpoints_mem : ∀ e ∈ edge, e.1 ∈ carrier ∧ e.2 ∈ carrier
  out_unique : ∀ {x y z}, (x, y) ∈ edge → (x, z) ∈ edge → y = z
  in_unique : ∀ {x y z}, (x, z) ∈ edge → (y, z) ∈ edge → x = y
  depth_step : ∀ {x y}, (x, y) ∈ edge → depth y = depth x + 1
  component_step : ∀ {x y}, (x, y) ∈ edge → component y = component x
  root_label : ∀ {x}, x ∈ carrier → depth x = 0 → component x = x
  predecessor : ∀ {x}, x ∈ carrier → 0 < depth x → ∃ y, (y, x) ∈ edge

namespace ForwardOrientation

variable (O : ForwardOrientation D)

noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def IsRoot (O : ForwardOrientation D) (x : V) : Prop :=
  x ∈ O.carrier ∧ O.depth x = 0

abbrev Root (O : ForwardOrientation D) := {x : V // O.IsRoot x}

def HasNext (O : ForwardOrientation D) (x : V) : Prop :=
  ∃ y, (x, y) ∈ O.edge

def next (O : ForwardOrientation D) (x : V) : V :=
  if h : O.HasNext x then Classical.choose h else x

theorem next_edge {x : V} (h : O.HasNext x) : (x, O.next x) ∈ O.edge := by
  simp only [next, dif_pos h]
  exact Classical.choose_spec h

theorem next_eq_of_edge {x y : V} (h : (x, y) ∈ O.edge) : O.next x = y := by
  exact O.out_unique (O.next_edge ⟨y, h⟩) h

def orbit (O : ForwardOrientation D) (x : V) (n : ℕ) : V := O.next^[n] x

@[simp] theorem orbit_zero (x : V) : O.orbit x 0 = x := rfl

theorem orbit_succ (x : V) (n : ℕ) :
    O.orbit x (n + 1) = O.next (O.orbit x n) := by
  simp only [orbit]
  rw [Function.iterate_succ_apply']

def Alive (O : ForwardOrientation D) (x : V) (n : ℕ) : Prop :=
  ∀ k, k < n → O.HasNext (O.orbit x k)

theorem alive_mono {x : V} {m n : ℕ} (h : O.Alive x n) (hmn : m ≤ n) :
    O.Alive x m := by
  intro k hk
  exact h k (hk.trans_le hmn)

theorem alive_succ_iff {x : V} {n : ℕ} :
    O.Alive x (n + 1) ↔ O.Alive x n ∧ O.HasNext (O.orbit x n) := by
  constructor
  · intro h
    exact ⟨O.alive_mono h (Nat.le_succ n), h n (Nat.lt_succ_self n)⟩
  · rintro ⟨h, hn⟩ k hk
    by_cases hkn : k < n
    · exact h k hkn
    · have : k = n := by omega
      simpa [this] using hn

theorem orbit_edge {x : V} {n : ℕ} (h : O.Alive x (n + 1)) :
    (O.orbit x n, O.orbit x (n + 1)) ∈ O.edge := by
  rw [O.orbit_succ]
  exact O.next_edge ((O.alive_succ_iff.mp h).2)

theorem orbit_mem_carrier_of_alive {x : V} {n : ℕ} (h : O.Alive x (n + 1)) :
    O.orbit x n ∈ O.carrier :=
  (O.endpoints_mem _ (O.orbit_edge h)).1

theorem orbit_depth {r : V} (hr : O.IsRoot r) {n : ℕ}
    (h : O.Alive r n) : O.depth (O.orbit r n) = n := by
  induction n with
  | zero => exact hr.2
  | succ n ih =>
      have hn : O.Alive r n := O.alive_mono h (Nat.le_succ n)
      rw [O.depth_step (O.orbit_edge h), ih hn]

theorem orbit_component {r : V} (hr : O.IsRoot r) {n : ℕ}
    (h : O.Alive r n) : O.component (O.orbit r n) = r := by
  induction n with
  | zero => exact O.root_label hr.1 hr.2
  | succ n ih =>
      have hn : O.Alive r n := O.alive_mono h (Nat.le_succ n)
      rw [O.component_step (O.orbit_edge h), ih hn]

theorem orbit_injective_on_alive {r : V} (hr : O.IsRoot r) {N : ℕ}
    (h : O.Alive r N) : Set.InjOn (O.orbit r) (Set.Iic N) := by
  intro m hm n hn hmn
  have hmAlive : O.Alive r m := O.alive_mono h hm
  have hnAlive : O.Alive r n := O.alive_mono h hn
  have := congrArg O.depth hmn
  simpa [O.orbit_depth hr hmAlive, O.orbit_depth hr hnAlive] using this

theorem orbit_injective_of_neverStops {r : V} (hr : O.IsRoot r)
    (h : ∀ n : ℕ, O.HasNext (O.orbit r n)) : Injective (O.orbit r) := by
  intro m n hmn
  have hmAlive : O.Alive r m := fun k _ ↦ h k
  have hnAlive : O.Alive r n := fun k _ ↦ h k
  have := congrArg O.depth hmn
  simpa [O.orbit_depth hr hmAlive, O.orbit_depth hr hnAlive] using this

/-- The first `n` orbit edges, as an endpoint-indexed walk. -/
noncomputable def orbitWalk (O : ForwardOrientation D) (r : V) :
    (n : ℕ) → O.Alive r n →
    Walk D r (O.orbit r n)
  | 0, _ => .nil
  | n + 1, h =>
      (O.orbitWalk r n (O.alive_mono h (Nat.le_succ n))).concat
        (O.edge_in_graph (O.orbit_edge h))

@[simp] theorem orbitWalk_support (r : V) (n : ℕ) (h : O.Alive r n) :
    (O.orbitWalk r n h).support = List.ofFn (fun i : Fin (n + 1) ↦ O.orbit r i) := by
  induction n with
  | zero => simp [orbitWalk]
  | succ n ih =>
      rw [orbitWalk, Walk.support_concat, ih]
      rw [@List.ofFn_succ_last V (n + 1)
        (fun i : Fin ((n + 1) + 1) ↦ O.orbit r i)]
      congr 1 <;> simp

theorem Walk.edgeSet_append {a b c : V} (p : Walk D a b) (q : Walk D b c) :
    (p.append q).edgeSet = p.edgeSet ∪ q.edgeSet := by
  induction p with
  | nil => simp [Walk.edgeSet]
  | cons e p ih =>
      ext z
      simp only [Walk.append, Walk.edgeSet_cons, ih, Set.mem_union,
        Set.mem_singleton_iff]
      tauto

theorem Walk.edgeSet_concat {a b c : V} (p : Walk D a b) (e : D.Adj b c) :
    (p.concat e).edgeSet = p.edgeSet ∪ {(b, c)} := by
  simp [Walk.concat, Walk.edgeSet_append, Walk.edgeSet]

theorem orbitWalk_isPath {r : V} (hr : O.IsRoot r) (n : ℕ)
    (h : O.Alive r n) : (O.orbitWalk r n h).IsPath := by
  rw [Walk.isPath_iff, O.orbitWalk_support]
  exact List.nodup_ofFn.mpr fun i j hij ↦ by
    apply Fin.ext
    exact O.orbit_injective_on_alive hr h i.is_le j.is_le hij

noncomputable def finiteOrbitPath {r : V} (hr : O.IsRoot r) (n : ℕ)
    (h : O.Alive r n) : FinitePath D where
  start := r
  finish := O.orbit r n
  walk := O.orbitWalk r n h
  isPath := O.orbitWalk_isPath hr n h

noncomputable def infiniteOrbitRay {r : V} (hr : O.IsRoot r)
    (h : ∀ n : ℕ, O.HasNext (O.orbit r n)) : Ray D where
  toFun := O.orbit r
  adj_succ n := O.edge_in_graph (O.orbit_edge (fun k _ ↦ h k))
  injective := O.orbit_injective_of_neverStops hr h

theorem finiteOrbitPath_edgeSet_subset {r : V} (hr : O.IsRoot r) (n : ℕ)
    (h : O.Alive r n) : (O.finiteOrbitPath hr n h).edgeSet ⊆ O.edge := by
  induction n with
  | zero => simp [finiteOrbitPath, orbitWalk, FinitePath.edgeSet]
  | succ n ih =>
      change (O.orbitWalk r (n + 1) h).edgeSet ⊆ O.edge
      rw [orbitWalk.eq_def, Walk.edgeSet_concat]
      exact Set.union_subset
        (ih (O.alive_mono h (Nat.le_succ n)))
        (Set.singleton_subset_iff.mpr (O.orbit_edge h))

/-- Every carrier vertex is reached from the depth-zero vertex named by its
component label.  This is the induction that rules out reverse-infinite and
double-infinite components. -/
theorem reachable_from_component (x : V) (hx : x ∈ O.carrier) :
    O.IsRoot (O.component x) ∧
      O.Alive (O.component x) (O.depth x) ∧
      O.orbit (O.component x) (O.depth x) = x := by
  generalize hn : O.depth x = n
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
      cases n with
      | zero =>
          have hc : O.component x = x := O.root_label hx hn
          rw [hc]
          exact ⟨⟨hx, hn⟩, by simp [Alive], by simp⟩
      | succ n =>
          have hpos : 0 < O.depth x := by omega
          obtain ⟨y, hyx⟩ := O.predecessor hx hpos
          have hy : y ∈ O.carrier := (O.endpoints_mem _ hyx).1
          have hdy : O.depth y = n := by
            have hs := O.depth_step hyx
            omega
          obtain ⟨hroot, halive, horbit⟩ := ih n (Nat.lt_succ_self n) y hy hdy
          have hc : O.component y = O.component x := (O.component_step hyx).symm
          rw [← hc]
          refine ⟨hroot, (O.alive_succ_iff.mpr ⟨halive, ?_⟩), ?_⟩
          · rw [horbit]
            exact ⟨x, hyx⟩
          · rw [O.orbit_succ, horbit, O.next_eq_of_edge hyx]

theorem orbitWalk_edgeSet_eq {r : V} (n : ℕ) (h : O.Alive r n) :
    (O.orbitWalk r n h).edgeSet =
      {e | ∃ k < n, e = (O.orbit r k, O.orbit r (k + 1))} := by
  induction n with
  | zero => simp [orbitWalk, Walk.edgeSet]
  | succ n ih =>
      rw [orbitWalk.eq_def, Walk.edgeSet_concat, ih]
      ext e
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro (⟨k, hk, rfl⟩ | rfl)
        · exact ⟨k, hk.trans (Nat.lt_succ_self n), rfl⟩
        · exact ⟨n, Nat.lt_succ_self n, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        by_cases hkn : k < n
        · exact Or.inl ⟨k, hkn, rfl⟩
        · have : k = n := by omega
          subst k
          exact Or.inr rfl

theorem finiteOrbitPath_edge_mem {r : V} (hr : O.IsRoot r) (n : ℕ)
    (h : O.Alive r n) {k : ℕ} (hk : k < n) :
    (O.orbit r k, O.orbit r (k + 1)) ∈
      (O.finiteOrbitPath hr n h).edgeSet := by
  rw [finiteOrbitPath, FinitePath.edgeSet, O.orbitWalk_edgeSet_eq]
  exact ⟨k, hk, rfl⟩

def NeverStops (O : ForwardOrientation D) (r : V) : Prop :=
  ∀ n : ℕ, O.HasNext (O.orbit r n)

noncomputable def stoppingIndex {r : V} (h : ¬ O.NeverStops r) : ℕ :=
  Nat.find (show ∃ n, ¬ O.HasNext (O.orbit r n) by
    simpa only [NeverStops, not_forall] using h)

theorem not_hasNext_stoppingIndex {r : V} (h : ¬ O.NeverStops r) :
    ¬ O.HasNext (O.orbit r (O.stoppingIndex h)) :=
  Nat.find_spec (show ∃ n, ¬ O.HasNext (O.orbit r n) by
    simpa only [NeverStops, not_forall] using h)

theorem alive_stoppingIndex {r : V} (h : ¬ O.NeverStops r) :
    O.Alive r (O.stoppingIndex h) := by
  intro k hk
  by_contra hkstop
  exact (Nat.not_le_of_lt hk)
    (Nat.find_min' (show ∃ n, ¬ O.HasNext (O.orbit r n) by
      simpa only [NeverStops, not_forall] using h) hkstop)

noncomputable def rootPath (r : O.Root) : Path D :=
  if h : O.NeverStops r.1 then
    .inr (O.infiniteOrbitRay r.2 h)
  else
    .inl (O.finiteOrbitPath r.2 (O.stoppingIndex h) (O.alive_stoppingIndex h))

theorem rootPath_initial (r : O.Root) : (O.rootPath r).initial = r.1 := by
  simp only [rootPath]
  split <;> rfl

theorem infiniteOrbitRay_edgeSet_subset {r : V} (hr : O.IsRoot r)
    (h : O.NeverStops r) : (O.infiniteOrbitRay hr h).edgeSet ⊆ O.edge := by
  rintro e ⟨n, rfl⟩
  exact O.orbit_edge (fun k _ ↦ h k)

theorem rootPath_edgeSet_subset (r : O.Root) : (O.rootPath r).edgeSet ⊆ O.edge := by
  simp only [rootPath]
  split_ifs with h
  · exact O.infiniteOrbitRay_edgeSet_subset r.2 h
  · exact O.finiteOrbitPath_edgeSet_subset r.2 _ _

theorem rootPath_eq_finite_of_stops (r : O.Root) (h : ¬ O.NeverStops r.1) :
    ∃ p : FinitePath D, O.rootPath r = .inl p := by
  rw [rootPath, dif_neg h]
  exact ⟨_, rfl⟩

theorem containsDirectedRay_of_neverStops (r : O.Root)
    (h : O.NeverStops r.1) : ContainsDirectedRay O.edge := by
  let R : DirectedRay V :=
    { vertex := O.orbit r.1
      injective := O.orbit_injective_of_neverStops r.2 h }
  refine ⟨R, ?_⟩
  rintro e ⟨n, rfl⟩
  exact O.orbit_edge (fun k _ ↦ h k)

theorem stops_of_not_containsDirectedRay
    (h : ¬ ContainsDirectedRay O.edge) (r : O.Root) :
    ¬ O.NeverStops r.1 := by
  intro hr
  exact h (O.containsDirectedRay_of_neverStops r hr)

theorem finiteOrbitPath_component_of_mem {r : V} (hr : O.IsRoot r) (n : ℕ)
    (h : O.Alive r n) {x : V} (hx : x ∈ (O.finiteOrbitPath hr n h).support) :
    O.component x = r := by
  change x ∈ (O.orbitWalk r n h).support at hx
  rw [O.orbitWalk_support] at hx
  simp only [List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact O.orbit_component hr (O.alive_mono h i.is_le)

theorem infiniteOrbitRay_component_of_mem {r : V} (hr : O.IsRoot r)
    (h : O.NeverStops r) {x : V} (hx : x ∈ (O.infiniteOrbitRay hr h).support) :
    O.component x = r := by
  rcases hx with ⟨n, rfl⟩
  exact O.orbit_component hr (fun k _ ↦ h k)

theorem rootPath_component_of_mem (r : O.Root) {x : V}
    (hx : x ∈ (O.rootPath r).support) : O.component x = r.1 := by
  simp only [rootPath] at hx
  split at hx <;> rename_i h
  · exact O.infiniteOrbitRay_component_of_mem r.2 h hx
  · exact O.finiteOrbitPath_component_of_mem r.2 _ _ hx

theorem rootPath_support_disjoint (r s : O.Root) (hrs : r ≠ s) :
    Disjoint (O.rootPath r).support (O.rootPath s).support := by
  rw [Set.disjoint_left]
  intro x hxr hxs
  have hcomp := (O.rootPath_component_of_mem r hxr).symm.trans
    (O.rootPath_component_of_mem s hxs)
  apply hrs
  exact Subtype.ext hcomp

theorem rootPath_contains_edge {x y : V} (hxy : (x, y) ∈ O.edge) :
    let r : O.Root :=
      ⟨O.component x, (O.reachable_from_component x
        (O.endpoints_mem _ hxy).1).1⟩
    (x, y) ∈ (O.rootPath r).edgeSet := by
  dsimp only
  obtain ⟨hroot, halive, horbit⟩ :=
    O.reachable_from_component x (O.endpoints_mem _ hxy).1
  have hnext : O.next x = y := O.next_eq_of_edge hxy
  have horbitSucc : O.orbit (O.component x) (O.depth x + 1) = y := by
    rw [O.orbit_succ, horbit, hnext]
  have hhas : O.HasNext (O.orbit (O.component x) (O.depth x)) := by
    exact ⟨y, by simpa only [horbit] using hxy⟩
  have haliveSucc : O.Alive (O.component x) (O.depth x + 1) :=
    O.alive_succ_iff.mpr ⟨halive, hhas⟩
  simp only [rootPath]
  split <;> rename_i hstop
  · refine ⟨O.depth x, ?_⟩
    change (x, y) =
      (O.orbit (O.component x) (O.depth x),
        O.orbit (O.component x) (O.depth x + 1))
    exact Prod.ext horbit.symm horbitSucc.symm
  · have hlt : O.depth x < O.stoppingIndex hstop := by
      by_contra hnot
      have hle : O.stoppingIndex hstop ≤ O.depth x := Nat.le_of_not_gt hnot
      have hsAlive : O.Alive (O.component x) (O.stoppingIndex hstop + 1) :=
        O.alive_mono haliveSucc (by omega)
      exact O.not_hasNext_stoppingIndex hstop
        ((O.alive_succ_iff.mp hsAlive).2)
    have hm := O.finiteOrbitPath_edge_mem hroot (O.stoppingIndex hstop)
      (O.alive_stoppingIndex hstop) hlt
    simpa only [Path.edgeSet_finite, horbit, horbitSucc] using hm

def rootPaths (O : ForwardOrientation D) : Set (Path D) :=
  Set.range O.rootPath

def rootPathEdges (O : ForwardOrientation D) : Set (V × V) :=
  ⋃ p ∈ O.rootPaths, p.edgeSet

theorem rootPathEdges_eq : O.rootPathEdges = O.edge := by
  apply Set.Subset.antisymm
  · intro e he
    simp only [rootPathEdges, Set.mem_iUnion, rootPaths, Set.mem_range] at he
    rcases he with ⟨p, ⟨r, rfl⟩, he⟩
    exact O.rootPath_edgeSet_subset r he
  · rintro ⟨x, y⟩ hxy
    simp only [rootPathEdges, Set.mem_iUnion, rootPaths, Set.mem_range]
    let r : O.Root :=
      ⟨O.component x, (O.reachable_from_component x
        (O.endpoints_mem _ hxy).1).1⟩
    exact ⟨O.rootPath r, ⟨r, rfl⟩, O.rootPath_contains_edge hxy⟩

theorem rootPaths_pairwiseDisjoint :
    O.rootPaths.PairwiseDisjoint Path.support := by
  intro p hp q hq hpq
  rcases hp with ⟨r, rfl⟩
  rcases hq with ⟨s, rfl⟩
  apply O.rootPath_support_disjoint r s
  intro hrs
  subst s
  exact hpq rfl

end

end ForwardOrientation

namespace DWeb

open Erdos599

variable {V : Type u} (G : DWeb V)

/-- A forward-oriented functional relation decomposes into the disjoint
finite paths and rays generated by its depth-zero roots. -/
theorem exists_warp_realizing_forwardOrientation
    (O : ForwardOrientation G.graph) :
    ∃ W : Set G.DPath, G.IsWarp W ∧ familyEdges W = O.edge := by
  refine ⟨O.rootPaths, O.rootPaths_pairwiseDisjoint, ?_⟩
  exact O.rootPathEdges_eq

/-- If every root orbit stops, the realizing warp has finite character. -/
theorem forwardOrientation_rootPaths_finite
    (O : ForwardOrientation G.graph)
    (hstop : ∀ r : O.Root, ¬ O.NeverStops r.1) :
    G.HasFiniteCharacter O.rootPaths := by
  intro p hp
  rcases hp with ⟨r, rfl⟩
  exact O.rootPath_eq_finite_of_stops r (hstop r)

theorem forwardOrientation_rootPaths_finite_of_noRay
    (O : ForwardOrientation G.graph)
    (h : ¬ ContainsDirectedRay O.edge) :
    G.HasFiniteCharacter O.rootPaths :=
  forwardOrientation_rootPaths_finite G O (O.stops_of_not_containsDirectedRay h)

end DWeb

end Erdos599.Alternating.RelationDecomposition

namespace Erdos599.Alternating.RelationDecomposition

open Set Function

universe u

variable {V : Type u} {D : Digraph V}

namespace ForwardOrientation

noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

private def CollisionDistance (f : ℕ → V) (d : ℕ) : Prop :=
  0 < d ∧ ∃ m, f (m + d) = f m

private theorem exists_collisionDistance_of_not_injective (f : ℕ → V)
    (hf : ¬ Injective f) : ∃ d, CollisionDistance f d := by
  obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hf
  rcases lt_or_gt_of_ne hne with hablt | hbalt
  · refine ⟨b - a, by omega, a, ?_⟩
    rw [Nat.add_sub_of_le (Nat.le_of_lt hablt)]
    exact hab.symm
  · refine ⟨a - b, by omega, b, ?_⟩
    rw [Nat.add_sub_of_le (Nat.le_of_lt hbalt)]
    exact hab

private theorem descending_chain_injective_of_noCycle
    (E : Set (V × V)) (hcycle : ¬ ContainsDirectedCycle E)
    (f : ℕ → V) (hf : ∀ n, (f (n + 1), f n) ∈ E) : Injective f := by
  by_contra hnot
  let hex := exists_collisionDistance_of_not_injective f hnot
  let d := Nat.find hex
  have hd := Nat.find_spec hex
  let m := Classical.choose hd.2
  have hm : f (m + d) = f m := Classical.choose_spec hd.2
  have hdmin : ∀ e < d, ¬ CollisionDistance f e := by
    intro e he hce
    exact (Nat.not_le_of_lt he) (Nat.find_min' hex hce)
  let C : DirectedCycle V :=
    { length := d
      positive := hd.1
      vertex := fun i ↦ f (m + i.rev.1)
      injective := by
        intro i j hij
        apply Fin.rev_injective
        apply Fin.ext
        by_contra hrev
        rcases lt_or_gt_of_ne hrev with hlt | hgt
        · let e := j.rev.1 - i.rev.1
          have hepos : 0 < e := by
            exact Nat.sub_pos_of_lt hlt
          have helt : e < d := by
            exact Nat.sub_lt_of_lt j.rev.2
          apply hdmin e helt
          refine ⟨hepos, m + i.rev.1, ?_⟩
          have hindex : (m + i.rev.1) + e = m + j.rev.1 := by
            calc
              (m + i.rev.1) + e = m + (i.rev.1 + e) := Nat.add_assoc _ _ _
              _ = m + (i.rev.1 + (j.rev.1 - i.rev.1)) := rfl
              _ = m + j.rev.1 := congrArg (m + ·)
                (Nat.add_sub_of_le (Nat.le_of_lt hlt))
          rw [hindex]
          exact hij.symm
        · let e := i.rev.1 - j.rev.1
          have hepos : 0 < e := by
            exact Nat.sub_pos_of_lt hgt
          have helt : e < d := by
            exact Nat.sub_lt_of_lt i.rev.2
          apply hdmin e helt
          refine ⟨hepos, m + j.rev.1, ?_⟩
          have hindex : (m + j.rev.1) + e = m + i.rev.1 := by
            calc
              (m + j.rev.1) + e = m + (j.rev.1 + e) := Nat.add_assoc _ _ _
              _ = m + (j.rev.1 + (i.rev.1 - j.rev.1)) := rfl
              _ = m + i.rev.1 := congrArg (m + ·)
                (Nat.add_sub_of_le (Nat.le_of_lt hgt))
          rw [hindex]
          exact hij }
  apply hcycle
  refine ⟨C, ?_⟩
  rintro e ⟨i, rfl⟩
  have hClen : C.length = d := rfl
  by_cases hi : i.1 + 1 < d
  · have hnext : (C.next i).1 = i.1 + 1 := by
      simp [DirectedCycle.next, hClen, Nat.mod_eq_of_lt hi]
    have hrev : (C.next i).rev.1 + 1 = i.rev.1 := by
      simp only [Fin.val_rev, hClen]
      have hii := i.2
      omega
    change (f (m + i.rev.1), f (m + (C.next i).rev.1)) ∈ E
    have hedge := hf (m + (C.next i).rev.1)
    rw [Nat.add_assoc, hrev] at hedge
    exact hedge
  · have hilast : i.1 = d - 1 := by omega
    have hisucc : i.1 + 1 = d := by omega
    have hnext : (C.next i).1 = 0 := by
      simp [DirectedCycle.next, hClen, hisucc]
    have hirev : i.rev.1 = 0 := by simp [Fin.val_rev, hClen, hisucc]
    have hnrev : (C.next i).rev.1 = d - 1 := by
      simp [Fin.val_rev, hClen, hnext]
    change (f (m + i.rev.1), f (m + (C.next i).rev.1)) ∈ E
    rw [hirev, hnrev, Nat.add_zero, ← hm]
    have hdsub : d - 1 + 1 = d := Nat.sub_add_cancel hd.1
    simpa only [Nat.add_assoc, hdsub] using hf (m + (d - 1))

theorem predecessor_wellFounded
    (E : Set (V × V)) (hcycle : ¬ ContainsDirectedCycle E)
    (hreverse : ¬ ContainsReverseDirectedRay E) :
    WellFounded (fun x y ↦ (x, y) ∈ E) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  constructor
  rintro ⟨f, hf⟩
  apply hreverse
  exact ⟨⟨f, descending_chain_injective_of_noCycle E hcycle f hf⟩, hf⟩

def HasPredecessor (E : Set (V × V)) (x : V) : Prop :=
  ∃ y, (y, x) ∈ E

noncomputable def chosenPred (E : Set (V × V)) (x : V) : V :=
  if h : HasPredecessor E x then Classical.choose h else x

theorem chosenPred_edge (E : Set (V × V)) {x : V}
    (h : HasPredecessor E x) : (chosenPred E x, x) ∈ E := by
  simp only [chosenPred, dif_pos h]
  exact Classical.choose_spec h

theorem chosenPred_eq_of_edge (E : Set (V × V))
    (hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E))
    {x y : V} (hxy : (x, y) ∈ E) : chosenPred E y = x := by
  exact hunique.1 (chosenPred_edge E ⟨x, hxy⟩) hxy

noncomputable def wellFoundedDepth (E : Set (V × V))
    (hwf : WellFounded (fun x y ↦ (x, y) ∈ E)) : V → ℕ :=
  hwf.fix fun x rec ↦
    if h : HasPredecessor E x then rec (chosenPred E x) (chosenPred_edge E h) + 1
    else 0

theorem wellFoundedDepth_eq (E : Set (V × V))
    (hwf : WellFounded (fun x y ↦ (x, y) ∈ E)) (x : V) :
    wellFoundedDepth E hwf x =
      if h : HasPredecessor E x then
        wellFoundedDepth E hwf (chosenPred E x) + 1 else 0 := by
  rw [wellFoundedDepth, WellFounded.fix_eq]

noncomputable def wellFoundedRoot (E : Set (V × V))
    (hwf : WellFounded (fun x y ↦ (x, y) ∈ E)) : V → V :=
  hwf.fix fun x rec ↦
    if h : HasPredecessor E x then rec (chosenPred E x) (chosenPred_edge E h)
    else x

theorem wellFoundedRoot_eq (E : Set (V × V))
    (hwf : WellFounded (fun x y ↦ (x, y) ∈ E)) (x : V) :
    wellFoundedRoot E hwf x =
      if h : HasPredecessor E x then
        wellFoundedRoot E hwf (chosenPred E x) else x := by
  rw [wellFoundedRoot, WellFounded.fix_eq]

theorem wellFoundedDepth_step (E : Set (V × V))
    (hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E))
    (hwf : WellFounded (fun x y ↦ (x, y) ∈ E))
    {x y : V} (hxy : (x, y) ∈ E) :
    wellFoundedDepth E hwf y = wellFoundedDepth E hwf x + 1 := by
  rw [wellFoundedDepth_eq, dif_pos ⟨x, hxy⟩,
    chosenPred_eq_of_edge E hunique hxy]

theorem wellFoundedRoot_step (E : Set (V × V))
    (hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E))
    (hwf : WellFounded (fun x y ↦ (x, y) ∈ E))
    {x y : V} (hxy : (x, y) ∈ E) :
    wellFoundedRoot E hwf y = wellFoundedRoot E hwf x := by
  rw [wellFoundedRoot_eq, dif_pos ⟨x, hxy⟩,
    chosenPred_eq_of_edge E hunique hxy]

theorem wellFoundedDepth_eq_zero_iff (E : Set (V × V))
    (hwf : WellFounded (fun x y ↦ (x, y) ∈ E)) (x : V) :
    wellFoundedDepth E hwf x = 0 ↔ ¬ HasPredecessor E x := by
  rw [wellFoundedDepth_eq]
  by_cases h : HasPredecessor E x
  · simp [h]
  · simp [h]

theorem wellFoundedRoot_eq_self_of_depth_eq_zero (E : Set (V × V))
    (hwf : WellFounded (fun x y ↦ (x, y) ∈ E)) {x : V}
    (hdepth : wellFoundedDepth E hwf x = 0) :
    wellFoundedRoot E hwf x = x := by
  have hpred : ¬ HasPredecessor E x :=
    (wellFoundedDepth_eq_zero_iff E hwf x).mp hdepth
  rw [wellFoundedRoot_eq, dif_neg hpred]

/-- A bi-unique acyclic edge relation with no reverse ray admits the
depth/root certificate used by the path decomposition theorem. -/
theorem exists_forwardOrientation
    (E : Set (V × V)) (carrier : Set V)
    (hgraph : E ⊆ {e | D.Adj e.1 e.2})
    (hendpoints : ∀ e ∈ E, e.1 ∈ carrier ∧ e.2 ∈ carrier)
    (hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E))
    (hcycle : ¬ ContainsDirectedCycle E)
    (hreverse : ¬ ContainsReverseDirectedRay E) :
    ∃ O : ForwardOrientation D, O.edge = E := by
  let hwf : WellFounded (fun x y ↦ (x, y) ∈ E) :=
    predecessor_wellFounded E hcycle hreverse
  let O : ForwardOrientation D :=
    { edge := E
      carrier := carrier
      depth := wellFoundedDepth E hwf
      component := wellFoundedRoot E hwf
      edge_in_graph := hgraph
      endpoints_mem := hendpoints
      out_unique := fun hxy hxz ↦ hunique.2 hxy hxz
      in_unique := fun hxz hyz ↦ hunique.1 hxz hyz
      depth_step := fun hxy ↦ wellFoundedDepth_step E hunique hwf hxy
      component_step := fun hxy ↦ wellFoundedRoot_step E hunique hwf hxy
      root_label := fun _hx hdepth ↦
        wellFoundedRoot_eq_self_of_depth_eq_zero E hwf hdepth
      predecessor := by
        intro x _hx hpos
        have hne : wellFoundedDepth E hwf x ≠ 0 := Nat.ne_of_gt hpos
        exact Classical.byContradiction fun hnot ↦
          hne ((wellFoundedDepth_eq_zero_iff E hwf x).mpr hnot) }
  refine ⟨O, ?_⟩
  rfl

end

end ForwardOrientation

end Erdos599.Alternating.RelationDecomposition
