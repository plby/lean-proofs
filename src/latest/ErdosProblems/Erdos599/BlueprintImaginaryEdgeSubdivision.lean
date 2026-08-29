/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.BlueprintSplice
import ErdosProblems.Erdos599.LadderSuccessorBridge
import ErdosProblems.Erdos599.SafeSwitchingAssembly

/-!
# Subdividing one imaginary edge of a linkage blueprint

An imaginary edge on one blueprint member may be replaced by a finite path
in the original graph with the same endpoints.  The interior of the real
path is required to avoid the old blueprint.  Unlike the stronger
predecessor-preserving replacement interfaces, subdivision is allowed to add
the final real edge entering the old head of the imaginary edge.

The construction below is occurrence-aware.  It first splits the unique old
member at the represented edge, inserts the lifted original path, and then
reattaches the unchanged suffix.  It works for both finite members and rays.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

universe u

variable {V : Type u}

namespace DirectedPath

namespace Walk

variable {D : Digraph V} {a b u v : V}

/-- An occurrence of `u → v` splits a finite walk into the prefix ending at
`u`, that edge, and the suffix beginning at `v`. -/
structure EdgeSplit (p : Walk D a b) (u v : V) where
  front : Walk D a u
  edge : D.Adj u v
  back : Walk D v b
  rebuild : p = front.append (.cons edge back)

/-- Every member of the edge set supplies an exact ordered edge split. -/
theorem exists_edgeSplit (p : Walk D a b) {u v : V}
    (h : (u, v) ∈ p.edgeSet) : Nonempty (p.EdgeSplit u v) := by
  induction p with
  | nil => simp at h
  | @cons a c b e p ih =>
      simp only [Walk.edgeSet_cons, Set.mem_union,
        Set.mem_singleton_iff] at h
      rcases h with huv | htail
      · have hau : a = u := (congrArg Prod.fst huv).symm
        have hcv : c = v := (congrArg Prod.snd huv).symm
        subst u
        subst v
        exact ⟨{
          front := .nil
          edge := e
          back := p
          rebuild := rfl }⟩
      · obtain ⟨S⟩ := ih htail
        exact ⟨{
          front := .cons e S.front
          edge := S.edge
          back := S.back
          rebuild := by
            exact congrArg (Walk.cons e) S.rebuild }⟩

theorem EdgeSplit.support_eq (S : EdgeSplit p u v) :
    p.support = S.front.support ++ S.back.support := by
  calc
    p.support = (S.front.append (.cons S.edge S.back)).support :=
      congrArg Walk.support S.rebuild
    _ = S.front.support ++ S.back.support := by
      rw [Walk.support_append]
      simp

theorem EdgeSplit.edgeSet_eq (S : EdgeSplit p u v) :
    p.edgeSet = S.front.edgeSet ∪ {(u, v)} ∪ S.back.edgeSet := by
  calc
    p.edgeSet = (S.front.append (.cons S.edge S.back)).edgeSet :=
      congrArg Walk.edgeSet S.rebuild
    _ = S.front.edgeSet ∪ {(u, v)} ∪ S.back.edgeSet := by
      rw [Walk.edgeSet_append']
      simp only [Walk.edgeSet_cons]
      exact (Set.union_assoc _ _ _).symm

theorem EdgeSplit.front_isPath (S : EdgeSplit p u v) (hp : p.IsPath) :
    S.front.IsPath := by
  rw [Walk.IsPath, S.support_eq] at hp
  exact (List.nodup_append.mp hp).1

theorem EdgeSplit.back_isPath (S : EdgeSplit p u v) (hp : p.IsPath) :
    S.back.IsPath := by
  rw [Walk.IsPath, S.support_eq] at hp
  exact (List.nodup_append.mp hp).2.1

theorem EdgeSplit.support_disjoint (S : EdgeSplit p u v) (hp : p.IsPath) :
    Disjoint ({x | x ∈ S.front.support} : Set V)
      {x | x ∈ S.back.support} := by
  rw [Walk.IsPath, S.support_eq] at hp
  apply Set.disjoint_left.2
  intro x hxfront hxback
  exact (List.nodup_append.mp hp).2.2 x hxfront x hxback rfl

end Walk

namespace Path

variable {D : Digraph V}

/-- Ordered data obtained by cutting a finite path or ray at one of its
directed edge occurrences. -/
structure EdgeSplit (q : Path D) (u v : V) where
  front : FinitePath D
  back : Path D
  front_start : front.start = q.initial
  front_finish : front.finish = u
  back_initial : back.initial = v
  back_terminal : back.terminal? = q.terminal?
  support_eq : q.support = front.support ∪ back.support
  edgeSet_eq : q.edgeSet = front.edgeSet ∪ {(u, v)} ∪ back.edgeSet
  support_disjoint : Disjoint front.support back.support

theorem EdgeSplit.front_finish_mem
    {q : Path D} {u v : V} (S : q.EdgeSplit u v) :
    u ∈ S.front.support :=
  Eq.mp (congrArg (fun z ↦ z ∈ S.front.support) S.front_finish)
    S.front.finish_mem_support

theorem EdgeSplit.back_initial_mem
    {q : Path D} {u v : V} (S : q.EdgeSplit u v) :
    v ∈ S.back.support :=
  Eq.mp (congrArg (fun z ↦ z ∈ S.back.support) S.back_initial)
    (Path.initial_mem_support S.back)

private noncomputable def finiteEdgeSplit (q : FinitePath D) {u v : V}
    (h : (u, v) ∈ q.edgeSet) : EdgeSplit (.inl q) u v := by
  let S := Classical.choice (q.walk.exists_edgeSplit h)
  let f : FinitePath D :=
    { start := q.start
      finish := u
      walk := S.front
      isPath := S.front_isPath q.isPath }
  let g : FinitePath D :=
    { start := v
      finish := q.finish
      walk := S.back
      isPath := S.back_isPath q.isPath }
  refine {
    front := f
    back := .inl g
    front_start := rfl
    front_finish := rfl
    back_initial := rfl
    back_terminal := rfl
    support_eq := ?_
    edgeSet_eq := ?_
    support_disjoint := ?_ }
  · exact Set.ext fun x ↦ by
      change x ∈ q.walk.support ↔
        x ∈ S.front.support ∨ x ∈ S.back.support
      rw [S.support_eq, List.mem_append]
  · exact S.edgeSet_eq
  · exact S.support_disjoint q.isPath

private noncomputable def rayEdgeIndex (r : Ray D) {u v : V}
    (h : (u, v) ∈ r.edgeSet) : ℕ := Classical.choose h

private theorem rayEdgeIndex_spec (r : Ray D) {u v : V}
    (h : (u, v) ∈ r.edgeSet) :
    (u, v) = (r (rayEdgeIndex r h), r (rayEdgeIndex r h + 1)) :=
  Classical.choose_spec h

private noncomputable def rayEdgeSplit (r : Ray D) {u v : V}
    (h : (u, v) ∈ r.edgeSet) : EdgeSplit (.inr r) u v := by
  let n := rayEdgeIndex r h
  have hpair : (u, v) = (r n, r (n + 1)) := rayEdgeIndex_spec r h
  have hu : u = r n := congrArg Prod.fst hpair
  have hv : v = r (n + 1) := congrArg Prod.snd hpair
  let f := Alternating.SwitchingCore.rayPrefixPath r n
  let s : Path D := .inr (r.tail (n + 1))
  refine {
    front := f
    back := s
    front_start := rfl
    front_finish := by
      change r n = u
      exact hu.symm
    back_initial := by
      change r (n + 1) = v
      exact hv.symm
    back_terminal := rfl
    support_eq := ?_
    edgeSet_eq := ?_
    support_disjoint := ?_ }
  · ext x
    constructor
    · rintro ⟨k, rfl⟩
      by_cases hk : k ≤ n
      · left
        change r k ∈
          (Alternating.SwitchingCore.rayPrefixWalk r n).support
        rw [Alternating.SwitchingCore.rayPrefixWalk_support]
        exact List.mem_ofFn.mpr ⟨⟨k, by omega⟩, rfl⟩
      · right
        refine ⟨k - (n + 1), ?_⟩
        change r ((n + 1) + (k - (n + 1))) = r k
        congr 1
        omega
    · rintro (hx | hx)
      · change x ∈
          (Alternating.SwitchingCore.rayPrefixWalk r n).support at hx
        rw [Alternating.SwitchingCore.rayPrefixWalk_support] at hx
        rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
        exact ⟨i.1, rfl⟩
      · rcases hx with ⟨k, rfl⟩
        exact ⟨n + 1 + k, rfl⟩
  · rw [Alternating.SwitchingCore.rayPrefixPath_edgeSet]
    ext e
    constructor
    · rintro ⟨k, rfl⟩
      by_cases hk : k < n
      · exact Or.inl (Or.inl ⟨k, hk, rfl⟩)
      by_cases hkn : k = n
      · subst k
        exact Or.inl (Or.inr (by simpa [hu, hv]))
      · apply Or.inr
        refine ⟨k - (n + 1), ?_⟩
        have hkge : n + 1 ≤ k := by omega
        change (r k, r (k + 1)) =
          (r ((n + 1) + (k - (n + 1))),
            r ((n + 1) + (k - (n + 1)) + 1))
        rw [Nat.add_sub_of_le hkge]
    · rintro (he | he)
      · rcases he with he | he
        · rcases he with ⟨k, hk, rfl⟩
          exact ⟨k, rfl⟩
        · have heq : e = (u, v) := Set.mem_singleton_iff.mp he
          subst e
          exact ⟨n, hpair⟩
      · rcases he with ⟨k, rfl⟩
        exact ⟨n + 1 + k, by simp [Nat.add_assoc]⟩
  · apply Set.disjoint_left.2
    intro x hxfront hxback
    change x ∈ (Alternating.SwitchingCore.rayPrefixWalk r n).support at hxfront
    rw [Alternating.SwitchingCore.rayPrefixWalk_support] at hxfront
    rcases List.mem_ofFn.mp hxfront with ⟨i, rfl⟩
    rcases hxback with ⟨k, heq⟩
    have := r.injective heq
    omega

/-- Split a path at a represented edge, preserving whether its suffix is
finite or a ray. -/
noncomputable def edgeSplit (q : Path D) {u v : V}
    (h : (u, v) ∈ q.edgeSet) : q.EdgeSplit u v := by
  rcases q with q | r
  · exact finiteEdgeSplit q h
  · exact rayEdgeSplit r h

/-- The part of the old member before the cut edge meets the inserted path
only at the old tail of that edge. -/
theorem EdgeSplit.front_inter_insert_subset
    {q : Path D} {u v : V} (S : q.EdgeSplit u v)
    (P : FinitePath D) (hstart : P.start = u)
    (hfresh : q.support ∩ P.support ⊆ {u, v}) :
    S.front.support ∩ P.support ⊆ {u} := by
  intro x hx
  have hxq : x ∈ q.support := by
    rw [S.support_eq]
    exact Or.inl hx.1
  have hxuv := hfresh ⟨hxq, hx.2⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxuv ⊢
  rcases hxuv with hxu | hxv
  · exact hxu
  · exfalso
    have hvback : v ∈ S.back.support := by
      exact S.back_initial_mem
    exact Set.disjoint_left.1 S.support_disjoint hx.1 (hxv ▸ hvback)

/-- Insert the finite replacement path immediately after the old finite
prefix. -/
noncomputable def insertFront
    {q : Path D} {u v : V} (S : q.EdgeSplit u v)
    (P : FinitePath D) (hstart : P.start = u)
    (hfresh : q.support ∩ P.support ⊆ {u, v}) : FinitePath D :=
  S.front.appendFinite P
    (hstart.trans S.front_finish.symm)
    (by
      intro x hx
      have hxu := S.front_inter_insert_subset P hstart hfresh hx
      exact Set.mem_singleton_iff.mpr
        ((Set.mem_singleton_iff.mp hxu).trans S.front_finish.symm))

@[simp] theorem insertFront_start
    {q : Path D} {u v : V} (S : q.EdgeSplit u v)
    (P : FinitePath D) (hstart : P.start = u)
    (hfresh : q.support ∩ P.support ⊆ {u, v}) :
    (insertFront S P hstart hfresh).start = S.front.start := by
  exact FinitePath.appendFinite_start _ _ _ _

@[simp] theorem insertFront_finish
    {q : Path D} {u v : V} (S : q.EdgeSplit u v)
    (P : FinitePath D) (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : q.support ∩ P.support ⊆ {u, v}) :
    (insertFront S P hstart hfresh).finish = v := by
  calc
    (insertFront S P hstart hfresh).finish = P.finish :=
      FinitePath.appendFinite_finish _ _ _ _
    _ = v := hfinish

@[simp] theorem insertFront_support
    {q : Path D} {u v : V} (S : q.EdgeSplit u v)
    (P : FinitePath D) (hstart : P.start = u)
    (hfresh : q.support ∩ P.support ⊆ {u, v}) :
    (insertFront S P hstart hfresh).support =
      S.front.support ∪ P.support := by
  exact FinitePath.support_appendFinite_eq_union _ _ _ _

@[simp] theorem insertFront_edgeSet
    {q : Path D} {u v : V} (S : q.EdgeSplit u v)
    (P : FinitePath D) (hstart : P.start = u)
    (hfresh : q.support ∩ P.support ⊆ {u, v}) :
    (insertFront S P hstart hfresh).edgeSet =
      S.front.edgeSet ∪ P.edgeSet := by
  exact Blueprint.LinkageBlueprint.FinitePath.edgeSet_appendFinite _ _ _ _

/-- After insertion, the only possible meeting with the untouched suffix is
its old initial vertex `v`. -/
theorem insertFront_inter_back_subset
    {q : Path D} {u v : V} (S : q.EdgeSplit u v)
    (P : FinitePath D) (hstart : P.start = u)
    (hfinish : P.finish = v)
    (hfresh : q.support ∩ P.support ⊆ {u, v}) :
    (insertFront S P hstart hfresh).support ∩ S.back.support ⊆ {v} := by
  intro x hx
  rw [insertFront_support] at hx
  rcases hx.1 with hxfront | hxP
  · exact (Set.disjoint_left.1 S.support_disjoint hxfront hx.2).elim
  · have hxq : x ∈ q.support := by
      rw [S.support_eq]
      exact Or.inr hx.2
    have hxuv := hfresh ⟨hxq, hxP⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxuv ⊢
    rcases hxuv with hxu | hxv
    · have hufront : u ∈ S.front.support := by
        exact S.front_finish_mem
      exact (Set.disjoint_left.1 S.support_disjoint
        (hxu ▸ hufront) hx.2).elim
    · exact hxv

private theorem insertFront_finish_mem_back
    {q : Path D} {u v : V} (S : q.EdgeSplit u v)
    (P : FinitePath D) (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : q.support ∩ P.support ⊆ {u, v}) :
    (insertFront S P hstart hfresh).finish ∈ S.back.support := by
  have hvback : v ∈ S.back.support := S.back_initial_mem
  exact (insertFront_finish S P hstart hfinish hfresh).symm ▸ hvback

private theorem insertFront_appendable
    {q : Path D} {u v : V} (S : q.EdgeSplit u v)
    (P : FinitePath D) (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : q.support ∩ P.support ⊆ {u, v}) :
    Path.Appendable (insertFront S P hstart hfresh) S.back
      (insertFront_finish_mem_back S P hstart hfinish hfresh) := by
  apply Set.disjoint_left.2
  intro x hxinsert hxback
  have hxback' : x ∈ S.back.support :=
    S.back.support_suffixFrom_subset _ _ hxback.1
  have hxv : x = v := Set.mem_singleton_iff.mp
    (insertFront_inter_back_subset S P hstart hfinish hfresh
      ⟨hxinsert, hxback'⟩)
  exact hxback.2 (by
    rw [insertFront_finish S P hstart hfinish hfresh]
    exact hxv)

/-- Replace one represented edge of a path by a finite path with the same
endpoints.  The old suffix, including its finite/ray character, is retained
verbatim. -/
noncomputable def subdivide
    {q : Path D} {u v : V} (S : q.EdgeSplit u v)
    (P : FinitePath D) (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : q.support ∩ P.support ⊆ {u, v}) : Path D :=
  Path.appendAt (insertFront S P hstart hfresh) S.back
    (insertFront_finish_mem_back S P hstart hfinish hfresh)
    (insertFront_appendable S P hstart hfinish hfresh)

private theorem suffixFrom_insertFront_finish
    {q : Path D} {u v : V} (S : q.EdgeSplit u v)
    (P : FinitePath D) (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : q.support ∩ P.support ⊆ {u, v}) :
    S.back.suffixFrom (insertFront S P hstart hfresh).finish
        (insertFront_finish_mem_back S P hstart hfinish hfresh) = S.back := by
  have hinitial : (insertFront S P hstart hfresh).finish = S.back.initial := by
    rw [insertFront_finish S P hstart hfinish hfresh, S.back_initial]
  simpa only [hinitial] using
    Path.suffixFrom_initial_eq S.back (Path.initial_mem_support S.back)

@[simp] theorem subdivide_initial
    {q : Path D} {u v : V} (S : q.EdgeSplit u v)
    (P : FinitePath D) (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : q.support ∩ P.support ⊆ {u, v}) :
    (subdivide S P hstart hfinish hfresh).initial = q.initial := by
  calc
    (subdivide S P hstart hfinish hfresh).initial =
        (insertFront S P hstart hfresh).start :=
      (Path.extends_initial (Path.extends_appendAt
        (insertFront S P hstart hfresh) S.back
        (insertFront_finish_mem_back S P hstart hfinish hfresh)
        (insertFront_appendable S P hstart hfinish hfresh))).symm
    _ = S.front.start := insertFront_start S P hstart hfresh
    _ = q.initial := S.front_start

@[simp] theorem subdivide_terminal?
    {q : Path D} {u v : V} (S : q.EdgeSplit u v)
    (P : FinitePath D) (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : q.support ∩ P.support ⊆ {u, v}) :
    (subdivide S P hstart hfinish hfresh).terminal? = q.terminal? := by
  rw [subdivide, Path.terminal?_appendAt, S.back_terminal]

@[simp] theorem subdivide_support
    {q : Path D} {u v : V} (S : q.EdgeSplit u v)
    (P : FinitePath D) (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : q.support ∩ P.support ⊆ {u, v}) :
    (subdivide S P hstart hfinish hfresh).support =
      q.support ∪ P.support := by
  rw [subdivide, Path.support_appendAt,
    suffixFrom_insertFront_finish S P hstart hfinish hfresh,
    insertFront_support, S.support_eq]
  ext x
  simp only [Set.mem_union]
  tauto

theorem EdgeSplit.cutEdge_not_mem_front
    {q : Path D} {u v : V} (S : q.EdgeSplit u v) :
    (u, v) ∉ S.front.edgeSet := by
  intro huv
  have hvfront := (S.front.edgeSet_subset_support_prod huv).2
  have hvback : v ∈ S.back.support := by
    exact S.back_initial_mem
  exact Set.disjoint_left.1 S.support_disjoint hvfront hvback

theorem EdgeSplit.cutEdge_not_mem_back
    {q : Path D} {u v : V} (S : q.EdgeSplit u v) :
    (u, v) ∉ S.back.edgeSet := by
  intro huv
  have huback := (S.back.edgeSet_subset_support_prod huv).1
  have hufront : u ∈ S.front.support := by
    exact S.front_finish_mem
  exact Set.disjoint_left.1 S.support_disjoint hufront huback

/-- Neither a finite path nor a ray has an edge entering its initial
vertex. -/
theorem no_incoming_edge_at_initial (q : Path D) (y : V) :
    (y, q.initial) ∉ q.edgeSet := by
  rcases q with p | r
  · exact _root_.Erdos599.Alternating.FinitePath.no_incoming_edge_at_start p y
  · rintro ⟨n, hn⟩
    have heq : r (n + 1) = r 0 := by
      simpa only [Path.initial, Ray.initial] using (congrArg Prod.snd hn).symm
    have := r.injective heq
    omega

@[simp] theorem subdivide_edgeSet
    {q : Path D} {u v : V} (S : q.EdgeSplit u v)
    (P : FinitePath D) (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : q.support ∩ P.support ⊆ {u, v}) :
    (subdivide S P hstart hfinish hfresh).edgeSet =
      (q.edgeSet \ {(u, v)}) ∪ P.edgeSet := by
  rw [subdivide, Path.edgeSet_appendAt,
    suffixFrom_insertFront_finish S P hstart hfinish hfresh,
    insertFront_edgeSet, S.edgeSet_eq]
  ext e
  simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
  by_cases he : e = (u, v)
  · subst e
    simp only [S.cutEdge_not_mem_front, S.cutEdge_not_mem_back,
      not_true_eq_false, and_false, false_or]
    tauto
  · simp only [he, not_false_eq_true, and_true]
    tauto

end Path
end DirectedPath

namespace Blueprint

open DirectedPath

namespace LinkageBlueprint

variable {Γ : DWeb V} {Y : Set Γ.DPath} {κ : Cardinal.{u}}

private theorem exists_edgeOwner (W : LinkageBlueprint Γ Y κ)
    {u v : V} (huv : (u, v) ∈ W.edgeSet) :
    ∃ q ∈ W.paths, (u, v) ∈ q.edgeSet := by
  simp only [LinkageBlueprint.edgeSet, Set.mem_iUnion] at huv
  rcases huv with ⟨q, hq, heq⟩
  exact ⟨q, hq, heq⟩

/-- The unique old blueprint member carrying the represented edge. -/
noncomputable def edgeOwner (W : LinkageBlueprint Γ Y κ)
    {u v : V} (huv : (u, v) ∈ W.edgeSet) :
    Path (imaginaryGraph Γ Y κ) :=
  Classical.choose (exists_edgeOwner W huv)

theorem edgeOwner_mem (W : LinkageBlueprint Γ Y κ)
    {u v : V} (huv : (u, v) ∈ W.edgeSet) :
    W.edgeOwner huv ∈ W.paths :=
  (Classical.choose_spec (exists_edgeOwner W huv)).1

theorem edgeOwner_edge (W : LinkageBlueprint Γ Y κ)
    {u v : V} (huv : (u, v) ∈ W.edgeSet) :
    (u, v) ∈ (W.edgeOwner huv).edgeSet :=
  (Classical.choose_spec (exists_edgeOwner W huv)).2

/-- Warp disjointness makes the carrier of an edge unique. -/
theorem eq_edgeOwner_of_mem_edge
    (W : LinkageBlueprint Γ Y κ) {u v : V}
    (huv : (u, v) ∈ W.edgeSet) {q : Path (imaginaryGraph Γ Y κ)}
    (hq : q ∈ W.paths) (heq : (u, v) ∈ q.edgeSet) :
    q = W.edgeOwner huv := by
  apply W.path_eq_of_mem_support hq (W.edgeOwner_mem huv)
  · exact (q.edgeSet_subset_support_prod heq).1
  · exact ((W.edgeOwner huv).edgeSet_subset_support_prod
      (W.edgeOwner_edge huv)).1

private theorem edgeOwner_insert_fresh
    (W : LinkageBlueprint Γ Y κ) {u v : V}
    (huv : (u, v) ∈ W.edgeSet) (P : FinitePath Γ.graph)
    (hfresh : W.vertexSet ∩ P.support ⊆ {u, v}) :
    (W.edgeOwner huv).support ∩
        (liftOriginal (Y := Y) (κ := κ) P).support ⊆ {u, v} := by
  intro x hx
  apply hfresh
  exact ⟨⟨W.edgeOwner huv, W.edgeOwner_mem huv, hx.1⟩,
    by simpa only [liftOriginal_support] using hx.2⟩

/-- The chosen occurrence split of the old edge carrier. -/
noncomputable def edgeOwnerSplit
    (W : LinkageBlueprint Γ Y κ) {u v : V}
    (huv : (u, v) ∈ W.edgeSet) :
    (W.edgeOwner huv).EdgeSplit u v :=
  Path.edgeSplit (W.edgeOwner huv) (W.edgeOwner_edge huv)

/-- The old edge carrier with exactly that edge replaced by the lifted real
path. -/
noncomputable def subdividedOwner
    (W : LinkageBlueprint Γ Y κ) {u v : V}
    (huv : (u, v) ∈ W.edgeSet) (P : FinitePath Γ.graph)
    (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : W.vertexSet ∩ P.support ⊆ {u, v}) :
    Path (imaginaryGraph Γ Y κ) :=
  Path.subdivide (W.edgeOwnerSplit huv)
    (liftOriginal (Y := Y) (κ := κ) P)
    (by simpa only [liftOriginal_start] using hstart)
    (by simpa only [liftOriginal_finish] using hfinish)
    (W.edgeOwner_insert_fresh huv P hfresh)

@[simp] theorem subdividedOwner_initial
    (W : LinkageBlueprint Γ Y κ) {u v : V}
    (huv : (u, v) ∈ W.edgeSet) (P : FinitePath Γ.graph)
    (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : W.vertexSet ∩ P.support ⊆ {u, v}) :
    (W.subdividedOwner huv P hstart hfinish hfresh).initial =
      (W.edgeOwner huv).initial := by
  exact Path.subdivide_initial _ _ _ _ _

@[simp] theorem subdividedOwner_terminal?
    (W : LinkageBlueprint Γ Y κ) {u v : V}
    (huv : (u, v) ∈ W.edgeSet) (P : FinitePath Γ.graph)
    (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : W.vertexSet ∩ P.support ⊆ {u, v}) :
    (W.subdividedOwner huv P hstart hfinish hfresh).terminal? =
      (W.edgeOwner huv).terminal? := by
  exact Path.subdivide_terminal? _ _ _ _ _

@[simp] theorem subdividedOwner_support
    (W : LinkageBlueprint Γ Y κ) {u v : V}
    (huv : (u, v) ∈ W.edgeSet) (P : FinitePath Γ.graph)
    (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : W.vertexSet ∩ P.support ⊆ {u, v}) :
    (W.subdividedOwner huv P hstart hfinish hfresh).support =
      (W.edgeOwner huv).support ∪ P.support := by
  rw [subdividedOwner, Path.subdivide_support, liftOriginal_support]

@[simp] theorem subdividedOwner_edgeSet
    (W : LinkageBlueprint Γ Y κ) {u v : V}
    (huv : (u, v) ∈ W.edgeSet) (P : FinitePath Γ.graph)
    (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : W.vertexSet ∩ P.support ⊆ {u, v}) :
    (W.subdividedOwner huv P hstart hfinish hfresh).edgeSet =
      ((W.edgeOwner huv).edgeSet \ {(u, v)}) ∪ P.edgeSet := by
  rw [subdividedOwner, Path.subdivide_edgeSet, liftOriginal_edgeSet]

/-- Replace the old edge carrier in the family by its subdivided version. -/
def subdividedPaths
    (W : LinkageBlueprint Γ Y κ) {u v : V}
    (huv : (u, v) ∈ W.edgeSet) (P : FinitePath Γ.graph)
    (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : W.vertexSet ∩ P.support ⊆ {u, v}) :
    Set (Path (imaginaryGraph Γ Y κ)) :=
  (W.paths \ {W.edgeOwner huv}) ∪
    {W.subdividedOwner huv P hstart hfinish hfresh}

private theorem old_other_disjoint_insert
    (W : LinkageBlueprint Γ Y κ) {u v : V}
    (huv : (u, v) ∈ W.edgeSet) (P : FinitePath Γ.graph)
    (hfresh : W.vertexSet ∩ P.support ⊆ {u, v})
    {q : Path (imaginaryGraph Γ Y κ)}
    (hq : q ∈ W.paths) (hne : q ≠ W.edgeOwner huv) :
    Disjoint q.support P.support := by
  apply Set.disjoint_left.2
  intro x hxq hxP
  have hxuv := hfresh ⟨⟨q, hq, hxq⟩, hxP⟩
  have huowner := ((W.edgeOwner huv).edgeSet_subset_support_prod
    (W.edgeOwner_edge huv)).1
  have hvowner := ((W.edgeOwner huv).edgeSet_subset_support_prod
    (W.edgeOwner_edge huv)).2
  have hqowner := W.isWarp hq (W.edgeOwner_mem huv) hne
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxuv
  rcases hxuv with rfl | rfl
  · exact Set.disjoint_left.1 hqowner hxq huowner
  · exact Set.disjoint_left.1 hqowner hxq hvowner

theorem subdividedPaths_isWarp
    (W : LinkageBlueprint Γ Y κ) {u v : V}
    (huv : (u, v) ∈ W.edgeSet) (P : FinitePath Γ.graph)
    (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : W.vertexSet ∩ P.support ⊆ {u, v}) :
    (imaginaryWeb Γ Y κ).IsWarp
      (W.subdividedPaths huv P hstart hfinish hfresh) := by
  change (W.subdividedPaths huv P hstart hfinish hfresh).PairwiseDisjoint
    Path.support
  intro q hq r hr hqr
  simp only [subdividedPaths, Set.mem_union, Set.mem_diff,
    Set.mem_singleton_iff] at hq hr
  rcases hq with hq | rfl <;> rcases hr with hr | rfl
  · exact W.isWarp hq.1 hr.1 hqr
  · change Disjoint q.support
      (W.subdividedOwner huv P hstart hfinish hfresh).support
    rw [subdividedOwner_support, Set.disjoint_union_right]
    exact ⟨W.isWarp hq.1 (W.edgeOwner_mem huv) hq.2,
      W.old_other_disjoint_insert huv P hfresh hq.1 hq.2⟩
  · change Disjoint
      (W.subdividedOwner huv P hstart hfinish hfresh).support r.support
    rw [subdividedOwner_support, Set.disjoint_union_left]
    exact ⟨W.isWarp (W.edgeOwner_mem huv) hr.1 (fun h ↦ hr.2 h.symm),
      (W.old_other_disjoint_insert huv P hfresh hr.1 hr.2).symm⟩
  · exact (hqr rfl).elim

/-- Subdivide one represented blueprint edge by a finite path in the original
graph. -/
noncomputable def subdivideEdge
    (W : LinkageBlueprint Γ Y κ) {u v : V}
    (huv : (u, v) ∈ W.edgeSet) (P : FinitePath Γ.graph)
    (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : W.vertexSet ∩ P.support ⊆ {u, v}) :
    LinkageBlueprint Γ Y κ where
  paths := W.subdividedPaths huv P hstart hfinish hfresh
  isWarp := W.subdividedPaths_isWarp huv P hstart hfinish hfresh

@[simp] theorem subdivideEdge_paths
    (W : LinkageBlueprint Γ Y κ) {u v : V}
    (huv : (u, v) ∈ W.edgeSet) (P : FinitePath Γ.graph)
    (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : W.vertexSet ∩ P.support ⊆ {u, v}) :
    (W.subdivideEdge huv P hstart hfinish hfresh).paths =
      (W.paths \ {W.edgeOwner huv}) ∪
        {W.subdividedOwner huv P hstart hfinish hfresh} :=
  rfl

@[simp] theorem subdivideEdge_vertexSet
    (W : LinkageBlueprint Γ Y κ) {u v : V}
    (huv : (u, v) ∈ W.edgeSet) (P : FinitePath Γ.graph)
    (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : W.vertexSet ∩ P.support ⊆ {u, v}) :
    (W.subdivideEdge huv P hstart hfinish hfresh).vertexSet =
      W.vertexSet ∪ P.support := by
  ext x
  constructor
  · rintro ⟨q, hq, hxq⟩
    simp only [subdivideEdge_paths, Set.mem_union, Set.mem_diff,
      Set.mem_singleton_iff] at hq
    rcases hq with hq | rfl
    · exact Or.inl ⟨q, hq.1, hxq⟩
    · have hxq' : x ∈
          (W.subdividedOwner huv P hstart hfinish hfresh :
            Path (imaginaryGraph Γ Y κ)).support := hxq
      rw [subdividedOwner_support] at hxq'
      exact hxq'.elim (fun hx ↦ Or.inl ⟨W.edgeOwner huv,
        W.edgeOwner_mem huv, hx⟩) Or.inr
  · rintro (hxW | hxP)
    · rcases hxW with ⟨q, hq, hxq⟩
      by_cases hqo : q = W.edgeOwner huv
      · subst q
        refine ⟨W.subdividedOwner huv P hstart hfinish hfresh, ?_, ?_⟩
        · exact Or.inr rfl
        · have hxnew : x ∈
              (W.subdividedOwner huv P hstart hfinish hfresh :
                Path (imaginaryGraph Γ Y κ)).support := by
              rw [subdividedOwner_support]
              exact Or.inl hxq
          exact hxnew
      · exact ⟨q, Or.inl ⟨hq, hqo⟩, hxq⟩
    · refine ⟨W.subdividedOwner huv P hstart hfinish hfresh, ?_, ?_⟩
      · exact Or.inr rfl
      · have hxnew : x ∈
            (W.subdividedOwner huv P hstart hfinish hfresh :
              Path (imaginaryGraph Γ Y κ)).support := by
            rw [subdividedOwner_support]
            exact Or.inr hxP
        exact hxnew

@[simp] theorem subdivideEdge_initialSet
    (W : LinkageBlueprint Γ Y κ) {u v : V}
    (huv : (u, v) ∈ W.edgeSet) (P : FinitePath Γ.graph)
    (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : W.vertexSet ∩ P.support ⊆ {u, v}) :
    (W.subdivideEdge huv P hstart hfinish hfresh).initialSet =
      W.initialSet := by
  ext x
  simp only [mem_initialSet, subdivideEdge_paths, Set.mem_union,
    Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨q, hq | rfl, hqx⟩
    · exact ⟨q, hq.1, hqx⟩
    · exact ⟨W.edgeOwner huv, W.edgeOwner_mem huv,
        (W.subdividedOwner_initial huv P hstart hfinish hfresh).symm.trans hqx⟩
  · rintro ⟨q, hq, hqx⟩
    by_cases hqo : q = W.edgeOwner huv
    · subst q
      exact ⟨W.subdividedOwner huv P hstart hfinish hfresh,
        Or.inr rfl,
        W.subdividedOwner_initial huv P hstart hfinish hfresh |>.trans hqx⟩
    · exact ⟨q, Or.inl ⟨hq, hqo⟩, hqx⟩

@[simp] theorem subdivideEdge_edgeSet
    (W : LinkageBlueprint Γ Y κ) {u v : V}
    (huv : (u, v) ∈ W.edgeSet) (P : FinitePath Γ.graph)
    (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : W.vertexSet ∩ P.support ⊆ {u, v}) :
    (W.subdivideEdge huv P hstart hfinish hfresh).edgeSet =
      (W.edgeSet \ {(u, v)}) ∪ P.edgeSet := by
  ext e
  simp only [LinkageBlueprint.edgeSet, Set.mem_iUnion,
    subdivideEdge_paths, Set.mem_union, Set.mem_diff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨q, hq | rfl, heq⟩
    · left
      refine ⟨⟨q, hq.1, heq⟩, ?_⟩
      intro he
      subst e
      exact hq.2 (W.eq_edgeOwner_of_mem_edge huv hq.1 heq)
    · rw [subdividedOwner_edgeSet] at heq
      rcases heq with heq | heP
      · exact Or.inl ⟨⟨W.edgeOwner huv, W.edgeOwner_mem huv,
          heq.1⟩, heq.2⟩
      · exact Or.inr heP
  · rintro (heW | heP)
    · rcases heW.1 with ⟨q, hq, heq⟩
      by_cases hqo : q = W.edgeOwner huv
      · subst q
        refine ⟨W.subdividedOwner huv P hstart hfinish hfresh,
          Or.inr rfl, ?_⟩
        rw [subdividedOwner_edgeSet]
        exact Or.inl ⟨heq, heW.2⟩
      · exact ⟨q, Or.inl ⟨hq, hqo⟩, heq⟩
    · refine ⟨W.subdividedOwner huv P hstart hfinish hfresh,
        Or.inr rfl, ?_⟩
      rw [subdividedOwner_edgeSet]
      exact Or.inr heP

/-- Every incoming edge at an old vertex is either already an old blueprint
edge, or is the final edge of the inserted real path entering `v`.  This is
the correct weaker replacement for a false global no-new-predecessors claim. -/
theorem subdivideEdge_incoming_old_vertex
    (W : LinkageBlueprint Γ Y κ) {u v : V}
    (huv : (u, v) ∈ W.edgeSet) (P : FinitePath Γ.graph)
    (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : W.vertexSet ∩ P.support ⊆ {u, v})
    {x y : V} (hx : x ∈ W.vertexSet)
    (hyx : (y, x) ∈ (W.subdivideEdge huv P hstart hfinish hfresh).edgeSet) :
    (y, x) ∈ W.edgeSet ∨ (x = v ∧ (y, v) ∈ P.edgeSet) := by
  rw [subdivideEdge_edgeSet] at hyx
  rcases hyx with hold | hP
  · exact Or.inl hold.1
  · have hxP := (P.edgeSet_subset_support_prod hP).2
    have hxuv := hfresh ⟨hx, hxP⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxuv
    rcases hxuv with hxu | hxv
    · exfalso
      apply _root_.Erdos599.Alternating.FinitePath.no_incoming_edge_at_start P y
      simpa only [hstart, hxu] using hP
    · exact Or.inr ⟨hxv, hxv ▸ hP⟩

/-- In particular subdivision introduces no incoming edge at an old root. -/
theorem subdivideEdge_incoming_initial_old
    (W : LinkageBlueprint Γ Y κ) {u v : V}
    (huv : (u, v) ∈ W.edgeSet) (P : FinitePath Γ.graph)
    (hstart : P.start = u) (hfinish : P.finish = v)
    (hfresh : W.vertexSet ∩ P.support ⊆ {u, v})
    {x y : V} (hx : x ∈ W.initialSet)
    (hyx : (y, x) ∈ (W.subdivideEdge huv P hstart hfinish hfresh).edgeSet) :
    (y, x) ∈ W.edgeSet := by
  rcases W.subdivideEdge_incoming_old_vertex huv P hstart hfinish hfresh
      (show x ∈ W.vertexSet by
        rcases hx with ⟨q, hq, hqx⟩
        exact ⟨q, hq,
          Eq.mp (congrArg (fun z ↦ z ∈ q.support) hqx)
            q.initial_mem_support⟩) hyx with hold | hnew
  · exact hold
  · rcases hx with ⟨q, hq, hqx⟩
    have hvq : v ∈ q.support :=
      Eq.mp (congrArg (fun z ↦ z ∈ q.support) (hqx.trans hnew.1))
        q.initial_mem_support
    have hqowner : q = W.edgeOwner huv :=
      W.path_eq_of_mem_support hq (W.edgeOwner_mem huv) hvq
        ((W.edgeOwner huv).edgeSet_subset_support_prod
          (W.edgeOwner_edge huv)).2
    subst q
    have hinit : (W.edgeOwner huv).initial = v := hqx.trans hnew.1
    exact False.elim ((Path.no_incoming_edge_at_initial (W.edgeOwner huv) u)
      (by simpa only [hinit] using W.edgeOwner_edge huv))

end LinkageBlueprint
end Blueprint

end Erdos599
