/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteMacroRouteRoot
import ErdosProblems.Erdos599.RunCompressor

/-!
# Tagged edge provenance for a finite macro route

The raw finite route is assembled from forward `Z` walks and reversed `Y`
walks.  We retain that construction tag at every raw edge, rather than
reconstructing a colour from the ambient edge relation (which would be
ambiguous when an edge belongs to both families).
-/

namespace Erdos599
namespace DirectedPath
namespace Walk

open Set

universe u

variable {V : Type u}


/-- Oriented edge occurrences of a walk, in traversal order. -/
def edgePairs {D : Digraph V} {a b : V} : Walk D a b → List (V × V)
  | .nil => []
  | @Walk.cons _ _ a c b h p => (a, c) :: edgePairs p

@[simp] theorem edgePairs_nil {D : Digraph V} (a : V) :
    edgePairs (.nil : Walk D a a) = [] := rfl

@[simp] theorem edgePairs_cons {D : Digraph V} {a b c : V}
    (h : D.Adj a b) (p : Walk D b c) :
    edgePairs (.cons h p) = (a, b) :: edgePairs p := rfl

@[simp] theorem edgePairs_length {D : Digraph V} {a b : V}
    (p : Walk D a b) : p.edgePairs.length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [edgePairs, ih]

/-- Edge occurrences are adjacent pairs in the ordered support. -/
theorem edgePairs_eq_zip_support_tail {D : Digraph V} {a b : V}
    (p : Walk D a b) : p.edgePairs = p.support.zip p.support.tail := by
  induction p with
  | nil => rfl
  | @cons a c b h p ih =>
      cases p with
      | nil => rfl
      | @cons c d b h' q =>
          simpa only [edgePairs, Walk.support_cons, List.tail_cons,
            List.zip_cons_cons] using congrArg (List.cons (a, c)) ih

@[simp] theorem edgePairs_append {D : Digraph V} {a b c : V}
    (p : Walk D a b) (q : Walk D b c) :
    (p.append q).edgePairs = p.edgePairs ++ q.edgePairs := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [edgePairs, ih]

@[simp] theorem edgePairs_castEndpoints {D : Digraph V} {a b c d : V}
    (ha : a = c) (hb : b = d) (p : Walk D a b) :
    (_root_.Erdos599.Alternating.Walk.castEndpoints ha hb p).edgePairs =
      p.edgePairs := by
  subst c
  subst d
  rfl

@[simp] theorem edgePairs_into {D : Digraph V} (E : V → V → Prop)
    {a b : V} (p : Walk D a b) (hsub) :
    (_root_.Erdos599.Alternating.Walk.into E p hsub).edgePairs = p.edgePairs := by
  induction p with
  | nil => rfl
  | cons h p ih =>
      simp [_root_.Erdos599.Alternating.Walk.into, edgePairs, ih]

theorem mem_edgePairs_edgeSet {D : Digraph V} {a b : V}
    (p : Walk D a b) {e : V × V} (he : e ∈ p.edgePairs) :
    e ∈ p.edgeSet := by
  induction p with
  | nil => simp [edgePairs] at he
  | @cons a c b h p ih =>
      simp only [edgePairs, List.mem_cons] at he
      rw [Walk.edgeSet_cons]
      rcases he with rfl | he
      · exact Set.mem_union_left _ (Set.mem_singleton _)
      · exact Set.mem_union_right _ (ih he)

theorem mem_edgePairs_reverseInto_swap {D : Digraph V}
    (E : V → V → Prop) {a b : V} (p : Walk D a b) (hsub)
    {e : V × V}
    (he : e ∈ (_root_.Erdos599.Alternating.Walk.reverseInto E p hsub).edgePairs) :
    (e.2, e.1) ∈ p.edgeSet := by
  induction p with
  | nil =>
      simp [_root_.Erdos599.Alternating.Walk.reverseInto, edgePairs] at he
  | @cons a c b h p ih =>
      simp only [_root_.Erdos599.Alternating.Walk.reverseInto,
        _root_.Erdos599.DirectedPath.Walk.concat,
        edgePairs_append, edgePairs] at he
      rw [Walk.edgeSet_cons]
      rcases List.mem_append.mp he with he | he
      · exact Set.mem_union_right _ (ih (fun _ _ hxy ↦ hsub (by
          rw [Walk.edgeSet_cons]
          exact Set.mem_union_right _ hxy)) he)
      · simp only [List.mem_singleton] at he
        subst e
        exact Set.mem_union_left _ (Set.mem_singleton _)

/-- Looking up edge occurrence `i` gives support vertices `i` and `i+1`. -/
theorem edgePairs_get_support {D : Digraph V} {a b : V}
    (p : Walk D a b) (i : Fin p.length) :
    p.edgePairs.get ⟨i.1, by simpa using i.2⟩ =
      (p.support.get ⟨i.1, by
          rw [_root_.Erdos599.Alternating.Walk.support_length_eq_length_add_one]
          omega⟩,
       p.support.get ⟨i.1 + 1, by
          rw [_root_.Erdos599.Alternating.Walk.support_length_eq_length_add_one]
          omega⟩) := by
  induction p with
  | nil => exact Fin.elim0 i
  | @cons a c b h p ih =>
      cases i using Fin.cases with
      | zero =>
          simp only [edgePairs, List.get_eq_getElem, List.getElem_cons_zero,
            Walk.support_cons, List.getElem_cons_succ]
          have hp : 0 < p.support.length :=
            List.length_pos_iff.mpr p.support_ne_nil
          simpa [List.getElem_zero hp, p.head_support]
      | succ i =>
          simp only [edgePairs, List.get_eq_getElem, List.getElem_cons_succ,
            Walk.support_cons]
          exact ih i

end Walk
end DirectedPath

namespace Alternating

open Set DirectedPath

variable {V : Type u} {Γ : DWeb V}

namespace FiniteMacroRoute

variable {Z Y : Set Γ.DPath} (C : FiniteMacroRoute Γ Z Y)

abbrev EdgeTag := Sum (Fin (C.lastIndex + 1)) (Fin C.lastIndex)

def edgeTagColour : C.EdgeTag → Direction
  | .inl _ => .forward
  | .inr _ => .backward

def edgeTagCarrier : C.EdgeTag → Γ.DPath
  | .inl i => (C.z i).1
  | .inr i => (C.y i).1

/-- Linear order rank of the alternating construction tags. -/
def edgeTagRank : C.EdgeTag → ℕ
  | .inl i => 2 * i.1
  | .inr i => 2 * i.1 + 1

theorem edgeTagRank_injective : Function.Injective C.edgeTagRank := by
  intro a b hab
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          simp only [edgeTagRank] at hab
          exact congrArg Sum.inl (Fin.ext (by omega))
      | inr j =>
          simp only [edgeTagRank] at hab
          exfalso
          omega
  | inr i =>
      cases b with
      | inl j =>
          simp only [edgeTagRank] at hab
          exfalso
          omega
      | inr j =>
          simp only [edgeTagRank] at hab
          exact congrArg Sum.inr (Fin.ext (by omega))

/-- Attach one construction tag to every edge occurrence of a walk. -/
def taggedWalkEdges {D : Digraph V} {a b : V}
    (tag : C.EdgeTag) (p : Walk D a b) : List (C.EdgeTag × (V × V)) :=
  p.edgePairs.map (tag, ·)

@[simp] theorem taggedWalkEdges_length {D : Digraph V} {a b : V}
    (tag : C.EdgeTag) (p : Walk D a b) :
    (C.taggedWalkEdges tag p).length = p.length := by
  simp [taggedWalkEdges]

theorem taggedWalkEdges_rank_pairwise {D : Digraph V} {a b : V}
    (tag : C.EdgeTag) (p : Walk D a b) :
    (C.taggedWalkEdges tag p).Pairwise
      (fun x y ↦ C.edgeTagRank x.1 ≤ C.edgeTagRank y.1) := by
  unfold taggedWalkEdges
  rw [List.pairwise_map]
  exact List.pairwise_of_forall (fun _ _ ↦ le_rfl)

/-- Tagged occurrences in the first `n` complete macro steps. -/
noncomputable def prefixTaggedEdges
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y) :
    (n : ℕ) → (hn : n ≤ C.lastIndex) → List (C.EdgeTag × (V × V))
  | 0, _ => []
  | n + 1, hn =>
      prefixTaggedEdges hZfin hYfin n (by omega) ++
        C.taggedWalkEdges (.inl ⟨n, by omega⟩)
          (C.zBlockWalk (Y := Y) hZfin ⟨n, by omega⟩) ++
      C.taggedWalkEdges (.inr ⟨n, by omega⟩)
          (C.yBlockWalk (Z := Z) hYfin ⟨n, by omega⟩)

@[simp] theorem stepBlockWalk_edgePairs
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (i : Fin C.lastIndex) :
    (C.stepBlockWalk hZfin hYfin i).edgePairs =
      (C.zBlockWalk (Y := Y) hZfin ⟨i.1, by omega⟩).edgePairs ++
        (C.yBlockWalk (Z := Z) hYfin i).edgePairs := by
  unfold stepBlockWalk
  simp

/-- All tagged occurrences in the finite route, including the final `Z`. -/
noncomputable def routeTaggedEdges
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y) :
    List (C.EdgeTag × (V × V)) :=
  C.prefixTaggedEdges hZfin hYfin C.lastIndex le_rfl ++
    C.taggedWalkEdges (.inl ⟨C.lastIndex, Nat.lt_succ_self _⟩)
      (C.zBlockWalk (Y := Y) hZfin
        ⟨C.lastIndex, Nat.lt_succ_self _⟩)

theorem prefixTaggedEdges_rank_lt
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y) :
    ∀ (n : ℕ) (hn : n ≤ C.lastIndex) {te},
      te ∈ C.prefixTaggedEdges hZfin hYfin n hn →
        C.edgeTagRank te.1 < 2 * n := by
  intro n
  induction n with
  | zero => simp [prefixTaggedEdges]
  | succ n ih =>
      intro hn te hte
      simp only [prefixTaggedEdges, List.mem_append] at hte
      rcases hte with hleft | hy
      · rcases hleft with hpre | hz
        · exact (ih (by omega) hpre).trans (by omega)
        · rcases List.mem_map.mp hz with ⟨e, he, rfl⟩
          change 2 * n < 2 * (n + 1)
          omega
      · rcases List.mem_map.mp hy with ⟨e, he, rfl⟩
        change 2 * n + 1 < 2 * (n + 1)
        omega

theorem prefixTaggedEdges_rank_pairwise
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y) :
    ∀ (n : ℕ) (hn : n ≤ C.lastIndex),
      (C.prefixTaggedEdges hZfin hYfin n hn).Pairwise
        (fun x y ↦ C.edgeTagRank x.1 ≤ C.edgeTagRank y.1) := by
  intro n
  induction n with
  | zero => intro hn; simp [prefixTaggedEdges]
  | succ n ih =>
      intro hn
      simp only [prefixTaggedEdges]
      rw [List.pairwise_append, List.pairwise_append]
      refine ⟨⟨ih (by omega),
        C.taggedWalkEdges_rank_pairwise _ _, ?_⟩,
        C.taggedWalkEdges_rank_pairwise _ _, ?_⟩
      · intro a ha b hb
        have ha' := C.prefixTaggedEdges_rank_lt hZfin hYfin n (by omega) ha
        rcases List.mem_map.mp hb with ⟨e, he, rfl⟩
        change C.edgeTagRank a.1 ≤ 2 * n
        exact Nat.le_of_lt ha'
      · intro a ha b hb
        rcases List.mem_append.mp ha with ha | ha
        · have ha' := C.prefixTaggedEdges_rank_lt hZfin hYfin n (by omega) ha
          rcases List.mem_map.mp hb with ⟨e, he, rfl⟩
          change C.edgeTagRank a.1 ≤ 2 * n + 1
          exact (Nat.le_of_lt ha').trans (by omega)
        · rcases List.mem_map.mp ha with ⟨e, he, rfl⟩
          rcases List.mem_map.mp hb with ⟨f, hf, rfl⟩
          simp [edgeTagRank]

theorem routeTaggedEdges_rank_pairwise
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y) :
    (C.routeTaggedEdges hZfin hYfin).Pairwise
      (fun x y ↦ C.edgeTagRank x.1 ≤ C.edgeTagRank y.1) := by
  unfold routeTaggedEdges
  rw [List.pairwise_append]
  refine ⟨C.prefixTaggedEdges_rank_pairwise hZfin hYfin _ le_rfl,
    C.taggedWalkEdges_rank_pairwise _ _, ?_⟩
  intro a ha b hb
  have ha' := C.prefixTaggedEdges_rank_lt hZfin hYfin
    C.lastIndex le_rfl ha
  rcases List.mem_map.mp hb with ⟨e, he, rfl⟩
  change C.edgeTagRank a.1 ≤ 2 * C.lastIndex
  exact Nat.le_of_lt ha'

theorem tagged_z_mem_prefixTaggedEdges
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    {i n : ℕ} (hi : i < n) (hn : n ≤ C.lastIndex)
    {te : C.EdgeTag × (V × V)}
    (hte : te ∈ C.taggedWalkEdges (.inl ⟨i, by omega⟩)
      (C.zBlockWalk (Y := Y) hZfin ⟨i, by omega⟩)) :
    te ∈ C.prefixTaggedEdges hZfin hYfin n hn := by
  induction n with
  | zero => omega
  | succ n ih =>
      simp only [prefixTaggedEdges, List.mem_append]
      by_cases hin : i < n
      · exact Or.inl (Or.inl (ih hin (by omega) hte))
      · have hieq : i = n := by omega
        subst i
        exact Or.inl (Or.inr hte)

theorem tagged_z_mem_routeTaggedEdges
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    {i : ℕ} (hi : i ≤ C.lastIndex)
    {te : C.EdgeTag × (V × V)}
    (hte : te ∈ C.taggedWalkEdges (.inl ⟨i, by omega⟩)
      (C.zBlockWalk (Y := Y) hZfin ⟨i, by omega⟩)) :
    te ∈ C.routeTaggedEdges hZfin hYfin := by
  unfold routeTaggedEdges
  rw [List.mem_append]
  by_cases hilast : i = C.lastIndex
  · subst i
    exact Or.inr hte
  · exact Or.inl (C.tagged_z_mem_prefixTaggedEdges hZfin hYfin
      (lt_of_le_of_ne hi hilast) le_rfl hte)

theorem routeTaggedEdges_rank_le
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    {te : C.EdgeTag × (V × V)}
    (hte : te ∈ C.routeTaggedEdges hZfin hYfin) :
    C.edgeTagRank te.1 ≤ 2 * C.lastIndex := by
  unfold routeTaggedEdges at hte
  rw [List.mem_append] at hte
  rcases hte with hpre | hfinal
  · exact Nat.le_of_lt (C.prefixTaggedEdges_rank_lt hZfin hYfin
      C.lastIndex le_rfl hpre)
  · rcases List.mem_map.mp hfinal with ⟨e, he, rfl⟩
    exact le_rfl

@[simp] theorem prefixTaggedEdges_map_snd
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y) :
    ∀ (n : ℕ) (hn : n ≤ C.lastIndex),
      (C.prefixTaggedEdges hZfin hYfin n hn).map Prod.snd =
        (C.prefixWalk hZfin hYfin n hn).edgePairs := by
  intro n
  induction n with
  | zero => intro hn; rfl
  | succ n ih =>
      intro hn
      simp only [prefixTaggedEdges, List.map_append, taggedWalkEdges,
        List.map_map, Function.comp_apply, prefixWalk, Walk.edgePairs_append,
        Walk.edgePairs_castEndpoints, ih, C.stepBlockWalk_edgePairs]
      simp [Function.comp_def, List.append_assoc]

@[simp] theorem routeTaggedEdges_map_snd
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y) :
    (C.routeTaggedEdges hZfin hYfin).map Prod.snd =
      (C.routeWalk hZfin hYfin).edgePairs := by
  unfold routeTaggedEdges routeWalk
  rw [List.map_append, C.prefixTaggedEdges_map_snd,
    Walk.edgePairs_append, Walk.edgePairs_castEndpoints]
  simp [taggedWalkEdges]

@[simp] theorem routeTaggedEdges_length
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y) :
    (C.routeTaggedEdges hZfin hYfin).length =
      (C.routeWalk hZfin hYfin).length := by
  have h := congrArg List.length
    (C.routeTaggedEdges_map_snd hZfin hYfin)
  simpa only [List.length_map, Walk.edgePairs_length] using h

/-- The canonical construction tag of raw edge `i`. -/
noncomputable def routeEdgeTag
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (i : Fin (C.routeWalk hZfin hYfin).length) : C.EdgeTag :=
  (C.routeTaggedEdges hZfin hYfin).get
    ⟨i.1, by simpa using i.2⟩ |>.1

noncomputable def routeColour
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (i : Fin (C.routeWalk hZfin hYfin).length) : Direction :=
  C.edgeTagColour (C.routeEdgeTag hZfin hYfin i)

/-- A tagged raw edge has the orientation asserted by its construction tag. -/
def EdgeTag.Valid (tag : C.EdgeTag) (e : V × V) : Prop :=
  match tag with
  | .inl i => e ∈ (C.z i).1.edgeSet
  | .inr i => (e.2, e.1) ∈ (C.y i).1.edgeSet

theorem tagged_z_valid
    (hZfin : Γ.HasFiniteCharacter Z) (i : Fin (C.lastIndex + 1))
    {te : C.EdgeTag × (V × V)}
    (hte : te ∈ C.taggedWalkEdges (.inl i)
      (C.zBlockWalk (Y := Y) hZfin i)) : te.1.Valid C te.2 := by
  rcases List.mem_map.mp hte with ⟨e, he, rfl⟩
  change e ∈ (C.z i).1.edgeSet
  rw [C.z_eq_zFinite hZfin i]
  have hepairs : (C.zBlockWalk (Y := Y) hZfin i).edgePairs =
      (C.zFinite hZfin i).walk.edgePairs := by
    rw [Walk.edgePairs_eq_zip_support_tail,
      Walk.edgePairs_eq_zip_support_tail, C.support_zBlockWalk]
  rw [hepairs] at he
  exact Walk.mem_edgePairs_edgeSet _ he

theorem tagged_y_valid
    (hYfin : Γ.HasFiniteCharacter Y) (i : Fin C.lastIndex)
    {te : C.EdgeTag × (V × V)}
    (hte : te ∈ C.taggedWalkEdges (.inr i)
      (C.yBlockWalk (Z := Z) hYfin i)) : te.1.Valid C te.2 := by
  rcases List.mem_map.mp hte with ⟨e, he, rfl⟩
  change (e.2, e.1) ∈ (C.y i).1.edgeSet
  rw [C.y_eq_yFinite hYfin i]
  exact Walk.mem_edgePairs_reverseInto_swap _ _ _ he

theorem prefixTaggedEdges_valid
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y) :
    ∀ (n : ℕ) (hn : n ≤ C.lastIndex) {te},
      te ∈ C.prefixTaggedEdges hZfin hYfin n hn → te.1.Valid C te.2 := by
  intro n
  induction n with
  | zero => simp [prefixTaggedEdges]
  | succ n ih =>
      intro hn te hte
      simp only [prefixTaggedEdges, List.mem_append] at hte
      rcases hte with hleft | hy
      · rcases hleft with hpre | hz
        · exact ih (by omega) hpre
        · exact C.tagged_z_valid hZfin ⟨n, by omega⟩ hz
      · exact C.tagged_y_valid hYfin ⟨n, by omega⟩ hy

theorem routeTaggedEdges_valid
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    {te : C.EdgeTag × (V × V)}
    (hte : te ∈ C.routeTaggedEdges hZfin hYfin) : te.1.Valid C te.2 := by
  unfold routeTaggedEdges at hte
  rw [List.mem_append] at hte
  rcases hte with hpre | hz
  · exact C.prefixTaggedEdges_valid hZfin hYfin _ le_rfl hpre
  · exact C.tagged_z_valid hZfin ⟨C.lastIndex, Nat.lt_succ_self _⟩ hz

theorem routeTaggedEdges_get_pair
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (i : Fin (C.routeWalk hZfin hYfin).length) :
    ((C.routeTaggedEdges hZfin hYfin).get
      ⟨i.1, by simpa using i.2⟩).2 =
      (C.routeRawVertex hZfin hYfin ⟨i.1, by omega⟩,
       C.routeRawVertex hZfin hYfin ⟨i.1 + 1, by omega⟩) := by
  have hmap :
      ((C.routeTaggedEdges hZfin hYfin).map Prod.snd)[i.1]'(by
        rw [List.length_map, C.routeTaggedEdges_length hZfin hYfin]
        exact i.2) =
        ((C.routeTaggedEdges hZfin hYfin)[i.1]'(by
          rw [C.routeTaggedEdges_length hZfin hYfin]
          exact i.2)).2 := by
    exact List.getElem_map Prod.snd
  have hget := List.getElem_of_eq
    (C.routeTaggedEdges_map_snd hZfin hYfin)
    (i := i.1) (by
      rw [List.length_map, C.routeTaggedEdges_length hZfin hYfin]
      exact i.2)
  have hedge := Walk.edgePairs_get_support
    (C.routeWalk hZfin hYfin) i
  rw [List.get_eq_getElem] at hedge
  rw [List.get_eq_getElem]
  exact hmap.symm.trans (hget.trans hedge)

/-- Forward-tagged raw edges belong to their selected `Z` carrier. -/
theorem routeEdge_mem_forward
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (i : Fin (C.routeWalk hZfin hYfin).length)
    (hi : C.routeColour hZfin hYfin i = .forward) :
    (C.routeRawVertex hZfin hYfin ⟨i.1, by omega⟩,
      C.routeRawVertex hZfin hYfin ⟨i.1 + 1, by omega⟩) ∈
        (C.edgeTagCarrier (C.routeEdgeTag hZfin hYfin i)).edgeSet := by
  let ti : Fin (C.routeTaggedEdges hZfin hYfin).length :=
    ⟨i.1, by simpa using i.2⟩
  have hv := C.routeTaggedEdges_valid hZfin hYfin
    (List.get_mem (C.routeTaggedEdges hZfin hYfin) ti)
  have hp := C.routeTaggedEdges_get_pair hZfin hYfin i
  have hp' : ((C.routeTaggedEdges hZfin hYfin).get ti).2 =
      (C.routeRawVertex hZfin hYfin ⟨i.1, by omega⟩,
       C.routeRawVertex hZfin hYfin ⟨i.1 + 1, by omega⟩) := by
    simpa [ti] using hp
  change C.edgeTagColour ((C.routeTaggedEdges hZfin hYfin).get ti).1 =
      .forward at hi
  change _ ∈ (C.edgeTagCarrier
    ((C.routeTaggedEdges hZfin hYfin).get ti).1).edgeSet
  change ((C.routeTaggedEdges hZfin hYfin).get ti).1.Valid C
    ((C.routeTaggedEdges hZfin hYfin).get ti).2 at hv
  cases ht : ((C.routeTaggedEdges hZfin hYfin).get ti).1 with
  | inl j =>
      rw [ht] at hv hi
      change ((C.routeTaggedEdges hZfin hYfin).get ti).2 ∈
        (C.z j).1.edgeSet at hv
      change _ ∈ (C.z j).1.edgeSet
      rw [hp'] at hv
      exact hv
  | inr j =>
      rw [ht] at hi
      simp [edgeTagColour] at hi

/-- Backward-tagged raw edges, reversed, belong to their selected `Y` carrier. -/
theorem routeEdge_mem_backward
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (i : Fin (C.routeWalk hZfin hYfin).length)
    (hi : C.routeColour hZfin hYfin i = .backward) :
    (C.routeRawVertex hZfin hYfin ⟨i.1 + 1, by omega⟩,
      C.routeRawVertex hZfin hYfin ⟨i.1, by omega⟩) ∈
        (C.edgeTagCarrier (C.routeEdgeTag hZfin hYfin i)).edgeSet := by
  let ti : Fin (C.routeTaggedEdges hZfin hYfin).length :=
    ⟨i.1, by simpa using i.2⟩
  have hv := C.routeTaggedEdges_valid hZfin hYfin
    (List.get_mem (C.routeTaggedEdges hZfin hYfin) ti)
  have hp := C.routeTaggedEdges_get_pair hZfin hYfin i
  have hp' : ((C.routeTaggedEdges hZfin hYfin).get ti).2 =
      (C.routeRawVertex hZfin hYfin ⟨i.1, by omega⟩,
       C.routeRawVertex hZfin hYfin ⟨i.1 + 1, by omega⟩) := by
    simpa [ti] using hp
  change C.edgeTagColour ((C.routeTaggedEdges hZfin hYfin).get ti).1 =
      .backward at hi
  change _ ∈ (C.edgeTagCarrier
    ((C.routeTaggedEdges hZfin hYfin).get ti).1).edgeSet
  change ((C.routeTaggedEdges hZfin hYfin).get ti).1.Valid C
    ((C.routeTaggedEdges hZfin hYfin).get ti).2 at hv
  cases ht : ((C.routeTaggedEdges hZfin hYfin).get ti).1 with
  | inl j =>
      rw [ht] at hi
      simp [edgeTagColour] at hi
  | inr j =>
      rw [ht] at hv hi
      change ((((C.routeTaggedEdges hZfin hYfin).get ti).2).2,
        (((C.routeTaggedEdges hZfin hYfin).get ti).2).1) ∈
          (C.y j).1.edgeSet at hv
      change _ ∈ (C.y j).1.edgeSet
      rw [hp'] at hv
      exact hv

theorem edgeTagCarrier_mem_forward (a : C.EdgeTag)
    (ha : C.edgeTagColour a = .forward) : C.edgeTagCarrier a ∈ Z := by
  cases a with
  | inl i => exact (C.z i).2
  | inr i => simp [edgeTagColour] at ha

theorem edgeTagCarrier_mem_backward (a : C.EdgeTag)
    (ha : C.edgeTagColour a = .backward) : C.edgeTagCarrier a ∈ Y := by
  cases a with
  | inl i => simp [edgeTagColour] at ha
  | inr i => exact (C.y i).2

theorem edgeTagCarrier_injective_on_colour
    (hZ : Γ.IsWarp Z) (hY : Γ.IsWarp Y)
    (hroot : (C.z ⟨0, Nat.zero_lt_succ _⟩).1.initial ∉ Γ.vertexSet Y)
    {a b : C.EdgeTag}
    (hcolour : C.edgeTagColour a = C.edgeTagColour b)
    (hcarrier : C.edgeTagCarrier a = C.edgeTagCarrier b) : a = b := by
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          have hij : i = j := C.z_injective hZ hY hroot
            (Subtype.ext hcarrier)
          simpa [hij]
      | inr j => simp [edgeTagColour] at hcolour
  | inr i =>
      cases b with
      | inl j => simp [edgeTagColour] at hcolour
      | inr j =>
          have hij : i = j := C.y_injective hZ hY hroot
            (Subtype.ext hcarrier)
          simpa [hij]

theorem routeEdgeTag_rank_mono
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    {i j : Fin (C.routeWalk hZfin hYfin).length} (hij : i ≤ j) :
    C.edgeTagRank (C.routeEdgeTag hZfin hYfin i) ≤
      C.edgeTagRank (C.routeEdgeTag hZfin hYfin j) := by
  let ti : Fin (C.routeTaggedEdges hZfin hYfin).length :=
    ⟨i.1, by simpa using i.2⟩
  let tj : Fin (C.routeTaggedEdges hZfin hYfin).length :=
    ⟨j.1, by simpa using j.2⟩
  change C.edgeTagRank ((C.routeTaggedEdges hZfin hYfin).get ti).1 ≤
    C.edgeTagRank ((C.routeTaggedEdges hZfin hYfin).get tj).1
  by_cases heq : i = j
  · subst j
    exact le_rfl
  · exact List.pairwise_iff_get.mp
      (C.routeTaggedEdges_rank_pairwise hZfin hYfin) ti tj
      (by exact Fin.mk_lt_mk.mpr (lt_of_le_of_ne hij (fun h ↦ heq (Fin.ext h))))

/-- Construction tags remain convex after selecting any increasing raw
subsequence, in particular after chronological loop erasure. -/
theorem routeEdgeTag_convex
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    {i j k : Fin (C.routeWalk hZfin hYfin).length}
    (hij : i ≤ j) (hjk : j ≤ k)
    (hik : C.routeEdgeTag hZfin hYfin i =
      C.routeEdgeTag hZfin hYfin k) :
    C.routeEdgeTag hZfin hYfin j =
      C.routeEdgeTag hZfin hYfin i := by
  apply C.edgeTagRank_injective
  have h₁ := C.routeEdgeTag_rank_mono hZfin hYfin hij
  have h₂ := C.routeEdgeTag_rank_mono hZfin hYfin hjk
  have hEq := congrArg C.edgeTagRank hik
  omega

theorem zBlockWalk_length_eq
    (hZfin : Γ.HasFiniteCharacter Z) (i : Fin (C.lastIndex + 1)) :
    (C.zBlockWalk (Y := Y) hZfin i).length =
      (C.zFinite hZfin i).walk.length := by
  have h := congrArg List.length (C.support_zBlockWalk hZfin i)
  rw [Walk.support_length_eq_length_add_one,
    Walk.support_length_eq_length_add_one] at h
  omega

theorem routeEdgeTag_first_forward
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hzpos : 0 < (C.zBlockWalk (Y := Y) hZfin
      ⟨0, Nat.zero_lt_succ _⟩).length)
    (i : Fin (C.routeWalk hZfin hYfin).length) (hi : i.1 = 0) :
    C.routeEdgeTag hZfin hYfin i =
      .inl ⟨0, Nat.zero_lt_succ _⟩ := by
  let ztag : C.EdgeTag := .inl ⟨0, Nat.zero_lt_succ _⟩
  let zw := C.zBlockWalk (Y := Y) hZfin ⟨0, Nat.zero_lt_succ _⟩
  have hzne : zw.edgePairs ≠ [] := by
    rw [List.ne_nil_iff_length_pos, Walk.edgePairs_length]
    exact hzpos
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil zw.edgePairs hzne
  have htagged : (ztag, e) ∈ C.taggedWalkEdges ztag zw :=
    List.mem_map.mpr ⟨e, he, rfl⟩
  have hroute : (ztag, e) ∈ C.routeTaggedEdges hZfin hYfin := by
    exact C.tagged_z_mem_routeTaggedEdges hZfin hYfin
      (i := 0) (Nat.zero_le _) htagged
  obtain ⟨t, ht⟩ := List.get_of_mem hroute
  let ti : Fin (C.routeTaggedEdges hZfin hYfin).length :=
    ⟨i.1, by simpa using i.2⟩
  have htTag : ((C.routeTaggedEdges hZfin hYfin).get t).1 = ztag :=
    congrArg Prod.fst ht
  have hRank : C.edgeTagRank
      ((C.routeTaggedEdges hZfin hYfin).get ti).1 ≤ 0 := by
    by_cases hit : ti = t
    · rw [hit, htTag]
      rfl
    · have hlt : ti < t := by
        apply Fin.mk_lt_mk.mpr
        change i.1 < t.1
        rw [hi]
        exact Nat.pos_of_ne_zero (fun ht0 ↦ hit (Fin.ext (by
          dsimp only [ti]
          omega)))
      have hrel := List.Pairwise.rel_get_of_lt
        (C.routeTaggedEdges_rank_pairwise hZfin hYfin) hlt
      rw [htTag] at hrel
      exact hrel
  apply C.edgeTagRank_injective
  change C.edgeTagRank ((C.routeTaggedEdges hZfin hYfin).get ti).1 = 0
  exact Nat.eq_zero_of_le_zero hRank

theorem routeEdgeTag_last_forward
    (hZfin : Γ.HasFiniteCharacter Z) (hYfin : Γ.HasFiniteCharacter Y)
    (hzpos : 0 < (C.zBlockWalk (Y := Y) hZfin
      ⟨C.lastIndex, Nat.lt_succ_self _⟩).length)
    (i : Fin (C.routeWalk hZfin hYfin).length)
    (hi : i.1 + 1 = (C.routeWalk hZfin hYfin).length) :
    C.routeEdgeTag hZfin hYfin i =
      .inl ⟨C.lastIndex, Nat.lt_succ_self _⟩ := by
  let ztag : C.EdgeTag :=
    .inl ⟨C.lastIndex, Nat.lt_succ_self _⟩
  let zw := C.zBlockWalk (Y := Y) hZfin
    ⟨C.lastIndex, Nat.lt_succ_self _⟩
  have hzne : zw.edgePairs ≠ [] := by
    rw [List.ne_nil_iff_length_pos, Walk.edgePairs_length]
    exact hzpos
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil zw.edgePairs hzne
  have htagged : (ztag, e) ∈ C.taggedWalkEdges ztag zw :=
    List.mem_map.mpr ⟨e, he, rfl⟩
  have hroute : (ztag, e) ∈ C.routeTaggedEdges hZfin hYfin := by
    exact C.tagged_z_mem_routeTaggedEdges hZfin hYfin
      (i := C.lastIndex) le_rfl htagged
  obtain ⟨t, ht⟩ := List.get_of_mem hroute
  let ti : Fin (C.routeTaggedEdges hZfin hYfin).length :=
    ⟨i.1, by simpa using i.2⟩
  have htTag : ((C.routeTaggedEdges hZfin hYfin).get t).1 = ztag :=
    congrArg Prod.fst ht
  have hLower : 2 * C.lastIndex ≤ C.edgeTagRank
      ((C.routeTaggedEdges hZfin hYfin).get ti).1 := by
    by_cases hit : t = ti
    · rw [← hit, htTag]
      exact le_rfl
    · have hlt : t < ti := by
        apply Fin.mk_lt_mk.mpr
        have htlt : t.1 < (C.routeTaggedEdges hZfin hYfin).length := t.2
        have hlen : (C.routeTaggedEdges hZfin hYfin).length = i.1 + 1 :=
          (C.routeTaggedEdges_length hZfin hYfin).trans hi.symm
        have htlei : t.1 ≤ i.1 := by omega
        exact lt_of_le_of_ne htlei (fun h ↦ hit (Fin.ext h))
      have hrel := List.Pairwise.rel_get_of_lt
        (C.routeTaggedEdges_rank_pairwise hZfin hYfin) hlt
      rw [htTag] at hrel
      exact hrel
  have hUpper : C.edgeTagRank
      ((C.routeTaggedEdges hZfin hYfin).get ti).1 ≤
      2 * C.lastIndex := C.routeTaggedEdges_rank_le hZfin hYfin
        (List.get_mem _ ti)
  apply C.edgeTagRank_injective
  change C.edgeTagRank ((C.routeTaggedEdges hZfin hYfin).get ti).1 =
    2 * C.lastIndex
  exact Nat.le_antisymm hUpper hLower

end FiniteMacroRoute

end Alternating
end Erdos599
