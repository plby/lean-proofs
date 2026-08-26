/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos556.TwoLinkage
import ErdosProblems.Erdos556.CycleArcs
import Mathlib.Tactic

/-!
# The two-path case of vertex Menger for Erdős Problem 58

This file proves the finite `k = 2` consequence of vertex Menger needed in
Gyárfás's proof.  The proof first establishes Whitney's elementary
characterization: in a finite vertex-two-connected graph, every two vertices
belong to a common simple cycle.  It then applies this result after adjoining
two fresh vertices attached to the two endpoint sets.  Removing those fresh
vertices from the two complementary arcs of the resulting cycle gives two
fully vertex-disjoint paths between the endpoint sets.

The endpoint sets must each contain at least two vertices.  This hypothesis is
sharp for the repository's `TwoLinkage`, whose two paths have disjoint *full*
supports.
-/

namespace Erdos556

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-- Two vertices occur on one genuine simple cycle. -/
def OnCommonCycle (G : SimpleGraph V) (x y : V) : Prop :=
  ∃ (z : V) (c : G.Walk z z), c.IsCycle ∧ x ∈ c.support ∧ y ∈ c.support

/-! ## Adjoining two endpoint vertices -/

/-- Original vertices together with two fresh endpoint vertices.  `false` is
the left endpoint and `true` the right endpoint. -/
abbrev LinkAugment (V : Type u) := Sum V Bool

/-- Add a fresh vertex adjacent precisely to `A` and a second fresh vertex
adjacent precisely to `B`. -/
def linkAugment (G : SimpleGraph V) (A B : Set V) :
    SimpleGraph (LinkAugment V) where
  Adj s t :=
    match s, t with
    | Sum.inl x, Sum.inl y => G.Adj x y
    | Sum.inl x, Sum.inr false => x ∈ A
    | Sum.inr false, Sum.inl x => x ∈ A
    | Sum.inl x, Sum.inr true => x ∈ B
    | Sum.inr true, Sum.inl x => x ∈ B
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨by
    intro s t h
    cases s with
    | inl x =>
        cases t with
        | inl y => exact h.symm
        | inr i => cases i <;> exact h
    | inr i =>
        cases t with
        | inl x => cases i <;> exact h
        | inr k =>
            cases i <;> cases k <;> exact False.elim h⟩
  loopless := ⟨by
    intro s h
    cases s with
    | inl x => exact h.ne rfl
    | inr i => cases i <;> exact False.elim h⟩

@[simp] theorem linkAugment_adj_inl_inl {A B : Set V} {x y : V} :
    (linkAugment G A B).Adj (Sum.inl x) (Sum.inl y) ↔ G.Adj x y :=
  Iff.rfl

@[simp] theorem linkAugment_adj_inl_left {A B : Set V} {x : V} :
    (linkAugment G A B).Adj (Sum.inl x) (Sum.inr false) ↔ x ∈ A :=
  Iff.rfl

@[simp] theorem linkAugment_adj_left_inl {A B : Set V} {x : V} :
    (linkAugment G A B).Adj (Sum.inr false) (Sum.inl x) ↔ x ∈ A :=
  Iff.rfl

@[simp] theorem linkAugment_adj_inl_right {A B : Set V} {x : V} :
    (linkAugment G A B).Adj (Sum.inl x) (Sum.inr true) ↔ x ∈ B :=
  Iff.rfl

@[simp] theorem linkAugment_adj_right_inl {A B : Set V} {x : V} :
    (linkAugment G A B).Adj (Sum.inr true) (Sum.inl x) ↔ x ∈ B :=
  Iff.rfl

/-- The canonical embedding of the old graph into its endpoint augmentation. -/
def linkAugmentEmbedding (G : SimpleGraph V) (A B : Set V) :
    G ↪g linkAugment G A B where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Iff.rfl

namespace TwoConnected

/-- Every edge of a finite vertex-two-connected graph belongs to a simple
cycle.  The proof chooses a second neighbor of one endpoint by finding a path
in the graph with the other endpoint deleted. -/
theorem exists_cycle_through_edge (hG : TwoConnected G) {x y : V}
    (hxy : G.Adj x y) :
    ∃ c : G.Walk x x, c.IsCycle ∧ y ∈ c.support := by
  obtain ⟨r, s, hry, hsy, hrs⟩ := hG.exists_two_ne y
  let t : V := if r = x then s else r
  have hty : t ≠ y := by
    dsimp [t]
    split <;> assumption
  have htx : t ≠ x := by
    dsimp [t]
    split_ifs with hrx
    · exact fun hsx ↦ hrs (hrx.trans hsx.symm)
    · exact hrx
  obtain ⟨p, hp, hpy⟩ := hG.exists_path_avoiding y hxy.ne hty
  have hp_nonNil : ¬ p.Nil := by
    exact Walk.not_nil_of_ne htx.symm
  let w : V := p.snd
  have hxw : G.Adj x w := p.adj_snd hp_nonNil
  have hwy : w ≠ y := by
    intro h
    exact hpy (h ▸ List.mem_of_mem_tail (p.snd_mem_tail_support hp_nonNil))
  obtain ⟨q₀, hq₀, hq₀x⟩ :=
    hG.exists_path_avoiding x hxy.ne.symm hxw.ne.symm
  let q : G.Walk y x := q₀.concat hxw.symm
  have hq : q.IsPath := hq₀.concat hq₀x hxw.symm
  have hedge : s(x, y) ∉ q.edges := by
    intro he
    have he' : s(y, x) ∈ q.edges := by simpa [Sym2.eq_swap] using he
    have hlen : q.length = 1 := hq.length_eq_one_of_mem_edges he'
    have hq₀len : q₀.length = 0 := by
      have : q.length = q₀.length + 1 := by simp [q]
      omega
    exact hwy (q₀.eq_of_length_eq_zero hq₀len).symm
  let c : G.Walk x x := Walk.cons hxy q
  have hc : c.IsCycle := (Walk.cons_isCycle_iff q hxy).2 ⟨hq, hedge⟩
  refine ⟨c, hc, ?_⟩
  simp [c]

/-- The two arcs between distinct vertices of a cycle.  One of them contains
any specified third vertex of the cycle. -/
private theorem exists_cycle_arc_through
    {z : V} {c : G.Walk z z} (hc : c.IsCycle)
    {x w t : V} (hx : x ∈ c.support) (hw : w ∈ c.support)
    (ht : t ∈ c.support) (hxw : x ≠ w) :
    ∃ r : G.Walk x w,
      r.IsPath ∧ t ∈ r.support ∧ (∀ v ∈ r.support, v ∈ c.support) := by
  let c' : G.Walk x x := c.rotate x hx
  have hc' : c'.IsCycle := hc.rotate hx
  have hw' : w ∈ c'.support := by
    simpa [c'] using (c.mem_support_rotate_iff x hx).2 hw
  have ht' : t ∈ c'.support := by
    simpa [c'] using (c.mem_support_rotate_iff x hx).2 ht
  let r₁ : G.Walk x w := c'.takeUntil w hw'
  let d : G.Walk w x := c'.dropUntil w hw'
  let r₂ : G.Walk x w := d.reverse
  have hr₁ : r₁.IsPath := hc'.isPath_takeUntil hw'
  have hr₂ : r₂.IsPath := by
    apply Walk.isPath_reverse_iff d |>.mpr
    have hcycleappend : (r₁.append d).IsCycle := by
      simpa [r₁, d] using hc'
    exact Walk.IsCycle.isPath_of_append_right (Walk.not_nil_of_ne hxw) hcycleappend
  have hr₁_sub : ∀ v ∈ r₁.support, v ∈ c.support := by
    intro v hv
    have hv' : v ∈ c'.support := c'.support_takeUntil_subset_support hw' hv
    exact (c.mem_support_rotate_iff x hx).1 (by simpa [c'] using hv')
  have hr₂_sub : ∀ v ∈ r₂.support, v ∈ c.support := by
    intro v hv
    have hvd : v ∈ d.support := by simpa [r₂] using hv
    have hv' : v ∈ c'.support := c'.support_dropUntil_subset_support hw' hvd
    exact (c.mem_support_rotate_iff x hx).1 (by simpa [c'] using hv')
  by_cases htr₁ : t ∈ r₁.support
  · exact ⟨r₁, hr₁, htr₁, hr₁_sub⟩
  · refine ⟨r₂, hr₂, ?_, hr₂_sub⟩
    have htappend : t ∈ (r₁.append d).support := by
      simpa [r₁, d, Walk.take_spec c' hw'] using ht'
    rw [Walk.mem_support_append_iff] at htappend
    have htd : t ∈ d.support := htappend.resolve_left htr₁
    simpa [r₂] using htd

/-- Extend a common cycle through `root` and `x` across an edge `x-y`.

The old cycle is avoided at `x`: in `G-x`, take a path from `y` to `root`
and stop at its first hit `w` on the old cycle.  The `x-w` arc of the old
cycle which contains `root`, together with the new path and the edge `x-y`,
is the required cycle. -/
private theorem onCommonCycle_of_adj_of_avoiding_path
    {root x y : V} (hxy : G.Adj x y) (hcycle : OnCommonCycle G root x)
    (p : G.Walk y root) (hp : p.IsPath) (hpx : x ∉ p.support) :
    OnCommonCycle G root y := by
  rcases hcycle with ⟨z, c, hc, hroot, hx⟩
  by_cases hyc : y ∈ c.support
  · exact ⟨z, c, hc, hroot, hyc⟩
  let Cset : Finset V := c.support.toFinset
  have hmeet : {v ∈ Cset | v ∈ p.support}.Nonempty := by
    refine ⟨root, ?_⟩
    simp [Cset, hroot]
  obtain ⟨w, hwC, hwp, hfirst⟩ :=
    p.exists_mem_support_forall_mem_support_imp_eq Cset hmeet
  have hwc : w ∈ c.support := by simpa [Cset] using hwC
  have hxw : x ≠ w := by
    intro h
    exact hpx (h ▸ hwp)
  let q : G.Walk y w := p.takeUntil w hwp
  have hq : q.IsPath := hp.takeUntil hwp
  obtain ⟨r, hr, hrootr, hrsub⟩ :=
    exists_cycle_arc_through hc hx hwc hroot hxw
  let body : G.Walk x y := r.append q.reverse
  have hdisj : r.support.Disjoint q.reverse.support.tail := by
    rw [List.disjoint_left]
    intro v hvr hvqtail
    have hvc : v ∈ c.support := hrsub v hvr
    have hvq : v ∈ q.support := by
      have : v ∈ q.reverse.support := List.mem_of_mem_tail hvqtail
      simpa using this
    have hvw : v = w := hfirst v (by simpa [Cset] using hvc) hvq
    subst v
    have hne := hq.reverse.support_nodup.rel_head_tail hvqtail
    exact hne (by simp)
  have hbody : body.IsPath := by
    simp only [Walk.isPath_def, body, Walk.support_append]
    exact List.Nodup.append hr.support_nodup hq.reverse.support_nodup.tail hdisj
  have hedge : s(y, x) ∉ body.edges := by
    intro he
    simp only [body, Walk.edges_append, List.mem_append] at he
    rcases he with her | heq
    · have hyv : y ∈ r.support := r.fst_mem_support_of_mem_edges her
      exact hyc (hrsub y hyv)
    · have hex : s(x, y) ∈ q.edges := by
        simpa [Walk.edges_reverse, Sym2.eq_swap] using heq
      have hxp : x ∈ p.support := by
        exact p.support_takeUntil_subset_support hwp
          (q.fst_mem_support_of_mem_edges hex)
      exact hpx hxp
  let d : G.Walk y y := Walk.cons hxy.symm body
  have hd : d.IsCycle := (Walk.cons_isCycle_iff body hxy.symm).2 ⟨hbody, hedge⟩
  refine ⟨y, d, hd, ?_, ?_⟩
  · have : root ∈ body.support := by
      simp only [body, Walk.mem_support_append_iff]
      exact Or.inl hrootr
    simp only [d, Walk.support_cons, List.mem_cons]
    exact Or.inr this
  · simp [d]

/-- The preceding geometric extension supplied by deletion connectivity. -/
private theorem onCommonCycle_of_adj
    (hG : TwoConnected G) {root x y : V} (hrx : root ≠ x)
    (hxy : G.Adj x y) (hcycle : OnCommonCycle G root x) :
    OnCommonCycle G root y := by
  obtain ⟨p, hp, hpx⟩ := hG.exists_path_avoiding x hxy.ne.symm hrx
  exact onCommonCycle_of_adj_of_avoiding_path hxy hcycle p hp hpx

/-- Propagate the common-cycle property along an adjacency chain which
avoids the fixed root. -/
private theorem onCommonCycle_along_chain
    (hG : TwoConnected G) {root x : V} :
    ∀ (l : List V), List.IsChain G.Adj (x :: l) →
      root ∉ x :: l → OnCommonCycle G root x →
      ∀ y ∈ x :: l, OnCommonCycle G root y := by
  intro l
  induction l generalizing x with
  | nil =>
      intro _ _ hcycle y hy
      simp only [List.mem_singleton] at hy
      simpa [hy] using hcycle
  | cons v l ih =>
      intro hchain hroot hcycle y hy
      have hc := List.isChain_cons_cons.mp hchain
      have hrel : G.Adj x v := hc.1
      have htailchain : List.IsChain G.Adj (v :: l) := hc.2
      have hrootx : root ≠ x := by
        intro h
        exact hroot (by simp [h])
      have hroottail : root ∉ v :: l := by
        intro h
        exact hroot (List.mem_cons_of_mem x h)
      have hnext : OnCommonCycle G root v :=
        onCommonCycle_of_adj hG hrootx hrel hcycle
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hcycle
      · exact ih htailchain hroottail hnext y (by simpa only [List.mem_cons] using hy)

/-- Once a cycle contains `root` and the initial vertex of a path which
avoids `root`, adjacency-chain propagation gives a cycle through `root` and
the other endpoint. -/
private theorem onCommonCycle_along_path
    (hG : TwoConnected G) {root x y : V}
    (p : G.Walk x y) (_hp : p.IsPath) (hroot : root ∉ p.support)
    (hcycle : OnCommonCycle G root x) :
    OnCommonCycle G root y := by
  exact onCommonCycle_along_chain hG p.support.tail
    (by rw [p.cons_tail_support]; exact p.isChain_adj_support)
    (by rw [p.cons_tail_support]; exact hroot) hcycle y
    (by rw [p.cons_tail_support]; exact p.end_mem_support)

/-- Every vertex of a finite vertex-two-connected graph lies on a simple
cycle. -/
theorem onCommonCycle_refl (hG : TwoConnected G) (x : V) :
    OnCommonCycle G x x := by
  obtain ⟨t, htx⟩ := hG.exists_ne x
  obtain ⟨p, hp⟩ := hG.connected.exists_isPath x t
  have hp_nonNil : ¬ p.Nil := Walk.not_nil_of_ne htx.symm
  have hxsnd : G.Adj x p.snd := p.adj_snd hp_nonNil
  obtain ⟨c, hc, -⟩ := hG.exists_cycle_through_edge hxsnd
  exact ⟨x, c, hc, c.start_mem_support, c.start_mem_support⟩

/-- Whitney's common-cycle characterization, in the direction needed here:
any two vertices of a finite vertex-two-connected graph lie on one simple
cycle. -/
theorem onCommonCycle (hG : TwoConnected G) (x y : V) :
    OnCommonCycle G x y := by
  by_cases hxy : x = y
  · subst y
    exact hG.onCommonCycle_refl x
  obtain ⟨p, hp⟩ := hG.connected.exists_isPath x y
  cases p with
  | nil => exact (hxy rfl).elim
  | @cons x v y h p =>
      have hp' : p.IsPath := hp.of_cons
      have hxnot : x ∉ p.support := (Walk.cons_isPath_iff h p).1 hp |>.2
      obtain ⟨c, hc, hv⟩ := hG.exists_cycle_through_edge h
      have hbase : OnCommonCycle G x v :=
        ⟨x, c, hc, c.start_mem_support, hv⟩
      exact onCommonCycle_along_path hG p hp' hxnot hbase

/-! ## The two-endpoint augmentation is two-connected -/

/-- A common anchor, joined to every vertex, proves connectedness. -/
private theorem connected_of_walks_to
    {W : Type*} {H : SimpleGraph W} (r : W)
    (h : ∀ w : W, Nonempty (H.Walk w r)) : H.Connected := by
  refine { preconnected := ?_, nonempty := ⟨r⟩ }
  intro u v
  obtain ⟨p⟩ := h u
  obtain ⟨q⟩ := h v
  exact ⟨p.append q.reverse⟩

/-- If every vertex other than `z` has a walk to a fixed surviving anchor,
and every such walk avoids `z`, then deleting `z` leaves a connected graph. -/
private theorem connected_induce_compl_singleton_of_walks_to
    {W : Type*} [DecidableEq W] {H : SimpleGraph W} (z r : W) (hr : r ≠ z)
    (h : ∀ w : W, w ≠ z →
      ∃ p : H.Walk w r, z ∉ p.support) :
    (H.induce ({z}ᶜ : Set W)).Connected := by
  let r' : ({z}ᶜ : Set W) := ⟨r, by simpa using hr⟩
  refine { preconnected := ?_, nonempty := ⟨r'⟩ }
  intro u v
  have hu' : (u : W) ∉ ({z} : Set W) := u.2
  have hv' : (v : W) ∉ ({z} : Set W) := v.2
  have hu : (u : W) ≠ z := fun huz ↦ hu' (by simpa using huz)
  have hv : (v : W) ≠ z := fun hvz ↦ hv' (by simpa using hvz)
  obtain ⟨p, hp⟩ := h u hu
  obtain ⟨q, hq⟩ := h v hv
  let w : H.Walk u v := p.append q.reverse
  have hw : ∀ x ∈ w.support, x ∈ ({z}ᶜ : Set W) := by
    intro x hx
    rw [Walk.mem_support_append_iff] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rcases hx with hxp | hxq
    · exact fun hzx ↦ hp (hzx ▸ hxp)
    · have hxq' : x ∈ q.support := by simpa using hxq
      exact fun hzx ↦ hq (hzx ▸ hxq')
  let wi := w.induce ({z}ᶜ : Set W) hw
  exact ⟨wi.copy (Subtype.ext rfl) (Subtype.ext rfl)⟩

/-- A base-graph walk maps to a walk between the corresponding old vertices
of the augmentation. -/
private theorem exists_old_walk (hG : G.Connected) (A B : Set V) (x y : V) :
    ∃ p : (linkAugment G A B).Walk (Sum.inl x) (Sum.inl y),
      ∀ z ∈ p.support, z ∈ Set.range (Sum.inl : V → LinkAugment V) := by
  obtain ⟨p⟩ := hG x y
  let r := p.map (linkAugmentEmbedding G A B).toHom
  have hr : ∀ z ∈ r.support,
      z ∈ Set.range (Sum.inl : V → LinkAugment V) := by
    intro z hz
    simp only [r, Walk.support_map, List.mem_map] at hz
    obtain ⟨w, -, rfl⟩ := hz
    exact Set.mem_range_self w
  let hx : (linkAugmentEmbedding G A B) x = Sum.inl x := rfl
  let hy : (linkAugmentEmbedding G A B) y = Sum.inl y := rfl
  let r' := r.copy hx hy
  have hsupp : r'.support = r.support := Walk.support_copy r hx hy
  refine ⟨r', ?_⟩
  intro z hz
  exact hr z (hsupp ▸ hz)

/-- A base-graph path avoiding `z` maps to an augmentation walk avoiding the
old copy of `z`. -/
private theorem exists_old_walk_avoiding (hG : TwoConnected G)
    (A B : Set V) (z : V) {x y : V} (hx : x ≠ z) (hy : y ≠ z) :
    ∃ p : (linkAugment G A B).Walk (Sum.inl x) (Sum.inl y),
      Sum.inl z ∉ p.support := by
  obtain ⟨p, -, hpz⟩ := hG.exists_path_avoiding z hx hy
  refine ⟨p.map (linkAugmentEmbedding G A B).toHom, ?_⟩
  intro hz
  change (linkAugmentEmbedding G A B) z ∈
    (p.map (linkAugmentEmbedding G A B).toHom).support at hz
  rw [Walk.support_map, List.mem_map] at hz
  obtain ⟨w, hw, hwz⟩ := hz
  exact hpz ((Sum.inl_injective hwz) ▸ hw)

/-- The endpoint augmentation is connected as soon as both endpoint sets are
nonempty. -/
private theorem linkAugment_connected (hG : G.Connected)
    {A B : Set V} (hA : A.Nonempty) (hB : B.Nonempty) :
    (linkAugment G A B).Connected := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  apply connected_of_walks_to (H := linkAugment G A B) (Sum.inl a)
  intro w
  cases w with
  | inl x =>
      obtain ⟨p, -⟩ := exists_old_walk hG A B x a
      exact ⟨p⟩
  | inr i =>
      cases i with
      | false =>
          exact ⟨Walk.cons (linkAugment_adj_left_inl.mpr ha) Walk.nil⟩
      | true =>
          obtain ⟨p, -⟩ := exists_old_walk hG A B b a
          exact ⟨Walk.cons (linkAugment_adj_right_inl.mpr hb) p⟩

/-- Deleting an old vertex leaves the endpoint augmentation connected. -/
private theorem linkAugment_delete_old_connected (hG : TwoConnected G)
    {A B : Set V} (hA : 2 ≤ A.ncard) (hB : 2 ≤ B.ncard) (z : V) :
    ((linkAugment G A B).induce
      ({Sum.inl z}ᶜ : Set (LinkAugment V))).Connected := by
  obtain ⟨a, ha, haz⟩ := A.exists_ne_of_one_lt_ncard (by omega) z
  obtain ⟨b, hb, hbz⟩ := B.exists_ne_of_one_lt_ncard (by omega) z
  apply connected_induce_compl_singleton_of_walks_to
    (H := linkAugment G A B) (Sum.inl z) (Sum.inl a) (by simpa)
  intro w hw
  cases w with
  | inl x =>
      have hxz : x ≠ z := by
        intro hxz
        exact hw (by simp [hxz])
      exact exists_old_walk_avoiding hG A B z hxz haz
  | inr i =>
      cases i with
      | false =>
          refine ⟨Walk.cons (linkAugment_adj_left_inl.mpr ha) Walk.nil, ?_⟩
          simp [haz.symm]
      | true =>
          obtain ⟨p, hp⟩ := exists_old_walk_avoiding hG A B z hbz haz
          refine ⟨Walk.cons (linkAugment_adj_right_inl.mpr hb) p, ?_⟩
          simpa using hp

/-- Deleting the left fresh endpoint leaves the augmentation connected. -/
private theorem linkAugment_delete_left_connected (hG : G.Connected)
    {A B : Set V} (hB : B.Nonempty) :
    ((linkAugment G A B).induce
      ({Sum.inr false}ᶜ : Set (LinkAugment V))).Connected := by
  obtain ⟨b, hb⟩ := hB
  apply connected_induce_compl_singleton_of_walks_to
    (H := linkAugment G A B) (Sum.inr false) (Sum.inl b) (by simp)
  intro w hw
  cases w with
  | inl x =>
      obtain ⟨p, hpold⟩ := exists_old_walk hG A B x b
      refine ⟨p, ?_⟩
      intro h
      obtain ⟨y, hy⟩ := hpold _ h
      cases hy
  | inr i =>
      cases i with
      | false => exact (hw rfl).elim
      | true =>
          refine ⟨Walk.cons (linkAugment_adj_right_inl.mpr hb) Walk.nil, ?_⟩
          simp

/-- Deleting the right fresh endpoint leaves the augmentation connected. -/
private theorem linkAugment_delete_right_connected (hG : G.Connected)
    {A B : Set V} (hA : A.Nonempty) :
    ((linkAugment G A B).induce
      ({Sum.inr true}ᶜ : Set (LinkAugment V))).Connected := by
  obtain ⟨a, ha⟩ := hA
  apply connected_induce_compl_singleton_of_walks_to
    (H := linkAugment G A B) (Sum.inr true) (Sum.inl a) (by simp)
  intro w hw
  cases w with
  | inl x =>
      obtain ⟨p, hpold⟩ := exists_old_walk hG A B x a
      refine ⟨p, ?_⟩
      intro h
      obtain ⟨y, hy⟩ := hpold _ h
      cases hy
  | inr i =>
      cases i with
      | false =>
          refine ⟨Walk.cons (linkAugment_adj_left_inl.mpr ha) Walk.nil, ?_⟩
          simp
      | true => exact (hw rfl).elim

/-- Adding one fresh vertex on each side makes the graph two-connected when
the base graph is two-connected and each attachment set has at least two
vertices. -/
theorem linkAugment_twoConnected (hG : TwoConnected G) {A B : Set V}
    (hA : 2 ≤ A.ncard) (hB : 2 ≤ B.ncard) :
    TwoConnected (linkAugment G A B) := by
  have hAne : A.Nonempty := (Set.ncard_pos (Set.toFinite A)).mp (by omega)
  have hBne : B.Nonempty := (Set.ncard_pos (Set.toFinite B)).mp (by omega)
  refine ⟨?_, linkAugment_connected hG.connected hAne hBne, ?_⟩
  · have hcard := hG.card_three_le
    simp [LinkAugment]
    omega
  · intro z
    cases z with
    | inl x => exact linkAugment_delete_old_connected hG hA hB x
    | inr i =>
        cases i with
        | false => exact linkAugment_delete_left_connected hG.connected hBne
        | true => exact linkAugment_delete_right_connected hG.connected hAne

/-! ## Removing the two fresh endpoints from the cycle arcs -/

/-- The old-vertex middle of a path from the left fresh endpoint to the
right fresh endpoint. -/
private structure StrippedAugmentPath (G : SimpleGraph V) (A B : Set V)
    (p : (linkAugment G A B).Walk (Sum.inr false) (Sum.inr true)) where
  a : V
  b : V
  walk : (linkAugment G A B).Walk (Sum.inl a) (Sum.inl b)
  isPath : walk.IsPath
  a_mem : a ∈ A
  b_mem : b ∈ B
  support_subset_tail : walk.support ⊆ p.support.tail
  old_support : ∀ x ∈ walk.support,
    x ∈ Set.range (Sum.inl : V → LinkAugment V)

/-- Strip the two fresh endpoints from an augmentation path.  Simplicity
ensures that neither fresh endpoint occurs in the remaining middle. -/
private theorem strip_augment_path {A B : Set V}
    (p : (linkAugment G A B).Walk (Sum.inr false) (Sum.inr true))
    (hp : p.IsPath) : Nonempty (StrippedAugmentPath G A B p) := by
  have hp_nonNil : ¬p.Nil := Walk.not_nil_of_ne (by simp)
  have htailPath : p.tail.IsPath := hp.tail
  have htail_nonNil : ¬p.tail.Nil := by
    intro hnil
    have hsnd : p.snd = Sum.inr true := htailPath.nil_iff_eq.mp hnil
    have hadj := p.adj_snd hp_nonNil
    rw [hsnd] at hadj
    simpa [linkAugment] using hadj
  have hpen : p.tail.penultimate = p.penultimate := by
    have h := Walk.penultimate_cons_of_not_nil
      (p.adj_snd hp_nonNil) p.tail htail_nonNil
    rw [p.cons_tail_eq hp_nonNil] at h
    exact h.symm
  have hleft := p.adj_snd hp_nonNil
  have hright := p.adj_penultimate hp_nonNil
  cases hs : p.snd with
  | inr i =>
    rw [hs] at hleft
    cases i <;> simp [linkAugment] at hleft
  | inl a =>
    rw [hs] at hleft
    cases ht : p.penultimate with
    | inr i =>
      rw [ht] at hright
      cases i <;> simp [linkAugment] at hright
    | inl b =>
      rw [ht] at hright
      have ha : a ∈ A := by simpa using hleft
      have hb : b ∈ B := by simpa using hright
      let m₀ := p.tail.dropLast
      have hm₀ : m₀.IsPath := hp.tail.dropLast
      have hmend : p.tail.penultimate = Sum.inl b := hpen.trans ht
      let m : (linkAugment G A B).Walk (Sum.inl a) (Sum.inl b) :=
        m₀.copy hs hmend
      have hmsub : m.support ⊆ p.support.tail := by
        intro x hx
        have hx₀ : x ∈ m₀.support := by simpa [m] using hx
        have hxdrop : x ∈ p.tail.support.dropLast := by
          simpa [m₀, Walk.support_dropLast htail_nonNil] using hx₀
        have hxtail : x ∈ p.tail.support := List.mem_of_mem_dropLast hxdrop
        simpa [p.support_tail_of_not_nil hp_nonNil] using hxtail
      have halpha : Sum.inr false ∉ p.support.tail := by
        have hn := hp.support_nodup
        rw [← p.cons_tail_support] at hn
        exact (List.nodup_cons.mp hn).1
      have hbeta : Sum.inr true ∉ m.support := by
        intro hx
        have hx₀ : Sum.inr true ∈ m₀.support := by simpa [m] using hx
        have hn := hp.tail.support_nodup
        rw [← p.tail.support_dropLast_concat htail_nonNil] at hn
        exact hn.disjoint hx₀ (by simp)
      refine ⟨{
        a := a
        b := b
        walk := m
        isPath := by simpa [m] using hm₀
        a_mem := ha
        b_mem := hb
        support_subset_tail := hmsub
        old_support := ?_ }⟩
      intro x hx
      cases x with
      | inl v => exact ⟨v, rfl⟩
      | inr i =>
          cases i with
          | false => exact (halpha (hmsub hx)).elim
          | true => exact (hbeta hx).elim

/-- A walk in the augmentation all of whose vertices are old is the image of
a unique old-graph walk.  Only existence and the mapping equality are needed
below. -/
private theorem exists_old_preimage {A B : Set V} {a b : V}
    (p : (linkAugment G A B).Walk (Sum.inl a) (Sum.inl b))
    (hold : ∀ x ∈ p.support,
      x ∈ Set.range (Sum.inl : V → LinkAugment V)) :
    ∃ q : G.Walk a b, q.map (linkAugmentEmbedding G A B).toHom = p := by
  classical
  let e := linkAugmentEmbedding G A B
  have hold' : ∀ x ∈ p.support, x ∈ Set.range e := by
    intro x hx
    obtain ⟨v, hv⟩ := hold x hx
    refine ⟨v, ?_⟩
    change Sum.inl v = x
    exact hv
  let p' := p.induce (Set.range e) hold'
  let q₀ := p'.map e.isoInduceRange.symm.toHom
  have hqa : e.isoInduceRange.symm
      ⟨Sum.inl a, Set.mem_range_self a⟩ = a := by
    exact e.isoInduceRange.symm_apply_apply a
  have hqb : e.isoInduceRange.symm
      ⟨Sum.inl b, Set.mem_range_self b⟩ = b := by
    exact e.isoInduceRange.symm_apply_apply b
  let q : G.Walk a b := q₀.copy hqa hqb
  refine ⟨q, ?_⟩
  apply Walk.ext_support
  calc
    (q.map (linkAugmentEmbedding G A B).toHom).support =
        (q₀.map e.toHom).support := by
      simp [q, e]
    _ = p.support := by
      simp only [q₀, Walk.support_map, List.map_map]
      change List.map (fun x : Set.range e => e (e.isoInduceRange.symm x))
          p'.support = p.support
      have hfun : (fun x : Set.range e => e (e.isoInduceRange.symm x)) =
          (fun x : Set.range e => (x : LinkAugment V)) := by
        funext x
        exact congrArg Subtype.val (e.isoInduceRange.apply_symm_apply x)
      rw [hfun]
      change ((p.induce (Set.range e) hold').support.map Subtype.val) = p.support
      rw [Walk.support_induce]
      exact List.attachWith_map_subtype_val hold'

/-- Pull a stripped augmentation path back to the base graph, retaining the
exact equality after mapping it into the augmentation. -/
private theorem StrippedAugmentPath.exists_old_path {A B : Set V}
    {p : (linkAugment G A B).Walk (Sum.inr false) (Sum.inr true)}
    (S : StrippedAugmentPath G A B p) :
    ∃ q : G.Walk S.a S.b,
      q.IsPath ∧ q.map (linkAugmentEmbedding G A B).toHom = S.walk := by
  obtain ⟨q, hq⟩ := exists_old_preimage S.walk S.old_support
  refine ⟨q, ?_, hq⟩
  have hmapped : (q.map (linkAugmentEmbedding G A B).toHom).IsPath := by
    rw [Walk.isPath_def, hq]
    exact S.isPath.support_nodup
  exact (Walk.isPath_map_iff_of_injective
    (f := (linkAugmentEmbedding G A B).toHom)
    (linkAugmentEmbedding G A B).injective).mp hmapped

/-- The fresh-endpoint cycle in the augmentation yields two fully disjoint
base-graph paths from `A` to `B`. -/
theorem exists_rawTwoPathPacking (hG : TwoConnected G) {A B : Set V}
    (hA : 2 ≤ A.ncard) (hB : 2 ≤ B.ncard) :
    Nonempty (RawTwoPathPacking G A B) := by
  let H := linkAugment G A B
  have hH : TwoConnected H := hG.linkAugment_twoConnected hA hB
  obtain ⟨z, c, hc, hleft, hright⟩ :=
    hH.onCommonCycle (Sum.inr false) (Sum.inr true)
  obtain ⟨p, q, hp, hq, -, -, -, hmeet, -, -, -⟩ :=
    exists_path_arcs_of_cycle hc hleft hright (by simp)
  obtain ⟨P⟩ := strip_augment_path p hp
  obtain ⟨Q⟩ := strip_augment_path q hq
  obtain ⟨pG, hpG, hpmap⟩ := P.exists_old_path
  obtain ⟨qG, hqG, hqmap⟩ := Q.exists_old_path
  have hdisj : pG.support.Disjoint qG.support := by
    rw [List.disjoint_left]
    intro x hxp hxq
    have hxp' : Sum.inl x ∈ P.walk.support := by
      have hxpmap : (linkAugmentEmbedding G A B) x ∈
          (pG.map (linkAugmentEmbedding G A B).toHom).support := by
        rw [Walk.support_map]
        exact List.mem_map.mpr ⟨x, hxp, rfl⟩
      rw [hpmap] at hxpmap
      exact hxpmap
    have hxq' : Sum.inl x ∈ Q.walk.support := by
      have hxqmap : (linkAugmentEmbedding G A B) x ∈
          (qG.map (linkAugmentEmbedding G A B).toHom).support := by
        rw [Walk.support_map]
        exact List.mem_map.mpr ⟨x, hxq, rfl⟩
      rw [hqmap] at hxqmap
      exact hxqmap
    have hxpArc : Sum.inl x ∈ p.support :=
      List.mem_of_mem_tail (P.support_subset_tail hxp')
    have hxqArc : Sum.inl x ∈ q.support :=
      List.mem_of_mem_tail (Q.support_subset_tail hxq')
    rcases hmeet (Sum.inl x) hxpArc hxqArc with h | h <;> simp at h
  exact ⟨{
    a₁ := P.a
    a₂ := Q.a
    b₁ := P.b
    b₂ := Q.b
    p := pG
    q := qG
    p_isPath := hpG
    q_isPath := hqG
    a₁_mem := P.a_mem
    a₂_mem := Q.a_mem
    b₁_mem := P.b_mem
    b₂_mem := Q.b_mem
    disjoint_support := hdisj }⟩

/-- The unconditional finite two-path Menger consequence needed for the
Gyárfás argument.  The endpoint-cardinality hypotheses are sharp for full
support disjointness. -/
theorem exists_twoLinkage (hG : TwoConnected G) {A B : Set V}
    (hA : 2 ≤ A.ncard) (hB : 2 ≤ B.ncard) :
    Nonempty (TwoLinkage G A B) := by
  obtain ⟨P⟩ := hG.exists_rawTwoPathPacking hA hB
  exact hG.twoLinkage_of_rawPacking P

end TwoConnected

end Erdos556

#print axioms Erdos556.TwoConnected.exists_twoLinkage

