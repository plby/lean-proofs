/-
# Erdős 58: the DFS upper bound

This file isolates the elementary (non-sharp) half of Erdős problem 58.  A
normal depth-first-search tree has the property that the ends of every edge
are comparable in the rooted-tree order.  Edges joining two levels of the
same parity therefore give pairwise different odd fundamental-cycle lengths.
Greedy coloring inside the two parity classes gives `2 * (k + 1)` colors.
-/

import ErdosProblems.Erdos58.Basic
import Mathlib

open scoped ENat

namespace Erdos58.DFSUpper

open SimpleGraph

universe u

/-- The finite set of odd lengths of simple cycles in `G`. -/
noncomputable def oddCycleLengths {V : Type u} [Finite V]
    (G : SimpleGraph V) : Finset ℕ := by
  classical
  exact (Finset.range (Nat.card V + 1)).filter fun n ↦
    Odd n ∧ ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = n

lemma IsCycle.length_le_card {V : Type u} [Finite V] {G : SimpleGraph V}
    {v : V} {c : G.Walk v v} (hc : c.IsCycle) : c.length ≤ Nat.card V := by
  letI := Fintype.ofFinite V
  have hlen : c.support.tail.length = c.length := by
    rw [List.length_tail, c.length_support]
    omega
  rw [← hlen]
  simpa only [Nat.card_eq_fintype_card] using hc.support_nodup.length_le_card

lemma mem_oddCycleLengths_iff {V : Type u} [Finite V] {G : SimpleGraph V} {n : ℕ} :
    n ∈ oddCycleLengths G ↔
      Odd n ∧ ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = n := by
  classical
  constructor
  · intro hn
    exact (Finset.mem_filter.mp hn).2
  · intro hn
    rw [oddCycleLengths, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.lt_succ_of_le ?_, hn⟩
    obtain ⟨v, c, hc, rfl⟩ := hn.2
    exact IsCycle.length_le_card hc

/-- The finite DFS representation contains exactly the elements of the
canonical set of odd cycle lengths from `Erdos58.Basic`. -/
lemma coe_oddCycleLengths_eq_canonical {V : Type u} [Finite V]
    (G : SimpleGraph V) :
    (↑(Erdos58.DFSUpper.oddCycleLengths G) : Set ℕ) =
      Erdos58.oddCycleLengths G := by
  ext n
  rw [Finset.mem_coe, Erdos58.DFSUpper.mem_oddCycleLengths_iff,
    Erdos58.mem_oddCycleLengths]

/-- The cardinality of the finite DFS representation is the `Set.ncard` of
the repository's canonical odd-cycle-length set. -/
lemma oddCycleLengths_card_eq_ncard_canonical {V : Type u} [Finite V]
    (G : SimpleGraph V) :
    (Erdos58.DFSUpper.oddCycleLengths G).card =
      (Erdos58.oddCycleLengths G).ncard := by
  rw [← Set.ncard_coe_finset,
    Erdos58.DFSUpper.coe_oddCycleLengths_eq_canonical]

/-- Root paths for a normal rooted spanning tree.  Storing the root paths is
more convenient here than storing parent pointers. -/
structure NormalTree {V : Type u} (G : SimpleGraph V) (root : V) where
  route : (v : V) → G.Walk root v
  route_isPath : ∀ v, (route v).IsPath
  normal : ∀ {u v : V}, G.Adj u v →
    (route u).support <+: (route v).support ∨
      (route v).support <+: (route u).support

namespace NormalTree

variable {V : Type u} {G : SimpleGraph V} {root : V} (T : NormalTree G root)

lemma root_mem_route (v : V) : root ∈ (T.route v).support :=
  (T.route v).start_mem_support

lemma end_mem_route (v : V) : v ∈ (T.route v).support :=
  (T.route v).end_mem_support

lemma length_eq_idxOf_end [DecidableEq V] (v : V) :
    (T.route v).support.idxOf v = (T.route v).length := by
  have hnodup : (T.route v).support.Nodup :=
    (SimpleGraph.Walk.isPath_def _).mp (T.route_isPath v)
  have hi : (T.route v).support.idxOf v < (T.route v).support.length :=
    List.idxOf_lt_length_of_mem (T.end_mem_route v)
  have hi' : (T.route v).support.idxOf v ≤ (T.route v).length := by
    rw [(T.route v).length_support] at hi
    omega
  apply (hnodup.getElem_inj_iff).mp
  rw [List.getElem_idxOf hi, (T.route v).support_getElem_eq_getVert (by
      rw [(T.route v).length_support]
      omega),
    (T.route v).getVert_length]

end NormalTree

/-! ## Greedy coloring along a rank -/

/-- If at most `k` same-parity neighbors of each vertex occur no later in a
natural-valued rank, then the graph is `2 * (k + 1)`-colorable. -/
private theorem colorable_of_rank_bound {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (rank : V → ℕ) (k : ℕ)
    (hbound : ∀ v : V,
      (Finset.univ.filter fun w ↦
        G.Adj v w ∧ rank w % 2 = rank v % 2 ∧ rank w ≤ rank v).card ≤ k) :
    G.Colorable (2 * (k + 1)) := by
  classical
  let Color := Fin 2 × Fin (k + 1)
  have h_colorable : ∀ S : Finset V,
      ∃ c : V → Fin (k + 1),
        ∀ v ∈ S, ∀ w ∈ S, G.Adj v w →
          rank v % 2 = rank w % 2 → c v ≠ c w := by
    intro S
    induction S using Finset.strongInduction with
    | H S ih =>
      by_cases hS : S.Nonempty
      · obtain ⟨v, hvS, hvmax⟩ := Finset.exists_max_image S rank hS
        obtain ⟨c, hc⟩ := ih (S.erase v) (Finset.erase_ssubset hvS)
        let N : Finset V := S.filter fun w ↦
          G.Adj v w ∧ rank w % 2 = rank v % 2
        have hNsub : N ⊆ Finset.univ.filter fun w ↦
            G.Adj v w ∧ rank w % 2 = rank v % 2 ∧ rank w ≤ rank v := by
          intro w hw
          rw [Finset.mem_filter] at hw ⊢
          exact ⟨Finset.mem_univ _, hw.2.1, hw.2.2, hvmax w hw.1⟩
        have hNcard : N.card ≤ k :=
          (Finset.card_mono hNsub).trans (hbound v)
        have hforbidden : (N.image c).card < k + 1 :=
          (Finset.card_image_le.trans hNcard).trans_lt (Nat.lt_succ_self k)
        obtain ⟨a, ha⟩ : ∃ a : Fin (k + 1), a ∉ N.image c := by
          obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
            (s := N.image c) (t := Finset.univ) (by
              simpa using hforbidden)
          exact ⟨a, ha⟩
        refine ⟨fun w ↦ if w = v then a else c w, ?_⟩
        intro x hx y hy hxy hpar
        by_cases hxv : x = v
        · subst x
          have hyv : y ≠ v := fun h ↦ G.ne_of_adj hxy h.symm
          simp only [if_pos, if_neg hyv]
          intro heq
          have hyN : y ∈ N := by simp [N, hy, hxy, hpar.symm]
          exact ha (Finset.mem_image.mpr ⟨y, hyN, heq.symm⟩)
        · by_cases hyv : y = v
          · subst y
            simp only [if_pos, if_neg hxv]
            intro heq
            have hxN : x ∈ N := by simp [N, hx, hxy.symm, hpar]
            exact ha (Finset.mem_image.mpr ⟨x, hxN, heq⟩)
          · simp only [if_neg hxv, if_neg hyv]
            exact hc x (Finset.mem_erase.mpr ⟨hxv, hx⟩) y
              (Finset.mem_erase.mpr ⟨hyv, hy⟩) hxy hpar
      · exact ⟨fun _ ↦ 0, by simpa [Finset.not_nonempty_iff_eq_empty.mp hS]⟩
  obtain ⟨c, hc⟩ := h_colorable Finset.univ
  let e : Color ≃ Fin (2 * (k + 1)) :=
    Fintype.equivFinOfCardEq (by simp [Color])
  let paired : V → Color := fun v ↦
    (⟨rank v % 2, Nat.mod_lt _ Nat.zero_lt_two⟩, c v)
  exact ⟨SimpleGraph.Coloring.mk (fun v ↦ e (paired v)) fun {v w} hvw h ↦ by
    have hp : paired v = paired w := e.injective h
    have hpar : rank v % 2 = rank w % 2 := by
      have := congrArg Prod.fst hp
      simpa [paired, Fin.ext_iff] using this
    exact hc v (Finset.mem_univ _) w (Finset.mem_univ _) hvw hpar
      (congrArg Prod.snd hp)⟩

/-! The existence proof is below.  It is the usual recursive DFS: remove the
root, recursively search every component, and join the root to each component
at the first edge entering it. -/

private lemma exists_root_neighbor_in_component
    {V : Type u} [Fintype V] (G : SimpleGraph V) (root : V) (hG : G.Connected)
    (H : SimpleGraph {v : V // v ≠ root})
    (hH : H = G.comap (Function.Embedding.subtype fun v : V ↦ v ≠ root))
    (C : H.ConnectedComponent) :
    ∃ x : C, G.Adj root x.1.1 := by
  classical
  let y : C := ⟨C.out, C.out_eq⟩
  have hyr : (y.1.1 : V) ≠ root := y.1.2
  obtain ⟨p, hp⟩ := (hG root y.1.1).exists_isPath
  let S : Set V := {z | ∃ hz : z ≠ root, (⟨z, hz⟩ : {v : V // v ≠ root}) ∈ C.supp}
  have hyS : (y.1.1 : V) ∈ S := ⟨hyr, y.2⟩
  have hrS : root ∉ S := by simp [S]
  obtain ⟨d, hd, hdS, hdnot⟩ := p.reverse.exists_boundary_dart S hyS hrS
  have hdsnd : d.snd = root := by
    by_contra hne
    have hfst_ne : d.fst ≠ root := by
      rintro rfl
      exact hrS hdS
    obtain ⟨hfst, hfstC⟩ := hdS
    have hadjH : H.Adj ⟨d.fst, hfst_ne⟩ ⟨d.snd, hne⟩ := by
      rw [hH]
      exact d.adj
    have hsndC : (⟨d.snd, hne⟩ : {v : V // v ≠ root}) ∈ C.supp :=
      C.mem_supp_of_adj_mem_supp hfstC hadjH
    exact hdnot ⟨hne, hsndC⟩
  have hfst_ne : d.fst ≠ root := by
    rintro rfl
    exact hrS hdS
  obtain ⟨_, hfstC⟩ := hdS
  refine ⟨⟨⟨d.fst, hfst_ne⟩, hfstC⟩, ?_⟩
  simpa [hdsnd] using d.adj.symm

theorem exists_normalTree_of_connected {V : Type u} [Finite V]
    (G : SimpleGraph V) (root : V) (hG : G.Connected) : Nonempty (NormalTree G root) := by
  classical
  letI := Fintype.ofFinite V
  induction hn : Nat.card V using Nat.strong_induction_on generalizing V with
  | h n ih =>
      let W := {v : V // v ≠ root}
      let emb : W ↪ V := Function.Embedding.subtype fun v : V ↦ v ≠ root
      let H : SimpleGraph W := G.comap emb
      have hx (C : H.ConnectedComponent) : ∃ x : C, G.Adj root x.1.1 :=
        exists_root_neighbor_in_component G root hG H rfl C
      choose x hx using hx
      have hcard (C : H.ConnectedComponent) : Nat.card C < n := by
        rw [← hn]
        simp only [Nat.card_eq_fintype_card]
        exact Fintype.card_lt_of_injective_of_notMem
          (fun z : C ↦ (z.1.1 : V))
          (fun a b hab ↦ Subtype.ext (Subtype.ext hab))
          (by
            rintro ⟨z, hz⟩
            exact z.1.2 hz)
      have subTree (C : H.ConnectedComponent) :
          Nonempty (NormalTree C.toSimpleGraph (x C)) := by
        exact ih (Nat.card C) (hcard C) C.toSimpleGraph (x C)
          C.connected_toSimpleGraph rfl
      let tree (C : H.ConnectedComponent) : NormalTree C.toSimpleGraph (x C) :=
        (subTree C).some
      let hom (C : H.ConnectedComponent) : C.toSimpleGraph →g G :=
        { toFun := fun z ↦ z.1.1
          map_rel' := fun hadj ↦ hadj }
      let route : (v : V) → G.Walk root v := fun v ↦
        if hv : v = root then
          (SimpleGraph.Walk.nil : G.Walk root root).copy rfl hv.symm
        else
          let w : W := ⟨v, hv⟩
          let C := H.connectedComponentMk w
          let z : C := ⟨w, ConnectedComponent.connectedComponentMk_mem⟩
          SimpleGraph.Walk.cons (hx C) ((tree C).route z |>.map (hom C))
      refine ⟨⟨route, ?_, ?_⟩⟩
      · intro v
        simp only [route]
        split_ifs with hv
        · subst v
          exact SimpleGraph.Walk.IsPath.nil
        · apply SimpleGraph.Walk.IsPath.cons
          · exact ((tree _).route_isPath _).map
              (fun _ _ h ↦ Subtype.ext (Subtype.ext h))
          · simp only [SimpleGraph.Walk.support_map, List.mem_map]
            rintro ⟨z, hz, hzr⟩
            have : (z.1.1 : V) ≠ root := z.1.2
            exact this hzr
      · intro u v huv
        by_cases hu : u = root
        · subst u
          left
          rw [show (route root).support = [root] by simp [route]]
          exact ⟨(route v).support.tail, by
            simpa using (route v).cons_tail_support⟩
        by_cases hv : v = root
        · subst v
          right
          rw [show (route root).support = [root] by simp [route]]
          exact ⟨(route u).support.tail, by
            simpa using (route u).cons_tail_support⟩
        let wu : W := ⟨u, hu⟩
        let wv : W := ⟨v, hv⟩
        have hadjH : H.Adj wu wv := huv
        have hC : H.connectedComponentMk wu = H.connectedComponentMk wv :=
          ConnectedComponent.sound hadjH.reachable
        have mapped_route_eq (C D : H.ConnectedComponent) (hCD : C = D)
            (w : W) (hwC : w ∈ C.supp) (hwD : w ∈ D.supp) :
            List.map (hom C)
                ((tree C).route (⟨w, hwC⟩ : C)).support =
              List.map (hom D)
                ((tree D).route (⟨w, hwD⟩ : D)).support := by
          subst D
          rfl
        let C := H.connectedComponentMk wu
        have hwuC : wu ∈ C.supp := ConnectedComponent.connectedComponentMk_mem
        have hwvC : wv ∈ C.supp := by
          change wv ∈ (H.connectedComponentMk wu).supp
          rw [hC]
          exact ConnectedComponent.connectedComponentMk_mem
        let zu : C := ⟨wu, hwuC⟩
        let zv : C := ⟨wv, hwvC⟩
        have hadjC : C.toSimpleGraph.Adj zu zv := hadjH
        have hvroute :
            List.map (hom C) ((tree C).route zv).support =
              List.map (hom (H.connectedComponentMk wv))
                ((tree (H.connectedComponentMk wv)).route
                  (⟨wv, ConnectedComponent.connectedComponentMk_mem⟩ :
                    H.connectedComponentMk wv)).support :=
          mapped_route_eq C (H.connectedComponentMk wv) hC wv hwvC
            ConnectedComponent.connectedComponentMk_mem
        rcases (tree C).normal hadjC with hpre | hpre
        · left
          simp only [route, dif_neg hu, dif_neg hv, SimpleGraph.Walk.support_cons,
            SimpleGraph.Walk.support_map, List.cons_prefix_cons]
          refine ⟨trivial, ?_⟩
          rw [← hvroute]
          exact hpre.map _
        · right
          simp only [route, dif_neg hu, dif_neg hv, SimpleGraph.Walk.support_cons,
            SimpleGraph.Walk.support_map, List.cons_prefix_cons]
          refine ⟨trivial, ?_⟩
          rw [← hvroute]
          exact hpre.map _

namespace NormalTree

variable {V : Type u} [Fintype V] {G : SimpleGraph V} {root : V}
    (T : NormalTree G root)

/-- The fundamental closed walk obtained by adding an edge from a vertex to
an ancestor on its DFS root path. -/
noncomputable def fundamentalCycle {v w : V} (hvw : G.Adj v w)
    (hw : w ∈ (T.route v).support) : G.Walk v v := by
  classical
  exact SimpleGraph.Walk.cons hvw (T.route v |>.dropUntil w hw)

lemma length_fundamentalCycle {v w : V} (hvw : G.Adj v w)
    (hpre : (T.route w).support <+: (T.route v).support) :
    (T.fundamentalCycle hvw (hpre.subset (T.end_mem_route w))).length =
      (T.route v).length - (T.route w).length + 1 := by
  classical
  simp only [fundamentalCycle, SimpleGraph.Walk.length_cons,
    SimpleGraph.Walk.length_dropUntil]
  rw [← hpre.idxOf_eq_of_mem (T.end_mem_route w), T.length_eq_idxOf_end]

lemma fundamentalCycle_isCycle {v w : V} (hvw : G.Adj v w)
    (hpre : (T.route w).support <+: (T.route v).support)
    (hpar : (T.route w).length % 2 = (T.route v).length % 2) :
    (T.fundamentalCycle hvw (hpre.subset (T.end_mem_route w))).IsCycle := by
  classical
  change (SimpleGraph.Walk.cons hvw
    ((T.route v).dropUntil w (hpre.subset (T.end_mem_route w)))).IsCycle
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  refine ⟨(T.route_isPath v).dropUntil _, ?_⟩
  intro hedge
  have hedge' : s(w, v) ∈
      ((T.route v).dropUntil w
        (hpre.subset (T.end_mem_route w))).edges := by
    simpa only [Sym2.eq_swap] using hedge
  have hone := ((T.route_isPath v).dropUntil
    (hpre.subset (T.end_mem_route w))).length_eq_one_of_mem_edges hedge'
  have hlen := T.length_fundamentalCycle hvw hpre
  simp only [fundamentalCycle, SimpleGraph.Walk.length_cons] at hlen
  have hwv : (T.route w).length ≤ (T.route v).length := by
    have := hpre.length_le
    simp only [SimpleGraph.Walk.length_support] at this
    omega
  have hne : v ≠ w := G.ne_of_adj hvw
  have hdepth_ne : (T.route v).length ≠ (T.route w).length := by
    intro heq
    have hsupp : (T.route w).support = (T.route v).support :=
      hpre.eq_of_length (by simpa only [SimpleGraph.Walk.length_support, heq])
    apply hne
    have hlast := List.getLast_congr (T.route w).support_ne_nil
      (T.route v).support_ne_nil hsupp
    simpa using hlast.symm
  omega

lemma fundamentalCycle_length_mem {v w : V} (hvw : G.Adj v w)
    (hpre : (T.route w).support <+: (T.route v).support)
    (hpar : (T.route w).length % 2 = (T.route v).length % 2) :
    (T.route v).length - (T.route w).length + 1 ∈ oddCycleLengths G := by
  classical
  rw [mem_oddCycleLengths_iff]
  have hle : (T.route w).length ≤ (T.route v).length := by
    have := hpre.length_le
    simp only [SimpleGraph.Walk.length_support] at this
    omega
  refine ⟨?_, v, T.fundamentalCycle hvw (hpre.subset (T.end_mem_route w)),
    T.fundamentalCycle_isCycle hvw hpre hpar, T.length_fundamentalCycle hvw hpre⟩
  rw [Nat.odd_iff]
  omega

/-- Same-parity adjacent ancestors of `v`. -/
noncomputable def ancestorNeighbors (v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun w ↦
    G.Adj v w ∧
      (T.route w).support <+: (T.route v).support ∧
      (T.route w).length % 2 = (T.route v).length % 2

lemma mem_ancestorNeighbors_iff {v w : V} : w ∈ T.ancestorNeighbors v ↔
    G.Adj v w ∧ (T.route w).support <+: (T.route v).support ∧
      (T.route w).length % 2 = (T.route v).length % 2 := by
  classical
  simp [ancestorNeighbors]

lemma ancestorNeighbors_card_le (v : V) :
    (T.ancestorNeighbors v).card ≤ (oddCycleLengths G).card := by
  classical
  let code : V → ℕ := fun w ↦ (T.route v).length - (T.route w).length + 1
  refine Finset.card_le_card_of_injOn code ?_ ?_
  · intro w hw
    have hw := T.mem_ancestorNeighbors_iff.mp hw
    exact T.fundamentalCycle_length_mem hw.1 hw.2.1 hw.2.2
  · intro a ha b hb hab
    have ha := T.mem_ancestorNeighbors_iff.mp ha
    have hb := T.mem_ancestorNeighbors_iff.mp hb
    have ha_le : (T.route a).length ≤ (T.route v).length := by
      have := ha.2.1.length_le
      simp only [SimpleGraph.Walk.length_support] at this
      omega
    have hb_le : (T.route b).length ≤ (T.route v).length := by
      have := hb.2.1.length_le
      simp only [SimpleGraph.Walk.length_support] at this
      omega
    have hdepth : (T.route a).length = (T.route b).length := by
      dsimp only [code] at hab
      omega
    have hia : (T.route v).support.idxOf a = (T.route a).length := by
      rw [← ha.2.1.idxOf_eq_of_mem (T.end_mem_route a), T.length_eq_idxOf_end]
    have hib : (T.route v).support.idxOf b = (T.route b).length := by
      rw [← hb.2.1.idxOf_eq_of_mem (T.end_mem_route b), T.length_eq_idxOf_end]
    calc
      a = (T.route v).getVert ((T.route v).support.idxOf a) :=
        (T.route v).getVert_support_idxOf
          (ha.2.1.subset (T.end_mem_route a)) |>.symm
      _ = (T.route v).getVert ((T.route v).support.idxOf b) := by rw [hia, hib, hdepth]
      _ = b := (T.route v).getVert_support_idxOf
        (hb.2.1.subset (T.end_mem_route b))

end NormalTree

private theorem colorable_of_normalTree {V : Type u} [Finite V]
    (G : SimpleGraph V) (k : ℕ) {root : V}
    (T : NormalTree G root) (hk : (oddCycleLengths G).card ≤ k) :
    G.Colorable (2 * (k + 1)) := by
  classical
  letI := Fintype.ofFinite V
  apply colorable_of_rank_bound G (fun v ↦ (T.route v).length) k
  intro v
  let earlier : Finset V := Finset.univ.filter fun w ↦
    G.Adj v w ∧
      (T.route w).length % 2 = (T.route v).length % 2 ∧
      (T.route w).length ≤ (T.route v).length
  have hsub : earlier ⊆ T.ancestorNeighbors v := by
    intro w hw
    rw [Finset.mem_filter] at hw
    apply T.mem_ancestorNeighbors_iff.mpr
    refine ⟨hw.2.1, ?_, hw.2.2.1⟩
    rcases T.normal hw.2.1 with hrev | hpre
    · have hsupp : (T.route v).support = (T.route w).support :=
        hrev.eq_of_length_le (by
          simp only [SimpleGraph.Walk.length_support]
          omega)
      have hvw : v = w := by
        have hlast := List.getLast_congr (T.route v).support_ne_nil
          (T.route w).support_ne_nil hsupp
        simpa using hlast
      exact (G.ne_of_adj hw.2.1 hvw).elim
    · exact hpre
  change earlier.card ≤ k
  exact (Finset.card_mono hsub).trans
    ((T.ancestorNeighbors_card_le v).trans hk)

/-- Connected case of the DFS upper bound. -/
theorem colorable_of_oddCycleLengths_card_le_of_connected
    {V : Type u} [Finite V] (G : SimpleGraph V)
    (k : ℕ) (hG : G.Connected) (hk : (oddCycleLengths G).card ≤ k) :
    G.Colorable (2 * k + 2) := by
  classical
  letI := Fintype.ofFinite V
  let root : V := hG.nonempty.some
  let T : NormalTree G root := (exists_normalTree_of_connected G root hG).some
  simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    colorable_of_normalTree G k T hk

/-- The elementary DFS conclusion in Erdős problem 58: at most `k` distinct
odd cycle lengths imply chromatic number at most `2k+2`. -/
theorem colorable_of_oddCycleLengths_card_le
    {V : Type u} [Finite V] (G : SimpleGraph V)
    (k : ℕ) (hk : (oddCycleLengths G).card ≤ k) :
    G.Colorable (2 * k + 2) := by
  classical
  letI := Fintype.ofFinite V
  rw [SimpleGraph.colorable_iff_forall_connectedComponent]
  intro C
  have hsubset : oddCycleLengths C.toSimpleGraph ⊆ oddCycleLengths G := by
    intro n hn
    rw [mem_oddCycleLengths_iff] at hn ⊢
    obtain ⟨hodd, v, c, hc, rfl⟩ := hn
    let f : C.toSimpleGraph →g G := C.toSimpleGraph_hom
    refine ⟨hodd, v.1, c.map f, ?_, SimpleGraph.Walk.length_map f c⟩
    exact hc.map Subtype.val_injective
  apply colorable_of_oddCycleLengths_card_le_of_connected C.toSimpleGraph k
    C.connected_toSimpleGraph
  exact (Finset.card_mono hsubset).trans hk

/-- Canonical-set form of the DFS upper bound: at most `k` distinct odd
cycle lengths imply a `(2 * k + 2)`-coloring. -/
theorem colorable_of_ncard_oddCycleLengths_le
    {V : Type u} [Finite V] (G : SimpleGraph V) (k : ℕ)
    (hk : (Erdos58.oddCycleLengths G).ncard ≤ k) :
    G.Colorable (2 * k + 2) := by
  apply Erdos58.DFSUpper.colorable_of_oddCycleLengths_card_le G k
  rw [Erdos58.DFSUpper.oddCycleLengths_card_eq_ncard_canonical]
  exact hk

end Erdos58.DFSUpper
