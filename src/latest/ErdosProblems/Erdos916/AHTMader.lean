/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTConnectivity
import ErdosProblems.Erdos916.AHTThreeConnected
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Edge-minimal three-connectivity and the Mader count

This file records the exact connectivity notions used in Section 4 of
Aboulker--Havet--Trotignon.  It also formalizes the elementary counting part
of Mader's theorem: if every cycle of a finite three-connected graph contains
a vertex of degree three, then at least `(2 * |V| + 2) / 5` vertices have
degree three.  The proof follows the published proof.  Removing the
degree-three vertices leaves a forest; the handshaking identity and the
forest edge bound then give the result.
-/

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Delete one displayed edge. -/
def eraseEdge (G : SimpleGraph V) (u v : V) : SimpleGraph V :=
  G.deleteEdges {s(u, v)}

instance instDecidableRelEraseEdge (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) : DecidableRel (eraseEdge G u v).Adj := by
  dsimp only [eraseEdge]
  infer_instance

@[simp] theorem eraseEdge_adj {u v x y : V} :
    (eraseEdge G u v).Adj x y ↔
      G.Adj x y ∧ ¬((x = u ∧ y = v) ∨ (x = v ∧ y = u)) := by
  simp [eraseEdge, Sym2.eq_iff]

theorem eraseEdge_le (G : SimpleGraph V) (u v : V) :
    eraseEdge G u v ≤ G :=
  SimpleGraph.deleteEdges_le _

/-- Edge-minimality for the separation-based three-connectivity predicate. -/
def IsEdgeMinimallyThreeConnected (G : SimpleGraph V) : Prop :=
  IsThreeConnected G ∧
    ∀ {u v : V}, G.Adj u v → ¬IsThreeConnected (eraseEdge G u v)

namespace IsEdgeMinimallyThreeConnected

theorem isThreeConnected (hG : IsEdgeMinimallyThreeConnected G) :
    IsThreeConnected G := hG.1

theorem eraseEdge_not_isThreeConnected
    (hG : IsEdgeMinimallyThreeConnected G) {u v : V} (huv : G.Adj u v) :
    ¬IsThreeConnected (eraseEdge G u v) :=
  hG.2 huv

end IsEdgeMinimallyThreeConnected

/-- Deleting an edge removes exactly the opposite endpoint from the open
neighbourhood of either endpoint. -/
theorem neighborFinset_eraseEdge_left {u v : V} (huv : G.Adj u v) :
    (eraseEdge G u v).neighborFinset u = G.neighborFinset u \ {v} := by
  classical
  ext w
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_sdiff,
    Finset.mem_singleton]
  change (G.deleteEdges {s(u, v)}).Adj u w ↔ G.Adj u w ∧ w ≠ v
  rw [SimpleGraph.deleteEdges_adj]
  simp only [Set.mem_singleton_iff, and_congr_right_iff]
  intro huw
  rw [Sym2.eq_iff]
  constructor
  · intro hne hwv
    exact hne (Or.inl ⟨rfl, hwv⟩)
  · intro hwv hEq
    rcases hEq with h | h
    · exact hwv h.2
    · exact G.loopless.irrefl u (by simpa [h.2] using huw)

theorem degree_eraseEdge_left_add_one {u v : V} (huv : G.Adj u v) :
    (eraseEdge G u v).degree u + 1 = G.degree u := by
  classical
  rw [← (eraseEdge G u v).card_neighborFinset_eq_degree,
    ← G.card_neighborFinset_eq_degree, neighborFinset_eraseEdge_left huv]
  have hvsub : ({v} : Finset V) ⊆ G.neighborFinset u := by
    simpa using huv
  rw [Finset.card_sdiff_of_subset hvsub]
  have hcard : 1 ≤ (G.neighborFinset u).card :=
    Finset.card_le_card hvsub
  simp only [Finset.card_singleton]
  omega

theorem eraseEdge_comm (G : SimpleGraph V) (u v : V) :
    eraseEdge G u v = eraseEdge G v u := by
  simp only [eraseEdge]
  rw [Sym2.eq_swap]

theorem degree_eraseEdge_right_add_one {u v : V} (huv : G.Adj u v) :
    (eraseEdge G u v).degree v + 1 = G.degree v := by
  classical
  have hvu : G.Adj v u := huv.symm
  have hN' : (eraseEdge G u v).neighborFinset v = G.neighborFinset v \ {u} := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_sdiff,
      Finset.mem_singleton]
    change (G.deleteEdges {s(u, v)}).Adj v w ↔ G.Adj v w ∧ w ≠ u
    rw [SimpleGraph.deleteEdges_adj]
    simp only [Set.mem_singleton_iff, and_congr_right_iff]
    intro hvw
    rw [Sym2.eq_iff]
    constructor
    · intro hne hwu
      exact hne (Or.inr ⟨rfl, hwu⟩)
    · intro hwu hEq
      rcases hEq with h | h
      · exact G.loopless.irrefl v (h.2 ▸ hvw)
      · exact hwu h.2
  rw [← (eraseEdge G u v).card_neighborFinset_eq_degree,
    ← G.card_neighborFinset_eq_degree, hN']
  have husub : ({u} : Finset V) ⊆ G.neighborFinset v := by
    simpa using hvu
  rw [Finset.card_sdiff_of_subset husub]
  have hcard : 1 ≤ (G.neighborFinset v).card :=
    Finset.card_le_card husub
  simp only [Finset.card_singleton]
  omega

/-- If deleting an edge preserves three-connectivity, both of its endpoints
had degree at least four before deletion. -/
theorem four_le_degree_endpoints_of_eraseEdge_isThreeConnected
    {u v : V} (huv : G.Adj u v)
    (hdel : IsThreeConnected (eraseEdge G u v)) :
    4 ≤ G.degree u ∧ 4 ≤ G.degree v := by
  have hu := hdel.degree_ge u
  have hv := hdel.degree_ge v
  have heu := degree_eraseEdge_left_add_one (G := G) huv
  have hev := degree_eraseEdge_right_add_one (G := G) huv
  omega

/-! ## The Mader cycle property and its counting consequence -/

/-- Mader's cycle conclusion specialized to connectivity three. -/
def MaderCycleProperty (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ {r : V} (p : G.Walk r r), p.IsCycle →
    ∃ v ∈ p.support, G.degree v = 3

/-- The vertices of degree different from three induce a forest whenever
Mader's cycle conclusion holds. -/
theorem isAcyclic_induce_degree_ne_three
    (hM : MaderCycleProperty G) :
    (G.induce {v : V | G.degree v ≠ 3}).IsAcyclic := by
  intro r p hp
  let inc : (G.induce {v : V | G.degree v ≠ 3}) →g G :=
    (SimpleGraph.Embedding.induce
      (G := G) (s := {v : V | G.degree v ≠ 3})).toHom
  have hpMap : (p.map inc).IsCycle := hp.map Subtype.val_injective
  obtain ⟨v, hvp, hvdeg⟩ := hM (p.map inc) hpMap
  rw [Walk.support_map] at hvp
  obtain ⟨w, hwp, hwv⟩ := List.mem_map.mp hvp
  change w.1 = v at hwv
  apply w.property
  rw [hwv]
  exact hvdeg

/-- Conversely, acyclicity after deleting the degree-three vertices is
exactly Mader's assertion that every ambient cycle meets that set. -/
theorem maderCycleProperty_of_isAcyclic_induce_degree_ne_three
    (hacyc : (G.induce {v : V | G.degree v ≠ 3}).IsAcyclic) :
    MaderCycleProperty G := by
  intro r p hp
  by_contra hnone
  have hdeg (v : V) (hv : v ∈ p.support) : G.degree v ≠ 3 := by
    intro hvdeg
    exact hnone ⟨v, hv, hvdeg⟩
  let q := p.induce {v : V | G.degree v ≠ 3} hdeg
  let inc : (G.induce {v : V | G.degree v ≠ 3}) →g G :=
    (SimpleGraph.Embedding.induce
      (G := G) (s := {v : V | G.degree v ≠ 3})).toHom
  have hq : q.IsCycle := by
    have hqMap : (q.map inc).IsCycle := by
      simpa [q, inc] using hp
    exact hqMap.of_map
  exact hacyc q hq

theorem maderCycleProperty_iff_isAcyclic_induce_degree_ne_three :
    MaderCycleProperty G ↔
      (G.induce {v : V | G.degree v ≠ 3}).IsAcyclic :=
  ⟨isAcyclic_induce_degree_ne_three,
    maderCycleProperty_of_isAcyclic_induce_degree_ne_three⟩

/-- The exact finite Mader--Bollobás count for connectivity three.  Written
without division, it says `2|V| + 2 ≤ 5s`, where `s` is the number of
degree-three vertices. -/
theorem mader_degree_three_count
    (hthree : IsThreeConnected G)
    (hM : MaderCycleProperty G) :
    2 * Fintype.card V + 2 ≤
      5 * (Finset.univ.filter fun v : V ↦ G.degree v = 3).card := by
  classical
  let S : Finset V := Finset.univ.filter fun v : V ↦ G.degree v = 3
  let T : Finset V := Sᶜ
  let H : SimpleGraph {v : V // v ∈ T} := G.induce (T : Set V)
  have hHacyc : H.IsAcyclic := by
    let e : {v : V // v ∈ T} ≃ {v : V // G.degree v ≠ 3} :=
      Equiv.setCongr (by
        apply Set.ext
        intro v
        change (v ∈ T ↔ G.degree v ≠ 3)
        simp [T, S])
    let gi : H ≃g (G.induce {v : V | G.degree v ≠ 3}) :=
      { toEquiv := e
        map_rel_iff' := by intro u v; rfl }
    exact gi.isAcyclic_iff.mpr (isAcyclic_induce_degree_ne_three hM)
  have hTdeg (v : {v : V // v ∈ T}) : 4 ≤ G.degree v.1 := by
    have hmin := hthree.degree_ge v.1
    have hne : G.degree v.1 ≠ 3 := by simpa [T, S] using v.2
    omega
  have hDegreeLower : 4 * T.card ≤ ∑ v ∈ T, G.degree v := by
    calc
      4 * T.card = ∑ _v ∈ T, 4 := by simp [mul_comm]
      _ ≤ ∑ v ∈ T, G.degree v := by
        exact Finset.sum_le_sum fun v hv ↦ hTdeg ⟨v, hv⟩
  have hCrossUpper :
      ∑ v ∈ T, (G.neighborFinset v ∩ S).card ≤ 3 * S.card := by
    let B : SimpleGraph V := G.between (T : Set V) (S : Set V)
    have hdisj : Disjoint (T : Set V) (S : Set V) := by
      rw [Set.disjoint_left]
      intro v hvT hvS
      have : v ∉ T := by simpa [T] using hvS
      exact this hvT
    have hbip : B.IsBipartiteWith T S := by
      exact SimpleGraph.between_isBipartiteWith hdisj
    have hBT (v : V) (hv : v ∈ T) :
        B.degree v = (G.neighborFinset v ∩ S).card := by
      rw [← B.card_neighborFinset_eq_degree]
      congr 1
      ext w
      have hvS : v ∉ S := by
        intro hv'
        exact Set.disjoint_left.1 hdisj hv hv'
      simp [B, SimpleGraph.between_adj, hv, hvS]
    have hBS (v : V) (hv : v ∈ S) :
        B.degree v = (G.neighborFinset v ∩ T).card := by
      rw [← B.card_neighborFinset_eq_degree]
      congr 1
      ext w
      have hvT : v ∉ T := by
        intro hv'
        exact Set.disjoint_left.1 hdisj hv' hv
      simp [B, SimpleGraph.between_adj, hv, hvT, G.adj_comm]
    have hswap :
        ∑ v ∈ T, (G.neighborFinset v ∩ S).card =
          ∑ v ∈ S, (G.neighborFinset v ∩ T).card := by
      calc
        ∑ v ∈ T, (G.neighborFinset v ∩ S).card =
            ∑ v ∈ T, B.degree v := by
              apply Finset.sum_congr rfl
              intro v hv
              exact (hBT v hv).symm
        _ = ∑ v ∈ S, B.degree v :=
          SimpleGraph.isBipartiteWith_sum_degrees_eq hbip
        _ = ∑ v ∈ S, (G.neighborFinset v ∩ T).card := by
              apply Finset.sum_congr rfl
              intro v hv
              exact hBS v hv
    rw [hswap]
    calc
      ∑ v ∈ S, (G.neighborFinset v ∩ T).card ≤
          ∑ _v ∈ S, 3 := by
            apply Finset.sum_le_sum
            intro v hv
            have hvdeg : G.degree v = 3 := by simpa [S] using hv
            rw [← hvdeg, ← G.card_neighborFinset_eq_degree]
            exact Finset.card_le_card (Finset.inter_subset_left)
      _ = 3 * S.card := by simp [mul_comm]
  by_cases hT : T = ∅
  · have hSuniv : S = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro v
      by_contra hv
      have hvT : v ∈ T := by simp [T, hv]
      rw [hT] at hvT
      simpa using hvT
    change 2 * Fintype.card V + 2 ≤ 5 * S.card
    simp [hSuniv]
    have := hthree.four_le_card
    omega
  · have hTpos : 0 < T.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hT)
    have hForest : H.edgeFinset.card + 1 ≤ T.card := by
      obtain ⟨z, hz⟩ := Finset.card_pos.mp hTpos
      letI : Nonempty {v : V // v ∈ T} := ⟨⟨z, hz⟩⟩
      obtain ⟨F, hHF, -, hFtree⟩ :=
        (SimpleGraph.connected_top (V := {v : V // v ∈ T})).exists_isTree_le_of_le_of_isAcyclic
          (G := ⊤) (H := H) le_top hHacyc
      have hedge : H.edgeFinset.card ≤ F.edgeFinset.card :=
        Finset.card_mono (SimpleGraph.edgeFinset_mono hHF)
      have htree := hFtree.card_edgeFinset
      have hSubtypeCard : Fintype.card {v : V // v ∈ T} = T.card := by simp
      rw [hSubtypeCard] at htree
      omega
    have hInternal (v : V) (hv : v ∈ T) :
        H.degree ⟨v, hv⟩ = (G.neighborFinset v ∩ T).card := by
      let val : {v : V // v ∈ T} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
      have heq : (H.neighborFinset ⟨v, hv⟩).map val =
          G.neighborFinset v ∩ T := by
        ext w
        simp [H, val]
      have hcard := congrArg Finset.card heq
      simpa using hcard
    have hDegreeSplit :
        ∑ v ∈ T, G.degree v =
          2 * H.edgeFinset.card +
            ∑ v ∈ T, (G.neighborFinset v ∩ S).card := by
      have hpartition (v : V) (hv : v ∈ T) :
          G.degree v = (G.neighborFinset v ∩ T).card +
            (G.neighborFinset v ∩ S).card := by
        rw [← G.card_neighborFinset_eq_degree, ← Finset.card_union_of_disjoint]
        · congr 1
          ext w
          by_cases hw : w ∈ S
          · have hwT : w ∉ T := by simp [T, hw]
            simp [hw, hwT]
          · have hwT : w ∈ T := by simp [T, hw]
            simp [hw, hwT]
        · apply Finset.disjoint_left.2
          intro w hwT hwS
          have hwT' : w ∈ T := (Finset.mem_inter.mp hwT).2
          have hwS' : w ∈ S := (Finset.mem_inter.mp hwS).2
          have : w ∉ T := by simpa [T] using hwS'
          exact this hwT'
      calc
        ∑ v ∈ T, G.degree v =
            ∑ v ∈ T, ((G.neighborFinset v ∩ T).card +
              (G.neighborFinset v ∩ S).card) := by
                apply Finset.sum_congr rfl
                intro v hv
                exact hpartition v hv
        _ = (∑ v ∈ T, (G.neighborFinset v ∩ T).card) +
              ∑ v ∈ T, (G.neighborFinset v ∩ S).card := by
                simp only [Finset.sum_add_distrib]
        _ = (∑ v : {v : V // v ∈ T}, H.degree v) +
              ∑ v ∈ T, (G.neighborFinset v ∩ S).card := by
                congr 1
                rw [← Finset.sum_attach]
                apply Finset.sum_congr rfl
                intro v hv
                exact (hInternal v.1 v.2).symm
        _ = 2 * H.edgeFinset.card +
              ∑ v ∈ T, (G.neighborFinset v ∩ S).card := by
                rw [H.sum_degrees_eq_twice_card_edges]
    have hMain : 4 * T.card ≤ 2 * H.edgeFinset.card + 3 * S.card := by
      rw [hDegreeSplit] at hDegreeLower
      exact hDegreeLower.trans (Nat.add_le_add_left hCrossUpper _)
    have hST : S.card + T.card = Fintype.card V := by simp [T]
    change 2 * Fintype.card V + 2 ≤ 5 * S.card
    omega

/-- In particular, a minimally three-connected graph satisfying Mader's
cycle conclusion has at least three degree-three vertices once it has at
least five vertices. -/
theorem three_le_card_degree_eq_three_of_five_le
    (hcard : 5 ≤ Fintype.card V)
    (hthree : IsThreeConnected G)
    (hM : MaderCycleProperty G) :
    3 ≤ (Finset.univ.filter fun v : V ↦ G.degree v = 3).card := by
  have hcount := mader_degree_three_count hthree hM
  omega

end Erdos916
