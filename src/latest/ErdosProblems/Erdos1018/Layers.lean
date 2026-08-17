import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Paths

open scoped BigOperators

namespace Erdos1018Aux

open SimpleGraph

universe u

variable {V : Type u} [Fintype V]
variable (G : SimpleGraph V)

noncomputable def boolColoringOfBipartite (hG : G.IsBipartite) : G.Coloring Bool :=
  SimpleGraph.recolorOfEquiv G finTwoEquiv hG.some

lemma dist_ne_of_adj_of_isBipartite_connected (hG : G.IsBipartite) (hconn : G.Connected)
    (r : V) {v w : V} (hvw : G.Adj v w) : G.dist r v ≠ G.dist r w := by
  intro hd
  let c : G.Coloring Bool := boolColoringOfBipartite G hG
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist r v
  obtain ⟨q, hq⟩ := hconn.exists_walk_length_eq_dist r w
  have hEven : Even p.length ↔ Even q.length := by simp [hp, hq, hd]
  by_cases hep : Even p.length
  · have heq : Even q.length := hEven.mp hep
    have hpcol : c r ↔ c v := (c.even_length_iff_congr p).mp hep
    have hqcol : c r ↔ c w := (c.even_length_iff_congr q).mp heq
    exact c.valid hvw (Bool.eq_iff_iff.mpr (hpcol.symm.trans hqcol))
  · have hop : Odd p.length := Nat.not_even_iff_odd.mp hep
    have hoq : Odd q.length := Nat.not_even_iff_odd.mp (fun h ↦ hep (hEven.mpr h))
    have hpcol : ¬c r ↔ c v := (c.odd_length_iff_not_congr p).mp hop
    have hqcol : ¬c r ↔ c w := (c.odd_length_iff_not_congr q).mp hoq
    exact c.valid hvw (Bool.eq_iff_iff.mpr (hpcol.symm.trans hqcol))

lemma adj_dist_consecutive (hG : G.IsBipartite) (hconn : G.Connected) (r : V)
    {v w : V} (hvw : G.Adj v w) :
    G.dist r v = G.dist r w + 1 ∨ G.dist r w = G.dist r v + 1 := by
  have hne := dist_ne_of_adj_of_isBipartite_connected G hG hconn r hvw
  grind [SimpleGraph.Adj.diff_dist_adj]

noncomputable def edgeLevel (r : V) (e : Sym2 V) : ℕ :=
  Sym2.lift ⟨fun v w ↦ min (G.dist r v) (G.dist r w), fun _ _ ↦ min_comm _ _⟩ e

@[simp] lemma edgeLevel_s(v w : V) (r : V) :
    edgeLevel G r s(v, w) = min (G.dist r v) (G.dist r w) := by
  simp [edgeLevel]

noncomputable def layer (r : V) (i : ℕ) : Finset V :=
  Finset.univ.filter fun v ↦ G.dist r v = i

noncomputable def pairedLayers (r : V) (i : ℕ) : Finset V := by
  classical
  exact layer G r i ∪ layer G r (i + 1)

@[simp] lemma mem_layer_iff (r : V) (i : ℕ) (v : V) :
    v ∈ layer G r i ↔ G.dist r v = i := by
  simp [layer]

@[simp] lemma mem_pairedLayers_iff (r : V) (i : ℕ) (v : V) :
    v ∈ pairedLayers G r i ↔ G.dist r v = i ∨ G.dist r v = i + 1 := by
  simp [pairedLayers]

lemma dist_lt_card (hconn : G.Connected) (r v : V) : G.dist r v < Fintype.card V := by
  obtain ⟨p, hp, hlen⟩ := (hconn r v).exists_path_of_dist
  rw [← hlen]
  exact hp.length_lt

lemma edgeLevel_lt_card (hconn : G.Connected) (r : V) (e : Sym2 V) :
    edgeLevel G r e < Fintype.card V := by
  induction e using Sym2.ind with
  | _ v w =>
      simp only [edgeLevel_s]
      exact (min_lt_iff.mpr (Or.inl (dist_lt_card G hconn r v)))

lemma sum_edgeLevel_fibers (hconn : G.Connected) [DecidableRel G.Adj] (r : V) :
    ∑ i ∈ Finset.range (Fintype.card V),
        ((G.edgeFinset.filter fun e ↦ edgeLevel G r e = i).card) = G.edgeFinset.card := by
  classical
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simp [edgeLevel_lt_card G hconn]

private lemma sum_two_neighbor_indicators_le_two (n d : ℕ) :
    (∑ i ∈ Finset.range n, if d = i ∨ d = i + 1 then (1 : ℕ) else 0) ≤ 2 := by
  calc
    (∑ i ∈ Finset.range n, if d = i ∨ d = i + 1 then (1 : ℕ) else 0)
        ≤ ∑ i ∈ Finset.range n,
            ((if d = i then (1 : ℕ) else 0) + (if d = i + 1 then 1 else 0)) := by
          apply Finset.sum_le_sum
          intro i hi
          split_ifs <;> omega
    _ = (∑ i ∈ Finset.range n, if d = i then (1 : ℕ) else 0) +
          ∑ i ∈ Finset.range n, if d = i + 1 then (1 : ℕ) else 0 := by
          rw [Finset.sum_add_distrib]
    _ ≤ 1 + 1 := Nat.add_le_add (by
          by_cases hdn : d < n <;> simp [hdn]) (by
          rw [← Finset.card_filter]
          apply Finset.card_le_one.mpr
          intro a ha b hb
          simp only [Finset.mem_filter] at ha hb
          omega)
    _ = 2 := by omega

lemma sum_pairedLayers_card_le (r : V) :
    (∑ i ∈ Finset.range (Fintype.card V), (pairedLayers G r i).card) ≤
      2 * Fintype.card V := by
  classical
  calc
    (∑ i ∈ Finset.range (Fintype.card V), (pairedLayers G r i).card)
        = ∑ i ∈ Finset.range (Fintype.card V),
            ∑ v ∈ Finset.univ, if v ∈ pairedLayers G r i then (1 : ℕ) else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.card_eq_sum_ones]
              rw [← Finset.sum_filter]
              congr 1
              ext v
              simp
    _ = ∑ v ∈ Finset.univ, ∑ i ∈ Finset.range (Fintype.card V),
          if v ∈ pairedLayers G r i then (1 : ℕ) else 0 := by
            rw [Finset.sum_comm]
    _ ≤ ∑ v ∈ Finset.univ, 2 := by
          apply Finset.sum_le_sum
          intro v hv
          simpa using sum_two_neighbor_indicators_le_two (Fintype.card V) (G.dist r v)
    _ = 2 * Fintype.card V := by simp [Nat.mul_comm]

lemma edge_mem_pairedLayers_sym2 (hG : G.IsBipartite) (hconn : G.Connected)
    [DecidableRel G.Adj] (r : V) {e : Sym2 V} {i : ℕ}
    (he : e ∈ G.edgeFinset) (hlevel : edgeLevel G r e = i) :
    e ∈ (pairedLayers G r i).sym2 := by
  induction e using Sym2.ind with
  | _ v w =>
      have hadj : G.Adj v w := by simpa using he
      have hcons := adj_dist_consecutive G hG hconn r hadj
      simp only [edgeLevel_s] at hlevel
      rw [Finset.mem_sym2_iff, Sym2.forall_mem_pair]
      simp only [mem_pairedLayers_iff]
      rcases hcons with hcons | hcons <;> omega

noncomputable def pairedGraph (r : V) (i : ℕ) :
    SimpleGraph (pairedLayers G r i) :=
  G.induce (pairedLayers G r i : Set V)

lemma edgeBucket_card_le_pairedGraph (hG : G.IsBipartite) (hconn : G.Connected)
    [DecidableRel G.Adj] (r : V) (i : ℕ) :
    (G.edgeFinset.filter fun e ↦ edgeLevel G r e = i).card ≤
      (pairedGraph G r i).edgeSet.ncard := by
  classical
  let S : Set V := pairedLayers G r i
  letI : Fintype S := Fintype.ofFinite S
  change (G.edgeFinset.filter fun e ↦ edgeLevel G r e = i).card ≤
    (G.induce S).edgeSet.ncard
  have hsub : (G.edgeFinset.filter fun e ↦ edgeLevel G r e = i) ⊆
      G.edgeFinset ∩ S.toFinset.sym2 := by
    intro e he
    rw [Finset.mem_inter]
    refine ⟨(Finset.mem_filter.mp he).1, ?_⟩
    simpa [S] using edge_mem_pairedLayers_sym2 G hG hconn r
      (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2
  calc
    (G.edgeFinset.filter fun e ↦ edgeLevel G r e = i).card
        ≤ (G.edgeFinset ∩ S.toFinset.sym2).card := Finset.card_le_card hsub
    _ = ((G.induce S).edgeFinset.map
          (Function.Embedding.subtype (fun v ↦ v ∈ S)).sym2Map).card := by
            convert congrArg Finset.card
              (SimpleGraph.map_edgeFinset_induce (G := G) (s := S)).symm using 1 <;>
                apply congrArg Finset.card <;> ext e <;> simp
    _ = (pairedGraph G r i).edgeSet.ncard := by
          rw [Finset.card_map]
          rw [SimpleGraph.edgeFinset_card]
          change Fintype.card (G.induce S).edgeSet = _
          rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
          rfl

private lemma exists_weighted_average
    {ι : Type*} (s : Finset ι) (a b : ι → ℕ) (e n : ℕ)
    (hs : s.Nonempty) (ha : ∑ i ∈ s, a i = e)
    (hb : (∑ i ∈ s, b i) ≤ 2 * n) :
    ∃ i ∈ s, e * b i ≤ 2 * a i * n := by
  by_contra h
  push Not at h
  have hlt : (∑ i ∈ s, 2 * a i * n) < ∑ i ∈ s, e * b i := by
    exact Finset.sum_lt_sum (fun i hi ↦ (h i hi).le) ⟨hs.choose, hs.choose_spec, h _ hs.choose_spec⟩
  have hleft : (∑ i ∈ s, 2 * a i * n) = 2 * e * n := by
    rw [← ha]
    simp only [Finset.mul_sum, Finset.sum_mul]
  have hright : (∑ i ∈ s, e * b i) = e * (∑ i ∈ s, b i) := by
    rw [Finset.mul_sum]
  have hcontra : 2 * e * n < e * (2 * n) := calc
    2 * e * n = ∑ i ∈ s, 2 * a i * n := hleft.symm
    _ < ∑ i ∈ s, e * b i := hlt
    _ = e * (∑ i ∈ s, b i) := hright
    _ ≤ e * (2 * n) := Nat.mul_le_mul_left e hb
  have hirr : 2 * e * n < 2 * e * n := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hcontra
  exact (Nat.lt_irrefl _ hirr)

private lemma exists_weighted_average_pos
    {ι : Type*} (s : Finset ι) (a b : ι → ℕ) (e n : ℕ)
    (he : 0 < e) (ha : ∑ i ∈ s, a i = e)
    (hb : (∑ i ∈ s, b i) ≤ 2 * n) :
    ∃ i ∈ s, 0 < a i ∧ e * b i ≤ 2 * a i * n := by
  classical
  let t := s.filter fun i ↦ 0 < a i
  have hta : ∑ i ∈ t, a i = e := by
    rw [← ha]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i his hit
    have : ¬ 0 < a i := by simpa [t, his] using hit
    omega
  have htb : (∑ i ∈ t, b i) ≤ 2 * n := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ ↦ Nat.zero_le _)).trans hb
  have ht : t.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hta
    simp at hta
    omega
  obtain ⟨i, hit, havg⟩ := exists_weighted_average t a b e n ht hta htb
  exact ⟨i, (Finset.mem_filter.mp hit).1, (Finset.mem_filter.mp hit).2, havg⟩

theorem exists_pairedLayers_half_average (hG : G.IsBipartite) (hconn : G.Connected)
    [DecidableRel G.Adj] (r : V) :
    ∃ i < Fintype.card V,
      G.edgeFinset.card * (pairedLayers G r i).card ≤
        2 * (pairedGraph G r i).edgeSet.ncard * Fintype.card V := by
  classical
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hconn.nonempty
  obtain ⟨i, hi, havg⟩ := exists_weighted_average
    (Finset.range (Fintype.card V))
    (fun i ↦ (G.edgeFinset.filter fun e ↦ edgeLevel G r e = i).card)
    (fun i ↦ (pairedLayers G r i).card)
    G.edgeFinset.card (Fintype.card V)
    ⟨0, Finset.mem_range.mpr hn⟩
    (sum_edgeLevel_fibers G hconn r)
    (sum_pairedLayers_card_le G r)
  refine ⟨i, Finset.mem_range.mp hi, ?_⟩
  exact havg.trans (by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      Nat.mul_le_mul_right (2 * Fintype.card V)
        (edgeBucket_card_le_pairedGraph G hG hconn r i))

theorem exists_nonempty_pairedLayers_half_average
    (hG : G.IsBipartite) (hconn : G.Connected) [DecidableRel G.Adj]
    (hE : 0 < G.edgeFinset.card) (r : V) :
    ∃ i < Fintype.card V, (pairedLayers G r i).Nonempty ∧
      G.edgeFinset.card * (pairedLayers G r i).card ≤
        2 * (pairedGraph G r i).edgeSet.ncard * Fintype.card V := by
  classical
  obtain ⟨i, hi, hbucket, havg⟩ := exists_weighted_average_pos
    (Finset.range (Fintype.card V))
    (fun i ↦ (G.edgeFinset.filter fun e ↦ edgeLevel G r e = i).card)
    (fun i ↦ (pairedLayers G r i).card)
    G.edgeFinset.card (Fintype.card V) hE
    (sum_edgeLevel_fibers G hconn r)
    (sum_pairedLayers_card_le G r)
  have hpair : (pairedLayers G r i).Nonempty := by
    obtain ⟨e, he⟩ := Finset.card_pos.mp hbucket
    have hemem := edge_mem_pairedLayers_sym2 G hG hconn r
      (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2
    induction e using Sym2.ind with
    | _ v w =>
        refine ⟨v, (Finset.mem_sym2_iff.mp hemem) v ?_⟩
        exact Sym2.mem_mk_left v w
  refine ⟨i, Finset.mem_range.mp hi, hpair, ?_⟩
  exact havg.trans (by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      Nat.mul_le_mul_right (2 * Fintype.card V)
        (edgeBucket_card_le_pairedGraph G hG hconn r i))

end Erdos1018Aux

namespace Erdos1018Aux

open SimpleGraph

universe u

variable {V : Type u} [Fintype V]

/-- This is definitionally the same shape as `Erdos1018.hostLayer`. -/
def hostLayer {G : SimpleGraph V} (J : G.Subgraph) (z : J.verts)
    (k : ℕ) : Set V :=
  {x | ∃ hx : x ∈ J.verts, J.coe.dist z ⟨x, hx⟩ = k}

lemma edgeSet_ncard_coe {G : SimpleGraph V} (J : G.Subgraph) :
    J.edgeSet.ncard = J.coe.edgeSet.ncard := by
  rw [← J.image_coe_edgeSet_coe]
  exact Set.ncard_image_of_injective _
    (Sym2.map.injective Subtype.val_injective)

lemma edgeFinset_card_eq_edgeSet_ncard {G : SimpleGraph V} (J : G.Subgraph)
    [Fintype J.verts] [DecidableRel J.coe.Adj] :
    J.coe.edgeFinset.card = J.edgeSet.ncard := by
  rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset,
    ← edgeSet_ncard_coe J]

lemma hostLayer_pair_preimage {G : SimpleGraph V} (J : G.Subgraph)
    [Fintype J.verts] (z : J.verts) (k : ℕ) :
    {x : J.verts | (x : V) ∈ hostLayer J z k ∪ hostLayer J z (k + 1)} =
      (Erdos1018Aux.pairedLayers J.coe z k : Set J.verts) := by
  ext x
  change ((∃ hx : (x : V) ∈ J.verts, J.coe.dist z ⟨x, hx⟩ = k) ∨
      (∃ hx : (x : V) ∈ J.verts, J.coe.dist z ⟨x, hx⟩ = k + 1)) ↔
    x ∈ Erdos1018Aux.pairedLayers J.coe z k
  rw [Erdos1018Aux.mem_pairedLayers_iff]
  constructor
  · rintro (⟨hx, hdist⟩ | ⟨hx, hdist⟩)
    · left
      simpa using hdist
    · right
      simpa using hdist
  · rintro (hdist | hdist)
    · exact Or.inl ⟨x.property, by simpa using hdist⟩
    · exact Or.inr ⟨x.property, by simpa using hdist⟩

lemma hostLayer_pair_subset_verts {G : SimpleGraph V} (J : G.Subgraph)
    (z : J.verts) (k : ℕ) :
    hostLayer J z k ∪ hostLayer J z (k + 1) ⊆ J.verts := by
  rintro x (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx

theorem exists_host_pairedLayers_half_average
    {G : SimpleGraph V} (J : G.Subgraph)
    (hconn : J.coe.Connected) (hbip : J.coe.IsBipartite)
    (hE : 0 < J.edgeSet.ncard) (z : J.verts) :
    ∃ k < J.verts.ncard,
      let K := J.induce (hostLayer J z k ∪ hostLayer J z (k + 1))
      K.verts.Nonempty ∧
        J.edgeSet.ncard * K.verts.ncard ≤
          2 * K.edgeSet.ncard * J.verts.ncard := by
  classical
  letI : Fintype J.verts := Fintype.ofFinite J.verts
  letI : DecidableRel J.coe.Adj := Classical.decRel _
  have hEcoe : 0 < J.coe.edgeFinset.card := by
    rw [edgeFinset_card_eq_edgeSet_ncard J]
    exact hE
  obtain ⟨k, hk, hpair, havg⟩ :=
    Erdos1018Aux.exists_nonempty_pairedLayers_half_average
      J.coe hbip hconn hEcoe z
  let P := Erdos1018Aux.pairedLayers J.coe z k
  let U := hostLayer J z k ∪ hostLayer J z (k + 1)
  let K := J.induce U
  have hU : U ⊆ J.verts := hostLayer_pair_subset_verts J z k
  have hpre : {x : J.verts | (x : V) ∈ U} = (P : Set J.verts) := by
    simpa [U, P] using hostLayer_pair_preimage J z k
  have hJverts : Fintype.card J.verts = J.verts.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hKverts : K.verts.ncard = P.card := by
    change Nat.card K.verts = P.card
    calc
      Nat.card K.verts = Nat.card {x : J.verts | (x : V) ∈ U} :=
        Nat.card_congr (J.coeInduceIso U hU).toEquiv
      _ = {x : J.verts | (x : V) ∈ U}.ncard :=
        Nat.card_coe_set_eq {x : J.verts | (x : V) ∈ U}
      _ = (P : Set J.verts).ncard := congrArg Set.ncard hpre
      _ = P.card := Set.ncard_coe_finset P
  have hKedges : K.edgeSet.ncard =
      (Erdos1018Aux.pairedGraph J.coe z k).edgeSet.ncard := by
    calc
      K.edgeSet.ncard = K.coe.edgeSet.ncard := edgeSet_ncard_coe K
      _ = (J.coe.induce {x : J.verts | (x : V) ∈ U}).edgeSet.ncard := by
        exact Nat.card_congr (J.coeInduceIso U hU).mapEdgeSet
      _ = (Erdos1018Aux.pairedGraph J.coe z k).edgeSet.ncard := by
        rw [hpre]
        rfl
  refine ⟨k, ?_, ?_⟩
  · simpa [hJverts] using hk
  dsimp only
  change K.verts.Nonempty ∧
    J.edgeSet.ncard * K.verts.ncard ≤ 2 * K.edgeSet.ncard * J.verts.ncard
  constructor
  · obtain ⟨x, hx⟩ := hpair
    refine ⟨(x : V), ?_⟩
    change (x : V) ∈ U
    have : x ∈ {y : J.verts | (y : V) ∈ U} := by
      rw [hpre]
      exact hx
    exact this
  · rw [edgeFinset_card_eq_edgeSet_ncard J, ← hKverts, ← hKedges,
      hJverts] at havg
    exact havg

end Erdos1018Aux
