/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos641.DenseFree

/-!
# The deterministic JSS obstruction

The probabilistic input is only the absence of a small dense strict prefix.
This file proves that a nonempty 4-regular subgraph would create precisely
such a prefix.
-/

open Finset Fintype Filter
open scoped BigOperators Classical

namespace Erdos641

open SimpleGraph
open Erdos182

noncomputable section

/-- Vertices strictly after layer `i`. -/
def jssStrictTail (n : ℕ) (i : Fin (prsLayerCount n)) :
    Finset (JSSVertex n) :=
  Finset.univ.filter fun v ↦ i < v.1

@[simp] lemma mem_jssStrictTail {n : ℕ} {i : Fin (prsLayerCount n)}
    {v : JSSVertex n} : v ∈ jssStrictTail n i ↔ i < v.1 := by
  simp [jssStrictTail]

/-- The three layer regions form a partition of the vertex type. -/
lemma jss_prefix_layer_tail_cover (n : ℕ) (i : Fin (prsLayerCount n)) :
    (Finset.univ : Finset (JSSVertex n)) ⊆
      jssPrefix n i ∪ jssLayer n i ∪ jssStrictTail n i := by
  intro v _hv
  simp only [Finset.mem_union, mem_jssPrefix, mem_jssLayer_iff,
    mem_jssStrictTail]
  omega

/-- Counting the sigma type layer by layer gives the cardinality of a
strict tail. -/
lemma card_jssStrictTail (n : ℕ) (i : Fin (prsLayerCount n)) :
    (jssStrictTail n i).card =
      ∑ j ∈ Finset.Ico (i.val + 1) (prsLayerCount n), prsLayerSize n j := by
  classical
  calc
    (jssStrictTail n i).card =
        ∑ v : JSSVertex n, if i < v.1 then 1 else 0 := by
      simp [jssStrictTail]
    _ = ∑ j : Fin (prsLayerCount n),
          ∑ _x : Fin (prsLayerSize n j), if i.val < j.val then 1 else 0 := by
      rw [Fintype.sum_sigma]
      rfl
    _ = ∑ j : Fin (prsLayerCount n),
          if i.val < j.val then prsLayerSize n j else 0 := by
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases h : i.val < j.val <;> simp [h]
    _ = ∑ j ∈ Finset.range (prsLayerCount n),
          if i.val < j then prsLayerSize n j else 0 := by
      exact Fin.sum_univ_eq_sum_range
        (fun j ↦ if i.val < j then prsLayerSize n j else 0)
        (prsLayerCount n)
    _ = ∑ j ∈ Finset.Ico (i.val + 1) (prsLayerCount n),
          prsLayerSize n j := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext j
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      · intro j _hj
        rfl

/-- Every edge of the JSS graph joins distinct layers. -/
lemma no_jssGraph_edge_inside_layer {n : ℕ} {ω : JSSOutcome n}
    {hω : ω ∈ jssOutcomeSpace n} {i : Fin (prsLayerCount n)}
    {u v : JSSVertex n} (hu : u.1 = i) (hv : v.1 = i) :
    ¬ (jssGraph ω hω).Adj u v := by
  intro huv
  rcases layer_lt_or_gt_of_jssGraph_adj huv with h | h <;> omega

/-! ## Elementary finite edge regions

These helpers are kept local to the Problem 641 development so that the
proof is source-complete and does not depend on a cached auxiliary module.
-/

/-- Edges whose two endpoints lie in `S`. -/
def layeredEdgesInside {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) :=
  K.edgeFinset.filter fun e ↦ ∀ v ∈ e.toFinset, v ∈ S

@[simp] lemma mem_layeredEdgesInside {V : Type*} [Fintype V]
    [DecidableEq V] {K : SimpleGraph V} {S : Finset V} {e : Sym2 V} :
    e ∈ layeredEdgesInside K S ↔
      e ∈ K.edgeFinset ∧ ∀ v ∈ e.toFinset, v ∈ S := by
  simp [layeredEdgesInside]

/-- Edges with at least one endpoint in `S`. -/
def layeredEdgesMeeting {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) :=
  K.edgeFinset.filter fun e ↦ ∃ v ∈ e.toFinset, v ∈ S

@[simp] lemma mem_layeredEdgesMeeting {V : Type*} [Fintype V]
    [DecidableEq V] {K : SimpleGraph V} {S : Finset V} {e : Sym2 V} :
    e ∈ layeredEdgesMeeting K S ↔
      e ∈ K.edgeFinset ∧ ∃ v ∈ e.toFinset, v ∈ S := by
  simp [layeredEdgesMeeting]

/-- Charging an edge meeting `S` to one incident vertex bounds their number
by the sum of the degrees on `S`. -/
lemma card_layeredEdgesMeeting_le_sum_degree {V : Type*} [Fintype V]
    [DecidableEq V] (K : SimpleGraph V) (S : Finset V) :
    (layeredEdgesMeeting K S).card ≤ ∑ v ∈ S, K.degree v := by
  classical
  have hsub : layeredEdgesMeeting K S ⊆
      S.biUnion fun v ↦ K.incidenceFinset v := by
    intro e he
    obtain ⟨heK, v, hve, hvS⟩ := mem_layeredEdgesMeeting.mp he
    apply Finset.mem_biUnion.mpr
    refine ⟨v, hvS, ?_⟩
    rw [SimpleGraph.mem_incidenceFinset]
    constructor
    · exact SimpleGraph.mem_edgeFinset.mp heK
    · simpa using hve
  calc
    (layeredEdgesMeeting K S).card ≤
        (S.biUnion fun v ↦ K.incidenceFinset v).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ v ∈ S, (K.incidenceFinset v).card := Finset.card_biUnion_le
    _ = ∑ v ∈ S, K.degree v := by simp

/-- Unpack a support-sensitive regular subgraph as a spanning coefficient
graph on the ambient vertex type. -/
lemma exists_supportedRegular_of_containsRegularSubgraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {k : ℕ} (hk : 0 < k)
    (hcontains : ContainsRegularSubgraph G k) :
    ∃ K : SimpleGraph V, K ≤ G ∧ K.support.Nonempty ∧
      ∀ v ∈ K.support, K.degree v = k := by
  classical
  obtain ⟨H, hHne, hHreg⟩ := hcontains
  let f : H.verts ↪ V := Function.Embedding.subtype _
  let K : SimpleGraph V := H.coe.map f
  have hKG : K ≤ G := by
    intro a b hab
    obtain ⟨_hne, x, y, hxy, hxa, hyb⟩ := hab
    subst a
    subst b
    exact H.adj_sub hxy
  have hKne : K.support.Nonempty := by
    obtain ⟨v, hv⟩ := hHne
    let vH : H.verts := ⟨v, hv⟩
    have hvDegree : H.coe.degree vH = k := by
      rw [← SimpleGraph.card_neighborSet_eq_degree,
        Set.fintypeCard_eq_ncard]
      exact hHreg vH
    have hvSupport : vH ∈ H.coe.support := by
      rw [← SimpleGraph.degree_pos_iff_mem_support, hvDegree]
      exact hk
    change (H.coe.map f).support.Nonempty
    rw [SimpleGraph.support_map]
    exact ⟨f vH, vH, hvSupport, rfl⟩
  refine ⟨K, hKG, hKne, ?_⟩
  intro w hw
  change w ∈ (H.coe.map f).support at hw
  rw [SimpleGraph.support_map] at hw
  obtain ⟨v, hv, hvw⟩ := hw
  subst w
  rw [show K = H.coe.map f by rfl]
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    Set.fintypeCard_eq_ncard,
    SimpleGraph.neighborSet_map,
    Set.ncard_image_of_injective _ f.injective]
  exact hHreg v

section EdgeCounts

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A degree sum over an ambient region may be restricted to the support. -/
lemma sum_degrees_eq_inter_support (K : SimpleGraph V) (A : Finset V) :
    ∑ v ∈ A, K.degree v = ∑ v ∈ K.support.toFinset ∩ A, K.degree v := by
  classical
  symm
  apply Finset.sum_subset
  · exact Finset.inter_subset_right
  · intro v hvA hvNot
    have hvNotSupport : v ∉ K.support := by
      intro hvSupport
      exact hvNot (Finset.mem_inter.mpr ⟨Set.mem_toFinset.mpr hvSupport, hvA⟩)
    exact (K.degree_eq_zero_iff_notMem_support v).mpr hvNotSupport

/-- If `H ≤ K`, a degree sum for `H` may be restricted to the support of
`K`. -/
lemma sum_degrees_eq_inter_support_of_le (H K : SimpleGraph V) (hHK : H ≤ K)
    (A : Finset V) :
    ∑ v ∈ A, H.degree v = ∑ v ∈ K.support.toFinset ∩ A, H.degree v := by
  classical
  symm
  apply Finset.sum_subset
  · exact Finset.inter_subset_right
  · intro v hvA hvNot
    have hvNotSupport : v ∉ K.support := by
      intro hvSupport
      exact hvNot (Finset.mem_inter.mpr ⟨Set.mem_toFinset.mpr hvSupport, hvA⟩)
    have hKzero : K.degree v = 0 :=
      (K.degree_eq_zero_iff_notMem_support v).mpr hvNotSupport
    have hle : H.degree v ≤ K.degree v := H.degree_le_of_le hHK
    omega

end EdgeCounts

/-- The edges of `K` running between the strict prefix and layer `i`. -/
def jssCross {n : ℕ} (K : SimpleGraph (JSSVertex n))
    (i : Fin (prsLayerCount n)) : SimpleGraph (JSSVertex n) :=
  K.between (jssPrefix n i : Set (JSSVertex n))
    (jssLayer n i : Set (JSSVertex n))

lemma jssCross_isBipartiteWith {n : ℕ} (K : SimpleGraph (JSSVertex n))
    (i : Fin (prsLayerCount n)) :
    (jssCross K i).IsBipartiteWith
      (jssPrefix n i : Set (JSSVertex n))
      (jssLayer n i : Set (JSSVertex n)) := by
  apply SimpleGraph.between_isBipartiteWith
  rw [Set.disjoint_left]
  intro v hvp hvl
  have hvlt := mem_jssPrefix.mp hvp
  have hveq := mem_jssLayer_iff.mp hvl
  omega

/-- On the prefix side, the JSS uniqueness rule bounds every cross-degree by
one. -/
lemma jssCross_degree_le_one {n : ℕ} {ω : JSSOutcome n}
    {hω : ω ∈ jssOutcomeSpace n} {K : SimpleGraph (JSSVertex n)}
    (hKG : K ≤ jssGraph ω hω) (i : Fin (prsLayerCount n))
    {u : JSSVertex n} (hu : u ∈ jssPrefix n i) :
    (jssCross K i).degree u ≤ 1 := by
  classical
  rw [← (jssCross K i).card_neighborFinset_eq_degree]
  apply Finset.card_le_one.mpr
  intro v hv w hw
  have huv := ((jssCross K i).mem_neighborFinset u v).mp hv
  have huw := ((jssCross K i).mem_neighborFinset u w).mp hw
  rw [jssCross, SimpleGraph.between_adj] at huv huw
  have hvLayer : v.1 = i := by
    rcases huv.2 with ⟨_huPrefix, hvMiddle⟩ | ⟨huMiddle, _hvPrefix⟩
    · exact mem_jssLayer_iff.mp hvMiddle
    · have huLayer := mem_jssLayer_iff.mp huMiddle
      have huPrefix := mem_jssPrefix.mp hu
      omega
  have hwLayer : w.1 = i := by
    rcases huw.2 with ⟨_huPrefix, hwMiddle⟩ | ⟨huMiddle, _hwPrefix⟩
    · exact mem_jssLayer_iff.mp hwMiddle
    · have huLayer := mem_jssLayer_iff.mp huMiddle
      have huPrefix := mem_jssPrefix.mp hu
      omega
  exact unique_neighbor_in_later_layer (hKG huv.1) (hKG huw.1)
    (by simpa [hvLayer] using mem_jssPrefix.mp hu)
    (by simpa [hwLayer] using mem_jssPrefix.mp hu) (hvLayer.trans hwLayer.symm)

/-- The cross-edge count is at most the number of supported prefix vertices. -/
lemma card_jssCross_le_prefixSupport {n : ℕ} {ω : JSSOutcome n}
    {hω : ω ∈ jssOutcomeSpace n} {K : SimpleGraph (JSSVertex n)}
    (hKG : K ≤ jssGraph ω hω) (i : Fin (prsLayerCount n)) :
    (jssCross K i).edgeFinset.card ≤
      (K.support.toFinset ∩ jssPrefix n i).card := by
  classical
  rw [← SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges
    (jssCross_isBipartiteWith K i)]
  rw [sum_degrees_eq_inter_support_of_le (jssCross K i) K
    SimpleGraph.between_le]
  calc
    ∑ v ∈ K.support.toFinset ∩ jssPrefix n i, (jssCross K i).degree v ≤
        ∑ _v ∈ K.support.toFinset ∩ jssPrefix n i, 1 := by
      apply Finset.sum_le_sum
      intro v hv
      exact jssCross_degree_le_one hKG i (Finset.mem_inter.mp hv).2
    _ = (K.support.toFinset ∩ jssPrefix n i).card := by simp

/-- For a supported 4-regular `K`, the same cross count is at most four
times the number of supported vertices in the middle layer. -/
lemma card_jssCross_le_four_mul_layerSupport {n : ℕ}
    {K : SimpleGraph (JSSVertex n)}
    (hKreg : ∀ v ∈ K.support, K.degree v = 4)
    (i : Fin (prsLayerCount n)) :
    (jssCross K i).edgeFinset.card ≤
      4 * (K.support.toFinset ∩ jssLayer n i).card := by
  classical
  rw [← SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges'
    (jssCross_isBipartiteWith K i)]
  rw [sum_degrees_eq_inter_support_of_le (jssCross K i) K
    SimpleGraph.between_le]
  calc
    ∑ v ∈ K.support.toFinset ∩ jssLayer n i, (jssCross K i).degree v ≤
        ∑ _v ∈ K.support.toFinset ∩ jssLayer n i, 4 := by
      apply Finset.sum_le_sum
      intro v hv
      exact ((jssCross K i).degree_le_of_le SimpleGraph.between_le).trans_eq
        (hKreg v (Set.mem_toFinset.mp (Finset.mem_inter.mp hv).1))
    _ = 4 * (K.support.toFinset ∩ jssLayer n i).card := by
      simp [Nat.mul_comm]

/-- Edges meeting the strict tail are bounded by four times the supported
tail size. -/
lemma card_tailMeeting_le_four_mul {n : ℕ} (K : SimpleGraph (JSSVertex n))
    (hKreg : ∀ v ∈ K.support, K.degree v = 4)
    (i : Fin (prsLayerCount n)) :
    (layeredEdgesMeeting K (jssStrictTail n i)).card ≤
      4 * (K.support.toFinset ∩ jssStrictTail n i).card := by
  classical
  calc
    (layeredEdgesMeeting K (jssStrictTail n i)).card ≤
        ∑ v ∈ jssStrictTail n i, K.degree v :=
      card_layeredEdgesMeeting_le_sum_degree K (jssStrictTail n i)
    _ = ∑ v ∈ K.support.toFinset ∩ jssStrictTail n i, K.degree v :=
      sum_degrees_eq_inter_support K (jssStrictTail n i)
    _ = ∑ _v ∈ K.support.toFinset ∩ jssStrictTail n i, 4 := by
      apply Finset.sum_congr rfl
      intro v hv
      exact hKreg v (Set.mem_toFinset.mp (Finset.mem_inter.mp hv).1)
    _ = 4 * (K.support.toFinset ∩ jssStrictTail n i).card := by
      simp [Nat.mul_comm]

/-- Every edge of a JSS subgraph is either internal to the strict prefix,
crosses from that prefix to the middle layer, or meets the strict tail. -/
lemma edgeFinset_subset_inside_cross_tail {n : ℕ} {ω : JSSOutcome n}
    {hω : ω ∈ jssOutcomeSpace n} {K : SimpleGraph (JSSVertex n)}
    (hKG : K ≤ jssGraph ω hω) (i : Fin (prsLayerCount n)) :
    K.edgeFinset ⊆
      layeredEdgesInside K (jssPrefix n i) ∪
        (jssCross K i).edgeFinset ∪
          layeredEdgesMeeting K (jssStrictTail n i) := by
  classical
  intro e he
  refine Sym2.inductionOn e (fun a b he ↦ ?_) he
  have hab : K.Adj a b := by
    rw [← K.mem_edgeSet]
    exact SimpleGraph.mem_edgeFinset.mp he
  have habG := hKG hab
  by_cases ha : a.1 < i
  · by_cases hb : b.1 < i
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply mem_layeredEdgesInside.mpr
      refine ⟨he, ?_⟩
      intro v hv
      have hv' : v = a ∨ v = b := by
        simpa [Sym2.mem_toFinset] using hv
      rcases hv' with rfl | rfl
      · exact mem_jssPrefix.mpr ha
      · exact mem_jssPrefix.mpr hb
    · by_cases hbTail : i < b.1
      · apply Finset.mem_union_right
        exact mem_layeredEdgesMeeting.mpr
          ⟨he, b, by simp, mem_jssStrictTail.mpr hbTail⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        rw [SimpleGraph.mem_edgeFinset]
        change (jssCross K i).Adj a b
        rw [jssCross, SimpleGraph.between_adj]
        exact ⟨hab, Or.inl ⟨mem_jssPrefix.mpr ha,
          mem_jssLayer_iff.mpr (by omega)⟩⟩
  · by_cases hb : b.1 < i
    · by_cases haTail : i < a.1
      · apply Finset.mem_union_right
        exact mem_layeredEdgesMeeting.mpr
          ⟨he, a, by simp, mem_jssStrictTail.mpr haTail⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        rw [SimpleGraph.mem_edgeFinset]
        change (jssCross K i).Adj a b
        rw [jssCross, SimpleGraph.between_adj]
        exact ⟨hab, Or.inr ⟨mem_jssLayer_iff.mpr (by omega),
          mem_jssPrefix.mpr hb⟩⟩
    · by_cases haTail : i < a.1
      · apply Finset.mem_union_right
        exact mem_layeredEdgesMeeting.mpr
          ⟨he, a, by simp, mem_jssStrictTail.mpr haTail⟩
      · by_cases hbTail : i < b.1
        · apply Finset.mem_union_right
          exact mem_layeredEdgesMeeting.mpr
            ⟨he, b, by simp, mem_jssStrictTail.mpr hbTail⟩
        · have haLayer : a.1 = i := by omega
          have hbLayer : b.1 = i := by omega
          exact (no_jssGraph_edge_inside_layer haLayer hbLayer habG).elim

/-- Cardinal version of the preceding three-way edge cover. -/
lemma card_edgeFinset_le_inside_cross_tail {n : ℕ} {ω : JSSOutcome n}
    {hω : ω ∈ jssOutcomeSpace n} {K : SimpleGraph (JSSVertex n)}
    (hKG : K ≤ jssGraph ω hω) (i : Fin (prsLayerCount n)) :
    K.edgeFinset.card ≤
      (layeredEdgesInside K (jssPrefix n i)).card +
        (jssCross K i).edgeFinset.card +
          (layeredEdgesMeeting K (jssStrictTail n i)).card := by
  calc
    K.edgeFinset.card ≤
        (layeredEdgesInside K (jssPrefix n i) ∪
          (jssCross K i).edgeFinset ∪
            layeredEdgesMeeting K (jssStrictTail n i)).card :=
      Finset.card_le_card (edgeFinset_subset_inside_cross_tail hKG i)
    _ ≤ (layeredEdgesInside K (jssPrefix n i)).card +
        (jssCross K i).edgeFinset.card +
          (layeredEdgesMeeting K (jssStrictTail n i)).card := by
      exact (Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)

/-- Prefix-internal edges of a subgraph are among the ambient edges induced
by the supported prefix vertices. -/
lemma card_inside_le_induce_supportInter {n : ℕ} {ω : JSSOutcome n}
    {hω : ω ∈ jssOutcomeSpace n} {K : SimpleGraph (JSSVertex n)}
    (hKG : K ≤ jssGraph ω hω) (i : Fin (prsLayerCount n)) :
    (layeredEdgesInside K (jssPrefix n i)).card ≤
      ((jssGraph ω hω).induce
        (↑(K.support.toFinset ∩ jssPrefix n i) :
          Set (JSSVertex n))).edgeFinset.card := by
  classical
  let S := K.support.toFinset ∩ jssPrefix n i
  have hsub : layeredEdgesInside K (jssPrefix n i) ⊆
      internalJSSEdges (jssGraph ω hω) S := by
    intro e he
    obtain ⟨heK, hePrefix⟩ := mem_layeredEdgesInside.mp he
    apply Finset.mem_filter.mpr
    constructor
    · exact SimpleGraph.edgeFinset_mono hKG heK
    · intro v hv
      refine Finset.mem_inter.mpr ⟨?_, hePrefix v hv⟩
      refine Set.mem_toFinset.mpr ?_
      refine Sym2.inductionOn e (fun a b heK hv ↦ ?_) heK hv
      have hab : K.Adj a b := by
        rw [← K.mem_edgeSet]
        exact SimpleGraph.mem_edgeFinset.mp heK
      have hv' : v = a ∨ v = b := by
        simpa [Sym2.mem_toFinset] using hv
      rcases hv' with rfl | rfl
      · exact hab.mem_support_left
      · exact hab.mem_support_right
  have hle : (layeredEdgesInside K (jssPrefix n i)).card ≤
      (internalJSSEdges (jssGraph ω hω) S).card :=
    Finset.card_le_card hsub
  have heq := card_internalJSSEdges (jssGraph ω hω) S
  simpa only [S] using hle.trans_eq heq

/-- Handshaking for a graph that is 4-regular on its nonempty support. -/
lemma card_edgeFinset_eq_two_mul_support {V : Type*} [Fintype V]
    [DecidableEq V] (K : SimpleGraph V)
    (hKreg : ∀ v ∈ K.support, K.degree v = 4) :
    K.edgeFinset.card = 2 * K.support.ncard := by
  classical
  have hhand : 4 * K.support.ncard = 2 * K.edgeFinset.card := by
    calc
      4 * K.support.ncard = ∑ v ∈ K.support.toFinset, 4 := by
        simp [Nat.mul_comm, Set.ncard_eq_toFinset_card']
      _ = ∑ v ∈ K.support.toFinset, K.degree v := by
        apply Finset.sum_congr rfl
        intro v hv
        exact (hKreg v (Set.mem_toFinset.mp hv)).symm
      _ = 2 * K.edgeFinset.card := by
        simpa only using K.sum_degrees_support_eq_twice_card_edges
  omega

/-- At a scale where the strict tail is tiny and the middle layer is still
large, a supported 4-regular subgraph forces a forbidden dense prefix. -/
lemma denseJSSPrefixBadAt_of_supportedRegular {n : ℕ} {ω : JSSOutcome n}
    {hω : ω ∈ jssOutcomeSpace n} {K : SimpleGraph (JSSVertex n)}
    (hKG : K ≤ jssGraph ω hω) (hKne : K.support.Nonempty)
    (hKreg : ∀ v ∈ K.support, K.degree v = 4)
    (i : Fin (prsLayerCount n))
    (hscale : K.support.ncard ≤ 1000 * prsLayerSize n i.val)
    (htail : 500 * (jssStrictTail n i).card < K.support.ncard) :
    DenseJSSPrefixBadAt (jssGraph ω hω) i := by
  classical
  let X := K.support.toFinset ∩ jssPrefix n i
  let Y := K.support.toFinset ∩ jssLayer n i
  let Z := K.support.toFinset ∩ jssStrictTail n i
  let m := K.support.ncard
  let a := (layeredEdgesInside K (jssPrefix n i)).card
  let c := (jssCross K i).edgeFinset.card
  let t := (layeredEdgesMeeting K (jssStrictTail n i)).card
  have hm : 0 < m := (Set.ncard_pos (Set.toFinite K.support)).mpr hKne
  have hX : X.card ≤ m := by
    calc
      X.card ≤ K.support.toFinset.card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = m := by simp [m, Set.ncard_eq_toFinset_card']
  have hXY : X.card + Y.card ≤ m := by
    have hdisj : Disjoint X Y := by
      rw [Finset.disjoint_left]
      intro v hvX hvY
      have hvlt := mem_jssPrefix.mp (Finset.mem_inter.mp hvX).2
      have hveq := mem_jssLayer_iff.mp (Finset.mem_inter.mp hvY).2
      omega
    rw [← Finset.card_union_of_disjoint hdisj]
    calc
      (X ∪ Y).card ≤ K.support.toFinset.card := by
        apply Finset.card_le_card
        intro v hv
        rcases Finset.mem_union.mp hv with hv | hv
        · exact (Finset.mem_inter.mp hv).1
        · exact (Finset.mem_inter.mp hv).1
      _ = m := by simp [m, Set.ncard_eq_toFinset_card']
  have hZtail : Z.card ≤ (jssStrictTail n i).card :=
    Finset.card_le_card Finset.inter_subset_right
  have htailZ : 500 * Z.card < m := by omega
  have hcX : c ≤ X.card := by
    simpa [c, X] using card_jssCross_le_prefixSupport hKG i
  have hcY : c ≤ 4 * Y.card := by
    simpa [c, Y] using card_jssCross_le_four_mul_layerSupport hKreg i
  have hc : 5 * c ≤ 4 * m := by omega
  have ht : t ≤ 4 * Z.card := by
    simpa [t, Z] using card_tailMeeting_le_four_mul K hKreg i
  have hedge : K.edgeFinset.card ≤ a + c + t := by
    simpa [a, c, t] using card_edgeFinset_le_inside_cross_tail hKG i
  have hcardEdge : K.edgeFinset.card = 2 * m := by
    simpa [m] using card_edgeFinset_eq_two_mul_support K hKreg
  have haDense : 11 * X.card ≤ 10 * a := by omega
  have haAmbient : a ≤
      ((jssGraph ω hω).induce (X : Set (JSSVertex n))).edgeFinset.card := by
    simpa [a, X] using card_inside_le_induce_supportInter hKG i
  have hXpos : 0 < X.card := by
    by_contra hzero
    have hXzero : X.card = 0 := by omega
    have haZero : a = 0 := by
      have hchoose := ((jssGraph ω hω).induce
        (X : Set (JSSVertex n))).card_edgeFinset_le_card_choose_two
      have hcardX : Fintype.card (X : Set (JSSVertex n)) = 0 := by
        simpa using hXzero
      have hIndZero : ((jssGraph ω hω).induce
          (X : Set (JSSVertex n))).edgeFinset.card = 0 := by
        have hle0 : ((jssGraph ω hω).induce
            (X : Set (JSSVertex n))).edgeFinset.card ≤ 0 := calc
          ((jssGraph ω hω).induce
              (X : Set (JSSVertex n))).edgeFinset.card ≤
              (Fintype.card (X : Set (JSSVertex n))).choose 2 := hchoose
          _ = 0 := by rw [hcardX]; norm_num
        omega
      omega
    omega
  refine ⟨X, Finset.card_pos.mp hXpos, ?_, ?_, ?_⟩
  · exact fun v hv ↦ (Finset.mem_inter.mp hv).2
  · exact hX.trans (by simpa [m] using hscale)
  · apply le_trans ?_ haAmbient
    simp only [prsBadEdgeCount]
    omega

/-- The analytic tail estimate selects a forbidden dense scale from every
hypothetical 4-regular subgraph.  Very large supports are disposed of at
layer zero; all other supports use the shifted PRS scale-selection lemma. -/
theorem denseJSSPrefixBad_of_containsRegularSubgraph {n : ℕ}
    (hcount : 2 ≤ prsLayerCount n)
    (htailBound : ∀ i : ℕ,
      ∑ j ∈ Finset.Ico (i + 1) (prsLayerCount n), prsLayerSize n j ≤
        2 * prsLayerSize n (i + 1))
    (ω : JSSOutcome n) (hω : ω ∈ jssOutcomeSpace n)
    (hcontains : ContainsRegularSubgraph (jssGraph ω hω) 4) :
    ∃ j : Fin (prsLayerCount n - 1),
      DenseJSSPrefixBadAt (jssGraph ω hω) (jssSuccessorLayer j) := by
  classical
  obtain ⟨K, hKG, hKne, hKreg⟩ :=
    exists_supportedRegular_of_containsRegularSubgraph (by norm_num) hcontains
  let m := K.support.ncard
  have hm : 0 < m := (Set.ncard_pos (Set.toFinite K.support)).mpr hKne
  by_cases hsmall : m ≤ 1000 * prsLayerSize n 1
  · let b := prsShiftedLayerSizes n
    have hshiftTail : ∀ (i : Fin (prsLayerCount n - 1))
        (hi : i.val + 1 < prsLayerCount n - 1),
        (layerStrictTail b i).card ≤
          2 * b (some ⟨i.val + 1, hi⟩) := by
      intro i hi
      change (layerStrictTail (prsShiftedLayerSizes n) i).card ≤
        2 * prsLayerSize n (i.val + 2)
      rw [card_prsLayerStrictTail n hcount i]
      exact htailBound (i.val + 1)
    obtain ⟨j, hjScale, hjTail⟩ :=
      exists_layerScale_of_tail b (by omega) m hm (by
        simpa [b, prsShiftedLayerSizes] using hsmall) hshiftTail
    refine ⟨j, denseJSSPrefixBadAt_of_supportedRegular hKG hKne hKreg
      (jssSuccessorLayer j) ?_ ?_⟩
    · simpa [m, b, prsShiftedLayerSizes] using hjScale
    · have hcardTail : (jssStrictTail n (jssSuccessorLayer j)).card =
          (layerStrictTail (prsShiftedLayerSizes n) j).card := by
        rw [card_jssStrictTail, card_prsLayerStrictTail n hcount j]
        rfl
      rw [hcardTail]
      simpa [m] using hjTail
  · have hlarge : 1000 * prsLayerSize n 1 < m := by omega
    let i0 : Fin (prsLayerCount n) := ⟨0, by omega⟩
    have hprefix0 : jssPrefix n i0 = ∅ := by
      ext v
      constructor
      · intro hv
        have hvlt := mem_jssPrefix.mp hv
        change v.1.val < 0 at hvlt
        omega
      · intro hv
        simp at hv
    have htail0 : (jssStrictTail n i0).card ≤
        2 * prsLayerSize n 1 := by
      rw [card_jssStrictTail]
      simpa [i0] using htailBound 0
    have hcross0 : (jssCross K i0).edgeFinset.card = 0 := by
      have hle := card_jssCross_le_prefixSupport hKG i0
      rw [hprefix0] at hle
      have hle0 : (jssCross K i0).edgeFinset.card ≤ 0 := by
        simpa using hle
      omega
    have hinside0 : (layeredEdgesInside K (jssPrefix n i0)).card = 0 := by
      rw [hprefix0]
      apply Finset.card_eq_zero.mpr
      rw [eq_empty_iff_forall_notMem]
      intro e he
      have hall := (mem_layeredEdgesInside.mp he).2
      exact Sym2.inductionOn e (fun a b hall ↦ by
        have ha : a ∈ (∅ : Finset (JSSVertex n)) := hall a (by simp)
        simp at ha) hall
    have hmeet0 : (layeredEdgesMeeting K (jssStrictTail n i0)).card ≤
        4 * (jssStrictTail n i0).card := by
      calc
        (layeredEdgesMeeting K (jssStrictTail n i0)).card ≤
            4 * (K.support.toFinset ∩ jssStrictTail n i0).card :=
          card_tailMeeting_le_four_mul K hKreg i0
        _ ≤ 4 * (jssStrictTail n i0).card := by
          exact Nat.mul_le_mul_left 4
            (Finset.card_le_card Finset.inter_subset_right)
    have hedge := card_edgeFinset_le_inside_cross_tail hKG i0
    have hcardEdge : K.edgeFinset.card = 2 * m := by
      simpa [m] using card_edgeFinset_eq_two_mul_support K hKreg
    omega

/-- Avoiding every dense successor-prefix event excludes 4-regular
subgraphs. -/
theorem isRegularSubgraphFree_four_of_avoids_dense {n : ℕ}
    (hcount : 2 ≤ prsLayerCount n)
    (htailBound : ∀ i : ℕ,
      ∑ j ∈ Finset.Ico (i + 1) (prsLayerCount n), prsLayerSize n j ≤
        2 * prsLayerSize n (i + 1))
    (ω : JSSOutcome n) (hω : ω ∈ jssOutcomeSpace n)
    (havoid : ∀ j : Fin (prsLayerCount n - 1),
      ¬ DenseJSSPrefixBadAt (jssGraph ω hω) (jssSuccessorLayer j)) :
    IsRegularSubgraphFree (jssGraph ω hω) 4 := by
  intro hcontains
  obtain ⟨j, hj⟩ := denseJSSPrefixBad_of_containsRegularSubgraph
    hcount htailBound ω hω hcontains
  exact havoid j hj

end

end Erdos641
