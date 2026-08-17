import ErdosProblems.Erdos113.HostCell
import ErdosProblems.Erdos113.Pruning
import ErdosProblems.Erdos113.FourCycles

open scoped SimpleGraph BigOperators

namespace Erdos113HostPruning

noncomputable section

open Erdos113Regular Erdos113CellPruning Erdos113HostCell
  Erdos113Pruning Erdos113Cycles Erdos113FourCycles

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma incidenceFinset_graphOfEdges_inter
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {D E : Finset (Sym2 V)} (hD : D ⊆ G.edgeFinset) (hED : E ⊆ D)
    (v : V) :
    E ∩ (graphOfEdges D).incidenceFinset v =
      (graphOfEdges E).incidenceFinset v := by
  have hE : E ⊆ G.edgeFinset := hED.trans hD
  rw [(graphOfEdges D).incidenceFinset_eq_filter,
    (graphOfEdges E).incidenceFinset_eq_filter,
    edgeFinset_graphOfEdges_of_subset hD,
    edgeFinset_graphOfEdges_of_subset hE]
  ext e
  simp only [Finset.mem_inter, Finset.mem_filter]
  tauto

lemma live_of_positive_degree_subset
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {D E : Finset (Sym2 V)} (hD : D ⊆ G.edgeFinset) (hED : E ⊆ D)
    (c : V → Fin 2) {b : Bool} {v : V}
    (hvside : sideOfColor c v = b)
    (hv : 0 < (graphOfEdges E).degree v) :
    v ∈ liveSideVertices D c b := by
  rw [mem_liveSideVertices]
  refine ⟨hvside, ?_⟩
  rw [← (graphOfEdges D).card_incidenceFinset_eq_degree]
  rw [← (graphOfEdges E).card_incidenceFinset_eq_degree] at hv
  exact hv.trans_le (Finset.card_le_card (by
      intro e he
      rw [← incidenceFinset_graphOfEdges_inter hD hED] at he
      exact (Finset.mem_inter.mp he).2))

/-- A final low-degree deletion on a dynamically pruned cell.  The balanced
cell estimate pays for both sides, so more than half of the edges remain. -/
theorem exists_minDegree_pruned_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (i j : Fin (degreeBinCount (W := V))) (b : Bool)
    (D : Finset (Sym2 V)) (hD : D ⊆ G.edgeFinset) (hDne : D.Nonempty)
    (hbalanced :
      (liveSideVertices D c b).card * 2 ^ (i.val + 1) +
          (liveSideVertices D c (!b)).card * 2 ^ (j.val + 1) <
        16 * degreeBinCount (W := V) * D.card) :
    ∃ E : Finset (Sym2 V),
      E ⊆ D ∧ D.card < 2 * E.card ∧ E.Nonempty ∧
      ∀ v, 0 < (graphOfEdges E).degree v →
        (if sideOfColor c v = b then
          cellThreshold (2 ^ (i.val + 1))
            (4 * degreeBinCount (W := V))
        else
          cellThreshold (2 ^ (j.val + 1))
            (4 * degreeBinCount (W := V))) ≤
          (graphOfEdges E).degree v := by
  classical
  let XL := liveSideVertices D c b
  let XR := liveSideVertices D c (!b)
  let S := XL ∪ XR
  let L := degreeBinCount (W := V)
  let tL := cellThreshold (2 ^ (i.val + 1)) (4 * L)
  let tR := cellThreshold (2 ^ (j.val + 1)) (4 * L)
  let threshold : V → ℕ := fun v ↦ if v ∈ XL then tL else tR
  let fiber : V → Finset (Sym2 V) := fun v ↦
    (graphOfEdges D).incidenceFinset v
  have hLpos : 0 < L := by dsimp [L, degreeBinCount]; omega
  have hXLXR : Disjoint XL XR := by
    rw [Finset.disjoint_left]
    intro v hvL hvR
    have hLside := (mem_liveSideVertices.mp hvL).1
    have hRside := (mem_liveSideVertices.mp hvR).1
    have hbad : b = !b := hLside.symm.trans hRside
    cases b <;> simp at hbad
  have hsumNat :
      ∑ v ∈ S, (threshold v - 1) =
        XL.card * (tL - 1) + XR.card * (tR - 1) := by
    change ∑ v ∈ XL ∪ XR, (threshold v - 1) = _
    rw [Finset.sum_union hXLXR]
    congr 1
    · calc
        ∑ v ∈ XL, (threshold v - 1) =
            ∑ _v ∈ XL, (tL - 1) := by
          apply Finset.sum_congr rfl
          intro v hvL
          simp [threshold, hvL]
        _ = XL.card * (tL - 1) := by simp
    · calc
        ∑ v ∈ XR, (threshold v - 1) =
            ∑ _v ∈ XR, (tR - 1) := by
          apply Finset.sum_congr rfl
          intro v hvR
          have hvnot : v ∉ XL := fun hvL ↦
            Finset.disjoint_left.mp hXLXR hvL hvR
          simp [threshold, hvnot]
        _ = XR.card * (tR - 1) := by simp
  have htL := cast_cellThreshold_sub_one_le
    (cap := 2 ^ (i.val + 1)) (L := 4 * L)
      (by positivity) (by positivity)
  have htR := cast_cellThreshold_sub_one_le
    (cap := 2 ^ (j.val + 1)) (L := 4 * L)
      (by positivity) (by positivity)
  have hcost : ((∑ v ∈ S, (threshold v - 1) : ℕ) : ℝ) <
      (D.card : ℝ) / 4 := by
    rw [hsumNat, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
    have hleft : (XL.card : ℝ) * (tL - 1 : ℕ) ≤
        (XL.card : ℝ) * (2 ^ (i.val + 1) : ℕ) / (64 * L) := by
      calc
        (XL.card : ℝ) * (tL - 1 : ℕ) ≤
            (XL.card : ℝ) *
              ((2 ^ (i.val + 1) : ℕ) / (16 * (4 * L) : ℕ)) := by
          gcongr
        _ = _ := by push_cast; ring
    have hright : (XR.card : ℝ) * (tR - 1 : ℕ) ≤
        (XR.card : ℝ) * (2 ^ (j.val + 1) : ℕ) / (64 * L) := by
      calc
        (XR.card : ℝ) * (tR - 1 : ℕ) ≤
            (XR.card : ℝ) *
              ((2 ^ (j.val + 1) : ℕ) / (16 * (4 * L) : ℕ)) := by
          gcongr
        _ = _ := by push_cast; ring
    have hbalancedR :
        (XL.card : ℝ) * (2 ^ (i.val + 1) : ℕ) +
            (XR.card : ℝ) * (2 ^ (j.val + 1) : ℕ) <
          16 * L * (D.card : ℝ) := by
      exact_mod_cast hbalanced
    calc
      (XL.card : ℝ) * (tL - 1 : ℕ) +
          (XR.card : ℝ) * (tR - 1 : ℕ) ≤
        (XL.card : ℝ) * (2 ^ (i.val + 1) : ℕ) / (64 * L) +
          (XR.card : ℝ) * (2 ^ (j.val + 1) : ℕ) / (64 * L) :=
        add_le_add hleft hright
      _ = ((XL.card : ℝ) * (2 ^ (i.val + 1) : ℕ) +
          (XR.card : ℝ) * (2 ^ (j.val + 1) : ℕ)) / (64 * L) := by ring
      _ < (16 * L * (D.card : ℝ)) / (64 * L) := by
        gcongr
      _ = (D.card : ℝ) / 4 := by
        have hLr : (0 : ℝ) < L := by exact_mod_cast hLpos
        field_simp
        ring
  obtain ⟨E, hED, hcard, hstable⟩ :=
    exists_pruned_indexed D S fiber threshold
  have hmore : D.card < 2 * E.card := by
    have hcardR : (D.card : ℝ) ≤ (E.card : ℝ) +
        ((∑ v ∈ S, (threshold v - 1) : ℕ) : ℝ) := by
      exact_mod_cast hcard
    have : (D.card : ℝ) < 2 * E.card := by nlinarith
    exact_mod_cast this
  have hEne : E.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    rw [hzero] at hmore
    simp at hmore
  refine ⟨E, hED, hmore, hEne, ?_⟩
  intro v hv
  have hside : sideOfColor c v = b ∨ sideOfColor c v = !b := by
    cases sideOfColor c v <;> cases b <;> simp
  have hvS : v ∈ S := by
    rcases hside with hs | hs
    · exact Finset.mem_union_left _
        (live_of_positive_degree_subset hD hED c hs hv)
    · exact Finset.mem_union_right _
        (live_of_positive_degree_subset hD hED c hs hv)
  have hincne : (E ∩ fiber v).Nonempty := by
    rw [show E ∩ fiber v = (graphOfEdges E).incidenceFinset v by
      exact incidenceFinset_graphOfEdges_inter hD hED v]
    rw [← Finset.card_pos, (graphOfEdges E).card_incidenceFinset_eq_degree]
    exact hv
  have hst := hstable v hvS hincne
  rw [show E ∩ fiber v = (graphOfEdges E).incidenceFinset v by
    exact incidenceFinset_graphOfEdges_inter hD hED v,
    (graphOfEdges E).card_incidenceFinset_eq_degree] at hst
  by_cases hs : sideOfColor c v = b
  · have hvXL : v ∈ XL := live_of_positive_degree_subset hD hED c hs hv
    simpa [threshold, tL, L, hs, hvXL] using hst
  · have hvnot : v ∉ XL := by
      intro hvXL
      exact hs (mem_liveSideVertices.mp hvXL).1
    simpa [threshold, tR, L, hs, hvnot] using hst

/-- The minimum-degree refinement of a named dense host cell. -/
structure MinDegreeHostCell
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G) where
  edges : Finset (Sym2 V)
  edges_subset : edges ⊆ H.edges
  dense : H.edges.card < 2 * edges.card
  edges_nonempty : edges.Nonempty
  min_degree : ∀ v, 0 < (graphOfEdges edges).degree v →
    (if sideOfColor H.color v = H.anchorSide then
      cellThreshold (2 ^ (H.leftIndex.val + 1))
        (4 * degreeBinCount (W := V))
    else
      cellThreshold (2 ^ (H.rightIndex.val + 1))
        (4 * degreeBinCount (W := V))) ≤
      (graphOfEdges edges).degree v

theorem DenseHostCell.exists_minDegreeHostCell
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G) :
    Nonempty (MinDegreeHostCell H) := by
  obtain ⟨E, hsub, hdense, hne, hmin⟩ := exists_minDegree_pruned_subset
    G H.color H.leftIndex H.rightIndex H.anchorSide H.edges
      H.edges_subset H.edges_nonempty H.balanced
  exact ⟨{
    edges := E
    edges_subset := hsub
    dense := hdense
    edges_nonempty := hne
    min_degree := hmin }⟩

abbrev LiveVertex (E : Finset (Sym2 V)) := (graphOfEdges E).support

def liveGraph (E : Finset (Sym2 V)) : SimpleGraph (LiveVertex E) :=
  (graphOfEdges E).induce (graphOfEdges E).support

noncomputable instance liveGraph_decidableRel (E : Finset (Sym2 V)) :
    DecidableRel (liveGraph E).Adj := Classical.decRel _

lemma liveGraph_degree (E : Finset (Sym2 V)) (v : LiveVertex E) :
    (liveGraph E).degree v = (graphOfEdges E).degree v.1 := by
  exact (graphOfEdges E).degree_induce_support v

def liveSide (E : Finset (Sym2 V)) (c : V → Fin 2)
    (v : LiveVertex E) : Bool := sideOfColor c v.1

lemma MinDegreeHostCell.live_cross
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : DenseHostCell G} (K : MinDegreeHostCell H)
    {x y : LiveVertex K.edges} (hxy : (liveGraph K.edges).Adj x y) :
    liveSide K.edges H.color y = !liveSide K.edges H.color x := by
  have hsub : K.edges ⊆ (graphOfEdges H.edges).edgeFinset := by
    simpa [edgeFinset_graphOfEdges_of_subset H.edges_subset] using K.edges_subset
  exact H.cross ((graphOfEdges_le hsub) hxy)

lemma MinDegreeHostCell.live_degree_cap
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : DenseHostCell G} (K : MinDegreeHostCell H)
    (v : LiveVertex K.edges) :
    (liveGraph K.edges).degree v ≤
      if liveSide K.edges H.color v = H.anchorSide then
        2 ^ (H.leftIndex.val + 1)
      else 2 ^ (H.rightIndex.val + 1) := by
  rw [liveGraph_degree]
  have hsub : K.edges ⊆ (graphOfEdges H.edges).edgeFinset := by
    simpa [edgeFinset_graphOfEdges_of_subset H.edges_subset] using K.edges_subset
  exact (SimpleGraph.degree_le_of_le (graphOfEdges_le hsub)).trans
    (H.degree_cap v.1)

lemma MinDegreeHostCell.live_degree_min
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : DenseHostCell G} (K : MinDegreeHostCell H)
    (v : LiveVertex K.edges) :
    (if liveSide K.edges H.color v = H.anchorSide then
      cellThreshold (2 ^ (H.leftIndex.val + 1))
        (4 * degreeBinCount (W := V))
    else
      cellThreshold (2 ^ (H.rightIndex.val + 1))
        (4 * degreeBinCount (W := V))) ≤
      (liveGraph K.edges).degree v := by
  rw [liveGraph_degree]
  apply K.min_degree
  rw [SimpleGraph.degree_pos_iff_mem_support]
  exact v.2

def sideMinimum
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G)
    (b : Bool) : ℝ :=
  (H.sideCap b : ℝ) / (64 * degreeBinCount (W := V) : ℕ)

lemma MinDegreeHostCell.live_degree_upper_real
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : DenseHostCell G} (K : MinDegreeHostCell H)
    (v : LiveVertex K.edges) :
    ((liveGraph K.edges).degree v : ℝ) ≤
      H.sideCap (liveSide K.edges H.color v) := by
  exact_mod_cast K.live_degree_cap v

lemma MinDegreeHostCell.live_degree_lower_real
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : DenseHostCell G} (K : MinDegreeHostCell H)
    (v : LiveVertex K.edges) :
    sideMinimum H (liveSide K.edges H.color v) ≤
      ((liveGraph K.edges).degree v : ℝ) := by
  let L := degreeBinCount (W := V)
  have hmin := K.live_degree_min v
  have hL : 0 < L := by dsimp [L, degreeBinCount]; omega
  by_cases hb : liveSide K.edges H.color v = H.anchorSide
  · have hceil := cap_div_le_cast_cellThreshold
        (cap := 2 ^ (H.leftIndex.val + 1)) (L := 4 * L)
    have hcast :
        ((cellThreshold (2 ^ (H.leftIndex.val + 1)) (4 * L) : ℕ) : ℝ) ≤
          ((liveGraph K.edges).degree v : ℝ) := by
      exact_mod_cast (by simpa [hb] using hmin)
    calc
      sideMinimum H (liveSide K.edges H.color v) =
          ((2 ^ (H.leftIndex.val + 1) : ℕ) : ℝ) /
            (16 * (4 * L) : ℕ) := by
        simp [sideMinimum, DenseHostCell.sideCap, hb, L]
        ring
      _ ≤ (cellThreshold (2 ^ (H.leftIndex.val + 1)) (4 * L) : ℕ) := hceil
      _ ≤ ((liveGraph K.edges).degree v : ℝ) := hcast
  · have hceil := cap_div_le_cast_cellThreshold
        (cap := 2 ^ (H.rightIndex.val + 1)) (L := 4 * L)
    have hcast :
        ((cellThreshold (2 ^ (H.rightIndex.val + 1)) (4 * L) : ℕ) : ℝ) ≤
          ((liveGraph K.edges).degree v : ℝ) := by
      exact_mod_cast (by simpa [hb] using hmin)
    calc
      sideMinimum H (liveSide K.edges H.color v) =
          ((2 ^ (H.rightIndex.val + 1) : ℕ) : ℝ) /
            (16 * (4 * L) : ℕ) := by
        simp [sideMinimum, DenseHostCell.sideCap, hb, L]
        ring
      _ ≤ (cellThreshold (2 ^ (H.rightIndex.val + 1)) (4 * L) : ℕ) := hceil
      _ ≤ ((liveGraph K.edges).degree v : ℝ) := hcast

lemma MinDegreeHostCell.liveGraph_edge_card
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : DenseHostCell G} (K : MinDegreeHostCell H) :
    (liveGraph K.edges).edgeFinset.card = K.edges.card := by
  have hKG : K.edges ⊆ G.edgeFinset := K.edges_subset.trans H.edges_subset
  calc
    (liveGraph K.edges).edgeFinset.card =
        (graphOfEdges K.edges).edgeFinset.card :=
      (graphOfEdges K.edges).card_edgeFinset_induce_support
    _ = K.edges.card := congrArg Finset.card
      (edgeFinset_graphOfEdges_of_subset hKG)

noncomputable def liveExtensionEmbedding (E : Finset (Sym2 V))
    (u y : LiveVertex E) :
    ↑(extensionsThroughEdge (liveGraph E) u y) →
      ↑(extensionsThroughEdge (graphOfEdges E) u.1 y.1) := fun p ↦ by
  refine ⟨⟨p.1.1.1, p.1.2.1⟩, ?_⟩
  have hp := mem_extensionsThroughEdge.mp p.2
  rw [mem_extensionsThroughEdge]
  exact ⟨hp.1, (fun h ↦ hp.2.1 (Subtype.ext h)),
    hp.2.2.1, hp.2.2.2.1,
      (fun h ↦ hp.2.2.2.2 (Subtype.ext h))⟩

lemma liveExtensionEmbedding_injective (E : Finset (Sym2 V))
    (u y : LiveVertex E) :
    Function.Injective (liveExtensionEmbedding E u y) := by
  intro p q hpq
  have ht := congrArg Subtype.val hpq
  change (⟨p.1.1.1, p.1.2.1⟩ : Σ _x : V, V) =
    ⟨q.1.1.1, q.1.2.1⟩ at ht
  apply Subtype.ext
  apply Sigma.ext
  · apply Subtype.ext
    exact congrArg (fun z : Σ _x : V, V ↦ z.1) ht
  · apply heq_of_eq
    apply Subtype.ext
    exact congrArg (fun z : Σ _x : V, V ↦ z.2) ht

lemma card_liveExtensions_le (E : Finset (Sym2 V))
    (u y : LiveVertex E) :
    (extensionsThroughEdge (liveGraph E) u y).card ≤
      (extensionsThroughEdge (graphOfEdges E) u.1 y.1).card := by
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective (liveExtensionEmbedding E u y)
      (liveExtensionEmbedding_injective E u y)

lemma MinDegreeHostCell.extensionsThroughEdge_le_dynamicCycleCap
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : DenseHostCell G} (K : MinDegreeHostCell H)
    {u y : LiveVertex K.edges} (huy : (liveGraph K.edges).Adj y u) :
    (extensionsThroughEdge (liveGraph K.edges) u y).card ≤
      H.dynamicCycleCap := by
  have hEU : (graphOfEdges K.edges).Adj y.1 u.1 := huy
  have hsub : K.edges ⊆ (graphOfEdges H.edges).edgeFinset := by
    simpa [edgeFinset_graphOfEdges_of_subset H.edges_subset] using K.edges_subset
  have hDU : (graphOfEdges H.edges).Adj y.1 u.1 :=
    (graphOfEdges_le hsub) hEU
  calc
    (extensionsThroughEdge (liveGraph K.edges) u y).card ≤
        (extensionsThroughEdge (graphOfEdges K.edges) u.1 y.1).card :=
      card_liveExtensions_le K.edges u y
    _ ≤ (cyclesThroughEdge (graphOfEdges K.edges) 4 s(u.1, y.1)).card :=
      card_extensionsThroughEdge_le_cyclesThroughEdge
        (graphOfEdges K.edges) u.1 y.1 hEU
    _ ≤ (cyclesThroughEdge (graphOfEdges H.edges) 4 s(u.1, y.1)).card :=
      Finset.card_le_card (cyclesThroughEdge_mono
        (graphOfEdges_le hsub) 4 s(u.1, y.1))
    _ ≤ H.dynamicCycleCap := H.cyclesThroughEdge_le_dynamicCycleCap hDU.symm

theorem MinDegreeHostCell.liveGraph_isContained_original
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {H : DenseHostCell G} (K : MinDegreeHostCell H) :
    liveGraph K.edges ⊑ G := by
  have hsub : K.edges ⊆ (graphOfEdges H.edges).edgeFinset := by
    simpa [edgeFinset_graphOfEdges_of_subset H.edges_subset] using K.edges_subset
  have hlive : liveGraph K.edges ⊑ graphOfEdges K.edges := by
    exact ⟨(SimpleGraph.Embedding.induce
      (graphOfEdges K.edges).support).toCopy⟩
  exact hlive.trans_le
    ((graphOfEdges_le hsub).trans (graphOfEdges_le H.edges_subset))

end

end Erdos113HostPruning
