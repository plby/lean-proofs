import ErdosProblems.Erdos113.ActiveBins
import ErdosProblems.Erdos113.CellPruning
import ErdosProblems.Erdos113.DynamicPruning
import ErdosProblems.Erdos113.FourCycles
import ErdosProblems.Erdos63.BipartiteHalf

open scoped SimpleGraph

namespace Erdos113HostCell

noncomputable section

open Erdos113Cycles Erdos113Regular Erdos113ActiveBins
  Erdos113CellPruning Erdos113CyclePruning Erdos113DynamicPruning
  Erdos113FourCycles

variable {V : Type*} [Fintype V] [DecidableEq V]

def sideOfColor (c : V → Fin 2) (v : V) : Bool :=
  decide (c v = 1)

lemma sideOfColor_cross {G : SimpleGraph V} {c : V → Fin 2}
    (hc : ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w)
    {v w : V} (hvw : G.Adj v w) :
    sideOfColor c w = !(sideOfColor c v) := by
  have hne := hc hvw
  have hv : c v = 0 ∨ c v = 1 := by omega
  have hw : c w = 0 ∨ c w = 1 := by omega
  rcases hv with hv | hv <;> rcases hw with hw | hw <;>
    simp_all [sideOfColor]

def cellPairsAtSide (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (i j : Fin (degreeBinCount (W := V))) (b : Bool) :
    Finset (BinVertex G i × BinVertex G j) :=
  (cellEdges G i j).filter fun p ↦ sideOfColor c p.1.1 = b

@[simp] lemma mem_cellPairsAtSide
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (i j : Fin (degreeBinCount (W := V)))
    {b : Bool} {p : BinVertex G i × BinVertex G j} :
    p ∈ cellPairsAtSide G c i j b ↔
      p ∈ cellEdges G i j ∧ sideOfColor c p.1.1 = b := by
  simp [cellPairsAtSide]

lemma exists_dense_oriented_cell
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (hedge : ∃ x y, G.Adj x y) :
    ∃ (i j : Fin (degreeBinCount (W := V))) (b : Bool),
      (cellPairsAtSide G c i j b).Nonempty ∧
      G.edgeFinset.card ≤
        2 * degreeBinCount (W := V) ^ 2 *
          (cellPairsAtSide G c i j b).card ∧
      (degreeBin G i).card * 2 ^ (i.val + 1) +
          (degreeBin G j).card * 2 ^ (j.val + 1) ≤
        8 * degreeBinCount (W := V) *
          (cellPairsAtSide G c i j b).card := by
  obtain ⟨i, j, hcellpos, hdense, hbalanced⟩ :=
    exists_dense_active_degree_cell G hedge
  let E₀ := cellPairsAtSide G c i j false
  let E₁ := cellPairsAtSide G c i j true
  have hsum : E₀.card + E₁.card = (cellEdges G i j).card := by
    have hunion : E₀ ∪ E₁ = cellEdges G i j := by
      ext p
      by_cases h : sideOfColor c p.1.1 = false <;>
        simp [E₀, E₁, cellPairsAtSide, h]
    have hdisj : Disjoint E₀ E₁ := by
      rw [Finset.disjoint_left]
      intro p hp₀ hp₁
      have h₀ := (mem_cellPairsAtSide G c i j).mp hp₀
      have h₁ := (mem_cellPairsAtSide G c i j).mp hp₁
      simp_all [E₀, E₁]
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  by_cases hhalf : (cellEdges G i j).card ≤ 2 * E₀.card
  · have hE₀pos : 0 < E₀.card := by
      rw [card_cellEdges] at hhalf
      omega
    refine ⟨i, j, false, Finset.card_pos.mp hE₀pos, ?_, ?_⟩
    · calc
        G.edgeFinset.card ≤
            degreeBinCount (W := V) ^ 2 * cellCount G i j := hdense
        _ = degreeBinCount (W := V) ^ 2 * (cellEdges G i j).card := by
          rw [card_cellEdges]
        _ ≤ degreeBinCount (W := V) ^ 2 * (2 * E₀.card) := by gcongr
        _ = 2 * degreeBinCount (W := V) ^ 2 *
            (cellPairsAtSide G c i j false).card := by
          dsimp [E₀]
          ring
    · calc
        (degreeBin G i).card * 2 ^ (i.val + 1) +
            (degreeBin G j).card * 2 ^ (j.val + 1) ≤
            4 * degreeBinCount (W := V) * cellCount G i j := hbalanced
        _ = 4 * degreeBinCount (W := V) * (cellEdges G i j).card := by
          rw [card_cellEdges]
        _ ≤ 4 * degreeBinCount (W := V) * (2 * E₀.card) := by gcongr
        _ = 8 * degreeBinCount (W := V) *
            (cellPairsAtSide G c i j false).card := by
          dsimp [E₀]
          ring
  · have hhalf₁ : (cellEdges G i j).card ≤ 2 * E₁.card := by omega
    have hE₁pos : 0 < E₁.card := by
      rw [card_cellEdges] at hhalf₁
      omega
    refine ⟨i, j, true, Finset.card_pos.mp hE₁pos, ?_, ?_⟩
    · calc
        G.edgeFinset.card ≤
            degreeBinCount (W := V) ^ 2 * cellCount G i j := hdense
        _ = degreeBinCount (W := V) ^ 2 * (cellEdges G i j).card := by
          rw [card_cellEdges]
        _ ≤ degreeBinCount (W := V) ^ 2 * (2 * E₁.card) := by gcongr
        _ = 2 * degreeBinCount (W := V) ^ 2 *
            (cellPairsAtSide G c i j true).card := by
          dsimp [E₁]
          ring
    · calc
        (degreeBin G i).card * 2 ^ (i.val + 1) +
            (degreeBin G j).card * 2 ^ (j.val + 1) ≤
            4 * degreeBinCount (W := V) * cellCount G i j := hbalanced
        _ = 4 * degreeBinCount (W := V) * (cellEdges G i j).card := by
          rw [card_cellEdges]
        _ ≤ 4 * degreeBinCount (W := V) * (2 * E₁.card) := by gcongr
        _ = 8 * degreeBinCount (W := V) *
            (cellPairsAtSide G c i j true).card := by
          dsimp [E₁]
          ring

def cellPairEdge {G : SimpleGraph V} [DecidableRel G.Adj]
    {i j : Fin (degreeBinCount (W := V))}
    (p : BinVertex G i × BinVertex G j) : Sym2 V :=
  s(p.1.1, p.2.1)

lemma cellPairEdge_injOn
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (hc : ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w)
    (i j : Fin (degreeBinCount (W := V))) (b : Bool) :
    Set.InjOn (cellPairEdge (G := G) (i := i) (j := j))
      (cellPairsAtSide G c i j b) := by
  intro p hp q hq hpq
  have hpdata := (mem_cellPairsAtSide G c i j).mp hp
  have hqdata := (mem_cellPairsAtSide G c i j).mp hq
  have hpAdj := (mem_cellEdges G i j p).mp hpdata.1
  have hqAdj := (mem_cellEdges G i j q).mp hqdata.1
  rcases Sym2.eq_iff.mp hpq with hsame | hswap
  · apply Prod.ext
    · apply Subtype.ext
      exact hsame.1
    · apply Subtype.ext
      exact hsame.2
  · have hpCross := sideOfColor_cross hc hpAdj
    have hqCross := sideOfColor_cross hc hqAdj
    have hbad : b = !b := by
      calc
        b = sideOfColor c p.1.1 := hpdata.2.symm
        _ = sideOfColor c q.2.1 := by rw [hswap.1]
        _ = !(sideOfColor c q.1.1) := hqCross
        _ = !b := by rw [hqdata.2]
    cases b <;> contradiction

def orientedCellEdges
  (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (i j : Fin (degreeBinCount (W := V))) (b : Bool) :
    Finset (Sym2 V) :=
  (cellPairsAtSide G c i j b).image
    (cellPairEdge (G := G) (i := i) (j := j))

lemma card_orientedCellEdges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (hc : ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w)
    (i j : Fin (degreeBinCount (W := V))) (b : Bool) :
    (orientedCellEdges G c i j b).card =
      (cellPairsAtSide G c i j b).card := by
  exact Finset.card_image_iff.mpr (cellPairEdge_injOn G c hc i j b)

lemma orientedCellEdges_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (i j : Fin (degreeBinCount (W := V))) (b : Bool) :
    orientedCellEdges G c i j b ⊆ G.edgeFinset := by
  intro e he
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
  have hpCell := (mem_cellPairsAtSide G c i j).mp hp
  have hpAdj := (mem_cellEdges G i j p).mp hpCell.1
  simpa [cellPairEdge] using hpAdj

lemma endpoint_mem_degreeBin_of_mem_orientedCellEdges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (hc : ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w)
    (i j : Fin (degreeBinCount (W := V))) (b : Bool)
    {v w : V} (hvw : s(v, w) ∈ orientedCellEdges G c i j b) :
    (sideOfColor c v = b → v ∈ degreeBin G i) ∧
      (sideOfColor c v ≠ b → v ∈ degreeBin G j) := by
  obtain ⟨p, hp, hpedge⟩ := Finset.mem_image.mp hvw
  have hpdata := (mem_cellPairsAtSide G c i j).mp hp
  have hpAdj := (mem_cellEdges G i j p).mp hpdata.1
  have hpCross := sideOfColor_cross hc hpAdj
  change s(p.1.1, p.2.1) = s(v, w) at hpedge
  rcases Sym2.eq_iff.mp hpedge with hsame | hswap
  · refine ⟨?_, ?_⟩
    · intro _
      simpa [← hsame.1] using p.1.2
    intro hne
    exact False.elim (hne (by simpa [← hsame.1] using hpdata.2))
  · refine ⟨?_, ?_⟩
    · intro heq
      have hsidev : sideOfColor c v = !b := by
        calc
          sideOfColor c v = sideOfColor c p.2.1 :=
            congrArg (sideOfColor c) hswap.2.symm
          _ = !(sideOfColor c p.1.1) := hpCross
          _ = !b := congrArg (fun x : Bool ↦ !x) hpdata.2
      cases b <;> simp_all
    · intro _
      simpa [← hswap.2] using p.2.2

lemma graphOfOrientedSubset_degree_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (hc : ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w)
    (i j : Fin (degreeBinCount (W := V))) (b : Bool)
    (D : Finset (Sym2 V)) (hD : D ⊆ orientedCellEdges G c i j b)
    (v : V) :
    (graphOfEdges D).degree v ≤
      if sideOfColor c v = b then 2 ^ (i.val + 1) else 2 ^ (j.val + 1) := by
  let P := graphOfEdges D
  by_cases hz : P.degree v = 0
  · simp [P, hz]
  · have hpos : 0 < P.degree v := Nat.pos_of_ne_zero hz
    have hneighbor : (P.neighborFinset v).Nonempty := Finset.card_pos.mp (by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact hpos)
    obtain ⟨w, hw⟩ := hneighbor
    have hpAdj : P.Adj v w := (P.mem_neighborFinset v w).mp hw
    have hedgeD : s(v, w) ∈ D := (graphOfEdges_adj_iff.mp hpAdj).1
    have hbins := endpoint_mem_degreeBin_of_mem_orientedCellEdges
      G c hc i j b (hD hedgeD)
    have hdegreeMono : P.degree v ≤ G.degree v := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree,
        ← SimpleGraph.card_neighborFinset_eq_degree]
      apply Finset.card_le_card
      intro y hy
      apply (G.mem_neighborFinset v y).mpr
      simpa using (orientedCellEdges_subset G c i j b
        (hD (graphOfEdges_adj_iff.mp ((P.mem_neighborFinset v y).mp hy)).1))
    by_cases hvb : sideOfColor c v = b
    · rw [if_pos hvb]
      exact hdegreeMono.trans (degree_bounds_of_mem_bin G i (hbins.1 hvb)).2.le
    · rw [if_neg hvb]
      exact hdegreeMono.trans (degree_bounds_of_mem_bin G j (hbins.2 hvb)).2.le

lemma graphOfOrientedSubset_cross
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (hc : ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w)
    (i j : Fin (degreeBinCount (W := V))) (b : Bool)
    (D : Finset (Sym2 V)) (hD : D ⊆ orientedCellEdges G c i j b)
    {v w : V} (hvw : (graphOfEdges D).Adj v w) :
    sideOfColor c w = !(sideOfColor c v) := by
  apply sideOfColor_cross hc
  simpa using (orientedCellEdges_subset G c i j b
    (hD (graphOfEdges_adj_iff.mp hvw).1))

lemma graphOfOrientedSubset_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (i j : Fin (degreeBinCount (W := V))) (b : Bool)
    (D : Finset (Sym2 V)) (hD : D ⊆ orientedCellEdges G c i j b) :
    graphOfEdges D ≤ G :=
  graphOfEdges_le (hD.trans (orientedCellEdges_subset G c i j b))

/-- Vertices on one color side which are incident with a retained edge. -/
def liveSideVertices (D : Finset (Sym2 V)) (c : V → Fin 2) (b : Bool) :
    Finset V :=
  Finset.univ.filter fun v ↦
    sideOfColor c v = b ∧ 0 < (graphOfEdges D).degree v

@[simp] lemma mem_liveSideVertices
    {D : Finset (Sym2 V)} {c : V → Fin 2} {b : Bool} {v : V} :
    v ∈ liveSideVertices D c b ↔
      sideOfColor c v = b ∧ 0 < (graphOfEdges D).degree v := by
  simp [liveSideVertices]

lemma liveSideVertices_subset_leftBin
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (hc : ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w)
    (i j : Fin (degreeBinCount (W := V))) (b : Bool)
    (D : Finset (Sym2 V)) (hD : D ⊆ orientedCellEdges G c i j b) :
    liveSideVertices D c b ⊆ degreeBin G i := by
  intro v hv
  have hvdata := mem_liveSideVertices.mp hv
  have hneigh : ((graphOfEdges D).neighborFinset v).Nonempty := by
    rw [← Finset.card_pos]
    simpa using hvdata.2
  obtain ⟨w, hw⟩ := hneigh
  have hvw := ((graphOfEdges D).mem_neighborFinset v w).mp hw
  have hedge : s(v, w) ∈ orientedCellEdges G c i j b :=
    hD (graphOfEdges_adj_iff.mp hvw).1
  exact (endpoint_mem_degreeBin_of_mem_orientedCellEdges
    G c hc i j b hedge).1 hvdata.1

lemma liveSideVertices_subset_rightBin
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Fin 2) (hc : ∀ ⦃v w⦄, G.Adj v w → c v ≠ c w)
    (i j : Fin (degreeBinCount (W := V))) (b : Bool)
    (D : Finset (Sym2 V)) (hD : D ⊆ orientedCellEdges G c i j b) :
    liveSideVertices D c (!b) ⊆ degreeBin G j := by
  intro v hv
  have hvdata := mem_liveSideVertices.mp hv
  have hneigh : ((graphOfEdges D).neighborFinset v).Nonempty := by
    rw [← Finset.card_pos]
    simpa using hvdata.2
  obtain ⟨w, hw⟩ := hneigh
  have hvw := ((graphOfEdges D).mem_neighborFinset v w).mp hw
  have hedge : s(v, w) ∈ orientedCellEdges G c i j b :=
    hD (graphOfEdges_adj_iff.mp hvw).1
  apply (endpoint_mem_degreeBin_of_mem_orientedCellEdges
    G c hc i j b hedge).2
  intro heq
  have hbad : b = !b := heq.symm.trans hvdata.1
  cases b <;> simp at hbad

/-- Every graph with an edge has a dense, genuinely bipartite dyadic cell
which has also been dynamically pruned.  The two dyadic degree caps are
retained, more than half of the oriented cell edges survive, and every
surviving edge has final-relative ordered-four-cycle load. -/
theorem exists_dense_dynamically_pruned_bipartite_cell
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hedge : ∃ x y, G.Adj x y) :
    ∃ (c : V → Fin 2) (i j : Fin (degreeBinCount (W := V)))
      (b : Bool) (D : Finset (Sym2 V)),
      D.Nonempty ∧ D ⊆ G.edgeFinset ∧
      G.edgeFinset.card <
        8 * degreeBinCount (W := V) ^ 2 * D.card ∧
      (∀ ⦃v w⦄, (graphOfEdges D).Adj v w →
        sideOfColor c w = !(sideOfColor c v)) ∧
      (∀ v, (graphOfEdges D).degree v ≤
        if sideOfColor c v = b then 2 ^ (i.val + 1)
        else 2 ^ (j.val + 1)) ∧
      2 ^ (i.val + 1) ≤ 2 * G.maxDegree ∧
      2 ^ (j.val + 1) ≤ 2 * G.maxDegree ∧
      (liveSideVertices D c b).card * 2 ^ (i.val + 1) +
          (liveSideVertices D c (!b)).card * 2 ^ (j.val + 1) <
        16 * degreeBinCount (W := V) * D.card ∧
      ∀ e ∈ D,
        D.card * (orderedFourCyclesThroughEdge D e).card ≤
          64 * degreeBinCount (W := V) *
            ((orderedFourCycles D).card + 1) := by
  classical
  obtain ⟨H, hHG, hHbip, hGHcard⟩ :=
    Erdos63.exists_bipartite_subgraph_half G
  obtain ⟨c, hc⟩ := hHbip
  have hcne : ∀ ⦃v w⦄, H.Adj v w → c v ≠ c w := by
    intro v w hvw
    simpa using hc hvw
  have hGcardpos : 0 < G.edgeFinset.card := by
    obtain ⟨x, y, hxy⟩ := hedge
    exact Finset.card_pos.mpr ⟨s(x, y), by simpa using hxy⟩
  have hHcardpos : 0 < H.edgeFinset.card := by omega
  have hHedge : ∃ x y, H.Adj x y := by
    obtain ⟨e, he⟩ := Finset.card_pos.mp hHcardpos
    induction e using Sym2.inductionOn with
    | _ x y => exact ⟨x, y, by simpa using he⟩
  obtain ⟨i, j, b, hcellne, hcellDense, hcellBalanced⟩ :=
    exists_dense_oriented_cell H c hHedge
  let E := orientedCellEdges H c i j b
  let C := graphOfEdges E
  have hEH : E ⊆ H.edgeFinset := orientedCellEdges_subset H c i j b
  have hCEdge : C.edgeFinset = E := by
    dsimp [C]
    exact edgeFinset_graphOfEdges_of_subset hEH
  have hEne : E.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hE
    have : (cellPairsAtSide H c i j b).card = 0 := by
      rw [← card_orientedCellEdges H c hcne i j b]
      simp [E, hE]
    have := Finset.card_pos.mpr hcellne
    omega
  have hCedge : ∃ x y, C.Adj x y := by
    obtain ⟨e, he⟩ := hEne
    induction e using Sym2.inductionOn with
    | _ x y =>
        refine ⟨x, y, ?_⟩
        rw [graphOfEdges_adj_iff]
        have hxy : H.Adj x y := by simpa using hEH he
        exact ⟨he, hxy.ne⟩
  obtain ⟨D, hDC, hCDcard, hDload⟩ :=
    exists_dynamically_pruned_edgeFinset C hCedge
  have hDE : D ⊆ E := by simpa [hCEdge] using hDC
  have hDorient : D ⊆ orientedCellEdges H c i j b := by simpa [E] using hDE
  have hDnonempty : D.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hDempty
    simp [hDempty] at hCDcard
  have hDG : D ⊆ G.edgeFinset :=
    hDorient.trans (orientedCellEdges_subset H c i j b) |>.trans
      (SimpleGraph.edgeFinset_mono hHG)
  have hEcard : E.card = (cellPairsAtSide H c i j b).card := by
    simpa [E] using card_orientedCellEdges H c hcne i j b
  obtain ⟨p, hp⟩ := hcellne
  have hpCell := (mem_cellPairsAtSide H c i j).mp hp
  have hleftCap : 2 ^ (i.val + 1) ≤ 2 * G.maxDegree := by
    have hlower := (degree_bounds_of_mem_bin H i p.1.2).1
    have hmono : H.degree p.1.1 ≤ G.degree p.1.1 :=
      SimpleGraph.degree_le_of_le hHG
    calc
      2 ^ (i.val + 1) = 2 * 2 ^ i.val := by ring
      _ ≤ 2 * H.degree p.1.1 := by gcongr
      _ ≤ 2 * G.degree p.1.1 := by gcongr
      _ ≤ 2 * G.maxDegree := by gcongr; exact G.degree_le_maxDegree _
  have hrightCap : 2 ^ (j.val + 1) ≤ 2 * G.maxDegree := by
    have hlower := (degree_bounds_of_mem_bin H j p.2.2).1
    have hmono : H.degree p.2.1 ≤ G.degree p.2.1 :=
      SimpleGraph.degree_le_of_le hHG
    calc
      2 ^ (j.val + 1) = 2 * 2 ^ j.val := by ring
      _ ≤ 2 * H.degree p.2.1 := by gcongr
      _ ≤ 2 * G.degree p.2.1 := by gcongr
      _ ≤ 2 * G.maxDegree := by gcongr; exact G.degree_le_maxDegree _
  have hDenseFinal : G.edgeFinset.card <
      8 * degreeBinCount (W := V) ^ 2 * D.card := by
    calc
      G.edgeFinset.card ≤ 2 * H.edgeFinset.card := hGHcard
      _ ≤ 2 * (2 * degreeBinCount (W := V) ^ 2 *
            (cellPairsAtSide H c i j b).card) := by gcongr
      _ = 4 * degreeBinCount (W := V) ^ 2 * E.card := by
        rw [hEcard]
        ring
      _ < 4 * degreeBinCount (W := V) ^ 2 * (2 * D.card) := by
        gcongr
        · dsimp [degreeBinCount]
          positivity
        · simpa [hCEdge] using hCDcard
      _ = 8 * degreeBinCount (W := V) ^ 2 * D.card := by ring
  have hBalancedFinal :
      (liveSideVertices D c b).card * 2 ^ (i.val + 1) +
          (liveSideVertices D c (!b)).card * 2 ^ (j.val + 1) <
        16 * degreeBinCount (W := V) * D.card := by
    calc
      (liveSideVertices D c b).card * 2 ^ (i.val + 1) +
          (liveSideVertices D c (!b)).card * 2 ^ (j.val + 1) ≤
          (degreeBin H i).card * 2 ^ (i.val + 1) +
            (degreeBin H j).card * 2 ^ (j.val + 1) := by
        apply Nat.add_le_add
        · exact Nat.mul_le_mul_right _ (Finset.card_le_card
            (liveSideVertices_subset_leftBin H c hcne i j b D hDorient))
        · exact Nat.mul_le_mul_right _ (Finset.card_le_card
            (liveSideVertices_subset_rightBin H c hcne i j b D hDorient))
      _ ≤ 8 * degreeBinCount (W := V) *
          (cellPairsAtSide H c i j b).card := hcellBalanced
      _ = 8 * degreeBinCount (W := V) * E.card := by rw [hEcard]
      _ < 8 * degreeBinCount (W := V) * (2 * D.card) := by
        gcongr
        · dsimp [degreeBinCount]
          positivity
        · simpa [hCEdge] using hCDcard
      _ = 16 * degreeBinCount (W := V) * D.card := by ring
  refine ⟨c, i, j, b, D, hDnonempty, hDG, hDenseFinal, ?_, ?_,
    hleftCap, hrightCap, ?_, ?_⟩
  · intro v w hvw
    exact graphOfOrientedSubset_cross H c hcne i j b D hDorient hvw
  · intro v
    exact graphOfOrientedSubset_degree_le H c hcne i j b D hDorient v
  · exact hBalancedFinal
  · intro e he
    simpa [hCEdge] using hDload e he

/-- A named package for the dynamically pruned balanced host cell. -/
structure DenseHostCell (G : SimpleGraph V) [DecidableRel G.Adj] where
  color : V → Fin 2
  leftIndex : Fin (degreeBinCount (W := V))
  rightIndex : Fin (degreeBinCount (W := V))
  anchorSide : Bool
  edges : Finset (Sym2 V)
  edges_nonempty : edges.Nonempty
  edges_subset : edges ⊆ G.edgeFinset
  dense : G.edgeFinset.card <
    8 * degreeBinCount (W := V) ^ 2 * edges.card
  cross : ∀ ⦃v w : V⦄, (graphOfEdges edges).Adj v w →
    sideOfColor color w = !(sideOfColor color v)
  degree_cap : ∀ v : V, (graphOfEdges edges).degree v ≤
    if sideOfColor color v = anchorSide then 2 ^ (leftIndex.1 + 1)
    else 2 ^ (rightIndex.1 + 1)
  leftCap_le : 2 ^ (leftIndex.1 + 1) ≤ 2 * G.maxDegree
  rightCap_le : 2 ^ (rightIndex.1 + 1) ≤ 2 * G.maxDegree
  balanced :
    (liveSideVertices edges color anchorSide).card * 2 ^ (leftIndex.1 + 1) +
        (liveSideVertices edges color (!anchorSide)).card *
          2 ^ (rightIndex.1 + 1) <
      16 * degreeBinCount (W := V) * edges.card
  local_load : ∀ e ∈ edges,
    edges.card * (orderedFourCyclesThroughEdge edges e).card ≤
      64 * degreeBinCount (W := V) *
        ((orderedFourCycles edges).card + 1)

theorem exists_denseHostCell
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hedge : ∃ x y, G.Adj x y) : Nonempty (DenseHostCell G) := by
  obtain ⟨c, i, j, b, D, hne, hsub, hdense, hcross, hcap,
      hleftCap, hrightCap, hbal, hload⟩ :=
    exists_dense_dynamically_pruned_bipartite_cell G hedge
  exact ⟨{
    color := c
    leftIndex := i
    rightIndex := j
    anchorSide := b
    edges := D
    edges_nonempty := hne
    edges_subset := hsub
    dense := hdense
    cross := hcross
    degree_cap := hcap
    leftCap_le := hleftCap
    rightCap_le := hrightCap
    balanced := hbal
    local_load := hload }⟩

def DenseHostCell.dynamicCycleCap
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G) : ℕ :=
  (64 * degreeBinCount (W := V) *
      ((orderedFourCycles H.edges).card + 1)) / H.edges.card

theorem DenseHostCell.cyclesThroughEdge_le_dynamicCycleCap
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G)
    {u v : V} (huv : (graphOfEdges H.edges).Adj u v) :
    (cyclesThroughEdge (graphOfEdges H.edges) 4 s(u, v)).card ≤
      H.dynamicCycleCap := by
  have hedge : s(u, v) ∈ H.edges := (graphOfEdges_adj_iff.mp huv).1
  rw [dynamicCycleCap, Nat.le_div_iff_mul_le H.edges_nonempty.card_pos]
  simpa [orderedFourCyclesThroughEdge, Nat.mul_comm] using
    H.local_load s(u, v) hedge

theorem DenseHostCell.extensionsThroughEdge_le_dynamicCycleCap
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G)
    {u v : V} (huv : (graphOfEdges H.edges).Adj v u) :
    (extensionsThroughEdge (graphOfEdges H.edges) u v).card ≤
      H.dynamicCycleCap :=
  (card_extensionsThroughEdge_le_cyclesThroughEdge
    (graphOfEdges H.edges) u v huv).trans
      (H.cyclesThroughEdge_le_dynamicCycleCap huv.symm)

def sideFinset (c : V → Fin 2) (b : Bool) : Finset V :=
  Finset.univ.filter fun v ↦ sideOfColor c v = b

@[simp] lemma mem_sideFinset {c : V → Fin 2} {b : Bool} {v : V} :
    v ∈ sideFinset c b ↔ sideOfColor c v = b := by
  simp [sideFinset]

lemma graphOfEdges_isBipartiteWith_sideClass
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G) :
    (graphOfEdges H.edges).IsBipartiteWith
      (↑(sideFinset H.color H.anchorSide) : Set V)
      (↑(sideFinset H.color (!H.anchorSide)) : Set V) := by
  refine ⟨?_, ?_⟩
  · rw [Set.disjoint_left]
    intro v hv hnv
    have hv' := mem_sideFinset.mp hv
    have hnv' := mem_sideFinset.mp hnv
    have hbad : H.anchorSide = !H.anchorSide := hv'.symm.trans hnv'
    cases H.anchorSide <;> simp at hbad
  · intro v w hvw
    have hcross := H.cross hvw
    by_cases hv : sideOfColor H.color v = H.anchorSide
    · left
      refine ⟨mem_sideFinset.mpr hv, mem_sideFinset.mpr ?_⟩
      simpa [hv] using hcross
    · right
      have hv' : sideOfColor H.color v = !H.anchorSide := by
        cases h : sideOfColor H.color v <;>
          cases hb : H.anchorSide <;> simp_all
      refine ⟨mem_sideFinset.mpr hv', mem_sideFinset.mpr ?_⟩
      simpa [hv'] using hcross

lemma DenseHostCell.edge_card_le_card_mul_leftCap
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G) :
    H.edges.card ≤ Fintype.card V * 2 ^ (H.leftIndex.val + 1) := by
  let P := graphOfEdges H.edges
  let S := sideFinset H.color H.anchorSide
  have hPG : H.edges ⊆ G.edgeFinset := H.edges_subset
  have hPE : P.edgeFinset = H.edges := by
    exact edgeFinset_graphOfEdges_of_subset hPG
  have hsum : ∑ v ∈ S, P.degree v = H.edges.card := by
    calc
      ∑ v ∈ S, P.degree v = P.edgeFinset.card := by
        simpa [S] using P.isBipartiteWith_sum_degrees_eq_card_edges
          (graphOfEdges_isBipartiteWith_sideClass H)
      _ = H.edges.card := congrArg Finset.card hPE
  rw [← hsum]
  calc
    ∑ v ∈ S, P.degree v ≤
        ∑ _v ∈ S, 2 ^ (H.leftIndex.val + 1) := by
      apply Finset.sum_le_sum
      intro v hv
      have hvside : sideOfColor H.color v = H.anchorSide := by
        simpa [S, sideFinset] using hv
      simpa [P, hvside] using H.degree_cap v
    _ = S.card * 2 ^ (H.leftIndex.val + 1) := by simp
    _ ≤ Fintype.card V * 2 ^ (H.leftIndex.val + 1) := by
      gcongr
      exact Finset.card_le_univ S

lemma DenseHostCell.edge_card_le_card_mul_rightCap
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G) :
    H.edges.card ≤ Fintype.card V * 2 ^ (H.rightIndex.val + 1) := by
  let P := graphOfEdges H.edges
  let S := sideFinset H.color (!H.anchorSide)
  have hPG : H.edges ⊆ G.edgeFinset := H.edges_subset
  have hPE : P.edgeFinset = H.edges := by
    exact edgeFinset_graphOfEdges_of_subset hPG
  have hsum : ∑ v ∈ S, P.degree v = H.edges.card := by
    calc
      ∑ v ∈ S, P.degree v = P.edgeFinset.card := by
        simpa [S] using P.isBipartiteWith_sum_degrees_eq_card_edges'
          (graphOfEdges_isBipartiteWith_sideClass H)
      _ = H.edges.card := congrArg Finset.card hPE
  rw [← hsum]
  calc
    ∑ v ∈ S, P.degree v ≤
        ∑ _v ∈ S, 2 ^ (H.rightIndex.val + 1) := by
      apply Finset.sum_le_sum
      intro v hv
      have hvside : sideOfColor H.color v = !H.anchorSide := by
        simpa [S, sideFinset] using hv
      have hvne : sideOfColor H.color v ≠ H.anchorSide := by
        intro heq
        have : H.anchorSide = !H.anchorSide := heq.symm.trans hvside
        cases H.anchorSide <;> simp at this
      simpa [P, hvne] using H.degree_cap v
    _ = S.card * 2 ^ (H.rightIndex.val + 1) := by simp
    _ ≤ Fintype.card V * 2 ^ (H.rightIndex.val + 1) := by
      gcongr
      exact Finset.card_le_univ S

def DenseHostCell.sideCap
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G)
    (b : Bool) : ℕ :=
  if b = H.anchorSide then 2 ^ (H.leftIndex.val + 1)
  else 2 ^ (H.rightIndex.val + 1)

lemma DenseHostCell.degree_le_sideCap
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G) (v : V) :
    (graphOfEdges H.edges).degree v ≤ H.sideCap (sideOfColor H.color v) := by
  simpa [DenseHostCell.sideCap] using H.degree_cap v

lemma DenseHostCell.edge_card_le_card_mul_sideCap
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G) (b : Bool) :
    H.edges.card ≤ Fintype.card V * H.sideCap b := by
  by_cases hb : b = H.anchorSide
  · subst b
    simpa [DenseHostCell.sideCap] using H.edge_card_le_card_mul_leftCap
  · have hb' : b = !H.anchorSide := by
      cases hb0 : b <;> cases ha : H.anchorSide <;> simp_all
    rw [hb']
    simpa [DenseHostCell.sideCap] using H.edge_card_le_card_mul_rightCap

lemma DenseHostCell.sideCap_le_two_maxDegree
    {G : SimpleGraph V} [DecidableRel G.Adj] (H : DenseHostCell G) (b : Bool) :
    H.sideCap b ≤ 2 * G.maxDegree := by
  by_cases hb : b = H.anchorSide
  · simpa [DenseHostCell.sideCap, hb] using H.leftCap_le
  · simpa [DenseHostCell.sideCap, hb] using H.rightCap_le

end

end Erdos113HostCell
