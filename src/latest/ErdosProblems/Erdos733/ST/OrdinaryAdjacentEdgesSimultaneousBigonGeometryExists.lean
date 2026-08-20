import ErdosProblems.Erdos733.ST.OrdinaryAdjacentEdgesSimultaneousBigonGeometryData
import ErdosProblems.Erdos733.ST.OrdinaryAdjacentEdgesProtectedTrimmedPresentation
import ErdosProblems.Erdos733.ST.OrdinaryAdjacentEdgesConcreteCollarGeometry
import ErdosProblems.Erdos733.ST.OrdinaryAdjacentEdgesTerminalCollarCompatibility
import ErdosProblems.Erdos733.ST.PolygonalArcEndpointIsolationExists
import ErdosProblems.Erdos733.ST.PlaneDrawingEndpointLocalGermCover
import ErdosProblems.Erdos733.ST.PlanarFiniteRayCappedSideSectors
import ErdosProblems.Erdos733.ST.BigonRerouteLocalSegmentDirection
import ErdosProblems.Erdos733.ST.PolygonalArcCompactAvoidanceScale
import Mathlib.Tactic

open Classical
noncomputable section

private lemma simultaneousBigonOpenNotVertices (Q : PolygonalArc)
    (p : EuclideanSpace ℝ (Fin 2)) (k : ℕ)
    (hk : k + 1 < Q.vertices.length)
    (hp : p ∈ openSegment ℝ Q.vertices[k] Q.vertices[k + 1]) :
    p ∉ Q.vertices := by
  intro hpv
  rcases List.getElem_of_mem hpv with ⟨m, hm, hmp⟩
  by_cases hmk : m = k
  · subst m
    have hne : Q.vertices[k] ≠ Q.vertices[k + 1] := by
      intro heq
      have := (Q.simple_vertices.getElem_inj_iff
        (i := k) (j := k + 1) (hi := by omega) (hj := hk)).1 heq
      omega
    exact hne ((left_mem_openSegment_iff (𝕜 := ℝ)).1 (hmp ▸ hp))
  · by_cases hmks : m = k + 1
    · subst m
      have hne : Q.vertices[k] ≠ Q.vertices[k + 1] := by
        intro heq
        have := (Q.simple_vertices.getElem_inj_iff
          (i := k) (j := k + 1) (hi := by omega) (hj := hk)).1 heq
        omega
      exact hne ((right_mem_openSegment_iff (𝕜 := ℝ)).1 (hmp ▸ hp))
    · exact Q.vertices_avoid_nonincident_interiors hk hm hmk hmks (hmp ▸ hp)

private lemma simultaneousBigonOpenIndexUnique (Q : PolygonalArc) :
    ∀ z a b (ha : a + 1 < Q.vertices.length)
      (hb : b + 1 < Q.vertices.length),
      z ∈ openSegment ℝ Q.vertices[a] Q.vertices[a + 1] →
      z ∈ openSegment ℝ Q.vertices[b] Q.vertices[b + 1] → a = b := by
  intro z a b ha hb hza hzb
  rcases lt_trichotomy a b with hab' | rfl | hba
  · have hzInter : z ∈ segment ℝ Q.vertices[a] Q.vertices[a + 1] ∩
        segment ℝ Q.vertices[b] Q.vertices[b + 1] :=
      ⟨openSegment_subset_segment ℝ _ _ hza,
        openSegment_subset_segment ℝ _ _ hzb⟩
    rw [Q.segment_intersections ha hb hab'] at hzInter
    by_cases hadj : b = a + 1
    · have hzbLeft : z ≠ Q.vertices[b] := by
        intro h
        have hne : Q.vertices[b] ≠ Q.vertices[b + 1] := by
          intro heq
          have := (Q.simple_vertices.getElem_inj_iff
            (i := b) (j := b + 1) (hi := by omega) (hj := hb)).1 heq
          omega
        exact hne ((left_mem_openSegment_iff (𝕜 := ℝ)).1 (h ▸ hzb))
      exact False.elim (hzbLeft (by simpa [hadj] using hzInter))
    · simpa [hadj] using hzInter
  · rfl
  · have hzInter : z ∈ segment ℝ Q.vertices[b] Q.vertices[b + 1] ∩
        segment ℝ Q.vertices[a] Q.vertices[a + 1] :=
      ⟨openSegment_subset_segment ℝ _ _ hzb,
        openSegment_subset_segment ℝ _ _ hza⟩
    rw [Q.segment_intersections hb ha hba] at hzInter
    by_cases hadj : a = b + 1
    · have hzaLeft : z ≠ Q.vertices[a] := by
        intro h
        have hne : Q.vertices[a] ≠ Q.vertices[a + 1] := by
          intro heq
          have := (Q.simple_vertices.getElem_inj_iff
            (i := a) (j := a + 1) (hi := by omega) (hj := ha)).1 heq
          omega
        exact hne ((left_mem_openSegment_iff (𝕜 := ℝ)).1 (h ▸ hza))
      exact False.elim (hzaLeft (by simpa [hadj] using hzInter))
    · simpa [hadj] using hzInter

private lemma simultaneousBigonPrefixEventMemOldRelative
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (firstEdge : G.edgeFinset)
    (firstArc : PolygonalArc) (x : EuclideanSpace ℝ (Fin 2))
    (FirstCut : PolygonalArcPointCutData firstArc x)
    (p : EuclideanSpace ℝ (Fin 2))
    (hfirstRelative : firstArc.relativeInterior =
      (D.edgeArc firstEdge).relativeInterior)
    (hpPrefix : p ∈ FirstCut.prefixArc.carrier)
    (hpPrefixRelative : p ∈ FirstCut.prefixArc.relativeInterior)
    (hpx : p ≠ x) :
    p ∈ (D.edgeArc firstEdge).relativeInterior := by
  rw [hfirstRelative.symm, firstArc.relativeInterior_eq]
  refine ⟨FirstCut.prefix_carrier_subset hpPrefix, ?_⟩
  intro hpEnds
  rcases hpEnds with hpSource | hpTarget
  · have hpPrefixSource : p = FirstCut.prefixArc.source :=
      hpSource.trans FirstCut.prefix_source.symm
    rw [FirstCut.prefixArc.relativeInterior_eq] at hpPrefixRelative
    exact hpPrefixRelative.2 (by simp [hpPrefixSource])
  · have hpSuffix : p ∈ FirstCut.suffixArc.carrier := by
      rw [hpTarget]
      have ht := FirstCut.suffix_target
      rw [← ht]
      rw [FirstCut.suffixArc.carrier_eq]
      have hlast : FirstCut.suffixArc.vertices.length - 2 + 1 <
          FirstCut.suffixArc.vertices.length := by
        have hlen := FirstCut.suffixArc.length_ge_two
        omega
      refine ⟨FirstCut.suffixArc.vertices.length - 2, hlast, ?_⟩
      have htargetIdx : FirstCut.suffixArc.vertices.length - 1 <
          FirstCut.suffixArc.vertices.length := by omega
      have htargetVertex :
          FirstCut.suffixArc.vertices[FirstCut.suffixArc.vertices.length - 1] =
            FirstCut.suffixArc.target := by
        have hget := FirstCut.suffixArc.target_eq_last
        rw [List.getLast?_eq_getElem?] at hget
        rw [List.getElem?_eq_getElem htargetIdx] at hget
        exact Option.some.inj hget
      have hidx : FirstCut.suffixArc.vertices.length - 2 + 1 =
          FirstCut.suffixArc.vertices.length - 1 := by omega
      simpa [hidx, htargetVertex] using
        (right_mem_segment ℝ
          FirstCut.suffixArc.vertices[FirstCut.suffixArc.vertices.length - 2]
          FirstCut.suffixArc.vertices[FirstCut.suffixArc.vertices.length - 1])
    have hpBoth : p ∈ FirstCut.prefixArc.carrier ∩ FirstCut.suffixArc.carrier :=
      ⟨hpPrefix, hpSuffix⟩
    have hpx' : p = x := by
      have : p ∈ ({x} : Set _) := FirstCut.carrier_intersection ▸ hpBoth
      simpa using this
    exact hpx hpx'

private lemma simultaneousBigonBplusSecondSegment
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (secondEdge : G.edgeFinset)
    (x y : EuclideanSpace ℝ (Fin 2))
    (Bplus : Set (EuclideanSpace ℝ (Fin 2)))
    (hx : x ∈ D.crossingSet)
    (Disk : OrdinaryLabeledCrossingDiskData G D ⟨x, hx⟩)
    (j : ℕ) (hj : j + 1 < (D.edgeArc secondEdge).vertices.length)
    (hBplus : Bplus = segment ℝ x y)
    (hBplusBall : Bplus ⊆ Metric.ball x Disk.radius)
    (hySecond : y ∈ (D.edgeArc secondEdge).relativeInterior)
    (hxOpenSecond : x ∈ openSegment ℝ (D.edgeArc secondEdge).vertices[j]
      (D.edgeArc secondEdge).vertices[j + 1])
    (second_disk_local :
      Metric.closedBall x Disk.radius ∩ (D.edgeArc secondEdge).carrier =
        Metric.closedBall x Disk.radius ∩
          segment ℝ (D.edgeArc secondEdge).vertices[j]
            (D.edgeArc secondEdge).vertices[j + 1]) :
    Bplus ⊆ segment ℝ (D.edgeArc secondEdge).vertices[j]
      (D.edgeArc secondEdge).vertices[j + 1] := by
  rw [hBplus]
  have hxSeg : x ∈ segment ℝ (D.edgeArc secondEdge).vertices[j]
      (D.edgeArc secondEdge).vertices[j + 1] :=
    openSegment_subset_segment ℝ _ _ hxOpenSecond
  have hySeg : y ∈ segment ℝ (D.edgeArc secondEdge).vertices[j]
      (D.edgeArc secondEdge).vertices[j + 1] := by
    have hyBall : y ∈ Metric.closedBall x Disk.radius :=
      Metric.ball_subset_closedBall
        (hBplusBall (by simpa [hBplus] using right_mem_segment ℝ x y))
    have hyCarrier : y ∈ (D.edgeArc secondEdge).carrier :=
      ((D.edgeArc secondEdge).relativeInterior_eq ▸ hySecond).1
    have hyLocal : y ∈ Metric.closedBall x Disk.radius ∩
        (D.edgeArc secondEdge).carrier := ⟨hyBall, hyCarrier⟩
    rw [second_disk_local] at hyLocal
    exact hyLocal.2
  exact (convex_segment _ _).segment_subset hxSeg hySeg

private lemma simultaneousBigonEventNotBplus
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (firstEdge secondEdge : G.edgeFinset)
    (x p : EuclideanSpace ℝ (Fin 2))
    (Bplus : Set (EuclideanSpace ℝ (Fin 2)))
    (hx : x ∈ D.crossingSet)
    (Disk : OrdinaryLabeledCrossingDiskData G D ⟨x, hx⟩)
    (hDiskEdges :
      (Disk.firstEdge = firstEdge ∧ Disk.secondEdge = secondEdge) ∨
        (Disk.firstEdge = secondEdge ∧ Disk.secondEdge = firstEdge))
    (hBplusBall : Bplus ⊆ Metric.ball x Disk.radius)
    (hBplusSecondCarrier : Bplus ⊆ (D.edgeArc secondEdge).carrier)
    (hpFirst : p ∈ (D.edgeArc firstEdge).relativeInterior)
    (hpx : p ≠ x) :
    p ∉ Bplus := by
  intro hpBplus
  have hpSecondCarrier := hBplusSecondCarrier hpBplus
  have hpSecond : p ∈ (D.edgeArc secondEdge).relativeInterior := by
    rw [(D.edgeArc secondEdge).relativeInterior_eq]
    refine ⟨hpSecondCarrier, ?_⟩
    intro hpEnds
    rcases D.edgeArc_endpoints secondEdge with ⟨a, b, _hab, _he, hends⟩
    rcases hends with ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩ <;>
      rcases hpEnds with hpS | hpT
    · rw [hpS, hsource] at hpFirst
      exact D.no_vertex_in_edge_interior a firstEdge hpFirst
    · rw [hpT, htarget] at hpFirst
      exact D.no_vertex_in_edge_interior b firstEdge hpFirst
    · rw [hpS, hsource] at hpFirst
      exact D.no_vertex_in_edge_interior b firstEdge hpFirst
    · rw [hpT, htarget] at hpFirst
      exact D.no_vertex_in_edge_interior a firstEdge hpFirst
  have hpBall : p ∈ Metric.closedBall x Disk.radius :=
    Metric.ball_subset_closedBall (hBplusBall hpBplus)
  apply hpx
  rcases hDiskEdges with hlabels | hlabels
  · have hpDiskFirst : p ∈ (D.edgeArc Disk.firstEdge).relativeInterior := by
      simpa [hlabels.1] using hpFirst
    have hpDiskSecond : p ∈ (D.edgeArc Disk.secondEdge).relativeInterior := by
      simpa [hlabels.2] using hpSecond
    exact Disk.pair_meets_only_at_center hpBall hpDiskFirst hpDiskSecond
  · have hpDiskFirst : p ∈ (D.edgeArc Disk.firstEdge).relativeInterior := by
      simpa [hlabels.1] using hpSecond
    have hpDiskSecond : p ∈ (D.edgeArc Disk.secondEdge).relativeInterior := by
      simpa [hlabels.2] using hpFirst
    exact Disk.pair_meets_only_at_center hpBall hpDiskFirst hpDiskSecond

private lemma simultaneousBigonSecondDiskLocal
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (firstEdge secondEdge : G.edgeFinset)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ D.crossingSet)
    (Disk : OrdinaryLabeledCrossingDiskData G D ⟨x, hx⟩)
    (hDiskEdges : (Disk.firstEdge = firstEdge ∧ Disk.secondEdge = secondEdge) ∨
      (Disk.firstEdge = secondEdge ∧ Disk.secondEdge = firstEdge))
    (j : ℕ) (hj : j + 1 < (D.edgeArc secondEdge).vertices.length)
    (hxOpenSecond : x ∈ openSegment ℝ (D.edgeArc secondEdge).vertices[j]
      (D.edgeArc secondEdge).vertices[j + 1]) :
    Metric.closedBall x Disk.radius ∩ (D.edgeArc secondEdge).carrier =
      Metric.closedBall x Disk.radius ∩
        segment ℝ (D.edgeArc secondEdge).vertices[j]
          (D.edgeArc secondEdge).vertices[j + 1] := by
  have branch_local (Br : OrdinaryCrossingLocalBranchData
      (D.edgeArc secondEdge) x Disk.radius) :
      Metric.closedBall x Disk.radius ∩ (D.edgeArc secondEdge).carrier =
        Metric.closedBall x Disk.radius ∩
          segment ℝ (D.edgeArc secondEdge).vertices[j]
            (D.edgeArc secondEdge).vertices[j + 1] := by
    rcases Br.center_case with hsame | hvert
    · rcases hsame with ⟨hafter, hxOpenBranch⟩
      have hbefore : Br.beforeIndex = j :=
        simultaneousBigonOpenIndexUnique (D.edgeArc secondEdge) x Br.beforeIndex j
          Br.beforeIndex_valid hj hxOpenBranch hxOpenSecond
      rw [Br.closedBall_carrier_eq]
      simp only [hafter, hbefore, Set.union_self]
    · rcases hvert with ⟨hafter, hxVertex⟩
      exfalso
      have hafterValid : Br.afterIndex < (D.edgeArc secondEdge).vertices.length := by
        rw [hafter]
        exact Br.beforeIndex_valid
      exact (simultaneousBigonOpenNotVertices (D.edgeArc secondEdge) x j hj hxOpenSecond)
        (by rw [hxVertex]; exact List.getElem_mem hafterValid)
  rcases hDiskEdges with hlabels | hlabels
  · have hlocal := branch_local (hlabels.2 ▸ Disk.secondBranch)
    simpa [hlabels.2] using hlocal
  · have hlocal := branch_local (hlabels.1 ▸ Disk.firstBranch)
    simpa [hlabels.1] using hlocal

private lemma simultaneousBigonLastDirectionScale
    (previous target storedLeft storedRight x d : EuclideanSpace ℝ (Fin 2))
    (r : ℝ) (hdne : d ≠ 0)
    (htarget : target = x) (hd : d = previous - x)
    (hxOpen : x ∈ openSegment ℝ storedLeft storedRight)
    (hr : 0 < r)
    (hlocal : Metric.ball x r ∩ segment ℝ previous target ⊆
      segment ℝ storedLeft storedRight) :
    ∃ scale : ℝ, scale ≠ 0 ∧ d = scale • (storedRight - storedLeft) := by
  have hpreviousTarget : previous ≠ target := by
    intro h
    apply hdne
    rw [hd, h, htarget]
    simp
  obtain ⟨t, ht, hdir⟩ :=
    BigonRerouteLocalSegmentDirection previous target storedLeft storedRight x
      hpreviousTarget (by simpa [htarget] using right_mem_segment ℝ previous target)
      (openSegment_subset_segment ℝ _ _ hxOpen) r hr hlocal
  refine ⟨-t, neg_ne_zero.mpr ht, ?_⟩
  rw [hd, ← htarget]
  simpa using congrArg Neg.neg hdir

private lemma simultaneousBigonStoredLastDirectionScale
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (firstEdge : G.edgeFinset)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ D.crossingSet)
    (Disk : OrdinaryLabeledCrossingDiskData G D ⟨x, hx⟩)
    (Q : PolygonalArc) (d : EuclideanSpace ℝ (Fin 2))
    (i jlast itarget : ℕ)
    (hi : i + 1 < (D.edgeArc firstEdge).vertices.length)
    (hjlast : jlast + 1 < Q.vertices.length)
    (hitarget : itarget < Q.vertices.length)
    (hdne : d ≠ 0) (htarget : Q.vertices[itarget] = x)
    (hd : d = Q.vertices[jlast] - x)
    (hxOpen : x ∈ openSegment ℝ (D.edgeArc firstEdge).vertices[i]
      (D.edgeArc firstEdge).vertices[i + 1])
    (hlocal : Metric.ball x Disk.radius ∩
      segment ℝ Q.vertices[jlast] Q.vertices[itarget] ⊆
        segment ℝ (D.edgeArc firstEdge).vertices[i]
          (D.edgeArc firstEdge).vertices[i + 1]) :
    ∃ scale : ℝ, scale ≠ 0 ∧
      d = scale • ((D.edgeArc firstEdge).vertices[i + 1] -
        (D.edgeArc firstEdge).vertices[i]) :=
  simultaneousBigonLastDirectionScale Q.vertices[jlast] Q.vertices[itarget]
    (D.edgeArc firstEdge).vertices[i] (D.edgeArc firstEdge).vertices[i + 1]
    x d Disk.radius hdne htarget hd hxOpen Disk.firstBranch.radius_pos hlocal

private lemma simultaneousBigonSecondDirectionScale
    (x y storedLeft storedRight : EuclideanSpace ℝ (Fin 2))
    (hyx : y ≠ x)
    (hxOpen : x ∈ openSegment ℝ storedLeft storedRight)
    (hlocal : segment ℝ x y ⊆ segment ℝ storedLeft storedRight) :
    ∃ scale : ℝ, scale ≠ 0 ∧ y - x = scale • (storedRight - storedLeft) := by
  apply BigonRerouteLocalSegmentDirection x y storedLeft storedRight x hyx.symm
    (left_mem_segment ℝ x y)
    (openSegment_subset_segment ℝ _ _ hxOpen) 1 (by norm_num)
  intro z hz
  exact hlocal hz.2

private lemma simultaneousBigonDirectionLinearIndependent
    (d v firstDirection secondDirection : EuclideanSpace ℝ (Fin 2))
    (hd : d ≠ 0)
    (hfirstScale : ∃ scaleA : ℝ, scaleA ≠ 0 ∧
      d = scaleA • firstDirection)
    (hsecondScale : ∃ scaleB : ℝ, scaleB ≠ 0 ∧
      v = scaleB • secondDirection)
    (hnonparallel : ¬ ∃ c : ℝ, secondDirection = c • firstDirection) :
    LinearIndependent ℝ ![d, v] := by
  rw [LinearIndependent.pair_iff' hd]
  intro c hcol
  obtain ⟨scaleA, hscaleA, hdscale⟩ := hfirstScale
  obtain ⟨scaleB, hscaleB, hvscale⟩ := hsecondScale
  apply hnonparallel
  refine ⟨c * scaleA / scaleB, ?_⟩
  rw [hvscale, hdscale] at hcol
  have hEq : scaleB • secondDirection = (c * scaleA) • firstDirection := by
    simpa [smul_smul] using hcol.symm
  apply (smul_right_injective (EuclideanSpace ℝ (Fin 2)) hscaleB)
  calc
    scaleB • secondDirection = (c * scaleA) • firstDirection := hEq
    _ = scaleB • ((c * scaleA / scaleB) • firstDirection) := by
      rw [smul_smul]
      congr 1
      field_simp [hscaleB]

private lemma simultaneousBigonStoredDirectionsLinearIndependent
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (firstEdge secondEdge : G.edgeFinset)
    (d v : EuclideanSpace ℝ (Fin 2)) (i j : ℕ)
    (hi : i + 1 < (D.edgeArc firstEdge).vertices.length)
    (hj : j + 1 < (D.edgeArc secondEdge).vertices.length)
    (hd : d ≠ 0)
    (hfirstScale : ∃ scaleA : ℝ, scaleA ≠ 0 ∧
      d = scaleA • ((D.edgeArc firstEdge).vertices[i + 1] -
        (D.edgeArc firstEdge).vertices[i]))
    (hsecondScale : ∃ scaleB : ℝ, scaleB ≠ 0 ∧
      v = scaleB • ((D.edgeArc secondEdge).vertices[j + 1] -
        (D.edgeArc secondEdge).vertices[j]))
    (hnonparallel : ¬ ∃ c : ℝ,
      (D.edgeArc secondEdge).vertices[j + 1] -
          (D.edgeArc secondEdge).vertices[j] =
        c • ((D.edgeArc firstEdge).vertices[i + 1] -
          (D.edgeArc firstEdge).vertices[i])) :
    LinearIndependent ℝ ![d, v] :=
  simultaneousBigonDirectionLinearIndependent d v
    ((D.edgeArc firstEdge).vertices[i + 1] -
      (D.edgeArc firstEdge).vertices[i])
    ((D.edgeArc secondEdge).vertices[j + 1] -
      (D.edgeArc secondEdge).vertices[j])
    hd hfirstScale hsecondScale hnonparallel

private lemma simultaneousBigonSourceAtZero (Q : PolygonalArc)
    (h0 : 0 < Q.vertices.length) :
    Q.vertices[0]'h0 = Q.source := by
  have hget := Q.source_eq_head
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0] at hget
  exact Option.some.inj hget

private lemma simultaneousBigonInitialDirectionNeZero (Q : PolygonalArc)
    (hfirst : 1 < Q.vertices.length) :
    Q.vertices[1]'hfirst - Q.source ≠ 0 := by
  have h0 : 0 < Q.vertices.length := by omega
  intro hzero
  have hsource0 := simultaneousBigonSourceAtZero Q h0
  have heq : Q.vertices[1]'hfirst = Q.vertices[0]'h0 := by
    rw [hsource0]
    exact sub_eq_zero.mp hzero
  have hidx := (Q.simple_vertices.getElem_inj_iff
    (i := 1) (j := 0) (hi := hfirst) (hj := h0)).1 heq
  omega

private lemma simultaneousBigonSourceCarrierTransfer
    (Q stored : PolygonalArc) (p : EuclideanSpace ℝ (Fin 2))
    (hfirst : 0 + 1 < Q.vertices.length)
    (hsource : Q.source = p) (hsubset : Q.carrier ⊆ stored.carrier) :
    p ∈ stored.carrier := by
  have h0 : 0 < Q.vertices.length := by omega
  have hsource0 := simultaneousBigonSourceAtZero Q h0
  apply hsubset
  rw [Q.carrier_eq]
  refine ⟨0, hfirst, ?_⟩
  simpa [hsource0, hsource] using
    left_mem_segment ℝ (Q.vertices[0]'h0) (Q.vertices[1]'hfirst)

private lemma simultaneousBigonStoredEndpoint
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (u : V) (edge : G.edgeFinset)
    (hmem : D.vertexPlacement u ∈ (D.edgeArc edge).carrier) :
    D.vertexPlacement u = (D.edgeArc edge).source ∨
      D.vertexPlacement u = (D.edgeArc edge).target := by
  by_contra hnot
  have hnotSource : D.vertexPlacement u ≠ (D.edgeArc edge).source :=
    fun h => hnot (Or.inl h)
  have hnotTarget : D.vertexPlacement u ≠ (D.edgeArc edge).target :=
    fun h => hnot (Or.inr h)
  have hrel : D.vertexPlacement u ∈ (D.edgeArc edge).relativeInterior := by
    rw [(D.edgeArc edge).relativeInterior_eq]
    exact ⟨hmem, by simp [hnotSource, hnotTarget]⟩
  exact D.no_vertex_in_edge_interior u edge hrel

private lemma simultaneousBigonPositiveDirectionScale
    (Q stored : PolygonalArc) (p d0 storedDir : EuclideanSpace ℝ (Fin 2))
    (hzero : 0 < Q.vertices.length) (hfirst : 1 < Q.vertices.length)
    (hsource0 : Q.vertices[0]'hzero = Q.source)
    (hsource : Q.source = p)
    (hd0eq : d0 = Q.vertices[1]'hfirst - Q.source) (hd0 : d0 ≠ 0)
    (hsubset : Q.carrier ⊆ stored.carrier)
    (storedRadius : ℝ) (hstoredRadius : 0 < storedRadius)
    (hray : Metric.ball p storedRadius ∩ stored.carrier ⊆
      {q | ∃ c : ℝ, 0 ≤ c ∧ q = p + c • storedDir}) :
    ∃ a : ℝ, 0 < a ∧ d0 = a • storedDir := by
  have hnormd0 : 0 < ‖d0‖ := norm_pos_iff.mpr hd0
  let s : ℝ := min (1 / 2) (storedRadius / (2 * ‖d0‖))
  have hs : 0 < s := by
    dsimp [s]
    exact lt_min (by norm_num) (by positivity)
  have hslt : s < 1 := by
    have := min_le_left (1 / 2 : ℝ) (storedRadius / (2 * ‖d0‖))
    linarith
  let q : EuclideanSpace ℝ (Fin 2) :=
    AffineMap.lineMap Q.source (Q.vertices[1]'hfirst) s
  have hqFormula : q = Q.source + s • d0 := by
    dsimp [q]
    rw [AffineMap.lineMap_apply_module, hd0eq]
    module
  have hqSegment : q ∈ segment ℝ (Q.vertices[0]'hzero)
      (Q.vertices[1]'hfirst) := by
    rw [segment_eq_image_lineMap]
    refine ⟨s, ⟨hs.le, hslt.le⟩, ?_⟩
    dsimp [q]
    rw [hsource0]
  have hqQ : q ∈ Q.carrier := by
    rw [Q.carrier_eq]
    exact ⟨0, hfirst, hqSegment⟩
  have hqStored : q ∈ stored.carrier := hsubset hqQ
  have hsdist : s * ‖d0‖ < storedRadius := by
    have hsle := min_le_right (1 / 2 : ℝ)
      (storedRadius / (2 * ‖d0‖))
    have hhalf : storedRadius / 2 < storedRadius := by linarith
    calc
      s * ‖d0‖ ≤ (storedRadius / (2 * ‖d0‖)) * ‖d0‖ :=
        mul_le_mul_of_nonneg_right hsle (norm_nonneg _)
      _ = storedRadius / 2 := by field_simp [hnormd0.ne']
      _ < storedRadius := hhalf
  have hqBall : q ∈ Metric.ball p storedRadius := by
    rw [Metric.mem_ball, ← hsource, hqFormula, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    exact hsdist
  obtain ⟨c, hc, hqRay⟩ := hray ⟨hqBall, hqStored⟩
  have hqNe : q ≠ Q.source := by
    intro heq
    rw [hqFormula] at heq
    have hsmul : s • d0 = 0 := by
      have := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z - Q.source) heq
      simpa using this
    exact hd0 (smul_eq_zero.mp hsmul |>.resolve_left hs.ne')
  have hcpos : 0 < c := by
    rcases hc.eq_or_lt with rfl | hcpos
    · exfalso
      apply hqNe
      simpa [hsource] using hqRay
    · exact hcpos
  refine ⟨c / s, by positivity, ?_⟩
  have heq : s • d0 = c • storedDir := by
    have hworld : Q.source + s • d0 = Q.source + c • storedDir :=
      hqFormula.symm.trans (by simpa [hsource] using hqRay)
    have := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z - Q.source) hworld
    simpa [hsource] using this
  apply (smul_right_injective (EuclideanSpace ℝ (Fin 2)) hs.ne')
  calc
    s • d0 = c • storedDir := heq
    _ = s • ((c / s) • storedDir) := by
      rw [smul_smul]
      congr 1
      field_simp [hs.ne']

private lemma simultaneousBigonMidpointBounds (a b : ℝ)
    (ha : 0 < a) (hab : a < b) :
    a < (a + b) / 2 ∧ (a + b) / 2 < b ∧ 0 < (a + b) / 2 := by
  constructor
  · linarith
  constructor
  · linarith
  · linarith

private def simultaneousBigonTargetCap (Q : PolygonalArc)
    (radius : Fin Q.vertices.length → ℝ) (targetIndex : Fin Q.vertices.length)
    (jlast : ℕ) (hjlast : jlast < Q.vertices.length) : ℝ :=
  radius targetIndex / dist Q.vertices[targetIndex.1] (Q.vertices[jlast]'hjlast)

private lemma simultaneousBigonTargetCapFacts (Q : PolygonalArc)
    (radius : Fin Q.vertices.length → ℝ) (targetIndex : Fin Q.vertices.length)
    (jlast : ℕ) (hjlast : jlast < Q.vertices.length)
    (x d : EuclideanSpace ℝ (Fin 2))
    (htarget : Q.vertices[targetIndex.1] = x)
    (hddef : d = Q.vertices[jlast]'hjlast - x) (hd : d ≠ 0)
    (hradius : 0 < radius targetIndex) :
    0 < simultaneousBigonTargetCap Q radius targetIndex jlast hjlast ∧
      simultaneousBigonTargetCap Q radius targetIndex jlast hjlast * ‖d‖ =
        radius targetIndex := by
  have hdist : dist Q.vertices[targetIndex.1] (Q.vertices[jlast]'hjlast) = ‖d‖ := by
    simp [htarget, hddef, dist_eq_norm, norm_sub_rev]
  constructor
  · dsimp [simultaneousBigonTargetCap]
    rw [hdist]
    positivity
  · dsimp [simultaneousBigonTargetCap]
    rw [hdist]
    have hnorm : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
    field_simp [hnorm]

private lemma simultaneousBigonKappaSmall (actualK mu nu : ℝ)
    (hactual : actualK < nu / (8 * (|mu| + 1))) (hnu : 0 < nu) :
    actualK * (|mu| + 1) < nu / 4 := by
  have hnonneg : 0 < |mu| + 1 := by positivity
  calc
    actualK * (|mu| + 1) < (nu / (8 * (|mu| + 1))) * (|mu| + 1) :=
      mul_lt_mul_of_pos_right hactual hnonneg
    _ = nu / 8 := by field_simp [hnonneg.ne']
    _ < nu / 4 := by linarith

private def simultaneousBigonLambda (cap mu nu rho normSum : ℝ) : ℝ :=
  min (1 / 2 : ℝ)
    (min (cap / (8 * (1 + |mu| + nu))) (rho / (2 * normSum)))

private lemma simultaneousBigonLambdaFacts (cap mu nu rho normSum : ℝ)
    (hcap : 0 < cap) (hnu : 0 < nu) (hrho : 0 < rho)
    (hnormSum : 0 < normSum) :
    0 < simultaneousBigonLambda cap mu nu rho normSum ∧
      simultaneousBigonLambda cap mu nu rho normSum < 1 ∧
      4 * simultaneousBigonLambda cap mu nu rho normSum *
          (1 + |mu| + nu) < cap ∧
      simultaneousBigonLambda cap mu nu rho normSum * normSum < rho := by
  have hsumPos : 0 < 1 + |mu| + nu := by positivity
  have hlambda : 0 < simultaneousBigonLambda cap mu nu rho normSum := by
    dsimp [simultaneousBigonLambda]
    exact lt_min (by norm_num)
      (lt_min (div_pos hcap (by positivity)) (div_pos hrho (by positivity)))
  have hlambdaOne : simultaneousBigonLambda cap mu nu rho normSum < 1 := by
    have hle : simultaneousBigonLambda cap mu nu rho normSum ≤ (1 / 2 : ℝ) :=
      min_le_left _ _
    linarith
  have hsmallCap : 4 * simultaneousBigonLambda cap mu nu rho normSum *
      (1 + |mu| + nu) < cap := by
    have hle : simultaneousBigonLambda cap mu nu rho normSum ≤
        cap / (8 * (1 + |mu| + nu)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hmul := mul_le_mul_of_nonneg_right hle hsumPos.le
    have hcalc : cap / (8 * (1 + |mu| + nu)) * (1 + |mu| + nu) =
        cap / 8 := by field_simp [hsumPos.ne']
    rw [hcalc] at hmul
    linarith
  have hsmallRho : simultaneousBigonLambda cap mu nu rho normSum * normSum <
      rho := by
    have hle : simultaneousBigonLambda cap mu nu rho normSum ≤
        rho / (2 * normSum) := (min_le_right _ _).trans (min_le_right _ _)
    have hmul := mul_le_mul_of_nonneg_right hle hnormSum.le
    have hcalc : rho / (2 * normSum) * normSum = rho / 2 := by
      field_simp [hnormSum.ne']
    rw [hcalc] at hmul
    linarith
  exact ⟨hlambda, hlambdaOne, hsmallCap, hsmallRho⟩

private lemma simultaneousBigonVectorLambdaFacts (cap mu nu rho : ℝ)
    (d v : EuclideanSpace ℝ (Fin 2))
    (hcap : 0 < cap) (hnu : 0 < nu) (hrho : 0 < rho)
    (hd : d ≠ 0) (hv : v ≠ 0) :
    0 < simultaneousBigonLambda cap mu nu rho (‖d‖ + ‖v‖) ∧
      simultaneousBigonLambda cap mu nu rho (‖d‖ + ‖v‖) < 1 ∧
      4 * simultaneousBigonLambda cap mu nu rho (‖d‖ + ‖v‖) *
          (1 + |mu| + nu) < cap ∧
      simultaneousBigonLambda cap mu nu rho (‖d‖ + ‖v‖) *
          (‖d‖ + ‖v‖) < rho :=
  simultaneousBigonLambdaFacts cap mu nu rho (‖d‖ + ‖v‖)
    hcap hnu hrho (add_pos (norm_pos_iff.mpr hd) (norm_pos_iff.mpr hv))

private lemma simultaneousBigonSegmentPointOnScaledLine
    (a b base z v : EuclideanSpace ℝ (Fin 2)) (scale : ℝ)
    (hbase : base ∈ segment ℝ a b) (hz : z ∈ segment ℝ a b)
    (hscale : v = scale • (b - a)) (hscale0 : scale ≠ 0) :
    ∃ c : ℝ, z = base + c • v := by
  rw [segment_eq_image_lineMap] at hbase hz
  rcases hbase with ⟨s, _hs, rfl⟩
  rcases hz with ⟨t, _ht, rfl⟩
  refine ⟨(t - s) / scale, ?_⟩
  simp only [AffineMap.lineMap_apply_module]
  rw [hscale, smul_smul]
  have hscalar : (t - s) / scale * scale = t - s := by
    field_simp [hscale0]
  rw [hscalar]
  module

private lemma simultaneousBigonPointsOnDirectionOfDiskLocal
    (Q : PolygonalArc) (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (i : ℕ) (hi : i + 1 < Q.vertices.length)
    (d : EuclideanSpace ℝ (Fin 2))
    (hlocal : Metric.closedBall x r ∩ Q.carrier =
      Metric.closedBall x r ∩ segment ℝ Q.vertices[i] Q.vertices[i + 1])
    (hxOpen : x ∈ openSegment ℝ Q.vertices[i] Q.vertices[i + 1])
    (hscale : ∃ scale : ℝ, scale ≠ 0 ∧
      d = scale • (Q.vertices[i + 1] - Q.vertices[i])) :
    ∀ z, z ∈ Metric.closedBall x r → z ∈ Q.carrier →
      ∃ c : ℝ, z = x + c • d := by
  intro z hzClosed hzCarrier
  have hzSeg : z ∈ segment ℝ Q.vertices[i] Q.vertices[i + 1] := by
    have hzBoth : z ∈ Metric.closedBall x r ∩ Q.carrier := ⟨hzClosed, hzCarrier⟩
    rw [hlocal] at hzBoth
    exact hzBoth.2
  rcases hscale with ⟨scale, hscale0, hscale⟩
  exact simultaneousBigonSegmentPointOnScaledLine _ _ x z d scale
    (openSegment_subset_segment ℝ _ _ hxOpen) hzSeg hscale hscale0

private lemma simultaneousBigonFirstDiskLocal
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (firstEdge secondEdge : G.edgeFinset)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ D.crossingSet)
    (Disk : OrdinaryLabeledCrossingDiskData G D ⟨x, hx⟩)
    (i : ℕ) (hi : i + 1 < (D.edgeArc firstEdge).vertices.length)
    (hxOpen : x ∈ openSegment ℝ (D.edgeArc firstEdge).vertices[i]
      (D.edgeArc firstEdge).vertices[i + 1])
    (hDiskEdges :
      (Disk.firstEdge = firstEdge ∧ Disk.secondEdge = secondEdge) ∨
        (Disk.firstEdge = secondEdge ∧ Disk.secondEdge = firstEdge)) :
    Metric.closedBall x Disk.radius ∩ (D.edgeArc firstEdge).carrier =
      Metric.closedBall x Disk.radius ∩
        segment ℝ (D.edgeArc firstEdge).vertices[i]
          (D.edgeArc firstEdge).vertices[i + 1] := by
  have branchLocal (Br : OrdinaryCrossingLocalBranchData
      (D.edgeArc firstEdge) x Disk.radius) :
      Metric.closedBall x Disk.radius ∩ (D.edgeArc firstEdge).carrier =
        Metric.closedBall x Disk.radius ∩
          segment ℝ (D.edgeArc firstEdge).vertices[i]
            (D.edgeArc firstEdge).vertices[i + 1] := by
    rcases Br.center_case with hsame | hvert
    · rcases hsame with ⟨hafter, hxOpenBranch⟩
      have hbefore : Br.beforeIndex = i :=
        simultaneousBigonOpenIndexUnique (D.edgeArc firstEdge) x Br.beforeIndex i
          Br.beforeIndex_valid hi hxOpenBranch hxOpen
      rw [Br.closedBall_carrier_eq]
      simp only [hafter, hbefore, Set.union_self]
    · rcases hvert with ⟨hafter, hxVertex⟩
      exfalso
      have hafterValid : Br.afterIndex < (D.edgeArc firstEdge).vertices.length := by
        rw [hafter]
        exact Br.beforeIndex_valid
      exact (simultaneousBigonOpenNotVertices (D.edgeArc firstEdge) x i hi hxOpen)
        (by rw [hxVertex]; exact List.getElem_mem hafterValid)
  rcases hDiskEdges with hlabels | hlabels
  · have h := branchLocal (hlabels.1 ▸ Disk.firstBranch)
    simpa [hlabels.1] using h
  · have h := branchLocal (hlabels.2 ▸ Disk.secondBranch)
    simpa [hlabels.2] using h

private lemma simultaneousBigonFirstBranchWithIndices
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (firstEdge secondEdge : G.edgeFinset)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ D.crossingSet)
    (Disk : OrdinaryLabeledCrossingDiskData G D ⟨x, hx⟩)
    (i : ℕ) (hi : i + 1 < (D.edgeArc firstEdge).vertices.length)
    (hxOpen : x ∈ openSegment ℝ (D.edgeArc firstEdge).vertices[i]
      (D.edgeArc firstEdge).vertices[i + 1])
    (hDiskEdges :
      (Disk.firstEdge = firstEdge ∧ Disk.secondEdge = secondEdge) ∨
        (Disk.firstEdge = secondEdge ∧ Disk.secondEdge = firstEdge)) :
    ∃ Br : OrdinaryCrossingLocalBranchData
        (D.edgeArc firstEdge) x Disk.radius,
      Br.beforeIndex = i ∧ Br.afterIndex = i := by
  have hNonempty : Nonempty (OrdinaryCrossingLocalBranchData
      (D.edgeArc firstEdge) x Disk.radius) := by
    rcases hDiskEdges with hlabels | hlabels
    · exact ⟨hlabels.1 ▸ Disk.firstBranch⟩
    · exact ⟨hlabels.2 ▸ Disk.secondBranch⟩
  let Br : OrdinaryCrossingLocalBranchData
      (D.edgeArc firstEdge) x Disk.radius := Classical.choice hNonempty
  refine ⟨Br, ?_⟩
  rcases Br.center_case with hsame | hvert
  · have hbefore : Br.beforeIndex = i :=
      simultaneousBigonOpenIndexUnique (D.edgeArc firstEdge) x Br.beforeIndex i
        Br.beforeIndex_valid hi hsame.2 hxOpen
    exact ⟨hbefore, hsame.1.trans hbefore⟩
  · exfalso
    have hafterValid : Br.afterIndex < (D.edgeArc firstEdge).vertices.length := by
      rw [hvert.1]
      exact Br.beforeIndex_valid
    exact (simultaneousBigonOpenNotVertices (D.edgeArc firstEdge) x i hi hxOpen)
      (by rw [hvert.2]; exact List.getElem_mem hafterValid)

private lemma simultaneousBigonHPointEdgeOrVertex
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (u : V)
    (firstEdge secondEdge : G.edgeFinset)
    (x y : EuclideanSpace ℝ (Fin 2))
    (A B Bplus H : Set (EuclideanSpace ℝ (Fin 2)))
    (hedges : firstEdge ≠ secondEdge)
    (hH : H =
      (⋃ edge : G.edgeFinset,
        if edge = firstEdge then
          (D.edgeArc edge).carrier \
            (A \ ({D.vertexPlacement u, x} : Set _))
        else if edge = secondEdge then
          (D.edgeArc edge).carrier \
            ((B \ ({D.vertexPlacement u, x} : Set _)) ∪
              (Bplus \ ({x, y} : Set _)))
        else (D.edgeArc edge).carrier) ∪
      {p | ∃ v : V, v ≠ u ∧ p = D.vertexPlacement v}) :
    ∀ z, z ∈ H →
      (∃ e : G.edgeFinset, z ∈ (D.edgeArc e).carrier) ∨
        ∃ v : V, z = D.vertexPlacement v := by
  intro z hzH
  rw [hH] at hzH
  rcases hzH with hzEdges | hzVertex
  · rcases Set.mem_iUnion.mp hzEdges with ⟨e, he⟩
    by_cases heFirst : e = firstEdge
    · subst e
      simp only [if_pos rfl] at he
      exact Or.inl ⟨firstEdge, he.1⟩
    · by_cases heSecond : e = secondEdge
      · subst e
        simp only [if_neg (Ne.symm hedges), if_pos rfl] at he
        exact Or.inl ⟨secondEdge, he.1⟩
      · simp only [if_neg heFirst, if_neg heSecond] at he
        exact Or.inl ⟨e, he⟩
  · rcases hzVertex with ⟨v, _hvu, rfl⟩
    exact Or.inr ⟨v, rfl⟩

private lemma simultaneousBigonOldPointEdgeOrVertex
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (firstEdge secondEdge : G.edgeFinset)
    (A B Bplus Rbeta H : Set (EuclideanSpace ℝ (Fin 2)))
    (hA : A ⊆ (D.edgeArc firstEdge).carrier)
    (hB : B ⊆ (D.edgeArc secondEdge).carrier)
    (hBplus : Bplus ⊆ (D.edgeArc secondEdge).carrier)
    (hRbeta : Rbeta ⊆ (D.edgeArc secondEdge).carrier)
    (hH : ∀ z, z ∈ H →
      (∃ e : G.edgeFinset, z ∈ (D.edgeArc e).carrier) ∨
        ∃ v : V, z = D.vertexPlacement v) :
    ∀ z, z ∈ A ∪ B ∪ Bplus ∪ Rbeta ∪ H →
      (∃ e : G.edgeFinset, z ∈ (D.edgeArc e).carrier) ∨
        ∃ v : V, z = D.vertexPlacement v := by
  intro z hz
  rcases hz with (((hzA | hzB) | hzBplus) | hzRbeta) | hzH
  · exact Or.inl ⟨firstEdge, hA hzA⟩
  · exact Or.inl ⟨secondEdge, hB hzB⟩
  · exact Or.inl ⟨secondEdge, hBplus hzBplus⟩
  · exact Or.inl ⟨secondEdge, hRbeta hzRbeta⟩
  · exact hH z hzH

private lemma simultaneousBigonOldLocal
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (firstEdge secondEdge : G.edgeFinset)
    (x : EuclideanSpace ℝ (Fin 2))
    (hx : x ∈ D.crossingSet)
    (Disk : OrdinaryLabeledCrossingDiskData G D ⟨x, hx⟩)
    (rhoTerm : ℝ) (Old : Set (EuclideanSpace ℝ (Fin 2)))
    (d v : EuclideanSpace ℝ (Fin 2))
    (hrhoTermDisk : rhoTerm < Disk.radius)
    (hDiskEdges :
      (Disk.firstEdge = firstEdge ∧ Disk.secondEdge = secondEdge) ∨
        (Disk.firstEdge = secondEdge ∧ Disk.secondEdge = firstEdge))
    (hOld : ∀ z, z ∈ Old →
      (∃ e : G.edgeFinset, z ∈ (D.edgeArc e).carrier) ∨
        ∃ w : V, z = D.vertexPlacement w)
    (hFirst : ∀ z, z ∈ Metric.closedBall x Disk.radius →
      z ∈ (D.edgeArc firstEdge).carrier →
        ∃ c : ℝ, z = x + c • d)
    (hSecond : ∀ z, z ∈ Metric.closedBall x Disk.radius →
      z ∈ (D.edgeArc secondEdge).carrier →
        ∃ c : ℝ, z = x + c • v) :
    Metric.closedBall x rhoTerm ∩ Old ⊆
      {z | ∃ c : ℝ, z = x + c • d} ∪
        {z | ∃ c : ℝ, z = x + c • v} := by
  intro z hz
  have hzDisk : z ∈ Metric.closedBall x Disk.radius :=
    Metric.closedBall_subset_closedBall hrhoTermDisk.le hz.1
  rcases hOld z hz.2 with ⟨e, hze⟩ | ⟨w, hzw⟩
  · have hzAll : z ∈ Metric.closedBall x Disk.radius ∩
        (⋃ e : G.edgeFinset, (D.edgeArc e).carrier) :=
      ⟨hzDisk, Set.mem_iUnion.mpr ⟨e, hze⟩⟩
    rw [Disk.exact_local_drawing_carrier] at hzAll
    rcases hzAll.2 with hzFirstDisk | hzSecondDisk
    · rcases hDiskEdges with hlabels | hlabels
      · exact Or.inl (hFirst z hzDisk (by simpa [hlabels.1] using hzFirstDisk))
      · exact Or.inr (hSecond z hzDisk (by simpa [hlabels.1] using hzFirstDisk))
    · rcases hDiskEdges with hlabels | hlabels
      · exact Or.inr (hSecond z hzDisk (by simpa [hlabels.2] using hzSecondDisk))
      · exact Or.inl (hFirst z hzDisk (by simpa [hlabels.2] using hzSecondDisk))
  · subst z
    exact False.elim (Disk.no_vertex_in_closedBall w hzDisk)

private def simultaneousBigonOtherSegments
    (Q : PolygonalArc)
    (eventIndex : EuclideanSpace ℝ (Fin 2) → ℕ)
    (p : EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ k : Fin (Q.vertices.length - 1),
    if k.1 = eventIndex p then ∅
    else segment ℝ Q.vertices[k.1] Q.vertices[k.1 + 1]

private lemma simultaneousBigonOtherSegmentsCompact
    (Q : PolygonalArc)
    (eventIndex : EuclideanSpace ℝ (Fin 2) → ℕ)
    (p : EuclideanSpace ℝ (Fin 2)) :
    IsCompact (simultaneousBigonOtherSegments Q eventIndex p) := by
  dsimp [simultaneousBigonOtherSegments]
  apply isCompact_iUnion
  intro k
  split_ifs
  · exact isCompact_empty
  · rw [segment_eq_image' ℝ]
    exact isCompact_Icc.image (by fun_prop)

private lemma simultaneousBigonEventNotOther
    (Q : PolygonalArc) (p : EuclideanSpace ℝ (Fin 2)) (eventIndex : ℕ)
    (hj : eventIndex + 1 < Q.vertices.length)
    (hpOpen : p ∈ openSegment ℝ Q.vertices[eventIndex]
      Q.vertices[eventIndex + 1]) :
    p ∉ simultaneousBigonOtherSegments Q (fun _ => eventIndex) p := by
  intro hpOther
  simp only [simultaneousBigonOtherSegments, Set.mem_iUnion] at hpOther
  rcases hpOther with ⟨k, hpOther⟩
  split_ifs at hpOther with hkEq
  · exact hpOther
  · have hk : k.1 + 1 < Q.vertices.length := by
      have hlen := Q.length_ge_two
      have hklt := k.2
      omega
    have hpOwner : p ∈ segment ℝ Q.vertices[eventIndex]
        Q.vertices[eventIndex + 1] :=
      openSegment_subset_segment ℝ _ _ hpOpen
    rcases lt_trichotomy k.1 eventIndex with hlt | heq | hgt
    · have hinter := Q.segment_intersections hk hj hlt
      have hpInter : p ∈
          segment ℝ Q.vertices[k.1] Q.vertices[k.1 + 1] ∩
            segment ℝ Q.vertices[eventIndex] Q.vertices[eventIndex + 1] :=
        ⟨hpOther, hpOwner⟩
      rw [hinter] at hpInter
      split_ifs at hpInter with hadj
      · have hpVertex : p = Q.vertices[eventIndex] := by simpa using hpInter
        exact (simultaneousBigonOpenNotVertices Q p eventIndex hj hpOpen)
          (by rw [hpVertex]; exact List.getElem_mem (by omega))
      · exact hpInter

    · exact hkEq heq
    · have hinter := Q.segment_intersections hj hk hgt
      have hpInter : p ∈
          segment ℝ Q.vertices[eventIndex] Q.vertices[eventIndex + 1] ∩
            segment ℝ Q.vertices[k.1] Q.vertices[k.1 + 1] :=
        ⟨hpOwner, hpOther⟩
      rw [hinter] at hpInter
      split_ifs at hpInter with hadj
      · have hpVertex : p = Q.vertices[k.1] := by simpa using hpInter
        exact (simultaneousBigonOpenNotVertices Q p eventIndex hj hpOpen)
          (by rw [hpVertex]; exact List.getElem_mem (by omega))
      · exact hpInter

private lemma simultaneousBigonInitialLeftChartEq
    (Q : PolygonalArc) (p : EuclideanSpace ℝ (Fin 2))
    (hfirst : 0 + 1 < Q.vertices.length) (hp : Q.source = p)
    (r k : ℝ) :
    let d0 : EuclideanSpace ℝ (Fin 2) := Q.vertices[1] - Q.source
    (fun z : EuclideanSpace ℝ (Fin 2) =>
      p + z 0 • d0 + z 1 • PlanarRot90 d0) ''
        {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖d0‖) ^ 2 ∧
          0 < z 1 ∧ z 1 < k * z 0} =
      (fun z : EuclideanSpace ℝ (Fin 2) =>
        Q.vertices[0] + z 0 • (Q.vertices[1] - Q.vertices[0]) +
          z 1 • PlanarRot90 (Q.vertices[1] - Q.vertices[0])) ''
        {z | 0 < z 0 ∧
          z 0 ^ 2 + z 1 ^ 2 < (r / dist Q.vertices[0] Q.vertices[1]) ^ 2 ∧
          0 < z 1 ∧ z 1 < k * z 0} := by
  dsimp only
  rw [simultaneousBigonSourceAtZero Q (by omega), hp]
  simp only [dist_eq_norm, norm_sub_rev]

private lemma simultaneousBigonInitialRightChartEq
    (Q : PolygonalArc) (p : EuclideanSpace ℝ (Fin 2))
    (hfirst : 0 + 1 < Q.vertices.length) (hp : Q.source = p)
    (r k : ℝ) :
    let d0 : EuclideanSpace ℝ (Fin 2) := Q.vertices[1] - Q.source
    (fun z : EuclideanSpace ℝ (Fin 2) =>
      p + z 0 • d0 + z 1 • PlanarRot90 d0) ''
        {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖d0‖) ^ 2 ∧
          -k * z 0 < z 1 ∧ z 1 < 0} =
      (fun z : EuclideanSpace ℝ (Fin 2) =>
        Q.vertices[0] + z 0 • (Q.vertices[1] - Q.vertices[0]) +
          z 1 • PlanarRot90 (Q.vertices[1] - Q.vertices[0])) ''
        {z | 0 < z 0 ∧
          z 0 ^ 2 + z 1 ^ 2 < (r / dist Q.vertices[0] Q.vertices[1]) ^ 2 ∧
          -k * z 0 < z 1 ∧ z 1 < 0} := by
  dsimp only
  rw [simultaneousBigonSourceAtZero Q (by omega), hp]
  simp only [dist_eq_norm, norm_sub_rev]

private lemma simultaneousBigonReflectLeftCone
    (x d : EuclideanSpace ℝ (Fin 2)) (cap k : ℝ) :
    (fun z : EuclideanSpace ℝ (Fin 2) =>
      x + z 0 • d + z 1 • PlanarRot90 d) ''
        {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < cap ^ 2 ∧
          -k * z 0 < z 1 ∧ z 1 < 0} =
      (fun z : EuclideanSpace ℝ (Fin 2) =>
        x + z 0 • d + z 1 • (-PlanarRot90 d)) ''
        {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < cap ^ 2 ∧
          0 < z 1 ∧ z 1 < k * z 0} := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    let w : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![z 0, -z 1]
    refine ⟨w, ?_, ?_⟩
    · dsimp [w]
      constructor
      · exact hz.1
      constructor
      · nlinarith [hz.2.1]
      constructor <;> linarith [hz.2.2.1, hz.2.2.2]
    · simp only [w, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, one_smul, neg_smul]
      module
  · rintro ⟨z, hz, rfl⟩
    let w : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![z 0, -z 1]
    refine ⟨w, ?_, ?_⟩
    · dsimp [w]
      constructor
      · exact hz.1
      constructor
      · nlinarith [hz.2.1]
      constructor <;> linarith [hz.2.2.1, hz.2.2.2]
    · simp only [w, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, one_smul, neg_smul]
      module

private lemma simultaneousBigonTargetSideNear
    (Q : PolygonalArc) (eta : ℝ)
    (controlRadii : PolygonalArcCollarControlRadii Q eta)
    (middleSegments : PolygonalArcCollarMiddleSegmentData Q controlRadii)
    (forbiddenMargins : PolygonalArcCollarMiddleForbiddenMargins
      Q controlRadii middleSegments)
    (compatibleTubes : PolygonalArcCollarCompatibleOrientedTubeData
      Q controlRadii middleSegments forbiddenMargins)
    (vertexLocalPieces : PolygonalArcCollarVertexLocalPieceData Q
      controlRadii middleSegments forbiddenMargins
      compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData)
    (localSideData : PolygonalArcCollarLocalSideData Q controlRadii
      middleSegments forbiddenMargins compatibleTubes.orientedTubes
      vertexLocalPieces)
    (S : PolygonalSideStrips Q)
    (x : EuclideanSpace ℝ (Fin 2))
    (targetIndex : Fin Q.vertices.length) (jlast : ℕ)
    (hjlast : jlast + 1 < Q.vertices.length)
    (hjlastTarget : jlast + 1 = targetIndex.1)
    (htargetLast : targetIndex.1 + 1 = Q.vertices.length)
    (htargetVertex : Q.vertices[targetIndex.1] = x)
    (positiveSide : Prop)
    (hLeftEq : S.leftStrip =
      ((⋃ (j : ℕ), ⋃ (hj : j + 1 < Q.vertices.length),
          compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf
            j hj) ∪
        (⋃ i : Fin Q.vertices.length, localSideData.leftSidePiece i)))
    (hRightEq : S.rightStrip =
      ((⋃ (j : ℕ), ⋃ (hj : j + 1 < Q.vertices.length),
          compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf
            j hj) ∪
        (⋃ i : Fin Q.vertices.length, localSideData.rightSidePiece i))) :
    let SelectedSide := if positiveSide then S.rightStrip else S.leftStrip
    let Vin := if positiveSide then localSideData.rightSidePiece targetIndex
      else localSideData.leftSidePiece targetIndex
    ∃ eps : ℝ, 0 < eps ∧ SelectedSide ∩ Metric.ball x eps ⊆ Vin := by
  dsimp only
  let sep := compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
  refine ⟨controlRadii.radius targetIndex, controlRadii.radius_pos targetIndex, ?_⟩
  intro q hq
  have hqTargetDisk : q ∈ vertexLocalPieces.vertexDisk targetIndex := by
    rw [vertexLocalPieces.vertexDisk_eq]
    simpa [htargetVertex] using hq.2
  have hqTargetClosed : q ∈
      Metric.closedBall Q.vertices[targetIndex.1]
        (controlRadii.radius targetIndex) :=
    vertexLocalPieces.vertexDisk_subset_closed_control_disk targetIndex hqTargetDisk
  have tubeNonterminalImpossible (k : ℕ)
      (hk : k + 1 < Q.vertices.length) (hklast : k ≠ jlast)
      (hqTube : q ∈ sep.tube k hk) : False := by
    have hkTarget : targetIndex.1 ≠ k := by omega
    have hkTargetSucc : targetIndex.1 ≠ k + 1 := by omega
    exact Set.disjoint_left.mp
      (vertexLocalPieces.vertexDisk_disjoint_nonincident_tubes
        targetIndex k hk hkTarget hkTargetSucc) hqTargetDisk hqTube
  have vertexNontargetImpossible (idx : Fin Q.vertices.length)
      (hne : idx ≠ targetIndex)
      (hqPiece : q ∈ localSideData.vertexCollar idx) : False := by
    have hqDisk := localSideData.vertexCollar_subset_vertexDisk idx hqPiece
    exact Set.disjoint_left.mp
      (vertexLocalPieces.vertexDisk_disjoint_other_control_disks hne)
        hqDisk hqTargetClosed
  by_cases hpos : positiveSide
  · have hqRight : q ∈ S.rightStrip := by simpa [hpos] using hq.1
    rw [hRightEq] at hqRight
    rcases hqRight with hqHalf | hqPiece
    · rcases Set.mem_iUnion.mp hqHalf with ⟨k, hkUnion⟩
      rcases Set.mem_iUnion.mp hkUnion with ⟨hk, hqHalf⟩
      by_cases hklast : k = jlast
      · subst k
        have hqAttach : q ∈
            vertexLocalPieces.incomingRightAttachment jlast hjlast := by
          rw [vertexLocalPieces.incomingRightAttachment_eq]
          exact ⟨by simpa [hjlastTarget] using hqTargetDisk,
            by simpa [sep] using hqHalf⟩
        have hqVin := localSideData.incomingRightAttachment_subset_rightSidePiece
          jlast hjlast hqAttach
        simpa [hpos, hjlastTarget] using hqVin
      · exact False.elim (tubeNonterminalImpossible k hk hklast
          (sep.rightHalf_subset_tube k hk (by simpa [sep] using hqHalf)))
    · rcases Set.mem_iUnion.mp hqPiece with ⟨idx, hqPiece⟩
      by_cases hidx : idx = targetIndex
      · subst idx
        simpa [hpos] using hqPiece
      · exact False.elim (vertexNontargetImpossible idx hidx
          (localSideData.rightSidePiece_subset_vertexCollar idx hqPiece))
  · have hqLeft : q ∈ S.leftStrip := by simpa [hpos] using hq.1
    rw [hLeftEq] at hqLeft
    rcases hqLeft with hqHalf | hqPiece
    · rcases Set.mem_iUnion.mp hqHalf with ⟨k, hkUnion⟩
      rcases Set.mem_iUnion.mp hkUnion with ⟨hk, hqHalf⟩
      by_cases hklast : k = jlast
      · subst k
        have hqAttach : q ∈
            vertexLocalPieces.incomingLeftAttachment jlast hjlast := by
          rw [vertexLocalPieces.incomingLeftAttachment_eq]
          exact ⟨by simpa [hjlastTarget] using hqTargetDisk,
            by simpa [sep] using hqHalf⟩
        have hqVin := localSideData.incomingLeftAttachment_subset_leftSidePiece
          jlast hjlast hqAttach
        simpa [hpos, hjlastTarget] using hqVin
      · exact False.elim (tubeNonterminalImpossible k hk hklast
          (sep.leftHalf_subset_tube k hk (by simpa [sep] using hqHalf)))
    · rcases Set.mem_iUnion.mp hqPiece with ⟨idx, hqPiece⟩
      by_cases hidx : idx = targetIndex
      · subst idx
        simpa [hpos] using hqPiece
      · exact False.elim (vertexNontargetImpossible idx hidx
          (localSideData.leftSidePiece_subset_vertexCollar idx hqPiece))
private lemma simultaneousBigonLeftHalfConvex
    (Q : PolygonalArc) {eta : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii Q eta)
    (middleSegments : PolygonalArcCollarMiddleSegmentData Q controlRadii)
    (forbiddenMargins : PolygonalArcCollarMiddleForbiddenMargins
      Q controlRadii middleSegments)
    (sep : PolygonalArcCollarSeparatedTubeData Q controlRadii middleSegments
      forbiddenMargins)
    (m : ℕ) (hm : m + 1 < Q.vertices.length) :
    Convex ℝ (sep.leftHalf m hm) := by
  rw [sep.leftHalf_eq]
  intro z₁ hz₁ z₂ hz₂ a b ha hb hab
  rcases hz₁ with ⟨t₁, ht₁, s₁, hs₁, rfl⟩
  rcases hz₂ with ⟨t₂, ht₂, s₂, hs₂, rfl⟩
  refine ⟨a * t₁ + b * t₂,
    (convex_Ioo (sep.lowerParam m hm) (sep.upperParam m hm))
      ht₁ ht₂ ha hb hab,
    a * s₁ + b * s₂,
    (convex_Ioo 0 (sep.halfWidth m hm)) hs₁ hs₂ ha hb hab, ?_⟩
  simp only [AffineMap.lineMap_apply_module]
  have hb' : b = 1 - a := by linarith
  subst b
  module

private lemma simultaneousBigonRightHalfConvex
    (Q : PolygonalArc) {eta : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii Q eta)
    (middleSegments : PolygonalArcCollarMiddleSegmentData Q controlRadii)
    (forbiddenMargins : PolygonalArcCollarMiddleForbiddenMargins
      Q controlRadii middleSegments)
    (sep : PolygonalArcCollarSeparatedTubeData Q controlRadii middleSegments
      forbiddenMargins)
    (m : ℕ) (hm : m + 1 < Q.vertices.length) :
    Convex ℝ (sep.rightHalf m hm) := by
  rw [sep.rightHalf_eq]
  intro z₁ hz₁ z₂ hz₂ a b ha hb hab
  rcases hz₁ with ⟨t₁, ht₁, s₁, hs₁, rfl⟩
  rcases hz₂ with ⟨t₂, ht₂, s₂, hs₂, rfl⟩
  refine ⟨a * t₁ + b * t₂,
    (convex_Ioo (sep.lowerParam m hm) (sep.upperParam m hm))
      ht₁ ht₂ ha hb hab,
    a * s₁ + b * s₂,
    (convex_Ioo (-sep.halfWidth m hm) 0) hs₁ hs₂ ha hb hab, ?_⟩
  simp only [AffineMap.lineMap_apply_module]
  have hb' : b = 1 - a := by linarith
  subst b
  module

private lemma simultaneousBigonOneEventSelectedSlice
    (Q : PolygonalArc) (eta : ℝ)
    (controlRadii : PolygonalArcCollarControlRadii Q eta)
    (middleSegments : PolygonalArcCollarMiddleSegmentData Q controlRadii)
    (forbiddenMargins : PolygonalArcCollarMiddleForbiddenMargins
      Q controlRadii middleSegments)
    (compatibleTubes : PolygonalArcCollarCompatibleOrientedTubeData
      Q controlRadii middleSegments forbiddenMargins)
    (vertexLocalPieces : PolygonalArcCollarVertexLocalPieceData Q
      controlRadii middleSegments forbiddenMargins
      compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData)
    (localSideData : PolygonalArcCollarLocalSideData Q controlRadii
      middleSegments forbiddenMargins compatibleTubes.orientedTubes
      vertexLocalPieces)
    (S : PolygonalSideStrips Q)
    (p : EuclideanSpace ℝ (Fin 2))
    (owner : ℕ) (hOwner : owner + 1 < Q.vertices.length)
    (eventRadius eventClearance : ℝ)
    (eventForbidden : Set (EuclideanSpace ℝ (Fin 2)))
    (positiveSide : Prop)
    (heta : 0 < eta)
    (hEtaRadius : eta < eventRadius)
    (hRadiusClearance : eventRadius < eventClearance / 4)
    (hClearanceAvoid : Metric.ball p eventClearance ⊆ eventForbiddenᶜ)
    (hVertexForbidden : ∀ idx : Fin Q.vertices.length,
      Q.vertices[idx.1] ∈ eventForbidden)
    (hOtherForbidden : ∀ m (hm : m + 1 < Q.vertices.length), m ≠ owner →
      segment ℝ Q.vertices[m] Q.vertices[m + 1] ⊆ eventForbidden)
    (hLeftEq : S.leftStrip =
      ((⋃ (j : ℕ), ⋃ (hj : j + 1 < Q.vertices.length),
          compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf
            j hj) ∪
        (⋃ i : Fin Q.vertices.length, localSideData.leftSidePiece i)))
    (hRightEq : S.rightStrip =
      ((⋃ (j : ℕ), ⋃ (hj : j + 1 < Q.vertices.length),
          compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf
            j hj) ∪
        (⋃ i : Fin Q.vertices.length, localSideData.rightSidePiece i))) :
    (if positiveSide then S.rightStrip else S.leftStrip) ∩
        Metric.ball p eventRadius =
      (if positiveSide then
          compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf
            owner hOwner
        else
          compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf
            owner hOwner) ∩ Metric.ball p eventRadius := by
  let sep := compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
  apply Set.Subset.antisymm
  · rintro q ⟨hqSelected, hqBall⟩
    have hqdist : dist p q < eventRadius := by
      simpa [Metric.mem_ball, dist_comm] using hqBall
    have vertexPieceImpossible (idx : Fin Q.vertices.length)
        (hqPiece : q ∈ localSideData.vertexCollar idx) : False := by
      have hqDisk := localSideData.vertexCollar_subset_vertexDisk idx hqPiece
      rw [vertexLocalPieces.vertexDisk_eq] at hqDisk
      have hqv : dist q Q.vertices[idx.1] < controlRadii.radius idx := by
        simpa [Metric.mem_ball] using hqDisk
      have hvball : Q.vertices[idx.1] ∈ Metric.ball p eventClearance := by
        rw [Metric.mem_ball]
        calc
          dist Q.vertices[idx.1] p = dist p Q.vertices[idx.1] := dist_comm _ _
          _ ≤ dist p q + dist q Q.vertices[idx.1] := dist_triangle _ _ _
          _ < eventRadius + eta := by linarith [controlRadii.radius_lt_eta idx]
          _ < eventClearance := by linarith
      exact (hClearanceAvoid hvball) (hVertexForbidden idx)
    have halfIndexEq (m : ℕ) (hm : m + 1 < Q.vertices.length)
        (s : ℝ) (hsabs : |s| < sep.halfWidth m hm)
        (t : ℝ) (ht : t ∈ Set.Ioo (sep.lowerParam m hm) (sep.upperParam m hm))
        (hqFormula : q = AffineMap.lineMap Q.vertices[m]
          Q.vertices[m + 1] t + s • sep.normal m hm) : m = owner := by
      by_contra hmOwner
      let center := AffineMap.lineMap Q.vertices[m] Q.vertices[m + 1] t
      have ht01 : t ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨(sep.lowerParam_pos m hm).le.trans ht.1.le,
          ht.2.le.trans (sep.upperParam_lt_one m hm).le⟩
      have hcenterSegment : center ∈ segment ℝ Q.vertices[m] Q.vertices[m + 1] := by
        rw [segment_eq_image_lineMap]
        exact ⟨t, ht01, rfl⟩
      have hqcenter : dist q center < eta := by
        rw [hqFormula, dist_eq_norm]
        have hsub : center + s • sep.normal m hm - center =
            s • sep.normal m hm := by abel
        rw [hsub, norm_smul, Real.norm_eq_abs]
        have hvertices : Q.vertices[m] ≠ Q.vertices[m + 1] := by
          intro heq
          have hidx := (Q.simple_vertices.getElem_inj_iff
            (i := m) (j := m + 1) (hi := by omega) (hj := hm)).1 heq
          omega
        have hnormpos : 0 < ‖sep.normal m hm‖ := by
          rw [sep.normal_norm_eq_segment_length m hm]
          exact dist_pos.mpr hvertices
        exact (mul_lt_mul_of_pos_right hsabs hnormpos).trans
          (sep.halfWidth_mul_normal_norm_lt_eta m hm)
      have hcenterBall : center ∈ Metric.ball p eventClearance := by
        rw [Metric.mem_ball]
        calc
          dist center p = dist p center := dist_comm _ _
          _ ≤ dist p q + dist q center := dist_triangle _ _ _
          _ < eventRadius + eta := by linarith
          _ < eventClearance := by linarith
      exact (hClearanceAvoid hcenterBall)
        (hOtherForbidden m hm hmOwner hcenterSegment)
    by_cases hpos : positiveSide
    · have hqRight : q ∈ S.rightStrip := by simpa [hpos] using hqSelected
      rw [hRightEq] at hqRight
      rcases hqRight with hqHalf | hqPiece
      · rcases Set.mem_iUnion.mp hqHalf with ⟨m, hqHalf⟩
        rcases Set.mem_iUnion.mp hqHalf with ⟨hm, hqHalf⟩
        rw [sep.rightHalf_eq] at hqHalf
        rcases hqHalf with ⟨t, ht, s, hs, hqFormula⟩
        have hsabs : |s| < sep.halfWidth m hm := by
          rw [abs_of_neg hs.2]
          simpa using neg_lt_neg hs.1
        have hmOwner := halfIndexEq m hm s hsabs t ht hqFormula
        subst m
        exact ⟨by simpa [hpos, sep] using
          (show q ∈ sep.rightHalf owner hOwner from
            (by rw [sep.rightHalf_eq]; exact ⟨t, ht, s, hs, hqFormula⟩)), hqBall⟩
      · rcases Set.mem_iUnion.mp hqPiece with ⟨idx, hqPiece⟩
        exact False.elim (vertexPieceImpossible idx
          (localSideData.rightSidePiece_subset_vertexCollar idx hqPiece))
    · have hqLeft : q ∈ S.leftStrip := by simpa [hpos] using hqSelected
      rw [hLeftEq] at hqLeft
      rcases hqLeft with hqHalf | hqPiece
      · rcases Set.mem_iUnion.mp hqHalf with ⟨m, hqHalf⟩
        rcases Set.mem_iUnion.mp hqHalf with ⟨hm, hqHalf⟩
        rw [sep.leftHalf_eq] at hqHalf
        rcases hqHalf with ⟨t, ht, s, hs, hqFormula⟩
        have hsabs : |s| < sep.halfWidth m hm := by
          rw [abs_of_pos hs.1]
          exact hs.2
        have hmOwner := halfIndexEq m hm s hsabs t ht hqFormula
        subst m
        exact ⟨by simpa [hpos, sep] using
          (show q ∈ sep.leftHalf owner hOwner from
            (by rw [sep.leftHalf_eq]; exact ⟨t, ht, s, hs, hqFormula⟩)), hqBall⟩
      · rcases Set.mem_iUnion.mp hqPiece with ⟨idx, hqPiece⟩
        exact False.elim (vertexPieceImpossible idx
          (localSideData.leftSidePiece_subset_vertexCollar idx hqPiece))
  · rintro q ⟨hqHalf, hqBall⟩
    refine ⟨?_, hqBall⟩
    by_cases hpos : positiveSide
    · simp only [if_pos hpos]
      rw [hRightEq]
      exact Or.inl (Set.mem_iUnion.mpr ⟨owner,
        Set.mem_iUnion.mpr ⟨hOwner, by simpa [hpos, sep] using hqHalf⟩⟩)
    · simp only [if_neg hpos]
      rw [hLeftEq]
      exact Or.inl (Set.mem_iUnion.mpr ⟨owner,
        Set.mem_iUnion.mpr ⟨hOwner, by simpa [hpos, sep] using hqHalf⟩⟩)

private lemma simultaneousBigonEventClean
    (Q : PolygonalArc)
    (points : Finset (EuclideanSpace ℝ (Fin 2)))
    (segments : Finset
      (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (XA : Finset (EuclideanSpace ℝ (Fin 2)))
    (eventIndex : EuclideanSpace ℝ (Fin 2) → ℕ)
    (hnot : ∀ p, p ∈ XA → p ∉ (points : Set _))
    (hspec : ∀ p, p ∈ XA →
      ∃ hm : eventIndex p + 1 < Q.vertices.length,
        p ∈ openSegment ℝ Q.vertices[eventIndex p]
          Q.vertices[eventIndex p + 1] ∧
        ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          s ∈ segments ∧ p ∈ openSegment ℝ s.1 s.2 ∧
          (¬ ∃ c : ℝ, s.2 - s.1 =
            c • (Q.vertices[eventIndex p + 1] - Q.vertices[eventIndex p])) ∧
          ∀ t, t ∈ segments → p ∈ openSegment ℝ t.1 t.2 → t = s) :
    ∀ p, p ∈ XA →
      p ∉ (points : Set _) ∧
        ∃ m : ℕ, ∃ hm : m + 1 < Q.vertices.length,
          p ∈ openSegment ℝ Q.vertices[m] Q.vertices[m + 1] ∧
          ∃! s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
            s ∈ segments ∧ p ∈ openSegment ℝ s.1 s.2 ∧
              ¬ ∃ c : ℝ, s.2 - s.1 =
                c • (Q.vertices[m + 1] - Q.vertices[m]) := by
  intro p hp
  obtain ⟨hm, hpOpen, s, hs, hps, hnonparallel, hunique⟩ := hspec p hp
  refine ⟨hnot p hp, eventIndex p, hm, hpOpen, s,
    ⟨hs, hps, hnonparallel⟩, ?_⟩
  intro t ht
  exact hunique t ht.1 ht.2.1

private lemma simultaneousBigonIteIntersectionEmpty
    {α : Type*} (P : Prop) [Decidable P] {L R T : Set α}
    (hL : L ∩ T = ∅) (hR : R ∩ T = ∅) :
    (if P then R else L) ∩ T = ∅ := by
  by_cases hP : P
  · simpa [hP] using hR
  · simpa [hP] using hL

private lemma simultaneousBigonIteIsOpen
    {α : Type*} [TopologicalSpace α] (P : Prop) [Decidable P]
    {L R : Set α} (hL : IsOpen L) (hR : IsOpen R) :
    IsOpen (if P then R else L) := by
  by_cases hP : P
  · simpa [hP] using hR
  · simpa [hP] using hL

private lemma simultaneousBigonIteConvex
    (P : Prop) [Decidable P]
    {L R : Set (EuclideanSpace ℝ (Fin 2))}
    (hL : Convex ℝ L) (hR : Convex ℝ R) :
    Convex ℝ (if P then R else L) := by
  by_cases hP : P
  · simpa [hP] using hR
  · simpa [hP] using hL

private lemma simultaneousBigonIteSubset
    {α : Type*} (P : Prop) [Decidable P] {L R T : Set α}
    (hL : L ⊆ T) (hR : R ⊆ T) : (if P then R else L) ⊆ T := by
  by_cases hP : P
  · simpa [hP] using hR
  · simpa [hP] using hL

private lemma simultaneousBigonIteEqLeftOrRight
    {α : Type*} (P : Prop) [Decidable P] (L R : Set α) :
    (if P then R else L) = L ∨ (if P then R else L) = R := by
  by_cases hP : P
  · exact Or.inr (by simp [hP])
  · exact Or.inl (by simp [hP])

private lemma simultaneousBigonClosureSubsetClosedBall
    {α : Type*} [PseudoMetricSpace α]
    (S : Set α) (p : α) (r R : ℝ)
    (hS : S ⊆ Metric.ball p r) (hr : r ≤ R) :
    closure S ⊆ Metric.closedBall p R := by
  apply closure_minimal
  · exact hS.trans (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall hr))
  · exact Metric.isClosed_closedBall

private lemma simultaneousBigonMemClosureIte
    {α : Type*} [TopologicalSpace α] (P : Prop) [Decidable P]
    {p : α} {L R : Set α} (hL : p ∈ closure L) (hR : p ∈ closure R) :
    p ∈ closure (if P then R else L) := by
  by_cases hP : P
  · simpa [hP] using hR
  · simpa [hP] using hL

private lemma simultaneousBigonNotMemIte
    {α : Type*} (P : Prop) [Decidable P] {p : α} {L R : Set α}
    (hL : p ∉ L) (hR : p ∉ R) : p ∉ (if P then R else L) := by
  by_cases hP : P
  · simpa [hP] using hR
  · simpa [hP] using hL

private lemma simultaneousBigonStartAvoidAxis
    (p d : EuclideanSpace ℝ (Fin 2)) (hd : d ≠ 0)
    (positiveSide : Prop) (leftSector rightSector : Set (EuclideanSpace ℝ (Fin 2)))
    (hLeft : ∀ q, q ∈ leftSector →
      ∃ z : EuclideanSpace ℝ (Fin 2), 0 < z 1 ∧
        q = p + z 0 • d + z 1 • PlanarRot90 d)
    (hRight : ∀ q, q ∈ rightSector →
      ∃ z : EuclideanSpace ℝ (Fin 2), z 1 < 0 ∧
        q = p + z 0 • d + z 1 • PlanarRot90 d) :
    (if positiveSide then rightSector else leftSector) ∩
      {q | ∃ c : ℝ, 0 ≤ c ∧ q = p + c • d} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  rcases hq.2 with ⟨c, _hc, hqAxis⟩
  have axisCoefficientZero :
      inner ℝ (q - p) (PlanarRot90 d) / (‖d‖ ^ 2) = 0 := by
    rw [hqAxis]
    simp only [add_sub_cancel_left, inner_smul_left, PlanarRot90Orthogonal,
      mul_zero, zero_div]
  by_cases hpos : positiveSide
  · obtain ⟨z, hzneg, hqFormula⟩ := hRight q (by simpa [hpos] using hq.1)
    have hrep : q - p = z 0 • d + z 1 • PlanarRot90 d := by
      rw [hqFormula]
      abel
    have hcoeff := PlanarRot90CoefficientUniqueness (d := d) (v := q - p) hd hrep
    have hz1 : z 1 = 0 := hcoeff.2.trans axisCoefficientZero
    linarith
  · obtain ⟨z, hzpos, hqFormula⟩ := hLeft q (by simpa [hpos] using hq.1)
    have hrep : q - p = z 0 • d + z 1 • PlanarRot90 d := by
      rw [hqFormula]
      abel
    have hcoeff := PlanarRot90CoefficientUniqueness (d := d) (v := q - p) hd hrep
    have hz1 : z 1 = 0 := hcoeff.2.trans axisCoefficientZero
    linarith

private lemma simultaneousBigonStartAvoidOld
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (firstEdge : G.edgeFinset)
    (Start Old Bad : Set (EuclideanSpace ℝ (Fin 2)))
    (hBadOld : Bad ⊆ Old)
    (hOld : ∀ q, q ∈ Old →
      (∃ e : G.edgeFinset, q ∈ (D.edgeArc e).carrier) ∨
        ∃ v : V, q = D.vertexPlacement v)
    (hFirst : Start ∩ (D.edgeArc firstEdge).carrier = ∅)
    (hWithout : Start ∩ OrdinaryDrawingImageWithoutEdge G D firstEdge = ∅) :
    Start ∩ (Old ∪ Bad) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hqOld : q ∈ Old := hq.2.elim id (fun h => hBadOld h)
  rcases hOld q hqOld with ⟨e, hqe⟩ | ⟨v, hqv⟩
  · by_cases he : e = firstEdge
    · subst e
      exact Set.eq_empty_iff_forall_notMem.mp hFirst q ⟨hq.1, hqe⟩
    · have hqWithout : q ∈ OrdinaryDrawingImageWithoutEdge G D firstEdge :=
        Or.inr (Set.mem_iUnion.mpr ⟨⟨e, he⟩, hqe⟩)
      exact Set.eq_empty_iff_forall_notMem.mp hWithout q ⟨hq.1, hqWithout⟩
  · have hqWithout : q ∈ OrdinaryDrawingImageWithoutEdge G D firstEdge :=
      Or.inl ⟨v, hqv.symm⟩
    exact Set.eq_empty_iff_forall_notMem.mp hWithout q ⟨hq.1, hqWithout⟩

private lemma simultaneousBigonIntersectionEmptyOfLocalCover
    {X : Type*} (Small Wide Local Image Cover : Set X)
    (hSmallWide : Small ⊆ Wide) (hSmallLocal : Small ⊆ Local)
    (hCover : Local ∩ Image ⊆ Cover) (hWideCover : Wide ∩ Cover = ∅) :
    Small ∩ Image = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  exact Set.eq_empty_iff_forall_notMem.mp hWideCover q
    ⟨hSmallWide hq.1, hCover ⟨hSmallLocal hq.1, hq.2⟩⟩

private lemma simultaneousBigonAvoidOld
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (firstEdge : G.edgeFinset)
    (Start Old : Set (EuclideanSpace ℝ (Fin 2)))
    (hOld : ∀ q, q ∈ Old →
      (∃ e : G.edgeFinset, q ∈ (D.edgeArc e).carrier) ∨
        ∃ v : V, q = D.vertexPlacement v)
    (hFirst : Start ∩ (D.edgeArc firstEdge).carrier = ∅)
    (hWithout : Start ∩ OrdinaryDrawingImageWithoutEdge G D firstEdge = ∅) :
    Start ∩ Old = ∅ := by
  simpa using simultaneousBigonStartAvoidOld G D firstEdge Start Old ∅
    (by simp) hOld hFirst hWithout

private lemma simultaneousBigonEndpointOutsideClosedBall
    (a x g : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (ha : a ≠ x) (hgOpen : g ∈ openSegment ℝ a x)
    (hgSphere : g ∈ Metric.sphere x r) :
    a ∉ Metric.closedBall x r := by
  rw [openSegment_eq_image_lineMap] at hgOpen
  rcases hgOpen with ⟨t, ht, rfl⟩
  intro haBall
  have hdistA : dist x a ≤ r := by
    simpa [Metric.mem_closedBall, dist_comm] using haBall
  have hdistApos : 0 < dist x a := dist_pos.mpr ha.symm
  have hlineDist :
      dist (AffineMap.lineMap a x t) x = (1 - t) * dist x a := by
    rw [dist_eq_norm]
    have hdiff : AffineMap.lineMap a x t - x = (1 - t) • (a - x) := by
      simp only [AffineMap.lineMap_apply_module]
      module
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht.2)]
    rw [dist_eq_norm]
    simpa [norm_sub_rev] using rfl
  have hsphere : dist (AffineMap.lineMap a x t) x = r := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hgSphere
  rw [hlineDist] at hsphere
  have htDistPos : 0 < t * dist x a := mul_pos ht.1 hdistApos
  have himpossible : r < r := calc
    r = (1 - t) * dist x a := hsphere.symm
    _ = dist x a - t * dist x a := by ring
    _ < dist x a := sub_lt_self _ htDistPos
    _ ≤ r := hdistA
  exact lt_irrefl _ himpossible

private lemma simultaneousBigonSegmentEndpointsOutsideClosedBall
    (Q : PolygonalArc) (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (i : ℕ) (hi : i + 1 < Q.vertices.length)
    (hxOpen : x ∈ openSegment ℝ Q.vertices[i] Q.vertices[i + 1])
    (Br : OrdinaryCrossingLocalBranchData Q x r)
    (hIndices : Br.beforeIndex = i ∧ Br.afterIndex = i) :
    Q.vertices[i] ∉ Metric.closedBall x r ∧
      Q.vertices[i + 1] ∉ Metric.closedBall x r := by
  constructor
  · apply simultaneousBigonEndpointOutsideClosedBall
    · intro heq
      have hne : Q.vertices[i] ≠ Q.vertices[i + 1] := by
        intro hv
        have hidx := (Q.simple_vertices.getElem_inj_iff
          (i := i) (j := i + 1) (hi := by omega) (hj := hi)).1 hv
        omega
      have hmem : Q.vertices[i] ∈ openSegment ℝ Q.vertices[i] Q.vertices[i + 1] := by
        have hmem' := hxOpen
        rw [← heq] at hmem'
        exact hmem'
      exact hne ((left_mem_openSegment_iff (𝕜 := ℝ)).1 hmem)
    · simpa [hIndices.1] using Br.beforeGate_open
    · exact Br.beforeGate_on_sphere
  · apply simultaneousBigonEndpointOutsideClosedBall
    · intro heq
      have hne : Q.vertices[i] ≠ Q.vertices[i + 1] := by
        intro hv
        have hidx := (Q.simple_vertices.getElem_inj_iff
          (i := i) (j := i + 1) (hi := by omega) (hj := hi)).1 hv
        omega
      have hmem : Q.vertices[i + 1] ∈ openSegment ℝ Q.vertices[i] Q.vertices[i + 1] := by
        have hmem' := hxOpen
        rw [← heq] at hmem'
        exact hmem'
      exact hne ((right_mem_openSegment_iff (𝕜 := ℝ)).1 hmem)
    · simpa [openSegment_symm, hIndices.2] using Br.afterGate_open
    · exact Br.afterGate_on_sphere

private lemma simultaneousBigonVertexMemCarrier
    (Q : PolygonalArc) (idx : Fin Q.vertices.length) :
    Q.vertices[idx.1] ∈ Q.carrier := by
  rw [Q.carrier_eq]
  have hlen := Q.length_ge_two
  by_cases hlast : idx.1 + 1 = Q.vertices.length
  · refine ⟨idx.1 - 1, by omega, ?_⟩
    have hidx : idx.1 - 1 + 1 = idx.1 := by omega
    simpa [hidx] using
      (right_mem_segment ℝ Q.vertices[idx.1 - 1] Q.vertices[idx.1])
  · refine ⟨idx.1, by omega, left_mem_segment ℝ _ _⟩

private lemma simultaneousBigonNonterminalVertexOutsideDisk
    (Q stored : PolygonalArc) (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (targetIndex : Fin Q.vertices.length) (i : ℕ)
    (hi : i + 1 < stored.vertices.length)
    (hCarrierSubset : Q.carrier ⊆ stored.carrier)
    (hLocal : Metric.closedBall x r ∩ stored.carrier =
      Metric.closedBall x r ∩ segment ℝ stored.vertices[i] stored.vertices[i + 1])
    (hLeftOutside : stored.vertices[i] ∉ Metric.closedBall x r)
    (hRightOutside : stored.vertices[i + 1] ∉ Metric.closedBall x r)
    (htargetVertex : Q.vertices[targetIndex.1] = x)
    (hTransfer : ∀ p,
      p ∈ openSegment ℝ stored.vertices[i] stored.vertices[i + 1] →
      p ∈ Q.carrier → p ≠ x →
        ∃ m : ℕ, ∃ hm : m + 1 < Q.vertices.length,
          p ∈ openSegment ℝ Q.vertices[m] Q.vertices[m + 1]) :
    ∀ idx : Fin Q.vertices.length, idx ≠ targetIndex →
      Q.vertices[idx.1] ∉ Metric.closedBall x r := by
  intro idx hne hzBall
  have hzQ := simultaneousBigonVertexMemCarrier Q idx
  have hzStored := hCarrierSubset hzQ
  have hzSeg : Q.vertices[idx.1] ∈
      segment ℝ stored.vertices[i] stored.vertices[i + 1] := by
    have hzBoth : Q.vertices[idx.1] ∈ Metric.closedBall x r ∩ stored.carrier :=
      ⟨hzBall, hzStored⟩
    rw [hLocal] at hzBoth
    exact hzBoth.2
  have hzOpen : Q.vertices[idx.1] ∈
      openSegment ℝ stored.vertices[i] stored.vertices[i + 1] := by
    rw [segment_eq_image_lineMap] at hzSeg
    rcases hzSeg with ⟨t, ht, hformula⟩
    rw [openSegment_eq_image_lineMap]
    refine ⟨t, ⟨?_, ?_⟩, hformula⟩
    · by_contra hnot
      have ht0 : t = 0 := le_antisymm (le_of_not_gt hnot) ht.1
      have hzLeft : Q.vertices[idx.1] = stored.vertices[i] := by
        simpa [ht0] using hformula.symm
      exact hLeftOutside (hzLeft ▸ hzBall)
    · by_contra hnot
      have ht1 : t = 1 := le_antisymm ht.2 (le_of_not_gt hnot)
      have hzRight : Q.vertices[idx.1] = stored.vertices[i + 1] := by
        simpa [ht1] using hformula.symm
      exact hRightOutside (hzRight ▸ hzBall)
  have hzNeX : Q.vertices[idx.1] ≠ x := by
    intro hzX
    apply hne
    apply Fin.ext
    have hvertexEq : Q.vertices[idx.1] = Q.vertices[targetIndex.1] := by
      simpa [htargetVertex] using hzX
    exact (Q.simple_vertices.getElem_inj_iff
      (hi := idx.2) (hj := targetIndex.2)).1 hvertexEq
  obtain ⟨m, hm, hzOpenQ⟩ := hTransfer _ hzOpen hzQ hzNeX
  exact (simultaneousBigonOpenNotVertices Q (Q.vertices[idx.1]) m hm hzOpenQ)
    (List.getElem_mem idx.2)

private lemma simultaneousBigonNonterminalVertexOutsideDiskOfTransfer
    (Q stored : PolygonalArc) (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (targetIndex : Fin Q.vertices.length) (i : ℕ)
    (hi : i + 1 < stored.vertices.length)
    (hCarrierSubset : Q.carrier ⊆ stored.carrier)
    (hLocal : Metric.closedBall x r ∩ stored.carrier =
      Metric.closedBall x r ∩ segment ℝ stored.vertices[i] stored.vertices[i + 1])
    (hLeftOutside : stored.vertices[i] ∉ Metric.closedBall x r)
    (hRightOutside : stored.vertices[i + 1] ∉ Metric.closedBall x r)
    (htargetVertex : Q.vertices[targetIndex.1] = x)
    (hTransfer : ∀ p k (hk : k + 1 < stored.vertices.length),
      p ∈ openSegment ℝ stored.vertices[k] stored.vertices[k + 1] →
      p ∈ Q.carrier → p ≠ x →
        ∃ j : ℕ, ∃ hj : j + 1 < Q.vertices.length,
          p ∈ openSegment ℝ Q.vertices[j] Q.vertices[j + 1] ∧
          ∃ scale : ℝ, scale ≠ 0 ∧
            Q.vertices[j + 1] - Q.vertices[j] =
              scale • (stored.vertices[k + 1] - stored.vertices[k])) :
    ∀ idx : Fin Q.vertices.length, idx ≠ targetIndex →
      Q.vertices[idx.1] ∉ Metric.closedBall x r :=
  simultaneousBigonNonterminalVertexOutsideDisk Q stored x r targetIndex i hi
    hCarrierSubset hLocal hLeftOutside hRightOutside htargetVertex
      (fun p hpOpen hpQ hpNe => by
        obtain ⟨m, hm, hpOpenQ, _scale, _hscale, _hdir⟩ :=
          hTransfer p i hi hpOpen hpQ hpNe
        exact ⟨m, hm, hpOpenQ⟩)

private lemma simultaneousBigonTerminalTubeOnly
    (Q stored : PolygonalArc) {eta : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii Q eta)
    (middleSegments : PolygonalArcCollarMiddleSegmentData Q controlRadii)
    (forbiddenMargins : PolygonalArcCollarMiddleForbiddenMargins
      Q controlRadii middleSegments)
    (sep : PolygonalArcCollarSeparatedTubeData Q controlRadii middleSegments
      forbiddenMargins)
    (x : EuclideanSpace ℝ (Fin 2)) (rho diskRadius : ℝ)
    (targetIndex : Fin Q.vertices.length) (jlast i : ℕ)
    (hi : i + 1 < stored.vertices.length)
    (htargetIndex : targetIndex.1 = Q.vertices.length - 1)
    (hjlastEq : jlast = Q.vertices.length - 2)
    (htargetVertex : Q.vertices[targetIndex.1] = x)
    (hetaGap : eta < diskRadius - rho)
    (hCarrierSubset : Q.carrier ⊆ stored.carrier)
    (hLocal : Metric.closedBall x diskRadius ∩ stored.carrier =
      Metric.closedBall x diskRadius ∩
        segment ℝ stored.vertices[i] stored.vertices[i + 1])
    (hLeftOutside : stored.vertices[i] ∉ Metric.closedBall x diskRadius)
    (hRightOutside : stored.vertices[i + 1] ∉ Metric.closedBall x diskRadius)
    (hNonterminal : ∀ idx : Fin Q.vertices.length, idx ≠ targetIndex →
      Q.vertices[idx.1] ∉ Metric.closedBall x diskRadius)
    (hTransfer : ∀ p k (hk : k + 1 < stored.vertices.length),
      p ∈ openSegment ℝ stored.vertices[k] stored.vertices[k + 1] →
      p ∈ Q.carrier → p ≠ x →
        ∃ owner : ℕ, ∃ howner : owner + 1 < Q.vertices.length,
          p ∈ openSegment ℝ Q.vertices[owner] Q.vertices[owner + 1] ∧
          ∃ scale : ℝ, scale ≠ 0 ∧
            Q.vertices[owner + 1] - Q.vertices[owner] =
              scale • (stored.vertices[k + 1] - stored.vertices[k]))
    (d : EuclideanSpace ℝ (Fin 2))
    (hLastScale : ∃ scaleLast : ℝ, scaleLast ≠ 0 ∧
      d = scaleLast • (stored.vertices[i + 1] - stored.vertices[i]))
    (hPointLine : ∀ z, z ∈ Metric.closedBall x diskRadius →
      z ∈ stored.carrier → ∃ c : ℝ, z = x + c • d)
    (hDiskRadius : 0 < diskRadius) :
    ∀ q, q ∈ Metric.closedBall x rho →
      ∀ m, ∀ hm : m + 1 < Q.vertices.length,
        q ∈ sep.tube m hm → m = jlast := by
  intro q hqBall m hm hqTube
  rw [sep.tube_eq] at hqTube
  rcases hqTube with ⟨t, ht, s, hs, hqFormula⟩
  let center := AffineMap.lineMap Q.vertices[m] Q.vertices[m + 1] t
  have ht01 : t ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨(sep.lowerParam_pos m hm).trans_le ht.1.le,
      ht.2.trans (sep.upperParam_lt_one m hm)⟩
  have hcenterOpen : center ∈
      openSegment ℝ Q.vertices[m] Q.vertices[m + 1] := by
    rw [openSegment_eq_image_lineMap]
    exact ⟨t, ht01, rfl⟩
  have hcenterQ : center ∈ Q.carrier := by
    rw [Q.carrier_eq]
    exact ⟨m, hm, openSegment_subset_segment ℝ _ _ hcenterOpen⟩
  have hqCenter : dist q center < eta := by
    rw [hqFormula, dist_eq_norm]
    have hsub : center + s • sep.normal m hm - center =
        s • sep.normal m hm := by abel
    rw [hsub, norm_smul, Real.norm_eq_abs]
    have hsabs : |s| < sep.halfWidth m hm := abs_lt.mpr hs
    have hnormalPos : 0 < ‖sep.normal m hm‖ := by
      rw [sep.normal_norm_eq_segment_length m hm]
      exact dist_pos.mpr (by
        intro heq
        have hidx := (Q.simple_vertices.getElem_inj_iff
          (i := m) (j := m + 1) (hi := by omega) (hj := hm)).1 heq
        omega)
    exact (mul_lt_mul_of_pos_right hsabs hnormalPos).trans
      (sep.halfWidth_mul_normal_norm_lt_eta m hm)
  have hcenterDiskOpen : center ∈ Metric.ball x diskRadius := by
    rw [Metric.mem_ball]
    have hqx : dist q x ≤ rho := by
      simpa [Metric.mem_closedBall] using hqBall
    calc
      dist center x ≤ dist center q + dist q x := dist_triangle _ _ _
      _ = dist q center + dist q x := by rw [dist_comm center q]
      _ < eta + rho := by linarith
      _ < diskRadius := by linarith
  have hcenterStored : center ∈ stored.carrier := hCarrierSubset hcenterQ
  have hcenterStoredSeg : center ∈
      segment ℝ stored.vertices[i] stored.vertices[i + 1] := by
    have hboth : center ∈ Metric.closedBall x diskRadius ∩ stored.carrier :=
      ⟨Metric.ball_subset_closedBall hcenterDiskOpen, hcenterStored⟩
    rw [hLocal] at hboth
    exact hboth.2
  have hcenterStoredOpen : center ∈
      openSegment ℝ stored.vertices[i] stored.vertices[i + 1] := by
    rw [segment_eq_image_lineMap] at hcenterStoredSeg
    rcases hcenterStoredSeg with ⟨v, hv, hvFormula⟩
    rw [openSegment_eq_image_lineMap]
    refine ⟨v, ⟨?_, ?_⟩, hvFormula⟩
    · by_contra hnot
      have hv0 : v = 0 := le_antisymm (le_of_not_gt hnot) hv.1
      have hleft : center = stored.vertices[i] := by
        simpa [hv0] using hvFormula.symm
      exact hLeftOutside (hleft ▸ Metric.ball_subset_closedBall hcenterDiskOpen)
    · by_contra hnot
      have hv1 : v = 1 := le_antisymm hv.2 (le_of_not_gt hnot)
      have hright : center = stored.vertices[i + 1] := by
        simpa [hv1] using hvFormula.symm
      exact hRightOutside (hright ▸ Metric.ball_subset_closedBall hcenterDiskOpen)
  have hcenterNeX : center ≠ x := by
    intro heq
    exact (simultaneousBigonOpenNotVertices Q center m hm hcenterOpen)
      (by rw [heq, ← htargetVertex]; exact List.getElem_mem targetIndex.2)
  obtain ⟨owner, howner, hcenterOwner, scale, hscale, hdir⟩ :=
    hTransfer center i hi hcenterStoredOpen hcenterQ hcenterNeX
  have hownerEq : owner = m :=
    simultaneousBigonOpenIndexUnique Q center owner m howner hm
      hcenterOwner hcenterOpen
  subst owner
  by_contra hmLast
  let leftIndex : Fin Q.vertices.length := ⟨m, by omega⟩
  let rightIndex : Fin Q.vertices.length := ⟨m + 1, hm⟩
  have hleftNeTarget : leftIndex ≠ targetIndex := by
    intro heq
    have hval : m = targetIndex.1 := congrArg Fin.val heq
    rw [htargetIndex] at hval
    omega
  have hrightNeTarget : rightIndex ≠ targetIndex := by
    intro heq
    have hval : m + 1 = targetIndex.1 := congrArg Fin.val heq
    rw [htargetIndex] at hval
    omega
  have hleftOutside := hNonterminal leftIndex hleftNeTarget
  have hrightOutside := hNonterminal rightIndex hrightNeTarget
  obtain ⟨scaleLast, hscaleLast, hdDir⟩ := hLastScale
  let ratio : ℝ := scale / scaleLast
  have hratio : ratio ≠ 0 := div_ne_zero hscale hscaleLast
  have hsegmentDir : Q.vertices[m + 1] - Q.vertices[m] = ratio • d := by
    rw [hdir, hdDir]
    dsimp [ratio]
    rw [smul_smul]
    congr 1
    field_simp [hscaleLast]
  obtain ⟨c, hcenterLine⟩ := hPointLine center
    (Metric.ball_subset_closedBall hcenterDiskOpen) hcenterStored
  let ca : ℝ := c - t * ratio
  let cb : ℝ := c + (1 - t) * ratio
  have hleftLine : Q.vertices[m] = x + ca • d := by
    have hlineMap : center = Q.vertices[m] +
        t • (Q.vertices[m + 1] - Q.vertices[m]) := by
      dsimp [center]
      simp only [AffineMap.lineMap_apply_module]
      module
    rw [hcenterLine, hsegmentDir] at hlineMap
    dsimp [ca]
    rw [smul_smul] at hlineMap
    calc
      Q.vertices[m] =
          (Q.vertices[m] + (t * ratio) • d) - (t * ratio) • d := by module
      _ = (x + c • d) - (t * ratio) • d := by rw [← hlineMap]
      _ = x + (c - t * ratio) • d := by module
  have hrightLine : Q.vertices[m + 1] = x + cb • d := by
    rw [← sub_add_cancel Q.vertices[m + 1] Q.vertices[m],
      hsegmentDir, hleftLine]
    dsimp [ca, cb]
    module
  have hcenterDist : |c| * ‖d‖ < diskRadius := by
    have hcenterDisk := hcenterDiskOpen
    rw [Metric.mem_ball, hcenterLine, dist_eq_norm] at hcenterDisk
    simpa [norm_smul, Real.norm_eq_abs] using hcenterDisk
  have hleftDist : diskRadius < |ca| * ‖d‖ := by
    rw [Metric.mem_closedBall, hleftLine, dist_eq_norm] at hleftOutside
    simpa [norm_smul, Real.norm_eq_abs] using lt_of_not_ge hleftOutside
  have hrightDist : diskRadius < |cb| * ‖d‖ := by
    rw [Metric.mem_closedBall, hrightLine, dist_eq_norm] at hrightOutside
    simpa [norm_smul, Real.norm_eq_abs] using lt_of_not_ge hrightOutside
  have hcConvex : c = (1 - t) * ca + t * cb := by
    dsimp [ca, cb]
    ring
  have htPos : 0 < t := (sep.lowerParam_pos m hm).trans ht.1
  have htOne : t < 1 := ht.2.trans (sep.upperParam_lt_one m hm)
  have hopposite : (ca < 0 ∧ 0 < cb) ∨ (cb < 0 ∧ 0 < ca) := by
    by_cases hca : 0 ≤ ca
    · by_cases hcb : 0 ≤ cb
      · rw [abs_of_nonneg hca] at hleftDist
        rw [abs_of_nonneg hcb] at hrightDist
        have htNonneg : 0 ≤ t := le_of_lt htPos
        have honeSubNonneg : 0 ≤ 1 - t := by linarith
        have hcNonneg : 0 ≤ c := by
          rw [hcConvex]
          exact add_nonneg (mul_nonneg honeSubNonneg hca)
            (mul_nonneg htNonneg hcb)
        rw [abs_of_nonneg hcNonneg] at hcenterDist
        have hleftWeighted := mul_le_mul_of_nonneg_left
          (le_of_lt hleftDist) honeSubNonneg
        have hrightWeighted := mul_le_mul_of_nonneg_left
          (le_of_lt hrightDist) htNonneg
        have hcLower : diskRadius ≤ c * ‖d‖ := by
          rw [hcConvex]
          calc
            diskRadius = (1 - t) * diskRadius + t * diskRadius := by ring
            _ ≤ (1 - t) * (ca * ‖d‖) + t * (cb * ‖d‖) :=
              add_le_add hleftWeighted hrightWeighted
            _ = ((1 - t) * ca + t * cb) * ‖d‖ := by ring
        exact (not_lt_of_ge hcLower hcenterDist).elim
      · exact Or.inr ⟨lt_of_not_ge hcb, by
          rw [abs_of_nonneg hca] at hleftDist
          have hprod : 0 < ca * ‖d‖ := lt_trans hDiskRadius hleftDist
          rcases (mul_pos_iff.mp hprod) with h | h
          · exact h.1
          · exact (not_lt_of_ge hca h.1).elim⟩
    · by_cases hcb : 0 ≤ cb
      · exact Or.inl ⟨lt_of_not_ge hca, by
          rw [abs_of_nonneg hcb] at hrightDist
          have hprod : 0 < cb * ‖d‖ := lt_trans hDiskRadius hrightDist
          rcases (mul_pos_iff.mp hprod) with h | h
          · exact h.1
          · exact (not_lt_of_ge hcb h.1).elim⟩
      · rw [abs_of_neg (lt_of_not_ge hca)] at hleftDist
        rw [abs_of_neg (lt_of_not_ge hcb)] at hrightDist
        have htNonneg : 0 ≤ t := le_of_lt htPos
        have honeSubNonneg : 0 ≤ 1 - t := by linarith
        have hcNonpos : c ≤ 0 := by
          rw [hcConvex]
          exact add_nonpos
            (mul_nonpos_of_nonneg_of_nonpos honeSubNonneg
              (le_of_lt (lt_of_not_ge hca)))
            (mul_nonpos_of_nonneg_of_nonpos htNonneg
              (le_of_lt (lt_of_not_ge hcb)))
        rw [abs_of_nonpos hcNonpos] at hcenterDist
        have hleftWeighted := mul_le_mul_of_nonneg_left
          (le_of_lt hleftDist) honeSubNonneg
        have hrightWeighted := mul_le_mul_of_nonneg_left
          (le_of_lt hrightDist) htNonneg
        have hcLower : diskRadius ≤ -c * ‖d‖ := by
          rw [hcConvex]
          calc
            diskRadius = (1 - t) * diskRadius + t * diskRadius := by ring
            _ ≤ (1 - t) * (-ca * ‖d‖) + t * (-cb * ‖d‖) :=
              add_le_add hleftWeighted hrightWeighted
            _ = -((1 - t) * ca + t * cb) * ‖d‖ := by ring
        exact (not_lt_of_ge hcLower hcenterDist).elim
  have hxOpenM : x ∈ openSegment ℝ Q.vertices[m] Q.vertices[m + 1] := by
    rw [openSegment_eq_image_lineMap]
    rcases hopposite with hop | hop
    · let v := -ca / (cb - ca)
      have hdenPos : 0 < cb - ca := sub_pos.mpr (lt_trans hop.1 hop.2)
      have hv : v ∈ Set.Ioo (0 : ℝ) 1 := by
        dsimp [v]
        exact ⟨div_pos (neg_pos.mpr hop.1) hdenPos,
          (div_lt_one hdenPos).2 (by linarith [hop.2])⟩
      refine ⟨v, hv, ?_⟩
      rw [hleftLine, hrightLine]
      dsimp [v]
      simp only [AffineMap.lineMap_apply_module]
      have hden : cb - ca ≠ 0 := hdenPos.ne'
      have hcoef :
          (1 - (-ca / (cb - ca))) * ca + (-ca / (cb - ca)) * cb = 0 := by
        field_simp [hden]
        ring
      calc
        (1 - (-ca / (cb - ca))) • (x + ca • d) +
              (-ca / (cb - ca)) • (x + cb • d) =
            x + (((1 - (-ca / (cb - ca))) * ca +
              (-ca / (cb - ca)) * cb) • d) := by module
        _ = x := by rw [hcoef, zero_smul, add_zero]
    · let v := ca / (ca - cb)
      have hdenPos : 0 < ca - cb := sub_pos.mpr (lt_trans hop.1 hop.2)
      have hv : v ∈ Set.Ioo (0 : ℝ) 1 := by
        dsimp [v]
        exact ⟨div_pos hop.2 hdenPos,
          (div_lt_one hdenPos).2 (by linarith [hop.1])⟩
      refine ⟨v, hv, ?_⟩
      rw [hleftLine, hrightLine]
      dsimp [v]
      simp only [AffineMap.lineMap_apply_module]
      have hden : ca - cb ≠ 0 := hdenPos.ne'
      have hcoef :
          (1 - (ca / (ca - cb))) * ca + (ca / (ca - cb)) * cb = 0 := by
        field_simp [hden]
        ring
      calc
        (1 - (ca / (ca - cb))) • (x + ca • d) +
              (ca / (ca - cb)) • (x + cb • d) =
            x + (((1 - (ca / (ca - cb))) * ca +
              (ca / (ca - cb)) * cb) • d) := by module
        _ = x := by rw [hcoef, zero_smul, add_zero]
  exact (simultaneousBigonOpenNotVertices Q x m hm hxOpenM)
    (by rw [← htargetVertex]; exact List.getElem_mem targetIndex.2)

private lemma simultaneousBigonTerminalRightHalfCoordinates
    (Q : PolygonalArc) {eta : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii Q eta)
    (middleSegments : PolygonalArcCollarMiddleSegmentData Q controlRadii)
    (forbiddenMargins : PolygonalArcCollarMiddleForbiddenMargins
      Q controlRadii middleSegments)
    (compatibleTubes : PolygonalArcCollarCompatibleOrientedTubeData
      Q controlRadii middleSegments forbiddenMargins)
    (x d n : EuclideanSpace ℝ (Fin 2)) (K : ℝ)
    (jlast : ℕ) (hjlast : jlast + 1 < Q.vertices.length)
    (hK : 0 < K)
    (hKDef : K = compatibleTubes.terminalConeBound jlast hjlast)
    (hlastVertex : Q.vertices[jlast + 1] = x)
    (hd : d = Q.vertices[jlast] - x) (hn : n = PlanarRot90 d) :
    ∀ q, q ∈ compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf
        jlast hjlast →
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ b < K * a ∧
        q = x + a • d + b • n := by
  intro q hqHalf
  let sep := compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
  rw [sep.rightHalf_eq] at hqHalf
  rcases hqHalf with ⟨t, ht, s, hs, hqFormula⟩
  let a := 1 - t
  let b := -s
  have ha : 0 < a := by
    dsimp [a]
    linarith [ht.2, sep.upperParam_lt_one jlast hjlast]
  have hb : 0 < b := by
    dsimp [b]
    exact neg_pos.mpr hs.2
  have hbBound : b < K * a := by
    have hw := compatibleTubes.terminal_halfWidth_lt_cone_mul_one_sub_upperParam
      jlast hjlast
    have hone : 1 - sep.upperParam jlast hjlast < 1 - t := by linarith [ht.2]
    dsimp [a, b]
    calc
      -s < sep.halfWidth jlast hjlast := by linarith [hs.1]
      _ < K * (1 - sep.upperParam jlast hjlast) := by
        simpa [sep, hKDef] using hw
      _ < K * (1 - t) := mul_lt_mul_of_pos_left hone hK
  refine ⟨a, b, ha, hb, hbBound, ?_⟩
  have hnormal : sep.normal jlast hjlast =
      PlanarRot90 (Q.vertices[jlast + 1] - Q.vertices[jlast]) := by
    simpa only [PlanarRot90] using
      compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn jlast hjlast
  have hdiff : Q.vertices[jlast + 1] - Q.vertices[jlast] = -d := by
    rw [hlastVertex, hd]
    module
  have hrotNeg : PlanarRot90 (-d) = -PlanarRot90 d := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [PlanarRot90]
  rw [hnormal, hdiff, hrotNeg] at hqFormula
  simp only [AffineMap.lineMap_apply_module, hlastVertex] at hqFormula
  rw [hqFormula]
  dsimp [a, b]
  rw [hn, hd]
  module

private lemma simultaneousBigonTerminalLeftHalfCoordinates
    (Q : PolygonalArc) {eta : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii Q eta)
    (middleSegments : PolygonalArcCollarMiddleSegmentData Q controlRadii)
    (forbiddenMargins : PolygonalArcCollarMiddleForbiddenMargins
      Q controlRadii middleSegments)
    (compatibleTubes : PolygonalArcCollarCompatibleOrientedTubeData
      Q controlRadii middleSegments forbiddenMargins)
    (x d n : EuclideanSpace ℝ (Fin 2)) (K : ℝ)
    (jlast : ℕ) (hjlast : jlast + 1 < Q.vertices.length)
    (hK : 0 < K)
    (hKDef : K = compatibleTubes.terminalConeBound jlast hjlast)
    (hlastVertex : Q.vertices[jlast + 1] = x)
    (hd : d = Q.vertices[jlast] - x) (hn : n = -PlanarRot90 d) :
    ∀ q, q ∈ compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf
        jlast hjlast →
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ b < K * a ∧
        q = x + a • d + b • n := by
  intro q hqHalf
  let sep := compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
  rw [sep.leftHalf_eq] at hqHalf
  rcases hqHalf with ⟨t, ht, s, hs, hqFormula⟩
  let a := 1 - t
  let b := s
  have ha : 0 < a := by
    dsimp [a]
    linarith [ht.2, sep.upperParam_lt_one jlast hjlast]
  have hb : 0 < b := hs.1
  have hbBound : b < K * a := by
    have hw := compatibleTubes.terminal_halfWidth_lt_cone_mul_one_sub_upperParam
      jlast hjlast
    have hone : 1 - sep.upperParam jlast hjlast < 1 - t := by linarith [ht.2]
    dsimp [a, b]
    calc
      s < sep.halfWidth jlast hjlast := hs.2
      _ < K * (1 - sep.upperParam jlast hjlast) := by
        simpa [sep, hKDef] using hw
      _ < K * (1 - t) := mul_lt_mul_of_pos_left hone hK
  refine ⟨a, b, ha, hb, hbBound, ?_⟩
  have hnormal : sep.normal jlast hjlast =
      PlanarRot90 (Q.vertices[jlast + 1] - Q.vertices[jlast]) := by
    simpa only [PlanarRot90] using
      compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn jlast hjlast
  have hdiff : Q.vertices[jlast + 1] - Q.vertices[jlast] = -d := by
    rw [hlastVertex, hd]
    module
  have hrotNeg : PlanarRot90 (-d) = -PlanarRot90 d := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [PlanarRot90]
  rw [hnormal, hdiff, hrotNeg] at hqFormula
  simp only [AffineMap.lineMap_apply_module, hlastVertex] at hqFormula
  rw [hqFormula]
  dsimp [a, b]
  rw [hn, hd]
  module

private lemma simultaneousBigonSourceTubeOnly
    (Q : PolygonalArc) {eta : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii Q eta)
    (middleSegments : PolygonalArcCollarMiddleSegmentData Q controlRadii)
    (forbiddenMargins : PolygonalArcCollarMiddleForbiddenMargins
      Q controlRadii middleSegments)
    (sep : PolygonalArcCollarSeparatedTubeData Q controlRadii middleSegments
      forbiddenMargins)
    (source : EuclideanSpace ℝ (Fin 2)) (sourceLocalRadius r0 : ℝ)
    (hfirst : 0 + 1 < Q.vertices.length)
    (hsource0 : Q.vertices[0] = source)
    (hsourceHalf : sourceLocalRadius ≤ r0 / 2)
    (hetaSource : eta < sourceLocalRadius)
    (hIso : Metric.closedBall source r0 ∩ Q.carrier ⊆
      segment ℝ Q.vertices[0] Q.vertices[1]) :
    ∀ q, q ∈ Metric.ball source sourceLocalRadius →
      ∀ m, ∀ hm : m + 1 < Q.vertices.length,
        q ∈ sep.tube m hm → m = 0 := by
  intro q hqBall m hm hqTube
  rw [sep.tube_eq] at hqTube
  rcases hqTube with ⟨t, ht, s, hs, hqFormula⟩
  let center := AffineMap.lineMap Q.vertices[m] Q.vertices[m + 1] t
  have ht01 : t ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨(sep.lowerParam_pos m hm).trans_le ht.1.le,
      ht.2.trans (sep.upperParam_lt_one m hm)⟩
  have hcenterOpen : center ∈
      openSegment ℝ Q.vertices[m] Q.vertices[m + 1] := by
    rw [openSegment_eq_image_lineMap]
    exact ⟨t, ht01, rfl⟩
  have hcenterQ : center ∈ Q.carrier := by
    rw [Q.carrier_eq]
    exact ⟨m, hm, openSegment_subset_segment ℝ _ _ hcenterOpen⟩
  have hqCenter : dist q center < eta := by
    rw [hqFormula, dist_eq_norm]
    have hsub : center + s • sep.normal m hm - center =
        s • sep.normal m hm := by abel
    rw [hsub, norm_smul, Real.norm_eq_abs]
    have hsabs : |s| < sep.halfWidth m hm := abs_lt.mpr hs
    have hnormalPos : 0 < ‖sep.normal m hm‖ := by
      rw [sep.normal_norm_eq_segment_length m hm]
      exact dist_pos.mpr (by
        intro heq
        have hidx := (Q.simple_vertices.getElem_inj_iff
          (i := m) (j := m + 1) (hi := by omega) (hj := hm)).1 heq
        omega)
    exact (mul_lt_mul_of_pos_right hsabs hnormalPos).trans
      (sep.halfWidth_mul_normal_norm_lt_eta m hm)
  have hcenterR0 : center ∈ Metric.ball source r0 := by
    rw [Metric.mem_ball]
    have hqSource : dist q source < sourceLocalRadius := by
      simpa [Metric.mem_ball] using hqBall
    calc
      dist center source ≤ dist center q + dist q source := dist_triangle _ _ _
      _ = dist q center + dist q source := by rw [dist_comm center q]
      _ < eta + sourceLocalRadius := by linarith
      _ < r0 := by linarith
  have hcenterInitial : center ∈ segment ℝ Q.vertices[0] Q.vertices[1] :=
    hIso ⟨Metric.ball_subset_closedBall hcenterR0, hcenterQ⟩
  have hcenterInitialOpen : center ∈
      openSegment ℝ Q.vertices[0] Q.vertices[1] := by
    rw [segment_eq_image_lineMap] at hcenterInitial
    rcases hcenterInitial with ⟨v, hv, hvFormula⟩
    rw [openSegment_eq_image_lineMap]
    refine ⟨v, ⟨?_, ?_⟩, hvFormula⟩
    · by_contra hnot
      have hv0 : v = 0 := le_antisymm (le_of_not_gt hnot) hv.1
      have hc0 : center = Q.vertices[0] := by
        simpa [hv0] using hvFormula.symm
      exact (simultaneousBigonOpenNotVertices Q center m hm hcenterOpen)
        (by rw [hc0]; exact List.getElem_mem (by omega))
    · by_contra hnot
      have hv1 : v = 1 := le_antisymm hv.2 (le_of_not_gt hnot)
      have hc1 : center = Q.vertices[1] := by
        simpa [hv1] using hvFormula.symm
      exact (simultaneousBigonOpenNotVertices Q center m hm hcenterOpen)
        (by rw [hc1]; exact List.getElem_mem (by omega))
  exact simultaneousBigonOpenIndexUnique Q center m 0 hm hfirst hcenterOpen
    hcenterInitialOpen

private lemma simultaneousBigonSourceCoordsInsideCap
    (source d : EuclideanSpace ℝ (Fin 2)) (radius : ℝ) (hd : d ≠ 0) :
    ∀ q a b,
      q = source + a • d + b • PlanarRot90 d →
      q ∈ Metric.ball source radius →
      a ^ 2 + b ^ 2 < (radius / ‖d‖) ^ 2 := by
  intro q a b hqFormula hqBall
  have hqdist : dist source q < radius := by
    simpa [Metric.mem_ball, dist_comm] using hqBall
  have hvec : q - source = a • d + b • PlanarRot90 d := by
    rw [hqFormula]
    abel
  have hsquare : dist source q ^ 2 = (a ^ 2 + b ^ 2) * ‖d‖ ^ 2 := by
    rw [dist_eq_norm, norm_sub_rev, hvec]
    have horth : inner ℝ (a • d) (b • PlanarRot90 d) = 0 := by
      rw [inner_smul_left, inner_smul_right, PlanarRot90Orthogonal]
      ring
    have hpyth :
        ‖a • d + b • PlanarRot90 d‖ ^ 2 =
          ‖a • d‖ ^ 2 + ‖b • PlanarRot90 d‖ ^ 2 := by
      simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real horth
    rw [hpyth, norm_smul, norm_smul, PlanarRot90Norm]
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [mul_pow, mul_pow, sq_abs, sq_abs]
    ring
  have hnormd : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hdistNonneg : 0 ≤ dist source q := dist_nonneg
  have hsquareLt : dist source q ^ 2 < radius ^ 2 := by nlinarith
  rw [hsquare] at hsquareLt
  have hnorm0 : ‖d‖ ≠ 0 := hnormd.ne'
  field_simp [hnorm0]
  nlinarith

private lemma simultaneousBigonNonSourceVertexOutside
    (Q : PolygonalArc) (source : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (hfirst : 0 + 1 < Q.vertices.length)
    (hLocal : Metric.closedBall source r ∩ Q.carrier ⊆
      segment ℝ Q.vertices[0] Q.vertices[1])
    (hNextOutside : Q.vertices[1] ∉ Metric.closedBall source r) :
    ∀ idx : Fin Q.vertices.length, idx.1 ≠ 0 →
      Q.vertices[idx.1] ∉ Metric.closedBall source r := by
  intro idx hne hzBall
  have hzQ := simultaneousBigonVertexMemCarrier Q idx
  have hzInitial : Q.vertices[idx.1] ∈
      segment ℝ Q.vertices[0] Q.vertices[1] := hLocal ⟨hzBall, hzQ⟩
  have hzNeSource : Q.vertices[idx.1] ≠ Q.vertices[0] := by
    intro heq
    have hidx := (Q.simple_vertices.getElem_inj_iff
      (i := idx.1) (j := 0) (hi := idx.2) (hj := by omega)).1 heq
    exact hne hidx
  have hzNeNext : Q.vertices[idx.1] ≠ Q.vertices[1] := by
    intro heq
    exact hNextOutside (heq ▸ hzBall)
  have hzOpen : Q.vertices[idx.1] ∈
      openSegment ℝ Q.vertices[0] Q.vertices[1] := by
    rw [segment_eq_image_lineMap] at hzInitial
    rcases hzInitial with ⟨t, ht, htFormula⟩
    rw [openSegment_eq_image_lineMap]
    refine ⟨t, ⟨?_, ?_⟩, htFormula⟩
    · by_contra hnot
      have ht0 : t = 0 := le_antisymm (le_of_not_gt hnot) ht.1
      exact hzNeSource (by simpa [ht0] using htFormula.symm)
    · by_contra hnot
      have ht1 : t = 1 := le_antisymm ht.2 (le_of_not_gt hnot)
      exact hzNeNext (by simpa [ht1] using htFormula.symm)
  exact (simultaneousBigonOpenNotVertices Q (Q.vertices[idx.1]) 0 hfirst hzOpen)
    (List.getElem_mem idx.2)

private lemma simultaneousBigonSelectedTerminalAvoidOld
    (Selected Old : Set (EuclideanSpace ℝ (Fin 2)))
    (x d n v : EuclideanSpace ℝ (Fin 2)) (rho K mu nu : ℝ)
    (hnormd : 0 < ‖d‖) (hnu : 0 < nu) (hK : 0 < K)
    (hkappaSmall : K * (|mu| + 1) < nu / 4)
    (hdd : inner ℝ d d = ‖d‖ ^ 2)
    (hdn : inner ℝ d n = 0) (hnd : inner ℝ n d = 0)
    (hnn : inner ℝ n n = ‖d‖ ^ 2)
    (hv : v = mu • d + nu • n)
    (hCone : ∀ q, q ∈ Selected ∩ Metric.closedBall x rho →
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ b < K * a ∧
        q = x + a • d + b • n)
    (hOldLocal : Metric.closedBall x rho ∩ Old ⊆
      {q | ∃ c : ℝ, q = x + c • d} ∪
        {q | ∃ c : ℝ, q = x + c • v}) :
    (Selected ∩ Metric.closedBall x rho) ∩ Old = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  obtain ⟨a, b, ha, hb, hbka, hqCone⟩ := hCone q hq.1
  have hqLocal := hOldLocal ⟨hq.1.2, hq.2⟩
  rcases hqLocal with ⟨c, hqLine⟩ | ⟨c, hqLine⟩
  · have hcoeff : b * ‖d‖ ^ 2 = 0 := by
      have heq : a • d + b • n = c • d := by
        calc
          a • d + b • n = (x + a • d + b • n) - x := by module
          _ = q - x := by rw [← hqCone]
          _ = (x + c • d) - x := by rw [hqLine]
          _ = c • d := by module
      calc
        b * ‖d‖ ^ 2 = inner ℝ (a • d + b • n) n := by
          simp only [inner_add_left, inner_smul_left_eq_smul, smul_eq_mul,
            hdn, hnn, mul_zero, zero_add]
        _ = inner ℝ (c • d) n := congrArg (fun z => inner ℝ z n) heq
        _ = 0 := by
          simp only [inner_smul_left_eq_smul, smul_eq_mul, hdn, mul_zero]
    nlinarith [sq_pos_of_pos hnormd]
  · have hcoeffD : a * ‖d‖ ^ 2 = c * mu * ‖d‖ ^ 2 := by
      have heq : a • d + b • n = c • v := by
        calc
          a • d + b • n = (x + a • d + b • n) - x := by module
          _ = q - x := by rw [← hqCone]
          _ = (x + c • v) - x := by rw [hqLine]
          _ = c • v := by module
      calc
        a * ‖d‖ ^ 2 = inner ℝ (a • d + b • n) d := by
          simp only [inner_add_left, inner_smul_left_eq_smul, smul_eq_mul,
            hdd, hnd, mul_zero, add_zero]
        _ = inner ℝ (c • v) d := congrArg (fun z => inner ℝ z d) heq
        _ = c * mu * ‖d‖ ^ 2 := by
          rw [hv]
          simp only [inner_add_left, inner_smul_left_eq_smul, smul_eq_mul,
            hdd, hnd, mul_zero, add_zero]
          ring
    have hcoeffN : b * ‖d‖ ^ 2 = c * nu * ‖d‖ ^ 2 := by
      have heq : a • d + b • n = c • v := by
        calc
          a • d + b • n = (x + a • d + b • n) - x := by module
          _ = q - x := by rw [← hqCone]
          _ = (x + c • v) - x := by rw [hqLine]
          _ = c • v := by module
      calc
        b * ‖d‖ ^ 2 = inner ℝ (a • d + b • n) n := by
          simp only [inner_add_left, inner_smul_left_eq_smul, smul_eq_mul,
            hdn, hnn, mul_zero, zero_add]
        _ = inner ℝ (c • v) n := congrArg (fun z => inner ℝ z n) heq
        _ = c * nu * ‖d‖ ^ 2 := by
          rw [hv]
          simp only [inner_add_left, inner_smul_left_eq_smul, smul_eq_mul,
            hdn, hnn, mul_zero, zero_add]
          ring
    have hnormsq := sq_pos_of_pos hnormd
    have haEq : a = c * mu := by nlinarith
    have hbEq : b = c * nu := by nlinarith
    have hc : 0 < c := by
      rw [hbEq] at hb
      rcases (mul_pos_iff.mp hb) with hcnu | hcnu
      · exact hcnu.1
      · exact (not_lt_of_ge (le_of_lt hnu) hcnu.2).elim
    have hkmu : K * mu < nu := by
      have habs := le_abs_self mu
      nlinarith
    rw [haEq, hbEq] at hbka
    nlinarith

private lemma simultaneousBigonVertexIndexTarget
    (Q : PolygonalArc) {eta : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii Q eta)
    (middleSegments : PolygonalArcCollarMiddleSegmentData Q controlRadii)
    (forbiddenMargins : PolygonalArcCollarMiddleForbiddenMargins
      Q controlRadii middleSegments)
    (compatibleTubes : PolygonalArcCollarCompatibleOrientedTubeData
      Q controlRadii middleSegments forbiddenMargins)
    (vertexLocalPieces : PolygonalArcCollarVertexLocalPieceData Q
      controlRadii middleSegments forbiddenMargins
      compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData)
    (localSideData : PolygonalArcCollarLocalSideData Q controlRadii
      middleSegments forbiddenMargins compatibleTubes.orientedTubes
      vertexLocalPieces)
    (x : EuclideanSpace ℝ (Fin 2)) (rho diskRadius : ℝ)
    (targetIndex : Fin Q.vertices.length)
    (hetaGap : eta < diskRadius - rho)
    (hNonterminal : ∀ idx : Fin Q.vertices.length, idx ≠ targetIndex →
      Q.vertices[idx.1] ∉ Metric.closedBall x diskRadius) :
    ∀ q, q ∈ Metric.closedBall x rho →
      ∀ idx, q ∈ localSideData.vertexCollar idx → idx = targetIndex := by
  intro q hqBall idx hqPiece
  by_contra hne
  have hqDisk := localSideData.vertexCollar_subset_vertexDisk idx hqPiece
  rw [vertexLocalPieces.vertexDisk_eq] at hqDisk
  have hqdist : dist q Q.vertices[idx.1] < eta := by
    have hrlt := controlRadii.radius_lt_eta idx
    simpa [Metric.mem_ball] using lt_trans
      (show dist q Q.vertices[idx.1] < controlRadii.radius idx by
        simpa [Metric.mem_ball] using hqDisk) hrlt
  have hvertexBall : Q.vertices[idx.1] ∈ Metric.closedBall x diskRadius := by
    rw [Metric.mem_closedBall]
    apply le_of_lt
    calc
      dist Q.vertices[idx.1] x ≤ dist Q.vertices[idx.1] q + dist q x :=
        dist_triangle _ _ _
      _ < eta + rho := add_lt_add_of_lt_of_le
        (by simpa [dist_comm] using hqdist) hqBall
      _ < diskRadius := by linarith
  exact hNonterminal idx hne hvertexBall

private lemma simultaneousBigonSelectedAvoidFar
    (Q : PolygonalArc) (Selected collar Far : Set (EuclideanSpace ℝ (Fin 2)))
    (eta etaSep : ℝ) (hSelected : Selected ⊆ collar)
    (hNear : ∀ z ∈ collar, ∃ p ∈ Q.carrier, dist z p < eta)
    (heta : eta ≤ etaSep)
    (hAvoid : ∀ z, (∃ p ∈ Q.carrier, dist z p < etaSep) →
      z ∈ Far → False) :
    Disjoint Selected Far := by
  rw [Set.disjoint_left]
  intro z hzSelected hzFar
  obtain ⟨p, hpQ, hzp⟩ := hNear z (hSelected hzSelected)
  exact hAvoid z ⟨p, hpQ, hzp.trans_le heta⟩ hzFar

private lemma simultaneousBigonSidePieceControlBall
    (Q : PolygonalArc) {eta : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii Q eta)
    (middleSegments : PolygonalArcCollarMiddleSegmentData Q controlRadii)
    (forbiddenMargins : PolygonalArcCollarMiddleForbiddenMargins
      Q controlRadii middleSegments)
    (compatibleTubes : PolygonalArcCollarCompatibleOrientedTubeData
      Q controlRadii middleSegments forbiddenMargins)
    (vertexLocalPieces : PolygonalArcCollarVertexLocalPieceData Q
      controlRadii middleSegments forbiddenMargins
      compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData)
    (localSideData : PolygonalArcCollarLocalSideData Q controlRadii
      middleSegments forbiddenMargins compatibleTubes.orientedTubes
      vertexLocalPieces)
    (Vin : Set (EuclideanSpace ℝ (Fin 2)))
    (targetIndex : Fin Q.vertices.length) (x : EuclideanSpace ℝ (Fin 2))
    (htarget : Q.vertices[targetIndex.1] = x)
    (hVin : Vin ⊆ localSideData.vertexCollar targetIndex) :
    Vin ⊆ Metric.ball x (controlRadii.radius targetIndex) := by
  intro z hz
  have hzCollar := hVin hz
  have hzDisk := localSideData.vertexCollar_subset_vertexDisk targetIndex hzCollar
  rw [vertexLocalPieces.vertexDisk_eq] at hzDisk
  simpa [htarget] using hzDisk

private lemma simultaneousBigonConePositive
    (Selected : Set (EuclideanSpace ℝ (Fin 2)))
    (x d n : EuclideanSpace ℝ (Fin 2)) (rho K : ℝ)
    (hnormd : 0 < ‖d‖)
    (hdd : inner ℝ d d = ‖d‖ ^ 2)
    (hdn : inner ℝ d n = 0) (hnd : inner ℝ n d = 0)
    (hnn : inner ℝ n n = ‖d‖ ^ 2)
    (hCone : ∀ q, q ∈ Selected ∩ Metric.closedBall x rho →
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ b < K * a ∧
        q = x + a • d + b • n) :
    ∀ q ∈ Selected ∩ Metric.closedBall x rho,
      0 < K * inner ℝ (q - x) d - inner ℝ (q - x) n := by
  intro q hq
  obtain ⟨a, b, _ha, _hb, hbka, hqFormula⟩ := hCone q hq
  have hsub : x + a • d + b • n - x = a • d + b • n := by abel
  have hnormsq : 0 < ‖d‖ ^ 2 := sq_pos_of_pos hnormd
  have hphi : K * inner ℝ (q - x) d - inner ℝ (q - x) n =
      (K * a - b) * ‖d‖ ^ 2 := by
    rw [hqFormula, hsub]
    simp only [inner_add_left, inner_smul_left_eq_smul, smul_eq_mul,
      hdd, hnd, hdn, hnn, mul_zero, zero_add, add_zero]
    ring
  rw [hphi]
  exact mul_pos (sub_pos.mpr hbka) hnormsq

private lemma simultaneousBigonConeAvoidSupporting
    (Selected Supporting : Set (EuclideanSpace ℝ (Fin 2)))
    (x d n : EuclideanSpace ℝ (Fin 2)) (rho K : ℝ)
    (hPositive : ∀ q ∈ Selected ∩ Metric.closedBall x rho,
      0 < K * inner ℝ (q - x) d - inner ℝ (q - x) n)
    (hSupporting : ∀ q ∈ Supporting,
      K * inner ℝ (q - x) d - inner ℝ (q - x) n ≤ 0) :
    (Selected ∩ Metric.closedBall x rho) ∩ Supporting = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  exact (not_lt_of_ge (hSupporting q hq.2))
    (hPositive q hq.1)

private lemma simultaneousBigonAvoidTerminalClosures
    (Selected Side Bridge Q : Set (EuclideanSpace ℝ (Fin 2)))
    (x : EuclideanSpace ℝ (Fin 2)) (rho : ℝ)
    (hSide : closure Side ⊆ Metric.ball x rho)
    (hBridge : closure Bridge ⊆ Metric.ball x rho)
    (hQ : closure Q ⊆ Metric.closedBall x rho)
    (hAvoid : (Selected ∩ Metric.closedBall x rho) ∩
      (closure Side ∪ closure Bridge ∪ closure Q) = ∅) :
    Selected ∩ (closure Side ∪ closure Bridge ∪ closure Q) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hqBall : q ∈ Metric.closedBall x rho := by
    rcases hq.2 with (hqSide | hqBridge) | hqQ
    · exact Metric.ball_subset_closedBall (hSide hqSide)
    · exact Metric.ball_subset_closedBall (hBridge hqBridge)
    · exact hQ hqQ
  exact Set.eq_empty_iff_forall_notMem.mp hAvoid q ⟨⟨hq.1, hqBall⟩, hq.2⟩

private lemma simultaneousBigonSourceRightHalfWide
    (Q : PolygonalArc) {eta : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii Q eta)
    (middleSegments : PolygonalArcCollarMiddleSegmentData Q controlRadii)
    (forbiddenMargins : PolygonalArcCollarMiddleForbiddenMargins
      Q controlRadii middleSegments)
    (compatibleTubes : PolygonalArcCollarCompatibleOrientedTubeData
      Q controlRadii middleSegments forbiddenMargins)
    (source d : EuclideanSpace ℝ (Fin 2)) (radius K : ℝ)
    (hfirst : 0 + 1 < Q.vertices.length)
    (hsource0 : Q.vertices[0] = source)
    (hd : d = Q.vertices[1] - source)
    (hK : 0 < K) (hKDef : K = compatibleTubes.initialConeBound 0 hfirst)
    (hCoords : ∀ q a b,
      q = source + a • d + b • PlanarRot90 d →
      q ∈ Metric.ball source radius →
      a ^ 2 + b ^ 2 < (radius / ‖d‖) ^ 2) :
    ∀ q, q ∈ Metric.ball source radius →
      q ∈ compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf
        0 hfirst →
      ∃ z : EuclideanSpace ℝ (Fin 2),
        (0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (radius / ‖d‖) ^ 2 ∧
          -K * z 0 < z 1 ∧ z 1 < 0) ∧
        source + z 0 • d + z 1 • PlanarRot90 d = q := by
  intro q hqBall hqHalf
  let sep := compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
  rw [sep.rightHalf_eq] at hqHalf
  rcases hqHalf with ⟨t, ht, s, hs, hqFormula⟩
  let z : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![t, s]
  have hqChart : q = source + t • d + s • PlanarRot90 d := by
    rw [compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn] at hqFormula
    calc
      q = AffineMap.lineMap Q.vertices[0] Q.vertices[1] t +
          s • PlanarRot90 (Q.vertices[1] - Q.vertices[0]) := hqFormula
      _ = source + t • d + s • PlanarRot90 d := by
        simp only [AffineMap.lineMap_apply_module]
        rw [hsource0, hd]
        module
  refine ⟨z, ?_, ?_⟩
  · dsimp [z]
    refine ⟨(sep.lowerParam_pos 0 hfirst).trans ht.1,
      hCoords q t s hqChart hqBall, ?_, hs.2⟩
    have hw := compatibleTubes.initial_halfWidth_lt_cone_mul_lowerParam 0 hfirst
    have htLower : sep.lowerParam 0 hfirst < t := ht.1
    calc
      -K * t < -K * sep.lowerParam 0 hfirst := by nlinarith
      _ < -sep.halfWidth 0 hfirst := by
        have hw' : sep.halfWidth 0 hfirst < K * sep.lowerParam 0 hfirst := by
          simpa [sep, hKDef] using hw
        linarith
      _ < s := hs.1
  · simpa [z] using hqChart.symm

private lemma simultaneousBigonSourceLeftHalfWide
    (Q : PolygonalArc) {eta : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii Q eta)
    (middleSegments : PolygonalArcCollarMiddleSegmentData Q controlRadii)
    (forbiddenMargins : PolygonalArcCollarMiddleForbiddenMargins
      Q controlRadii middleSegments)
    (compatibleTubes : PolygonalArcCollarCompatibleOrientedTubeData
      Q controlRadii middleSegments forbiddenMargins)
    (source d : EuclideanSpace ℝ (Fin 2)) (radius K : ℝ)
    (hfirst : 0 + 1 < Q.vertices.length)
    (hsource0 : Q.vertices[0] = source)
    (hd : d = Q.vertices[1] - source)
    (hK : 0 < K) (hKDef : K = compatibleTubes.initialConeBound 0 hfirst)
    (hCoords : ∀ q a b,
      q = source + a • d + b • PlanarRot90 d →
      q ∈ Metric.ball source radius →
      a ^ 2 + b ^ 2 < (radius / ‖d‖) ^ 2) :
    ∀ q, q ∈ Metric.ball source radius →
      q ∈ compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf
        0 hfirst →
      ∃ z : EuclideanSpace ℝ (Fin 2),
        (0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (radius / ‖d‖) ^ 2 ∧
          0 < z 1 ∧ z 1 < K * z 0) ∧
        source + z 0 • d + z 1 • PlanarRot90 d = q := by
  intro q hqBall hqHalf
  let sep := compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
  rw [sep.leftHalf_eq] at hqHalf
  rcases hqHalf with ⟨t, ht, s, hs, hqFormula⟩
  let z : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![t, s]
  have hqChart : q = source + t • d + s • PlanarRot90 d := by
    rw [compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn] at hqFormula
    calc
      q = AffineMap.lineMap Q.vertices[0] Q.vertices[1] t +
          s • PlanarRot90 (Q.vertices[1] - Q.vertices[0]) := hqFormula
      _ = source + t • d + s • PlanarRot90 d := by
        simp only [AffineMap.lineMap_apply_module]
        rw [hsource0, hd]
        module
  refine ⟨z, ?_, ?_⟩
  · dsimp [z]
    refine ⟨(sep.lowerParam_pos 0 hfirst).trans ht.1,
      hCoords q t s hqChart hqBall, hs.1, ?_⟩
    have hw := compatibleTubes.initial_halfWidth_lt_cone_mul_lowerParam 0 hfirst
    have htLower : sep.lowerParam 0 hfirst < t := ht.1
    calc
      s < sep.halfWidth 0 hfirst := hs.2
      _ < K * sep.lowerParam 0 hfirst := by simpa [sep, hKDef] using hw
      _ < K * t := mul_lt_mul_of_pos_left htLower hK
  · simpa [z] using hqChart.symm

private lemma simultaneousBigonWideSourceAvoidAxis
    (source d : EuclideanSpace ℝ (Fin 2)) (radius K : ℝ)
    (hd : d ≠ 0) (positiveSide : Prop) [Decidable positiveSide]
    (wideLeft wideRight Wide : Set (EuclideanSpace ℝ (Fin 2)))
    (hWide : Wide = if positiveSide then wideRight else wideLeft)
    (hRight : wideRight = {q | ∃ z : EuclideanSpace ℝ (Fin 2),
      (0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (radius / ‖d‖) ^ 2 ∧
        -K * z 0 < z 1 ∧ z 1 < 0) ∧
      source + z 0 • d + z 1 • PlanarRot90 d = q})
    (hLeft : wideLeft = {q | ∃ z : EuclideanSpace ℝ (Fin 2),
      (0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (radius / ‖d‖) ^ 2 ∧
        0 < z 1 ∧ z 1 < K * z 0) ∧
      source + z 0 • d + z 1 • PlanarRot90 d = q}) :
    Wide ∩ {q | ∃ c : ℝ, 0 ≤ c ∧ q = source + c • d} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  rcases hq.2 with ⟨c, _hc, hqAxis⟩
  have axisCoefficientZero :
      inner ℝ (q - source) (PlanarRot90 d) / (‖d‖ ^ 2) = 0 := by
    rw [hqAxis]
    simp only [add_sub_cancel_left, inner_smul_left, PlanarRot90Orthogonal,
      mul_zero, zero_div]
  by_cases hpos : positiveSide
  · have hqSector : q ∈ wideRight := by
      rw [hWide, if_pos hpos] at hq
      exact hq.1
    rw [hRight] at hqSector
    rcases hqSector with ⟨z, hz, hqFormula⟩
    have hrep : q - source = z 0 • d + z 1 • PlanarRot90 d := by
      rw [← hqFormula]
      abel
    have hcoeff := PlanarRot90CoefficientUniqueness
      (d := d) (v := q - source) hd hrep
    have hz1 : z 1 = 0 := hcoeff.2.trans axisCoefficientZero
    linarith [hz.2.2.2]
  · have hqSector : q ∈ wideLeft := by
      rw [hWide, if_neg hpos] at hq
      exact hq.1
    rw [hLeft] at hqSector
    rcases hqSector with ⟨z, hz, hqFormula⟩
    have hrep : q - source = z 0 • d + z 1 • PlanarRot90 d := by
      rw [← hqFormula]
      abel
    have hcoeff := PlanarRot90CoefficientUniqueness
      (d := d) (v := q - source) hd hrep
    have hz1 : z 1 = 0 := hcoeff.2.trans axisCoefficientZero
    linarith [hz.2.2.1]

private lemma simultaneousBigonSelectedSourceWideFromPieces
    (Q : PolygonalArc) {eta : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii Q eta)
    (middleSegments : PolygonalArcCollarMiddleSegmentData Q controlRadii)
    (forbiddenMargins : PolygonalArcCollarMiddleForbiddenMargins
      Q controlRadii middleSegments)
    (compatibleTubes : PolygonalArcCollarCompatibleOrientedTubeData
      Q controlRadii middleSegments forbiddenMargins)
    (vertexLocalPieces : PolygonalArcCollarVertexLocalPieceData Q
      controlRadii middleSegments forbiddenMargins
      compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData)
    (localSideData : PolygonalArcCollarLocalSideData Q controlRadii
      middleSegments forbiddenMargins compatibleTubes.orientedTubes
      vertexLocalPieces)
    (S : PolygonalSideStrips Q)
    (Ball wideLeft wideRight Selected Wide : Set (EuclideanSpace ℝ (Fin 2)))
    (positiveSide : Prop) [Decidable positiveSide]
    (hfirst : 0 + 1 < Q.vertices.length)
    (hSelected : Selected = if positiveSide then S.rightStrip else S.leftStrip)
    (hWide : Wide = if positiveSide then wideRight else wideLeft)
    (hLeftEq : S.leftStrip =
      ((⋃ (j : ℕ), ⋃ (hj : j + 1 < Q.vertices.length),
          compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf
            j hj) ∪
        (⋃ i : Fin Q.vertices.length, localSideData.leftSidePiece i)))
    (hRightEq : S.rightStrip =
      ((⋃ (j : ℕ), ⋃ (hj : j + 1 < Q.vertices.length),
          compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf
            j hj) ∪
        (⋃ i : Fin Q.vertices.length, localSideData.rightSidePiece i)))
    (hTubeOnly : ∀ q, q ∈ Ball → ∀ m,
      ∀ hm : m + 1 < Q.vertices.length,
        q ∈ compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.tube
          m hm → m = 0)
    (hVertexIndex : ∀ q, q ∈ Ball → ∀ idx,
      q ∈ localSideData.vertexCollar idx → idx.1 = 0)
    (hRightHalf : ∀ q, q ∈ Ball →
      q ∈ compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.rightHalf
        0 hfirst → q ∈ wideRight)
    (hLeftHalf : ∀ q, q ∈ Ball →
      q ∈ compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData.leftHalf
        0 hfirst → q ∈ wideLeft)
    (hRightPiece : ∀ q, q ∈ Ball →
      q ∈ localSideData.rightSidePiece ⟨0, by omega⟩ → q ∈ wideRight)
    (hLeftPiece : ∀ q, q ∈ Ball →
      q ∈ localSideData.leftSidePiece ⟨0, by omega⟩ → q ∈ wideLeft) :
    Selected ∩ Ball ⊆ Wide := by
  intro q hq
  let sep := compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
  by_cases hpos : positiveSide
  · have hqRight : q ∈ S.rightStrip := by
      rw [hSelected, if_pos hpos] at hq
      exact hq.1
    rw [hRightEq] at hqRight
    rw [hWide, if_pos hpos]
    rcases hqRight with hqHalf | hqPiece
    · rcases Set.mem_iUnion.mp hqHalf with ⟨m, hqHalf⟩
      rcases Set.mem_iUnion.mp hqHalf with ⟨hm, hqHalf⟩
      have hm0 := hTubeOnly q hq.2 m hm
        (sep.rightHalf_subset_tube m hm hqHalf)
      subst m
      exact hRightHalf q hq.2 hqHalf
    · rcases Set.mem_iUnion.mp hqPiece with ⟨idx, hqPiece⟩
      have hidx0 := hVertexIndex q hq.2 idx
        (localSideData.rightSidePiece_subset_vertexCollar idx hqPiece)
      have hidx : idx = (⟨0, by omega⟩ : Fin Q.vertices.length) := Fin.ext hidx0
      rw [hidx] at hqPiece
      exact hRightPiece q hq.2 hqPiece
  · have hqLeft : q ∈ S.leftStrip := by
      rw [hSelected, if_neg hpos] at hq
      exact hq.1
    rw [hLeftEq] at hqLeft
    rw [hWide, if_neg hpos]
    rcases hqLeft with hqHalf | hqPiece
    · rcases Set.mem_iUnion.mp hqHalf with ⟨m, hqHalf⟩
      rcases Set.mem_iUnion.mp hqHalf with ⟨hm, hqHalf⟩
      have hm0 := hTubeOnly q hq.2 m hm
        (sep.leftHalf_subset_tube m hm hqHalf)
      subst m
      exact hLeftHalf q hq.2 hqHalf
    · rcases Set.mem_iUnion.mp hqPiece with ⟨idx, hqPiece⟩
      have hidx0 := hVertexIndex q hq.2 idx
        (localSideData.leftSidePiece_subset_vertexCollar idx hqPiece)
      have hidx : idx = (⟨0, by omega⟩ : Fin Q.vertices.length) := Fin.ext hidx0
      rw [hidx] at hqPiece
      exact hLeftPiece q hq.2 hqPiece

private lemma simultaneousBigonOldCoreSubsetOld
    {X : Type*} (A B Bplus Rbeta H : Set X) :
    B ∪ Bplus ∪ Rbeta ∪ H ⊆ A ∪ B ∪ Bplus ∪ Rbeta ∪ H := by
  intro q hq
  rcases hq with ((hqB | hqBplus) | hqRbeta) | hqH
  · exact Or.inl (Or.inl (Or.inl (Or.inr hqB)))
  · exact Or.inl (Or.inl (Or.inr hqBplus))
  · exact Or.inl (Or.inr hqRbeta)
  · exact Or.inr hqH

private lemma simultaneousBigonSelectedOldCoreLocalization
    {X : Type*}
    (Selected OldCore Old SourceOpen TerminalOpen TerminalClosed EndpointEvents
      Events EndpointOpen FarOld : Set X)
    (hEndpointOpen : EndpointOpen = SourceOpen ∪ TerminalOpen ∪ EndpointEvents)
    (hFarOld : FarOld = OldCore \ EndpointOpen)
    (hCoreOld : OldCore ⊆ Old)
    (hTerminalSubset : TerminalOpen ⊆ TerminalClosed)
    (hEventsSubset : EndpointEvents ⊆ Events)
    (hSourceAvoid : (Selected ∩ SourceOpen) ∩ Old = ∅)
    (hTerminalAvoid : (Selected ∩ TerminalClosed) ∩ Old = ∅)
    (hFarAvoid : Disjoint Selected FarOld) :
    Selected ∩ OldCore ⊆ Events := by
  intro q hq
  by_cases hqOpen : q ∈ EndpointOpen
  · rw [hEndpointOpen] at hqOpen
    rcases hqOpen with (hqSource | hqTerminal) | hqEvent
    · have hqOld : q ∈ Old := hCoreOld hq.2
      exact False.elim
        (Set.eq_empty_iff_forall_notMem.mp hSourceAvoid q
          ⟨⟨hq.1, hqSource⟩, hqOld⟩)
    · have hqOld : q ∈ Old := hCoreOld hq.2
      exact False.elim
        (Set.eq_empty_iff_forall_notMem.mp hTerminalAvoid q
          ⟨⟨hq.1, hTerminalSubset hqTerminal⟩, hqOld⟩)
    · exact hEventsSubset hqEvent
  · have hqFar : q ∈ FarOld := by
      rw [hFarOld]
      exact ⟨hq.2, hqOpen⟩
    exact False.elim (Set.disjoint_left.mp hFarAvoid hq.1 hqFar)

private lemma simultaneousBigonSelectedMeetsSubset
    {X : Type*} (Selected H OldCore Events : Set X)
    (hHCore : H ⊆ OldCore)
    (hLocalization : Selected ∩ OldCore ⊆ Events) :
    Selected ∩ H ⊆ Events := by
  intro q hq
  exact hLocalization ⟨hq.1, hHCore hq.2⟩

private lemma simultaneousBigonSelectedAvoidsEventForbidden
    {X : Type*} [PseudoMetricSpace X]
    (XA : Finset X) (eventRadius : X → ℝ)
    (Selected B Bplus Rbeta H Bad OldCore : Set X)
    (eventForbidden : X → Set X)
    (hOldCore : OldCore = B ∪ Bplus ∪ Rbeta ∪ H)
    (hBadH : Bad ⊆ H)
    (hLocalization : Selected ∩ OldCore ⊆
      ⋃ p ∈ (XA : Set X), Metric.ball p (eventRadius p))
    (hBForbidden : ∀ p, B ⊆ eventForbidden p)
    (hBplusForbidden : ∀ p, Bplus ⊆ eventForbidden p)
    (hBadForbidden : ∀ p, Bad ⊆ eventForbidden p)
    (hEventAvoid : ∀ p, p ∈ XA →
      Disjoint (Metric.closedBall p (eventRadius p)) (eventForbidden p))
    (hRbetaAvoid : ∀ p, p ∈ XA →
      Metric.ball p (eventRadius p) ∩ Rbeta = ∅) :
    Selected ∩ (B ∪ Bplus ∪ Rbeta ∪ Bad) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hqCore : q ∈ OldCore := by
    rw [hOldCore]
    rcases hq.2 with ((hqB | hqBplus) | hqRbeta) | hqBad
    · exact Or.inl (Or.inl (Or.inl hqB))
    · exact Or.inl (Or.inl (Or.inr hqBplus))
    · exact Or.inl (Or.inr hqRbeta)
    · exact Or.inr (hBadH hqBad)
  have hqEvent := hLocalization ⟨hq.1, hqCore⟩
  rcases Set.mem_iUnion.mp hqEvent with ⟨p, hqEvent⟩
  rcases Set.mem_iUnion.mp hqEvent with ⟨hp, hqBall⟩
  rcases hq.2 with ((hqB | hqBplus) | hqRbeta) | hqBad
  · exact Set.disjoint_left.mp (hEventAvoid p hp)
      (Metric.ball_subset_closedBall hqBall) (hBForbidden p hqB)
  · exact Set.disjoint_left.mp (hEventAvoid p hp)
      (Metric.ball_subset_closedBall hqBall) (hBplusForbidden p hqBplus)
  · have hqEmpty : q ∈ Metric.ball p (eventRadius p) ∩ Rbeta :=
      ⟨hqBall, hqRbeta⟩
    rw [hRbetaAvoid p hp] at hqEmpty
    exact hqEmpty
  · exact Set.disjoint_left.mp (hEventAvoid p hp)
      (Metric.ball_subset_closedBall hqBall) (hBadForbidden p hqBad)
-- [TABLET NODE: OrdinaryAdjacentEdgesSimultaneousBigonGeometryExists]
private structure SimultaneousBigonGeometryHypotheses
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (u : V) (firstEdge secondEdge : G.edgeFinset)
    (firstArc secondArc : PolygonalArc)
    (x y : EuclideanSpace ℝ (Fin 2))
    (FirstCut : PolygonalArcPointCutData firstArc x)
    (SecondCut : PolygonalArcPointCutData secondArc x)
    (A B Bplus Rbeta H : Set (EuclideanSpace ℝ (Fin 2)))
    (Tail : BigonRerouteOrderedBetaTailData
      G D secondEdge u y B Bplus Rbeta H)
    (retainedArc : G.edgeFinset → PolygonalArc)
    (XA : Finset (EuclideanSpace ℝ (Fin 2)))
    (hx : x ∈ D.crossingSet)
    (Disk : OrdinaryLabeledCrossingDiskData G D ⟨x, hx⟩)
    (i j : ℕ)
    (hi : i + 1 < (D.edgeArc firstEdge).vertices.length)
    (hj : j + 1 < (D.edgeArc secondEdge).vertices.length) where
  hclean : ∀ (e f : G.edgeFinset)
      (p : EuclideanSpace ℝ (Fin 2)), e ≠ f →
        p ∈ (D.edgeArc e).relativeInterior →
          p ∈ (D.edgeArc f).relativeInterior →
            ∃ i j : ℕ,
              ∃ (hi : i + 1 < (D.edgeArc e).vertices.length)
                (hj : j + 1 < (D.edgeArc f).vertices.length),
                p ∈ openSegment ℝ (D.edgeArc e).vertices[i]
                    (D.edgeArc e).vertices[i + 1] ∧
                  p ∈ openSegment ℝ (D.edgeArc f).vertices[j]
                    (D.edgeArc f).vertices[j + 1] ∧
                    ¬ ∃ c : ℝ,
                      (D.edgeArc f).vertices[j + 1] -
                          (D.edgeArc f).vertices[j] =
                        c • ((D.edgeArc e).vertices[i + 1] -
                          (D.edgeArc e).vertices[i])
  hedges : firstEdge ≠ secondEdge
  hfirstCarrier : firstArc.carrier = (D.edgeArc firstEdge).carrier
  hfirstRelative : firstArc.relativeInterior =
      (D.edgeArc firstEdge).relativeInterior
  hfirstSource : firstArc.source = D.vertexPlacement u
  hsecondCarrier : secondArc.carrier = (D.edgeArc secondEdge).carrier
  hsecondRelative : secondArc.relativeInterior =
      (D.edgeArc secondEdge).relativeInterior
  hsecondSource : secondArc.source = D.vertexPlacement u
  hxFirst : x ∈ (D.edgeArc firstEdge).relativeInterior
  hxSecond : x ∈ (D.edgeArc secondEdge).relativeInterior
  hySecond : y ∈ (D.edgeArc secondEdge).relativeInterior
  hyx : y ≠ x
  hA : A = FirstCut.prefixArc.carrier
  hB : B = SecondCut.prefixArc.carrier
  hBplus : Bplus = segment ℝ x y
  hAB : A ∩ B = ({D.vertexPlacement u, x} : Set _)
  hBBplus : B ∩ Bplus = ({x} : Set _)
  hBplusBall : Bplus ⊆ Metric.ball x Disk.radius
  hRbeta : Rbeta =
      (D.edgeArc secondEdge).carrier \ ((B ∪ Bplus) \ ({y} : Set _))
  hH : H =
      (⋃ edge : G.edgeFinset,
        if edge = firstEdge then
          (D.edgeArc edge).carrier \
            (A \ ({D.vertexPlacement u, x} : Set _))
        else if edge = secondEdge then
          (D.edgeArc edge).carrier \
            ((B \ ({D.vertexPlacement u, x} : Set _)) ∪
              (Bplus \ ({x, y} : Set _)))
        else (D.edgeArc edge).carrier) ∪
      {p | ∃ v : V, v ≠ u ∧ p = D.vertexPlacement v}
  hATail : Disjoint A Tail.tailArc.carrier
  hretained : retainedArc = fun e =>
      if e = firstEdge then FirstCut.suffixArc
      else if e = secondEdge then Tail.tailArc
      else D.edgeArc e
  hXASpec : ∀ p, p ∈ XA ↔
      p ∈ A \ ({D.vertexPlacement u, x} : Set _) ∧ p ∈ H
  hFirstPrefixTransfer : ∀ p i
        (hi : i + 1 < (D.edgeArc firstEdge).vertices.length),
      p ∈ openSegment ℝ (D.edgeArc firstEdge).vertices[i]
          (D.edgeArc firstEdge).vertices[i + 1] →
      p ∈ FirstCut.prefixArc.carrier → p ≠ x →
      ∃ j : ℕ, ∃ hj : j + 1 < FirstCut.prefixArc.vertices.length,
        p ∈ openSegment ℝ FirstCut.prefixArc.vertices[j]
            FirstCut.prefixArc.vertices[j + 1] ∧
          ∃ scale : ℝ, scale ≠ 0 ∧
            FirstCut.prefixArc.vertices[j + 1] -
                FirstCut.prefixArc.vertices[j] =
              scale • ((D.edgeArc firstEdge).vertices[i + 1] -
                (D.edgeArc firstEdge).vertices[i])
  hDiskEdges : (Disk.firstEdge = firstEdge ∧ Disk.secondEdge = secondEdge) ∨
      (Disk.firstEdge = secondEdge ∧ Disk.secondEdge = firstEdge)
  hxOpenFirst : x ∈ openSegment ℝ
      ((D.edgeArc firstEdge).vertices.get ⟨i, by omega⟩)
      ((D.edgeArc firstEdge).vertices.get ⟨i + 1, by omega⟩)
  hxOpenSecond : x ∈ openSegment ℝ
      ((D.edgeArc secondEdge).vertices.get ⟨j, by omega⟩)
      ((D.edgeArc secondEdge).vertices.get ⟨j + 1, by omega⟩)
  hnonparallel : ¬ ∃ c : ℝ,
      (D.edgeArc secondEdge).vertices.get ⟨j + 1, by omega⟩ -
          (D.edgeArc secondEdge).vertices.get ⟨j, by omega⟩ =
        c • ((D.edgeArc firstEdge).vertices.get ⟨i + 1, by omega⟩ -
          (D.edgeArc firstEdge).vertices.get ⟨i, by omega⟩)

private noncomputable def ordinaryAdjacentEdgesSimultaneousBigonGeometryPrepareFromContext
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (u : V) (firstEdge secondEdge : G.edgeFinset)
    (firstArc secondArc : PolygonalArc)
    (x y : EuclideanSpace ℝ (Fin 2))
    (FirstCut : PolygonalArcPointCutData firstArc x)
    (SecondCut : PolygonalArcPointCutData secondArc x)
    (A B Bplus Rbeta H : Set (EuclideanSpace ℝ (Fin 2)))
    (Tail : BigonRerouteOrderedBetaTailData
      G D secondEdge u y B Bplus Rbeta H)
    (retainedArc : G.edgeFinset → PolygonalArc)
    (XA : Finset (EuclideanSpace ℝ (Fin 2)))
    (hx : x ∈ D.crossingSet)
    (Disk : OrdinaryLabeledCrossingDiskData G D ⟨x, hx⟩)
    (i j : ℕ)
    (hi : i + 1 < (D.edgeArc firstEdge).vertices.length)
    (hj : j + 1 < (D.edgeArc secondEdge).vertices.length)
    (ctx : SimultaneousBigonGeometryHypotheses G D u firstEdge secondEdge
      firstArc secondArc x y FirstCut SecondCut A B Bplus Rbeta H Tail
      retainedArc XA hx Disk i j hi hj) :
    Nonempty (OrdinaryAdjacentEdgesSimultaneousBigonGeometryData
      G D u firstEdge secondEdge x y A B Bplus Rbeta H
      (FirstCut.prefixArc) XA hx Disk) := by
-- BODY
  classical
  rcases ctx with ⟨hclean, hedges, hfirstCarrier, hfirstRelative, hfirstSource,
    hsecondCarrier, hsecondRelative, hsecondSource, hxFirst, hxSecond,
    hySecond, hyx, hA, hB, hBplus, hAB, hBBplus, hBplusBall, hRbeta, hH,
    hATail, hretained, hXASpec, hFirstPrefixTransfer, hDiskEdges,
    hxOpenFirst, hxOpenSecond, hnonparallel⟩
  let Aarc := FirstCut.prefixArc
  have hAarcSource : Aarc.source = D.vertexPlacement u := by
    dsimp [Aarc]
    rw [FirstCut.prefix_source, hfirstSource]
  have hAarcTarget : Aarc.target = x := by
    dsimp [Aarc]
    exact FirstCut.prefix_target
  obtain ⟨Kclean, hKcarrier, hKsegments, hKpoints, hKvertices,
      hKevent⟩ :=
    OrdinaryAdjacentEdgesProtectedTrimmedPresentation G D u firstEdge
      secondEdge firstArc x y FirstCut A B Bplus Rbeta H Tail retainedArc XA
      hclean hedges hfirstCarrier hfirstRelative hfirstSource hxFirst hA
      hRbeta hH hATail hretained hXASpec hFirstPrefixTransfer
  have hBadFinite : ((Kclean.points : Set
      (EuclideanSpace ℝ (Fin 2)))).Finite := Kclean.points.finite_toSet
  have second_disk_local :
      Metric.closedBall x Disk.radius ∩ (D.edgeArc secondEdge).carrier =
        Metric.closedBall x Disk.radius ∩
      segment ℝ (D.edgeArc secondEdge).vertices[j]
            (D.edgeArc secondEdge).vertices[j + 1] :=
    simultaneousBigonSecondDiskLocal G D firstEdge secondEdge x hx Disk
      hDiskEdges j hj hxOpenSecond
  have event_data := hKevent
  let eventIndex : EuclideanSpace ℝ (Fin 2) → ℕ := fun p =>
    if hp : p ∈ XA then Classical.choose (event_data p hp).2 else 0
  have eventIndex_spec (p) (hp : p ∈ XA) :
      ∃ hj : eventIndex p + 1 < Aarc.vertices.length,
        p ∈ openSegment ℝ Aarc.vertices[eventIndex p]
          Aarc.vertices[eventIndex p + 1] ∧
        ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          s ∈ Kclean.segments ∧ p ∈ openSegment ℝ s.1 s.2 ∧
          (¬ ∃ c : ℝ, s.2 - s.1 =
            c • (Aarc.vertices[eventIndex p + 1] -
              Aarc.vertices[eventIndex p])) ∧
          (∀ t, t ∈ Kclean.segments →
            p ∈ openSegment ℝ t.1 t.2 → t = s) ∧
          ∀ upper : ℝ, 0 < upper →
            ∃ r : ℝ, 0 < r ∧ r < upper ∧
              Metric.ball p r ∩ H =
                Metric.ball p r ∩ segment ℝ s.1 s.2 ∧
              Metric.ball p r ∩ Rbeta = ∅ := by
    simpa only [eventIndex, dif_pos hp] using
      (Classical.choose_spec (event_data p hp).2)
  let otherSegments := simultaneousBigonOtherSegments Aarc eventIndex
  have otherSegments_compact (p) : IsCompact (otherSegments p) := by
    simpa only [otherSegments] using
      simultaneousBigonOtherSegmentsCompact Aarc eventIndex p
  have event_not_other (p) (hp : p ∈ XA) : p ∉ otherSegments p := by
    obtain ⟨hj, hpOpen, _⟩ := eventIndex_spec p hp
    change p ∉ simultaneousBigonOtherSegments Aarc eventIndex p
    change p ∉ simultaneousBigonOtherSegments Aarc (fun _ => eventIndex p) p
    exact simultaneousBigonEventNotOther Aarc p (eventIndex p) hj hpOpen
  have hAarcCarrier : Aarc.carrier = A := by
    simpa [Aarc] using hA.symm
  have event_mem_A (p) (hp : p ∈ XA) :
      p ∈ A \ ({D.vertexPlacement u, x} : Set _) := (hXASpec p).1 hp |>.1
  have event_mem_Aarc_relative (p) (hp : p ∈ XA) :
      p ∈ Aarc.relativeInterior := by
    obtain ⟨hj, hpOpen, _⟩ := eventIndex_spec p hp
    exact PolygonalArcOpenSegmentSubsetRelativeInterior Aarc (eventIndex p) hj hpOpen
  have event_mem_first_relative (p) (hp : p ∈ XA) :
      p ∈ (D.edgeArc firstEdge).relativeInterior := by
    have hpx : p ≠ x := by
      intro h
      exact (event_mem_A p hp).2 (by simp [h])
    exact simultaneousBigonPrefixEventMemOldRelative G D firstEdge firstArc x
      FirstCut p hfirstRelative (hAarcCarrier ▸ (event_mem_A p hp).1)
      (event_mem_Aarc_relative p hp) hpx
  have event_not_B (p) (hp : p ∈ XA) : p ∉ B := by
    intro hpB
    have hpAB : p ∈ A ∩ B := ⟨(event_mem_A p hp).1, hpB⟩
    have hpEnds : p ∈ ({D.vertexPlacement u, x} : Set _) := hAB ▸ hpAB
    exact (event_mem_A p hp).2 hpEnds
  have hBplusSecondSegment :=
    simultaneousBigonBplusSecondSegment G D secondEdge x y Bplus hx Disk j hj
      hBplus hBplusBall hySecond hxOpenSecond second_disk_local
  have hBplusSecondCarrier : Bplus ⊆ (D.edgeArc secondEdge).carrier := by
    intro z hz
    rw [(D.edgeArc secondEdge).carrier_eq]
    exact ⟨j, hj, hBplusSecondSegment hz⟩
  have event_not_Bplus (p) (hp : p ∈ XA) : p ∉ Bplus := by
    have hpFirst := event_mem_first_relative p hp
    have hpx : p ≠ x := by
      intro h
      exact (event_mem_A p hp).2 (by simp [h])
    exact simultaneousBigonEventNotBplus G D firstEdge secondEdge x p Bplus hx
      Disk hDiskEdges hBplusBall hBplusSecondCarrier hpFirst hpx
  let eventForbidden : EuclideanSpace ℝ (Fin 2) →
      Set (EuclideanSpace ℝ (Fin 2)) := fun p =>
    ((XA.erase p : Finset (EuclideanSpace ℝ (Fin 2))) : Set _) ∪
      (Aarc.vertices.toFinset : Set _) ∪ B ∪ Bplus ∪
        (Kclean.points : Set _) ∪ otherSegments p
  have hBSubsetEventForbidden : ∀ p, B ⊆ eventForbidden p := by
    intro p q hq
    exact Or.inl (Or.inl (Or.inl (Or.inr hq)))
  have hBplusSubsetEventForbidden : ∀ p, Bplus ⊆ eventForbidden p := by
    intro p q hq
    exact Or.inl (Or.inl (Or.inr hq))
  have hBadSubsetEventForbidden : ∀ p,
      (Kclean.points : Set (EuclideanSpace ℝ (Fin 2))) ⊆ eventForbidden p := by
    intro p q hq
    exact Or.inl (Or.inr hq)
  have hBcompact : IsCompact B := by
    rw [hB]
    exact PolygonalArcCarrierCompact SecondCut.prefixArc
  have hBplusCompact : IsCompact Bplus := by
    rw [hBplus]
    rw [segment_eq_image' ℝ]
    exact isCompact_Icc.image (by fun_prop)
  have eventForbidden_compact (p) : IsCompact (eventForbidden p) := by
    dsimp [eventForbidden]
    exact (((Set.Finite.isCompact (Finset.finite_toSet (XA.erase p))).union
      (Set.Finite.isCompact Aarc.vertices.toFinset.finite_toSet)).union
      hBcompact).union hBplusCompact |>.union hBadFinite.isCompact |>.union
        (otherSegments_compact p)
  have event_not_forbidden (p) (hp : p ∈ XA) : p ∉ eventForbidden p := by
    intro hpF
    rcases hpF with (((((hpErase | hpVertices) | hpB) | hpBplus) | hpBad) | hpOther)
    · exact (Finset.mem_erase.mp hpErase).1 rfl
    · obtain ⟨hj, hpOpen, _⟩ := eventIndex_spec p hp
      exact (simultaneousBigonOpenNotVertices Aarc p (eventIndex p) hj hpOpen)
        (by simpa using hpVertices)
    · exact event_not_B p hp hpB
    · exact event_not_Bplus p hp hpBplus
    · exact (event_data p hp).1 hpBad
    · exact event_not_other p hp hpOther
  have eventClearance_exists (p) (hp : p ∈ XA) :
      ∃ ε : ℝ, 0 < ε ∧ Metric.ball p ε ⊆ (eventForbidden p)ᶜ := by
    have hpCompl : p ∈ (eventForbidden p)ᶜ := event_not_forbidden p hp
    have hnhds : (eventForbidden p)ᶜ ∈ nhds p :=
      (eventForbidden_compact p).isClosed.isOpen_compl.mem_nhds hpCompl
    exact Metric.mem_nhds_iff.mp hnhds
  let eventClearance : EuclideanSpace ℝ (Fin 2) → ℝ := fun p =>
    if hp : p ∈ XA then Classical.choose (eventClearance_exists p hp) else 1
  have eventClearance_spec (p) (hp : p ∈ XA) :
      0 < eventClearance p ∧
        Metric.ball p (eventClearance p) ⊆ (eventForbidden p)ᶜ := by
    simpa only [eventClearance, dif_pos hp] using
      (Classical.choose_spec (eventClearance_exists p hp))
  have eventPackage_exists (p) (hp : p ∈ XA) :
      ∃ r : ℝ,
        ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
          0 < r ∧ r < eventClearance p / 4 ∧
          s ∈ Kclean.segments ∧ p ∈ openSegment ℝ s.1 s.2 ∧
          Metric.ball p r ∩ H = Metric.ball p r ∩ segment ℝ s.1 s.2 ∧
          Metric.ball p r ∩ Rbeta = ∅ := by
    obtain ⟨_hj, _hpOpen, s, hsK, hps, _hnonparallel,
      _hunique, hlocal⟩ := eventIndex_spec p hp
    have hupper : 0 < eventClearance p / 4 := by
      have := (eventClearance_spec p hp).1
      positivity
    obtain ⟨r, hr, hrlt, hHlocal, hRlocal⟩ := hlocal _ hupper
    exact ⟨r, s, hr, hrlt, hsK, hps, hHlocal, hRlocal⟩
  let eventRadius : EuclideanSpace ℝ (Fin 2) → ℝ := fun p =>
    if hp : p ∈ XA then Classical.choose (eventPackage_exists p hp) else 1
  let eventSegment : EuclideanSpace ℝ (Fin 2) →
      EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) :=
    fun p => if hp : p ∈ XA then
      Classical.choose (Classical.choose_spec (eventPackage_exists p hp))
    else (0, 0)
  have eventPackage_spec (p) (hp : p ∈ XA) :
      0 < eventRadius p ∧ eventRadius p < eventClearance p / 4 ∧
      eventSegment p ∈ Kclean.segments ∧
      p ∈ openSegment ℝ (eventSegment p).1 (eventSegment p).2 ∧
      Metric.ball p (eventRadius p) ∩ H =
        Metric.ball p (eventRadius p) ∩
          segment ℝ (eventSegment p).1 (eventSegment p).2 ∧
      Metric.ball p (eventRadius p) ∩ Rbeta = ∅ := by
    simpa only [eventRadius, eventSegment, dif_pos hp] using
      (Classical.choose_spec
        (Classical.choose_spec (eventPackage_exists p hp)))
  have eventBallAvoidsRbeta (p) (hp : p ∈ XA) :
      Metric.ball p (eventRadius p) ∩ Rbeta = ∅ :=
    (eventPackage_spec p hp).2.2.2.2.2
  have eventRadius_lt_clearance (p) (hp : p ∈ XA) :
      eventRadius p < eventClearance p := by
    have hpos := (eventClearance_spec p hp).1
    have hlt := (eventPackage_spec p hp).2.1
    linarith
  have event_closedBall_avoids_forbidden (p) (hp : p ∈ XA) :
      Disjoint (Metric.closedBall p (eventRadius p)) (eventForbidden p) := by
    rw [Set.disjoint_left]
    intro z hzBall hzForbidden
    have hzOpen : z ∈ Metric.ball p (eventClearance p) :=
      Metric.closedBall_subset_ball (eventRadius_lt_clearance p hp) hzBall
    exact (eventClearance_spec p hp).2 hzOpen hzForbidden
  have event_pairwise (p q) (hp : p ∈ XA) (hq : q ∈ XA) (hpq : p ≠ q) :
      Disjoint (Metric.closedBall p (eventRadius p))
        (Metric.closedBall q (eventRadius q)) := by
    rw [Set.disjoint_left]
    intro z hzp hzq
    have hqForbidden : q ∈ eventForbidden p := by
      exact Or.inl (Or.inl (Or.inl (Or.inl
        (Or.inl (Finset.mem_erase.mpr ⟨hpq.symm, hq⟩)))))
    have hpForbidden : p ∈ eventForbidden q := by
      exact Or.inl (Or.inl (Or.inl (Or.inl
        (Or.inl (Finset.mem_erase.mpr ⟨hpq, hp⟩)))))
    have hclearP : eventClearance p ≤ dist p q := by
      by_contra hnot
      have hqBall : q ∈ Metric.ball p (eventClearance p) := by
        rw [Metric.mem_ball, dist_comm]
        exact lt_of_not_ge hnot
      exact (eventClearance_spec p hp).2 hqBall hqForbidden
    have hclearQ : eventClearance q ≤ dist p q := by
      by_contra hnot
      have hpBall : p ∈ Metric.ball q (eventClearance q) := by
        rw [Metric.mem_ball]
        exact lt_of_not_ge hnot
      exact (eventClearance_spec q hq).2 hpBall hpForbidden
    have hrp := (eventPackage_spec p hp).2.1
    have hrq := (eventPackage_spec q hq).2.1
    have hzpDist : dist p z ≤ eventRadius p := by
      simpa [Metric.mem_closedBall, dist_comm] using hzp
    have hzqDist : dist z q ≤ eventRadius q := by
      simpa [Metric.mem_closedBall] using hzq
    have htri := dist_triangle p z q
    have hpqPos : 0 < dist p q := dist_pos.mpr hpq
    linarith
  have event_away_vertices (p) (hp : p ∈ XA) (z)
      (hz : z ∈ Aarc.vertices) :
      z ∉ Metric.closedBall p (eventRadius p) := by
    intro hzBall
    have hzForbidden : z ∈ eventForbidden p := by
      exact Or.inl (Or.inl (Or.inl (Or.inl
        (Or.inr (by simpa using hz)))))
    exact Set.disjoint_left.mp (event_closedBall_avoids_forbidden p hp)
      hzBall hzForbidden
  have first_disk_local := simultaneousBigonFirstDiskLocal G D firstEdge secondEdge
    x hx Disk i hi hxOpenFirst hDiskEdges
  let itarget : ℕ := Aarc.vertices.length - 1
  have hitarget : itarget < Aarc.vertices.length := by
    dsimp [itarget]
    have hlen := Aarc.length_ge_two
    omega
  let jlast : ℕ := Aarc.vertices.length - 2
  have hjlast : jlast + 1 < Aarc.vertices.length := by
    dsimp [jlast]
    have hlen := Aarc.length_ge_two
    omega
  have hjlast_target : jlast + 1 = itarget := by
    dsimp [jlast, itarget]
    omega
  have htargetVertex : Aarc.vertices[itarget] = x := by
    have hget := Aarc.target_eq_last
    rw [List.getLast?_eq_getElem?] at hget
    rw [List.getElem?_eq_getElem hitarget] at hget
    have := Option.some.inj hget
    simpa [hAarcTarget] using this
  have hlastVertex : Aarc.vertices[jlast + 1] = x := by
    have hindex : Aarc.vertices[jlast + 1] = Aarc.vertices[itarget] := by congr
    exact hindex.trans htargetVertex
  let d : EuclideanSpace ℝ (Fin 2) := Aarc.vertices[jlast] - x
  have hd : d ≠ 0 := by
    dsimp [d]
    intro hd0
    have heq : Aarc.vertices[jlast] = Aarc.vertices[itarget] := by
      rw [htargetVertex]
      exact sub_eq_zero.mp hd0
    have hidx := (Aarc.simple_vertices.getElem_inj_iff
      (i := jlast) (j := itarget) (hi := by omega) (hj := hitarget)).1 heq
    dsimp [jlast, itarget] at hidx
    omega
  have hlastSegmentFirst :
      Metric.ball x Disk.radius ∩
          segment ℝ Aarc.vertices[jlast] Aarc.vertices[itarget] ⊆
        segment ℝ (D.edgeArc firstEdge).vertices[i]
          (D.edgeArc firstEdge).vertices[i + 1] := by
    intro z hz
    have hzAarc : z ∈ Aarc.carrier := by
      rw [Aarc.carrier_eq]
      exact ⟨jlast, hjlast, by simpa [hjlast_target] using hz.2⟩
    have hzFirst : z ∈ (D.edgeArc firstEdge).carrier := by
      have hzFirstArc := FirstCut.prefix_carrier_subset hzAarc
      simpa [hfirstCarrier] using hzFirstArc
    have hzClosed : z ∈ Metric.closedBall x Disk.radius :=
      Metric.ball_subset_closedBall hz.1
    have hzLocal : z ∈ Metric.closedBall x Disk.radius ∩
        (D.edgeArc firstEdge).carrier := ⟨hzClosed, hzFirst⟩
    exact (by rw [first_disk_local] at hzLocal; exact hzLocal.2)
  have hlastScale :=
    simultaneousBigonStoredLastDirectionScale G D firstEdge x hx Disk Aarc d
      i jlast itarget hi hjlast hitarget hd htargetVertex rfl hxOpenFirst
      hlastSegmentFirst
  have hsecondScale :=
    simultaneousBigonSecondDirectionScale x y
      (D.edgeArc secondEdge).vertices[j]
      (D.edgeArc secondEdge).vertices[j + 1] hyx hxOpenSecond (by
      intro z hz
      exact hBplusSecondSegment (by simpa [hBplus] using hz))
  have hlinear : LinearIndependent ℝ ![d, y - x] :=
    simultaneousBigonStoredDirectionsLinearIndependent G D firstEdge secondEdge
      d (y - x) i j hi hj hd hlastScale hsecondScale hnonparallel
  let mu : ℝ := inner ℝ (y - x) d / (‖d‖ ^ 2)
  let nuRaw : ℝ := inner ℝ (y - x) (PlanarRot90 d) / (‖d‖ ^ 2)
  have hyDecompRaw : y - x = mu • d + nuRaw • PlanarRot90 d := by
    simpa [mu, nuRaw] using PlanarRot90Decomposition d (y - x) hd
  have hnuRaw : nuRaw ≠ 0 := by
    intro hzero
    have hcol : y - x = mu • d := by simpa [hzero] using hyDecompRaw
    have hp := hlinear
    rw [LinearIndependent.pair_iff' hd] at hp
    exact hp mu hcol.symm
  let positiveSide : Prop := 0 < nuRaw
  let n : EuclideanSpace ℝ (Fin 2) :=
    if positiveSide then PlanarRot90 d else -PlanarRot90 d
  let nu : ℝ := if positiveSide then nuRaw else -nuRaw
  have hnu : 0 < nu := by
    dsimp [nu, positiveSide]
    split_ifs with hpos
    · exact hpos
    · exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hpos) hnuRaw)
  have hyDecomp : y - x = mu • d + nu • n := by
    dsimp [n, nu, positiveSide]
    split_ifs with hpos
    · exact hyDecompRaw
    · simpa using hyDecompRaw
  have hdn : inner ℝ d n = 0 := by
    dsimp [n, positiveSide]
    split_ifs
    · exact PlanarRot90Orthogonal d
    · rw [inner_neg_right, PlanarRot90Orthogonal]
      simp
  have hnd : inner ℝ n d = 0 := by
    rw [real_inner_comm]
    exact hdn
  have hdd : inner ℝ d d = ‖d‖ ^ 2 := real_inner_self_eq_norm_sq d
  have hnn : inner ℝ n n = ‖d‖ ^ 2 := by
    dsimp [n, positiveSide]
    split_ifs
    · rw [real_inner_self_eq_norm_sq, PlanarRot90Norm]
    · rw [real_inner_self_eq_norm_sq, norm_neg, PlanarRot90Norm]
  let K1 : ℝ := nu / (8 * (|mu| + 1))
  have hK1 : 0 < K1 := by
    dsimp [K1]
    positivity
  have hAarc0 : 0 < Aarc.vertices.length := by omega
  have hsource0 := simultaneousBigonSourceAtZero Aarc hAarc0
  have hfirstAarc : 0 + 1 < Aarc.vertices.length := by omega
  let d0 : EuclideanSpace ℝ (Fin 2) := Aarc.vertices[1] - Aarc.source
  have hd0 : d0 ≠ 0 := by
    simpa only [d0] using
      simultaneousBigonInitialDirectionNeZero Aarc hfirstAarc
  have hprefixCarrierSubset : Aarc.carrier ⊆ (D.edgeArc firstEdge).carrier := by
    intro z hz
    have hzFirst := FirstCut.prefix_carrier_subset hz
    simpa [hfirstCarrier] using hzFirst
  have hsourceInStored := simultaneousBigonSourceCarrierTransfer Aarc
    (D.edgeArc firstEdge) (D.vertexPlacement u) hfirstAarc hAarcSource
    hprefixCarrierSubset
  have hsourceStoredEndpoint :=
    simultaneousBigonStoredEndpoint G D u firstEdge hsourceInStored
  obtain ⟨rhoInitial, rhoTerminal, hrhoInitial, hrhoTerminal,
      initialDirections, terminalDirections, hnoInitial, hnoTerminal,
      hcoverInitial, hcoverTerminal⟩ :=
    PlaneDrawingEndpointLocalGermCover G D firstEdge (D.edgeArc firstEdge) rfl
  have positive_direction_scale
      (storedDir : EuclideanSpace ℝ (Fin 2))
      (storedRadius : ℝ) (hstoredRadius : 0 < storedRadius)
      (hray : Metric.ball (D.vertexPlacement u) storedRadius ∩
          (D.edgeArc firstEdge).carrier ⊆
        {q | ∃ c : ℝ, 0 ≤ c ∧
          q = D.vertexPlacement u + c • storedDir}) :
      ∃ a : ℝ, 0 < a ∧ d0 = a • storedDir :=
    simultaneousBigonPositiveDirectionScale Aarc (D.edgeArc firstEdge)
      (D.vertexPlacement u) d0 storedDir hAarc0 hfirstAarc hsource0
      hAarcSource rfl hd0 hprefixCarrierSubset storedRadius hstoredRadius hray
  have source_germ_package :
      ∃ sourceRadius : ℝ,
        ∃ sourceDirections : Finset (EuclideanSpace ℝ (Fin 2)),
          0 < sourceRadius ∧
          (∀ v ∈ sourceDirections,
            ¬ ∃ a : ℝ, 0 < a ∧ v = a • d0) ∧
          (Metric.ball (D.vertexPlacement u) sourceRadius ∩
              OrdinaryDrawingImageWithoutEdge G D firstEdge ⊆
            ({D.vertexPlacement u} : Set _) ∪
              ⋃ v : {v : EuclideanSpace ℝ (Fin 2) // v ∈ sourceDirections},
                {q | ∃ c : ℝ, 0 ≤ c ∧
                  q = D.vertexPlacement u + c • v.1}) ∧
          (Metric.ball (D.vertexPlacement u) sourceRadius ∩
              (D.edgeArc firstEdge).carrier ⊆
            {q | ∃ c : ℝ, 0 ≤ c ∧ q = D.vertexPlacement u + c • d0}) := by
    rcases hsourceStoredEndpoint with hsrc | htgt
    · let hfirstStored : 1 < (D.edgeArc firstEdge).vertices.length :=
        Nat.lt_of_succ_le (D.edgeArc firstEdge).length_ge_two
      have hcoverInitialU := hcoverInitial
      rw [← hsrc] at hcoverInitialU
      let storedDir := (D.edgeArc firstEdge).vertices[1]'hfirstStored -
        (D.edgeArc firstEdge).source
      obtain ⟨rayRadius, hrayRadius, hray⟩ :=
        PolygonalArcSourceEndpointRayCover (D.edgeArc firstEdge)
      have hray' : Metric.ball (D.vertexPlacement u) rayRadius ∩
          (D.edgeArc firstEdge).carrier ⊆
        {q | ∃ c : ℝ, 0 ≤ c ∧
          q = D.vertexPlacement u + c • storedDir} := by
        simpa [storedDir, hsrc] using hray
      obtain ⟨a, ha, hd0scale⟩ :=
        positive_direction_scale storedDir rayRadius hrayRadius hray'
      refine ⟨min rhoInitial rayRadius, initialDirections,
        lt_min hrhoInitial hrayRadius, ?_, ?_, ?_⟩
      · intro v hv
        intro hvd0
        rcases hvd0 with ⟨b, hb, hvb⟩
        exact hnoInitial v hv ⟨b * a, mul_pos hb ha, by
          rw [hvb, hd0scale, smul_smul]⟩
      · intro q hq
        exact hcoverInitialU
          ⟨Metric.ball_subset_ball (min_le_left _ _) hq.1, hq.2⟩
      · rintro q ⟨hqBall, hqEdge⟩
        obtain ⟨c, hc, hq⟩ := hray' ⟨
          Metric.ball_subset_ball (min_le_right _ _) hqBall, hqEdge⟩
        refine ⟨c / a, div_nonneg hc ha.le, ?_⟩
        have ha0 : a ≠ 0 := ha.ne'
        calc
          q = D.vertexPlacement u + c • storedDir := hq
          _ = D.vertexPlacement u + (c / a) • d0 := by
            rw [hd0scale, smul_smul]
            congr 1
            field_simp [ha0]
    · let hprevStored : (D.edgeArc firstEdge).vertices.length - 2 <
          (D.edgeArc firstEdge).vertices.length := by
          have hlen := (D.edgeArc firstEdge).length_ge_two
          omega
      have hcoverTerminalU := hcoverTerminal
      rw [← htgt] at hcoverTerminalU
      let storedDir :=
        (D.edgeArc firstEdge).vertices[
          (D.edgeArc firstEdge).vertices.length - 2]'hprevStored -
            (D.edgeArc firstEdge).target
      obtain ⟨rayRadius, hrayRadius, hray⟩ :=
        PolygonalArcTargetEndpointRayCover (D.edgeArc firstEdge)
      have hray' : Metric.ball (D.vertexPlacement u) rayRadius ∩
          (D.edgeArc firstEdge).carrier ⊆
        {q | ∃ c : ℝ, 0 ≤ c ∧
          q = D.vertexPlacement u + c • storedDir} := by
        simpa [storedDir, htgt] using hray
      obtain ⟨a, ha, hd0scale⟩ :=
        positive_direction_scale storedDir rayRadius hrayRadius hray'
      refine ⟨min rhoTerminal rayRadius, terminalDirections,
        lt_min hrhoTerminal hrayRadius, ?_, ?_, ?_⟩
      · intro v hv
        intro hvd0
        rcases hvd0 with ⟨b, hb, hvb⟩
        exact hnoTerminal v hv ⟨b * a, mul_pos hb ha, by
          rw [hvb, hd0scale, smul_smul]⟩
      · intro q hq
        exact hcoverTerminalU
          ⟨Metric.ball_subset_ball (min_le_left _ _) hq.1, hq.2⟩
      · rintro q ⟨hqBall, hqEdge⟩
        obtain ⟨c, hc, hq⟩ := hray' ⟨
          Metric.ball_subset_ball (min_le_right _ _) hqBall, hqEdge⟩
        refine ⟨c / a, div_nonneg hc ha.le, ?_⟩
        have ha0 : a ≠ 0 := ha.ne'
        calc
          q = D.vertexPlacement u + c • storedDir := hq
          _ = D.vertexPlacement u + (c / a) • d0 := by
            rw [hd0scale, smul_smul]
            congr 1
            field_simp [ha0]
  obtain ⟨sourceRadius, sourceDirections, hsourceRadius,
      hsourceNoPos, hsourceCover, hsourceEdgeCover⟩ := source_germ_package
  obtain ⟨sourceKappa, hsourceKappa, hsourceSectors⟩ :=
    PlanarFiniteRayCappedSideSectors sourceDirections
      (D.vertexPlacement u) d0 sourceRadius hd0 hsourceRadius hsourceNoPos
  let K0 : ℝ := sourceKappa / 2
  have hK0 : 0 < K0 := by dsimp [K0]; linarith
  obtain ⟨r0Base, r1Base, hIsoBase⟩ :=
    PolygonalArcEndpointIsolationExists Aarc
  let EventClosed : Set (EuclideanSpace ℝ (Fin 2)) :=
    ⋃ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ XA},
      Metric.closedBall p.1 (eventRadius p.1)
  have hEventClosedCompact : IsCompact EventClosed := by
    dsimp [EventClosed]
    exact isCompact_iUnion (fun p => isCompact_closedBall p.1 (eventRadius p.1))
  have hsourceNotEventClosed : D.vertexPlacement u ∉ EventClosed := by
    intro hs
    rcases Set.mem_iUnion.mp hs with ⟨p, hsBall⟩
    have hsourceVertex : D.vertexPlacement u ∈ Aarc.vertices := by
      rw [← hAarcSource, ← hsource0]
      exact List.getElem_mem (by omega)
    exact event_away_vertices p.1 p.2 (D.vertexPlacement u) hsourceVertex hsBall
  have htargetNotEventClosed : x ∉ EventClosed := by
    intro hs
    rcases Set.mem_iUnion.mp hs with ⟨p, hsBall⟩
    have hxVertex : x ∈ Aarc.vertices := by
      rw [← htargetVertex]
      exact List.getElem_mem hitarget
    exact event_away_vertices p.1 p.2 x hxVertex hsBall
  have endpointEventClearance (z : EuclideanSpace ℝ (Fin 2))
      (hz : z ∉ EventClosed) :
      ∃ eps : ℝ, 0 < eps ∧ Metric.ball z eps ⊆ EventClosedᶜ := by
    exact Metric.mem_nhds_iff.mp
      (hEventClosedCompact.isClosed.isOpen_compl.mem_nhds hz)
  obtain ⟨sourceEventEps, hsourceEventEps, hsourceEventBall⟩ :=
    endpointEventClearance (D.vertexPlacement u) hsourceNotEventClosed
  obtain ⟨targetEventEps, htargetEventEps, htargetEventBall⟩ :=
    endpointEventClearance x htargetNotEventClosed
  have hnormd : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hDiskRadius : 0 < Disk.radius := Disk.firstBranch.radius_pos
  have hyBplus : y ∈ Bplus := by
    rw [hBplus]
    exact right_mem_segment ℝ x y
  have hyDisk : y ∈ Metric.ball x Disk.radius := hBplusBall hyBplus
  have hyDist : dist x y < Disk.radius := by
    simpa [dist_comm] using hyDisk
  let rhoTerm : ℝ := (dist x y + Disk.radius) / 2
  have hRhoTermBounds := simultaneousBigonMidpointBounds (dist x y) Disk.radius
    (dist_pos.mpr hyx.symm) hyDist
  have hyRhoTerm : dist x y < rhoTerm := by simpa only [rhoTerm] using hRhoTermBounds.1
  have hrhoTermDisk : rhoTerm < Disk.radius := by
    simpa only [rhoTerm] using hRhoTermBounds.2.1
  have hrhoTerm : 0 < rhoTerm := by simpa only [rhoTerm] using hRhoTermBounds.2.2
  let terminalRadiusCap : ℝ :=
    min (rhoTerm / (8 * ‖d‖)) (rhoTerm / 8)
  have hterminalRadiusCap : 0 < terminalRadiusCap := by
    dsimp [terminalRadiusCap]
    positivity
  let r0 : ℝ := min r0Base (min sourceRadius (sourceEventEps / 2))
  let r1 : ℝ := min r1Base (min terminalRadiusCap (targetEventEps / 2))
  have hr0 : 0 < r0 := by
    dsimp [r0]
    exact lt_min hIsoBase.source_pos
      (lt_min hsourceRadius (half_pos hsourceEventEps))
  have hr1 : 0 < r1 := by
    dsimp [r1]
    exact lt_min hIsoBase.target_pos
      (lt_min hterminalRadiusCap (half_pos htargetEventEps))
  have hr0Base : r0 ≤ r0Base := by exact min_le_left _ _
  have hr1Base : r1 ≤ r1Base := by exact min_le_left _ _
  have hr0Source : r0 ≤ sourceRadius := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hr1Cap : r1 ≤ terminalRadiusCap := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hr0Event : r0 < sourceEventEps := by
    have hle : r0 ≤ sourceEventEps / 2 :=
      (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hr1Event : r1 < targetEventEps := by
    have hle : r1 ≤ targetEventEps / 2 :=
      (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hIso : PolygonalArcEndpointIsolation Aarc r0 r1 := by
    refine
      { source_pos := hr0
        target_pos := hr1
        source_lt_initial_length := hr0Base.trans_lt
          hIsoBase.source_lt_initial_length
        target_lt_terminal_length := hr1Base.trans_lt
          hIsoBase.target_lt_terminal_length
        endpoint_closedBalls_disjoint :=
          hIsoBase.endpoint_closedBalls_disjoint.mono
            (Metric.closedBall_subset_closedBall hr0Base)
            (Metric.closedBall_subset_closedBall hr1Base)
        source_closedBall_carrier_subset_initial_segment := ?_
        target_closedBall_carrier_subset_terminal_segment := ?_ }
    · exact fun ⦃z⦄ hz =>
        hIsoBase.source_closedBall_carrier_subset_initial_segment
          ⟨Metric.closedBall_subset_closedBall hr0Base hz.1, hz.2⟩
    · exact fun ⦃z⦄ hz =>
        hIsoBase.target_closedBall_carrier_subset_terminal_segment
          ⟨Metric.closedBall_subset_closedBall hr1Base hz.1, hz.2⟩
  have event_away_sourceBall (p) (hp : p ∈ XA) :
      Disjoint (Metric.closedBall p (eventRadius p))
        (Metric.closedBall (D.vertexPlacement u) r0) := by
    rw [Set.disjoint_left]
    intro z hzp hzs
    have hzsOpen : z ∈ Metric.ball (D.vertexPlacement u) sourceEventEps :=
      Metric.closedBall_subset_ball hr0Event hzs
    have hzEvent : z ∈ EventClosed :=
      Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hzp⟩
    exact hsourceEventBall hzsOpen hzEvent
  have event_away_targetBall (p) (hp : p ∈ XA) :
      Disjoint (Metric.closedBall p (eventRadius p))
        (Metric.closedBall x r1) := by
    rw [Set.disjoint_left]
    intro z hzp hzt
    have hztOpen : z ∈ Metric.ball x targetEventEps :=
      Metric.closedBall_subset_ball hr1Event hzt
    have hzEvent : z ∈ EventClosed :=
      Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hzp⟩
    exact htargetEventBall hztOpen hzEvent
  have hKcompact : IsCompact H := by
    rw [← hKcarrier, Kclean.carrier_eq]
    apply hBadFinite.isCompact.union
    apply isCompact_iUnion
    intro s
    rw [segment_eq_image' ℝ]
    exact isCompact_Icc.image (by fun_prop)
  have hRbetaCompact : IsCompact Rbeta := by
    rw [← Tail.carrier_eq]
    exact PolygonalArcCarrierCompact Tail.tailArc
  have hBadSubsetH : (Kclean.points : Set
      (EuclideanSpace ℝ (Fin 2))) ⊆ H := by
    intro z hz
    rw [← hKcarrier, Kclean.carrier_eq]
    exact Or.inl hz
  let sourceLocalRadius : ℝ := min sourceRadius (r0 / 2)
  have hsourceLocalRadius : 0 < sourceLocalRadius := by
    dsimp [sourceLocalRadius]
    exact lt_min hsourceRadius (half_pos hr0)
  let EndpointEventOpen : Set (EuclideanSpace ℝ (Fin 2)) :=
    Metric.ball (D.vertexPlacement u) sourceLocalRadius ∪
      Metric.ball x rhoTerm ∪
      ⋃ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ XA},
        Metric.ball p.1 (eventRadius p.1)
  have hEndpointEventOpen : IsOpen EndpointEventOpen := by
    dsimp [EndpointEventOpen]
    exact (Metric.isOpen_ball.union Metric.isOpen_ball).union
      (isOpen_iUnion (fun p => Metric.isOpen_ball))
  let OldCore : Set (EuclideanSpace ℝ (Fin 2)) :=
    B ∪ Bplus ∪ Rbeta ∪ H
  have hOldCoreCompact : IsCompact OldCore := by
    dsimp [OldCore]
    exact ((hBcompact.union hBplusCompact).union hRbetaCompact).union hKcompact
  let FarOld : Set (EuclideanSpace ℝ (Fin 2)) :=
    OldCore \ EndpointEventOpen
  have hFarOldCompact : IsCompact FarOld :=
    hOldCoreCompact.diff hEndpointEventOpen
  have A_nonendpoint_first_relative (z : EuclideanSpace ℝ (Fin 2))
      (hzA : z ∈ A) (hzEnds : z ∉ ({D.vertexPlacement u, x} : Set _)) :
      z ∈ (D.edgeArc firstEdge).relativeInterior := by
    have hzAarc : z ∈ Aarc.carrier := hAarcCarrier.symm ▸ hzA
    have hzAarcRel : z ∈ Aarc.relativeInterior := by
      rw [Aarc.relativeInterior_eq]
      simpa [hAarcSource, hAarcTarget] using And.intro hzAarc hzEnds
    have hzFirstCarrier : z ∈ firstArc.carrier :=
      FirstCut.prefix_carrier_subset hzAarc
    rw [hfirstRelative.symm, firstArc.relativeInterior_eq]
    refine ⟨hzFirstCarrier, ?_⟩
    intro hzFirstEnds
    rcases hzFirstEnds with hzSource | hzTarget
    · exact hzEnds (by simpa [hfirstSource] using Or.inl hzSource)
    · have hzSuffix : z ∈ FirstCut.suffixArc.carrier := by
        rw [hzTarget, ← FirstCut.suffix_target]
        rw [FirstCut.suffixArc.carrier_eq]
        let klast := FirstCut.suffixArc.vertices.length - 2
        have hklast : klast + 1 < FirstCut.suffixArc.vertices.length := by
          dsimp [klast]
          have hlen := FirstCut.suffixArc.length_ge_two
          omega
        refine ⟨klast, hklast, ?_⟩
        have htargetIdx : FirstCut.suffixArc.vertices.length - 1 <
            FirstCut.suffixArc.vertices.length := by omega
        have htargetVertex :
            FirstCut.suffixArc.vertices[FirstCut.suffixArc.vertices.length - 1] =
              FirstCut.suffixArc.target := by
          have hget := FirstCut.suffixArc.target_eq_last
          rw [List.getLast?_eq_getElem?] at hget
          rw [List.getElem?_eq_getElem htargetIdx] at hget
          exact Option.some.inj hget
        have hidx : klast + 1 = FirstCut.suffixArc.vertices.length - 1 := by
          dsimp [klast]
          omega
        simpa [hidx, htargetVertex] using
          (right_mem_segment ℝ FirstCut.suffixArc.vertices[klast]
            FirstCut.suffixArc.vertices[klast + 1])
      have hzBoth : z ∈ FirstCut.prefixArc.carrier ∩
          FirstCut.suffixArc.carrier := ⟨hzAarc, hzSuffix⟩
      have hzx : z = x := by
        have : z ∈ ({x} : Set _) := FirstCut.carrier_intersection ▸ hzBoth
        simpa using this
      exact hzEnds (by simp [hzx])
  have hABplusOnly : A ∩ Bplus ⊆ ({x} : Set _) := by
    intro z hz
    by_cases hzx : z = x
    · simp [hzx]
    have hzNotSource : z ≠ D.vertexPlacement u := by
      intro hzu
      have hzBall := hBplusBall hz.2
      have hzClosed := Metric.ball_subset_closedBall hzBall
      exact Disk.no_vertex_in_closedBall u (by simpa [hzu] using hzClosed)
    have hzEnds : z ∉ ({D.vertexPlacement u, x} : Set _) := by
      simp [hzNotSource, hzx]
    have hzFirst := A_nonendpoint_first_relative z hz.1 hzEnds
    have hzSecondCarrier := hBplusSecondCarrier hz.2
    have hzSecond : z ∈ (D.edgeArc secondEdge).relativeInterior := by
      rw [(D.edgeArc secondEdge).relativeInterior_eq]
      refine ⟨hzSecondCarrier, ?_⟩
      intro hzEdgeEnds
      rcases D.edgeArc_endpoints secondEdge with
        ⟨a, b, _hab, _he, hends⟩
      rcases hends with ⟨hsource, htarget⟩ | ⟨hsource, htarget⟩ <;>
        rcases hzEdgeEnds with hzS | hzT
      · rw [hzS, hsource] at hzFirst
        exact D.no_vertex_in_edge_interior a firstEdge hzFirst
      · rw [hzT, htarget] at hzFirst
        exact D.no_vertex_in_edge_interior b firstEdge hzFirst
      · rw [hzS, hsource] at hzFirst
        exact D.no_vertex_in_edge_interior b firstEdge hzFirst
      · rw [hzT, htarget] at hzFirst
        exact D.no_vertex_in_edge_interior a firstEdge hzFirst
    have hzClosed : z ∈ Metric.closedBall x Disk.radius :=
      Metric.ball_subset_closedBall (hBplusBall hz.2)
    have : z = x := by
      rcases hDiskEdges with hlabels | hlabels
      · exact Disk.pair_meets_only_at_center hzClosed
          (by simpa [hlabels.1] using hzFirst)
          (by simpa [hlabels.2] using hzSecond)
      · exact Disk.pair_meets_only_at_center hzClosed
          (by simpa [hlabels.1] using hzSecond)
          (by simpa [hlabels.2] using hzFirst)
    exact False.elim (hzx this)
  have hFarOldDisjoint : Disjoint FarOld Aarc.carrier := by
    rw [Set.disjoint_left]
    intro z hzFar hzAarc
    have hzA : z ∈ A := hAarcCarrier ▸ hzAarc
    have hzNotOpen := hzFar.2
    rcases hzFar.1 with ((hzB | hzBplus) | hzRbeta) | hzH
    · have hzEnds : z ∈ ({D.vertexPlacement u, x} : Set _) := by
        have : z ∈ A ∩ B := ⟨hzA, hzB⟩
        simpa [hAB] using this
      have hzEnds' : z = D.vertexPlacement u ∨ z = x := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hzEnds
      rcases hzEnds' with hzu | hzx
      · subst z
        exact hzNotOpen
          (Or.inl (Or.inl (Metric.mem_ball_self hsourceLocalRadius)))
      · subst z
        exact hzNotOpen (Or.inl (Or.inr (Metric.mem_ball_self hrhoTerm)))
    · have hzx : z = x := by
        have : z ∈ ({x} : Set _) := hABplusOnly ⟨hzA, hzBplus⟩
        simpa using this
      subst z
      exact hzNotOpen (Or.inl (Or.inr (Metric.mem_ball_self hrhoTerm)))
    · have hzTail : z ∈ Tail.tailArc.carrier := by
        simpa [Tail.carrier_eq] using hzRbeta
      exact Set.disjoint_left.mp hATail hzA hzTail
    · by_cases hzEnds : z ∈ ({D.vertexPlacement u, x} : Set _)
      · have hzEnds' : z = D.vertexPlacement u ∨ z = x := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hzEnds
        rcases hzEnds' with hzu | hzx
        · subst z
          exact hzNotOpen
            (Or.inl (Or.inl (Metric.mem_ball_self hsourceLocalRadius)))
        · subst z
          exact hzNotOpen (Or.inl (Or.inr (Metric.mem_ball_self hrhoTerm)))
      · have hzXA : z ∈ XA := (hXASpec z).2 ⟨⟨hzA, hzEnds⟩, hzH⟩
        apply hzNotOpen
        exact Or.inr (Set.mem_iUnion.mpr
          ⟨⟨z, hzXA⟩, Metric.mem_ball_self (eventPackage_spec z hzXA).1⟩)
  obtain ⟨etaSep, hetaSep, hetaAvoid⟩ :=
    PolygonalArcCompactAvoidanceScale Aarc FarOld hFarOldCompact
      hFarOldDisjoint
  let radiusValues : Finset ℝ := XA.image eventRadius
  have radiusValues_nonempty (hXA : XA.Nonempty) : radiusValues.Nonempty := by
    rcases hXA with ⟨p, hp⟩
    exact ⟨eventRadius p, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
  let eventMin : ℝ := if hXA : XA.Nonempty then
      radiusValues.min' (radiusValues_nonempty hXA) else 1
  have heventMin : 0 < eventMin := by
    dsimp [eventMin]
    split_ifs with hXA
    · have hmem := Finset.min'_mem radiusValues (radiusValues_nonempty hXA)
      rcases Finset.mem_image.mp hmem with ⟨p, hp, heq⟩
      simpa [heq] using (eventPackage_spec p hp).1
    · norm_num
  have heventMin_le (p) (hp : p ∈ XA) : eventMin ≤ eventRadius p := by
    dsimp [eventMin]
    rw [dif_pos ⟨p, hp⟩]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  let eta : ℝ := min etaSep
    (min (eventMin / 4)
      (min ((Disk.radius - rhoTerm) / 4) (sourceLocalRadius / 4)))
  have heta : 0 < eta := by
    dsimp [eta]
    exact lt_min hetaSep
      (lt_min (by positivity) (lt_min (by linarith) (by positivity)))
  have heta_le_sep : eta ≤ etaSep := min_le_left _ _
  have heta_event (p) (hp : p ∈ XA) : eta < eventRadius p := by
    have hle : eta ≤ eventMin / 4 :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hminle := heventMin_le p hp
    have hrpos := (eventPackage_spec p hp).1
    linarith
  have heta_terminal_gap : eta < Disk.radius - rhoTerm := by
    have hle : eta ≤ (Disk.radius - rhoTerm) / 4 :=
      (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have heta_source_gap : eta < sourceLocalRadius := by
    have hle : eta ≤ sourceLocalRadius / 4 :=
      (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  obtain ⟨controlRadii, middleSegments, forbiddenMargins, compatibleTubes,
      vertexLocalPieces, localSideData, S, hConcrete⟩ :=
    OrdinaryAdjacentEdgesConcreteCollarGeometry Aarc eta r0 r1 K0 K1
      heta hIso hK0 hK1
  dsimp only at hConcrete
  rcases hConcrete with
    ⟨hControlSource, hControlTarget, hActualK0, hActualK1,
      hControlAwaySource, hControlAwayTarget, hSourceOmit, hTargetOmit,
      hSourceCone, hTargetCone, hCollarEq, hLeftEq, hRightEq, hCollarNear,
      hSourceCoreEq, hSourceLeftEq, hSourceRightEq,
      hTargetCoreEq, hTargetLeftEq, hTargetRightEq⟩
  let sep := compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
  let actualK0 := compatibleTubes.initialConeBound 0 hfirstAarc
  let actualK1 := compatibleTubes.terminalConeBound jlast hjlast
  have hActualK0Pos : 0 < actualK0 :=
    compatibleTubes.initialConeBound_pos 0 hfirstAarc
  have hActualK1Pos : 0 < actualK1 :=
    compatibleTubes.terminalConeBound_pos jlast hjlast
  have hControlSourcePos : 0 < controlRadii.radius ⟨0, by omega⟩ :=
    controlRadii.radius_pos ⟨0, by omega⟩
  have hControlSourceLe : controlRadii.radius ⟨0, by omega⟩ ≤ sourceRadius :=
    (le_of_lt hControlSource).trans hr0Source
  have hActualK0LeSource : actualK0 ≤ sourceKappa := by
    dsimp [actualK0, K0] at hActualK0 ⊢
    linarith
  obtain ⟨sourceLeftSector, sourceRightSector,
      hSourceLeftSectorEq, hSourceRightSectorEq,
      hSourceLeftOpen, hSourceRightOpen,
      hSourceLeftConvex, hSourceRightConvex,
      hSourceLeftBall, hSourceRightBall,
      hSourceLeftClosure, hSourceRightClosure,
      hSourceNotLeft, hSourceNotRight,
      hSourceLeftAvoid, hSourceRightAvoid⟩ :=
    hsourceSectors (controlRadii.radius ⟨0, by omega⟩) actualK0
      hControlSourcePos hControlSourceLe hActualK0Pos hActualK0LeSource
  let SelectedSide : Set (EuclideanSpace ℝ (Fin 2)) :=
    if positiveSide then S.rightStrip else S.leftStrip
  let StartSector : Set (EuclideanSpace ℝ (Fin 2)) :=
    if positiveSide then sourceRightSector else sourceLeftSector
  let targetIndex : Fin Aarc.vertices.length := ⟨itarget, hitarget⟩
  let Vin : Set (EuclideanSpace ℝ (Fin 2)) :=
    if positiveSide then localSideData.rightSidePiece targetIndex
    else localSideData.leftSidePiece targetIndex
  have hjlast' : jlast < Aarc.vertices.length := by omega
  let cap : ℝ := simultaneousBigonTargetCap Aarc controlRadii.radius targetIndex
    jlast hjlast'
  have hControlTargetPos : 0 < controlRadii.radius targetIndex :=
    controlRadii.radius_pos targetIndex
  have hcapFacts := simultaneousBigonTargetCapFacts Aarc controlRadii.radius
    targetIndex jlast hjlast' x d (by simpa [targetIndex] using htargetVertex)
    rfl hd hControlTargetPos
  have hcap : 0 < cap := by simpa only [cap] using hcapFacts.1
  have hcapNorm : cap * ‖d‖ = controlRadii.radius targetIndex := by
    simpa only [cap] using hcapFacts.2
  have hcapRho : 2 * cap * ‖d‖ < rhoTerm := by
    have hrad : controlRadii.radius targetIndex < r1 := by
      simpa [targetIndex] using hControlTarget
    have hr1rho : r1 ≤ rhoTerm / 8 := by
      exact hr1Cap.trans (by simp [terminalRadiusCap])
    rw [mul_assoc, hcapNorm]
    linarith
  have hkappaSmall : actualK1 * (|mu| + 1) < nu / 4 :=
    simultaneousBigonKappaSmall actualK1 mu nu
      (by simpa [actualK1, K1] using hActualK1) hnu
  let lambda : ℝ := simultaneousBigonLambda cap mu nu rhoTerm
    (‖d‖ + ‖y - x‖)
  have hLambdaFacts := simultaneousBigonVectorLambdaFacts cap mu nu rhoTerm
    d (y - x) hcap hnu hrhoTerm hd (sub_ne_zero.mpr hyx)
  have hlambda : 0 < lambda := by simpa only [lambda] using hLambdaFacts.1
  have hlambda_one : lambda < 1 := by simpa only [lambda] using hLambdaFacts.2.1
  have hsmallCap : 4 * lambda * (1 + |mu| + nu) < cap := by
    simpa only [lambda] using hLambdaFacts.2.2.1
  have hsmallRho : lambda * (‖d‖ + ‖y - x‖) < rhoTerm := by
    simpa only [lambda] using hLambdaFacts.2.2.2
  have first_point_line := simultaneousBigonPointsOnDirectionOfDiskLocal
    (D.edgeArc firstEdge) x Disk.radius i hi d first_disk_local hxOpenFirst
      hlastScale
  have second_point_line := simultaneousBigonPointsOnDirectionOfDiskLocal
    (D.edgeArc secondEdge) x Disk.radius j hj (y - x) second_disk_local
      hxOpenSecond hsecondScale
  let Old : Set (EuclideanSpace ℝ (Fin 2)) := A ∪ B ∪ Bplus ∪ Rbeta ∪ H
  have hAStored : A ⊆ (D.edgeArc firstEdge).carrier := by
    intro z hz
    have hz' := FirstCut.prefix_carrier_subset (hA ▸ hz)
    simpa [hfirstCarrier] using hz'
  have hBStored : B ⊆ (D.edgeArc secondEdge).carrier := by
    intro z hz
    have hz' := SecondCut.prefix_carrier_subset (hB ▸ hz)
    simpa [hsecondCarrier] using hz'
  have hRbetaStored : Rbeta ⊆ (D.edgeArc secondEdge).carrier := by
    intro z hz
    exact (hRbeta ▸ hz).1
  have hHPointEdgeOrVertex := simultaneousBigonHPointEdgeOrVertex G D u
    firstEdge secondEdge x y A B Bplus H hedges hH
  have old_point_edge_or_vertex := simultaneousBigonOldPointEdgeOrVertex G D
    firstEdge secondEdge A B Bplus Rbeta H hAStored hBStored
    hBplusSecondCarrier hRbetaStored hHPointEdgeOrVertex
  have hOldLocal := simultaneousBigonOldLocal G D firstEdge secondEdge x hx Disk
    rhoTerm Old d (y - x) hrhoTermDisk hDiskEdges old_point_edge_or_vertex
    first_point_line second_point_line
  have hSourceLeftPiece := hSourceLeftSectorEq.trans
    ((simultaneousBigonInitialLeftChartEq Aarc (D.vertexPlacement u)
      hfirstAarc hAarcSource (controlRadii.radius ⟨0, by omega⟩)
        actualK0).trans hSourceLeftEq.symm)
  have hSourceRightPiece := hSourceRightSectorEq.trans
    ((simultaneousBigonInitialRightChartEq Aarc (D.vertexPlacement u)
      hfirstAarc hAarcSource (controlRadii.radius ⟨0, by omega⟩)
        actualK0).trans hSourceRightEq.symm)
  have hTargetRightNormalized : localSideData.rightSidePiece targetIndex =
      (fun z : EuclideanSpace ℝ (Fin 2) =>
        x + z 0 • d + z 1 • PlanarRot90 d) ''
        {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < cap ^ 2 ∧
          0 < z 1 ∧ z 1 < actualK1 * z 0} := by
    simpa [targetIndex, itarget, jlast, htargetVertex, d, cap,
      simultaneousBigonTargetCap, actualK1]
      using hTargetRightEq
  have hTargetLeftNormalized : localSideData.leftSidePiece targetIndex =
      (fun z : EuclideanSpace ℝ (Fin 2) =>
        x + z 0 • d + z 1 • PlanarRot90 d) ''
        {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < cap ^ 2 ∧
          -actualK1 * z 0 < z 1 ∧ z 1 < 0} := by
    simpa [targetIndex, itarget, jlast, htargetVertex, d, cap,
      simultaneousBigonTargetCap, actualK1]
      using hTargetLeftEq
  have hVinEq : Vin =
      (fun z : EuclideanSpace ℝ (Fin 2) => x + z 0 • d + z 1 • n) ''
        {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < cap ^ 2 ∧
          0 < z 1 ∧ z 1 < actualK1 * z 0} := by
    by_cases hpos : positiveSide
    · simpa [Vin, n, hpos] using hTargetRightNormalized
    · rw [show Vin = localSideData.leftSidePiece targetIndex by simp [Vin, hpos],
          hTargetLeftNormalized]
      simpa [n, hpos] using simultaneousBigonReflectLeftCone x d cap actualK1
  have hVinOpen : IsOpen Vin := by
    by_cases hpos : positiveSide
    · simpa [Vin, hpos] using localSideData.rightSidePiece_open targetIndex
    · simpa [Vin, hpos] using localSideData.leftSidePiece_open targetIndex
  have hVinSelected : Vin ⊆ SelectedSide := by
    intro z hz
    by_cases hpos : positiveSide
    · simp only [SelectedSide, if_pos hpos]
      rw [hRightEq]
      exact Or.inr (Set.mem_iUnion.mpr ⟨targetIndex, by simpa [Vin, hpos] using hz⟩)
    · simp only [SelectedSide, if_neg hpos]
      rw [hLeftEq]
      exact Or.inr (Set.mem_iUnion.mpr ⟨targetIndex, by simpa [Vin, hpos] using hz⟩)
  have hStartSubset : StartSector ⊆ SelectedSide := by
    intro z hz
    by_cases hpos : positiveSide
    · simp only [SelectedSide, if_pos hpos]
      rw [hRightEq]
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨0, by omega⟩,
        by simpa [StartSector, hpos, hSourceRightPiece] using hz⟩)
    · simp only [SelectedSide, if_neg hpos]
      rw [hLeftEq]
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨0, by omega⟩,
        by simpa [StartSector, hpos, hSourceLeftPiece] using hz⟩)
  have hNear := simultaneousBigonTargetSideNear Aarc eta controlRadii
    middleSegments forbiddenMargins compatibleTubes vertexLocalPieces
    localSideData S x targetIndex jlast hjlast hjlast_target (by
      dsimp [targetIndex, itarget]
      omega) htargetVertex positiveSide hLeftEq hRightEq
  have hyOld : y ∈ Old := by
    exact Or.inl (Or.inl (Or.inr hyBplus))
  have hyRho : y ∈ Metric.ball x rhoTerm := by
    simpa [Metric.mem_ball, dist_comm] using hyRhoTerm
  obtain ⟨k, hk, Q, Side, Bridge, terminalGate, sideSource,
      quadrantGate, h, predecessor, approach, lastGate,
      hQconvex, hQcompact, hxQ, hyQ, hxnotQ,
      hSideOpen, hSideConvex, hSideCompact,
      hBridgeOpen, hBridgeConvex, hBridgeCompact,
      hterminalSideClosure, hterminalNotSide,
      hsourceSideClosure, hsourceNotSide,
      hsourceBridgeClosure, hsourceNotBridge,
      hquadrantBridgeClosure, hquadrantNotBridge,
      hterminalNeSource, hsourceNeQuadrant,
      hterminalSourceSegment, hterminalSourceOpen,
      hsourceQuadrantSegment, hsourceQuadrantOpen,
      hquadrantQ, hquadrantNe,
      hsourceQuadrantQ, hSideBridgeClosure, hSideQClosure,
      hBridgeQClosure, hquadrantYSegment, hQBall, hQOld, hQBad,
      hSideBall, hBridgeBall, hCellsOld,
      hVinOpen', hVinConvex, hhVin, hhNeTerminal, hVinSelected',
      hxVinClosure, hNear', hVinBall, hVinQ, hVinOld,
      hterminalVinClosure, hterminalNotVin,
      hhTerminalSegment, hhTerminalOpen,
      hVinSideClosure, hVinBridgeClosure, hVinSide,
      hPredecessorSubset, hApproachSubset,
      hPredecessorTarget, hApproachSource, hPredecessorApproach,
      hApproachTarget, hApproachTerminal, hPredecessorTerminal,
      hSupporting, gateA, gateB, hgateA, hgateB, hgateEq,
      hterminalGateFormula⟩ :=
    OrdinaryAdjacentEdgesTerminalCollarCompatibility
      x y d n lambda mu nu actualK1 cap rhoTerm
      SelectedSide Vin Old (∅ : Finset (EuclideanSpace ℝ (Fin 2)))
      hlambda hlambda_one hnu hActualK1Pos hcap hkappaSmall hrhoTerm hd
      hdn hnd hdd hnn hyDecomp hlinear hVinEq hVinOpen hVinSelected hNear
      hyRho hsmallCap hcapRho hsmallRho hOldLocal hyOld (by simp)
  have left_half_convex := simultaneousBigonLeftHalfConvex Aarc controlRadii
    middleSegments forbiddenMargins sep
  have right_half_convex := simultaneousBigonRightHalfConvex Aarc controlRadii
    middleSegments forbiddenMargins sep
  have event_selected_slice (p : EuclideanSpace ℝ (Fin 2)) (hp : p ∈ XA) :=
    simultaneousBigonOneEventSelectedSlice Aarc eta controlRadii middleSegments
      forbiddenMargins compatibleTubes vertexLocalPieces localSideData S p
      (eventIndex p) (eventIndex_spec p hp).choose (eventRadius p)
      (eventClearance p) (eventForbidden p) positiveSide heta (heta_event p hp)
      (eventPackage_spec p hp).2.1 (eventClearance_spec p hp).2
      (fun idx => by
        dsimp only [eventForbidden]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
          (by simpa using List.getElem_mem idx.2))))))
      (fun m hm hne z hz => by
        dsimp only [eventForbidden]
        exact Or.inr (by
          simp only [otherSegments, simultaneousBigonOtherSegments,
            Set.mem_iUnion]
          let fm : Fin (Aarc.vertices.length - 1) := ⟨m, by omega⟩
          refine ⟨fm, ?_⟩
          simpa only [fm, hne, ↓reduceIte]))
      hLeftEq hRightEq
  have hEventLocal : ∀ p : EuclideanSpace ℝ (Fin 2), p ∈ XA →
      0 < eventRadius p ∧
        Convex ℝ (SelectedSide ∩ Metric.ball p (eventRadius p)) ∧
          ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
            s ∈ Kclean.segments ∧ p ∈ openSegment ℝ s.1 s.2 ∧
              Metric.ball p (eventRadius p) ∩ H =
                Metric.ball p (eventRadius p) ∩ segment ℝ s.1 s.2 ∧
              Metric.ball p (eventRadius p) ∩ Rbeta = ∅ := by
    intro p hp
    refine ⟨(eventPackage_spec p hp).1, ?_, eventSegment p,
      (eventPackage_spec p hp).2.2.1,
      (eventPackage_spec p hp).2.2.2.1,
      (eventPackage_spec p hp).2.2.2.2.1,
      (eventPackage_spec p hp).2.2.2.2.2⟩
    rw [event_selected_slice p hp]
    by_cases hpos : positiveSide
    · simp only [if_pos hpos]
      exact (right_half_convex (eventIndex p) (eventIndex_spec p hp).choose).inter
        (convex_ball p (eventRadius p))
    · simp only [if_neg hpos]
      exact (left_half_convex (eventIndex p) (eventIndex_spec p hp).choose).inter
        (convex_ball p (eventRadius p))
  have hEventClean := simultaneousBigonEventClean Aarc Kclean.points
    Kclean.segments XA eventIndex (fun p hp => (event_data p hp).1) (fun p hp => by
      obtain ⟨hm, hpOpen, s, hs, hps, hnonparallel, hunique, _hlocal⟩ :=
        eventIndex_spec p hp
      exact ⟨hm, hpOpen, s, hs, hps, hnonparallel, hunique⟩)
  have hStartOpen := simultaneousBigonIteIsOpen positiveSide
    hSourceLeftOpen hSourceRightOpen
  have hStartConvex := simultaneousBigonIteConvex positiveSide
    hSourceLeftConvex hSourceRightConvex
  have hStartBall := simultaneousBigonIteSubset positiveSide
    hSourceLeftBall hSourceRightBall
  have hSourceStartClosure := simultaneousBigonMemClosureIte positiveSide
    hSourceLeftClosure hSourceRightClosure
  have hSourceNotStart := simultaneousBigonNotMemIte positiveSide
    hSourceNotLeft hSourceNotRight
  have hStartAvoidRaySet := simultaneousBigonIteIntersectionEmpty positiveSide
    hSourceLeftAvoid hSourceRightAvoid
  have hStartAvoidAxis := simultaneousBigonStartAvoidAxis
    (D.vertexPlacement u) d0 hd0 positiveSide sourceLeftSector sourceRightSector
    (fun q hq => by
      rw [hSourceLeftSectorEq] at hq
      rcases hq with ⟨z, hz, hqFormula⟩
      exact ⟨z, hz.2.2.1, hqFormula.symm⟩)
    (fun q hq => by
      rw [hSourceRightSectorEq] at hq
      rcases hq with ⟨z, hz, hqFormula⟩
      exact ⟨z, hz.2.2.2, hqFormula.symm⟩)
  have hStartAvoidFirstEdge :
      StartSector ∩ (D.edgeArc firstEdge).carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqSourceRadius : q ∈ Metric.ball (D.vertexPlacement u) sourceRadius :=
      Metric.ball_subset_ball hControlSourceLe (hStartBall hq.1)
    have hqAxis := hsourceEdgeCover ⟨hqSourceRadius, hq.2⟩
    exact Set.eq_empty_iff_forall_notMem.mp hStartAvoidAxis q ⟨hq.1, hqAxis⟩
  have hStartAvoidWithoutFirst :
      StartSector ∩ OrdinaryDrawingImageWithoutEdge G D firstEdge = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqSourceRadius : q ∈ Metric.ball (D.vertexPlacement u) sourceRadius :=
      Metric.ball_subset_ball hControlSourceLe (hStartBall hq.1)
    have hqRays := hsourceCover ⟨hqSourceRadius, hq.2⟩
    exact Set.eq_empty_iff_forall_notMem.mp hStartAvoidRaySet q ⟨hq.1, hqRays⟩
  have hStartAvoidOld := simultaneousBigonStartAvoidOld G D firstEdge StartSector
    Old (Kclean.points : Set (EuclideanSpace ℝ (Fin 2)))
    (fun q hq => Or.inr (hBadSubsetH hq)) old_point_edge_or_vertex
    hStartAvoidFirstEdge hStartAvoidWithoutFirst
  have hStartClosureBall := simultaneousBigonClosureSubsetClosedBall
    StartSector (D.vertexPlacement u) (controlRadii.radius ⟨0, by omega⟩) r0
      hStartBall hControlSource.le
  have hEventAvoidStart : ∀ p : EuclideanSpace ℝ (Fin 2), p ∈ XA →
      Disjoint (Metric.closedBall p (eventRadius p)) (closure StartSector) := by
    intro p hp
    exact (event_away_sourceBall p hp).mono_right hStartClosureBall
  have hSelectedChoice :
      SelectedSide = S.leftStrip ∨ SelectedSide = S.rightStrip :=
    simultaneousBigonIteEqLeftOrRight positiveSide S.leftStrip S.rightStrip
  have hSourceSelectedClosure :
      D.vertexPlacement u ∈ closure SelectedSide := by
    exact closure_mono hStartSubset hSourceStartClosure
  have hSelectedCollar : SelectedSide ⊆ S.collar :=
    simultaneousBigonIteSubset positiveSide
      S.left_subset_collar S.right_subset_collar
  have hSelectedAvoidFar := simultaneousBigonSelectedAvoidFar Aarc SelectedSide
    S.collar FarOld eta etaSep hSelectedCollar hCollarNear heta_le_sep hetaAvoid
  have hVinVertexCollar := simultaneousBigonIteSubset positiveSide
    (localSideData.leftSidePiece_subset_vertexCollar targetIndex)
    (localSideData.rightSidePiece_subset_vertexCollar targetIndex)
  have hVinControlBall := simultaneousBigonSidePieceControlBall Aarc controlRadii
    middleSegments forbiddenMargins compatibleTubes vertexLocalPieces
      localSideData Vin targetIndex x htargetVertex hVinVertexCollar
  have hVinClosureTargetBall := simultaneousBigonClosureSubsetClosedBall
    Vin x (controlRadii.radius targetIndex) r1
      hVinControlBall hControlTarget.le
  have hEventAvoidVin : ∀ p : EuclideanSpace ℝ (Fin 2), p ∈ XA →
      Disjoint (Metric.closedBall p (eventRadius p)) (closure Vin) := by
    intro p hp
    exact (event_away_targetBall p hp).mono_right hVinClosureTargetBall
  obtain ⟨FirstBranch, hFirstBranchIndices⟩ :=
    simultaneousBigonFirstBranchWithIndices G D firstEdge secondEdge x hx Disk
      i hi hxOpenFirst hDiskEdges
  have hFirstEndpointsOutside := simultaneousBigonSegmentEndpointsOutsideClosedBall
    (D.edgeArc firstEdge) x Disk.radius i hi hxOpenFirst FirstBranch
      hFirstBranchIndices
  have hFirstLeftOutside := hFirstEndpointsOutside.1
  have hFirstRightOutside := hFirstEndpointsOutside.2
  have hNonterminalVertexOutsideDisk :=
    simultaneousBigonNonterminalVertexOutsideDiskOfTransfer Aarc
      (D.edgeArc firstEdge) x
      Disk.radius targetIndex i hi hprefixCarrierSubset
      first_disk_local hFirstLeftOutside
      hFirstRightOutside htargetVertex hFirstPrefixTransfer
  have hTerminalTubeOnly := simultaneousBigonTerminalTubeOnly
    Aarc (D.edgeArc firstEdge) controlRadii middleSegments forbiddenMargins sep
      x rhoTerm Disk.radius targetIndex jlast i hi
      rfl rfl htargetVertex heta_terminal_gap
      hprefixCarrierSubset
      first_disk_local hFirstLeftOutside hFirstRightOutside
      hNonterminalVertexOutsideDisk
      hFirstPrefixTransfer
      d hlastScale first_point_line hDiskRadius
  have hSelectedTerminalCone
      (q : EuclideanSpace ℝ (Fin 2))
      (hq : q ∈ SelectedSide ∩ Metric.closedBall x rhoTerm) :
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ b < actualK1 * a ∧
        q = x + a • d + b • n := by
    have vertex_index_target := simultaneousBigonVertexIndexTarget Aarc
      controlRadii middleSegments forbiddenMargins compatibleTubes
      vertexLocalPieces localSideData x rhoTerm Disk.radius targetIndex
      heta_terminal_gap hNonterminalVertexOutsideDisk q hq.2
    have target_piece_coordinates
        (hqVin : q ∈ Vin) :
        ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ b < actualK1 * a ∧
          q = x + a • d + b • n := by
      rw [hVinEq] at hqVin
      rcases hqVin with ⟨z, hz, rfl⟩
      exact ⟨z 0, z 1, hz.1, hz.2.2.1, hz.2.2.2, rfl⟩
    by_cases hpos : positiveSide
    · have hqRight : q ∈ S.rightStrip := by
        simpa only [SelectedSide, if_pos hpos] using hq.1
      rw [hRightEq] at hqRight
      rcases hqRight with hqHalf | hqPiece
      · rcases Set.mem_iUnion.mp hqHalf with ⟨m, hqHalf⟩
        rcases Set.mem_iUnion.mp hqHalf with ⟨hm, hqHalf⟩
        have hmLast := hTerminalTubeOnly q hq.2 m hm
          (sep.rightHalf_subset_tube m hm hqHalf)
        subst m
        exact simultaneousBigonTerminalRightHalfCoordinates Aarc controlRadii
          middleSegments forbiddenMargins compatibleTubes x d n actualK1
          jlast hjlast hActualK1Pos rfl hlastVertex rfl (by simp [n, hpos]) q hqHalf
        /-
        rw [sep.rightHalf_eq] at hqHalf
        rcases hqHalf with ⟨t, ht, s, hs, hqFormula⟩
        let a := 1 - t
        let b := -s
        have ha : 0 < a := by
          dsimp [a]
          linarith [ht.2, sep.upperParam_lt_one jlast hjlast]
        have hb : 0 < b := by
          dsimp [b]
          exact neg_pos.mpr hs.2
        have hbBound : b < actualK1 * a := by
          have hw := compatibleTubes.terminal_halfWidth_lt_cone_mul_one_sub_upperParam
            jlast hjlast
          have hone : 1 - sep.upperParam jlast hjlast < 1 - t := by linarith [ht.2]
          dsimp [a, b]
          calc
            -s < sep.halfWidth jlast hjlast := by linarith [hs.1]
            _ < actualK1 * (1 - sep.upperParam jlast hjlast) := hw
            _ < actualK1 * (1 - t) := mul_lt_mul_of_pos_left hone hActualK1Pos
        refine ⟨a, b, ha, hb, hbBound, ?_⟩
        have hnormal : sep.normal jlast hjlast =
            PlanarRot90 (Aarc.vertices[jlast + 1] - Aarc.vertices[jlast]) := by
          simpa only [PlanarRot90] using
            compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn
              jlast hjlast
        have hdiff : Aarc.vertices[jlast + 1] - Aarc.vertices[jlast] = -d := by
          rw [hlastVertex]
          dsimp [d]
          module
        rw [hnormal, hdiff, planarRot90_neg] at hqFormula
        simp only [AffineMap.lineMap_apply_module, hlastVertex] at hqFormula
        rw [hqFormula]
        dsimp [a, b, d, n]
        rw [if_pos hpos]
        module
        -/
      · rcases Set.mem_iUnion.mp hqPiece with ⟨idx, hqPiece⟩
        have hidx := vertex_index_target idx
          (localSideData.rightSidePiece_subset_vertexCollar idx hqPiece)
        subst idx
        apply target_piece_coordinates
        simpa [Vin, hpos] using hqPiece
    · have hqLeft : q ∈ S.leftStrip := by
        simpa only [SelectedSide, if_neg hpos] using hq.1
      rw [hLeftEq] at hqLeft
      rcases hqLeft with hqHalf | hqPiece
      · rcases Set.mem_iUnion.mp hqHalf with ⟨m, hqHalf⟩
        rcases Set.mem_iUnion.mp hqHalf with ⟨hm, hqHalf⟩
        have hmLast := hTerminalTubeOnly q hq.2 m hm
          (sep.leftHalf_subset_tube m hm hqHalf)
        subst m
        exact simultaneousBigonTerminalLeftHalfCoordinates Aarc controlRadii
          middleSegments forbiddenMargins compatibleTubes x d n actualK1
          jlast hjlast hActualK1Pos rfl hlastVertex rfl (by simp [n, hpos]) q hqHalf
        /-
        rw [sep.leftHalf_eq] at hqHalf
        rcases hqHalf with ⟨t, ht, s, hs, hqFormula⟩
        let a := 1 - t
        let b := s
        have ha : 0 < a := by
          dsimp [a]
          linarith [ht.2, sep.upperParam_lt_one jlast hjlast]
        have hb : 0 < b := by exact hs.1
        have hbBound : b < actualK1 * a := by
          have hw := compatibleTubes.terminal_halfWidth_lt_cone_mul_one_sub_upperParam
            jlast hjlast
          have hone : 1 - sep.upperParam jlast hjlast < 1 - t := by linarith [ht.2]
          dsimp [a, b]
          calc
            s < sep.halfWidth jlast hjlast := hs.2
            _ < actualK1 * (1 - sep.upperParam jlast hjlast) := hw
            _ < actualK1 * (1 - t) := mul_lt_mul_of_pos_left hone hActualK1Pos
        refine ⟨a, b, ha, hb, hbBound, ?_⟩
        have hnormal : sep.normal jlast hjlast =
            PlanarRot90 (Aarc.vertices[jlast + 1] - Aarc.vertices[jlast]) := by
          simpa only [PlanarRot90] using
            compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn
              jlast hjlast
        have hdiff : Aarc.vertices[jlast + 1] - Aarc.vertices[jlast] = -d := by
          rw [hlastVertex]
          dsimp [d]
          module
        rw [hnormal, hdiff, planarRot90_neg] at hqFormula
        simp only [AffineMap.lineMap_apply_module, hlastVertex] at hqFormula
        rw [hqFormula]
        dsimp [a, b, d, n]
        rw [if_neg hpos]
        module
        -/
      · rcases Set.mem_iUnion.mp hqPiece with ⟨idx, hqPiece⟩
        have hidx := vertex_index_target idx
          (localSideData.leftSidePiece_subset_vertexCollar idx hqPiece)
        subst idx
        apply target_piece_coordinates
        simpa [Vin, hpos] using hqPiece
  have hSelectedPositive := simultaneousBigonConePositive SelectedSide x d n
    rhoTerm actualK1 hnormd hdd hdn hnd hnn hSelectedTerminalCone
  have hSelectedAvoidTerminalClosures := simultaneousBigonConeAvoidSupporting
    SelectedSide (closure Side ∪ closure Bridge ∪ closure Q) x d n rhoTerm
      actualK1 hSelectedPositive hSupporting
  have hSelectedTerminalAvoidOld := simultaneousBigonSelectedTerminalAvoidOld
    SelectedSide Old x d n (y - x) rhoTerm actualK1 mu nu hnormd hnu
      hActualK1Pos hkappaSmall hdd hdn hnd hnn hyDecomp
      hSelectedTerminalCone hOldLocal
  have hsourceLocalLe : sourceLocalRadius ≤ sourceRadius := by
    exact min_le_left _ _
  obtain ⟨wideSourceLeft, wideSourceRight,
      hWideSourceLeftEq, hWideSourceRightEq,
      hWideSourceLeftOpen, hWideSourceRightOpen,
      hWideSourceLeftConvex, hWideSourceRightConvex,
      hWideSourceLeftBall, hWideSourceRightBall,
      hWideSourceLeftClosure, hWideSourceRightClosure,
      hWideSourceNotLeft, hWideSourceNotRight,
      hWideSourceLeftAvoid, hWideSourceRightAvoid⟩ :=
    hsourceSectors sourceLocalRadius actualK0 hsourceLocalRadius
      hsourceLocalLe hActualK0Pos hActualK0LeSource
  let WideSourceSector : Set (EuclideanSpace ℝ (Fin 2)) :=
    if positiveSide then wideSourceRight else wideSourceLeft
  have hNonSourceVertexOutsideR0 := simultaneousBigonNonSourceVertexOutside
    Aarc (D.vertexPlacement u) r0 hfirstAarc (fun z hz => by
      have hz' := hIso.source_closedBall_carrier_subset_initial_segment
        ⟨by simpa [hAarcSource] using hz.1, hz.2⟩
      simpa [hsource0] using hz') (by
        intro hz
        have hdistNext : dist Aarc.source Aarc.vertices[1] ≤ r0 := by
          simpa [hAarcSource, dist_comm] using hz
        exact (not_lt_of_ge hdistNext) hIso.source_lt_initial_length)
  have hSourceTubeOnly := simultaneousBigonSourceTubeOnly Aarc controlRadii
    middleSegments forbiddenMargins sep (D.vertexPlacement u) sourceLocalRadius r0
      hfirstAarc (hsource0.trans hAarcSource) (min_le_right _ _)
      heta_source_gap (fun z hz => by
        have hz' := hIso.source_closedBall_carrier_subset_initial_segment
          ⟨by simpa [hAarcSource] using hz.1, hz.2⟩
        simpa [hsource0] using hz')
  have source_coords_inside_cap := simultaneousBigonSourceCoordsInsideCap
    (D.vertexPlacement u) d0 sourceLocalRadius hd0
  have hSelectedSourceWide :
      SelectedSide ∩ Metric.ball (D.vertexPlacement u) sourceLocalRadius ⊆
        WideSourceSector := by
    apply simultaneousBigonSelectedSourceWideFromPieces Aarc controlRadii
      middleSegments forbiddenMargins compatibleTubes vertexLocalPieces
      localSideData S (Metric.ball (D.vertexPlacement u) sourceLocalRadius)
      wideSourceLeft wideSourceRight SelectedSide WideSourceSector positiveSide
      hfirstAarc rfl rfl hLeftEq hRightEq
    · exact hSourceTubeOnly
    · intro q hqBall idx hqPiece
      let sourceIndex : Fin Aarc.vertices.length := ⟨0, by omega⟩
      have hetaDisk : eta < r0 - sourceLocalRadius := by
        have hsourceHalf : sourceLocalRadius ≤ r0 / 2 := min_le_right _ _
        linarith
      have hidx := simultaneousBigonVertexIndexTarget Aarc controlRadii
        middleSegments forbiddenMargins compatibleTubes vertexLocalPieces
        localSideData (D.vertexPlacement u) sourceLocalRadius r0 sourceIndex
        hetaDisk (by
          intro k hk
          exact hNonSourceVertexOutsideR0 k (by
            intro hk0
            apply hk
            apply Fin.ext
            simpa [sourceIndex] using hk0)) q
        (Metric.ball_subset_closedBall hqBall) idx hqPiece
      exact congrArg Fin.val hidx
    · intro q hqBall hqHalf
      rw [hWideSourceRightEq]
      exact simultaneousBigonSourceRightHalfWide Aarc controlRadii
        middleSegments forbiddenMargins compatibleTubes (D.vertexPlacement u)
        d0 sourceLocalRadius actualK0 hfirstAarc (hsource0.trans hAarcSource)
        (by simp [d0, hAarcSource]) hActualK0Pos rfl source_coords_inside_cap
        q hqBall hqHalf
    · intro q hqBall hqHalf
      rw [hWideSourceLeftEq]
      exact simultaneousBigonSourceLeftHalfWide Aarc controlRadii
        middleSegments forbiddenMargins compatibleTubes (D.vertexPlacement u)
        d0 sourceLocalRadius actualK0 hfirstAarc (hsource0.trans hAarcSource)
        (by simp [d0, hAarcSource]) hActualK0Pos rfl source_coords_inside_cap
        q hqBall hqHalf
    · intro q hqBall hqPiece
      rw [hWideSourceRightEq]
      rw [← hSourceRightPiece, hSourceRightSectorEq] at hqPiece
      rcases hqPiece with ⟨z, hz, hqFormula⟩
      have hqChart : q =
          D.vertexPlacement u + z 0 • d0 + z 1 • PlanarRot90 d0 := by
        simpa [hsource0, hAarcSource, d0] using hqFormula.symm
      exact ⟨z, ⟨hz.1, source_coords_inside_cap q (z 0) (z 1)
        hqChart hqBall, hz.2.2.1, hz.2.2.2⟩, hqChart.symm⟩
    · intro q hqBall hqPiece
      rw [hWideSourceLeftEq]
      rw [← hSourceLeftPiece, hSourceLeftSectorEq] at hqPiece
      rcases hqPiece with ⟨z, hz, hqFormula⟩
      have hqChart : q =
          D.vertexPlacement u + z 0 • d0 + z 1 • PlanarRot90 d0 := by
        simpa [hsource0, hAarcSource, d0] using hqFormula.symm
      exact ⟨z, ⟨hz.1, source_coords_inside_cap q (z 0) (z 1)
        hqChart hqBall, hz.2.2.1, hz.2.2.2⟩, hqChart.symm⟩
  have hWideSourceAvoidRays :
      WideSourceSector ∩
        (({D.vertexPlacement u} : Set (EuclideanSpace ℝ (Fin 2))) ∪
          ⋃ v : {v : EuclideanSpace ℝ (Fin 2) // v ∈ sourceDirections},
            {q | ∃ c : ℝ, 0 ≤ c ∧
              q = D.vertexPlacement u + c • v.1}) = ∅ := by
    by_cases hpos : positiveSide
    · simpa [WideSourceSector, hpos] using hWideSourceRightAvoid
    · simpa [WideSourceSector, hpos] using hWideSourceLeftAvoid
  have hWideSourceAvoidAxis :
      WideSourceSector ∩
        {q | ∃ c : ℝ, 0 ≤ c ∧ q = D.vertexPlacement u + c • d0} = ∅ := by
    exact simultaneousBigonWideSourceAvoidAxis (D.vertexPlacement u) d0
      sourceLocalRadius actualK0 hd0 positiveSide wideSourceLeft wideSourceRight
      WideSourceSector rfl hWideSourceRightEq hWideSourceLeftEq
  have hSelectedSourceAvoidOld :
      (SelectedSide ∩ Metric.ball (D.vertexPlacement u) sourceLocalRadius) ∩
        Old = ∅ := by
    let Small := SelectedSide ∩
      Metric.ball (D.vertexPlacement u) sourceLocalRadius
    have hSmallSourceRadius : Small ⊆
        Metric.ball (D.vertexPlacement u) sourceRadius := by
      intro q hq
      exact Metric.ball_subset_ball hsourceLocalLe hq.2
    have hSmallFirst : Small ∩ (D.edgeArc firstEdge).carrier = ∅ :=
      simultaneousBigonIntersectionEmptyOfLocalCover Small WideSourceSector
        (Metric.ball (D.vertexPlacement u) sourceRadius)
        (D.edgeArc firstEdge).carrier
        {q | ∃ c : ℝ, 0 ≤ c ∧ q = D.vertexPlacement u + c • d0}
        hSelectedSourceWide hSmallSourceRadius hsourceEdgeCover
        hWideSourceAvoidAxis
    have hSmallWithout : Small ∩
        OrdinaryDrawingImageWithoutEdge G D firstEdge = ∅ :=
      simultaneousBigonIntersectionEmptyOfLocalCover Small WideSourceSector
        (Metric.ball (D.vertexPlacement u) sourceRadius)
        (OrdinaryDrawingImageWithoutEdge G D firstEdge)
        (({D.vertexPlacement u} : Set (EuclideanSpace ℝ (Fin 2))) ∪
          ⋃ v : {v : EuclideanSpace ℝ (Fin 2) // v ∈ sourceDirections},
            {q | ∃ c : ℝ, 0 ≤ c ∧ q = D.vertexPlacement u + c • v.1})
        hSelectedSourceWide hSmallSourceRadius hsourceCover hWideSourceAvoidRays
    exact simultaneousBigonAvoidOld G D firstEdge Small Old
      old_point_edge_or_vertex hSmallFirst hSmallWithout
  have hOldCoreSubsetOld : OldCore ⊆ Old := by
    change B ∪ Bplus ∪ Rbeta ∪ H ⊆ A ∪ B ∪ Bplus ∪ Rbeta ∪ H
    exact simultaneousBigonOldCoreSubsetOld A B Bplus Rbeta H
  have hSelectedOldCoreLocalization :
      SelectedSide ∩ OldCore ⊆
        ⋃ p ∈ (XA : Set (EuclideanSpace ℝ (Fin 2))),
          Metric.ball p (eventRadius p) := by
    apply simultaneousBigonSelectedOldCoreLocalization SelectedSide OldCore Old
      (Metric.ball (D.vertexPlacement u) sourceLocalRadius)
      (Metric.ball x rhoTerm) (Metric.closedBall x rhoTerm)
      (⋃ p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ XA},
        Metric.ball p.1 (eventRadius p.1))
      (⋃ p ∈ (XA : Set (EuclideanSpace ℝ (Fin 2))),
        Metric.ball p (eventRadius p)) EndpointEventOpen FarOld
    · rfl
    · rfl
    · exact hOldCoreSubsetOld
    · exact Metric.ball_subset_closedBall
    · intro q hq
      rcases Set.mem_iUnion.mp hq with ⟨p, hqp⟩
      exact Set.mem_iUnion.mpr ⟨p.1, Set.mem_iUnion.mpr ⟨p.2, hqp⟩⟩
    · exact hSelectedSourceAvoidOld
    · exact hSelectedTerminalAvoidOld
    · exact hSelectedAvoidFar
  have hSelectedMeetsHOnlyInEvents :
      SelectedSide ∩ H ⊆
        ⋃ p ∈ (XA : Set (EuclideanSpace ℝ (Fin 2))),
          Metric.ball p (eventRadius p) := by
    apply simultaneousBigonSelectedMeetsSubset SelectedSide H OldCore
      (⋃ p ∈ (XA : Set (EuclideanSpace ℝ (Fin 2))),
        Metric.ball p (eventRadius p))
    · intro q hq
      change q ∈ B ∪ Bplus ∪ Rbeta ∪ H
      exact Or.inr hq
    · exact hSelectedOldCoreLocalization
  have hSelectedAvoidsOld :
      SelectedSide ∩ (B ∪ Bplus ∪ Rbeta ∪
        (Kclean.points : Set (EuclideanSpace ℝ (Fin 2)))) = ∅ := by
    exact simultaneousBigonSelectedAvoidsEventForbidden XA eventRadius SelectedSide
      B Bplus Rbeta H (Kclean.points : Set _) OldCore eventForbidden rfl
      hBadSubsetH hSelectedOldCoreLocalization hBSubsetEventForbidden
      hBplusSubsetEventForbidden hBadSubsetEventForbidden
      event_closedBall_avoids_forbidden eventBallAvoidsRbeta
  have hBadSubsetOld :
      (Kclean.points : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Old := by
    intro q hq
    exact Or.inr (hBadSubsetH hq)
  have hOldUnionBad :
      Old ∪ (Kclean.points : Set (EuclideanSpace ℝ (Fin 2))) = Old :=
    Set.union_eq_left.mpr hBadSubsetOld
  have hCellsAvoidActual :
      (closure Side ∪ closure Bridge) ∩
        (Old ∪ (Kclean.points : Set (EuclideanSpace ℝ (Fin 2)))) = ∅ := by
    rw [hOldUnionBad]
    simpa using hCellsOld
  have hVinAvoidActual :
      Vin ∩ (Old ∪ (Kclean.points : Set (EuclideanSpace ℝ (Fin 2)))) = ∅ := by
    rw [hOldUnionBad]
    simpa using hVinOld
  have hQSubsetDelta : Q ⊆ Metric.ball x Disk.radius := by
    intro q hq
    have hqClosed : q ∈ closure Q := subset_closure hq
    exact Metric.closedBall_subset_ball hrhoTermDisk (hQBall hqClosed)
  have hSideSubsetDelta : Side ⊆ Metric.ball x Disk.radius := by
    intro q hq
    exact Metric.ball_subset_ball hrhoTermDisk.le
      (hSideBall (subset_closure hq))
  have hBridgeSubsetDelta : Bridge ⊆ Metric.ball x Disk.radius := by
    intro q hq
    exact Metric.ball_subset_ball hrhoTermDisk.le
      (hBridgeBall (subset_closure hq))
  have hTerminalGateDelta : terminalGate ∈ Metric.ball x Disk.radius :=
    Metric.ball_subset_ball hrhoTermDisk.le (hSideBall hterminalSideClosure)
  have hSideSourceDelta : sideSource ∈ Metric.ball x Disk.radius :=
    Metric.ball_subset_ball hrhoTermDisk.le (hSideBall hsourceSideClosure)
  have hTerminalGateNotQ : terminalGate ∉ Q := by
    intro hgateQ
    have hgateInter : terminalGate ∈ closure Side ∩ closure Q :=
      ⟨hterminalSideClosure, subset_closure hgateQ⟩
    rw [hSideQClosure] at hgateInter
    exact hgateInter
  have hSideAvoidActual :
      (Side ∪ ({terminalGate, sideSource} : Set _)) ∩
        (Old ∪ (Kclean.points : Set (EuclideanSpace ℝ (Fin 2)))) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqClosure : q ∈ closure Side ∪ closure Bridge := by
      rcases hq.1 with hqSide | hqGates
      · exact Or.inl (subset_closure hqSide)
      · rcases hqGates with hqGate | hqSource
        · exact Or.inl (hqGate ▸ hterminalSideClosure)
        · exact Or.inl (hqSource ▸ hsourceSideClosure)
    exact Set.eq_empty_iff_forall_notMem.mp hCellsAvoidActual q
      ⟨hqClosure, hq.2⟩
  have hBridgeAvoidActual :
      (Bridge ∪ ({sideSource, quadrantGate} : Set _)) ∩
        (Old ∪ (Kclean.points : Set (EuclideanSpace ℝ (Fin 2)))) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqClosure : q ∈ closure Side ∪ closure Bridge := by
      rcases hq.1 with hqBridge | hqGates
      · exact Or.inr (subset_closure hqBridge)
      · rcases hqGates with hqSource | hqGate
        · exact Or.inr (hqSource ▸ hsourceBridgeClosure)
        · exact Or.inr (hqGate ▸ hquadrantBridgeClosure)
    exact Set.eq_empty_iff_forall_notMem.mp hCellsAvoidActual q
      ⟨hqClosure, hq.2⟩
  have hQuadrantOpenAvoidActual :
      openSegment ℝ quadrantGate y ∩
        (Old ∪ (Kclean.points : Set (EuclideanSpace ℝ (Fin 2)))) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqQ : q ∈ Q := hquadrantYSegment
      (openSegment_subset_segment ℝ _ _ hq.1)
    have hqOld : q ∉ Old := by
      intro hqOld
      have hqy : q ∈ ({y} : Set _) := by
        rw [← hQOld]
        exact ⟨hqQ, hqOld⟩
      have : q = y := by simpa using hqy
      exact hquadrantNe
        ((right_mem_openSegment_iff (𝕜 := ℝ)).1 (this ▸ hq.1))
    exact hqOld (hOldUnionBad ▸ hq.2)
  have hhAvoidActual :
      h ∉ A ∪ B ∪ Bplus ∪ Rbeta ∪ H ∪
        (Kclean.points : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro hh
    exact Set.eq_empty_iff_forall_notMem.mp hVinAvoidActual h
      ⟨hhVin, by simpa [Old, Set.union_assoc] using hh⟩
  have hVinAvoidOldActual :
      Vin ∩ ((A ∪ B ∪ Bplus ∪ Rbeta ∪ H) ∪
        (Kclean.points : Set (EuclideanSpace ℝ (Fin 2)))) = ∅ := by
    simpa [Old, Set.union_assoc] using hVinAvoidActual
  have hSideAvoidOldActual :
      (Side ∪ ({terminalGate, sideSource} : Set _)) ∩
        ((A ∪ B ∪ Bplus ∪ Rbeta ∪ H) ∪
          (Kclean.points : Set (EuclideanSpace ℝ (Fin 2)))) = ∅ := by
    simpa [Old, Set.union_assoc] using hSideAvoidActual
  have hBridgeAvoidOldActual :
      (Bridge ∪ ({sideSource, quadrantGate} : Set _)) ∩
        ((A ∪ B ∪ Bplus ∪ Rbeta ∪ H) ∪
          (Kclean.points : Set (EuclideanSpace ℝ (Fin 2)))) = ∅ := by
    simpa [Old, Set.union_assoc] using hBridgeAvoidActual
  have hQuadrantOpenAvoidOldActual :
      openSegment ℝ quadrantGate y ∩
        ((A ∪ B ∪ Bplus ∪ Rbeta ∪ H) ∪
          (Kclean.points : Set (EuclideanSpace ℝ (Fin 2)))) = ∅ := by
    simpa [Old, Set.union_assoc] using hQuadrantOpenAvoidActual
  have hVinSubsetDelta : Vin ⊆ Metric.ball x Disk.radius := by
    intro q hq
    exact Metric.ball_subset_ball hrhoTermDisk.le (hVinBall hq)
  have hTerminalSegmentMeetsSide :
      segment ℝ h terminalGate ∩ (Side ∪ ({terminalGate} : Set _)) =
        ({terminalGate} : Set _) := by
    apply Set.Subset.antisymm
    · intro q hq
      rcases hhTerminalSegment hq.1 with hqVin | hqGate
      · rcases hq.2 with hqSide | hqGate'
        · exact False.elim (Set.eq_empty_iff_forall_notMem.mp hVinSide q
            ⟨hqVin, hqSide⟩)
        · simpa using hqGate'
      · simpa using hqGate
    · intro q hq
      have hqGate : q = terminalGate := by simpa using hq
      subst q
      exact ⟨right_mem_segment ℝ _ _, Or.inr (by simp)⟩
  refine ⟨{
    Kclean := Kclean
    Bad := (Kclean.points : Set _)
    DeltaX := Metric.ball x Disk.radius
    eventRadius := eventRadius
    S := S
    SelectedSide := SelectedSide
    StartSector := StartSector
    Qx := Q
    TerminalSideRegion := Side
    TerminalBridgeRegion := Bridge
    terminalGate := terminalGate
    terminalSideSource := sideSource
    quadrantGate := quadrantGate
    h := h
    Vin := Vin
    predecessor := predecessor
    approach := approach
    lastGate := lastGate
    kclean_carrier := hKcarrier
    bad_eq_points := rfl
    deltaX_eq := rfl
    non_u_vertices_are_points := hKvertices
    event_clean_segments := hEventClean
    selected_side_choice := hSelectedChoice
    source_mem_selected_closure := hSourceSelectedClosure
    start_open := hStartOpen
    start_convex := hStartConvex
    start_subset_selected := hStartSubset
    source_mem_start_closure := hSourceStartClosure
    source_not_mem_start := hSourceNotStart
    start_avoids_old := by simpa [Old, Set.union_assoc] using hStartAvoidOld
    event_balls_avoid_start := hEventAvoidStart
    event_local_geometry := hEventLocal
    event_closedBalls_pairwise := event_pairwise
    selected_avoids_old := hSelectedAvoidsOld
    selected_avoids_terminal_closures :=
      simultaneousBigonAvoidTerminalClosures SelectedSide Side Bridge Q x rhoTerm
        hSideBall hBridgeBall hQBall hSelectedAvoidTerminalClosures
    selected_meets_H_only_in_events := hSelectedMeetsHOnlyInEvents
    x_mem_deltaX := Metric.mem_ball_self hDiskRadius
    y_mem_deltaX := hyDisk
    bplus_subset_deltaX := hBplusBall
    q_subset_deltaX := hQSubsetDelta
    q_convex := hQconvex
    q_compact_closure := hQcompact
    x_mem_q_closure := hxQ
    q_has_nonterminal_point := ⟨quadrantGate, hquadrantQ, hquadrantNe⟩
    y_mem_q := hyQ
    x_not_mem_q := hxnotQ
    q_meets_old_only_at_y := by simpa [Old, Set.union_assoc] using hQOld
    terminal_side_open := hSideOpen
    terminal_side_convex := hSideConvex
    terminal_side_compact_closure := hSideCompact
    terminal_side_subset_deltaX := hSideSubsetDelta
    terminal_side_avoids_old := hSideAvoidOldActual
    terminal_gate_mem_deltaX := hTerminalGateDelta
    terminal_gate_mem_side_closure := hterminalSideClosure
    terminal_gate_not_mem_side := hterminalNotSide
    terminal_gate_not_mem_q := hTerminalGateNotQ
    terminal_side_source_mem_side_closure := hsourceSideClosure
    terminal_side_source_mem_deltaX := hSideSourceDelta
    terminal_side_source_not_mem_side := hsourceNotSide
    terminal_gate_ne_side_source := hterminalNeSource
    terminal_side_segment := hterminalSourceSegment
    terminal_side_open_segment := hterminalSourceOpen
    terminal_bridge_open := hBridgeOpen
    terminal_bridge_convex := hBridgeConvex
    terminal_bridge_compact_closure := hBridgeCompact
    terminal_bridge_subset_deltaX := hBridgeSubsetDelta
    terminal_bridge_avoids_old := hBridgeAvoidOldActual
    terminal_side_source_mem_bridge_closure := hsourceBridgeClosure
    terminal_side_source_not_mem_bridge := hsourceNotBridge
    quadrant_gate_mem_bridge_closure := hquadrantBridgeClosure
    quadrant_gate_not_mem_bridge := hquadrantNotBridge
    terminal_side_source_ne_quadrant_gate := hsourceNeQuadrant
    terminal_bridge_segment := hsourceQuadrantSegment
    terminal_bridge_open_segment := hsourceQuadrantOpen
    quadrant_gate_mem_q := hquadrantQ
    quadrant_gate_ne_y := hquadrantNe
    bridge_segment_meets_q_at_gate := hsourceQuadrantQ
    side_bridge_closures := hSideBridgeClosure
    side_q_closures_disjoint := hSideQClosure
    bridge_q_closures := hBridgeQClosure
    quadrant_to_y_segment := hquadrantYSegment
    quadrant_to_y_avoids_old := hQuadrantOpenAvoidOldActual
    predecessor_subset := hPredecessorSubset
    approach_subset := hApproachSubset
    predecessor_target := hPredecessorTarget
    approach_source := hApproachSource
    predecessor_approach_meet := hPredecessorApproach
    approach_target := hApproachTarget
    approach_meets_terminal_segment := hApproachTerminal
    predecessor_disjoint_terminal_segment := hPredecessorTerminal
    vin_open := hVinOpen'
    vin_convex := hVinConvex
    h_mem_vin := hhVin
    h_ne_terminal_gate := hhNeTerminal
    h_avoids_old := hhAvoidActual
    vin_subset_selected := hVinSelected'
    x_mem_vin_closure := hxVinClosure
    selected_near_x_subset_vin := hNear'
    vin_subset_deltaX := hVinSubsetDelta
    vin_q_disjoint := hVinQ
    vin_avoids_old := hVinAvoidOldActual
    terminal_gate_mem_vin_closure := hterminalVinClosure
    terminal_gate_not_mem_vin := hterminalNotVin
    h_to_terminal_gate_segment := hhTerminalSegment
    h_to_terminal_gate_open_segment := hhTerminalOpen
    h_to_terminal_gate_meets_side := hTerminalSegmentMeetsSide
    vin_side_closures := hVinSideClosure
    vin_bridge_closures_disjoint := hVinBridgeClosure
    vin_side_disjoint := hVinSide
    event_balls_avoid_vin := hEventAvoidVin
  }⟩

noncomputable def OrdinaryAdjacentEdgesSimultaneousBigonGeometryExists
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (u : V) (firstEdge secondEdge : G.edgeFinset)
    (firstArc secondArc : PolygonalArc)
    (x y : EuclideanSpace ℝ (Fin 2))
    (FirstCut : PolygonalArcPointCutData firstArc x)
    (SecondCut : PolygonalArcPointCutData secondArc x)
    (A B Bplus Rbeta H : Set (EuclideanSpace ℝ (Fin 2)))
    (Tail : BigonRerouteOrderedBetaTailData
      G D secondEdge u y B Bplus Rbeta H)
    (retainedArc : G.edgeFinset → PolygonalArc)
    (XA : Finset (EuclideanSpace ℝ (Fin 2)))
    (hx : x ∈ D.crossingSet)
    (Disk : OrdinaryLabeledCrossingDiskData G D ⟨x, hx⟩)
    (hclean : ∀ (e f : G.edgeFinset)
      (p : EuclideanSpace ℝ (Fin 2)), e ≠ f →
        p ∈ (D.edgeArc e).relativeInterior →
          p ∈ (D.edgeArc f).relativeInterior →
            ∃ i j : ℕ,
              ∃ (hi : i + 1 < (D.edgeArc e).vertices.length)
                (hj : j + 1 < (D.edgeArc f).vertices.length),
                p ∈ openSegment ℝ (D.edgeArc e).vertices[i]
                    (D.edgeArc e).vertices[i + 1] ∧
                  p ∈ openSegment ℝ (D.edgeArc f).vertices[j]
                    (D.edgeArc f).vertices[j + 1] ∧
                    ¬ ∃ c : ℝ,
                      (D.edgeArc f).vertices[j + 1] -
                          (D.edgeArc f).vertices[j] =
                        c • ((D.edgeArc e).vertices[i + 1] -
                          (D.edgeArc e).vertices[i]))
    (hedges : firstEdge ≠ secondEdge)
    (hfirstCarrier : firstArc.carrier = (D.edgeArc firstEdge).carrier)
    (hfirstRelative : firstArc.relativeInterior =
      (D.edgeArc firstEdge).relativeInterior)
    (hfirstSource : firstArc.source = D.vertexPlacement u)
    (hsecondCarrier : secondArc.carrier = (D.edgeArc secondEdge).carrier)
    (hsecondRelative : secondArc.relativeInterior =
      (D.edgeArc secondEdge).relativeInterior)
    (hsecondSource : secondArc.source = D.vertexPlacement u)
    (hxFirst : x ∈ (D.edgeArc firstEdge).relativeInterior)
    (hxSecond : x ∈ (D.edgeArc secondEdge).relativeInterior)
    (hySecond : y ∈ (D.edgeArc secondEdge).relativeInterior)
    (hyx : y ≠ x)
    (hA : A = FirstCut.prefixArc.carrier)
    (hB : B = SecondCut.prefixArc.carrier)
    (hBplus : Bplus = segment ℝ x y)
    (hAB : A ∩ B = ({D.vertexPlacement u, x} : Set _))
    (hBBplus : B ∩ Bplus = ({x} : Set _))
    (hBplusBall : Bplus ⊆ Metric.ball x Disk.radius)
    (hRbeta : Rbeta =
      (D.edgeArc secondEdge).carrier \ ((B ∪ Bplus) \ ({y} : Set _)))
    (hH : H =
      (⋃ edge : G.edgeFinset,
        if edge = firstEdge then
          (D.edgeArc edge).carrier \
            (A \ ({D.vertexPlacement u, x} : Set _))
        else if edge = secondEdge then
          (D.edgeArc edge).carrier \
            ((B \ ({D.vertexPlacement u, x} : Set _)) ∪
              (Bplus \ ({x, y} : Set _)))
        else (D.edgeArc edge).carrier) ∪
      {p | ∃ v : V, v ≠ u ∧ p = D.vertexPlacement v})
    (hATail : Disjoint A Tail.tailArc.carrier)
    (hretained : retainedArc = fun e =>
      if e = firstEdge then FirstCut.suffixArc
      else if e = secondEdge then Tail.tailArc
      else D.edgeArc e)
    (hXASpec : ∀ p, p ∈ XA ↔
      p ∈ A \ ({D.vertexPlacement u, x} : Set _) ∧ p ∈ H)
    (hFirstPrefixTransfer : ∀ p i
        (hi : i + 1 < (D.edgeArc firstEdge).vertices.length),
      p ∈ openSegment ℝ (D.edgeArc firstEdge).vertices[i]
          (D.edgeArc firstEdge).vertices[i + 1] →
      p ∈ FirstCut.prefixArc.carrier → p ≠ x →
      ∃ j : ℕ, ∃ hj : j + 1 < FirstCut.prefixArc.vertices.length,
        p ∈ openSegment ℝ FirstCut.prefixArc.vertices[j]
            FirstCut.prefixArc.vertices[j + 1] ∧
          ∃ scale : ℝ, scale ≠ 0 ∧
            FirstCut.prefixArc.vertices[j + 1] -
                FirstCut.prefixArc.vertices[j] =
              scale • ((D.edgeArc firstEdge).vertices[i + 1] -
                (D.edgeArc firstEdge).vertices[i]))
    (hDiskEdges : (Disk.firstEdge = firstEdge ∧ Disk.secondEdge = secondEdge) ∨
      (Disk.firstEdge = secondEdge ∧ Disk.secondEdge = firstEdge))
    (i j : ℕ)
    (hi : i + 1 < (D.edgeArc firstEdge).vertices.length)
    (hj : j + 1 < (D.edgeArc secondEdge).vertices.length)
    (hxOpenFirst : x ∈ openSegment ℝ (D.edgeArc firstEdge).vertices[i]
      (D.edgeArc firstEdge).vertices[i + 1])
    (hxOpenSecond : x ∈ openSegment ℝ (D.edgeArc secondEdge).vertices[j]
      (D.edgeArc secondEdge).vertices[j + 1])
    (hnonparallel : ¬ ∃ c : ℝ,
      (D.edgeArc secondEdge).vertices[j + 1] -
          (D.edgeArc secondEdge).vertices[j] =
        c • ((D.edgeArc firstEdge).vertices[i + 1] -
          (D.edgeArc firstEdge).vertices[i])) :
    Nonempty (OrdinaryAdjacentEdgesSimultaneousBigonGeometryData
      G D u firstEdge secondEdge x y A B Bplus Rbeta H
      FirstCut.prefixArc XA hx Disk) :=
  ordinaryAdjacentEdgesSimultaneousBigonGeometryPrepareFromContext
    G D u firstEdge secondEdge firstArc secondArc x y FirstCut SecondCut
    A B Bplus Rbeta H Tail retainedArc XA hx Disk i j hi hj
    { hclean := hclean
      hedges := hedges
      hfirstCarrier := hfirstCarrier
      hfirstRelative := hfirstRelative
      hfirstSource := hfirstSource
      hsecondCarrier := hsecondCarrier
      hsecondRelative := hsecondRelative
      hsecondSource := hsecondSource
      hxFirst := hxFirst
      hxSecond := hxSecond
      hySecond := hySecond
      hyx := hyx
      hA := hA
      hB := hB
      hBplus := hBplus
      hAB := hAB
      hBBplus := hBBplus
      hBplusBall := hBplusBall
      hRbeta := hRbeta
      hH := hH
      hATail := hATail
      hretained := hretained
      hXASpec := hXASpec
      hFirstPrefixTransfer := hFirstPrefixTransfer
      hDiskEdges := hDiskEdges
      hxOpenFirst := hxOpenFirst
      hxOpenSecond := hxOpenSecond
      hnonparallel := hnonparallel }
