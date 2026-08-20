import ErdosProblems.Erdos733.ST.BigonRerouteOrderedBetaTailData
import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing
import ErdosProblems.Erdos733.ST.PolygonalArcFiniteInteriorFirstPoint
import ErdosProblems.Erdos733.ST.PolygonalArcInteriorPointCutDataExists
import ErdosProblems.Erdos733.ST.PolygonalArcOpenSegmentSubsetRelativeInterior
import ErdosProblems.Erdos733.ST.PolygonalArcPointCutDataExists
import ErdosProblems.Erdos733.ST.PolygonalArcReverse
import Mathlib.Tactic

open Classical
noncomputable section

lemma ordinaryAdjacentEdgesChooseShort
    {V : Type*} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (S : PolygonalArc)
    (x : EuclideanSpace ℝ (Fin 2))
    (hS01 : 0 + 1 < S.vertices.length)
    (hS0 : S.vertices[0] = x)
    (hS01ne : S.vertices[0] ≠ S.vertices[1]) :
    ∃ y : EuclideanSpace ℝ (Fin 2),
      y ∈ openSegment ℝ S.vertices[0] S.vertices[1] ∧
        ∀ p, p ∈ segment ℝ S.vertices[0] y →
          p ∈ D.crossingSet → p = x := by
  let Y := (D.crossingSet.erase x).filter
    (fun p => p ∈ segment ℝ S.vertices[0] S.vertices[1])
  by_cases hY : Y.Nonempty
  · obtain ⟨z, hzY, hzmin⟩ :=
      Finset.exists_min_image Y (fun p => dist S.vertices[0] p) hY
    have hzErase : z ∈ D.crossingSet.erase x := (Finset.mem_filter.mp hzY).1
    have hzCross : z ∈ D.crossingSet := Finset.mem_of_mem_erase hzErase
    have hzx : z ≠ x := (Finset.mem_erase.mp hzErase).1
    have hzSeg : z ∈ segment ℝ S.vertices[0] S.vertices[1] :=
      (Finset.mem_filter.mp hzY).2
    have hz0 : z ≠ S.vertices[0] := by simpa [hS0] using hzx
    let y := midpoint ℝ S.vertices[0] z
    have hySubOpen : y ∈ openSegment ℝ S.vertices[0] z := by
      simpa [y] using midpoint_mem_openSegment (𝕜 := ℝ) S.vertices[0] z
    have hySeg : y ∈ segment ℝ S.vertices[0] S.vertices[1] :=
      (convex_segment S.vertices[0] S.vertices[1]).segment_subset
        (left_mem_segment ℝ _ _) hzSeg
        (openSegment_subset_segment ℝ _ _ hySubOpen)
    have hy0 : y ≠ S.vertices[0] := by
      intro h
      have : S.vertices[0] ∈ openSegment ℝ S.vertices[0] z := h ▸ hySubOpen
      exact hz0 (((left_mem_openSegment_iff (𝕜 := ℝ)).1 this).symm)
    have hy1 : y ≠ S.vertices[1] := by
      intro h
      have hdistz : dist S.vertices[0] z ≤ dist S.vertices[0] S.vertices[1] := by
        have hball : z ∈ Metric.closedBall S.vertices[0]
            (dist S.vertices[0] S.vertices[1]) :=
          (convex_closedBall S.vertices[0] (dist S.vertices[0] S.vertices[1])).segment_subset
            (by simp [Metric.mem_closedBall])
            (by simp [Metric.mem_closedBall, dist_comm]) hzSeg
        simpa [Metric.mem_closedBall, dist_comm] using hball
      have hmid : dist S.vertices[0] y = (1 / 2 : ℝ) * dist S.vertices[0] z := by
        simpa [y, invOf_eq_inv, Real.norm_ofNat, one_div] using
          (dist_left_midpoint (𝕜 := ℝ) S.vertices[0] z)
      have hzpos : (0 : ℝ) < dist S.vertices[0] z := dist_pos.2 hz0.symm
      rw [h] at hmid
      nlinarith
    refine ⟨y, mem_openSegment_of_ne_left_right hy0.symm hy1.symm hySeg, ?_⟩
    intro p hpSeg hpCross
    by_contra hpx
    have hpY : p ∈ Y := Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨hpx, hpCross⟩,
        (convex_segment S.vertices[0] S.vertices[1]).segment_subset
          (left_mem_segment ℝ _ _) hySeg hpSeg⟩
    have hmin := hzmin p hpY
    have hpdist : dist S.vertices[0] p ≤ dist S.vertices[0] y := by
      have hball : p ∈ Metric.closedBall S.vertices[0] (dist S.vertices[0] y) :=
        (convex_closedBall S.vertices[0] (dist S.vertices[0] y)).segment_subset
          (by simp [Metric.mem_closedBall])
          (by simp [Metric.mem_closedBall, dist_comm]) hpSeg
      simpa [Metric.mem_closedBall, dist_comm] using hball
    have hmid : dist S.vertices[0] y = (1 / 2 : ℝ) * dist S.vertices[0] z := by
      simpa [y, invOf_eq_inv, Real.norm_ofNat, one_div] using
        (dist_left_midpoint (𝕜 := ℝ) S.vertices[0] z)
    have hzpos : (0 : ℝ) < dist S.vertices[0] z := dist_pos.2 hz0.symm
    nlinarith
  · let y := midpoint ℝ S.vertices[0] S.vertices[1]
    have hyOpen : y ∈ openSegment ℝ S.vertices[0] S.vertices[1] := by
      simpa [y] using midpoint_mem_openSegment (𝕜 := ℝ)
        S.vertices[0] S.vertices[1]
    refine ⟨y, hyOpen, ?_⟩
    intro p hpSeg hpCross
    by_contra hpx
    have hpY : p ∈ Y := Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨hpx, hpCross⟩,
        (convex_segment S.vertices[0] S.vertices[1]).segment_subset
          (left_mem_segment ℝ _ _)
          (openSegment_subset_segment ℝ _ _ hyOpen) hpSeg⟩
    exact hY ⟨p, hpY⟩


-- [TABLET NODE: OrdinaryAdjacentEdgesFavorableTailFreeCandidate]
lemma OrdinaryAdjacentEdgesFavorableTailFreeCandidate {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (alpha beta : G.edgeFinset) (u : V)
    (hopen : forall p : EuclideanSpace ℝ (Fin 2),
      p ∈ D.crossingSet ->
        p ∈ (D.edgeArc alpha).relativeInterior ->
          p ∈ (D.edgeArc beta).relativeInterior ->
            exists i j : ℕ,
              exists (hi : i + 1 < (D.edgeArc alpha).vertices.length)
                (hj : j + 1 < (D.edgeArc beta).vertices.length),
                p ∈ openSegment ℝ (D.edgeArc alpha).vertices[i]
                    (D.edgeArc alpha).vertices[i + 1] ∧
                  p ∈ openSegment ℝ (D.edgeArc beta).vertices[j]
                    (D.edgeArc beta).vertices[j + 1]) :
    alpha ≠ beta ->
      u ∈ alpha.1 ->
        u ∈ beta.1 ->
          (exists p : EuclideanSpace ℝ (Fin 2),
            p ∈ D.crossingSet ∧
              p ∈ (D.edgeArc alpha).relativeInterior ∧
                p ∈ (D.edgeArc beta).relativeInterior) ->
            exists firstEdge secondEdge : G.edgeFinset,
              (firstEdge = alpha ∧ secondEdge = beta ∨
                firstEdge = beta ∧ secondEdge = alpha) ∧
              exists firstArc secondArc : PolygonalArc,
                firstArc.carrier = (D.edgeArc firstEdge).carrier ∧
                firstArc.relativeInterior =
                  (D.edgeArc firstEdge).relativeInterior ∧
                firstArc.source = D.vertexPlacement u ∧
                secondArc.carrier = (D.edgeArc secondEdge).carrier ∧
                secondArc.relativeInterior =
                  (D.edgeArc secondEdge).relativeInterior ∧
                secondArc.source = D.vertexPlacement u ∧
                exists x y : EuclideanSpace ℝ (Fin 2),
                  exists FirstCut : PolygonalArcPointCutData firstArc x,
                    exists SecondCut : PolygonalArcPointCutData secondArc x,
                      exists OutCut :
                        PolygonalArcPointCutData SecondCut.suffixArc y,
                        x ∈ D.crossingSet ∧
                        x ∈ (D.edgeArc firstEdge).relativeInterior ∧
                        x ∈ (D.edgeArc secondEdge).relativeInterior ∧
                        y ∈ (D.edgeArc secondEdge).relativeInterior ∧
                        y ≠ x ∧
                        OutCut.prefixArc.carrier = segment ℝ x y ∧
                        FirstCut.prefixArc.carrier ∩
                            SecondCut.prefixArc.carrier =
                          ({D.vertexPlacement u, x} : Set _) ∧
                        SecondCut.prefixArc.carrier ∩
                            OutCut.prefixArc.carrier = ({x} : Set _) ∧
                        Disjoint FirstCut.prefixArc.carrier
                          OutCut.suffixArc.carrier ∧
                        exists XA XB : Finset (EuclideanSpace ℝ (Fin 2)),
                          (forall p, p ∈ XA ↔
                            p ∈ FirstCut.prefixArc.carrier \
                              ({D.vertexPlacement u, x} : Set _) ∧
                            exists e : G.edgeFinset,
                              e ≠ firstEdge ∧ e ≠ secondEdge ∧
                                p ∈ (D.edgeArc e).relativeInterior) ∧
                          (forall p, p ∈ XB ↔
                            p ∈ SecondCut.prefixArc.carrier \
                              ({D.vertexPlacement u, x} : Set _) ∧
                            exists e : G.edgeFinset,
                              e ≠ firstEdge ∧ e ≠ secondEdge ∧
                                p ∈ (D.edgeArc e).relativeInterior) ∧
                          XA.card ≤ XB.card ∧
                          (exists A B Bplus Rbeta H :
                              Set (EuclideanSpace ℝ (Fin 2)),
                            A = FirstCut.prefixArc.carrier ∧
                            B = SecondCut.prefixArc.carrier ∧
                            Bplus = OutCut.prefixArc.carrier ∧
                            Rbeta =
                              (D.edgeArc secondEdge).carrier \
                                ((B ∪ Bplus) \ ({y} : Set _)) ∧
                            H =
                              (⋃ edge : G.edgeFinset,
                                if edge = firstEdge then
                                  (D.edgeArc edge).carrier \
                                    (A \ ({D.vertexPlacement u, x} : Set _))
                                else if edge = secondEdge then
                                  (D.edgeArc edge).carrier \
                                    ((B \ ({D.vertexPlacement u, x} : Set _)) ∪
                                      (Bplus \ ({x, y} : Set _)))
                                else (D.edgeArc edge).carrier) ∪
                              {p | exists v : V,
                                v ≠ u ∧ p = D.vertexPlacement v} ∧
                            (exists Tail : BigonRerouteOrderedBetaTailData
                                G D secondEdge u y B Bplus Rbeta H,
                              (forall p, p ∈ Bplus →
                                p ∈ D.crossingSet → p = x) ∧
                              (forall v : V,
                                D.vertexPlacement v ∈ Bplus → False) ∧
                              (exists XAexact XBexact :
                                  Finset (EuclideanSpace ℝ (Fin 2)),
                                XAexact = XA ∧ XB ⊆ XBexact ∧
                                (forall p, p ∈ XAexact ↔
                                  p ∈ A \
                                    ({D.vertexPlacement u, x} : Set _) ∧
                                  p ∈ H) ∧
                                (forall p, p ∈ XBexact ↔
                                  p ∈ B \
                                    ({D.vertexPlacement u, x} : Set _) ∧
                                  p ∈ H) ∧
                                XAexact.card ≤ XBexact.card))) := by
-- BODY
  intro hab huAlpha huBeta hcross
  have endpoint_at (e : G.edgeFinset) (hu : u ∈ e.1) :
      (D.edgeArc e).source = D.vertexPlacement u ∨
        (D.edgeArc e).target = D.vertexPlacement u := by
    rcases D.edgeArc_endpoints e with ⟨a, b, _hadj, he, hends⟩
    have huab : u = a ∨ u = b := by
      have : u ∈ (Sym2.mk a b : Sym2 V) := by simpa [he] using hu
      simpa [Sym2.mem_iff'] using this
    rcases hends with hends | hends <;> rcases huab with rfl | rfl
    · exact Or.inl hends.1
    · exact Or.inr hends.2
    · exact Or.inr hends.2
    · exact Or.inl hends.1
  let orient : G.edgeFinset → PolygonalArc := fun e =>
    if (D.edgeArc e).source = D.vertexPlacement u then
      D.edgeArc e
    else PolygonalArcReverse (D.edgeArc e)
  have orient_carrier (e : G.edgeFinset) :
      (orient e).carrier = (D.edgeArc e).carrier := by
    dsimp [orient]
    split_ifs
    · rfl
    · rfl
  have orient_relative (e : G.edgeFinset) :
      (orient e).relativeInterior = (D.edgeArc e).relativeInterior := by
    dsimp [orient]
    split_ifs
    · rfl
    · rfl
  have orient_source (e : G.edgeFinset) (hu : u ∈ e.1) :
      (orient e).source = D.vertexPlacement u := by
    dsimp [orient]
    split_ifs with h
    · exact h
    · rcases endpoint_at e hu with hs | ht
      · exact (h hs).elim
      · exact ht
  have open_not_vertex (Q : PolygonalArc) (p : EuclideanSpace ℝ (Fin 2))
      (i : ℕ) (hi : i + 1 < Q.vertices.length)
      (hp : p ∈ openSegment ℝ Q.vertices[i] Q.vertices[i + 1]) :
      p ∉ Q.vertices := by
    intro hpv
    rcases List.getElem_of_mem hpv with ⟨k, hk, hkp⟩
    by_cases hki : k = i
    · subst k
      have hne : Q.vertices[i] ≠ Q.vertices[i + 1] := by
        intro heq
        have := (Q.simple_vertices.getElem_inj_iff
          (i := i) (j := i + 1) (hi := by omega) (hj := hi)).1 heq
        omega
      exact hne ((left_mem_openSegment_iff (𝕜 := ℝ)).1 (hkp ▸ hp))
    · by_cases hkis : k = i + 1
      · subst k
        have hne : Q.vertices[i] ≠ Q.vertices[i + 1] := by
          intro heq
          have := (Q.simple_vertices.getElem_inj_iff
            (i := i) (j := i + 1) (hi := by omega) (hj := hi)).1 heq
          omega
        exact hne ((right_mem_openSegment_iff (𝕜 := ℝ)).1 (hkp ▸ hp))
      · exact Q.vertices_avoid_nonincident_interiors hi hk hki hkis (hkp ▸ hp)
  let X : Finset (EuclideanSpace ℝ (Fin 2)) :=
    D.crossingSet.filter (fun p =>
      p ∈ (D.edgeArc alpha).relativeInterior ∧
        p ∈ (D.edgeArc beta).relativeInterior)
  have hXnonempty : X.Nonempty := by
    rcases hcross with ⟨p, hpD, hpA, hpB⟩
    refine ⟨p, ?_⟩
    simp [X, hpD, hpA, hpB]
  have hXalpha : ∀ p, p ∈ X → p ∈ (orient alpha).relativeInterior := by
    intro p hp
    rw [orient_relative]
    exact (Finset.mem_filter.mp hp).2.1
  have hXbeta : ∀ p, p ∈ X → p ∈ (orient beta).relativeInterior := by
    intro p hp
    rw [orient_relative]
    exact (Finset.mem_filter.mp hp).2.2
  have hXnotAlphaVertices : ∀ p, p ∈ X → p ∉ (orient alpha).vertices := by
    intro p hp
    rcases hopen p (Finset.mem_filter.mp hp).1
        (Finset.mem_filter.mp hp).2.1 (Finset.mem_filter.mp hp).2.2 with
      ⟨i, j, hi, hj, hpAi, hpBj⟩
    have hnot := open_not_vertex (D.edgeArc alpha) p i hi hpAi
    dsimp [orient]
    split_ifs
    · exact hnot
    · simpa only [PolygonalArcReverse, List.mem_reverse] using hnot
  have hXnotBetaVertices : ∀ p, p ∈ X → p ∉ (orient beta).vertices := by
    intro p hp
    rcases hopen p (Finset.mem_filter.mp hp).1
        (Finset.mem_filter.mp hp).2.1 (Finset.mem_filter.mp hp).2.2 with
      ⟨i, j, hi, hj, hpAi, hpBj⟩
    have hnot := open_not_vertex (D.edgeArc beta) p j hj hpBj
    dsimp [orient]
    split_ifs
    · exact hnot
    · simpa only [PolygonalArcReverse, List.mem_reverse] using hnot
  have open_index_unique (Q : PolygonalArc) :
      ∀ z a b (ha : a + 1 < Q.vertices.length)
        (hb : b + 1 < Q.vertices.length),
        z ∈ openSegment ℝ Q.vertices[a] Q.vertices[a + 1] →
        z ∈ segment ℝ Q.vertices[b] Q.vertices[b + 1] → a = b := by
    intro z a b ha hb hza hzb
    have habne : Q.vertices[a] ≠ Q.vertices[a + 1] := by
      intro heq
      have hidx := (Q.simple_vertices.getElem_inj_iff
        (i := a) (j := a + 1) (hi := by omega) (hj := ha)).1 heq
      omega
    have hzleft : z ≠ Q.vertices[a] := by
      intro hz
      subst z
      exact habne ((left_mem_openSegment_iff (𝕜 := ℝ)).1 hza)
    have hzright : z ≠ Q.vertices[a + 1] := by
      intro hz
      subst z
      exact habne ((right_mem_openSegment_iff (𝕜 := ℝ)).1 hza)
    rcases lt_trichotomy a b with hab | rfl | hba
    · have hraw := Q.segment_intersections ha hb hab
      have hzint : z ∈ segment ℝ Q.vertices[a] Q.vertices[a + 1] ∩
          segment ℝ Q.vertices[b] Q.vertices[b + 1] :=
        ⟨openSegment_subset_segment ℝ _ _ hza, hzb⟩
      by_cases hadj : b = a + 1
      · rw [hraw, if_pos hadj] at hzint
        exact False.elim (hzright (by simpa [hadj] using hzint))
      · rw [hraw, if_neg hadj] at hzint
        exact False.elim hzint
    · rfl
    · have hraw := Q.segment_intersections hb ha hba
      have hzint : z ∈ segment ℝ Q.vertices[b] Q.vertices[b + 1] ∩
          segment ℝ Q.vertices[a] Q.vertices[a + 1] :=
        ⟨hzb, openSegment_subset_segment ℝ _ _ hza⟩
      by_cases hadj : a = b + 1
      · rw [hraw, if_pos hadj] at hzint
        exact False.elim (hzleft (by simpa [hadj] using hzint))
      · rw [hraw, if_neg hadj] at hzint
        exact False.elim hzint
  have first_package (Q : PolygonalArc)
      (hrel : ∀ p, p ∈ X → p ∈ Q.relativeInterior)
      (hnotverts : ∀ p, p ∈ X → p ∉ Q.vertices) :
      ∃ x : EuclideanSpace ℝ (Fin 2),
        ∃ j : ℕ, ∃ hj : j + 1 < Q.vertices.length,
          ∃ Cut : PolygonalArcPointCutData Q x,
            x ∈ X ∧
            x ∈ openSegment ℝ Q.vertices[j] Q.vertices[j + 1] ∧
            Cut.cutIndex = j ∧
            (∀ z, z ∈ X → z ∈ Cut.prefixArc.carrier → z = x) ∧
            ∀ z, z ∈ X → ∀ ZCut : PolygonalArcPointCutData Q z,
              Cut.prefixArc.carrier ⊆ ZCut.prefixArc.carrier := by
    obtain ⟨x, j, hj, hxX, hxseg, hminimal⟩ :=
      PolygonalArcFiniteInteriorFirstPoint Q X hXnonempty hrel
    have hxopen : x ∈ openSegment ℝ Q.vertices[j] Q.vertices[j + 1] := by
      apply mem_openSegment_of_ne_left_right
      · intro h
        apply hnotverts x hxX
        rw [← h]
        exact List.getElem_mem (by omega)
      · intro h
        apply hnotverts x hxX
        rw [← h]
        exact List.getElem_mem hj
      · exact hxseg
    obtain ⟨Cut⟩ := PolygonalArcInteriorPointCutDataExists Q j hj x hxopen
    have hcut : Cut.cutIndex = j :=
      (open_index_unique Q x j Cut.cutIndex hj Cut.cutIndex_valid hxopen
        Cut.cut_mem_segment).symm
    have hCutRegion : Cut.prefixArc.carrier =
        {z | ∃ i : ℕ, ∃ hi : i + 1 < Q.vertices.length,
          i < j ∧ z ∈ segment ℝ Q.vertices[i] Q.vertices[i + 1]} ∪
          segment ℝ Q.vertices[j] x := by
      simpa only [hcut] using Cut.prefix_carrier_region
    have hminPrefix : ∀ z, z ∈ X → z ∈ Cut.prefixArc.carrier → z = x := by
      intro z hzX hzCut
      rw [hCutRegion] at hzCut
      rcases hzCut with hzEarlier | hzLast
      · apply hminimal z hzX
        left
        rcases hzEarlier with ⟨i, hi, hij, hzi⟩
        rw [ArcCrossingEarlierPrefix]
        apply Set.mem_iUnion.mpr
        exact ⟨⟨i, hij⟩, hzi⟩
      · exact hminimal z hzX (Or.inr hzLast)
    refine ⟨x, j, hj, Cut, hxX, hxopen, hcut, hminPrefix, ?_⟩
    intro z hzX ZCut w hw
    have hk0 : ZCut.cutIndex < Q.vertices.length :=
      Nat.lt_trans (Nat.lt_succ_self _) ZCut.cutIndex_valid
    have hk1 : ZCut.cutIndex + 1 < Q.vertices.length := ZCut.cutIndex_valid
    have hzOpen : z ∈ openSegment ℝ Q.vertices[ZCut.cutIndex]
        Q.vertices[ZCut.cutIndex + 1] := by
      apply mem_openSegment_of_ne_left_right
      · intro h
        apply hnotverts z hzX
        rw [← h]
        exact List.getElem_mem (by omega)
      · intro h
        apply hnotverts z hzX
        rw [← h]
        exact List.getElem_mem ZCut.cutIndex_valid
      · exact ZCut.cut_mem_segment
    have hjle : j ≤ ZCut.cutIndex := by
      by_contra hnot
      have hlt : ZCut.cutIndex < j := by omega
      have hzEarlier : z ∈ ArcCrossingEarlierPrefix Q j hj := by
        rw [ArcCrossingEarlierPrefix]
        apply Set.mem_iUnion.mpr
        exact ⟨⟨ZCut.cutIndex, hlt⟩, ZCut.cut_mem_segment⟩
      have hzx : z = x := hminimal z hzX (Or.inl hzEarlier)
      subst z
      have := open_index_unique Q x j ZCut.cutIndex hj
        ZCut.cutIndex_valid hxopen ZCut.cut_mem_segment
      omega
    rw [hCutRegion] at hw
    rw [ZCut.prefix_carrier_region]
    rcases lt_or_eq_of_le hjle with hjlt | hjeq
    · left
      rcases hw with hwEarlier | hwLast
      · rcases hwEarlier with ⟨i, hi, hij, hwi⟩
        exact ⟨i, hi, by omega, hwi⟩
      · exact ⟨j, hj, hjlt, (convex_segment Q.vertices[j]
          Q.vertices[j + 1]).segment_subset
            (left_mem_segment ℝ _ _)
            (openSegment_subset_segment ℝ _ _ hxopen) hwLast⟩
    · have hjeq' : ZCut.cutIndex = j := hjeq.symm
      simp only [hjeq']
      rcases hw with hwEarlier | hwLast
      · exact Or.inl hwEarlier
      · right
        have hxFull : x ∈ segment ℝ Q.vertices[j] Q.vertices[j + 1] :=
          openSegment_subset_segment ℝ _ _ hxopen
        have hzFull : z ∈ segment ℝ Q.vertices[j] Q.vertices[j + 1] :=
          by simpa only [hjeq'] using ZCut.cut_mem_segment
        have hbaseNe : Q.vertices[j] ≠ Q.vertices[j + 1] := by
          intro heq
          have hidx := (Q.simple_vertices.getElem_inj_iff
            (i := j) (j := j + 1) (hi := by omega) (hj := hj)).1 heq
          omega
        have hsameray : SameRay ℝ (x - Q.vertices[j]) (z - Q.vertices[j]) := by
          have hxray := (mem_segment_iff_wbtw.mp hxFull).sameRay_vsub_left
          have hzray := (mem_segment_iff_wbtw.mp hzFull).sameRay_vsub_left
          exact hxray.trans hzray.symm (by
            intro hzero
            have heq : Q.vertices[j + 1] = Q.vertices[j] := sub_eq_zero.mp hzero
            exact (hbaseNe heq.symm).elim)
        have hsameray' : SameRay ℝ (x -ᵥ Q.vertices[j])
            (z -ᵥ Q.vertices[j]) := by
          simpa only [vsub_eq_sub] using hsameray
        rcases wbtw_total_of_sameRay_vsub_left hsameray' with hxz | hzx
        · exact (convex_segment Q.vertices[j] z).segment_subset
            (left_mem_segment ℝ _ _) hxz.mem_segment hwLast
        · have hzx' : z = x := hminimal z hzX (Or.inr hzx.mem_segment)
          simpa [hzx'] using hwLast
  obtain ⟨xAlpha, jAlpha, hjAlpha, AlphaCut, hxAlphaX, hxAlphaOpen,
      hAlphaCutIndex, hAlphaMinimal, hAlphaPrefixSmall⟩ :=
    first_package (orient alpha) hXalpha hXnotAlphaVertices
  obtain ⟨xBeta, jBeta, hjBeta, BetaCut, hxBetaX, hxBetaOpen,
      hBetaCutIndex, hBetaMinimal, hBetaPrefixSmall⟩ :=
    first_package (orient beta) hXbeta hXnotBetaVertices
  obtain ⟨AlphaAtBeta⟩ := PolygonalArcPointCutDataExists (orient alpha) xBeta
    (hXalpha xBeta hxBetaX)
  obtain ⟨BetaAtAlpha⟩ := PolygonalArcPointCutDataExists (orient beta) xAlpha
    (hXbeta xAlpha hxAlphaX)
  have hAlphaPrefixInBeta := hAlphaPrefixSmall xBeta hxBetaX AlphaAtBeta
  have hBetaPrefixInAlpha := hBetaPrefixSmall xAlpha hxAlphaX BetaAtAlpha
  have arc_source_mem (Q : PolygonalArc) : Q.source ∈ Q.carrier := by
    have hlen := Q.length_ge_two
    rw [Q.carrier_eq]
    have hzero : Q.vertices[0] = Q.source := by
      have hhead := Q.source_eq_head
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhead
      exact Option.some.inj hhead
    exact ⟨0, by omega, by simpa [hzero] using
      (left_mem_segment ℝ Q.source Q.vertices[1])⟩
  have arc_target_mem (Q : PolygonalArc) : Q.target ∈ Q.carrier := by
    have hlen := Q.length_ge_two
    rw [Q.carrier_eq]
    let k := Q.vertices.length - 2
    have hk : k + 1 < Q.vertices.length := by dsimp [k]; omega
    have hlast : Q.vertices[k + 1] = Q.target := by
      have ht := Q.target_eq_last
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at ht
      have heq : k + 1 = Q.vertices.length - 1 := by dsimp [k]; omega
      simpa [heq] using Option.some.inj ht
    exact ⟨k, hk, by simpa [hlast] using
      (right_mem_segment ℝ Q.vertices[k] Q.target)⟩
  have orient_target_vertex (e : G.edgeFinset) :
      ∃ v : V, (orient e).target = D.vertexPlacement v := by
    rcases D.edgeArc_endpoints e with ⟨a, b, _hab, _he, hends⟩
    dsimp [orient]
    by_cases hs : (D.edgeArc e).source = D.vertexPlacement u
    · simp only [if_pos hs]
      rcases hends with hends | hends
      · exact ⟨b, hends.2⟩
      · exact ⟨a, hends.2⟩
    · simp only [if_neg hs, PolygonalArcReverse]
      rcases hends with hends | hends
      · exact ⟨a, hends.1⟩
      · exact ⟨b, hends.1⟩
  have alphaPrefixBeta :
      AlphaCut.prefixArc.carrier ∩ (orient beta).carrier =
        ({D.vertexPlacement u, xAlpha} : Set _) := by
    ext z
    constructor
    · intro hz
      have hzAlphaTarget : z ≠ (orient alpha).target := by
        intro hzt
        have htSuffix : (orient alpha).target ∈ AlphaCut.suffixArc.carrier := by
          rw [← AlphaCut.suffix_target]
          exact arc_target_mem AlphaCut.suffixArc
        have hzInter : z ∈ AlphaCut.prefixArc.carrier ∩
            AlphaCut.suffixArc.carrier := ⟨hz.1, hzt ▸ htSuffix⟩
        have hzx : z = xAlpha := by
          have : z ∈ ({xAlpha} : Set _) := AlphaCut.carrier_intersection ▸ hzInter
          simpa using this
        have hxRel := hXalpha xAlpha hxAlphaX
        rw [(orient alpha).relativeInterior_eq] at hxRel
        exact hxRel.2 (by simp [← hzx, hzt])
      by_cases hzu : z = D.vertexPlacement u
      · simp [hzu]
      have hzAlphaRel : z ∈ (orient alpha).relativeInterior := by
        rw [(orient alpha).relativeInterior_eq]
        refine ⟨AlphaCut.prefix_carrier_subset hz.1, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun hs => hzu (hs.trans (orient_source alpha huAlpha)), hzAlphaTarget⟩
      have hzBetaRel : z ∈ (orient beta).relativeInterior := by
        rw [(orient beta).relativeInterior_eq]
        refine ⟨hz.2, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        constructor
        · intro hs
          exact hzu (hs.trans (orient_source beta huBeta))
        · intro ht
          rcases orient_target_vertex beta with ⟨v, htv⟩
          have hzOldAlpha : z ∈ (D.edgeArc alpha).relativeInterior := by
            simpa only [orient_relative alpha] using hzAlphaRel
          exact D.no_vertex_in_edge_interior v alpha (ht.trans htv ▸ hzOldAlpha)
      have hzX : z ∈ X := by
        apply Finset.mem_filter.mpr
        refine ⟨(D.crossingSet_spec z).2 ⟨alpha, beta, hab, ?_, ?_⟩, ?_, ?_⟩
        · simpa only [orient_relative alpha] using hzAlphaRel
        · simpa only [orient_relative beta] using hzBetaRel
        · simpa only [orient_relative alpha] using hzAlphaRel
        · simpa only [orient_relative beta] using hzBetaRel
      have hzx := hAlphaMinimal z hzX hz.1
      simp [hzx]
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hzu | hzx
      · subst z
        constructor
        · have hs := arc_source_mem AlphaCut.prefixArc
          rw [AlphaCut.prefix_source, orient_source alpha huAlpha] at hs
          exact hs
        · rw [← orient_source beta huBeta]
          exact arc_source_mem (orient beta)
      · subst z
        constructor
        · have ht := arc_target_mem AlphaCut.prefixArc
          rw [AlphaCut.prefix_target] at ht
          exact ht
        · have hr := hXbeta xAlpha hxAlphaX
          rw [(orient beta).relativeInterior_eq] at hr
          exact hr.1
  have betaPrefixAlpha :
      BetaCut.prefixArc.carrier ∩ (orient alpha).carrier =
        ({D.vertexPlacement u, xBeta} : Set _) := by
    ext z
    constructor
    · intro hz
      have hzBetaTarget : z ≠ (orient beta).target := by
        intro hzt
        have htSuffix : (orient beta).target ∈ BetaCut.suffixArc.carrier := by
          rw [← BetaCut.suffix_target]
          exact arc_target_mem BetaCut.suffixArc
        have hzInter : z ∈ BetaCut.prefixArc.carrier ∩
            BetaCut.suffixArc.carrier := ⟨hz.1, hzt ▸ htSuffix⟩
        have hzx : z = xBeta := by
          have : z ∈ ({xBeta} : Set _) := BetaCut.carrier_intersection ▸ hzInter
          simpa using this
        have hxRel := hXbeta xBeta hxBetaX
        rw [(orient beta).relativeInterior_eq] at hxRel
        exact hxRel.2 (by simp [← hzx, hzt])
      by_cases hzu : z = D.vertexPlacement u
      · simp [hzu]
      have hzBetaRel : z ∈ (orient beta).relativeInterior := by
        rw [(orient beta).relativeInterior_eq]
        refine ⟨BetaCut.prefix_carrier_subset hz.1, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun hs => hzu (hs.trans (orient_source beta huBeta)), hzBetaTarget⟩
      have hzAlphaRel : z ∈ (orient alpha).relativeInterior := by
        rw [(orient alpha).relativeInterior_eq]
        refine ⟨hz.2, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        constructor
        · intro hs
          exact hzu (hs.trans (orient_source alpha huAlpha))
        · intro ht
          rcases orient_target_vertex alpha with ⟨v, htv⟩
          have hzOldBeta : z ∈ (D.edgeArc beta).relativeInterior := by
            simpa only [orient_relative beta] using hzBetaRel
          exact D.no_vertex_in_edge_interior v beta (ht.trans htv ▸ hzOldBeta)
      have hzX : z ∈ X := by
        apply Finset.mem_filter.mpr
        refine ⟨(D.crossingSet_spec z).2 ⟨beta, alpha, hab.symm, ?_, ?_⟩, ?_, ?_⟩
        · simpa only [orient_relative beta] using hzBetaRel
        · simpa only [orient_relative alpha] using hzAlphaRel
        · simpa only [orient_relative alpha] using hzAlphaRel
        · simpa only [orient_relative beta] using hzBetaRel
      have hzx := hBetaMinimal z hzX hz.1
      simp [hzx]
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hzu | hzx
      · subst z
        constructor
        · have hs := arc_source_mem BetaCut.prefixArc
          rw [BetaCut.prefix_source, orient_source beta huBeta] at hs
          exact hs
        · rw [← orient_source alpha huAlpha]
          exact arc_source_mem (orient alpha)
      · subst z
        constructor
        · have ht := arc_target_mem BetaCut.prefixArc
          rw [BetaCut.prefix_target] at ht
          exact ht
        · have hr := hXalpha xBeta hxBetaX
          rw [(orient alpha).relativeInterior_eq] at hr
          exact hr.1
  have outgoing_package (Q : PolygonalArc) (x : EuclideanSpace ℝ (Fin 2))
      (Cut : PolygonalArcPointCutData Q x)
      (hQsource : Q.source = D.vertexPlacement u)
      (hxrel : x ∈ Q.relativeInterior) :
      ∃ y : EuclideanSpace ℝ (Fin 2),
        ∃ OutCut : PolygonalArcPointCutData Cut.suffixArc y,
          y ∈ Q.relativeInterior ∧ y ≠ x ∧
          OutCut.prefixArc.carrier = segment ℝ x y ∧
          (∀ p, p ∈ OutCut.prefixArc.carrier → p ∈ D.crossingSet → p = x) ∧
          Cut.prefixArc.carrier ∩ OutCut.prefixArc.carrier = ({x} : Set _) ∧
          ∀ P : Set (EuclideanSpace ℝ (Fin 2)),
            P ∩ Q.carrier = ({D.vertexPlacement u, x} : Set _) →
              Disjoint P OutCut.suffixArc.carrier := by
    let S := Cut.suffixArc
    have hS0 : S.vertices[0]'(by
        have := S.length_ge_two
        omega) = x := by
      have hlen := S.length_ge_two
      have hhead := S.source_eq_head
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by
        have := S.length_ge_two
        omega)] at hhead
      exact Option.some.inj hhead |>.trans Cut.suffix_source
    have hS01 : 0 + 1 < S.vertices.length := by
      have := S.length_ge_two
      omega
    have hS01ne : S.vertices[0] ≠ S.vertices[1] := by
      intro heq
      have hidx := (S.simple_vertices.getElem_inj_iff
        (i := 0) (j := 1) (hi := by omega) (hj := hS01)).1 heq
      omega
    have chooseShort : ∃ y : EuclideanSpace ℝ (Fin 2),
        y ∈ openSegment ℝ S.vertices[0] S.vertices[1] ∧
          ∀ p, p ∈ segment ℝ S.vertices[0] y →
            p ∈ D.crossingSet → p = x :=
      ordinaryAdjacentEdgesChooseShort G D S x hS01 hS0 hS01ne
    obtain ⟨y, hyOpen0, hshort⟩ := chooseShort
    have hyne : y ≠ x := by
      intro hyx
      have hleft : S.vertices[0] ∈ openSegment ℝ S.vertices[0] S.vertices[1] := by
        simpa [hS0, hyx] using hyOpen0
      exact hS01ne ((left_mem_openSegment_iff (𝕜 := ℝ)).1 hleft)
    obtain ⟨OutCut⟩ :=
      PolygonalArcInteriorPointCutDataExists S 0 hS01 y hyOpen0
    have hOutIndex : OutCut.cutIndex = 0 :=
      (open_index_unique S y 0 OutCut.cutIndex hS01 OutCut.cutIndex_valid
        hyOpen0 OutCut.cut_mem_segment).symm
    have hOutCarrier : OutCut.prefixArc.carrier = segment ℝ x y := by
      rw [OutCut.prefix_carrier_region]
      have hEarlier :
          {z | ∃ i : ℕ, ∃ hi : i + 1 < S.vertices.length,
            i < OutCut.cutIndex ∧ z ∈ segment ℝ S.vertices[i] S.vertices[i + 1]} =
            (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
        ext z
        simp [hOutIndex]
      rw [hEarlier, Set.empty_union]
      simpa only [hOutIndex, hS0]
    have hOutCross : ∀ p, p ∈ OutCut.prefixArc.carrier →
        p ∈ D.crossingSet → p = x := by
      intro p hp hpCross
      apply hshort p
      · rw [hOutCarrier] at hp
        simpa only [hS0] using hp
      · exact hpCross
    have hySrel : y ∈ S.relativeInterior :=
      PolygonalArcOpenSegmentSubsetRelativeInterior S 0 hS01 hyOpen0
    have hyQcarrier : y ∈ Q.carrier :=
      Cut.suffix_carrier_subset ((S.relativeInterior_eq ▸ hySrel).1)
    have hyQsource : y ≠ Q.source := by
      intro hySource
      have hsourcePrefix : Q.source ∈ Cut.prefixArc.carrier := by
        have hs := arc_source_mem Cut.prefixArc
        rw [Cut.prefix_source] at hs
        exact hs
      have hyInter : y ∈ Cut.prefixArc.carrier ∩ S.carrier := by
        refine ⟨hySource ▸ hsourcePrefix, (S.relativeInterior_eq ▸ hySrel).1⟩
      have hyx : y = x := by
        have : y ∈ ({x} : Set _) := Cut.carrier_intersection ▸ hyInter
        simpa using this
      exact hyne hyx
    have hyQtarget : y ≠ Q.target := by
      intro hyTarget
      have hyNotSTarget : y ≠ S.target := by
        rw [S.relativeInterior_eq] at hySrel
        exact fun h => hySrel.2 (by simp [h])
      exact hyNotSTarget (hyTarget.trans Cut.suffix_target.symm)
    have hyQrel : y ∈ Q.relativeInterior := by
      rw [Q.relativeInterior_eq]
      refine ⟨hyQcarrier, ?_⟩
      simp [hyQsource, hyQtarget]
    have hPrefixOut : Cut.prefixArc.carrier ∩ OutCut.prefixArc.carrier =
        ({x} : Set _) := by
      ext z
      constructor
      · intro hz
        have hzS : z ∈ S.carrier :=
          OutCut.prefix_carrier_subset hz.2
        have hzCut : z ∈ Cut.prefixArc.carrier ∩ S.carrier := ⟨hz.1, hzS⟩
        exact Cut.carrier_intersection ▸ hzCut
      · intro hz
        have hzx : z = x := by simpa using hz
        subst z
        constructor
        · have ht := arc_target_mem Cut.prefixArc
          rw [Cut.prefix_target] at ht
          exact ht
        · have hs := arc_source_mem OutCut.prefixArc
          rw [OutCut.prefix_source, Cut.suffix_source] at hs
          exact hs
    refine ⟨y, OutCut, hyQrel, hyne, hOutCarrier, hOutCross, hPrefixOut, ?_⟩
    intro P hPQ
    rw [Set.disjoint_left]
    intro z hzP hzTail
    have hzQ : z ∈ Q.carrier :=
      Cut.suffix_carrier_subset (OutCut.suffix_carrier_subset hzTail)
    have hzPair : z ∈ ({D.vertexPlacement u, x} : Set _) := hPQ ▸ ⟨hzP, hzQ⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzPair
    rcases hzPair with hzu | hzx
    · have huPrefix : D.vertexPlacement u ∈ Cut.prefixArc.carrier := by
        have hs := arc_source_mem Cut.prefixArc
        rw [Cut.prefix_source, hQsource] at hs
        exact hs
      have huS : D.vertexPlacement u ∈ S.carrier :=
        OutCut.suffix_carrier_subset (hzu ▸ hzTail)
      have hux : D.vertexPlacement u = x := by
        have huInter : D.vertexPlacement u ∈ Cut.prefixArc.carrier ∩ S.carrier :=
          ⟨huPrefix, huS⟩
        have : D.vertexPlacement u ∈ ({x} : Set _) :=
          Cut.carrier_intersection ▸ huInter
        simpa using this
      rw [Q.relativeInterior_eq] at hxrel
      exact hxrel.2 (by simp [← hux, hQsource])
    · have hxOutPrefix : x ∈ OutCut.prefixArc.carrier := by
        have hs := arc_source_mem OutCut.prefixArc
        rw [OutCut.prefix_source, Cut.suffix_source] at hs
        exact hs
      have hxInter : x ∈ OutCut.prefixArc.carrier ∩ OutCut.suffixArc.carrier :=
        ⟨hxOutPrefix, hzx ▸ hzTail⟩
      have hxy : x = y := by
        have : x ∈ ({y} : Set _) := OutCut.carrier_intersection ▸ hxInter
        simpa using this
      exact hyne hxy.symm
  obtain ⟨yAlpha, OutAlpha, hyAlphaRel, hyAlphaNe, hOutAlphaCarrier,
      hOutAlphaCross, hBAlphaBplus, hAlphaTail⟩ :=
    outgoing_package (orient beta) xAlpha BetaAtAlpha
      (orient_source beta huBeta) (hXbeta xAlpha hxAlphaX)
  obtain ⟨yBeta, OutBeta, hyBetaRel, hyBetaNe, hOutBetaCarrier,
      hOutBetaCross, hABetaAplus, hBetaTail⟩ :=
    outgoing_package (orient alpha) xBeta AlphaAtBeta
      (orient_source alpha huAlpha) (hXalpha xBeta hxBetaX)
  have hAlphaTailDisjoint :
      Disjoint AlphaCut.prefixArc.carrier OutAlpha.suffixArc.carrier :=
    hAlphaTail AlphaCut.prefixArc.carrier alphaPrefixBeta
  have hBetaTailDisjoint :
      Disjoint BetaCut.prefixArc.carrier OutBeta.suffixArc.carrier :=
    hBetaTail BetaCut.prefixArc.carrier betaPrefixAlpha
  have hAlphaBetaPrefixes :
      AlphaCut.prefixArc.carrier ∩ BetaAtAlpha.prefixArc.carrier =
        ({D.vertexPlacement u, xAlpha} : Set _) := by
    ext z
    constructor
    · intro hz
      have hzWhole : z ∈ AlphaCut.prefixArc.carrier ∩ (orient beta).carrier :=
        ⟨hz.1, BetaAtAlpha.prefix_carrier_subset hz.2⟩
      exact alphaPrefixBeta ▸ hzWhole
    · intro hz
      have hzPair : z = D.vertexPlacement u ∨ z = xAlpha := by simpa using hz
      constructor
      · exact (alphaPrefixBeta ▸ hz).1
      · rcases hzPair with hzu | hzx
        · subst z
          have hs := arc_source_mem BetaAtAlpha.prefixArc
          rw [BetaAtAlpha.prefix_source, orient_source beta huBeta] at hs
          exact hs
        · subst z
          have ht := arc_target_mem BetaAtAlpha.prefixArc
          rw [BetaAtAlpha.prefix_target] at ht
          exact ht
  have hBetaAlphaPrefixes :
      BetaCut.prefixArc.carrier ∩ AlphaAtBeta.prefixArc.carrier =
        ({D.vertexPlacement u, xBeta} : Set _) := by
    ext z
    constructor
    · intro hz
      have hzWhole : z ∈ BetaCut.prefixArc.carrier ∩ (orient alpha).carrier :=
        ⟨hz.1, AlphaAtBeta.prefix_carrier_subset hz.2⟩
      exact betaPrefixAlpha ▸ hzWhole
    · intro hz
      have hzPair : z = D.vertexPlacement u ∨ z = xBeta := by simpa using hz
      constructor
      · exact (betaPrefixAlpha ▸ hz).1
      · rcases hzPair with hzu | hzx
        · subst z
          have hs := arc_source_mem AlphaAtBeta.prefixArc
          rw [AlphaAtBeta.prefix_source, orient_source alpha huAlpha] at hs
          exact hs
        · subst z
          have ht := arc_target_mem AlphaAtBeta.prefixArc
          rw [AlphaAtBeta.prefix_target] at ht
          exact ht
  let third : EuclideanSpace ℝ (Fin 2) → Prop := fun p =>
    ∃ e : G.edgeFinset, e ≠ alpha ∧ e ≠ beta ∧
      p ∈ (D.edgeArc e).relativeInterior
  let contacts : PolygonalArc → Finset (EuclideanSpace ℝ (Fin 2)) := fun P =>
    D.crossingSet.filter (fun p => p ∈ P.carrier ∧ third p)
  have contacts_mono : ∀ P Q : PolygonalArc,
      P.carrier ⊆ Q.carrier → contacts P ⊆ contacts Q := by
    intro P Q hPQ p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hPQ hp.2.1, hp.2.2⟩
  have hAlphaContactsMono :
      contacts AlphaCut.prefixArc ⊆ contacts AlphaAtBeta.prefixArc :=
    contacts_mono _ _ hAlphaPrefixInBeta
  have hBetaContactsMono :
      contacts BetaCut.prefixArc ⊆ contacts BetaAtAlpha.prefixArc :=
    contacts_mono _ _ hBetaPrefixInAlpha
  have hAlphaCardMono :
      (contacts AlphaCut.prefixArc).card ≤
        (contacts AlphaAtBeta.prefixArc).card :=
    Finset.card_le_card hAlphaContactsMono
  have hBetaCardMono :
      (contacts BetaCut.prefixArc).card ≤
        (contacts BetaAtAlpha.prefixArc).card :=
    Finset.card_le_card hBetaContactsMono
  have prefixInterior (e : G.edgeFinset) (Q : PolygonalArc)
      (hQ : Q = orient e) (hu : u ∈ e.1)
      (x : EuclideanSpace ℝ (Fin 2))
      (Cut : PolygonalArcPointCutData Q x)
      (p : EuclideanSpace ℝ (Fin 2))
      (hp : p ∈ Cut.prefixArc.carrier)
      (hpu : p ≠ D.vertexPlacement u) (hpx : p ≠ x) :
      p ∈ (D.edgeArc e).relativeInterior := by
    have hpTarget : p ≠ Q.target := by
      intro hpT
      have htargetSuffix : Q.target ∈ Cut.suffixArc.carrier := by
        have ht := arc_target_mem Cut.suffixArc
        rw [Cut.suffix_target] at ht
        exact ht
      have hpInter : p ∈ Cut.prefixArc.carrier ∩ Cut.suffixArc.carrier :=
        ⟨hp, hpT ▸ htargetSuffix⟩
      have hpx' : p = x := by
        have : p ∈ ({x} : Set _) := Cut.carrier_intersection ▸ hpInter
        simpa using this
      exact hpx hpx'
    have hpQrel : p ∈ Q.relativeInterior := by
      rw [Q.relativeInterior_eq]
      refine ⟨Cut.prefix_carrier_subset hp, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro hpSource
        apply hpu
        have hsource : Q.source = D.vertexPlacement u := by
          rw [hQ]
          exact orient_source e hu
        exact hpSource.trans hsource
      · exact hpTarget
    subst Q
    simpa only [orient_relative e] using hpQrel
  have contacts_spec (e : G.edgeFinset) (hu : u ∈ e.1)
      (he : e = alpha ∨ e = beta)
      (x : EuclideanSpace ℝ (Fin 2))
      (hxA : x ∈ (D.edgeArc alpha).relativeInterior)
      (hxB : x ∈ (D.edgeArc beta).relativeInterior)
      (Cut : PolygonalArcPointCutData (orient e) x) :
      ∀ p, p ∈ contacts Cut.prefixArc ↔
        p ∈ Cut.prefixArc.carrier \
            ({D.vertexPlacement u, x} : Set _) ∧ third p := by
    intro p
    constructor
    · intro hp
      rw [Finset.mem_filter] at hp
      rcases hp.2.2 with ⟨f, hfA, hfB, hpf⟩
      have hpu : p ≠ D.vertexPlacement u := by
        intro h
        exact D.no_vertex_in_edge_interior u f (h ▸ hpf)
      have hpx : p ≠ x := by
        intro h
        exact D.no_three_edge_interiors_meet hab hfA.symm hfB.symm
          hxA hxB (h ▸ hpf)
      exact ⟨⟨hp.2.1, by simp [hpu, hpx]⟩, ⟨f, hfA, hfB, hpf⟩⟩
    · rintro ⟨⟨hpPrefix, hpEnds⟩, hpThird⟩
      have hpne : p ≠ D.vertexPlacement u ∧ p ≠ x := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hpEnds
      rcases hpThird with ⟨f, hfA, hfB, hpf⟩
      have hpe : p ∈ (D.edgeArc e).relativeInterior :=
        prefixInterior e (orient e) rfl hu x Cut p hpPrefix hpne.1 hpne.2
      have hef : e ≠ f := by
        rcases he with rfl | rfl
        · exact hfA.symm
        · exact hfB.symm
      apply Finset.mem_filter.mpr
      exact ⟨(D.crossingSet_spec p).2 ⟨e, f, hef, hpe, hpf⟩,
        hpPrefix, ⟨f, hfA, hfB, hpf⟩⟩
  have hAlphaFirstSpec := contacts_spec alpha huAlpha (Or.inl rfl) xAlpha
    (Finset.mem_filter.mp hxAlphaX).2.1 (Finset.mem_filter.mp hxAlphaX).2.2
    AlphaCut
  have hBetaAtAlphaSpec := contacts_spec beta huBeta (Or.inr rfl) xAlpha
    (Finset.mem_filter.mp hxAlphaX).2.1 (Finset.mem_filter.mp hxAlphaX).2.2
    BetaAtAlpha
  have hBetaFirstSpec := contacts_spec beta huBeta (Or.inr rfl) xBeta
    (Finset.mem_filter.mp hxBetaX).2.1 (Finset.mem_filter.mp hxBetaX).2.2
    BetaCut
  have hAlphaAtBetaSpec := contacts_spec alpha huAlpha (Or.inl rfl) xBeta
    (Finset.mem_filter.mp hxBetaX).2.1 (Finset.mem_filter.mp hxBetaX).2.2
    AlphaAtBeta
  have geometry_package
      (firstEdge secondEdge : G.edgeFinset)
      (hpair : (firstEdge = alpha ∧ secondEdge = beta) ∨
        (firstEdge = beta ∧ secondEdge = alpha))
      (huFirst : u ∈ firstEdge.1) (huSecond : u ∈ secondEdge.1)
      (x y : EuclideanSpace ℝ (Fin 2))
      (FirstCut : PolygonalArcPointCutData (orient firstEdge) x)
      (SecondCut : PolygonalArcPointCutData (orient secondEdge) x)
      (OutCut : PolygonalArcPointCutData SecondCut.suffixArc y)
      (hxA : x ∈ (D.edgeArc alpha).relativeInterior)
      (hxB : x ∈ (D.edgeArc beta).relativeInterior)
      (hySecond : y ∈ (D.edgeArc secondEdge).relativeInterior)
      (hFirstWhole : FirstCut.prefixArc.carrier ∩
        (orient secondEdge).carrier = ({D.vertexPlacement u, x} : Set _))
      (hOutCarrier : OutCut.prefixArc.carrier = segment ℝ x y)
      (hOutCross : ∀ p, p ∈ OutCut.prefixArc.carrier →
        p ∈ D.crossingSet → p = x)
      (XAcopy XBremoved : Finset (EuclideanSpace ℝ (Fin 2)))
      (hXAcopy : ∀ p, p ∈ XAcopy ↔
        p ∈ FirstCut.prefixArc.carrier \
            ({D.vertexPlacement u, x} : Set _) ∧
          ∃ e : G.edgeFinset,
            e ≠ firstEdge ∧ e ≠ secondEdge ∧
              p ∈ (D.edgeArc e).relativeInterior)
      (hXBremoved : ∀ p, p ∈ XBremoved ↔
        p ∈ SecondCut.prefixArc.carrier \
            ({D.vertexPlacement u, x} : Set _) ∧
          ∃ e : G.edgeFinset,
            e ≠ firstEdge ∧ e ≠ secondEdge ∧
              p ∈ (D.edgeArc e).relativeInterior)
      (hcount : XAcopy.card ≤ XBremoved.card) :
      ∃ A B Bplus Rbeta H : Set (EuclideanSpace ℝ (Fin 2)),
        A = FirstCut.prefixArc.carrier ∧
        B = SecondCut.prefixArc.carrier ∧
        Bplus = OutCut.prefixArc.carrier ∧
        Rbeta = (D.edgeArc secondEdge).carrier \
          ((B ∪ Bplus) \ ({y} : Set _)) ∧
        H =
          (⋃ edge : G.edgeFinset,
            if edge = firstEdge then
              (D.edgeArc edge).carrier \
                (A \ ({D.vertexPlacement u, x} : Set _))
            else if edge = secondEdge then
              (D.edgeArc edge).carrier \
                ((B \ ({D.vertexPlacement u, x} : Set _)) ∪
                  (Bplus \ ({x, y} : Set _)))
            else (D.edgeArc edge).carrier) ∪
          {p | ∃ v : V, v ≠ u ∧ p = D.vertexPlacement v} ∧
        ∃ Tail : BigonRerouteOrderedBetaTailData
            G D secondEdge u y B Bplus Rbeta H,
          (∀ p, p ∈ Bplus → p ∈ D.crossingSet → p = x) ∧
          (∀ v : V, D.vertexPlacement v ∈ Bplus → False) ∧
          ∃ XAexact XBexact : Finset (EuclideanSpace ℝ (Fin 2)),
            XAexact = XAcopy ∧ XBremoved ⊆ XBexact ∧
            (∀ p, p ∈ XAexact ↔
              p ∈ A \ ({D.vertexPlacement u, x} : Set _) ∧ p ∈ H) ∧
            (∀ p, p ∈ XBexact ↔
              p ∈ B \ ({D.vertexPlacement u, x} : Set _) ∧ p ∈ H) ∧
            XAexact.card ≤ XBexact.card := by
    have hEdgesNe : firstEdge ≠ secondEdge := by
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab
      · exact hab.symm
    have arc_ends_ne (Q : PolygonalArc) : Q.source ≠ Q.target := by
      intro h
      have hlen := Q.length_ge_two
      have hzero : Q.vertices[0] = Q.source := by
        have hh := Q.source_eq_head
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
        exact Option.some.inj hh
      have hlast : Q.vertices[Q.vertices.length - 1] = Q.target := by
        have ht := Q.target_eq_last
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at ht
        exact Option.some.inj ht
      have hidx := (Q.simple_vertices.getElem_inj_iff
        (i := 0) (j := Q.vertices.length - 1)
        (hi := by omega) (hj := by omega)).1 (by rw [hzero, hlast, h])
      omega
    have hxy : x ≠ y := by
      intro h
      apply arc_ends_ne OutCut.prefixArc
      rw [OutCut.prefix_source, OutCut.prefix_target, SecondCut.suffix_source, h]
    let A : Set (EuclideanSpace ℝ (Fin 2)) := FirstCut.prefixArc.carrier
    let B : Set (EuclideanSpace ℝ (Fin 2)) := SecondCut.prefixArc.carrier
    let Bplus : Set (EuclideanSpace ℝ (Fin 2)) := OutCut.prefixArc.carrier
    let Rbeta : Set (EuclideanSpace ℝ (Fin 2)) := OutCut.suffixArc.carrier
    let H : Set (EuclideanSpace ℝ (Fin 2)) :=
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
    have hxBplus : x ∈ Bplus := by
      dsimp [Bplus]
      have hs := arc_source_mem OutCut.prefixArc
      rw [OutCut.prefix_source, SecondCut.suffix_source] at hs
      exact hs
    have hyBplus : y ∈ Bplus := by
      dsimp [Bplus]
      have ht := arc_target_mem OutCut.prefixArc
      rw [OutCut.prefix_target] at ht
      exact ht
    have hyTail : y ∈ Rbeta := by
      dsimp [Rbeta]
      have hs := arc_source_mem OutCut.suffixArc
      rw [OutCut.suffix_source] at hs
      exact hs
    have hxNotTail : x ∉ Rbeta := by
      intro hxTail
      have hxInter : x ∈ OutCut.prefixArc.carrier ∩ OutCut.suffixArc.carrier :=
        ⟨hxBplus, hxTail⟩
      have : x ∈ ({y} : Set _) := OutCut.carrier_intersection ▸ hxInter
      exact hxy (by simpa using this)
    have hyNotB : y ∉ B := by
      intro hyB
      have hySuffix : y ∈ SecondCut.suffixArc.carrier :=
        OutCut.prefix_carrier_subset hyBplus
      have hyInter : y ∈ SecondCut.prefixArc.carrier ∩
          SecondCut.suffixArc.carrier := ⟨hyB, hySuffix⟩
      have : y ∈ ({x} : Set _) := SecondCut.carrier_intersection ▸ hyInter
      have hyx : y = x := by simpa using this
      exact hxy hyx.symm
    have hTailOld : Rbeta ⊆ (D.edgeArc secondEdge).carrier := by
      intro p hp
      have hpOrient : p ∈ (orient secondEdge).carrier :=
        SecondCut.suffix_carrier_subset (OutCut.suffix_carrier_subset hp)
      rw [orient_carrier secondEdge] at hpOrient
      exact hpOrient
    have hRbetaExact :
        Rbeta = (D.edgeArc secondEdge).carrier \
          ((B ∪ Bplus) \ ({y} : Set _)) := by
      ext p
      constructor
      · intro hp
        refine ⟨hTailOld hp, ?_⟩
        rintro ⟨hpB | hpBplus, hpy⟩
        · have hpSuffix : p ∈ SecondCut.suffixArc.carrier :=
            OutCut.suffix_carrier_subset hp
          have hpInter : p ∈ SecondCut.prefixArc.carrier ∩
              SecondCut.suffixArc.carrier := ⟨hpB, hpSuffix⟩
          have hpx : p = x := by
            have : p ∈ ({x} : Set _) := SecondCut.carrier_intersection ▸ hpInter
            simpa using this
          exact hxNotTail (hpx ▸ hp)
        · have hpInter : p ∈ OutCut.prefixArc.carrier ∩
              OutCut.suffixArc.carrier := ⟨hpBplus, hp⟩
          have hpy' : p = y := by
            have : p ∈ ({y} : Set _) := OutCut.carrier_intersection ▸ hpInter
            simpa using this
          exact hpy (by simp [hpy'])
      · rintro ⟨hpOld, hpNotRemoved⟩
        have hpOrient : p ∈ (orient secondEdge).carrier := by
          rw [orient_carrier secondEdge]
          exact hpOld
        rw [SecondCut.carrier_decomposition] at hpOrient
        rcases hpOrient with hpB | hpSuffix
        · exfalso
          apply hpNotRemoved
          refine ⟨Or.inl hpB, ?_⟩
          intro hpy
          have : p = y := by simpa using hpy
          exact hyNotB (this ▸ hpB)
        · rw [OutCut.carrier_decomposition] at hpSuffix
          rcases hpSuffix with hpBplus | hpTail
          · by_cases hpy : p = y
            · simpa [hpy] using hyTail
            · exfalso
              exact hpNotRemoved ⟨Or.inr hpBplus, by simpa using hpy⟩
          · exact hpTail
    have hTailRelative : OutCut.suffixArc.relativeInterior ⊆
        (D.edgeArc secondEdge).relativeInterior := by
      intro p hp
      rw [(D.edgeArc secondEdge).relativeInterior_eq]
      refine ⟨hTailOld ((OutCut.suffixArc.relativeInterior_eq ▸ hp).1), ?_⟩
      have hpOrientTarget : p ≠ (orient secondEdge).target := by
        intro hpt
        rw [OutCut.suffixArc.relativeInterior_eq] at hp
        apply hp.2
        right
        rw [OutCut.suffix_target, SecondCut.suffix_target]
        exact hpt
      have hpOrientSource : p ≠ (orient secondEdge).source := by
        intro hps
        have huB : (orient secondEdge).source ∈ SecondCut.prefixArc.carrier := by
          have hs := arc_source_mem SecondCut.prefixArc
          rw [SecondCut.prefix_source] at hs
          exact hs
        have hpSuffix : p ∈ SecondCut.suffixArc.carrier :=
          OutCut.suffix_carrier_subset ((OutCut.suffixArc.relativeInterior_eq ▸ hp).1)
        have hpInter : p ∈ SecondCut.prefixArc.carrier ∩
            SecondCut.suffixArc.carrier := ⟨hps ▸ huB, hpSuffix⟩
        have hpx : p = x := by
          have : p ∈ ({x} : Set _) := SecondCut.carrier_intersection ▸ hpInter
          simpa using this
        exact hxNotTail (hpx ▸ ((OutCut.suffixArc.relativeInterior_eq ▸ hp).1))
      by_cases hs : (D.edgeArc secondEdge).source = D.vertexPlacement u
      · simp only [orient, if_pos hs] at hpOrientSource hpOrientTarget
        simpa [hpOrientSource, hpOrientTarget]
      · simp only [orient, if_neg hs, PolygonalArcReverse] at hpOrientSource hpOrientTarget
        simpa [hpOrientSource, hpOrientTarget, and_comm]
    have hTailRemoved : OutCut.suffixArc.carrier ∩ (B ∪ Bplus) =
        ({y} : Set _) := by
      ext p
      constructor
      · rintro ⟨hpTail, hpB | hpBplus⟩
        · have hpSuffix := OutCut.suffix_carrier_subset hpTail
          have hpInter : p ∈ SecondCut.prefixArc.carrier ∩
              SecondCut.suffixArc.carrier := ⟨hpB, hpSuffix⟩
          have hpx : p = x := by
            have : p ∈ ({x} : Set _) := SecondCut.carrier_intersection ▸ hpInter
            simpa using this
          exact (hxNotTail (hpx ▸ hpTail)).elim
        · have hpInter : p ∈ OutCut.prefixArc.carrier ∩
              OutCut.suffixArc.carrier := ⟨hpBplus, hpTail⟩
          exact OutCut.carrier_intersection ▸ hpInter
      · intro hp
        have hpy : p = y := by simpa using hp
        subst p
        exact ⟨hyTail, Or.inr hyBplus⟩
    have hTailH : OutCut.suffixArc.carrier ⊆ H := by
      intro p hpTail
      left
      apply Set.mem_iUnion.mpr
      refine ⟨secondEdge, ?_⟩
      rw [if_neg hEdgesNe.symm, if_pos rfl]
      refine ⟨hTailOld hpTail, ?_⟩
      rintro (hpB | hpBplus)
      · have hpSuffix := OutCut.suffix_carrier_subset hpTail
        have hpInter : p ∈ SecondCut.prefixArc.carrier ∩
            SecondCut.suffixArc.carrier := ⟨hpB.1, hpSuffix⟩
        have hpx : p = x := by
          have : p ∈ ({x} : Set _) := SecondCut.carrier_intersection ▸ hpInter
          simpa using this
        exact hpB.2 (by simp [hpx])
      · have hpInter : p ∈ OutCut.prefixArc.carrier ∩
            OutCut.suffixArc.carrier := ⟨hpBplus.1, hpTail⟩
        have hpy : p = y := by
          have : p ∈ ({y} : Set _) := OutCut.carrier_intersection ▸ hpInter
          simpa using this
        exact hpBplus.2 (by simp [hpy])
    have orient_target_data (e : G.edgeFinset) :
        ∃ v : V, v ∈ e.1 ∧ (orient e).target = D.vertexPlacement v := by
      rcases D.edgeArc_endpoints e with ⟨a, b, _hadj, he, hends⟩
      dsimp [orient]
      by_cases hs : (D.edgeArc e).source = D.vertexPlacement u
      · simp only [if_pos hs]
        rcases hends with hends | hends
        · refine ⟨b, ?_, hends.2⟩
          rw [he]
          simp [Sym2.mem_iff']
        · refine ⟨a, ?_, hends.2⟩
          rw [he]
          simp [Sym2.mem_iff']
      · simp only [if_neg hs, PolygonalArcReverse]
        rcases hends with hends | hends
        · refine ⟨a, ?_, hends.1⟩
          rw [he]
          simp [Sym2.mem_iff']
        · refine ⟨b, ?_, hends.1⟩
          rw [he]
          simp [Sym2.mem_iff']
    obtain ⟨far, hfarMem, hOrientTarget⟩ := orient_target_data secondEdge
    have hfarNe : far ≠ u := by
      intro h
      apply arc_ends_ne (orient secondEdge)
      rw [orient_source secondEdge huSecond, hOrientTarget, h]
    have hTailTarget : OutCut.suffixArc.target = D.vertexPlacement far := by
      rw [OutCut.suffix_target, SecondCut.suffix_target, hOrientTarget]
    have hOldOrientation :
        ((D.edgeArc secondEdge).source = D.vertexPlacement u →
            OutCut.suffixArc.target = (D.edgeArc secondEdge).target) ∧
          ((D.edgeArc secondEdge).target = D.vertexPlacement u →
            OutCut.suffixArc.target = (D.edgeArc secondEdge).source) := by
      constructor
      · intro hs
        have hOrient : orient secondEdge = D.edgeArc secondEdge := by
          simp [orient, hs]
        rw [OutCut.suffix_target, SecondCut.suffix_target, hOrient]
      · intro ht
        have hsne : (D.edgeArc secondEdge).source ≠ D.vertexPlacement u := by
          intro hs
          exact arc_ends_ne (D.edgeArc secondEdge) (hs.trans ht.symm)
        have hOrient : (orient secondEdge).target =
            (D.edgeArc secondEdge).source := by
          simp [orient, hsne, PolygonalArcReverse]
        rw [OutCut.suffix_target, SecondCut.suffix_target, hOrient]
    let Tail : BigonRerouteOrderedBetaTailData
        G D secondEdge u y B Bplus Rbeta H :=
      { tailArc := OutCut.suffixArc
        farEndpoint := far
        u_mem_beta := huSecond
        farEndpoint_mem_beta := hfarMem
        farEndpoint_ne_u := hfarNe
        source_eq := OutCut.suffix_source
        target_eq := hTailTarget
        carrier_eq := rfl
        carrier_subset_old_beta := hTailOld
        relativeInterior_subset_old_beta := hTailRelative
        meets_removed_subarc := hTailRemoved
        carrier_subset_H := hTailH
        old_orientation_compatible := hOldOrientation }
    have hxFirst : x ∈ (D.edgeArc firstEdge).relativeInterior := by
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxA
      · exact hxB
    have hxSecond : x ∈ (D.edgeArc secondEdge).relativeInterior := by
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxB
      · exact hxA
    have hBplusNoVertex : ∀ v : V,
        D.vertexPlacement v ∈ Bplus → False := by
      intro v hv
      have hvOrient : D.vertexPlacement v ∈ (orient secondEdge).carrier :=
        SecondCut.suffix_carrier_subset (OutCut.prefix_carrier_subset hv)
      have hvSource : D.vertexPlacement v ≠ (orient secondEdge).source := by
        intro hs
        have hvPrefix : D.vertexPlacement v ∈ SecondCut.prefixArc.carrier := by
          have hs' := arc_source_mem SecondCut.prefixArc
          rw [SecondCut.prefix_source] at hs'
          simpa [hs] using hs'
        have hvSuffix : D.vertexPlacement v ∈ SecondCut.suffixArc.carrier :=
          OutCut.prefix_carrier_subset hv
        have hvInter : D.vertexPlacement v ∈ SecondCut.prefixArc.carrier ∩
            SecondCut.suffixArc.carrier := ⟨hvPrefix, hvSuffix⟩
        have hvx : D.vertexPlacement v = x := by
          have : D.vertexPlacement v ∈ ({x} : Set _) :=
            SecondCut.carrier_intersection ▸ hvInter
          simpa using this
        exact D.no_vertex_in_edge_interior v secondEdge (hvx ▸ hxSecond)
      have hvTarget : D.vertexPlacement v ≠ (orient secondEdge).target := by
        intro ht
        have hvOutTail : D.vertexPlacement v ∈
            OutCut.prefixArc.carrier ∩ OutCut.suffixArc.carrier := by
          refine ⟨hv, ?_⟩
          have htargetTail := arc_target_mem OutCut.suffixArc
          rw [OutCut.suffix_target, SecondCut.suffix_target] at htargetTail
          simpa [ht] using htargetTail
        have hvy : D.vertexPlacement v = y := by
          have : D.vertexPlacement v ∈ ({y} : Set _) :=
            OutCut.carrier_intersection ▸ hvOutTail
          simpa using this
        exact D.no_vertex_in_edge_interior v secondEdge (hvy ▸ hySecond)
      have hvRel : D.vertexPlacement v ∈ (orient secondEdge).relativeInterior := by
        rw [(orient secondEdge).relativeInterior_eq]
        exact ⟨hvOrient, by simp [hvSource, hvTarget]⟩
      rw [orient_relative secondEdge] at hvRel
      exact D.no_vertex_in_edge_interior v secondEdge hvRel
    have carrierRelativeOfNotVertex (p : EuclideanSpace ℝ (Fin 2))
        (hpNotVertex : ∀ v : V, p ≠ D.vertexPlacement v)
        (e : G.edgeFinset) (hp : p ∈ (D.edgeArc e).carrier) :
        p ∈ (D.edgeArc e).relativeInterior := by
      rw [(D.edgeArc e).relativeInterior_eq]
      refine ⟨hp, ?_⟩
      rcases D.edgeArc_endpoints e with ⟨a, b, _hab, _he, hends⟩
      rcases hends with hends | hends
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun h => hpNotVertex a (h.trans hends.1),
          fun h => hpNotVertex b (h.trans hends.2)⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun h => hpNotVertex b (h.trans hends.1),
          fun h => hpNotVertex a (h.trans hends.2)⟩
    have firstContactThird : ∀ p,
        p ∈ A \ ({D.vertexPlacement u, x} : Set _) →
          (p ∈ H ↔
            ∃ e : G.edgeFinset,
              e ≠ firstEdge ∧ e ≠ secondEdge ∧
                p ∈ (D.edgeArc e).relativeInterior) := by
      intro p hpA
      have hpEnds : p ≠ D.vertexPlacement u ∧ p ≠ x := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hpA.2
      have hpFirst : p ∈ (D.edgeArc firstEdge).relativeInterior :=
        prefixInterior firstEdge (orient firstEdge) rfl huFirst x FirstCut p
          hpA.1 hpEnds.1 hpEnds.2
      have hpNotVertex : ∀ v : V, p ≠ D.vertexPlacement v := by
        intro v h
        exact D.no_vertex_in_edge_interior v firstEdge (h ▸ hpFirst)
      constructor
      · intro hpH
        rcases hpH with hpEdges | hpVertex
        · rcases Set.mem_iUnion.mp hpEdges with ⟨e, hpe⟩
          by_cases heFirst : e = firstEdge
          · subst e
            rw [if_pos rfl] at hpe
            exact (hpe.2 hpA).elim
          · rw [if_neg heFirst] at hpe
            by_cases heSecond : e = secondEdge
            · subst e
              rw [if_pos rfl] at hpe
              have hpOrientSecond : p ∈ (orient secondEdge).carrier := by
                rw [orient_carrier secondEdge]
                exact hpe.1
              have hpPair : p ∈ ({D.vertexPlacement u, x} : Set _) :=
                hFirstWhole ▸ ⟨hpA.1, hpOrientSecond⟩
              exact (hpA.2 hpPair).elim
            · rw [if_neg heSecond] at hpe
              exact ⟨e, heFirst, heSecond,
                carrierRelativeOfNotVertex p hpNotVertex e hpe⟩
        · rcases hpVertex with ⟨v, _hv, hpv⟩
          exact (hpNotVertex v hpv).elim
      · rintro ⟨e, heFirst, heSecond, hpe⟩
        left
        apply Set.mem_iUnion.mpr
        refine ⟨e, ?_⟩
        rw [if_neg heFirst, if_neg heSecond]
        exact (D.edgeArc e).relativeInterior_eq ▸ hpe |>.1
    let XBexact : Finset (EuclideanSpace ℝ (Fin 2)) :=
      D.crossingSet.filter (fun p =>
        p ∈ B \ ({D.vertexPlacement u, x} : Set _) ∧ p ∈ H)
    have secondContactCrossing : ∀ p,
        p ∈ B \ ({D.vertexPlacement u, x} : Set _) →
          p ∈ H → p ∈ D.crossingSet := by
      intro p hpB hpH
      have hpEnds : p ≠ D.vertexPlacement u ∧ p ≠ x := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hpB.2
      have hpSecond : p ∈ (D.edgeArc secondEdge).relativeInterior :=
        prefixInterior secondEdge (orient secondEdge) rfl huSecond x SecondCut p
          hpB.1 hpEnds.1 hpEnds.2
      have hpNotVertex : ∀ v : V, p ≠ D.vertexPlacement v := by
        intro v h
        exact D.no_vertex_in_edge_interior v secondEdge (h ▸ hpSecond)
      rcases hpH with hpEdges | hpVertex
      · rcases Set.mem_iUnion.mp hpEdges with ⟨e, hpe⟩
        by_cases heFirst : e = firstEdge
        · subst e
          rw [if_pos rfl] at hpe
          have hpFirst : p ∈ (D.edgeArc firstEdge).relativeInterior :=
            carrierRelativeOfNotVertex p hpNotVertex firstEdge hpe.1
          exact (D.crossingSet_spec p).2
            ⟨secondEdge, firstEdge, hEdgesNe.symm, hpSecond, hpFirst⟩
        · rw [if_neg heFirst] at hpe
          by_cases heSecond : e = secondEdge
          · subst e
            rw [if_pos rfl] at hpe
            exact (hpe.2 (Or.inl hpB)).elim
          · rw [if_neg heSecond] at hpe
            have hpOther : p ∈ (D.edgeArc e).relativeInterior :=
              carrierRelativeOfNotVertex p hpNotVertex e hpe
            exact (D.crossingSet_spec p).2
              ⟨secondEdge, e, Ne.symm heSecond, hpSecond, hpOther⟩
      · rcases hpVertex with ⟨v, _hv, hpv⟩
        exact (hpNotVertex v hpv).elim
    have hXBexactSpec : ∀ p, p ∈ XBexact ↔
        p ∈ B \ ({D.vertexPlacement u, x} : Set _) ∧ p ∈ H := by
      intro p
      rw [Finset.mem_filter]
      constructor
      · exact fun hp => hp.2
      · intro hp
        exact ⟨secondContactCrossing p hp.1 hp.2, hp⟩
    have hXBsubset : XBremoved ⊆ XBexact := by
      intro p hp
      rcases (hXBremoved p).1 hp with ⟨hpB, e, heFirst, heSecond, hpe⟩
      apply (hXBexactSpec p).2
      refine ⟨hpB, ?_⟩
      left
      apply Set.mem_iUnion.mpr
      refine ⟨e, ?_⟩
      rw [if_neg heFirst, if_neg heSecond]
      exact ((D.edgeArc e).relativeInterior_eq ▸ hpe).1
    have hXAexactSpec : ∀ p, p ∈ XAcopy ↔
        p ∈ A \ ({D.vertexPlacement u, x} : Set _) ∧ p ∈ H := by
      intro p
      rw [hXAcopy p]
      constructor
      · rintro ⟨hpA, hpThird⟩
        exact ⟨hpA, (firstContactThird p hpA).2 hpThird⟩
      · rintro ⟨hpA, hpH⟩
        exact ⟨hpA, (firstContactThird p hpA).1 hpH⟩
    have hFinalCount : XAcopy.card ≤ XBexact.card :=
      le_trans hcount (Finset.card_le_card hXBsubset)
    refine ⟨A, B, Bplus, Rbeta, H, rfl, rfl, rfl, hRbetaExact, rfl,
      Tail, ?_, hBplusNoVertex, XAcopy, XBexact, rfl, hXBsubset,
      hXAexactSpec, hXBexactSpec, hFinalCount⟩
    intro p hpBplus hpCross
    exact hOutCross p hpBplus hpCross
  by_cases hFavorableAlpha :
      (contacts AlphaCut.prefixArc).card ≤
        (contacts BetaAtAlpha.prefixArc).card
  · refine ⟨alpha, beta, Or.inl ⟨rfl, rfl⟩, orient alpha, orient beta,
      orient_carrier alpha, orient_relative alpha, orient_source alpha huAlpha,
      orient_carrier beta, orient_relative beta, orient_source beta huBeta,
      xAlpha, yAlpha, AlphaCut, BetaAtAlpha, OutAlpha, ?_, ?_, ?_, ?_,
      hyAlphaNe, hOutAlphaCarrier, hAlphaBetaPrefixes, hBAlphaBplus,
      hAlphaTailDisjoint,
      contacts AlphaCut.prefixArc, contacts BetaAtAlpha.prefixArc,
      hAlphaFirstSpec, hBetaAtAlphaSpec, ⟨hFavorableAlpha, ?_⟩⟩
    · exact (Finset.mem_filter.mp hxAlphaX).1
    · exact (Finset.mem_filter.mp hxAlphaX).2.1
    · exact (Finset.mem_filter.mp hxAlphaX).2.2
    · simpa only [orient_relative beta] using hyAlphaRel
    · exact geometry_package alpha beta (Or.inl ⟨rfl, rfl⟩) huAlpha huBeta
        xAlpha yAlpha AlphaCut BetaAtAlpha OutAlpha
        (Finset.mem_filter.mp hxAlphaX).2.1
        (Finset.mem_filter.mp hxAlphaX).2.2
        (by simpa only [orient_relative beta] using hyAlphaRel)
        alphaPrefixBeta hOutAlphaCarrier hOutAlphaCross
        (contacts AlphaCut.prefixArc) (contacts BetaAtAlpha.prefixArc)
        hAlphaFirstSpec hBetaAtAlphaSpec hFavorableAlpha
  · have hFavorableBeta :
        (contacts BetaCut.prefixArc).card ≤
          (contacts AlphaAtBeta.prefixArc).card := by
      by_contra hnot
      push Not at hFavorableAlpha hnot
      omega
    refine ⟨beta, alpha, Or.inr ⟨rfl, rfl⟩, orient beta, orient alpha,
      orient_carrier beta, orient_relative beta, orient_source beta huBeta,
      orient_carrier alpha, orient_relative alpha, orient_source alpha huAlpha,
      xBeta, yBeta, BetaCut, AlphaAtBeta, OutBeta, ?_, ?_, ?_, ?_,
      hyBetaNe, hOutBetaCarrier, hBetaAlphaPrefixes, hABetaAplus,
      hBetaTailDisjoint,
      contacts BetaCut.prefixArc, contacts AlphaAtBeta.prefixArc,
      ?_, ?_, ⟨hFavorableBeta, ?_⟩⟩
    · exact (Finset.mem_filter.mp hxBetaX).1
    · exact (Finset.mem_filter.mp hxBetaX).2.2
    · exact (Finset.mem_filter.mp hxBetaX).2.1
    · simpa only [orient_relative alpha] using hyBetaRel
    · intro p
      constructor
      · intro hp
        rcases (hBetaFirstSpec p).1 hp with ⟨hpPrefix, f, hfA, hfB, hpf⟩
        exact ⟨hpPrefix, f, hfB, hfA, hpf⟩
      · rintro ⟨hpPrefix, f, hfB, hfA, hpf⟩
        exact (hBetaFirstSpec p).2 ⟨hpPrefix, f, hfA, hfB, hpf⟩
    · intro p
      constructor
      · intro hp
        rcases (hAlphaAtBetaSpec p).1 hp with ⟨hpPrefix, f, hfA, hfB, hpf⟩
        exact ⟨hpPrefix, f, hfB, hfA, hpf⟩
      · rintro ⟨hpPrefix, f, hfB, hfA, hpf⟩
        exact (hAlphaAtBetaSpec p).2 ⟨hpPrefix, f, hfA, hfB, hpf⟩
    · apply geometry_package beta alpha (Or.inr ⟨rfl, rfl⟩) huBeta huAlpha
        xBeta yBeta BetaCut AlphaAtBeta OutBeta
        (Finset.mem_filter.mp hxBetaX).2.1
        (Finset.mem_filter.mp hxBetaX).2.2
        (by simpa only [orient_relative alpha] using hyBetaRel)
        betaPrefixAlpha hOutBetaCarrier hOutBetaCross
        (contacts BetaCut.prefixArc) (contacts AlphaAtBeta.prefixArc)
      · intro p
        constructor
        · intro hp
          rcases (hBetaFirstSpec p).1 hp with ⟨hpPrefix, f, hfA, hfB, hpf⟩
          exact ⟨hpPrefix, f, hfB, hfA, hpf⟩
        · rintro ⟨hpPrefix, f, hfB, hfA, hpf⟩
          exact (hBetaFirstSpec p).2 ⟨hpPrefix, f, hfA, hfB, hpf⟩
      · intro p
        constructor
        · intro hp
          rcases (hAlphaAtBetaSpec p).1 hp with ⟨hpPrefix, f, hfA, hfB, hpf⟩
          exact ⟨hpPrefix, f, hfB, hfA, hpf⟩
        · rintro ⟨hpPrefix, f, hfB, hfA, hpf⟩
          exact (hAlphaAtBetaSpec p).2 ⟨hpPrefix, f, hfA, hfB, hpf⟩
      · exact hFavorableBeta
