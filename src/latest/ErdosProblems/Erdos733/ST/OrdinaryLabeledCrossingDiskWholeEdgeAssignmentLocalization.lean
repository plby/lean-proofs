import ErdosProblems.Erdos733.ST.OrdinaryLabeledCrossingDiskFiniteEdgeSubstitution
open Classical
noncomputable section

private lemma wholeEdgeFillingTransfer
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (F : OrdinaryLabeledCrossingDiskFamily G D)
    (L : OrdinaryLabeledCrossingDiskFillingFamily G D F)
    (edgeArc' : G.edgeFinset → PolygonalArc)
    (hOwnedTransfer : ∀ e, ∀ x ∈
      Finset.univ.filter (fun y : {p // p ∈ D.crossingSet} =>
        (F.disk y).firstEdge = e ∨ (F.disk y).secondEdge = e),
      ∀ z m
        (hm : m + 1 < (L.fillingArc x
          (if (F.disk x).firstEdge = e then 0 else 1)).vertices.length),
        z ∈ openSegment ℝ
          (L.fillingArc x
            (if (F.disk x).firstEdge = e then 0 else 1)).vertices[m]
          (L.fillingArc x
            (if (F.disk x).firstEdge = e then 0 else 1)).vertices[m + 1] →
        ∃ j : ℕ, ∃ hj : j + 1 < (edgeArc' e).vertices.length,
          z ∈ openSegment ℝ (edgeArc' e).vertices[j]
              (edgeArc' e).vertices[j + 1] ∧
            ∃ c : ℝ, c ≠ 0 ∧
              (edgeArc' e).vertices[j + 1] - (edgeArc' e).vertices[j] =
                c • ((L.fillingArc x
                  (if (F.disk x).firstEdge = e then 0 else 1)).vertices[m + 1] -
                  (L.fillingArc x
                    (if (F.disk x).firstEdge = e then 0 else 1)).vertices[m])) :
    ∀ x i z m (hm : m + 1 < (L.fillingArc x i).vertices.length),
      z ∈ openSegment ℝ (L.fillingArc x i).vertices[m]
          (L.fillingArc x i).vertices[m + 1] →
        ∃ j : ℕ, ∃ hj : j + 1 < (edgeArc' (L.ownerEdge x i)).vertices.length,
          z ∈ openSegment ℝ (edgeArc' (L.ownerEdge x i)).vertices[j]
              (edgeArc' (L.ownerEdge x i)).vertices[j + 1] ∧
            ∃ c : ℝ, c ≠ 0 ∧
              (edgeArc' (L.ownerEdge x i)).vertices[j + 1] -
                  (edgeArc' (L.ownerEdge x i)).vertices[j] =
                c • ((L.fillingArc x i).vertices[m + 1] -
                  (L.fillingArc x i).vertices[m]) := by
  intro x i z m hm hz
  fin_cases i
  · change m + 1 < (L.fillingArc x 0).vertices.length at hm
    change z ∈ openSegment ℝ (L.fillingArc x 0).vertices[m]
      (L.fillingArc x 0).vertices[m + 1] at hz
    have howner : L.ownerEdge x 0 = (F.disk x).firstEdge := L.owner_zero x
    have hxmem : x ∈ Finset.univ.filter
        (fun y : {p // p ∈ D.crossingSet} =>
          (F.disk y).firstEdge = (F.disk x).firstEdge ∨
            (F.disk y).secondEdge = (F.disk x).firstEdge) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ x, Or.inl rfl⟩
    have htrans := hOwnedTransfer (F.disk x).firstEdge x hxmem z m
    simp at htrans
    simpa [howner] using htrans hm hz
  · change m + 1 < (L.fillingArc x 1).vertices.length at hm
    change z ∈ openSegment ℝ (L.fillingArc x 1).vertices[m]
      (L.fillingArc x 1).vertices[m + 1] at hz
    have howner : L.ownerEdge x 1 = (F.disk x).secondEdge := L.owner_one x
    have hxmem : x ∈ Finset.univ.filter
        (fun y : {p // p ∈ D.crossingSet} =>
          (F.disk y).firstEdge = (F.disk x).secondEdge ∨
            (F.disk y).secondEdge = (F.disk x).secondEdge) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ x, Or.inr rfl⟩
    have htrans := hOwnedTransfer (F.disk x).secondEdge x hxmem z m
    simp [(F.disk x).edges_ne] at htrans
    simpa [howner] using htrans hm hz

-- [TABLET NODE: OrdinaryLabeledCrossingDiskWholeEdgeAssignmentLocalization]
lemma OrdinaryLabeledCrossingDiskWholeEdgeAssignmentLocalization {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (F : OrdinaryLabeledCrossingDiskFamily G D)
    (L : OrdinaryLabeledCrossingDiskFillingFamily G D F) :
    let allOpenBalls :=
      ⋃ x : {p // p ∈ D.crossingSet},
        Metric.ball x.1 (F.disk x).radius
    let side := fun x : {p // p ∈ D.crossingSet} =>
      fun e : G.edgeFinset =>
        if (F.disk x).firstEdge = e then (0 : Fin 2) else (1 : Fin 2)
    ∃ edgeArc' : G.edgeFinset → PolygonalArc,
      (∀ e, (edgeArc' e).source = (D.edgeArc e).source) ∧
      (∀ e, (edgeArc' e).target = (D.edgeArc e).target) ∧
      (∀ e, (edgeArc' e).carrier \ allOpenBalls =
        (D.edgeArc e).carrier \ allOpenBalls) ∧
      (∀ x e,
        ((F.disk x).firstEdge = e ∨ (F.disk x).secondEdge = e) →
          Metric.closedBall x.1 (F.disk x).radius ∩ (edgeArc' e).carrier =
            (L.fillingArc x (side x e)).carrier) ∧
      (∀ x e,
        (F.disk x).firstEdge ≠ e →
          (F.disk x).secondEdge ≠ e →
            Metric.closedBall x.1 (F.disk x).radius ∩
                (edgeArc' e).carrier = ∅) ∧
      (∀ x i z m
          (hm : m + 1 < (L.fillingArc x i).vertices.length),
        z ∈ openSegment ℝ (L.fillingArc x i).vertices[m]
            (L.fillingArc x i).vertices[m + 1] →
          ∃ j : ℕ, ∃ hj : j + 1 < (edgeArc' (L.ownerEdge x i)).vertices.length,
            z ∈ openSegment ℝ (edgeArc' (L.ownerEdge x i)).vertices[j]
                (edgeArc' (L.ownerEdge x i)).vertices[j + 1] ∧
              ∃ c : ℝ, c ≠ 0 ∧
                (edgeArc' (L.ownerEdge x i)).vertices[j + 1] -
                    (edgeArc' (L.ownerEdge x i)).vertices[j] =
                  c • ((L.fillingArc x i).vertices[m + 1] -
                    (L.fillingArc x i).vertices[m])) ∧
      ∀ e₁ e₂ p,
        e₁ ≠ e₂ →
          p ∈ (edgeArc' e₁).relativeInterior →
            p ∈ (edgeArc' e₂).relativeInterior →
              ∃ x : {q // q ∈ D.crossingSet},
                p ∈ Metric.ball x.1 (F.disk x).radius ∧
                (∀ y : {q // q ∈ D.crossingSet},
                  p ∈ Metric.ball y.1 (F.disk y).radius → y = x) ∧
                (((F.disk x).firstEdge = e₁ ∧
                    (F.disk x).secondEdge = e₂ ∧
                    p ∈ (L.fillingArc x 0).relativeInterior ∧
                    p ∈ (L.fillingArc x 1).relativeInterior) ∨
                  ((F.disk x).secondEdge = e₁ ∧
                    (F.disk x).firstEdge = e₂ ∧
                    p ∈ (L.fillingArc x 1).relativeInterior ∧
                    p ∈ (L.fillingArc x 0).relativeInterior)) ∧
                (∀ q,
                  q ∈ (L.fillingArc x 0).relativeInterior →
                    q ∈ (L.fillingArc x 1).relativeInterior → q = p) := by
-- BODY
  classical
  let allOpenBalls :=
    ⋃ x : {p // p ∈ D.crossingSet},
      Metric.ball x.1 (F.disk x).radius
  let side := fun x : {p // p ∈ D.crossingSet} =>
    fun e : G.edgeFinset =>
      if (F.disk x).firstEdge = e then (0 : Fin 2) else (1 : Fin 2)
  change ∃ edgeArc' : G.edgeFinset → PolygonalArc,
    (∀ e, (edgeArc' e).source = (D.edgeArc e).source) ∧
    (∀ e, (edgeArc' e).target = (D.edgeArc e).target) ∧
    (∀ e, (edgeArc' e).carrier \ allOpenBalls =
      (D.edgeArc e).carrier \ allOpenBalls) ∧
    (∀ x e,
      ((F.disk x).firstEdge = e ∨ (F.disk x).secondEdge = e) →
        Metric.closedBall x.1 (F.disk x).radius ∩ (edgeArc' e).carrier =
          (L.fillingArc x (side x e)).carrier) ∧
    (∀ x e,
      (F.disk x).firstEdge ≠ e →
        (F.disk x).secondEdge ≠ e →
          Metric.closedBall x.1 (F.disk x).radius ∩
              (edgeArc' e).carrier = ∅) ∧
    (∀ x i z m
        (hm : m + 1 < (L.fillingArc x i).vertices.length),
      z ∈ openSegment ℝ (L.fillingArc x i).vertices[m]
          (L.fillingArc x i).vertices[m + 1] →
        ∃ j : ℕ, ∃ hj : j + 1 < (edgeArc' (L.ownerEdge x i)).vertices.length,
          z ∈ openSegment ℝ (edgeArc' (L.ownerEdge x i)).vertices[j]
              (edgeArc' (L.ownerEdge x i)).vertices[j + 1] ∧
            ∃ c : ℝ, c ≠ 0 ∧
              (edgeArc' (L.ownerEdge x i)).vertices[j + 1] -
                  (edgeArc' (L.ownerEdge x i)).vertices[j] =
                c • ((L.fillingArc x i).vertices[m + 1] -
                  (L.fillingArc x i).vertices[m])) ∧
    ∀ e₁ e₂ p,
      e₁ ≠ e₂ →
        p ∈ (edgeArc' e₁).relativeInterior →
          p ∈ (edgeArc' e₂).relativeInterior →
            ∃ x : {q // q ∈ D.crossingSet},
              p ∈ Metric.ball x.1 (F.disk x).radius ∧
              (∀ y : {q // q ∈ D.crossingSet},
                p ∈ Metric.ball y.1 (F.disk y).radius → y = x) ∧
              (((F.disk x).firstEdge = e₁ ∧
                  (F.disk x).secondEdge = e₂ ∧
                  p ∈ (L.fillingArc x 0).relativeInterior ∧
                  p ∈ (L.fillingArc x 1).relativeInterior) ∨
                ((F.disk x).secondEdge = e₁ ∧
                  (F.disk x).firstEdge = e₂ ∧
                  p ∈ (L.fillingArc x 1).relativeInterior ∧
                  p ∈ (L.fillingArc x 0).relativeInterior)) ∧
              (∀ q,
                q ∈ (L.fillingArc x 0).relativeInterior →
                  q ∈ (L.fillingArc x 1).relativeInterior → q = p)
  let fixedSpec := fun e : G.edgeFinset =>
    OrdinaryLabeledCrossingDiskFiniteEdgeSubstitution G D F L e
  let edgeArc' : G.edgeFinset → PolygonalArc := fun e =>
    Classical.choose (fixedSpec e)
  have edgeArcSpec : ∀ e, _ := fun e => Classical.choose_spec (fixedSpec e)
  have outsideOwned : ∀ e,
      (edgeArc' e).carrier \
          (⋃ x ∈ ((Finset.univ.filter (fun x : {p // p ∈ D.crossingSet} =>
              (F.disk x).firstEdge = e ∨ (F.disk x).secondEdge = e) :
                Finset {p // p ∈ D.crossingSet}) : Set {p // p ∈ D.crossingSet}),
            Metric.ball x.1 (F.disk x).radius) =
        (D.edgeArc e).carrier \
          (⋃ x ∈ ((Finset.univ.filter (fun x : {p // p ∈ D.crossingSet} =>
              (F.disk x).firstEdge = e ∨ (F.disk x).secondEdge = e) :
                Finset {p // p ∈ D.crossingSet}) : Set {p // p ∈ D.crossingSet}),
            Metric.ball x.1 (F.disk x).radius) := by
    intro e
    exact (edgeArcSpec e).2.2.2.1
  have localOwned : ∀ x e,
      ((F.disk x).firstEdge = e ∨ (F.disk x).secondEdge = e) →
        Metric.closedBall x.1 (F.disk x).radius ∩ (edgeArc' e).carrier =
          (L.fillingArc x (side x e)).carrier := by
    intro x e hx
    have hxmem : x ∈ Finset.univ.filter
        (fun y : {p // p ∈ D.crossingSet} =>
          (F.disk y).firstEdge = e ∨ (F.disk y).secondEdge = e) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
    simpa only [side] using (edgeArcSpec e).2.2.2.2.1 x hxmem
  have fillingTransfer : ∀ x i z m
      (hm : m + 1 < (L.fillingArc x i).vertices.length),
      z ∈ openSegment ℝ (L.fillingArc x i).vertices[m]
          (L.fillingArc x i).vertices[m + 1] →
        ∃ j : ℕ, ∃ hj : j + 1 < (edgeArc' (L.ownerEdge x i)).vertices.length,
          z ∈ openSegment ℝ (edgeArc' (L.ownerEdge x i)).vertices[j]
              (edgeArc' (L.ownerEdge x i)).vertices[j + 1] ∧
            ∃ c : ℝ, c ≠ 0 ∧
              (edgeArc' (L.ownerEdge x i)).vertices[j + 1] -
                  (edgeArc' (L.ownerEdge x i)).vertices[j] =
                c • ((L.fillingArc x i).vertices[m + 1] -
                  (L.fillingArc x i).vertices[m]) := by
    exact wholeEdgeFillingTransfer G D F L edgeArc'
      (fun e => (edgeArcSpec e).2.2.2.2.2.2)
  have oldRelativeOfClosedCarrier : ∀ x e z,
      z ∈ Metric.closedBall x.1 (F.disk x).radius →
        z ∈ (D.edgeArc e).carrier →
          z ∈ (D.edgeArc e).relativeInterior := by
    intro x e z hzClosed hzCarrier
    rw [(D.edgeArc e).relativeInterior_eq]
    refine ⟨hzCarrier, ?_⟩
    rcases D.edgeArc_endpoints e with ⟨u, v, _huv, _he, hend⟩
    have hzu : z ≠ D.vertexPlacement u := by
      intro h
      apply (F.disk x).no_vertex_in_closedBall u
      rwa [← h]
    have hzv : z ≠ D.vertexPlacement v := by
      intro h
      apply (F.disk x).no_vertex_in_closedBall v
      rwa [← h]
    rcases hend with hend | hend
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
        hend.1, hend.2] using And.intro hzu hzv
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or,
        hend.1, hend.2] using And.intro hzv hzu
  have outsideAll : ∀ e,
      (edgeArc' e).carrier \ allOpenBalls =
        (D.edgeArc e).carrier \ allOpenBalls := by
    intro e
    apply Set.Subset.antisymm
    · rintro z ⟨hzArc, hzAll⟩
      have hzOwned : z ∉
          (⋃ x ∈ ((Finset.univ.filter (fun x : {p // p ∈ D.crossingSet} =>
              (F.disk x).firstEdge = e ∨ (F.disk x).secondEdge = e) :
                Finset {p // p ∈ D.crossingSet}) : Set {p // p ∈ D.crossingSet}),
            Metric.ball x.1 (F.disk x).radius) := by
        intro hz
        rcases Set.mem_iUnion.mp hz with ⟨x, hz⟩
        rcases Set.mem_iUnion.mp hz with ⟨_hx, hzBall⟩
        apply hzAll
        exact Set.mem_iUnion.mpr ⟨x, hzBall⟩
      have hz : z ∈ (edgeArc' e).carrier \
          (⋃ x ∈ ((Finset.univ.filter (fun x : {p // p ∈ D.crossingSet} =>
              (F.disk x).firstEdge = e ∨ (F.disk x).secondEdge = e) :
                Finset {p // p ∈ D.crossingSet}) : Set {p // p ∈ D.crossingSet}),
            Metric.ball x.1 (F.disk x).radius) := ⟨hzArc, hzOwned⟩
      rw [outsideOwned e] at hz
      exact ⟨hz.1, hzAll⟩
    · rintro z ⟨hzArc, hzAll⟩
      have hzOwned : z ∉
          (⋃ x ∈ ((Finset.univ.filter (fun x : {p // p ∈ D.crossingSet} =>
              (F.disk x).firstEdge = e ∨ (F.disk x).secondEdge = e) :
                Finset {p // p ∈ D.crossingSet}) : Set {p // p ∈ D.crossingSet}),
            Metric.ball x.1 (F.disk x).radius) := by
        intro hz
        rcases Set.mem_iUnion.mp hz with ⟨x, hz⟩
        rcases Set.mem_iUnion.mp hz with ⟨_hx, hzBall⟩
        apply hzAll
        exact Set.mem_iUnion.mpr ⟨x, hzBall⟩
      have hz : z ∈ (D.edgeArc e).carrier \
          (⋃ x ∈ ((Finset.univ.filter (fun x : {p // p ∈ D.crossingSet} =>
              (F.disk x).firstEdge = e ∨ (F.disk x).secondEdge = e) :
                Finset {p // p ∈ D.crossingSet}) : Set {p // p ∈ D.crossingSet}),
            Metric.ball x.1 (F.disk x).radius) := ⟨hzArc, hzOwned⟩
      rw [← outsideOwned e] at hz
      exact ⟨hz.1, hzAll⟩
  have nonownerEmpty : ∀ x e,
      (F.disk x).firstEdge ≠ e →
        (F.disk x).secondEdge ≠ e →
          Metric.closedBall x.1 (F.disk x).radius ∩
              (edgeArc' e).carrier = ∅ := by
    intro x e hfirst hsecond
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    rcases hz with ⟨hzClosed, hzArc⟩
    have hzOutsideOwned : z ∉
        (⋃ y ∈ ((Finset.univ.filter (fun y : {p // p ∈ D.crossingSet} =>
            (F.disk y).firstEdge = e ∨ (F.disk y).secondEdge = e) :
              Finset {p // p ∈ D.crossingSet}) : Set {p // p ∈ D.crossingSet}),
          Metric.ball y.1 (F.disk y).radius) := by
      intro hzUnion
      rcases Set.mem_iUnion.mp hzUnion with ⟨y, hzUnion⟩
      rcases Set.mem_iUnion.mp hzUnion with ⟨hyMem, hzBall⟩
      have hyOwner := (Finset.mem_filter.mp hyMem).2
      have hyne : y ≠ x := by
        intro hyx
        subst y
        exact hyOwner.elim hfirst hsecond
      exact (Set.disjoint_left.mp (F.closedBalls_pairwise_disjoint hyne)
        (Metric.ball_subset_closedBall hzBall)) hzClosed
    have hzOld : z ∈ (D.edgeArc e).carrier := by
      have hzDiff : z ∈ (edgeArc' e).carrier \
          (⋃ y ∈ ((Finset.univ.filter (fun y : {p // p ∈ D.crossingSet} =>
              (F.disk y).firstEdge = e ∨ (F.disk y).secondEdge = e) :
                Finset {p // p ∈ D.crossingSet}) : Set {p // p ∈ D.crossingSet}),
            Metric.ball y.1 (F.disk y).radius) := ⟨hzArc, hzOutsideOwned⟩
      rw [outsideOwned e] at hzDiff
      exact hzDiff.1
    have hzDrawing : z ∈ ⋃ a : G.edgeFinset, (D.edgeArc a).carrier :=
      Set.mem_iUnion.mpr ⟨e, hzOld⟩
    have hzLocal : z ∈ Metric.closedBall x.1 (F.disk x).radius ∩
        ((D.edgeArc (F.disk x).firstEdge).carrier ∪
          (D.edgeArc (F.disk x).secondEdge).carrier) := by
      rw [← (F.disk x).exact_local_drawing_carrier]
      exact ⟨hzClosed, hzDrawing⟩
    have hzERel := oldRelativeOfClosedCarrier x e z hzClosed hzOld
    rcases hzLocal.2 with hzFirst | hzSecond
    · have hzFirstRel := oldRelativeOfClosedCarrier x
          (F.disk x).firstEdge z hzClosed hzFirst
      have hzCross : z ∈ D.crossingSet :=
        (D.crossingSet_spec z).mpr
          ⟨e, (F.disk x).firstEdge, hfirst.symm, hzERel, hzFirstRel⟩
      let y : {p // p ∈ D.crossingSet} := ⟨z, hzCross⟩
      have hyx : y = x := by
        by_contra hyx
        exact (F.disk x).no_other_crossing_in_closedBall y hyx hzClosed
      have hzx : z = x.1 := congrArg Subtype.val hyx
      have hzSecondRel : z ∈ (D.edgeArc (F.disk x).secondEdge).relativeInterior := by
        rw [hzx]
        exact (F.disk x).center_second
      exact D.no_three_edge_interiors_meet hfirst.symm hsecond.symm
        (F.disk x).edges_ne hzERel hzFirstRel hzSecondRel
    · have hzSecondRel := oldRelativeOfClosedCarrier x
          (F.disk x).secondEdge z hzClosed hzSecond
      have hzCross : z ∈ D.crossingSet :=
        (D.crossingSet_spec z).mpr
          ⟨e, (F.disk x).secondEdge, hsecond.symm, hzERel, hzSecondRel⟩
      let y : {p // p ∈ D.crossingSet} := ⟨z, hzCross⟩
      have hyx : y = x := by
        by_contra hyx
        exact (F.disk x).no_other_crossing_in_closedBall y hyx hzClosed
      have hzx : z = x.1 := congrArg Subtype.val hyx
      have hzFirstRel : z ∈ (D.edgeArc (F.disk x).firstEdge).relativeInterior := by
        rw [hzx]
        exact (F.disk x).center_first
      exact D.no_three_edge_interiors_meet hfirst.symm hsecond.symm
        (F.disk x).edges_ne hzERel hzFirstRel hzSecondRel
  have fillingRelativeOfBallCarrier : ∀ x i z,
      z ∈ Metric.ball x.1 (F.disk x).radius →
        z ∈ (L.fillingArc x i).carrier →
          z ∈ (L.fillingArc x i).relativeInterior := by
    intro x i z hzBall hzCarrier
    fin_cases i
    · change z ∈ (L.fillingArc x 0).carrier at hzCarrier
      change z ∈ (L.fillingArc x 0).relativeInterior
      rw [(L.fillingArc x 0).relativeInterior_eq]
      refine ⟨hzCarrier, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro hzSource
        have hzSphere : z ∈ Metric.sphere x.1 (F.disk x).radius := by
          rw [hzSource, L.source_zero]
          exact (F.disk x).firstBranch.beforeGate_on_sphere
        have hzlt := Metric.mem_ball.mp hzBall
        have hzeq := Metric.mem_sphere.mp hzSphere
        linarith
      · intro hzTarget
        have hzSphere : z ∈ Metric.sphere x.1 (F.disk x).radius := by
          rw [hzTarget, L.target_zero]
          exact (F.disk x).firstBranch.afterGate_on_sphere
        have hzlt := Metric.mem_ball.mp hzBall
        have hzeq := Metric.mem_sphere.mp hzSphere
        linarith
    · change z ∈ (L.fillingArc x 1).carrier at hzCarrier
      change z ∈ (L.fillingArc x 1).relativeInterior
      rw [(L.fillingArc x 1).relativeInterior_eq]
      refine ⟨hzCarrier, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro hzSource
        have hzSphere : z ∈ Metric.sphere x.1 (F.disk x).radius := by
          rw [hzSource, L.source_one]
          exact (F.disk x).secondBranch.beforeGate_on_sphere
        have hzlt := Metric.mem_ball.mp hzBall
        have hzeq := Metric.mem_sphere.mp hzSphere
        linarith
      · intro hzTarget
        have hzSphere : z ∈ Metric.sphere x.1 (F.disk x).radius := by
          rw [hzTarget, L.target_one]
          exact (F.disk x).secondBranch.afterGate_on_sphere
        have hzlt := Metric.mem_ball.mp hzBall
        have hzeq := Metric.mem_sphere.mp hzSphere
        linarith
  refine ⟨edgeArc', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    exact (edgeArcSpec e).1
  · intro e
    exact (edgeArcSpec e).2.1
  · exact outsideAll
  · exact localOwned
  · exact nonownerEmpty
  · exact fillingTransfer
  · intro e₁ e₂ p he12 hp₁ hp₂
    have hp₁Carrier : p ∈ (edgeArc' e₁).carrier := by
      rw [(edgeArc' e₁).relativeInterior_eq] at hp₁
      exact hp₁.1
    have hp₂Carrier : p ∈ (edgeArc' e₂).carrier := by
      rw [(edgeArc' e₂).relativeInterior_eq] at hp₂
      exact hp₂.1
    have hpBallExists : ∃ x : {q // q ∈ D.crossingSet},
        p ∈ Metric.ball x.1 (F.disk x).radius := by
      by_contra hnone
      simp only [not_exists] at hnone
      have hpOutside : p ∉ allOpenBalls := by
        intro hpAll
        rcases Set.mem_iUnion.mp hpAll with ⟨x, hpBall⟩
        exact hnone x hpBall
      have hpOld₁Carrier : p ∈ (D.edgeArc e₁).carrier := by
        have hpDiff : p ∈ (edgeArc' e₁).carrier \ allOpenBalls :=
          ⟨hp₁Carrier, hpOutside⟩
        rw [outsideAll e₁] at hpDiff
        exact hpDiff.1
      have hpOld₂Carrier : p ∈ (D.edgeArc e₂).carrier := by
        have hpDiff : p ∈ (edgeArc' e₂).carrier \ allOpenBalls :=
          ⟨hp₂Carrier, hpOutside⟩
        rw [outsideAll e₂] at hpDiff
        exact hpDiff.1
      have hpOld₁Rel : p ∈ (D.edgeArc e₁).relativeInterior := by
        rw [(D.edgeArc e₁).relativeInterior_eq]
        refine ⟨hpOld₁Carrier, ?_⟩
        rw [(edgeArc' e₁).relativeInterior_eq] at hp₁
        intro hpOldEnd
        apply hp₁.2
        rcases hpOldEnd with hpSource | hpTarget
        · exact Or.inl (hpSource.trans (edgeArcSpec e₁).1.symm)
        · exact Or.inr (hpTarget.trans (edgeArcSpec e₁).2.1.symm)
      have hpOld₂Rel : p ∈ (D.edgeArc e₂).relativeInterior := by
        rw [(D.edgeArc e₂).relativeInterior_eq]
        refine ⟨hpOld₂Carrier, ?_⟩
        rw [(edgeArc' e₂).relativeInterior_eq] at hp₂
        intro hpOldEnd
        apply hp₂.2
        rcases hpOldEnd with hpSource | hpTarget
        · exact Or.inl (hpSource.trans (edgeArcSpec e₂).1.symm)
        · exact Or.inr (hpTarget.trans (edgeArcSpec e₂).2.1.symm)
      have hpCross : p ∈ D.crossingSet :=
        (D.crossingSet_spec p).mpr ⟨e₁, e₂, he12, hpOld₁Rel, hpOld₂Rel⟩
      let x : {q // q ∈ D.crossingSet} := ⟨p, hpCross⟩
      have hpSelf : p ∈ Metric.ball x.1 (F.disk x).radius := by
        apply Metric.mem_ball.mpr
        simpa only [x, dist_self] using (F.disk x).firstBranch.radius_pos
      exact hnone x hpSelf
    let x : {q // q ∈ D.crossingSet} := Classical.choose hpBallExists
    have hpBall : p ∈ Metric.ball x.1 (F.disk x).radius :=
      Classical.choose_spec hpBallExists
    have hpUnique : ∀ y : {q // q ∈ D.crossingSet},
        p ∈ Metric.ball y.1 (F.disk y).radius → y = x := by
      intro y hpY
      by_contra hyx
      exact (Set.disjoint_left.mp (F.closedBalls_pairwise_disjoint hyx)
        (Metric.ball_subset_closedBall hpY))
          (Metric.ball_subset_closedBall hpBall)
    have he₁Owner : (F.disk x).firstEdge = e₁ ∨
        (F.disk x).secondEdge = e₁ := by
      by_contra howner
      have hfirst : (F.disk x).firstEdge ≠ e₁ := fun h => howner (Or.inl h)
      have hsecond : (F.disk x).secondEdge ≠ e₁ := fun h => howner (Or.inr h)
      have hpMem : p ∈ Metric.closedBall x.1 (F.disk x).radius ∩
          (edgeArc' e₁).carrier :=
        ⟨Metric.ball_subset_closedBall hpBall, hp₁Carrier⟩
      rw [nonownerEmpty x e₁ hfirst hsecond] at hpMem
      exact hpMem
    have he₂Owner : (F.disk x).firstEdge = e₂ ∨
        (F.disk x).secondEdge = e₂ := by
      by_contra howner
      have hfirst : (F.disk x).firstEdge ≠ e₂ := fun h => howner (Or.inl h)
      have hsecond : (F.disk x).secondEdge ≠ e₂ := fun h => howner (Or.inr h)
      have hpMem : p ∈ Metric.closedBall x.1 (F.disk x).radius ∩
          (edgeArc' e₂).carrier :=
        ⟨Metric.ball_subset_closedBall hpBall, hp₂Carrier⟩
      rw [nonownerEmpty x e₂ hfirst hsecond] at hpMem
      exact hpMem
    refine ⟨x, hpBall, hpUnique, ?_, ?_⟩
    · rcases he₁Owner with h1First | h1Second
      · rcases he₂Owner with h2First | h2Second
        · exact False.elim (he12 (h1First.symm.trans h2First))
        · have hpFill0Carrier : p ∈ (L.fillingArc x 0).carrier := by
            have hpLocal : p ∈ Metric.closedBall x.1 (F.disk x).radius ∩
                (edgeArc' e₁).carrier :=
              ⟨Metric.ball_subset_closedBall hpBall, hp₁Carrier⟩
            rw [localOwned x e₁ (Or.inl h1First)] at hpLocal
            simpa only [side, if_pos h1First] using hpLocal
          have hFirstNeE₂ : (F.disk x).firstEdge ≠ e₂ := by
            rw [← h2Second]
            exact (F.disk x).edges_ne
          have hpFill1Carrier : p ∈ (L.fillingArc x 1).carrier := by
            have hpLocal : p ∈ Metric.closedBall x.1 (F.disk x).radius ∩
                (edgeArc' e₂).carrier :=
              ⟨Metric.ball_subset_closedBall hpBall, hp₂Carrier⟩
            rw [localOwned x e₂ (Or.inr h2Second)] at hpLocal
            simpa only [side, if_neg hFirstNeE₂] using hpLocal
          exact Or.inl ⟨h1First, h2Second,
            fillingRelativeOfBallCarrier x 0 p hpBall hpFill0Carrier,
            fillingRelativeOfBallCarrier x 1 p hpBall hpFill1Carrier⟩
      · rcases he₂Owner with h2First | h2Second
        · have hFirstNeE₁ : (F.disk x).firstEdge ≠ e₁ := by
            rw [← h1Second]
            exact (F.disk x).edges_ne
          have hpFill1Carrier : p ∈ (L.fillingArc x 1).carrier := by
            have hpLocal : p ∈ Metric.closedBall x.1 (F.disk x).radius ∩
                (edgeArc' e₁).carrier :=
              ⟨Metric.ball_subset_closedBall hpBall, hp₁Carrier⟩
            rw [localOwned x e₁ (Or.inr h1Second)] at hpLocal
            simpa only [side, if_neg hFirstNeE₁] using hpLocal
          have hpFill0Carrier : p ∈ (L.fillingArc x 0).carrier := by
            have hpLocal : p ∈ Metric.closedBall x.1 (F.disk x).radius ∩
                (edgeArc' e₂).carrier :=
              ⟨Metric.ball_subset_closedBall hpBall, hp₂Carrier⟩
            rw [localOwned x e₂ (Or.inl h2First)] at hpLocal
            simpa only [side, if_pos h2First] using hpLocal
          exact Or.inr ⟨h1Second, h2First,
            fillingRelativeOfBallCarrier x 1 p hpBall hpFill1Carrier,
            fillingRelativeOfBallCarrier x 0 p hpBall hpFill0Carrier⟩
        · exact False.elim (he12 (h1Second.symm.trans h2Second))
    · intro q hq0 hq1
      exact L.pair_meets_at_most_once x hq0 hq1
        (by
          rcases he₁Owner with h1First | h1Second
          · rcases he₂Owner with h2First | h2Second
            · exact False.elim (he12 (h1First.symm.trans h2First))
            · have hpLocal : p ∈ Metric.closedBall x.1 (F.disk x).radius ∩
                  (edgeArc' e₁).carrier :=
                ⟨Metric.ball_subset_closedBall hpBall, hp₁Carrier⟩
              rw [localOwned x e₁ (Or.inl h1First)] at hpLocal
              exact fillingRelativeOfBallCarrier x 0 p hpBall
                (by simpa only [side, if_pos h1First] using hpLocal)
          · rcases he₂Owner with h2First | h2Second
            · have hpLocal : p ∈ Metric.closedBall x.1 (F.disk x).radius ∩
                  (edgeArc' e₂).carrier :=
                ⟨Metric.ball_subset_closedBall hpBall, hp₂Carrier⟩
              rw [localOwned x e₂ (Or.inl h2First)] at hpLocal
              exact fillingRelativeOfBallCarrier x 0 p hpBall
                (by simpa only [side, if_pos h2First] using hpLocal)
            · exact False.elim (he12 (h1Second.symm.trans h2Second)))
        (by
          rcases he₁Owner with h1First | h1Second
          · rcases he₂Owner with h2First | h2Second
            · exact False.elim (he12 (h1First.symm.trans h2First))
            · have hFirstNeE₂ : (F.disk x).firstEdge ≠ e₂ := by
                rw [← h2Second]
                exact (F.disk x).edges_ne
              have hpLocal : p ∈ Metric.closedBall x.1 (F.disk x).radius ∩
                  (edgeArc' e₂).carrier :=
                ⟨Metric.ball_subset_closedBall hpBall, hp₂Carrier⟩
              rw [localOwned x e₂ (Or.inr h2Second)] at hpLocal
              exact fillingRelativeOfBallCarrier x 1 p hpBall
                (by simpa only [side, if_neg hFirstNeE₂] using hpLocal)
          · rcases he₂Owner with h2First | h2Second
            · have hFirstNeE₁ : (F.disk x).firstEdge ≠ e₁ := by
                rw [← h1Second]
                exact (F.disk x).edges_ne
              have hpLocal : p ∈ Metric.closedBall x.1 (F.disk x).radius ∩
                  (edgeArc' e₁).carrier :=
                ⟨Metric.ball_subset_closedBall hpBall, hp₁Carrier⟩
              rw [localOwned x e₁ (Or.inr h1Second)] at hpLocal
              exact fillingRelativeOfBallCarrier x 1 p hpBall
                (by simpa only [side, if_neg hFirstNeE₁] using hpLocal)
            · exact False.elim (he12 (h1Second.symm.trans h2Second)))
