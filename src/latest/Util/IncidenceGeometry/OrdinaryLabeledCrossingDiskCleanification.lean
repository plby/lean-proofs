import Util.IncidenceGeometry.FiniteLocalizedPolygonalEdgeAssignmentCertification
import Util.IncidenceGeometry.OrdinaryLabeledCrossingDiskWholeEdgeAssignmentLocalization

open Classical
noncomputable section


lemma OrdinaryLabeledCrossingDiskCleanification {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G)
    (F : OrdinaryLabeledCrossingDiskFamily G D)
    (L : OrdinaryLabeledCrossingDiskFillingFamily G D F) :
    let LocalWitness := fun (Dclean : OrdinaryPolygonalDrawing G)
        (x : {q // q ∈ D.crossingSet})
        (p : EuclideanSpace ℝ (Fin 2)) =>
      p ∈ Metric.ball x.1 (F.disk x).radius ∧
        p ∈ (L.fillingArc x 0).relativeInterior ∧
        p ∈ (L.fillingArc x 1).relativeInterior ∧
        p ∈ (Dclean.edgeArc (F.disk x).firstEdge).relativeInterior ∧
        p ∈ (Dclean.edgeArc (F.disk x).secondEdge).relativeInterior ∧
        ∃ i j : ℕ,
          ∃ (hi : i + 1 <
                (Dclean.edgeArc (F.disk x).firstEdge).vertices.length)
            (hj : j + 1 <
                (Dclean.edgeArc (F.disk x).secondEdge).vertices.length),
            p ∈ openSegment ℝ
                (Dclean.edgeArc (F.disk x).firstEdge).vertices[i]
                (Dclean.edgeArc (F.disk x).firstEdge).vertices[i + 1] ∧
              p ∈ openSegment ℝ
                (Dclean.edgeArc (F.disk x).secondEdge).vertices[j]
                (Dclean.edgeArc (F.disk x).secondEdge).vertices[j + 1] ∧
              ¬ ∃ c : ℝ,
                (Dclean.edgeArc (F.disk x).secondEdge).vertices[j + 1] -
                    (Dclean.edgeArc (F.disk x).secondEdge).vertices[j] =
                  c • ((Dclean.edgeArc (F.disk x).firstEdge).vertices[i + 1] -
                    (Dclean.edgeArc (F.disk x).firstEdge).vertices[i])
    ∃ Dclean : OrdinaryPolygonalDrawing G,
      Dclean.vertexPlacement = D.vertexPlacement ∧
        Dclean.crossingSet.card ≤ D.crossingSet.card ∧
        ∃ provenance : {p // p ∈ Dclean.crossingSet} →
            {q // q ∈ D.crossingSet},
          Function.Injective provenance ∧
            (∀ p,
              LocalWitness Dclean (provenance p) p.1 ∧
                ∀ y : {q // q ∈ D.crossingSet},
                  p.1 ∈ Metric.ball y.1 (F.disk y).radius →
                    y = provenance p) ∧
            (Dclean.crossingSet.card = D.crossingSet.card →
              ∀ x : {q // q ∈ D.crossingSet},
                ∃ p : {q // q ∈ Dclean.crossingSet},
                  provenance p = x ∧ LocalWitness Dclean x p.1) := by
  classical
  let LocalWitness := fun (Dclean : OrdinaryPolygonalDrawing G)
      (x : {q // q ∈ D.crossingSet})
      (p : EuclideanSpace ℝ (Fin 2)) =>
    p ∈ Metric.ball x.1 (F.disk x).radius ∧
      p ∈ (L.fillingArc x 0).relativeInterior ∧
      p ∈ (L.fillingArc x 1).relativeInterior ∧
      p ∈ (Dclean.edgeArc (F.disk x).firstEdge).relativeInterior ∧
      p ∈ (Dclean.edgeArc (F.disk x).secondEdge).relativeInterior ∧
      ∃ i j : ℕ,
        ∃ (hi : i + 1 <
              (Dclean.edgeArc (F.disk x).firstEdge).vertices.length)
          (hj : j + 1 <
              (Dclean.edgeArc (F.disk x).secondEdge).vertices.length),
          p ∈ openSegment ℝ
              (Dclean.edgeArc (F.disk x).firstEdge).vertices[i]
              (Dclean.edgeArc (F.disk x).firstEdge).vertices[i + 1] ∧
            p ∈ openSegment ℝ
              (Dclean.edgeArc (F.disk x).secondEdge).vertices[j]
              (Dclean.edgeArc (F.disk x).secondEdge).vertices[j + 1] ∧
            ¬ ∃ c : ℝ,
              (Dclean.edgeArc (F.disk x).secondEdge).vertices[j + 1] -
                  (Dclean.edgeArc (F.disk x).secondEdge).vertices[j] =
                c • ((Dclean.edgeArc (F.disk x).firstEdge).vertices[i + 1] -
                  (Dclean.edgeArc (F.disk x).firstEdge).vertices[i])
  change ∃ Dclean : OrdinaryPolygonalDrawing G,
    Dclean.vertexPlacement = D.vertexPlacement ∧
      Dclean.crossingSet.card ≤ D.crossingSet.card ∧
      ∃ provenance : {p // p ∈ Dclean.crossingSet} →
          {q // q ∈ D.crossingSet},
        Function.Injective provenance ∧
          (∀ p,
            LocalWitness Dclean (provenance p) p.1 ∧
              ∀ y : {q // q ∈ D.crossingSet},
                p.1 ∈ Metric.ball y.1 (F.disk y).radius →
                  y = provenance p) ∧
          (Dclean.crossingSet.card = D.crossingSet.card →
            ∀ x : {q // q ∈ D.crossingSet},
              ∃ p : {q // q ∈ Dclean.crossingSet},
                provenance p = x ∧ LocalWitness Dclean x p.1)
  rcases OrdinaryLabeledCrossingDiskWholeEdgeAssignmentLocalization G D F L with
    ⟨edgeArc', hsource, htarget, houtside, _howned, _hnonowner,
      hfillingTransfer, hlocalize⟩
  let candidatePoint := fun x : {q // q ∈ D.crossingSet} =>
    if h : ∃ p : EuclideanSpace ℝ (Fin 2),
        p ∈ (L.fillingArc x 0).relativeInterior ∧
          p ∈ (L.fillingArc x 1).relativeInterior then
      Classical.choose h
    else x.1
  have candidatePoint_eq : ∀ (x : {q // q ∈ D.crossingSet})
      (p : EuclideanSpace ℝ (Fin 2)),
      p ∈ (L.fillingArc x 0).relativeInterior →
        p ∈ (L.fillingArc x 1).relativeInterior → candidatePoint x = p := by
    intro x p hp0 hp1
    have hex : ∃ q : EuclideanSpace ℝ (Fin 2),
        q ∈ (L.fillingArc x 0).relativeInterior ∧
          q ∈ (L.fillingArc x 1).relativeInterior := ⟨p, hp0, hp1⟩
    dsimp only [candidatePoint]
    rw [dif_pos hex]
    have hchosen := Classical.choose_spec hex
    exact L.pair_meets_at_most_once x hchosen.1 hchosen.2 hp0 hp1
  let candidate : Finset (EuclideanSpace ℝ (Fin 2)) :=
    D.crossingSet.attach.image candidatePoint
  have hlocalized : ∀ p : EuclideanSpace ℝ (Fin 2),
      (∃ e₁ e₂ : G.edgeFinset,
        e₁ ≠ e₂ ∧
          p ∈ (edgeArc' e₁).relativeInterior ∧
            p ∈ (edgeArc' e₂).relativeInterior) → p ∈ candidate := by
    intro p hp
    rcases hp with ⟨e₁, e₂, he₁₂, hp₁, hp₂⟩
    rcases hlocalize e₁ e₂ p he₁₂ hp₁ hp₂ with
      ⟨x, _hpBall, _hpUnique, howners, _hpMeetUnique⟩
    have hpFill : p ∈ (L.fillingArc x 0).relativeInterior ∧
        p ∈ (L.fillingArc x 1).relativeInterior := by
      rcases howners with howners | howners
      · exact ⟨howners.2.2.1, howners.2.2.2⟩
      · exact ⟨howners.2.2.2, howners.2.2.1⟩
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_attach D.crossingSet x, ?_⟩
    exact candidatePoint_eq x p hpFill.1 hpFill.2
  rcases FiniteLocalizedPolygonalEdgeAssignmentCertification G edgeArc'
      candidate hlocalized with
    ⟨crossingSet, _hcrossSubset, hcrossSpec, htransverse, hnoShared⟩
  have hedgeEndpoints : ∀ e : G.edgeFinset,
      ∃ u v : V,
        G.Adj u v ∧ e.1 = Sym2.mk u v ∧
          (((edgeArc' e).source = D.vertexPlacement u ∧
              (edgeArc' e).target = D.vertexPlacement v) ∨
            ((edgeArc' e).source = D.vertexPlacement v ∧
              (edgeArc' e).target = D.vertexPlacement u)) := by
    intro e
    rcases D.edgeArc_endpoints e with ⟨u, v, huv, he, hends⟩
    refine ⟨u, v, huv, he, ?_⟩
    rcases hends with hends | hends
    · exact Or.inl ⟨(hsource e).trans hends.1, (htarget e).trans hends.2⟩
    · exact Or.inr ⟨(hsource e).trans hends.1, (htarget e).trans hends.2⟩
  have hvertexAvoidance : ∀ (v : V) (e : G.edgeFinset),
      D.vertexPlacement v ∉ (edgeArc' e).relativeInterior := by
    intro v e hv
    by_cases hball : ∃ x : {q // q ∈ D.crossingSet},
        D.vertexPlacement v ∈ Metric.ball x.1 (F.disk x).radius
    · rcases hball with ⟨x, hx⟩
      exact (F.disk x).no_vertex_in_closedBall v
        (Metric.ball_subset_closedBall hx)
    · have hvOutside : D.vertexPlacement v ∉
          ⋃ x : {q // q ∈ D.crossingSet},
            Metric.ball x.1 (F.disk x).radius := by
        intro hvUnion
        rcases Set.mem_iUnion.mp hvUnion with ⟨x, hx⟩
        exact hball ⟨x, hx⟩
      have hvNewCarrier : D.vertexPlacement v ∈ (edgeArc' e).carrier := by
        rw [(edgeArc' e).relativeInterior_eq] at hv
        exact hv.1
      have hvOldCarrier : D.vertexPlacement v ∈ (D.edgeArc e).carrier := by
        have hvDiff : D.vertexPlacement v ∈ (edgeArc' e).carrier \
            (⋃ x : {q // q ∈ D.crossingSet},
              Metric.ball x.1 (F.disk x).radius) := ⟨hvNewCarrier, hvOutside⟩
        rw [houtside e] at hvDiff
        exact hvDiff.1
      have hvOldRelative : D.vertexPlacement v ∈
          (D.edgeArc e).relativeInterior := by
        rw [(D.edgeArc e).relativeInterior_eq]
        refine ⟨hvOldCarrier, ?_⟩
        rw [(edgeArc' e).relativeInterior_eq] at hv
        intro hvEnd
        apply hv.2
        rcases hvEnd with hvSource | hvTarget
        · exact Or.inl (hvSource.trans (hsource e).symm)
        · exact Or.inr (hvTarget.trans (htarget e).symm)
      exact D.no_vertex_in_edge_interior v e hvOldRelative
  have hnoThree : ∀ ⦃e₁ e₂ e₃ : G.edgeFinset⦄
      ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      e₁ ≠ e₂ → e₁ ≠ e₃ → e₂ ≠ e₃ →
        p ∈ (edgeArc' e₁).relativeInterior →
          p ∈ (edgeArc' e₂).relativeInterior →
            p ∈ (edgeArc' e₃).relativeInterior → False := by
    intro e₁ e₂ e₃ p he₁₂ he₁₃ he₂₃ hp₁ hp₂ hp₃
    rcases hlocalize e₁ e₂ p he₁₂ hp₁ hp₂ with
      ⟨x, hpX, hpUnique, howners₁₂, _hmeet₁₂⟩
    rcases hlocalize e₁ e₃ p he₁₃ hp₁ hp₃ with
      ⟨y, hpY, _hpUniqueY, howners₁₃, _hmeet₁₃⟩
    have hyx : y = x := hpUnique y hpY
    subst y
    rcases howners₁₂ with howners₁₂ | howners₁₂ <;>
      rcases howners₁₃ with howners₁₃ | howners₁₃
    · exact he₂₃ (howners₁₂.2.1.symm.trans howners₁₃.2.1)
    · exact (F.disk x).edges_ne
        (howners₁₂.1.trans howners₁₃.1.symm)
    · exact (F.disk x).edges_ne
        (howners₁₃.1.trans howners₁₂.1.symm)
    · exact he₂₃ (howners₁₂.2.1.symm.trans howners₁₃.2.1)
  let Dclean : OrdinaryPolygonalDrawing G :=
    { vertexPlacement := D.vertexPlacement
      vertexPlacement_injective := D.vertexPlacement_injective
      edgeArc := edgeArc'
      edgeArc_endpoints := hedgeEndpoints
      crossingSet := crossingSet
      no_vertex_in_edge_interior := hvertexAvoidance
      no_three_edge_interiors_meet := hnoThree
      transverse_intersections := htransverse
      no_shared_nondegenerate_subarc := hnoShared
      crossingSet_spec := hcrossSpec
      adjacentEdgeCrossingCount :=
        (crossingSet.filter (fun p =>
          ∃ e₁ e₂ : G.edgeFinset,
            e₁ ≠ e₂ ∧
              (∃ v : V, v ∈ e₁.1 ∧ v ∈ e₂.1) ∧
                p ∈ (edgeArc' e₁).relativeInterior ∧
                  p ∈ (edgeArc' e₂).relativeInterior)).card
      adjacentEdgeCrossingCount_eq := rfl }
  have crossingData : ∀ p : {q // q ∈ Dclean.crossingSet},
      ∃ x : {q // q ∈ D.crossingSet},
        LocalWitness Dclean x p.1 ∧
          ∀ y : {q // q ∈ D.crossingSet},
            p.1 ∈ Metric.ball y.1 (F.disk y).radius → y = x := by
    intro p
    have hpCross : p.1 ∈ crossingSet := by
      simpa only [Dclean] using p.2
    rcases (hcrossSpec p.1).mp hpCross with
      ⟨e₁, e₂, he₁₂, hp₁, hp₂⟩
    rcases hlocalize e₁ e₂ p.1 he₁₂ hp₁ hp₂ with
      ⟨x, hpBall, hpUnique, howners, _hpMeetUnique⟩
    have hpFill : p.1 ∈ (L.fillingArc x 0).relativeInterior ∧
        p.1 ∈ (L.fillingArc x 1).relativeInterior := by
      rcases howners with howners | howners
      · exact ⟨howners.2.2.1, howners.2.2.2⟩
      · exact ⟨howners.2.2.2, howners.2.2.1⟩
    have hpFinal : p.1 ∈ (edgeArc' (F.disk x).firstEdge).relativeInterior ∧
        p.1 ∈ (edgeArc' (F.disk x).secondEdge).relativeInterior := by
      rcases howners with howners | howners
      · rw [howners.1, howners.2.1]
        exact ⟨hp₁, hp₂⟩
      · rw [howners.2.1, howners.1]
        exact ⟨hp₂, hp₁⟩
    rcases L.crossing_open_segments x hpFill.1 hpFill.2 with
      ⟨m, n, hm, hn, hpOpen0, hpOpen1, hfillNonparallel⟩
    rcases hfillingTransfer x 0 p.1 m hm hpOpen0 with
      ⟨i, hiOwner, hpOpenFirstOwner, c₀, hc₀, hdir₀Owner⟩
    rcases hfillingTransfer x 1 p.1 n hn hpOpen1 with
      ⟨j, hjOwner, hpOpenSecondOwner, c₁, hc₁, hdir₁Owner⟩
    have hi : i + 1 <
        (edgeArc' (F.disk x).firstEdge).vertices.length := by
      simpa only [L.owner_zero x] using hiOwner
    have hpOpenFirst : p.1 ∈ openSegment ℝ
        (edgeArc' (F.disk x).firstEdge).vertices[i]
        (edgeArc' (F.disk x).firstEdge).vertices[i + 1] := by
      simpa only [L.owner_zero x] using hpOpenFirstOwner
    have hdir₀ :
        (edgeArc' (F.disk x).firstEdge).vertices[i + 1] -
            (edgeArc' (F.disk x).firstEdge).vertices[i] =
          c₀ • ((L.fillingArc x 0).vertices[m + 1] -
            (L.fillingArc x 0).vertices[m]) := by
      simpa only [L.owner_zero x] using hdir₀Owner
    have hj : j + 1 <
        (edgeArc' (F.disk x).secondEdge).vertices.length := by
      simpa only [L.owner_one x] using hjOwner
    have hpOpenSecond : p.1 ∈ openSegment ℝ
        (edgeArc' (F.disk x).secondEdge).vertices[j]
        (edgeArc' (F.disk x).secondEdge).vertices[j + 1] := by
      simpa only [L.owner_one x] using hpOpenSecondOwner
    have hdir₁ :
        (edgeArc' (F.disk x).secondEdge).vertices[j + 1] -
            (edgeArc' (F.disk x).secondEdge).vertices[j] =
          c₁ • ((L.fillingArc x 1).vertices[n + 1] -
            (L.fillingArc x 1).vertices[n]) := by
      simpa only [L.owner_one x] using hdir₁Owner
    have hfinalNonparallel : ¬ ∃ c : ℝ,
        (edgeArc' (F.disk x).secondEdge).vertices[j + 1] -
            (edgeArc' (F.disk x).secondEdge).vertices[j] =
          c • ((edgeArc' (F.disk x).firstEdge).vertices[i + 1] -
            (edgeArc' (F.disk x).firstEdge).vertices[i]) := by
      rintro ⟨c, hc⟩
      apply hfillNonparallel
      refine ⟨c₁⁻¹ * (c * c₀), ?_⟩
      calc
        (L.fillingArc x 1).vertices[n + 1] -
              (L.fillingArc x 1).vertices[n] =
            c₁⁻¹ • (c₁ • ((L.fillingArc x 1).vertices[n + 1] -
              (L.fillingArc x 1).vertices[n])) := by
                simp [smul_smul, hc₁]
        _ = c₁⁻¹ • ((edgeArc' (F.disk x).secondEdge).vertices[j + 1] -
              (edgeArc' (F.disk x).secondEdge).vertices[j]) := by rw [hdir₁]
        _ = c₁⁻¹ • (c •
              ((edgeArc' (F.disk x).firstEdge).vertices[i + 1] -
                (edgeArc' (F.disk x).firstEdge).vertices[i])) := by rw [hc]
        _ = c₁⁻¹ • (c • (c₀ •
              ((L.fillingArc x 0).vertices[m + 1] -
                (L.fillingArc x 0).vertices[m]))) := by rw [hdir₀]
        _ = (c₁⁻¹ * (c * c₀)) •
              ((L.fillingArc x 0).vertices[m + 1] -
                (L.fillingArc x 0).vertices[m]) := by
                  simp only [smul_smul]
    refine ⟨x, ?_, hpUnique⟩
    dsimp only [LocalWitness, Dclean]
    exact ⟨hpBall, hpFill.1, hpFill.2, hpFinal.1, hpFinal.2,
      i, j, hi, hj, hpOpenFirst, hpOpenSecond, hfinalNonparallel⟩
  let provenance : {p // p ∈ Dclean.crossingSet} →
      {q // q ∈ D.crossingSet} := fun p => Classical.choose (crossingData p)
  have provenanceSpec : ∀ p : {q // q ∈ Dclean.crossingSet},
      LocalWitness Dclean (provenance p) p.1 ∧
        ∀ y : {q // q ∈ D.crossingSet},
          p.1 ∈ Metric.ball y.1 (F.disk y).radius →
            y = provenance p := by
    intro p
    exact Classical.choose_spec (crossingData p)
  have provenanceInjective : Function.Injective provenance := by
    intro p q hpq
    have hpSpec := provenanceSpec p
    have hqSpec := provenanceSpec q
    have hpFill0 : p.1 ∈
        (L.fillingArc (provenance p) 0).relativeInterior := hpSpec.1.2.1
    have hpFill1 : p.1 ∈
        (L.fillingArc (provenance p) 1).relativeInterior := hpSpec.1.2.2.1
    have hqFill0 : q.1 ∈
        (L.fillingArc (provenance p) 0).relativeInterior := by
      simpa only [hpq] using hqSpec.1.2.1
    have hqFill1 : q.1 ∈
        (L.fillingArc (provenance p) 1).relativeInterior := by
      simpa only [hpq] using hqSpec.1.2.2.1
    apply Subtype.ext
    exact L.pair_meets_at_most_once (provenance p)
      hpFill0 hpFill1 hqFill0 hqFill1
  have hcard : Dclean.crossingSet.card ≤ D.crossingSet.card := by
    simpa only [Fintype.card_coe] using
      (Fintype.card_le_of_injective provenance provenanceInjective)
  refine ⟨Dclean, rfl, hcard, provenance, provenanceInjective,
    provenanceSpec, ?_⟩
  intro hcardEq x
  have htypeCard :
      Fintype.card {p // p ∈ Dclean.crossingSet} =
        Fintype.card {q // q ∈ D.crossingSet} := by
    simpa only [Fintype.card_coe] using hcardEq
  have hbijective : Function.Bijective provenance :=
    (Fintype.bijective_iff_injective_and_card provenance).2
      ⟨provenanceInjective, htypeCard⟩
  rcases hbijective.2 x with ⟨p, hp⟩
  refine ⟨p, hp, ?_⟩
  simpa only [hp] using (provenanceSpec p).1
