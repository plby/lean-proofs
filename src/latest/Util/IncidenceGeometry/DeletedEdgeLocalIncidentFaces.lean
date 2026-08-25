import Util.IncidenceGeometry.PlaneFaceData
import Util.IncidenceGeometry.OrdinaryDrawingImage
import Util.IncidenceGeometry.OrdinaryPolygonalDrawing
import Util.IncidenceGeometry.PolygonalArc

open Classical
noncomputable section

lemma DeletedEdgeLocalIncidentFaces {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) (e : G.edgeFinset)
    (d : G.Dart) (hd : d.edge = e.1) :
    ∀ x ∈ (D.edgeArc e).relativeInterior,
      ∃ U : Set (EuclideanSpace ℝ (Fin 2)),
        IsOpen U ∧ x ∈ U ∧
          U ∩ (OrdinaryDrawingImage G D)ᶜ ⊆
            A.faceSet (A.leftFace d) ∪ A.faceSet (A.leftFace d.symm) := by
  intro x hx
  have hdartRelEq :
      (A.dartArc d).relativeInterior = (D.edgeArc e).relativeInterior := by
    have hdartEdge : A.dartEdge d = e := by
      apply Subtype.ext
      exact (A.dartEdge_eq d).trans hd
    have hcarrier : (A.dartArc d).carrier = (D.edgeArc e).carrier := by
      simpa [hdartEdge] using A.dartArc_carrier d
    have hdedge : e.1 = s(d.toProd.1, d.toProd.2) := by
      simpa [SimpleGraph.Dart.edge] using hd.symm
    rcases D.edgeArc_endpoints e with ⟨u, v, _huv, huv_edge, hends⟩
    have huv_cases :
        (u = d.toProd.1 ∧ v = d.toProd.2) ∨
          (u = d.toProd.2 ∧ v = d.toProd.1) := by
      have hsym : s(u, v) = s(d.toProd.1, d.toProd.2) := by
        exact huv_edge.symm.trans hdedge
      have hpair :
          (u, v) = d.toProd ∨ (u, v) = d.toProd.swap := by
        simpa [Sym2.eq_iff] using hsym
      rcases hpair with hpair | hpair
      · left
        constructor
        · simpa using congrArg Prod.fst hpair
        · simpa using congrArg Prod.snd hpair
      · right
        constructor
        · simpa using congrArg Prod.fst hpair
        · simpa using congrArg Prod.snd hpair
    have hDendpoints :
        ({(D.edgeArc e).source, (D.edgeArc e).target} :
            Set (EuclideanSpace ℝ (Fin 2))) =
          {D.vertexPlacement d.toProd.1, D.vertexPlacement d.toProd.2} := by
      rcases hends with hdir | hdir
      · rcases hdir with ⟨hsource, htarget⟩
        rcases huv_cases with huv | huv
        · rcases huv with ⟨rfl, rfl⟩
          simp [hsource, htarget]
        · rcases huv with ⟨rfl, rfl⟩
          simp [hsource, htarget, Set.pair_comm]
      · rcases hdir with ⟨hsource, htarget⟩
        rcases huv_cases with huv | huv
        · rcases huv with ⟨rfl, rfl⟩
          simp [hsource, htarget, Set.pair_comm]
        · rcases huv with ⟨rfl, rfl⟩
          simp [hsource, htarget]
    have hdartEndpoints :
        ({(A.dartArc d).source, (A.dartArc d).target} :
            Set (EuclideanSpace ℝ (Fin 2))) =
          {D.vertexPlacement d.toProd.1, D.vertexPlacement d.toProd.2} := by
      simp [A.dartArc_source d, A.dartArc_target d]
    rw [(A.dartArc d).relativeInterior_eq, (D.edgeArc e).relativeInterior_eq,
      hcarrier, hdartEndpoints, ← hDendpoints]
  have hxDart : x ∈ (A.dartArc d).relativeInterior := by
    simpa [hdartRelEq] using hx
  rcases A.localComplement_subset_sideStrips d x hxDart with
    ⟨U, hUopen, hxU, hUsubset⟩
  refine ⟨U, hUopen, hxU, ?_⟩
  intro y hy
  have hySide : y ∈ A.leftSideStrip d ∪ A.leftSideStrip d.symm :=
    hUsubset hy
  rcases hySide with hyLeft | hyRight
  · exact Or.inl (A.leftFace_contains d hyLeft)
  · exact Or.inr (A.leftFace_contains d.symm hyRight)
