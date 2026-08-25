import Util.IncidenceGeometry.OrdinaryPolygonalDrawing
import Util.IncidenceGeometry.PolygonalArc
import Util.IncidenceGeometry.PolygonalArcSideStripsAvoidCompactWithEndpointConeCaps
import Util.IncidenceGeometry.PolygonalSideStrips
import Util.IncidenceGeometry.OrdinaryDrawingImage
import Util.IncidenceGeometry.OrdinaryDrawingImageWithoutEdge
import Util.IncidenceGeometry.PlaneDrawingSelectedEdgeAwayFromEndpointCompact
import Util.IncidenceGeometry.PlaneDrawingSelectedEdgeEndpointGermApertures

open Classical
noncomputable section

lemma PlaneDrawingEdgeArcSideStripsAvoidImage {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] [DecidableRel G.Adj]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0)
    (e : G.edgeFinset) (γ : PolygonalArc)
    (F : Set (EuclideanSpace ℝ (Fin 2))) :
    IsCompact F →
      Disjoint F γ.carrier →
        D.edgeArc e = γ →
          ∃ S : PolygonalSideStrips γ,
            Disjoint S.collar F ∧
              S.collar ⊆ (OrdinaryDrawingImage G D)ᶜ ∪ γ.relativeInterior ∧
                S.leftStrip ⊆ (OrdinaryDrawingImage G D)ᶜ ∧
                  S.rightStrip ⊆ (OrdinaryDrawingImage G D)ᶜ := by
  intro hF hFγ hγ
  obtain ⟨r₀, r₁, K₀, K₁, hIso, hK₀, hK₁, hinitAvoid, htermAvoid⟩ :=
    PlaneDrawingSelectedEdgeEndpointGermApertures G D hD e γ hγ
  have hr₀ : 0 < r₀ := hIso.source_pos
  have hr₁ : 0 < r₁ := hIso.target_pos
  let Other : Set (EuclideanSpace ℝ (Fin 2)) :=
    OrdinaryDrawingImageWithoutEdge G D e
  let A : Set (EuclideanSpace ℝ (Fin 2)) :=
    Other \ (Metric.ball γ.source r₀ ∪ Metric.ball γ.target r₁)
  have hAway :=
    PlaneDrawingSelectedEdgeAwayFromEndpointCompact G D hD e γ hγ r₀ r₁ hr₀ hr₁
  have hAcompact : IsCompact A := by
    simpa [A, Other] using hAway.1
  have hAdisjoint : Disjoint A γ.carrier := by
    simpa [A, Other] using hAway.2
  obtain ⟨S, hSF, hSA, hsource_not, htarget_not, hinitSub, htermSub⟩ :=
    PolygonalArcSideStripsAvoidCompactWithEndpointConeCaps γ F A r₀ r₁ K₀ K₁
      hF hFγ hAcompact hAdisjoint hIso hK₀ hK₁
  have hImage_cases :
      ∀ ⦃x : EuclideanSpace ℝ (Fin 2)⦄,
        x ∈ OrdinaryDrawingImage G D → x ∈ γ.carrier ∨ x ∈ Other := by
    intro x hx
    rw [OrdinaryDrawingImage] at hx
    dsimp [Other, OrdinaryDrawingImageWithoutEdge]
    rcases hx with hxv | hxedges
    · exact Or.inr (Or.inl hxv)
    · rcases Set.mem_iUnion.mp hxedges with ⟨f, hxf⟩
      by_cases hfe : f = e
      · subst f
        exact Or.inl (by simpa [hγ] using hxf)
      · exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨⟨f, hfe⟩, hxf⟩))
  have hCollarImage :
      S.collar ⊆ (OrdinaryDrawingImage G D)ᶜ ∪ γ.relativeInterior := by
    intro x hxS
    by_cases hxRel : x ∈ γ.relativeInterior
    · exact Or.inr hxRel
    · refine Or.inl ?_
      intro hxImg
      rcases hImage_cases hxImg with hxCarrier | hxOther
      · have hxEnd : x = γ.source ∨ x = γ.target := by
          have hxNot :
              x ∉ γ.carrier \ ({γ.source, γ.target} :
                Set (EuclideanSpace ℝ (Fin 2))) := by
            simpa [γ.relativeInterior_eq] using hxRel
          have hxEndMem :
              x ∈ ({γ.source, γ.target} : Set (EuclideanSpace ℝ (Fin 2))) := by
            by_contra hxNotEnd
            exact hxNot ⟨hxCarrier, hxNotEnd⟩
          simpa using hxEndMem
        rcases hxEnd with rfl | rfl
        · exact hsource_not hxS
        · exact htarget_not hxS
      · by_cases hxB₀ : x ∈ Metric.ball γ.source r₀
        · have hxCone :
            x ∈ PolygonalArcInitialEndpointCone γ r₀ K₀ :=
              hinitSub ⟨⟨hxS, hxB₀⟩, hxRel⟩
          exact (Set.disjoint_left.mp hinitAvoid hxCone) (by simpa [Other] using hxOther)
        · by_cases hxB₁ : x ∈ Metric.ball γ.target r₁
          · have hxCone :
              x ∈ PolygonalArcTerminalEndpointCone γ r₁ K₁ :=
                htermSub ⟨⟨hxS, hxB₁⟩, hxRel⟩
            exact (Set.disjoint_left.mp htermAvoid hxCone) (by simpa [Other] using hxOther)
          · have hxA : x ∈ A := by
              refine ⟨by simpa [Other] using hxOther, ?_⟩
              intro hxUnion
              rcases hxUnion with hx0 | hx1
              · exact hxB₀ hx0
              · exact hxB₁ hx1
            exact (Set.disjoint_left.mp hSA hxS) hxA
  have hLeft : S.leftStrip ⊆ (OrdinaryDrawingImage G D)ᶜ := by
    intro x hxLeft hxImg
    have hxCollar := S.left_subset_collar hxLeft
    rcases hCollarImage hxCollar with hxComp | hxRel
    · exact hxComp hxImg
    · have hxCarrier : x ∈ γ.carrier := by
        have hxRel' :
            x ∈ γ.carrier \ ({γ.source, γ.target} :
              Set (EuclideanSpace ℝ (Fin 2))) := by
          simpa [γ.relativeInterior_eq] using hxRel
        exact hxRel'.1
      exact (Set.disjoint_left.mp S.left_disjoint_arc hxLeft) hxCarrier
  have hRight : S.rightStrip ⊆ (OrdinaryDrawingImage G D)ᶜ := by
    intro x hxRight hxImg
    have hxCollar := S.right_subset_collar hxRight
    rcases hCollarImage hxCollar with hxComp | hxRel
    · exact hxComp hxImg
    · have hxCarrier : x ∈ γ.carrier := by
        have hxRel' :
            x ∈ γ.carrier \ ({γ.source, γ.target} :
              Set (EuclideanSpace ℝ (Fin 2))) := by
          simpa [γ.relativeInterior_eq] using hxRel
        exact hxRel'.1
      exact (Set.disjoint_left.mp S.right_disjoint_arc hxRight) hxCarrier
  exact ⟨S, hSF, hCollarImage, hLeft, hRight⟩
