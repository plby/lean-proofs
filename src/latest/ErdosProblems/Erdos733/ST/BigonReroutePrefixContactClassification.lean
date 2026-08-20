import ErdosProblems.Erdos733.ST.BigonRerouteContactOldEdgeOwner
import ErdosProblems.Erdos733.ST.BigonRerouteFinitePresentationLocalBranch
import ErdosProblems.Erdos733.ST.EndpointSidePrefixAttachment
import ErdosProblems.Erdos733.ST.PolygonalArcCarrierCompact

open Classical
noncomputable section

-- [TABLET NODE: BigonReroutePrefixContactClassification]
lemma BigonReroutePrefixContactClassification
    {V : Type*} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (alpha beta : G.edgeFinset) (u : V)
    (x y : EuclideanSpace ℝ (Fin 2))
    (A B Bplus Rbeta H Bad DeltaX Qx : Set (EuclideanSpace ℝ (Fin 2)))
    (Aarc Barc BplusArc Bprefix : PolygonalArc)
    (K : FinitePolygonalSet) (XA : Finset (EuclideanSpace ℝ (Fin 2)))
    (E : EndpointSidePrefixAttachment Aarc Barc BplusArc
      Rbeta H Bad DeltaX Qx K XA)
    (hDuA : D.vertexPlacement u ∈ A)
    (hA : Aarc.carrier = A) (hB : Barc.carrier = B)
    (hBplus : BplusArc.carrier = Bplus)
    (hRbeta :
      Rbeta = (D.edgeArc beta).carrier \ ((B ∪ Bplus) \ ({y} : Set _)))
    (hH :
      H =
        (⋃ edge : G.edgeFinset,
          if edge = alpha then
            (D.edgeArc edge).carrier \ (A \ ({D.vertexPlacement u, x} : Set _))
          else if edge = beta then
            (D.edgeArc edge).carrier \
              ((B \ ({D.vertexPlacement u, x} : Set _)) ∪
                (Bplus \ ({x, y} : Set _)))
          else (D.edgeArc edge).carrier) ∪
        {p | ∃ v : V, v ≠ u ∧ p = D.vertexPlacement v})
    (hK : K.carrier = H)
    (hvertices : ∀ v : V, v ≠ u → D.vertexPlacement v ∈ (K.points : Set _))
    (hpointsBad : (K.points : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Bad)
    (hprefixSource : Bprefix.source = D.vertexPlacement u)
    (hprefixContacts : Bprefix.relativeInterior ∩ H = (E.xPrefix : Set _))
    (hprefixAvoid :
      Bprefix.relativeInterior ∩ (A ∪ B ∪ Bplus ∪ Rbeta) =
        (∅ : Set (EuclideanSpace ℝ (Fin 2)))) :
    (∀ (v : V), D.vertexPlacement v ∉ Bprefix.relativeInterior) ∧
      ∀ (e : G.edgeFinset) (he : e ≠ beta)
        (p : EuclideanSpace ℝ (Fin 2)),
        p ∈ Bprefix.relativeInterior →
          p ∈ (D.edgeArc e).relativeInterior →
            p ∈ E.xPrefix ∧
              ∀ f : G.edgeFinset,
                p ∈ (D.edgeArc f).relativeInterior → f = e := by
-- BODY
  have hprefixAvoidPoint : ∀ p, p ∈ Bprefix.relativeInterior →
      p ∉ A ∪ B ∪ Bplus ∪ Rbeta := by
    intro p hp hbad
    have : p ∈ Bprefix.relativeInterior ∩ (A ∪ B ∪ Bplus ∪ Rbeta) :=
      ⟨hp, hbad⟩
    rw [hprefixAvoid] at this
    exact this
  have hNoVertex : ∀ (v : V), D.vertexPlacement v ∉ Bprefix.relativeInterior := by
    intro v hv
    by_cases hvu : v = u
    · subst v
      rw [Bprefix.relativeInterior_eq] at hv
      exact hv.2 (by simp [hprefixSource])
    · have hvPoint := hvertices v hvu
      have hvH : D.vertexPlacement v ∈ H := by
        rw [hH]
        exact Or.inr ⟨v, hvu, rfl⟩
      have hvX : D.vertexPlacement v ∈ E.xPrefix := by
        have hvInter : D.vertexPlacement v ∈ Bprefix.relativeInterior ∩ H :=
          ⟨hv, hvH⟩
        rw [hprefixContacts] at hvInter
        exact hvInter
      exact (E.xPrefix_clean _ hvX).1 (hpointsBad hvPoint)
  refine ⟨hNoVertex, ?_⟩
  intro e he p hpPrefix hpEdge
  have hpAvoid := hprefixAvoidPoint p hpPrefix
  have hpH : p ∈ H := by
    rw [hH]
    left
    apply Set.mem_iUnion.mpr
    refine ⟨e, ?_⟩
    by_cases heAlpha : e = alpha
    · subst e
      rw [if_pos rfl]
      exact ⟨by
        rw [(D.edgeArc alpha).relativeInterior_eq] at hpEdge
        exact hpEdge.1, fun hpA => hpAvoid (Or.inl (Or.inl (Or.inl hpA.1)))⟩
    · rw [if_neg heAlpha, if_neg he]
      rw [(D.edgeArc e).relativeInterior_eq] at hpEdge
      exact hpEdge.1
  have hpX : p ∈ E.xPrefix := by
    have hpInter : p ∈ Bprefix.relativeInterior ∩ H := ⟨hpPrefix, hpH⟩
    rw [hprefixContacts] at hpInter
    exact hpInter
  rcases E.xPrefix_clean p hpX with
    ⟨_hpNotBad, hpNotPoints, i, hi, j, hj, hpOpen, s, hsUnique⟩
  rcases hsUnique.1 with ⟨hs, hpSOpen, _hNonparallel⟩
  rcases BigonRerouteFinitePresentationLocalBranch K s hs p hpNotPoints hpSOpen with
    ⟨r, hr, hlocalK⟩
  have hlocalH :
      Metric.ball p r ∩ H = Metric.ball p r ∩ segment ℝ s.1 s.2 := by
    rw [← hK, hlocalK]
  rcases BigonRerouteContactOldEdgeOwner G D alpha beta u x y p
      A B Bplus Rbeta H K s r hDuA
      (by simpa [← hA] using (PolygonalArcCarrierCompact Aarc).isClosed)
      (by simpa [← hB] using (PolygonalArcCarrierCompact Barc).isClosed)
      (by simpa [← hBplus] using (PolygonalArcCarrierCompact BplusArc).isClosed)
      hRbeta hH hK hvertices hpNotPoints
      (by
        intro hpOld
        rcases hpOld with hpAB | hpBplus
        · rcases hpAB with hpA | hpB
          · exact hpAvoid (Or.inl (Or.inl (Or.inl hpA)))
          · exact hpAvoid (Or.inl (Or.inl (Or.inr hpB)))
        · exact hpAvoid (Or.inl (Or.inr hpBplus)))
      hs hpSOpen hr hlocalH with
    ⟨owner, hpOwner, hOwnerUnique, _hAlpha, _hBeta, _hDirection⟩
  have heOwner : e = owner := hOwnerUnique e hpEdge
  refine ⟨hpX, ?_⟩
  intro f hpF
  calc
    f = owner := hOwnerUnique f hpF
    _ = e := heOwner.symm
