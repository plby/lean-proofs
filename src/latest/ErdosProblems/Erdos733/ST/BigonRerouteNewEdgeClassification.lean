import ErdosProblems.Erdos733.ST.BigonRerouteOrderedBetaTailData
import ErdosProblems.Erdos733.ST.OrdinaryPolygonalDrawing

open Classical
noncomputable section

-- [TABLET NODE: BigonRerouteNewEdgeClassification]
lemma BigonRerouteNewEdgeClassification
    {V : Type*} [Fintype V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (beta : G.edgeFinset) (u : V)
    (x y : EuclideanSpace ℝ (Fin 2))
    (B Bplus Rbeta H : Set (EuclideanSpace ℝ (Fin 2)))
    (XB Xnew : Finset (EuclideanSpace ℝ (Fin 2)))
    (Bprefix betaArcNew : PolygonalArc)
    (edgeArcNew : G.edgeFinset → PolygonalArc)
    (Tail : BigonRerouteOrderedBetaTailData G D beta u y B Bplus Rbeta H)
    (hxCross : x ∈ D.crossingSet)
    (hxBeta : x ∈ (D.edgeArc beta).relativeInterior)
    (hyBeta : y ∈ (D.edgeArc beta).relativeInterior)
    (hyx : y ≠ x)
    (hB : B ⊆ (D.edgeArc beta).carrier)
    (hyBplus : y ∈ Bplus)
    (hBplusCross : ∀ p, p ∈ Bplus → p ∈ D.crossingSet → p = x)
    (hBplusNoVertex : ∀ v : V, D.vertexPlacement v ∈ Bplus → False)
    (hXB : ∀ p, p ∈ XB ↔
      p ∈ B \ ({D.vertexPlacement u, x} : Set _) ∧ p ∈ H)
    (hxNotTail : x ∉ Tail.tailArc.carrier)
    (hprefixSource : Bprefix.source = D.vertexPlacement u)
    (hprefixTarget : Bprefix.target = y)
    (hprefixNoVertex : ∀ v : V, D.vertexPlacement v ∉ Bprefix.relativeInterior)
    (hprefixContacts :
      ∀ (e : G.edgeFinset), e ≠ beta →
        ∀ p : EuclideanSpace ℝ (Fin 2),
          p ∈ Bprefix.relativeInterior →
            p ∈ (D.edgeArc e).relativeInterior →
              p ∈ Xnew ∧
                ∀ f : G.edgeFinset,
                  p ∈ (D.edgeArc f).relativeInterior → f = e)
    (hbetaEdge : edgeArcNew beta = betaArcNew)
    (hotherEdges : ∀ e : G.edgeFinset, e ≠ beta →
      edgeArcNew e = D.edgeArc e)
    (hbetaSource : betaArcNew.source = D.vertexPlacement u)
    (hbetaTarget : betaArcNew.target = D.vertexPlacement Tail.farEndpoint)
    (hbetaCarrier : betaArcNew.carrier =
      Bprefix.carrier ∪ Tail.tailArc.carrier)
    (hbetaRelative : betaArcNew.relativeInterior =
      (Bprefix.carrier ∪ Tail.tailArc.carrier) \
        ({D.vertexPlacement u, D.vertexPlacement Tail.farEndpoint} : Set _)) :
    (∀ (v : V) (e : G.edgeFinset),
      D.vertexPlacement v ∉ (edgeArcNew e).relativeInterior) ∧
      (∀ ⦃e₁ e₂ e₃ : G.edgeFinset⦄
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        e₁ ≠ e₂ → e₁ ≠ e₃ → e₂ ≠ e₃ →
          p ∈ (edgeArcNew e₁).relativeInterior →
            p ∈ (edgeArcNew e₂).relativeInterior →
              p ∈ (edgeArcNew e₃).relativeInterior → False) ∧
        ∀ p : EuclideanSpace ℝ (Fin 2),
          (∃ e₁ e₂ : G.edgeFinset,
            e₁ ≠ e₂ ∧
              p ∈ (edgeArcNew e₁).relativeInterior ∧
                p ∈ (edgeArcNew e₂).relativeInterior) →
            p ∈ (D.crossingSet.erase x \ XB) ∪ Xnew := by
-- BODY
  have hyNoOther : ∀ (e : G.edgeFinset), e ≠ beta →
      y ∉ (D.edgeArc e).relativeInterior := by
    intro e he hye
    have hyCross : y ∈ D.crossingSet :=
      (D.crossingSet_spec y).2 ⟨beta, e, he.symm, hyBeta, hye⟩
    exact hyx (hBplusCross y hyBplus hyCross)
  have oldCarrierNotVertexToRelative :
      ∀ (e f : G.edgeFinset) (p : EuclideanSpace ℝ (Fin 2)),
        p ∈ (D.edgeArc e).relativeInterior →
          p ∈ (D.edgeArc f).carrier →
            p ∈ (D.edgeArc f).relativeInterior := by
    intro e f p hpe hpf
    rw [(D.edgeArc f).relativeInterior_eq]
    refine ⟨hpf, ?_⟩
    rcases D.edgeArc_endpoints f with ⟨a, b, _hab, _hf, hends⟩
    rcases hends with hends | hends
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (hpSource | hpTarget)
      · exact D.no_vertex_in_edge_interior a e
          ((hpSource.trans hends.1) ▸ hpe)
      · exact D.no_vertex_in_edge_interior b e
          ((hpTarget.trans hends.2) ▸ hpe)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (hpSource | hpTarget)
      · exact D.no_vertex_in_edge_interior b e
          ((hpSource.trans hends.1) ▸ hpe)
      · exact D.no_vertex_in_edge_interior a e
          ((hpTarget.trans hends.2) ▸ hpe)
  have betaPointCases : ∀ (p : EuclideanSpace ℝ (Fin 2)),
      p ∈ betaArcNew.relativeInterior →
        p ∈ Bprefix.relativeInterior ∨ p = y ∨
          p ∈ Tail.tailArc.relativeInterior := by
    intro p hp
    rw [hbetaRelative] at hp
    rcases hp.1 with hpPrefix | hpTail
    · by_cases hpu : p = D.vertexPlacement u
      · exact False.elim (hp.2 (by simp [hpu]))
      by_cases hpy : p = y
      · exact Or.inr (Or.inl hpy)
      · left
        rw [Bprefix.relativeInterior_eq]
        exact ⟨hpPrefix, by simp [hprefixSource, hprefixTarget, hpu, hpy]⟩
    · by_cases hpy : p = y
      · exact Or.inr (Or.inl hpy)
      · right
        right
        rw [Tail.tailArc.relativeInterior_eq]
        refine ⟨hpTail, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        refine ⟨?_, ?_⟩
        · simpa [Tail.source_eq] using hpy
        · intro hpFar
          exact hp.2 (by simp [hpFar, Tail.target_eq])
  have hNoVertex : ∀ (v : V) (e : G.edgeFinset),
      D.vertexPlacement v ∉ (edgeArcNew e).relativeInterior := by
    intro v e hp
    by_cases he : e = beta
    · subst e
      rw [hbetaEdge] at hp
      rcases betaPointCases _ hp with hpPrefix | hpy | hpTail
      · exact hprefixNoVertex v hpPrefix
      · exact hBplusNoVertex v (by simpa [hpy] using hyBplus)
      · exact D.no_vertex_in_edge_interior v beta
          (Tail.relativeInterior_subset_old_beta hpTail)
    · rw [hotherEdges e he] at hp
      exact D.no_vertex_in_edge_interior v e hp
  have hNoThree : ∀ ⦃e₁ e₂ e₃ : G.edgeFinset⦄
      ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      e₁ ≠ e₂ → e₁ ≠ e₃ → e₂ ≠ e₃ →
        p ∈ (edgeArcNew e₁).relativeInterior →
          p ∈ (edgeArcNew e₂).relativeInterior →
            p ∈ (edgeArcNew e₃).relativeInterior → False := by
    intro e₁ e₂ e₃ p he12 he13 he23 hp1 hp2 hp3
    by_cases h1 : e₁ = beta
    · subst e₁
      have h2 : e₂ ≠ beta := he12.symm
      have h3 : e₃ ≠ beta := he13.symm
      rw [hbetaEdge] at hp1
      rw [hotherEdges e₂ h2] at hp2
      rw [hotherEdges e₃ h3] at hp3
      rcases betaPointCases p hp1 with hpPrefix | hpy | hpTail
      · have hown2 := (hprefixContacts e₂ h2 p hpPrefix hp2).2 e₃ hp3
        exact he23 hown2.symm
      · exact hyNoOther e₂ h2 (hpy ▸ hp2)
      · exact D.no_three_edge_interiors_meet
          (e₁ := beta) (e₂ := e₂) (e₃ := e₃) h2.symm h3.symm he23
          (Tail.relativeInterior_subset_old_beta hpTail) hp2 hp3
    · by_cases h2 : e₂ = beta
      · subst e₂
        have h3 : e₃ ≠ beta := he23.symm
        rw [hotherEdges e₁ h1] at hp1
        rw [hbetaEdge] at hp2
        rw [hotherEdges e₃ h3] at hp3
        rcases betaPointCases p hp2 with hpPrefix | hpy | hpTail
        · have hown1 := (hprefixContacts e₁ h1 p hpPrefix hp1).2 e₃ hp3
          exact he13 hown1.symm
        · exact hyNoOther e₁ h1 (hpy ▸ hp1)
        · exact D.no_three_edge_interiors_meet
            (e₁ := e₁) (e₂ := beta) (e₃ := e₃) h1 he13 h3.symm
            hp1 (Tail.relativeInterior_subset_old_beta hpTail) hp3
      · by_cases h3 : e₃ = beta
        · subst e₃
          rw [hotherEdges e₁ h1] at hp1
          rw [hotherEdges e₂ h2] at hp2
          rw [hbetaEdge] at hp3
          rcases betaPointCases p hp3 with hpPrefix | hpy | hpTail
          · have hown1 := (hprefixContacts e₁ h1 p hpPrefix hp1).2 e₂ hp2
            exact he12 hown1.symm
          · exact hyNoOther e₁ h1 (hpy ▸ hp1)
          · exact D.no_three_edge_interiors_meet
              (e₁ := e₁) (e₂ := e₂) (e₃ := beta) he12 h1 h2
              hp1 hp2 (Tail.relativeInterior_subset_old_beta hpTail)
        · rw [hotherEdges e₁ h1] at hp1
          rw [hotherEdges e₂ h2] at hp2
          rw [hotherEdges e₃ h3] at hp3
          exact D.no_three_edge_interiors_meet he12 he13 he23 hp1 hp2 hp3
  refine ⟨hNoVertex, hNoThree, ?_⟩
  intro p hpCross
  rcases hpCross with ⟨e₁, e₂, he12, hp1, hp2⟩
  by_cases h1 : e₁ = beta
  · subst e₁
    have h2 : e₂ ≠ beta := he12.symm
    rw [hbetaEdge] at hp1
    rw [hotherEdges e₂ h2] at hp2
    rcases betaPointCases p hp1 with hpPrefix | hpy | hpTail
    · exact Finset.mem_union_right _ (hprefixContacts e₂ h2 p hpPrefix hp2).1
    · exact False.elim (hyNoOther e₂ h2 (hpy ▸ hp2))
    · apply Finset.mem_union_left
      have hpBeta := Tail.relativeInterior_subset_old_beta hpTail
      have hpOldCross : p ∈ D.crossingSet :=
        (D.crossingSet_spec p).2 ⟨beta, e₂, h2.symm, hpBeta, hp2⟩
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨?_, hpOldCross⟩, ?_⟩
      · intro hpx
        subst p
        exact hxNotTail (by
          rw [Tail.tailArc.relativeInterior_eq] at hpTail
          exact hpTail.1)
      · intro hpXB
        have hpB := (hXB p).1 hpXB |>.1.1
        have hpMeet : p ∈ Tail.tailArc.carrier ∩ (B ∪ Bplus) := by
          refine ⟨?_, Or.inl hpB⟩
          rw [Tail.tailArc.relativeInterior_eq] at hpTail
          exact hpTail.1
        rw [Tail.meets_removed_subarc] at hpMeet
        have hpy' : p = y := by simpa using hpMeet
        exact hyNoOther e₂ h2 (hpy' ▸ hp2)
  · by_cases h2 : e₂ = beta
    · subst e₂
      rw [hotherEdges e₁ h1] at hp1
      rw [hbetaEdge] at hp2
      rcases betaPointCases p hp2 with hpPrefix | hpy | hpTail
      · exact Finset.mem_union_right _ (hprefixContacts e₁ h1 p hpPrefix hp1).1
      · exact False.elim (hyNoOther e₁ h1 (hpy ▸ hp1))
      · apply Finset.mem_union_left
        have hpBeta := Tail.relativeInterior_subset_old_beta hpTail
        have hpOldCross : p ∈ D.crossingSet :=
          (D.crossingSet_spec p).2 ⟨e₁, beta, h1, hp1, hpBeta⟩
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨?_, hpOldCross⟩, ?_⟩
        · intro hpx
          subst p
          exact hxNotTail (by
            rw [Tail.tailArc.relativeInterior_eq] at hpTail
            exact hpTail.1)
        · intro hpXB
          have hpB := (hXB p).1 hpXB |>.1.1
          have hpMeet : p ∈ Tail.tailArc.carrier ∩ (B ∪ Bplus) := by
            refine ⟨?_, Or.inl hpB⟩
            rw [Tail.tailArc.relativeInterior_eq] at hpTail
            exact hpTail.1
          rw [Tail.meets_removed_subarc] at hpMeet
          have hpy' : p = y := by simpa using hpMeet
          exact hyNoOther e₁ h1 (hpy' ▸ hp1)
    · rw [hotherEdges e₁ h1] at hp1
      rw [hotherEdges e₂ h2] at hp2
      apply Finset.mem_union_left
      have hpOldCross : p ∈ D.crossingSet :=
        (D.crossingSet_spec p).2 ⟨e₁, e₂, he12, hp1, hp2⟩
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨?_, hpOldCross⟩, ?_⟩
      · intro hpx
        subst p
        exact D.no_three_edge_interiors_meet
          (e₁ := e₁) (e₂ := e₂) (e₃ := beta) he12 h1 h2
          hp1 hp2 hxBeta
      · intro hpXB
        have hpB : p ∈ B := (hXB p).1 hpXB |>.1.1
        have hpBetaCarrier : p ∈ (D.edgeArc beta).carrier := hB hpB
        have hpBetaRel := oldCarrierNotVertexToRelative e₁ beta p hp1 hpBetaCarrier
        exact D.no_three_edge_interiors_meet
          (e₁ := e₁) (e₂ := e₂) (e₃ := beta) he12 h1 h2
          hp1 hp2 hpBetaRel
