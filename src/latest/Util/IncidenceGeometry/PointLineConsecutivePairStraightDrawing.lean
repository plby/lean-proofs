import Util.IncidenceGeometry.GeometricArcDrawing
import Util.IncidenceGeometry.PointLineConsecutivePairGraphData

open Classical
noncomputable section

lemma PointLineConsecutivePairStraightDrawing
    {P : Finset (EuclideanSpace ℝ (Fin 2))}
    {L : Finset {ell : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) //
      IsAffineLine ell}}
    (A : PointLineConsecutivePairGraphData P L) :
    ∃ D : GeometricArcDrawing A.graph,
      D.localPairCount ≤ A.retainedLines.card ^ 2 := by
  let source (e : A.graph.edgeFinset) : EuclideanSpace ℝ (Fin 2) :=
    (A.edgeSourceVertex e).1
  let target (e : A.graph.edgeFinset) : EuclideanSpace ℝ (Fin 2) :=
    (A.edgeTargetVertex e).1
  let carrier (e : A.graph.edgeFinset) : Set (EuclideanSpace ℝ (Fin 2)) :=
    segment ℝ (source e) (target e)
  let interior (e : A.graph.edgeFinset) : Set (EuclideanSpace ℝ (Fin 2)) :=
    openSegment ℝ (source e) (target e)
  have source_ne_target (e : A.graph.edgeFinset) : source e ≠ target e := by
    intro h
    have hv : A.edgeSourceVertex e = A.edgeTargetVertex e := Subtype.ext h
    exact (A.graph.ne_of_adj (A.edge_adjacent e)) hv
  have point_on_owner (e : A.graph.edgeFinset)
      {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ interior e) :
      p ∈ ((A.edgeOwner e).1.1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) := by
    exact (A.edgeOwner e).1.1.convex.openSegment_subset
      (A.edge_source_on_owner e) (A.edge_target_on_owner e) hp
  have owner_intersection_subsingleton (e₁ e₂ : A.graph.edgeFinset)
      (howner : A.edgeOwner e₁ ≠ A.edgeOwner e₂) :
      (((A.edgeOwner e₁).1.1 : Set (EuclideanSpace ℝ (Fin 2))) ∩
        ((A.edgeOwner e₂).1.1 : Set (EuclideanSpace ℝ (Fin 2)))).Subsingleton := by
    intro p hp q hq
    by_contra hpq
    let linepq : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
      affineSpan ℝ ({p, q} : Set (EuclideanSpace ℝ (Fin 2)))
    have line_le₁ : linepq ≤ (A.edgeOwner e₁).1.1 :=
      affineSpan_le.2 (by
        intro z hz
        rcases hz with (rfl | hz)
        · exact hp.1
        · simpa only [Set.mem_singleton_iff] using hz ▸ hq.1)
    have line_le₂ : linepq ≤ (A.edgeOwner e₂).1.1 :=
      affineSpan_le.2 (by
        intro z hz
        rcases hz with (rfl | hz)
        · exact hp.2
        · simpa only [Set.mem_singleton_iff] using hz ▸ hq.2)
    have line_rank : Module.finrank ℝ linepq.direction = 1 := by
      rw [direction_affineSpan, vectorSpan_pair]
      exact finrank_span_singleton (vsub_ne_zero.2 hpq)
    have dir₁ : linepq.direction = (A.edgeOwner e₁).1.1.direction :=
      Submodule.eq_of_le_of_finrank_eq
        (AffineSubspace.direction_le line_le₁)
        (line_rank.trans (A.edgeOwner e₁).1.property.2.symm)
    have dir₂ : linepq.direction = (A.edgeOwner e₂).1.1.direction :=
      Submodule.eq_of_le_of_finrank_eq
        (AffineSubspace.direction_le line_le₂)
        (line_rank.trans (A.edgeOwner e₂).1.property.2.symm)
    have hell : (A.edgeOwner e₁).1.1 = (A.edgeOwner e₂).1.1 :=
      AffineSubspace.ext_of_direction_eq (dir₁.symm.trans dir₂)
        ⟨p, hp.1, hp.2⟩
    exact howner (Subtype.ext (Subtype.ext hell))
  have carrier_intersection_subsingleton (e₁ e₂ : A.graph.edgeFinset)
      (hne : e₁ ≠ e₂) :
      (carrier e₁ ∩ carrier e₂).Subsingleton := by
    by_cases ho : A.edgeOwner e₁ = A.edgeOwner e₂
    · exact A.same_owner_segment_intersection_subsingleton e₁ e₂ hne ho
    · intro p hp q hq
      apply owner_intersection_subsingleton e₁ e₂ ho
      · exact ⟨
          (A.edgeOwner e₁).1.1.convex.segment_subset
            (A.edge_source_on_owner e₁) (A.edge_target_on_owner e₁) hp.1,
          (A.edgeOwner e₂).1.1.convex.segment_subset
            (A.edge_source_on_owner e₂) (A.edge_target_on_owner e₂) hp.2⟩
      · exact ⟨
          (A.edgeOwner e₁).1.1.convex.segment_subset
            (A.edge_source_on_owner e₁) (A.edge_target_on_owner e₁) hq.1,
          (A.edgeOwner e₂).1.1.convex.segment_subset
            (A.edge_source_on_owner e₂) (A.edge_target_on_owner e₂) hq.2⟩
  let crossingSet : Set (EuclideanSpace ℝ (Fin 2)) :=
    {p | ∃ e₁ e₂ : A.graph.edgeFinset,
      e₁ ≠ e₂ ∧ p ∈ interior e₁ ∧ p ∈ interior e₂}
  have crossingSet_finite : crossingSet.Finite := by
    let pairSet (e₁ e₂ : A.graph.edgeFinset) : Set (EuclideanSpace ℝ (Fin 2)) :=
      if h : e₁ = e₂ then ∅ else interior e₁ ∩ interior e₂
    have pairSet_finite (e₁ e₂ : A.graph.edgeFinset) : (pairSet e₁ e₂).Finite := by
      by_cases h : e₁ = e₂
      · simp [pairSet, h]
      · simp only [pairSet, h, ↓reduceDIte]
        apply Set.Subsingleton.finite
        intro p hp q hq
        apply carrier_intersection_subsingleton e₁ e₂ h
        · exact ⟨openSegment_subset_segment ℝ _ _ hp.1,
            openSegment_subset_segment ℝ _ _ hp.2⟩
        · exact ⟨openSegment_subset_segment ℝ _ _ hq.1,
            openSegment_subset_segment ℝ _ _ hq.2⟩
    have hunion : (⋃ e₁, ⋃ e₂, pairSet e₁ e₂).Finite := by
      apply Set.finite_iUnion
      intro e₁
      apply Set.finite_iUnion
      exact pairSet_finite e₁
    apply hunion.subset
    rintro p ⟨e₁, e₂, hne, hp₁, hp₂⟩
    simp only [Set.mem_iUnion]
    exact ⟨e₁, e₂, by simp [pairSet, hne, hp₁, hp₂]⟩
  let points := crossingSet_finite.toFinset
  have points_spec (p : EuclideanSpace ℝ (Fin 2)) :
      p ∈ points ↔ ∃ e₁ e₂ : A.graph.edgeFinset,
        e₁ ≠ e₂ ∧ p ∈ interior e₁ ∧ p ∈ interior e₂ := by
    simpa [points, crossingSet] using crossingSet_finite.mem_toFinset
  let incident (p : EuclideanSpace ℝ (Fin 2)) : Finset A.graph.edgeFinset :=
    Finset.univ.filter (fun e => p ∈ interior e)
  have mem_incident (p : EuclideanSpace ℝ (Fin 2)) (e : A.graph.edgeFinset) :
      e ∈ incident p ↔ p ∈ interior e := by
    simp [incident]
  have owner_inj_on_incident (p : EuclideanSpace ℝ (Fin 2))
      (s : Finset A.graph.edgeFinset) (hs : s ⊆ incident p) :
      Set.InjOn A.edgeOwner (s : Set A.graph.edgeFinset) := by
    intro e₁ he₁ e₂ he₂ ho
    by_contra hne
    have hp₁ : p ∈ interior e₁ := (mem_incident p e₁).1 (hs he₁)
    have hp₂ : p ∈ interior e₂ := (mem_incident p e₂).1 (hs he₂)
    exact (Set.disjoint_left.1
      (A.same_owner_openSegment_disjoint e₁ e₂ hne ho) hp₁) hp₂
  let localCount := points.sum (fun p => Nat.choose (incident p).card 2)
  have hcount : localCount ≤ A.retainedLines.card ^ 2 := by
    let localPairs := points.sigma fun p => (incident p).powersetCard 2
    have localCount_eq : localCount = localPairs.card := by
      simp [localCount, localPairs, Finset.card_sigma, Finset.card_powersetCard]
    let ownerPairs :=
      (Finset.univ : Finset A.retainedLines).powersetCard 2
    let ownerMap : localPairs → ownerPairs := fun z => by
      let image := z.1.2.image A.edgeOwner
      refine ⟨image, ?_⟩
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ image, ?_⟩
      have hz := Finset.mem_sigma.1 z.2
      have hzpair := Finset.mem_powersetCard.1 hz.2
      exact (Finset.card_image_iff.2
        (owner_inj_on_incident z.1.1 z.1.2 hzpair.1)).trans hzpair.2
    have ownerMap_injective : Function.Injective ownerMap := by
      rintro ⟨⟨p, s⟩, hs⟩ ⟨⟨q, t⟩, ht⟩ hab
      have hsigma := Finset.mem_sigma.1 hs
      have htigma := Finset.mem_sigma.1 ht
      have hspair := Finset.mem_powersetCard.1 hsigma.2
      have htpair := Finset.mem_powersetCard.1 htigma.2
      have himage : s.image A.edgeOwner = t.image A.edgeOwner := by
        exact congrArg Subtype.val hab
      have hpq : p = q := by
        obtain ⟨e₁, e₂, hene, hse⟩ := Finset.card_eq_two.1 hspair.2
        have hse' : s = {e₁, e₂} := by simpa only using hse
        have he₁s : e₁ ∈ s := by
          rw [hse']
          exact Finset.mem_insert_self _ _
        have he₂s : e₂ ∈ s := by
          rw [hse']
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have he₁owner : A.edgeOwner e₁ ∈ t.image A.edgeOwner := by
          rw [← himage]
          exact Finset.mem_image.2 ⟨e₁, he₁s, rfl⟩
        have he₂owner : A.edgeOwner e₂ ∈ t.image A.edgeOwner := by
          rw [← himage]
          exact Finset.mem_image.2 ⟨e₂, he₂s, rfl⟩
        obtain ⟨f₁, hf₁t, hf₁owner⟩ := Finset.mem_image.1 he₁owner
        obtain ⟨f₂, hf₂t, hf₂owner⟩ := Finset.mem_image.1 he₂owner
        apply owner_intersection_subsingleton e₁ e₂
          (fun ho => hene (owner_inj_on_incident p s hspair.1 he₁s he₂s ho))
        · exact ⟨point_on_owner e₁ ((mem_incident p e₁).1 (hspair.1 he₁s)),
            point_on_owner e₂ ((mem_incident p e₂).1 (hspair.1 he₂s))⟩
        · exact ⟨hf₁owner ▸ point_on_owner f₁
              ((mem_incident q f₁).1 (htpair.1 hf₁t)),
            hf₂owner ▸ point_on_owner f₂
              ((mem_incident q f₂).1 (htpair.1 hf₂t))⟩
      have hst : s = t := by
        apply Finset.Subset.antisymm
        · intro e hes
          have heowner : A.edgeOwner e ∈ t.image A.edgeOwner := by
            rw [← himage]
            exact Finset.mem_image.2 ⟨e, hes, rfl⟩
          obtain ⟨f, hft, hfo⟩ := Finset.mem_image.1 heowner
          by_contra hef
          have hef' : e ≠ f := fun h => hef (h ▸ hft)
          have hp_e : p ∈ interior e := (mem_incident p e).1 (hspair.1 hes)
          have hp_f : p ∈ interior f := by
            rw [hpq]
            exact (mem_incident q f).1 (htpair.1 hft)
          exact (Set.disjoint_left.1
            (A.same_owner_openSegment_disjoint e f hef' hfo.symm) hp_e) hp_f
        · intro f hft
          have hfowner : A.edgeOwner f ∈ s.image A.edgeOwner := by
            rw [himage]
            exact Finset.mem_image.2 ⟨f, hft, rfl⟩
          obtain ⟨e, hes, heo⟩ := Finset.mem_image.1 hfowner
          by_contra hfe
          have hfe' : f ≠ e := fun h => hfe (h ▸ hes)
          have hp_f : p ∈ interior f := by
            rw [hpq]
            exact (mem_incident q f).1 (htpair.1 hft)
          have hp_e : p ∈ interior e := (mem_incident p e).1 (hspair.1 hes)
          exact (Set.disjoint_left.1
            (A.same_owner_openSegment_disjoint f e hfe' heo.symm) hp_f) hp_e
      apply Subtype.ext
      exact Sigma.ext hpq (hst ▸ HEq.rfl)
    rw [localCount_eq]
    exact (Finset.card_le_card_of_injective ownerMap_injective).trans
      ((Finset.card_powersetCard 2
        (Finset.univ : Finset A.retainedLines)).trans_le (by
          simpa using Nat.choose_le_pow A.retainedLines.card 2))
  let D : GeometricArcDrawing A.graph := {
    vertexPlacement := fun p => p.1
    vertexPlacement_injective := Subtype.val_injective
    edgeSource := source
    edgeTarget := target
    edgeCarrier := carrier
    edgeRelativeInterior := interior
    edgeArc_endpoints := by
      intro e
      exact ⟨A.edgeSourceVertex e, A.edgeTargetVertex e, A.edge_adjacent e,
        A.edge_eq_mk e, Or.inl ⟨rfl, rfl⟩⟩
    edge_is_simple_lineSegment_or_circularArc := by
      intro e
      exact Or.inl ⟨source_ne_target e, rfl, rfl⟩
    no_vertex_in_edge_interior := by
      intro v e
      exact A.edge_no_point_in_openSegment e v
    no_shared_nondegenerate_subarc := by
      intro e₁ e₂ hne
      rintro ⟨gamma, -, hinj, hend, hrange⟩
      have hsub := carrier_intersection_subsingleton e₁ e₂ hne
      exact hend (hsub (hrange (Set.mem_range_self ⟨0, by simp⟩))
        (hrange (Set.mem_range_self ⟨1, by simp⟩)))
    intersectionPoints := points
    intersectionPoints_spec := points_spec
    localPairCount := localCount
    localPairCount_eq := by rfl
  }
  exact ⟨D, hcount⟩
