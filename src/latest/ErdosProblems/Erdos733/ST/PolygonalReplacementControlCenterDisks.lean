import ErdosProblems.Erdos733.ST.GeometricArcDrawing

open Classical
noncomputable section

-- [TABLET NODE: PolygonalReplacementControlCenterDisks]
lemma PolygonalReplacementControlCenterDisks {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G) :
    ∃ vertexRadius : V → ℝ,
      ∃ intersectionRadius : {p // p ∈ D.intersectionPoints} → ℝ,
        (∀ v, 0 < vertexRadius v) ∧
          (∀ x, 0 < intersectionRadius x) ∧
            (∀ ⦃v w⦄, v ≠ w →
              Disjoint (Metric.closedBall (D.vertexPlacement v) (vertexRadius v))
                (Metric.closedBall (D.vertexPlacement w) (vertexRadius w))) ∧
              (∀ v x,
                Disjoint (Metric.closedBall (D.vertexPlacement v) (vertexRadius v))
                  (Metric.closedBall x.1 (intersectionRadius x))) ∧
                (∀ ⦃x y⦄, x ≠ y →
                  Disjoint (Metric.closedBall x.1 (intersectionRadius x))
                    (Metric.closedBall y.1 (intersectionRadius y))) := by
-- BODY
  let Index := V ⊕ {p // p ∈ D.intersectionPoints}
  let center : Index → EuclideanSpace ℝ (Fin 2) :=
    fun i => Sum.elim D.vertexPlacement (fun x => x.1) i
  have hcenter : Function.Injective center := by
    intro a b h
    cases a with
    | inl v =>
        cases b with
        | inl w =>
            have hvw : v = w := by
              apply D.vertexPlacement_injective
              simpa [center] using h
            subst hvw
            rfl
        | inr x =>
            exfalso
            have hx :=
              (D.intersectionPoints_spec x.1).mp x.2
            rcases hx with ⟨e₁, _e₂, _hne, hx₁, _hx₂⟩
            have hvx : D.vertexPlacement v = x.1 := by
              simpa [center] using h
            have hmem : D.vertexPlacement v ∈ D.edgeRelativeInterior e₁ := by
              simpa [← hvx] using hx₁
            exact (D.no_vertex_in_edge_interior v e₁) hmem
    | inr x =>
        cases b with
        | inl v =>
            exfalso
            have hx :=
              (D.intersectionPoints_spec x.1).mp x.2
            rcases hx with ⟨e₁, _e₂, _hne, hx₁, _hx₂⟩
            have hxv : x.1 = D.vertexPlacement v := by
              simpa [center] using h
            have hmem : D.vertexPlacement v ∈ D.edgeRelativeInterior e₁ := by
              simpa [hxv] using hx₁
            exact (D.no_vertex_in_edge_interior v e₁) hmem
        | inr y =>
            have hxy : x = y := by
              apply Subtype.ext
              simpa [center] using h
            subst hxy
            rfl
  let radius : Index → ℝ := fun i =>
    letI : Nonempty Index := ⟨i⟩
    (Finset.univ.inf' Finset.univ_nonempty
      (fun j : Index =>
        if i = j then (1 : ℝ) else dist (center i) (center j) / 3)) / 2
  have inf_pos :
      ∀ i,
        0 < Finset.univ.inf' (by
          letI : Nonempty Index := ⟨i⟩
          exact Finset.univ_nonempty)
          (fun j : Index =>
            if i = j then (1 : ℝ) else dist (center i) (center j) / 3) := by
    intro i
    letI : Nonempty Index := ⟨i⟩
    exact (Finset.lt_inf'_iff _).2 (by
      intro j _hj
      by_cases hij : i = j
      · simp [hij]
      · have hc_ne : center i ≠ center j := by
          intro hc
          exact hij (hcenter hc)
        simp [hij, dist_pos.mpr hc_ne])
  have radius_pos : ∀ i, 0 < radius i := by
    intro i
    dsimp [radius]
    exact half_pos (inf_pos i)
  have radius_lt :
      ∀ ⦃i j : Index⦄, i ≠ j → radius i < dist (center i) (center j) / 3 := by
    intro i j hij
    dsimp [radius]
    have hhalf :
        (Finset.univ.inf' (by
          letI : Nonempty Index := ⟨i⟩
          exact Finset.univ_nonempty)
          (fun j : Index =>
            if i = j then (1 : ℝ) else dist (center i) (center j) / 3)) / 2 <
          Finset.univ.inf' (by
            letI : Nonempty Index := ⟨i⟩
            exact Finset.univ_nonempty)
            (fun j : Index =>
              if i = j then (1 : ℝ) else dist (center i) (center j) / 3) :=
      half_lt_self (inf_pos i)
    have hle :
        Finset.univ.inf' (by
          letI : Nonempty Index := ⟨i⟩
          exact Finset.univ_nonempty)
          (fun j : Index =>
            if i = j then (1 : ℝ) else dist (center i) (center j) / 3) ≤
          dist (center i) (center j) / 3 := by
      have hle' :=
        Finset.inf'_le
          (fun j : Index =>
            if i = j then (1 : ℝ) else dist (center i) (center j) / 3)
          (Finset.mem_univ j)
      rw [if_neg hij] at hle'
      exact hle'
    exact hhalf.trans_le hle
  have radius_disjoint :
      ∀ ⦃i j : Index⦄, i ≠ j →
        Disjoint (Metric.closedBall (center i) (radius i))
          (Metric.closedBall (center j) (radius j)) := by
    intro i j hij
    apply Metric.closedBall_disjoint_closedBall
    have hi : radius i < dist (center i) (center j) / 3 := radius_lt hij
    have hj : radius j < dist (center i) (center j) / 3 := by
      simpa [dist_comm] using radius_lt (i := j) (j := i) (Ne.symm hij)
    have hdist_pos : 0 < dist (center i) (center j) := by
      exact dist_pos.mpr (by
        intro hc
        exact hij (hcenter hc))
    nlinarith
  refine ⟨fun v => radius (Sum.inl v), fun x => radius (Sum.inr x), ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    exact radius_pos (Sum.inl v)
  · intro x
    exact radius_pos (Sum.inr x)
  · intro v w hvw
    have hidx : (Sum.inl v : Index) ≠ Sum.inl w := by
      intro h
      exact hvw (by simpa using h)
    simpa [center] using radius_disjoint hidx
  · intro v x
    have hidx : (Sum.inl v : Index) ≠ Sum.inr x := by
      intro h
      cases h
    simpa [center] using radius_disjoint hidx
  · intro x y hxy
    have hidx : (Sum.inr x : Index) ≠ Sum.inr y := by
      intro h
      exact hxy (by simpa using h)
    simpa [center] using radius_disjoint hidx
