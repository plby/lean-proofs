import ErdosProblems.Erdos733.ST.EndpointFixedPolygonalDiskFillingClean
import ErdosProblems.Erdos733.ST.PolygonalReplacementTubeChainData

open Classical
noncomputable section

-- [TABLET NODE: PolygonalReplacementIntersectionDiskChains]
lemma PolygonalReplacementIntersectionDiskChains {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (tubeChains : PolygonalReplacementTubeChainData G D controlDisks) :
    ∃ intersection_chain :
        (x : {p // p ∈ D.intersectionPoints}) →
          {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e} → PolygonalArc,
      (∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
        (intersection_chain x e).source ≠ (intersection_chain x e).target) ∧
      (∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
        (intersection_chain x e).source ∈
            Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
          (intersection_chain x e).source ∈ D.edgeCarrier e.1) ∧
      (∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
        (intersection_chain x e).target ∈
            Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
          (intersection_chain x e).target ∈ D.edgeCarrier e.1) ∧
      (∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
        ∃! i : tubeChains.pieceIndex,
          tubeChains.owner i = e.1 ∧
            (tubeChains.source i = (intersection_chain x e).source ∨
              tubeChains.target i = (intersection_chain x e).source)) ∧
      (∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
        ∃! i : tubeChains.pieceIndex,
          tubeChains.owner i = e.1 ∧
            (tubeChains.source i = (intersection_chain x e).target ∨
              tubeChains.target i = (intersection_chain x e).target)) ∧
      (∀ ⦃x : {p // p ∈ D.intersectionPoints}⦄ ⦃e : G.edgeFinset⦄
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄
        (hxe : x.1 ∈ D.edgeRelativeInterior e),
        p ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) →
          p ∈ D.edgeCarrier e →
            (intersection_chain x ⟨e, hxe⟩).source = p ∨
              (intersection_chain x ⟨e, hxe⟩).target = p) ∧
      (∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
        (intersection_chain x e).carrier ⊆
          Metric.closedBall x.1 (controlDisks.intersectionRadius x)) ∧
      (∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
        (intersection_chain x e).relativeInterior ⊆
          Metric.ball x.1 (controlDisks.intersectionRadius x)) ∧
      (∀ x ⦃e f : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}⦄,
        e ≠ f →
          ¬ ∃ m n : ℕ,
            ∃ (hm : m + 1 < (intersection_chain x e).vertices.length)
              (hn : n + 1 < (intersection_chain x f).vertices.length),
              ∃ p q : EuclideanSpace ℝ (Fin 2),
                p ≠ q ∧
                  segment ℝ p q ⊆
                    segment ℝ (intersection_chain x e).vertices[m]
                        (intersection_chain x e).vertices[m + 1] ∩
                      segment ℝ (intersection_chain x f).vertices[n]
                        (intersection_chain x f).vertices[n + 1]) ∧
      (∀ x ⦃e f g : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}⦄
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        e ≠ f → e ≠ g → f ≠ g →
          p ∈ (intersection_chain x e).relativeInterior →
            p ∈ (intersection_chain x f).relativeInterior →
              p ∈ (intersection_chain x g).relativeInterior → False) ∧
      (∀ x ⦃e f : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}⦄
        ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
        e ≠ f →
          p ∈ (intersection_chain x e).relativeInterior →
            p ∈ (intersection_chain x f).relativeInterior →
              ∃ m n : ℕ,
                ∃ (hm : m + 1 < (intersection_chain x e).vertices.length)
                  (hn : n + 1 < (intersection_chain x f).vertices.length),
                  p ∈ segment ℝ (intersection_chain x e).vertices[m]
                      (intersection_chain x e).vertices[m + 1] ∧
                    p ∈ segment ℝ (intersection_chain x f).vertices[n]
                        (intersection_chain x f).vertices[n + 1] ∧
                      ¬ ∃ t : ℝ,
                        (intersection_chain x f).vertices[n + 1] -
                            (intersection_chain x f).vertices[n] =
                          t • ((intersection_chain x e).vertices[m + 1] -
                            (intersection_chain x e).vertices[m])) ∧
      (∀ x ⦃e f : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}⦄
        ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
        e ≠ f →
          p ∈ (intersection_chain x e).relativeInterior →
            p ∈ (intersection_chain x f).relativeInterior →
              q ∈ (intersection_chain x e).relativeInterior →
                q ∈ (intersection_chain x f).relativeInterior →
                  p = q) := by
-- BODY
  classical
  let endpointA :
      (x : {p // p ∈ D.intersectionPoints}) →
        {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e} →
          EuclideanSpace ℝ (Fin 2) :=
    fun x e =>
      Classical.choose
        (controlDisks.intersection_boundary_two_points (x := x) (e := e.1) e.2)
  let endpointB :
      (x : {p // p ∈ D.intersectionPoints}) →
        {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e} →
          EuclideanSpace ℝ (Fin 2) :=
    fun x e =>
      Classical.choose
        (Classical.choose_spec
          (controlDisks.intersection_boundary_two_points (x := x) (e := e.1) e.2))
  have endpointSpec :
      ∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
        endpointA x e ≠ endpointB x e ∧
          endpointA x e ∈
              Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
            endpointA x e ∈ D.edgeCarrier e.1 ∧
              endpointB x e ∈
                  Metric.sphere x.1 (controlDisks.intersectionRadius x) ∧
                endpointB x e ∈ D.edgeCarrier e.1 ∧
                  ∀ p,
                    p ∈ Metric.sphere x.1 (controlDisks.intersectionRadius x) →
                      p ∈ D.edgeCarrier e.1 →
                        p = endpointA x e ∨ p = endpointB x e := by
    intro x e
    exact
      Classical.choose_spec
        (Classical.choose_spec
          (controlDisks.intersection_boundary_two_points (x := x) (e := e.1) e.2))
  have endpointA_dist :
      ∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
        dist (endpointA x e) x.1 = controlDisks.intersectionRadius x := by
    intro x e
    simpa [Metric.mem_sphere, dist_eq_norm] using (endpointSpec x e).2.1
  have endpointB_dist :
      ∀ x (e : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}),
        dist (endpointB x e) x.1 = controlDisks.intersectionRadius x := by
    intro x e
    simpa [Metric.mem_sphere, dist_eq_norm] using (endpointSpec x e).2.2.2.1
  have endpointInjective :
      ∀ x,
        Function.Injective
          (fun y :
              ({e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e} ⊕
                {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}) =>
            Sum.elim (endpointA x) (endpointB x) y) := by
    intro x y z hyz
    cases y with
    | inl e =>
        cases z with
        | inl f =>
            have hAeq : endpointA x e = endpointA x f := by
              simpa using hyz
            have hedge : e.1 = f.1 := by
              exact
                controlDisks.intersection_boundary_point_edge_unique
                  (x := x) (e₁ := e.1) (e₂ := f.1) (p := endpointA x e)
                  e.2 f.2 (endpointSpec x e).2.1
                  (endpointSpec x e).2.2.1
                  (by simpa [hAeq] using (endpointSpec x f).2.2.1)
            have hsub : e = f := Subtype.ext hedge
            cases hsub
            rfl
        | inr f =>
            have hABeq : endpointA x e = endpointB x f := by
              simpa using hyz
            have hedge : e.1 = f.1 := by
              exact
                controlDisks.intersection_boundary_point_edge_unique
                  (x := x) (e₁ := e.1) (e₂ := f.1) (p := endpointA x e)
                  e.2 f.2 (endpointSpec x e).2.1
                  (endpointSpec x e).2.2.1
                  (by simpa [hABeq] using (endpointSpec x f).2.2.2.2.1)
            have hsub : e = f := Subtype.ext hedge
            have hsame : endpointA x e = endpointB x e := by
              simpa [hsub] using hABeq
            exact False.elim ((endpointSpec x e).1 hsame)
    | inr e =>
        cases z with
        | inl f =>
            have hBAeq : endpointB x e = endpointA x f := by
              simpa using hyz
            have hedge : e.1 = f.1 := by
              exact
                controlDisks.intersection_boundary_point_edge_unique
                  (x := x) (e₁ := e.1) (e₂ := f.1) (p := endpointB x e)
                  e.2 f.2 (endpointSpec x e).2.2.2.1
                  (endpointSpec x e).2.2.2.2.1
                  (by simpa [hBAeq] using (endpointSpec x f).2.2.1)
            have hsub : e = f := Subtype.ext hedge
            have hsame : endpointA x e = endpointB x e := by
              symm
              simpa [hsub] using hBAeq
            exact False.elim ((endpointSpec x e).1 hsame)
        | inr f =>
            have hBeq : endpointB x e = endpointB x f := by
              simpa using hyz
            have hedge : e.1 = f.1 := by
              exact
                controlDisks.intersection_boundary_point_edge_unique
                  (x := x) (e₁ := e.1) (e₂ := f.1) (p := endpointB x e)
                  e.2 f.2 (endpointSpec x e).2.2.2.1
                  (endpointSpec x e).2.2.2.2.1
                  (by simpa [hBeq] using (endpointSpec x f).2.2.2.2.1)
            have hsub : e = f := Subtype.ext hedge
            cases hsub
            rfl
  let fillingExists :
      (x : {p // p ∈ D.intersectionPoints}) →
        ∃ Γ : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e} → PolygonalArc,
          (∀ i,
            (Γ i).source = endpointA x i ∧
              (Γ i).target = endpointB x i ∧
                (Γ i).carrier ⊆ Metric.closedBall x.1 (controlDisks.intersectionRadius x) ∧
                  (Γ i).relativeInterior ⊆
                    Metric.ball x.1 (controlDisks.intersectionRadius x)) ∧
          (∀ ⦃i j : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}⦄,
            i ≠ j →
              ¬ ∃ m n : ℕ,
                ∃ (hm : m + 1 < (Γ i).vertices.length)
                  (hn : n + 1 < (Γ j).vertices.length),
                  ∃ p q : EuclideanSpace ℝ (Fin 2),
                    p ≠ q ∧
                      segment ℝ p q ⊆
                        segment ℝ (Γ i).vertices[m] (Γ i).vertices[m + 1] ∩
                          segment ℝ (Γ j).vertices[n] (Γ j).vertices[n + 1]) ∧
          (∀ ⦃i j k : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}⦄
            ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
            i ≠ j → i ≠ k → j ≠ k →
              p ∈ (Γ i).relativeInterior →
                p ∈ (Γ j).relativeInterior →
                  p ∈ (Γ k).relativeInterior → False) ∧
          (∀ ⦃i j : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}⦄
            ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
            i ≠ j →
              p ∈ (Γ i).relativeInterior →
                p ∈ (Γ j).relativeInterior →
                  ∃ m n : ℕ,
                    ∃ (hm : m + 1 < (Γ i).vertices.length)
                      (hn : n + 1 < (Γ j).vertices.length),
                      p ∈ segment ℝ (Γ i).vertices[m] (Γ i).vertices[m + 1] ∧
                        p ∈ segment ℝ (Γ j).vertices[n] (Γ j).vertices[n + 1] ∧
                          ¬ ∃ t : ℝ,
                            (Γ j).vertices[n + 1] - (Γ j).vertices[n] =
                              t • ((Γ i).vertices[m + 1] - (Γ i).vertices[m])) ∧
          (∀ ⦃i j : {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e}⦄
            ⦃p q : EuclideanSpace ℝ (Fin 2)⦄,
            i ≠ j →
              p ∈ (Γ i).relativeInterior →
                p ∈ (Γ j).relativeInterior →
                  q ∈ (Γ i).relativeInterior →
                    q ∈ (Γ j).relativeInterior →
                      p = q) := by
    intro x
    obtain ⟨Γ, hbasic, hnoShared, hnoTriple, htransverse, hunique, _hclean⟩ :=
      EndpointFixedPolygonalDiskFillingClean x.1
        (controlDisks.intersectionRadius x) (endpointA x) (endpointB x)
        (controlDisks.intersectionRadius_pos x) (endpointA_dist x)
        (endpointB_dist x) (endpointInjective x)
    exact ⟨Γ, hbasic, hnoShared, hnoTriple, htransverse, hunique⟩
  let intersectionChain :
      (x : {p // p ∈ D.intersectionPoints}) →
        {e : G.edgeFinset // x.1 ∈ D.edgeRelativeInterior e} →
          PolygonalArc :=
    fun x => Classical.choose (fillingExists x)
  have fillingSpec := fun x => Classical.choose_spec (fillingExists x)
  refine ⟨intersectionChain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x e hst
    have hsrc : (intersectionChain x e).source = endpointA x e :=
      ((fillingSpec x).1 e).1
    have htgt : (intersectionChain x e).target = endpointB x e :=
      ((fillingSpec x).1 e).2.1
    have hsame : endpointA x e = endpointB x e := by
      simpa [hsrc, htgt] using hst
    exact (endpointSpec x e).1 hsame
  · intro x e
    have hsrc : (intersectionChain x e).source = endpointA x e :=
      ((fillingSpec x).1 e).1
    constructor
    · simpa [hsrc] using (endpointSpec x e).2.1
    · simpa [hsrc] using (endpointSpec x e).2.2.1
  · intro x e
    have htgt : (intersectionChain x e).target = endpointB x e :=
      ((fillingSpec x).1 e).2.1
    constructor
    · simpa [htgt] using (endpointSpec x e).2.2.2.1
    · simpa [htgt] using (endpointSpec x e).2.2.2.2.1
  · intro x e
    have hsrc : (intersectionChain x e).source = endpointA x e :=
      ((fillingSpec x).1 e).1
    simpa [hsrc] using
      tubeChains.intersection_boundary_attached e.2 (endpointSpec x e).2.1
        (endpointSpec x e).2.2.1
  · intro x e
    have htgt : (intersectionChain x e).target = endpointB x e :=
      ((fillingSpec x).1 e).2.1
    simpa [htgt] using
      tubeChains.intersection_boundary_attached e.2 (endpointSpec x e).2.2.2.1
        (endpointSpec x e).2.2.2.2.1
  · intro x e p hxe hpSphere hpCarrier
    have hsrc : (intersectionChain x ⟨e, hxe⟩).source =
        endpointA x ⟨e, hxe⟩ :=
      ((fillingSpec x).1 ⟨e, hxe⟩).1
    have htgt : (intersectionChain x ⟨e, hxe⟩).target =
        endpointB x ⟨e, hxe⟩ :=
      ((fillingSpec x).1 ⟨e, hxe⟩).2.1
    rcases (endpointSpec x ⟨e, hxe⟩).2.2.2.2.2 p hpSphere hpCarrier with
      hpA | hpB
    · left
      exact hsrc.trans hpA.symm
    · right
      exact htgt.trans hpB.symm
  · intro x e
    exact ((fillingSpec x).1 e).2.2.1
  · intro x e
    exact ((fillingSpec x).1 e).2.2.2
  · intro x e f hef
    exact (fillingSpec x).2.1 hef
  · intro x e f g p hef heg hfg hpe hpf hpg
    exact (fillingSpec x).2.2.1 hef heg hfg hpe hpf hpg
  · intro x e f p hef hpe hpf
    exact (fillingSpec x).2.2.2.1 hef hpe hpf
  · intro x e f p q hef hpe hpf hqe hqf
    exact (fillingSpec x).2.2.2.2 hef hpe hpf hqe hqf
