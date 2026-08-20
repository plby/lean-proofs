import ErdosProblems.Erdos733.ST.GeometricArcDrawingEdgeParametrization
import ErdosProblems.Erdos733.ST.PolygonalReplacementBoundaryPointData

open Classical
noncomputable section

universe u

-- [TABLET NODE: PolygonalReplacementBoundaryPointParametersExist]
lemma PolygonalReplacementBoundaryPointParametersExist {V : Type u} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (D : GeometricArcDrawing G)
    (controlDisks : PolygonalReplacementControlDiskData G D)
    (boundaryPoints :
      PolygonalReplacementBoundaryPointData.{u, u} G D controlDisks) :
    ∃ edgeParam :
        (e : G.edgeFinset) → Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2),
      (∀ e,
        Continuous (edgeParam e) ∧ Function.Injective (edgeParam e) ∧
          edgeParam e ⟨0, by simp⟩ = D.edgeSource e ∧
            edgeParam e ⟨1, by simp⟩ = D.edgeTarget e ∧
              D.edgeCarrier e = Set.range (edgeParam e) ∧
                D.edgeRelativeInterior e =
                  Set.range (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
                    edgeParam e
                      ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩)) ∧
        ∀ i : boundaryPoints.boundaryIndex,
          ∃! t : Set.Icc (0 : ℝ) 1,
            edgeParam (boundaryPoints.owner i) t = boundaryPoints.point i := by
-- BODY
  classical
  let edgeParam :
      (e : G.edgeFinset) → Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2) :=
    fun e => Classical.choose (GeometricArcDrawingEdgeParametrization D e)
  have edgeParam_spec :
      ∀ e,
        Continuous (edgeParam e) ∧ Function.Injective (edgeParam e) ∧
          edgeParam e ⟨0, by simp⟩ = D.edgeSource e ∧
            edgeParam e ⟨1, by simp⟩ = D.edgeTarget e ∧
              D.edgeCarrier e = Set.range (edgeParam e) ∧
                D.edgeRelativeInterior e =
                  Set.range (fun t : {t : ℝ // 0 < t ∧ t < 1} =>
                    edgeParam e
                      ⟨t.1, ⟨le_of_lt t.2.1, le_of_lt t.2.2⟩⟩) := by
    intro e
    exact Classical.choose_spec (GeometricArcDrawingEdgeParametrization D e)
  refine ⟨edgeParam, edgeParam_spec, ?_⟩
  intro i
  have hpoint_carrier :
      boundaryPoints.point i ∈ D.edgeCarrier (boundaryPoints.owner i) := by
    rcases boundaryPoints.point_on_control_boundary i with hvertex | hintersection
    · rcases hvertex with ⟨_v, _hv_owner, _hp_sphere, hp_carrier⟩
      exact hp_carrier
    · rcases hintersection with ⟨_x, _hx_owner, _hp_sphere, hp_carrier⟩
      exact hp_carrier
  rcases edgeParam_spec (boundaryPoints.owner i) with
    ⟨_hcont, hinj, _hsource, _htarget, hcarrier, _hinterior⟩
  rw [hcarrier] at hpoint_carrier
  rcases hpoint_carrier with ⟨t0, ht0⟩
  refine ⟨t0, ht0, ?_⟩
  intro t ht
  exact hinj (ht.trans ht0.symm)
