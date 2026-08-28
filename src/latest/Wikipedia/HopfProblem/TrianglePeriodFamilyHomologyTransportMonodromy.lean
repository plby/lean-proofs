import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportMarking
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportFunctor

/-!
# Actual higher-homology monodromy of transported family fibres

The proved commutative square of actual fibre homeomorphisms computes the
actual singular-homology action. Its exterior action uses the inverse lifted
endpoint, exactly as in degree one. Specified projected paths prove their own
endpoint; no geometric-meridian property is attributed to a chosen path.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Data

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusHigherHomologyExterior LocalSystemMatrices

variable {V B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
  (D : TrianglePeriodFamily.Data V B)
  (hq : IsQuotientCoveringMap D.baseQuotient TriangleGroup)

/-- The actual degree-2 action of every loop is the exterior action of its lifted endpoint. -/
theorem transport_singularH2 (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b))
    (a : SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 2) :
    D.fibreSingularH2Equiv hq b
      (singularHomologyMap (D.transport hq γ :
        C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) 2 a) =
      exteriorPower.map 2 (D.latticeTransportHom hq b γ : LatticeMatrix).mulVecLin
        (D.fibreSingularH2Equiv hq b a) := by
  obtain ⟨a, rfl⟩ := (homeomorphHomologyEquiv (D.flatFibreHomeomorph hq b) 2).surjective a
  change D.fibreSingularH2Equiv hq b
    (singularHomologyMap (D.transport hq γ :
      C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) 2
      (singularHomologyMap (D.flatFibreHomeomorph hq b :
        C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b})) 2 a)) =
    exteriorPower.map 2 (D.latticeTransportHom hq b γ : LatticeMatrix).mulVecLin
      (D.fibreSingularH2Equiv hq b
        (singularHomologyMap (D.flatFibreHomeomorph hq b :
          C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b})) 2 a))
  rw [D.transport_inducedHomologyDegree_flat, D.fibreSingularH2Equiv_inducedHomology_flat,
    FlatTorus.singularH2Equiv_inducedHomology_triangle,
    D.fibreSingularH2Equiv_inducedHomology_flat, D.latticeTransportHom_apply]

/-- Conjugating actual fibre transport gives the actual exterior-power linear map. -/
theorem transport_singularH2_conjugate (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b)) :
    (D.fibreSingularH2Equiv hq b).toLinearMap.comp
      ((singularHomologyMap (D.transport hq γ :
        C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) 2).comp
          (D.fibreSingularH2Equiv hq b).symm.toLinearMap) =
      exteriorPower.map 2 (D.latticeTransportHom hq b γ : LatticeMatrix).mulVecLin := by
  apply LinearMap.ext
  intro c
  change D.fibreSingularH2Equiv hq b
    (singularHomologyMap (D.transport hq γ :
      C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) 2
      ((D.fibreSingularH2Equiv hq b).symm c)) = _
  rw [D.transport_singularH2, LinearEquiv.apply_symm_apply]

/-- An inverse deck endpoint computes the action of that deck element, with its sign convention. -/
theorem transport_singularH2_of_inverse_endpoint (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b)) (g : TriangleGroup)
    (hγ : (hq.isCoveringMap.monodromy γ ⟨b, rfl⟩ : B) = g⁻¹ • b)
    (a : SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 2) :
    D.fibreSingularH2Equiv hq b
      (singularHomologyMap (D.transport hq γ :
        C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) 2 a) =
      exteriorPower.map 2 (triangleDualRepresentation g : LatticeMatrix).mulVecLin
        (D.fibreSingularH2Equiv hq b a) := by
  rw [D.transport_singularH2, D.latticeTransportHom_eq_of_inverse_endpoint hq b γ g hγ]

/-- A positive deck endpoint gives the inverse deck action in the initial fibre marking. -/
theorem transport_singularH2_of_endpoint (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b)) (g : TriangleGroup)
    (hγ : (hq.isCoveringMap.monodromy γ ⟨b, rfl⟩ : B) = g • b)
    (a : SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 2) :
    D.fibreSingularH2Equiv hq b
      (singularHomologyMap (D.transport hq γ :
        C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) 2 a) =
      exteriorPower.map 2 (triangleDualRepresentation g⁻¹ : LatticeMatrix).mulVecLin
        (D.fibreSingularH2Equiv hq b a) := by
  rw [D.transport_singularH2, D.latticeTransportHom_eq_of_endpoint hq b γ g hγ]

/-- The specified upstairs path computes its actual induced fibre map
without an endpoint assumption. -/
theorem projectedLoop_transport_singularH2 (b : B) (g : TriangleGroup)
    (δ : Path b (g⁻¹ • b))
    (a : SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 2) :
    D.fibreSingularH2Equiv hq b
      (singularHomologyMap (D.pathTransport hq (D.projectedLoop hq b g δ) :
        C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) 2 a) =
      exteriorPower.map 2 (triangleDualRepresentation g : LatticeMatrix).mulVecLin
        (D.fibreSingularH2Equiv hq b a) := by
  change D.fibreSingularH2Equiv hq b
    (singularHomologyMap (D.transport hq
      (Path.Homotopic.Quotient.mk (D.projectedLoop hq b g δ)) :
      C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) 2 a) = _
  rw [D.transport_singularH2, D.latticeTransportHom_projectedLoop]

/-- The same actual transport action in the literal ordered-minor coordinates. -/
theorem transport_singularH2Coordinates (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b))
    (a : SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 2) :
    D.fibreSingularH2Coordinates hq b
      (singularHomologyMap (D.transport hq γ :
        C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) 2 a) =
      exteriorSquare (D.latticeTransportHom hq b γ : LatticeMatrix) *ᵥ
        D.fibreSingularH2Coordinates hq b a := by
  change squareCoordinates (D.fibreSingularH2Equiv hq b
    (singularHomologyMap (D.transport hq γ :
      C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) 2 a)) = _
  rw [D.transport_singularH2]
  exact squareCoordinates_map (D.latticeTransportHom hq b γ : LatticeMatrix)
    (D.fibreSingularH2Equiv hq b a)

/-- The actual degree-3 action of every loop is the exterior action of its lifted endpoint. -/
theorem transport_singularH3 (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b))
    (a : SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 3) :
    D.fibreSingularH3Equiv hq b
      (singularHomologyMap (D.transport hq γ :
        C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) 3 a) =
      exteriorPower.map 3 (D.latticeTransportHom hq b γ : LatticeMatrix).mulVecLin
        (D.fibreSingularH3Equiv hq b a) := by
  obtain ⟨a, rfl⟩ := (homeomorphHomologyEquiv (D.flatFibreHomeomorph hq b) 3).surjective a
  change D.fibreSingularH3Equiv hq b
    (singularHomologyMap (D.transport hq γ :
      C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) 3
      (singularHomologyMap (D.flatFibreHomeomorph hq b :
        C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b})) 3 a)) =
    exteriorPower.map 3 (D.latticeTransportHom hq b γ : LatticeMatrix).mulVecLin
      (D.fibreSingularH3Equiv hq b
        (singularHomologyMap (D.flatFibreHomeomorph hq b :
          C(RealTorus₄, D.projection ⁻¹' {D.baseQuotient b})) 3 a))
  rw [D.transport_inducedHomologyDegree_flat, D.fibreSingularH3Equiv_inducedHomology_flat,
    FlatTorus.singularH3Equiv_inducedHomology_triangle,
    D.fibreSingularH3Equiv_inducedHomology_flat, D.latticeTransportHom_apply]

/-- Conjugating actual fibre transport gives the actual exterior-power linear map. -/
theorem transport_singularH3_conjugate (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b)) :
    (D.fibreSingularH3Equiv hq b).toLinearMap.comp
      ((singularHomologyMap (D.transport hq γ :
        C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) 3).comp
          (D.fibreSingularH3Equiv hq b).symm.toLinearMap) =
      exteriorPower.map 3 (D.latticeTransportHom hq b γ : LatticeMatrix).mulVecLin := by
  apply LinearMap.ext
  intro c
  change D.fibreSingularH3Equiv hq b
    (singularHomologyMap (D.transport hq γ :
      C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) 3
      ((D.fibreSingularH3Equiv hq b).symm c)) = _
  rw [D.transport_singularH3, LinearEquiv.apply_symm_apply]

/-- An inverse deck endpoint computes the action of that deck element, with its sign convention. -/
theorem transport_singularH3_of_inverse_endpoint (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b)) (g : TriangleGroup)
    (hγ : (hq.isCoveringMap.monodromy γ ⟨b, rfl⟩ : B) = g⁻¹ • b)
    (a : SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 3) :
    D.fibreSingularH3Equiv hq b
      (singularHomologyMap (D.transport hq γ :
        C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) 3 a) =
      exteriorPower.map 3 (triangleDualRepresentation g : LatticeMatrix).mulVecLin
        (D.fibreSingularH3Equiv hq b a) := by
  rw [D.transport_singularH3, D.latticeTransportHom_eq_of_inverse_endpoint hq b γ g hγ]

/-- A positive deck endpoint gives the inverse deck action in the initial fibre marking. -/
theorem transport_singularH3_of_endpoint (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b)) (g : TriangleGroup)
    (hγ : (hq.isCoveringMap.monodromy γ ⟨b, rfl⟩ : B) = g • b)
    (a : SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 3) :
    D.fibreSingularH3Equiv hq b
      (singularHomologyMap (D.transport hq γ :
        C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) 3 a) =
      exteriorPower.map 3 (triangleDualRepresentation g⁻¹ : LatticeMatrix).mulVecLin
        (D.fibreSingularH3Equiv hq b a) := by
  rw [D.transport_singularH3, D.latticeTransportHom_eq_of_endpoint hq b γ g hγ]

/-- The specified upstairs path computes its actual induced fibre map
without an endpoint assumption. -/
theorem projectedLoop_transport_singularH3 (b : B) (g : TriangleGroup)
    (δ : Path b (g⁻¹ • b))
    (a : SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 3) :
    D.fibreSingularH3Equiv hq b
      (singularHomologyMap (D.pathTransport hq (D.projectedLoop hq b g δ) :
        C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) 3 a) =
      exteriorPower.map 3 (triangleDualRepresentation g : LatticeMatrix).mulVecLin
        (D.fibreSingularH3Equiv hq b a) := by
  change D.fibreSingularH3Equiv hq b
    (singularHomologyMap (D.transport hq
      (Path.Homotopic.Quotient.mk (D.projectedLoop hq b g δ)) :
      C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) 3 a) = _
  rw [D.transport_singularH3, D.latticeTransportHom_projectedLoop]

/-- The same actual transport action in the literal ordered-minor coordinates. -/
theorem transport_singularH3Coordinates (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b))
    (a : SingularHomology (D.projection ⁻¹' {D.baseQuotient b}) 3) :
    D.fibreSingularH3Coordinates hq b
      (singularHomologyMap (D.transport hq γ :
        C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) 3 a) =
      exteriorCube (D.latticeTransportHom hq b γ : LatticeMatrix) *ᵥ
        D.fibreSingularH3Coordinates hq b a := by
  change cubeCoordinates (D.fibreSingularH3Equiv hq b
    (singularHomologyMap (D.transport hq γ :
      C(D.projection ⁻¹' {D.baseQuotient b}, D.projection ⁻¹' {D.baseQuotient b})) 3 a)) = _
  rw [D.transport_singularH3]
  exact cubeCoordinates_map (D.latticeTransportHom hq b γ : LatticeMatrix)
    (D.fibreSingularH3Equiv hq b a)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Data
