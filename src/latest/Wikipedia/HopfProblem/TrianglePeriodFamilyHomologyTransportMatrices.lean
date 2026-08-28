import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportRegular
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyExteriorLatticeMatrices

/-!
# Actual regular-family transport in the ordered minor bases

These matrices represent the actual singular-homology transport maps.
The six-coordinate basis has ordered pairs `01,02,03,12,13,23`; the
four-coordinate basis has ordered triples `012,013,023,123`.

Every triangle-group element is realized by an actual projected loop.
The chosen realizing loops are not asserted to be geometric meridians.
-/

noncomputable section

open UpperHalfPlane
open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomologyExterior LocalSystemMatrices

variable (P : HolomorphicPeriodMap ℂ ℍ)
  (h₁ : ∀ z : ℍ, P.point (Triangle.generatorOneSL • z) = (P.point z).step₁)
  (h₂ : ∀ z : ℍ, P.point (Triangle.generatorTwoSL • z) = (P.point z).step₂)

/-- Ordered minor coordinates for the actual integral singular homology of a regular fibre. -/
def regularFibreSingularH2Coordinates (b : TriangleRegularPoint) :
    SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 2 ≃ₗ[ℤ]
      (Fin 6 → ℤ) :=
  (regularFibreSingularH2Equiv P h₁ h₂ b).trans squareCoordinates

/-- The actual loop transport is the ordered-minor matrix of its actual lattice monodromy. -/
theorem regularTransport_singularH2Coordinates (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b))
    (a : SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 2) :
    regularFibreSingularH2Coordinates P h₁ h₂ b
      (singularHomologyMap (regularTransport P h₁ h₂ γ :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) 2 a) =
      exteriorSquare (regularLatticeTransportHom P h₁ h₂ b γ : LatticeMatrix) *ᵥ
        regularFibreSingularH2Coordinates P h₁ h₂ b a := by
  change squareCoordinates (regularFibreSingularH2Equiv P h₁ h₂ b
    (singularHomologyMap (regularTransport P h₁ h₂ γ :
      C(RegularFibre P h₁ h₂ (triangleRegularProject b),
        RegularFibre P h₁ h₂ (triangleRegularProject b))) 2 a)) = _
  rw [regularTransport_singularH2]
  exact squareCoordinates_map (regularLatticeTransportHom P h₁ h₂ b γ : LatticeMatrix)
    (regularFibreSingularH2Equiv P h₁ h₂ b a)

/-- An equality of the actual conjugated homology map with its literal minor-matrix map. -/
theorem regularTransport_singularH2Coordinates_conjugate (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b)) :
    (regularFibreSingularH2Coordinates P h₁ h₂ b).toLinearMap.comp
      ((singularHomologyMap (regularTransport P h₁ h₂ γ :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) 2).comp
        (regularFibreSingularH2Coordinates P h₁ h₂ b).symm.toLinearMap) =
      (exteriorSquare (regularLatticeTransportHom P h₁ h₂ b γ : LatticeMatrix)).mulVecLin := by
  apply LinearMap.ext
  intro v
  change regularFibreSingularH2Coordinates P h₁ h₂ b
    (singularHomologyMap (regularTransport P h₁ h₂ γ :
      C(RegularFibre P h₁ h₂ (triangleRegularProject b),
        RegularFibre P h₁ h₂ (triangleRegularProject b))) 2
      ((regularFibreSingularH2Coordinates P h₁ h₂ b).symm v)) = _
  rw [regularTransport_singularH2Coordinates, LinearEquiv.apply_symm_apply]
  rfl

/-- Every triangle element is realized on actual fibre homology, with its proved minor matrix. -/
theorem regularDeckLoop_transport_singularH2Coordinates (b : TriangleRegularPoint)
    (g : TriangleGroup)
    (a : SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 2) :
    regularFibreSingularH2Coordinates P h₁ h₂ b
      (singularHomologyMap
        (regularPathTransport P h₁ h₂ (regularDeckLoop P h₁ h₂ b g) :
          C(RegularFibre P h₁ h₂ (triangleRegularProject b),
            RegularFibre P h₁ h₂ (triangleRegularProject b))) 2 a) =
      exteriorSquare (triangleDualRepresentation g : LatticeMatrix) *ᵥ
        regularFibreSingularH2Coordinates P h₁ h₂ b a := by
  change squareCoordinates (regularFibreSingularH2Equiv P h₁ h₂ b
    (singularHomologyMap
      (regularPathTransport P h₁ h₂ (regularDeckLoop P h₁ h₂ b g) :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) 2 a)) = _
  rw [regularDeckLoop_transport_singularH2]
  exact squareCoordinates_map (triangleDualRepresentation g : LatticeMatrix)
    (regularFibreSingularH2Equiv P h₁ h₂ b a)

theorem regularDeckLoop_generator₁_singularH2Coordinates (b : TriangleRegularPoint)
    (a : SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 2) :
    regularFibreSingularH2Coordinates P h₁ h₂ b
      (singularHomologyMap
        (regularPathTransport P h₁ h₂ (regularDeckLoop P h₁ h₂ b triangleGenerator₁) :
          C(RegularFibre P h₁ h₂ (triangleRegularProject b),
            RegularFibre P h₁ h₂ (triangleRegularProject b))) 2 a) =
      squareA₁ *ᵥ regularFibreSingularH2Coordinates P h₁ h₂ b a := by
  rw [regularDeckLoop_transport_singularH2Coordinates, triangleDualRepresentation_generator₁_matrix]
  rfl

theorem regularDeckLoop_generator₂_singularH2Coordinates (b : TriangleRegularPoint)
    (a : SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 2) :
    regularFibreSingularH2Coordinates P h₁ h₂ b
      (singularHomologyMap
        (regularPathTransport P h₁ h₂ (regularDeckLoop P h₁ h₂ b triangleGenerator₂) :
          C(RegularFibre P h₁ h₂ (triangleRegularProject b),
            RegularFibre P h₁ h₂ (triangleRegularProject b))) 2 a) =
      squareA₂ *ᵥ regularFibreSingularH2Coordinates P h₁ h₂ b a := by
  rw [regularDeckLoop_transport_singularH2Coordinates, triangleDualRepresentation_generator₂_matrix]
  rfl

theorem regularDeckLoop_cusp_singularH2Coordinates (b : TriangleRegularPoint)
    (a : SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 2) :
    regularFibreSingularH2Coordinates P h₁ h₂ b
      (singularHomologyMap
        (regularPathTransport P h₁ h₂ (regularDeckLoop P h₁ h₂ b triangleCuspGenerator) :
          C(RegularFibre P h₁ h₂ (triangleRegularProject b),
            RegularFibre P h₁ h₂ (triangleRegularProject b))) 2 a) =
      squareM₀ *ᵥ regularFibreSingularH2Coordinates P h₁ h₂ b a := by
  rw [regularDeckLoop_transport_singularH2Coordinates, triangleDualRepresentation_cusp_matrix]
  rfl

/-- Ordered minor coordinates for the actual integral singular homology of a regular fibre. -/
def regularFibreSingularH3Coordinates (b : TriangleRegularPoint) :
    SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 3 ≃ₗ[ℤ]
      (Fin 4 → ℤ) :=
  (regularFibreSingularH3Equiv P h₁ h₂ b).trans cubeCoordinates

/-- The actual loop transport is the ordered-minor matrix of its actual lattice monodromy. -/
theorem regularTransport_singularH3Coordinates (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b))
    (a : SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 3) :
    regularFibreSingularH3Coordinates P h₁ h₂ b
      (singularHomologyMap (regularTransport P h₁ h₂ γ :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) 3 a) =
      exteriorCube (regularLatticeTransportHom P h₁ h₂ b γ : LatticeMatrix) *ᵥ
        regularFibreSingularH3Coordinates P h₁ h₂ b a := by
  change cubeCoordinates (regularFibreSingularH3Equiv P h₁ h₂ b
    (singularHomologyMap (regularTransport P h₁ h₂ γ :
      C(RegularFibre P h₁ h₂ (triangleRegularProject b),
        RegularFibre P h₁ h₂ (triangleRegularProject b))) 3 a)) = _
  rw [regularTransport_singularH3]
  exact cubeCoordinates_map (regularLatticeTransportHom P h₁ h₂ b γ : LatticeMatrix)
    (regularFibreSingularH3Equiv P h₁ h₂ b a)

/-- An equality of the actual conjugated homology map with its literal minor-matrix map. -/
theorem regularTransport_singularH3Coordinates_conjugate (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b)) :
    (regularFibreSingularH3Coordinates P h₁ h₂ b).toLinearMap.comp
      ((singularHomologyMap (regularTransport P h₁ h₂ γ :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) 3).comp
        (regularFibreSingularH3Coordinates P h₁ h₂ b).symm.toLinearMap) =
      (exteriorCube (regularLatticeTransportHom P h₁ h₂ b γ : LatticeMatrix)).mulVecLin := by
  apply LinearMap.ext
  intro v
  change regularFibreSingularH3Coordinates P h₁ h₂ b
    (singularHomologyMap (regularTransport P h₁ h₂ γ :
      C(RegularFibre P h₁ h₂ (triangleRegularProject b),
        RegularFibre P h₁ h₂ (triangleRegularProject b))) 3
      ((regularFibreSingularH3Coordinates P h₁ h₂ b).symm v)) = _
  rw [regularTransport_singularH3Coordinates, LinearEquiv.apply_symm_apply]
  rfl

/-- Every triangle element is realized on actual fibre homology, with its proved minor matrix. -/
theorem regularDeckLoop_transport_singularH3Coordinates (b : TriangleRegularPoint)
    (g : TriangleGroup)
    (a : SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 3) :
    regularFibreSingularH3Coordinates P h₁ h₂ b
      (singularHomologyMap
        (regularPathTransport P h₁ h₂ (regularDeckLoop P h₁ h₂ b g) :
          C(RegularFibre P h₁ h₂ (triangleRegularProject b),
            RegularFibre P h₁ h₂ (triangleRegularProject b))) 3 a) =
      exteriorCube (triangleDualRepresentation g : LatticeMatrix) *ᵥ
        regularFibreSingularH3Coordinates P h₁ h₂ b a := by
  change cubeCoordinates (regularFibreSingularH3Equiv P h₁ h₂ b
    (singularHomologyMap
      (regularPathTransport P h₁ h₂ (regularDeckLoop P h₁ h₂ b g) :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) 3 a)) = _
  rw [regularDeckLoop_transport_singularH3]
  exact cubeCoordinates_map (triangleDualRepresentation g : LatticeMatrix)
    (regularFibreSingularH3Equiv P h₁ h₂ b a)

theorem regularDeckLoop_generator₁_singularH3Coordinates (b : TriangleRegularPoint)
    (a : SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 3) :
    regularFibreSingularH3Coordinates P h₁ h₂ b
      (singularHomologyMap
        (regularPathTransport P h₁ h₂ (regularDeckLoop P h₁ h₂ b triangleGenerator₁) :
          C(RegularFibre P h₁ h₂ (triangleRegularProject b),
            RegularFibre P h₁ h₂ (triangleRegularProject b))) 3 a) =
      cubeA₁ *ᵥ regularFibreSingularH3Coordinates P h₁ h₂ b a := by
  rw [regularDeckLoop_transport_singularH3Coordinates, triangleDualRepresentation_generator₁_matrix]
  rfl

theorem regularDeckLoop_generator₂_singularH3Coordinates (b : TriangleRegularPoint)
    (a : SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 3) :
    regularFibreSingularH3Coordinates P h₁ h₂ b
      (singularHomologyMap
        (regularPathTransport P h₁ h₂ (regularDeckLoop P h₁ h₂ b triangleGenerator₂) :
          C(RegularFibre P h₁ h₂ (triangleRegularProject b),
            RegularFibre P h₁ h₂ (triangleRegularProject b))) 3 a) =
      cubeA₂ *ᵥ regularFibreSingularH3Coordinates P h₁ h₂ b a := by
  rw [regularDeckLoop_transport_singularH3Coordinates, triangleDualRepresentation_generator₂_matrix]
  rfl

theorem regularDeckLoop_cusp_singularH3Coordinates (b : TriangleRegularPoint)
    (a : SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 3) :
    regularFibreSingularH3Coordinates P h₁ h₂ b
      (singularHomologyMap
        (regularPathTransport P h₁ h₂ (regularDeckLoop P h₁ h₂ b triangleCuspGenerator) :
          C(RegularFibre P h₁ h₂ (triangleRegularProject b),
            RegularFibre P h₁ h₂ (triangleRegularProject b))) 3 a) =
      cubeM₀ *ᵥ regularFibreSingularH3Coordinates P h₁ h₂ b a := by
  rw [regularDeckLoop_transport_singularH3Coordinates, triangleDualRepresentation_cusp_matrix]
  rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily

