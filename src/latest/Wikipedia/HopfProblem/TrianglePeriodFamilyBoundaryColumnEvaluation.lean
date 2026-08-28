import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryIntersectionComponents

/-!
# Boundary comparison from genuine component labels and fibre maps

Both columns are evaluated by their actual quarter-time maps. If geometry
proves which actual overlap component contains each map, the comparison is
the corresponding two-column block map with the actual fibre-coordinate
homology maps as entries. There is no assumed identification of a filling
map with a named integer matrix.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SingularMayerVietoris Homology
open MappingTorus.HomologyCover

variable {X : Type} [TopologicalSpace X]
  (D : Data ℂ TriangleRegularPoint) (φ : X ≃ₜ X)
  (F : C(MappingTorus.Torus φ, D.Space))
  (hU : Set.MapsTo F (U φ) (upperFamily D))
  (hV : Set.MapsTo F (V φ) (lowerFamily D))
  (b : SlitBaseLift) (i₀ i₁ : Fin 3)
  (h₀ : ∀ x, lowerColumnMap φ D F hU hV x ∈ intersectionPiece D i₀)
  (h₁ : ∀ x, upperColumnMap φ D F hU hV x ∈ intersectionPiece D i₁)

/-- The lower column occupies its geometrically proved component and retains
its actual fibre map. -/
theorem intersectionComparison_lower_component (n : ℕ) (a : SingularHomology X n) :
    intersectionComparison D φ F hU hV b n (a, 0) =
      componentCoordinates i₀
        (singularHomologyMap
          (componentFibreMap D b (lowerColumnMap φ D F hU hV) i₀ h₀) n a) :=
  (intersectionComparison_lowerColumn φ D F hU hV b n a).trans
    (intersectionHomology_componentMap D b (lowerColumnMap φ D F hU hV) i₀ h₀ n a)

/-- The upper column occupies its proved component with its complete actual fibre map. -/
theorem intersectionComparison_upper_component (n : ℕ) (a : SingularHomology X n) :
    intersectionComparison D φ F hU hV b n (0, a) =
      componentCoordinates i₁
        (singularHomologyMap
          (componentFibreMap D b (upperColumnMap φ D F hU hV) i₁ h₁) n a) :=
  (intersectionComparison_upperColumn φ D F hU hV b n a).trans
    (intersectionHomology_componentMap D b (upperColumnMap φ D F hU hV) i₁ h₁ n a)

/-- The entire actual intersection comparison is determined by the two actual component maps. -/
theorem intersectionComparison_geometric_pair (n : ℕ)
    (a₀ a₁ : SingularHomology X n) :
    intersectionComparison D φ F hU hV b n (a₀, a₁) =
      componentCoordinates i₀
        (singularHomologyMap
          (componentFibreMap D b (lowerColumnMap φ D F hU hV) i₀ h₀) n a₀) +
      componentCoordinates i₁
        (singularHomologyMap
          (componentFibreMap D b (upperColumnMap φ D F hU hV) i₁ h₁) n a₁) := by
  have hpair : (a₀, a₁) = (a₀, (0 : SingularHomology X n)) + (0, a₁) := by
    ext <;> simp
  rw [hpair, map_add, intersectionComparison_lower_component D φ F hU hV b i₀ h₀,
    intersectionComparison_upper_component D φ F hU hV b i₁ h₁]

/-- The source-oriented actual boundary is computed by the actual geometric columns.
This retains the fixed meridian change of coordinates from the regular-family calculation. -/
theorem sourceKernelProjection_geometric_columns
    (h₀' : ∀ x, lowerColumnMap φ D F hU hV x ∈ intersectionPiece D i₀)
    (h₁' : ∀ x, upperColumnMap φ D F hU hV x ∈ intersectionPiece D i₁)
    (n : ℕ) (a : SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    (sourceKernelProjection D n (singularHomologyMap F (n + 1) a) :
      SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) =
      normalizedSourceDomainEquiv n
        (-componentCoordinates i₀
          (singularHomologyMap
            (componentFibreMap D normalizedSlitBaseLift
              (lowerColumnMap φ D F hU hV) i₀ h₀') n
            (MappingTorusHomology.wangBoundary φ n a)) +
        componentCoordinates i₁
          (singularHomologyMap
            (componentFibreMap D normalizedSlitBaseLift
              (upperColumnMap φ D F hU hV) i₁ h₁') n
            (MappingTorusHomology.wangBoundary φ n a))).2 := by
  rw [sourceKernelProjection_wangBoundary D φ F hU hV n a,
    intersectionComparison_antidiagonal,
    intersectionComparison_lower_component D φ F hU hV normalizedSlitBaseLift i₀ h₀',
    intersectionComparison_upper_component D φ F hU hV normalizedSlitBaseLift i₁ h₁']

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
