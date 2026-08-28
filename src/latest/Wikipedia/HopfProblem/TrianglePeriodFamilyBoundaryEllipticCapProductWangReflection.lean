import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapProductWangReflectionCore

/-!
# The signed actual Wang boundary under time reflection

The literal map of the two actual intersections exchanges their components.
Naturality of the genuine singular Mayer--Vietoris connecting homomorphism
therefore gives the negative sign in the Wang boundary. Both quarter-time
fibre maps retain the actual inverse target monodromy coordinate change.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct

open SingularMayerVietoris PeriodTorusHigherHomology MappingTorus MappingTorus.HomologyCover

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (f : X ≃ₜ X) (g : Y ≃ₜ Y) (F : C(Torus f, Torus g))
  (G : ℝ → C(X, Y))
  (hF : ∀ (t : ℝ) (x : X), F (mk f (t, x)) = mk g (-t, G t x))

include hF

/-- The homology map of the actual reflected intersection, in the two
genuine component markings. -/
def reflectionIntersectionComparison (n : ℕ) :
    (SingularHomology X n × SingularHomology X n) →ₗ[ℤ]
      (SingularHomology Y n × SingularHomology Y n) :=
  (MappingTorusHomology.intersectionHomologyEquiv g n).toLinearMap.comp
    ((singularHomologyMap (reflectionIntersectionMap f g F G hF) n).comp
      (MappingTorusHomology.intersectionHomologyEquiv f n).symm.toLinearMap)

@[simp] theorem reflectionIntersectionComparison_apply (n : ℕ)
    (a : SingularHomology X n × SingularHomology X n) :
    reflectionIntersectionComparison f g F G hF n a =
      MappingTorusHomology.intersectionHomologyEquiv g n
        (singularHomologyMap (reflectionIntersectionMap f g F G hF) n
          ((MappingTorusHomology.intersectionHomologyEquiv f n).symm a)) := rfl

/-- The first actual source column becomes the second target column. -/
theorem reflectionIntersectionComparison_lower (n : ℕ) (a : SingularHomology X n) :
    reflectionIntersectionComparison f g F G hF n (a, 0) =
      (0, singularHomologyMap ((g.symm : C(Y, Y)).comp (G (1 / 4))) n a) := by
  rw [reflectionIntersectionComparison_apply, intersectionHomologyEquiv_symm_lower,
    ← LinearMap.comp_apply, ← singularHomologyMap_comp, reflectionIntersectionMap_lower,
    singularHomologyMap_comp, LinearMap.comp_apply, upperComponentFibre_homology]

/-- The second actual source column becomes the first target column. -/
theorem reflectionIntersectionComparison_upper (n : ℕ) (a : SingularHomology X n) :
    reflectionIntersectionComparison f g F G hF n (0, a) =
      (singularHomologyMap ((g.symm : C(Y, Y)).comp (G (3 / 4))) n a, 0) := by
  rw [reflectionIntersectionComparison_apply, intersectionHomologyEquiv_symm_upper,
    ← LinearMap.comp_apply, ← singularHomologyMap_comp, reflectionIntersectionMap_upper,
    singularHomologyMap_comp, LinearMap.comp_apply, lowerComponentFibre_homology]

/-- The complete two-component map follows from the actual two geometric columns. -/
theorem reflectionIntersectionComparison_pair (n : ℕ) (a b : SingularHomology X n) :
    reflectionIntersectionComparison f g F G hF n (a, b) =
      (singularHomologyMap ((g.symm : C(Y, Y)).comp (G (3 / 4))) n b,
        singularHomologyMap ((g.symm : C(Y, Y)).comp (G (1 / 4))) n a) := by
  have hab : (a, b) = (a, (0 : SingularHomology X n)) + (0, b) := by ext <;> simp
  rw [hab, map_add, reflectionIntersectionComparison_lower, reflectionIntersectionComparison_upper]
  simp

/-- Genuine connecting-map naturality for the actual reflected map and covers. -/
theorem reflection_boundaryCoordinates_naturality (n : ℕ)
    (a : SingularHomology (Torus f) (n + 1)) :
    MappingTorusHomology.boundaryCoordinates g n (singularHomologyMap F (n + 1) a) =
      MappingTorusHomology.intersectionHomologyEquiv g n
        (singularHomologyMap (reflectionIntersectionMap f g F G hF) n
          (MappingTorusHomology.mayerVietorisConnecting f n a)) := by
  have h := connectingHomomorphism_naturality_apply F (U f) (V f) (U g) (V g)
    (reflection_mapsTo_U f g F G hF) (reflection_mapsTo_V f g F G hF)
    (U_open f) (V_open f) (cover f) (U_open g) (V_open g) (cover g) n a
  exact (congrArg (MappingTorusHomology.intersectionHomologyEquiv g n) h).symm

/-- Apply the actual reflected intersection map to the source Wang antidiagonal. -/
theorem reflection_boundaryCoordinates_comparison (n : ℕ)
    (a : SingularHomology (Torus f) (n + 1)) :
    MappingTorusHomology.boundaryCoordinates g n (singularHomologyMap F (n + 1) a) =
      reflectionIntersectionComparison f g F G hF n
        (-MappingTorusHomology.wangBoundary f n a, MappingTorusHomology.wangBoundary f n a) := by
  rw [reflection_boundaryCoordinates_naturality f g F G hF,
    mappingTorusConnecting_eq_marked_boundary f n a]
  rfl

/-- The two actual connecting coordinates, including their signs and both
literal quarter-time fibre maps. -/
theorem reflection_boundaryCoordinates_quarters (n : ℕ)
    (a : SingularHomology (Torus f) (n + 1)) :
    MappingTorusHomology.boundaryCoordinates g n (singularHomologyMap F (n + 1) a) =
      (singularHomologyMap ((g.symm : C(Y, Y)).comp (G (3 / 4))) n
          (MappingTorusHomology.wangBoundary f n a),
        -singularHomologyMap ((g.symm : C(Y, Y)).comp (G (1 / 4))) n
          (MappingTorusHomology.wangBoundary f n a)) := by
  rw [reflection_boundaryCoordinates_comparison f g F G hF,
    reflectionIntersectionComparison_pair, map_neg]

/-- Time reflection reverses the actual Wang sign. The remaining fibre map
is the genuine upper-quarter map in its actual target chart. -/
theorem wangBoundary_timeReflection (n : ℕ)
    (a : SingularHomology (Torus f) (n + 1)) :
    MappingTorusHomology.wangBoundary g n (singularHomologyMap F (n + 1) a) =
      -singularHomologyMap ((g.symm : C(Y, Y)).comp (G (3 / 4))) n
        (MappingTorusHomology.wangBoundary f n a) := by
  change -(MappingTorusHomology.boundaryCoordinates g n
    (singularHomologyMap F (n + 1) a)).1 = _
  rw [reflection_boundaryCoordinates_quarters f g F G hF]

/-- A checked fibre comparison on the actual Wang class specializes the
literal time-reflection formula to the desired fibre map. -/
theorem wangBoundary_timeReflection_of_quarter (h : C(X, Y)) (n : ℕ)
    (a : SingularHomology (Torus f) (n + 1))
    (hquarter : singularHomologyMap ((g.symm : C(Y, Y)).comp (G (3 / 4))) n
        (MappingTorusHomology.wangBoundary f n a) =
      singularHomologyMap h n (MappingTorusHomology.wangBoundary f n a)) :
    MappingTorusHomology.wangBoundary g n (singularHomologyMap F (n + 1) a) =
      -singularHomologyMap h n (MappingTorusHomology.wangBoundary f n a) := by
  rw [wangBoundary_timeReflection f g F G hF, hquarter]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct
