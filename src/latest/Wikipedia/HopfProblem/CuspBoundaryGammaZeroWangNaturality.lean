import Wikipedia.HopfProblem.CuspBoundaryGammaZeroMappingTorus
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryWangComponents

/-!
# Naturality of the actual Wang boundary under a fibre map

An equivariant continuous fibre map induces a genuine time-preserving map
of the two mapping-torus quotients. It preserves both open arcs and both
overlap components. Naturality of the actual singular Mayer--Vietoris
connecting map therefore gives Wang naturality without a sign change.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspBoundaryGammaZero

open SingularMayerVietoris PeriodTorusHigherHomology MappingTorus MappingTorus.HomologyCover
open TrianglePeriodFamily.Boundary

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : C(X, Y))
  (he : ∀ x, e (f x) = g (e x))

/-- The actual quotient map preserves the first open arc. -/
theorem mappingTorusMap_mapsTo_U : Set.MapsTo (mappingTorusMap f g e he) (U f) (U g) := by
  intro q hq
  change base g (mappingTorusMap f g e he q) ≠ ((0 : ℝ) : MappingTorus.Circle)
  rw [mappingTorusMap_base]
  exact hq

/-- The actual quotient map also preserves the second open arc. -/
theorem mappingTorusMap_mapsTo_V : Set.MapsTo (mappingTorusMap f g e he) (V f) (V g) := by
  intro q hq
  change base g (mappingTorusMap f g e he q) ≠ ((-(1 / 2 : ℝ)) : MappingTorus.Circle)
  rw [mappingTorusMap_base]
  exact hq

/-- The literal restriction to the intersections of the genuine two-arc covers. -/
def mappingTorusIntersectionMap :
    C((U f ∩ V f : Set (Torus f)), (U g ∩ V g : Set (Torus g))) :=
  intersectionRestriction (mappingTorusMap f g e he) (U f) (V f) (U g) (V g)
    (mappingTorusMap_mapsTo_U f g e he) (mappingTorusMap_mapsTo_V f g e he)

@[simp] theorem mappingTorusIntersectionMap_coe (q : (U f ∩ V f : Set (Torus f))) :
    (mappingTorusIntersectionMap f g e he q).val = mappingTorusMap f g e he q.val := rfl

/-- The lower geometric component retains its position and has fibre map `e`. -/
theorem mappingTorusIntersectionMap_lower :
    (mappingTorusIntersectionMap f g e he).comp (lowerComponentFibre f) =
      (lowerComponentFibre g).comp e := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change mappingTorusMap f g e he (lowerComponentFibre f x).val =
    (lowerComponentFibre g (e x)).val
  simp only [lowerComponentFibre_coe, mappingTorusMap_mk]

/-- The upper geometric component likewise retains its position. -/
theorem mappingTorusIntersectionMap_upper :
    (mappingTorusIntersectionMap f g e he).comp (upperComponentFibre f) =
      (upperComponentFibre g).comp e := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change mappingTorusMap f g e he (upperComponentFibre f x).val =
    (upperComponentFibre g (e x)).val
  simp only [upperComponentFibre_coe, mappingTorusMap_mk]

/-- The induced intersection map in the actual two-component homology markings. -/
def mappingTorusIntersectionComparison (n : ℕ) :
    (SingularHomology X n × SingularHomology X n) →ₗ[ℤ]
      (SingularHomology Y n × SingularHomology Y n) :=
  (MappingTorusHomology.intersectionHomologyEquiv g n).toLinearMap.comp
    ((singularHomologyMap (mappingTorusIntersectionMap f g e he) n).comp
      (MappingTorusHomology.intersectionHomologyEquiv f n).symm.toLinearMap)

@[simp] theorem mappingTorusIntersectionComparison_apply (n : ℕ)
    (a : SingularHomology X n × SingularHomology X n) :
    mappingTorusIntersectionComparison f g e he n a =
      MappingTorusHomology.intersectionHomologyEquiv g n
        (singularHomologyMap (mappingTorusIntersectionMap f g e he) n
          ((MappingTorusHomology.intersectionHomologyEquiv f n).symm a)) := rfl

/-- The first actual homology column is the fibre map in the first target component. -/
theorem mappingTorusIntersectionComparison_lower (n : ℕ) (a : SingularHomology X n) :
    mappingTorusIntersectionComparison f g e he n (a, 0) =
      (singularHomologyMap e n a, 0) := by
  rw [mappingTorusIntersectionComparison_apply, intersectionHomologyEquiv_symm_lower,
    ← LinearMap.comp_apply, ← singularHomologyMap_comp, mappingTorusIntersectionMap_lower,
    singularHomologyMap_comp, LinearMap.comp_apply, lowerComponentFibre_homology]

/-- The second actual homology column is the same fibre map in the second component. -/
theorem mappingTorusIntersectionComparison_upper (n : ℕ) (a : SingularHomology X n) :
    mappingTorusIntersectionComparison f g e he n (0, a) =
      (0, singularHomologyMap e n a) := by
  rw [mappingTorusIntersectionComparison_apply, intersectionHomologyEquiv_symm_upper,
    ← LinearMap.comp_apply, ← singularHomologyMap_comp, mappingTorusIntersectionMap_upper,
    singularHomologyMap_comp, LinearMap.comp_apply, upperComponentFibre_homology]

/-- The complete intersection map acts by the actual fibre homology map in both coordinates. -/
theorem mappingTorusIntersectionComparison_pair (n : ℕ) (a b : SingularHomology X n) :
    mappingTorusIntersectionComparison f g e he n (a, b) =
      (singularHomologyMap e n a, singularHomologyMap e n b) := by
  have hab : (a, b) = (a, (0 : SingularHomology X n)) + (0, b) := by ext <;> simp
  rw [hab, map_add, mappingTorusIntersectionComparison_lower,
    mappingTorusIntersectionComparison_upper]
  simp

/-- Naturality of the genuine Mayer--Vietoris connecting map for these actual covers. -/
theorem mappingTorus_boundaryCoordinates_naturality (n : ℕ)
    (a : SingularHomology (Torus f) (n + 1)) :
    MappingTorusHomology.boundaryCoordinates g n
        (singularHomologyMap (mappingTorusMap f g e he) (n + 1) a) =
      MappingTorusHomology.intersectionHomologyEquiv g n
        (singularHomologyMap (mappingTorusIntersectionMap f g e he) n
          (MappingTorusHomology.mayerVietorisConnecting f n a)) := by
  have h := connectingHomomorphism_naturality_apply
    (mappingTorusMap f g e he) (U f) (V f) (U g) (V g)
    (mappingTorusMap_mapsTo_U f g e he) (mappingTorusMap_mapsTo_V f g e he)
    (U_open f) (V_open f) (cover f) (U_open g) (V_open g) (cover g) n a
  exact (congrArg (MappingTorusHomology.intersectionHomologyEquiv g n) h).symm

/-- Apply the actual intersection map to the source Wang antidiagonal. -/
theorem mappingTorus_boundaryCoordinates_comparison (n : ℕ)
    (a : SingularHomology (Torus f) (n + 1)) :
    MappingTorusHomology.boundaryCoordinates g n
        (singularHomologyMap (mappingTorusMap f g e he) (n + 1) a) =
      mappingTorusIntersectionComparison f g e he n
        (-MappingTorusHomology.wangBoundary f n a, MappingTorusHomology.wangBoundary f n a) := by
  rw [mappingTorus_boundaryCoordinates_naturality f g e he,
    mappingTorusConnecting_eq_marked_boundary f n a]
  rfl

/-- The two target boundary coordinates, with the unchanged Wang sign convention. -/
theorem mappingTorus_boundaryCoordinates_pair (n : ℕ)
    (a : SingularHomology (Torus f) (n + 1)) :
    MappingTorusHomology.boundaryCoordinates g n
        (singularHomologyMap (mappingTorusMap f g e he) (n + 1) a) =
      (-singularHomologyMap e n (MappingTorusHomology.wangBoundary f n a),
        singularHomologyMap e n (MappingTorusHomology.wangBoundary f n a)) := by
  rw [mappingTorus_boundaryCoordinates_comparison f g e he,
    mappingTorusIntersectionComparison_pair, map_neg]

/-- The actual Wang boundary is natural for an equivariant continuous fibre map in every degree. -/
theorem wangBoundary_mappingTorusMap (n : ℕ)
    (a : SingularHomology (Torus f) (n + 1)) :
    MappingTorusHomology.wangBoundary g n
        (singularHomologyMap (mappingTorusMap f g e he) (n + 1) a) =
      singularHomologyMap e n (MappingTorusHomology.wangBoundary f n a) := by
  change -(MappingTorusHomology.boundaryCoordinates g n
    (singularHomologyMap (mappingTorusMap f g e he) (n + 1) a)).1 = _
  rw [mappingTorus_boundaryCoordinates_pair f g e he, neg_neg]

/-- The same naturality statement as an equality of actual homology linear maps. -/
theorem wangBoundary_mappingTorusMap_linear (n : ℕ) :
    (MappingTorusHomology.wangBoundary g n).comp
        (singularHomologyMap (mappingTorusMap f g e he) (n + 1)) =
      (singularHomologyMap e n).comp (MappingTorusHomology.wangBoundary f n) := by
  apply LinearMap.ext
  intro a
  exact wangBoundary_mappingTorusMap f g e he n a

end Wikipedia.HopfProblem.CuspBoundaryGammaZero
