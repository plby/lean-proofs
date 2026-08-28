import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleProduct
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleProductNaturalityCoordinates
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleMayerVietorisNaturality

/-!
# Naturality of the actual circle-product homology splitting

The map `id × f` preserves the explicit two-arc cover. The actual
Mayer–Vietoris connecting square and the actual intersection-coordinate
square therefore prove naturality of the signed circle coordinate.
Projection gives naturality of the other coordinate.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris CircleTopology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem circleProductMap_mapsToU (f : C(X, Y)) :
    Set.MapsTo (circleProductMap f) (productU X) (productU Y) := fun _ h => h

theorem circleProductMap_mapsToV (f : C(X, Y)) :
    Set.MapsTo (circleProductMap f) (productV X) (productV Y) := fun _ h => h

/-- The generic cover restriction is the literal product-intersection map. -/
theorem circleProductIntersectionRestriction_eq (f : C(X, Y)) :
    intersectionRestriction (circleProductMap f) (productU X) (productV X)
        (productU Y) (productV Y) (circleProductMap_mapsToU f) (circleProductMap_mapsToV f) =
      intersectionProductMap f := rfl

/-- The actual circle-product Mayer–Vietoris connecting square. -/
theorem circleMayerVietorisConnecting_naturality (f : C(X, Y)) (n : ℕ) :
    (singularHomologyMap (intersectionProductMap f) n).comp
        (circleMayerVietorisConnecting X n) =
      (circleMayerVietorisConnecting Y n).comp
        (singularHomologyMap (circleProductMap f) (n + 1)) := by
  have h := connectingHomomorphism_naturality (circleProductMap f)
    (productU X) (productV X) (productU Y) (productV Y)
    (circleProductMap_mapsToU f) (circleProductMap_mapsToV f)
    (productU_open X) (productV_open X) (product_cover X)
    (productU_open Y) (productV_open Y) (product_cover Y) n
  rw [circleProductIntersectionRestriction_eq] at h
  exact h

/-- Both raw intersection components of the actual connecting map are natural. -/
theorem circleBoundaryCoordinates_naturality (f : C(X, Y)) (n : ℕ)
    (a : SingularHomology (Circle × X) (n + 1)) :
    circleBoundaryCoordinates Y n
        (singularHomologyMap (circleProductMap f) (n + 1) a) =
      (singularHomologyMap f n (circleBoundaryCoordinates X n a).1,
        singularHomologyMap f n (circleBoundaryCoordinates X n a).2) := by
  have h := LinearMap.congr_fun (circleMayerVietorisConnecting_naturality f n) a
  change singularHomologyMap (intersectionProductMap f) n
    (circleMayerVietorisConnecting X n a) =
      circleMayerVietorisConnecting Y n
        (singularHomologyMap (circleProductMap f) (n + 1) a) at h
  change productIntersectionHomologyEquiv Y n
    (circleMayerVietorisConnecting Y n
      (singularHomologyMap (circleProductMap f) (n + 1) a)) = _
  rw [← h]
  exact productIntersectionHomologyEquiv_naturality f n (circleMayerVietorisConnecting X n a)

/-- The signed circle coordinate is natural under arbitrary continuous maps. -/
theorem circleBoundary_naturality (f : C(X, Y)) (n : ℕ)
    (a : SingularHomology (Circle × X) (n + 1)) :
    circleBoundary Y n (singularHomologyMap (circleProductMap f) (n + 1) a) =
      singularHomologyMap f n (circleBoundary X n a) := by
  change -(circleBoundaryCoordinates Y n
    (singularHomologyMap (circleProductMap f) (n + 1) a)).1 =
      singularHomologyMap f n (-(circleBoundaryCoordinates X n a).1)
  rw [circleBoundaryCoordinates_naturality, map_neg]

/-- Naturality of the actual integral circle-product splitting in every positive degree. -/
theorem circleProductHomologyEquiv_naturality (f : C(X, Y)) (n : ℕ)
    (a : SingularHomology (Circle × X) (n + 1)) :
    circleProductHomologyEquiv Y n
        (singularHomologyMap (circleProductMap f) (n + 1) a) =
      (singularHomologyMap f (n + 1) (circleProductHomologyEquiv X n a).1,
        singularHomologyMap f n (circleProductHomologyEquiv X n a).2) := by
  apply Prod.ext
  · exact LinearMap.congr_fun (circleProjectionHomology_naturality f (n + 1)) a
  · exact circleBoundary_naturality f n a

/-- The canonical inverse-coordinate classes are natural as actual homology classes. -/
theorem circleProductHomologyEquiv_symm_naturality (f : C(X, Y)) (n : ℕ)
    (a : SingularHomology X (n + 1) × SingularHomology X n) :
    singularHomologyMap (circleProductMap f) (n + 1)
        ((circleProductHomologyEquiv X n).symm a) =
      (circleProductHomologyEquiv Y n).symm
        (singularHomologyMap f (n + 1) a.1, singularHomologyMap f n a.2) := by
  apply (circleProductHomologyEquiv Y n).injective
  rw [circleProductHomologyEquiv_naturality, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/-- The degree-zero actual projection equivalence is natural as well. -/
theorem circleProductHomologyZeroEquiv_naturality (f : C(X, Y))
    (a : SingularHomology (Circle × X) 0) :
    circleProductHomologyZeroEquiv Y (singularHomologyMap (circleProductMap f) 0 a) =
      singularHomologyMap f 0 (circleProductHomologyZeroEquiv X a) :=
  LinearMap.congr_fun (circleProjectionHomology_naturality f 0) a

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
