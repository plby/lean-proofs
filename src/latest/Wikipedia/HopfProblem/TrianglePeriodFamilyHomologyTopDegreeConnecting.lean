import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleProductNaturality
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleIntersectionCycles

/-!
# The actual circle connecting map for circle-coordinate-preserving maps

A continuous map that preserves the first circle coordinate carries the
actual two-arc cover into itself. The quarter and three-quarter sections
give the two summands of actual intersection homology. Naturality of the
actual Mayer--Vietoris sequence then identifies the signed connecting
coordinate with the induced map on the quarter-point fibre.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusHigherHomology.CircleTopology PeriodTorusHigherHomology.CirclePaths

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual second-coordinate map on a fixed circle fibre. -/
def headMapFibre (F : C(Circle × X, Circle × Y)) (z : Circle) : C(X, Y) :=
  (productProjection Y).comp
    (F.comp ((ContinuousMap.const X z).prodMk (ContinuousMap.id X)))

@[simp] theorem headMapFibre_apply (F : C(Circle × X, Circle × Y))
    (z : Circle) (x : X) : headMapFibre F z x = (F (z, x)).2 := rfl

theorem headMap_mapsToU (F : C(Circle × X, Circle × Y))
    (hF : ∀ z, (F z).1 = z.1) : Set.MapsTo F (productU X) (productU Y) := by
  intro z hz
  change (F z).1 ∈ arcU
  rw [hF]
  exact hz

theorem headMap_mapsToV (F : C(Circle × X, Circle × Y))
    (hF : ∀ z, (F z).1 = z.1) : Set.MapsTo F (productV X) (productV Y) := by
  intro z hz
  change (F z).1 ∈ arcV
  rw [hF]
  exact hz

/-- The actual restriction to the two-component arc intersection. -/
def headIntersectionMap (F : C(Circle × X, Circle × Y))
    (hF : ∀ z, (F z).1 = z.1) :
    C(↥(productU X ∩ productV X), ↥(productU Y ∩ productV Y)) :=
  intersectionRestriction F (productU X) (productV X) (productU Y) (productV Y)
    (headMap_mapsToU F hF) (headMap_mapsToV F hF)

/-- On the first explicit intersection section the restricted map is the actual fibre map. -/
theorem headIntersectionMap_quarter (F : C(Circle × X, Circle × Y))
    (hF : ∀ z, (F z).1 = z.1) :
    (headIntersectionMap F hF).comp (quarterIntersectionSection X) =
      (quarterIntersectionSection Y).comp (headMapFibre F quarterPoint) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact hF (quarterPoint, x)
  · rfl

/-- The corresponding literal formula on the second intersection section. -/
theorem headIntersectionMap_threeQuarter (F : C(Circle × X, Circle × Y))
    (hF : ∀ z, (F z).1 = z.1) :
    (headIntersectionMap F hF).comp (threeQuarterIntersectionSection X) =
      (threeQuarterIntersectionSection Y).comp (headMapFibre F threeQuarterPoint) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact hF (threeQuarterPoint, x)
  · rfl

/-- Both actual section images generate all actual intersection homology. -/
theorem intersectionHomology_sections (n : ℕ)
    (a : SingularHomology (productU X ∩ productV X : Set (Circle × X)) n) :
    a = singularHomologyMap (quarterIntersectionSection X) n
          (productIntersectionHomologyEquiv X n a).1 +
        singularHomologyMap (threeQuarterIntersectionSection X) n
          (productIntersectionHomologyEquiv X n a).2 := by
  apply (productIntersectionHomologyEquiv X n).injective
  rw [map_add, quarterIntersectionHomology_coordinates,
    threeQuarterIntersectionHomology_coordinates]
  simp only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta]

/-- The first actual homology summand is carried by the quarter fibre map. -/
theorem headIntersectionHomology_quarter (F : C(Circle × X, Circle × Y))
    (hF : ∀ z, (F z).1 = z.1) (n : ℕ) (a : SingularHomology X n) :
    productIntersectionHomologyEquiv Y n
        (singularHomologyMap (headIntersectionMap F hF) n
          (singularHomologyMap (quarterIntersectionSection X) n a)) =
      (singularHomologyMap (headMapFibre F quarterPoint) n a, 0) := by
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, headIntersectionMap_quarter,
    singularHomologyMap_comp, LinearMap.comp_apply, quarterIntersectionHomology_coordinates]

/-- The second actual homology summand is carried by the three-quarter fibre map. -/
theorem headIntersectionHomology_threeQuarter (F : C(Circle × X, Circle × Y))
    (hF : ∀ z, (F z).1 = z.1) (n : ℕ) (a : SingularHomology X n) :
    productIntersectionHomologyEquiv Y n
        (singularHomologyMap (headIntersectionMap F hF) n
          (singularHomologyMap (threeQuarterIntersectionSection X) n a)) =
      (0, singularHomologyMap (headMapFibre F threeQuarterPoint) n a) := by
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, headIntersectionMap_threeQuarter,
    singularHomologyMap_comp, LinearMap.comp_apply, threeQuarterIntersectionHomology_coordinates]

/-- The two-component formula follows from the actual section generators. -/
theorem headIntersectionHomology_coordinates (F : C(Circle × X, Circle × Y))
    (hF : ∀ z, (F z).1 = z.1) (n : ℕ)
    (a : SingularHomology (productU X ∩ productV X : Set (Circle × X)) n) :
    productIntersectionHomologyEquiv Y n
        (singularHomologyMap (headIntersectionMap F hF) n a) =
      (singularHomologyMap (headMapFibre F quarterPoint) n
          (productIntersectionHomologyEquiv X n a).1,
        singularHomologyMap (headMapFibre F threeQuarterPoint) n
          (productIntersectionHomologyEquiv X n a).2) := by
  conv_lhs => rw [intersectionHomology_sections n a]
  rw [map_add, map_add, headIntersectionHomology_quarter,
    headIntersectionHomology_threeQuarter]
  simp only [Prod.mk_add_mk, add_zero, zero_add]

/-- Naturality of the actual raw Mayer--Vietoris connecting map for a head-preserving map. -/
theorem circleConnecting_headMap (F : C(Circle × X, Circle × Y))
    (hF : ∀ z, (F z).1 = z.1) (n : ℕ)
    (a : SingularHomology (Circle × X) (n + 1)) :
    singularHomologyMap (headIntersectionMap F hF) n (circleMayerVietorisConnecting X n a) =
      circleMayerVietorisConnecting Y n (singularHomologyMap F (n + 1) a) :=
  connectingHomomorphism_naturality_apply F
    (productU X) (productV X) (productU Y) (productV Y)
    (headMap_mapsToU F hF) (headMap_mapsToV F hF)
    (productU_open X) (productV_open X) (product_cover X)
    (productU_open Y) (productV_open Y) (product_cover Y) n a

/-- The signed circle coordinate transforms by the actual quarter-fibre homology map. -/
theorem circleBoundary_headMap (F : C(Circle × X, Circle × Y))
    (hF : ∀ z, (F z).1 = z.1) (n : ℕ)
    (a : SingularHomology (Circle × X) (n + 1)) :
    circleBoundary Y n (singularHomologyMap F (n + 1) a) =
      singularHomologyMap (headMapFibre F quarterPoint) n (circleBoundary X n a) := by
  change -(productIntersectionHomologyEquiv Y n
    (circleMayerVietorisConnecting Y n (singularHomologyMap F (n + 1) a))).1 =
      singularHomologyMap (headMapFibre F quarterPoint) n
        (-(productIntersectionHomologyEquiv X n (circleMayerVietorisConnecting X n a)).1)
  rw [← circleConnecting_headMap F hF, headIntersectionHomology_coordinates, map_neg]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
