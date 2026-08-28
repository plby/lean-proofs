import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleDisjoint
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleTopologyProductCover
import Wikipedia.HopfProblem.SingularMayerVietoris

/-!
# The actual maps in the circle-product Mayer–Vietoris sequence

The two open members retract to the unchanged factor. Their intersection
retracts to two copies of that factor. In the resulting actual homology
coordinates the intersection map is `(a,b) ↦ (a+b,-(a+b))`, and the map
to the ambient product is the zero-section map applied to `a+b`.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris CircleTopology

variable (X : Type) [TopologicalSpace X]

/-- Actual homology coordinates on the pair of open members. -/
def productArcHomologyEquiv (n : ℕ) :
    (SingularHomology (productU X) n × SingularHomology (productV X) n) ≃ₗ[ℤ]
      (SingularHomology X n × SingularHomology X n) :=
  ((homotopyEquivHomologyEquiv (productUHomotopyEquiv X) n).toAddEquiv.prodCongr
    (homotopyEquivHomologyEquiv (productVHomotopyEquiv X) n).toAddEquiv).toIntLinearEquiv

@[simp] theorem productArcHomologyEquiv_apply (n : ℕ)
    (a : SingularHomology (productU X) n × SingularHomology (productV X) n) :
    productArcHomologyEquiv X n a =
      (homotopyEquivHomologyEquiv (productUHomotopyEquiv X) n a.1,
        homotopyEquivHomologyEquiv (productVHomotopyEquiv X) n a.2) := rfl

/-- Actual intersection homology, with the lower interval component first. -/
def productIntersectionHomologyEquiv (n : ℕ) :
    SingularHomology (productU X ∩ productV X : Set (Circle × X)) n ≃ₗ[ℤ]
      (SingularHomology X n × SingularHomology X n) :=
  (homotopyEquivHomologyEquiv (productIntersectionHomotopyEquiv X) n).trans
    (sumHomologyEquiv X X n)

@[simp] theorem productIntersectionHomologyEquiv_apply (n : ℕ)
    (a : SingularHomology (productU X ∩ productV X : Set (Circle × X)) n) :
    productIntersectionHomologyEquiv X n a =
      sumHomologyEquiv X X n
        (singularHomologyMap (productIntersectionHomotopyEquiv X).toFun n a) := rfl

/-- The actual map induced by the fixed circle-coordinate section. -/
abbrev circleSectionHomology (n : ℕ) :
    SingularHomology X n →ₗ[ℤ] SingularHomology (Circle × X) n :=
  singularHomologyMap (productSection X) n

/-- The actual map induced by projection to the unchanged factor. -/
abbrev circleProjectionHomology (n : ℕ) :
    SingularHomology (Circle × X) n →ₗ[ℤ] SingularHomology X n :=
  singularHomologyMap (productProjection X) n

@[simp] theorem circleProjection_section (n : ℕ) :
    (circleProjectionHomology X n).comp (circleSectionHomology X n) = LinearMap.id := by
  rw [← singularHomologyMap_comp, productProjection_comp_productSection,
    singularHomologyMap_id]

theorem circleSectionHomology_injective (n : ℕ) :
    Function.Injective (circleSectionHomology X n) :=
  (show Function.LeftInverse (circleProjectionHomology X n) (circleSectionHomology X n)
    from fun a => LinearMap.congr_fun (circleProjection_section X n) a).injective

/-- The first actual cover inclusion is homotopic to the fixed section after projection. -/
theorem productUInclusion_homology (n : ℕ) :
    singularHomologyMap (productUInclusion X) n =
      (circleSectionHomology X n).comp
        (homotopyEquivHomologyEquiv (productUHomotopyEquiv X) n).toLinearMap := by
  rw [homotopy_homologyMap (productUInclusionHomotopy X) n, singularHomologyMap_comp]
  rfl

/-- The second actual cover inclusion gives the same fixed section after projection. -/
theorem productVInclusion_homology (n : ℕ) :
    singularHomologyMap (productVInclusion X) n =
      (circleSectionHomology X n).comp
        (homotopyEquivHomologyEquiv (productVHomotopyEquiv X) n).toLinearMap := by
  rw [homotopy_homologyMap (productVInclusionHomotopy X) n, singularHomologyMap_comp]
  rfl

/-- The actual topological fold map adds the two disjoint-union homology coordinates. -/
theorem productFold_homology (n : ℕ) (a : SingularHomology (X ⊕ X) n) :
    singularHomologyMap (foldMap X) n a =
      (sumHomologyEquiv X X n a).1 + (sumHomologyEquiv X X n a).2 :=
  sumHomologyEquiv_fold n a

/-- The first intersection inclusion becomes the fold under the actual homotopy equivalences. -/
theorem productIntersectionToU_homology (n : ℕ)
    (a : SingularHomology (productU X ∩ productV X : Set (Circle × X)) n) :
    homotopyEquivHomologyEquiv (productUHomotopyEquiv X) n
        (singularHomologyMap (productIntersectionToU X) n a) =
      (productIntersectionHomologyEquiv X n a).1 +
        (productIntersectionHomologyEquiv X n a).2 := by
  change singularHomologyMap (productUHomotopyEquiv X).toFun n
    (singularHomologyMap (productIntersectionToU X) n a) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    productIntersectionToU_fold, singularHomologyMap_comp]
  exact productFold_homology X n _

/-- The second intersection inclusion becomes the same fold. -/
theorem productIntersectionToV_homology (n : ℕ)
    (a : SingularHomology (productU X ∩ productV X : Set (Circle × X)) n) :
    homotopyEquivHomologyEquiv (productVHomotopyEquiv X) n
        (singularHomologyMap (productIntersectionToV X) n a) =
      (productIntersectionHomologyEquiv X n a).1 +
        (productIntersectionHomologyEquiv X n a).2 := by
  change singularHomologyMap (productVHomotopyEquiv X).toFun n
    (singularHomologyMap (productIntersectionToV X) n a) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    productIntersectionToV_fold, singularHomologyMap_comp]
  exact productFold_homology X n _

/-- The actual first Mayer–Vietoris map is the signed fold in these coordinates. -/
theorem circleProductLeftHomologyMap_apply (n : ℕ)
    (a : SingularHomology (productU X ∩ productV X : Set (Circle × X)) n) :
    productArcHomologyEquiv X n (leftHomologyMap (productU X) (productV X) n a) =
      ((productIntersectionHomologyEquiv X n a).1 +
        (productIntersectionHomologyEquiv X n a).2,
        -((productIntersectionHomologyEquiv X n a).1 +
          (productIntersectionHomologyEquiv X n a).2)) := by
  rw [leftHomologyMap_apply]
  change
    (homotopyEquivHomologyEquiv (productUHomotopyEquiv X) n
      (singularHomologyMap (productIntersectionToU X) n a),
      homotopyEquivHomologyEquiv (productVHomotopyEquiv X) n
        (-singularHomologyMap (productIntersectionToV X) n a)) = _
  rw [map_neg, productIntersectionToU_homology, productIntersectionToV_homology]

/-- The actual second Mayer–Vietoris map is the section applied to the sum of coordinates. -/
theorem circleProductRightHomologyMap_apply (n : ℕ)
    (a : SingularHomology (productU X) n × SingularHomology (productV X) n) :
    rightHomologyMap (productU X) (productV X) n a =
      circleSectionHomology X n
        ((productArcHomologyEquiv X n a).1 + (productArcHomologyEquiv X n a).2) := by
  rw [rightHomologyMap_apply]
  change singularHomologyMap (productUInclusion X) n a.1 +
    singularHomologyMap (productVInclusion X) n a.2 = _
  rw [productUInclusion_homology, productVInclusion_homology]
  exact (map_add (circleSectionHomology X n) _ _).symm

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
