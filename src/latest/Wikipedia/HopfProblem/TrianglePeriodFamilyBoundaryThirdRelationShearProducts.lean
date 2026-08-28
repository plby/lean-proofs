import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryThirdRelationShearBasic

/-!
# The actual cross-product correction of a vertical circle shear

The original positive-circle cross class is the Pontryagin product of
the circle and group insertions. A vertical shear changes only the
first insertion, by adding the given genuine circle map. Naturality and
bilinearity therefore give its full correction in every degree.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology CircleTopology
open PeriodTorusHigherHomologyPontryagin

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
  PeriodTorusHigherHomology.integerTensorModule

variable (G : Type) [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]

/-- The literal positive-circle cross product is the actual product of the two insertions. -/
theorem circleCross_eq_product (n : ℕ) (b : SingularHomology G n) :
    positiveCircleCross G n b =
      product (Circle × G) n
        (singularHomologyMap (circleHeadMap G) 1
          (loopHomologyClass CirclePaths.positiveLoop))
        (circleSectionHomology G n b) := by
  rw [product_apply]
  rw [← crossProductHomology_natural (circleHeadMap G) (productSection G) n
    (loopHomologyClass CirclePaths.positiveLoop) b]
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    ← circleProduct_identity_eq_add, singularHomologyMap_id]
  rfl

/-- The full first-homology change of the circle insertion is the original circle-map class. -/
theorem verticalProductShear_headHomology (v : C(Circle, G))
    (hv : ∀ x y, v (x + y) = v x + v y) (a : SingularHomology Circle 1) :
    singularHomologyMap (verticalProductShear G v) 1
        (singularHomologyMap (circleHeadMap G) 1 a) =
      singularHomologyMap (circleHeadMap G) 1 a +
        circleSectionHomology G 1 (singularHomologyMap v 1 a) := by
  have hzero : ((productSection G).comp v) (0 : Circle) = 0 := by
    change (0, v 0) = (0, 0)
    rw [circleMorphism_zero G v hv]
  have hsum : singularHomologyMap (circleHeadMap G + (productSection G).comp v) 1 =
      singularHomologyMap (circleHeadMap G) 1 +
        singularHomologyMap ((productSection G).comp v) 1 := by
    simpa only [singularHomologyMap_one] using
      inducedH1_add_of_zero (circleHeadMap G) ((productSection G).comp v)
        (0 : Circle) (circleHeadMap_zero G) hzero
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    verticalProductShear_comp_head, hsum, LinearMap.add_apply,
    singularHomologyMap_comp, LinearMap.comp_apply]

/-- Every actual section homology class is unchanged by the shear. -/
theorem verticalProductShear_sectionHomology (v : C(Circle, G))
    (hv : ∀ x y, v (x + y) = v x + v y) (n : ℕ) (b : SingularHomology G n) :
    singularHomologyMap (verticalProductShear G v) n (circleSectionHomology G n b) =
      circleSectionHomology G n b := by
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    verticalProductShear_comp_section G v hv]

/-- In every degree the exact correction is the original fibre Pontryagin product.
The circle is the first factor, fixing the integral sign. -/
theorem verticalProductShear_positiveCircleCross (v : C(Circle, G))
    (hv : ∀ x y, v (x + y) = v x + v y) (n : ℕ) (b : SingularHomology G n) :
    singularHomologyMap (verticalProductShear G v) (n + 1)
        (positiveCircleCross G n b) =
      positiveCircleCross G n b + circleSectionHomology G (n + 1)
        (product G n (singularHomologyMap v 1
          (loopHomologyClass CirclePaths.positiveLoop)) b) := by
  rw [circleCross_eq_product, product_natural (verticalProductShear G v)
    (verticalProductShear_add G v hv), verticalProductShear_headHomology G v hv,
    verticalProductShear_sectionHomology G v hv,
    (product (Circle × G) n).map_add, LinearMap.add_apply]
  rw [← circleCross_eq_product]
  congr 1
  exact (product_natural (productSection G) (productSection_add G) n
    (singularHomologyMap v 1 (loopHomologyClass CirclePaths.positiveLoop)) b).symm

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation
