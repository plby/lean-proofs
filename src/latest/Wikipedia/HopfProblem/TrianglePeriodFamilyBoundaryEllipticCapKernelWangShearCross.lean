import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangShearH1
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangShearProducts
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeSurjectiveProductTorus

/-!
# Shears preserve the actual positive-circle cross summand in degrees two and three

The coordinate splitting is the actual homeomorphism from five circles to
one circle times four circles. Its cross product is the actual Pontryagin
product with the positive first-coordinate loop. The genuine first-homology
shear formula and repeated-factor cancellation prove invariance. In degree
three, the proved surjectivity of the actual coordinate-loop exterior-square
map extends the product calculation to every singular-homology class.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryEllipticCapKernelWangShear

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
  PeriodTorusHigherHomologyPontryagin PeriodTorusHigherHomology.CircleTopology

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
  PeriodTorusHigherHomology.integerTensorModule

/-- The literal conjugacy of the continuous maps induces the same conjugacy in homology. -/
theorem shear_unsplit_homology (χ : C(ProductTorus 4, Circle)) (n : ℕ)
    (a : SingularHomology (Circle × ProductTorus 4) n) :
    singularHomologyMap ((productTorusSuccHomeomorph 4).symm :
        C(Circle × ProductTorus 4, ProductTorus 5)) n
      (singularHomologyMap (shear χ) n a) =
    singularHomologyMap (torusShear χ) n
      (singularHomologyMap ((productTorusSuccHomeomorph 4).symm :
        C(Circle × ProductTorus 4, ProductTorus 5)) n a) := by
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    ← torusShear_comp_unsplit, singularHomologyMap_comp, LinearMap.comp_apply]

/-- The first-coordinate loop has the orientation fixed by the native circle normalization. -/
theorem unsplit_positiveCircleCross (n : ℕ) (b : SingularHomology (ProductTorus 4) n) :
    singularHomologyMap ((productTorusSuccHomeomorph 4).symm :
        C(Circle × ProductTorus 4, ProductTorus 5)) (n + 1)
      (positiveCircleCross (ProductTorus 4) n b) =
    product (ProductTorus 5) n headClass (singularHomologyMap (torusTailMap 4) n b) := by
  rw [torusSplit_positiveCircleCross, torusHeadCircleMap_positiveHomology]
  rfl

/-- Transfer an actual product calculation through the native coordinate-splitting homeomorphism. -/
theorem shear_positiveCircleCross_of_product (χ : C(ProductTorus 4, Circle)) (n : ℕ)
    (b : SingularHomology (ProductTorus 4) n)
    (h : singularHomologyMap (torusShear χ) (n + 1)
        (product (ProductTorus 5) n headClass (singularHomologyMap (torusTailMap 4) n b)) =
      product (ProductTorus 5) n headClass (singularHomologyMap (torusTailMap 4) n b)) :
    singularHomologyMap (shear χ) (n + 1) (positiveCircleCross (ProductTorus 4) n b) =
      positiveCircleCross (ProductTorus 4) n b := by
  apply (homeomorphHomologyEquiv (productTorusSuccHomeomorph 4).symm (n + 1)).injective
  change singularHomologyMap ((productTorusSuccHomeomorph 4).symm :
      C(Circle × ProductTorus 4, ProductTorus 5)) (n + 1)
    (singularHomologyMap (shear χ) (n + 1) (positiveCircleCross (ProductTorus 4) n b)) =
    singularHomologyMap ((productTorusSuccHomeomorph 4).symm :
      C(Circle × ProductTorus 4, ProductTorus 5)) (n + 1)
    (positiveCircleCross (ProductTorus 4) n b)
  rw [shear_unsplit_homology, unsplit_positiveCircleCross]
  exact h

/-- An additive character shear fixes every actual positive-circle cross class in degree two. -/
theorem shear_positiveCircleCross_one (χ : C(ProductTorus 4, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y)
    (b : SingularHomology (ProductTorus 4) 1) :
    singularHomologyMap (shear χ) 2 (positiveCircleCross (ProductTorus 4) 1 b) =
      positiveCircleCross (ProductTorus 4) 1 b := by
  let := productTorus_homology_torsionFree 5 2
  apply shear_positiveCircleCross_of_product χ 1 b
  exact product11_fixed_of_head (ProductTorus 5) (torusShear χ) (torusShear_add χ hχ)
    headClass (singularHomologyMap (torusTailMap 4) 1 b)
    (circleHomologyOneEquiv (singularHomologyMap χ 1 b))
    (torusShear_headClass χ hχ) (torusShear_tailHomology χ hχ b)

/-- Degree-three invariance on a pair of arbitrary genuine degree-one classes. -/
theorem shear_positiveCircleCross_two_product11 (χ : C(ProductTorus 4, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y)
    (b c : SingularHomology (ProductTorus 4) 1) :
    singularHomologyMap (shear χ) 3
      (positiveCircleCross (ProductTorus 4) 2 (product11 (ProductTorus 4) b c)) =
    positiveCircleCross (ProductTorus 4) 2 (product11 (ProductTorus 4) b c) := by
  let := productTorus_homology_torsionFree 5 2
  apply shear_positiveCircleCross_of_product χ 2 (product11 (ProductTorus 4) b c)
  rw [product_natural (torusTailMap 4) (torusTailMap_add 4) 1]
  exact tripleProduct_fixed_of_head (ProductTorus 5) (torusShear χ) (torusShear_add χ hχ)
    headClass (singularHomologyMap (torusTailMap 4) 1 b)
    (singularHomologyMap (torusTailMap 4) 1 c)
    (circleHomologyOneEquiv (singularHomologyMap χ 1 b))
    (circleHomologyOneEquiv (singularHomologyMap χ 1 c))
    (torusShear_headClass χ hχ) (torusShear_tailHomology χ hχ b)
    (torusShear_tailHomology χ hχ c)

/-- Surjectivity of the actual loop-product map gives degree-three invariance on every class. -/
theorem shear_positiveCircleCross_two (χ : C(ProductTorus 4, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y)
    (b : SingularHomology (ProductTorus 4) 2) :
    singularHomologyMap (shear χ) 3 (positiveCircleCross (ProductTorus 4) 2 b) =
      positiveCircleCross (ProductTorus 4) 2 b := by
  have h : ((singularHomologyMap (shear χ) 3).comp
        (positiveCircleCross (ProductTorus 4) 2)).comp coordinateTorusWedgeTwo =
      (positiveCircleCross (ProductTorus 4) 2).comp coordinateTorusWedgeTwo := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change singularHomologyMap (shear χ) 3
        (positiveCircleCross (ProductTorus 4) 2
          (coordinateTorusWedgeTwo (exteriorPower.ιMulti ℤ 2 v))) =
      positiveCircleCross (ProductTorus 4) 2
        (coordinateTorusWedgeTwo (exteriorPower.ιMulti ℤ 2 v))
    rw [coordinateTorusWedgeTwo_apply_ιMulti]
    exact shear_positiveCircleCross_two_product11 χ hχ _ _
  obtain ⟨v, rfl⟩ := coordinateTorusWedgeTwo_surjective b
  exact LinearMap.congr_fun h v

/-- The two degrees needed by the boundary Wang kernel use the same actual shear map. -/
theorem shear_positiveCircleCross (χ : C(ProductTorus 4, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) (n : ℕ) (hn : n = 1 ∨ n = 2)
    (b : SingularHomology (ProductTorus 4) n) :
    singularHomologyMap (shear χ) (n + 1) (positiveCircleCross (ProductTorus 4) n b) =
      positiveCircleCross (ProductTorus 4) n b := by
  rcases hn with rfl | rfl
  · exact shear_positiveCircleCross_one χ hχ b
  · exact shear_positiveCircleCross_two χ hχ b

end Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryEllipticCapKernelWangShear
