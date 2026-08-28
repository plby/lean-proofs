import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTopShearThreeTorus
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeSurjectiveMaps

/-!
# Degree-three shear invariance from actual coordinate subtori

Every coordinate three-subtorus gives an actual homology class, and these
classes form the proved integral basis of the four-torus's third homology.
The literal product map intertwines its restricted character shear with the
ambient shear. Naturality of the genuine positive-circle cross product
therefore extends the top-degree three-torus calculation to every class.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryEllipticCapKernelWangShear

open SingularMayerVietoris PeriodTorusHigherHomology
  PeriodTorusHigherHomology.CircleTopology

/-- The actual shear square commutes for any continuous three-torus map. -/
theorem shear_comp_threeSubtorus (χ : C(ProductTorus 4, Circle))
    (f : C(ProductTorus 3, ProductTorus 4)) :
    (shear χ).comp (circleProductMap f) =
      (circleProductMap f).comp (shearOn 3 (χ.comp f)) := by
  apply ContinuousMap.ext
  intro x
  rfl

/-- A genuine additive three-torus image supplies fixed positive-circle cross classes. -/
theorem shear_positiveCircleCross_three_map (χ : C(ProductTorus 4, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y)
    (f : C(ProductTorus 3, ProductTorus 4))
    (hf : ∀ x y, f (x + y) = f x + f y)
    (b : SingularHomology (ProductTorus 3) 3) :
    singularHomologyMap (shear χ) 4
        (positiveCircleCross (ProductTorus 4) 3 (singularHomologyMap f 3 b)) =
      positiveCircleCross (ProductTorus 4) 3 (singularHomologyMap f 3 b) := by
  have hχf : ∀ x y, (χ.comp f) (x + y) = (χ.comp f) x + (χ.comp f) y := by
    intro x y
    change χ (f (x + y)) = χ (f x) + χ (f y)
    rw [hf, hχ]
  have hnat := positiveCircleCross_naturality f 3 b
  calc
    singularHomologyMap (shear χ) 4
        (positiveCircleCross (ProductTorus 4) 3 (singularHomologyMap f 3 b)) =
      singularHomologyMap (shear χ) 4
        (singularHomologyMap (circleProductMap f) 4
          (positiveCircleCross (ProductTorus 3) 3 b)) :=
      congrArg (singularHomologyMap (shear χ) 4) hnat.symm
    _ = singularHomologyMap (circleProductMap f) 4
        (singularHomologyMap (shearOn 3 (χ.comp f)) 4
          (positiveCircleCross (ProductTorus 3) 3 b)) := by
      rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, shear_comp_threeSubtorus,
        singularHomologyMap_comp, LinearMap.comp_apply]
    _ = singularHomologyMap (circleProductMap f) 4
        (positiveCircleCross (ProductTorus 3) 3 b) :=
      congrArg (singularHomologyMap (circleProductMap f) 4)
        (shearOn_three_homologyFour (χ.comp f) hχf (positiveCircleCross (ProductTorus 3) 3 b))
    _ = positiveCircleCross (ProductTorus 4) 3 (singularHomologyMap f 3 b) := hnat

/-- Every third-homology class, not merely each product generator, has a fixed cross class. -/
theorem shear_positiveCircleCross_three (χ : C(ProductTorus 4, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y)
    (b : SingularHomology (ProductTorus 4) 3) :
    singularHomologyMap (shear χ) 4 (positiveCircleCross (ProductTorus 4) 3 b) =
      positiveCircleCross (ProductTorus 4) 3 b := by
  have h : (singularHomologyMap (shear χ) 4).comp (positiveCircleCross (ProductTorus 4) 3) =
      positiveCircleCross (ProductTorus 4) 3 := by
    apply (coordinateTorusBasis 4 3).ext
    intro i
    simp only [LinearMap.comp_apply, coordinateTorusBasis_apply, coordinateTorusClass]
    exact shear_positiveCircleCross_three_map χ hχ (coordinateTorusMap 4 3 i)
      (coordinateTorusMap_add 4 3 i) (productTorusTopClass 3)
  exact LinearMap.congr_fun h b

end Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryEllipticCapKernelWangShear
