import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTopShearBasic

/-!
# The native top-homology shear of a circle times a two-torus

The two-torus is a literal coordinate retract of the four-torus. Extending
the character along this retraction permits the established positive-circle
cross-product calculation to be pulled back through an injective actual
singular-homology map. The vanishing of the two-torus's third homology makes
that cross-product calculation exhaustive in degree three.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryEllipticCapKernelWangShear

open SingularMayerVietoris PeriodTorusHigherHomology CircleTopology

private def twoToFour : C(ProductTorus 2, ProductTorus 4) :=
  (torusTailMap 3).comp (torusTailMap 2)

private def fourToTwo : C(ProductTorus 4, ProductTorus 2) :=
  ⟨fun x i => x i.succ.succ, continuous_pi fun i => continuous_apply i.succ.succ⟩

private theorem fourToTwo_twoToFour (x : ProductTorus 2) :
    fourToTwo (twoToFour x) = x := by
  funext i
  rfl

private theorem circleProduct_retract :
    (circleProductMap fourToTwo).comp (circleProductMap twoToFour) =
      ContinuousMap.id (Circle × ProductTorus 2) := by
  apply ContinuousMap.ext
  intro p
  exact Prod.ext rfl (fourToTwo_twoToFour p.2)

private theorem circleProduct_twoToFour_homology_injective (n : ℕ) :
    Function.Injective (singularHomologyMap (circleProductMap twoToFour) n) := by
  have h : Function.LeftInverse
      (singularHomologyMap (circleProductMap fourToTwo) n)
      (singularHomologyMap (circleProductMap twoToFour) n) := by
    intro a
    change ((singularHomologyMap (circleProductMap fourToTwo) n).comp
      (singularHomologyMap (circleProductMap twoToFour) n)) a = a
    rw [← singularHomologyMap_comp, circleProduct_retract, singularHomologyMap_id,
      LinearMap.id_apply]
  exact h.injective

private theorem positiveCircleCross_two_surjective :
    Function.Surjective (positiveCircleCross (ProductTorus 2) 2) := by
  let := productTorus_homology_subsingleton_of_lt (show 2 < 3 by decide)
  intro a
  obtain ⟨b, rfl⟩ := (circleProductHomologyEquiv (ProductTorus 2) 2).symm.surjective a
  refine ⟨b.2, ?_⟩
  rw [circleProductHomologyEquiv_symm_eq_section_add_cross,
    (Subsingleton.elim b.1 0), map_zero, zero_add]

private theorem twoToFour_shear (χ : C(ProductTorus 2, Circle)) :
    (circleProductMap twoToFour).comp (shearOn 2 χ) =
      (shear (χ.comp fourToTwo)).comp (circleProductMap twoToFour) := by
  apply ContinuousMap.ext
  rintro ⟨c, x⟩
  change (c - χ x, twoToFour x) =
    (c - χ (fourToTwo (twoToFour x)), twoToFour x)
  rw [fourToTwo_twoToFour]

private theorem shearOn_two_positiveCircleCross (χ : C(ProductTorus 2, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y)
    (b : SingularHomology (ProductTorus 2) 2) :
    singularHomologyMap (shearOn 2 χ) 3 (positiveCircleCross (ProductTorus 2) 2 b) =
      positiveCircleCross (ProductTorus 2) 2 b := by
  apply circleProduct_twoToFour_homology_injective 3
  change ((singularHomologyMap (circleProductMap twoToFour) 3).comp
    (singularHomologyMap (shearOn 2 χ) 3)) (positiveCircleCross (ProductTorus 2) 2 b) = _
  rw [← singularHomologyMap_comp, twoToFour_shear, singularHomologyMap_comp,
    LinearMap.comp_apply, positiveCircleCross_naturality]
  apply shear_positiveCircleCross_two (χ.comp fourToTwo)
  intro x y
  change χ (fourToTwo x + fourToTwo y) = χ (fourToTwo x) + χ (fourToTwo y)
  exact hχ _ _

/-- An additive character shear fixes every genuine top-homology class of
the circle times the two-torus. -/
theorem shearOn_two_homologyThree (χ : C(ProductTorus 2, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y)
    (a : SingularHomology (Circle × ProductTorus 2) 3) :
    singularHomologyMap (shearOn 2 χ) 3 a = a := by
  obtain ⟨b, rfl⟩ := positiveCircleCross_two_surjective a
  exact shearOn_two_positiveCircleCross χ hχ b

end Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryEllipticCapKernelWangShear
