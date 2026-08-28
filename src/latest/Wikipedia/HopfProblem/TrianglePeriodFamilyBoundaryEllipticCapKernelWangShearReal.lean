import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangShearCross

/-!
# The shear calculation on the original real lattice torus

The character and shear are defined on the original quotient torus.
The actual flat-torus homeomorphism conjugates this shear to the one on
four additive circles. Naturality of the genuine positive-circle cross
product transports the preceding calculation without changing its sign
or identifying homology by an abstract rank comparison.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryEllipticCapKernelWangShear

open SingularMayerVietoris PeriodTorusHigherHomology
  PeriodTorusHigherHomology.CircleTopology

/-- Subtract the actual character value while keeping the original quotient-torus point. -/
def realShear (χ : C(RealTorus₄, Circle)) : C(Circle × RealTorus₄, Circle × RealTorus₄) where
  toFun z := (z.1 - χ z.2, z.2)
  continuous_toFun := (continuous_fst.sub (χ.continuous.comp continuous_snd)).prodMk
    continuous_snd

@[simp] theorem realShear_apply (χ : C(RealTorus₄, Circle)) (z : Circle × RealTorus₄) :
    realShear χ z = (z.1 - χ z.2, z.2) := rfl

/-- The same character in the actual four-circle coordinates. -/
def coordinateCharacter (χ : C(RealTorus₄, Circle)) : C(ProductTorus 4, Circle) :=
  χ.comp (flatTorusCircleHomeomorph.symm : C(ProductTorus 4, RealTorus₄))

@[simp] theorem coordinateCharacter_apply (χ : C(RealTorus₄, Circle)) (x : ProductTorus 4) :
    coordinateCharacter χ x = χ (flatTorusCircleHomeomorph.symm x) := rfl

/-- Additivity follows from the literal additive flat-torus homeomorphism. -/
theorem coordinateCharacter_add (χ : C(RealTorus₄, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) (x y : ProductTorus 4) :
    coordinateCharacter χ (x + y) = coordinateCharacter χ x + coordinateCharacter χ y := by
  have h : flatTorusCircleHomeomorph.symm (x + y) =
      flatTorusCircleHomeomorph.symm x + flatTorusCircleHomeomorph.symm y := by
    apply flatTorusCircleHomeomorph.injective
    rw [Homeomorph.apply_symm_apply, flatTorusCircleHomeomorph_add,
      Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  change χ (flatTorusCircleHomeomorph.symm (x + y)) =
    χ (flatTorusCircleHomeomorph.symm x) + χ (flatTorusCircleHomeomorph.symm y)
  rw [h, hχ]

/-- The actual product homeomorphism leaves the circle coordinate untouched. -/
def realCircleCoordinates : (Circle × RealTorus₄) ≃ₜ (Circle × ProductTorus 4) :=
  (Homeomorph.refl Circle).prodCongr flatTorusCircleHomeomorph

@[simp] theorem realCircleCoordinates_apply (z : Circle × RealTorus₄) :
    realCircleCoordinates z = (z.1, flatTorusCircleHomeomorph z.2) := rfl

/-- The native product homeomorphism has exactly the map used in cross-product naturality. -/
theorem realCircleCoordinates_toContinuousMap :
    (realCircleCoordinates : C(Circle × RealTorus₄, Circle × ProductTorus 4)) =
      circleProductMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) := rfl

/-- Equality of the original maps, before passing to homology. -/
theorem realShear_coordinates (χ : C(RealTorus₄, Circle)) :
    (circleProductMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4))).comp
        (realShear χ) =
      (shear (coordinateCharacter χ)).comp
        (circleProductMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4))) := by
  apply ContinuousMap.ext
  rintro ⟨z, x⟩
  change (z - χ x, flatTorusCircleHomeomorph x) =
    (z - χ (flatTorusCircleHomeomorph.symm (flatTorusCircleHomeomorph x)),
      flatTorusCircleHomeomorph x)
  rw [Homeomorph.symm_apply_apply]

/-- The coordinate square commutes for the actual induced singular-homology maps. -/
theorem realShear_coordinate_homology (χ : C(RealTorus₄, Circle)) (n : ℕ)
    (a : SingularHomology (Circle × RealTorus₄) n) :
    singularHomologyMap
        (circleProductMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4))) n
      (singularHomologyMap (realShear χ) n a) =
    singularHomologyMap (shear (coordinateCharacter χ)) n
      (singularHomologyMap
        (circleProductMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4))) n a) := by
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, realShear_coordinates,
    singularHomologyMap_comp, LinearMap.comp_apply]

/-- The real-torus shear fixes the genuine cross summand in both required Wang degrees. -/
theorem realShear_positiveCircleCross (χ : C(RealTorus₄, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) (n : ℕ) (hn : n = 1 ∨ n = 2)
    (b : SingularHomology RealTorus₄ n) :
    singularHomologyMap (realShear χ) (n + 1) (positiveCircleCross RealTorus₄ n b) =
      positiveCircleCross RealTorus₄ n b := by
  apply (homeomorphHomologyEquiv realCircleCoordinates (n + 1)).injective
  change singularHomologyMap
      (circleProductMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4))) (n + 1)
    (singularHomologyMap (realShear χ) (n + 1) (positiveCircleCross RealTorus₄ n b)) =
    singularHomologyMap
      (circleProductMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4))) (n + 1)
    (positiveCircleCross RealTorus₄ n b)
  simp only [realShear_coordinate_homology, positiveCircleCross_naturality]
  exact shear_positiveCircleCross (coordinateCharacter χ) (coordinateCharacter_add χ hχ)
    n hn (singularHomologyMap (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) n b)

theorem realShear_positiveCircleCross_one (χ : C(RealTorus₄, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) (b : SingularHomology RealTorus₄ 1) :
    singularHomologyMap (realShear χ) 2 (positiveCircleCross RealTorus₄ 1 b) =
      positiveCircleCross RealTorus₄ 1 b :=
  realShear_positiveCircleCross χ hχ 1 (Or.inl rfl) b

theorem realShear_positiveCircleCross_two (χ : C(RealTorus₄, Circle))
    (hχ : ∀ x y, χ (x + y) = χ x + χ y) (b : SingularHomology RealTorus₄ 2) :
    singularHomologyMap (realShear χ) 3 (positiveCircleCross RealTorus₄ 2 b) =
      positiveCircleCross RealTorus₄ 2 b :=
  realShear_positiveCircleCross χ hχ 2 (Or.inr rfl) b

end Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryEllipticCapKernelWangShear
