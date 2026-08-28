import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleProductMaps
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCoordinateAlgebra

/-!
# The actual integral homology splitting for a circle product

The proved singular Mayer–Vietoris sequence for the explicit two-arc
cover gives the antidiagonal image of its connecting map. Projection
onto the unchanged factor splits the actual fixed-section homomorphism.
Together these facts give `H_{n+1}(Circle × X) ≃ H_{n+1}(X) × H_n(X)`.

The lower interval is the first intersection component. We take the
negative of its connecting coordinate; thus a raw connecting value
`(-a,a)` has marked circle coordinate `a`. No Künneth or Eilenberg–Zilber
statement is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris CircleTopology

variable (X : Type) [TopologicalSpace X]

/-- The actual connecting map for the explicit circle-product open cover. -/
abbrev circleMayerVietorisConnecting (n : ℕ) :
    SingularHomology (Circle × X) (n + 1) →ₗ[ℤ]
      SingularHomology (productU X ∩ productV X : Set (Circle × X)) n :=
  connectingHomomorphism (productU X) (productV X)
    (productU_open X) (productV_open X) (product_cover X) n

/-- The two actual intersection coordinates of the circle connecting map. -/
def circleBoundaryCoordinates (n : ℕ) :
    SingularHomology (Circle × X) (n + 1) →ₗ[ℤ]
      (SingularHomology X n × SingularHomology X n) :=
  (productIntersectionHomologyEquiv X n).toLinearMap.comp
    (circleMayerVietorisConnecting X n)

@[simp] theorem circleBoundaryCoordinates_apply (n : ℕ)
    (a : SingularHomology (Circle × X) (n + 1)) :
    circleBoundaryCoordinates X n a =
      productIntersectionHomologyEquiv X n (circleMayerVietorisConnecting X n a) := rfl

/-- Exactness identifies the actual connecting image with the antidiagonal. -/
theorem circleBoundaryCoordinates_range (n : ℕ) :
    LinearMap.range (circleBoundaryCoordinates X n) =
      LinearMap.ker (pairSumMap (SingularHomology X n)) := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    have hb : circleMayerVietorisConnecting X n b ∈
        LinearMap.range (circleMayerVietorisConnecting X n) := ⟨b, rfl⟩
    rw [exact_at_intersection (productU X) (productV X)
      (productU_open X) (productV_open X) (product_cover X)] at hb
    have he := congrArg (productArcHomologyEquiv X n) hb
    rw [circleProductLeftHomologyMap_apply, map_zero] at he
    exact congrArg Prod.fst he
  · intro ha
    have ha' : a.1 + a.2 = 0 := ha
    have hleft : leftHomologyMap (productU X) (productV X) n
        ((productIntersectionHomologyEquiv X n).symm a) = 0 := by
      apply (productArcHomologyEquiv X n).injective
      rw [circleProductLeftHomologyMap_apply, LinearEquiv.apply_symm_apply, map_zero]
      exact Prod.ext ha' (ha' ▸ neg_zero)
    have hi : (productIntersectionHomologyEquiv X n).symm a ∈
        LinearMap.range (circleMayerVietorisConnecting X n) := by
      rw [exact_at_intersection (productU X) (productV X)
        (productU_open X) (productV_open X) (product_cover X)]
      exact hleft
    obtain ⟨b, hb⟩ := hi
    refine ⟨b, ?_⟩
    change productIntersectionHomologyEquiv X n (circleMayerVietorisConnecting X n b) = a
    rw [hb, LinearEquiv.apply_symm_apply]

/-- The actual right Mayer–Vietoris map and the fixed section have the same image. -/
theorem circleProductRightHomologyMap_range (n : ℕ) :
    LinearMap.range (rightHomologyMap (productU X) (productV X) n) =
      LinearMap.range (circleSectionHomology X n) := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(productArcHomologyEquiv X n a).1 + (productArcHomologyEquiv X n a).2,
      (circleProductRightHomologyMap_apply X n a).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨(productArcHomologyEquiv X n).symm (a, 0), ?_⟩
    rw [circleProductRightHomologyMap_apply, LinearEquiv.apply_symm_apply]
    exact congrArg (circleSectionHomology X n) (add_zero a)

/-- Exactness at ambient homology identifies the connecting kernel with
the image of the actual section, not merely an abstract isomorphic subgroup. -/
theorem circleBoundaryCoordinates_ker (n : ℕ) :
    LinearMap.range (circleSectionHomology X (n + 1)) =
      LinearMap.ker (circleBoundaryCoordinates X n) := by
  rw [circleBoundaryCoordinates, rightTransport_second_ker]
  rw [← exact_at_ambient (productU X) (productV X)
    (productU_open X) (productV_open X) (product_cover X)]
  exact (circleProductRightHomologyMap_range X (n + 1)).symm

/-- The signed circle coordinate is the negative lower-component connecting coordinate. -/
def circleBoundary (n : ℕ) :
    SingularHomology (Circle × X) (n + 1) →ₗ[ℤ] SingularHomology X n :=
  (negativeFirstMap (SingularHomology X n)).comp (circleBoundaryCoordinates X n)

@[simp] theorem circleBoundary_apply (n : ℕ)
    (a : SingularHomology (Circle × X) (n + 1)) :
    circleBoundary X n a = -(circleBoundaryCoordinates X n a).1 := rfl

/-- The actual signed circle connecting coordinate is onto in every degree. -/
theorem circleBoundary_surjective (n : ℕ) : Function.Surjective (circleBoundary X n) :=
  circleBoundary_negativeFirst_surjective (circleBoundaryCoordinates X n)
    (circleBoundaryCoordinates_range X n)

/-- The actual circle-product short exact sequence in adjacent degrees. -/
theorem circleBoundary_exact (n : ℕ) :
    LinearMap.range (circleSectionHomology X (n + 1)) =
      LinearMap.ker (circleBoundary X n) :=
  (circleBoundaryCoordinates_ker X n).trans
    (circleBoundary_negativeFirst_ker (circleBoundaryCoordinates X n)
      (circleBoundaryCoordinates_range X n)).symm

/-- The actual integral circle-product homology splitting in every positive degree. -/
def circleProductHomologyEquiv (n : ℕ) :
    SingularHomology (Circle × X) (n + 1) ≃ₗ[ℤ]
      (SingularHomology X (n + 1) × SingularHomology X n) :=
  circleSplitExactEquiv (circleSectionHomology X (n + 1))
    (circleProjectionHomology X (n + 1)) (circleBoundaryCoordinates X n)
    (circleProjection_section X (n + 1)) (circleBoundaryCoordinates_ker X n)
    (circleBoundaryCoordinates_range X n)

@[simp] theorem circleProductHomologyEquiv_apply (n : ℕ)
    (a : SingularHomology (Circle × X) (n + 1)) :
    circleProductHomologyEquiv X n a =
      (circleProjectionHomology X (n + 1) a, circleBoundary X n a) := rfl

/-- The first summand is exactly the actual zero-section homology map. -/
@[simp] theorem circleProductHomologyEquiv_section (n : ℕ)
    (a : SingularHomology X (n + 1)) :
    circleProductHomologyEquiv X n (circleSectionHomology X (n + 1) a) = (a, 0) :=
  circleSplitExactEquiv_apply_inclusion _ _ _ _ _ _ a

@[simp] theorem circleProductHomologyEquiv_symm_inl (n : ℕ)
    (a : SingularHomology X (n + 1)) :
    (circleProductHomologyEquiv X n).symm (a, 0) = circleSectionHomology X (n + 1) a :=
  circleSplitExactEquiv_symm_apply_inl _ _ _ _ _ _ a

@[simp] theorem circleProductHomologyEquiv_symm_projection (n : ℕ)
    (a : SingularHomology X (n + 1) × SingularHomology X n) :
    circleProjectionHomology X (n + 1) ((circleProductHomologyEquiv X n).symm a) = a.1 :=
  circleSplitExactEquiv_symm_fst _ _ _ _ _ _ a

/-- The raw connecting value records the lower/upper component signs explicitly. -/
theorem circleProductHomologyEquiv_symm_boundaryCoordinates (n : ℕ)
    (a : SingularHomology X (n + 1) × SingularHomology X n) :
    circleBoundaryCoordinates X n ((circleProductHomologyEquiv X n).symm a) =
      (-a.2, a.2) :=
  circleSplitExactEquiv_symm_boundary _ _ _ _ _ _ a

/-- The actual section is also onto in degree zero. -/
theorem circleSectionHomology_zero_surjective :
    Function.Surjective (circleSectionHomology X 0) := by
  intro b
  obtain ⟨a, ha⟩ := rightHomologyMap_zero_surjective (productU X) (productV X)
    (productU_open X) (productV_open X) (product_cover X) b
  exact ⟨(productArcHomologyEquiv X 0 a).1 + (productArcHomologyEquiv X 0 a).2,
    (circleProductRightHomologyMap_apply X 0 a).symm.trans ha⟩

/-- Degree-zero homology of the circle product is the actual projection
isomorphism, with inverse the actual fixed section. -/
def circleProductHomologyZeroEquiv :
    SingularHomology (Circle × X) 0 ≃ₗ[ℤ] SingularHomology X 0 where
  toLinearMap := circleProjectionHomology X 0
  invFun := circleSectionHomology X 0
  left_inv b := by
    obtain ⟨a, rfl⟩ := circleSectionHomology_zero_surjective X b
    exact congrArg (circleSectionHomology X 0)
      (LinearMap.congr_fun (circleProjection_section X 0) a)
  right_inv a := LinearMap.congr_fun (circleProjection_section X 0) a

@[simp] theorem circleProductHomologyZeroEquiv_apply
    (a : SingularHomology (Circle × X) 0) :
    circleProductHomologyZeroEquiv X a = circleProjectionHomology X 0 a := rfl

@[simp] theorem circleProductHomologyZeroEquiv_symm_apply (a : SingularHomology X 0) :
    (circleProductHomologyZeroEquiv X).symm a = circleSectionHomology X 0 a := rfl

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
