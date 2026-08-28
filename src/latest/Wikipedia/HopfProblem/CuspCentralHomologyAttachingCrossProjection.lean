import Wikipedia.HopfProblem.CuspCentralHomologyAttachingCross

/-!
# Actual projection maps for a right-hand circle factor

The established circle-product homology splitting is transported through the
literal coordinate homeomorphism from the additive circle on the left to the
complex circle on the right. Its first coordinate is the actual projection
map, and its second coordinate identifies that projection's actual kernel.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspCentralHomology

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] integerLinearMapModule integerTensorModule

variable (X : Type) [TopologicalSpace X]

/-- The literal section at the identity of the right-hand complex circle. -/
def rightCircleSection : C(X, X × _root_.Circle) :=
  (ContinuousMap.id X).prodMk (ContinuousMap.const X 1)

@[simp] theorem rightCircleSection_apply (x : X) : rightCircleSection X x = (x, 1) := rfl

/-- The actual projection has the actual identity-circle section as a right inverse. -/
theorem rightCircleProjection_section (n : ℕ) :
    (singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X)) n).comp
      (singularHomologyMap (rightCircleSection X) n) = LinearMap.id := by
  rw [← singularHomologyMap_comp]
  exact singularHomologyMap_id X n

/-- Projection to the unchanged factor is surjective on actual homology in every degree. -/
theorem rightCircleProjection_surjective_allDegrees (n : ℕ) :
    Function.Surjective
      (singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X)) n) := by
  intro a
  exact ⟨singularHomologyMap (rightCircleSection X) n a,
    LinearMap.congr_fun (rightCircleProjection_section X n) a⟩

/-- Successor-degree form of actual projection surjectivity, indexed as the splitting below. -/
theorem rightCircleProjection_surjective (n : ℕ) :
    Function.Surjective
      (singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X)) (n + 1)) :=
  rightCircleProjection_surjective_allDegrees X (n + 1)

/-- The actual positive-degree circle-product splitting with the circle on the right. -/
def rightCircleProductHomologyEquiv (n : ℕ) :
    SingularHomology (X × _root_.Circle) (n + 1) ≃ₗ[ℤ]
      (SingularHomology X (n + 1) × SingularHomology X n) :=
  (homeomorphHomologyEquiv (circleParametrizedSourceHomeomorph X).symm (n + 1)).trans
    (circleProductHomologyEquiv X n)

/-- The first coordinate is the induced map of the literal product projection. -/
@[simp] theorem rightCircleProductHomologyEquiv_fst (n : ℕ)
    (a : SingularHomology (X × _root_.Circle) (n + 1)) :
    (rightCircleProductHomologyEquiv X n a).1 =
      singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X)) (n + 1) a := by
  change circleProjectionHomology X (n + 1)
    (singularHomologyMap ((circleParametrizedSourceHomeomorph X).symm :
      C(X × _root_.Circle, AddCircle (1 : ℝ) × X)) (n + 1) a) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

@[simp] theorem rightCircleProductHomologyEquiv_symm_projection (n : ℕ)
    (a : SingularHomology X (n + 1) × SingularHomology X n) :
    singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X)) (n + 1)
      ((rightCircleProductHomologyEquiv X n).symm a) = a.1 := by
  rw [← rightCircleProductHomologyEquiv_fst, LinearEquiv.apply_symm_apply]

/-- On the literal projection kernel, the second homology coordinate is an equivalence. -/
def rightCircleProjectionKernelEquiv (n : ℕ) :
    LinearMap.ker
      (singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X)) (n + 1)) ≃ₗ[ℤ]
      SingularHomology X n :=
  ({
    toFun a := (rightCircleProductHomologyEquiv X n a).2
    invFun b := ⟨(rightCircleProductHomologyEquiv X n).symm (0, b), by
      rw [LinearMap.mem_ker, rightCircleProductHomologyEquiv_symm_projection]⟩
    left_inv a := by
      apply Subtype.ext
      apply (rightCircleProductHomologyEquiv X n).injective
      rw [LinearEquiv.apply_symm_apply]
      apply Prod.ext
      · rw [rightCircleProductHomologyEquiv_fst]
        exact a.property.symm
      · rfl
    right_inv b := by
      change ((rightCircleProductHomologyEquiv X n)
        ((rightCircleProductHomologyEquiv X n).symm (0, b))).2 = b
      rw [LinearEquiv.apply_symm_apply]
    map_add' a b := by
      change (rightCircleProductHomologyEquiv X n ((a : _) + b)).2 = _
      rw [map_add]
      rfl
  } : LinearMap.ker
      (singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X)) (n + 1)) ≃+
        SingularHomology X n).toIntLinearEquiv

@[simp] theorem rightCircleProjectionKernelEquiv_apply (n : ℕ)
    (a : LinearMap.ker
      (singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X)) (n + 1))) :
    rightCircleProjectionKernelEquiv X n a =
      (rightCircleProductHomologyEquiv X n a).2 := rfl

@[simp] theorem rightCircleProjectionKernelEquiv_symm_coe (n : ℕ)
    (b : SingularHomology X n) :
    ((rightCircleProjectionKernelEquiv X n).symm b :
      SingularHomology (X × _root_.Circle) (n + 1)) =
        (rightCircleProductHomologyEquiv X n).symm (0, b) := rfl

theorem circleParametrizedSourceHomeomorph_symm_section :
    ((circleParametrizedSourceHomeomorph X).symm :
      C(X × _root_.Circle, AddCircle (1 : ℝ) × X)).comp (rightCircleSection X) =
        CircleTopology.productSection X := by
  apply ContinuousMap.ext
  intro x
  change (circleCoordinateHomeomorph (1 : _root_.Circle), x) = (0, x)
  rw [circleCoordinateHomeomorph_one]

/-- The literal identity-circle section is precisely the first homology summand. -/
@[simp] theorem rightCircleProductHomologyEquiv_section (n : ℕ)
    (a : SingularHomology X (n + 1)) :
    rightCircleProductHomologyEquiv X n
      (singularHomologyMap (rightCircleSection X) (n + 1) a) = (a, 0) := by
  change circleProductHomologyEquiv X n
    (singularHomologyMap ((circleParametrizedSourceHomeomorph X).symm :
      C(X × _root_.Circle, AddCircle (1 : ℝ) × X)) (n + 1)
        (singularHomologyMap (rightCircleSection X) (n + 1) a)) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    circleParametrizedSourceHomeomorph_symm_section]
  exact circleProductHomologyEquiv_section X n a

@[simp] theorem rightCircleProductHomologyEquiv_symm_inl (n : ℕ)
    (a : SingularHomology X (n + 1)) :
    (rightCircleProductHomologyEquiv X n).symm (a, 0) =
      singularHomologyMap (rightCircleSection X) (n + 1) a := by
  apply (rightCircleProductHomologyEquiv X n).injective
  rw [LinearEquiv.apply_symm_apply, rightCircleProductHomologyEquiv_section]

end Wikipedia.HopfProblem.CuspCentralHomology
