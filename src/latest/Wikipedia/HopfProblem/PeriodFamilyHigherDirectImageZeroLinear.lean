import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageZeroSections

/-!
# The original base-function action on period-family holomorphic descent

Base functions act on the full-preimage sections by multiplication with
their literal pullbacks. The proved all-open holomorphic descent is
linear for this genuine action and commutes with actual restrictions.
The action is not assigned through an abstract vector-space equivalence.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.Zero

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- Actual base functions act through the original holomorphic pullback ring map. -/
instance preimageSectionAlgebra (P : HolomorphicPeriodMap V B) (U : Opens B) :
    Algebra (BaseSection P U) (PreimageSection P U) :=
  (pullbackSection P U).toRingHom.toAlgebra

@[simp] theorem preimageSectionAlgebra_algebraMap (P : HolomorphicPeriodMap V B)
    (U : Opens B) :
    algebraMap (BaseSection P U) (PreimageSection P U) = (pullbackSection P U).toRingHom := rfl

/-- The base action is literally multiplication by the original pullback. -/
theorem base_smul_eq_pullback_mul (P : HolomorphicPeriodMap V B) (U : Opens B)
    (a : BaseSection P U) (s : PreimageSection P U) :
    a • s = pullbackSection P U a * s := rfl

@[simp] theorem base_smul_apply (P : HolomorphicPeriodMap V B) (U : Opens B)
    (a : BaseSection P U) (s : PreimageSection P U) (x : basePreimage P U) :
    (a • s) x = a (baseProjection P U x) * s x := rfl

instance preimageSectionScalarTower (P : HolomorphicPeriodMap V B) (U : Opens B) :
    IsScalarTower ℂ (BaseSection P U) (PreimageSection P U) where
  smul_assoc c a s := by
    let := P.totalChartedSpace
    apply ContMDiffMap.ext
    intro x
    exact mul_assoc c (a (baseProjection P U x)) (s x)

instance preimageSectionSMulCommClass (P : HolomorphicPeriodMap V B) (U : Opens B) :
    SMulCommClass ℂ (BaseSection P U) (PreimageSection P U) where
  smul_comm c a s := by
    let := P.totalChartedSpace
    apply ContMDiffMap.ext
    intro x
    exact mul_left_comm c (a (baseProjection P U x)) (s x)

/-- Actual holomorphic pullback is linear for multiplication by genuine base functions. -/
def pullbackSectionLinearEquiv (P : HolomorphicPeriodMap V B) (U : Opens B) :
    BaseSection P U ≃ₗ[BaseSection P U] PreimageSection P U where
  toFun := pullbackSection P U
  invFun := descendedSection P U
  left_inv := descendedSection_pullbackSection P U
  right_inv := pullbackSection_descendedSection P U
  map_add' := (pullbackSection P U).map_add
  map_smul' a s := (pullbackSection P U).map_mul a s

@[simp] theorem pullbackSectionLinearEquiv_apply (P : HolomorphicPeriodMap V B)
    (U : Opens B) (f : BaseSection P U) :
    pullbackSectionLinearEquiv P U f = pullbackSection P U f := rfl

@[simp] theorem pullbackSectionLinearEquiv_symm_apply (P : HolomorphicPeriodMap V B)
    (U : Opens B) (s : PreimageSection P U) :
    (pullbackSectionLinearEquiv P U).symm s = descendedSection P U s := rfl

/-- The literal zero-section inverse respects the original base-function action. -/
theorem descendedSection_base_smul (P : HolomorphicPeriodMap V B) (U : Opens B)
    (a : BaseSection P U) (s : PreimageSection P U) :
    descendedSection P U (a • s) = a * descendedSection P U s :=
  (pullbackSectionLinearEquiv P U).symm.map_smul a s

/-- The same inverse retains its original pointwise complex scalar action. -/
theorem descendedSection_complex_smul (P : HolomorphicPeriodMap V B) (U : Opens B)
    (c : ℂ) (s : PreimageSection P U) :
    descendedSection P U (c • s) = c • descendedSection P U s :=
  (descendedSection P U).toLinearMap.map_smul c s

/-- The genuine base-function action commutes with the original restrictions. -/
theorem restrict_preimage_base_smul (P : HolomorphicPeriodMap V B) {U W : Opens B}
    (h : U ≤ W) (a : BaseSection P W) (s : PreimageSection P W) :
    preimageRestriction P h (a • s) =
      baseRestriction P h a • preimageRestriction P h s := by
  let := P.totalChartedSpace
  apply ContMDiffMap.ext
  intro x
  rfl

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.Zero
