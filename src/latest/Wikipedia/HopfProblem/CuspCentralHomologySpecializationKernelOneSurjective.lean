import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusHomology
import Wikipedia.HopfProblem.CuspCentralHomologyLowDegrees
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationKernelMap
import Mathlib.RingTheory.Noetherian.Orzech

/-!
# Actual degree-one surjectivity of the marked central collapse

The geometric base projection and its geometric section split the actual
singular-homology maps.  Both first-homology groups are independently
integral rank two, so the projection and section are isomorphisms.  The
section factors through the actual product collapse, which therefore
surjects on first homology.  No small-radius assumption or kernel formula
is used in this argument.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction SingularMayerVietoris PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

/-- Surjectivity of the actual base projection is injectivity because
the two actual first-homology groups have the same integral rank. -/
theorem baseTorusProjection_homology_one_injective :
    Function.Injective (baseTorusProjectionHomologyMap C r hr hC 1) := by
  let := productTorus_homology_finite 2 1
  let e : SingularHomology (QuotientCentralFibre C r) 1 ≃ₗ[ℤ]
      SingularHomology (ProductTorus 2) 1 :=
    (centralSingularH1Equiv C r hr hC).trans (productTorusHomologyEquiv 2 1).symm
  exact IsNoetherian.injective_of_surjective_of_injective e.toLinearMap
    (baseTorusProjectionHomologyMap C r hr hC 1) e.injective
    (baseTorusProjectionHomologyMap_surjective C r hr hC 1)

include hC in
/-- Every actual first-homology class of the central fibre comes from
the constructed geometric base section. -/
theorem baseTorusSection_homology_one_surjective :
    Function.Surjective (baseTorusSectionHomologyMap C r hr 1) := by
  intro a
  refine ⟨baseTorusProjectionHomologyMap C r hr hC 1 a, ?_⟩
  apply baseTorusProjection_homology_one_injective C r hr hC
  exact baseTorusProjectionHomologyMap_section C r hr hC 1 _

/-- The first-homology isomorphism is the map of the actual geometric section. -/
def baseTorusSectionHomologyOneEquiv :
    SingularHomology (ProductTorus 2) 1 ≃ₗ[ℤ]
      SingularHomology (QuotientCentralFibre C r) 1 :=
  LinearEquiv.ofBijective (baseTorusSectionHomologyMap C r hr 1)
    ⟨baseTorusSectionHomologyMap_injective C r hr hC 1,
      baseTorusSection_homology_one_surjective C r hr hC⟩

@[simp] theorem baseTorusSectionHomologyOneEquiv_apply
    (a : SingularHomology (ProductTorus 2) 1) :
    baseTorusSectionHomologyOneEquiv C r hr hC a =
      baseTorusSectionHomologyMap C r hr 1 a := rfl

/-- Its inverse is the actual map of the base projection, not a chosen splitting. -/
@[simp] theorem baseTorusSectionHomologyOneEquiv_symm_apply
    (a : SingularHomology (QuotientCentralFibre C r) 1) :
    (baseTorusSectionHomologyOneEquiv C r hr hC).symm a =
      baseTorusProjectionHomologyMap C r hr hC 1 a := by
  apply (baseTorusSectionHomologyOneEquiv C r hr hC).injective
  rw [LinearEquiv.apply_symm_apply, baseTorusSectionHomologyOneEquiv_apply]
  apply baseTorusProjection_homology_one_injective C r hr hC
  exact (baseTorusProjectionHomologyMap_section C r hr hC 1 _).symm

namespace SpecializationModel

/-- The literal unit-phase section of the marked product source. -/
def productBaseTorusSection : C(ProductTorus 2, CompactFibreTorus × ProductTorus 2) where
  toFun b := (1, b)
  continuous_toFun := continuous_const.prodMk continuous_id

/-- The geometric base section factors through the original collapse exactly. -/
theorem productCollapse_comp_baseTorusSection :
    (productCollapse C r hr).comp productBaseTorusSection = baseTorusSection C r hr :=
  ContinuousMap.ext fun _ => rfl

include hC in
/-- Actual first-homology surjectivity follows from the geometric section. -/
theorem productCollapse_homology_one_surjective :
    Function.Surjective (singularHomologyMap (productCollapse C r hr) 1) := by
  intro a
  obtain ⟨b, hb⟩ := baseTorusSection_homology_one_surjective C r hr hC a
  refine ⟨singularHomologyMap productBaseTorusSection 1 b, ?_⟩
  change ((singularHomologyMap (productCollapse C r hr) 1).comp
    (singularHomologyMap productBaseTorusSection 1)) b = a
  rw [← singularHomologyMap_comp, productCollapse_comp_baseTorusSection]
  exact hb

include hC in
/-- The one fixed four-period marking retains actual first-homology surjectivity. -/
theorem markedCollapse_homology_one_surjective :
    Function.Surjective (singularHomologyMap (markedCollapse C r hr) 1) :=
  markedCollapse_homology_surjective_of_product C r hr 1
    (productCollapse_homology_one_surjective C r hr hC)

end SpecializationModel

end Wikipedia.HopfProblem.CuspCentralHomology
