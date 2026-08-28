import Wikipedia.HopfProblem.CuspCentralHomologyMiddleMaps
import Wikipedia.HopfProblem.CuspCentralHomologyMiddleMayerVietoris
import Wikipedia.HopfProblem.CuspCentralHomologyMiddleAlgebra

/-!
# The actual middle-degree short exact sequence

For the radial open cover of the literal central cusp, the outer
inclusion injects on degree-two homology. Its image is the kernel of
the actual connecting map, expressed in the single integral coordinate
of the projection kernel. A lift of `1` therefore splits the extension.
No short exact sequence or splitting is assumed.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction SingularMayerVietoris PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)

local notation "U" => outerRegion C ε hε a
local notation "V" => innerRegion C ε hε

/-- The actual degree-one difference-map kernel is one copy of `ℤ`. -/
def middleConnectingKernelEquiv :
    LinearMap.ker (leftHomologyMap U V 1) ≃ₗ[ℤ] ℤ :=
  (middleLeftKernelEquiv C ε hε hε1 hC hR a ha ha1 0).trans
    ((compactFibreTorusHomologyEquiv 0).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ))

/-- The quotient coordinate is the actual Mayer–Vietoris connecting
map, followed by the computed one-dimensional kernel coordinate. -/
def middleQuotientMap : SingularHomology (QuotientCentralFibre C ε) 2 →ₗ[ℤ] ℤ :=
  (middleConnectingKernelEquiv C ε hε hε1 hC hR a ha ha1).toLinearMap.comp
    (coverConnectingToKernel U V
      (outerRegion_isOpen C ε hε hε1 hC hR a)
      (innerRegion_isOpen C ε hε hε1 hC hR)
      (outerRegion_union_innerRegion C ε hε a ha1) 1)

include hε1 hC hR ha ha1

theorem middleQuotientMap_surjective :
    Function.Surjective (middleQuotientMap C ε hε hε1 hC hR a ha ha1) :=
  (middleConnectingKernelEquiv C ε hε hε1 hC hR a ha ha1).surjective.comp
    (coverConnectingToKernel_surjective U V
      (outerRegion_isOpen C ε hε hε1 hC hR a)
      (innerRegion_isOpen C ε hε hε1 hC hR)
      (outerRegion_union_innerRegion C ε hε a ha1) 1)

theorem middleQuotientMap_ker :
    LinearMap.ker (middleQuotientMap C ε hε hε1 hC hR a ha ha1) =
      LinearMap.ker (coverConnectingToKernel U V
        (outerRegion_isOpen C ε hε hε1 hC hR a)
        (innerRegion_isOpen C ε hε hε1 hC hR)
        (outerRegion_union_innerRegion C ε hε a ha1) 1) := by
  ext x
  change middleConnectingKernelEquiv C ε hε hε1 hC hR a ha ha1
    (coverConnectingToKernel U V _ _ _ 1 x) = 0 ↔ _
  constructor
  · intro hx
    apply (middleConnectingKernelEquiv C ε hε hε1 hC hR a ha ha1).injective
    simpa only [map_zero] using hx
  · intro hx
    change coverConnectingToKernel U V _ _ _ 1 x = 0 at hx
    rw [hx, map_zero]

omit hε1 hC hR ha ha1 in
/-- The first summand of the genuine sum-of-inclusions map is exactly
the induced map of the actual outer-subset inclusion. -/
theorem middleOuterInclusion_eq_firstSummand :
    singularHomologyMap (subtypeInclusion U) 2 =
      firstSummandMap (rightHomologyMap U V 2) := by
  apply LinearMap.ext
  intro x
  change singularHomologyMap (subtypeInclusion U) 2 x =
    singularHomologyMap (subtypeInclusion U) 2 x +
      singularHomologyMap (subtypeInclusion V) 2 0
  rw [map_zero, add_zero]

theorem middleOuterInclusion_injective :
    Function.Injective (singularHomologyMap (subtypeInclusion U) 2) := by
  rw [middleOuterInclusion_eq_firstSummand C ε hε a]
  exact firstSummandMap_injective_of_signed_formula
    (leftHomologyMap U V 2) (singularHomologyMap (overlapIntoInner C ε hε a) 2)
    (rightHomologyMap U V 2)
    (middleLeftHomologyMap_apply C ε hε hε1 hC hR a ha ha1 1)
    (exact_at_pair U V
      (outerRegion_isOpen C ε hε hε1 hC hR a)
      (innerRegion_isOpen C ε hε hε1 hC hR)
      (outerRegion_union_innerRegion C ε hε a ha1) 2)

theorem middleOuterInclusion_range :
    LinearMap.range (singularHomologyMap (subtypeInclusion U) 2) =
      LinearMap.range (rightHomologyMap U V 2) := by
  rw [middleOuterInclusion_eq_firstSummand C ε hε a]
  exact firstSummandMap_range_of_signed_formula
    (leftHomologyMap U V 2) (singularHomologyMap (overlapIntoInner C ε hε a) 2)
    (overlapIntoInner_homology_surjective C ε hε hε1 hC hR a ha ha1 1)
    (rightHomologyMap U V 2)
    (middleLeftHomologyMap_apply C ε hε hε1 hC hR a ha ha1 1)
    (exact_at_pair U V
      (outerRegion_isOpen C ε hε hε1 hC hR a)
      (innerRegion_isOpen C ε hε hε1 hC hR)
      (outerRegion_union_innerRegion C ε hε a ha1) 2)

/-- Exactness of the actual inclusion and actual integer connecting
coordinate, obtained from singular Mayer–Vietoris. -/
theorem middleSecondHomology_exact :
    LinearMap.range (singularHomologyMap (subtypeInclusion U) 2) =
      LinearMap.ker (middleQuotientMap C ε hε hε1 hC hR a ha ha1) := by
  rw [middleOuterInclusion_range C ε hε hε1 hC hR a ha ha1,
    middleQuotientMap_ker]
  exact coverConnectingToKernel_exact U V
    (outerRegion_isOpen C ε hε hε1 hC hR a)
    (innerRegion_isOpen C ε hε hε1 hC hR)
    (outerRegion_union_innerRegion C ε hε a ha1) 1

/-- The genuine degree-two extension splits by lifting the integer
generator; the outer summand remains the actual inclusion. -/
def middleSecondHomologySplit :
    SingularHomology (QuotientCentralFibre C ε) 2 ≃ₗ[ℤ]
      (SingularHomology U 2 × ℤ) :=
  splitIntegerExtensionEquiv (singularHomologyMap (subtypeInclusion U) 2)
    (middleQuotientMap C ε hε hε1 hC hR a ha ha1)
    (middleOuterInclusion_injective C ε hε hε1 hC hR a ha ha1)
    (middleQuotientMap_surjective C ε hε hε1 hC hR a ha ha1)
    (middleSecondHomology_exact C ε hε hε1 hC hR a ha ha1)

@[simp] theorem middleSecondHomologySplit_snd
    (x : SingularHomology (QuotientCentralFibre C ε) 2) :
    (middleSecondHomologySplit C ε hε hε1 hC hR a ha ha1 x).2 =
      middleQuotientMap C ε hε hε1 hC hR a ha ha1 x :=
  splitIntegerExtensionEquiv_snd _ _ _ _ _ x

@[simp] theorem middleSecondHomologySplit_inclusion (x : SingularHomology U 2) :
    middleSecondHomologySplit C ε hε hε1 hC hR a ha ha1
      (singularHomologyMap (subtypeInclusion U) 2 x) = (x, 0) :=
  splitIntegerExtensionEquiv_apply_inclusion _ _ _ _ _ x

end Wikipedia.HopfProblem.CuspCentralHomology
