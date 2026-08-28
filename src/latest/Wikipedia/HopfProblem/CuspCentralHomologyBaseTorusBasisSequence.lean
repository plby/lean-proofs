import Wikipedia.HopfProblem.CuspCentralHomologyMiddleSequence
import Wikipedia.HopfProblem.CuspCentralHomologyBoundaryLoopNullhomotopy

/-!
# The actual boundary degree-two integral exact sequence

The outer region at radius one half deformation retracts onto the literal
central double locus. Its inverse homotopy-equivalence map is the actual
boundary inclusion into that region. Transporting the proved middle-degree
Mayer--Vietoris sequence therefore gives an injection of the actual boundary
homology and a surjective integer quotient with precisely that image as
kernel. No splitting or chosen basis is assumed.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction SingularMayerVietoris PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)

/-- The homomorphism induced by the literal inclusion of the central double locus. -/
abbrev boundaryH2Inclusion :
    SingularHomology (centralBoundary C r hr) 2 →ₗ[ℤ]
      SingularHomology (QuotientCentralFibre C r) 2 :=
  singularHomologyMap (centralBoundaryInclusion C r hr) 2

variable (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : SmallDrift C r)

/-- The genuine Mayer--Vietoris integer quotient, with the fixed half-radius cover. -/
def boundaryH2Quotient : SingularHomology (QuotientCentralFibre C r) 2 →ₗ[ℤ] ℤ :=
  middleQuotientMap C r hr hr1 hC hR (1 / 2) (by norm_num) (by norm_num)

include hr1 hC hR

local notation "U" => outerRegion C r hr (1 / 2)

/-- The actual boundary inclusion is injective on integral degree-two homology. -/
theorem boundaryH2Inclusion_injective : Function.Injective (boundaryH2Inclusion C r hr) := by
  let e := outerRegionBoundaryHomotopyEquiv C r hr (1 / 2)
    (by norm_num) (by norm_num) hr1 hC hR
  have he : (subtypeInclusion U).comp e.symm.toFun = centralBoundaryInclusion C r hr := by
    apply ContinuousMap.ext
    intro q
    rfl
  change Function.Injective (singularHomologyMap (centralBoundaryInclusion C r hr) 2)
  rw [← he, singularHomologyMap_comp]
  intro x y hxy
  have hE : singularHomologyMap e.symm.toFun 2 x =
      singularHomologyMap e.symm.toFun 2 y :=
    (middleOuterInclusion_injective C r hr hr1 hC hR
      (1 / 2) (by norm_num) (by norm_num)) hxy
  apply (homotopyEquivHomologyEquiv e 2).symm.injective
  simpa only [homotopyEquivHomologyEquiv_symm_apply] using hE

/-- The original boundary inclusion and outer-region inclusion have exactly
the same integral homology image. -/
theorem boundaryH2Inclusion_range_eq_outer :
    LinearMap.range (boundaryH2Inclusion C r hr) =
      LinearMap.range (singularHomologyMap (subtypeInclusion U) 2) := by
  let e := outerRegionBoundaryHomotopyEquiv C r hr (1 / 2)
    (by norm_num) (by norm_num) hr1 hC hR
  have he : (subtypeInclusion U).comp e.symm.toFun = centralBoundaryInclusion C r hr := by
    apply ContinuousMap.ext
    intro q
    rfl
  change LinearMap.range (singularHomologyMap (centralBoundaryInclusion C r hr) 2) = _
  rw [← he, singularHomologyMap_comp]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearEquiv.range (homotopyEquivHomologyEquiv e 2).symm)

theorem boundaryH2Quotient_surjective :
    Function.Surjective (boundaryH2Quotient C r hr hr1 hC hR) :=
  middleQuotientMap_surjective C r hr hr1 hC hR
    (1 / 2) (by norm_num) (by norm_num)

/-- The literal boundary image is precisely the kernel of the actual
integer quotient, over the integers without tensoring. -/
theorem boundaryH2Inclusion_range_eq_ker :
    LinearMap.range (boundaryH2Inclusion C r hr) =
      LinearMap.ker (boundaryH2Quotient C r hr hr1 hC hR) := by
  rw [boundaryH2Inclusion_range_eq_outer C r hr hr1 hC hR]
  exact middleSecondHomology_exact C r hr hr1 hC hR
    (1 / 2) (by norm_num) (by norm_num)

@[simp] theorem boundaryH2Quotient_inclusion
    (x : SingularHomology (centralBoundary C r hr) 2) :
    boundaryH2Quotient C r hr hr1 hC hR (boundaryH2Inclusion C r hr x) = 0 := by
  have hx : boundaryH2Inclusion C r hr x ∈ LinearMap.range (boundaryH2Inclusion C r hr) :=
    ⟨x, rfl⟩
  rw [boundaryH2Inclusion_range_eq_ker C r hr hr1 hC hR] at hx
  exact hx

theorem boundaryH2Quotient_comp_inclusion :
    (boundaryH2Quotient C r hr hr1 hC hR).comp (boundaryH2Inclusion C r hr) = 0 := by
  apply LinearMap.ext
  intro x
  exact boundaryH2Quotient_inclusion C r hr hr1 hC hR x

end Wikipedia.HopfProblem.CuspCentralHomology
