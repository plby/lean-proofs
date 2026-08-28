import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusHomology
import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusBasisAlgebra
import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusBasisSequence

/-!
# The actual boundary and base torus generate the integral second homology

The genuine boundary inclusion has an exact integral quotient `ℤ`, as
proved by the actual Mayer–Vietoris sequence. The actual base projection
kills this inclusion and is split by the geometric base section. Its
integer-valued marking therefore differs from the exact connecting
coordinate by a unit. Consequently its kernel is exactly the boundary
image, and the sum of the two actual geometric maps is an isomorphism.

No rank-only argument or unproved primitivity of the boundary image is
used. The final equivalence retains both original maps literally.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction SingularMayerVietoris PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : SmallDrift C r)

theorem baseTorusH2Functional_surjective :
    Function.Surjective (baseTorusH2Functional C r hr hC) :=
  baseTorusH2Marking.surjective.comp
    (baseTorusProjectionHomologyMap_surjective C r hr hC 2)

/-- Marking the target torus does not change the actual projection kernel. -/
theorem baseTorusH2Functional_ker :
    LinearMap.ker (baseTorusH2Functional C r hr hC) =
      LinearMap.ker (baseTorusProjectionHomologyMap C r hr hC 2) := by
  ext x
  change baseTorusH2Marking (baseTorusProjectionHomologyMap C r hr hC 2 x) = 0 ↔
    baseTorusProjectionHomologyMap C r hr hC 2 x = 0
  constructor
  · intro h
    apply baseTorusH2Marking.injective
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

include hr1 hC hR

/-- Exactness holds for the actual geometric base functional, integrally. -/
theorem boundaryH2Inclusion_range_eq_ker_baseFunctional :
    LinearMap.range (boundaryH2Inclusion C r hr) =
      LinearMap.ker (baseTorusH2Functional C r hr hC) :=
  integerExtension_replaceQuotient (boundaryH2Inclusion C r hr)
    (boundaryH2Quotient C r hr hr1 hC hR) (baseTorusH2Functional C r hr hC)
    (boundaryH2Inclusion_injective C r hr hr1 hC hR)
    (boundaryH2Quotient_surjective C r hr hr1 hC hR)
    (boundaryH2Inclusion_range_eq_ker C r hr hr1 hC hR)
    (baseTorusH2Functional_boundary C r hr hC hr1 hR)
    (baseTorusH2Functional_surjective C r hr hC)

/-- The actual base projection has precisely the genuine double-locus
image as its kernel, not merely the same rational rank. -/
theorem baseTorusProjectionHomologyMap_ker :
    LinearMap.ker (baseTorusProjectionHomologyMap C r hr hC 2) =
      LinearMap.range (boundaryH2Inclusion C r hr) := by
  rw [← baseTorusH2Functional_ker,
    ← boundaryH2Inclusion_range_eq_ker_baseFunctional C r hr hr1 hC hR]

/-- The integral splitting uses the literal boundary inclusion and the
literal geometric base-torus section as its two forward maps. -/
def baseTorusH2Split :
    (SingularHomology (centralBoundary C r hr) 2 ×
      SingularHomology (ProductTorus 2) 2) ≃ₗ[ℤ]
        SingularHomology (QuotientCentralFibre C r) 2 :=
  splitFromActualSection (boundaryH2Inclusion C r hr)
    (baseTorusProjectionHomologyMap C r hr hC 2)
    (baseTorusSectionHomologyMap C r hr 2)
    (boundaryH2Inclusion_injective C r hr hr1 hC hR)
    (baseTorusProjectionHomologyMap_ker C r hr hr1 hC hR).symm
    (baseTorusProjectionHomologyMap_section C r hr hC 2)

@[simp] theorem baseTorusH2Split_apply
    (p : SingularHomology (centralBoundary C r hr) 2 ×
      SingularHomology (ProductTorus 2) 2) :
    baseTorusH2Split C r hr hr1 hC hR p =
      singularHomologyMap (centralBoundaryInclusion C r hr) 2 p.1 +
        baseTorusSectionHomologyMap C r hr 2 p.2 := rfl

@[simp] theorem baseTorusH2Split_projection
    (p : SingularHomology (centralBoundary C r hr) 2 ×
      SingularHomology (ProductTorus 2) 2) :
    baseTorusProjectionHomologyMap C r hr hC 2
      (baseTorusH2Split C r hr hr1 hC hR p) = p.2 :=
  splitFromActualSection_projection _ _ _ _ _ _ p

@[simp] theorem baseTorusH2Split_symm_snd
    (x : SingularHomology (QuotientCentralFibre C r) 2) :
    ((baseTorusH2Split C r hr hr1 hC hR).symm x).2 =
      baseTorusProjectionHomologyMap C r hr hC 2 x :=
  splitFromActualSection_symm_snd _ _ _ _ _ _ x

@[simp] theorem baseTorusH2Split_inclusion
    (a : SingularHomology (centralBoundary C r hr) 2) :
    baseTorusH2Split C r hr hr1 hC hR (a, 0) =
      singularHomologyMap (centralBoundaryInclusion C r hr) 2 a :=
  splitFromActualSection_apply_inl _ _ _ _ _ _ a

@[simp] theorem baseTorusH2Split_section
    (b : SingularHomology (ProductTorus 2) 2) :
    baseTorusH2Split C r hr hr1 hC hR (0, b) =
      baseTorusSectionHomologyMap C r hr 2 b :=
  splitFromActualSection_apply_inr _ _ _ _ _ _ b

/-- Every integral second-homology class is a sum of the two specified
geometric images. -/
theorem baseTorusH2_generated
    (x : SingularHomology (QuotientCentralFibre C r) 2) :
    ∃ a : SingularHomology (centralBoundary C r hr) 2,
      ∃ b : SingularHomology (ProductTorus 2) 2,
        singularHomologyMap (centralBoundaryInclusion C r hr) 2 a +
          baseTorusSectionHomologyMap C r hr 2 b = x := by
  obtain ⟨⟨a, b⟩, h⟩ := (baseTorusH2Split C r hr hr1 hC hR).surjective x
  exact ⟨a, b, h⟩

end Wikipedia.HopfProblem.CuspCentralHomology
