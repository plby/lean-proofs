import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusSection
import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusTheta
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroupsTopClass

/-!
# Singular homology of the geometric base-torus section

The actual base projection is a left inverse of its constructed geometric
section. Functoriality gives a split injection on integral singular homology
in every degree. The marked top class of the two-torus therefore gives a
specified primitive, infinite-order class in the original central fibre.
No splitting of its homology is chosen, and no claim is made here that
this class and the double curves form a complete basis.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction SingularMayerVietoris PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)

/-- The actual map induced by the geometric section in every degree. -/
abbrev baseTorusSectionHomologyMap (n : ℕ) :
    SingularHomology (ProductTorus 2) n →ₗ[ℤ]
      SingularHomology (QuotientCentralFibre C r) n :=
  singularHomologyMap (baseTorusSection C r hr) n

/-- The actual map induced by projection onto the geometric base torus. -/
abbrev baseTorusProjectionHomologyMap
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) (n : ℕ) :
    SingularHomology (QuotientCentralFibre C r) n →ₗ[ℤ]
      SingularHomology (ProductTorus 2) n :=
  singularHomologyMap (baseTorusProjectionMap C r hr hC) n

variable (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

@[simp] theorem baseTorusProjectionMap_comp_section :
    (baseTorusProjectionMap C r hr hC).comp (baseTorusSection C r hr) =
      ContinuousMap.id (ProductTorus 2) :=
  ContinuousMap.ext (baseTorusProjection_section C r hr)

/-- The splitting is induced by the proved identity of the actual maps. -/
@[simp] theorem baseTorusProjectionHomologyMap_comp_section (n : ℕ) :
    (baseTorusProjectionHomologyMap C r hr hC n).comp
      (baseTorusSectionHomologyMap C r hr n) = LinearMap.id := by
  rw [← singularHomologyMap_comp, baseTorusProjectionMap_comp_section,
    singularHomologyMap_id]

@[simp] theorem baseTorusProjectionHomologyMap_section (n : ℕ)
    (a : SingularHomology (ProductTorus 2) n) :
    baseTorusProjectionHomologyMap C r hr hC n
      (baseTorusSectionHomologyMap C r hr n a) = a :=
  LinearMap.congr_fun (baseTorusProjectionHomologyMap_comp_section C r hr hC n) a

include hC in
theorem baseTorusSectionHomologyMap_injective (n : ℕ) :
    Function.Injective (baseTorusSectionHomologyMap C r hr n) :=
  (show Function.LeftInverse (baseTorusProjectionHomologyMap C r hr hC n)
    (baseTorusSectionHomologyMap C r hr n) from
      baseTorusProjectionHomologyMap_section C r hr hC n).injective

theorem baseTorusProjectionHomologyMap_surjective (n : ℕ) :
    Function.Surjective (baseTorusProjectionHomologyMap C r hr hC n) :=
  (show Function.LeftInverse (baseTorusProjectionHomologyMap C r hr hC n)
    (baseTorusSectionHomologyMap C r hr n) from
      baseTorusProjectionHomologyMap_section C r hr hC n).surjective

/-- The previously proved product-torus marking, evaluated at its unique
top-degree coordinate. -/
def baseTorusH2Marking : SingularHomology (ProductTorus 2) 2 ≃ₗ[ℤ] ℤ :=
  (productTorusHomologyEquiv 2 2).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ)

@[simp] theorem baseTorusH2Marking_topClass :
    baseTorusH2Marking (productTorusTopClass 2) = 1 := by
  exact congrArg (LinearEquiv.funUnique (Fin 1) ℤ ℤ)
    (productTorusHomologyEquiv_topClass 2)

/-- The actual base-torus class is the image of its marked top class
under the genuine geometric section. -/
def baseTorusH2Class : SingularHomology (QuotientCentralFibre C r) 2 :=
  baseTorusSectionHomologyMap C r hr 2 (productTorusTopClass 2)

@[simp] theorem baseTorusProjectionHomologyMap_class :
    baseTorusProjectionHomologyMap C r hr hC 2 (baseTorusH2Class C r hr) =
      productTorusTopClass 2 :=
  baseTorusProjectionHomologyMap_section C r hr hC 2 (productTorusTopClass 2)

/-- The integral coefficient obtained by actual projection to the base torus. -/
def baseTorusH2Functional : SingularHomology (QuotientCentralFibre C r) 2 →ₗ[ℤ] ℤ :=
  baseTorusH2Marking.toLinearMap.comp (baseTorusProjectionHomologyMap C r hr hC 2)

@[simp] theorem baseTorusH2Functional_class :
    baseTorusH2Functional C r hr hC (baseTorusH2Class C r hr) = 1 := by
  change baseTorusH2Marking
    (baseTorusProjectionHomologyMap C r hr hC 2 (baseTorusH2Class C r hr)) = 1
  rw [baseTorusProjectionHomologyMap_class, baseTorusH2Marking_topClass]

include hC in
theorem baseTorusH2Class_ne_zero : baseTorusH2Class C r hr ≠ 0 := by
  intro h
  have he := congrArg (baseTorusH2Functional C r hr hC) h
  rw [baseTorusH2Functional_class, map_zero] at he
  exact one_ne_zero he

include hC in
/-- No nonzero integral multiple of the actual section class vanishes. -/
theorem baseTorusH2Class_zsmul_eq_zero_iff (m : ℤ) :
    m • baseTorusH2Class C r hr = 0 ↔ m = 0 := by
  constructor
  · intro h
    have he := congrArg (baseTorusH2Functional C r hr hC) h
    simpa only [map_zsmul, baseTorusH2Functional_class, map_zero, zsmul_eq_mul,
      Int.cast_id, mul_one]
      using he
  · rintro rfl
    exact zero_smul _ _

include hC in
theorem baseTorusH2Class_zsmul_injective :
    Function.Injective (fun m : ℤ => m • baseTorusH2Class C r hr) := by
  intro m n h
  have he := congrArg (baseTorusH2Functional C r hr hC) h
  simpa only [map_zsmul, baseTorusH2Functional_class, zsmul_eq_mul, Int.cast_id,
    mul_one] using he

include hC in
/-- Primitivity is witnessed by the actual projection functional: an
integral divisor of this class must be a unit. -/
theorem baseTorusH2Class_isUnit_of_smul_eq (m : ℤ)
    (a : SingularHomology (QuotientCentralFibre C r) 2)
    (h : m • a = baseTorusH2Class C r hr) : IsUnit m := by
  have he : m * baseTorusH2Functional C r hr hC a = 1 := by
    have hf := congrArg (baseTorusH2Functional C r hr hC) h
    simpa only [map_zsmul, baseTorusH2Functional_class, zsmul_eq_mul, Int.cast_id] using hf
  exact ⟨⟨m, baseTorusH2Functional C r hr hC a, he, (mul_comm _ _).trans he⟩, rfl⟩

/-- The actual base-torus coefficient vanishes on the homology image
of the genuine central double locus. -/
theorem baseTorusH2Functional_boundary (hr1 : r < 1) (hR : SmallDrift C r)
    (a : SingularHomology (centralBoundary C r hr) 2) :
    baseTorusH2Functional C r hr hC
      (singularHomologyMap (centralBoundaryInclusion C r hr) 2 a) = 0 := by
  change baseTorusH2Marking
    (((baseTorusProjectionHomologyMap C r hr hC 2).comp
      (singularHomologyMap (centralBoundaryInclusion C r hr) 2)) a) = 0
  rw [← singularHomologyMap_comp,
    baseTorusProjection_boundary_homology_two_eq_zero C r hr hr1 hC hR,
    LinearMap.zero_apply, map_zero]

include hC in
/-- The actual base-torus class is not contributed by the double locus. -/
theorem baseTorusH2Class_not_mem_boundary_range (hr1 : r < 1) (hR : SmallDrift C r) :
    baseTorusH2Class C r hr ∉
      LinearMap.range (singularHomologyMap (centralBoundaryInclusion C r hr) 2) := by
  rintro ⟨a, ha⟩
  have he := baseTorusH2Functional_boundary C r hr hC hr1 hR a
  rw [ha, baseTorusH2Functional_class] at he
  exact one_ne_zero he

end Wikipedia.HopfProblem.CuspCentralHomology
