import Wikipedia.HopfProblem.TrianglePeriodFamilyGammaZeroHomology
import Wikipedia.HopfProblem.TrianglePeriodFamilyGammaZeroFibres
import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalRegular

/-!
# Zero-γ detection in the constructed special regular family

Every period, covariance, and covering object here is the previously
constructed special one.  The subfamily is a literal closed subspace
of the actual regular family; its fibres and fourth-homology detection
are the proved native constructions, without extra geometric inputs.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.GammaZero

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology

/-- The zero-coordinate subspace of the actual special regular family. -/
abbrev SpecialSpace := Space Canonical.specialRegularData

/-- Its literal inclusion into the original special regular family. -/
def specialInclusion : C(SpecialSpace, Canonical.SpecialRegularFamily) :=
  inclusion Canonical.specialRegularData

def specialProjection : C(SpecialSpace, TriangleRegularQuotient) :=
  projection Canonical.specialRegularData

/-- Each literal special subfamily fibre is an actual product of three circles. -/
def specialFibreTorusHomeomorphAt (b : TriangleRegularPoint) :
    FibreAt Canonical.specialRegularData b ≃ₜ ProductTorus 3 :=
  fibreTorusHomeomorphAt Canonical.specialRegularData b

/-- The actual integral homology map of the special subfamily inclusion. -/
def specialHomologyInclusion (n : ℕ) :
    SingularHomology SpecialSpace n →ₗ[ℤ]
      SingularHomology Canonical.SpecialRegularFamily n :=
  homologyInclusion Canonical.specialRegularData n

@[simp] theorem specialHomologyInclusion_eq_map (n : ℕ) :
    specialHomologyInclusion n = singularHomologyMap specialInclusion n := rfl

theorem specialHomologyInclusion_four_injective :
    Function.Injective (specialHomologyInclusion 4) :=
  homologyInclusion_four_injective Canonical.specialRegularData

/-- The genuine source-kernel coordinate detects all special zero-γ `H₄` classes. -/
theorem specialSourceKernelProjection_comp_inclusion_injective :
    Function.Injective
      ((Homology.sourceKernelProjection Canonical.specialRegularData 3).comp
        (specialHomologyInclusion 4)) :=
  sourceKernelProjection_comp_homologyInclusion_injective Canonical.specialRegularData

/-- Actual residual-fibre control for classes proved to come from this special subfamily. -/
theorem special_eq_zero_of_mem_range_of_sourceKernelProjection_eq_zero
    (a : SingularHomology Canonical.SpecialRegularFamily 4)
    (ha : a ∈ LinearMap.range (specialHomologyInclusion 4))
    (h : Homology.sourceKernelProjection Canonical.specialRegularData 3 a = 0) : a = 0 :=
  eq_zero_of_mem_range_of_sourceKernelProjection_eq_zero Canonical.specialRegularData a ha h

/-- The two actual submodules have zero intersection,
without choosing a regular-family splitting. -/
theorem specialRange_inf_sourceKernelProjection_ker :
    LinearMap.range (specialHomologyInclusion 4) ⊓
      LinearMap.ker (Homology.sourceKernelProjection Canonical.specialRegularData 3) = ⊥ :=
  range_inf_sourceKernelProjection_ker Canonical.specialRegularData

end Wikipedia.HopfProblem.TrianglePeriodFamily.GammaZero
