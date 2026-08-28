import Wikipedia.HopfProblem.CuspCentralCohomologyCoordinatesBasic
import Wikipedia.HopfProblem.CuspCentralCohomologyCoordinatesMatrices
import Wikipedia.HopfProblem.SingularCohomologyFreeCoinvariants

/-!
# Fixed classes for the actual native singular-cohomology pullback

The fixed equations use the actual pullback of `torusMatrixMap M₀` on the
native singular cochain cohomology.  Its proved transpose matrix gives
the exact integral coordinate descriptions.  The displayed sections are
injective and have the entire native fixed submodule as their ranges.
-/

noncomputable section

open scoped Matrix ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open SingularMayerVietoris SingularCohomologyFree PeriodTorusHigherHomology
open PeriodTorusHigherHomologyExterior

/-- The actual first-cohomology fixed equation in positive-loop dual coordinates. -/
theorem coordinateTorusH1_pullback_fixed_iff (a : SingularCohomology (ProductTorus 4) 1) :
    singularCohomologyPullback (torusMatrixMap M₀) 1 a = a ↔
      coordinateTorusH1CohomologyCoordinates a 2 = 0 ∧
        coordinateTorusH1CohomologyCoordinates a 3 = 0 := by
  rw [← coordinateTorusH1CohomologyCoordinates.injective.eq_iff,
    coordinateTorusH1CohomologyCoordinates_pullback]
  exact transpose_M₀_fixed_iff _

theorem coordinateTorusH1_pullback_fixed_iff_exists
    (a : SingularCohomology (ProductTorus 4) 1) :
    singularCohomologyPullback (torusMatrixMap M₀) 1 a = a ↔
      ∃ b c : ℤ, coordinateTorusH1CohomologyCoordinates a = ![b, c, 0, 0] := by
  rw [← coordinateTorusH1CohomologyCoordinates.injective.eq_iff,
    coordinateTorusH1CohomologyCoordinates_pullback]
  exact transpose_M₀_fixed_iff_exists _

/-- The genuine degree-two fixed equation retains the primitive coefficient relation. -/
theorem coordinateTorusH2_pullback_fixed_iff (a : SingularCohomology (ProductTorus 4) 2) :
    singularCohomologyPullback (torusMatrixMap M₀) 2 a = a ↔
      coordinateTorusH2CohomologyCoordinates a 4 = -coordinateTorusH2CohomologyCoordinates a 1 ∧
        coordinateTorusH2CohomologyCoordinates a 5 = 0 := by
  rw [← coordinateTorusH2CohomologyCoordinates.injective.eq_iff,
    coordinateTorusH2CohomologyCoordinates_pullback]
  exact transpose_squareM₀_fixed_iff _

theorem coordinateTorusH2_pullback_fixed_iff_exists
    (a : SingularCohomology (ProductTorus 4) 2) :
    singularCohomologyPullback (torusMatrixMap M₀) 2 a = a ↔
      ∃ b c d e : ℤ, coordinateTorusH2CohomologyCoordinates a = ![b, c, d, e, -c, 0] := by
  rw [← coordinateTorusH2CohomologyCoordinates.injective.eq_iff,
    coordinateTorusH2CohomologyCoordinates_pullback]
  exact transpose_squareM₀_fixed_iff_exists _

/-- The actual third-cohomology fixed equation in the ordered dual-minor basis. -/
theorem coordinateTorusH3_pullback_fixed_iff (a : SingularCohomology (ProductTorus 4) 3) :
    singularCohomologyPullback (torusMatrixMap M₀) 3 a = a ↔
      coordinateTorusH3CohomologyCoordinates a 2 = 0 ∧
        coordinateTorusH3CohomologyCoordinates a 3 = 0 := by
  rw [← coordinateTorusH3CohomologyCoordinates.injective.eq_iff,
    coordinateTorusH3CohomologyCoordinates_pullback]
  exact transpose_cubeM₀_fixed_iff _

theorem coordinateTorusH3_pullback_fixed_iff_exists
    (a : SingularCohomology (ProductTorus 4) 3) :
    singularCohomologyPullback (torusMatrixMap M₀) 3 a = a ↔
      ∃ b c : ℤ, coordinateTorusH3CohomologyCoordinates a = ![b, c, 0, 0] := by
  rw [← coordinateTorusH3CohomologyCoordinates.injective.eq_iff,
    coordinateTorusH3CohomologyCoordinates_pullback]
  exact transpose_cubeM₀_fixed_iff_exists _

theorem coordinateTorusH1_pullback_fixed_iff_mem_range
    (a : SingularCohomology (ProductTorus 4) 1) :
    singularCohomologyPullback (torusMatrixMap M₀) 1 a = a ↔
      coordinateTorusH1CohomologyCoordinates a ∈ LinearMap.range oneFixedSection := by
  rw [← coordinateTorusH1CohomologyCoordinates.injective.eq_iff,
    coordinateTorusH1CohomologyCoordinates_pullback]
  exact transpose_M₀_fixed_iff_mem_range _

theorem coordinateTorusH2_pullback_fixed_iff_mem_range
    (a : SingularCohomology (ProductTorus 4) 2) :
    singularCohomologyPullback (torusMatrixMap M₀) 2 a = a ↔
      coordinateTorusH2CohomologyCoordinates a ∈ LinearMap.range twoFixedSection := by
  rw [← coordinateTorusH2CohomologyCoordinates.injective.eq_iff,
    coordinateTorusH2CohomologyCoordinates_pullback]
  exact transpose_squareM₀_fixed_iff_mem_range _

theorem coordinateTorusH3_pullback_fixed_iff_mem_range
    (a : SingularCohomology (ProductTorus 4) 3) :
    singularCohomologyPullback (torusMatrixMap M₀) 3 a = a ↔
      coordinateTorusH3CohomologyCoordinates a ∈ LinearMap.range threeFixedSection := by
  rw [← coordinateTorusH3CohomologyCoordinates.injective.eq_iff,
    coordinateTorusH3CohomologyCoordinates_pullback]
  exact transpose_cubeM₀_fixed_iff_mem_range _

/-- Integer parameters give actual native first-cohomology classes. -/
def coordinateTorusH1FixedSection :
    (Fin 2 → ℤ) →ₗ[ℤ] SingularCohomology (ProductTorus 4) 1 :=
  coordinateTorusH1CohomologyCoordinates.symm.toLinearMap.comp oneFixedSection

/-- Integer parameters give actual native second-cohomology classes. -/
def coordinateTorusH2FixedSection :
    (Fin 4 → ℤ) →ₗ[ℤ] SingularCohomology (ProductTorus 4) 2 :=
  coordinateTorusH2CohomologyCoordinates.symm.toLinearMap.comp twoFixedSection

/-- Integer parameters give actual native third-cohomology classes. -/
def coordinateTorusH3FixedSection :
    (Fin 2 → ℤ) →ₗ[ℤ] SingularCohomology (ProductTorus 4) 3 :=
  coordinateTorusH3CohomologyCoordinates.symm.toLinearMap.comp threeFixedSection

theorem coordinateTorusH1FixedSection_injective :
    Function.Injective coordinateTorusH1FixedSection :=
  coordinateTorusH1CohomologyCoordinates.symm.injective.comp oneFixedSection_injective

theorem coordinateTorusH2FixedSection_injective :
    Function.Injective coordinateTorusH2FixedSection :=
  coordinateTorusH2CohomologyCoordinates.symm.injective.comp twoFixedSection_injective

theorem coordinateTorusH3FixedSection_injective :
    Function.Injective coordinateTorusH3FixedSection :=
  coordinateTorusH3CohomologyCoordinates.symm.injective.comp threeFixedSection_injective

theorem mem_range_equiv_symm_comp {M : Type*} [AddCommGroup M] [Module ℤ M] {k r : ℕ}
    (e : M ≃ₗ[ℤ] (Fin k → ℤ)) (p : (Fin r → ℤ) →ₗ[ℤ] (Fin k → ℤ)) (x : M) :
    x ∈ LinearMap.range (e.symm.toLinearMap.comp p) ↔ e x ∈ LinearMap.range p := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, (e.apply_symm_apply (p y)).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    change e.symm (p y) = x
    rw [hy, LinearEquiv.symm_apply_apply]

/-- These parameters exhaust the literal native first-cohomology fixed submodule. -/
theorem coordinateTorusH1FixedSection_range :
    LinearMap.range coordinateTorusH1FixedSection =
      singularCohomologyFixed (torusMatrixMap M₀) 1 := by
  ext a
  rw [mem_singularCohomologyFixed_iff, coordinateTorusH1_pullback_fixed_iff_mem_range]
  exact mem_range_equiv_symm_comp coordinateTorusH1CohomologyCoordinates oneFixedSection a

/-- These parameters exhaust the literal native second-cohomology fixed submodule. -/
theorem coordinateTorusH2FixedSection_range :
    LinearMap.range coordinateTorusH2FixedSection =
      singularCohomologyFixed (torusMatrixMap M₀) 2 := by
  ext a
  rw [mem_singularCohomologyFixed_iff, coordinateTorusH2_pullback_fixed_iff_mem_range]
  exact mem_range_equiv_symm_comp coordinateTorusH2CohomologyCoordinates twoFixedSection a

/-- These parameters exhaust the literal native third-cohomology fixed submodule. -/
theorem coordinateTorusH3FixedSection_range :
    LinearMap.range coordinateTorusH3FixedSection =
      singularCohomologyFixed (torusMatrixMap M₀) 3 := by
  ext a
  rw [mem_singularCohomologyFixed_iff, coordinateTorusH3_pullback_fixed_iff_mem_range]
  exact mem_range_equiv_symm_comp coordinateTorusH3CohomologyCoordinates threeFixedSection a

end Wikipedia.HopfProblem.CuspCentralCohomology
