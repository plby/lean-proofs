import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologySourceSequence
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologySplitting

/-!
# Splitting the actual regular-family homology extension

Once the right endpoint is proved free, projectivity supplies a linear
section of the actual connecting projection. The resulting integral
equivalence preserves the original positive fibre inclusion and the
original source-oriented connecting map. The section is not assumed and
no extra topological comparison enters this construction.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SpecialPeriods SingularMayerVietoris TrianglePeriodFamilyHomologySplitting

variable (D : Data ℂ TriangleRegularPoint) (n : ℕ)

/-- The actual family extension splits integrally whenever its proved kernel module is free. -/
def familyHomologySplitEquiv [Module.Free ℤ (LinearMap.ker (sourceDifference n))] :
    SingularHomology D.Space (n + 1) ≃ₗ[ℤ]
      ((SingularHomology RealTorus₄ (n + 1) ⧸ LinearMap.range (sourceDifference (n + 1))) ×
        LinearMap.ker (sourceDifference n)) :=
  freeRightSplitEquiv (sourceCoinvariantInclusion D (n + 1)) (sourceKernelProjection D n)
    (sourceCoinvariantInclusion_kernelProjection_exact D n)
    (sourceCoinvariantInclusion_injective D (n + 1)) (sourceKernelProjection_surjective D n)

@[simp] theorem familyHomologySplitEquiv_inclusion
    [Module.Free ℤ (LinearMap.ker (sourceDifference n))]
    (a : SingularHomology RealTorus₄ (n + 1) ⧸ LinearMap.range (sourceDifference (n + 1))) :
    familyHomologySplitEquiv D n (sourceCoinvariantInclusion D (n + 1) a) = (a, 0) :=
  freeRightSplitEquiv_inclusion _ _ _ _ _ a

/-- The literal fibre class becomes its coinvariant class in the first summand. -/
@[simp] theorem familyHomologySplitEquiv_fibre
    [Module.Free ℤ (LinearMap.ker (sourceDifference n))]
    (a : SingularHomology RealTorus₄ (n + 1)) :
    familyHomologySplitEquiv D n
      (singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift) (n + 1) a) =
      (Submodule.Quotient.mk a, 0) := by
  rw [← sourceCoinvariantInclusion_mk, familyHomologySplitEquiv_inclusion]

/-- The second summand retains the actual source-oriented connecting projection. -/
@[simp] theorem familyHomologySplitEquiv_snd
    [Module.Free ℤ (LinearMap.ker (sourceDifference n))]
    (a : SingularHomology D.Space (n + 1)) :
    (familyHomologySplitEquiv D n a).2 = sourceKernelProjection D n a :=
  freeRightSplitEquiv_snd _ _ _ _ _ a

variable {L K : Type*} [AddCommGroup L] [AddCommGroup K] [Module ℤ K]
  (ec : (SingularHomology RealTorus₄ (n + 1) ⧸
    LinearMap.range (sourceDifference (n + 1))) ≃+ L)
  (ek : LinearMap.ker (sourceDifference n) ≃+ K) [Module.Free ℤ K]

/-- Marking both actual endpoints gives an integral marking of the actual middle group. -/
def familyHomologyMarkedEquiv : SingularHomology D.Space (n + 1) ≃ₗ[ℤ] (L × K) := by
  letI := Module.Free.of_equiv ek.toIntLinearEquiv.symm
  exact ((familyHomologySplitEquiv D n).toAddEquiv.trans
    (ec.prodCongr ek)).toIntLinearEquiv

/-- The marked splitting retains every actual fibre-inclusion class. -/
@[simp] theorem familyHomologyMarkedEquiv_fibre
    (a : SingularHomology RealTorus₄ (n + 1)) :
    familyHomologyMarkedEquiv D n ec ek
      (singularHomologyMap (familyFibreInclusion D normalizedSlitBaseLift) (n + 1) a) =
      (ec (Submodule.Quotient.mk a), 0) := by
  let := Module.Free.of_equiv ek.toIntLinearEquiv.symm
  change (ec ((familyHomologySplitEquiv D n) _).1,
    ek ((familyHomologySplitEquiv D n) _).2) = _
  rw [familyHomologySplitEquiv_fibre]
  simp only [map_zero]

/-- The marked second coordinate is the actual connecting projection in the kernel marking. -/
@[simp] theorem familyHomologyMarkedEquiv_snd
    (a : SingularHomology D.Space (n + 1)) :
    (familyHomologyMarkedEquiv D n ec ek a).2 = ek (sourceKernelProjection D n a) := by
  let := Module.Free.of_equiv ek.toIntLinearEquiv.symm
  change ek ((familyHomologySplitEquiv D n a).2) = _
  rw [familyHomologySplitEquiv_snd]

/-- Its inverse on the first summand is the original positive coinvariant inclusion. -/
@[simp] theorem familyHomologyMarkedEquiv_symm_inl (a : L) :
    (familyHomologyMarkedEquiv D n ec ek).symm (a, 0) =
      sourceCoinvariantInclusion D (n + 1) (ec.symm a) := by
  apply (familyHomologyMarkedEquiv D n ec ek).injective
  rw [LinearEquiv.apply_symm_apply]
  let := Module.Free.of_equiv ek.toIntLinearEquiv.symm
  change (a, 0) = (ec ((familyHomologySplitEquiv D n) _).1,
    ek ((familyHomologySplitEquiv D n) _).2)
  rw [familyHomologySplitEquiv_inclusion]
  simp only [AddEquiv.apply_symm_apply, map_zero]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
