import Wikipedia.HopfProblem.ThreefoldHomologyBoundaryFirstMonodromy
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusHomology
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologySplitting
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyFreeCoordinates

/-!
# First integral homology of the three actual boundaries

The genuine Wang sequence has the proved endpoints `ℤ²` and `ℤ`.
Projectivity of the latter supplies a section of the actual Wang map;
it is not a splitting hypothesis.  Each literal mapping-torus boundary
therefore has actual singular first homology `ℤ³`, with no torsion.

The two first coordinates retain the actual fibre coinvariants.  The
last coordinate is the genuine signed Wang boundary, measured by the
positive degree-zero augmentation.  The actual overlap homotopy
equivalences transport these conclusions to the original intersections.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.BoundaryFirst

open SingularMayerVietoris PeriodTorusHigherHomology MappingTorusHomology
open ThreefoldOverlapMappingTorus TrianglePeriodFamily
open TrianglePeriodFamilyHomologySplitting TrianglePeriodFamilyHomologyFreeCoordinates

/-- The actual first Wang extension splits because its actual right endpoint is free. -/
def boundaryH1SplitEquiv (i : Puncture) :
    SingularHomology (Boundary i) 1 ≃ₗ[ℤ]
      ((SingularHomology RealTorus₄ 1 ⧸ LinearMap.range (wangDifference (monodromy i) 1)) ×
        LinearMap.ker (wangDifference (monodromy i) 0)) := by
  letI := Module.Free.of_equiv (boundaryKernelZeroEquiv i).toAddEquiv.symm.toIntLinearEquiv
  exact freeRightSplitEquiv (cokernelInclusion (monodromy i) 1)
    (kernelBoundary (monodromy i) 0)
    (LinearMap.exact_iff.mpr
      (cokernelInclusion_range_eq_ker_kernelBoundary (monodromy i) 0).symm)
    (cokernelInclusion_injective (monodromy i) 1)
    (kernelBoundary_surjective (monodromy i) 0)

/-- The positive fibre inclusion is the first summand of the genuine Wang extension. -/
@[simp] theorem boundaryH1SplitEquiv_fibre (i : Puncture)
    (a : SingularHomology RealTorus₄ 1) :
    boundaryH1SplitEquiv i (fibreHomologyMap (monodromy i) 1 a) =
      (Submodule.Quotient.mk a, 0) := by
  let := Module.Free.of_equiv (boundaryKernelZeroEquiv i).toAddEquiv.symm.toIntLinearEquiv
  exact freeRightSplitEquiv_inclusion (cokernelInclusion (monodromy i) 1)
    (kernelBoundary (monodromy i) 0)
    (LinearMap.exact_iff.mpr
      (cokernelInclusion_range_eq_ker_kernelBoundary (monodromy i) 0).symm)
    (cokernelInclusion_injective (monodromy i) 1)
    (kernelBoundary_surjective (monodromy i) 0) (Submodule.Quotient.mk a)

/-- The second summand of the splitting is the original kernel-valued Wang boundary. -/
@[simp] theorem boundaryH1SplitEquiv_snd (i : Puncture)
    (a : SingularHomology (Boundary i) 1) :
    (boundaryH1SplitEquiv i a).2 = kernelBoundary (monodromy i) 0 a := by
  let := Module.Free.of_equiv (boundaryKernelZeroEquiv i).toAddEquiv.symm.toIntLinearEquiv
  exact freeRightSplitEquiv_snd (cokernelInclusion (monodromy i) 1)
    (kernelBoundary (monodromy i) 0)
    (LinearMap.exact_iff.mpr
      (cokernelInclusion_range_eq_ker_kernelBoundary (monodromy i) 0).symm)
    (cokernelInclusion_injective (monodromy i) 1)
    (kernelBoundary_surjective (monodromy i) 0) a

/-- The proved integral endpoint coordinates mark the actual first homology. -/
def boundaryH1ProductEquiv (i : Puncture) :
    SingularHomology (Boundary i) 1 ≃ₗ[ℤ] ((Fin 2 → ℤ) × ℤ) :=
  ((boundaryH1SplitEquiv i).toAddEquiv.trans
    ((boundaryCokernelOneEquiv i).toAddEquiv.prodCongr
      (boundaryKernelZeroEquiv i).toAddEquiv)).toIntLinearEquiv

/-- Fibre classes retain exactly their two primitive integral coinvariant coordinates. -/
@[simp] theorem boundaryH1ProductEquiv_fibre (i : Puncture)
    (a : SingularHomology RealTorus₄ 1) :
    boundaryH1ProductEquiv i (fibreHomologyMap (monodromy i) 1 a) =
      (latticeCoinvariantMap i (FlatTorus.singularH1Equiv a), 0) := by
  change (boundaryCokernelOneEquiv i
      ((boundaryH1SplitEquiv i) (fibreHomologyMap (monodromy i) 1 a)).1,
    boundaryKernelZeroEquiv i
      ((boundaryH1SplitEquiv i) (fibreHomologyMap (monodromy i) 1 a)).2) = _
  rw [boundaryH1SplitEquiv_fibre, boundaryCokernelOneEquiv_mk]
  simp only [map_zero]

/-- The last marked coordinate is the actual signed Wang map, not a chosen projection. -/
@[simp] theorem boundaryH1ProductEquiv_snd (i : Puncture)
    (a : SingularHomology (Boundary i) 1) :
    (boundaryH1ProductEquiv i a).2 =
      connectedHomologyZeroEquiv RealTorus₄ (wangBoundary (monodromy i) 0 a) := by
  change boundaryKernelZeroEquiv i (boundaryH1SplitEquiv i a).2 = _
  rw [boundaryH1SplitEquiv_snd]
  rfl

/-- Ordered coordinates with the two fibre coordinates before the Wang coordinate. -/
def twoFibreOneBaseEquiv : ((Fin 2 → ℤ) × ℤ) ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  (((AddEquiv.refl (Fin 2 → ℤ)).prodCongr
    (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm.toAddEquiv).trans
      (freeCoordinateSumEquiv 2 1).toAddEquiv).toIntLinearEquiv

@[simp] theorem twoFibreOneBaseEquiv_apply (x : (Fin 2 → ℤ) × ℤ) :
    twoFibreOneBaseEquiv x = ![x.1 0, x.1 1, x.2] := by
  ext k
  fin_cases k <;> rfl

/-- Each actual boundary has free integral first homology of rank three. -/
def boundaryH1Equiv (i : Puncture) :
    SingularHomology (Boundary i) 1 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  (boundaryH1ProductEquiv i).trans twoFibreOneBaseEquiv

/-- The actual fibre map in the three integral coordinates. -/
@[simp] theorem boundaryH1Equiv_fibre (i : Puncture)
    (a : SingularHomology RealTorus₄ 1) :
    boundaryH1Equiv i (fibreHomologyMap (monodromy i) 1 a) =
      ![latticeCoinvariantMap i (FlatTorus.singularH1Equiv a) 0,
        latticeCoinvariantMap i (FlatTorus.singularH1Equiv a) 1, 0] := by
  change twoFibreOneBaseEquiv
    (boundaryH1ProductEquiv i (fibreHomologyMap (monodromy i) 1 a)) = _
  rw [boundaryH1ProductEquiv_fibre, twoFibreOneBaseEquiv_apply]

/-- The third coordinate is the literal signed Wang boundary in its positive point marking. -/
@[simp] theorem boundaryH1Equiv_boundary (i : Puncture)
    (a : SingularHomology (Boundary i) 1) :
    boundaryH1Equiv i a 2 =
      connectedHomologyZeroEquiv RealTorus₄ (wangBoundary (monodromy i) 0 a) := by
  change (boundaryH1ProductEquiv i a).2 = _
  exact boundaryH1ProductEquiv_snd i a

theorem boundaryH1_free (i : Puncture) : Module.Free ℤ (SingularHomology (Boundary i) 1) :=
  Module.Free.of_equiv (boundaryH1Equiv i).symm

theorem boundaryH1_finite (i : Puncture) : Module.Finite ℤ (SingularHomology (Boundary i) 1) :=
  Module.Finite.of_surjective (boundaryH1Equiv i).symm.toLinearMap
    (boundaryH1Equiv i).symm.surjective

theorem boundaryH1_torsionFree (i : Puncture) :
    Module.IsTorsionFree ℤ (SingularHomology (Boundary i) 1) := by
  have := boundaryH1_free i
  infer_instance

theorem boundaryH1_finrank (i : Puncture) :
    Module.finrank ℤ (SingularHomology (Boundary i) 1) = 3 := by
  rw [(boundaryH1Equiv i).finrank_eq]
  simp

/-- The actual overlap comparison carries the original intersection's first homology to `ℤ³`. -/
def overlapH1Equiv (i : Puncture) :
    SingularHomology (RegularOverlap i) 1 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  (overlapHomologyEquiv i 1).trans (boundaryH1Equiv i)

theorem overlapH1_free (i : Puncture) :
    Module.Free ℤ (SingularHomology (RegularOverlap i) 1) :=
  Module.Free.of_equiv (overlapH1Equiv i).symm

theorem overlapH1_finite (i : Puncture) :
    Module.Finite ℤ (SingularHomology (RegularOverlap i) 1) :=
  Module.Finite.of_surjective (overlapH1Equiv i).symm.toLinearMap
    (overlapH1Equiv i).symm.surjective

theorem overlapH1_torsionFree (i : Puncture) :
    Module.IsTorsionFree ℤ (SingularHomology (RegularOverlap i) 1) := by
  have := overlapH1_free i
  infer_instance

theorem overlapH1_finrank (i : Puncture) :
    Module.finrank ℤ (SingularHomology (RegularOverlap i) 1) = 3 := by
  rw [(overlapH1Equiv i).finrank_eq]
  simp

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.BoundaryFirst
