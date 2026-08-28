import Wikipedia.HopfProblem.ThreefoldHomologyBoundaryFirstLattice
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusSpaces
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticTailHomology
import Wikipedia.HopfProblem.TrianglePeriodFamilyTransportTorus
import Wikipedia.HopfProblem.SpecialPeriodsCuspGlobalOverlapMonodromy
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyDifferenceEquiv
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePointClass

/-!
# Actual degree-one Wang endpoints for the three boundaries

The literal affine elliptic monodromies and clockwise cusp monodromy
act on actual singular first homology by their original integral column
matrices.  The genuine period-loop marking transports the actual Wang
cokernels to the computed integral coinvariant lattices.  In degree zero,
naturality of augmentation identifies the actual invariant group with `ℤ`.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.BoundaryFirst

open SingularMayerVietoris PeriodTorusHigherHomology MappingTorusHomology
open ThreefoldOverlapMappingTorus TrianglePeriodFamily TrianglePeriodFamily.HomologyDifference

/-- The actual boundary monodromy has the source's integral matrix in
the genuine singular first-homology period marking. -/
theorem boundaryMonodromy_one_coordinates (i : Puncture)
    (a : SingularHomology RealTorus₄ 1) :
    FlatTorus.singularH1Equiv (monodromyHomologyMap (monodromy i) 1 a) =
      latticeMonodromy i *ᵥ FlatTorus.singularH1Equiv a := by
  cases i with
  | none =>
    change FlatTorus.singularH1Equiv
      (singularHomologyMap (CuspFamily.cuspTorusHomeomorph 1 :
        C(RealTorus₄, RealTorus₄)) 1 a) = M₀ *ᵥ FlatTorus.singularH1Equiv a
    rw [← triangleTorusHomeomorph_cusp_zpow 1]
    change FlatTorus.singularH1Equiv
      (FirstHurewicz.inducedHomology
        (triangleTorusHomeomorph (triangleCuspGenerator ^ (1 : ℤ)) :
          C(RealTorus₄, RealTorus₄)) a) = _
    rw [FlatTorus.singularH1Equiv_inducedHomology_triangle,
      triangleDualRepresentation_cusp_zpow_matrix, CuspFamily.cuspIntegralMatrix_one]
  | some j =>
    change FlatTorus.singularH1Equiv
      (singularHomologyMap (Elliptic.flatTorusAffine j j.twist :
        C(RealTorus₄, RealTorus₄)) 1 a) = j.matrix *ᵥ FlatTorus.singularH1Equiv a
    rw [TrianglePeriodFamily.Boundary.flatTorusAffine_homology_triangle]
    change FlatTorus.singularH1Equiv
      (FirstHurewicz.inducedHomology
        (triangleTorusHomeomorph (Triangle.ellipticGenerator j) :
          C(RealTorus₄, RealTorus₄)) a) = _
    rw [FlatTorus.singularH1Equiv_inducedHomology_triangle]
    cases j
    · rw [Triangle.ellipticGenerator, triangleDualRepresentation_generator₁_matrix]
      rfl
    · rw [Triangle.ellipticGenerator, triangleDualRepresentation_generator₂_matrix]
      rfl

/-- The literal Wang differential has precisely the signed integral matrix
used in the preceding coinvariant computation. -/
theorem boundaryWangDifference_one_coordinates (i : Puncture)
    (a : SingularHomology RealTorus₄ 1) :
    FlatTorus.singularH1Equiv (wangDifference (monodromy i) 1 a) =
      latticeDifference i (FlatTorus.singularH1Equiv a) := by
  change FlatTorus.singularH1Equiv
    (a - monodromyHomologyMap (monodromy i) 1 a) = _
  rw [map_sub, boundaryMonodromy_one_coordinates, latticeDifference_apply]

private def boundaryCokernelOneCoordinatesAddEquiv (i : Puncture) :
    (SingularHomology RealTorus₄ 1 ⧸ LinearMap.range (wangDifference (monodromy i) 1))
      ≃+ (Lattice ⧸ LinearMap.range (latticeDifference i)) := by
  letI := Submodule.Quotient.module (LinearMap.range (wangDifference (monodromy i) 1))
  letI := Submodule.Quotient.module (LinearMap.range (latticeDifference i))
  exact (cokernelEquivOfCommuting (wangDifference (monodromy i) 1) (latticeDifference i)
    FlatTorus.singularH1Equiv FlatTorus.singularH1Equiv
    (boundaryWangDifference_one_coordinates i)).toAddEquiv

/-- The actual quotient by the actual degree-one Wang differential,
transported by the genuine period-loop marking, with its native integer action. -/
def boundaryCokernelOneCoordinates (i : Puncture) :
    (SingularHomology RealTorus₄ 1 ⧸ LinearMap.range (wangDifference (monodromy i) 1))
      ≃ₗ[ℤ] (Lattice ⧸ LinearMap.range (latticeDifference i)) :=
  (boundaryCokernelOneCoordinatesAddEquiv i).toIntLinearEquiv

@[simp] theorem boundaryCokernelOneCoordinates_mk (i : Puncture)
    (a : SingularHomology RealTorus₄ 1) :
    boundaryCokernelOneCoordinates i (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (FlatTorus.singularH1Equiv a) := rfl

private def latticeCokernelAddEquiv (i : Puncture) :
    (Lattice ⧸ LinearMap.range (latticeDifference i)) ≃+ (Fin 2 → ℤ) := by
  letI := Submodule.Quotient.module (LinearMap.range (latticeDifference i))
  exact (latticeCokernelEquiv i).toAddEquiv

/-- Every actual first Wang cokernel is `ℤ²`, with no torsion. -/
def boundaryCokernelOneEquiv (i : Puncture) :
    (SingularHomology RealTorus₄ 1 ⧸ LinearMap.range (wangDifference (monodromy i) 1))
      ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((boundaryCokernelOneCoordinates i).toAddEquiv.trans
    (latticeCokernelAddEquiv i)).toIntLinearEquiv

/-- The actual first Wang quotient keeps the primitive lattice coordinates. -/
@[simp] theorem boundaryCokernelOneEquiv_mk (i : Puncture)
    (a : SingularHomology RealTorus₄ 1) :
    boundaryCokernelOneEquiv i (Submodule.Quotient.mk a) =
      latticeCoinvariantMap i (FlatTorus.singularH1Equiv a) := rfl

/-- Every actual boundary monodromy fixes the positive augmentation class. -/
theorem boundaryMonodromy_zero_identity (i : Puncture) :
    monodromyHomologyMap (monodromy i) 0 = LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply (connectedHomologyZeroEquiv RealTorus₄).injective
  exact connectedHomologyZeroEquiv_natural (monodromy i : C(RealTorus₄, RealTorus₄)) a

/-- The genuine degree-zero Wang differential vanishes. -/
theorem boundaryWangDifference_zero (i : Puncture) :
    wangDifference (monodromy i) 0 = 0 := by
  apply LinearMap.ext
  intro a
  change a - monodromyHomologyMap (monodromy i) 0 a = 0
  rw [boundaryMonodromy_zero_identity, LinearMap.id_apply, sub_self]

/-- The genuine degree-zero invariant group, marked by positive augmentation. -/
def boundaryKernelZeroEquiv (i : Puncture) :
    LinearMap.ker (wangDifference (monodromy i) 0) ≃ₗ[ℤ] ℤ :=
  ({ toFun a := connectedHomologyZeroEquiv RealTorus₄ a.val
     invFun z := ⟨(connectedHomologyZeroEquiv RealTorus₄).symm z, by
       rw [boundaryWangDifference_zero, LinearMap.ker_zero]
       trivial⟩
     left_inv a := Subtype.ext ((connectedHomologyZeroEquiv RealTorus₄).symm_apply_apply a.val)
     right_inv z := (connectedHomologyZeroEquiv RealTorus₄).apply_symm_apply z
     map_add' a b := (connectedHomologyZeroEquiv RealTorus₄).map_add a.val b.val
   } : LinearMap.ker (wangDifference (monodromy i) 0) ≃+ ℤ).toIntLinearEquiv

@[simp] theorem boundaryKernelZeroEquiv_apply (i : Puncture)
    (a : LinearMap.ker (wangDifference (monodromy i) 0)) :
    boundaryKernelZeroEquiv i a = connectedHomologyZeroEquiv RealTorus₄ a.val := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.BoundaryFirst
