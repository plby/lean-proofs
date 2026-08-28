import Wikipedia.HopfProblem.ThreefoldHomologyCapEliminationSource
import Wikipedia.HopfProblem.ThreefoldHomologyCuspKernel
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWang
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTop

/-!
# Genuine cap-kernel classes in the existing integral markings

The elliptic classes are the inverses of the already constructed native
cap-kernel coordinate equivalences.  At the cusp, an actual invariant
torus class has a unique native cap-kernel preimage under the proved
Wang equivalence.  These constructions provide original boundary
classes, not just vectors satisfying a proposed matrix equation.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.CapElimination

open SingularMayerVietoris ThreefoldOverlapMappingTorus MappingTorusHomology
open PeriodTorusHigherHomology PeriodTorusHigherHomologyExterior TrianglePeriodFamily
open TrianglePeriodFamily.Homology
open TrianglePeriodFamily.Boundary.EllipticCapProduct
open TrianglePeriodFamily.Boundary.EllipticCapKernelWang
open Elliptic Elliptic.HigherHomology SpecialPeriods.EllipticFilling
open ThreefoldHomologyCuspFibre

/-- A degree-two native elliptic cap-kernel class in the original surface `H₁` coordinates. -/
def ellipticOneClass (j : Kind) (a : Fin 2 → ℤ) : NativeCapKernel (some j) 2 :=
  (boundaryCapKernelEquiv j 1).symm
    ((surfaceH1Equiv j (specialLocalData j).centralPeriod).symm a)

/-- Its Wang coordinate is the proved original affine-cover formula, with its actual shear. -/
theorem ellipticOneClass_wang (j : Kind) (a : Fin 2 → ℤ) :
    FlatTorus.singularH1Equiv (wangBoundary (monodromy (some j)) 1 (ellipticOneClass j a).val) =
      a 1 • j.twist + ((fibreNormIndex j : ℤ) * a 0 - h1ShearCorrection j * a 1) •
        deltaVector := by
  have h := capKernel_wang_h1_coordinates j
    ((surfaceH1Equiv j (specialLocalData j).centralPeriod).symm a)
  simpa only [LinearEquiv.apply_symm_apply, ellipticOneClass] using! h

/-- A degree-four native elliptic kernel class in the unchanged original surface `H₃` marking. -/
def ellipticThreeClass (j : Kind) (a : Fin 2 → ℤ) : NativeCapKernel (some j) 4 :=
  (boundaryCapH4KernelEquiv j).symm a

/-- The full actual exterior-cube column, retaining the genuine old-marking shear. -/
theorem ellipticThreeClass_wang (j : Kind) (a : Fin 2 → ℤ) :
    FlatTorus.singularH3Coordinates
      (wangBoundary (monodromy (some j)) 3 (ellipticThreeClass j a).val) =
      topWangMatrix j (sourceShearThree j) *ᵥ a :=
  capKernelWangH4Coordinates_symm j a

/-- The native cusp monodromy has exactly the original exterior-cube matrix. -/
theorem cuspMonodromy_three_coordinates (a : SingularHomology RealTorus₄ 3) :
    FlatTorus.singularH3Coordinates (monodromyHomologyMap (monodromy none) 3 a) =
      cubeM₀ *ᵥ FlatTorus.singularH3Coordinates a := by
  have h := LinearMap.congr_fun
    (TrianglePeriodFamily.Boundary.Cusp.monodromyHomology_triangle 3) a
  have h' : monodromyHomologyMap (monodromy none) 3 a =
      triangleHomologyEquiv triangleCuspGenerator 3 a := h
  rw [h']
  change FlatTorus.singularH3Coordinates
    (singularHomologyMap (triangleTorusHomeomorph triangleCuspGenerator :
      C(RealTorus₄, RealTorus₄)) 3 a) = _
  rw [FlatTorus.singularH3Coordinates_inducedHomology_triangle,
    triangleDualRepresentation_cusp_matrix]
  rfl

/-- A literal cusp-invariant lattice vector defines an actual degree-one Wang invariant. -/
def cuspOneInvariant (v : Lattice) (hv : M₀ *ᵥ v = v) :
    LinearMap.ker (wangDifference (monodromy none) 1) :=
  ⟨FlatTorus.singularH1Equiv.symm v, by
    apply FlatTorus.singularH1Equiv.injective
    change FlatTorus.singularH1Equiv
      (FlatTorus.singularH1Equiv.symm v -
        monodromyHomologyMap (monodromy none) 1 (FlatTorus.singularH1Equiv.symm v)) = _
    rw [map_sub, BoundaryFirst.boundaryMonodromy_one_coordinates,
      LinearEquiv.apply_symm_apply, map_zero]
    exact sub_eq_zero.mpr hv.symm⟩

/-- A literal exterior-cube invariant defines an actual degree-three Wang invariant. -/
def cuspThreeInvariant (v : Lattice) (hv : cubeM₀ *ᵥ v = v) :
    LinearMap.ker (wangDifference (monodromy none) 3) :=
  ⟨FlatTorus.singularH3Coordinates.symm v, by
    apply FlatTorus.singularH3Coordinates.injective
    change FlatTorus.singularH3Coordinates
      (FlatTorus.singularH3Coordinates.symm v -
        monodromyHomologyMap (monodromy none) 3 (FlatTorus.singularH3Coordinates.symm v)) = _
    rw [map_sub, cuspMonodromy_three_coordinates, LinearEquiv.apply_symm_apply, map_zero]
    exact sub_eq_zero.mpr hv.symm⟩

/-- The unique original cusp cap-kernel class with the specified actual degree-one Wang vector. -/
def cuspOneClass (v : Lattice) (hv : M₀ *ᵥ v = v) : NativeCapKernel none 2 :=
  (cuspCapKernelWangEquivDegree 1).symm (cuspOneInvariant v hv)

@[simp] theorem cuspOneClass_wang (v : Lattice) (hv : M₀ *ᵥ v = v) :
    FlatTorus.singularH1Equiv (wangBoundary (monodromy none) 1 (cuspOneClass v hv).val) = v := by
  change FlatTorus.singularH1Equiv
    (wangBoundary (monodromy none) 1
      ((cuspCapKernelWangEquivDegree 1).symm (cuspOneInvariant v hv)).val) = v
  rw [cuspCapKernelWangEquivDegree_symm_wang]
  exact LinearEquiv.apply_symm_apply _ _

/-- The corresponding unique original cusp cap-kernel class in degree four. -/
def cuspThreeClass (v : Lattice) (hv : cubeM₀ *ᵥ v = v) : NativeCapKernel none 4 :=
  (cuspCapKernelWangEquivDegree 3).symm (cuspThreeInvariant v hv)

@[simp] theorem cuspThreeClass_wang (v : Lattice) (hv : cubeM₀ *ᵥ v = v) :
    FlatTorus.singularH3Coordinates
      (wangBoundary (monodromy none) 3 (cuspThreeClass v hv).val) = v := by
  change FlatTorus.singularH3Coordinates
    (wangBoundary (monodromy none) 3
      ((cuspCapKernelWangEquivDegree 3).symm (cuspThreeInvariant v hv)).val) = v
  rw [cuspCapKernelWangEquivDegree_symm_wang]
  exact LinearEquiv.apply_symm_apply _ _

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.CapElimination
