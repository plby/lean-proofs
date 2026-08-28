import Wikipedia.HopfProblem.ThreefoldHomologyCapElimination
import Wikipedia.HopfProblem.ThreefoldHomologyFourthWangSource
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspWang
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyDifferenceLowCoordinates
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyDifferenceCoordinates

/-!
# Source coordinates of the actual native cap-kernel relation map

Compose the genuine regular coefficient with the genuine source-kernel
projection.  Its two coordinates are the original signed Wang columns.
The actual cusp word replaces the inverse first-generator action by the
second-generator action on its genuine Wang class.  The resulting
degree-one and degree-three formulas use the original integral lattice
and exterior-cube matrices, not a selected abstract kernel basis.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.CapElimination

open SingularMayerVietoris ThreefoldOverlapMappingTorus MappingTorusHomology
open PeriodTorusHigherHomology TrianglePeriodFamily
open TrianglePeriodFamily.Homology
  (sourceKernelProjection sourceDifference generatorHomologyEquiv triangleHomologyEquiv)
open TrianglePeriodFamily.HomologyDifference

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The original source-kernel projection of the actual native regular relation map. -/
def nativeCapKernelSourceMap (n : ℕ) :
    (∀ i : Puncture, NativeCapKernel i (n + 1)) →ₗ[ℤ] LinearMap.ker (sourceDifference n) :=
  intLinearMapOfAddHom
    { toFun a := sourceKernelProjection Dsp n (nativeCapKernelRegularMap (n + 1) a)
      map_zero' := by rw [map_zero, map_zero]
      map_add' a b := by rw [map_add, map_add] }

@[simp] theorem nativeCapKernelSourceMap_apply (n : ℕ)
    (a : ∀ i : Puncture, NativeCapKernel i (n + 1)) :
    nativeCapKernelSourceMap n a =
      sourceKernelProjection Dsp n (nativeCapKernelRegularMap (n + 1) a) := rfl

/-- The genuine Wang class of a native cap-kernel component. -/
def nativeCapKernelWangValue (n : ℕ)
    (a : ∀ i : Puncture, NativeCapKernel i (n + 1)) (i : Puncture) :
    SingularHomology RealTorus₄ n :=
  wangBoundary (monodromy i) n (a i).val

/-- Both actual source columns, before simplifying the cusp word. -/
theorem nativeCapKernelSourceMap_val (n : ℕ)
    (a : ∀ i : Puncture, NativeCapKernel i (n + 1)) :
    (nativeCapKernelSourceMap n a).val =
      (nativeCapKernelWangValue n a (some .three) -
          triangleHomologyEquiv triangleGenerator₁⁻¹ n (nativeCapKernelWangValue n a none),
        nativeCapKernelWangValue n a (some .four) - nativeCapKernelWangValue n a none) := by
  classical
  change FourthWang.regularSourcePair n (nativeCapKernelRegularMap (n + 1) a) = _
  rw [nativeCapKernelRegularMap_apply, map_sum]
  simp only [FourthWang.regularSourcePair_boundary]
  rw [Fintype.sum_option]
  have hu : (Finset.univ : Finset Elliptic.Kind) = {.three, .four} := by
    ext j
    cases j <;> simp
  rw [hu, Finset.sum_pair (by decide : Elliptic.Kind.three ≠ .four)]
  simp only [FourthWang.sourceColumn, nativeCapKernelWangValue, Prod.mk_add_mk,
    add_zero, zero_add, sub_eq_add_neg]
  exact Prod.ext (add_comm _ _) (add_comm _ _)

/-- The literal cusp relation identifies the remaining inverse action on this actual Wang class. -/
theorem nativeCapKernelWangValue_first_inv (n : ℕ)
    (a : ∀ i : Puncture, NativeCapKernel i (n + 1)) :
    triangleHomologyEquiv triangleGenerator₁⁻¹ n (nativeCapKernelWangValue n a none) =
      generatorHomologyEquiv true n (nativeCapKernelWangValue n a none) := by
  have h := congrArg (generatorHomologyEquiv true n)
    (TrianglePeriodFamily.Boundary.Cusp.wangBoundary_inverse_word n (a none).val)
  simpa only [LinearEquiv.apply_symm_apply, nativeCapKernelWangValue] using! h

/-- An equivalent source formula using the original second-generator action. -/
theorem nativeCapKernelSourceMap_val_second (n : ℕ)
    (a : ∀ i : Puncture, NativeCapKernel i (n + 1)) :
    (nativeCapKernelSourceMap n a).val =
      (nativeCapKernelWangValue n a (some .three) -
          generatorHomologyEquiv true n (nativeCapKernelWangValue n a none),
        nativeCapKernelWangValue n a (some .four) - nativeCapKernelWangValue n a none) := by
  rw [nativeCapKernelSourceMap_val, nativeCapKernelWangValue_first_inv]

/-- The original integral degree-one coordinates of the actual source map. -/
theorem nativeCapKernelSourceMap_one_coordinates
    (a : ∀ i : Puncture, NativeCapKernel i 2) :
    (FlatTorus.singularH1Equiv (nativeCapKernelSourceMap 1 a).val.1,
      FlatTorus.singularH1Equiv (nativeCapKernelSourceMap 1 a).val.2) =
      (FlatTorus.singularH1Equiv (nativeCapKernelWangValue 1 a (some .three)) -
          A₂ *ᵥ FlatTorus.singularH1Equiv (nativeCapKernelWangValue 1 a none),
        FlatTorus.singularH1Equiv (nativeCapKernelWangValue 1 a (some .four)) -
          FlatTorus.singularH1Equiv (nativeCapKernelWangValue 1 a none)) := by
  rw [nativeCapKernelSourceMap_val_second]
  simp only [map_sub, generatorHomologyOne_true_coordinates]

/-- The original ordered exterior-cube coordinates of the same genuine map. -/
theorem nativeCapKernelSourceMap_three_coordinates
    (a : ∀ i : Puncture, NativeCapKernel i 4) :
    (FlatTorus.singularH3Coordinates (nativeCapKernelSourceMap 3 a).val.1,
      FlatTorus.singularH3Coordinates (nativeCapKernelSourceMap 3 a).val.2) =
      (FlatTorus.singularH3Coordinates (nativeCapKernelWangValue 3 a (some .three)) -
          PeriodTorusHigherHomologyExterior.cubeA₂ *ᵥ
            FlatTorus.singularH3Coordinates (nativeCapKernelWangValue 3 a none),
        FlatTorus.singularH3Coordinates (nativeCapKernelWangValue 3 a (some .four)) -
          FlatTorus.singularH3Coordinates (nativeCapKernelWangValue 3 a none)) := by
  rw [nativeCapKernelSourceMap_val_second]
  simp only [map_sub, generatorHomologyThree_coordinates, if_true]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.CapElimination
