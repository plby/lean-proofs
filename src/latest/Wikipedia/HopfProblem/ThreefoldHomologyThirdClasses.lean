import Wikipedia.HopfProblem.ThreefoldHomologyCapEliminationClasses
import Wikipedia.HopfProblem.ThreefoldHomologyThirdSourceLatticeKernel

/-!
# Native third-degree cap-kernel classes and their actual Wang values

The elliptic classes use the original surface second-homology markings.
The cusp class is the unique genuine cap-kernel class with its specified
actual invariant.  The common reference tuple has zero actual source
projection; no value of its remaining regular fibre coefficient is
asserted here.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.ThirdDegree

open SingularMayerVietoris ThreefoldOverlapMappingTorus MappingTorusHomology
open PeriodTorusHigherHomology PeriodTorusHigherHomologyExterior TrianglePeriodFamily
open TrianglePeriodFamily.Homology TrianglePeriodFamily.HomologyDifference
open TrianglePeriodFamily.Boundary.EllipticCapProduct
open TrianglePeriodFamily.Boundary.EllipticCapKernelWang
open Elliptic Elliptic.HigherHomology SpecialPeriods.EllipticFilling
open ThreefoldHomologyCuspFibre CapElimination

/-- An actual elliptic cap-kernel class in the unchanged surface second-homology marking. -/
def ellipticTwoClass (j : Kind) (a : Fin 2 → ℤ) : NativeCapKernel (some j) 3 :=
  (boundaryCapKernelEquiv j 2).symm
    ((surfaceH2Equiv j (specialLocalData j).centralPeriod).symm a)

/-- Its actual Wang vector, including the genuine covering shear. -/
theorem ellipticTwoClass_wang (j : Kind) (a : Fin 2 → ℤ) :
    FlatTorus.singularH2Coordinates
      (wangBoundary (monodromy (some j)) 2 (ellipticTwoClass j a).val) =
      ((fibreNormIndex j : ℤ) * a 0 - sourceShearTwo j * a 1) •
        fibreInvariantPairVector j + a 1 • twistDeltaVector j := by
  have h := capKernel_wang_h2_coordinates j
    ((surfaceH2Equiv j (specialLocalData j).centralPeriod).symm a)
  simpa only [LinearEquiv.apply_symm_apply, ellipticTwoClass] using! h

/-- The original cusp monodromy on the six ordered second-homology coordinates. -/
theorem cuspMonodromy_two_coordinates (a : SingularHomology RealTorus₄ 2) :
    FlatTorus.singularH2Coordinates (monodromyHomologyMap (monodromy none) 2 a) =
      squareM₀ *ᵥ FlatTorus.singularH2Coordinates a := by
  have h := LinearMap.congr_fun
    (TrianglePeriodFamily.Boundary.Cusp.monodromyHomology_triangle 2) a
  have h' : monodromyHomologyMap (monodromy none) 2 a =
      triangleHomologyEquiv triangleCuspGenerator 2 a := h
  rw [h']
  change FlatTorus.singularH2Coordinates
    (singularHomologyMap (triangleTorusHomeomorph triangleCuspGenerator :
      C(RealTorus₄, RealTorus₄)) 2 a) = _
  rw [FlatTorus.singularH2Coordinates_inducedHomology_triangle,
    triangleDualRepresentation_cusp_matrix]
  rfl

/-- A literal invariant vector defines an actual second-degree Wang invariant. -/
def cuspTwoInvariant (v : Fin 6 → ℤ) (hv : squareM₀ *ᵥ v = v) :
    LinearMap.ker (wangDifference (monodromy none) 2) :=
  ⟨FlatTorus.singularH2Coordinates.symm v, by
    apply FlatTorus.singularH2Coordinates.injective
    change FlatTorus.singularH2Coordinates
      (FlatTorus.singularH2Coordinates.symm v -
        monodromyHomologyMap (monodromy none) 2 (FlatTorus.singularH2Coordinates.symm v)) = _
    rw [map_sub, cuspMonodromy_two_coordinates, LinearEquiv.apply_symm_apply, map_zero]
    exact sub_eq_zero.mpr hv.symm⟩

/-- The unique native cusp cap-kernel class with the specified actual second-degree Wang vector. -/
def cuspTwoClass (v : Fin 6 → ℤ) (hv : squareM₀ *ᵥ v = v) : NativeCapKernel none 3 :=
  (cuspCapKernelWangEquivDegree 2).symm (cuspTwoInvariant v hv)

@[simp] theorem cuspTwoClass_wang (v : Fin 6 → ℤ) (hv : squareM₀ *ᵥ v = v) :
    FlatTorus.singularH2Coordinates
      (wangBoundary (monodromy none) 2 (cuspTwoClass v hv).val) = v := by
  change FlatTorus.singularH2Coordinates
    (wangBoundary (monodromy none) 2
      ((cuspCapKernelWangEquivDegree 2).symm (cuspTwoInvariant v hv)).val) = v
  rw [cuspCapKernelWangEquivDegree_symm_wang]
  exact LinearEquiv.apply_symm_apply _ _

/-- The actual source formula in the original ordered exterior-square marking. -/
theorem nativeCapKernelSourceMap_two_coordinates
    (a : ∀ i : Puncture, NativeCapKernel i 3) :
    (FlatTorus.singularH2Coordinates (nativeCapKernelSourceMap 2 a).val.1,
      FlatTorus.singularH2Coordinates (nativeCapKernelSourceMap 2 a).val.2) =
      (FlatTorus.singularH2Coordinates (nativeCapKernelWangValue 2 a (some .three)) -
          squareA₂ *ᵥ FlatTorus.singularH2Coordinates (nativeCapKernelWangValue 2 a none),
        FlatTorus.singularH2Coordinates (nativeCapKernelWangValue 2 a (some .four)) -
          FlatTorus.singularH2Coordinates (nativeCapKernelWangValue 2 a none)) := by
  rw [nativeCapKernelSourceMap_val_second]
  simp only [map_sub, generatorHomologyTwo_coordinates, if_true]

/-- The common original invariant `2 γ∧δ + 12 u∧w`. -/
def commonWangVector : Fin 6 → ℤ := ![0, 0, 2, 12, 0, 0]

theorem commonWangVector_cusp_fixed : squareM₀ *ᵥ commonWangVector = commonWangVector := by
  rw [squareM₀_eq]
  decide

theorem commonWangVector_second_fixed : squareA₂ *ᵥ commonWangVector = commonWangVector := by
  rw [squareA₂_eq]
  decide

/-- The three original cap-kernel classes spanning the remaining source-kernel direction. -/
def referenceClasses : ∀ i : Puncture, NativeCapKernel i 3
  | none => cuspTwoClass commonWangVector commonWangVector_cusp_fixed
  | some .three => ellipticTwoClass .three ![2 * sourceShearTwo .three + 4, 2]
  | some .four => ellipticTwoClass .four ![3 - sourceShearTwo .four, -2]

/-- Every component has this exact actual Wang vector, with the original positive signs. -/
theorem referenceClasses_wang (i : Puncture) :
    FlatTorus.singularH2Coordinates (nativeCapKernelWangValue 2 referenceClasses i) =
      commonWangVector := by
  cases i with
  | none => exact cuspTwoClass_wang _ _
  | some j =>
    cases j <;>
      change FlatTorus.singularH2Coordinates
        (wangBoundary (monodromy (some _)) 2 (ellipticTwoClass _ _).val) = _
    all_goals rw [ellipticTwoClass_wang]
    all_goals
      ext i
      fin_cases i <;>
        simp [fibreNormIndex, fibreInvariantPairVector, fibreSquareKernelVector,
          twistDeltaVector, Kind.twist, ε, ε', commonWangVector] <;> ring

/-- Only the source projection is evaluated here, not the remaining genuine fibre coefficient. -/
theorem referenceClasses_source_eq_zero : nativeCapKernelSourceMap 2 referenceClasses = 0 := by
  have h := nativeCapKernelSourceMap_two_coordinates referenceClasses
  simp only [referenceClasses_wang, commonWangVector_second_fixed, sub_self] at h
  apply Subtype.ext
  apply Prod.ext
  · apply FlatTorus.singularH2Coordinates.injective
    exact (congrArg Prod.fst h).trans (map_zero _).symm
  · apply FlatTorus.singularH2Coordinates.injective
    exact (congrArg Prod.snd h).trans (map_zero _).symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.ThirdDegree
