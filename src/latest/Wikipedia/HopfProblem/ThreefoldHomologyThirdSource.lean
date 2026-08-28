import Wikipedia.HopfProblem.ThreefoldHomologyThirdClasses
import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepCentralCoordinates

/-!
# Surjectivity onto the actual third-degree source kernel

The geometric central sweep proves the divisibility of the original
order-four covering shear.  Its actual integral correction specializes
the lattice reconstruction, whose preimages are realized in the
original elliptic and cusp cap kernels.  The source map is therefore
surjective without any parity or marking hypothesis.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.ThirdSource

open SingularMayerVietoris ThreefoldOverlapMappingTorus MappingTorusHomology
open TrianglePeriodFamily
open TrianglePeriodFamily.Homology (sourceDifference)
open TrianglePeriodFamily.HomologyDifference TrianglePeriodFamilyHomologyLattice
open TrianglePeriodFamily.Boundary.EllipticCapKernelWang
open Elliptic Elliptic.HigherHomology CapElimination ThirdDegree

local notation "c₃" => sourceShearTwo Kind.three
local notation "k₄" => DeltaSweep.centralSweepShearCorrection Kind.four

/-- The actual sweep supplies the half-shear required by the integral reconstruction. -/
theorem twice_fourShearCorrection : 2 * k₄ = sourceShearTwo .four := by
  simpa only [fibreNormIndex_four, Nat.cast_ofNat] using
    DeltaSweep.fibreNormIndex_mul_centralSweepShearCorrection Kind.four

/-- The actual order-three Wang map is the original literal six-coordinate column. -/
theorem ellipticTwoClass_wang_three (a : Fin 2 → ℤ) :
    FlatTorus.singularH2Coordinates
      (wangBoundary (monodromy (some .three)) 2 (ellipticTwoClass .three a).val) =
      threeWangVector c₃ a := by
  have h := ellipticTwoClass_wang .three a
  simpa only [fibreNormIndex_three, Nat.cast_one, one_mul, fibreInvariantPairVector,
    fibreSquareKernelVector, twistDeltaVector, Kind.twist, ε, threeWangVector] using! h

/-- The actual order-four column retains its original shear, now proved to be twice `k₄`. -/
theorem ellipticTwoClass_wang_four (a : Fin 2 → ℤ) :
    FlatTorus.singularH2Coordinates
      (wangBoundary (monodromy (some .four)) 2 (ellipticTwoClass .four a).val) =
      fourWangVector (2 * k₄) a := by
  have h := ellipticTwoClass_wang .four a
  rw [← twice_fourShearCorrection] at h
  simpa only [fibreNormIndex_four, Nat.cast_ofNat, fibreInvariantPairVector,
    fibreSquareKernelVector, twistDeltaVector, Kind.twist, ε', fourWangVector] using! h

/-- The explicit integral reconstruction realized in the three original cap kernels. -/
def nativeSourceClasses (x y : Fin 6 → ℤ) : ∀ i : Puncture, NativeCapKernel i 3
  | none => cuspTwoClass (cuspCoordinates x y) (cuspCoordinates_fixed x y)
  | some .three => ellipticTwoClass .three (threeCoordinates c₃ x y)
  | some .four => ellipticTwoClass .four (fourCoordinates k₄ x y)

theorem nativeSourceClasses_wang_three (x y : Fin 6 → ℤ) :
    FlatTorus.singularH2Coordinates
      (nativeCapKernelWangValue 2 (nativeSourceClasses x y) (some .three)) =
      threeWangVector c₃ (threeCoordinates c₃ x y) :=
  ellipticTwoClass_wang_three _

theorem nativeSourceClasses_wang_four (x y : Fin 6 → ℤ) :
    FlatTorus.singularH2Coordinates
      (nativeCapKernelWangValue 2 (nativeSourceClasses x y) (some .four)) =
      fourWangVector (2 * k₄) (fourCoordinates k₄ x y) :=
  ellipticTwoClass_wang_four _

theorem nativeSourceClasses_wang_cusp (x y : Fin 6 → ℤ) :
    FlatTorus.singularH2Coordinates
      (nativeCapKernelWangValue 2 (nativeSourceClasses x y) none) =
      cuspCoordinates x y :=
  cuspTwoClass_wang _ _

/-- The unchanged native source map reconstructs the prescribed ordered coordinates. -/
theorem nativeSourceClasses_source_coordinates (x y : Fin 6 → ℤ)
    (hxy : (x, y) ∈ LinearMap.ker deltaTwo) :
    (FlatTorus.singularH2Coordinates (nativeCapKernelSourceMap 2 (nativeSourceClasses x y)).val.1,
      FlatTorus.singularH2Coordinates
        (nativeCapKernelSourceMap 2 (nativeSourceClasses x y)).val.2) = (x, y) := by
  rw [nativeCapKernelSourceMap_two_coordinates]
  simp only [nativeSourceClasses_wang_three, nativeSourceClasses_wang_four,
    nativeSourceClasses_wang_cusp]
  exact Prod.ext (threeCoordinates_source c₃ x y hxy) (fourCoordinates_source k₄ x y hxy)

/-- The actual degree-three cap kernels surject onto the genuine second-degree source kernel. -/
theorem nativeCapKernelSourceMap_two_surjective :
    Function.Surjective (nativeCapKernelSourceMap 2) := by
  intro a
  have hxy : (FlatTorus.singularH2Coordinates a.val.1,
      FlatTorus.singularH2Coordinates a.val.2) ∈ LinearMap.ker deltaTwo := by
    change deltaTwo (FlatTorus.singularH2Coordinates a.val.1,
      FlatTorus.singularH2Coordinates a.val.2) = 0
    have h := sourceDifferenceTwo_coordinates a.val
    rw [show sourceDifference 2 a.val = 0 from a.property, map_zero] at h
    exact h.symm
  have h := nativeSourceClasses_source_coordinates
    (FlatTorus.singularH2Coordinates a.val.1) (FlatTorus.singularH2Coordinates a.val.2) hxy
  refine ⟨nativeSourceClasses (FlatTorus.singularH2Coordinates a.val.1)
    (FlatTorus.singularH2Coordinates a.val.2), ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact FlatTorus.singularH2Coordinates.injective (congrArg Prod.fst h)
  · exact FlatTorus.singularH2Coordinates.injective (congrArg Prod.snd h)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.ThirdSource
