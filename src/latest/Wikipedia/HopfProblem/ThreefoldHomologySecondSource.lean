import Wikipedia.HopfProblem.ThreefoldHomologySecondSourceLattice
import Wikipedia.HopfProblem.ThreefoldHomologyCapEliminationClasses

/-!
# Surjectivity onto the actual second-degree source kernel

The integral reconstruction is realized by the original elliptic cap
kernels and the genuine cusp cap-kernel Wang equivalence.  The resulting
original attachment map therefore surjects onto the degree-one source
kernel.  No choice of a splitting of regular-family homology is used.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.SecondSource

open SingularMayerVietoris TrianglePeriodFamily
open TrianglePeriodFamily.Homology (sourceDifference)
open TrianglePeriodFamily.HomologyDifference
open TrianglePeriodFamilyHomologyLattice
open TrianglePeriodFamily.Boundary.EllipticCapKernelWang
open CapElimination

local notation "κ₃" => h1ShearCorrection Elliptic.Kind.three
local notation "κ₄" => h1ShearCorrection Elliptic.Kind.four

/-- The lattice reconstruction realized by three actual native cap-kernel classes. -/
def nativeSourceClasses (x y : Lattice) : ∀ i : Puncture, NativeCapKernel i 2
  | none => cuspOneClass (cuspCoordinates κ₄ x y) (cuspCoordinates_fixed κ₄ x y)
  | some .three => ellipticOneClass .three (threeCoordinates κ₃ κ₄ x y)
  | some .four => ellipticOneClass .four (fourCoordinates x y)

/-- The actual order-three component has the original affine-cover Wang vector. -/
theorem nativeSourceClasses_wang_three (x y : Lattice) :
    FlatTorus.singularH1Equiv
      (nativeCapKernelWangValue 1 (nativeSourceClasses x y) (some .three)) =
      threeWangVector κ₃ (threeCoordinates κ₃ κ₄ x y) := by
  have h := ellipticOneClass_wang .three (threeCoordinates κ₃ κ₄ x y)
  simpa only [Elliptic.HigherHomology.fibreNormIndex_three, Nat.cast_one, one_mul,
    Elliptic.Kind.twist, threeWangVector] using! h

/-- The order-four component retains both the actual negative twist and its actual shear. -/
theorem nativeSourceClasses_wang_four (x y : Lattice) :
    FlatTorus.singularH1Equiv
      (nativeCapKernelWangValue 1 (nativeSourceClasses x y) (some .four)) =
      fourWangVector κ₄ (fourCoordinates x y) := by
  have h := ellipticOneClass_wang .four (fourCoordinates x y)
  simpa only [Elliptic.HigherHomology.fibreNormIndex_four, Nat.cast_ofNat,
    Elliptic.Kind.twist, fourWangVector] using! h

/-- The cusp component realizes the constructed genuine invariant, with no lift premise. -/
theorem nativeSourceClasses_wang_cusp (x y : Lattice) :
    FlatTorus.singularH1Equiv
      (nativeCapKernelWangValue 1 (nativeSourceClasses x y) none) =
      cuspCoordinates κ₄ x y :=
  cuspOneClass_wang _ _

/-- The actual source coordinates of the three original cap-kernel classes. -/
theorem nativeSourceClasses_source_coordinates (x y : Lattice)
    (hxy : deltaOne (x, y) = 0) :
    (FlatTorus.singularH1Equiv (nativeCapKernelSourceMap 1 (nativeSourceClasses x y)).val.1,
      FlatTorus.singularH1Equiv
        (nativeCapKernelSourceMap 1 (nativeSourceClasses x y)).val.2) = (x, y) := by
  rw [nativeCapKernelSourceMap_one_coordinates]
  simp only [nativeSourceClasses_wang_three, nativeSourceClasses_wang_four,
    nativeSourceClasses_wang_cusp]
  exact Prod.ext (threeCoordinates_reconstruct κ₃ κ₄ x y hxy)
    (fourCoordinates_reconstruct κ₄ x y hxy)

/-- The genuine degree-two cap kernels surject onto the actual degree-one source kernel. -/
theorem nativeCapKernelSourceMap_one_surjective :
    Function.Surjective (nativeCapKernelSourceMap 1) := by
  intro a
  have hxy : deltaOne (FlatTorus.singularH1Equiv a.val.1,
      FlatTorus.singularH1Equiv a.val.2) = 0 := by
    have h := sourceDifferenceOne_coordinates a.val
    rw [show sourceDifference 1 a.val = 0 from a.property, map_zero] at h
    exact h.symm
  have h := nativeSourceClasses_source_coordinates
    (FlatTorus.singularH1Equiv a.val.1) (FlatTorus.singularH1Equiv a.val.2) hxy
  refine ⟨nativeSourceClasses (FlatTorus.singularH1Equiv a.val.1)
    (FlatTorus.singularH1Equiv a.val.2), ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact FlatTorus.singularH1Equiv.injective (congrArg Prod.fst h)
  · exact FlatTorus.singularH1Equiv.injective (congrArg Prod.snd h)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.SecondSource
