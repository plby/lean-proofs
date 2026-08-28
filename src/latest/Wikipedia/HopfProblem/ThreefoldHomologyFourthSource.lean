import Wikipedia.HopfProblem.ThreefoldHomologyFourthSourceLattice
import Wikipedia.HopfProblem.ThreefoldHomologyCapEliminationClasses

/-!
# Surjectivity onto the actual fourth-degree source kernel

The explicit integral preimages are realized by the original elliptic
cap-kernel classes and by the actual cusp cap-kernel Wang equivalence.
The original source-coordinate formula then proves surjectivity onto
the kernel of the genuine degree-three source difference map.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FourthSource

open SingularMayerVietoris TrianglePeriodFamily
open TrianglePeriodFamily.Homology (sourceDifference)
open TrianglePeriodFamily.HomologyDifference
open TrianglePeriodFamilyHomologyLattice
open TrianglePeriodFamily.Boundary.EllipticCapKernelWang
open CapElimination

local notation "c₃" => sourceShearThree Elliptic.Kind.three
local notation "c₄" => sourceShearThree Elliptic.Kind.four

/-- The lattice preimages realized in the three original native cap kernels. -/
def nativeSourceClasses (x y : Lattice) : ∀ i : Puncture, NativeCapKernel i 4
  | none => cuspThreeClass (cuspCoordinates c₃ c₄ x y) (cuspCoordinates_fixed c₃ c₄ x y)
  | some .three => ellipticThreeClass .three (threeCoordinates c₃ c₄ x y)
  | some .four => ellipticThreeClass .four (fourCoordinates c₃ c₄ x y)

/-- The actual order-three component has the original top Wang column. -/
theorem nativeSourceClasses_wang_three (x y : Lattice) :
    FlatTorus.singularH3Coordinates
      (nativeCapKernelWangValue 3 (nativeSourceClasses x y) (some .three)) =
      topWangMatrix .three c₃ *ᵥ threeCoordinates c₃ c₄ x y :=
  ellipticThreeClass_wang .three _

/-- The actual order-four component retains its original shear and column. -/
theorem nativeSourceClasses_wang_four (x y : Lattice) :
    FlatTorus.singularH3Coordinates
      (nativeCapKernelWangValue 3 (nativeSourceClasses x y) (some .four)) =
      topWangMatrix .four c₄ *ᵥ fourCoordinates c₃ c₄ x y :=
  ellipticThreeClass_wang .four _

/-- The actual cusp component realizes the constructed genuine cusp invariant. -/
theorem nativeSourceClasses_wang_cusp (x y : Lattice) :
    FlatTorus.singularH3Coordinates
      (nativeCapKernelWangValue 3 (nativeSourceClasses x y) none) =
      cuspCoordinates c₃ c₄ x y :=
  cuspThreeClass_wang _ _

/-- The original native source map has the exact prescribed ordered coordinates. -/
theorem nativeSourceClasses_source_coordinates (x y : Lattice)
    (hxy : (x, y) ∈ LinearMap.ker deltaThree) :
    (FlatTorus.singularH3Coordinates (nativeCapKernelSourceMap 3 (nativeSourceClasses x y)).val.1,
      FlatTorus.singularH3Coordinates
        (nativeCapKernelSourceMap 3 (nativeSourceClasses x y)).val.2) = (x, y) := by
  rw [nativeCapKernelSourceMap_three_coordinates]
  simp only [nativeSourceClasses_wang_three, nativeSourceClasses_wang_four,
    nativeSourceClasses_wang_cusp]
  exact Prod.ext (threeCoordinates_source c₃ c₄ x y hxy)
    (fourCoordinates_source c₃ c₄ x y hxy)

/-- The genuine degree-four cap kernels surject onto the actual source-difference kernel. -/
theorem nativeCapKernelSourceMap_three_surjective :
    Function.Surjective (nativeCapKernelSourceMap 3) := by
  intro a
  have hxy : (FlatTorus.singularH3Coordinates a.val.1,
      FlatTorus.singularH3Coordinates a.val.2) ∈ LinearMap.ker deltaThree := by
    change deltaThree (FlatTorus.singularH3Coordinates a.val.1,
      FlatTorus.singularH3Coordinates a.val.2) = 0
    have h := sourceDifferenceThree_coordinates a.val
    rw [show sourceDifference 3 a.val = 0 from a.property, map_zero] at h
    exact h.symm
  have h := nativeSourceClasses_source_coordinates
    (FlatTorus.singularH3Coordinates a.val.1) (FlatTorus.singularH3Coordinates a.val.2) hxy
  refine ⟨nativeSourceClasses (FlatTorus.singularH3Coordinates a.val.1)
    (FlatTorus.singularH3Coordinates a.val.2), ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact FlatTorus.singularH3Coordinates.injective (congrArg Prod.fst h)
  · exact FlatTorus.singularH3Coordinates.injective (congrArg Prod.snd h)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FourthSource
