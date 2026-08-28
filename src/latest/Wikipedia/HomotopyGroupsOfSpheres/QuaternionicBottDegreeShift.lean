import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottHomotopy
import Wikipedia.NoExoticSixSphere.LoopSpaceDimensionShift

/-!
# The first Bott comparison with the next symplectic homotopy group

Compose the actual Bott loop map with the native loop-space dimension shift.
The result is a group isomorphism in positive degree within the proved range.
No vanishing of either side is assumed or asserted here.
-/

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization

variable {n : ℕ}

noncomputable def bottDegreeShiftEquiv (d : ℕ) (a b : symplecticSubgroup n)
    (hanti : (a⁻¹ * b).val.val.val = -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (J₀ : ComplexStructures.Space n) (hd : d + 1 < n) :
    HomotopyGroup (Fin d) (ComplexStructures.Space n) J₀ ≃
      HomotopyGroup (Fin (d + 1)) (symplecticSubgroup n) a :=
  (bottHomotopyEquiv d a b hanti J₀ hd).trans (GeneralizedLoopCurrying.homotopyEquiv d a)

noncomputable def bottDegreeShiftMulEquiv (d : ℕ) [NeZero d] (a b : symplecticSubgroup n)
    (hanti : (a⁻¹ * b).val.val.val = -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (J₀ : ComplexStructures.Space n) (hd : d + 1 < n) :
    HomotopyGroup (Fin d) (ComplexStructures.Space n) J₀ ≃*
      HomotopyGroup (Fin (d + 1)) (symplecticSubgroup n) a :=
  (bottHomotopyMulEquiv d a b hanti J₀ hd).trans (GeneralizedLoopCurrying.homotopyMulEquiv d a)

/-- The first Bott step for the native sixth symplectic homotopy group. -/
noncomputable def fifthComplexStructureEquivSixthSymplectic
    (a b : symplecticSubgroup n)
    (hanti : (a⁻¹ * b).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (J₀ : ComplexStructures.Space n) (hn : 6 < n) :
    HomotopyGroup (Fin 5) (ComplexStructures.Space n) J₀ ≃*
      HomotopyGroup (Fin 6) (symplecticSubgroup n) a :=
  bottDegreeShiftMulEquiv 5 a b hanti J₀ hn

/-- The first Bott step for the native seventh symplectic homotopy group. -/
noncomputable def sixthComplexStructureEquivSeventhSymplectic
    (a b : symplecticSubgroup n)
    (hanti : (a⁻¹ * b).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (J₀ : ComplexStructures.Space n) (hn : 7 < n) :
    HomotopyGroup (Fin 6) (ComplexStructures.Space n) J₀ ≃*
      HomotopyGroup (Fin 7) (symplecticSubgroup n) a :=
  bottDegreeShiftMulEquiv 6 a b hanti J₀ hn

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
