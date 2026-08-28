import Wikipedia.NoExoticSixSphere.OrthogonalBottHomotopy
import Wikipedia.NoExoticSixSphere.LoopSpaceDimensionShift

/-!
# The first Bott comparison with the next orthogonal homotopy group

Compose the actual Bott loop map with the native loop-space dimension shift.
The result is a group isomorphism in positive degree within the proved range.
No vanishing of either side is assumed or asserted here.
-/

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization

variable {n : ℕ}

noncomputable def bottDegreeShiftEquiv (d : ℕ) (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (J₀ : OrthogonalComplexStructures.Space n) (hd : d + 3 < n) :
    HomotopyGroup (Fin d) (OrthogonalComplexStructures.Space n) J₀ ≃
      HomotopyGroup (Fin (d + 1)) (OrthogonalOperators n) a :=
  (bottHomotopyEquiv d a b hanti J₀ hd).trans (GeneralizedLoopCurrying.homotopyEquiv d a)

noncomputable def bottDegreeShiftMulEquiv (d : ℕ) [NeZero d] (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (J₀ : OrthogonalComplexStructures.Space n) (hd : d + 3 < n) :
    HomotopyGroup (Fin d) (OrthogonalComplexStructures.Space n) J₀ ≃*
      HomotopyGroup (Fin (d + 1)) (OrthogonalOperators n) a :=
  (bottHomotopyMulEquiv d a b hanti J₀ hd).trans (GeneralizedLoopCurrying.homotopyMulEquiv d a)

/-- The dimension-five orthogonal group is identified with the dimension-four
group of actual orthogonal complex structures at every rank above seven. -/
noncomputable def fourthComplexStructureEquivFifthOrthogonal
    (a b : OrthogonalOperators n)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (J₀ : OrthogonalComplexStructures.Space n) (hn : 7 < n) :
    HomotopyGroup (Fin 4) (OrthogonalComplexStructures.Space n) J₀ ≃*
      HomotopyGroup (Fin 5) (OrthogonalOperators n) a :=
  bottDegreeShiftMulEquiv 4 a b hanti J₀ hn

end NoExoticSixSphere.OrthogonalPolygon
