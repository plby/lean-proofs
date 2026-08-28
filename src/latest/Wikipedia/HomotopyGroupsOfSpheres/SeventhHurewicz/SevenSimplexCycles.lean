import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.SevenSimplexBasic
import Wikipedia.HopfProblem.FourthHurewiczFourSimplexSimplexSum

/-!
# The actual corrected seven-simplex cycle

Subtracting the constant simplex gives the corrected cycle in any degree.
The signed permutation formula is the existing generic chain identity.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The original seven-simplex minus the actual constant seven-simplex. -/
def basedSevenSimplexChain (τ : BasedSevenSimplex x) : Chains X 7 :=
  HigherHurewicz.correctedSimplexChain 7 x τ.val

@[simp] theorem basedSevenSimplexChain_eq (τ : BasedSevenSimplex x) :
    basedSevenSimplexChain τ =
      simplexChain X 7 τ.val - simplexChain X 7 (ContinuousMap.const (Simplex 7) x) := rfl

theorem basedSevenSimplexChain_boundary (τ : BasedSevenSimplex x) :
    ((singularComplex X).d 7 6).hom (basedSevenSimplexChain τ) = 0 :=
  HigherHurewicz.correctedSimplexChain_boundary 6 x τ.val (basedSevenSimplex_face τ)

/-- The corrected cycle in the original unnormalized singular complex. -/
def basedSevenSimplexCycle (τ : BasedSevenSimplex x) :
    ModuleHomology.Cycle (singularComplex X) 7 :=
  HigherHurewicz.correctedSimplexCycle 6 x τ.val (basedSevenSimplex_face τ)

@[simp] theorem basedSevenSimplexCycle_val (τ : BasedSevenSimplex x) :
    (basedSevenSimplexCycle τ).1 = basedSevenSimplexChain τ := rfl

@[simp] theorem basedSevenSimplexCycle_constant (x : X) :
    basedSevenSimplexCycle (constantBasedSevenSimplex x) = 0 := by
  apply Subtype.ext
  exact sub_self _

/-- The signed 5040-cell simplex chain is exactly the corrected seven-simplex. -/
theorem basedSevenSimplex_simplexChain_sum (τ : BasedSevenSimplex x) :
    (∑ e : Equiv.Perm (Fin 7), HigherHurewicz.CubeTriangulation.cubeOrientation e •
      simplexChain X 7 ((basedSevenSimplexLoop τ).val.comp
        (HigherHurewicz.CubeTriangulation.cubeSimplex e))) = basedSevenSimplexChain τ :=
  HigherHurewicz.SimplexGeometry.basedSimplex_simplexChain_sum (n := 5) τ

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
