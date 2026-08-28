import Wikipedia.HopfProblem.FifthHurewiczFiveSimplexBasic
import Wikipedia.HopfProblem.FourthHurewiczFourSimplexSimplexSum

/-!
# The actual corrected five-simplex cycle

Both the original based five-simplex and the constant five-simplex have
zero boundary.  Their difference is the precise cycle represented by the
native simplex quotient.  The signed permutation-cell identity is the
degree-five instance of the existing dimension-generic chain theorem.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FifthHurewicz

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The original five-simplex minus the actual constant five-simplex. -/
def basedFiveSimplexChain (τ : BasedFiveSimplex x) : Chains X 5 :=
  HigherHurewicz.correctedSimplexChain 5 x τ.val

@[simp] theorem basedFiveSimplexChain_eq (τ : BasedFiveSimplex x) :
    basedFiveSimplexChain τ =
      simplexChain X 5 τ.val - simplexChain X 5 (ContinuousMap.const (Simplex 5) x) := rfl

theorem basedFiveSimplexChain_boundary (τ : BasedFiveSimplex x) :
    ((singularComplex X).d 5 4).hom (basedFiveSimplexChain τ) = 0 :=
  HigherHurewicz.correctedSimplexChain_boundary 4 x τ.val (basedFiveSimplex_face τ)

/-- In odd degree the original based simplex itself has zero boundary. -/
theorem basedFiveSimplex_boundary (τ : BasedFiveSimplex x) :
    ((singularComplex X).d 5 4).hom (simplexChain X 5 τ.val) = 0 := by
  have h := basedFiveSimplexChain_boundary τ
  rw [basedFiveSimplexChain_eq, map_sub] at h
  have hc := HigherHurewicz.boundary_constantSimplexChain_odd 4 x (by decide)
  rw [show ((singularComplex X).d 5 4).hom
      (simplexChain X 5 (ContinuousMap.const (Simplex 5) x)) = 0 from hc,
    sub_zero] at h
  exact h

/-- The corrected cycle in the original unnormalized singular complex. -/
def basedFiveSimplexCycle (τ : BasedFiveSimplex x) :
    ModuleHomology.Cycle (singularComplex X) 5 :=
  HigherHurewicz.correctedSimplexCycle 4 x τ.val (basedFiveSimplex_face τ)

@[simp] theorem basedFiveSimplexCycle_val (τ : BasedFiveSimplex x) :
    (basedFiveSimplexCycle τ).1 = basedFiveSimplexChain τ := rfl

@[simp] theorem basedFiveSimplexCycle_constant (x : X) :
    basedFiveSimplexCycle (constantBasedFiveSimplex x) = 0 := by
  apply Subtype.ext
  exact sub_self _

/-- The signed 120-cell simplex chain is exactly the corrected five-simplex. -/
theorem basedFiveSimplex_simplexChain_sum (τ : BasedFiveSimplex x) :
    (∑ e : Equiv.Perm (Fin 5), HigherHurewicz.CubeTriangulation.cubeOrientation e •
      simplexChain X 5 ((basedFiveSimplexLoop τ).val.comp
        (HigherHurewicz.CubeTriangulation.cubeSimplex e))) = basedFiveSimplexChain τ :=
  HigherHurewicz.SimplexGeometry.basedSimplex_simplexChain_sum (n := 3) τ

end Wikipedia.HopfProblem.FifthHurewicz
