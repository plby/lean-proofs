import Wikipedia.HopfProblem.FourthHurewiczFourSimplexBasic
import Wikipedia.HopfProblem.HigherHurewiczHomologyDescentConstants

/-!
# The corrected cycle of an actual based four-simplex

In degree four a constant simplex has the constant three-simplex as its
boundary.  Subtracting this same constant from the original based simplex
therefore gives a cycle in the original unnormalized singular complex.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The original four-simplex minus the actual constant four-simplex. -/
def basedFourSimplexChain (τ : BasedFourSimplex x) : Chains X 4 :=
  HigherHurewicz.correctedSimplexChain 4 x τ.val

@[simp] theorem basedFourSimplexChain_eq (τ : BasedFourSimplex x) :
    basedFourSimplexChain τ =
      simplexChain X 4 τ.val - simplexChain X 4 (ContinuousMap.const (Simplex 4) x) := rfl

theorem basedFourSimplexChain_boundary (τ : BasedFourSimplex x) :
    ((singularComplex X).d 4 3).hom (basedFourSimplexChain τ) = 0 :=
  HigherHurewicz.correctedSimplexChain_boundary 3 x τ.val (basedFourSimplex_face τ)

/-- In even degree the uncorrected simplex need not be a cycle. -/
theorem basedFourSimplex_boundary (τ : BasedFourSimplex x) :
    ((singularComplex X).d 4 3).hom (simplexChain X 4 τ.val) =
      simplexChain X 3 (ContinuousMap.const (Simplex 3) x) := by
  have h := basedFourSimplexChain_boundary τ
  rw [basedFourSimplexChain_eq, map_sub] at h
  have hc := HigherHurewicz.boundary_constantSimplexChain_even 3 x (by decide)
  rw [show ((singularComplex X).d 4 3).hom
      (simplexChain X 4 (ContinuousMap.const (Simplex 4) x)) =
      simplexChain X 3 (ContinuousMap.const (Simplex 3) x) from hc] at h
  exact sub_eq_zero.mp h

/-- The actual corrected singular four-cycle. -/
def basedFourSimplexCycle (τ : BasedFourSimplex x) :
    ModuleHomology.Cycle (singularComplex X) 4 :=
  HigherHurewicz.correctedSimplexCycle 3 x τ.val (basedFourSimplex_face τ)

@[simp] theorem basedFourSimplexCycle_val (τ : BasedFourSimplex x) :
    (basedFourSimplexCycle τ).1 = basedFourSimplexChain τ := rfl

@[simp] theorem basedFourSimplexCycle_constant (x : X) :
    basedFourSimplexCycle (constantBasedFourSimplex x) = 0 := by
  apply Subtype.ext
  exact sub_self _

end Wikipedia.HopfProblem.FourthHurewicz
