import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupMarked
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupExteriorDimension
import Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishingDetection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The genuine native exterior cup is an isomorphism on every period torus

The nonzero value is proved by the actual cup of the two original
unit-marked Dolbeault classes. Together with the proved dimensions of
the original Ext groups, this shows that the original exterior cup
itself is bijective. Its forward map and Haar-coordinate formula are
retained literally.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup

open PeriodTorusHolomorphicCohomology

variable (p : PeriodDomain)

/-- The actual exterior cup has the proved nonzero value on the original two marked classes. -/
theorem exteriorCup_ne_zero : exteriorCup p ≠ 0 :=
  CuspHolomorphicCupNonvanishing.linearMap_ne_zero_of_nonzero_value (exteriorCup p)
    (exteriorPower.ιMulti ℂ 2 ![h1Constant p ![1, 0], h1Constant p ![0, 1]])
    (cup p (h1Constant p ![1, 0]) (h1Constant p ![0, 1]))
    (exteriorCup_ιMulti p ![h1Constant p ![1, 0], h1Constant p ![0, 1]])
    (cup_marked_generators_ne_zero p)

/-- The original native exterior-square cup map is genuinely bijective. -/
theorem exteriorCup_bijective : Function.Bijective (exteriorCup p) := by
  let : FiniteDimensional ℂ (⋀[ℂ]^2 (H p 1)) :=
    FiniteDimensional.of_finrank_eq_succ (exterior_finrank p)
  let : FiniteDimensional ℂ (H p 2) :=
    FiniteDimensional.of_finrank_eq_succ (h2_finrank p)
  have hs : Function.Surjective (exteriorCup p) :=
    surjective_of_nonzero_of_finrank_eq_one (h2_finrank p) (exteriorCup_ne_zero p)
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    ((exterior_finrank p).trans (h2_finrank p).symm)).mpr hs, hs⟩

/-- The actual original cup map, bundled using its proved bijectivity. -/
def exteriorCupEquiv : ⋀[ℂ]^2 (H p 1) ≃ₗ[ℂ] H p 2 :=
  LinearEquiv.ofBijective (exteriorCup p) (exteriorCup_bijective p)

@[simp] theorem exteriorCupEquiv_toLinearMap :
    (exteriorCupEquiv p).toLinearMap = exteriorCup p := rfl

@[simp] theorem exteriorCupEquiv_apply (a : ⋀[ℂ]^2 (H p 1)) :
    exteriorCupEquiv p a = exteriorCup p a := rfl

/-- The equivalence still acts by the original native cup on every wedge generator. -/
@[simp] theorem exteriorCupEquiv_ιMulti (a : Fin 2 → H p 1) :
    exteriorCupEquiv p (exteriorPower.ιMulti ℂ 2 a) = cup p (a 0) (a 1) :=
  exteriorCup_ιMulti p a

/-- The original Haar markings give the positive determinant on every genuine wedge. -/
theorem h2Equiv_exteriorCup (a : Fin 2 → H p 1) :
    h2Equiv p (exteriorCup p (exteriorPower.ιMulti ℂ 2 a)) =
      h1Equiv p (a 0) 0 * h1Equiv p (a 1) 1 -
        h1Equiv p (a 0) 1 * h1Equiv p (a 1) 0 :=
  (congrArg (h2Equiv p) (exteriorCup_ιMulti p a)).trans (h2Equiv_cup p (a 0) (a 1))

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup
