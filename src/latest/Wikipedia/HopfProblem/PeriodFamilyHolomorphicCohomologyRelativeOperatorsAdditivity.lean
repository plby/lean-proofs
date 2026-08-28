import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeOperatorsAdditivityBasic

/-!
# Additivity of the actual scalar relative operators

The three operators preserve pointwise addition and multiplication by a
constant complex scalar. These are identities of actual functions on the
original open base times the unit torus, proved from the corresponding
Fréchet derivative identities. No operator-linearity premise is supplied.
-/

noncomputable section

open TopologicalSpace

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeOperators

open FourierParameter

variable {U : Opens ℂ} {d : Type*} [Fintype d]

/-- The genuine antiholomorphic base operator preserves the pointwise sum. -/
theorem d0_add (f g : SmoothFamily U d) (x : U × UnitAddTorus d) :
    d0 (add f g) x = d0 f x + d0 g x := by
  rcases x with ⟨b, t⟩
  simp only [d0_apply, baseDerivative_add]
  ring

/-- The genuine antiholomorphic base operator commutes with constant complex scalars. -/
theorem d0_constMul (a : ℂ) (f : SmoothFamily U d) (x : U × UnitAddTorus d) :
    d0 (constMul a f) x = a * d0 f x := by
  rcases x with ⟨b, t⟩
  simp only [d0_apply, baseDerivative_constMul]
  ring

variable (P : HolomorphicPeriodMap ℂ U)

/-- The first actual marked vertical operator preserves the pointwise sum. -/
theorem d1_add (f g : SmoothFamily U (Fin 4)) (x : U × UnitAddTorus (Fin 4)) :
    d1 P (add f g) x = d1 P f x + d1 P g x := by
  rcases x with ⟨b, t⟩
  simp only [d1_apply, verticalDerivative_add]
  ring

/-- The second actual marked vertical operator preserves the pointwise sum. -/
theorem d2_add (f g : SmoothFamily U (Fin 4)) (x : U × UnitAddTorus (Fin 4)) :
    d2 P (add f g) x = d2 P f x + d2 P g x := by
  rcases x with ⟨b, t⟩
  simp only [d2_apply, verticalDerivative_add]
  ring

/-- The first actual marked vertical operator commutes with constant complex scalars. -/
theorem d1_constMul (a : ℂ) (f : SmoothFamily U (Fin 4))
    (x : U × UnitAddTorus (Fin 4)) :
    d1 P (constMul a f) x = a * d1 P f x := by
  rcases x with ⟨b, t⟩
  simp only [d1_apply, verticalDerivative_constMul]
  ring

/-- The second actual marked vertical operator commutes with constant complex scalars. -/
theorem d2_constMul (a : ℂ) (f : SmoothFamily U (Fin 4))
    (x : U × UnitAddTorus (Fin 4)) :
    d2 P (constMul a f) x = a * d2 P f x := by
  rcases x with ⟨b, t⟩
  simp only [d2_apply, verticalDerivative_constMul]
  ring

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeOperators
