import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeHomotopyNeighborhood
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeHomotopyLocalInverse
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeOperatorsAdditivity

/-!
# A genuine local normal form for every closed smooth relative triple

Add the actual selected-inverse Fourier potential to the genuine
Cauchy--Green primitive of its original base mean. Their sum has exactly
the original base component as its base antiholomorphic derivative. Its
two vertical derivatives differ from the original vertical components
only by their actual holomorphic Haar means.

This is an analytic theorem about actual smooth functions and actual
differential operators. No cohomological representation, local freeness,
or higher-direct-image comparison is an assumption or a conclusion here.
-/

noncomputable section

open TopologicalSpace UnitAddTorus
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy

open FourierParameter RelativeOperators RelativeBasePrimitive

/-- The indexed original vertical operator preserves actual pointwise addition. -/
theorem verticalOperator_add {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)
    (j : Fin 2) (f g : SmoothFamily U (Fin 4)) (x : U × UnitAddTorus (Fin 4)) :
    verticalOperator P j (add f g) x = verticalOperator P j f x + verticalOperator P j g x := by
  fin_cases j
  · simpa [verticalOperator] using d1_add P f g x
  · simpa [verticalOperator] using d2_add P f g x

/-- A genuine torus-constant smooth family has zero vertical components. -/
theorem verticalOperator_constantFamily {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)
    (j : Fin 2) (u : ℂ → ℂ) (hu : ContDiffOn ℝ ∞ u U)
    (b : U) (t : UnitAddTorus (Fin 4)) :
    verticalOperator P j (constantFamily u hu) (b, t) = 0 := by
  unfold verticalOperator
  split_ifs
  · rw [d1_apply]
    simp only [constantFamily_verticalDerivative, mul_zero, zero_add, sub_zero]
  · rw [d2_apply]
    simp only [constantFamily_verticalDerivative, mul_zero, zero_add, sub_zero]

/-- Every actual closed smooth triple is locally an actual derivative
plus its two original holomorphic vertical Haar means. -/
theorem exists_local_primitive_mod_vertical_means {U : Opens ℂ}
    (P : HolomorphicPeriodMap ℂ U) (a₀ : SmoothFamily U (Fin 4))
    (a : Fin 2 → SmoothFamily U (Fin 4)) (hclosed : IsClosedTriple P a₀ a) (b₀ : U) :
    ∃ V : Opens ℂ, ∃ hVU : V ≤ U, (b₀ : ℂ) ∈ V ∧ ∃ g : SmoothFamily V (Fin 4),
      (∀ (b : V) (t : UnitAddTorus (Fin 4)), d0 g (b, t) = a₀ (Set.inclusion hVU b, t)) ∧
      (∀ (j : Fin 2) (b : V) (t : UnitAddTorus (Fin 4)),
        verticalOperator (restrictPeriods P hVU) j g (b, t) =
          a j (Set.inclusion hVU b, t) - (a j).coefficientValue 0 (b : ℂ)) ∧
      ∀ j : Fin 2, ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
        (fun b : V => (a j).coefficientValue 0 (b : ℂ)) := by
  obtain ⟨V, hVU, hb, hm, hhol, hinverse, u, hu, hprimitive⟩ :=
    exists_open_inverse_and_mean_primitive P a₀ b₀
  let g₁ := potentialOfFamilies P (P.point b₀) hVU a hm
  let g₀ : SmoothFamily V (Fin 4) := constantFamily u hu.contDiffOn
  refine ⟨V, hVU, hb, add g₁ g₀, ?_, ?_, ?_⟩
  · intro b t
    rw [d0_add, potentialOfFamilies_d0_apply P (P.point b₀) hVU a₀ a hm hinverse hhol hclosed,
      constantFamily_d0, hprimitive b]
    ring
  · intro j b t
    rw [verticalOperator_add,
      potentialOfFamilies_vertical_apply P (P.point b₀) hVU a₀ a hm hinverse hclosed,
      verticalOperator_constantFamily, add_zero]
  · intro j
    exact (hclosed.vertical_mean_contMDiff j).comp (contMDiff_inclusion hVU)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy
