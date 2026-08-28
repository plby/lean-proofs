import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsCotangent
import Wikipedia.HopfProblem.PeriodFamily

/-!
# Real-linear decomposition for the original inverse-coordinate pullback

Only the source `ℂ × ComplexPlane₂` carries its original complex structure.
The target `ℂ × RealPlane₄` is used here strictly as a real normed space.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Pullback

open Complex HolomorphicDolbeaultThree
open scoped BigOperators

/-- The antiholomorphic coefficient of the actual real-linear restriction
to the original complex base direction. -/
def baseCoefficient (L : (ℂ × RealPlane₄) →L[ℝ] ℂ) : ℂ :=
  (L (1, 0) + I * L (I, 0)) / 2

/-- Evaluation of an actual real-linear covector on an original marked
real coordinate direction. -/
def realCoefficient (L : (ℂ × RealPlane₄) →L[ℝ] ℂ) (j : Fin 4) : ℂ :=
  L (0, Pi.single j 1)

/-- Restriction to the real coordinate factor is recovered from its actual
values on the four marked real unit vectors. -/
theorem real_apply_eq_sum (L : (ℂ × RealPlane₄) →L[ℝ] ℂ) (x : RealPlane₄) :
    L (0, x) = ∑ j : Fin 4, realCoefficient L j * (x j : ℂ) := by
  let R := L.comp (ContinuousLinearMap.inr ℝ ℂ RealPlane₄)
  have h : R x = ∑ j : Fin 4, x j • R (Pi.single j 1) := by
    conv_lhs => rw [pi_eq_sum_univ' x, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact R.map_smul _ _
  simpa only [R, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    realCoefficient, Complex.real_smul, mul_comm] using h

/-- The actual base restriction and the four marked real values give the
full real-linear covector. -/
theorem apply_eq_base_add_real (L : (ℂ × RealPlane₄) →L[ℝ] ℂ)
    (s : ℂ) (x : RealPlane₄) :
    L (s, x) = L (s, 0) + ∑ j : Fin 4, realCoefficient L j * (x j : ℂ) := by
  have hpair : (s, x) = (s, (0 : RealPlane₄)) + (0, x) := by simp
  rw [hpair, map_add, real_apply_eq_sum]

/-- Decomposition after composition with an actual real-linear map whose
base component is the original base projection. -/
theorem comp_graph_decomposition (L : (ℂ × RealPlane₄) →L[ℝ] ℂ)
    (A : Model →L[ℝ] RealPlane₄) :
    L.comp ((ContinuousLinearMap.fst ℝ ℂ ComplexPlane₂).prod A) =
      L.comp ((ContinuousLinearMap.fst ℝ ℂ ComplexPlane₂).prod
        (0 : Model →L[ℝ] RealPlane₄)) +
      ∑ j : Fin 4, realCoefficient L j •
        Complex.ofRealCLM.comp ((ContinuousLinearMap.proj j).comp A) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_fst', zero_apply, add_apply, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply,
    Complex.ofRealCLM_apply, smul_eq_mul]
  exact apply_eq_base_add_real L v.1 (A v)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Pullback
