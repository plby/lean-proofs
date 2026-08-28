import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsPullbackLinearBasic

/-!
# Antiholomorphic projection of the real-linear pullback decomposition

The projection is the native operator on the unchanged complex model.
No complex structure is assigned to the real coordinate target.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Pullback

open Complex HolomorphicDolbeaultThree
open scoped BigOperators

/-- The antiholomorphic part of the actual base restriction is its genuine
base coefficient times the original conjugate-base covector. -/
theorem antiPart_comp_base (L : (ℂ × RealPlane₄) →L[ℝ] ℂ) :
    antiPart (L.comp ((ContinuousLinearMap.fst ℝ ℂ ComplexPlane₂).prod
      (0 : Model →L[ℝ] RealPlane₄))) = baseCoefficient L • baseCovector.val := by
  let K := L.comp ((ContinuousLinearMap.fst ℝ ℂ ComplexPlane₂).prod
    (0 : Model →L[ℝ] RealPlane₄))
  let F : AntiCovector Model := ⟨antiPart K, antiPart_mem K⟩
  have h : F = baseCoefficient L • baseCovector := by
    apply antiCovector_ext
    · change antiPart K (1, 0) = baseCoefficient L * baseCovector.val (1, 0)
      simp [K, antiPart_apply, baseCoefficient, smul_eq_mul]
    · intro i
      change antiPart K (0, Pi.single i 1) =
        baseCoefficient L * baseCovector.val (0, Pi.single i 1)
      have hzero : L (0, (0 : RealPlane₄)) = 0 := L.map_zero
      simp [K, antiPart_apply, hzero]
  exact congrArg Subtype.val h

/-- Exact native antiholomorphic projection of the real-linear graph
pullback. This identity is subsequently applied to genuine Fréchet
derivatives of the original inverse-coordinate map. -/
theorem antiPart_comp_graph (L : (ℂ × RealPlane₄) →L[ℝ] ℂ)
    (A : Model →L[ℝ] RealPlane₄) :
    antiPart (L.comp ((ContinuousLinearMap.fst ℝ ℂ ComplexPlane₂).prod A)) =
      baseCoefficient L • baseCovector.val +
      ∑ j : Fin 4, realCoefficient L j •
        antiPart (Complex.ofRealCLM.comp ((ContinuousLinearMap.proj j).comp A)) := by
  rw [comp_graph_decomposition, antiPart_add, antiPart_comp_base]
  congr 1
  change antiPartLinear (∑ j : Fin 4, realCoefficient L j •
    Complex.ofRealCLM.comp ((ContinuousLinearMap.proj j).comp A)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact antiPart_complex_smul _ _

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Pullback
