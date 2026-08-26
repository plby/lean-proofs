import ErdosProblems.Erdos1038.TaoUpperCaseOneContradiction
import ErdosProblems.Erdos1038.TaoUpperCaseTwoQuantile
import ErdosProblems.Erdos1038.TaoUpperCaseThreeQuantile
import ErdosProblems.Erdos1038.TaoUpperEndpointReduction

/-!
# Assembly of Tao's three upper-bound parameter ranges

All three cases are discharged by their compiled quantile contradictions.
Together they give the sharp left-endpoint control and hence every exact
upper-extremum clause of `MainTheorem` unconditionally.
-/

open scoped ENNReal
open Polynomial Set

namespace Erdos1038

noncomputable section

/-- The already-closed Cases 1 and 2 reduce the full endpoint theorem to
the middle Case 3 interval. -/
theorem taoSharpLeftEndpointControl_of_caseThree
    (hcaseThree : ∀ {f : Polynomial ℝ} (hf : IsAdmissible f),
      closedUnitSublevelLeft f hf < -Real.sqrt 2 →
      ENNReal.ofReal taoUpperEdge ≤ sublevelVolume f →
      taoNormalizedCenter f hf ∈
        Icc taoCaseThreeCenterFloor taoCaseThreeCenterCeiling → False) :
    TaoSharpLeftEndpointControl := by
  intro f hf hvolume
  apply le_of_not_gt
  intro hfarLeft
  let t0 := taoNormalizedCenter f hf
  by_cases hcaseOne : t0 < taoCaseOneCeiling
  · obtain ⟨Q, hQleft, hQupper, hQF, _⟩ :=
      exists_closedTarget_quantileData_of_le hf hfarLeft hvolume
    have hQF' : Q.F =
        volumeCumulative (taoNormalizedRightTarget f hf) Q.left := by
      rw [hQleft]
      exact hQF
    exact false_of_tao_case_one_quantile Q f hf hfarLeft
      (by simpa [t0] using! hcaseOne) hQleft hQupper hQF'
  · have hcaseThreeLower : taoCaseThreeCenterFloor ≤ t0 := by
      have hnotLower : taoCaseOneCeiling ≤ t0 := le_of_not_gt hcaseOne
      simpa [taoCaseOneCeiling, taoCaseThreeCenterFloor] using! hnotLower
    by_cases hcaseTwo : taoCaseTwoCenterFloor ≤ t0
    · exact false_of_taoCaseTwo_normalizedCenter hf hfarLeft hvolume
        (by simpa [t0] using! hcaseTwo)
    · have hcaseThreeUpper : t0 ≤ taoCaseThreeCenterCeiling := by
        have hupper : t0 ≤ taoCaseTwoCenterFloor := le_of_not_ge hcaseTwo
        simpa [taoCaseTwoCenterFloor, taoCaseThreeCenterCeiling] using! hupper
      exact hcaseThree hf hfarLeft hvolume
        (by simpa [t0] using!
          (show t0 ∈ Icc taoCaseThreeCenterFloor
              taoCaseThreeCenterCeiling from
            ⟨hcaseThreeLower, hcaseThreeUpper⟩))

/-- Once the checked Case 3 contradiction is supplied, the full sharp
upper value and equality classification follow immediately. -/
theorem mainTheorem_upper_clauses_of_caseThree
    (hcaseThree : ∀ {f : Polynomial ℝ} (hf : IsAdmissible f),
      closedUnitSublevelLeft f hf < -Real.sqrt 2 →
      ENNReal.ofReal taoUpperEdge ≤ sublevelVolume f →
      taoNormalizedCenter f hf ∈
        Icc taoCaseThreeCenterFloor taoCaseThreeCenterCeiling → False) :
    supremumLength = ENNReal.ofReal (2 * Real.sqrt 2) ∧
    (∀ m : ℕ, 0 < m →
      IsAdmissible ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ m) ∧
      sublevelVolume ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ m) =
        ENNReal.ofReal (2 * Real.sqrt 2)) ∧
    (∀ f : Polynomial ℝ, IsAdmissible f →
      (sublevelVolume f = ENNReal.ofReal (2 * Real.sqrt 2) ↔
        ∃ m : ℕ, 0 < m ∧ f = (Polynomial.X ^ 2 - 1) ^ m)) :=
  mainTheorem_upper_clauses_of_taoSharpLeftEndpointControl
    (taoSharpLeftEndpointControl_of_caseThree hcaseThree)

/-- Tao's three checked trial-measure cases rule out every far-left
counterexample at the sharp volume threshold. -/
theorem taoSharpLeftEndpointControl : TaoSharpLeftEndpointControl := by
  apply taoSharpLeftEndpointControl_of_caseThree
  intro f hf hfarLeft hvolume hcaseThree
  exact false_of_taoCaseThree_normalizedCenter hf hfarLeft hvolume
    hcaseThree.1 hcaseThree.2

/-- The sharp upper value, the extremizing family, and the complete equality
classification, with no remaining analytic hypotheses. -/
theorem mainTheorem_upper_clauses :
    supremumLength = ENNReal.ofReal (2 * Real.sqrt 2) ∧
    (∀ m : ℕ, 0 < m →
      IsAdmissible ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ m) ∧
      sublevelVolume ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ m) =
        ENNReal.ofReal (2 * Real.sqrt 2)) ∧
    (∀ f : Polynomial ℝ, IsAdmissible f →
      (sublevelVolume f = ENNReal.ofReal (2 * Real.sqrt 2) ↔
        ∃ m : ℕ, 0 < m ∧ f = (Polynomial.X ^ 2 - 1) ^ m)) :=
  mainTheorem_upper_clauses_of_taoSharpLeftEndpointControl
    taoSharpLeftEndpointControl

end

end Erdos1038
