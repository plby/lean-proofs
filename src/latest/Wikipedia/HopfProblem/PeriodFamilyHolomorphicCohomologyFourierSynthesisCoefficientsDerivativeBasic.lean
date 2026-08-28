import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisCoefficientsBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisCoefficientsWords

/-!
# Base derivatives and zero smooth rapidly decreasing coefficients

A further real base derivative preserves the original coefficient condition.
Its majorant is the already proved majorant for the word with that direction
appended on the right, retaining the original tail-first order. The zero
coefficient family also satisfies the condition with the literal zero majorant.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis

open FourierParameter

local notation "word" => iteratedDirectionalDerivativeList

variable {U : Opens ℂ} {c : Coefficients}

/-- An additional base derivative preserves genuine local smoothness and all
compact-uniform weighted majorants, without commuting derivative directions. -/
theorem SmoothRapidCoefficients.baseDiff (hc : SmoothRapidCoefficients U c) (v : ℂ) :
    SmoothRapidCoefficients U (baseDiff v c) where
  smooth k :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen U.isOpen).mp (hc.smooth k)).2.clm_apply
      contDiffOn_const
  majorant := by
    intro s K hK r
    obtain ⟨u, hu, hsum, hbound⟩ := hc.majorant (s ++ [v]) K hK r
    refine ⟨u, hu, hsum, ?_⟩
    intro b hb k
    have hword : word (s ++ [v]) (c k) = word s (FourierSynthesis.baseDiff v c k) :=
      word_append s [v] (c k)
    rw [← hword]
    exact hbound b hb k

/-- Every literal real directional-derivative word annihilates the zero function. -/
@[simp] theorem word_zero (s : List ℂ) :
    word s (fun _ : ℂ => 0) = fun _ => 0 := by
  induction s with
  | nil => rfl
  | cons v s ih =>
    change (fun z => fderiv ℝ (word s (fun _ : ℂ => 0)) z v) = fun _ => 0
    rw [ih]
    funext z
    simp only [fderiv_const_apply, zero_apply]

/-- The literal zero coefficient family has the literal zero summable majorant. -/
theorem SmoothRapidCoefficients.zero (U : Opens ℂ) :
    SmoothRapidCoefficients U (0 : Coefficients) where
  smooth _ := contDiffOn_const
  majorant := by
    intro s K _ r
    refine ⟨0, fun _ => le_rfl, summable_zero, ?_⟩
    intro b _ k
    change _ * ‖word s (fun _ : ℂ => 0) (b : ℂ)‖ ≤ (0 : ℝ)
    simp only [word_zero, norm_zero, mul_zero, le_refl]

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis
