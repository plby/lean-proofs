import ErdosProblems.Erdos421.BuchstabPrimeWeight

/-! # Regularity of a composed Buchstab prime weight -/

namespace Erdos421

theorem buchstabPrimeWeight_regular {X a b : ℝ} {F : ℝ → ℝ} (ha : 1 < a)
    (hF : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ F (logarithmicBuchstabArgument X t))
    (hF' : ContinuousOn (fun t ↦ deriv F (logarithmicBuchstabArgument X t)) (Set.Icc a b)) :
    (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (buchstabPrimeWeight X F) t) ∧
      ContinuousOn (deriv (buchstabPrimeWeight X F)) (Set.Icc a b) := by
  have hsub : Set.Icc a b ⊆ Set.Ioi 1 := fun t ht ↦ ha.trans_le ht.1
  have hcomp : ContinuousOn (fun t ↦ F (logarithmicBuchstabArgument X t)) (Set.Icc a b) := by
    intro t ht
    exact ((hF t ht).continuousAt.comp
      (logarithmicBuchstabArgument_hasDerivAt X (hsub ht)).continuousAt).continuousWithinAt
  have harg : ContinuousOn (fun t ↦ -Real.log X / (t * (Real.log t) ^ 2)) (Set.Icc a b) := by
    intro t ht
    have htp : 0 < t := by have ht1 : 1 < t := hsub ht; linarith
    have ht0 : t ≠ 0 := htp.ne'
    have hlog : 0 < Real.log t := Real.log_pos (hsub ht)
    have hden : t * (Real.log t) ^ 2 ≠ 0 := by positivity
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hrec : ContinuousOn (fun t ↦ -(Real.log t + 2) / (t ^ 2 * (Real.log t) ^ 3))
      (Set.Icc a b) := by
    intro t ht
    have htp : 0 < t := by have ht1 : 1 < t := hsub ht; linarith
    have ht0 : t ≠ 0 := htp.ne'
    have hlog : 0 < Real.log t := Real.log_pos (hsub ht)
    have hden : t ^ 2 * (Real.log t) ^ 3 ≠ 0 := by positivity
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  constructor
  · intro t ht
    exact (buchstabPrimeWeight_hasDerivAt (hsub ht) (hF t ht)).differentiableAt
  · have hc : ContinuousOn (fun t ↦ deriv F (logarithmicBuchstabArgument X t) *
          (-Real.log X / (t * (Real.log t) ^ 2)) * reciprocalLogSquare t +
        F (logarithmicBuchstabArgument X t) *
          (-(Real.log t + 2) / (t ^ 2 * (Real.log t) ^ 3))) (Set.Icc a b) :=
      ((hF'.mul harg).mul (reciprocalLogSquare_continuousOn.mono hsub)).add (hcomp.mul hrec)
    apply hc.congr
    intro t ht
    exact (buchstabPrimeWeight_hasDerivAt (hsub ht) (hF t ht)).deriv

end Erdos421
