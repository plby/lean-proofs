import ErdosProblems.Erdos783.GSContinuous
import ErdosProblems.Erdos783.GSExistence

namespace Erdos783

noncomputable section

/-- Granville--Soundararajan Proposition 6.1, discharged in every scale
range. -/
theorem gs_proposition61
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hsigma : IsGSSolution chi sigma) :
    GSProposition61 chi sigma :=
  gs_proposition61_estimate hchi hsigma

/-- The unconditional continuous extremal theorem underlying Hildebrand's
prime-only sieve estimate. -/
theorem gs_continuous_extremal
    {chi sigma : ℝ → ℝ} (hchi : IsGSKernel chi)
    (hsigma : IsGSSolution chi sigma) :
    ∀ u : ℝ, 0 ≤ u → dickmanRho (gsScale chi u) ≤ sigma u := by
  exact gs_continuous_extremal_of_section61 hchi hsigma
    (gs_oddBonferroni hchi hsigma) (gs_proposition61 hchi hsigma)

/-- Every admissible kernel has an explicit canonical solution, and that
solution satisfies the unconditional Granville--Soundararajan lower bound. -/
theorem gs_continuous_extremal_canonical
    {chi : ℝ → ℝ} (hchi : IsGSKernel chi) (u : ℝ) (hu : 0 ≤ u) :
    dickmanRho (gsScale chi u) ≤ gsCanonicalSolution chi u :=
  gs_continuous_extremal hchi
    (isGSSolution_gsCanonicalSolution hchi) u hu

end

end Erdos783
