import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisCoefficients

/-!
# Local Leibniz recursion for the original derivative words

Equality on the original open base is preserved by each actual real
directional-derivative word. Appending one direction to a word therefore
gives a literal two-term Leibniz recursion for a product. Derivatives are
never reordered, and no smooth extension across the base boundary is used.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis

open FourierParameter

variable {U : Opens ℂ} {f g : ℂ → ℂ}

/-- The original word operator depends only on the function in the original open. -/
theorem word_congr_eqOn (hfg : Set.EqOn f g U) (s : List ℂ) :
    Set.EqOn (iteratedDirectionalDerivativeList s f)
      (iteratedDirectionalDerivativeList s g) U := by
  induction s with
  | nil => exact hfg
  | cons v s ih =>
    intro z hz
    have hnear : iteratedDirectionalDerivativeList s f =ᶠ[𝓝 z]
        iteratedDirectionalDerivativeList s g :=
      Filter.mem_of_superset (U.isOpen.mem_nhds hz) (fun _ hy => ih hy)
    exact congrArg (fun A : ℂ →L[ℝ] ℂ => A v) hnear.fderiv_eq

/-- The actual real product rule inside the original base open. -/
theorem baseDiff_mul_eqOn (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (v : ℂ) :
    Set.EqOn (fun z => fderiv ℝ (fun y => f y * g y) z v)
      (fun z => fderiv ℝ f z v * g z + f z * fderiv ℝ g z v) U := by
  intro z hz
  have hdf := (hf.contDiffAt (U.isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hdg := (hg.contDiffAt (U.isOpen.mem_nhds hz)).differentiableAt (by simp)
  change fderiv ℝ (fun y => f y * g y) z v =
    fderiv ℝ f z v * g z + f z * fderiv ℝ g z v
  rw [fderiv_fun_mul hdf hdg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Appending a direction gives the finite-word Leibniz recursion, locally on the base. -/
theorem word_append_mul_eqOn (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (s : List ℂ) (v : ℂ) :
    Set.EqOn (iteratedDirectionalDerivativeList (s ++ [v]) (fun z => f z * g z))
      (fun z =>
        iteratedDirectionalDerivativeList s (fun y => fderiv ℝ f y v * g y) z +
        iteratedDirectionalDerivativeList s (fun y => f y * fderiv ℝ g y v) z) U := by
  have hdf : ContDiffOn ℝ ∞ (fun y => fderiv ℝ f y v) U :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen U.isOpen).mp hf).2.clm_apply contDiffOn_const
  have hdg : ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y v) U :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen U.isOpen).mp hg).2.clm_apply contDiffOn_const
  rw [word_append]
  exact (word_congr_eqOn (baseDiff_mul_eqOn hf hg v) s).trans
    (word_add_eqOn (hdf.mul hg) (hf.mul hdg) s)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis
