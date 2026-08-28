import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDoublePuncturedDbarOneLocal
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDoublePuncturedDbarOneApproximation
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationDbarAnalytic

/-!
# The actual finite Laurent correction step on `(ℂ*)²`

The difference of successive local primitives is analytic on the common
larger product of annuli. Its proved finite Laurent approximation
corrects the next primitive without changing either coordinate ∂̄.
-/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarOne

open PeriodTorusLineBundleClassification

def IsPrimitiveStage (f g : ℂ × ℂ → ℂ) (n : ℕ) (u : ℂ × ℂ → ℂ) : Prop :=
  ContDiffOn ℝ ∞ u domain ∧ ∀ q ∈ primitiveStageSet n,
    dbarFirst u q = f q ∧ dbarSecond u q = g q

theorem exists_primitiveStage {f g : ℂ × ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f domain) (hg : ContDiffOn ℝ ∞ g domain)
    (hclosed : ∀ q ∈ domain, dbarFirst g q = dbarSecond f q) (n : ℕ) :
    ∃ u, IsPrimitiveStage f g n u := by
  obtain ⟨u, hu, hdu⟩ := exists_smooth_primitive_on_annularClosed hf hg hclosed
    ((n : ℝ) + 3) (by positivity)
  exact ⟨u, hu.contDiffOn, hdu⟩

theorem primitiveStage_successor {f g : ℂ × ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f domain) (hg : ContDiffOn ℝ ∞ g domain)
    (hclosed : ∀ q ∈ domain, dbarFirst g q = dbarSecond f q)
    (n : ℕ) (u : ℂ × ℂ → ℂ) (hu : IsPrimitiveStage f g n u) :
    ∃ v, IsPrimitiveStage f g (n + 1) v ∧
      ∀ q ∈ annularClosed ((n : ℝ) + 2), ‖v q - u q‖ < (1 / 2 : ℝ) ^ n := by
  obtain ⟨w, hw⟩ := exists_primitiveStage hf hg hclosed (n + 1)
  let V : Set (ℂ × ℂ) := annularOpen ((n : ℝ) + 3)
  have hV : IsOpen V := isOpen_annularOpen _
  have hVs : V ⊆ primitiveStageSet n := annularOpen_subset_closed _
  have hVs' : V ⊆ primitiveStageSet (n + 1) :=
    hVs.trans (monotone_primitiveStageSet (Nat.le_succ n))
  have hVd : V ⊆ domain := hVs.trans (primitiveStageSet_subset_domain n)
  have hdiff : AnalyticOnNhd ℂ (fun q => w q - u q) V := by
    apply analyticOnNhd_sub_of_coordinate_dbar_eq hV
      ((hw.1.differentiableOn (by simp)).mono hVd)
      ((hu.1.differentiableOn (by simp)).mono hVd)
    · intro q hq
      exact (hw.2 q (hVs' hq)).1.trans (hu.2 q (hVs hq)).1.symm
    · intro q hq
      exact (hw.2 q (hVs' hq)).2.trans (hu.2 q (hVs hq)).2.symm
  obtain ⟨P, _, hP, herr⟩ := exists_laurent_polynomial_approximation
    (r := (n : ℝ) + 2) (R := (n : ℝ) + 3) (ε := (1 / 2 : ℝ) ^ n)
    (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith) (by positivity) hdiff
  have hPc : ContDiffOn ℂ ∞ P domain := hP.contDiffOn_of_completeSpace
  have hPr : ContDiffOn ℝ ∞ P domain := hPc.restrict_scalars ℝ
  have hPzero (q : ℂ × ℂ) (hq : q ∈ domain) :
      dbarFirst P q = 0 ∧ dbarSecond P q = 0 :=
    coordinate_dbar_zero_of_analyticAt (hP q hq)
  refine ⟨fun q => w q - P q, ⟨hw.1.sub hPr, ?_⟩, ?_⟩
  · intro q hq
    have hqd := primitiveStageSet_subset_domain (n + 1) hq
    have hwd : DifferentiableAt ℝ w q :=
      (hw.1.differentiableOn (by simp) q hqd).differentiableAt (isOpen_domain.mem_nhds hqd)
    have hPd : DifferentiableAt ℝ P q :=
      (hPr.differentiableOn (by simp) q hqd).differentiableAt (isOpen_domain.mem_nhds hqd)
    constructor
    · rw [dbarFirst_sub hwd hPd, (hPzero q hqd).1, sub_zero]
      exact (hw.2 q hq).1
    · rw [dbarSecond_sub hwd hPd, (hPzero q hqd).2, sub_zero]
      exact (hw.2 q hq).2
  · intro q hq
    dsimp only
    rw [show (w q - P q) - u q = -(P q - (w q - u q)) by ring, norm_neg]
    exact herr q hq

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarOne
