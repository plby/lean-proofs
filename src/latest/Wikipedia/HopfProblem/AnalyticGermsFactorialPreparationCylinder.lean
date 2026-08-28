import Wikipedia.HopfProblem.CuspNormalizationGermsNormalCylinder

/-!
# An actual bidisc for preparation

An analytic function whose second-axis germ is nonzero admits a closed
bidisc on which it is analytic, with a zero-free boundary cylinder and no
possible zero of the central slice except the origin. All these conditions
are derived from local analyticity and analytic isolation of zeros.
-/

open Set Metric Filter Topology
open Wikipedia.HopfProblem.CuspNormalization.Germs

namespace Wikipedia.HopfProblem.AnalyticGermsFactorial.PreparationCylinder

/-- Choose an actual closed bidisc suitable for constructing a preparation
polynomial. The central slice has no nonzero roots in the entire closed disc. -/
theorem exists_preparation_cylinder {f : ℂ × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0)
    (hline : ¬ (fun w : ℂ => f (0, w)) =ᶠ[𝓝 0] 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ R : ℝ, 0 < R ∧
      AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) R) ∧
      (∀ p ∈ closedBall (0 : ℂ) r ×ˢ sphere (0 : ℂ) R, f p ≠ 0) ∧
      (∀ w ∈ closedBall (0 : ℂ) R, w ≠ 0 → f (0, w) ≠ 0) := by
  have haxis : AnalyticAt ℂ (fun w : ℂ => f (0, w)) 0 :=
    hf.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hpunctured := haxis.eventually_eq_zero_or_eventually_ne_zero.resolve_left hline
  have hisolated : ∀ᶠ w in 𝓝 (0 : ℂ), w ≠ 0 → f (0, w) ≠ 0 := by
    simpa only [eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff]
      using hpunctured
  have hlocal : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ),
      AnalyticAt ℂ f p ∧ (p.2 ≠ 0 → f (0, p.2) ≠ 0) :=
    hf.eventually_analyticAt.and
      ((continuous_snd.tendsto (0 : ℂ × ℂ)).eventually hisolated)
  obtain ⟨r, hr, R, hR, hlocal, hboundary⟩ :=
    NormalCylinder.exists_zero_free_cylinder hf hline hlocal
  refine ⟨r, hr, R, hR, fun p hp => (hlocal p hp).1, hboundary, ?_⟩
  intro w hw
  exact (hlocal (0, w) ⟨mem_closedBall_self hr.le, hw⟩).2

end Wikipedia.HopfProblem.AnalyticGermsFactorial.PreparationCylinder
