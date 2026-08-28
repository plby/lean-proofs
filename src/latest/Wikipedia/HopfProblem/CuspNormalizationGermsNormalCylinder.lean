import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Complex.Basic

/-!
# A zero-free boundary cylinder for an analytic denominator

A denominator with a nonzero germ on the second coordinate axis has no
zeros on a sufficiently small circle in that axis. Compactness of this
circle makes its nonvanishing uniform in the first coordinate. The
resulting closed bidisc can be chosen inside any prescribed neighbourhood
of the origin; in particular, it preserves a local bound for a quotient.
-/

noncomputable section

open Set Filter Topology Metric

namespace Wikipedia.HopfProblem.CuspNormalization.Germs.NormalCylinder

/-- A nonzero analytic line germ has a zero-free small circle. The radius
can be chosen below any prescribed positive upper bound. -/
theorem exists_zero_free_circle {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0)
    (hne : ¬ g =ᶠ[𝓝 0] 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ R ≤ ε ∧ ∀ t ∈ sphere (0 : ℂ) R, g t ≠ 0 := by
  have hpunctured := hg.eventually_eq_zero_or_eventually_ne_zero.resolve_left hne
  have hnear : ∀ᶠ t in 𝓝 (0 : ℂ), t ≠ 0 → g t ≠ 0 := by
    simpa only [eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff] using hpunctured
  obtain ⟨δ, hδ, hδne⟩ := nhds_basis_closedBall.mem_iff.mp hnear
  refine ⟨min ε δ, lt_min hε hδ, min_le_left _ _, ?_⟩
  intro t ht
  exact hδne (closedBall_subset_closedBall (min_le_right _ _) (sphere_subset_closedBall ht))
    (ne_of_mem_sphere ht (ne_of_gt (lt_min hε hδ)))

/-- A small closed bidisc lies in any prescribed neighbourhood predicate,
while the denominator has no zeros on its entire boundary cylinder.
Nonvanishing on that cylinder is proved, not assumed. -/
theorem exists_zero_free_cylinder {g : ℂ × ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0)
    (hline : ¬ (fun t : ℂ => g (0, t)) =ᶠ[𝓝 0] 0)
    {P : ℂ × ℂ → Prop} (hP : ∀ᶠ z in 𝓝 (0 : ℂ × ℂ), P z) :
    ∃ r : ℝ, 0 < r ∧ ∃ R : ℝ, 0 < R ∧
      (∀ z ∈ closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) R, P z) ∧
      (∀ z ∈ closedBall (0 : ℂ) r ×ˢ sphere (0 : ℂ) R, g z ≠ 0) := by
  have hlocal : ∀ᶠ z in 𝓝 (0 : ℂ × ℂ), AnalyticAt ℂ g z ∧ P z :=
    hg.eventually_analyticAt.and hP
  obtain ⟨ε, hε, hεlocal⟩ := nhds_basis_closedBall.mem_iff.mp hlocal
  have hgline : AnalyticAt ℂ (fun t : ℂ => g (0, t)) 0 :=
    hg.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  obtain ⟨R, hR, hRε, hRne⟩ := exists_zero_free_circle hgline hline hε
  have hzero : (0 : ℂ) ∈ closedBall (0 : ℂ) ε := mem_closedBall_self hε.le
  have hparameter : ∀ᶠ w in 𝓝 (0 : ℂ), ∀ t ∈ sphere (0 : ℂ) R, g (w, t) ≠ 0 := by
    apply (isCompact_sphere (0 : ℂ) R).eventually_forall_of_forall_eventually
    intro t ht
    have htε : t ∈ closedBall (0 : ℂ) ε :=
      closedBall_subset_closedBall hRε (sphere_subset_closedBall ht)
    have hzt : (0, t) ∈ closedBall (0 : ℂ × ℂ) ε := by
      rw [← closedBall_prod_same]
      exact ⟨hzero, htε⟩
    exact (hεlocal hzt).1.continuousAt.eventually_ne (hRne t ht)
  obtain ⟨η, hη, hηne⟩ := nhds_basis_closedBall.mem_iff.mp hparameter
  refine ⟨min ε η, lt_min hε hη, R, hR, ?_, ?_⟩
  · intro z hz
    apply (hεlocal ?_).2
    rw [← closedBall_prod_same]
    exact ⟨closedBall_subset_closedBall (min_le_left _ _) hz.1,
      closedBall_subset_closedBall hRε hz.2⟩
  · intro z hz
    exact hηne (closedBall_subset_closedBall (min_le_right _ _) hz.1) z.2 hz.2

/-- The analytic numerator and denominator, the quotient bound, and a
zero-free denominator on the boundary cylinder all hold on one actual
closed bidisc around the origin. -/
theorem exists_bounded_analytic_cylinder {f g : ℂ × ℂ → ℂ} {M : ℝ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hline : ¬ (fun t : ℂ => g (0, t)) =ᶠ[𝓝 0] 0)
    (hbound : ∀ᶠ z in 𝓝 (0 : ℂ × ℂ), g z ≠ 0 → ‖f z / g z‖ ≤ M) :
    ∃ r : ℝ, 0 < r ∧ ∃ R : ℝ, 0 < R ∧
      AnalyticOnNhd ℂ f (closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) R) ∧
      AnalyticOnNhd ℂ g (closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) R) ∧
      (∀ z ∈ closedBall (0 : ℂ) r ×ˢ closedBall (0 : ℂ) R,
        g z ≠ 0 → ‖f z / g z‖ ≤ M) ∧
      (∀ z ∈ closedBall (0 : ℂ) r ×ˢ sphere (0 : ℂ) R, g z ≠ 0) := by
  have hlocal : ∀ᶠ z in 𝓝 (0 : ℂ × ℂ),
      AnalyticAt ℂ f z ∧ AnalyticAt ℂ g z ∧ (g z ≠ 0 → ‖f z / g z‖ ≤ M) := by
    filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt, hbound] with z hfz hgz hz
    exact ⟨hfz, hgz, hz⟩
  obtain ⟨r, hr, R, hR, hlocal, hboundary⟩ := exists_zero_free_cylinder hg hline hlocal
  exact ⟨r, hr, R, hR, fun z hz => (hlocal z hz).1,
    fun z hz => (hlocal z hz).2.1, fun z hz => (hlocal z hz).2.2, hboundary⟩

end Wikipedia.HopfProblem.CuspNormalization.Germs.NormalCylinder
