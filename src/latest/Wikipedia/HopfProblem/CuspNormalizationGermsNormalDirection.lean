import Wikipedia.HopfProblem.CuspNormalizationGermsBasicDomain
import Wikipedia.HopfProblem.ToricCharts
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Pi

/-!
# A transverse line for a nonzero analytic germ

A nonzero analytic germ has a nonzero restriction to a complex line through
the origin. In dimension two an explicit invertible linear change of
coordinates makes that line the second coordinate axis. Both assertions
concern actual analytic functions and actual neighbourhood germs.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.CuspNormalization.Germs.NormalDirection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A nonzero analytic germ has a nonzero restriction to some nonzero
complex line. The identity principle is applied on a disk containing both
zero and one in the line parameter. -/
theorem exists_nonzero_line [Nontrivial E] {g : E → ℂ}
    (hg : AnalyticAt ℂ g 0) (hne : ¬ g =ᶠ[𝓝 0] 0) :
    ∃ v : E, v ≠ 0 ∧ ¬ (fun t : ℂ => g (t • v)) =ᶠ[𝓝 0] 0 := by
  classical
  by_cases hgzero : g 0 = 0
  · obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hg.eventually_analyticAt
    obtain ⟨v, hvball, hgv⟩ : ∃ v ∈ Metric.ball (0 : E) (r / 2), g v ≠ 0 := by
      by_contra hnone
      apply hne
      filter_upwards [Metric.ball_mem_nhds (0 : E) (by positivity : 0 < r / 2)] with v hv
      by_contra hgv
      exact hnone ⟨v, hv, hgv⟩
    have hv : v ≠ 0 := fun he => hgv (he ▸ hgzero)
    refine ⟨v, hv, ?_⟩
    intro hline
    have hvnorm : ‖v‖ < r / 2 := by simpa using hvball
    have hlineAnalytic : AnalyticOnNhd ℂ (fun t : ℂ => g (t • v))
        (Metric.ball 0 2) := by
      intro t ht
      have htnorm : ‖t‖ < 2 := by simpa using ht
      have htv : t • v ∈ Metric.ball (0 : E) r := by
        simp only [Metric.mem_ball, dist_zero_right, norm_smul]
        nlinarith [norm_nonneg t, norm_nonneg v]
      have hsmul : AnalyticAt ℂ (fun w : ℂ => w • v) t :=
        analyticAt_id.smul analyticAt_const
      exact AnalyticAt.comp (f := fun w : ℂ => w • v) (x := t) (hball htv) hsmul
    have hid := hlineAnalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      Metric.isPreconnected_ball (Metric.mem_ball_self (by norm_num)) hline
    have h := hid (by norm_num : (1 : ℂ) ∈ Metric.ball 0 2)
    exact hgv (by simpa using h)
  · obtain ⟨v, hv⟩ := exists_ne (0 : E)
    refine ⟨v, hv, ?_⟩
    intro hline
    exact hgzero (by simpa using hline.eq_of_nhds)

/-- An explicit triangular linear change of the two coordinates. -/
def triangularLinearEquiv (u v : ℂ) (hv : v ≠ 0) :
    (ℂ × ℂ) ≃ₗ[ℂ] (ℂ × ℂ) where
  toFun z := (z.1 + z.2 * u, z.2 * v)
  invFun z := (z.1 - z.2 / v * u, z.2 / v)
  left_inv z := by
    apply Prod.ext
    · dsimp
      field_simp
      ring
    · dsimp
      field_simp
  right_inv z := by
    apply Prod.ext
    · dsimp
      ring
    · dsimp
      field_simp
  map_add' z w := by
    apply Prod.ext <;> dsimp <;> ring
  map_smul' c z := by
    apply Prod.ext <;> dsimp <;> ring

@[simp] theorem triangularLinearEquiv_axis (u v : ℂ) (hv : v ≠ 0) (t : ℂ) :
    triangularLinearEquiv u v hv (0, t) = (t * u, t * v) := by
  simp [triangularLinearEquiv]

/-- Every nonzero vector in the two-dimensional coordinate space can be
the second column of a continuous complex-linear equivalence. -/
theorem exists_axis_equiv (v : ToricCharts.CoordinateSpace 2) (hv : v ≠ 0) :
    ∃ e : (ℂ × ℂ) ≃L[ℂ] ToricCharts.CoordinateSpace 2,
      ∀ t : ℂ, e (0, t) = t • v := by
  by_cases hv1 : v 1 ≠ 0
  · let e := (triangularLinearEquiv (v 0) (v 1) hv1).trans
      (LinearEquiv.finTwoArrow ℂ ℂ).symm
    refine ⟨e.toContinuousLinearEquiv, ?_⟩
    intro t
    funext i
    fin_cases i <;> simp [e, LinearEquiv.finTwoArrow, triangularLinearEquiv]
  · have hv0 : v 0 ≠ 0 := by
      intro hzero
      apply hv
      funext i
      fin_cases i <;> simp_all
    let e := ((triangularLinearEquiv (v 1) (v 0) hv0).trans
      (LinearEquiv.prodComm ℂ ℂ ℂ)).trans (LinearEquiv.finTwoArrow ℂ ℂ).symm
    refine ⟨e.toContinuousLinearEquiv, ?_⟩
    intro t
    funext i
    fin_cases i <;> simp [e, LinearEquiv.finTwoArrow, triangularLinearEquiv]

/-- A nonzero two-variable analytic germ becomes nonzero on the second
coordinate axis after a genuine continuous linear coordinate change. -/
theorem exists_coordinate_change_nonzero_line
    {g : ToricCharts.CoordinateSpace 2 → ℂ}
    (hg : AnalyticAt ℂ g 0) (hne : ¬ g =ᶠ[𝓝 0] 0) :
    ∃ e : (ℂ × ℂ) ≃L[ℂ] ToricCharts.CoordinateSpace 2,
      ¬ (fun t : ℂ => g (e (0, t))) =ᶠ[𝓝 0] 0 := by
  obtain ⟨v, hv, hline⟩ := exists_nonzero_line hg hne
  obtain ⟨e, he⟩ := exists_axis_equiv v hv
  exact ⟨e, by simpa only [he] using hline⟩

end Wikipedia.HopfProblem.CuspNormalization.Germs.NormalDirection
