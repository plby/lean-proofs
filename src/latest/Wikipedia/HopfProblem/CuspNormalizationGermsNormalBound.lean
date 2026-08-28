import Wikipedia.HopfProblem.CuspNormalizationGermsNormalBoundFunctions
import Wikipedia.HopfProblem.CuspNormalizationGermsNormalBoundRoots

/-!
# Local boundedness of integral fractions of actual analytic germs

An integral fraction satisfies a monic relation with actual analytic
coefficients on one common neighbourhood.  The locally uniform Cauchy
bound for that relation bounds the actual quotient away from its
denominator's zero set.  Analytic extension across that zero set is a
separate statement and is not assumed here.
-/

noncomputable section

open Set Filter Topology Polynomial

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {a : E} {f g : E → ℂ}

/-- A fraction integral over the actual analytic-germ ring is locally
bounded off the zero set of its actual analytic denominator. -/
theorem exists_pos_eventually_norm_div_le_off_zero_of_isIntegral
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a)
    (hgerm : ofAnalytic g hg ≠ 0)
    (hint : IsIntegral (AnalyticGerm a)
      (algebraMap (AnalyticGerm a) (FractionRing (AnalyticGerm a)) (ofAnalytic f hf) /
        algebraMap (AnalyticGerm a) (FractionRing (AnalyticGerm a)) (ofAnalytic g hg))) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ z in 𝓝 a, g z ≠ 0 → ‖f z / g z‖ ≤ M := by
  obtain ⟨q, hq, hroot⟩ := exists_monic_eventually_isRoot_div hf hg hgerm hint
  obtain ⟨M, hM, hbound⟩ := exists_pos_eventually_root_norm_le
    (fun z => q.map (analyticFunctionEval a z)) q.natDegree
    (fun z => hq.map (analyticFunctionEval a z))
    (fun z => (hq.natDegree_map (analyticFunctionEval a z)).le)
    (by
      intro i _
      simpa only [Polynomial.coeff_map, analyticFunctionEval_apply] using
        (q.coeff i).property.continuousAt)
  refine ⟨M, hM, ?_⟩
  filter_upwards [hroot, hbound] with z hz hb hgz
  exact hb (f z / g z) (hz hgz)

/-- The total complex quotient is bounded as well: its value where the
denominator vanishes is zero under Lean's field convention. -/
theorem exists_pos_eventually_norm_div_le_of_isIntegral
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a)
    (hgerm : ofAnalytic g hg ≠ 0)
    (hint : IsIntegral (AnalyticGerm a)
      (algebraMap (AnalyticGerm a) (FractionRing (AnalyticGerm a)) (ofAnalytic f hf) /
        algebraMap (AnalyticGerm a) (FractionRing (AnalyticGerm a)) (ofAnalytic g hg))) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ z in 𝓝 a, ‖f z / g z‖ ≤ M := by
  obtain ⟨M, hM, hbound⟩ :=
    exists_pos_eventually_norm_div_le_off_zero_of_isIntegral hf hg hgerm hint
  refine ⟨M, hM, ?_⟩
  filter_upwards [hbound] with z hz
  by_cases hgz : g z = 0
  · simpa only [hgz, div_zero, norm_zero] using hM.le
  · exact hz hgz

/-- On a common neighbourhood, an integral analytic-germ fraction is
analytic wherever its denominator is nonzero and has a uniform norm bound. -/
theorem exists_pos_eventually_analyticAt_div_and_norm_le_of_isIntegral
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a)
    (hgerm : ofAnalytic g hg ≠ 0)
    (hint : IsIntegral (AnalyticGerm a)
      (algebraMap (AnalyticGerm a) (FractionRing (AnalyticGerm a)) (ofAnalytic f hf) /
        algebraMap (AnalyticGerm a) (FractionRing (AnalyticGerm a)) (ofAnalytic g hg))) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ z in 𝓝 a, g z ≠ 0 →
      AnalyticAt ℂ (fun w => f w / g w) z ∧ ‖f z / g z‖ ≤ M := by
  obtain ⟨M, hM, hbound⟩ :=
    exists_pos_eventually_norm_div_le_off_zero_of_isIntegral hf hg hgerm hint
  refine ⟨M, hM, ?_⟩
  filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt, hbound]
    with z hfz hgz hz hgz0
  exact ⟨hfz.div hgz hgz0, hz hgz0⟩

end Wikipedia.HopfProblem.CuspNormalization.Germs
