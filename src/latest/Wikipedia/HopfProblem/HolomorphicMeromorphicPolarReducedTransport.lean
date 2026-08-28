import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarIsolatedGerms
import Wikipedia.HopfProblem.AnalyticGermsFactorialCoordinates

/-!
# Isolated common zeros and actual linear coordinate changes

Isolation of common zeros is stated for every pair of analytic representatives
of the specified actual germs. An actual coordinate-power germ relation proves
this property. It is preserved when undoing a genuine linear coordinate change,
by composing representatives with that change and pulling the resulting
neighborhood back along the inverse map.
-/

open Set Filter Topology

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarReduced

open CuspNormalization.Germs CuspNormalization.Germs.CoordinateDivision
open CuspNormalization.Germs.Coordinates

/-- Any analytic representatives of these actual germs have no nearby common
zero except possibly the origin. -/
def IsolatedCommonZero (a b : O₂) : Prop :=
  ∀ (f g : ℂ × ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0),
    ofAnalytic f hf = a → ofAnalytic g hg = b →
      ∀ᶠ z in 𝓝 (0 : ℂ × ℂ), f z = 0 → g z = 0 → z = 0

/-- The coordinate-power relation isolates common zeros for all representatives. -/
theorem isolatedCommonZero_of_germ_relation
    {P Q A C U : O₂} {n : ℕ} (hU : IsUnit U)
    (hrel : A * P + C * Q = firstCoordinateGerm ^ n * U)
    (hQ : ¬ firstCoordinateGerm ∣ Q) : IsolatedCommonZero P Q := by
  intro f g hf hg hP hQrep
  exact PolarIsolated.eventually_common_zero_eq_zero_of_germ_relation
    hU hrel hQ hf hg hP hQrep

/-- The zero germ together with the constant-one germ has no common zeros. -/
theorem isolatedCommonZero_zero_one : IsolatedCommonZero 0 1 := by
  intro f g hf hg _ hgerm
  have hgone : g =ᶠ[𝓝 (0 : ℂ × ℂ)] (fun _ => 1) :=
    (ofAnalytic_eq_iff g (fun _ => 1) hg analyticAt_const).mp hgerm
  filter_upwards [hgone] with z hz
  intro _ hgzero
  exact False.elim (one_ne_zero (hz.symm.trans hgzero))

/-- Isolation of common zeros can be transported back through a genuine linear
coordinate change; no representative or coordinate-change coherence is assumed. -/
theorem isolatedCommonZero_of_linearPullback
    (e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ)) {a b : O₂}
    (h : IsolatedCommonZero (linearPullbackEquiv e a) (linearPullbackEquiv e b)) :
    IsolatedCommonZero a b := by
  intro f g hf hg hfa hgb
  have hfe : AnalyticAt ℂ (f ∘ e) 0 :=
    hf.comp_of_eq (e.analyticAt 0) (map_zero e)
  have hge : AnalyticAt ℂ (g ∘ e) 0 :=
    hg.comp_of_eq (e.analyticAt 0) (map_zero e)
  have hfa' : ofAnalytic (f ∘ e) hfe = linearPullbackEquiv e a := by
    rw [← hfa, linearPullbackEquiv_ofAnalytic]
  have hgb' : ofAnalytic (g ∘ e) hge = linearPullbackEquiv e b := by
    rw [← hgb, linearPullbackEquiv_ofAnalytic]
  have hlocal := h (f ∘ e) (g ∘ e) hfe hge hfa' hgb'
  have ht : Tendsto e.symm (𝓝 (0 : ℂ × ℂ)) (𝓝 (0 : ℂ × ℂ)) := by
    simpa only [map_zero] using e.symm.continuous.tendsto (0 : ℂ × ℂ)
  filter_upwards [ht.eventually hlocal] with z hz
  intro hfz hgz
  have hzero : e.symm z = 0 := hz (by simpa only [Function.comp_apply, e.apply_symm_apply]
    using hfz) (by simpa only [Function.comp_apply, e.apply_symm_apply] using hgz)
  simpa only [e.apply_symm_apply, map_zero] using congrArg e hzero

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarReduced
