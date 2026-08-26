import ErdosProblems.Erdos1038.PlatformReferenceQuantileContinuity

/-!
# Angular integral formula for the platform reference quantile

The canonical quantile is obtained by inverting normalized cumulative angular
mass.  This file records the corresponding change-of-variables formula: an
observable averaged uniformly in quantile space is the same observable
averaged against the normalized platform angular density.
-/

set_option warningAsError false

open MeasureTheory Set

namespace Erdos1038

noncomputable section

private lemma platformAngularDistance_pos_all
    {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 2) (theta : ℝ) :
    0 < platformAngularDistance a theta := by
  have hradius : 0 ≤ platformRadius a := by
    unfold platformRadius
    linarith
  have hmul : platformRadius a * Real.cos theta ≤ platformRadius a :=
    by simpa only [mul_one] using!
      mul_le_mul_of_nonneg_left (Real.cos_le_one theta) hradius
  have hlower : a ≤ platformAngularDistance a theta := by
    calc
      a = platformCenter a - platformRadius a :=
        (platformCenter_sub_radius a).symm
      _ ≤ platformCenter a - platformRadius a * Real.cos theta :=
        sub_le_sub_left hmul (platformCenter a)
      _ = platformAngularDistance a theta := rfl
  exact ha.trans_le hlower

private lemma continuous_platformAngularDensity_all
    (k : ℝ) {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 2) :
    Continuous (platformAngularDensity k a) := by
  have hdistance : Continuous (platformAngularDistance a) := by
    unfold platformAngularDistance
    fun_prop
  have hdistance_ne : ∀ theta : ℝ, platformAngularDistance a theta ≠ 0 :=
    fun theta ↦ (platformAngularDistance_pos_all ha ha2 theta).ne'
  unfold platformAngularDensity platformDensityCoefficient
  exact continuous_const.sub (continuous_const.div hdistance hdistance_ne)

lemma hasDerivAt_platformReferenceCumulative
    (k : ℝ) {a theta : ℝ} (ha : 0 < a) (ha2 : a ≤ 2) :
    HasDerivAt (platformReferenceCumulative k a)
      ((1 / Real.pi) * platformAngularDensity k a theta) theta := by
  have hdensity := continuous_platformAngularDensity_all k ha ha2
  have hprimitive : HasDerivAt
      (fun right ↦ ∫ phi : ℝ in 0..right,
        platformAngularDensity k a phi)
      (platformAngularDensity k a theta) theta :=
    intervalIntegral.integral_hasDerivAt_right
      (hdensity.intervalIntegrable 0 theta)
      hdensity.aestronglyMeasurable.stronglyMeasurableAtFilter
      hdensity.continuousAt
  simpa only [platformReferenceCumulative] using!
    hprimitive.const_mul (1 / Real.pi)

@[simp]
lemma platformReferenceQuantile_cumulativeMap
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (theta : Icc (0 : ℝ) Real.pi) :
    platformReferenceQuantile k a hk ha ha2 hthreshold
        (platformReferenceCumulativeMap k a hk ha ha2 hthreshold theta) =
      platformAngularDistance a theta := by
  unfold platformReferenceQuantile
  apply congrArg (platformAngularDistance a)
  simpa only [platformReferenceCutMap] using!
    congrArg Subtype.val
      (platformReferenceCutMap_leftInverse
        k a hk ha ha2 hthreshold theta)

/-- Integrating an observable of the canonical platform quantile against
uniform probability mass is the normalized angular-density integral. -/
theorem integral_platformReferenceQuantile_eq_angular
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (F : ℝ → ℝ) (hF : ContinuousOn F (Icc a 2)) :
    (∫ u in (0 : ℝ)..1,
        F (platformReferenceQuantile k a hk ha ha2 hthreshold
          (projIcc 0 1 zero_le_one u))) =
      (1 / Real.pi) *
        ∫ theta in (0 : ℝ)..Real.pi,
          platformAngularDensity k a theta *
            F (platformAngularDistance a theta) := by
  let G : ℝ → ℝ := fun u ↦
    F (platformReferenceQuantile k a hk ha ha2 hthreshold
      (projIcc 0 1 zero_le_one u))
  have hG : Continuous G := by
    have hquantile : Continuous (fun u : ℝ ↦
        platformReferenceQuantile k a hk ha ha2 hthreshold
          (projIcc 0 1 zero_le_one u)) :=
      (continuous_platformReferenceQuantile
        k a hk ha ha2 hthreshold).comp continuous_projIcc
    exact hF.comp_continuous hquantile fun u ↦
      platformReferenceQuantile_mem_Icc k a hk ha ha2 hthreshold
        (projIcc 0 1 zero_le_one u)
  have hdensity := continuous_platformAngularDensity_all k ha ha2.le
  have hderivative : ∀ theta ∈ Set.uIcc (0 : ℝ) Real.pi,
      HasDerivAt (platformReferenceCumulative k a)
        ((1 / Real.pi) * platformAngularDensity k a theta) theta :=
    fun theta _ ↦ hasDerivAt_platformReferenceCumulative k ha ha2.le
  have hderivativeContinuous : ContinuousOn
      (fun theta ↦ (1 / Real.pi) * platformAngularDensity k a theta)
      (Set.uIcc (0 : ℝ) Real.pi) :=
    (continuous_const.mul hdensity).continuousOn
  have hsubstitution := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := Real.pi)
    (f := platformReferenceCumulative k a)
    (f' := fun theta ↦ (1 / Real.pi) * platformAngularDensity k a theta)
    (g := G) hderivative hderivativeContinuous hG
  rw [platformReferenceCumulative_zero,
    platformReferenceCumulative_pi k ha ha2.le] at hsubstitution
  have hcompose (theta : ℝ) (htheta : theta ∈ Set.uIcc (0 : ℝ) Real.pi) :
      G (platformReferenceCumulative k a theta) =
        F (platformAngularDistance a theta) := by
    rw [uIcc_of_le Real.pi_pos.le] at htheta
    have hcumulative := platformReferenceCumulative_mem_Icc
      hk ha ha2 hthreshold htheta
    dsimp only [G]
    rw [projIcc_of_mem zero_le_one hcumulative]
    change F (platformReferenceQuantile k a hk ha ha2 hthreshold
      (platformReferenceCumulativeMap k a hk ha ha2 hthreshold
        ⟨theta, htheta⟩)) = _
    rw [platformReferenceQuantile_cumulativeMap]
  change (∫ u in (0 : ℝ)..1, G u) = _
  calc
    (∫ u in (0 : ℝ)..1, G u) =
        ∫ theta in (0 : ℝ)..Real.pi,
          (G ∘ platformReferenceCumulative k a) theta *
            ((1 / Real.pi) * platformAngularDensity k a theta) :=
      hsubstitution.symm
    _ = ∫ theta in (0 : ℝ)..Real.pi,
          (1 / Real.pi) *
            (platformAngularDensity k a theta *
              F (platformAngularDistance a theta)) := by
      apply intervalIntegral.integral_congr
      intro theta htheta
      change G (platformReferenceCumulative k a theta) *
          ((1 / Real.pi) * platformAngularDensity k a theta) = _
      rw [hcompose theta htheta]
      ring
    _ = (1 / Real.pi) *
        ∫ theta in (0 : ℝ)..Real.pi,
          platformAngularDensity k a theta *
            F (platformAngularDistance a theta) := by
      rw [intervalIntegral.integral_const_mul]

end

end Erdos1038
