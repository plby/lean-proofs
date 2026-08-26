import ErdosProblems.Erdos1038.PlatformPoissonIntegral

/-!
# Normalized angular densities for the circle block

The circle rearrangement uses the reference and adjoint angular densities
after division by their values at `π`.  Their monotonicity makes the
normalized functions lie in `[0,1]`; their total integrals give the exact
mass conversion factors used in equation (5.1) of the manuscript.
-/

open Set

namespace Erdos1038

noncomputable section

def platformNormalizedReferenceDensity (k a θ : ℝ) : ℝ :=
  platformAngularDensity k a θ / platformAPi k a

def platformNormalizedAdjointDensity
    (a xMinus xPlus sigmaMinus sigmaPlus θ : ℝ) : ℝ :=
  platformAngularAdjointDensity
    a xMinus xPlus sigmaMinus sigmaPlus θ /
      platformBPi a xMinus xPlus sigmaMinus sigmaPlus

@[simp]
theorem platformNormalizedReferenceDensity_pi
    {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a ≤ 2) :
    platformNormalizedReferenceDensity k a Real.pi = 1 := by
  unfold platformNormalizedReferenceDensity platformAPi
  exact div_self (platformAPi_pos hk ha ha2).ne'

@[simp]
theorem platformNormalizedAdjointDensity_pi
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (ha2 : a < 2) :
    platformNormalizedAdjointDensity
      a xMinus xPlus sigmaMinus sigmaPlus Real.pi = 1 := by
  unfold platformNormalizedAdjointDensity platformBPi
  exact div_self
    (platformBPi_pos hxMinus hxPlus hsigmaMinus hsigmaPlus ha2).ne'

theorem platformNormalizedReferenceDensity_mem_Icc
    {k a θ : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a ≤ 2)
    (hthreshold : platformThreshold k ≤ a) (hθ : θ ∈ Icc 0 Real.pi) :
    platformNormalizedReferenceDensity k a θ ∈ Icc 0 1 := by
  have hapi : 0 < platformAPi k a := platformAPi_pos hk ha ha2
  have hnonneg := platformAngularDensity_nonneg
    hk ha ha2 hthreshold hθ
  have hle : platformAngularDensity k a θ ≤ platformAPi k a := by
    exact platformAngularDensity_monoOn hk ha ha2 hθ
      ⟨Real.pi_pos.le, le_rfl⟩ hθ.2
  unfold platformNormalizedReferenceDensity
  exact ⟨div_nonneg hnonneg hapi.le, (div_le_one hapi).2 hle⟩

theorem platformNormalizedAdjointDensity_mem_Icc
    {a xMinus xPlus sigmaMinus sigmaPlus θ : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (ha2 : a < 2) (hθ : θ ∈ Icc 0 Real.pi) :
    platformNormalizedAdjointDensity
      a xMinus xPlus sigmaMinus sigmaPlus θ ∈ Icc 0 1 := by
  have hbpi : 0 < platformBPi
      a xMinus xPlus sigmaMinus sigmaPlus :=
    platformBPi_pos hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
  have hnonneg := platformAngularAdjointDensity_nonneg
    hxMinus hxPlus hsigmaMinus hsigmaPlus ha2 hθ
  have hle : platformAngularAdjointDensity
      a xMinus xPlus sigmaMinus sigmaPlus θ ≤
      platformBPi a xMinus xPlus sigmaMinus sigmaPlus := by
    exact (platformAngularAdjointDensity_strictMonoOn
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2).monotoneOn hθ
        ⟨Real.pi_pos.le, le_rfl⟩ hθ.2
  unfold platformNormalizedAdjointDensity
  exact ⟨div_nonneg hnonneg hbpi.le, (div_le_one hbpi).2 hle⟩

theorem platformNormalizedReferenceDensity_monoOn
    {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a ≤ 2) :
    MonotoneOn (platformNormalizedReferenceDensity k a)
      (Icc 0 Real.pi) := by
  have hapi : 0 < platformAPi k a := platformAPi_pos hk ha ha2
  intro θ hθ φ hφ hθφ
  unfold platformNormalizedReferenceDensity
  exact div_le_div_of_nonneg_right
    (platformAngularDensity_monoOn hk ha ha2 hθ hφ hθφ) hapi.le

theorem platformNormalizedAdjointDensity_strictMonoOn
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (ha2 : a < 2) :
    StrictMonoOn
      (platformNormalizedAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus) (Icc 0 Real.pi) := by
  have hbpi : 0 < platformBPi
      a xMinus xPlus sigmaMinus sigmaPlus :=
    platformBPi_pos hxMinus hxPlus hsigmaMinus hsigmaPlus ha2
  intro θ hθ φ hφ hθφ
  unfold platformNormalizedAdjointDensity
  exact div_lt_div_of_pos_right
    (platformAngularAdjointDensity_strictMonoOn
      hxMinus hxPlus hsigmaMinus hsigmaPlus ha2 hθ hφ hθφ) hbpi

lemma intervalIntegrable_platformNormalizedReferenceDensity
    (k : ℝ) {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 2) :
    IntervalIntegrable (platformNormalizedReferenceDensity k a)
      MeasureTheory.volume 0 Real.pi := by
  unfold platformNormalizedReferenceDensity
  exact (intervalIntegrable_platformAngularDensity k ha ha2).div_const
    (platformAPi k a)

lemma intervalIntegrable_platformNormalizedAdjointDensity
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (ha2 : a < 2) :
    IntervalIntegrable
      (platformNormalizedAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus)
      MeasureTheory.volume 0 Real.pi := by
  unfold platformNormalizedAdjointDensity
  exact (intervalIntegrable_platformAngularAdjointDensity
    hxMinus hxPlus ha2).div_const
      (platformBPi a xMinus xPlus sigmaMinus sigmaPlus)

theorem integral_platformNormalizedReferenceDensity
    (k : ℝ) {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 2) :
    (∫ θ in 0..Real.pi, platformNormalizedReferenceDensity k a θ) =
      Real.pi / platformAPi k a := by
  unfold platformNormalizedReferenceDensity
  rw [intervalIntegral.integral_div, integral_platformAngularDensity k ha ha2]

theorem integral_platformNormalizedAdjointDensity
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (ha2 : a < 2) :
    (∫ θ in 0..Real.pi,
        platformNormalizedAdjointDensity
          a xMinus xPlus sigmaMinus sigmaPlus θ) =
      Real.pi * platformAdjointMass
          a xMinus xPlus sigmaMinus sigmaPlus /
        platformBPi a xMinus xPlus sigmaMinus sigmaPlus := by
  unfold platformNormalizedAdjointDensity
  rw [intervalIntegral.integral_div,
    integral_platformAngularAdjointDensity hxMinus hxPlus ha2]

end

end Erdos1038
