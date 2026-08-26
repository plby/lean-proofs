import ErdosProblems.Erdos1038.ConstantPlatformMeasure

/-!
# Monotonicity of the angular platform and adjoint densities

Both densities used in the circle comparison increase from the left endpoint
of the platform interval to the right endpoint.  The adjoint density vanishes
only at the left endpoint and is strictly positive thereafter.
-/

open Set

namespace Erdos1038

noncomputable section

theorem platformAngularDistance_strictMonoOn {a : ℝ} (ha2 : a < 2) :
    StrictMonoOn (platformAngularDistance a) (Icc 0 Real.pi) := by
  intro θ hθ φ hφ hθφ
  have hcos : Real.cos φ < Real.cos θ :=
    Real.strictAntiOn_cos hθ hφ hθφ
  have hr : 0 < platformRadius a := platformRadius_pos ha2
  unfold platformAngularDistance
  nlinarith [mul_pos hr (sub_pos.mpr hcos)]

theorem platformAngularDistance_monoOn {a : ℝ} (ha2 : a ≤ 2) :
    MonotoneOn (platformAngularDistance a) (Icc 0 Real.pi) := by
  rcases ha2.eq_or_lt with rfl | ha2
  · intro θ hθ φ hφ hθφ
    simp [platformAngularDistance, platformRadius]
  · exact (platformAngularDistance_strictMonoOn ha2).monotoneOn

theorem platformAngularDensity_monoOn {k a : ℝ}
    (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a ≤ 2) :
    MonotoneOn (platformAngularDensity k a) (Icc 0 Real.pi) := by
  intro θ hθ φ hφ hθφ
  apply platformDensityCoefficient_monoOn hk ha
  · exact Set.mem_Ici.mpr (platformAngularDistance_mem_Icc ha2 hθ).1
  · exact Set.mem_Ici.mpr (platformAngularDistance_mem_Icc ha2 hφ).1
  · exact platformAngularDistance_monoOn ha2 hθ hφ hθφ

def platformAPi (k a : ℝ) : ℝ :=
  platformAngularDensity k a Real.pi

theorem one_le_platformAPi {k a : ℝ} (hk : 0 ≤ k)
    (ha : 0 < a) (ha2 : a ≤ 2) :
    1 ≤ platformAPi k a := by
  have hsnonneg : 0 ≤ Real.sqrt (2 * a) := Real.sqrt_nonneg _
  have hsSq : (Real.sqrt (2 * a)) ^ 2 = 2 * a :=
    Real.sq_sqrt (by positivity)
  have hsle : Real.sqrt (2 * a) ≤ 2 := by
    nlinarith [sq_nonneg (Real.sqrt (2 * a) + 2)]
  have hscaled : k * Real.sqrt (2 * a) ≤ k * 2 :=
    mul_le_mul_of_nonneg_left hsle hk
  unfold platformAPi platformAngularDensity platformDensityCoefficient
  rw [platformAngularDistance_pi]
  nlinarith

theorem platformAPi_pos {k a : ℝ} (hk : 0 ≤ k)
    (ha : 0 < a) (ha2 : a ≤ 2) :
    0 < platformAPi k a :=
  zero_lt_one.trans_le (one_le_platformAPi hk ha ha2)

def platformAngularAdjointDensity
    (a xMinus xPlus sigmaMinus sigmaPlus θ : ℝ) : ℝ :=
  adjointNumerator a xMinus xPlus sigmaMinus sigmaPlus
    (platformAngularDistance a θ)

theorem platformAngularAdjointDensity_strictMonoOn
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (ha2 : a < 2) :
    StrictMonoOn
      (platformAngularAdjointDensity
        a xMinus xPlus sigmaMinus sigmaPlus) (Icc 0 Real.pi) := by
  intro θ hθ φ hφ hθφ
  apply adjointNumerator_strictMonoOn hxMinus hxPlus
    hsigmaMinus hsigmaPlus ha2
  · exact Set.mem_Ici.mpr
      (platformAngularDistance_mem_Icc ha2.le hθ).1
  · exact Set.mem_Ici.mpr
      (platformAngularDistance_mem_Icc ha2.le hφ).1
  · exact platformAngularDistance_strictMonoOn ha2 hθ hφ hθφ

theorem platformAngularAdjointDensity_nonneg
    {a xMinus xPlus sigmaMinus sigmaPlus θ : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (ha2 : a < 2) (hθ : θ ∈ Icc 0 Real.pi) :
    0 ≤ platformAngularAdjointDensity
      a xMinus xPlus sigmaMinus sigmaPlus θ := by
  apply adjointNumerator_nonneg_on hxMinus hxPlus
    hsigmaMinus hsigmaPlus ha2
  exact platformAngularDistance_mem_Icc ha2.le hθ

theorem platformAngularAdjointDensity_pos
    {a xMinus xPlus sigmaMinus sigmaPlus θ : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (ha2 : a < 2) (hθ : θ ∈ Ioc 0 Real.pi) :
    0 < platformAngularAdjointDensity
      a xMinus xPlus sigmaMinus sigmaPlus θ := by
  apply adjointNumerator_pos_of_left_lt hxMinus hxPlus
    hsigmaMinus hsigmaPlus ha2
  have hd := platformAngularDistance_strictMonoOn ha2
    ⟨le_rfl, Real.pi_pos.le⟩ ⟨hθ.1.le, hθ.2⟩ hθ.1
  simpa only [platformAngularDistance_zero] using! hd

def platformBPi
    (a xMinus xPlus sigmaMinus sigmaPlus : ℝ) : ℝ :=
  platformAngularAdjointDensity
    a xMinus xPlus sigmaMinus sigmaPlus Real.pi

theorem platformBPi_pos
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (ha2 : a < 2) :
    0 < platformBPi a xMinus xPlus sigmaMinus sigmaPlus := by
  apply platformAngularAdjointDensity_pos hxMinus hxPlus
    hsigmaMinus hsigmaPlus ha2
  exact ⟨Real.pi_pos, le_rfl⟩

end

end Erdos1038
