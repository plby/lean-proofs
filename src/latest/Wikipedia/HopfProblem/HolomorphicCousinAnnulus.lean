import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The Cauchy formula on an annulus

The additive Cousin problem on two overlapping discs is solved by its two
boundary Cauchy integrals.  This file proves the needed annular Cauchy formula
from Cauchy--Goursat, rather than assuming a cohomology-vanishing theorem.
-/

noncomputable section

open Complex Metric Set
open scoped Topology Real

namespace Wikipedia.HopfProblem.HolomorphicCousin

/-- A round open annulus in the complex plane. -/
def annulus (r R : ℝ) : Set ℂ := {z | r < ‖z‖ ∧ ‖z‖ < R}

@[simp] theorem mem_annulus {r R : ℝ} {z : ℂ} :
    z ∈ annulus r R ↔ r < ‖z‖ ∧ ‖z‖ < R := Iff.rfl

theorem isOpen_annulus (r R : ℝ) : IsOpen (annulus r R) :=
  (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

theorem closedAnnulus_subset_annulus {r a b R : ℝ}
    (hra : r < a) (hbR : b < R) :
    closedBall (0 : ℂ) b \ ball 0 a ⊆ annulus r R := by
  intro z hz
  simp only [mem_sdiff, mem_closedBall, mem_ball, dist_zero_right, not_lt] at hz
  exact ⟨hra.trans_le hz.2, hz.1.trans_lt hbR⟩

/-- The Cauchy kernel has zero circle integral when its pole is outside the
closed disc. -/
theorem circleIntegral_kernel_eq_zero {a : ℝ} (ha : 0 ≤ a) {z : ℂ}
    (hz : a < ‖z‖) :
    (∮ w in C(0, a), (w - z)⁻¹) = 0 := by
  have hne (w : ℂ) (hw : w ∈ closedBall 0 a) : w - z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro hwz
    subst w
    exact (not_le.mpr hz) (by simpa only [mem_closedBall, dist_zero_right] using hw)
  exact circleIntegral_eq_zero_of_differentiable_on_off_countable ha countable_empty
    ((continuousOn_id.sub continuousOn_const).inv₀ hne)
    (fun w hw => (differentiableAt_id.sub_const z).inv (hne w (ball_subset_closedBall hw.1)))

/-- The removable divided difference separates the Cauchy integral into its
pole term and a holomorphic term. -/
theorem circleIntegral_dslope {h : ℂ → ℂ} {a : ℝ} (ha : 0 ≤ a) {z : ℂ}
    (hh : ContinuousOn h (sphere 0 a)) (hz : z ∉ sphere 0 a) :
    (∮ w in C(0, a), dslope h z w) =
      (∮ w in C(0, a), (w - z)⁻¹ * h w) -
        (∮ w in C(0, a), (w - z)⁻¹) * h z := by
  have hne (w : ℂ) (hw : w ∈ sphere 0 a) : w ≠ z :=
    ne_of_mem_of_not_mem hw hz
  have hc : ContinuousOn (fun w : ℂ => (w - z)⁻¹) (sphere 0 a) :=
    (continuousOn_id.sub continuousOn_const).inv₀
      (fun w hw => sub_ne_zero.mpr (hne w hw))
  calc
    (∮ w in C(0, a), dslope h z w) =
        ∮ w in C(0, a), (w - z)⁻¹ • h w - (w - z)⁻¹ • h z := by
      apply circleIntegral.integral_congr ha
      intro w hw
      rw [dslope_of_ne _ (hne w hw)]
      simp only [slope_def_module, smul_sub]
    _ = (∮ w in C(0, a), (w - z)⁻¹ • h w) -
        ∮ w in C(0, a), (w - z)⁻¹ • h z :=
      circleIntegral.integral_sub ((hc.smul hh).circleIntegrable ha)
        ((hc.smul continuousOn_const).circleIntegrable ha)
    _ = _ := by rw [circleIntegral.integral_smul_const]; rfl

/-- **Cauchy's formula on an annulus.** The oriented difference of the two
boundary integrals is `2πi` times the value at an interior point. -/
theorem circleIntegral_sub_eq_two_pi_I_mul {h : ℂ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hh : AnalyticOnNhd ℂ h (closedBall 0 b \ ball 0 a))
    {z : ℂ} (hz : z ∈ annulus a b) :
    (∮ w in C(0, b), (w - z)⁻¹ * h w) -
        (∮ w in C(0, a), (w - z)⁻¹ * h w) =
      (2 * Real.pi * I) * h z := by
  have hzA : z ∈ closedBall (0 : ℂ) b \ ball 0 a := by
    simpa only [mem_sdiff, mem_closedBall, mem_ball, dist_zero_right, not_lt] using
      And.intro hz.2.le hz.1.le
  have hc : ContinuousOn (dslope h z) (closedBall (0 : ℂ) b \ ball 0 a) := by
    intro w hw
    by_cases hwz : w = z
    · subst w
      exact (continuousAt_dslope_same.mpr (hh z hzA).differentiableAt).continuousWithinAt
    · exact ((continuousAt_dslope_of_ne hwz).mpr
        (hh w hw).continuousAt).continuousWithinAt
  have hd : ∀ w ∈ (ball (0 : ℂ) b \ closedBall 0 a) \ {z},
      DifferentiableAt ℂ (dslope h z) w := by
    intro w hw
    apply (differentiableAt_dslope_of_ne hw.2).mpr
    apply (hh w ?_).differentiableAt
    exact ⟨ball_subset_closedBall hw.1.1, fun hw' => hw.1.2 (ball_subset_closedBall hw')⟩
  have hds := circleIntegral_eq_of_differentiable_on_annulus_off_countable ha hab.le
    (countable_singleton z) hc hd
  have hba : sphere (0 : ℂ) b ⊆ closedBall 0 b \ ball 0 a := by
    intro w hw
    have hwn : ‖w‖ = b := by simpa only [mem_sphere, dist_zero_right] using hw
    simp only [mem_sdiff, mem_closedBall, mem_ball, dist_zero_right, not_lt]
    exact ⟨hwn.le, hwn.symm ▸ hab.le⟩
  have haa : sphere (0 : ℂ) a ⊆ closedBall 0 b \ ball 0 a := by
    intro w hw
    have hwn : ‖w‖ = a := by simpa only [mem_sphere, dist_zero_right] using hw
    simp only [mem_sdiff, mem_closedBall, mem_ball, dist_zero_right, not_lt]
    exact ⟨hwn.trans_le hab.le, hwn.ge⟩
  have hzb : z ∉ sphere (0 : ℂ) b := by
    simpa only [mem_sphere, dist_zero_right] using hz.2.ne
  have hza : z ∉ sphere (0 : ℂ) a := by
    simpa only [mem_sphere, dist_zero_right] using hz.1.ne'
  rw [circleIntegral_dslope (ha.trans hab).le (hh.continuousOn.mono hba) hzb,
    circleIntegral_dslope ha.le (hh.continuousOn.mono haa) hza,
    circleIntegral.integral_sub_inv_of_mem_ball
      (by simpa only [mem_ball, dist_zero_right] using hz.2),
    circleIntegral_kernel_eq_zero ha.le hz.1, zero_mul, sub_zero] at hds
  exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp hds).trans (add_comm _ _))

/-- The normalized annular Cauchy formula. -/
theorem normalized_circleIntegral_sub {h : ℂ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hh : AnalyticOnNhd ℂ h (closedBall 0 b \ ball 0 a))
    {z : ℂ} (hz : z ∈ annulus a b) :
    (2 * Real.pi * I : ℂ)⁻¹ * (∮ w in C(0, b), (w - z)⁻¹ * h w) -
        (2 * Real.pi * I : ℂ)⁻¹ * (∮ w in C(0, a), (w - z)⁻¹ * h w) = h z := by
  rw [← mul_sub, circleIntegral_sub_eq_two_pi_I_mul ha hab hh hz,
    ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]

/-- Continuity on every intermediate circle follows from the given
holomorphy on the open annulus. -/
theorem continuousOn_sphere_of_analyticOnNhd_annulus {h : ℂ → ℂ} {r R a : ℝ}
    (hh : AnalyticOnNhd ℂ h (annulus r R)) (hra : r < a) (haR : a < R) :
    ContinuousOn h (sphere 0 a) := by
  refine hh.continuousOn.mono ?_
  intro z hz
  have hzn : ‖z‖ = a := by simpa only [mem_sphere, dist_zero_right] using hz
  exact ⟨hzn.symm ▸ hra, hzn.symm ▸ haR⟩

/-- Changing the integration radius does not change a Cauchy integral if
the pole is outside the intervening closed annulus. -/
theorem circleIntegral_cauchy_radius_eq {h : ℂ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hh : AnalyticOnNhd ℂ h (closedBall 0 b \ ball 0 a))
    {z : ℂ} (hz : ‖z‖ < a ∨ b < ‖z‖) :
    (∮ w in C(0, b), (w - z)⁻¹ * h w) =
      ∮ w in C(0, a), (w - z)⁻¹ * h w := by
  have hne (w : ℂ) (hw : w ∈ closedBall 0 b \ ball 0 a) : w - z ≠ 0 := by
    apply sub_ne_zero.mpr
    intro hwz
    subst w
    simp only [mem_sdiff, mem_closedBall, mem_ball, dist_zero_right, not_lt] at hw
    rcases hz with hz | hz
    · exact (not_le.mpr hz) hw.2
    · exact (not_le.mpr hz) hw.1
  apply circleIntegral_eq_of_differentiable_on_annulus_off_countable ha hab countable_empty
  · exact ((continuousOn_id.sub continuousOn_const).inv₀ hne).mul hh.continuousOn
  · intro w hw
    have hwA : w ∈ closedBall (0 : ℂ) b \ ball 0 a :=
      ⟨ball_subset_closedBall hw.1.1, fun hw' => hw.1.2 (ball_subset_closedBall hw')⟩
    exact ((differentiableAt_id.sub_const z).inv (hne w hwA)).mul
      (hh w hwA).differentiableAt

end Wikipedia.HopfProblem.HolomorphicCousin
