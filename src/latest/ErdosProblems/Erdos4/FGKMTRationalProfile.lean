import ErdosProblems.Erdos4.FGKMTUniformAbel

/-! Calculus and uniform variation bounds for the logarithmic-gain profile. -/

open scoped Topology

namespace Erdos4.FGKMT

open MeasureTheory

noncomputable def logarithmicReciprocal (b x : ℝ) : ℝ := (1 + b * Real.log x)⁻¹

noncomputable def logarithmicReciprocalDerivative (b x : ℝ) : ℝ :=
  -(b * x⁻¹) / (1 + b * Real.log x) ^ 2

theorem logarithmicReciprocal_base_pos {b x : ℝ} (hb : 0 ≤ b) (hx : 1 ≤ x) :
    0 < 1 + b * Real.log x := by
  have hh := Real.log_nonneg hx
  positivity

theorem logarithmicReciprocal_nonneg {b x : ℝ} (hb : 0 ≤ b) (hx : 1 ≤ x) :
    0 ≤ logarithmicReciprocal b x :=
  (inv_pos.mpr (logarithmicReciprocal_base_pos hb hx)).le

theorem logarithmicReciprocal_le_one {b x : ℝ} (hb : 0 ≤ b) (hx : 1 ≤ x) :
    logarithmicReciprocal b x ≤ 1 := by
  unfold logarithmicReciprocal
  apply (inv_le_one₀ (logarithmicReciprocal_base_pos hb hx)).mpr
  have hh := mul_nonneg hb (Real.log_nonneg hx)
  linarith

theorem hasDerivAt_logarithmicReciprocal {b x : ℝ} (hb : 0 ≤ b) (hx : 1 ≤ x) :
    HasDerivAt (logarithmicReciprocal b) (logarithmicReciprocalDerivative b x) x := by
  have hx0 : x ≠ 0 := (zero_lt_one.trans_le hx).ne'
  have hh := (((Real.hasDerivAt_log hx0).const_mul b).const_add 1).inv
    (logarithmicReciprocal_base_pos hb hx).ne'
  exact hh

theorem continuousAt_logarithmicReciprocalDerivative {b x : ℝ} (hb : 0 ≤ b) (hx : 1 ≤ x) :
    ContinuousAt (logarithmicReciprocalDerivative b) x := by
  have hx0 : x ≠ 0 := (zero_lt_one.trans_le hx).ne'
  have hlog : ContinuousAt (fun t : ℝ => 1 + b * Real.log t) x :=
    continuousAt_const.add (continuousAt_const.mul (Real.continuousAt_log hx0))
  exact (continuousAt_const.mul (continuousAt_id.inv₀ hx0)).neg.div
    (hlog.pow 2) (pow_ne_zero 2 (logarithmicReciprocal_base_pos hb hx).ne')

theorem continuousOn_deriv_logarithmicReciprocal {b T : ℝ} (hb : 0 ≤ b) :
    ContinuousOn (deriv (logarithmicReciprocal b)) (Set.Icc 1 T) := by
  apply (show ContinuousOn (logarithmicReciprocalDerivative b) (Set.Icc 1 T) from
    fun x hx => (continuousAt_logarithmicReciprocalDerivative hb hx.1).continuousWithinAt).congr
  intro x hx
  exact (hasDerivAt_logarithmicReciprocal hb hx.1).deriv

theorem deriv_logarithmicReciprocal_nonpos {b x : ℝ} (hb : 0 ≤ b) (hx : 1 ≤ x) :
    deriv (logarithmicReciprocal b) x ≤ 0 := by
  rw [(hasDerivAt_logarithmicReciprocal hb hx).deriv]
  unfold logarithmicReciprocalDerivative
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hb (by positivity))) (sq_nonneg _)

theorem logarithmicReciprocal_variation {b T : ℝ} (hb : 0 ≤ b) (hT : 1 ≤ T) :
    (∫ x in (1 : ℝ)..T, |deriv (logarithmicReciprocal b) x|) ≤ 1 := by
  exact monotone_variation_le_one hT
    (fun x hx => (hasDerivAt_logarithmicReciprocal hb hx.1).differentiableAt)
    (continuousOn_deriv_logarithmicReciprocal hb)
    (fun x hx => deriv_logarithmicReciprocal_nonpos hb hx.1)
    (by simp [logarithmicReciprocal]) (logarithmicReciprocal_nonneg hb hT)

theorem continuousOn_deriv_logarithmicReciprocal_sq {b T : ℝ} (hb : 0 ≤ b) :
    ContinuousOn (deriv (fun x => logarithmicReciprocal b x ^ 2)) (Set.Icc 1 T) := by
  have hcont : ContinuousOn (fun x => 2 * logarithmicReciprocal b x *
      logarithmicReciprocalDerivative b x) (Set.Icc 1 T) := by
    intro x hx
    exact ((continuousAt_const.mul (hasDerivAt_logarithmicReciprocal hb hx.1).continuousAt).mul
      (continuousAt_logarithmicReciprocalDerivative hb hx.1)).continuousWithinAt
  apply hcont.congr
  intro x hx
  simpa only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, Pi.pow_def] using
    ((hasDerivAt_logarithmicReciprocal hb hx.1).pow 2).deriv

theorem deriv_logarithmicReciprocal_sq_nonpos {b x : ℝ} (hb : 0 ≤ b) (hx : 1 ≤ x) :
    deriv (fun t => logarithmicReciprocal b t ^ 2) x ≤ 0 := by
  have hh := ((hasDerivAt_logarithmicReciprocal hb hx).pow 2).deriv
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, Pi.pow_def] at hh
  rw [hh]
  have hd : logarithmicReciprocalDerivative b x ≤ 0 := by
    rw [← (hasDerivAt_logarithmicReciprocal hb hx).deriv]
    exact deriv_logarithmicReciprocal_nonpos hb hx
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) (logarithmicReciprocal_nonneg hb hx)) hd

theorem logarithmicReciprocal_sq_variation {b T : ℝ} (hb : 0 ≤ b) (hT : 1 ≤ T) :
    (∫ x in (1 : ℝ)..T, |deriv (fun t => logarithmicReciprocal b t ^ 2) x|) ≤ 1 := by
  exact monotone_variation_le_one hT
    (fun x hx => ((hasDerivAt_logarithmicReciprocal hb hx.1).pow 2).differentiableAt)
    (continuousOn_deriv_logarithmicReciprocal_sq hb)
    (fun x hx => deriv_logarithmicReciprocal_sq_nonpos hb hx.1)
    (by simp [logarithmicReciprocal]) (sq_nonneg _)

end Erdos4.FGKMT
