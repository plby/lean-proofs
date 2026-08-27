import ErdosProblems.Erdos4.FGKMTRationalProfile

/-! Exact main terms and uniform finite harmonic masses of the sieve profile. -/

open scoped Topology BigOperators

namespace Erdos4.FGKMT

open MeasureTheory BoundedGaps.Maynard

theorem logarithmicAbelMain_reciprocal {b : ℝ} (hb : 0 < b)
    {T : ℕ} (hT : 1 ≤ T) (ρ : ℝ) :
    logarithmicAbelMain T ρ (logarithmicReciprocal b) =
      ρ * (Real.log (1 + b * Real.log (T : ℝ)) / b) := by
  have hTreal : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hcont : ContinuousOn (logarithmicReciprocal b) (Set.Icc (1 : ℝ) T) :=
    fun x hx => (hasDerivAt_logarithmicReciprocal hb.le hx.1).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Icc (1 : ℝ) T,
      HasDerivAt (logarithmicReciprocal b) (deriv (logarithmicReciprocal b) x) x :=
    fun x hx => (hasDerivAt_logarithmicReciprocal hb.le hx.1).differentiableAt.hasDerivAt
  have hderivint : IntervalIntegrable (deriv (logarithmicReciprocal b)) volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hTreal]
    exact continuousOn_deriv_logarithmicReciprocal hb.le
  rw [logarithmicAbelMain_eq_intervalIntegral_div hT hcont hderiv hderivint]
  let F : ℝ → ℝ := fun x => ρ * (Real.log (1 + b * Real.log x) / b)
  have hF : ∀ x ∈ Set.uIcc (1 : ℝ) T,
      HasDerivAt F (logarithmicReciprocal b x * (ρ / x)) x := by
    intro x hx
    rw [Set.uIcc_of_le hTreal] at hx
    have hxpos := zero_lt_one.trans_le hx.1
    have hbase := logarithmicReciprocal_base_pos hb.le hx.1
    have hd := (((((Real.hasDerivAt_log hxpos.ne').const_mul b).const_add 1).log hbase.ne').div_const b).const_mul ρ
    have heq : ρ * ((b * x⁻¹ / (1 + b * Real.log x)) / b) =
        logarithmicReciprocal b x * (ρ / x) := by
      unfold logarithmicReciprocal
      field_simp
    rw [heq] at hd
    exact hd
  have hint : IntervalIntegrable (fun x => logarithmicReciprocal b x * (ρ / x)) volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hTreal]
    exact hcont.mul (continuousOn_const.div continuousOn_id
      (fun x hx => (zero_lt_one.trans_le hx.1).ne'))
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint
  simpa only [F, Real.log_one, mul_zero, add_zero, zero_div, sub_zero] using hh

theorem logarithmicAbelMain_reciprocal_sq {b : ℝ} (hb : 0 ≤ b)
    {T : ℕ} (hT : 1 ≤ T) (ρ : ℝ) :
    logarithmicAbelMain T ρ (fun x => logarithmicReciprocal b x ^ 2) =
      ρ * (Real.log (T : ℝ) / (1 + b * Real.log (T : ℝ))) := by
  have hTreal : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hcont : ContinuousOn (fun x => logarithmicReciprocal b x ^ 2) (Set.Icc (1 : ℝ) T) :=
    fun x hx => ((hasDerivAt_logarithmicReciprocal hb hx.1).continuousAt.pow 2).continuousWithinAt
  have hderiv : ∀ x ∈ Set.Icc (1 : ℝ) T,
      HasDerivAt (fun t => logarithmicReciprocal b t ^ 2)
        (deriv (fun t => logarithmicReciprocal b t ^ 2) x) x := by
    intro x hx
    exact ((hasDerivAt_logarithmicReciprocal hb hx.1).differentiableAt.pow 2).hasDerivAt
  have hderivint : IntervalIntegrable (deriv (fun x => logarithmicReciprocal b x ^ 2)) volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hTreal]
    exact continuousOn_deriv_logarithmicReciprocal_sq hb
  rw [logarithmicAbelMain_eq_intervalIntegral_div hT hcont hderiv hderivint]
  let F : ℝ → ℝ := fun x => ρ * (Real.log x / (1 + b * Real.log x))
  have hF : ∀ x ∈ Set.uIcc (1 : ℝ) T,
      HasDerivAt F (logarithmicReciprocal b x ^ 2 * (ρ / x)) x := by
    intro x hx
    rw [Set.uIcc_of_le hTreal] at hx
    have hxpos := zero_lt_one.trans_le hx.1
    have hbase := logarithmicReciprocal_base_pos hb hx.1
    have hd := ((Real.hasDerivAt_log hxpos.ne').div
      (((Real.hasDerivAt_log hxpos.ne').const_mul b).const_add 1) hbase.ne').const_mul ρ
    have heq : ρ * ((x⁻¹ * (1 + b * Real.log x) - Real.log x * (b * x⁻¹)) /
        (1 + b * Real.log x) ^ 2) = logarithmicReciprocal b x ^ 2 * (ρ / x) := by
      unfold logarithmicReciprocal
      field_simp
      ring
    rw [heq] at hd
    exact hd
  have hint : IntervalIntegrable (fun x => logarithmicReciprocal b x ^ 2 * (ρ / x)) volume 1 T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hTreal]
    exact hcont.mul (continuousOn_const.div continuousOn_id
      (fun x hx => (zero_lt_one.trans_le hx.1).ne'))
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint
  simpa only [F, Real.log_one, zero_div, mul_zero, sub_zero] using hh

noncomputable def harmonicTransferError (W : ℕ) : ℝ :=
  2 * (uniformHarmonicConstant + 1) * (1 + Real.log (W : ℝ))

theorem harmonicTransferError_pos (W : ℕ) : 0 < harmonicTransferError W := by
  have hh := uniformHarmonicConstant_pos
  have hlog := Real.log_natCast_nonneg W
  unfold harmonicTransferError
  positivity

theorem reciprocal_harmonic_mass_error {W T : ℕ} (hW : 0 < W) (hSq : Squarefree W) (hT : 1 ≤ T)
    {b : ℝ} (hb : 0 < b) :
    |(∑ n ∈ Finset.Icc 1 T, logarithmicReciprocal b n * squarefreeHarmonicWeight W n) -
      coprimeHarmonicDensity W * (Real.log (1 + b * Real.log (T : ℝ)) / b)| ≤
      harmonicTransferError W := by
  have hTreal : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hh := weighted_harmonic_error hW hSq hT
    (fun x hx => (hasDerivAt_logarithmicReciprocal hb.le hx.1).differentiableAt)
    (continuousOn_deriv_logarithmicReciprocal hb.le)
    (logarithmicReciprocal_variation hb.le hTreal)
  rw [logarithmicAbelMain_reciprocal hb hT] at hh
  have hf : |logarithmicReciprocal b T| ≤ 1 := by
    rw [abs_of_nonneg (logarithmicReciprocal_nonneg hb.le hTreal)]
    exact logarithmicReciprocal_le_one hb.le hTreal
  apply hh.trans
  unfold harmonicTransferError
  have hnonneg : 0 ≤ (uniformHarmonicConstant + 1) * (1 + Real.log (W : ℝ)) := by
    have hc := uniformHarmonicConstant_pos
    positivity
  exact (mul_le_mul_of_nonneg_left (by linarith : |logarithmicReciprocal b T| + 1 ≤ 2) hnonneg).trans_eq (by ring)

theorem reciprocal_sq_harmonic_mass_error {W T : ℕ} (hW : 0 < W) (hSq : Squarefree W) (hT : 1 ≤ T)
    {b : ℝ} (hb : 0 ≤ b) :
    |(∑ n ∈ Finset.Icc 1 T, logarithmicReciprocal b n ^ 2 * squarefreeHarmonicWeight W n) -
      coprimeHarmonicDensity W * (Real.log (T : ℝ) / (1 + b * Real.log (T : ℝ)))| ≤
      harmonicTransferError W := by
  have hTreal : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hh := weighted_harmonic_error hW hSq hT
    (fun x hx => ((hasDerivAt_logarithmicReciprocal hb hx.1).differentiableAt.pow 2))
    (continuousOn_deriv_logarithmicReciprocal_sq hb)
    (logarithmicReciprocal_sq_variation hb hTreal)
  simp only [Pi.pow_def] at hh
  rw [logarithmicAbelMain_reciprocal_sq hb hT] at hh
  have hf : |logarithmicReciprocal b T ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    have hf0 := logarithmicReciprocal_nonneg hb hTreal
    have hf1 := logarithmicReciprocal_le_one hb hTreal
    nlinarith
  apply hh.trans
  unfold harmonicTransferError
  have hnonneg : 0 ≤ (uniformHarmonicConstant + 1) * (1 + Real.log (W : ℝ)) := by
    have hc := uniformHarmonicConstant_pos
    positivity
  exact (mul_le_mul_of_nonneg_left (by linarith : |logarithmicReciprocal b T ^ 2| + 1 ≤ 2) hnonneg).trans_eq (by ring)

end Erdos4.FGKMT
