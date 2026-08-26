import ErdosProblems.Erdos4.PrimitiveProfile

/-!
# Smoothness and bounded variation of the logarithmic profile

The profile derivative has an explicit nonpositive factor. On every
logarithmically scaled interval beginning at one, its total variation is
at most one, independently of both endpoints.
-/

open MeasureTheory
open scoped Topology

namespace Erdos4.ProfileSmooth

open PrimitiveProfile

noncomputable def profileDerivative (m k t : ℝ) : ℝ :=
  4 * k * (1 - m) * (2 + 4 * k * t) * (1 + 4 * m * k * t) ^ (1 / m - 3)

theorem hasDerivAt_profile {m k t : ℝ} (hm : 0 < m) (hk : 0 ≤ k) (ht : 0 ≤ t) :
    HasDerivAt (profile m k) (profileDerivative m k t) t := by
  have hb := base_pos hm.le hk ht
  have hlin₁ : HasDerivAt (fun u : ℝ => 1 + 4 * k * u) (4 * k) t := by
    simpa using ((hasDerivAt_id t).const_mul (4 * k)).const_add 1
  have hlin₂ : HasDerivAt (fun u : ℝ => 1 + 4 * m * k * u) (4 * m * k) t := by
    simpa using ((hasDerivAt_id t).const_mul (4 * m * k)).const_add 1
  have hh := hlin₁.mul (hlin₂.rpow_const (p := 1 / m - 2) (Or.inl hb.ne'))
  change HasDerivAt (profile m k)
    (4 * k * (1 + 4 * m * k * t) ^ (1 / m - 2) +
      (1 + 4 * k * t) * (4 * m * k * (1 / m - 2) *
        (1 + 4 * m * k * t) ^ (1 / m - 2 - 1))) t at hh
  have hshift : (1 + 4 * m * k * t) ^ (1 / m - 2) =
      (1 + 4 * m * k * t) ^ (1 / m - 3) * (1 + 4 * m * k * t) := by
    rw [show 1 / m - 2 = (1 / m - 3) + 1 by ring]
    exact Real.rpow_add_one hb.ne' _
  have heq : profileDerivative m k t =
      4 * k * (1 + 4 * m * k * t) ^ (1 / m - 2) +
        (1 + 4 * k * t) * (4 * m * k * (1 / m - 2) *
          (1 + 4 * m * k * t) ^ (1 / m - 2 - 1)) := by
    unfold profileDerivative
    rw [hshift, show 1 / m - 2 - 1 = 1 / m - 3 by ring]
    field_simp
    ring
  rw [← heq] at hh
  exact hh

theorem profileDerivative_nonpos {m k t : ℝ} (hm : 1 ≤ m) (hk : 0 ≤ k) (ht : 0 ≤ t) :
    profileDerivative m k t ≤ 0 := by
  unfold profileDerivative
  apply mul_nonpos_of_nonpos_of_nonneg
  · apply mul_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    · positivity
  · exact Real.rpow_nonneg (base_pos (by linarith) hk ht).le _

theorem continuousAt_profileDerivative {m k t : ℝ} (hm : 0 ≤ m) (hk : 0 ≤ k) (ht : 0 ≤ t) :
    ContinuousAt (profileDerivative m k) t := by
  have hleft : ContinuousAt (fun u : ℝ => 4 * k * (1 - m) * (2 + 4 * k * u)) t := by fun_prop
  have hbase : ContinuousAt (fun u : ℝ => 1 + 4 * m * k * u) t := by fun_prop
  exact hleft.mul (hbase.rpow_const (Or.inl (base_pos hm hk ht).ne'))

noncomputable def scaled (m k : ℝ) (R : ℕ) (x : ℝ) : ℝ :=
  profile m k (Real.log x / Real.log R)

noncomputable def scaledDerivative (m k : ℝ) (R : ℕ) (x : ℝ) : ℝ :=
  profileDerivative m k (Real.log x / Real.log R) * (x⁻¹ / Real.log R)

theorem hasDerivAt_scaled {m k : ℝ} (hm : 0 < m) (hk : 0 ≤ k) {R : ℕ} (hR : 2 ≤ R)
    {x : ℝ} (hx : 1 ≤ x) : HasDerivAt (scaled m k R) (scaledDerivative m k R x) x := by
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  exact (hasDerivAt_profile hm hk (div_nonneg (Real.log_nonneg hx) hlog.le)).comp x
    ((Real.hasDerivAt_log hxpos.ne').div_const (Real.log R))

theorem continuousOn_scaledDerivative {m k : ℝ} (hm : 0 < m) (hk : 0 ≤ k)
    {R : ℕ} (hR : 2 ≤ R) (T : ℝ) : ContinuousOn (scaledDerivative m k R) (Set.Icc 1 T) := by
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
  have ht : 0 ≤ Real.log x / Real.log R := div_nonneg (Real.log_nonneg hx.1) hlog.le
  have hinner : ContinuousAt (fun x : ℝ => Real.log x / Real.log R) x :=
    (continuousAt_id.log hxpos.ne').div_const _
  have hleft : ContinuousAt (fun x : ℝ => profileDerivative m k (Real.log x / Real.log R)) x :=
    (continuousAt_profileDerivative hm.le hk ht).comp (f := fun x : ℝ => Real.log x / Real.log R) hinner
  have hright : ContinuousAt (fun x : ℝ => x⁻¹ / Real.log R) x :=
    (continuousAt_id.inv₀ hxpos.ne').div_const _
  exact (hleft.mul hright).continuousWithinAt

theorem continuousOn_deriv_scaled {m k : ℝ} (hm : 0 < m) (hk : 0 ≤ k)
    {R : ℕ} (hR : 2 ≤ R) (T : ℝ) :
    ContinuousOn (deriv (scaled m k R)) (Set.Icc 1 T) := by
  apply (continuousOn_scaledDerivative hm hk hR T).congr
  intro x hx
  exact (hasDerivAt_scaled hm hk hR hx.1).deriv

theorem deriv_scaled_nonpos {m k : ℝ} (hm : 1 ≤ m) (hk : 0 ≤ k)
    {R : ℕ} (hR : 2 ≤ R) {x : ℝ} (hx : 1 ≤ x) : deriv (scaled m k R) x ≤ 0 := by
  have hlog : 0 ≤ Real.log (R : ℝ) := Real.log_natCast_nonneg _
  rw [(hasDerivAt_scaled (by linarith) hk hR hx).deriv]
  exact mul_nonpos_of_nonpos_of_nonneg
    (profileDerivative_nonpos hm hk (div_nonneg (Real.log_nonneg hx) hlog))
    (div_nonneg (inv_nonneg.mpr (by linarith)) hlog)

/-- The total variation needed by Abel summation is bounded independently
of the logarithmic scale and the completion endpoint. -/
theorem variation_le_one {m k : ℝ} (hm : 1 ≤ m) (hk : 0 ≤ k)
    {R : ℕ} (hR : 2 ≤ R) {T : ℝ} (hT : 1 ≤ T) :
    (∫ x in (1 : ℝ)..T, |deriv (scaled m k R) x|) ≤ 1 := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hcont : ContinuousOn (deriv (scaled m k R)) (Set.uIcc 1 T) := by
    rw [Set.uIcc_of_le hT]
    exact continuousOn_deriv_scaled hmpos hk hR T
  have hFTC : (∫ x in (1 : ℝ)..T, deriv (scaled m k R) x) = scaled m k R T - scaled m k R 1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => by
        have hd := hasDerivAt_scaled hmpos hk hR (x := x) (by
          rw [Set.uIcc_of_le hT] at hx; exact hx.1)
        simpa only [hd.deriv] using hd) hcont.intervalIntegrable
  have heq : (∫ x in (1 : ℝ)..T, |deriv (scaled m k R) x|) =
      -(∫ x in (1 : ℝ)..T, deriv (scaled m k R) x) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hT] at hx
    exact abs_of_nonpos (deriv_scaled_nonpos hm hk hR hx.1)
  have hnonneg : 0 ≤ scaled m k R T :=
    (profile_pos hmpos.le hk (div_nonneg (Real.log_nonneg hT) (Real.log_natCast_nonneg R))).le
  rw [heq, hFTC]
  have hone : scaled m k R 1 = 1 := by simp [scaled, profile_zero]
  rw [hone]
  linarith

end Erdos4.ProfileSmooth
