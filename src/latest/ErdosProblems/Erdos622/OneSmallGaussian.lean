import ErdosProblems.Erdos622.AlmostBipartite

/-!
# Gaussian parameters for the one-small-cover regime

The relevant window lies wholly on the negative half-line.  Its left endpoint
tends to `-∞` with `M`, while its right endpoint tends to zero with `K`.  This
file packages the resulting elementary parameter choice, including the
separation `16 * M < K` required by the combinatorial argument.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology Interval

namespace Erdos622.OneSmallGaussian

noncomputable section

/-- A Gaussian window wholly on the negative half-line is the difference of
the corresponding two positive half-integrals. -/
lemma gaussianWindowMass_neg_neg {u v : ℝ}
    (hv : 0 ≤ v) (hvu : v ≤ u) :
    BinomialCLT.gaussianWindowMass (-u) (-v) =
      (gaussianHalfInterval u - gaussianHalfInterval v) /
        Real.sqrt (2 * Real.pi) := by
  unfold BinomialCLT.gaussianWindowMass BinomialCLT.standardGaussian
  change ENNReal.toReal (gaussianReal 0 1 (Icc (-u) (-v))) = _
  rw [gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0)
    (Icc (-u) (-v))]
  rw [ENNReal.toReal_ofReal]
  · simp_rw [Erdos622.gaussianPDFReal_zero_one_eq]
    rw [MeasureTheory.integral_div]
    rw [integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (neg_le_neg hvu)]
    have hcomp :
        (∫ x : ℝ in v..u, gaussianKernel (-x)) =
          ∫ x : ℝ in -u..-v, gaussianKernel x := by
      simpa using
        (intervalIntegral.integral_comp_neg
          (f := gaussianKernel) (a := v) (b := u))
    rw [← hcomp]
    have heven : (fun x : ℝ ↦ gaussianKernel (-x)) = gaussianKernel := by
      funext x
      simp [gaussianKernel]
    rw [heven]
    rw [gaussianHalfInterval, gaussianHalfInterval]
    apply congrArg (fun z : ℝ ↦ z / Real.sqrt (2 * Real.pi))
    exact (intervalIntegral.integral_interval_sub_left
      (gaussianKernel_intervalIntegrable 0 u)
      (gaussianKernel_intervalIntegrable 0 v)).symm
  · exact integral_nonneg (fun x ↦ gaussianPDFReal_nonneg 0 1 x)

lemma gaussianHalfInterval_tendsto_atTop :
    Tendsto gaussianHalfInterval atTop
      (nhds (Real.sqrt (2 * Real.pi) / 2)) := by
  have hint : IntegrableOn gaussianKernel (Ioi (0 : ℝ)) := by
    exact ((integrable_exp_neg_mul_sq one_half_pos).congr
      (ae_of_all _ fun x ↦ by simp [gaussianKernel]; ring)).integrableOn
  have h :=
    intervalIntegral_tendsto_integral_Ioi (f := gaussianKernel) 0 hint tendsto_id
  change Tendsto (fun x : ℝ ↦ ∫ t : ℝ in 0..x, gaussianKernel t) atTop
    (nhds (Real.sqrt (2 * Real.pi) / 2))
  simpa only [id_eq, gaussianKernel_integral_Ioi] using h

lemma gaussianHalfInterval_tendsto_zero :
    Tendsto gaussianHalfInterval (nhds 0) (nhds 0) := by
  have hcont : Continuous gaussianHalfInterval :=
    intervalIntegral.continuous_primitive gaussianKernel_intervalIntegrable 0
  have h := hcont.continuousAt (x := (0 : ℝ))
  have hz : gaussianHalfInterval 0 = 0 := by simp [gaussianHalfInterval]
  change Tendsto gaussianHalfInterval (nhds 0)
    (nhds (gaussianHalfInterval 0)) at h
  rw [hz] at h
  exact h

/-- For every positive error, integer parameters can be chosen so that the
negative Gaussian window has mass above `1/2 - ε/2`, while retaining the
combinatorial scale separation `16 * M < K`. -/
theorem exists_oneSmallCover_gaussian_parameters {ε : ℝ} (hε : 0 < ε) :
    ∃ K M : ℕ, 0 < M ∧ 16 * M < K ∧
      (1 / 2 : ℝ) - ε / 2 <
        BinomialCLT.gaussianWindowMass (-(M * Real.sqrt 2))
          (-(Real.sqrt 2 / K)) := by
  let c : ℝ := Real.sqrt (2 * Real.pi)
  have hc : 0 < c := Real.sqrt_pos.2 (mul_pos two_pos Real.pi_pos)
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hscale : Tendsto (fun m : ℕ ↦ (m : ℝ) * Real.sqrt 2) atTop atTop := by
    simpa [mul_comm] using tendsto_natCast_atTop_atTop.const_mul_atTop hsqrt2
  have hMlim : Tendsto
      (fun m : ℕ ↦ gaussianHalfInterval ((m : ℝ) * Real.sqrt 2))
      atTop (nhds (c / 2)) := by
    exact gaussianHalfInterval_tendsto_atTop.comp hscale
  have hMbound : c / 2 - ε * c / 4 < c / 2 := by
    nlinarith [mul_pos hε hc]
  have hMgood : ∀ᶠ m : ℕ in atTop,
      c / 2 - ε * c / 4 <
        gaussianHalfInterval ((m : ℝ) * Real.sqrt 2) :=
    hMlim.eventually_const_lt hMbound
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp hMgood
  let M : ℕ := max M₀ 1
  have hM₀M : M₀ ≤ M := le_max_left _ _
  have hMpos : 0 < M := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hMhalf : c / 2 - ε * c / 4 <
      gaussianHalfInterval ((M : ℝ) * Real.sqrt 2) := hM₀ M hM₀M
  have hdiv : Tendsto (fun k : ℕ ↦ Real.sqrt 2 / (k : ℝ)) atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hKlim : Tendsto
      (fun k : ℕ ↦ gaussianHalfInterval (Real.sqrt 2 / (k : ℝ)))
      atTop (nhds 0) := gaussianHalfInterval_tendsto_zero.comp hdiv
  have hKtarget : 0 < ε * c / 4 := by positivity
  have hKgood : ∀ᶠ k : ℕ in atTop,
      gaussianHalfInterval (Real.sqrt 2 / (k : ℝ)) < ε * c / 4 :=
    hKlim.eventually_lt_const hKtarget
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp hKgood
  let K : ℕ := max K₀ (16 * M + 1)
  have hK₀K : K₀ ≤ K := le_max_left _ _
  have hKM : 16 * M < K := by
    dsimp [K]
    omega
  have hKpos : 0 < K := lt_of_le_of_lt (Nat.zero_le (16 * M)) hKM
  have hKhalf : gaussianHalfInterval (Real.sqrt 2 / (K : ℝ)) < ε * c / 4 :=
    hK₀ K hK₀K
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hv : 0 ≤ Real.sqrt 2 / (K : ℝ) := (div_pos hsqrt2 hKreal).le
  have hvu : Real.sqrt 2 / (K : ℝ) ≤ (M : ℝ) * Real.sqrt 2 := by
    have hKone : (1 : ℝ) ≤ K := by exact_mod_cast hKpos
    have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
    have hinv : (1 : ℝ) / K ≤ M :=
      ((div_le_one hKreal).2 hKone).trans hMone
    have := mul_le_mul_of_nonneg_right hinv hsqrt2.le
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  refine ⟨K, M, hMpos, hKM, ?_⟩
  rw [gaussianWindowMass_neg_neg hv hvu]
  change (1 / 2 : ℝ) - ε / 2 <
    (gaussianHalfInterval ((M : ℝ) * Real.sqrt 2) -
      gaussianHalfInterval (Real.sqrt 2 / (K : ℝ))) / c
  rw [lt_div_iff₀ hc]
  nlinarith

end

end Erdos622.OneSmallGaussian
