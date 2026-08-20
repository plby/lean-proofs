import ErdosProblems.Erdos525.OddNarrow

open scoped BigOperators Topology ComplexConjugate RealInnerProductSpace

namespace Erdos525

open Classical Filter Finset Set MeasureTheory

namespace Odd


noncomputable def globalAccelerationBound (n : ℕ) : ℝ :=
  Real.sqrt (2 * n + 1 : ℝ) + extraAccelerationBound n

lemma globalAccelerationBound_nonneg (n : ℕ) :
    0 ≤ globalAccelerationBound n :=
  add_nonneg (Real.sqrt_nonneg _) (extraAccelerationBound_nonneg n)

lemma norm_acceleration_le (n : ℕ) (e : SignVector (2 * n + 1)) (t : ℝ) :
    ‖acceleration n e t‖ ≤ globalAccelerationBound n := by
  have hprefix := norm_rescaledCenteredAcceleration_le n (initialSegment n e) t
  unfold acceleration globalAccelerationBound
  calc
    ‖(prefixScale n : ℂ) *
          rescaledCenteredAcceleration n (initialSegment n e) t +
        ((sign (lastSign n e) / Real.sqrt (2 * n + 2 : ℝ) : ℝ) : ℂ) *
          (((((n + 1 : ℕ) : ℝ) / n : ℂ) * Complex.I) ^ 2) *
          Complex.exp ((((n + 1 : ℕ) : ℝ) * (t / n) : ℂ) * Complex.I)‖ ≤
      ‖(prefixScale n : ℂ) *
          rescaledCenteredAcceleration n (initialSegment n e) t‖ +
        ‖((sign (lastSign n e) / Real.sqrt (2 * n + 2 : ℝ) : ℝ) : ℂ) *
          (((((n + 1 : ℕ) : ℝ) / n : ℂ) * Complex.I) ^ 2) *
          Complex.exp ((((n + 1 : ℕ) : ℝ) * (t / n) : ℂ) * Complex.I)‖ :=
        norm_add_le _ _
    _ = prefixScale n *
          ‖rescaledCenteredAcceleration n (initialSegment n e) t‖ +
        extraAccelerationBound n := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (prefixScale_pos n), norm_extra_acceleration]
    _ ≤ Real.sqrt (2 * n + 1 : ℝ) + extraAccelerationBound n := by
      gcongr
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (prefixScale_le_one n)).trans hprefix

lemma norm_eval_sub_linear_le (n : ℕ) (e : SignVector (2 * n + 1))
    (x y : ℝ) :
    ‖eval n e y - (eval n e x + ((y - x : ℝ) : ℂ) * velocity n e x)‖ ≤
      globalAccelerationBound n * (y - x) ^ 2 := by
  by_cases hxy : x ≤ y
  · exact norm_taylor_sub_le_of_le
      (eval n e) (velocity n e) (acceleration n e)
      (globalAccelerationBound n) x y hxy
      (hasDerivAt_eval n e) (hasDerivAt_velocity n e)
      (globalAccelerationBound_nonneg n) (norm_acceleration_le n e)
  · exact norm_taylor_sub_le_of_ge
      (eval n e) (velocity n e) (acceleration n e)
      (globalAccelerationBound n) x y (le_of_not_ge hxy)
      (hasDerivAt_eval n e) (hasDerivAt_velocity n e)
      (globalAccelerationBound_nonneg n) (norm_acceleration_le n e)

noncomputable def localMeshTaylorError (n : ℕ) : ℝ :=
  globalAccelerationBound n * localMeshHalfWidth n ^ 2

lemma scaled_localMeshTaylorError_tendsto_zero :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * localMeshTaylorError n) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hextraDiv := extraAccelerationBound_tendsto_zero.mul hinv
  simp only [zero_mul] at hextraDiv
  have hextra := hextraDiv.mul scaled_localMeshHalfWidth_sq_tendsto
  simp only [zero_mul] at hextra
  have hsum := Erdos525.scaled_localMeshTaylorError_tendsto_zero.add hextra
  convert hsum using 1
  · funext n
    by_cases hn : n = 0
    · subst n
      simp [localMeshTaylorError, globalAccelerationBound, localMeshHalfWidth]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    unfold localMeshTaylorError globalAccelerationBound Erdos525.localMeshTaylorError
    field_simp
  · norm_num

lemma oddCenteredMin_le_eval (n : ℕ) (hn : 0 < n)
    (e : SignVector (2 * n + 1)) (t : ℝ) :
    oddCenteredMin n e ≤ ‖eval n e t‖ := by
  rw [oddCenteredMin_eq_minModulus_div_sqrt]
  have hsqrt : 0 < Real.sqrt (2 * n + 2 : ℝ) := by positivity
  have hcircle : Complex.exp ((((t / n : ℝ) : ℂ) * Complex.I)) ∈
      unitCircle := by
    simp [unitCircle, Complex.norm_exp, Complex.mul_re]
  have hmin := minModulus_le e hcircle
  have hnorm := norm_eval n e t
  rw [hnorm]
  calc
    minModulus e / Real.sqrt (2 * n + 2 : ℝ) ≤
        ‖littlewoodEval e
          (Complex.exp ((((t / n : ℝ) : ℂ) * Complex.I)))‖ /
            Real.sqrt (2 * n + 2 : ℝ) :=
      (div_le_div_iff_of_pos_right hsqrt).2 hmin
    _ = ‖oddCenteredEval n e (t / n)‖ := by
      rw [norm_oddCenteredEval]

lemma IsTruncatedLocalRepresentative.oddCenteredMin_le
    {n : ℕ} (hn : 0 < n) {u velocityLower velocityUpper : ℝ}
    {e : SignVector (2 * n + 1)} {a : Fin (localMeshSize n)}
    (h : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a) :
    oddCenteredMin n e ≤ u / n + localMeshTaylorError n := by
  let x := localMeshPoint n a
  let s := localAffineOffset n e a
  let A := eval n e x + (s : ℂ) * velocity n e x
  have htime := oddCenteredMin_le_eval n hn e (x + s)
  have htaylor := norm_eval_sub_linear_le n e x (x + s)
  have hlin : ‖A‖ ≤ u / n := by
    simpa [x, s, A] using h.affine_norm_le hn
  have hvalue : ‖eval n e (x + s)‖ ≤ ‖eval n e (x + s) - A‖ + ‖A‖ := by
    have heq : eval n e (x + s) = (eval n e (x + s) - A) + A := by abel
    calc
      ‖eval n e (x + s)‖ = ‖(eval n e (x + s) - A) + A‖ :=
        congrArg norm heq
      _ ≤ ‖eval n e (x + s) - A‖ + ‖A‖ :=
        norm_add_le (eval n e (x + s) - A) A
  calc
    oddCenteredMin n e ≤ ‖eval n e (x + s)‖ := htime
    _ ≤ ‖eval n e (x + s) - A‖ + ‖A‖ := hvalue
    _ ≤ globalAccelerationBound n * s ^ 2 + u / n := by
      gcongr
      simpa [x, s, A] using htaylor
    _ ≤ localMeshTaylorError n + u / n := by
      have hs := h.1.2.1
      change |s| ≤ localMeshHalfWidth n at hs
      have hh : 0 ≤ localMeshHalfWidth n := by
        unfold localMeshHalfWidth
        positivity
      have hsSq : s ^ 2 ≤ localMeshHalfWidth n ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg s) hh).2 hs
      unfold localMeshTaylorError
      exact add_le_add
        (mul_le_mul_of_nonneg_left hsSq (globalAccelerationBound_nonneg n)) le_rfl
    _ = u / n + localMeshTaylorError n := by ring

theorem eventually_tail_le_halfFactoredVoid
    (u v widthFactor velocityLower velocityUpper : ℝ)
    (hvu : v < u) (hfactor : widthFactor ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      tail n u ≤ uniformProbability (fun e : SignVector (2 * n + 1) ↦
        halfFactoredTruncatedLocalMinimumCount n widthFactor v
          velocityLower velocityUpper e = 0) := by
  have herr : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * localMeshTaylorError n < u - v :=
    scaled_localMeshTaylorError_tendsto_zero.eventually
      (Iio_mem_nhds (sub_pos.mpr hvu))
  filter_upwards [Nat.eventually_pos, herr] with n hn herrN
  unfold tail
  apply uniformProbability_mono
  intro e htail
  by_contra hcount
  rw [halfFactoredTruncatedLocalMinimumCount] at hcount
  simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    not_forall, not_or, not_not] at hcount
  rcases hcount with ⟨a, ha, hrep⟩
  have hfull := isFactoredTruncatedLocalRepresentative_to_truncated n widthFactor
    v velocityLower velocityUpper hfactor e a hrep
  have hmin := hfull.oddCenteredMin_le hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hscaled : v / n + localMeshTaylorError n < u / n := by
    apply (lt_div_iff₀ hnR).2
    calc
      (v / n + localMeshTaylorError n) * n =
          v + n * localMeshTaylorError n := by field_simp [hnR.ne']
      _ < u := by linarith
  exact (not_lt_of_ge hmin) (htail.trans' hscaled)

theorem tail_limsup_le_cutoffIntensity
    (u widthFactor velocityLower velocityUpper : ℝ)
    (hu : 0 < u) (hfactor0 : 0 < widthFactor) (hfactor1 : widthFactor < 1)
    (hvelLower : 0 < velocityLower) (hvelUpper : 0 < velocityUpper)
    {b : ℝ}
    (hb : Real.exp (-(widthFactor * ((6 * u / Real.pi) *
      blockVelocityMass velocityLower velocityUpper))) < b) :
    ∀ᶠ n : ℕ in atTop, tail n u < b := by
  let vSeq : ℕ → ℝ := fun k ↦ u - 1 / (k + 1 : ℝ)
  have hone : Tendsto (fun k : ℕ ↦ (1 : ℝ) / (k + 1 : ℝ))
      atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hvSeq : Tendsto vSeq atTop (𝓝 u) := by
    simpa [vSeq] using tendsto_const_nhds.sub hone
  have hexp : Tendsto (fun k : ℕ ↦
      Real.exp (-(widthFactor * ((6 * vSeq k / Real.pi) *
        blockVelocityMass velocityLower velocityUpper)))) atTop
      (𝓝 (Real.exp (-(widthFactor * ((6 * u / Real.pi) *
        blockVelocityMass velocityLower velocityUpper))))) := by
    apply Real.continuous_exp.continuousAt.tendsto.comp
    simpa only [mul_assoc] using
      (((tendsto_const_nhds.mul
        ((tendsto_const_nhds.mul hvSeq).div_const Real.pi)).mul_const
          (blockVelocityMass velocityLower velocityUpper)).neg)
  have hsmall := hexp.eventually (Iio_mem_nhds hb)
  have hpos := hvSeq.eventually (Ioi_mem_nhds hu)
  rcases (hsmall.and hpos).exists with ⟨k, hsmallK, hposK⟩
  have hvu : vSeq k < u := by
    dsimp [vSeq]
    have : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
    linarith
  have hle := eventually_tail_le_halfFactoredVoid
    u (vSeq k) widthFactor velocityLower velocityUpper hvu hfactor1.le
  have hvoid := uniformProbability_halfFactoredTruncatedLocalMinimumCount_eq_zero_tendsto
    widthFactor (vSeq k) velocityLower velocityUpper hfactor0 hfactor1 hposK
      hvelLower hvelUpper
  have hlt := hvoid.eventually (Iio_mem_nhds hsmallK)
  filter_upwards [hle, hlt] with n hnLe hnLt
  exact hnLe.trans_lt hnLt

end Odd

end Erdos525
