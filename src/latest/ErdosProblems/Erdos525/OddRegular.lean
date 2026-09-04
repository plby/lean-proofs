import ErdosProblems.Erdos525.OddTransfer

open scoped BigOperators Topology ComplexConjugate RealInnerProductSpace

namespace Erdos525

open Classical Filter Finset Set MeasureTheory

namespace Odd


lemma globalAccelerationBound_div_tendsto_zero :
    Tendsto (fun n : ℕ ↦ globalAccelerationBound n / (n : ℝ))
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hextra := extraAccelerationBound_tendsto_zero.mul hinv
  simp only [zero_mul] at hextra
  have hsum := sqrt_centeredCount_div_tendsto_zero.add hextra
  convert hsum using 1
  · funext n
    unfold globalAccelerationBound
    simp only [add_div, div_eq_mul_inv]
    ring
  · norm_num

lemma globalAccelerationBound_mul_halfWidth_tendsto_zero :
    Tendsto (fun n : ℕ ↦ globalAccelerationBound n * localMeshHalfWidth n)
      atTop (𝓝 0) := by
  have hextra := extraAccelerationBound_tendsto_zero.mul
    localMeshHalfWidth_tendsto_zero
  simp only [zero_mul] at hextra
  have hsum := sqrt_centeredCount_mul_halfWidth_tendsto_zero.add hextra
  convert hsum using 1
  · funext n
    unfold globalAccelerationBound
    ring
  · norm_num

lemma norm_velocity_sub_le (n : ℕ) (e : SignVector (2 * n + 1))
    (x y : ℝ) :
    ‖velocity n e y - velocity n e x‖ ≤
      globalAccelerationBound n * |y - x| := by
  by_cases hxy : x ≤ y
  · have hbound := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := velocity n e) (f' := acceleration n e)
      (a := x) (b := y) (C := globalAccelerationBound n)
      (fun t _ht ↦ (hasDerivAt_velocity n e t).hasDerivWithinAt)
      (fun t _ht ↦ norm_acceleration_le n e t)
      y (Set.right_mem_Icc.mpr hxy)
    simpa [abs_of_nonneg (sub_nonneg.mpr hxy)] using hbound
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hbound := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := velocity n e) (f' := acceleration n e)
      (a := y) (b := x) (C := globalAccelerationBound n)
      (fun t _ht ↦ (hasDerivAt_velocity n e t).hasDerivWithinAt)
      (fun t _ht ↦ norm_acceleration_le n e t)
      x (Set.right_mem_Icc.mpr hyx)
    rw [← norm_neg, neg_sub]
    simpa [abs_of_nonpos (sub_nonpos.mpr hyx)] using hbound

lemma eval_neg (n : ℕ) (e : SignVector (2 * n + 1)) (t : ℝ) :
    eval n e (-t) = conj (eval n e t) := by
  unfold eval
  rw [rescaledCenteredEval_neg]
  rw [map_add, map_mul]
  congr 1
  · simp
  · rw [map_mul]
    congr 1
    · simp
    · rw [← Complex.exp_conj]
      congr 1
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

@[simp] lemma norm_eval_neg (n : ℕ) (e : SignVector (2 * n + 1)) (t : ℝ) :
    ‖eval n e (-t)‖ = ‖eval n e t‖ := by
  rw [eval_neg, Complex.norm_conj]

lemma norm_eval_nat_mul (n : ℕ) (hn : 0 < n)
    (e : SignVector (2 * n + 1)) (x : ℝ) :
    ‖eval n e (n * x)‖ = ‖oddCenteredEval n e x‖ := by
  rw [norm_eval]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  congr 2
  field_simp

lemma exists_halfPeriod_oddCenteredMin
    (n : ℕ) (hn : 0 < n) (e : SignVector (2 * n + 1)) :
    ∃ t ∈ Set.Icc (0 : ℝ) (Real.pi * n),
      ‖eval n e t‖ = oddCenteredMin n e := by
  rcases oddCenteredMin_mem_range n e with ⟨x, hx, hmin⟩
  let t : ℝ := n * |x|
  refine ⟨t, ?_, ?_⟩
  · constructor
    · exact mul_nonneg (Nat.cast_nonneg n) (abs_nonneg x)
    · have habs : |x| ≤ Real.pi := by rw [abs_le]; exact hx
      dsimp [t]
      nlinarith [show (0 : ℝ) < n by exact_mod_cast hn]
  · rw [show t = n * |x| by rfl, norm_eval_nat_mul n hn]
    by_cases hx0 : 0 ≤ x
    · rw [abs_of_nonneg hx0]
      exact hmin
    · have hxneg : x < 0 := lt_of_not_ge hx0
      rw [abs_of_neg hxneg]
      have hsym := norm_eval_neg n e (n * x)
      rw [norm_eval_nat_mul n hn,
        show -(n * x : ℝ) = n * -x by ring,
        norm_eval_nat_mul n hn] at hsym
      rw [hsym]
      exact hmin

noncomputable def energy (n : ℕ) (e : SignVector (2 * n + 1))
    (t : ℝ) : ℝ := ‖eval n e t‖ ^ 2

lemma hasDerivAt_energy (n : ℕ) (e : SignVector (2 * n + 1)) (t : ℝ) :
    HasDerivAt (energy n e)
      (2 * (eval n e t * conj (velocity n e t)).re) t := by
  have h := (hasDerivAt_eval n e t).norm_sq
  change HasDerivAt (fun s ↦ ‖eval n e s‖ ^ 2) _ t
  convert h using 1
  simp [Complex.inner, Complex.mul_re]
  ring

lemma exists_halfPeriod_oddCenteredMin_orthogonal
    (n : ℕ) (hn : 0 < n) (e : SignVector (2 * n + 1)) :
    ∃ t ∈ Set.Icc (0 : ℝ) (Real.pi * n),
      ‖eval n e t‖ = oddCenteredMin n e ∧
      (eval n e t * conj (velocity n e t)).re = 0 := by
  rcases exists_halfPeriod_oddCenteredMin n hn e with ⟨t, ht, hmin⟩
  have hlocal : IsLocalMin (energy n e) t := by
    change ∀ᶠ s in 𝓝 t, energy n e t ≤ energy n e s
    exact Eventually.of_forall fun s ↦ by
      have hle := oddCenteredMin_le_eval n hn e s
      have hnonneg : 0 ≤ oddCenteredMin n e := by
        rw [← hmin]
        exact norm_nonneg _
      unfold energy
      rw [hmin]
      exact pow_le_pow_left₀ hnonneg hle 2
  have hzero : deriv (energy n e) t = 0 := hlocal.deriv_eq_zero
  have hderiv := (hasDerivAt_energy n e t).deriv
  refine ⟨t, ht, hmin, ?_⟩
  rw [hzero] at hderiv
  linarith

noncomputable def minimumAffineOffsetError
    (n : ℕ) (u velocityLower velocityUpper : ℝ) : ℝ :=
  globalAccelerationBound n * localMeshHalfWidth n *
      (u / n + localMeshHalfWidth n * velocityUpper) /
    velocityLower ^ 2

noncomputable def minimumTransferWidthFactor
    (n : ℕ) (u velocityLower velocityUpper : ℝ) : ℝ :=
  1 + minimumAffineOffsetError n u velocityLower velocityUpper /
    localMeshHalfWidth n

noncomputable def minimumTransferHeight (n : ℕ) (u : ℝ) : ℝ :=
  u + n * globalAccelerationBound n * localMeshHalfWidth n ^ 2

noncomputable def minimumVelocityTransferError (n : ℕ) : ℝ :=
  globalAccelerationBound n * localMeshHalfWidth n

lemma minimumTransferWidthFactor_tendsto_one
    (u velocityLower velocityUpper : ℝ) (hvelocityLower : velocityLower ≠ 0) :
    Tendsto (fun n : ℕ ↦
      minimumTransferWidthFactor n u velocityLower velocityUpper)
      atTop (𝓝 1) := by
  have hfirst := globalAccelerationBound_div_tendsto_zero.const_mul u
  have hsecond := globalAccelerationBound_mul_halfWidth_tendsto_zero.const_mul
    velocityUpper
  have hfirst0 : Tendsto (fun n : ℕ ↦
      u * (globalAccelerationBound n / n)) atTop (𝓝 0) := by
    simpa using hfirst
  have hfirst' : Tendsto (fun n : ℕ ↦
      globalAccelerationBound n * (u / n)) atTop (𝓝 0) := by
    refine hfirst0.congr' (Eventually.of_forall fun n ↦ ?_)
    ring
  have hsecond0 : Tendsto (fun n : ℕ ↦
      velocityUpper * (globalAccelerationBound n * localMeshHalfWidth n))
      atTop (𝓝 0) := by
    simpa using hsecond
  have hsecond' : Tendsto (fun n : ℕ ↦
      globalAccelerationBound n * localMeshHalfWidth n * velocityUpper)
      atTop (𝓝 0) := by
    refine hsecond0.congr' (Eventually.of_forall fun n ↦ ?_)
    ring
  have hsum : Tendsto (fun n : ℕ ↦
      globalAccelerationBound n * (u / n) +
        globalAccelerationBound n * localMeshHalfWidth n * velocityUpper)
      atTop (𝓝 0) := by
    simpa using hfirst'.add hsecond'
  have hdiv := hsum.div_const (velocityLower ^ 2)
  have hdiv' : Tendsto (fun n : ℕ ↦
      (globalAccelerationBound n * (u / n) +
        globalAccelerationBound n * localMeshHalfWidth n * velocityUpper) /
          velocityLower ^ 2) atTop (𝓝 0) := by
    simpa [hvelocityLower] using hdiv
  have herror : Tendsto (fun n : ℕ ↦
      minimumAffineOffsetError n u velocityLower velocityUpper /
        localMeshHalfWidth n) atTop (𝓝 0) := by
    refine hdiv'.congr' ?_
    filter_upwards [Nat.eventually_pos] with n hn
    have hh : localMeshHalfWidth n ≠ 0 := by
      unfold localMeshHalfWidth
      exact div_ne_zero (mul_ne_zero Real.pi_ne_zero (by exact_mod_cast hn.ne'))
        (by exact_mod_cast (localMeshSize_pos n).ne')
    unfold minimumAffineOffsetError
    field_simp [hh]
  simpa [minimumTransferWidthFactor] using tendsto_const_nhds.add herror

lemma minimumTransferHeight_tendsto (u : ℝ) :
    Tendsto (fun n : ℕ ↦ minimumTransferHeight n u) atTop (𝓝 u) := by
  have hprod := scaled_localMeshHalfWidth_tendsto_pi.mul
    globalAccelerationBound_mul_halfWidth_tendsto_zero
  have hprod' : Tendsto (fun n : ℕ ↦
      ((n : ℝ) * localMeshHalfWidth n) *
        (globalAccelerationBound n * localMeshHalfWidth n))
      atTop (𝓝 0) := by
    simpa using hprod
  have hzero : Tendsto (fun n : ℕ ↦
      (n : ℝ) * globalAccelerationBound n * localMeshHalfWidth n ^ 2)
      atTop (𝓝 0) := by
    refine hprod'.congr' (Eventually.of_forall fun n ↦ ?_)
    ring
  simpa [minimumTransferHeight] using tendsto_const_nhds.add hzero

lemma minimumVelocityTransferError_tendsto_zero :
    Tendsto minimumVelocityTransferError atTop (𝓝 0) := by
  exact globalAccelerationBound_mul_halfWidth_tendsto_zero

lemma localAffineOffset_sub_minimizer_le
    (n : ℕ) (hn : 0 < n) (e : SignVector (2 * n + 1))
    (u velocityLower velocityUpper t : ℝ)
    (hmin : ‖eval n e t‖ ≤ u / n)
    (hortho : (eval n e t * conj (velocity n e t)).re = 0)
    (a : Fin (localMeshSize n))
    (haNear : |t - localMeshPoint n a| ≤ localMeshHalfWidth n)
    (hvelocityLower : 0 < velocityLower)
    (haLower : velocityLower ≤ ‖velocity n e (localMeshPoint n a)‖)
    (haUpper : ‖velocity n e (localMeshPoint n a)‖ ≤ velocityUpper) :
    |localAffineOffset n e a - (t - localMeshPoint n a)| ≤
      minimumAffineOffsetError n u velocityLower velocityUpper := by
  let x := localMeshPoint n a
  let d := t - x
  let A := eval n e x
  let B := velocity n e x
  let P := eval n e t
  let V := velocity n e t
  let R := P - (A + (d : ℂ) * B)
  let C := globalAccelerationBound n
  let h := localMeshHalfWidth n
  have hC0 : 0 ≤ C := globalAccelerationBound_nonneg n
  have hh0 : 0 ≤ h := by dsimp [h, localMeshHalfWidth]; positivity
  have hd : |d| ≤ h := by simpa [d, x] using haNear
  have hR : ‖R‖ ≤ C * h ^ 2 := by
    have hraw := norm_eval_sub_linear_le n e x t
    have hsq : (t - x) ^ 2 ≤ h ^ 2 := by
      have hs := pow_le_pow_left₀ (abs_nonneg d) hd 2
      simpa [d, sq_abs] using hs
    calc
      ‖R‖ ≤ C * (t - x) ^ 2 := by simpa [R, P, A, d, B, C] using hraw
      _ ≤ C * h ^ 2 := mul_le_mul_of_nonneg_left hsq hC0
  have hVB : ‖V - B‖ ≤ C * h := by
    have hraw := norm_velocity_sub_le n e x t
    calc
      ‖V - B‖ = ‖velocity n e t - velocity n e x‖ := by rfl
      _ ≤ C * |t - x| := by simpa [C] using hraw
      _ ≤ C * h := mul_le_mul_of_nonneg_left (by simpa [d] using hd) hC0
  have hB0 : B ≠ 0 := by
    apply norm_ne_zero_iff.mp
    exact (hvelocityLower.trans_le (by simpa [B, x] using haLower)).ne'
  have hBpos : 0 < ‖B‖ := norm_pos_iff.mpr hB0
  have hPB : |(P * conj B).re| ≤ (u / n) * (C * h) := by
    have hid : (P * conj B).re = (P * conj (B - V)).re := by
      have hcomplex : P * conj B = P * conj V + P * conj (B - V) := by
        rw [← mul_add, ← map_add]
        congr 2
        ring
      rw [hcomplex, Complex.add_re,
        show (P * conj V).re = 0 by simpa [P, V] using hortho, zero_add]
    rw [hid]
    calc
      |(P * conj (B - V)).re| ≤ ‖P * conj (B - V)‖ :=
        Complex.abs_re_le_norm _
      _ = ‖P‖ * ‖V - B‖ := by
        rw [norm_mul, Complex.norm_conj, norm_sub_rev]
      _ ≤ (u / n) * (C * h) := by
        exact mul_le_mul (by simpa [P] using hmin) hVB
          (norm_nonneg _) (by
            have := (norm_nonneg P).trans (by simpa [P] using hmin)
            exact this)
  have hRB : |(R * conj B).re| ≤ (C * h ^ 2) * velocityUpper := by
    calc
      |(R * conj B).re| ≤ ‖R * conj B‖ := Complex.abs_re_le_norm _
      _ = ‖R‖ * ‖B‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ (C * h ^ 2) * velocityUpper := by
        exact mul_le_mul hR (by simpa [B, x] using haUpper)
          (norm_nonneg _) (mul_nonneg hC0 (sq_nonneg h))
  have hnum : |((A + (d : ℂ) * B) * conj B).re| ≤
      C * h * (u / n + h * velocityUpper) := by
    have hid : ((A + (d : ℂ) * B) * conj B).re =
        (P * conj B).re - (R * conj B).re := by
      have hP : P = A + (d : ℂ) * B + R := by dsimp [R]; ring
      have hcomplex : (A + (d : ℂ) * B) * conj B =
          P * conj B - R * conj B := by rw [hP]; ring
      exact congrArg Complex.re hcomplex
    rw [hid]
    calc
      |(P * conj B).re - (R * conj B).re| ≤
          |(P * conj B).re| + |(R * conj B).re| := abs_sub _ _
      _ ≤ (u / n) * (C * h) + (C * h ^ 2) * velocityUpper :=
        add_le_add hPB hRB
      _ = C * h * (u / n + h * velocityUpper) := by ring
  have hoff : localAffineOffset n e a - d =
      -(((A + (d : ℂ) * B) * conj B).re) / Complex.normSq B := by
    change -(A * conj B).re / Complex.normSq B - d = _
    have hreal : (((d : ℂ) * B) * conj B).re = d * Complex.normSq B := by
      rw [mul_assoc, Complex.mul_conj]
      simp
    rw [add_mul, Complex.add_re, hreal]
    have hnormSq0 : Complex.normSq B ≠ 0 :=
      fun hz ↦ hB0 (Complex.normSq_eq_zero.mp hz)
    field_simp [hnormSq0]
    ring
  rw [hoff, abs_div, abs_neg,
    abs_of_nonneg (Complex.normSq_nonneg B), Complex.normSq_eq_norm_sq]
  have hden : velocityLower ^ 2 ≤ ‖B‖ ^ 2 :=
    pow_le_pow_left₀ hvelocityLower.le (by simpa [B, x] using haLower) 2
  have hdenPos : 0 < ‖B‖ ^ 2 := sq_pos_of_pos hBpos
  calc
    |((A + (d : ℂ) * B) * conj B).re| / ‖B‖ ^ 2 ≤
        (C * h * (u / n + h * velocityUpper)) / ‖B‖ ^ 2 :=
      div_le_div_of_nonneg_right hnum hdenPos.le
    _ ≤ (C * h * (u / n + h * velocityUpper)) / velocityLower ^ 2 := by
      apply div_le_div_of_nonneg_left
      · exact (abs_nonneg _).trans hnum
      · exact sq_pos_of_pos hvelocityLower
      · exact hden
    _ = minimumAffineOffsetError n u velocityLower velocityUpper := rfl

lemma abs_localSignedHeight_le_of_minimizer
    (n : ℕ) (hn : 0 < n) (e : SignVector (2 * n + 1))
    (u velocityLower t : ℝ)
    (hmin : ‖eval n e t‖ ≤ u / n)
    (a : Fin (localMeshSize n))
    (haNear : |t - localMeshPoint n a| ≤ localMeshHalfWidth n)
    (hvelocityLower : 0 < velocityLower)
    (haLower : velocityLower ≤ ‖velocity n e (localMeshPoint n a)‖) :
    |localSignedHeight n e a| ≤ minimumTransferHeight n u := by
  let x := localMeshPoint n a
  let d := t - x
  let A := eval n e x
  let B := velocity n e x
  let P := eval n e t
  let C := globalAccelerationBound n
  let h := localMeshHalfWidth n
  have hC0 : 0 ≤ C := globalAccelerationBound_nonneg n
  have hh0 : 0 ≤ h := by dsimp [h, localMeshHalfWidth]; positivity
  have hd : |d| ≤ h := by simpa [d, x] using haNear
  have hsq : d ^ 2 ≤ h ^ 2 := by
    have hs := pow_le_pow_left₀ (abs_nonneg d) hd 2
    simpa [sq_abs] using hs
  have hB0 : B ≠ 0 := by
    apply norm_ne_zero_iff.mp
    exact (hvelocityLower.trans_le (by simpa [B, x] using haLower)).ne'
  have htaylor := norm_eval_sub_linear_le n e x t
  have hlinear : ‖A + (d : ℂ) * B‖ ≤ u / n + C * h ^ 2 := by
    have htri : ‖A + (d : ℂ) * B‖ ≤
        ‖P‖ + ‖P - (A + (d : ℂ) * B)‖ := by
      have hid : A + (d : ℂ) * B = P - (P - (A + (d : ℂ) * B)) := by ring
      calc
        ‖A + (d : ℂ) * B‖ = ‖P - (P - (A + (d : ℂ) * B))‖ :=
          congrArg norm hid
        _ ≤ ‖P‖ + ‖P - (A + (d : ℂ) * B)‖ :=
          norm_sub_le P (P - (A + (d : ℂ) * B))
    calc
      ‖A + (d : ℂ) * B‖ ≤ ‖P‖ + ‖P - (A + (d : ℂ) * B)‖ := htri
      _ ≤ u / n + C * d ^ 2 := by
        exact add_le_add (by simpa [P] using hmin)
          (by simpa [P, A, d, B, C] using htaylor)
      _ ≤ u / n + C * h ^ 2 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq hC0)
  have hclosest := affine_closest_min A B hB0 d
  have hheightNorm := norm_localAffineValue n hn e a (by simpa [B, x] using hB0)
  have hdiv : |localSignedHeight n e a| / n ≤ u / n + C * h ^ 2 := by
    rw [← hheightNorm]
    exact hclosest.trans (by simpa [A, B, d, x, localAffineOffset] using hlinear)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    |localSignedHeight n e a| = n * (|localSignedHeight n e a| / n) := by
      field_simp
    _ ≤ n * (u / n + C * h ^ 2) :=
      mul_le_mul_of_nonneg_left hdiv hnR.le
    _ = minimumTransferHeight n u := by
      unfold minimumTransferHeight
      dsimp [C, h]
      field_simp [hnR.ne']

lemma isFactoredTruncatedLocalRepresentative_of_minimizer
    (n : ℕ) (hn : 0 < n) (e : SignVector (2 * n + 1))
    (u velocityLower velocityUpper t : ℝ)
    (hmin : ‖eval n e t‖ ≤ u / n)
    (hortho : (eval n e t * conj (velocity n e t)).re = 0)
    (a : Fin (localMeshSize n))
    (haNear : |t - localMeshPoint n a| ≤ localMeshHalfWidth n)
    (hvelocityLower : 0 < velocityLower)
    (haLower : velocityLower ≤ ‖velocity n e (localMeshPoint n a)‖)
    (haUpper : ‖velocity n e (localMeshPoint n a)‖ ≤ velocityUpper) :
    IsFactoredTruncatedLocalRepresentative n
      (minimumTransferWidthFactor n u velocityLower velocityUpper)
      (minimumTransferHeight n u) velocityLower velocityUpper e a := by
  let s := localAffineOffset n e a
  let d := t - localMeshPoint n a
  let h := localMeshHalfWidth n
  let err := minimumAffineOffsetError n u velocityLower velocityUpper
  have hhpos : 0 < h := by
    dsimp [h]
    unfold localMeshHalfWidth
    exact div_pos (mul_pos Real.pi_pos (by exact_mod_cast hn))
      (by exact_mod_cast localMeshSize_pos n)
  have hsminus : |s - d| ≤ err := by
    simpa [s, d, err] using localAffineOffset_sub_minimizer_le
      n hn e u velocityLower velocityUpper t hmin hortho a haNear
        hvelocityLower haLower haUpper
  have hd : |d| ≤ h := by simpa [d, h] using haNear
  have hs : |s| ≤ (1 + err / h) * h := by
    calc
      |s| = |(s - d) + d| := by ring_nf
      _ ≤ |s - d| + |d| := abs_add_le _ _
      _ ≤ err + h := add_le_add hsminus hd
      _ = (1 + err / h) * h := by field_simp [hhpos.ne']; ring
  have hheight := abs_localSignedHeight_le_of_minimizer
    n hn e u velocityLower t hmin a haNear hvelocityLower haLower
  refine ⟨?_, ?_, hheight, haLower, haUpper⟩
  · apply norm_ne_zero_iff.mp
    exact (hvelocityLower.trans_le haLower).ne'
  · simpa [minimumTransferWidthFactor, s, h, err] using hs

lemma abs_norm_velocity_sub_le_of_near
    (n : ℕ) (e : SignVector (2 * n + 1)) (t : ℝ)
    (a : Fin (localMeshSize n))
    (haNear : |t - localMeshPoint n a| ≤ localMeshHalfWidth n) :
    |‖velocity n e (localMeshPoint n a)‖ - ‖velocity n e t‖| ≤
      minimumVelocityTransferError n := by
  have hvel := norm_velocity_sub_le n e t (localMeshPoint n a)
  calc
    |‖velocity n e (localMeshPoint n a)‖ - ‖velocity n e t‖| ≤
      ‖velocity n e (localMeshPoint n a) - velocity n e t‖ :=
      abs_norm_sub_norm_le _ _
    _ ≤ globalAccelerationBound n * |localMeshPoint n a - t| := hvel
    _ ≤ minimumVelocityTransferError n := by
      unfold minimumVelocityTransferError
      rw [abs_sub_comm]
      exact mul_le_mul_of_nonneg_left haNear (globalAccelerationBound_nonneg n)

lemma exists_smooth_factoredTruncatedLocalRepresentative_of_minimizer
    (n : ℕ) (hn : 0 < n) (e : SignVector (2 * n + 1))
    (u velocityLower velocityUpper t : ℝ)
    (hwidth : 2 * localMeshHalfWidth n <
      Real.pi * (2 * rigiditySmoothScale n))
    (hnearestSmooth : ∀ a : Fin (localMeshSize n),
      |t - localMeshPoint n a| ≤ localMeshHalfWidth n →
      IsSmooth n (rigiditySmoothScale n) (localMeshPoint n a))
    (htSmooth : IsSmooth n (2 * rigiditySmoothScale n) t)
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi * n))
    (hmin : ‖eval n e t‖ ≤ u / n)
    (hortho : (eval n e t * conj (velocity n e t)).re = 0)
    (hvelocityLower : 0 < velocityLower)
    (htLower : velocityLower + minimumVelocityTransferError n ≤
      ‖velocity n e t‖)
    (htUpper : ‖velocity n e t‖ ≤
      velocityUpper - minimumVelocityTransferError n) :
    ∃ a ∈ halfSmoothLocalMeshSites n,
      IsFactoredTruncatedLocalRepresentative n
        (minimumTransferWidthFactor n u velocityLower velocityUpper)
        (minimumTransferHeight n u) velocityLower velocityUpper e a := by
  rcases exists_halfLocalMeshSite_within_halfWidth n hn
      (2 * rigiditySmoothScale n) t hwidth htSmooth ht with
    ⟨a, haHalf, haNear⟩
  have haSmooth := hnearestSmooth a haNear
  have hvelocityDiff := abs_norm_velocity_sub_le_of_near n e t a haNear
  have hdiffLower : ‖velocity n e t‖ - minimumVelocityTransferError n ≤
      ‖velocity n e (localMeshPoint n a)‖ := by
    rw [abs_le] at hvelocityDiff
    linarith [hvelocityDiff.2]
  have haLower : velocityLower ≤ ‖velocity n e (localMeshPoint n a)‖ :=
    (by linarith : velocityLower ≤
      ‖velocity n e t‖ - minimumVelocityTransferError n).trans hdiffLower
  have hdiffUpper : ‖velocity n e (localMeshPoint n a)‖ ≤
      ‖velocity n e t‖ + minimumVelocityTransferError n := by
    rw [abs_le] at hvelocityDiff
    linarith [hvelocityDiff.1]
  have haUpper : ‖velocity n e (localMeshPoint n a)‖ ≤ velocityUpper :=
    hdiffUpper.trans (by linarith)
  refine ⟨a, Finset.mem_filter.mpr ⟨haHalf, haSmooth⟩,
    isFactoredTruncatedLocalRepresentative_of_minimizer
      n hn e u velocityLower velocityUpper t hmin hortho a haNear
        hvelocityLower haLower haUpper⟩

end Odd

end Erdos525
