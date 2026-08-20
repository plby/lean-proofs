import ErdosProblems.Erdos525.OddCount

open scoped BigOperators Topology ComplexConjugate RealInnerProductSpace

namespace Erdos525

open Classical Filter Finset Set MeasureTheory

namespace Odd


def HasHighPrefixFineMeshAcceleration (k n : ℕ)
    (e : SignVector (2 * n + 1)) : Prop :=
  HasHighFineMeshAcceleration k n (initialSegment n e)

lemma uniformProbability_highPrefixFineMeshAcceleration (k n : ℕ) :
    uniformProbability (HasHighPrefixFineMeshAcceleration k n) =
      uniformProbability (HasHighFineMeshAcceleration k n) := by
  rw [uniformProbability_split]
  simp only [HasHighPrefixFineMeshAcceleration, initialSegment_appendSign]
  ring

theorem localMeshSize_pow_mul_highPrefixFineMeshAcceleration_tendsto_zero
    (k d : ℕ) :
    Tendsto (fun n : ℕ ↦ (localMeshSize n : ℝ) ^ d *
      uniformProbability (HasHighPrefixFineMeshAcceleration k n))
      atTop (𝓝 0) := by
  apply (localMeshSize_pow_mul_highFineMeshAcceleration_tendsto_zero k d).congr'
  exact Eventually.of_forall fun n ↦ by
    simp only
    rw [uniformProbability_highPrefixFineMeshAcceleration]

noncomputable def extraAccelerationBound (n : ℕ) : ℝ :=
  (((n + 1 : ℕ) : ℝ) / n) ^ 2 / Real.sqrt (2 * n + 2 : ℝ)

lemma extraAccelerationBound_nonneg (n : ℕ) :
    0 ≤ extraAccelerationBound n := by
  unfold extraAccelerationBound
  positivity

lemma norm_extra_acceleration (n : ℕ) (b : Bool) (t : ℝ) :
    ‖((sign b / Real.sqrt (2 * n + 2 : ℝ) : ℝ) : ℂ) *
        (((((n + 1 : ℕ) : ℝ) / n : ℂ) * Complex.I) ^ 2) *
        Complex.exp ((((n + 1 : ℕ) : ℝ) * (t / n) : ℂ) * Complex.I)‖ =
      extraAccelerationBound n := by
  simp [extraAccelerationBound, norm_mul, Complex.norm_exp, Real.norm_eq_abs,
    abs_div, abs_sign, abs_of_nonneg]
  rw [show ‖((n : ℕ) : ℂ) + 1‖ = (n : ℝ) + 1 by
    rw [← Nat.cast_one, ← Nat.cast_add, Complex.norm_natCast]
    norm_num]
  ring

noncomputable def fineGlobalAccelerationBound (k n : ℕ) : ℝ :=
  Erdos525.fineGlobalAccelerationBound k n + extraAccelerationBound n

lemma fineGlobalAccelerationBound_nonneg (k n : ℕ) :
    0 ≤ fineGlobalAccelerationBound k n := by
  unfold fineGlobalAccelerationBound Erdos525.fineGlobalAccelerationBound
  exact add_nonneg
    (add_nonneg (rigidityPower_nonneg n _)
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (by unfold localMeshHalfWidth; positivity)))
    (extraAccelerationBound_nonneg n)

lemma norm_acceleration_le_of_not_highPrefixFine
    (k n : ℕ) (hn : 0 < n) (e : SignVector (2 * n + 1))
    (hgood : ¬HasHighPrefixFineMeshAcceleration k n e)
    (t : ℝ) (ht : t ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n)) :
    ‖acceleration n e t‖ ≤ fineGlobalAccelerationBound k n := by
  have hprefix := norm_rescaledCenteredAcceleration_le_of_not_highFine
    k n hn (initialSegment n e) hgood t ht
  unfold acceleration fineGlobalAccelerationBound
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
    _ ≤ Erdos525.fineGlobalAccelerationBound k n + extraAccelerationBound n := by
      gcongr
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (prefixScale_le_one n)).trans hprefix

lemma norm_eval_sub_linear_le_of_not_highPrefixFine
    (k n : ℕ) (hn : 0 < n) (e : SignVector (2 * n + 1))
    (hgood : ¬HasHighPrefixFineMeshAcceleration k n e)
    (x y : ℝ)
    (hx : x ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n))
    (hy : y ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n)) :
    ‖eval n e y - (eval n e x + ((y - x : ℝ) : ℂ) * velocity n e x)‖ ≤
      fineGlobalAccelerationBound k n * (y - x) ^ 2 := by
  by_cases hxy : x ≤ y
  · apply norm_taylor_sub_le_of_le_on
      (eval n e) (velocity n e) (acceleration n e)
      (fineGlobalAccelerationBound k n) x y hxy
      (hasDerivAt_eval n e) (hasDerivAt_velocity n e)
    · exact fineGlobalAccelerationBound_nonneg k n
    · intro t htseg
      apply norm_acceleration_le_of_not_highPrefixFine k n hn e hgood
      exact ⟨hx.1.trans htseg.1, htseg.2.trans hy.2⟩
  · have hyx : y ≤ x := le_of_not_ge hxy
    apply norm_taylor_sub_le_of_ge_on
      (eval n e) (velocity n e) (acceleration n e)
      (fineGlobalAccelerationBound k n) x y hyx
      (hasDerivAt_eval n e) (hasDerivAt_velocity n e)
    · exact fineGlobalAccelerationBound_nonneg k n
    · intro t htseg
      apply norm_acceleration_le_of_not_highPrefixFine k n hn e hgood
      exact ⟨hy.1.trans htseg.1, htseg.2.trans hx.2⟩

lemma norm_velocity_sub_le_of_not_highPrefixFine
    (k n : ℕ) (hn : 0 < n) (e : SignVector (2 * n + 1))
    (hgood : ¬HasHighPrefixFineMeshAcceleration k n e)
    (x y : ℝ)
    (hx : x ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n))
    (hy : y ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n)) :
    ‖velocity n e y - velocity n e x‖ ≤
      fineGlobalAccelerationBound k n * |y - x| := by
  by_cases hxy : x ≤ y
  · have hbound := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := velocity n e) (f' := acceleration n e)
      (a := x) (b := y) (C := fineGlobalAccelerationBound k n)
      (fun t _ht ↦ (hasDerivAt_velocity n e t).hasDerivWithinAt)
      (fun t ht ↦ norm_acceleration_le_of_not_highPrefixFine
        k n hn e hgood t ⟨hx.1.trans ht.1, ht.2.le.trans hy.2⟩)
      y (Set.right_mem_Icc.mpr hxy)
    simpa [abs_of_nonneg (sub_nonneg.mpr hxy)] using hbound
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hbound := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := velocity n e) (f' := acceleration n e)
      (a := y) (b := x) (C := fineGlobalAccelerationBound k n)
      (fun t _ht ↦ (hasDerivAt_velocity n e t).hasDerivWithinAt)
      (fun t ht ↦ norm_acceleration_le_of_not_highPrefixFine
        k n hn e hgood t ⟨hy.1.trans ht.1, ht.2.le.trans hx.2⟩)
      x (Set.right_mem_Icc.mpr hyx)
    rw [← norm_neg, neg_sub]
    simpa [abs_of_nonpos (sub_nonpos.mpr hyx)] using hbound

lemma extraAccelerationBound_le {n : ℕ} (hn : 0 < n) :
    extraAccelerationBound n ≤ 4 / Real.sqrt (2 * n + 2 : ℝ) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 : 0 ≤ ((n + 1 : ℕ) : ℝ) / n := by positivity
  have hq : ((n + 1 : ℕ) : ℝ) / n ≤ 2 := by
    rw [div_le_iff₀ hnreal]
    push_cast
    linarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]
  unfold extraAccelerationBound
  gcongr
  nlinarith

lemma extraAccelerationBound_tendsto_zero :
    Tendsto extraAccelerationBound atTop (𝓝 0) := by
  have hsqrtTop : Tendsto (fun n : ℕ ↦ Real.sqrt (2 * n + 2 : ℝ))
      atTop atTop := by
    apply Real.tendsto_sqrt_atTop.comp
    have htwo : Tendsto (fun n : ℕ ↦ (2 : ℝ) * n) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num)
    simpa only [Nat.cast_ofNat, Nat.cast_add, Nat.cast_mul] using
      tendsto_atTop_add_const_right atTop (2 : ℝ) htwo
  have hinv : Tendsto (fun n : ℕ ↦
      (Real.sqrt (2 * n + 2 : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrtTop
  have hupper := hinv.const_mul 4
  simp only [mul_zero] at hupper
  apply squeeze_zero' (Eventually.of_forall extraAccelerationBound_nonneg)
  · filter_upwards [Nat.eventually_pos] with n hn
    simpa [div_eq_mul_inv] using extraAccelerationBound_le hn
  · simpa [mul_comm] using hupper

lemma fineGlobalAccelerationBound_div_tendsto_zero (k : ℕ) :
    Tendsto (fun n : ℕ ↦ fineGlobalAccelerationBound k n / (n : ℝ))
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hextra := extraAccelerationBound_tendsto_zero.mul hinv
  simp only [zero_mul] at hextra
  have hsum := Erdos525.fineGlobalAccelerationBound_div_tendsto_zero k |>.add hextra
  convert hsum using 1
  · funext n
    unfold fineGlobalAccelerationBound
    simp only [add_div, div_eq_mul_inv]
    ring
  · norm_num

lemma fineGlobalAccelerationBound_mul_halfWidth_tendsto_zero (k : ℕ) :
    Tendsto (fun n : ℕ ↦
      fineGlobalAccelerationBound k n * localMeshHalfWidth n)
      atTop (𝓝 0) := by
  have hextra := extraAccelerationBound_tendsto_zero.mul
    localMeshHalfWidth_tendsto_zero
  simp only [zero_mul] at hextra
  have hsum := Erdos525.fineGlobalAccelerationBound_mul_halfWidth_tendsto_zero k
    |>.add hextra
  convert hsum using 1
  · funext n
    unfold fineGlobalAccelerationBound
    ring
  · norm_num

lemma fineGlobalAccelerationBound_mul_weakSpread_tendsto_zero (k : ℕ) :
    Tendsto (fun n : ℕ ↦
      fineGlobalAccelerationBound k n * weakSpreadScale k n)
      atTop (𝓝 0) := by
  have hextra := extraAccelerationBound_tendsto_zero.mul
    (weakSpreadScale_tendsto_zero k)
  simp only [zero_mul] at hextra
  have hsum := Erdos525.fineGlobalAccelerationBound_mul_weakSpread_tendsto_zero k
    |>.add hextra
  convert hsum using 1
  · funext n
    unfold fineGlobalAccelerationBound
    ring
  · norm_num

lemma norm_localAffineValue (n : ℕ) (hn : 0 < n)
    (e : SignVector (2 * n + 1)) (a : Fin (localMeshSize n))
    (hvel : velocity n e (localMeshPoint n a) ≠ 0) :
    ‖eval n e (localMeshPoint n a) +
        (localAffineOffset n e a : ℂ) * velocity n e (localMeshPoint n a)‖ =
      |localSignedHeight n e a| / n := by
  change
    ‖eval n e (localMeshPoint n a) +
        (affineClosestOffset (eval n e (localMeshPoint n a))
          (velocity n e (localMeshPoint n a)) : ℂ) *
          velocity n e (localMeshPoint n a)‖ = _
  rw [affine_closest_norm _ _ hvel]
  unfold localSignedHeight
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hnorm : 0 < ‖velocity n e (localMeshPoint n a)‖ :=
    norm_pos_iff.mpr hvel
  rw [abs_mul, abs_of_pos hnreal, abs_div, abs_of_nonneg (norm_nonneg _)]
  field_simp

lemma IsTruncatedLocalRepresentative.affine_norm_le
    {n : ℕ} (hn : 0 < n) {u velocityLower velocityUpper : ℝ}
    {e : SignVector (2 * n + 1)} {a : Fin (localMeshSize n)}
    (h : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a) :
    ‖eval n e (localMeshPoint n a) +
        (localAffineOffset n e a : ℂ) * velocity n e (localMeshPoint n a)‖ ≤
      u / n := by
  rw [norm_localAffineValue n hn e a h.1.1]
  exact div_le_div_of_nonneg_right h.1.2.2 (Nat.cast_nonneg n)

lemma isFactoredTruncatedLocalRepresentative_to_truncated
    (n : ℕ) (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor : widthFactor ≤ 1) (e : SignVector (2 * n + 1))
    (a : Fin (localMeshSize n))
    (h : IsFactoredTruncatedLocalRepresentative n widthFactor u
      velocityLower velocityUpper e a) :
    IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a := by
  refine ⟨⟨h.1, ?_, h.2.2.1⟩, h.2.2.2.1, h.2.2.2.2⟩
  exact h.2.1.trans (mul_le_of_le_one_left
    (by unfold localMeshHalfWidth; positivity) hfactor)

lemma localRepresentative_pair_affine_displacement_bound_fine
    (k n : ℕ) (hn : 0 < n) (e : SignVector (2 * n + 1))
    (hgood : ¬HasHighPrefixFineMeshAcceleration k n e)
    (u velocityLower velocityUpper : ℝ)
    (a b : Fin (localMeshSize n))
    (ha : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)
    (hb : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e b) :
    velocityLower *
        |(localMeshPoint n b + localAffineOffset n e b) -
          (localMeshPoint n a + localAffineOffset n e a)| ≤
      2 * (u / n) +
        fineGlobalAccelerationBound k n *
          (localMeshPoint n b - localMeshPoint n a) ^ 2 +
        localMeshHalfWidth n *
          (fineGlobalAccelerationBound k n *
            |localMeshPoint n b - localMeshPoint n a|) := by
  let x : ℝ := localMeshPoint n a
  let y : ℝ := localMeshPoint n b
  let sx : ℝ := localAffineOffset n e a
  let sy : ℝ := localAffineOffset n e b
  let X : ℂ := eval n e x
  let Y : ℂ := eval n e y
  let Bx : ℂ := velocity n e x
  let By : ℂ := velocity n e y
  let Ax : ℂ := X + (sx : ℂ) * Bx
  let Ay : ℂ := Y + (sy : ℂ) * By
  let R : ℂ := Y - (X + ((y - x : ℝ) : ℂ) * Bx)
  let dr : ℝ := (y + sy) - (x + sx)
  have hx : x ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n) :=
    ⟨(localMeshPoint_mem_Ico n hn a).1,
      (localMeshPoint_mem_Ico n hn a).2.le⟩
  have hy : y ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n) :=
    ⟨(localMeshPoint_mem_Ico n hn b).1,
      (localMeshPoint_mem_Ico n hn b).2.le⟩
  have hAx : ‖Ax‖ ≤ u / n := by
    simpa [Ax, X, Bx, sx, x] using ha.affine_norm_le hn
  have hAy : ‖Ay‖ ≤ u / n := by
    simpa [Ay, Y, By, sy, y] using hb.affine_norm_le hn
  have hR : ‖R‖ ≤ fineGlobalAccelerationBound k n * (y - x) ^ 2 := by
    simpa [R, X, Y, Bx] using
      norm_eval_sub_linear_le_of_not_highPrefixFine
        k n hn e hgood x y hx hy
  have hvel : ‖By - Bx‖ ≤
      fineGlobalAccelerationBound k n * |y - x| := by
    simpa [Bx, By] using
      norm_velocity_sub_le_of_not_highPrefixFine
        k n hn e hgood x y hx hy
  have hsy : |sy| ≤ localMeshHalfWidth n := by
    simpa [sy] using hb.1.2.1
  have hBx : velocityLower ≤ ‖Bx‖ := by
    simpa [Bx, x] using ha.2.1
  have hid : Ay - Ax =
      (dr : ℂ) * Bx + R + (sy : ℂ) * (By - Bx) := by
    dsimp [Ay, Ax, dr, R]
    simp only [Complex.ofReal_add, Complex.ofReal_sub]
    ring
  have hdrnorm : |dr| * ‖Bx‖ ≤
      ‖Ay - Ax‖ + ‖R‖ + ‖(sy : ℂ) * (By - Bx)‖ := by
    have hrearrange : (dr : ℂ) * Bx =
        (Ay - Ax) - R - (sy : ℂ) * (By - Bx) := by
      rw [hid]
      abel
    calc
      |dr| * ‖Bx‖ = ‖(dr : ℂ) * Bx‖ := by simp
      _ = ‖(Ay - Ax) - R - (sy : ℂ) * (By - Bx)‖ := by rw [hrearrange]
      _ ≤ ‖(Ay - Ax) - R‖ + ‖(sy : ℂ) * (By - Bx)‖ := norm_sub_le _ _
      _ ≤ (‖Ay - Ax‖ + ‖R‖) + ‖(sy : ℂ) * (By - Bx)‖ := by
        exact add_le_add (norm_sub_le (Ay - Ax) R) le_rfl
  have hleft : velocityLower * |dr| ≤ |dr| * ‖Bx‖ := by
    rw [mul_comm velocityLower]
    exact mul_le_mul_of_nonneg_left hBx (abs_nonneg dr)
  calc
    velocityLower * |dr| ≤ |dr| * ‖Bx‖ := hleft
    _ ≤ ‖Ay - Ax‖ + ‖R‖ + ‖(sy : ℂ) * (By - Bx)‖ := hdrnorm
    _ ≤ (‖Ay‖ + ‖Ax‖) + ‖R‖ + (|sy| * ‖By - Bx‖) := by
      gcongr
      · exact norm_sub_le Ay Ax
      · simp
    _ ≤ (u / n + u / n) +
          fineGlobalAccelerationBound k n * (y - x) ^ 2 +
          (localMeshHalfWidth n *
            (fineGlobalAccelerationBound k n * |y - x|)) := by
      have hhalf : 0 ≤ localMeshHalfWidth n := by
        unfold localMeshHalfWidth
        positivity
      exact add_le_add
        (add_le_add (add_le_add hAy hAx) hR)
        (mul_le_mul hsy hvel (norm_nonneg _) hhalf)
    _ = 2 * (u / n) +
        fineGlobalAccelerationBound k n * (y - x) ^ 2 +
        localMeshHalfWidth n *
          (fineGlobalAccelerationBound k n * |y - x|) := by ring

lemma localMeshCenterDistance_le_of_two_representatives_fine
    (k n : ℕ) (hn : 0 < n) (e : SignVector (2 * n + 1))
    (hgood : ¬HasHighPrefixFineMeshAcceleration k n e)
    (u velocityLower velocityUpper : ℝ)
    (hu : 0 ≤ u) (hvelocityLower : 0 < velocityLower)
    (a b : Fin (localMeshSize n))
    (ha : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)
    (hb : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e b)
    (hquadratic : fineGlobalAccelerationBound k n *
      |localMeshPoint n b - localMeshPoint n a| ≤ velocityLower / 4)
    (hcell : fineGlobalAccelerationBound k n * localMeshHalfWidth n ≤
      velocityLower / 4) :
    |localMeshPoint n b - localMeshPoint n a| ≤
      4 * localMeshHalfWidth n + 4 * (u / n) / velocityLower := by
  let x : ℝ := localMeshPoint n a
  let y : ℝ := localMeshPoint n b
  let sx : ℝ := localAffineOffset n e a
  let sy : ℝ := localAffineOffset n e b
  let h : ℝ := localMeshHalfWidth n
  let C : ℝ := fineGlobalAccelerationBound k n
  let d : ℝ := |y - x|
  let q : ℝ := u / n
  have hd : 0 ≤ d := abs_nonneg _
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hC : 0 ≤ C := by exact fineGlobalAccelerationBound_nonneg k n
  have hh : 0 ≤ h := by dsimp [h, localMeshHalfWidth]; positivity
  have hsx : |sx| ≤ h := by simpa [sx, h] using ha.1.2.1
  have hsy : |sy| ≤ h := by simpa [sy, h] using hb.1.2.1
  have hadjusted : d - 2 * h ≤ |(y + sy) - (x + sx)| :=
    centerDistance_sub_offsets_le_adjustedDistance x y sx sy h hsx hsy
  have hpair : velocityLower * |(y + sy) - (x + sx)| ≤
      2 * q + C * d ^ 2 + h * (C * d) := by
    simpa [x, y, sx, sy, h, C, d, q, sq_abs] using
      localRepresentative_pair_affine_displacement_bound_fine
        k n hn e hgood u velocityLower velocityUpper a b ha hb
  have hleft : velocityLower * (d - 2 * h) ≤
      velocityLower * |(y + sy) - (x + sx)| :=
    mul_le_mul_of_nonneg_left hadjusted hvelocityLower.le
  have hquad : C * d ≤ velocityLower / 4 := by
    simpa [C, d, x, y] using hquadratic
  have hcell' : C * h ≤ velocityLower / 4 := by
    simpa [C, h, mul_comm] using hcell
  have hquadTerm : C * d ^ 2 ≤ velocityLower / 4 * d := by
    calc
      C * d ^ 2 = (C * d) * d := by ring
      _ ≤ (velocityLower / 4) * d :=
        mul_le_mul_of_nonneg_right hquad hd
  have hcellTerm : h * (C * d) ≤ velocityLower / 4 * d := by
    calc
      h * (C * d) = (C * h) * d := by ring
      _ ≤ (velocityLower / 4) * d :=
        mul_le_mul_of_nonneg_right hcell' hd
  have hmul : velocityLower * d ≤ 4 * velocityLower * h + 4 * q := by
    nlinarith [hleft.trans hpair]
  calc
    d = (velocityLower * d) / velocityLower := by field_simp
    _ ≤ (4 * velocityLower * h + 4 * q) / velocityLower :=
      div_le_div_of_nonneg_right hmul hvelocityLower.le
    _ = 4 * h + 4 * q / velocityLower := by field_simp

lemma localRepresentative_pair_affine_location_bound_fine
    (k n : ℕ) (hn : 0 < n) (e : SignVector (2 * n + 1))
    (hgood : ¬HasHighPrefixFineMeshAcceleration k n e)
    (u velocityLower velocityUpper : ℝ)
    (hu : 0 ≤ u) (hvelocityLower : 0 ≤ velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper)
    (a b : Fin (localMeshSize n))
    (ha : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)
    (hb : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e b) :
    velocityLower ^ 2 *
        |(localMeshPoint n b + localAffineOffset n e b) -
          (localMeshPoint n a + localAffineOffset n e a)| ≤
      (u / n) *
          (fineGlobalAccelerationBound k n *
            |localMeshPoint n b - localMeshPoint n a|) +
        (fineGlobalAccelerationBound k n *
            (localMeshPoint n b - localMeshPoint n a) ^ 2) *
          velocityUpper +
        localMeshHalfWidth n *
          (fineGlobalAccelerationBound k n *
            |localMeshPoint n b - localMeshPoint n a|) *
          velocityUpper := by
  let x : ℝ := localMeshPoint n a
  let y : ℝ := localMeshPoint n b
  let sx : ℝ := localAffineOffset n e a
  let sy : ℝ := localAffineOffset n e b
  let X : ℂ := eval n e x
  let Y : ℂ := eval n e y
  let Bx : ℂ := velocity n e x
  let By : ℂ := velocity n e y
  let Ax : ℂ := X + (sx : ℂ) * Bx
  let Ay : ℂ := Y + (sy : ℂ) * By
  let R : ℂ := Y - (X + ((y - x : ℝ) : ℂ) * Bx)
  let dr : ℝ := (y + sy) - (x + sx)
  have hx : x ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n) :=
    ⟨(localMeshPoint_mem_Ico n hn a).1,
      (localMeshPoint_mem_Ico n hn a).2.le⟩
  have hy : y ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n) :=
    ⟨(localMeshPoint_mem_Ico n hn b).1,
      (localMeshPoint_mem_Ico n hn b).2.le⟩
  have hAy : ‖Ay‖ ≤ u / n := by
    simpa [Ay, Y, By, sy, y] using hb.affine_norm_le hn
  have hR : ‖R‖ ≤ fineGlobalAccelerationBound k n * (y - x) ^ 2 := by
    simpa [R, X, Y, Bx] using
      norm_eval_sub_linear_le_of_not_highPrefixFine k n hn e hgood x y hx hy
  have hvel : ‖By - Bx‖ ≤
      fineGlobalAccelerationBound k n * |y - x| := by
    simpa [Bx, By] using
      norm_velocity_sub_le_of_not_highPrefixFine k n hn e hgood x y hx hy
  have hsy : |sy| ≤ localMeshHalfWidth n := by
    simpa [sy] using hb.1.2.1
  have hBxLower : velocityLower ≤ ‖Bx‖ := by
    simpa [Bx, x] using ha.2.1
  have hBxUpper : ‖Bx‖ ≤ velocityUpper := by
    simpa [Bx, x] using ha.2.2
  have hBx : Bx ≠ 0 := by simpa [Bx, x] using ha.1.1
  have hBy : By ≠ 0 := by simpa [By, y] using hb.1.1
  have hAxOrth : (Ax * conj Bx).re = 0 := by
    simpa [Ax, X, Bx, sx, x, localAffineOffset] using
      affineClosestOffset_real_projection_zero X Bx hBx
  have hAyOrth : (Ay * conj By).re = 0 := by
    simpa [Ay, Y, By, sy, y, localAffineOffset] using
      affineClosestOffset_real_projection_zero Y By hBy
  have hid : Ay - Ax =
      (dr : ℂ) * Bx + R + (sy : ℂ) * (By - Bx) := by
    dsimp [Ay, Ax, dr, R]
    simp only [Complex.ofReal_add, Complex.ofReal_sub]
    ring
  have hprojection : dr * Complex.normSq Bx =
      (Ay * conj (Bx - By)).re - (R * conj Bx).re -
        (((sy : ℂ) * (By - Bx)) * conj Bx).re := by
    have hrearrange : (dr : ℂ) * Bx =
        (Ay - Ax) - R - (sy : ℂ) * (By - Bx) := by
      rw [hid]
      abel
    have hAyRewrite : (Ay * conj Bx).re =
        (Ay * conj (Bx - By)).re := by
      have hc : conj Bx = conj (Bx - By) + conj By := by
        rw [map_sub]
        ring
      rw [hc, mul_add, Complex.add_re, hAyOrth, add_zero]
    calc
      dr * Complex.normSq Bx = (((dr : ℂ) * Bx) * conj Bx).re := by
        simp [Complex.normSq_apply]
        ring
      _ = (((Ay - Ax) - R - (sy : ℂ) * (By - Bx)) * conj Bx).re := by
        rw [hrearrange]
      _ = (Ay * conj (Bx - By)).re - (R * conj Bx).re -
          (((sy : ℂ) * (By - Bx)) * conj Bx).re := by
        simp only [sub_mul, Complex.sub_re, map_sub]
        rw [hAyRewrite, hAxOrth]
        rw [map_sub, mul_sub, Complex.sub_re]
        ring
  have hprojectionAbs : |dr| * ‖Bx‖ ^ 2 ≤
      ‖Ay‖ * ‖By - Bx‖ + ‖R‖ * ‖Bx‖ +
        |sy| * ‖By - Bx‖ * ‖Bx‖ := by
    have habs := congrArg abs hprojection
    rw [abs_mul, abs_of_nonneg (Complex.normSq_nonneg Bx),
      Complex.normSq_eq_norm_sq] at habs
    rw [habs]
    calc
      |(Ay * conj (Bx - By)).re - (R * conj Bx).re -
          (((sy : ℂ) * (By - Bx)) * conj Bx).re| ≤
        |(Ay * conj (Bx - By)).re| + |(R * conj Bx).re| +
          |(((sy : ℂ) * (By - Bx)) * conj Bx).re| := by
        exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ ‖Ay * conj (Bx - By)‖ + ‖R * conj Bx‖ +
          ‖((sy : ℂ) * (By - Bx)) * conj Bx‖ := by
        gcongr <;> exact Complex.abs_re_le_norm _
      _ = ‖Ay‖ * ‖By - Bx‖ + ‖R‖ * ‖Bx‖ +
          |sy| * ‖By - Bx‖ * ‖Bx‖ := by
        simp only [norm_mul, Complex.norm_conj, Complex.norm_real,
          Real.norm_eq_abs]
        rw [norm_sub_rev Bx By]
  have hleft : velocityLower ^ 2 * |dr| ≤ |dr| * ‖Bx‖ ^ 2 := by
    have hsquare : velocityLower ^ 2 ≤ ‖Bx‖ ^ 2 :=
      (sq_le_sq₀ hvelocityLower (norm_nonneg Bx)).2 hBxLower
    nlinarith [abs_nonneg dr]
  calc
    velocityLower ^ 2 * |dr| ≤ |dr| * ‖Bx‖ ^ 2 := hleft
    _ ≤ ‖Ay‖ * ‖By - Bx‖ + ‖R‖ * ‖Bx‖ +
          |sy| * ‖By - Bx‖ * ‖Bx‖ := hprojectionAbs
    _ ≤ (u / n) * (fineGlobalAccelerationBound k n * |y - x|) +
          (fineGlobalAccelerationBound k n * (y - x) ^ 2) * velocityUpper +
          localMeshHalfWidth n *
            (fineGlobalAccelerationBound k n * |y - x|) * velocityUpper := by
      have hnR : (0 : ℝ) ≤ n := by positivity
      have hC : 0 ≤ fineGlobalAccelerationBound k n :=
        fineGlobalAccelerationBound_nonneg k n
      have hhalf : 0 ≤ localMeshHalfWidth n := by
        unfold localMeshHalfWidth
        positivity
      exact add_le_add
        (add_le_add
          (mul_le_mul hAy hvel (norm_nonneg _) (div_nonneg hu hnR))
          (mul_le_mul hR hBxUpper (norm_nonneg _)
            (mul_nonneg hC (sq_nonneg _))))
        (mul_le_mul
          (mul_le_mul hsy hvel (norm_nonneg _) hhalf)
          hBxUpper (norm_nonneg _) (mul_nonneg hhalf
            (mul_nonneg hC (abs_nonneg _))))

lemma localRepresentatives_adjacent_of_fine_bounds
    (k n : ℕ) (hn : 0 < n) (e : SignVector (2 * n + 1))
    (hgood : ¬HasHighPrefixFineMeshAcceleration k n e)
    (u velocityLower velocityUpper D : ℝ)
    (hu : 0 ≤ u) (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper) (hD : 0 ≤ D)
    (a b : Fin (localMeshSize n)) (hne : a ≠ b)
    (ha : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)
    (hb : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e b)
    (hcenter : |localMeshPoint n b - localMeshPoint n a| ≤ D / n)
    (herror :
      (u / n) * (fineGlobalAccelerationBound k n * (D / n)) +
          (fineGlobalAccelerationBound k n * (D / n) ^ 2) * velocityUpper +
          localMeshHalfWidth n *
            (fineGlobalAccelerationBound k n * (D / n)) * velocityUpper <
        velocityLower ^ 2 * (2 * localMeshHalfWidth n)) :
    b.val = a.val + 1 ∨ a.val = b.val + 1 := by
  by_contra hnonadj
  have hlower := adjustedCenterDistance_ge_two_halfWidth_of_nonadjacent
    n a b (localAffineOffset n e a) (localAffineOffset n e b)
      ha.1.2.1 hb.1.2.1 hne hnonadj
  have hloc := localRepresentative_pair_affine_location_bound_fine
    k n hn e hgood u velocityLower velocityUpper hu hvelocityLower.le
      hvelocityUpper a b ha hb
  have hnR : (0 : ℝ) ≤ n := by positivity
  have hC : 0 ≤ fineGlobalAccelerationBound k n :=
    fineGlobalAccelerationBound_nonneg k n
  have hhalf : 0 ≤ localMeshHalfWidth n := by
    unfold localMeshHalfWidth
    positivity
  have hDn : 0 ≤ D / n := div_nonneg hD hnR
  have hfirst : fineGlobalAccelerationBound k n *
      |localMeshPoint n b - localMeshPoint n a| ≤
      fineGlobalAccelerationBound k n * (D / n) :=
    mul_le_mul_of_nonneg_left hcenter hC
  have hsq : (localMeshPoint n b - localMeshPoint n a) ^ 2 ≤
      (D / n) ^ 2 := by
    have hs := (sq_le_sq₀ (abs_nonneg _) hDn).2 hcenter
    simpa only [sq_abs] using hs
  have hsecond : fineGlobalAccelerationBound k n *
      (localMeshPoint n b - localMeshPoint n a) ^ 2 ≤
      fineGlobalAccelerationBound k n * (D / n) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hC
  have hupper :
      (u / n) * (fineGlobalAccelerationBound k n *
          |localMeshPoint n b - localMeshPoint n a|) +
        (fineGlobalAccelerationBound k n *
          (localMeshPoint n b - localMeshPoint n a) ^ 2) * velocityUpper +
        localMeshHalfWidth n * (fineGlobalAccelerationBound k n *
          |localMeshPoint n b - localMeshPoint n a|) * velocityUpper ≤
      (u / n) * (fineGlobalAccelerationBound k n * (D / n)) +
        (fineGlobalAccelerationBound k n * (D / n) ^ 2) * velocityUpper +
        localMeshHalfWidth n *
          (fineGlobalAccelerationBound k n * (D / n)) * velocityUpper := by
    gcongr
  have hleft : velocityLower ^ 2 * (2 * localMeshHalfWidth n) ≤
      velocityLower ^ 2 *
        |(localMeshPoint n b + localAffineOffset n e b) -
          (localMeshPoint n a + localAffineOffset n e a)| :=
    mul_le_mul_of_nonneg_left hlower (sq_nonneg velocityLower)
  exact (not_lt_of_ge (hleft.trans (hloc.trans hupper))) herror

theorem eventually_scaledWeakClose_representatives_adjacent
    (k : ℕ) (L u velocityLower velocityUpper : ℝ)
    (hL : 0 ≤ L) (hu : 0 ≤ u)
    (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper) :
    ∀ᶠ n : ℕ in atTop, ∀ (e : SignVector (2 * n + 1)),
      ¬HasHighPrefixFineMeshAcceleration k n e →
      ∀ a b : Fin (localMeshSize n), a ≠ b →
        IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a →
        IsTruncatedLocalRepresentative n u velocityLower velocityUpper e b →
        |localMeshPoint n b - localMeshPoint n a| < L * weakSpreadScale k n →
        b.val = a.val + 1 ∨ a.val = b.val + 1 := by
  let D : ℝ := 4 * Real.pi + 4 * u / velocityLower
  let A : ℝ := u * D + D ^ 2 * velocityUpper +
    Real.pi * D * velocityUpper
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hweakLimit : Tendsto (fun n : ℕ ↦
      fineGlobalAccelerationBound k n * (L * weakSpreadScale k n))
      atTop (𝓝 0) := by
    have h := (fineGlobalAccelerationBound_mul_weakSpread_tendsto_zero k)
      |>.const_mul L
    convert h using 1
    · funext n
      ring
    · ring
  have hweak : ∀ᶠ n : ℕ in atTop,
      fineGlobalAccelerationBound k n * (L * weakSpreadScale k n) <
        velocityLower / 4 :=
    hweakLimit.eventually (Iio_mem_nhds (by positivity))
  have hcell : ∀ᶠ n : ℕ in atTop,
      fineGlobalAccelerationBound k n * localMeshHalfWidth n <
        velocityLower / 4 :=
    (fineGlobalAccelerationBound_mul_halfWidth_tendsto_zero k).eventually
      (Iio_mem_nhds (by positivity))
  have hnormalized : Tendsto (fun n : ℕ ↦
      A * (fineGlobalAccelerationBound k n / (n : ℝ))) atTop (𝓝 0) := by
    simpa using (fineGlobalAccelerationBound_div_tendsto_zero k).const_mul A
  have herrorScale : ∀ᶠ n : ℕ in atTop,
      A * (fineGlobalAccelerationBound k n / (n : ℝ)) <
        velocityLower ^ 2 * Real.pi :=
    hnormalized.eventually (Iio_mem_nhds (by positivity))
  filter_upwards [Nat.eventually_pos, hweak, hcell, herrorScale]
    with n hn hweakN hcellN herrorN
  intro e hgood a b hne ha hb hclose
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hC : 0 ≤ fineGlobalAccelerationBound k n :=
    fineGlobalAccelerationBound_nonneg k n
  have hquadratic : fineGlobalAccelerationBound k n *
      |localMeshPoint n b - localMeshPoint n a| ≤ velocityLower / 4 :=
    (mul_le_mul_of_nonneg_left hclose.le hC).trans hweakN.le
  have hcenterRaw := localMeshCenterDistance_le_of_two_representatives_fine
    k n hn e hgood u velocityLower velocityUpper hu hvelocityLower a b ha hb
      hquadratic hcellN.le
  have hcenter : |localMeshPoint n b - localMeshPoint n a| ≤ D / n := by
    have hhUpper := localMeshHalfWidth_le_pi_div n hn
    dsimp [D]
    calc
      _ ≤ 4 * localMeshHalfWidth n + 4 * (u / n) / velocityLower := hcenterRaw
      _ ≤ 4 * (Real.pi / n) + 4 * (u / n) / velocityLower := by gcongr
      _ = (4 * Real.pi + 4 * u / velocityLower) / n := by field_simp
  have hhalfLower := pi_div_two_mul_le_localMeshHalfWidth n hn
  have hleftLower : velocityLower ^ 2 * (Real.pi / n) ≤
      velocityLower ^ 2 * (2 * localMeshHalfWidth n) := by
    have htwo : Real.pi / n ≤ 2 * localMeshHalfWidth n := by
      calc
        Real.pi / n = 2 * (Real.pi / (2 * n)) := by ring
        _ ≤ 2 * localMeshHalfWidth n :=
          mul_le_mul_of_nonneg_left hhalfLower (by norm_num)
    exact mul_le_mul_of_nonneg_left htwo (sq_nonneg velocityLower)
  let error : ℝ :=
      (u / n) * (fineGlobalAccelerationBound k n * (D / n)) +
        (fineGlobalAccelerationBound k n * (D / n) ^ 2) * velocityUpper +
        localMeshHalfWidth n *
          (fineGlobalAccelerationBound k n * (D / n)) * velocityUpper
  have herrorUpper : error ≤
      (A * (fineGlobalAccelerationBound k n / n)) / n := by
    have hhUpper := localMeshHalfWidth_le_pi_div n hn
    dsimp [error, A]
    calc
      (u / n) * (fineGlobalAccelerationBound k n * (D / n)) +
          (fineGlobalAccelerationBound k n * (D / n) ^ 2) * velocityUpper +
          localMeshHalfWidth n *
            (fineGlobalAccelerationBound k n * (D / n)) * velocityUpper ≤
        (u / n) * (fineGlobalAccelerationBound k n * (D / n)) +
          (fineGlobalAccelerationBound k n * (D / n) ^ 2) * velocityUpper +
          (Real.pi / n) *
            (fineGlobalAccelerationBound k n * (D / n)) * velocityUpper := by
          gcongr
      _ = ((u * D + D ^ 2 * velocityUpper +
          Real.pi * D * velocityUpper) *
            (fineGlobalAccelerationBound k n / n)) / n := by field_simp
  have herrorFinal : error <
      velocityLower ^ 2 * (2 * localMeshHalfWidth n) := by
    have hdiv :
        (A * (fineGlobalAccelerationBound k n / n)) / n <
          (velocityLower ^ 2 * Real.pi) / n :=
      (div_lt_div_iff_of_pos_right hnR).2 herrorN
    have hid : (velocityLower ^ 2 * Real.pi) / n =
        velocityLower ^ 2 * (Real.pi / n) := by ring
    rw [hid] at hdiv
    exact herrorUpper.trans_lt (hdiv.trans_le hleftLower)
  exact localRepresentatives_adjacent_of_fine_bounds
    k n hn e hgood u velocityLower velocityUpper D hu hvelocityLower
      hvelocityUpper hD a b hne ha hb hcenter
        (by simpa [error] using herrorFinal)

noncomputable def fineAdjacentAffineLocationError
    (k n : ℕ) (u velocityLower velocityUpper : ℝ) : ℝ :=
  ((u / n) *
      (fineGlobalAccelerationBound k n * (2 * localMeshHalfWidth n)) +
    (fineGlobalAccelerationBound k n * (2 * localMeshHalfWidth n) ^ 2) *
      velocityUpper +
    localMeshHalfWidth n *
      (fineGlobalAccelerationBound k n * (2 * localMeshHalfWidth n)) *
      velocityUpper) / velocityLower ^ 2

lemma adjacentRepresentatives_affine_locations_close_fine
    (k n : ℕ) (hn : 0 < n) (e : SignVector (2 * n + 1))
    (hgood : ¬HasHighPrefixFineMeshAcceleration k n e)
    (u velocityLower velocityUpper : ℝ)
    (hu : 0 ≤ u) (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper)
    (a b : Fin (localMeshSize n)) (hab : b.val = a.val + 1)
    (ha : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)
    (hb : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e b) :
    |(localMeshPoint n b + localAffineOffset n e b) -
        (localMeshPoint n a + localAffineOffset n e a)| ≤
      fineAdjacentAffineLocationError k n u velocityLower velocityUpper := by
  have hbound := localRepresentative_pair_affine_location_bound_fine
    k n hn e hgood u velocityLower velocityUpper hu hvelocityLower.le
      hvelocityUpper a b ha hb
  rw [localMeshPoint_sub_eq_two_halfWidth_of_succ n a b hab] at hbound
  have hsq : velocityLower ^ 2 > 0 := sq_pos_of_pos hvelocityLower
  have htwo : 0 ≤ 2 * localMeshHalfWidth n := by
    unfold localMeshHalfWidth
    positivity
  rw [abs_of_nonneg htwo] at hbound
  unfold fineAdjacentAffineLocationError
  exact (le_div_iff₀ hsq).2 (by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hbound)

theorem fineAdjacentAffineLocationError_relative_tendsto_zero
    (k : ℕ) (u velocityLower velocityUpper : ℝ)
    (hvelocityLower : velocityLower ≠ 0) :
    Tendsto (fun n : ℕ ↦
      fineAdjacentAffineLocationError k n u velocityLower velocityUpper /
        localMeshHalfWidth n) atTop (𝓝 0) := by
  let reference : ℕ → ℝ := fun n ↦
    (2 * u * (fineGlobalAccelerationBound k n / (n : ℝ)) +
      6 * velocityUpper *
        (fineGlobalAccelerationBound k n * localMeshHalfWidth n)) /
      velocityLower ^ 2
  have href : Tendsto reference atTop (𝓝 0) := by
    have hnum :=
      (fineGlobalAccelerationBound_div_tendsto_zero k).const_mul (2 * u) |>.add
        ((fineGlobalAccelerationBound_mul_halfWidth_tendsto_zero k).const_mul
          (6 * velocityUpper))
    have hdiv := hnum.div_const (velocityLower ^ 2)
    simpa [reference] using hdiv
  apply href.congr'
  filter_upwards [Nat.eventually_pos] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hh : localMeshHalfWidth n ≠ 0 := by
    unfold localMeshHalfWidth
    exact div_ne_zero (mul_ne_zero Real.pi_ne_zero (by exact_mod_cast hn.ne'))
      (by exact_mod_cast (localMeshSize_pos n).ne')
  dsimp [reference]
  unfold fineAdjacentAffineLocationError
  field_simp
  ring

lemma adjacent_factoredRepresentatives_impossible_of_error_lt
    (k n : ℕ) (hn : 0 < n) (e : SignVector (2 * n + 1))
    (hgood : ¬HasHighPrefixFineMeshAcceleration k n e)
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor0 : 0 ≤ widthFactor) (hfactor1 : widthFactor < 1)
    (hu : 0 ≤ u) (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper)
    (herr : fineAdjacentAffineLocationError k n u velocityLower velocityUpper /
        localMeshHalfWidth n < 2 * (1 - widthFactor))
    (a b : Fin (localMeshSize n)) (hab : b.val = a.val + 1)
    (ha : IsFactoredTruncatedLocalRepresentative n widthFactor u
      velocityLower velocityUpper e a)
    (hb : IsFactoredTruncatedLocalRepresentative n widthFactor u
      velocityLower velocityUpper e b) : False := by
  have ha' := isFactoredTruncatedLocalRepresentative_to_truncated n widthFactor
    u velocityLower velocityUpper hfactor1.le e a ha
  have hb' := isFactoredTruncatedLocalRepresentative_to_truncated n widthFactor
    u velocityLower velocityUpper hfactor1.le e b hb
  have hupper := adjacentRepresentatives_affine_locations_close_fine
    k n hn e hgood u velocityLower velocityUpper hu hvelocityLower
      hvelocityUpper a b hab ha' hb'
  have hhalf : 0 < localMeshHalfWidth n := by
    unfold localMeshHalfWidth
    exact div_pos (mul_pos Real.pi_pos (by exact_mod_cast hn))
      (by exact_mod_cast localMeshSize_pos n)
  have hcenter : |localMeshPoint n b - localMeshPoint n a| =
      2 * localMeshHalfWidth n := by
    rw [localMeshPoint_sub_eq_two_halfWidth_of_succ n a b hab]
    exact abs_of_nonneg (by positivity)
  have hlower := centerDistance_sub_offsets_le_adjustedDistance
    (localMeshPoint n a) (localMeshPoint n b)
    (localAffineOffset n e a) (localAffineOffset n e b)
    (widthFactor * localMeshHalfWidth n) ha.2.1 hb.2.1
  rw [hcenter] at hlower
  have herr' : fineAdjacentAffineLocationError k n u velocityLower velocityUpper <
      2 * (1 - widthFactor) * localMeshHalfWidth n :=
    (div_lt_iff₀ hhalf).1 herr
  have hid : 2 * localMeshHalfWidth n -
        2 * (widthFactor * localMeshHalfWidth n) =
      2 * (1 - widthFactor) * localMeshHalfWidth n := by ring
  rw [hid] at hlower
  exact (not_lt_of_ge (hlower.trans hupper)) herr'

theorem eventually_halfVeryClose_factoredRepresentatives_imply_highPrefix
    (k : ℕ) (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor0 : 0 ≤ widthFactor) (hfactor1 : widthFactor < 1)
    (hu : 0 ≤ u) (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper) :
    ∀ᶠ n : ℕ in atTop, ∀ (e : SignVector (2 * n + 1)),
      ∀ s ∈ halfVeryCloseLocalSiteSets n k,
        (∀ a ∈ s,
          IsFactoredTruncatedLocalRepresentative n widthFactor u
            velocityLower velocityUpper e a) →
        HasHighPrefixFineMeshAcceleration k n e := by
  have htarget : 0 < 2 * (1 - widthFactor) := by linarith
  have herr : ∀ᶠ n : ℕ in atTop,
      fineAdjacentAffineLocationError k n u velocityLower velocityUpper /
          localMeshHalfWidth n < 2 * (1 - widthFactor) :=
    (fineAdjacentAffineLocationError_relative_tendsto_zero
      k u velocityLower velocityUpper hvelocityLower.ne').eventually
        (Iio_mem_nhds htarget)
  filter_upwards [Nat.eventually_pos,
      eventually_two_weakSpreadScale_le_rigiditySmoothScale k,
      eventually_scaledWeakClose_representatives_adjacent
        k (2 * Real.pi) u velocityLower velocityUpper
          (by positivity) hu hvelocityLower hvelocityUpper,
      herr]
    with n hn hscale hadj herrN
  intro e s hs hreps
  by_contra hnotHigh
  have hclose := Finset.mem_filter.mp hs
  have hnonspread := Finset.mem_filter.mp hclose.1
  have hpowerset := Finset.mem_powersetCard.mp hnonspread.1
  rcases halfSmooth_not_weakSpread_has_close_pair n hn k hscale s
      hpowerset.1 hclose.2 with ⟨a, ha, b, hb, hab, hdist⟩
  have haFull := isFactoredTruncatedLocalRepresentative_to_truncated n
    widthFactor u velocityLower velocityUpper hfactor1.le e a (hreps a ha)
  have hbFull := isFactoredTruncatedLocalRepresentative_to_truncated n
    widthFactor u velocityLower velocityUpper hfactor1.le e b (hreps b hb)
  rcases hadj e hnotHigh a b hab haFull hbFull hdist with hsucc | hsucc
  · exact adjacent_factoredRepresentatives_impossible_of_error_lt
      k n hn e hnotHigh widthFactor u velocityLower velocityUpper hfactor0
        hfactor1 hu hvelocityLower hvelocityUpper herrN a b hsucc
          (hreps a ha) (hreps b hb)
  · exact adjacent_factoredRepresentatives_impossible_of_error_lt
      k n hn e hnotHigh widthFactor u velocityLower velocityUpper hfactor0
        hfactor1 hu hvelocityLower hvelocityUpper herrN b a hsucc
          (hreps b hb) (hreps a ha)

noncomputable def halfVeryCloseFactoredChooseContribution
    (n k : ℕ) (widthFactor u velocityLower velocityUpper : ℝ) : ℝ :=
  ∑ s ∈ halfVeryCloseLocalSiteSets n k,
    uniformProbability (fun e : SignVector (2 * n + 1) ↦
      ∀ a ∈ s,
        IsFactoredTruncatedLocalRepresentative n widthFactor u
          velocityLower velocityUpper e a)

theorem halfVeryCloseFactoredChooseContribution_tendsto_zero
    (k : ℕ) (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor0 : 0 ≤ widthFactor) (hfactor1 : widthFactor < 1)
    (hu : 0 ≤ u) (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper) :
    Tendsto (fun n : ℕ ↦
      halfVeryCloseFactoredChooseContribution n k widthFactor u
        velocityLower velocityUpper) atTop (𝓝 0) := by
  have hupper : ∀ᶠ n : ℕ in atTop,
      halfVeryCloseFactoredChooseContribution n k widthFactor u
          velocityLower velocityUpper ≤
        (localMeshSize n : ℝ) ^ k *
          uniformProbability (HasHighPrefixFineMeshAcceleration k n) := by
    filter_upwards [
      eventually_halfVeryClose_factoredRepresentatives_imply_highPrefix
        k widthFactor u velocityLower velocityUpper hfactor0 hfactor1 hu
          hvelocityLower hvelocityUpper] with n himply
    have hterm : ∀ s ∈ halfVeryCloseLocalSiteSets n k,
        uniformProbability (fun e : SignVector (2 * n + 1) ↦
          ∀ a ∈ s,
            IsFactoredTruncatedLocalRepresentative n widthFactor u
              velocityLower velocityUpper e a) ≤
          uniformProbability (HasHighPrefixFineMeshAcceleration k n) := by
      intro s hs
      exact uniformProbability_mono (fun e he ↦ himply e s hs he)
    calc
      halfVeryCloseFactoredChooseContribution n k widthFactor u
          velocityLower velocityUpper ≤
        ∑ _s ∈ halfVeryCloseLocalSiteSets n k,
          uniformProbability (HasHighPrefixFineMeshAcceleration k n) := by
        unfold halfVeryCloseFactoredChooseContribution
        exact Finset.sum_le_sum fun s hs ↦ hterm s hs
      _ = ((halfVeryCloseLocalSiteSets n k).card : ℝ) *
          uniformProbability (HasHighPrefixFineMeshAcceleration k n) := by simp
      _ ≤ (localMeshSize n : ℝ) ^ k *
          uniformProbability (HasHighPrefixFineMeshAcceleration k n) := by
        apply mul_le_mul_of_nonneg_right _ (uniformProbability_nonneg _)
        exact_mod_cast halfVeryCloseLocalSiteSets_card_le_pow n k
  apply squeeze_zero'
    (Eventually.of_forall fun n ↦ by
      unfold halfVeryCloseFactoredChooseContribution
      exact Finset.sum_nonneg fun s _ ↦ uniformProbability_nonneg _)
    hupper
  exact localMeshSize_pow_mul_highPrefixFineMeshAcceleration_tendsto_zero k k

noncomputable def halfNonspreadFactoredChooseContribution
    (n k : ℕ) (widthFactor u velocityLower velocityUpper : ℝ) : ℝ :=
  ∑ s ∈ halfNonspreadLocalSiteSets n k,
    uniformProbability (fun e : SignVector (2 * n + 1) ↦
      ∀ a ∈ s,
        IsFactoredTruncatedLocalRepresentative n widthFactor u
          velocityLower velocityUpper e a)

lemma halfNonspreadFactoredChooseContribution_eq_weak_add_veryClose
    (n k : ℕ) (widthFactor u velocityLower velocityUpper : ℝ) :
    halfNonspreadFactoredChooseContribution n k widthFactor u
        velocityLower velocityUpper =
      halfWeakNonspreadFactoredChooseContribution n k widthFactor u
          velocityLower velocityUpper +
        halfVeryCloseFactoredChooseContribution n k widthFactor u
          velocityLower velocityUpper := by
  rw [halfNonspreadFactoredChooseContribution,
    halfNonspread_eq_weak_union_veryClose,
    Finset.sum_union (halfWeakNonspread_disjoint_veryClose n k)]
  rfl

theorem halfNonspreadFactoredChooseContribution_tendsto_zero
    (k : ℕ) (hk : 0 < k)
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor0 : 0 ≤ widthFactor) (hfactor1 : widthFactor < 1)
    (hu : 0 ≤ u) (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper) :
    Tendsto (fun n : ℕ ↦
      halfNonspreadFactoredChooseContribution n k widthFactor u
        velocityLower velocityUpper) atTop (𝓝 0) := by
  have hweak := halfWeakNonspreadFactoredChooseContribution_tendsto_zero
    k hk widthFactor u velocityLower velocityUpper hfactor0 hu
      hvelocityLower hvelocityUpper
  have hclose := halfVeryCloseFactoredChooseContribution_tendsto_zero
    k widthFactor u velocityLower velocityUpper hfactor0 hfactor1 hu
      hvelocityLower hvelocityUpper
  have hsum := hweak.add hclose
  have hsum' := hsum.congr' (Eventually.of_forall fun n ↦
    (halfNonspreadFactoredChooseContribution_eq_weak_add_veryClose
      n k widthFactor u velocityLower velocityUpper).symm)
  simpa only [zero_add] using hsum'

noncomputable def halfFactoredTruncatedLocalMinimumCount
    (n : ℕ) (widthFactor u velocityLower velocityUpper : ℝ)
    (e : SignVector (2 * n + 1)) : ℕ :=
  ((halfSmoothLocalMeshSites n).filter fun a ↦
    IsFactoredTruncatedLocalRepresentative n widthFactor u
      velocityLower velocityUpper e a).card

lemma uniformChooseMoment_halfFactoredTruncatedLocalMinimumCount
    (n k : ℕ) (widthFactor u velocityLower velocityUpper : ℝ) :
    uniformChooseMoment
        (halfFactoredTruncatedLocalMinimumCount n widthFactor u
          velocityLower velocityUpper) k =
      ∑ s ∈ (halfSmoothLocalMeshSites n).powersetCard k,
        uniformProbability (fun e : SignVector (2 * n + 1) ↦
          ∀ a ∈ s,
            IsFactoredTruncatedLocalRepresentative n widthFactor u
              velocityLower velocityUpper e a) := by
  unfold uniformChooseMoment
  have heq :
      (fun e : SignVector (2 * n + 1) ↦
        (Nat.choose
          (halfFactoredTruncatedLocalMinimumCount n widthFactor u
            velocityLower velocityUpper e) k : ℝ)) =
      (fun e ↦ ∑ s ∈ (halfSmoothLocalMeshSites n).powersetCard k,
        if ∀ a ∈ s,
          IsFactoredTruncatedLocalRepresentative n widthFactor u
            velocityLower velocityUpper e a
        then (1 : ℝ) else 0) := by
    funext e
    unfold halfFactoredTruncatedLocalMinimumCount
    have hnat := choose_card_filter_eq_sum_powersetCard_on
      (halfSmoothLocalMeshSites n)
      (fun a ↦ IsFactoredTruncatedLocalRepresentative n widthFactor u
        velocityLower velocityUpper e a) k
    rw [hnat]
    push_cast
    apply Finset.sum_congr rfl
    intro s _hs
    by_cases h : ∀ a ∈ s,
        IsFactoredTruncatedLocalRepresentative n widthFactor u
          velocityLower velocityUpper e a
    · simp [h]
    · simp [h]
  rw [heq]
  rw [uniformExpectation_finset_sum
    (Ω := SignVector (2 * n + 1))
    (I := Finset (Fin (localMeshSize n)))
    (s := (halfSmoothLocalMeshSites n).powersetCard k)
    (X := fun s (e : SignVector (2 * n + 1)) ↦
      if ∀ a ∈ s,
        IsFactoredTruncatedLocalRepresentative n widthFactor u
          velocityLower velocityUpper e a
      then (1 : ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro s _hs
  unfold uniformExpectation uniformProbability
  congr 1
  simp
  apply congrArg Finset.card
  ext e
  simp

lemma uniformChooseMoment_halfFactored_eq_good_add_nonspread
    (n k : ℕ) (widthFactor u velocityLower velocityUpper : ℝ) :
    uniformChooseMoment
        (halfFactoredTruncatedLocalMinimumCount n widthFactor u
          velocityLower velocityUpper) k =
      halfGoodFactoredTruncatedChooseContribution n k widthFactor u
          velocityLower velocityUpper +
        halfNonspreadFactoredChooseContribution n k widthFactor u
          velocityLower velocityUpper := by
  rw [uniformChooseMoment_halfFactoredTruncatedLocalMinimumCount]
  rw [halfSmoothPowerset_eq_good_union_nonspread]
  rw [Finset.sum_union (halfGoodLocalSiteSets_disjoint_halfNonspread n k)]
  rfl

theorem uniformChooseMoment_halfFactoredTruncatedLocalMinimumCount_tendsto
    (k : ℕ) (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor0 : 0 < widthFactor) (hfactor1 : widthFactor < 1)
    (hu : 0 < u) (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 < velocityUpper) :
    Tendsto (fun n : ℕ ↦
      uniformChooseMoment
        (halfFactoredTruncatedLocalMinimumCount n widthFactor u
          velocityLower velocityUpper) k) atTop
      (𝓝 (((widthFactor * ((6 * u / Real.pi) *
        blockVelocityMass velocityLower velocityUpper)) ^ k) /
          (k.factorial : ℝ))) := by
  by_cases hk : k = 0
  · subst k
    convert tendsto_const_nhds (x := (1 : ℝ)) using 1
    · funext n
      unfold uniformChooseMoment uniformExpectation
      simp
    · norm_num
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hgood := halfGoodFactoredTruncatedChooseContribution_tendsto
      k hkpos widthFactor u velocityLower velocityUpper hfactor0 hu
        hvelocityLower hvelocityUpper
    have hbad := halfNonspreadFactoredChooseContribution_tendsto_zero
      k hkpos widthFactor u velocityLower velocityUpper hfactor0.le hfactor1
        hu.le hvelocityLower hvelocityUpper.le
    have hsum := hgood.add hbad
    have hsum' := hsum.congr' (Eventually.of_forall fun n ↦
      (uniformChooseMoment_halfFactored_eq_good_add_nonspread
        n k widthFactor u velocityLower velocityUpper).symm)
    simpa only [add_zero] using hsum'

theorem uniformProbability_halfFactoredTruncatedLocalMinimumCount_eq_zero_tendsto
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor0 : 0 < widthFactor) (hfactor1 : widthFactor < 1)
    (hu : 0 < u) (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 < velocityUpper) :
    Tendsto (fun n : ℕ ↦
      uniformProbability (fun e : SignVector (2 * n + 1) ↦
        halfFactoredTruncatedLocalMinimumCount n widthFactor u
          velocityLower velocityUpper e = 0)) atTop
      (𝓝 (Real.exp (-(widthFactor * ((6 * u / Real.pi) *
        blockVelocityMass velocityLower velocityUpper))))) := by
  exact uniformVoidProbability_tendsto_of_chooseMoments
    (fun n ↦ 2 * n + 1)
    (fun n ↦ halfFactoredTruncatedLocalMinimumCount n widthFactor u
      velocityLower velocityUpper)
    (widthFactor * ((6 * u / Real.pi) *
      blockVelocityMass velocityLower velocityUpper))
    (fun k ↦
      uniformChooseMoment_halfFactoredTruncatedLocalMinimumCount_tendsto
        k widthFactor u velocityLower velocityUpper hfactor0 hfactor1 hu
          hvelocityLower hvelocityUpper)

end Odd

end Erdos525
