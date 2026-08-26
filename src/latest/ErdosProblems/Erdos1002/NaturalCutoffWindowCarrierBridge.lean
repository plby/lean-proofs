import ErdosProblems.Erdos1002.NaturalCutoffShotCoefficientBridge
import ErdosProblems.Erdos1002.WindowCarrierSummation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The positive-frequency window/carrier bridge

This file identifies the analytic nearest-cell window transform with the
absolutely convergent Bernoulli carrier series.  The sign is recorded
carefully: `finiteWindowFourierPolynomial` represents `shot - reconstruction`,
whereas `naturalCutoffShotErrorL2` represents `reconstruction - shot`.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ComplexConjugate Real Topology

namespace Erdos1002

noncomputable section

theorem sineIntegralTruncation_half_eq_paperSineIntegral (a : ℝ) :
    sineIntegralTruncation a (1 / 2) = paperSineIntegral (a / 2) := by
  unfold sineIntegralTruncation sineKernel paperSineIntegral
  rw [intervalIntegral.integral_const_mul]
  have h := intervalIntegral.smul_integral_comp_mul_left
    (fun x : ℝ ↦ Real.sinc x) a (a := (0 : ℝ)) (b := (1 / 2 : ℝ))
  simp only [smul_eq_mul, mul_zero, mul_one_div] at h
  exact h

/-- The manuscript's window coefficient is exactly the finite symmetric
exponential integral minus its full principal-value limit. -/
theorem windowKernelCoefficient_eq_truncation_sub_principalValue
    (d : ℕ) (m : ℤ) (hd : 0 < d) :
    windowKernelCoefficient d m =
      symmetricExponentialTruncation ((m : ℝ) / (d : ℝ)) (1 / 2) -
        signedExponentialPV ((m : ℝ) / (d : ℝ)) := by
  rw [symmetricExponentialTruncation_eq,
    sineIntegralTruncation_half_eq_paperSineIntegral]
  have harg :
      (2 * Real.pi * ((m : ℝ) / (d : ℝ))) / 2 =
        Real.pi * (m : ℝ) / (d : ℝ) := by ring
  rw [harg]
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rcases lt_trichotomy m 0 with hm | hm | hm
  · have hm0 : m ≠ 0 := ne_of_lt hm
    have hratio : (m : ℝ) / (d : ℝ) < 0 :=
      div_neg_of_neg_of_pos (by exact_mod_cast hm) hdR
    rw [windowKernelCoefficient, if_neg hm0,
      Int.sign_eq_neg_one_iff_neg.mpr hm]
    unfold signedExponentialPV
    rw [if_neg (not_lt.mpr hratio.le), if_pos hratio]
    push_cast
    ring
  · subst m
    simp [windowKernelCoefficient, signedExponentialPV,
      paperSineIntegral]
  · have hm0 : m ≠ 0 := ne_of_gt hm
    have hratio : 0 < (m : ℝ) / (d : ℝ) :=
      div_pos (by exact_mod_cast hm) hdR
    rw [windowKernelCoefficient, if_neg hm0,
      Int.sign_eq_one_iff_pos.mpr hm]
    unfold signedExponentialPV
    rw [if_pos hratio]
    push_cast
    ring

/-- One positive cosine mode packages the zero, positive, and negative
Bernoulli Fourier carriers. -/
def windowCosineCarrierMode (N d : ℕ) (m : ℤ) (k : ℕ) : ℂ :=
  ((1 / (2 * Real.pi ^ 2 * (k : ℝ) ^ 2) : ℝ) : ℂ) *
    (windowKernelCoefficient d m -
      (1 / 2 : ℂ) * windowKernelCoefficient d
        (m - ((k * N * d : ℕ) : ℤ)) -
      (1 / 2 : ℂ) * windowKernelCoefficient d
        (m + ((k * N * d : ℕ) : ℤ)))

theorem windowCosineCarrierMode_eq_modeTruncation_sub_principalValue
    (N d : ℕ) (m : ℤ) (k : ℕ) (hd : 0 < d) :
    windowCosineCarrierMode N d m k =
      bernoulliModeTruncation N ((m : ℝ) / (d : ℝ)) k (1 / 2) -
        bernoulliModePrincipalValue N ((m : ℝ) / (d : ℝ)) k := by
  rw [bernoulliModeTruncation_eq_closedForm]
  unfold windowCosineCarrierMode bernoulliModeClosedForm
    bernoulliModePrincipalValue
  rw [windowKernelCoefficient_eq_truncation_sub_principalValue d m hd,
    windowKernelCoefficient_eq_truncation_sub_principalValue d
      (m - ((k * N * d : ℕ) : ℤ)) hd,
    windowKernelCoefficient_eq_truncation_sub_principalValue d
      (m + ((k * N * d : ℕ) : ℤ)) hd]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hminus :
      ((m - ((k * N * d : ℕ) : ℤ) : ℤ) : ℝ) / (d : ℝ) =
        (m : ℝ) / (d : ℝ) - (k : ℝ) * N := by
    push_cast
    field_simp [hdR]
  have hplus :
      ((m + ((k * N * d : ℕ) : ℤ) : ℤ) : ℝ) / (d : ℝ) =
        (m : ℝ) / (d : ℝ) + (k : ℝ) * N := by
    push_cast
    field_simp [hdR]
  rw [hminus, hplus]
  ring

theorem nearestCellTransform_eq_bernoulliPairedTruncation
    (N n p : ℕ) :
    nearestCellTransform N n p =
      bernoulliPairedTruncation N ((n : ℝ) / (p : ℝ)) (1 / 2) := by
  have h := principalValueTruncation_eq_paired N
    ((n : ℝ) / (p : ℝ)) (1 / 2)
  unfold principalValueTruncation at h
  unfold nearestCellTransform periodizedTransformIntegrand
  convert! h using 1
  norm_num

theorem tsum_bernoulliModePrincipalValue_eq_hStarRatio
    (N m d : ℕ) (hN : 0 < N) (hm : 0 < m) (hd : 0 < d) :
    (∑' k : ℕ,
      bernoulliModePrincipalValue N ((m : ℝ) / (d : ℝ)) k) =
        naturalCoefficientNormalization * (hStarRatio m (d * N) : ℂ) := by
  rw [tsum_bernoulliModePrincipalValue_eq_tail N
      ((m : ℝ) / (d : ℝ)) hN (div_pos (Nat.cast_pos.mpr hm)
        (Nat.cast_pos.mpr hd)),
    halfWeightedTail_div_eq_hStarRatio N m d hd]
  unfold naturalCoefficientNormalization
  ring

/-- The full-minus-nearest transform is the negative of the grouped
Bernoulli carrier series.  Every series in this identity is summable. -/
theorem nearestCellWindowTransform_eq_neg_tsum_cosineCarrier
    (N m d : ℕ) (hN : 0 < N) (hm : 0 < m) (hd : 0 < d) :
    nearestCellWindowTransform N m d =
      -(∑' k : ℕ, windowCosineCarrierMode N d (m : ℤ) k) := by
  let s : ℝ := (m : ℝ) / (d : ℝ)
  have hs : 0 < s := div_pos (Nat.cast_pos.mpr hm) (Nat.cast_pos.mpr hd)
  have htrunc : Summable fun k : ℕ ↦
      bernoulliModeTruncation N s k (1 / 2) :=
    (hasSum_bernoulliModeTruncation N s (1 / 2)).summable
  have hpv : Summable fun k : ℕ ↦ bernoulliModePrincipalValue N s k :=
    summable_bernoulliModePrincipalValue N s hN hs
  have hcos : Summable (windowCosineCarrierMode N d (m : ℤ)) := by
    apply htrunc.sub hpv |>.congr
    intro k
    exact (windowCosineCarrierMode_eq_modeTruncation_sub_principalValue
      N d (m : ℤ) k hd).symm
  have hcosValue :
      (∑' k : ℕ, windowCosineCarrierMode N d (m : ℤ) k) =
        (∑' k : ℕ, bernoulliModeTruncation N s k (1 / 2)) -
          ∑' k : ℕ, bernoulliModePrincipalValue N s k := by
    rw [← htrunc.tsum_sub hpv]
    exact tsum_congr fun k ↦
      windowCosineCarrierMode_eq_modeTruncation_sub_principalValue
        N d (m : ℤ) k hd
  have hnearest :
      (∑' k : ℕ, bernoulliModeTruncation N s k (1 / 2)) =
        nearestCellTransform N m d := by
    rw [(hasSum_bernoulliModeTruncation N s (1 / 2)).tsum_eq]
    exact (nearestCellTransform_eq_bernoulliPairedTruncation N m d).symm
  have hfull :
      (∑' k : ℕ, bernoulliModePrincipalValue N s k) =
        naturalCoefficientNormalization * (hStarRatio m (d * N) : ℂ) := by
    exact tsum_bernoulliModePrincipalValue_eq_hStarRatio N m d hN hm hd
  unfold nearestCellWindowTransform
  rw [hcosValue, hnearest, hfull]
  ring

theorem norm_windowKernelCoefficient_le_twelve
    (d : ℕ) (m : ℤ) (hd : 0 < d) :
    ‖windowKernelCoefficient d m‖ ≤ 12 := by
  by_cases hcentral : |(m : ℝ)| ≤ (d : ℝ)
  · exact norm_windowKernelCoefficient_le_twelve_of_abs_le hd m hcentral
  · have hm0 : m ≠ 0 := by
      intro hm
      subst m
      simp at hcentral
    have htail := norm_windowKernelCoefficient_le_six_mul_div_abs hd hm0
    have habsPos : 0 < |(m : ℝ)| := abs_pos.mpr (by exact_mod_cast hm0)
    have hdle : (d : ℝ) ≤ |(m : ℝ)| := le_of_not_ge hcentral
    calc
      ‖windowKernelCoefficient d m‖ ≤
          6 * (d : ℝ) / |(m : ℝ)| := htail
      _ ≤ 6 := by
        rw [div_le_iff₀ habsPos]
        nlinarith
      _ ≤ 12 := by norm_num

/-- One ungrouped integer carrier at frequency `m`. -/
def windowCarrierKernelTerm (N d : ℕ) (m : ℤ) (ell : ℤ) : ℂ :=
  bernoulliMarkFourierCoefficient ell *
    windowKernelCoefficient d
      (m - ell * ((N * d : ℕ) : ℤ))

theorem summable_windowCarrierKernelTerm
    (N d : ℕ) (m : ℤ) (hd : 0 < d) :
    Summable (windowCarrierKernelTerm N d m) := by
  apply Summable.of_norm
  apply (summable_bernoulliCarrierMajorant.mul_right 12).of_nonneg_of_le
  · intro ell
    exact norm_nonneg _
  · intro ell
    unfold windowCarrierKernelTerm
    rw [norm_mul]
    exact mul_le_mul
      (norm_bernoulliMarkFourierCoefficient_le_majorant ell)
      (norm_windowKernelCoefficient_le_twelve d _ hd)
      (norm_nonneg _) (bernoulliCarrierMajorant_nonneg ell)

private theorem tsum_shifted_inverseSquare :
    (∑' k : ℕ, 1 / (((k + 1 : ℕ) : ℝ) ^ 2)) = Real.pi ^ 2 / 6 := by
  have hsplit := hasSum_zeta_two.summable.tsum_eq_zero_add
  rw [hasSum_zeta_two.tsum_eq] at hsplit
  simpa using! hsplit.symm

theorem tsum_windowCosineConstantCoefficient :
    (∑' k : ℕ,
      (1 : ℝ) / (2 * Real.pi ^ 2 * (((k + 1 : ℕ) : ℝ) ^ 2))) =
        1 / 12 := by
  calc
    (∑' k : ℕ,
        (1 : ℝ) / (2 * Real.pi ^ 2 * (((k + 1 : ℕ) : ℝ) ^ 2))) =
      (1 / (2 * Real.pi ^ 2)) *
        ∑' k : ℕ, 1 / (((k + 1 : ℕ) : ℝ) ^ 2) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      ring
    _ = (1 / (2 * Real.pi ^ 2)) * (Real.pi ^ 2 / 6) := by
      rw [tsum_shifted_inverseSquare]
    _ = 1 / 12 := by
      field_simp [Real.pi_ne_zero]
      norm_num

theorem windowCarrierKernelTerm_zero_eq_tsum_constantModes
    (N d : ℕ) (m : ℤ) :
    windowCarrierKernelTerm N d m 0 =
      ∑' k : ℕ,
        (((1 : ℝ) /
          (2 * Real.pi ^ 2 * (((k + 1 : ℕ) : ℝ) ^ 2)) : ℝ) : ℂ) *
          windowKernelCoefficient d m := by
  unfold windowCarrierKernelTerm bernoulliMarkFourierCoefficient
  simp only [if_pos, zero_mul, sub_zero]
  have hcoef :
      (∑' k : ℕ,
        (((1 : ℝ) /
          (2 * Real.pi ^ 2 * (((k + 1 : ℕ) : ℝ) ^ 2)) : ℝ) : ℂ)) =
        (1 / 12 : ℂ) := by
    rw [← Complex.ofReal_tsum, tsum_windowCosineConstantCoefficient]
    norm_num
  symm
  calc
    (∑' k : ℕ,
        (((1 : ℝ) /
          (2 * Real.pi ^ 2 * (((k + 1 : ℕ) : ℝ) ^ 2)) : ℝ) : ℂ) *
          windowKernelCoefficient d m) =
      (∑' k : ℕ,
        (((1 : ℝ) /
          (2 * Real.pi ^ 2 * (((k + 1 : ℕ) : ℝ) ^ 2)) : ℝ) : ℂ)) *
        windowKernelCoefficient d m := tsum_mul_right
    _ = (1 / 12 : ℂ) * windowKernelCoefficient d m := by rw [hcoef]

theorem windowCosineCarrierMode_succ_eq_groupedCarriers
    (N d : ℕ) (m : ℤ) (k : ℕ) :
    windowCosineCarrierMode N d m (k + 1) =
      ((((1 : ℝ) /
          (2 * Real.pi ^ 2 * (((k + 1 : ℕ) : ℝ) ^ 2)) : ℝ) : ℂ) *
          windowKernelCoefficient d m +
        windowCarrierKernelTerm N d m ((k + 1 : ℕ) : ℤ)) +
      windowCarrierKernelTerm N d m (-((k + 1 : ℕ) : ℤ)) := by
  have hk : ((k + 1 : ℕ) : ℤ) ≠ 0 := by omega
  unfold windowCosineCarrierMode windowCarrierKernelTerm
    bernoulliMarkFourierCoefficient
  rw [if_neg hk, if_neg (neg_ne_zero.mpr hk)]
  push_cast
  field_simp [Real.pi_ne_zero]
  ring_nf

/- Regrouping the absolutely convergent integer carrier series into its
positive cosine modes.  The zero carrier is distributed using
`sum k⁻² = pi²/6`; no conditional rearrangement occurs. -/
set_option maxHeartbeats 1600000 in
theorem tsum_windowCarrierKernelTerm_eq_tsum_cosineCarrier
    (N d : ℕ) (m : ℤ) (hd : 0 < d) :
    (∑' ell : ℤ, windowCarrierKernelTerm N d m ell) =
      ∑' k : ℕ, windowCosineCarrierMode N d m k := by
  let f : ℤ → ℂ := windowCarrierKernelTerm N d m
  let g : ℕ → ℂ := fun k ↦
    (((1 : ℝ) /
      (2 * Real.pi ^ 2 * (((k + 1 : ℕ) : ℝ) ^ 2)) : ℝ) : ℂ) *
      windowKernelCoefficient d m
  let fp : ℕ → ℂ := fun k ↦ f ((k + 1 : ℕ) : ℤ)
  let fn : ℕ → ℂ := fun k ↦ f (-((k + 1 : ℕ) : ℤ))
  have hf : Summable f := summable_windowCarrierKernelTerm N d m hd
  have hfPos : Summable fun k : ℕ ↦ f (k : ℤ) :=
    hf.comp_injective Nat.cast_injective
  have hfNeg : Summable fun k : ℕ ↦ f (-((k : ℕ) : ℤ)) :=
    hf.comp_injective (neg_injective.comp Nat.cast_injective)
  have hfPosShift : Summable fp := by
    simpa only [fp, Nat.cast_add, Nat.cast_one] using!
      (summable_nat_add_iff 1).mpr hfPos
  have hfNegShift : Summable fn := by
    simpa only [fn, Nat.cast_add, Nat.cast_one] using!
      (summable_nat_add_iff 1).mpr hfNeg
  have hinv : Summable fun k : ℕ ↦
      1 / (((k + 1 : ℕ) : ℝ) ^ 2) := by
    exact (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num))
  have hreal : Summable fun k : ℕ ↦
      (1 : ℝ) /
        (2 * Real.pi ^ 2 * (((k + 1 : ℕ) : ℝ) ^ 2)) := by
    have hscaled := hinv.mul_left (1 / (2 * Real.pi ^ 2))
    exact hscaled.congr fun k ↦ by ring
  have hg : Summable g := by
    have hcast : Summable fun k : ℕ ↦
        (((1 : ℝ) /
          (2 * Real.pi ^ 2 * (((k + 1 : ℕ) : ℝ) ^ 2)) : ℝ) : ℂ) :=
      Complex.summable_ofReal.mpr hreal
    exact hcast.mul_right (windowKernelCoefficient d m)
  have hgrouped : Summable fun k : ℕ ↦
      (g k + fp k) + fn k :=
    (hg.add hfPosShift).add hfNegShift
  have hcosShift : Summable fun k : ℕ ↦
      windowCosineCarrierMode N d m (k + 1) := by
    apply hgrouped.congr
    intro k
    exact (windowCosineCarrierMode_succ_eq_groupedCarriers N d m k).symm
  have hcos : Summable (windowCosineCarrierMode N d m) :=
    (summable_nat_add_iff 1).mp hcosShift
  have hsplit := tsum_of_add_one_of_neg_add_one hfPosShift hfNegShift
  have hzero : f 0 = ∑' k : ℕ, g k := by
    simpa only [f, g] using!
      windowCarrierKernelTerm_zero_eq_tsum_constantModes N d m
  have hfirst := hg.tsum_add hfPosShift
  have hsecond := (hg.add hfPosShift).tsum_add hfNegShift
  have hshiftValue :
      (∑' k : ℕ, windowCosineCarrierMode N d m (k + 1)) =
        ((∑' k : ℕ, g k) +
          (∑' k : ℕ, fp k)) +
          (∑' k : ℕ, fn k) := by
    calc
      (∑' k : ℕ, windowCosineCarrierMode N d m (k + 1)) =
          (∑' k : ℕ,
            ((g k + fp k) + fn k)) := by
        apply tsum_congr
        intro k
        simpa only [fp, fn] using!
          windowCosineCarrierMode_succ_eq_groupedCarriers N d m k
      _ = (∑' k : ℕ, (g k + fp k)) +
          (∑' k : ℕ, fn k) := hsecond
      _ = ((∑' k : ℕ, g k) +
          (∑' k : ℕ, fp k)) +
          (∑' k : ℕ, fn k) := by rw [hfirst]
  have hcosZero : windowCosineCarrierMode N d m 0 = 0 := by
    simp [windowCosineCarrierMode]
  have hcosDecomp := hcos.tsum_eq_zero_add
  rw [hcosZero, zero_add] at hcosDecomp
  change (∑' ell : ℤ, f ell) =
    ∑' k : ℕ, windowCosineCarrierMode N d m k
  calc
    (∑' ell : ℤ, f ell) =
        (∑' k : ℕ, fp k) + f 0 +
          (∑' k : ℕ, fn k) := by
      simpa only [fp, fn, Nat.cast_add, Nat.cast_one] using! hsplit
    _ = (∑' k : ℕ, fp k) +
        (∑' k : ℕ, g k) +
          (∑' k : ℕ, fn k) := by rw [hzero]
    _ = (∑' k : ℕ, g k) +
        (∑' k : ℕ, fp k) +
          (∑' k : ℕ, fn k) := by ring
    _ = ∑' k : ℕ, windowCosineCarrierMode N d m (k + 1) :=
      hshiftValue.symm
    _ = ∑' k : ℕ, windowCosineCarrierMode N d m k := hcosDecomp.symm

theorem nearestCellWindowTransform_eq_neg_tsum_carrier
    (N m d : ℕ) (hN : 0 < N) (hm : 0 < m) (hd : 0 < d) :
    nearestCellWindowTransform N m d =
      -(∑' ell : ℤ, windowCarrierKernelTerm N d (m : ℤ) ell) := by
  rw [nearestCellWindowTransform_eq_neg_tsum_cosineCarrier N m d hN hm hd,
    ← tsum_windowCarrierKernelTerm_eq_tsum_cosineCarrier N d (m : ℤ) hd]

/-- Cancelling a common positive factor in the sampled rational frequency
preserves both the full and nearest-cell transforms. -/
theorem nearestCellWindowTransform_mul_cancel
    (N n d r : ℕ) (hd : 0 < d) (hr : 0 < r) (hrn : r ∣ n) :
    nearestCellWindowTransform N n (d * r) =
      nearestCellWindowTransform N (n / r) d := by
  have hnprod : n / r * r = n := Nat.div_mul_cancel hrn
  have hhstar :
      hStarRatio n (d * r * N) = hStarRatio (n / r) (d * N) := by
    have h := hStarRatio_mul_scale_cancel (n / r) (d * N) r hr
    simpa [hnprod, mul_assoc, mul_left_comm, mul_comm] using! h
  have hratio :
      (n : ℝ) / ((d * r : ℕ) : ℝ) =
        ((n / r : ℕ) : ℝ) / (d : ℝ) := by
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    have hnprodR : (((n / r : ℕ) : ℝ) * (r : ℝ)) = (n : ℝ) := by
      exact_mod_cast hnprod
    push_cast
    rw [← hnprodR]
    field_simp [hdR, hrR]
  have hnearest : nearestCellTransform N n (d * r) =
      nearestCellTransform N (n / r) d := by
    unfold nearestCellTransform periodizedTransformIntegrand
    apply intervalIntegral.integral_congr
    intro x hx
    rw [hratio]
  unfold nearestCellWindowTransform
  rw [hhstar, hnearest]

/-! ## Finite Ramanujan--Möbius reindexing -/

/-- Pairs `(p,r)` with `p ≤ P` and `r` dividing both `p` and the Fourier
frequency. -/
def ramanujanWindowPairs (P n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 P).product (Finset.Icc 1 P)).filter fun z ↦
    z.2 ∣ z.1 ∧ z.2 ∣ n

theorem mem_ramanujanWindowPairs_iff
    {P n : ℕ} {z : ℕ × ℕ} :
    z ∈ ramanujanWindowPairs P n ↔
      1 ≤ z.1 ∧ z.1 ≤ P ∧ 1 ≤ z.2 ∧ z.2 ≤ P ∧
        z.2 ∣ z.1 ∧ z.2 ∣ n := by
  simp [ramanujanWindowPairs, and_assoc]

def ramanujanWindowPairSummand
    (F : ℕ → ℂ) (z : ℕ × ℕ) : ℂ :=
  ((1 / (z.1 : ℝ) ^ 2 : ℝ) : ℂ) * (z.2 : ℂ) *
    (ArithmeticFunction.moebius (z.1 / z.2) : ℂ) * F z.1

def mobiusWindowPairSummand
    (F : ℕ → ℂ) (z : ℕ × ℕ) : ℂ :=
  ((ArithmeticFunction.moebius z.1 : ℤ) : ℂ) /
      ((z.1 : ℂ) ^ 2 * (z.2 : ℂ)) * F (z.1 * z.2)

theorem sum_ramanujanWindow_eq_ramanujanPairs
    (P n : ℕ) (F : ℕ → ℂ) :
    (∑ p ∈ Finset.Icc 1 P,
      ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
        ramanujanSum p (n : ℤ) * F p) =
      ∑ z ∈ ramanujanWindowPairs P n,
        ramanujanWindowPairSummand F z := by
  unfold ramanujanWindowPairs
  rw [Finset.sum_filter]
  change (∑ p ∈ Finset.Icc 1 P,
      ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
        ramanujanSum p (n : ℤ) * F p) =
    ∑ z ∈ (Finset.Icc 1 P) ×ˢ (Finset.Icc 1 P),
      if z.2 ∣ z.1 ∧ z.2 ∣ n then
        ramanujanWindowPairSummand F z else 0
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p hp
  have hpPos : 0 < p := (Finset.mem_Icc.mp hp).1
  rw [ramanujanSum_nat_divisor_moebius p n hpPos.ne']
  have hgcd : Nat.gcd p n ≠ 0 := Nat.gcd_ne_zero_left hpPos.ne'
  have hset :
      (Nat.gcd p n).divisors =
        (Finset.Icc 1 P).filter fun r ↦ r ∣ p ∧ r ∣ n := by
    ext r
    simp only [Nat.mem_divisors, hgcd, ne_eq, not_false_eq_true,
      Finset.mem_filter, Finset.mem_Icc, and_true]
    constructor
    · intro h
      have hdiv : r ∣ p ∧ r ∣ n := Nat.dvd_gcd_iff.mp h
      have hrPos : 0 < r := Nat.pos_of_dvd_of_pos hdiv.1 hpPos
      have hrle : r ≤ p := Nat.le_of_dvd hpPos hdiv.1
      exact ⟨⟨by omega, hrle.trans (Finset.mem_Icc.mp hp).2⟩,
        hdiv⟩
    · intro h
      exact Nat.dvd_gcd_iff.mpr h.2
  rw [hset, Finset.sum_filter]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hdiv : r ∣ p ∧ r ∣ n
  · simp only [if_pos hdiv]
    unfold ramanujanWindowPairSummand
    ring
  · simp only [if_neg hdiv, mul_zero, zero_mul]

theorem sum_ramanujanPairs_eq_windowDivisorPairs
    (P n : ℕ) (F : ℕ → ℂ) :
    (∑ z ∈ ramanujanWindowPairs P n,
      ramanujanWindowPairSummand F z) =
      ∑ z ∈ windowDivisorPairs P n,
        mobiusWindowPairSummand F z := by
  apply Finset.sum_bij
      (fun z _hz ↦ (z.1 / z.2, z.2))
  · intro z hz
    rcases mem_ramanujanWindowPairs_iff.mp hz with
      ⟨hpOne, hpP, hrOne, hrP, hrp, hrn⟩
    have hpPos : 0 < z.1 := by omega
    have hrPos : 0 < z.2 := by omega
    have hquotPos : 0 < z.1 / z.2 :=
      Nat.div_pos (Nat.le_of_dvd hpPos hrp) hrPos
    have hprod : z.1 / z.2 * z.2 = z.1 := Nat.div_mul_cancel hrp
    apply mem_windowDivisorPairs_iff.mpr
    exact ⟨hquotPos, (Nat.div_le_self _ _).trans hpP,
      hrOne, hrP, hprod.le.trans hpP, hrn⟩
  · intro z₁ hz₁ z₂ hz₂ heq
    rcases mem_ramanujanWindowPairs_iff.mp hz₁ with
      ⟨_hpOne₁, _hpP₁, _hrOne₁, _hrP₁, hrp₁, _hrn₁⟩
    rcases mem_ramanujanWindowPairs_iff.mp hz₂ with
      ⟨_hpOne₂, _hpP₂, _hrOne₂, _hrP₂, hrp₂, _hrn₂⟩
    have hfirst : z₁.1 / z₁.2 = z₂.1 / z₂.2 :=
      @congrArg (ℕ × ℕ) ℕ
        (z₁.1 / z₁.2, z₁.2) (z₂.1 / z₂.2, z₂.2)
        (fun w ↦ Prod.fst w) heq
    have hsecond : z₁.2 = z₂.2 :=
      @congrArg (ℕ × ℕ) ℕ
        (z₁.1 / z₁.2, z₁.2) (z₂.1 / z₂.2, z₂.2)
        (fun w ↦ Prod.snd w) heq
    apply Prod.ext
    · calc
        z₁.1 = z₁.1 / z₁.2 * z₁.2 := (Nat.div_mul_cancel hrp₁).symm
        _ = z₂.1 / z₂.2 * z₂.2 := by rw [hfirst, hsecond]
        _ = z₂.1 := Nat.div_mul_cancel hrp₂
    · exact hsecond
  · intro z hz
    rcases mem_windowDivisorPairs_iff.mp hz with
      ⟨hdOne, hdP, hrOne, hrP, hprodP, hrn⟩
    let source : ℕ × ℕ := (z.1 * z.2, z.2)
    have hsource : source ∈ ramanujanWindowPairs P n := by
      apply mem_ramanujanWindowPairs_iff.mpr
      dsimp [source]
      exact ⟨Nat.mul_pos (by omega) (by omega), hprodP,
        hrOne, hrP, dvd_mul_left _ _, hrn⟩
    refine ⟨source, hsource, ?_⟩
    apply Prod.ext
    · dsimp [source]
      exact Nat.mul_div_left z.1 (by omega)
    · rfl
  · intro z hz
    rcases mem_ramanujanWindowPairs_iff.mp hz with
      ⟨hpOne, _hpP, hrOne, _hrP, hrp, _hrn⟩
    have hpPos : 0 < z.1 := by omega
    have hrPos : 0 < z.2 := by omega
    have hquotPos : 0 < z.1 / z.2 :=
      Nat.div_pos (Nat.le_of_dvd hpPos hrp) hrPos
    have hprod : z.1 / z.2 * z.2 = z.1 := Nat.div_mul_cancel hrp
    have hprodR : (z.1 : ℝ) =
        ((z.1 / z.2 : ℕ) : ℝ) * (z.2 : ℝ) := by
      exact_mod_cast hprod.symm
    unfold ramanujanWindowPairSummand mobiusWindowPairSummand
    rw [hprod, hprodR]
    push_cast
    field_simp [Nat.cast_ne_zero.mpr hquotPos.ne',
      Nat.cast_ne_zero.mpr hrPos.ne']

theorem sum_ramanujanWindow_eq_windowDivisorPairs
    (P n : ℕ) (F : ℕ → ℂ) :
    (∑ p ∈ Finset.Icc 1 P,
      ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
        ramanujanSum p (n : ℤ) * F p) =
      ∑ z ∈ windowDivisorPairs P n,
        mobiusWindowPairSummand F z := by
  rw [sum_ramanujanWindow_eq_ramanujanPairs,
    sum_ramanujanPairs_eq_windowDivisorPairs]

/-! ## Exchange of the finite divisor sum with the carrier series -/

def windowDivisorCarrierSummand
    (N n : ℕ) (ell : ℤ) (z : ℕ × ℕ) : ℂ :=
  ((ArithmeticFunction.moebius z.1 : ℤ) : ℂ) /
      ((z.1 : ℂ) ^ 2 * (z.2 : ℂ)) *
    windowCarrierKernelTerm N z.1 ((n / z.2 : ℕ) : ℤ) ell

theorem sum_windowDivisorCarrierSummand_eq
    (N P n : ℕ) (ell : ℤ) :
    (∑ z ∈ windowDivisorPairs P n,
      windowDivisorCarrierSummand N n ell z) =
      bernoulliMarkFourierCoefficient ell *
        windowModeCoefficient N P ell n := by
  unfold windowModeCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  unfold windowDivisorCarrierSummand windowCarrierKernelTerm
    windowModeSummand
  ring

theorem summable_windowDivisorCarrierSummand
    (N P n : ℕ) (ellPair : ℕ × ℕ)
    (hz : ellPair ∈ windowDivisorPairs P n) :
    Summable fun ell : ℤ ↦
      windowDivisorCarrierSummand N n ell ellPair := by
  have hd : 0 < ellPair.1 := by
    have h := mem_windowDivisorPairs_iff.mp hz
    omega
  have hbase := summable_windowCarrierKernelTerm
    N ellPair.1 ((n / ellPair.2 : ℕ) : ℤ) hd
  exact hbase.mul_left
    (((ArithmeticFunction.moebius ellPair.1 : ℤ) : ℂ) /
      ((ellPair.1 : ℂ) ^ 2 * (ellPair.2 : ℂ)))

/-- Absolute convergence of the carrier expansion of each finite-window
Fourier coefficient.  This is stated separately so later Parseval arguments
do not need to recover convergence from a `tsum` identity. -/
theorem summable_bernoulliMarkFourierCoefficient_mul_windowModeCoefficient
    (N P n : ℕ) :
    Summable fun ell : ℤ ↦
      bernoulliMarkFourierCoefficient ell *
        windowModeCoefficient N P ell n := by
  let S := windowDivisorPairs P n
  have hfinite : ∀ T : Finset (ℕ × ℕ),
      (∀ z ∈ T, Summable fun ell : ℤ ↦
        windowDivisorCarrierSummand N n ell z) →
      Summable fun ell : ℤ ↦
        ∑ z ∈ T, windowDivisorCarrierSummand N n ell z := by
    intro T hT
    induction T using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty] using!
          (summable_zero : Summable fun _ell : ℤ ↦ (0 : ℂ))
    | @insert z T hz ih =>
        have hadd := (hT z (Finset.mem_insert_self z T)).add
          (ih fun w hw ↦ hT w (Finset.mem_insert_of_mem hw))
        simpa only [Finset.sum_insert hz] using! hadd
  have hsum : Summable fun ell : ℤ ↦
      ∑ z ∈ S, windowDivisorCarrierSummand N n ell z := by
    apply hfinite S
    intro z hz
    exact summable_windowDivisorCarrierSummand N P n z (by simpa [S] using! hz)
  apply hsum.congr
  intro ell
  simpa only [S] using! sum_windowDivisorCarrierSummand_eq N P n ell

theorem mobiusWindowPairSummand_nearestCell_eq_neg_tsum
    (N P n : ℕ) (z : ℕ × ℕ)
    (hN : 0 < N) (hn : 0 < n) (hz : z ∈ windowDivisorPairs P n) :
    mobiusWindowPairSummand (nearestCellWindowTransform N n) z =
      -(∑' ell : ℤ, windowDivisorCarrierSummand N n ell z) := by
  rcases mem_windowDivisorPairs_iff.mp hz with
    ⟨hdOne, _hdP, hrOne, _hrP, _hprodP, hrn⟩
  have hd : 0 < z.1 := by omega
  have hr : 0 < z.2 := by omega
  have hm : 0 < n / z.2 :=
    Nat.div_pos (Nat.le_of_dvd hn hrn) hr
  have hcancel := nearestCellWindowTransform_mul_cancel
    N n z.1 z.2 hd hr hrn
  have hcarrier := nearestCellWindowTransform_eq_neg_tsum_carrier
    N (n / z.2) z.1 hN hm hd
  unfold mobiusWindowPairSummand
  rw [hcancel, hcarrier, mul_neg]
  rw [← tsum_mul_left]
  apply congrArg Neg.neg
  apply tsum_congr
  intro ell
  rfl

theorem sum_ramanujanWindow_nearestCell_eq_neg_tsum_windowMode
    (N P n : ℕ) (hN : 0 < N) (hn : 0 < n) :
    (∑ p ∈ Finset.Icc 1 P,
      ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
        ramanujanSum p (n : ℤ) *
          nearestCellWindowTransform N n p) =
      -(∑' ell : ℤ,
        bernoulliMarkFourierCoefficient ell *
          windowModeCoefficient N P ell n) := by
  rw [sum_ramanujanWindow_eq_windowDivisorPairs]
  have hsummable : ∀ z ∈ windowDivisorPairs P n,
      Summable fun ell : ℤ ↦
        windowDivisorCarrierSummand N n ell z :=
    fun z hz ↦ summable_windowDivisorCarrierSummand N P n z hz
  calc
    (∑ z ∈ windowDivisorPairs P n,
        mobiusWindowPairSummand (nearestCellWindowTransform N n) z) =
      ∑ z ∈ windowDivisorPairs P n,
        -(∑' ell : ℤ, windowDivisorCarrierSummand N n ell z) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact mobiusWindowPairSummand_nearestCell_eq_neg_tsum
        N P n z hN hn hz
    _ = -(∑ z ∈ windowDivisorPairs P n,
        ∑' ell : ℤ, windowDivisorCarrierSummand N n ell z) := by
      rw [Finset.sum_neg_distrib]
    _ = -(∑' ell : ℤ, ∑ z ∈ windowDivisorPairs P n,
        windowDivisorCarrierSummand N n ell z) := by
      rw [Summable.tsum_finsetSum hsummable]
    _ = -(∑' ell : ℤ,
        bernoulliMarkFourierCoefficient ell *
          windowModeCoefficient N P ell n) := by
      congr 1
      apply tsum_congr
      intro ell
      exact sum_windowDivisorCarrierSummand_eq N P n ell

/-- Final exact positive-frequency coefficient bridge.  The minus sign is
forced by the opposite orientations of the two error definitions. -/
theorem naturalCutoffShotErrorCoefficient_eq_neg_tsum_windowMode
    (N : ℕ+) (n : ℕ) (hn : 0 < n) :
    naturalCutoffShotErrorCoefficient N (n : ℤ) =
      -(∑' ell : ℤ,
        bernoulliMarkFourierCoefficient ell *
          windowModeCoefficient (N : ℕ) (N : ℕ) ell n) := by
  rw [naturalCutoffShotErrorCoefficient_nat N n hn]
  exact sum_ramanujanWindow_nearestCell_eq_neg_tsum_windowMode
    (N : ℕ) (N : ℕ) n N.pos hn

end

end Erdos1002
