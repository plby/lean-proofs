import ErdosProblems.Erdos444.Analytic

/-!
# A discrete parameter estimate for the support split

The coarse proof of Erdős 444 uses two integer scales.  Put `r = m²`, take
the large-prime cutoff `y = m²`, declare multiplicity excess above
`2*r*b` exceptional, and require at least `4*r*b` distinct primes in the
remaining case.  The estimates below show that both exceptional supports
are small enough for the tuple moment after multiplication by any fixed
power `y^q`, provided `b ≥ q+2`.
-/

namespace Erdos444

/-- The elementary scale inequality used for the square-divisor part. -/
theorem four_mul_scaledPower_le_parameterPower
    (m b q : ℕ) (hm : 2 ≤ m) (hb : q + 2 ≤ b) :
    (4 : ℝ) * (2 * ((m ^ 2 : ℕ) : ℝ) ^ q) ^ (m ^ 2) ≤
      ((m ^ 2 : ℕ) : ℝ) ^ ((m ^ 2) * b) := by
  let y : ℝ := ((m ^ 2 : ℕ) : ℝ)
  let r : ℕ := m ^ 2
  have hy : (2 : ℝ) ≤ y := by
    dsimp [y]
    norm_num only [Nat.cast_pow]
    nlinarith [show (2 : ℝ) ≤ m by exact_mod_cast hm]
  have hr : 2 ≤ r := by
    dsimp [r]
    nlinarith
  have hbase : 2 * y ^ q ≤ y ^ (q + 1) := by
    rw [pow_succ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hy) (pow_nonneg (by positivity) q)]
  have hscale : (2 * y ^ q) ^ r ≤ y ^ ((q + 1) * r) := by
    simpa [pow_mul] using pow_le_pow_left₀ (by positivity) hbase r
  have hfour : (4 : ℝ) ≤ y ^ r := by
    have : (4 : ℝ) ≤ y ^ 2 := by nlinarith [sq_nonneg (y - 2)]
    exact this.trans (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ y) (by omega))
  calc
    (4 : ℝ) * (2 * (((m ^ 2 : ℕ) : ℝ)) ^ q) ^ (m ^ 2) =
        4 * (2 * y ^ q) ^ r := by rfl
    _ ≤ y ^ r * y ^ ((q + 1) * r) :=
      mul_le_mul hfour hscale (pow_nonneg (by positivity) r) (by positivity)
    _ = y ^ ((q + 2) * r) := by rw [← pow_add]; congr 1; ring
    _ ≤ y ^ (r * b) := by
      apply pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ y)
      nlinarith
    _ = ((m ^ 2 : ℕ) : ℝ) ^ ((m ^ 2) * b) := by rfl

/-- The same scale is also dominated by the much larger factorial threshold
power `m^(4*r*b)`. -/
theorem four_mul_scaledPower_le_deviationPower
    (m b q : ℕ) (hm : 2 ≤ m) (hb : q + 2 ≤ b) :
    (4 : ℝ) * (2 * ((m ^ 2 : ℕ) : ℝ) ^ q) ^ (m ^ 2) ≤
      (m : ℝ) ^ (4 * (m ^ 2) * b) := by
  have hfirst := four_mul_scaledPower_le_parameterPower m b q hm hb
  have hcast : (((m ^ 2 : ℕ) : ℝ)) ^ ((m ^ 2) * b) =
      (m : ℝ) ^ (2 * ((m ^ 2) * b)) := by
    norm_num only [Nat.cast_pow]
    rw [← pow_mul]
  rw [hcast] at hfirst
  have hm1 : 1 ≤ m := by omega
  exact hfirst.trans (pow_le_pow_right₀
    (by exact_mod_cast hm1 : (1 : ℝ) ≤ m)
    (by nlinarith : 2 * (m ^ 2 * b) ≤ 4 * m ^ 2 * b))

/-- At the threshold `K=4*m²*b`, the elementary-symmetric deviation term is
at most `m⁻ᴷ`, as soon as its mean is at most `m`. -/
theorem factorialDeviation_le_inv_parameterPower
    (μ : ℝ) (m b : ℕ) (hμ0 : 0 ≤ μ) (hμm : μ ≤ m)
    (hm : 2 ≤ m) (hb : 1 ≤ b) :
    μ ^ (4 * (m ^ 2) * b) / ((4 * (m ^ 2) * b).factorial : ℝ) ≤
      ((m : ℝ) ^ (4 * (m ^ 2) * b))⁻¹ := by
  let K : ℕ := 4 * (m ^ 2) * b
  have hK : 0 < K := by dsimp [K]; positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hm)
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbase : Real.exp 1 * μ / (K : ℝ) ≤ (m : ℝ)⁻¹ := by
    rw [div_le_iff₀ (by exact_mod_cast hK : (0 : ℝ) < K)]
    rw [show (m : ℝ)⁻¹ * (K : ℝ) = (K : ℝ) / (m : ℝ) by
      rw [div_eq_mul_inv]; ring]
    rw [le_div_iff₀ hmR]
    dsimp [K]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    have hexp : Real.exp 1 < 3 := Real.exp_one_lt_three
    have hmcast : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hem : Real.exp 1 * μ ≤ 3 * (m : ℝ) :=
      mul_le_mul hexp.le hμm hμ0 (by positivity)
    have hemm := mul_le_mul_of_nonneg_right hem hmR.le
    have hb4 : (3 : ℝ) ≤ 4 * b := by nlinarith
    have hlast : 3 * (m : ℝ) * m ≤ 4 * m ^ 2 * b := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hb4) (sq_nonneg (m : ℝ))]
    exact hemm.trans hlast
  calc
    μ ^ (4 * (m ^ 2) * b) / ((4 * (m ^ 2) * b).factorial : ℝ) =
        μ ^ K / (K.factorial : ℝ) := by rfl
    _ ≤ (Real.exp 1 * μ / (K : ℝ)) ^ K :=
      pow_div_factorial_le_exp_mul_div_pow μ K hμ0 hK
    _ ≤ ((m : ℝ)⁻¹) ^ K :=
      pow_le_pow_left₀ (by positivity) hbase K
    _ = ((m : ℝ) ^ (4 * (m ^ 2) * b))⁻¹ := by
      rw [inv_pow]

/-- Combined support-size estimate.  `N` is the ambient interval size and
`S` the support cardinality.  The two summands are precisely the
square-divisor and many-distinct-primes bounds. -/
theorem support_scale_bound
    (N S μ : ℝ) (m b q : ℕ)
    (hN : 0 ≤ N) (_hS : 0 ≤ S) (hμ0 : 0 ≤ μ) (hμm : μ ≤ m)
    (hm : 2 ≤ m) (hb : q + 2 ≤ b)
    (hbound : S ≤
      N / ((m ^ 2 : ℕ) : ℝ) ^ ((m ^ 2) * b) +
      N * (μ ^ (4 * (m ^ 2) * b) /
        ((4 * (m ^ 2) * b).factorial : ℝ))) :
    2 * S * (2 * ((m ^ 2 : ℕ) : ℝ) ^ q) ^ (m ^ 2) ≤ N := by
  let scale : ℝ := (2 * ((m ^ 2 : ℕ) : ℝ) ^ q) ^ (m ^ 2)
  let den₁ : ℝ := ((m ^ 2 : ℕ) : ℝ) ^ ((m ^ 2) * b)
  let den₂ : ℝ := (m : ℝ) ^ (4 * (m ^ 2) * b)
  have hden₁ : 0 < den₁ := by dsimp [den₁]; positivity
  have hden₂ : 0 < den₂ := by dsimp [den₂]; positivity
  have hs₁ : 4 * scale ≤ den₁ := by
    exact four_mul_scaledPower_le_parameterPower m b q hm hb
  have hs₂ : 4 * scale ≤ den₂ := by
    exact four_mul_scaledPower_le_deviationPower m b q hm hb
  have hfac : μ ^ (4 * (m ^ 2) * b) /
      ((4 * (m ^ 2) * b).factorial : ℝ) ≤ den₂⁻¹ :=
    factorialDeviation_le_inv_parameterPower μ m b hμ0 hμm hm (by omega)
  have hone : N / den₁ * scale ≤ N / 4 := by
    have hratio : scale / den₁ ≤ (1 : ℝ) / 4 := by
      rw [div_le_iff₀ hden₁]
      nlinarith
    calc
      N / den₁ * scale = N * (scale / den₁) := by ring
      _ ≤ N * ((1 : ℝ) / 4) := mul_le_mul_of_nonneg_left hratio hN
      _ = N / 4 := by ring
  have htwo : N * (μ ^ (4 * (m ^ 2) * b) /
      ((4 * (m ^ 2) * b).factorial : ℝ)) * scale ≤ N / 4 := by
    calc
      N * (μ ^ (4 * (m ^ 2) * b) /
          ((4 * (m ^ 2) * b).factorial : ℝ)) * scale
          ≤ N * den₂⁻¹ * scale := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hfac hN) (by positivity)
      _ ≤ N / 4 := by
        have hratio : den₂⁻¹ * scale ≤ (1 : ℝ) / 4 := by
          rw [inv_mul_eq_div, div_le_iff₀ hden₂]
          nlinarith
        calc
          N * den₂⁻¹ * scale = N * (den₂⁻¹ * scale) := by ring
          _ ≤ N * ((1 : ℝ) / 4) := mul_le_mul_of_nonneg_left hratio hN
          _ = N / 4 := by ring
  have hscaled : S * scale ≤ N / 2 := by
    calc
      S * scale ≤
          (N / den₁ + N * (μ ^ (4 * (m ^ 2) * b) /
            ((4 * (m ^ 2) * b).factorial : ℝ))) * scale :=
        mul_le_mul_of_nonneg_right hbound (by positivity)
      _ = N / den₁ * scale + N * (μ ^ (4 * (m ^ 2) * b) /
            ((4 * (m ^ 2) * b).factorial : ℝ)) * scale := by ring
      _ ≤ N / 4 + N / 4 := add_le_add hone htwo
      _ = N / 2 := by ring
  nlinarith

end Erdos444
