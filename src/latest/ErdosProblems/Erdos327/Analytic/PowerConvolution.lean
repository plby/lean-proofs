import Mathlib

/-!
# Finite convolution bounds for negative real powers

This file records the elementary terminal-sum estimate used when two
logarithmic power envelopes are convolved.  Both endpoint exponents are
assumed to lie in `(-1, 0)`: the lower bound by `-1` makes the endpoint
singularities summable, while the upper bound by `0` supplies the
monotonicity used in the proof.
-/

namespace Erdos327.Analytic

open Filter Finset Real Set Topology

open scoped BigOperators

noncomputable section

/-- A convenient constant for partial sums of a power in `(-1, 0]`. -/
def partialRpowConstant (r : ℝ) : ℝ := (r + 1)⁻¹

theorem partialRpowConstant_pos
    {r : ℝ} (hr : -1 < r) :
    0 < partialRpowConstant r := by
  unfold partialRpowConstant
  exact inv_pos.mpr (by linarith)

/-- The partial sums of `j ↦ (j + 1) ^ r`, for `-1 < r ≤ 0`, have their
expected integral-test upper bound. -/
theorem sum_range_add_one_rpow_le
    {r : ℝ} (hrLower : -1 < r) (hrUpper : r ≤ 0) (n : ℕ) :
    (∑ j ∈ range (n + 1), ((j + 1 : ℕ) : ℝ) ^ r) ≤
      partialRpowConstant r * (((n + 1 : ℕ) : ℝ) ^ (r + 1)) := by
  have hrOne : 0 < r + 1 := by linarith
  have hrOneLe : r + 1 ≤ 1 := by linarith
  have hanti :
      AntitoneOn (fun x : ℝ ↦ x ^ r)
        (Icc 1 (1 + (n : ℝ))) := by
    exact
      (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hrUpper).mono
        (by
          intro x hx
          exact lt_of_lt_of_le zero_lt_one hx.1)
  have hint :=
    AntitoneOn.sum_le_integral
      (x₀ := (1 : ℝ)) (a := n) (f := fun x : ℝ ↦ x ^ r) hanti
  have hint' :
      (∑ j ∈ range n, (((j + 2 : ℕ) : ℝ) ^ r)) ≤
        ((((n + 1 : ℕ) : ℝ) ^ (r + 1) - 1) / (r + 1)) := by
    rw [integral_rpow (Or.inl hrLower)] at hint
    convert hint using 1 <;>
      norm_num [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]
  have hbase : 1 ≤ (((n + 1 : ℕ) : ℝ) ^ (r + 1)) := by
    have h :=
      Real.rpow_le_rpow (x := (1 : ℝ)) (y := ((n + 1 : ℕ) : ℝ))
        (z := r + 1) (by norm_num)
        (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) hrOne.le
    simpa only [Real.one_rpow] using h
  rw [sum_range_succ']
  change
    (∑ j ∈ range n, (((j + 2 : ℕ) : ℝ) ^ r)) +
        (((1 : ℕ) : ℝ) ^ r) ≤ _
  simp only [Nat.cast_one, Real.one_rpow]
  unfold partialRpowConstant
  rw [inv_mul_eq_div]
  calc
    ∑ j ∈ range n, ((j + 2 : ℕ) : ℝ) ^ r + 1
        ≤ 1 + ((((n + 1 : ℕ) : ℝ) ^ (r + 1) - 1) / (r + 1)) :=
          by linarith
    _ ≤ (((n + 1 : ℕ) : ℝ) ^ (r + 1)) / (r + 1) := by
      have hdiv :
          ((((n + 1 : ℕ) : ℝ) ^ (r + 1) - 1) / (r + 1)) ≤
            ((((n + 1 : ℕ) : ℝ) ^ (r + 1) - (r + 1)) / (r + 1)) := by
        exact (div_le_div_iff_of_pos_right hrOne).2 (by linarith)
      calc
        1 + ((((n + 1 : ℕ) : ℝ) ^ (r + 1) - 1) / (r + 1))
            ≤ 1 + ((((n + 1 : ℕ) : ℝ) ^ (r + 1) - (r + 1)) / (r + 1)) :=
              by linarith
        _ = (((n + 1 : ℕ) : ℝ) ^ (r + 1)) / (r + 1) := by
          field_simp
          ring

/-- Reflection of a finite power sum across the interval `0, ..., n`. -/
theorem sum_range_sub_add_one_rpow
    (r : ℝ) (n : ℕ) :
    (∑ j ∈ range (n + 1), (((n - j + 1 : ℕ) : ℝ) ^ r)) =
      ∑ j ∈ range (n + 1), (((j + 1 : ℕ) : ℝ) ^ r) := by
  apply Finset.sum_bij (fun j _ ↦ n - j)
  · intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  · intro a₁ ha₁ a₂ ha₂ h
    simp only [Finset.mem_range] at ha₁ ha₂
    omega
  · intro b hb
    simp only [Finset.mem_range] at hb
    refine ⟨n - b, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro j hj
    rfl

/-- Constant in the two-ended finite power-convolution estimate. -/
def powerConvolutionConstant (p q : ℝ) : ℝ :=
  (1 / 2 : ℝ) ^ q * partialRpowConstant p +
    (1 / 2 : ℝ) ^ p * partialRpowConstant q

theorem powerConvolutionConstant_pos
    {p q : ℝ} (hp : -1 < p) (hq : -1 < q) :
    0 < powerConvolutionConstant p q := by
  unfold powerConvolutionConstant
  exact
    add_pos
      (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
        (partialRpowConstant_pos hp))
      (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
        (partialRpowConstant_pos hq))

private theorem power_convolution_term_le
    {p q : ℝ} (hp : p ≤ 0) (hq : q ≤ 0)
    {n j : ℕ} (hj : j ∈ range (n + 1)) :
    (((j + 1 : ℕ) : ℝ) ^ p) *
          (((n - j + 1 : ℕ) : ℝ) ^ q) ≤
      ((1 / 2 : ℝ) ^ q * (((n + 1 : ℕ) : ℝ) ^ q)) *
          (((j + 1 : ℕ) : ℝ) ^ p) +
        ((1 / 2 : ℝ) ^ p * (((n + 1 : ℕ) : ℝ) ^ p)) *
          (((n - j + 1 : ℕ) : ℝ) ^ q) := by
  have hjn : j ≤ n := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hj
  have hNpos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have haPos : 0 < (((j + 1 : ℕ) : ℝ)) := by positivity
  have hbPos : 0 < (((n - j + 1 : ℕ) : ℝ)) := by positivity
  by_cases hab : j + 1 ≤ n - j + 1
  · have hhalf :
        (((n + 1 : ℕ) : ℝ)) / 2 ≤
          (((n - j + 1 : ℕ) : ℝ)) := by
      have hnat : n + 1 ≤ 2 * (n - j + 1) := by omega
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      exact_mod_cast (by simpa [mul_comm] using hnat)
    have hqpow :
        (((n - j + 1 : ℕ) : ℝ) ^ q) ≤
          ((((n + 1 : ℕ) : ℝ) / 2) ^ q) :=
      Real.rpow_le_rpow_of_nonpos
        (div_pos hNpos (by norm_num)) hhalf hq
    calc
      (((j + 1 : ℕ) : ℝ) ^ p) *
            (((n - j + 1 : ℕ) : ℝ) ^ q)
          ≤ (((j + 1 : ℕ) : ℝ) ^ p) *
              ((((n + 1 : ℕ) : ℝ) / 2) ^ q) :=
            mul_le_mul_of_nonneg_left hqpow (Real.rpow_nonneg haPos.le _)
      _ = ((1 / 2 : ℝ) ^ q * (((n + 1 : ℕ) : ℝ) ^ q)) *
            (((j + 1 : ℕ) : ℝ) ^ p) := by
          rw [show (((n + 1 : ℕ) : ℝ) / 2) =
              (1 / 2 : ℝ) * (((n + 1 : ℕ) : ℝ)) by ring,
            Real.mul_rpow (by norm_num) hNpos.le]
          ring
      _ ≤ ((1 / 2 : ℝ) ^ q * (((n + 1 : ℕ) : ℝ) ^ q)) *
              (((j + 1 : ℕ) : ℝ) ^ p) +
            ((1 / 2 : ℝ) ^ p * (((n + 1 : ℕ) : ℝ) ^ p)) *
              (((n - j + 1 : ℕ) : ℝ) ^ q) := by
          apply le_add_of_nonneg_right
          exact
            mul_nonneg
              (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
                (Real.rpow_nonneg hNpos.le _))
              (Real.rpow_nonneg hbPos.le _)
  · have hba : n - j + 1 ≤ j + 1 := by omega
    have hhalf :
        (((n + 1 : ℕ) : ℝ)) / 2 ≤
          (((j + 1 : ℕ) : ℝ)) := by
      have hnat : n + 1 ≤ 2 * (j + 1) := by omega
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      exact_mod_cast (by simpa [mul_comm] using hnat)
    have hppow :
        (((j + 1 : ℕ) : ℝ) ^ p) ≤
          ((((n + 1 : ℕ) : ℝ) / 2) ^ p) :=
      Real.rpow_le_rpow_of_nonpos
        (div_pos hNpos (by norm_num)) hhalf hp
    calc
      (((j + 1 : ℕ) : ℝ) ^ p) *
            (((n - j + 1 : ℕ) : ℝ) ^ q)
          ≤ ((((n + 1 : ℕ) : ℝ) / 2) ^ p) *
              (((n - j + 1 : ℕ) : ℝ) ^ q) :=
            mul_le_mul_of_nonneg_right hppow (Real.rpow_nonneg hbPos.le _)
      _ = ((1 / 2 : ℝ) ^ p * (((n + 1 : ℕ) : ℝ) ^ p)) *
            (((n - j + 1 : ℕ) : ℝ) ^ q) := by
          rw [show (((n + 1 : ℕ) : ℝ) / 2) =
              (1 / 2 : ℝ) * (((n + 1 : ℕ) : ℝ)) by ring,
            Real.mul_rpow (by norm_num) hNpos.le]
      _ ≤ ((1 / 2 : ℝ) ^ q * (((n + 1 : ℕ) : ℝ) ^ q)) *
              (((j + 1 : ℕ) : ℝ) ^ p) +
            ((1 / 2 : ℝ) ^ p * (((n + 1 : ℕ) : ℝ) ^ p)) *
              (((n - j + 1 : ℕ) : ℝ) ^ q) := by
          apply le_add_of_nonneg_left
          exact
            mul_nonneg
              (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
                (Real.rpow_nonneg hNpos.le _))
              (Real.rpow_nonneg haPos.le _)

/-- A finite convolution of two powers in `(-1, 0)` is bounded by the
power predicted by scaling.  The constant is explicit and independent of
`n`. -/
theorem sum_range_power_convolution_le
    {p q : ℝ}
    (hpLower : -1 < p) (hpUpper : p ≤ 0)
    (hqLower : -1 < q) (hqUpper : q ≤ 0)
    (n : ℕ) :
    (∑ j ∈ range (n + 1),
        (((j + 1 : ℕ) : ℝ) ^ p) *
          (((n - j + 1 : ℕ) : ℝ) ^ q)) ≤
      powerConvolutionConstant p q *
        (((n + 1 : ℕ) : ℝ) ^ (p + q + 1)) := by
  have hNpos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hpSum :=
    sum_range_add_one_rpow_le hpLower hpUpper n
  have hqSum :=
    sum_range_add_one_rpow_le hqLower hqUpper n
  have hqSum' :
      (∑ j ∈ range (n + 1),
          (((n - j + 1 : ℕ) : ℝ) ^ q)) ≤
        partialRpowConstant q *
          (((n + 1 : ℕ) : ℝ) ^ (q + 1)) := by
    rw [sum_range_sub_add_one_rpow]
    exact hqSum
  calc
    (∑ j ∈ range (n + 1),
        (((j + 1 : ℕ) : ℝ) ^ p) *
          (((n - j + 1 : ℕ) : ℝ) ^ q))
        ≤ ∑ j ∈ range (n + 1),
            (((1 / 2 : ℝ) ^ q * (((n + 1 : ℕ) : ℝ) ^ q)) *
                (((j + 1 : ℕ) : ℝ) ^ p) +
              ((1 / 2 : ℝ) ^ p * (((n + 1 : ℕ) : ℝ) ^ p)) *
                (((n - j + 1 : ℕ) : ℝ) ^ q)) := by
          apply sum_le_sum
          intro j hj
          exact power_convolution_term_le hpUpper hqUpper hj
    _ =
        ((1 / 2 : ℝ) ^ q * (((n + 1 : ℕ) : ℝ) ^ q)) *
            (∑ j ∈ range (n + 1), (((j + 1 : ℕ) : ℝ) ^ p)) +
          ((1 / 2 : ℝ) ^ p * (((n + 1 : ℕ) : ℝ) ^ p)) *
            (∑ j ∈ range (n + 1),
              (((n - j + 1 : ℕ) : ℝ) ^ q)) := by
          rw [sum_add_distrib, mul_sum, mul_sum]
    _ ≤
        ((1 / 2 : ℝ) ^ q * (((n + 1 : ℕ) : ℝ) ^ q)) *
            (partialRpowConstant p *
              (((n + 1 : ℕ) : ℝ) ^ (p + 1))) +
          ((1 / 2 : ℝ) ^ p * (((n + 1 : ℕ) : ℝ) ^ p)) *
            (partialRpowConstant q *
              (((n + 1 : ℕ) : ℝ) ^ (q + 1))) := by
          exact
            add_le_add
              (mul_le_mul_of_nonneg_left hpSum
                (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
                  (Real.rpow_nonneg hNpos.le _)))
              (mul_le_mul_of_nonneg_left hqSum'
                (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
                  (Real.rpow_nonneg hNpos.le _)))
    _ = powerConvolutionConstant p q *
          (((n + 1 : ℕ) : ℝ) ^ (p + q + 1)) := by
      have hqp :
          (((n + 1 : ℕ) : ℝ) ^ q) *
              (((n + 1 : ℕ) : ℝ) ^ (p + 1)) =
            (((n + 1 : ℕ) : ℝ) ^ (p + q + 1)) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
      have hpq :
          (((n + 1 : ℕ) : ℝ) ^ p) *
              (((n + 1 : ℕ) : ℝ) ^ (q + 1)) =
            (((n + 1 : ℕ) : ℝ) ^ (p + q + 1)) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
      unfold powerConvolutionConstant
      calc
        ((1 / 2 : ℝ) ^ q * (((n + 1 : ℕ) : ℝ) ^ q)) *
              (partialRpowConstant p *
                (((n + 1 : ℕ) : ℝ) ^ (p + 1))) +
            ((1 / 2 : ℝ) ^ p * (((n + 1 : ℕ) : ℝ) ^ p)) *
              (partialRpowConstant q *
                (((n + 1 : ℕ) : ℝ) ^ (q + 1)))
            =
              ((1 / 2 : ℝ) ^ q * partialRpowConstant p) *
                  ((((n + 1 : ℕ) : ℝ) ^ q) *
                    (((n + 1 : ℕ) : ℝ) ^ (p + 1))) +
                ((1 / 2 : ℝ) ^ p * partialRpowConstant q) *
                  ((((n + 1 : ℕ) : ℝ) ^ p) *
                    (((n + 1 : ℕ) : ℝ) ^ (q + 1))) := by ring
        _ =
              ((1 / 2 : ℝ) ^ q * partialRpowConstant p) *
                  (((n + 1 : ℕ) : ℝ) ^ (p + q + 1)) +
                ((1 / 2 : ℝ) ^ p * partialRpowConstant q) *
                  (((n + 1 : ℕ) : ℝ) ^ (p + q + 1)) := by
              rw [hqp, hpq]
        _ =
              ((1 / 2 : ℝ) ^ q * partialRpowConstant p +
                  (1 / 2 : ℝ) ^ p * partialRpowConstant q) *
                (((n + 1 : ℕ) : ℝ) ^ (p + q + 1)) := by ring

/-- If the scaling exponent is negative, the finite convolution tends to
zero.  This is the terminal form used after inserting the chosen analytic
parameters. -/
theorem tendsto_sum_range_power_convolution_atTop
    {p q : ℝ}
    (hpLower : -1 < p) (hpUpper : p ≤ 0)
    (hqLower : -1 < q) (hqUpper : q ≤ 0)
    (hsum : p + q + 1 < 0) :
    Tendsto
      (fun n : ℕ ↦
        ∑ j ∈ range (n + 1),
          (((j + 1 : ℕ) : ℝ) ^ p) *
            (((n - j + 1 : ℕ) : ℝ) ^ q))
      atTop (𝓝 0) := by
  have hscale :
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hrpow :
      Tendsto
        (fun n : ℕ ↦
          (((n + 1 : ℕ) : ℝ) ^ (p + q + 1)))
        atTop (𝓝 0) := by
    have h :=
      (tendsto_rpow_neg_atTop (y := -(p + q + 1))
        (neg_pos.mpr hsum)).comp hscale
    convert h using 1
    funext n
    congr 1
    ring
  apply squeeze_zero
  · intro n
    apply sum_nonneg
    intro j hj
    exact
      mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg (by positivity) _)
  · intro n
    exact
      sum_range_power_convolution_le
        hpLower hpUpper hqLower hqUpper n
  · simpa using
      (hrpow.const_mul (powerConvolutionConstant p q))

end

end Erdos327.Analytic
