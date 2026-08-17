import ErdosProblems.Erdos469

/-!
# The small-prime Euler ratio for Erdős Problem 121

In the specialized `K₅` construction a small prime is either unused or is
assigned to one of the ten edges, with assigned weight `1/(4p)`.  After one
output vertex is fixed, only the six nonincident edges remain free.  The
ratio of the corresponding Euler products is `O(1 / log Y)`.  This is the
single logarithmic gain in Tao's marginal estimate.
-/

open scoped BigOperators

namespace Erdos121

set_option autoImplicit false

noncomputable section

/-- Euler normalization when a small prime has `a` possible assigned labels,
each carrying weight `1/(4p)`. -/
def smallEuler (a Y : ℕ) : ℝ :=
  (Erdos469.primesThrough Y).prod fun p => 1 + (a : ℝ) / (4 * p)

lemma smallEuler_pos (a Y : ℕ) : 0 < smallEuler a Y := by
  apply Finset.prod_pos
  intro p hp
  have hpPos : (0 : ℝ) < p := by
    exact_mod_cast (Erdos469.mem_primesThrough.mp hp).1.pos
  positivity

private lemma local_six_ten_ratio {p : ℕ} (hp : p.Prime) :
    1 + (6 : ℝ) / (4 * p) ≤
      (1 + 5 / (p : ℝ) ^ 2) * Erdos469.mertensLinearFactor p *
        (1 + (10 : ℝ) / (4 * p)) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (by positivity)
  rw [Erdos469.mertensLinearFactor]
  simp only [zpow_neg, zpow_ofNat]
  field_simp
  ring_nf
  have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hnonneg : 0 ≤ ((p : ℝ) - 2) * ((p : ℝ) + 2) :=
    mul_nonneg (sub_nonneg.mpr hp2R) (by positivity)
  nlinarith

lemma smallEuler_six_le_correction_mul_linear_mul_ten (Y : ℕ) :
    smallEuler 6 Y ≤
      ((Erdos469.primesThrough Y).prod fun p => 1 + 5 / (p : ℝ) ^ 2) *
        ((Erdos469.primesThrough Y).prod Erdos469.mertensLinearFactor) *
          smallEuler 10 Y := by
  rw [smallEuler, smallEuler]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    simpa [mul_assoc] using
      local_six_ten_ratio (Erdos469.mem_primesThrough.mp hp).1

lemma smallEuler_correction_le (Y : ℕ) :
    (Erdos469.primesThrough Y).prod (fun p => 1 + 5 / (p : ℝ) ^ 2) ≤
      Real.exp (5 * Erdos469.naturalSquareSeries) := by
  calc
    (Erdos469.primesThrough Y).prod (fun p => 1 + 5 / (p : ℝ) ^ 2) ≤
        (Erdos469.primesThrough Y).prod
          (fun p => Real.exp (5 / (p : ℝ) ^ 2)) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        simpa [add_comm] using Real.add_one_le_exp (5 / (p : ℝ) ^ 2)
    _ = Real.exp ((Erdos469.primesThrough Y).sum
        (fun p => 5 / (p : ℝ) ^ 2)) := by
      rw [← Real.exp_sum]
    _ ≤ Real.exp (5 * Erdos469.naturalSquareSeries) := by
      apply Real.exp_le_exp.mpr
      simp only [div_eq_mul_inv]
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [Erdos469.naturalSquareSeries]
      simpa [one_div] using
        (Erdos469.summable_naturalSquareSeries.sum_le_tsum
          (Erdos469.primesThrough Y) (fun _ _ => by positivity))

/-- The six-label normalization is smaller than the ten-label normalization
by one full logarithm. -/
theorem smallEuler_six_le_ten_div_log {Y : ℕ} (hY : 2 ≤ Y) :
    smallEuler 6 Y ≤
      (Real.exp (5 * Erdos469.naturalSquareSeries) *
          Erdos469.naturalLinearMertensUpper / Real.log (Y : ℝ)) *
        smallEuler 10 Y := by
  have hcorr := smallEuler_correction_le Y
  have hlinear := (Erdos469.natural_linearMertensProduct_bounds hY).2
  have hten : 0 ≤ smallEuler 10 Y := (smallEuler_pos 10 Y).le
  have hlinNonneg : 0 ≤
      (Erdos469.primesThrough Y).prod Erdos469.mertensLinearFactor :=
    Erdos469.linearMertensProduct_nonneg Y
  calc
    smallEuler 6 Y ≤
        ((Erdos469.primesThrough Y).prod fun p => 1 + 5 / (p : ℝ) ^ 2) *
          ((Erdos469.primesThrough Y).prod Erdos469.mertensLinearFactor) *
            smallEuler 10 Y :=
      smallEuler_six_le_correction_mul_linear_mul_ten Y
    _ ≤ Real.exp (5 * Erdos469.naturalSquareSeries) *
          ((Erdos469.primesThrough Y).prod Erdos469.mertensLinearFactor) *
            smallEuler 10 Y := by
      gcongr
    _ ≤ Real.exp (5 * Erdos469.naturalSquareSeries) *
          (Erdos469.naturalLinearMertensUpper / Real.log (Y : ℝ)) *
            smallEuler 10 Y := by
      gcongr
    _ = (Real.exp (5 * Erdos469.naturalSquareSeries) *
          Erdos469.naturalLinearMertensUpper / Real.log (Y : ℝ)) *
        smallEuler 10 Y := by ring

end

end Erdos121
