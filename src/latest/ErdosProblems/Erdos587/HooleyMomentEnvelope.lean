import ErdosProblems.Erdos587.HooleyPrimeRecursion

/-!
# An integer-exponent envelope for the moment induction

The final square-location argument has enough room to use a weaker Delta
mean bound. The envelope `(q!)^2 B^(q-1)` avoids fractional exponents and
the Gaussian truncation in the sharp Koukoulopoulos--Tao estimate. Here
we prove its algebraic convolution and growth bounds, not a mean-value
estimate.
-/

open scoped BigOperators

namespace Erdos587

def deltaMomentEnvelope (B : ℝ) (q : ℕ) : ℝ :=
  (q.factorial : ℝ) ^ 2 * B ^ (q - 1)

@[simp] lemma deltaMomentEnvelope_one (B : ℝ) : deltaMomentEnvelope B 1 = 1 := by
  norm_num [deltaMomentEnvelope]

@[simp] lemma deltaMomentEnvelope_two (B : ℝ) : deltaMomentEnvelope B 2 = 4 * B := by
  norm_num [deltaMomentEnvelope]

lemma deltaMomentEnvelope_nonneg {B : ℝ} (hB : 0 ≤ B) (q : ℕ) :
    0 ≤ deltaMomentEnvelope B q := by
  unfold deltaMomentEnvelope
  positivity

lemma self_le_choose_of_le_half {q b : ℕ} (hb : 1 ≤ b) (hbq : b ≤ q / 2) :
    q ≤ q.choose b := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases hb0 : b = 0
    · simp [hb0]
    · exact (ih (Nat.one_le_iff_ne_zero.mpr hb0) (by omega)).trans
        (Nat.choose_le_succ_of_lt_half_left (by omega))

lemma deltaMomentEnvelope_binomial_term {B : ℝ} (hB : 0 ≤ B)
    {q b : ℕ} (hb : 1 ≤ b) (hbq : b ≤ q / 2) :
    B * (q : ℝ) * ((q.choose b : ℝ) * deltaMomentEnvelope B b *
      deltaMomentEnvelope B (q - b)) ≤ deltaMomentEnvelope B q := by
  have hble : b ≤ q := hbq.trans (Nat.div_le_self q 2)
  have hfact : (q.choose b : ℝ) * b.factorial * (q - b).factorial = q.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hble
  have hchoose : (q : ℝ) ≤ q.choose b := by
    exact_mod_cast self_le_choose_of_le_half hb hbq
  have hfactor : (q : ℝ) * q.choose b * (b.factorial : ℝ) ^ 2 *
      ((q - b).factorial : ℝ) ^ 2 ≤ (q.factorial : ℝ) ^ 2 := by
    calc
      _ = (q : ℝ) * ((q.choose b : ℝ) * (b.factorial : ℝ) ^ 2 *
          ((q - b).factorial : ℝ) ^ 2) := by ring
      _ ≤ (q.choose b : ℝ) * ((q.choose b : ℝ) * (b.factorial : ℝ) ^ 2 *
          ((q - b).factorial : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hchoose (by positivity)
      _ = ((q.choose b : ℝ) * b.factorial * (q - b).factorial) ^ 2 := by ring
      _ = (q.factorial : ℝ) ^ 2 := by rw [hfact]
  have hexp : b - 1 + (q - b - 1) + 1 = q - 1 := by omega
  calc
    _ = ((q : ℝ) * q.choose b * (b.factorial : ℝ) ^ 2 *
          ((q - b).factorial : ℝ) ^ 2) *
        (B ^ (b - 1) * B ^ (q - b - 1) * B) := by
      unfold deltaMomentEnvelope
      ring
    _ = ((q : ℝ) * q.choose b * (b.factorial : ℝ) ^ 2 *
          ((q - b).factorial : ℝ) ^ 2) * B ^ (q - 1) := by
      rw [← pow_add, ← pow_succ, hexp]
    _ ≤ deltaMomentEnvelope B q :=
      mul_le_mul_of_nonneg_right hfactor (pow_nonneg hB _)

/-- The full convolution is paid for by one factor of the envelope scale. -/
theorem deltaMomentEnvelope_convolution {B : ℝ} (hB : 0 ≤ B)
    {q : ℕ} (hq : q ≠ 0) :
    B * (∑ b ∈ Finset.Icc 1 (q / 2),
      (q.choose b : ℝ) * deltaMomentEnvelope B b * deltaMomentEnvelope B (q - b)) ≤
        deltaMomentEnvelope B q := by
  have hs := Finset.sum_le_sum (s := Finset.Icc 1 (q / 2))
    (fun b hb => deltaMomentEnvelope_binomial_term hB
      (Finset.mem_Icc.mp hb).1 (Finset.mem_Icc.mp hb).2)
  rw [← Finset.mul_sum] at hs
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hs
  have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  apply (mul_le_mul_iff_right₀ hqR).mp
  calc
    _ = B * (q : ℝ) * (∑ b ∈ Finset.Icc 1 (q / 2),
        (q.choose b : ℝ) * deltaMomentEnvelope B b * deltaMomentEnvelope B (q - b)) := by
      ring
    _ ≤ (q / 2 : ℕ) * deltaMomentEnvelope B q := hs
    _ ≤ (q : ℝ) * deltaMomentEnvelope B q := by
      have hhalf : ((q / 2 : ℕ) : ℝ) ≤ q := by exact_mod_cast Nat.div_le_self q 2
      exact mul_le_mul_of_nonneg_right hhalf (deltaMomentEnvelope_nonneg hB q)

/-- A convenient bound before taking a positive-order root. -/
theorem mul_deltaMomentEnvelope_le_pow {A B : ℝ} (hB : 0 ≤ B) (hAB : A ≤ B)
    {q : ℕ} (hq : q ≠ 0) :
    A * deltaMomentEnvelope B q ≤ ((q : ℝ) ^ 2 * B) ^ q := by
  have hfact : (q.factorial : ℝ) ≤ (q : ℝ) ^ q := by
    exact_mod_cast Nat.factorial_le_pow q
  calc
    A * deltaMomentEnvelope B q ≤ B * deltaMomentEnvelope B q :=
      mul_le_mul_of_nonneg_right hAB (deltaMomentEnvelope_nonneg hB q)
    _ = (q.factorial : ℝ) ^ 2 * B ^ q := by
      unfold deltaMomentEnvelope
      rw [mul_left_comm B, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hq)]
    _ ≤ ((q : ℝ) ^ q) ^ 2 * B ^ q :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hfact 2)
        (pow_nonneg hB q)
    _ = ((q : ℝ) ^ 2 * B) ^ q := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm q 2]

end Erdos587
