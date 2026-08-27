import ErdosProblems.Erdos587.HooleyMomentEnvelope

/-!
# An envelope that absorbs smoothing losses

Multiplying the previous envelope by one further factorial absorbs an
extra factor `2^b` in every mixed-moment term. This permits unit-window
smoothing in the prime average, at the cost of one further log-log power.
-/

open scoped BigOperators

namespace Erdos587

lemma two_pow_le_central_choose (b : ℕ) : 2 ^ b ≤ (2 * b).choose b := by
  induction b with
  | zero => norm_num
  | succ b ih =>
    have hsym : (2 * b + 1).choose (b + 1) = (2 * b + 1).choose b := by
      have h := Nat.choose_symm (show b ≤ 2 * b + 1 by omega)
      simpa only [show 2 * b + 1 - b = b + 1 by omega] using h
    have hrec : (2 * (b + 1)).choose (b + 1) = 2 * (2 * b + 1).choose b := by
      rw [show 2 * (b + 1) = (2 * b + 1) + 1 by omega, Nat.choose_succ_succ, hsym]
      omega
    calc
      2 ^ (b + 1) = 2 * 2 ^ b := pow_succ' 2 b
      _ ≤ 2 * (2 * b).choose b := Nat.mul_le_mul_left 2 ih
      _ ≤ 2 * (2 * b + 1).choose b := Nat.mul_le_mul_left 2 (Nat.choose_le_succ _ _)
      _ = _ := hrec.symm

lemma two_pow_le_choose_of_le_half {q b : ℕ} (hbq : b ≤ q / 2) :
    2 ^ b ≤ q.choose b :=
  (two_pow_le_central_choose b).trans (Nat.choose_le_choose b (by omega))

def deltaSmoothMomentEnvelope (B : ℝ) (q : ℕ) : ℝ :=
  (q.factorial : ℝ) * deltaMomentEnvelope B q

lemma deltaSmoothMomentEnvelope_nonneg {B : ℝ} (hB : 0 ≤ B) (q : ℕ) :
    0 ≤ deltaSmoothMomentEnvelope B q :=
  mul_nonneg (Nat.cast_nonneg _) (deltaMomentEnvelope_nonneg hB q)

@[simp] lemma deltaSmoothMomentEnvelope_one (B : ℝ) :
    deltaSmoothMomentEnvelope B 1 = 1 := by simp [deltaSmoothMomentEnvelope]

@[simp] lemma deltaSmoothMomentEnvelope_two (B : ℝ) :
    deltaSmoothMomentEnvelope B 2 = 8 * B := by
  norm_num [deltaSmoothMomentEnvelope]
  ring

lemma deltaSmoothMomentEnvelope_binomial_term {B : ℝ} (hB : 0 ≤ B)
    {q b : ℕ} (hb : 1 ≤ b) (hbq : b ≤ q / 2) :
    B * (q : ℝ) * (2 ^ b * (q.choose b : ℝ) * deltaSmoothMomentEnvelope B b *
      deltaSmoothMomentEnvelope B (q - b)) ≤ deltaSmoothMomentEnvelope B q := by
  have hble : b ≤ q := hbq.trans (Nat.div_le_self q 2)
  have hfact : (q.choose b : ℝ) * b.factorial * (q - b).factorial = q.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hble
  have htwo : (2 : ℝ) ^ b ≤ q.choose b := by
    exact_mod_cast two_pow_le_choose_of_le_half hbq
  have hfactor : (2 : ℝ) ^ b * b.factorial * (q - b).factorial ≤ q.factorial := by
    calc
      _ ≤ (q.choose b : ℝ) * b.factorial * (q - b).factorial := by gcongr
      _ = _ := hfact
  have he := deltaMomentEnvelope_binomial_term hB hb hbq
  calc
    _ = (B * (q : ℝ) * ((q.choose b : ℝ) * deltaMomentEnvelope B b *
        deltaMomentEnvelope B (q - b))) *
          (2 ^ b * (b.factorial : ℝ) * (q - b).factorial) := by
      unfold deltaSmoothMomentEnvelope
      ring
    _ ≤ deltaMomentEnvelope B q * q.factorial :=
      mul_le_mul he hfactor (by positivity) (deltaMomentEnvelope_nonneg hB q)
    _ = deltaSmoothMomentEnvelope B q := mul_comm _ _

theorem deltaSmoothMomentEnvelope_convolution {B : ℝ} (hB : 0 ≤ B)
    {q : ℕ} (hq : q ≠ 0) :
    B * (∑ b ∈ Finset.Icc 1 (q / 2),
      2 ^ b * (q.choose b : ℝ) * deltaSmoothMomentEnvelope B b *
        deltaSmoothMomentEnvelope B (q - b)) ≤ deltaSmoothMomentEnvelope B q := by
  have hs := Finset.sum_le_sum (s := Finset.Icc 1 (q / 2))
    (fun b hb => deltaSmoothMomentEnvelope_binomial_term hB
      (Finset.mem_Icc.mp hb).1 (Finset.mem_Icc.mp hb).2)
  rw [← Finset.mul_sum] at hs
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hs
  have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  apply (mul_le_mul_iff_right₀ hqR).mp
  calc
    _ = B * (q : ℝ) * (∑ b ∈ Finset.Icc 1 (q / 2),
        2 ^ b * (q.choose b : ℝ) * deltaSmoothMomentEnvelope B b *
          deltaSmoothMomentEnvelope B (q - b)) := by ring
    _ ≤ (q / 2 : ℕ) * deltaSmoothMomentEnvelope B q := hs
    _ ≤ (q : ℝ) * deltaSmoothMomentEnvelope B q := by
      have hhalf : ((q / 2 : ℕ) : ℝ) ≤ q := by exact_mod_cast Nat.div_le_self q 2
      exact mul_le_mul_of_nonneg_right hhalf (deltaSmoothMomentEnvelope_nonneg hB q)

theorem mul_deltaSmoothMomentEnvelope_le_pow {A B : ℝ} (hB : 0 ≤ B) (hAB : A ≤ B)
    {q : ℕ} (hq : q ≠ 0) :
    A * deltaSmoothMomentEnvelope B q ≤ ((q : ℝ) ^ 3 * B) ^ q := by
  have hfact : (q.factorial : ℝ) ≤ (q : ℝ) ^ q := by
    exact_mod_cast Nat.factorial_le_pow q
  calc
    _ = (q.factorial : ℝ) * (A * deltaMomentEnvelope B q) := by
      unfold deltaSmoothMomentEnvelope
      ring
    _ ≤ (q.factorial : ℝ) * ((q : ℝ) ^ 2 * B) ^ q :=
      mul_le_mul_of_nonneg_left (mul_deltaMomentEnvelope_le_pow hB hAB hq) (by positivity)
    _ ≤ (q : ℝ) ^ q * ((q : ℝ) ^ 2 * B) ^ q :=
      mul_le_mul_of_nonneg_right hfact (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; ring

end Erdos587
