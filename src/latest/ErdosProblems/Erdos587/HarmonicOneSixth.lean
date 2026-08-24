import ErdosProblems.Erdos587.OneSixthPair

/-! Uniform one-sixth estimates for every nonzero harmonic. -/

open scoped BigOperators

namespace Erdos587

lemma phaseIncrement_const_mul (c : ℝ) (f : ℕ → ℝ) (n : ℕ) :
    phaseIncrement (fun n => c * f n) n = c * phaseIncrement f n := by
  unfold phaseIncrement
  ring

lemma phaseIncrement_twice_const_mul (c : ℝ) (f : ℕ → ℝ) (n : ℕ) :
    phaseIncrement (phaseIncrement (fun n => c * f n)) n = c * phaseIncrement (phaseIncrement f) n := by
  have heq : phaseIncrement (fun n => c * f n) = fun n => c * phaseIncrement f n :=
    funext (phaseIncrement_const_mul c f)
  rw [heq, phaseIncrement_const_mul]

lemma phaseIncrement_thrice_const_mul (c : ℝ) (f : ℕ → ℝ) (n : ℕ) :
    phaseIncrement (phaseIncrement (phaseIncrement (fun n => c * f n))) n =
      c * phaseIncrement (phaseIncrement (phaseIncrement f)) n := by
  have heq : phaseIncrement (phaseIncrement (fun n => c * f n)) =
      fun n => c * phaseIncrement (phaseIncrement f) n :=
    funext (phaseIncrement_twice_const_mul c f)
  rw [heq, phaseIncrement_const_mul]

theorem norm_phase_real_harmonic_sum_le (f : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {F C : ℝ} (hNF : (N : ℝ) ≤ F) (hC : 1 ≤ C)
    (hsecondLo : ∀ n, n + 1 < N → -(C * (F / (N : ℝ) ^ 2)) ≤ phaseIncrement (phaseIncrement f) n)
    (hsecondHi : ∀ n, n + 1 < N → phaseIncrement (phaseIncrement f) n ≤ -(F / (N : ℝ) ^ 2))
    (hthirdLo : ∀ n, n + 2 < N → F / (N : ℝ) ^ 3 ≤ phaseIncrement (phaseIncrement (phaseIncrement f)) n)
    (hthirdHi : ∀ n, n + 2 < N → phaseIncrement (phaseIncrement (phaseIncrement f)) n ≤ C * (F / (N : ℝ) ^ 3))
    {r : ℝ} (hr : 1 ≤ r) :
    ‖∑ n ∈ Finset.range N, phase (r * f n)‖ ≤
      (100 * C * F ^ (1 / 6 : ℝ) * Real.sqrt N) * r ^ (1 / 6 : ℝ) := by
  have hrpos : 0 < r := by linarith
  have hFpos : 0 < F := (show (0 : ℝ) < N by exact_mod_cast hN).trans_le hNF
  have hNFr : (N : ℝ) ≤ r * F := hNF.trans (le_mul_of_one_le_left hFpos.le hr)
  have h₂lo (n : ℕ) (hn : n + 1 < N) :
      -(C * (r * F / (N : ℝ) ^ 2)) ≤ phaseIncrement (phaseIncrement (fun n => r * f n)) n := by
    rw [phaseIncrement_twice_const_mul]
    calc
      _ = r * (-(C * (F / (N : ℝ) ^ 2))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsecondLo n hn) hrpos.le
  have h₂hi (n : ℕ) (hn : n + 1 < N) :
      phaseIncrement (phaseIncrement (fun n => r * f n)) n ≤ -(r * F / (N : ℝ) ^ 2) := by
    rw [phaseIncrement_twice_const_mul]
    calc
      _ ≤ r * (-(F / (N : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left (hsecondHi n hn) hrpos.le
      _ = _ := by ring
  have h₃lo (n : ℕ) (hn : n + 2 < N) :
      r * F / (N : ℝ) ^ 3 ≤ phaseIncrement (phaseIncrement (phaseIncrement (fun n => r * f n))) n := by
    rw [phaseIncrement_thrice_const_mul]
    calc
      _ = r * (F / (N : ℝ) ^ 3) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hthirdLo n hn) hrpos.le
  have h₃hi (n : ℕ) (hn : n + 2 < N) :
      phaseIncrement (phaseIncrement (phaseIncrement (fun n => r * f n))) n ≤ C * (r * F / (N : ℝ) ^ 3) := by
    rw [phaseIncrement_thrice_const_mul]
    calc
      _ ≤ r * (C * (F / (N : ℝ) ^ 3)) := mul_le_mul_of_nonneg_left (hthirdHi n hn) hrpos.le
      _ = _ := by ring
  have hh := norm_phase_sum_le_one_sixth_pair (fun n => r * f n) hN hNFr hC h₂lo h₂hi h₃lo h₃hi
  apply hh.trans_eq
  rw [Real.mul_rpow hrpos.le hFpos.le]
  ring

theorem norm_phase_integer_harmonic_sum_le (f : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    {F C : ℝ} (hNF : (N : ℝ) ≤ F) (hC : 1 ≤ C)
    (hsecondLo : ∀ n, n + 1 < N → -(C * (F / (N : ℝ) ^ 2)) ≤ phaseIncrement (phaseIncrement f) n)
    (hsecondHi : ∀ n, n + 1 < N → phaseIncrement (phaseIncrement f) n ≤ -(F / (N : ℝ) ^ 2))
    (hthirdLo : ∀ n, n + 2 < N → F / (N : ℝ) ^ 3 ≤ phaseIncrement (phaseIncrement (phaseIncrement f)) n)
    (hthirdHi : ∀ n, n + 2 < N → phaseIncrement (phaseIncrement (phaseIncrement f)) n ≤ C * (F / (N : ℝ) ^ 3))
    (m : ℤ) (hm : m ≠ 0) :
    ‖∑ n ∈ Finset.range N, phase ((m : ℝ) * f n)‖ ≤
      (100 * C * F ^ (1 / 6 : ℝ) * Real.sqrt N) * |(m : ℝ)| ^ (1 / 6 : ℝ) := by
  by_cases hmpos : 0 ≤ m
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show (1 : ℤ) ≤ m by omega)
    rw [abs_of_nonneg (by exact_mod_cast hmpos : (0 : ℝ) ≤ m)]
    exact norm_phase_real_harmonic_sum_le f hN hNF hC hsecondLo hsecondHi hthirdLo hthirdHi hm1
  · have hmR : (m : ℝ) < 0 := by exact_mod_cast (show m < 0 by omega)
    have hm1 : (1 : ℝ) ≤ -(m : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ -m by omega)
    have hh := norm_phase_real_harmonic_sum_le f hN hNF hC hsecondLo hsecondHi hthirdLo hthirdHi hm1
    have heq : (fun n => -(m : ℝ) * f n) = fun n => -((m : ℝ) * f n) := by
      funext n
      ring
    change ‖∑ n ∈ Finset.range N, phase ((fun n => -(m : ℝ) * f n) n)‖ ≤ _ at hh
    rw [heq, norm_phase_sum_neg] at hh
    simpa only [abs_of_neg hmR] using hh

end Erdos587
