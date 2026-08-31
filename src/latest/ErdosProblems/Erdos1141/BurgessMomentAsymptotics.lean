import ErdosProblems.Erdos1141.BurgessCompositeMoment
import ErdosProblems.Erdos1141.BurgessSubpower

/-!
# Absorbing composite moment losses into an arbitrarily small power
-/

namespace Pollack17.Burgess

open Filter
open scoped BigOperators

theorem composite_moment_second_term (C w V n : ℕ) (hn : 0 < n) (q : ℝ) :
    (C : ℝ) ^ w * q * n * V * (2 * V * (2 : ℝ) ^ w) ^ (n - 1) =
      ((n : ℝ) * 2 ^ (n - 1)) * ((C * 2 ^ (n - 1) : ℕ) : ℝ) ^ w * q * (V : ℝ) ^ n := by
  have hV : (V : ℝ) * (V : ℝ) ^ (n - 1) = (V : ℝ) ^ n := by
    rw [← pow_succ']
    congr 1
    omega
  have htwo : ((2 : ℝ) ^ w) ^ (n - 1) = ((2 : ℝ) ^ (n - 1)) ^ w := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_pow, htwo]
  calc
    _ = ((n : ℝ) * 2 ^ (n - 1)) *
        ((C : ℝ) ^ w * (2 ^ (n - 1)) ^ w) * q * ((V : ℝ) * (V : ℝ) ^ (n - 1)) := by ring
    _ = _ := by rw [hV]

theorem eventually_productChar_moment_le (r : ℕ) (hr : 0 < r)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q : ℕ, ∀ (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime), Q ≤ primeModulus s →
      ∀ V : ℕ, letI : NeZero (primeModulus s) := ⟨(primeModulus_pos s hs).ne'⟩
      (∑ x : ZMod (primeModulus s), naturalShiftSum (productChar s hs) V x ^ (2 * r)) ≤
        (primeModulus s : ℝ) ^ δ *
          ((primeModulus s : ℝ) * (V : ℝ) ^ r +
            Real.sqrt (primeModulus s) * (V : ℝ) ^ (2 * r)) := by
  let n := 2 * r
  let C := Stepanov.simpleRootConstant n
  let b := C * 2 ^ (n - 1)
  have hb : 1 ≤ b := Nat.mul_pos (simpleRootConstant_one_le n) (by positivity)
  have hfirst := eventually_const_mul_pow_primeFactors_le ((r : ℝ) ^ (2 * r)) 1 (by omega) hδ
  have hsecond := eventually_const_mul_pow_primeFactors_le ((n : ℝ) * 2 ^ (n - 1)) b hb hδ
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp (hfirst.and hsecond)
  refine ⟨Q, fun s hs hq V => ?_⟩
  have : NeZero (primeModulus s) := ⟨(primeModulus_pos s hs).ne'⟩
  have hc₁ : (r : ℝ) ^ (2 * r) ≤ (primeModulus s : ℝ) ^ δ := by
    simpa using (hQ (primeModulus s) hq).1
  have hc₂ : ((n : ℝ) * 2 ^ (n - 1)) * (b : ℝ) ^ s.card ≤
      (primeModulus s : ℝ) ^ δ := by
    simpa only [primeModulus_primeFactors s hs] using (hQ (primeModulus s) hq).2
  have hm := productChar_even_moment_le s hs V r
  rw [primeModulus_card_divisors s hs, Nat.cast_pow, Nat.cast_ofNat] at hm
  have heq := composite_moment_second_term C s.card V n (by dsimp [n]; omega)
    (Real.sqrt (primeModulus s))
  change _ = ((n : ℝ) * 2 ^ (n - 1)) * (b : ℝ) ^ s.card *
    Real.sqrt (primeModulus s) * (V : ℝ) ^ n at heq
  rw [heq] at hm
  have h₁ := mul_le_mul_of_nonneg_right hc₁
    (mul_nonneg (Nat.cast_nonneg (primeModulus s)) (pow_nonneg (Nat.cast_nonneg V) r))
  have h₂ := mul_le_mul_of_nonneg_right hc₂
    (mul_nonneg (Real.sqrt_nonneg (primeModulus s)) (pow_nonneg (Nat.cast_nonneg V) n))
  refine hm.trans ?_
  nlinarith only [h₁, h₂]

end Pollack17.Burgess
