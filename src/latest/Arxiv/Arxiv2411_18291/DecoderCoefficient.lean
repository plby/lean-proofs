import Arxiv.Arxiv2411_18291.LocalDecoder
import Mathlib.Tactic

/-! # Exact coefficients of the local decoder -/

open Finset
open scoped BigOperators

namespace Arxiv2411_18291

/-- The decoder coefficient when exactly `t` root vertices lie outside the clique. -/
def decoderCoefficient (q r t : ℕ) : ℤ :=
  ∑ i ∈ range (t + 1), (t.choose i : ℤ) * decoderWeight q r i

theorem decoderWeight_succ (q r i : ℕ) :
    decoderWeight (q + 1) (r + 1) (i + 1) = -(q + 1 : ℤ) * decoderWeight q r i := by
  simp only [decoderWeight, Nat.succ_descFactorial_succ, Nat.add_sub_add_right,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  ring

theorem decoderCoefficient_succ (q r t : ℕ) :
    decoderCoefficient (q + 1) (r + 1) (t + 1) =
      decoderCoefficient (q + 1) (r + 1) t - (q + 1 : ℤ) * decoderCoefficient q r t := by
  unfold decoderCoefficient
  rw [sum_choose_succ_mul (fun i _ => decoderWeight (q + 1) (r + 1) i) t]
  simp only [decoderWeight_succ]
  rw [sub_eq_add_neg, ← neg_mul, mul_sum]
  congr 1
  apply sum_congr rfl
  intro i _
  ring

theorem decoderCoefficient_eq (q r t : ℕ) (hqr : r < q) (htr : t ≤ r) :
    decoderCoefficient q r t =
      (-1 : ℤ) ^ t * ((q - r).ascFactorial t : ℤ) * ((r - t).factorial : ℤ) := by
  induction t generalizing q r with
  | zero => simp [decoderCoefficient, decoderWeight]
  | succ t ih =>
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    simp only [Nat.succ_eq_add_one] at *
    have htr' : t ≤ r := by omega
    have hqr' : r < q := by omega
    rw [decoderCoefficient_succ, ih (q + 1) (r + 1) (by omega) (by omega),
      ih q r hqr' htr']
    have hs : r + 1 - t = (r - t) + 1 := by omega
    simp only [Nat.add_sub_add_right, hs, Nat.factorial_succ, Nat.ascFactorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    have hsubq : ((q - r : ℕ) : ℤ) = (q : ℤ) - r := Nat.cast_sub hqr'.le
    have hsubr : ((r - t : ℕ) : ℤ) = (r : ℤ) - t := Nat.cast_sub htr'
    rw [hsubq, hsubr]
    ring

end Arxiv2411_18291
