import ErdosProblems.Erdos587.HooleyApproximationCount
import ErdosProblems.Erdos587.HooleyDivisorCounting

/-! # Divisor fibers for approximants to reciprocal quadratic coefficients -/

open scoped BigOperators

namespace Erdos587

def deltaReciprocalApproximantError (c : ℕ) (A : ℕ → ℤ) (x : DeltaApproximant) : ℤ :=
  (x.denominator : ℤ) * A x.index - (c * x.index : ℕ) * x.numerator

lemma delta_reciprocal_approximant_eq_of_encoding {c : ℕ} (hc : 0 < c)
    (A : ℕ → ℤ) {x y : DeltaApproximant} (hx : 0 < x.index)
    (hindex : x.index = y.index) (hden : x.denominator = y.denominator)
    (herr : deltaReciprocalApproximantError c A x = deltaReciprocalApproximantError c A y) :
    x = y := by
  have hd : ((c * x.index : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hc hx).ne'
  have hnum : x.numerator = y.numerator := by
    dsimp only [deltaReciprocalApproximantError] at herr
    rw [← hindex, ← hden] at herr
    apply mul_left_cancel₀ hd
    linarith
  exact DeltaApproximant.ext hindex hden hnum

lemma delta_reciprocal_approximant_encoding_dvd {c q : ℕ} {a v : ℤ}
    (A : ℕ → ℤ) (x : DeltaApproximant)
    (hrel : ((c * x.index : ℕ) : ℤ) ∣ (q : ℤ) * A x.index - a * v) :
    c * x.index ∣ ((x.denominator : ℤ) * a * v -
      q * deltaReciprocalApproximantError c A x).natAbs := by
  apply Int.natCast_dvd.mp
  have h := reciprocal_delta_encoding_dvd (b := (x.denominator : ℤ)) (h := x.numerator) hrel
  convert h using 1
  dsimp only [deltaReciprocalApproximantError]
  ring

theorem delta_reciprocal_approximant_card_le_delta_sum {c q b : ℕ} {a v : ℤ}
    (hc : 0 < c) (A : ℕ → ℤ) {R : ℝ} (hR : 0 < R)
    (S : Finset DeltaApproximant) (E : Finset ℤ)
    (hlow : ∀ x ∈ S, R < x.index) (hupp : ∀ x ∈ S, (x.index : ℝ) ≤ 2 * R)
    (hden : ∀ x ∈ S, x.denominator = b)
    (hrel : ∀ x ∈ S, ((c * x.index : ℕ) : ℤ) ∣ (q : ℤ) * A x.index - a * v)
    (hzero : ∀ t ∈ E, (b : ℤ) * a * v - q * t ≠ 0)
    (herror : ∀ x ∈ S, deltaReciprocalApproximantError c A x ∈ E) :
    S.card ≤ ∑ t ∈ E, hooleyDelta ((b : ℤ) * a * v - q * t).natAbs := by
  classical
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hfiber (t : ℤ) (ht : t ∈ E) :
      (S.filter (fun x => deltaReciprocalApproximantError c A x = t)).card ≤
        hooleyDelta ((b : ℤ) * a * v - q * t).natAbs := by
    apply card_le_hooleyDelta_of_divisor_encoding
      (S.filter (fun x => deltaReciprocalApproximantError c A x = t))
      (fun x => c * x.index) (Int.natAbs_ne_zero.mpr (hzero t ht)) (mul_pos hcR hR)
    · intro x hx
      have h := delta_reciprocal_approximant_encoding_dvd A x (hrel x (Finset.mem_filter.mp hx).1)
      simpa only [hden x (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2] using h
    · intro x hx
      have h := mul_lt_mul_of_pos_left (hlow x (Finset.mem_filter.mp hx).1) hcR
      exact_mod_cast h
    · intro x hx
      have h := mul_le_mul_of_nonneg_left (hupp x (Finset.mem_filter.mp hx).1) hcR.le
      push_cast
      nlinarith
    · intro x hx y hy heq
      have hxS := (Finset.mem_filter.mp hx).1
      have hyS := (Finset.mem_filter.mp hy).1
      have hxpos : 0 < x.index := by exact_mod_cast hR.trans (hlow x hxS)
      have hxy : x.index = y.index := Nat.eq_of_mul_eq_mul_left hc heq
      apply delta_reciprocal_approximant_eq_of_encoding hc A hxpos hxy
        ((hden x hxS).trans (hden y hyS).symm)
      exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
  calc
    _ = ∑ t ∈ E, (S.filter (fun x => deltaReciprocalApproximantError c A x = t)).card :=
      Finset.card_eq_sum_card_fiberwise herror
    _ ≤ _ := Finset.sum_le_sum hfiber

end Erdos587
