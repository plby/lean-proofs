import ErdosProblems.Erdos587.HooleyDelta

/-!
# Exact divisor-counting identities for the log-log proof

The centered quadratic estimate excludes the zero error before summing
gcd-divisor factors. The identity below therefore has no additive
`τ(q)` term. The reciprocal encoding separately excludes a zero encoded
integer before invoking a Delta bound.
-/

open scoped BigOperators

namespace Erdos587

lemma delta_divisors_gcd_eq_filter {q : ℕ} (hq : q ≠ 0) (t : ℕ) :
    (q.gcd t).divisors = q.divisors.filter (fun d => d ∣ t) := by
  have hg : q.gcd t ≠ 0 := Nat.gcd_ne_zero_left hq
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
  tauto

/-- Exact double-counting over positive errors. In particular, zero is
not present in the interval on the left. -/
theorem sum_Ioc_card_divisors_gcd {q : ℕ} (hq : q ≠ 0) (T : ℕ) :
    (∑ t ∈ Finset.Ioc 0 T, (q.gcd t).divisors.card) =
      ∑ d ∈ q.divisors, T / d := by
  classical
  calc
    (∑ t ∈ Finset.Ioc 0 T, (q.gcd t).divisors.card) =
        ∑ t ∈ Finset.Ioc 0 T, ∑ d ∈ q.divisors, if d ∣ t then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [delta_divisors_gcd_eq_filter hq t, Finset.card_eq_sum_ones,
        Finset.sum_filter]
    _ = ∑ d ∈ q.divisors, ∑ t ∈ Finset.Ioc 0 T, if d ∣ t then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ d ∈ q.divisors, T / d := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      simpa using Nat.Ioc_filter_dvd_card_eq_div T d

/-- The gcd factor costs only a reciprocal-divisor sum. -/
theorem sum_Ioc_card_divisors_gcd_le {q : ℕ} (hq : q ≠ 0) (T : ℕ) :
    (∑ t ∈ Finset.Ioc 0 T, ((q.gcd t).divisors.card : ℝ)) ≤
      (T : ℝ) * ∑ d ∈ q.divisors, 1 / (d : ℝ) := by
  have hsum : (∑ t ∈ Finset.Ioc 0 T, ((q.gcd t).divisors.card : ℝ)) =
      ∑ d ∈ q.divisors, ((T / d : ℕ) : ℝ) := by
    exact_mod_cast sum_Ioc_card_divisors_gcd hq T
  rw [hsum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  rw [mul_one_div]
  exact Nat.cast_div_le

/-- Algebraic divisor encoding after a rational approximation to an
inverse coefficient. It does not require choosing an inverse operation. -/
lemma reciprocal_delta_encoding_dvd {D q A a v b h : ℤ}
    (hrel : D ∣ q * A - a * v) :
    D ∣ b * a * v - q * (b * A - h * D) := by
  have h₁ : D ∣ b * (q * A - a * v) := dvd_mul_of_dvd_right hrel b
  have h₂ : D ∣ (q * h) * D := dvd_mul_of_dvd_right (dvd_refl D) (q * h)
  rw [show b * a * v - q * (b * A - h * D) =
    (q * h) * D - b * (q * A - a * v) by ring]
  exact dvd_sub h₂ h₁

/-- The reciprocal encoding never asks for the divisors of zero. -/
lemma reciprocal_delta_encoding_ne_zero {a b v q K : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hbK : b ≤ K)
    (hcop : q.Coprime v) (hq : a * K < q) (t : ℤ) :
    (a : ℤ) * b * v - q * t ≠ 0 := by
  intro hzero
  have hdivZ : (q : ℤ) ∣ (a : ℤ) * b * v :=
    ⟨t, sub_eq_zero.mp hzero⟩
  have hdiv : q ∣ a * b * v := by exact_mod_cast hdivZ
  have hab : q ∣ a * b := hcop.dvd_of_dvd_mul_right hdiv
  have hle : q ≤ a * b := Nat.le_of_dvd (Nat.mul_pos ha hb) hab
  exact (not_le_of_gt hq) (hle.trans (Nat.mul_le_mul_left a hbK))

/-- A Dirichlet approximant whose denominator is below the exact reduced
denominator cannot have zero error. This is the zero exclusion required
before applying `sum_Ioc_card_divisors_gcd_le`. -/
lemma centered_delta_encoding_ne_zero {q a m b L : ℕ}
    (hq : 0 < q) (hcop : q.Coprime a) (hb : 0 < b) (hbL : b ≤ L)
    (hden : L < q / q.gcd m) (h : ℤ) :
    (a : ℤ) * m * b - q * h ≠ 0 := by
  intro hzero
  have hdivZ : (q : ℤ) ∣ (a : ℤ) * m * b :=
    ⟨h, sub_eq_zero.mp hzero⟩
  have hdiv : q ∣ a * m * b := by exact_mod_cast hdivZ
  have hmb : q ∣ m * b :=
    hcop.dvd_of_dvd_mul_left (by simpa only [mul_assoc] using hdiv)
  have hbdiv : q / q.gcd m ∣ b := by
    rw [Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left q m)
      (Nat.gcd_pos_of_pos_left m hq)]
    exact Nat.dvd_gcd_mul_iff_dvd_mul.mpr hmb
  have hle : q / q.gcd m ≤ b := Nat.le_of_dvd hb hbdiv
  exact (not_le_of_gt hden) (hle.trans hbL)

end Erdos587
