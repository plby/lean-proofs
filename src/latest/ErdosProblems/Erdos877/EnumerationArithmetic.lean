import ErdosProblems.Erdos877.EnumerationFingerprints

namespace Erdos877.Enumeration

/-- The reciprocal of the fixed container parameter, recorded integrally. -/
def fingerprintScale : ℕ := 72 * fingerprintR * fingerprintK

theorem fingerprintScale_pos : 0 < fingerprintScale := by
  norm_num [fingerprintScale, fingerprintR, fingerprintK]

theorem fingerprintP_eq_inv_scale :
    fingerprintP = ((fingerprintScale : ℕ) : ℝ)⁻¹ := by
  simp only [fingerprintP, fingerprintScale, one_div]
  norm_num

/-- Clearing the fixed positive denominator in the container edge bound. -/
theorem edge_bound_to_nat {e m : ℕ}
    (h : fingerprintP ^ 2 * (e : ℝ) ≤ 6 * (m : ℝ)) :
    e ≤ 6 * m * fingerprintScale ^ 2 := by
  have hs : 0 < ((fingerprintScale : ℕ) : ℝ) := by
    exact_mod_cast fingerprintScale_pos
  have hdiv :
      (e : ℝ) / ((fingerprintScale : ℕ) : ℝ) ^ 2 ≤ 6 * (m : ℝ) := by
    rw [fingerprintP_eq_inv_scale] at h
    convert h using 1
    all_goals field_simp
  have hmul := (div_le_iff₀ (sq_pos_of_pos hs)).mp hdiv
  exact_mod_cast hmul

/-- The integral coefficient controlling the supersaturation error. -/
def enumerationLinearConstant : ℕ := 12 * fingerprintScale ^ 2 + 3

theorem enumerationLinearConstant_pos : 0 < enumerationLinearConstant := by
  simp [enumerationLinearConstant]

theorem schur_linear_bound {e m n : ℕ}
    (hm : m ≤ n)
    (hedge : fingerprintP ^ 2 * (e : ℝ) ≤ 6 * (m : ℝ)) :
    2 * e + 3 * n ≤ enumerationLinearConstant * n := by
  have he : e ≤ 6 * m * fingerprintScale ^ 2 := edge_bound_to_nat hedge
  calc
    2 * e + 3 * n ≤ 2 * (6 * m * fingerprintScale ^ 2) + 3 * n := by omega
    _ ≤ 2 * (6 * n * fingerprintScale ^ 2) + 3 * n := by
      gcongr
    _ = enumerationLinearConstant * n := by
      simp only [enumerationLinearConstant]
      ring

theorem square_floor_sub_one_eventually (d K n : ℕ)
    (hd : 1 ≤ d) (hK : 1 ≤ K) (hn : 4 * K * d * d ≤ n) :
    K * n < (n / d - 1) * (n / d - 1) := by
  let t := n / d
  let q := t - 1
  have hnlt : n < d * (t + 1) := by
    calc
      n < n / d * d + d := Nat.lt_div_mul_add hd
      _ = d * (t + 1) := by simp [t]; ring
  have ht : 2 * K * d + 1 ≤ t := by
    nlinarith
  have hq : 2 * K * d ≤ q := by
    dsimp [q]
    omega
  have hq2 : 2 ≤ q := by nlinarith
  have htq : t = q + 1 := by
    dsimp [q]
    omega
  have hnq : n < d * (q + 2) := by
    rw [htq] at hnlt
    simpa [add_assoc] using hnlt
  have hleft : K * n < K * (d * (q + 2)) := by
    nlinarith
  have hright : K * (d * (q + 2)) ≤ q * q := by
    nlinarith
  simpa [q, t] using hleft.trans_le hright

theorem card_le_half_add_small_of_fixedDensity_failure {m n : ℕ}
    (h : ¬ (((2 : ℕ) ^ 34 + 1) * n ≤ (2 : ℕ) ^ 35 * m)) :
    m ≤ n / 2 + n / 2 ^ 32 := by
  norm_num [pow_succ] at h ⊢
  omega

end Erdos877.Enumeration
