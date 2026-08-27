import Arxiv.Arxiv2411_18291.PaperSizeParameters

/-! # Explicit parameters after adjoining decoders to multiplicity-16 generators -/

namespace Arxiv2411_18291

def absorberCoefficientCap (q r : ℕ) : ℕ := 17 * 2 ^ q * r.factorial

def absorberGeneratorMultiplicity (q r : ℕ) : ℕ := 16 + q.choose r

def absorberNormalizationFactor (q r : ℕ) : ℕ :=
  absorberGeneratorMultiplicity q r * (2 + 4 * r.factorial * (q + r).choose r)

theorem absorberCoefficientCap_pos (q r : ℕ) : 0 < absorberCoefficientCap q r := by
  unfold absorberCoefficientCap
  positivity

theorem absorberNormalizationFactor_pos (q r : ℕ) : 0 < absorberNormalizationFactor q r := by
  unfold absorberNormalizationFactor absorberGeneratorMultiplicity
  positivity

theorem absorberGeneratorMultiplicity_le_power (q r : ℕ) :
    absorberGeneratorMultiplicity q r ≤ 17 * 2 ^ q := by
  have hk := Nat.choose_le_two_pow q r
  have hp : 1 ≤ 2 ^ q := one_le_pow₀ (by decide)
  unfold absorberGeneratorMultiplicity
  omega

theorem decoder_normalization_factor_le {q r : ℕ} (hqr : r < q) :
    2 + 4 * r.factorial * (q + r).choose r ≤ 6 * r.factorial * 2 ^ (2 * q) := by
  have hJ : (q + r).choose r ≤ 2 ^ (2 * q) :=
    (Nat.choose_le_two_pow (q + r) r).trans
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  have hp : 1 ≤ r.factorial * 2 ^ (2 * q) :=
    one_le_mul_of_one_le_of_one_le (Nat.factorial_pos r) (one_le_pow₀ (by decide))
  have hh := Nat.mul_le_mul_left (4 * r.factorial) hJ
  nlinarith only [hp, hh]

theorem absorber_splitting_density_constant {q r : ℕ} (hr : 1 ≤ r) (hqr : r < q) :
    4 * absorberCoefficientCap q r * absorberNormalizationFactor q r ≤
      (4 * q) ^ (8 * q) := by
  have hq : 2 ≤ q := by omega
  have hA := Nat.mul_le_mul (absorberGeneratorMultiplicity_le_power q r)
    (decoder_normalization_factor_le hqr)
  have hco : 6936 ≤ (4 * q) ^ 5 := by
    have hh := Nat.pow_le_pow_left (by omega : 8 ≤ 4 * q) 5
    norm_num at hh
    omega
  have hpow : 2 ^ (4 * q) ≤ (4 * q) ^ (2 * q) := by
    calc
      _ = 4 ^ (2 * q) := by rw [show 4 * q = 2 * (2 * q) by omega, pow_mul]; norm_num
      _ ≤ _ := Nat.pow_le_pow_left (by omega) _
  have hfac : r.factorial ≤ (4 * q) ^ q :=
    (Nat.factorial_le hqr.le).trans ((Nat.factorial_le_pow q).trans
      (Nat.pow_le_pow_left (by omega) q))
  calc
    _ ≤ 4 * absorberCoefficientCap q r *
        ((17 * 2 ^ q) * (6 * r.factorial * 2 ^ (2 * q))) := Nat.mul_le_mul_left _ hA
    _ = 6936 * 2 ^ (4 * q) * r.factorial ^ 2 := by
      unfold absorberCoefficientCap
      rw [show 2 * q = q * 2 by omega, pow_mul,
        show 4 * q = q * 4 by omega, pow_mul]
      ring
    _ ≤ (4 * q) ^ 5 * (4 * q) ^ (2 * q) * ((4 * q) ^ q) ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul hco hpow) (Nat.pow_le_pow_left hfac 2)
    _ = (4 * q) ^ (5 + 2 * q + q * 2) := by rw [← pow_mul, ← pow_add, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem absorber_splitting_conflict_constant {q r : ℕ} (hr : 1 ≤ r) (hqr : r < q) :
    q.choose r * ((2 * absorberCoefficientCap q r) * absorberGeneratorMultiplicity q r) ≤
      (4 * q) ^ (8 * q) := by
  have hq : 2 ≤ q := by omega
  have hK := Nat.choose_le_two_pow q r
  have hM := absorberGeneratorMultiplicity_le_power q r
  have hco : 578 ≤ (4 * q) ^ 4 := by
    have hh := Nat.pow_le_pow_left (by omega : 8 ≤ 4 * q) 4
    norm_num at hh
    omega
  have hpow : 2 ^ (3 * q) ≤ (4 * q) ^ q := by
    calc
      _ = 8 ^ q := by rw [pow_mul]; norm_num
      _ ≤ _ := Nat.pow_le_pow_left (by omega) _
  have hfac : r.factorial ≤ (4 * q) ^ q :=
    (Nat.factorial_le hqr.le).trans ((Nat.factorial_le_pow q).trans
      (Nat.pow_le_pow_left (by omega) q))
  calc
    _ ≤ 2 ^ q * ((2 * absorberCoefficientCap q r) * (17 * 2 ^ q)) :=
      Nat.mul_le_mul hK (Nat.mul_le_mul_left _ hM)
    _ = 578 * 2 ^ (3 * q) * r.factorial := by
      unfold absorberCoefficientCap
      rw [show 3 * q = q * 3 by omega, pow_mul]
      ring
    _ ≤ (4 * q) ^ 4 * (4 * q) ^ q * (4 * q) ^ q :=
      Nat.mul_le_mul (Nat.mul_le_mul hco hpow) hfac
    _ = (4 * q) ^ (4 + q + q) := by rw [← pow_add, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem paper_exchange_graph_bound {q r : ℕ} (hr : 1 ≤ r) (hqr : r < q) :
    3 * (2 * q) ^ r * (q.choose r) ^ 2 ≤ (4 * q) ^ (2 * q) := by
  have hq : 2 ≤ q := by omega
  have hk : (q.choose r) ^ 2 ≤ (4 * q) ^ q := by
    calc
      _ ≤ (2 ^ q) ^ 2 := Nat.pow_le_pow_left (Nat.choose_le_two_pow q r) 2
      _ = 4 ^ q := by rw [← pow_mul, Nat.mul_comm q 2, pow_mul]; norm_num
      _ ≤ _ := Nat.pow_le_pow_left (by omega) q
  calc
    _ ≤ (4 * q) ^ 1 * (4 * q) ^ r * (4 * q) ^ q :=
      Nat.mul_le_mul (Nat.mul_le_mul (by simp only [pow_one]; omega)
        (Nat.pow_le_pow_left (by omega) r)) hk
    _ = (4 * q) ^ (1 + r + q) := by rw [← pow_add, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

end Arxiv2411_18291
