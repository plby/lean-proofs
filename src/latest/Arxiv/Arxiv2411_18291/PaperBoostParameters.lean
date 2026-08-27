import Arxiv.Arxiv2411_18291.FractionalBoostMassNumerics

/-! # Numerical margins at the paper's complement bound -/

namespace Arxiv2411_18291

theorem choose_succ_le_pow_two (n k : ℕ) : (n + 1).choose k ≤ 2 ^ n := by
  induction n generalizing k with
  | zero => simpa using Nat.choose_le_pow 1 k
  | succ n ih =>
    cases k with
    | zero =>
      simp only [Nat.choose_zero_right]
      exact Nat.succ_le_of_lt (by positivity)
    | succ k =>
      rw [Nat.choose_succ_succ, pow_succ]
      calc
        _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add (ih k) (ih (k + 1))
        _ = _ := by ring

theorem paper_boost_cost_nat (q r : ℕ) (hqr : r < q) :
    4 * (2 ^ r * q.choose r) * (2 * q.choose r) ≤ 2 ^ (3 * q) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  have hc := choose_succ_le_pow_two s r
  have hp : 2 ^ r ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) (by omega)
  calc
    _ ≤ 4 * (2 ^ s * 2 ^ s) * (2 * 2 ^ s) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 4 (Nat.mul_le_mul hp hc))
        (Nat.mul_le_mul_left 2 hc)
    _ = _ := by
      rw [show 3 * s.succ = s + s + s + 3 by omega]
      simp only [pow_add]
      norm_num
      ring

/-- `2^(-3q)`, written using the inverse of a natural power. -/
noncomputable def boostComplementBound (q : ℕ) : ℝ := ((2 : ℝ) ^ (3 * q))⁻¹

theorem paper_boost_parameters (q r : ℕ) (hqr : r < q) :
    let θ := boostComplementBound q
    let ε := 2 * (q.choose r : ℝ) * θ
    0 < θ ∧ 0 < ε ∧ ε ≤ 1 / 2 ∧ (2 : ℝ) ^ r * q.choose r * ε ≤ 1 / 2 ∧
      (q.choose r : ℝ) * θ < ε ∧ ((q + r).choose r : ℝ) * θ < 1 / 2 := by
  let θ := boostComplementBound q
  let ε := 2 * (q.choose r : ℝ) * θ
  have hden : (0 : ℝ) < (2 : ℝ) ^ (3 * q) := by positivity
  have hθ : 0 < θ := by dsimp only [θ, boostComplementBound]; positivity
  have hk : (0 : ℝ) < q.choose r := by exact_mod_cast Nat.choose_pos hqr.le
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hK : (1 : ℝ) ≤ (2 : ℝ) ^ r * q.choose r := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.mul_pos (by positivity : 0 < 2 ^ r)
      (Nat.choose_pos hqr.le))
  have hnum : 4 * ((2 : ℝ) ^ r * q.choose r) * (2 * q.choose r) ≤ (2 : ℝ) ^ (3 * q) := by
    exact_mod_cast paper_boost_cost_nat q r hqr
  have hcost : (2 : ℝ) ^ r * q.choose r * ε ≤ 1 / 2 := by
    have hh : 4 * ((2 : ℝ) ^ r * q.choose r) * ε ≤ 1 := by
      calc
        _ = (4 * ((2 : ℝ) ^ r * q.choose r) * (2 * q.choose r)) /
            (2 : ℝ) ^ (3 * q) := by dsimp only [ε, θ, boostComplementBound]; ring
        _ ≤ _ := (div_le_one hden).mpr hnum
    linarith only [hh]
  have hhalf : ε ≤ 1 / 2 := by
    have hh := mul_le_mul_of_nonneg_right hK hε.le
    linarith only [hh, hcost]
  have hsmall_nat : 2 * (q + r).choose r < 2 ^ (3 * q) := by
    apply lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.choose_le_two_pow (q + r) r))
    rw [mul_comm, ← pow_succ]
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  have hsmall : 2 * ((q + r).choose r : ℝ) < (2 : ℝ) ^ (3 * q) := by
    exact_mod_cast hsmall_nat
  have hdecode : ((q + r).choose r : ℝ) * θ < 1 / 2 := by
    have hh : 2 * (((q + r).choose r : ℝ) * θ) < 1 := by
      calc
        _ = (2 * ((q + r).choose r : ℝ)) / (2 : ℝ) ^ (3 * q) := by
          dsimp only [θ, boostComplementBound]
          ring
        _ < _ := (div_lt_one hden).mpr hsmall
    linarith only [hh]
  refine ⟨hθ, hε, hhalf, hcost, ?_, hdecode⟩
  change (q.choose r : ℝ) * θ < 2 * (q.choose r : ℝ) * θ
  nlinarith only [mul_pos hk hθ]

end Arxiv2411_18291
