/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Choice of geometric subsequence for the small-ball repulsion argument.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.LacunarySums

namespace Erdos521

theorem exists_lacunary_stride {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    ∃ L : ℕ, 0 < L ∧ (2 / 5 : ℝ) * x < x ^ L ∧ x ^ L ≤ 2 / 5 ∧
      (L : ℝ) * (1 - x) ≤ 3 := by
  have hex : ∃ L : ℕ, x ^ L ≤ 2 / 5 :=
    (exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 2 / 5) hx₁).imp (fun _ h ↦ h.le)
  let L := Nat.find hex
  have hspec : x ^ L ≤ 2 / 5 := Nat.find_spec hex
  have hL : 0 < L := by
    by_contra hh
    have hzero : L = 0 := by omega
    norm_num [hzero] at hspec
  have hprev : (2 / 5 : ℝ) < x ^ (L - 1) := by
    apply lt_of_not_ge
    exact Nat.find_min hex (by change L - 1 < L; omega)
  have hstride : (2 / 5 : ℝ) * x < x ^ L := by
    have h := mul_lt_mul_of_pos_right hprev hx₀
    rwa [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ L)] at h
  have hexp := pow_le_exp_nat_mul (u := -(1 - x)) hx₀.le (by linarith) (L - 1)
  have hlog := Real.log_lt_log (by norm_num : (0 : ℝ) < 2 / 5) (hprev.trans_le hexp)
  rw [Real.log_exp] at hlog
  have hlogBound : -(2 : ℝ) < Real.log (2 / 5) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5 / 2)
    rw [show (2 / 5 : ℝ) = (5 / 2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    linarith
  have hcast : (L : ℝ) = ((L - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ L)).symm
  refine ⟨L, hL, hstride, hspec, ?_⟩
  rw [hcast]
  nlinarith

theorem lacunary_stride_square_lower {x : ℝ} (hx : 9 / 10 ≤ x) (L : ℕ)
    (hstride : (2 / 5 : ℝ) * x < x ^ L) : (1 / 8 : ℝ) ≤ (x ^ L) ^ 2 := by
  have hq : (9 / 25 : ℝ) ≤ x ^ L := by linarith
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9 / 25) hq 2
  norm_num at hpow
  linarith

theorem geometric_subsequence_smallBall_dyadic (n L j : ℕ) (hL : 0 < L)
    (hdegree : L * (2 * j) ≤ n) {x z : ℝ} (hx₀ : 0 ≤ x ^ L)
    (hx₁ : x ^ L ≤ 2 / 5) (hscale : (1 / 8 : ℝ) ≤ (x ^ L) ^ 2) :
    sequenceLaw.real {ε | |powerSum ε (n + 1) x - z| ≤ (1 / 4) * (1 / 8 : ℝ) ^ j} ≤
      (1 / 4 : ℝ) ^ j := by
  have hpow : (1 / 8 : ℝ) ^ j ≤ (x ^ L) ^ (2 * j) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) hscale j
  have hδ : 2 * ((1 / 4) * (1 / 8 : ℝ) ^ j) < (x ^ L) ^ (2 * j) := by
    have hpos : 0 < (1 / 8 : ℝ) ^ j := by positivity
    linarith
  have h := geometric_subsequence_smallBall n L (2 * j) hL
    (fun i ↦ (Nat.mul_le_mul_left L (Nat.le_of_lt i.isLt)).trans hdegree)
    (z := z) hx₀ hx₁ hδ
  apply h.trans_eq
  calc
    1 / (2 : ℝ) ^ (2 * j) = 1 / (4 : ℝ) ^ j := by rw [pow_mul]; norm_num
    _ = (1 / 4 : ℝ) ^ j := (one_div_pow _ _).symm

end Erdos521
