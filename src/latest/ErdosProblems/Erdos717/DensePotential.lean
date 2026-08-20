/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- The dense graph potential bound. -/

import ErdosProblems.Erdos717.DenseLogArithmetic

open Function Set
open SimpleGraph

namespace Erdos717

/-- Logarithmic lower bounds for the two canonical reservoir parameters. -/
theorem dense_parameter_log_bounds
    (n L Q : ℕ) (d : ℝ)
    (hn : 0 < n) (hL : 1 ≤ L) (hQ : 1 ≤ Q) (hd : 0 < d)
    (hdLower : (1 / 10 ^ (20 : ℕ) : ℝ) ≤ d)
    (hdnQ : d * n < 200 * Q)
    (hdnL : d ^ 2 * n < 2000 * L) :
    Real.log (n : ℝ) - 3000 ≤ Real.log (L : ℝ) ∧
      Real.log (n : ℝ) - 400 ≤ Real.log (Q : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hLR : (0 : ℝ) < L := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hL)
  have hQR : (0 : ℝ) < Q := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hQ)
  have hbase : (0 : ℝ) < 1 / 10 ^ (20 : ℕ) := by positivity
  have hlogd := Real.strictMonoOn_log.monotoneOn hbase hd hdLower
  have hlogTen : Real.log (10 : ℝ) < 9 := by
    convert Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 10) using 1 <;>
      norm_num
  have hlogdLower : -180 < Real.log d := by
    rw [one_div, Real.log_inv, Real.log_pow] at hlogd
    norm_num at hlogd
    nlinarith
  have hlogQineq := Real.strictMonoOn_log
    (mul_pos hd hnR) (by positivity : (0 : ℝ) < 200 * (Q : ℝ)) hdnQ
  rw [Real.log_mul hd.ne' hnR.ne',
    Real.log_mul (by norm_num : (200 : ℝ) ≠ 0) hQR.ne'] at hlogQineq
  have hlog200 : Real.log (200 : ℝ) < 199 := by
    convert Real.log_lt_sub_one_of_pos
      (by norm_num : (0 : ℝ) < 200) (by norm_num : (200 : ℝ) ≠ 1) using 1 <;>
      norm_num
  have hQbound : Real.log (n : ℝ) - 400 ≤ Real.log (Q : ℝ) := by
    linarith
  have hlogLineq := Real.strictMonoOn_log
    (mul_pos (sq_pos_of_pos hd) hnR)
    (by positivity : (0 : ℝ) < 2000 * (L : ℝ)) hdnL
  rw [Real.log_mul (pow_ne_zero 2 hd.ne') hnR.ne', Real.log_pow,
    Real.log_mul (by norm_num : (2000 : ℝ) ≠ 0) hLR.ne'] at hlogLineq
  have hlog2000 : Real.log (2000 : ℝ) < 1999 := by
    convert Real.log_lt_sub_one_of_pos
      (by norm_num : (0 : ℝ) < 2000) (by norm_num : (2000 : ℝ) ≠ 1) using 1 <;>
      norm_num
  have hLbound : Real.log (n : ℝ) - 3000 ≤ Real.log (L : ℝ) := by
    norm_num at hlogLineq
    nlinarith
  exact ⟨hLbound, hQbound⟩

/-- In density at least `10⁻²⁰`, absence of `TK_k` forces the dense
potential below `k`. -/
theorem dense_graph_potential_lt_forbidden_order
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a k : ℕ) (hind : G.indepNum ≤ a)
    (hnHuge : 10 ^ 100 ≤ Fintype.card V)
    (hdLower : (1 / 10 ^ (20 : ℕ) : ℝ) ≤
      (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) ^ 2)
    (ha : 1 ≤ a) (hk : 2 ≤ k)
    (hnot : ¬Erdos718.ContainsCliqueSubdivision G k) :
    densePotential (Fintype.card V) a < k := by
  classical
  let n := Fintype.card V
  let m := G.edgeFinset.card
  let d : ℝ := (m : ℝ) / (n : ℝ) ^ 2
  let X0 := reservoirSizeParameter m n
  let L := reservoirRouteParameter m n
  let Q := X0 / 5
  have hn : 0 < n := lt_of_lt_of_le (by norm_num) hnHuge
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdLower' : (1 / 10 ^ (20 : ℕ) : ℝ) ≤ d := by
    simpa only [d, m, n] using hdLower
  have hd : 0 < d := lt_of_lt_of_le (by positivity) hdLower'
  have hmR : (m : ℝ) = d * n ^ 2 := by
    dsimp only [d]
    field_simp
  have hmPos : 0 < m := by
    have : (0 : ℝ) < m := by nlinarith
    exact_mod_cast this
  have hXlarge : 320 * n ≤ m := by
    have hnScale : (320 : ℝ) * 10 ^ (20 : ℕ) ≤ n := by
      have hnHugeR : (10 : ℝ) ^ (100 : ℕ) ≤ n := by exact_mod_cast hnHuge
      exact (by norm_num : (320 : ℝ) * 10 ^ (20 : ℕ) ≤ 10 ^ (100 : ℕ)).trans
        hnHugeR
    have hreal : (320 : ℝ) * n ≤ m := by
      have hscaled := mul_le_mul_of_nonneg_right hdLower' (sq_nonneg (n : ℝ))
      rw [hmR]
      nlinarith
    exact_mod_cast hreal
  have hLlarge : 5000 * (n * n * n) ≤ m * m := by
    have hnScale : (5000 : ℝ) * 10 ^ (40 : ℕ) ≤ n := by
      have hnHugeR : (10 : ℝ) ^ (100 : ℕ) ≤ n := by exact_mod_cast hnHuge
      exact (by norm_num : (5000 : ℝ) * 10 ^ (40 : ℕ) ≤ 10 ^ (100 : ℕ)).trans
        hnHugeR
    have hdSq : (1 / 10 ^ (40 : ℕ) : ℝ) ≤ d ^ 2 := by
      nlinarith [sq_nonneg (d - 1 / 10 ^ (20 : ℕ) : ℝ)]
    have hreal : (5000 : ℝ) * ((n : ℝ) * n * n) ≤ m * m := by
      have hscaleMul := mul_le_mul_of_nonneg_right hnScale
        (show (0 : ℝ) ≤ (n : ℝ) ^ 3 by positivity)
      have hbaseReal : (5000 : ℝ) * ((n : ℝ) * n * n) ≤
          (1 / 10 ^ (40 : ℕ) : ℝ) * ((n : ℝ) ^ 2) ^ 2 := by
        nlinarith
      have hdMul := mul_le_mul_of_nonneg_right hdSq
        (sq_nonneg ((n : ℝ) ^ 2))
      rw [hmR]
      nlinarith
    exact_mod_cast hreal
  have hmle : m ≤ n * n := by
    have hedge := G.card_edgeFinset_le_card_choose_two
    exact hedge.trans (by
      rw [Nat.choose_two_right]
      apply Nat.div_le_of_le_mul
      nlinarith [Nat.sub_le n 1])
  have hcases := dense_reservoir_order_inequality G a k hind hn hmPos hmle
    (by simpa only [n, m] using hXlarge)
    (by simpa only [n, m] using hLlarge) ha hk hnot
  have hX0 : 20 ≤ X0 := reservoirSizeParameter_ge_twenty m n hn hXlarge
  have hL : 5 ≤ L := by
    apply reservoirRouteParameter_ge_five m n hn
    simpa only [pow_two] using hLlarge
  have hQ : 1 ≤ Q := by
    dsimp only [Q]
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 5)]
    omega
  have hmX : m < 16 * n * (X0 + 1) := by
    have hq : m / (16 * n) < m / (16 * n) + 1 := Nat.lt_succ_self _
    rw [Nat.div_lt_iff_lt_mul (Nat.mul_pos (by norm_num) hn)] at hq
    simpa [X0, reservoirSizeParameter, mul_comm] using hq
  have hXQ : X0 < 10 * Q := by
    have hq : X0 / 5 < X0 / 5 + 1 := Nat.lt_succ_self _
    rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 5)] at hq
    have hQone : Q + 1 ≤ 2 * Q := by omega
    calc
      X0 < 5 * (Q + 1) := by simpa only [Q, mul_comm] using hq
      _ ≤ 5 * (2 * Q) := Nat.mul_le_mul_left 5 hQone
      _ = 10 * Q := by ring
  have hdnQ : d * n < 200 * Q := by
    have hmXR : (m : ℝ) < 160 * n * Q := by
      exact_mod_cast (show m < 160 * n * Q by nlinarith [hmX, hXQ])
    rw [show d * (n : ℝ) = (m : ℝ) / n by
      dsimp only [d]
      field_simp]
    rw [div_lt_iff₀ hnR]
    nlinarith
  have hmL : m * m < 2000 * (n * n * n) * L := by
    have hq : m * m / (1000 * (n * n * n)) <
        m * m / (1000 * (n * n * n)) + 1 := Nat.lt_succ_self _
    rw [Nat.div_lt_iff_lt_mul
      (Nat.mul_pos (by norm_num) (Nat.mul_pos (Nat.mul_pos hn hn) hn))] at hq
    have hLone : L + 1 ≤ 2 * L := by omega
    change m * m < (L + 1) * (1000 * (n * n * n)) at hq
    calc
      m * m < (L + 1) * (1000 * (n * n * n)) := hq
      _ ≤ (2 * L) * (1000 * (n * n * n)) := Nat.mul_le_mul_right _ hLone
      _ = 2000 * (n * n * n) * L := by ring
  have hdnL : d ^ 2 * n < 2000 * L := by
    have hmLR : (m : ℝ) * m < 2000 * ((n : ℝ) * n * n) * L := by
      exact_mod_cast hmL
    rw [show d ^ 2 * (n : ℝ) =
      ((m : ℝ) * m) / ((n : ℝ) * n * n) by
      dsimp only [d]
      field_simp]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) * n * n)]
    nlinarith
  obtain ⟨hlogL, hlogQ⟩ := dense_parameter_log_bounds n L Q d hn
    (by omega) hQ hd hdLower' hdnQ hdnL
  have hlogn : 100 ≤ Real.log (n : ℝ) := by
    have hcast : (10 : ℝ) ^ (100 : ℕ) ≤ n := by exact_mod_cast hnHuge
    have hmono := Real.strictMonoOn_log.monotoneOn
      (pow_pos (by norm_num : (0 : ℝ) < 10) _) hnR hcast
    rw [Real.log_pow] at hmono
    have hlogTen : 1 < Real.log (10 : ℝ) := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 10)]
      exact Real.exp_one_lt_three.trans (by norm_num)
    norm_num at hmono
    nlinarith
  apply densePotential_lt_of_reservoir_alternative n a k L Q hn ha hk
    (by omega) hQ hlogn hlogL hlogQ
  simpa only [X0, L, Q, m, n] using hcases

end Erdos717
