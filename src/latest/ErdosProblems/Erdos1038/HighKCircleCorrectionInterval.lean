import ErdosProblems.Erdos1038.HighKPlatformIntervalFormula

/-!
# Finite interval bounds for the circle correction

The correction is evaluated through the diagonal Fourier series.  The first
`N` nonnegative terms are enclosed by `HighKIntervalExpr`; the omitted tail is
bounded by the exact telescoping estimate

`sum_{m > N} 1 / m^3 <= 1 / (2 N^2)`.
-/

set_option warningAsError false
set_option maxHeartbeats 1000000

open Set
open scoped BigOperators

namespace Erdos1038

noncomputable section

lemma one_div_cube_le_telescope {x : ℝ} (hx : 2 ≤ x) :
    1 / x ^ 3 ≤
      1 / (2 * (x - 1) ^ 2) - 1 / (2 * x ^ 2) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hxm0 : 0 < x - 1 := by linarith
  field_simp [hx0.ne', hxm0.ne']
  nlinarith

/-- Exact tail estimate used by the numerical verifier. -/
theorem positiveFrequency_cube_tail_le {N : ℕ} (hN : 0 < N) :
    (∑' n : ℕ, 1 / ((((N + n + 1 : ℕ) : ℝ) ^ 3))) ≤
      1 / (2 * (N : ℝ) ^ 2) := by
  let f : ℕ → ℝ := fun n ↦ 1 / (2 * (((N + n : ℕ) : ℝ) ^ 2))
  have hf : Summable f := by
    have hp : Summable (fun n : ℕ ↦
        1 / ((((N + n : ℕ) : ℝ) ^ 2))) := by
      have hbase : Summable (fun n : ℕ ↦
          1 / (((n : ℝ) ^ 2))) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num)
      simpa only [Nat.add_comm] using! (summable_nat_add_iff N).mpr hbase
    simpa only [f, one_div, mul_inv_rev] using! hp.mul_right (2 : ℝ)⁻¹
  have hfshift : Summable (fun n : ℕ ↦ f (n + 1)) := by
    simpa only [Nat.add_comm] using! (summable_nat_add_iff 1).mpr hf
  have htel :
      (∑' n : ℕ, (f n - f (n + 1))) = f 0 := by
    rw [hf.tsum_sub hfshift]
    have hsplit := hf.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one] at hsplit
    linarith
  have hg : Summable (fun n : ℕ ↦
      1 / ((((N + n + 1 : ℕ) : ℝ) ^ 3))) := by
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using!
      (summable_nat_add_iff N).mpr summable_one_div_positiveFrequency_cube
  calc
    (∑' n : ℕ, 1 / ((((N + n + 1 : ℕ) : ℝ) ^ 3))) ≤
        ∑' n : ℕ, (f n - f (n + 1)) := by
      exact Summable.tsum_le_tsum
        (fun n ↦ by
          have hx : 2 ≤ (((N + n + 1 : ℕ) : ℝ)) := by
            have : 2 ≤ N + n + 1 := by omega
            exact_mod_cast this
          have h := one_div_cube_le_telescope hx
          dsimp only [f]
          convert! h using 1
          all_goals norm_num
          all_goals ring)
        hg (hf.sub hfshift)
    _ = f 0 := htel
    _ = 1 / (2 * (N : ℝ) ^ 2) := by simp [f]

lemma circleSincTerm_self_eq {Q : ℝ} (hQ : Q ≠ 0) (n : ℕ) :
    circleSincTerm Q Q n =
      Real.sin (((n + 1 : ℕ) : ℝ) * Q) ^ 2 /
        ((((n + 1 : ℕ) : ℝ) ^ 3) * Q ^ 2) := by
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [circleSincTerm, Real.sinc_of_ne_zero (mul_ne_zero hn hQ)]
  field_simp [hn, hQ]

lemma circleCorrection_eq_neg_tsum_sub_log {Q : ℝ}
    (hQ : 0 < Q) (hQpi : Q ≤ Real.pi) :
    circleCorrection Q =
      -(∑' n : ℕ, circleSincTerm Q Q n) - Real.log (Q / Real.pi) := by
  have hfourier := circleArcEnergy_self_eq_circleSelfEnergy hQ hQpi
  rw [circleSelfEnergy_eq_log_div_add_circleCorrection hQ] at hfourier
  unfold circleArcEnergy at hfourier
  linarith

lemma circleSincTerm_self_le_cube {Q : ℝ} (hQ : 0 < Q) (n : ℕ) :
    circleSincTerm Q Q n ≤
      1 / (((((n + 1 : ℕ) : ℝ) ^ 3) * Q ^ 2)) := by
  rw [circleSincTerm_self_eq hQ.ne']
  have hsin : Real.sin (((n + 1 : ℕ) : ℝ) * Q) ^ 2 ≤ 1 := by
    nlinarith [Real.neg_one_le_sin (((n + 1 : ℕ) : ℝ) * Q),
      Real.sin_le_one (((n + 1 : ℕ) : ℝ) * Q)]
  have hden : 0 < ((((n + 1 : ℕ) : ℝ) ^ 3) * Q ^ 2) := by
    positivity
  exact div_le_div_of_nonneg_right hsin hden.le

theorem circleSincTerm_tail_le {Q : ℝ} {N : ℕ}
    (hQ : 0 < Q) (hN : 0 < N) :
    (∑' n : ℕ, circleSincTerm Q Q (N + n)) ≤
      1 / (2 * (N : ℝ) ^ 2 * Q ^ 2) := by
  let major : ℕ → ℝ := fun n ↦
    1 / (((((N + n + 1 : ℕ) : ℝ) ^ 3) * Q ^ 2))
  have hmajor : Summable major := by
    have hbase : Summable (fun n : ℕ ↦
        1 / ((((N + n + 1 : ℕ) : ℝ) ^ 3))) := by
      simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using!
        (summable_nat_add_iff N).mpr summable_one_div_positiveFrequency_cube
    simpa only [major, one_div, mul_inv_rev, mul_comm] using!
      hbase.mul_right (Q ^ 2)⁻¹
  have hseries : Summable (fun n : ℕ ↦ circleSincTerm Q Q (N + n)) := by
    simpa only [Nat.add_comm] using!
      (summable_nat_add_iff N).mpr (summable_circleSincTerm hQ hQ)
  calc
    (∑' n : ℕ, circleSincTerm Q Q (N + n)) ≤
        ∑' n : ℕ, major n := by
      exact Summable.tsum_le_tsum
        (fun n ↦ by
          simpa only [major, Nat.add_assoc] using!
            circleSincTerm_self_le_cube hQ (N + n))
        hseries hmajor
    _ = (1 / Q ^ 2) *
        (∑' n : ℕ, 1 / ((((N + n + 1 : ℕ) : ℝ) ^ 3))) := by
      calc
        (∑' n : ℕ, major n) =
            ∑' n : ℕ, (1 / Q ^ 2) *
              (1 / ((((N + n + 1 : ℕ) : ℝ) ^ 3))) := by
          apply tsum_congr
          intro n
          dsimp only [major]
          ring
        _ = _ := tsum_mul_left
    _ ≤ (1 / Q ^ 2) * (1 / (2 * (N : ℝ) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left
        (positiveFrequency_cube_tail_le hN) (by positivity)
    _ = 1 / (2 * (N : ℝ) ^ 2 * Q ^ 2) := by ring

/-- A finite sine sum plus the exact tail cap is a lower bound for the
circle correction. -/
theorem circleCorrection_finite_lower_bound {Q : ℝ} {N : ℕ}
    (hQ : 0 < Q) (hQpi : Q ≤ Real.pi) (hN : 0 < N) :
    -(∑ n ∈ Finset.range N,
        Real.sin (((n + 1 : ℕ) : ℝ) * Q) ^ 2 /
          ((((n + 1 : ℕ) : ℝ) ^ 3) * Q ^ 2)) -
        1 / (2 * (N : ℝ) ^ 2 * Q ^ 2) - Real.log (Q / Real.pi) ≤
      circleCorrection Q := by
  have hsum := (summable_circleSincTerm hQ hQ).sum_add_tsum_nat_add N
  have htail := circleSincTerm_tail_le hQ hN
  have hprefix :
      (∑ n ∈ Finset.range N,
          Real.sin (((n + 1 : ℕ) : ℝ) * Q) ^ 2 /
            ((((n + 1 : ℕ) : ℝ) ^ 3) * Q ^ 2)) =
        ∑ n ∈ Finset.range N, circleSincTerm Q Q n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact (circleSincTerm_self_eq hQ.ne' n).symm
  rw [circleCorrection_eq_neg_tsum_sub_log hQ hQpi, hprefix]
  have htail' :
      (∑' n : ℕ, circleSincTerm Q Q (n + N)) ≤
        1 / (2 * (N : ℝ) ^ 2 * Q ^ 2) := by
    simpa only [Nat.add_comm] using! htail
  linarith

namespace HighKIntervalExpr

/-- The `n+1` Fourier summand, encoded in the exact interval language. -/
def circleSelfTermE {m : ℕ} (trigDoubles : ℕ)
    (q : HighKIntervalExpr m) (n : ℕ) : HighKIntervalExpr m :=
  let frequency : Rat := (n + 1 : ℕ)
  .div
    (.sq (.sin trigDoubles (.mul (.rat frequency) q)))
    (.mul (.rat (frequency ^ 3)) (.sq q))

/-- Recursive form of the finite sum, convenient both for evaluation and
for a proof by induction. -/
def circleSelfSumE {m : ℕ} (trigDoubles : ℕ)
    (q : HighKIntervalExpr m) : ℕ → HighKIntervalExpr m
  | 0 => .rat 0
  | N + 1 => .add (circleSelfSumE trigDoubles q N)
      (circleSelfTermE trigDoubles q N)

/-- Certified lower approximation to `circleCorrection q`. -/
def circleCorrectionLowerE {m : ℕ}
    (logTerms trigDoubles N : ℕ)
    (q pi : HighKIntervalExpr m) : HighKIntervalExpr m :=
  .sub
    (.sub (.neg (circleSelfSumE trigDoubles q N))
      (.div (.rat 1)
        (.mul (.mul (.rat 2) (.sq (.rat (N : Rat)))) (.sq q))))
    (.log logTerms (.div q pi))

@[simp] theorem circleSelfTermE_eval {m : ℕ} (v : Fin m → ℝ)
    (trigDoubles : ℕ) (q : HighKIntervalExpr m) (n : ℕ) :
    evalReal v (circleSelfTermE trigDoubles q n) =
      Real.sin (((n + 1 : ℕ) : ℝ) * evalReal v q) ^ 2 /
        ((((n + 1 : ℕ) : ℝ) ^ 3) * (evalReal v q) ^ 2) := by
  simp [circleSelfTermE, HighKIntervalExpr.div,
    HighKIntervalExpr.sq, div_eq_mul_inv, pow_two]

@[simp] theorem circleSelfSumE_eval {m : ℕ} (v : Fin m → ℝ)
    (trigDoubles : ℕ) (q : HighKIntervalExpr m) (N : ℕ) :
    evalReal v (circleSelfSumE trigDoubles q N) =
      ∑ n ∈ Finset.range N,
        Real.sin (((n + 1 : ℕ) : ℝ) * evalReal v q) ^ 2 /
          ((((n + 1 : ℕ) : ℝ) ^ 3) * (evalReal v q) ^ 2) := by
  induction N with
  | zero => simp [circleSelfSumE]
  | succ N ih =>
      simp [circleSelfSumE, ih, Finset.sum_range_succ]

@[simp] theorem circleCorrectionLowerE_eval {m : ℕ}
    (v : Fin m → ℝ) (logTerms trigDoubles N : ℕ)
    (q pi : HighKIntervalExpr m) :
    evalReal v (circleCorrectionLowerE logTerms trigDoubles N q pi) =
      -(∑ n ∈ Finset.range N,
          Real.sin (((n + 1 : ℕ) : ℝ) * evalReal v q) ^ 2 /
            ((((n + 1 : ℕ) : ℝ) ^ 3) * (evalReal v q) ^ 2)) -
        1 / (2 * (N : ℝ) ^ 2 * (evalReal v q) ^ 2) -
          Real.log (evalReal v q / evalReal v pi) := by
  simp [circleCorrectionLowerE, HighKIntervalExpr.sub,
    HighKIntervalExpr.div, HighKIntervalExpr.sq,
    div_eq_mul_inv, sub_eq_add_neg]
  ring

/-- Semantic soundness of the finite correction expression.  All numerical
work needed to use this theorem is delegated to `evalInterval_sound`. -/
theorem circleCorrectionLowerE_le {m : ℕ}
    {v : Fin m → ℝ} {logTerms trigDoubles N : ℕ}
    {q pi : HighKIntervalExpr m}
    (hq : 0 < evalReal v q)
    (hqpi : evalReal v q ≤ Real.pi)
    (hpi : evalReal v pi = Real.pi)
    (hN : 0 < N) :
    evalReal v (circleCorrectionLowerE
      logTerms trigDoubles N q pi) ≤ circleCorrection (evalReal v q) := by
  rw [circleCorrectionLowerE_eval, hpi]
  exact circleCorrection_finite_lower_bound hq hqpi hN

end HighKIntervalExpr

end

end Erdos1038
