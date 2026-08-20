import ErdosProblems.Erdos746.Asymptotics
import ErdosProblems.Erdos746.BinomialBounds

/-!
# The small-set expansion range for Erdős 746

This file formalizes Range I of the expansion union bound.  The edge
probability is `c log n / n`, the probability that a fixed outside vertex
sees an `s`-set is `1 - (1-p)^s`, and `rangeOneMean` is the corresponding
binomial mean.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos746

noncomputable section

/-- Edge probability in the auxiliary binomial random graph. -/
def rangeOneProbability (c : ℝ) (n : ℕ) : ℝ :=
  c * Real.log (n : ℝ) / (n : ℝ)

/-- Probability that an outside vertex has a neighbor in a fixed `s`-set. -/
def rangeOneSuccess (c : ℝ) (n s : ℕ) : ℝ :=
  1 - (1 - rangeOneProbability c n) ^ s

/-- Mean number of outside neighbors of a fixed `s`-set. -/
def rangeOneMean (c : ℝ) (n s : ℕ) : ℝ :=
  ((n - s : ℕ) : ℝ) * rangeOneSuccess c n s

/-- The constant occurring in equation (5) of the mathematical proof. -/
def rangeOneConstant (c : ℝ) : ℝ := Real.exp 3 * c ^ 2 / 4

/-- Integer-power Bernoulli inequality in the form needed for the upper
bound on `1-(1-p)^s`. -/
lemma one_sub_nat_mul_le_pow_one_sub {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ s : ℕ, 1 - (s : ℝ) * p ≤ (1 - p) ^ s := by
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
      rw [pow_succ, Nat.cast_succ]
      have hb : 0 ≤ 1 - p := sub_nonneg.mpr hp1
      calc
        1 - ((s : ℝ) + 1) * p ≤
            (1 - (s : ℝ) * p) * (1 - p) := by
              nlinarith [mul_nonneg (Nat.cast_nonneg s) (sq_nonneg p)]
        _ ≤ (1 - p) ^ s * (1 - p) :=
          mul_le_mul_of_nonneg_right ih hb

lemma rangeOneSuccess_nonneg {c : ℝ} {n s : ℕ}
    (hp0 : 0 ≤ rangeOneProbability c n)
    (hp1 : rangeOneProbability c n ≤ 1) :
    0 ≤ rangeOneSuccess c n s := by
  unfold rangeOneSuccess
  have hbase0 : 0 ≤ 1 - rangeOneProbability c n := sub_nonneg.mpr hp1
  have hbase1 : 1 - rangeOneProbability c n ≤ 1 := by linarith
  linarith [show (1 - rangeOneProbability c n) ^ s ≤ 1 from
    pow_le_one₀ hbase0 hbase1]

/-- Union-bound upper estimate for the chance that one outside vertex sees
the fixed set. -/
lemma rangeOneSuccess_le {c : ℝ} {n s : ℕ}
    (hp0 : 0 ≤ rangeOneProbability c n)
    (hp1 : rangeOneProbability c n ≤ 1) :
    rangeOneSuccess c n s ≤ (s : ℝ) * rangeOneProbability c n := by
  unfold rangeOneSuccess
  linarith [one_sub_nat_mul_le_pow_one_sub hp0 hp1 s]

/-- Elementary rational lower bound for `1-exp(-x)`. -/
lemma div_one_add_le_one_sub_exp_neg {x : ℝ} (hx : 0 ≤ x) :
    x / (1 + x) ≤ 1 - Real.exp (-x) := by
  have hden : 0 < 1 + x := by linarith
  have hexpmul : Real.exp (-x) * (1 + x) ≤ 1 := by
    calc
      Real.exp (-x) * (1 + x) = (1 + x) / Real.exp x := by
        rw [Real.exp_neg]
        field_simp
      _ ≤ Real.exp x / Real.exp x := by
        exact (div_le_div_iff_of_pos_right (Real.exp_pos x)).2
          (by simpa [add_comm] using Real.add_one_le_exp x)
      _ = 1 := div_self (Real.exp_ne_zero x)
  have hexp : Real.exp (-x) ≤ 1 / (1 + x) :=
    (le_div_iff₀ hden).2 (by simpa using hexpmul)
  calc
    x / (1 + x) = 1 - 1 / (1 + x) := by field_simp; ring
    _ ≤ 1 - Real.exp (-x) := sub_le_sub_left hexp 1

/-- A nonempty edge bundle has probability at least `ps/(1+ps)`. -/
lemma mul_div_one_add_le_rangeOneSuccess {c : ℝ} {n s : ℕ}
    (hp0 : 0 ≤ rangeOneProbability c n)
    (hp1 : rangeOneProbability c n ≤ 1) :
    rangeOneProbability c n * s / (1 + rangeOneProbability c n * s) ≤
      rangeOneSuccess c n s := by
  let p := rangeOneProbability c n
  let x := p * (s : ℝ)
  have hx : 0 ≤ x := mul_nonneg hp0 (Nat.cast_nonneg s)
  have hbase0 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hbaseExp : 1 - p ≤ Real.exp (-p) := by
    linarith [Real.add_one_le_exp (-p)]
  have hpow : (1 - p) ^ s ≤ Real.exp (-x) := by
    calc
      (1 - p) ^ s ≤ (Real.exp (-p)) ^ s :=
        pow_le_pow_left₀ hbase0 hbaseExp s
      _ = Real.exp (-x) := by
        rw [← Real.exp_nat_mul]
        congr 1
        simp [x]
        ring
  calc
    rangeOneProbability c n * s /
          (1 + rangeOneProbability c n * s) = x / (1 + x) := by
      simp [p, x]
    _ ≤ 1 - Real.exp (-x) := div_one_add_le_one_sub_exp_neg hx
    _ ≤ 1 - (1 - p) ^ s := sub_le_sub_left hpow 1
    _ = rangeOneSuccess c n s := by rfl

/-- `c log n / n` is eventually a genuine probability when `c>0`. -/
lemma eventually_rangeOneProbability_mem_Icc {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, rangeOneProbability c n ∈ Set.Icc (0 : ℝ) 1 := by
  have hpzero : Tendsto (rangeOneProbability c) atTop (nhds 0) := by
    unfold rangeOneProbability
    simpa [mul_div_assoc] using
      (tendsto_const_nhds.mul tendsto_log_div_nat :
        Tendsto (fun n : ℕ ↦ c * (Real.log (n : ℝ) / (n : ℝ))) atTop (nhds (c * 0)))
  have hpUpper := hpzero.eventually (Iio_mem_nhds zero_lt_one)
  filter_upwards [hpUpper, eventually_ge_atTop 2] with n hpUpper hn
  refine ⟨?_, hpUpper.le⟩
  unfold rangeOneProbability
  positivity

end

end Erdos746
