import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# Finite binomial tail bounds for Erdős 746

This file keeps the probabilistic estimates used by the random-graph
argument entirely finite.  `binomialTerm a q i` is the mass of the `i`th
layer in a binomial experiment with `a` trials and success parameter `q`.
The main estimates are proved by multiplying every tail term by an
exponential weight and applying the finite binomial theorem.
-/

open scoped BigOperators

namespace Erdos746

noncomputable section

/-- The `i`th mass in the binomial distribution with `a` trials and
success parameter `q`.  It is zero when `a < i`, because `a.choose i = 0`.
-/
def binomialTerm (a : ℕ) (q : ℝ) (i : ℕ) : ℝ :=
  (a.choose i : ℝ) * q ^ i * (1 - q) ^ (a - i)

/-- The binomial mass of the event `X < K`. -/
def binomialLowerTail (a K : ℕ) (q : ℝ) : ℝ :=
  ∑ i ∈ Finset.range K, binomialTerm a q i

/-- The binomial mass of the event `K ≤ X`. -/
def binomialUpperTail (a K : ℕ) (q : ℝ) : ℝ :=
  ∑ i ∈ (Finset.range (a + 1)).filter (K ≤ ·), binomialTerm a q i

theorem binomialTerm_nonneg {a i : ℕ} {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ binomialTerm a q i := by
  unfold binomialTerm
  positivity

/-- Finite probability-generating-function identity for the binomial
weights. -/
theorem binomial_pgf (a : ℕ) (q z : ℝ) :
    (∑ i ∈ Finset.range (a + 1), z ^ i * binomialTerm a q i) =
      (1 - q + q * z) ^ a := by
  rw [show 1 - q + q * z = q * z + (1 - q) by ring, add_pow]
  apply Finset.sum_congr rfl
  intro i hi
  unfold binomialTerm
  ring

/-- The binomial masses sum to one. -/
@[simp]
theorem sum_binomialTerm (a : ℕ) (q : ℝ) :
    (∑ i ∈ Finset.range (a + 1), binomialTerm a q i) = 1 := by
  simpa using binomial_pgf a q 1

/-- Every finite lower-tail sum is at most one.  The cutoff need not be at
most `a`; terms above `a` vanish automatically. -/
theorem binomialLowerTail_le_one (a K : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    binomialLowerTail a K q ≤ 1 := by
  classical
  by_cases hKa : K ≤ a + 1
  · rw [← sum_binomialTerm a q]
    unfold binomialLowerTail
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono hKa)
      (fun i _ _ ↦ binomialTerm_nonneg hq0 hq1)
  · have hzero : ∀ i ∈ Finset.Ico (a + 1) K, binomialTerm a q i = 0 := by
      intro i hi
      have hleft := (Finset.mem_Ico.mp hi).1
      have hai : a < i := by omega
      simp [binomialTerm, Nat.choose_eq_zero_of_lt hai]
    unfold binomialLowerTail
    rw [← Finset.sum_range_add_sum_Ico (fun i ↦ binomialTerm a q i)
      (Nat.le_of_lt (Nat.lt_of_not_ge hKa))]
    rw [Finset.sum_eq_zero hzero, add_zero]
    exact (sum_binomialTerm a q).le

/-- A direct finite combinatorial estimate for the lower tail.  It is the
form used in union bounds: after choosing at most `r` successful trials, all
remaining trials fail. -/
theorem binomialLowerTail_le_choose_sum_mul
    (a r : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    binomialLowerTail a (r + 1) q ≤
      (∑ i ∈ Finset.range (r + 1), (a.choose i : ℝ)) *
        (1 - q) ^ (a - r) := by
  unfold binomialLowerTail
  calc
    (∑ i ∈ Finset.range (r + 1), binomialTerm a q i) ≤
        ∑ i ∈ Finset.range (r + 1),
          (a.choose i : ℝ) * (1 - q) ^ (a - r) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hir : i ≤ r := by omega
      have hsub : a - r ≤ a - i := Nat.sub_le_sub_left hir a
      unfold binomialTerm
      have hqpow : q ^ i ≤ 1 := pow_le_one₀ hq0 hq1
      have hfail0 : 0 ≤ 1 - q := sub_nonneg.mpr hq1
      have hfail1 : 1 - q ≤ 1 := by linarith
      have hfailpow : (1 - q) ^ (a - i) ≤ (1 - q) ^ (a - r) :=
        pow_le_pow_of_le_one hfail0 hfail1 hsub
      calc
        (a.choose i : ℝ) * q ^ i * (1 - q) ^ (a - i) ≤
            (a.choose i : ℝ) * (1 - q) ^ (a - i) := by
          have hfirst : (a.choose i : ℝ) * q ^ i ≤ (a.choose i : ℝ) :=
            (mul_le_mul_of_nonneg_left hqpow (Nat.cast_nonneg _)).trans_eq (mul_one _)
          exact mul_le_mul_of_nonneg_right hfirst (pow_nonneg hfail0 _)
        _ ≤ (a.choose i : ℝ) * (1 - q) ^ (a - r) := by
          gcongr
    _ = (∑ i ∈ Finset.range (r + 1), (a.choose i : ℝ)) *
          (1 - q) ^ (a - r) := by rw [Finset.sum_mul]

/-- A fully elementary version of the preceding estimate, with the number
of possible sets bounded by `(r+1) * a^r`. -/
theorem binomialLowerTail_le_card_mul_pow
    (a r : ℕ) {q : ℝ} (ha : 1 ≤ a) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    binomialLowerTail a (r + 1) q ≤
      (r + 1 : ℝ) * (a : ℝ) ^ r * (1 - q) ^ (a - r) := by
  calc
    binomialLowerTail a (r + 1) q ≤
        (∑ i ∈ Finset.range (r + 1), (a.choose i : ℝ)) *
          (1 - q) ^ (a - r) :=
      binomialLowerTail_le_choose_sum_mul a r hq0 hq1
    _ ≤ ((r + 1 : ℝ) * (a : ℝ) ^ r) * (1 - q) ^ (a - r) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) _)
      calc
        (∑ i ∈ Finset.range (r + 1), (a.choose i : ℝ)) ≤
            ∑ _i ∈ Finset.range (r + 1), (a : ℝ) ^ r := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' := Finset.mem_range.mp hi
          have hir : i ≤ r := by omega
          have hchoose : (a.choose i : ℝ) ≤ (a : ℝ) ^ i := by
            exact_mod_cast Nat.choose_le_pow a i
          exact hchoose.trans (pow_le_pow_right₀ (by exact_mod_cast ha) hir)
        _ = (r + 1 : ℝ) * (a : ℝ) ^ r := by simp
    _ = (r + 1 : ℝ) * (a : ℝ) ^ r * (1 - q) ^ (a - r) := rfl

/-! ## Exponential-moment bounds -/

/-- The finite exponential-Markov estimate for the lower tail.  This is an
exact finite-sum theorem; no measure-theoretic or independence assumption is
hidden in it. -/
theorem binomialLowerTail_le_exp_mul_pgf
    (a K : ℕ) {q t : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ht : 0 ≤ t) (hK : K ≤ a + 1) :
    binomialLowerTail a K q ≤
      Real.exp (t * (K - 1 : ℕ)) * (1 - q + q * Real.exp (-t)) ^ a := by
  unfold binomialLowerTail
  let z : ℝ := Real.exp (-t)
  have hz0 : 0 ≤ z := Real.exp_nonneg _
  calc
    (∑ i ∈ Finset.range K, binomialTerm a q i) ≤
        ∑ i ∈ Finset.range K,
          Real.exp (t * (K - 1 : ℕ)) * (z ^ i * binomialTerm a q i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiK : i < K := Finset.mem_range.mp hi
      have hiPred : i ≤ K - 1 := by omega
      have hscale : 1 ≤ Real.exp (t * (K - 1 : ℕ)) * z ^ i := by
        dsimp [z]
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        apply Real.one_le_exp
        have hcast : (i : ℝ) ≤ (K - 1 : ℕ) := by exact_mod_cast hiPred
        nlinarith
      have hmass : 0 ≤ binomialTerm a q i := binomialTerm_nonneg hq0 hq1
      calc
        binomialTerm a q i ≤
            (Real.exp (t * (K - 1 : ℕ)) * z ^ i) * binomialTerm a q i :=
          le_mul_of_one_le_left hmass hscale
        _ = Real.exp (t * (K - 1 : ℕ)) * (z ^ i * binomialTerm a q i) := by ring
    _ = Real.exp (t * (K - 1 : ℕ)) *
          (∑ i ∈ Finset.range K, z ^ i * binomialTerm a q i) := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (t * (K - 1 : ℕ)) *
          (∑ i ∈ Finset.range (a + 1), z ^ i * binomialTerm a q i) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hK)
      intro i _ _
      exact mul_nonneg (pow_nonneg hz0 _) (binomialTerm_nonneg hq0 hq1)
    _ = Real.exp (t * (K - 1 : ℕ)) * (1 - q + q * Real.exp (-t)) ^ a := by
      rw [binomial_pgf]

/-- Standard exponential Chernoff form for the finite lower binomial tail:

`P(X < K) ≤ exp(t (K-1) + a q (exp(-t)-1))` for every `t ≥ 0`.
-/
theorem binomialLowerTail_chernoff
    (a K : ℕ) {q t : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ht : 0 ≤ t) (hK : K ≤ a + 1) :
    binomialLowerTail a K q ≤
      Real.exp (t * (K - 1 : ℕ) + a * q * (Real.exp (-t) - 1)) := by
  have hraw := binomialLowerTail_le_exp_mul_pgf a K hq0 hq1 ht hK
  have hbase0 : 0 ≤ 1 - q + q * Real.exp (-t) := by
    nlinarith [mul_nonneg hq0 (Real.exp_nonneg (-t))]
  have hbase :
      1 - q + q * Real.exp (-t) ≤
        Real.exp (q * (Real.exp (-t) - 1)) := by
    convert Real.add_one_le_exp (q * (Real.exp (-t) - 1)) using 1
    ring
  calc
    binomialLowerTail a K q ≤
        Real.exp (t * (K - 1 : ℕ)) * (1 - q + q * Real.exp (-t)) ^ a := hraw
    _ ≤ Real.exp (t * (K - 1 : ℕ)) *
          (Real.exp (q * (Real.exp (-t) - 1))) ^ a := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hbase0 hbase a) (Real.exp_nonneg _)
    _ = Real.exp (t * (K - 1 : ℕ) + a * q * (Real.exp (-t) - 1)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

/-- The customary optimized lower-tail Chernoff estimate.  Writing
`μ = a*q`, for every positive integer `r ≤ μ`,

`P(X ≤ r) ≤ exp(-μ) * (exp(1) * μ / r)^r`.

The left side is `binomialLowerTail a (r+1) q`, since that definition uses
the strict cutoff. -/
theorem binomialLowerTail_chernoff_classic
    (a r : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hr : 0 < r) (hrμ : (r : ℝ) ≤ (a : ℝ) * q) :
    binomialLowerTail a (r + 1) q ≤
      Real.exp (-((a : ℝ) * q)) *
        (Real.exp 1 * ((a : ℝ) * q) / r) ^ r := by
  let μ : ℝ := (a : ℝ) * q
  let t : ℝ := Real.log (μ / r)
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hμpos : 0 < μ := lt_of_lt_of_le hrR (by simpa [μ] using hrμ)
  have hratio_pos : 0 < μ / (r : ℝ) := div_pos hμpos hrR
  have hratio_one : 1 ≤ μ / (r : ℝ) := by
    rw [le_div_iff₀ hrR]
    simpa [μ] using hrμ
  have ht : 0 ≤ t := by
    dsimp [t]
    exact Real.log_nonneg hratio_one
  have hμ_le_a : μ ≤ (a : ℝ) := by
    dsimp [μ]
    have := mul_le_mul_of_nonneg_left hq1 (Nat.cast_nonneg a : (0 : ℝ) ≤ a)
    simpa using this
  have hrμ' : (r : ℝ) ≤ μ := by simpa [μ] using hrμ
  have hraR : (r : ℝ) ≤ a := hrμ'.trans hμ_le_a
  have hra : r ≤ a := by exact_mod_cast hraR
  have hcut : r + 1 ≤ a + 1 := Nat.add_le_add_right hra 1
  have hexpneg : Real.exp (-t) = (r : ℝ) / μ := by
    dsimp [t]
    rw [Real.exp_neg, Real.exp_log hratio_pos]
    field_simp
  have hbase : Real.exp 1 * μ / (r : ℝ) =
      Real.exp (1 + Real.log (μ / r)) := by
    rw [Real.exp_add, Real.exp_log hratio_pos]
    ring
  have hchern := binomialLowerTail_chernoff a (r + 1) hq0 hq1 ht hcut
  calc
    binomialLowerTail a (r + 1) q ≤
        Real.exp
          (t * ((r + 1) - 1 : ℕ) +
            a * q * (Real.exp (-t) - 1)) := hchern
    _ = Real.exp (-μ) * (Real.exp 1 * μ / (r : ℝ)) ^ r := by
      rw [show (r + 1) - 1 = r by omega, show (a : ℝ) * q = μ by rfl,
        hexpneg, hbase, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      dsimp [t]
      field_simp [hμpos.ne', hrR.ne']
      ring
    _ = Real.exp (-((a : ℝ) * q)) *
          (Real.exp 1 * ((a : ℝ) * q) / r) ^ r := by rfl

/-- The finite exponential-Markov estimate for the upper tail. -/
theorem binomialUpperTail_le_exp_mul_pgf
    (a K : ℕ) {q t : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t) :
    binomialUpperTail a K q ≤
      Real.exp (-(t * K)) * (1 - q + q * Real.exp t) ^ a := by
  unfold binomialUpperTail
  let z : ℝ := Real.exp t
  have hz0 : 0 ≤ z := Real.exp_nonneg _
  calc
    (∑ i ∈ (Finset.range (a + 1)).filter (K ≤ ·), binomialTerm a q i) ≤
        ∑ i ∈ (Finset.range (a + 1)).filter (K ≤ ·),
          Real.exp (-(t * K)) * (z ^ i * binomialTerm a q i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hKi : K ≤ i := (Finset.mem_filter.mp hi).2
      have hscale : 1 ≤ Real.exp (-(t * K)) * z ^ i := by
        dsimp [z]
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        apply Real.one_le_exp
        have hcast : (K : ℝ) ≤ i := by exact_mod_cast hKi
        nlinarith
      have hmass : 0 ≤ binomialTerm a q i := binomialTerm_nonneg hq0 hq1
      calc
        binomialTerm a q i ≤
            (Real.exp (-(t * K)) * z ^ i) * binomialTerm a q i :=
          le_mul_of_one_le_left hmass hscale
        _ = Real.exp (-(t * K)) * (z ^ i * binomialTerm a q i) := by ring
    _ = Real.exp (-(t * K)) *
          (∑ i ∈ (Finset.range (a + 1)).filter (K ≤ ·),
            z ^ i * binomialTerm a q i) := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (-(t * K)) *
          (∑ i ∈ Finset.range (a + 1), z ^ i * binomialTerm a q i) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro i _ _
        exact mul_nonneg (pow_nonneg hz0 _) (binomialTerm_nonneg hq0 hq1)
    _ = Real.exp (-(t * K)) * (1 - q + q * Real.exp t) ^ a := by
      rw [binomial_pgf]

/-- Standard exponential Chernoff form for the finite upper binomial tail:

`P(K ≤ X) ≤ exp(-t K + a q (exp(t)-1))` for every `t ≥ 0`.
-/
theorem binomialUpperTail_chernoff
    (a K : ℕ) {q t : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ht : 0 ≤ t) :
    binomialUpperTail a K q ≤
      Real.exp (-(t * K) + a * q * (Real.exp t - 1)) := by
  have hraw := binomialUpperTail_le_exp_mul_pgf a K hq0 hq1 ht
  have hbase0 : 0 ≤ 1 - q + q * Real.exp t := by
    nlinarith [mul_nonneg hq0 (Real.exp_nonneg t)]
  have hbase :
      1 - q + q * Real.exp t ≤ Real.exp (q * (Real.exp t - 1)) := by
    convert Real.add_one_le_exp (q * (Real.exp t - 1)) using 1
    ring
  calc
    binomialUpperTail a K q ≤
        Real.exp (-(t * K)) * (1 - q + q * Real.exp t) ^ a := hraw
    _ ≤ Real.exp (-(t * K)) *
          (Real.exp (q * (Real.exp t - 1))) ^ a := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hbase0 hbase a) (Real.exp_nonneg _)
    _ = Real.exp (-(t * K) + a * q * (Real.exp t - 1)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

/-- The upper-tail estimate specialized to the number `n.choose 2` of
possible edges of a labelled graph. -/
theorem edgeCountUpperTail_chernoff
    (n K : ℕ) {p t : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht : 0 ≤ t) :
    binomialUpperTail (n.choose 2) K p ≤
      Real.exp (-(t * K) + (n.choose 2 : ℝ) * p * (Real.exp t - 1)) :=
  binomialUpperTail_chernoff (n.choose 2) K hp0 hp1 ht

end

end Erdos746
