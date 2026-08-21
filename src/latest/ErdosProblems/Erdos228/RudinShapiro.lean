import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Rudin--Shapiro polynomials

This file develops the finite Rudin--Shapiro recursion used in the proof of
Erdős Problem 228.  The normalization is

`P 0 = Q 0 = 1`,
`P (t+1) = P t + X^(2^t) Q t`, and
`Q (t+1) = P t - X^(2^t) Q t`.
-/

namespace Erdos228

open scoped ComplexConjugate

noncomputable section

mutual
  /-- The first Rudin--Shapiro polynomial. -/
  def rudinShapiroP : ℕ → Polynomial ℂ
    | 0 => 1
    | t + 1 => rudinShapiroP t + Polynomial.X ^ (2 ^ t) * rudinShapiroQ t

  /-- The companion Rudin--Shapiro polynomial. -/
  def rudinShapiroQ : ℕ → Polynomial ℂ
    | 0 => 1
    | t + 1 => rudinShapiroP t - Polynomial.X ^ (2 ^ t) * rudinShapiroQ t
end

@[simp] theorem rudinShapiroP_zero : rudinShapiroP 0 = 1 := rfl
@[simp] theorem rudinShapiroQ_zero : rudinShapiroQ 0 = 1 := rfl

@[simp] theorem rudinShapiroP_succ (t : ℕ) :
    rudinShapiroP (t + 1) =
      rudinShapiroP t + Polynomial.X ^ (2 ^ t) * rudinShapiroQ t := rfl

@[simp] theorem rudinShapiroQ_succ (t : ℕ) :
    rudinShapiroQ (t + 1) =
      rudinShapiroP t - Polynomial.X ^ (2 ^ t) * rudinShapiroQ t := rfl

@[simp] theorem eval_rudinShapiroP_succ (t : ℕ) (z : ℂ) :
    (rudinShapiroP (t + 1)).eval z =
      (rudinShapiroP t).eval z + z ^ (2 ^ t) * (rudinShapiroQ t).eval z := by
  simp [rudinShapiroP_succ]

@[simp] theorem eval_rudinShapiroQ_succ (t : ℕ) (z : ℂ) :
    (rudinShapiroQ (t + 1)).eval z =
      (rudinShapiroP t).eval z - z ^ (2 ^ t) * (rudinShapiroQ t).eval z := by
  simp [rudinShapiroQ_succ]

/-- The parallelogram identity in the form needed by the recursion. -/
lemma normSq_add_mul_add_normSq_sub_mul (a b u : ℂ) :
    Complex.normSq (a + u * b) + Complex.normSq (a - u * b) =
      2 * (Complex.normSq a + Complex.normSq u * Complex.normSq b) := by
  rw [Complex.normSq_add, Complex.normSq_sub, Complex.normSq_mul]
  ring

/-- Rudin--Shapiro's exact energy identity on the unit circle. -/
theorem rudinShapiro_energy (t : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(rudinShapiroP t).eval z‖ ^ 2 + ‖(rudinShapiroQ t).eval z‖ ^ 2 =
      (2 ^ (t + 1) : ℝ) := by
  induction t with
  | zero => norm_num
  | succ t ih =>
      rw [eval_rudinShapiroP_succ, eval_rudinShapiroQ_succ,
        ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
        normSq_add_mul_add_normSq_sub_mul]
      have hzu : Complex.normSq (z ^ (2 ^ t)) = 1 := by
        simp [Complex.normSq_eq_norm_sq, norm_pow, hz]
      rw [hzu, one_mul, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, ih]
      rw [show (2 ^ (t + 1 + 1) : ℝ) = 2 ^ (t + 1) * 2 by
        rw [pow_succ]]
      ring

/-- Each of the two Rudin--Shapiro evaluations is at most `sqrt (2^(t+1))`. -/
theorem norm_eval_rudinShapiroP_le (t : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(rudinShapiroP t).eval z‖ ≤ Real.sqrt (2 ^ (t + 1) : ℝ) := by
  have h := rudinShapiro_energy t hz
  have hsq : ‖(rudinShapiroP t).eval z‖ ^ 2 ≤ (2 ^ (t + 1) : ℝ) := by
    nlinarith [sq_nonneg ‖(rudinShapiroQ t).eval z‖]
  nlinarith [Real.sq_sqrt (show 0 ≤ (2 ^ (t + 1) : ℝ) by positivity),
    Real.sqrt_nonneg (2 ^ (t + 1) : ℝ)]

/-- The same pointwise bound for the companion polynomial. -/
theorem norm_eval_rudinShapiroQ_le (t : ℕ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(rudinShapiroQ t).eval z‖ ≤ Real.sqrt (2 ^ (t + 1) : ℝ) := by
  have h := rudinShapiro_energy t hz
  have hsq : ‖(rudinShapiroQ t).eval z‖ ^ 2 ≤ (2 ^ (t + 1) : ℝ) := by
    nlinarith [sq_nonneg ‖(rudinShapiroP t).eval z‖]
  nlinarith [Real.sq_sqrt (show 0 ≤ (2 ^ (t + 1) : ℝ) by positivity),
    Real.sqrt_nonneg (2 ^ (t + 1) : ℝ)]

/-- The coefficient and support assertions maintained by the recursion. -/
structure RudinShapiroCoeffFacts (t : ℕ) : Prop where
  p_sign : ∀ k < 2 ^ t, (rudinShapiroP t).coeff k = 1 ∨
    (rudinShapiroP t).coeff k = -1
  q_sign : ∀ k < 2 ^ t, (rudinShapiroQ t).coeff k = 1 ∨
    (rudinShapiroQ t).coeff k = -1
  p_zero : ∀ k, 2 ^ t ≤ k → (rudinShapiroP t).coeff k = 0
  q_zero : ∀ k, 2 ^ t ≤ k → (rudinShapiroQ t).coeff k = 0

/-- Both polynomials have sign coefficients precisely on the first `2^t`
positions and vanish after that block. -/
theorem rudinShapiro_coeffFacts (t : ℕ) : RudinShapiroCoeffFacts t := by
  induction t with
  | zero =>
      constructor
      · intro k hk
        have : k = 0 := by omega
        subst k
        simp
      · intro k hk
        have : k = 0 := by omega
        subst k
        simp
      · intro k hk
        have : k ≠ 0 := by omega
        simp [Polynomial.coeff_one, this]
      · intro k hk
        have : k ≠ 0 := by omega
        simp [Polynomial.coeff_one, this]
  | succ t ih =>
      have hpow : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by
        simp [pow_succ, mul_two]
      constructor
      · intro k hk
        rw [rudinShapiroP_succ, Polynomial.coeff_add,
          Polynomial.coeff_X_pow_mul']
        by_cases hlow : k < 2 ^ t
        · rw [if_neg (Nat.not_le.mpr hlow), add_zero]
          exact ih.p_sign k hlow
        · have hle : 2 ^ t ≤ k := Nat.le_of_not_gt hlow
          rw [if_pos hle, ih.p_zero k hle, zero_add]
          have hrest : k - 2 ^ t < 2 ^ t := by omega
          exact ih.q_sign (k - 2 ^ t) hrest
      · intro k hk
        rw [rudinShapiroQ_succ, Polynomial.coeff_sub,
          Polynomial.coeff_X_pow_mul']
        by_cases hlow : k < 2 ^ t
        · rw [if_neg (Nat.not_le.mpr hlow), sub_zero]
          exact ih.p_sign k hlow
        · have hle : 2 ^ t ≤ k := Nat.le_of_not_gt hlow
          rw [if_pos hle, ih.p_zero k hle, zero_sub]
          have hrest : k - 2 ^ t < 2 ^ t := by omega
          rcases ih.q_sign (k - 2 ^ t) hrest with h | h
          · right
            rw [h]
          · left
            rw [h]
            simp
      · intro k hk
        rw [rudinShapiroP_succ, Polynomial.coeff_add,
          Polynomial.coeff_X_pow_mul']
        have hle : 2 ^ t ≤ k := by omega
        rw [if_pos hle, ih.p_zero k hle, zero_add]
        apply ih.q_zero
        omega
      · intro k hk
        rw [rudinShapiroQ_succ, Polynomial.coeff_sub,
          Polynomial.coeff_X_pow_mul']
        have hle : 2 ^ t ≤ k := by omega
        rw [if_pos hle, ih.p_zero k hle, zero_sub]
        rw [ih.q_zero]
        · simp
        · omega

theorem coeff_rudinShapiroP_eq_one_or_neg_one {t k : ℕ} (hk : k < 2 ^ t) :
    (rudinShapiroP t).coeff k = 1 ∨ (rudinShapiroP t).coeff k = -1 :=
  (rudinShapiro_coeffFacts t).p_sign k hk

theorem coeff_rudinShapiroQ_eq_one_or_neg_one {t k : ℕ} (hk : k < 2 ^ t) :
    (rudinShapiroQ t).coeff k = 1 ∨ (rudinShapiroQ t).coeff k = -1 :=
  (rudinShapiro_coeffFacts t).q_sign k hk

theorem coeff_rudinShapiroP_eq_zero {t k : ℕ} (hk : 2 ^ t ≤ k) :
    (rudinShapiroP t).coeff k = 0 :=
  (rudinShapiro_coeffFacts t).p_zero k hk

theorem coeff_rudinShapiroQ_eq_zero {t k : ℕ} (hk : 2 ^ t ≤ k) :
    (rudinShapiroQ t).coeff k = 0 :=
  (rudinShapiro_coeffFacts t).q_zero k hk

theorem natDegree_rudinShapiroP (t : ℕ) :
    (rudinShapiroP t).natDegree = 2 ^ t - 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    apply coeff_rudinShapiroP_eq_zero
    have hpos : 0 < 2 ^ t := by positivity
    omega
  · have hpos : 0 < 2 ^ t := by positivity
    have hlt : 2 ^ t - 1 < 2 ^ t := by omega
    rcases coeff_rudinShapiroP_eq_one_or_neg_one hlt with h | h <;> simp [h]

theorem natDegree_rudinShapiroQ (t : ℕ) :
    (rudinShapiroQ t).natDegree = 2 ^ t - 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    apply coeff_rudinShapiroQ_eq_zero
    have hpos : 0 < 2 ^ t := by positivity
    omega
  · have hpos : 0 < 2 ^ t := by positivity
    have hlt : 2 ^ t - 1 < 2 ^ t := by omega
    rcases coeff_rudinShapiroQ_eq_one_or_neg_one hlt with h | h <;> simp [h]

theorem rudinShapiroP_ne_zero (t : ℕ) : rudinShapiroP t ≠ 0 := by
  intro hp
  have hpos : 0 < 2 ^ t := by positivity
  have hlt : 2 ^ t - 1 < 2 ^ t := by omega
  have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff (2 ^ t - 1)) hp
  rcases coeff_rudinShapiroP_eq_one_or_neg_one hlt with hc | hc
  · simp [hc] at hcoeff
  · simp [hc] at hcoeff

theorem rudinShapiroQ_ne_zero (t : ℕ) : rudinShapiroQ t ≠ 0 := by
  intro hq
  have hpos : 0 < 2 ^ t := by positivity
  have hlt : 2 ^ t - 1 < 2 ^ t := by omega
  have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff (2 ^ t - 1)) hq
  rcases coeff_rudinShapiroQ_eq_one_or_neg_one hlt with hc | hc
  · simp [hc] at hcoeff
  · simp [hc] at hcoeff

theorem degree_rudinShapiroP (t : ℕ) :
    (rudinShapiroP t).degree = (2 ^ t - 1 : ℕ) := by
  rw [Polynomial.degree_eq_natDegree (rudinShapiroP_ne_zero t), natDegree_rudinShapiroP]

theorem degree_rudinShapiroQ (t : ℕ) :
    (rudinShapiroQ t).degree = (2 ^ t - 1 : ℕ) := by
  rw [Polynomial.degree_eq_natDegree (rudinShapiroQ_ne_zero t), natDegree_rudinShapiroQ]

/-- Keep only the coefficients in positions strictly below `m`. -/
def polynomialPrefix (p : Polynomial ℂ) (m : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range m, Polynomial.C (p.coeff k) * Polynomial.X ^ k

@[simp] theorem polynomialPrefix_zero (p : Polynomial ℂ) : polynomialPrefix p 0 = 0 := by
  simp [polynomialPrefix]

theorem eval_polynomialPrefix (p : Polynomial ℂ) (m : ℕ) (z : ℂ) :
    (polynomialPrefix p m).eval z = ∑ k ∈ Finset.range m, p.coeff k * z ^ k := by
  simp only [polynomialPrefix, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

theorem coeff_polynomialPrefix (p : Polynomial ℂ) (m k : ℕ) :
    (polynomialPrefix p m).coeff k = if k < m then p.coeff k else 0 := by
  simp [polynomialPrefix, Polynomial.coeff_C_mul]

theorem polynomialPrefix_eq_self {p : Polynomial ℂ} {m : ℕ} (hp : p.natDegree < m) :
    polynomialPrefix p m = p := by
  exact (p.as_sum_range_C_mul_X_pow' hp).symm

theorem coeff_rudinShapiroP_succ_of_lt {t k : ℕ} (hk : k < 2 ^ t) :
    (rudinShapiroP (t + 1)).coeff k = (rudinShapiroP t).coeff k := by
  rw [rudinShapiroP_succ, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul',
    if_neg (Nat.not_le.mpr hk), add_zero]

theorem coeff_rudinShapiroQ_succ_of_lt {t k : ℕ} (hk : k < 2 ^ t) :
    (rudinShapiroQ (t + 1)).coeff k = (rudinShapiroP t).coeff k := by
  rw [rudinShapiroQ_succ, Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul',
    if_neg (Nat.not_le.mpr hk), sub_zero]

@[simp] theorem coeff_rudinShapiroP_succ_add (t k : ℕ) :
    (rudinShapiroP (t + 1)).coeff (2 ^ t + k) = (rudinShapiroQ t).coeff k := by
  rw [rudinShapiroP_succ, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul',
    if_pos (Nat.le_add_right _ _), coeff_rudinShapiroP_eq_zero]
  · simp
  · exact Nat.le_add_right _ _

@[simp] theorem coeff_rudinShapiroQ_succ_add (t k : ℕ) :
    (rudinShapiroQ (t + 1)).coeff (2 ^ t + k) = -(rudinShapiroQ t).coeff k := by
  rw [rudinShapiroQ_succ, Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul',
    if_pos (Nat.le_add_right _ _), coeff_rudinShapiroP_eq_zero]
  · simp
  · exact Nat.le_add_right _ _

theorem polynomialPrefix_rudinShapiroP_succ_of_le {t m : ℕ} (hm : m ≤ 2 ^ t) :
    polynomialPrefix (rudinShapiroP (t + 1)) m =
      polynomialPrefix (rudinShapiroP t) m := by
  ext k
  rw [coeff_polynomialPrefix, coeff_polynomialPrefix]
  split_ifs with hk
  · exact coeff_rudinShapiroP_succ_of_lt (lt_of_lt_of_le hk hm)
  · rfl

theorem polynomialPrefix_rudinShapiroQ_succ_of_le {t m : ℕ} (hm : m ≤ 2 ^ t) :
    polynomialPrefix (rudinShapiroQ (t + 1)) m =
      polynomialPrefix (rudinShapiroP t) m := by
  ext k
  rw [coeff_polynomialPrefix, coeff_polynomialPrefix]
  split_ifs with hk
  · exact coeff_rudinShapiroQ_succ_of_lt (lt_of_lt_of_le hk hm)
  · rfl

theorem polynomialPrefix_rudinShapiroP_succ_add (t r : ℕ) :
    polynomialPrefix (rudinShapiroP (t + 1)) (2 ^ t + r) =
      rudinShapiroP t + Polynomial.X ^ (2 ^ t) * polynomialPrefix (rudinShapiroQ t) r := by
  ext k
  rw [coeff_polynomialPrefix, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul',
    coeff_polynomialPrefix]
  by_cases hlow : k < 2 ^ t
  · have htotal : k < 2 ^ t + r := lt_of_lt_of_le hlow (Nat.le_add_right _ _)
    rw [if_pos htotal, if_neg (Nat.not_le.mpr hlow), add_zero]
    exact coeff_rudinShapiroP_succ_of_lt hlow
  · have hle : 2 ^ t ≤ k := Nat.le_of_not_gt hlow
    rw [if_pos hle, coeff_rudinShapiroP_eq_zero hle, zero_add]
    by_cases htotal : k < 2 ^ t + r
    · have hrest : k - 2 ^ t < r := by omega
      rw [if_pos htotal, if_pos hrest]
      rw [← Nat.add_sub_of_le hle, coeff_rudinShapiroP_succ_add]
      simp
    · have hrest : ¬ k - 2 ^ t < r := by omega
      rw [if_neg htotal, if_neg hrest]

theorem polynomialPrefix_rudinShapiroQ_succ_add (t r : ℕ) :
    polynomialPrefix (rudinShapiroQ (t + 1)) (2 ^ t + r) =
      rudinShapiroP t - Polynomial.X ^ (2 ^ t) * polynomialPrefix (rudinShapiroQ t) r := by
  ext k
  rw [coeff_polynomialPrefix, Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul',
    coeff_polynomialPrefix]
  by_cases hlow : k < 2 ^ t
  · have htotal : k < 2 ^ t + r := lt_of_lt_of_le hlow (Nat.le_add_right _ _)
    rw [if_pos htotal, if_neg (Nat.not_le.mpr hlow), sub_zero]
    exact coeff_rudinShapiroQ_succ_of_lt hlow
  · have hle : 2 ^ t ≤ k := Nat.le_of_not_gt hlow
    rw [if_pos hle, coeff_rudinShapiroP_eq_zero hle, zero_sub]
    by_cases htotal : k < 2 ^ t + r
    · have hrest : k - 2 ^ t < r := by omega
      rw [if_pos htotal, if_pos hrest]
      rw [← Nat.add_sub_of_le hle, coeff_rudinShapiroQ_succ_add]
      simp
    · have hrest : ¬ k - 2 ^ t < r := by omega
      rw [if_neg htotal, if_neg hrest, neg_zero]

private lemma sqrt_two_mul_add_five_sqrt_le_five_sqrt_add
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hyx : y ≤ x) :
    Real.sqrt (2 * x) + 5 * Real.sqrt y ≤ 5 * Real.sqrt (x + y) := by
  have h2x : 0 ≤ 2 * x := by positivity
  have hxy : 0 ≤ x + y := by positivity
  have hs2x := Real.sq_sqrt h2x
  have hsy := Real.sq_sqrt hy
  have hsxy := Real.sq_sqrt hxy
  have hn2x := Real.sqrt_nonneg (2 * x)
  have hny := Real.sqrt_nonneg y
  have hnxy := Real.sqrt_nonneg (x + y)
  nlinarith [sq_nonneg (Real.sqrt (2 * x) - Real.sqrt y),
    sq_nonneg (Real.sqrt (2 * x) + 5 * Real.sqrt y - 5 * Real.sqrt (x + y))]

/-- Uniform prefix estimate.  This is the finite form of the standard
Rudin--Shapiro prefix bound used by BBMST; the constant `5` is deliberately
loose and is stable under the dyadic recursion. -/
theorem norm_eval_polynomialPrefix_rudinShapiro (t m : ℕ) {z : ℂ}
    (hm : m ≤ 2 ^ t) (hz : ‖z‖ = 1) :
    ‖(polynomialPrefix (rudinShapiroP t) m).eval z‖ ≤ 5 * Real.sqrt m ∧
      ‖(polynomialPrefix (rudinShapiroQ t) m).eval z‖ ≤ 5 * Real.sqrt m := by
  induction t generalizing m with
  | zero =>
      have hm' : m ≤ 1 := by simpa using hm
      interval_cases m <;> norm_num [polynomialPrefix, rudinShapiroP, rudinShapiroQ]
  | succ t ih =>
      have hpow : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by simp [pow_succ, mul_two]
      by_cases hlow : m ≤ 2 ^ t
      · rw [polynomialPrefix_rudinShapiroP_succ_of_le hlow,
          polynomialPrefix_rudinShapiroQ_succ_of_le hlow]
        exact ⟨(ih m hlow).1, (ih m hlow).1⟩
      · have hAm : 2 ^ t ≤ m := by omega
        let r := m - 2 ^ t
        have hm_eq : 2 ^ t + r = m := by
          dsimp [r]
          omega
        have hr : r ≤ 2 ^ t := by omega
        have hir := ih r hr
        have hfull := norm_eval_rudinShapiroP_le t hz
        have hcastpow : (2 ^ (t + 1) : ℝ) = 2 * (2 ^ t : ℝ) := by
          rw [pow_succ]
          ring
        have hsqrt : Real.sqrt (2 ^ (t + 1) : ℝ) =
            Real.sqrt (2 * (2 ^ t : ℝ)) := congrArg Real.sqrt hcastpow
        have hsqrt_bound : Real.sqrt (2 * (2 ^ t : ℝ)) + 5 * Real.sqrt (r : ℝ) ≤
            5 * Real.sqrt ((2 ^ t : ℝ) + r) := by
          apply sqrt_two_mul_add_five_sqrt_le_five_sqrt_add
          · positivity
          · positivity
          · exact_mod_cast hr
        constructor
        · rw [← hm_eq, polynomialPrefix_rudinShapiroP_succ_add,
            Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
          calc
            ‖(rudinShapiroP t).eval z + z ^ 2 ^ t *
                (polynomialPrefix (rudinShapiroQ t) r).eval z‖
                ≤ ‖(rudinShapiroP t).eval z‖ +
                    ‖z ^ 2 ^ t * (polynomialPrefix (rudinShapiroQ t) r).eval z‖ :=
              norm_add_le _ _
            _ = ‖(rudinShapiroP t).eval z‖ +
                ‖(polynomialPrefix (rudinShapiroQ t) r).eval z‖ := by
              rw [norm_mul, norm_pow, hz, one_pow, one_mul]
            _ ≤ Real.sqrt (2 * (2 ^ t : ℝ)) + 5 * Real.sqrt (r : ℝ) := by
              rw [← hsqrt]
              exact add_le_add hfull hir.2
            _ ≤ 5 * Real.sqrt ((2 ^ t : ℝ) + r) := hsqrt_bound
            _ = 5 * Real.sqrt ((2 ^ t + r : ℕ) : ℝ) := by norm_num
        · rw [← hm_eq, polynomialPrefix_rudinShapiroQ_succ_add,
            Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
          calc
            ‖(rudinShapiroP t).eval z - z ^ 2 ^ t *
                (polynomialPrefix (rudinShapiroQ t) r).eval z‖
                ≤ ‖(rudinShapiroP t).eval z‖ +
                    ‖z ^ 2 ^ t * (polynomialPrefix (rudinShapiroQ t) r).eval z‖ :=
              norm_sub_le _ _
            _ = ‖(rudinShapiroP t).eval z‖ +
                ‖(polynomialPrefix (rudinShapiroQ t) r).eval z‖ := by
              rw [norm_mul, norm_pow, hz, one_pow, one_mul]
            _ ≤ Real.sqrt (2 * (2 ^ t : ℝ)) + 5 * Real.sqrt (r : ℝ) := by
              rw [← hsqrt]
              exact add_le_add hfull hir.2
            _ ≤ 5 * Real.sqrt ((2 ^ t : ℝ) + r) := hsqrt_bound
            _ = 5 * Real.sqrt ((2 ^ t + r : ℕ) : ℝ) := by norm_num

theorem norm_eval_polynomialPrefix_rudinShapiroP_le (t m : ℕ) {z : ℂ}
    (hm : m ≤ 2 ^ t) (hz : ‖z‖ = 1) :
    ‖(polynomialPrefix (rudinShapiroP t) m).eval z‖ ≤ 5 * Real.sqrt m :=
  (norm_eval_polynomialPrefix_rudinShapiro t m hm hz).1

theorem norm_eval_polynomialPrefix_rudinShapiroQ_le (t m : ℕ) {z : ℂ}
    (hm : m ≤ 2 ^ t) (hz : ‖z‖ = 1) :
    ‖(polynomialPrefix (rudinShapiroQ t) m).eval z‖ ≤ 5 * Real.sqrt m :=
  (norm_eval_polynomialPrefix_rudinShapiro t m hm hz).2

end

end Erdos228
