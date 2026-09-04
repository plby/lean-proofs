import ErdosProblems.Erdos448.HRLemma2Lean448
import ErdosProblems.Erdos448.TauInvTypeMean448

/-!
Prime-power estimates for the correction factor in Erdős--Tenenbaum
Lemma 2.  The hypotheses `0 ≤ v(p^j) ≤ 1` are exactly what is used in the
two applications in Proposition 3 (the constant weight in the first one and
the truncated Rankin weight in the second one).
-/

open scoped BigOperators

namespace TauInvCorrection448

open ErdosTenenbaumLemma2Scratch

/-- A quantitatively convenient version of ``tau-inverse type''.  The
logarithm is retained because this is the error produced literally by the
weighted Euler numerator in Lemma 2. -/
def IsTauInverseLogType (u : ℕ → ℝ) (C : ℝ) : Prop :=
  0 ≤ C ∧
    ∀ {p nu : ℕ}, p.Prime → 1 ≤ nu →
      |u (p ^ nu) - 1 / ((nu + 1 : ℕ) : ℝ)| ≤
        C * (1 + Real.log (p : ℝ)) / (p : ℝ)

/-- The power-saving interface used by the Proposition 3 consumer. -/
def IsTauInverseType (u : ℕ → ℝ) (C delta : ℝ) : Prop :=
  0 ≤ C ∧ 0 < delta ∧
    ∀ {p nu : ℕ}, p.Prime → 1 ≤ nu →
      |u (p ^ nu) - 1 / ((nu + 1 : ℕ) : ℝ)| ≤
        C * (p : ℝ) ^ (-delta)

/-- A relative prime-power class.  Unlike an additive asymptotic error, this
controls quotients at arbitrarily large exponents. -/
structure IsTauInverseRelativeType (u : ℕ → ℝ) (A B : ℝ) : Prop where
  A_pos : 0 < A
  A_le_one : A ≤ 1
  one_le_B : 1 ≤ B
  prime_pow_lower : ∀ {p nu : ℕ}, p.Prime → 1 ≤ nu →
    A / ((nu + 1 : ℕ) : ℝ) ≤ u (p ^ nu)
  prime_pow_upper : ∀ {p nu : ℕ}, p.Prime → 1 ≤ nu →
    u (p ^ nu) ≤ B / ((nu + 1 : ℕ) : ℝ)

/-- The scale which occurs naturally in the correction numerator. -/
noncomputable def primeLogScale (p : ℕ) : ℝ :=
  (1 + Real.log (p : ℝ)) / (p : ℝ)

lemma primeLogScale_nonneg {p : ℕ} (hp : p.Prime) :
    0 ≤ primeLogScale p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  exact div_nonneg (by linarith) hpR.le

lemma primeLogScale_le_one {p : ℕ} (hp : p.Prime) :
    primeLogScale p ≤ 1 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog := Real.log_le_sub_one_of_pos hpR
  rw [primeLogScale, div_le_one hpR]
  linarith

lemma IsTauInverseLogType.prime_pow_le_one_add
    {u : ℕ → ℝ} {C : ℝ} (hu : IsTauInverseLogType u C)
    (huOne : u 1 = 1) {p m : ℕ} (hp : p.Prime) :
    u (p ^ m) ≤ 1 + C := by
  by_cases hm : m = 0
  · subst m
    simp [huOne, hu.1]
  · have hmOne : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have herr := hu.2 hp hmOne
    have hself : u (p ^ m) - 1 / ((m + 1 : ℕ) : ℝ) ≤
        |u (p ^ m) - 1 / ((m + 1 : ℕ) : ℝ)| := le_abs_self _
    have htarget : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      norm_num
    have hscale := primeLogScale_le_one hp
    have herrBound :
        |u (p ^ m) - 1 / ((m + 1 : ℕ) : ℝ)| ≤ C := by
      calc
        |u (p ^ m) - 1 / ((m + 1 : ℕ) : ℝ)|
            ≤ C * (1 + Real.log (p : ℝ)) / (p : ℝ) := herr
        _ = C * primeLogScale p := by rw [primeLogScale]; ring
        _ ≤ C * 1 := mul_le_mul_of_nonneg_left hscale hu.1
        _ = C := mul_one C
    linarith

/-- The elementary dyadic series used to majorize every local tail. -/
lemma dyadic_shifted_weight_summable_and_tsum_le :
    Summable (fun j : ℕ => ((j + 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ j) ∧
      (∑' j : ℕ, ((j + 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ j) ≤ 8 := by
  have hrnorm : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  have hj : Summable (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hrnorm).summable
  have hg : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j) :=
    summable_geometric_two
  have hsplit : (fun j : ℕ => ((j + 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ j) =
      fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j +
        2 * (1 / 2 : ℝ) ^ j := by
    funext j
    push_cast
    ring
  rw [hsplit]
  refine ⟨hj.add (hg.mul_left 2), ?_⟩
  rw [hj.tsum_add (hg.mul_left 2),
    tsum_coe_mul_geometric_of_norm_lt_one hrnorm]
  rw [show (∑' j : ℕ, 2 * (1 / 2 : ℝ) ^ j) = 4 by
    rw [tsum_mul_left, tsum_geometric_two]
    norm_num]
  norm_num

/-- For a prime `p`, the logarithmically weighted geometric tail beginning
at exponent one is at most `8 (1+log p)/p`. -/
lemma prime_geometric_log_tail
    {p : ℕ} (hp : p.Prime) :
    Summable (fun j : ℕ =>
      (1 / (p : ℝ)) ^ (j + 1) *
        (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ))) ∧
      (∑' j : ℕ,
        (1 / (p : ℝ)) ^ (j + 1) *
          (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ))) ≤
        8 * (1 + Real.log (p : ℝ)) / (p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hr : 0 ≤ (1 / (p : ℝ)) := by positivity
  have hrHalf : (1 / (p : ℝ)) ≤ (1 / 2 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) hpTwo
  let major : ℕ → ℝ := fun j =>
    ((1 + Real.log (p : ℝ)) / (p : ℝ)) *
      (((j + 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ j)
  have hmajorSummable : Summable major := by
    exact dyadic_shifted_weight_summable_and_tsum_le.1.mul_left
      ((1 + Real.log (p : ℝ)) / (p : ℝ))
  have hpoint : ∀ j : ℕ,
      (1 / (p : ℝ)) ^ (j + 1) *
          (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) ≤ major j := by
    intro j
    have hrpow : (1 / (p : ℝ)) ^ j ≤ (1 / 2 : ℝ) ^ j :=
      pow_le_pow_left₀ hr hrHalf j
    have hweight :
        1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ) ≤
          ((j + 2 : ℕ) : ℝ) * (1 + Real.log (p : ℝ)) := by
      push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg j) hlog]
    rw [pow_succ]
    dsimp [major]
    have hleftNonneg : 0 ≤ (1 / (p : ℝ)) ^ j := pow_nonneg hr _
    calc
      (1 / (p : ℝ)) ^ j * (1 / (p : ℝ)) *
            (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ))
          = (1 / (p : ℝ)) *
              ((1 / (p : ℝ)) ^ j *
                (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ))) := by ring
      _ ≤ (1 / (p : ℝ)) *
              ((1 / (p : ℝ)) ^ j *
                (((j + 2 : ℕ) : ℝ) * (1 + Real.log (p : ℝ)))) := by
            gcongr
      _ ≤ (1 / (p : ℝ)) *
              ((1 / 2 : ℝ) ^ j *
                (((j + 2 : ℕ) : ℝ) * (1 + Real.log (p : ℝ)))) := by
            gcongr
      _ = ((1 + Real.log (p : ℝ)) / (p : ℝ)) *
              (((j + 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ j) := by ring
  have hsummable : Summable (fun j : ℕ =>
      (1 / (p : ℝ)) ^ (j + 1) *
        (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ))) := by
    exact Summable.of_nonneg_of_le
      (fun j => mul_nonneg (pow_nonneg hr _) (by positivity)) hpoint hmajorSummable
  refine ⟨hsummable, (hsummable.tsum_le_tsum hpoint hmajorSummable).trans ?_⟩
  change (∑' j : ℕ, major j) ≤ _
  rw [show (∑' j : ℕ, major j) =
      ((1 + Real.log (p : ℝ)) / (p : ℝ)) *
        (∑' j : ℕ, ((j + 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ j) by
      exact tsum_mul_left]
  have hfac : 0 ≤ (1 + Real.log (p : ℝ)) / (p : ℝ) := by positivity
  calc
    ((1 + Real.log (p : ℝ)) / (p : ℝ)) *
          (∑' j : ℕ, ((j + 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ j)
        ≤ ((1 + Real.log (p : ℝ)) / (p : ℝ)) * 8 := by
          gcongr
          exact dyadic_shifted_weight_summable_and_tsum_le.2
    _ = 8 * (1 + Real.log (p : ℝ)) / (p : ℝ) := by ring

/-- A reusable local-tail estimate from a uniform bound on the prime-power
numerators. -/
lemma weighted_tail_of_uniform_bound
    (u v : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime)
    (i : ℕ) (U : ℝ) (hU : 0 ≤ U)
    (huNonneg : ∀ n, 0 ≤ u n) (hvNonneg : ∀ n, 0 ≤ v n)
    (hvPowLe : ∀ j : ℕ, v (p ^ j) ≤ 1)
    (huBound : ∀ j : ℕ, u (p ^ (i + (j + 1))) ≤ U) :
    Summable (fun j : ℕ =>
      u (p ^ (i + (j + 1))) * v (p ^ (j + 1)) *
        (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) /
        ((p ^ (j + 1) : ℕ) : ℝ)) ∧
      (∑' j : ℕ,
        u (p ^ (i + (j + 1))) * v (p ^ (j + 1)) *
          (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) /
          ((p ^ (j + 1) : ℕ) : ℝ)) ≤
        8 * U * primeLogScale p := by
  let a : ℕ → ℝ := fun j =>
    u (p ^ (i + (j + 1))) * v (p ^ (j + 1)) *
      (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) /
      ((p ^ (j + 1) : ℕ) : ℝ)
  let b : ℕ → ℝ := fun j =>
    U * ((1 / (p : ℝ)) ^ (j + 1) *
      (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ)))
  have hbSummable : Summable b :=
    (prime_geometric_log_tail hp).1.mul_left U
  have haNonneg : ∀ j, 0 ≤ a j := by
    intro j
    exact div_nonneg
      (mul_nonneg (mul_nonneg (huNonneg _) (hvNonneg _)) (by positivity))
      (Nat.cast_nonneg _)
  have hab : ∀ j, a j ≤ b j := by
    intro j
    have huvLe :
        u (p ^ (i + (j + 1))) * v (p ^ (j + 1)) ≤ U := by
      calc
        u (p ^ (i + (j + 1))) * v (p ^ (j + 1))
            ≤ U * v (p ^ (j + 1)) :=
              mul_le_mul_of_nonneg_right (huBound j) (hvNonneg _)
        _ ≤ U * 1 := mul_le_mul_of_nonneg_left (hvPowLe (j + 1)) hU
        _ = U := mul_one U
    have hweight :
        0 ≤ 1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ) := by
      have hlog : 0 ≤ Real.log (p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
      positivity
    have hdenom : (0 : ℝ) < ((p ^ (j + 1) : ℕ) : ℝ) := by
      exact_mod_cast pow_pos hp.pos (j + 1)
    dsimp [a, b]
    calc
      u (p ^ (i + (j + 1))) * v (p ^ (j + 1)) *
            (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) /
            ((p ^ (j + 1) : ℕ) : ℝ)
          ≤ U * (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) /
            ((p ^ (j + 1) : ℕ) : ℝ) := by gcongr
      _ = U * ((1 / (p : ℝ)) ^ (j + 1) *
            (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ))) := by
          simp only [Nat.cast_pow, div_eq_mul_inv]
          ring
  have haSummable : Summable a :=
    Summable.of_nonneg_of_le haNonneg hab hbSummable
  refine ⟨haSummable, ?_⟩
  change (∑' j, a j) ≤ _
  calc
    (∑' j, a j) ≤ ∑' j, b j := haSummable.tsum_le_tsum hab hbSummable
    _ = U * (∑' j : ℕ,
        (1 / (p : ℝ)) ^ (j + 1) *
          (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ))) := tsum_mul_left
    _ ≤ U * (8 * (1 + Real.log (p : ℝ)) / (p : ℝ)) := by
      gcongr
      exact (prime_geometric_log_tail hp).2
    _ = 8 * U * primeLogScale p := by rw [primeLogScale]; ring

/-- The tail of a weighted shifted Euler numerator.  The estimate is
uniform in the shift exponent `i`. -/
lemma weighted_shifted_tail_summable_and_le
    (u v : ArithmeticFunction ℝ)
    (huOne : u 1 = 1) (huNonneg : ∀ n, 0 ≤ u n)
    (hvNonneg : ∀ n, 0 ≤ v n)
    {C : ℝ} (huType : IsTauInverseLogType u C)
    {p : ℕ} (hp : p.Prime)
    (hvPowLe : ∀ j : ℕ, v (p ^ j) ≤ 1)
    (i : ℕ) :
    Summable (fun j : ℕ =>
      u (p ^ (i + (j + 1))) * v (p ^ (j + 1)) *
        (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) /
        ((p ^ (j + 1) : ℕ) : ℝ)) ∧
      (∑' j : ℕ,
        u (p ^ (i + (j + 1))) * v (p ^ (j + 1)) *
          (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) /
          ((p ^ (j + 1) : ℕ) : ℝ)) ≤
        8 * (1 + C) * primeLogScale p := by
  let U : ℝ := 1 + C
  have hC : 0 ≤ C := huType.1
  have hU : 0 ≤ U := by dsimp [U]; linarith
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  let a : ℕ → ℝ := fun j =>
    u (p ^ (i + (j + 1))) * v (p ^ (j + 1)) *
      (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) /
      ((p ^ (j + 1) : ℕ) : ℝ)
  let b : ℕ → ℝ := fun j =>
    U * ((1 / (p : ℝ)) ^ (j + 1) *
      (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ)))
  have hbSummable : Summable b := by
    exact (prime_geometric_log_tail hp).1.mul_left U
  have haNonneg : ∀ j, 0 ≤ a j := by
    intro j
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (huNonneg _) (hvNonneg _)) (by positivity))
      (Nat.cast_nonneg _)
  have hab : ∀ j, a j ≤ b j := by
    intro j
    have huLe : u (p ^ (i + (j + 1))) ≤ U := by
      exact huType.prime_pow_le_one_add huOne hp
    have huvLe : u (p ^ (i + (j + 1))) * v (p ^ (j + 1)) ≤ U := by
      calc
        u (p ^ (i + (j + 1))) * v (p ^ (j + 1))
            ≤ U * v (p ^ (j + 1)) :=
              mul_le_mul_of_nonneg_right huLe (hvNonneg _)
        _ ≤ U * 1 := mul_le_mul_of_nonneg_left (hvPowLe (j + 1)) hU
        _ = U := mul_one U
    have hweight :
        0 ≤ 1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ) := by positivity
    have hdenom : (0 : ℝ) < ((p ^ (j + 1) : ℕ) : ℝ) := by
      exact_mod_cast pow_pos hp.pos (j + 1)
    dsimp [a, b]
    calc
      u (p ^ (i + (j + 1))) * v (p ^ (j + 1)) *
            (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) /
            ((p ^ (j + 1) : ℕ) : ℝ)
          ≤ U *
            (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) /
            ((p ^ (j + 1) : ℕ) : ℝ) := by
              gcongr
      _ = U * ((1 / (p : ℝ)) ^ (j + 1) *
            (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ))) := by
              simp only [Nat.cast_pow, div_eq_mul_inv]
              ring
  have haSummable : Summable a :=
    Summable.of_nonneg_of_le haNonneg hab hbSummable
  refine ⟨haSummable, ?_⟩
  change (∑' j : ℕ, a j) ≤ _
  calc
    (∑' j : ℕ, a j) ≤ ∑' j : ℕ, b j :=
      haSummable.tsum_le_tsum hab hbSummable
    _ = U * (∑' j : ℕ,
        (1 / (p : ℝ)) ^ (j + 1) *
          (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ))) := by
      exact tsum_mul_left
    _ ≤ U * (8 * (1 + Real.log (p : ℝ)) / (p : ℝ)) := by
      gcongr
      exact (prime_geometric_log_tail hp).2
    _ = 8 * (1 + C) * primeLogScale p := by
      dsimp [U, primeLogScale]
      ring

/-- The unweighted diagonal tail is bounded by the same majorant. -/
lemma diagonal_tail_summable_and_le
    (u v : ArithmeticFunction ℝ)
    (huOne : u 1 = 1) (huNonneg : ∀ n, 0 ≤ u n)
    (hvNonneg : ∀ n, 0 ≤ v n)
    {C : ℝ} (huType : IsTauInverseLogType u C)
    {p : ℕ} (hp : p.Prime)
    (hvPowLe : ∀ j : ℕ, v (p ^ j) ≤ 1) :
    Summable (fun j : ℕ =>
      u (p ^ (j + 1)) * v (p ^ (j + 1)) /
        ((p ^ (j + 1) : ℕ) : ℝ)) ∧
      (∑' j : ℕ,
        u (p ^ (j + 1)) * v (p ^ (j + 1)) /
          ((p ^ (j + 1) : ℕ) : ℝ)) ≤
        8 * (1 + C) * primeLogScale p := by
  let a : ℕ → ℝ := fun j =>
    u (p ^ (j + 1)) * v (p ^ (j + 1)) /
      ((p ^ (j + 1) : ℕ) : ℝ)
  let b : ℕ → ℝ := fun j =>
    u (p ^ (0 + (j + 1))) * v (p ^ (j + 1)) *
      (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) /
      ((p ^ (j + 1) : ℕ) : ℝ)
  have hb := weighted_shifted_tail_summable_and_le
    u v huOne huNonneg hvNonneg huType hp hvPowLe 0
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have haNonneg : ∀ j, 0 ≤ a j := by
    intro j
    exact div_nonneg (mul_nonneg (huNonneg _) (hvNonneg _))
      (Nat.cast_nonneg _)
  have hab : ∀ j, a j ≤ b j := by
    intro j
    have hbase : 0 ≤ u (p ^ (j + 1)) * v (p ^ (j + 1)) :=
      mul_nonneg (huNonneg _) (hvNonneg _)
    have hdenom : (0 : ℝ) < ((p ^ (j + 1) : ℕ) : ℝ) := by
      exact_mod_cast pow_pos hp.pos (j + 1)
    dsimp [a, b]
    simp only [zero_add]
    apply (div_le_div_iff_of_pos_right hdenom).2
    nlinarith [mul_nonneg (Nat.cast_nonneg (j + 1)) hlog]
  have haSummable : Summable a :=
    Summable.of_nonneg_of_le haNonneg hab hb.1
  refine ⟨haSummable, (haSummable.tsum_le_tsum hab hb.1).trans ?_⟩
  exact hb.2

/-- A purely ordered-field estimate which turns bounds for the two local
tails into a bound for the normalized correction factor. -/
lemma normalized_ratio_error
    {N D u0 t nTail dTail : ℝ}
    (hN : N = u0 + nTail) (hD : D = 1 + dTail)
    (hn : 0 ≤ nTail) (hd : 0 ≤ dTail)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |N / D - t| ≤ |u0 - t| + nTail + dTail := by
  have hDone : 1 ≤ D := by rw [hD]; linarith
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hDone
  have hrewrite :
      N / D - t = ((u0 - t) + (nTail - t * dTail)) / D := by
    rw [hN, hD]
    field_simp [ne_of_gt hDpos]
    ring
  rw [hrewrite, abs_div, abs_of_pos hDpos]
  have hdiv :
      |(u0 - t) + (nTail - t * dTail)| / D ≤
        |(u0 - t) + (nTail - t * dTail)| := by
    rw [div_le_iff₀ hDpos]
    have habs : 0 ≤ |(u0 - t) + (nTail - t * dTail)| := abs_nonneg _
    nlinarith [mul_nonneg habs (sub_nonneg.mpr hDone)]
  calc
    |(u0 - t) + (nTail - t * dTail)| / D
        ≤ |(u0 - t) + (nTail - t * dTail)| := hdiv
    _ ≤ |u0 - t| + |nTail - t * dTail| := abs_add_le _ _
    _ ≤ |u0 - t| + (nTail + t * dTail) := by
      gcongr
      calc
        |nTail - t * dTail| = |nTail + -(t * dTail)| := by ring_nf
        _ ≤ |nTail| + |-(t * dTail)| := abs_add_le _ _
        _ = nTail + t * dTail := by
          rw [abs_of_nonneg hn, abs_neg, abs_of_nonneg (mul_nonneg ht0 hd)]
    _ ≤ |u0 - t| + nTail + dTail := by
      nlinarith [mul_le_mul_of_nonneg_right ht1 hd]

/-- Local closure under the correction operation in Lemma 2.  The explicit
constant is immaterial analytically; what matters is that it is independent
of both the prime and the exponent. -/
theorem eulerCorrection_isTauInverseLogType_local
    (u v : ArithmeticFunction ℝ)
    (huOne : u 1 = 1) (hvOne : v 1 = 1)
    (huNonneg : ∀ n, 0 ≤ u n) (hvNonneg : ∀ n, 0 ≤ v n)
    {C : ℝ} (huType : IsTauInverseLogType u C)
    {p nu : ℕ} (hp : p.Prime) (hnu : 1 ≤ nu)
    (hvPowLe : ∀ j : ℕ, v (p ^ j) ≤ 1) :
    |eulerCorrection u v p nu - 1 / ((nu + 1 : ℕ) : ℝ)| ≤
      (16 + 17 * C) * primeLogScale p := by
  let target : ℝ := 1 / ((nu + 1 : ℕ) : ℝ)
  let nTail : ℝ := ∑' j : ℕ,
    u (p ^ (nu + (j + 1))) * v (p ^ (j + 1)) *
      (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) /
      ((p ^ (j + 1) : ℕ) : ℝ)
  let dTail : ℝ := ∑' j : ℕ,
    u (p ^ (j + 1)) * v (p ^ (j + 1)) /
      ((p ^ (j + 1) : ℕ) : ℝ)
  have hnInfo := weighted_shifted_tail_summable_and_le
    u v huOne huNonneg hvNonneg huType hp hvPowLe nu
  have hdInfo := diagonal_tail_summable_and_le
    u v huOne huNonneg hvNonneg huType hp hvPowLe
  have hnNonneg : 0 ≤ nTail := by
    dsimp [nTail]
    exact tsum_nonneg fun j =>
      div_nonneg
        (mul_nonneg (mul_nonneg (huNonneg _) (hvNonneg _)) (by positivity))
        (Nat.cast_nonneg _)
  have hdNonneg : 0 ≤ dTail := by
    dsimp [dTail]
    exact tsum_nonneg fun j =>
      div_nonneg (mul_nonneg (huNonneg _) (hvNonneg _)) (Nat.cast_nonneg _)
  have hnLe : nTail ≤ 8 * (1 + C) * primeLogScale p := by
    exact hnInfo.2
  have hdLe : dTail ≤ 8 * (1 + C) * primeLogScale p := by
    exact hdInfo.2
  have hweighted : Summable (fun j : ℕ =>
      u (p ^ (nu + j)) * v (p ^ j) *
        (1 + (j : ℝ) * Real.log (p : ℝ)) /
        ((p ^ j : ℕ) : ℝ)) := by
    apply (summable_nat_add_iff (f := fun j : ℕ =>
      u (p ^ (nu + j)) * v (p ^ j) *
        (1 + (j : ℝ) * Real.log (p : ℝ)) /
        ((p ^ j : ℕ) : ℝ)) 1).mp
    simpa [Nat.add_assoc] using hnInfo.1
  have hdiag : Summable (fun j : ℕ =>
      u (p ^ j) * v (p ^ j) / ((p ^ j : ℕ) : ℝ)) := by
    apply (summable_nat_add_iff (f := fun j : ℕ =>
      u (p ^ j) * v (p ^ j) / ((p ^ j : ℕ) : ℝ)) 1).mp
    exact hdInfo.1
  have hNsplit : weightedShiftedEuler u v p nu = u (p ^ nu) + nTail := by
    unfold weightedShiftedEuler
    rw [hweighted.tsum_eq_zero_add]
    simp only [add_zero, pow_zero, hvOne, Nat.cast_zero, zero_mul, add_zero,
      mul_one, Nat.cast_one, div_one]
    rfl
  have hDsplit : diagonalEuler u v p = 1 + dTail := by
    unfold diagonalEuler
    rw [hdiag.tsum_eq_zero_add]
    simp only [pow_zero, huOne, hvOne, mul_one, Nat.cast_one, div_one]
    rfl
  have htarget0 : 0 ≤ target := by dsimp [target]; positivity
  have htarget1 : target ≤ 1 := by
    dsimp [target]
    rw [div_le_one (by positivity)]
    norm_num
  have hratio := normalized_ratio_error hNsplit hDsplit
    hnNonneg hdNonneg htarget0 htarget1
  have huErr : |u (p ^ nu) - target| ≤ C * primeLogScale p := by
    dsimp [target, primeLogScale]
    convert huType.2 hp hnu using 1
    ring
  rw [eulerCorrection]
  refine hratio.trans ?_
  have hscale0 := primeLogScale_nonneg hp
  have hC := huType.1
  calc
    |u (p ^ nu) - target| + nTail + dTail
        ≤ C * primeLogScale p +
            8 * (1 + C) * primeLogScale p +
            8 * (1 + C) * primeLogScale p := by
          gcongr
    _ = (16 + 17 * C) * primeLogScale p := by ring

/-- Relative prime-power bounds are preserved by one local correction. -/
theorem eulerCorrection_relative_local
    (u v : ArithmeticFunction ℝ)
    (huOne : u 1 = 1) (hvOne : v 1 = 1)
    (huNonneg : ∀ n, 0 ≤ u n) (hvNonneg : ∀ n, 0 ≤ v n)
    {A B : ℝ} (huRel : IsTauInverseRelativeType u A B)
    {p nu : ℕ} (hp : p.Prime) (hnu : 1 ≤ nu)
    (hvPowLe : ∀ j : ℕ, v (p ^ j) ≤ 1) :
    A / ((1 + 8 * B) * ((nu + 1 : ℕ) : ℝ)) ≤
        eulerCorrection u v p nu ∧
      eulerCorrection u v p nu ≤ B * 9 / ((nu + 1 : ℕ) : ℝ) := by
  let q : ℝ := ((nu + 1 : ℕ) : ℝ)
  let U : ℝ := B / q
  let nTail : ℝ := ∑' j : ℕ,
    u (p ^ (nu + (j + 1))) * v (p ^ (j + 1)) *
      (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) /
      ((p ^ (j + 1) : ℕ) : ℝ)
  let dTail : ℝ := ∑' j : ℕ,
    u (p ^ (j + 1)) * v (p ^ (j + 1)) /
      ((p ^ (j + 1) : ℕ) : ℝ)
  have hB0 : 0 ≤ B := huRel.one_le_B.trans' zero_le_one
  have hq : 0 < q := by dsimp [q]; positivity
  have hU : 0 ≤ U := div_nonneg hB0 hq.le
  have huShiftBound : ∀ j : ℕ, u (p ^ (nu + (j + 1))) ≤ U := by
    intro j
    have hExp : 1 ≤ nu + (j + 1) := by omega
    have hu := huRel.prime_pow_upper hp hExp
    have hden : q ≤ (((nu + (j + 1) + 1 : ℕ) : ℝ)) := by
      dsimp [q]
      exact_mod_cast (show nu + 1 ≤ nu + (j + 1) + 1 by omega)
    calc
      u (p ^ (nu + (j + 1)))
          ≤ B / (((nu + (j + 1) + 1 : ℕ) : ℝ)) := hu
      _ ≤ B / q := by
        exact div_le_div_of_nonneg_left hB0 hq hden
      _ = U := rfl
  have hnInfo := weighted_tail_of_uniform_bound u v hp nu U hU
    huNonneg hvNonneg hvPowLe huShiftBound
  have huDiagBound : ∀ j : ℕ, u (p ^ (0 + (j + 1))) ≤ B := by
    intro j
    simp only [zero_add]
    have hu := huRel.prime_pow_upper hp (show 1 ≤ j + 1 by omega)
    have hden : (1 : ℝ) ≤ (((j + 1 + 1 : ℕ) : ℝ)) := by
      exact_mod_cast (show 1 ≤ j + 1 + 1 by omega)
    exact hu.trans ((div_le_iff₀ (by positivity)).2 (by nlinarith))
  have hdWeighted := weighted_tail_of_uniform_bound u v hp 0 B hB0
    huNonneg hvNonneg hvPowLe huDiagBound
  let dw : ℕ → ℝ := fun j =>
    u (p ^ (0 + (j + 1))) * v (p ^ (j + 1)) *
      (1 + ((j + 1 : ℕ) : ℝ) * Real.log (p : ℝ)) /
      ((p ^ (j + 1) : ℕ) : ℝ)
  let da : ℕ → ℝ := fun j =>
    u (p ^ (j + 1)) * v (p ^ (j + 1)) /
      ((p ^ (j + 1) : ℕ) : ℝ)
  have hdaNonneg : ∀ j, 0 ≤ da j := by
    intro j
    exact div_nonneg (mul_nonneg (huNonneg _) (hvNonneg _)) (Nat.cast_nonneg _)
  have hdaLe : ∀ j, da j ≤ dw j := by
    intro j
    have hlog : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    have hbase : 0 ≤ u (p ^ (j + 1)) * v (p ^ (j + 1)) :=
      mul_nonneg (huNonneg _) (hvNonneg _)
    have hden : (0 : ℝ) < ((p ^ (j + 1) : ℕ) : ℝ) := by
      exact_mod_cast pow_pos hp.pos (j + 1)
    dsimp [da, dw]
    simp only [zero_add]
    apply (div_le_div_iff_of_pos_right hden).2
    nlinarith [mul_nonneg (Nat.cast_nonneg (j + 1)) hlog]
  have hdaSummable : Summable da :=
    Summable.of_nonneg_of_le hdaNonneg hdaLe hdWeighted.1
  have hdLeWeighted : (∑' j, da j) ≤ ∑' j, dw j :=
    hdaSummable.tsum_le_tsum hdaLe hdWeighted.1
  have hnNonneg : 0 ≤ nTail := by
    dsimp [nTail]
    exact tsum_nonneg fun j =>
      div_nonneg
        (mul_nonneg (mul_nonneg (huNonneg _) (hvNonneg _)) (by positivity))
        (Nat.cast_nonneg _)
  have hdNonneg : 0 ≤ dTail := by
    change 0 ≤ ∑' j, da j
    exact tsum_nonneg hdaNonneg
  have hscale := primeLogScale_le_one hp
  have hnLe : nTail ≤ 8 * U := by
    calc
      nTail ≤ 8 * U * primeLogScale p := hnInfo.2
      _ ≤ 8 * U * 1 := mul_le_mul_of_nonneg_left hscale (mul_nonneg (by norm_num) hU)
      _ = 8 * U := by ring
  have hdLe : dTail ≤ 8 * B := by
    calc
      dTail = ∑' j, da j := rfl
      _ ≤ ∑' j, dw j := hdLeWeighted
      _ ≤ 8 * B * primeLogScale p := hdWeighted.2
      _ ≤ 8 * B * 1 := mul_le_mul_of_nonneg_left hscale (mul_nonneg (by norm_num) hB0)
      _ = 8 * B := by ring
  have hweighted : Summable (fun j : ℕ =>
      u (p ^ (nu + j)) * v (p ^ j) *
        (1 + (j : ℝ) * Real.log (p : ℝ)) /
        ((p ^ j : ℕ) : ℝ)) := by
    apply (summable_nat_add_iff (f := fun j : ℕ =>
      u (p ^ (nu + j)) * v (p ^ j) *
        (1 + (j : ℝ) * Real.log (p : ℝ)) /
        ((p ^ j : ℕ) : ℝ)) 1).mp
    simpa [Nat.add_assoc] using hnInfo.1
  have hdiag : Summable (fun j : ℕ =>
      u (p ^ j) * v (p ^ j) / ((p ^ j : ℕ) : ℝ)) := by
    apply (summable_nat_add_iff (f := fun j : ℕ =>
      u (p ^ j) * v (p ^ j) / ((p ^ j : ℕ) : ℝ)) 1).mp
    simpa [da] using hdaSummable
  have hNsplit : weightedShiftedEuler u v p nu = u (p ^ nu) + nTail := by
    unfold weightedShiftedEuler
    rw [hweighted.tsum_eq_zero_add]
    simp only [add_zero, pow_zero, hvOne, Nat.cast_zero, zero_mul, add_zero,
      mul_one, Nat.cast_one, div_one]
    rfl
  have hDsplit : diagonalEuler u v p = 1 + dTail := by
    unfold diagonalEuler
    rw [hdiag.tsum_eq_zero_add]
    simp only [pow_zero, huOne, hvOne, mul_one, Nat.cast_one, div_one]
    rfl
  let N := weightedShiftedEuler u v p nu
  let D := diagonalEuler u v p
  have hN0 : 0 ≤ N := weightedShiftedEuler_nonneg u v huNonneg hvNonneg hp nu
  have hDOne : 1 ≤ D := by dsimp [D]; rw [hDsplit]; linarith
  have hDpos : 0 < D := zero_lt_one.trans_le hDOne
  have hDupper : D ≤ 1 + 8 * B := by dsimp [D]; rw [hDsplit]; linarith
  have huLower := huRel.prime_pow_lower hp hnu
  have huUpper := huRel.prime_pow_upper hp hnu
  have hNlower : A / q ≤ N := by dsimp [N, q]; rw [hNsplit]; linarith
  have hNupper : N ≤ B * 9 / q := by
    dsimp [N]
    rw [hNsplit]
    dsimp [U] at hnLe
    dsimp [q] at huUpper ⊢
    have : 0 < (((nu + 1 : ℕ) : ℝ)) := by positivity
    calc
      u (p ^ nu) + nTail
          ≤ B / (((nu + 1 : ℕ) : ℝ)) + 8 * (B / (((nu + 1 : ℕ) : ℝ))) :=
            add_le_add huUpper hnLe
      _ = B * 9 / (((nu + 1 : ℕ) : ℝ)) := by ring
  rw [eulerCorrection]
  change A / ((1 + 8 * B) * q) ≤ N / D ∧ N / D ≤ B * 9 / q
  constructor
  · rw [le_div_iff₀ hDpos]
    calc
      A / ((1 + 8 * B) * q) * D
          ≤ A / ((1 + 8 * B) * q) * (1 + 8 * B) := by
            have hden : 0 ≤ (1 + 8 * B) * q :=
              mul_nonneg (by nlinarith) hq.le
            exact mul_le_mul_of_nonneg_left hDupper
              (div_nonneg huRel.A_pos.le hden)
      _ = A / q := by
        have hden : 0 < 1 + 8 * B := by nlinarith
        field_simp [ne_of_gt hden, ne_of_gt hq]
      _ ≤ N := hNlower
  · calc
      N / D ≤ N := by
        rw [div_le_iff₀ hDpos]
        nlinarith [mul_nonneg hN0 (sub_nonneg.mpr hDOne)]
      _ ≤ B * 9 / q := hNupper

/-- The multiplicative correction weight assembled from the local factors
of Lemma 2. -/
noncomputable def correctionWeight
    (u v : ArithmeticFunction ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0
  else n.factorization.prod fun p i =>
    if i = 0 then 1 else eulerCorrection u v p i

@[simp] lemma correctionWeight_zero (u v : ArithmeticFunction ℝ) :
    correctionWeight u v 0 = 0 := by simp [correctionWeight]

@[simp] lemma correctionWeight_one (u v : ArithmeticFunction ℝ) :
    correctionWeight u v 1 = 1 := by simp [correctionWeight]

lemma correctionWeight_mul_of_coprime
    (u v : ArithmeticFunction ℝ) {m n : ℕ} (hmn : m.Coprime n) :
    correctionWeight u v (m * n) =
      correctionWeight u v m * correctionWeight u v n := by
  by_cases hm : m = 0
  · subst m
    have hn : n = 1 := by simpa using hmn
    subst n
    simp
  by_cases hn : n = 0
  · subst n
    have hm1 : m = 1 := by simpa [Nat.coprime_comm] using hmn
    subst m
    simp
  have hmn0 : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  simp only [correctionWeight, if_neg hm, if_neg hn, if_neg hmn0]
  rw [Nat.factorization_mul_of_coprime hmn, ← Finsupp.prod_add_index_of_disjoint]
  exact hmn.disjoint_primeFactors

/-- The correction weight bundled as an arithmetic function. -/
noncomputable def correctionWeightAF
    (u v : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨correctionWeight u v, correctionWeight_zero u v⟩

@[simp] lemma correctionWeightAF_apply
    (u v : ArithmeticFunction ℝ) (n : ℕ) :
    correctionWeightAF u v n = correctionWeight u v n := rfl

lemma correctionWeightAF_multiplicative
    (u v : ArithmeticFunction ℝ) :
    ArithmeticFunction.IsMultiplicative (correctionWeightAF u v) := by
  refine ⟨correctionWeight_one u v, ?_⟩
  intro m n hmn
  exact correctionWeight_mul_of_coprime u v hmn

lemma correctionWeight_nonneg
    (u v : ArithmeticFunction ℝ)
    (huOne : u 1 = 1) (hvOne : v 1 = 1)
    (huNonneg : ∀ n, 0 ≤ u n) (hvNonneg : ∀ n, 0 ≤ v n)
    {C : ℝ} (huType : IsTauInverseLogType u C)
    (hvPowLe : ∀ {p : ℕ}, p.Prime → ∀ j : ℕ, v (p ^ j) ≤ 1)
    (n : ℕ) :
    0 ≤ correctionWeight u v n := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  rw [correctionWeight, if_neg hn]
  change 0 ≤ ∏ p ∈ n.factorization.support,
    (if n.factorization p = 0 then 1
      else eulerCorrection u v p (n.factorization p))
  apply Finset.prod_nonneg
  intro p hpSupport
  split_ifs with hi0
  · norm_num
  · have hpMem : p ∈ n.primeFactors := by
      simpa only [Nat.support_factorization] using hpSupport
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpMem
    have hdInfo := diagonal_tail_summable_and_le
      u v huOne huNonneg hvNonneg huType hpPrime (hvPowLe hpPrime)
    have hdiag : Summable (fun j : ℕ =>
        u (p ^ j) * v (p ^ j) / ((p ^ j : ℕ) : ℝ)) := by
      apply (summable_nat_add_iff (f := fun j : ℕ =>
        u (p ^ j) * v (p ^ j) / ((p ^ j : ℕ) : ℝ)) 1).mp
      exact hdInfo.1
    exact eulerCorrection_nonneg u v huOne hvOne huNonneg hvNonneg
      hpPrime (n.factorization p) hdiag

lemma correctionWeight_prime_pow
    (u v : ArithmeticFunction ℝ) {p nu : ℕ}
    (hp : p.Prime) (hnu : 1 ≤ nu) :
    correctionWeight u v (p ^ nu) = eulerCorrection u v p nu := by
  have hnu0 : nu ≠ 0 := Nat.one_le_iff_ne_zero.mp hnu
  have hpnu0 : p ^ nu ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [correctionWeight, if_neg hpnu0, hp.factorization_pow]
  rw [Finsupp.prod_single_index (by simp)]
  simp [hnu0]

/-- Uniform closure of the logarithmic tau-inverse class under the full
multiplicative correction operation. -/
theorem correctionWeight_isTauInverseLogType
    (u v : ArithmeticFunction ℝ)
    (huOne : u 1 = 1) (hvOne : v 1 = 1)
    (huNonneg : ∀ n, 0 ≤ u n) (hvNonneg : ∀ n, 0 ≤ v n)
    {C : ℝ} (huType : IsTauInverseLogType u C)
    (hvPowLe : ∀ {p : ℕ}, p.Prime → ∀ j : ℕ, v (p ^ j) ≤ 1) :
    IsTauInverseLogType (correctionWeight u v) (16 + 17 * C) := by
  refine ⟨by nlinarith [huType.1], ?_⟩
  intro p nu hp hnu
  rw [correctionWeight_prime_pow u v hp hnu]
  simpa [primeLogScale, mul_div_assoc] using
    (eulerCorrection_isTauInverseLogType_local
      u v huOne hvOne huNonneg hvNonneg huType hp hnu (hvPowLe hp))

/-- Global relative class of the multiplicative correction weight. -/
theorem correctionWeight_isTauInverseRelativeType
    (u v : ArithmeticFunction ℝ)
    (huOne : u 1 = 1) (hvOne : v 1 = 1)
    (huNonneg : ∀ n, 0 ≤ u n) (hvNonneg : ∀ n, 0 ≤ v n)
    {A B : ℝ} (huRel : IsTauInverseRelativeType u A B)
    (hvPowLe : ∀ {p : ℕ}, p.Prime → ∀ j : ℕ, v (p ^ j) ≤ 1) :
    IsTauInverseRelativeType (correctionWeight u v)
      (A / (1 + 8 * B)) (9 * B) := by
  have hden : 0 < 1 + 8 * B := by nlinarith [huRel.one_le_B]
  refine
    { A_pos := div_pos huRel.A_pos hden
      A_le_one := by
        rw [div_le_one hden]
        linarith [huRel.A_le_one, huRel.one_le_B]
      one_le_B := by nlinarith [huRel.one_le_B]
      prime_pow_lower := ?_
      prime_pow_upper := ?_ }
  · intro p nu hp hnu
    rw [correctionWeight_prime_pow u v hp hnu]
    have hlocal := (eulerCorrection_relative_local u v huOne hvOne huNonneg
      hvNonneg huRel hp hnu (hvPowLe hp)).1
    calc
      (A / (1 + 8 * B)) / (((nu + 1 : ℕ) : ℝ)) =
          A / ((1 + 8 * B) * (((nu + 1 : ℕ) : ℝ))) := by
            have hq : (0 : ℝ) < ((nu + 1 : ℕ) : ℝ) := by positivity
            field_simp [ne_of_gt hden, ne_of_gt hq]
      _ ≤ eulerCorrection u v p nu := hlocal
  · intro p nu hp hnu
    rw [correctionWeight_prime_pow u v hp hnu]
    have hlocal := (eulerCorrection_relative_local u v huOne hvOne huNonneg
      hvNonneg huRel hp hnu (hvPowLe hp)).2
    calc
      eulerCorrection u v p nu ≤ B * 9 / (((nu + 1 : ℕ) : ℝ)) := hlocal
      _ = (9 * B) / (((nu + 1 : ℕ) : ℝ)) := by ring

/-- Relative bounds give the exact normalized local hypothesis required by
the unconditional HR Lemma 2 engine, with `lambda₂ = 1`. -/
theorem relative_normalized_prime_power_ratio
    (u v : ArithmeticFunction ℝ)
    (huOne : u 1 = 1) (huNonneg : ∀ n, 0 ≤ u n)
    (_hvNonneg : ∀ n, 0 ≤ v n)
    {A B : ℝ} (huRel : IsTauInverseRelativeType u A B)
    {p : ℕ} (hp : p.Prime)
    (hvPowLe : ∀ j : ℕ, v (p ^ j) ≤ 1)
    (i j : ℕ) :
    u (p ^ (i + (j + 1))) * v (p ^ (j + 1)) /
        u (p ^ i) ≤ B / A := by
  let q : ℝ := ((i + 1 : ℕ) : ℝ)
  have hq : 0 < q := by dsimp [q]; positivity
  have hAq : 0 < A / q := div_pos huRel.A_pos hq
  have hdenLower : A / q ≤ u (p ^ i) := by
    by_cases hi : i = 0
    · subst i
      simp only [pow_zero, huOne]
      dsimp [q]
      simpa using huRel.A_le_one
    · exact huRel.prime_pow_lower hp (Nat.one_le_iff_ne_zero.mpr hi)
  have hdenPos : 0 < u (p ^ i) := hAq.trans_le hdenLower
  have hnumUpper : u (p ^ (i + (j + 1))) ≤ B / q := by
    have hExp : 1 ≤ i + (j + 1) := by omega
    have hu := huRel.prime_pow_upper hp hExp
    have hqden : q ≤ (((i + (j + 1) + 1 : ℕ) : ℝ)) := by
      dsimp [q]
      exact_mod_cast (show i + 1 ≤ i + (j + 1) + 1 by omega)
    exact hu.trans (div_le_div_of_nonneg_left
      (huRel.one_le_B.trans' zero_le_one) hq hqden)
  have hnumNonneg := huNonneg (p ^ (i + (j + 1)))
  have hprodUpper :
      u (p ^ (i + (j + 1))) * v (p ^ (j + 1)) ≤ B / q := by
    calc
      u (p ^ (i + (j + 1))) * v (p ^ (j + 1))
          ≤ u (p ^ (i + (j + 1))) * 1 :=
            mul_le_mul_of_nonneg_left (hvPowLe (j + 1)) hnumNonneg
      _ = u (p ^ (i + (j + 1))) := mul_one _
      _ ≤ B / q := hnumUpper
  have hB0 : 0 ≤ B := huRel.one_le_B.trans' zero_le_one
  calc
    u (p ^ (i + (j + 1))) * v (p ^ (j + 1)) / u (p ^ i)
        ≤ (B / q) / u (p ^ i) :=
          div_le_div_of_nonneg_right hprodUpper hdenPos.le
    _ ≤ (B / q) / (A / q) :=
      div_le_div_of_nonneg_left (div_nonneg hB0 hq.le) hAq hdenLower
    _ = B / A := by
      field_simp [ne_of_gt huRel.A_pos, ne_of_gt hq]

theorem correctionWeight_pos_relative
    (u v : ArithmeticFunction ℝ)
    (huOne : u 1 = 1) (hvOne : v 1 = 1)
    (huNonneg : ∀ n, 0 ≤ u n) (hvNonneg : ∀ n, 0 ≤ v n)
    {A B : ℝ} (huRel : IsTauInverseRelativeType u A B)
    (hvPowLe : ∀ {p : ℕ}, p.Prime → ∀ j : ℕ, v (p ^ j) ≤ 1)
    {n : ℕ} (hn : n ≠ 0) :
    0 < correctionWeight u v n := by
  classical
  rw [correctionWeight, if_neg hn]
  change 0 < ∏ p ∈ n.factorization.support,
    (if n.factorization p = 0 then 1
      else eulerCorrection u v p (n.factorization p))
  apply Finset.prod_pos
  intro p hpSupport
  have hpMem : p ∈ n.primeFactors := by
    simpa only [Nat.support_factorization] using hpSupport
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpMem
  have hi0 : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hpSupport
  rw [if_neg hi0]
  have hi : 1 ≤ n.factorization p := Nat.one_le_iff_ne_zero.mpr hi0
  have hlocal := (eulerCorrection_relative_local u v huOne hvOne huNonneg
    hvNonneg huRel hpPrime hi (hvPowLe hpPrime)).1
  have hden : 0 < (1 + 8 * B) * (((n.factorization p + 1 : ℕ) : ℝ)) := by
    have hB : 0 < 1 + 8 * B := by nlinarith [huRel.one_le_B]
    exact mul_pos hB (by positivity)
  exact (div_pos huRel.A_pos hden).trans_le hlocal

theorem correctionWeight_nonneg_relative
    (u v : ArithmeticFunction ℝ)
    (huOne : u 1 = 1) (hvOne : v 1 = 1)
    (huNonneg : ∀ n, 0 ≤ u n) (hvNonneg : ∀ n, 0 ≤ v n)
    {A B : ℝ} (huRel : IsTauInverseRelativeType u A B)
    (hvPowLe : ∀ {p : ℕ}, p.Prime → ∀ j : ℕ, v (p ^ j) ≤ 1)
    (n : ℕ) :
    0 ≤ correctionWeight u v n := by
  by_cases hn : n = 0
  · subst n
    simp
  · exact (correctionWeight_pos_relative u v huOne hvOne huNonneg hvNonneg
      huRel hvPowLe hn).le

/-- The exact HR `hpow` inequality when the output of one correction is used
as `u` in the following shifted application. -/
theorem correctionWeight_normalized_prime_power_ratio
    (u v z : ArithmeticFunction ℝ)
    (huOne : u 1 = 1) (hvOne : v 1 = 1)
    (huNonneg : ∀ n, 0 ≤ u n) (hvNonneg : ∀ n, 0 ≤ v n)
    (hzNonneg : ∀ n, 0 ≤ z n)
    {A B : ℝ} (huRel : IsTauInverseRelativeType u A B)
    (hvPowLe : ∀ {p : ℕ}, p.Prime → ∀ j : ℕ, v (p ^ j) ≤ 1)
    {p : ℕ} (hp : p.Prime)
    (hzPowLe : ∀ j : ℕ, z (p ^ j) ≤ 1)
    (i j : ℕ) :
    correctionWeight u v (p ^ (i + (j + 1))) * z (p ^ (j + 1)) /
        correctionWeight u v (p ^ i) ≤
      (9 * B) / (A / (1 + 8 * B)) := by
  apply relative_normalized_prime_power_ratio (correctionWeightAF u v) z
  · exact correctionWeight_one u v
  · exact correctionWeight_nonneg_relative u v huOne hvOne huNonneg hvNonneg
      huRel hvPowLe
  · exact hzNonneg
  · exact correctionWeight_isTauInverseRelativeType u v huOne hvOne huNonneg
      hvNonneg huRel hvPowLe
  · exact hp
  · exact hzPowLe

/-- The literal logarithmic local error is a power saving.  The exponent
`1/2` is chosen only for convenience. -/
lemma primeLogScale_le_three_rpow_neg_half
    {p : ℕ} (hp : p.Prime) :
    primeLogScale p ≤ 3 * (p : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hone : (1 : ℝ) ≤ (p : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      (1 : ℝ) = (1 : ℝ) ^ (1 / 2 : ℝ) := by norm_num
      _ ≤ (p : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) hpOne hhalf.le
  have hlogRaw := Real.log_le_rpow_div (show (0 : ℝ) ≤ p by positivity) hhalf
  have hlog : Real.log (p : ℝ) ≤ 2 * (p : ℝ) ^ (1 / 2 : ℝ) := by
    convert hlogRaw using 1
    field_simp
  have hnum :
      1 + Real.log (p : ℝ) ≤ 3 * (p : ℝ) ^ (1 / 2 : ℝ) := by
    linarith
  rw [primeLogScale]
  calc
    (1 + Real.log (p : ℝ)) / (p : ℝ)
        ≤ (3 * (p : ℝ) ^ (1 / 2 : ℝ)) / (p : ℝ) :=
          div_le_div_of_nonneg_right hnum hpR.le
    _ = 3 * (p : ℝ) ^ (-(1 : ℝ) / 2) := by
      rw [show -(1 : ℝ) / 2 = (1 / 2 : ℝ) - 1 by ring,
        Real.rpow_sub hpR, Real.rpow_one]
      ring

/-- Conversion from the exact logarithmic error class to the power-saving
interface used by the rest of Proposition 3. -/
lemma IsTauInverseLogType.isTauInverseType
    {u : ℕ → ℝ} {C : ℝ} (hu : IsTauInverseLogType u C) :
    IsTauInverseType u (3 * C) (1 / 2) := by
  refine ⟨mul_nonneg (by norm_num) hu.1, by norm_num, ?_⟩
  intro p nu hp hnu
  have hlocal := hu.2 hp hnu
  have hscale := primeLogScale_le_three_rpow_neg_half hp
  calc
    |u (p ^ nu) - 1 / ((nu + 1 : ℕ) : ℝ)|
        ≤ C * primeLogScale p := by
          simpa [primeLogScale, mul_div_assoc] using hlocal
    _ ≤ C * (3 * (p : ℝ) ^ (-(1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hscale hu.1
    _ = 3 * C * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by ring_nf

/-- Consumer-shaped power-saving form of correction closure. -/
theorem correctionWeight_isTauInverseType
    (u v : ArithmeticFunction ℝ)
    (huOne : u 1 = 1) (hvOne : v 1 = 1)
    (huNonneg : ∀ n, 0 ≤ u n) (hvNonneg : ∀ n, 0 ≤ v n)
    {C : ℝ} (huType : IsTauInverseLogType u C)
    (hvPowLe : ∀ {p : ℕ}, p.Prime → ∀ j : ℕ, v (p ^ j) ≤ 1) :
    IsTauInverseType (correctionWeight u v)
      (3 * (16 + 17 * C)) (1 / 2) :=
  (correctionWeight_isTauInverseLogType u v huOne hvOne huNonneg hvNonneg
    huType hvPowLe).isTauInverseType

/-- A pointwise maximum is a convenient local envelope for hybrid weights
which use one correction below a cutoff and another one above it. -/
lemma max_isTauInverseLogType
    {w₁ w₂ : ℕ → ℝ} {C₁ C₂ : ℝ}
    (h₁ : IsTauInverseLogType w₁ C₁)
    (h₂ : IsTauInverseLogType w₂ C₂) :
    IsTauInverseLogType (fun n => max (w₁ n) (w₂ n)) (max C₁ C₂) := by
  refine ⟨h₁.1.trans (le_max_left _ _), ?_⟩
  intro p nu hp hnu
  have hs := primeLogScale_nonneg hp
  change |max (w₁ (p ^ nu)) (w₂ (p ^ nu)) -
      1 / ((nu + 1 : ℕ) : ℝ)| ≤
    max C₁ C₂ * (1 + Real.log (p : ℝ)) / (p : ℝ)
  by_cases hw : w₁ (p ^ nu) ≤ w₂ (p ^ nu)
  · rw [max_eq_right hw]
    calc
      |w₂ (p ^ nu) - 1 / ((nu + 1 : ℕ) : ℝ)|
          ≤ C₂ * (1 + Real.log (p : ℝ)) / (p : ℝ) := h₂.2 hp hnu
      _ = C₂ * primeLogScale p := by rw [primeLogScale]; ring
      _ ≤ max C₁ C₂ * primeLogScale p :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hs
      _ = max C₁ C₂ * (1 + Real.log (p : ℝ)) / (p : ℝ) := by
        rw [primeLogScale]
        ring
  · have hw' : w₂ (p ^ nu) ≤ w₁ (p ^ nu) := le_of_not_ge hw
    rw [max_eq_left hw']
    calc
      |w₁ (p ^ nu) - 1 / ((nu + 1 : ℕ) : ℝ)|
          ≤ C₁ * (1 + Real.log (p : ℝ)) / (p : ℝ) := h₁.2 hp hnu
      _ = C₁ * primeLogScale p := by rw [primeLogScale]; ring
      _ ≤ max C₁ C₂ * primeLogScale p :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hs
      _ = max C₁ C₂ * (1 + Real.log (p : ℝ)) / (p : ℝ) := by
        rw [primeLogScale]
        ring

/-! ## Bridge to the mean-value package's bundled interface -/

lemma one_add_log_le_three_log {p : ℕ} (hp : p.Prime) :
    1 + Real.log (p : ℝ) ≤ 3 * Real.log (p : ℝ) := by
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlogMon : Real.log 2 ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) hpTwo
  have hlogTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  linarith

lemma meanType_to_localLogType
    {w : ℕ → ℝ} {C : ℝ}
    (hw : TauInvTypeMean448.IsTauInverseLogType w C) :
    IsTauInverseLogType w C := by
  refine ⟨hw.C_nonneg, ?_⟩
  intro p nu hp hnu
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  calc
    |w (p ^ nu) - 1 / ((nu + 1 : ℕ) : ℝ)|
        ≤ C * Real.log (p : ℝ) / (p : ℝ) := hw.prime_pow_close hp hnu
    _ ≤ C * (1 + Real.log (p : ℝ)) / (p : ℝ) := by
      apply div_le_div_of_nonneg_right _ hpR.le
      exact mul_le_mul_of_nonneg_left (by linarith) hw.C_nonneg

/-- Exact interface consumed by `TauInvTypeMean448`: the correction remains
nonnegative and multiplicative, and its local error has the package's
`C log p / p` form. -/
theorem correctionWeight_meanType
    (u v : ArithmeticFunction ℝ) {C : ℝ}
    (huType : TauInvTypeMean448.IsTauInverseLogType u C)
    (hvOne : v 1 = 1) (hvNonneg : ∀ n, 0 ≤ v n)
    (hvPowLe : ∀ {p : ℕ}, p.Prime → ∀ j : ℕ, v (p ^ j) ≤ 1) :
    TauInvTypeMean448.IsTauInverseLogType (correctionWeight u v)
      (3 * (16 + 17 * C)) := by
  have huLocal : IsTauInverseLogType u C := meanType_to_localLogType huType
  have hout := correctionWeight_isTauInverseLogType
    u v huType.map_one hvOne huType.nonneg hvNonneg huLocal hvPowLe
  refine
    { C_nonneg := by nlinarith [huType.C_nonneg]
      map_zero := correctionWeight_zero u v
      map_one := correctionWeight_one u v
      map_mul_of_coprime := fun hmn => correctionWeight_mul_of_coprime u v hmn
      nonneg := correctionWeight_nonneg u v huType.map_one hvOne huType.nonneg
        hvNonneg huLocal hvPowLe
      prime_pow_close := ?_ }
  intro p nu hp hnu
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog0 : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hscale := one_add_log_le_three_log hp
  have hK : 0 ≤ 16 + 17 * C := by nlinarith [huType.C_nonneg]
  calc
    |correctionWeight u v (p ^ nu) - 1 / ((nu + 1 : ℕ) : ℝ)|
        ≤ (16 + 17 * C) * (1 + Real.log (p : ℝ)) / (p : ℝ) :=
          hout.2 hp hnu
    _ ≤ (16 + 17 * C) * (3 * Real.log (p : ℝ)) / (p : ℝ) := by
      apply div_le_div_of_nonneg_right _ hpR.le
      exact mul_le_mul_of_nonneg_left hscale hK
    _ = 3 * (16 + 17 * C) * Real.log (p : ℝ) / (p : ℝ) := by ring

/-- The multiplicative prime-power maximum used to dominate a hybrid shift
factor: below a cutoff it may use one weight and above it the other. -/
noncomputable def maxPrimePowerWeight
    (w₁ w₂ : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0
  else n.factorization.prod fun p i =>
    if i = 0 then 1 else max (w₁ (p ^ i)) (w₂ (p ^ i))

@[simp] lemma maxPrimePowerWeight_zero (w₁ w₂ : ℕ → ℝ) :
    maxPrimePowerWeight w₁ w₂ 0 = 0 := by simp [maxPrimePowerWeight]

@[simp] lemma maxPrimePowerWeight_one (w₁ w₂ : ℕ → ℝ) :
    maxPrimePowerWeight w₁ w₂ 1 = 1 := by simp [maxPrimePowerWeight]

noncomputable def maxPrimePowerWeightAF
    (w₁ w₂ : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨maxPrimePowerWeight w₁ w₂, maxPrimePowerWeight_zero w₁ w₂⟩

@[simp] lemma maxPrimePowerWeightAF_apply
    (w₁ w₂ : ℕ → ℝ) (n : ℕ) :
    maxPrimePowerWeightAF w₁ w₂ n = maxPrimePowerWeight w₁ w₂ n := rfl

lemma maxPrimePowerWeight_mul_of_coprime
    (w₁ w₂ : ℕ → ℝ) {m n : ℕ} (hmn : m.Coprime n) :
    maxPrimePowerWeight w₁ w₂ (m * n) =
      maxPrimePowerWeight w₁ w₂ m * maxPrimePowerWeight w₁ w₂ n := by
  by_cases hm : m = 0
  · subst m
    have hn : n = 1 := by simpa using hmn
    subst n
    simp
  by_cases hn : n = 0
  · subst n
    have hm1 : m = 1 := by simpa [Nat.coprime_comm] using hmn
    subst m
    simp
  have hmn0 : m * n ≠ 0 := Nat.mul_ne_zero hm hn
  simp only [maxPrimePowerWeight, if_neg hm, if_neg hn, if_neg hmn0]
  rw [Nat.factorization_mul_of_coprime hmn, ← Finsupp.prod_add_index_of_disjoint]
  exact hmn.disjoint_primeFactors

lemma maxPrimePowerWeightAF_multiplicative (w₁ w₂ : ℕ → ℝ) :
    ArithmeticFunction.IsMultiplicative (maxPrimePowerWeightAF w₁ w₂) := by
  refine ⟨maxPrimePowerWeight_one w₁ w₂, ?_⟩
  intro m n hmn
  exact maxPrimePowerWeight_mul_of_coprime w₁ w₂ hmn

lemma maxPrimePowerWeight_prime_pow
    (w₁ w₂ : ℕ → ℝ) {p nu : ℕ}
    (hp : p.Prime) (hnu : 1 ≤ nu) :
    maxPrimePowerWeight w₁ w₂ (p ^ nu) =
      max (w₁ (p ^ nu)) (w₂ (p ^ nu)) := by
  have hnu0 : nu ≠ 0 := Nat.one_le_iff_ne_zero.mp hnu
  have hpnu0 : p ^ nu ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [maxPrimePowerWeight, if_neg hpnu0, hp.factorization_pow]
  rw [Finsupp.prod_single_index (by simp)]
  simp [hnu0]

lemma maxPrimePowerWeight_nonneg
    {w₁ w₂ : ℕ → ℝ} (h₁ : ∀ n, 0 ≤ w₁ n) (_h₂ : ∀ n, 0 ≤ w₂ n)
    (n : ℕ) :
    0 ≤ maxPrimePowerWeight w₁ w₂ n := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  rw [maxPrimePowerWeight, if_neg hn]
  change 0 ≤ ∏ p ∈ n.factorization.support,
    (if n.factorization p = 0 then 1
      else max (w₁ (p ^ n.factorization p)) (w₂ (p ^ n.factorization p)))
  apply Finset.prod_nonneg
  intro p hp
  split_ifs
  · norm_num
  · exact (h₁ _).trans (le_max_left _ _)

/-- Bundled tau-inverse type of the true multiplicative hybrid envelope. -/
theorem maxPrimePowerWeight_meanType
    {w₁ w₂ : ℕ → ℝ} {C₁ C₂ : ℝ}
    (h₁ : TauInvTypeMean448.IsTauInverseLogType w₁ C₁)
    (h₂ : TauInvTypeMean448.IsTauInverseLogType w₂ C₂) :
    TauInvTypeMean448.IsTauInverseLogType
      (maxPrimePowerWeight w₁ w₂) (max C₁ C₂) := by
  refine
    { C_nonneg := h₁.C_nonneg.trans (le_max_left _ _)
      map_zero := maxPrimePowerWeight_zero w₁ w₂
      map_one := maxPrimePowerWeight_one w₁ w₂
      map_mul_of_coprime := fun hmn => maxPrimePowerWeight_mul_of_coprime w₁ w₂ hmn
      nonneg := maxPrimePowerWeight_nonneg h₁.nonneg h₂.nonneg
      prime_pow_close := ?_ }
  intro p nu hp hnu
  rw [maxPrimePowerWeight_prime_pow w₁ w₂ hp hnu]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog0 : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hscale : 0 ≤ Real.log (p : ℝ) / (p : ℝ) := div_nonneg hlog0 hpR.le
  by_cases hw : w₁ (p ^ nu) ≤ w₂ (p ^ nu)
  · rw [max_eq_right hw]
    calc
      |w₂ (p ^ nu) - 1 / ((nu + 1 : ℕ) : ℝ)|
          ≤ C₂ * Real.log (p : ℝ) / (p : ℝ) := h₂.prime_pow_close hp hnu
      _ = C₂ * (Real.log (p : ℝ) / (p : ℝ)) := by ring
      _ ≤ max C₁ C₂ * (Real.log (p : ℝ) / (p : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hscale
      _ = max C₁ C₂ * Real.log (p : ℝ) / (p : ℝ) := by ring
  · have hw' : w₂ (p ^ nu) ≤ w₁ (p ^ nu) := le_of_not_ge hw
    rw [max_eq_left hw']
    calc
      |w₁ (p ^ nu) - 1 / ((nu + 1 : ℕ) : ℝ)|
          ≤ C₁ * Real.log (p : ℝ) / (p : ℝ) := h₁.prime_pow_close hp hnu
      _ = C₁ * (Real.log (p : ℝ) / (p : ℝ)) := by ring
      _ ≤ max C₁ C₂ * (Real.log (p : ℝ) / (p : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hscale
      _ = max C₁ C₂ * Real.log (p : ℝ) / (p : ℝ) := by ring

/-- The multiplicative prime-power maximum preserves relative bounds. -/
theorem maxPrimePowerWeight_isTauInverseRelativeType
    {w₁ w₂ : ℕ → ℝ} {A₁ B₁ A₂ B₂ : ℝ}
    (h₁ : IsTauInverseRelativeType w₁ A₁ B₁)
    (h₂ : IsTauInverseRelativeType w₂ A₂ B₂) :
    IsTauInverseRelativeType (maxPrimePowerWeight w₁ w₂)
      (min A₁ A₂) (max B₁ B₂) := by
  refine
    { A_pos := lt_min h₁.A_pos h₂.A_pos
      A_le_one := (min_le_left A₁ A₂).trans h₁.A_le_one
      one_le_B := h₁.one_le_B.trans (le_max_left B₁ B₂)
      prime_pow_lower := ?_
      prime_pow_upper := ?_ }
  · intro p nu hp hnu
    rw [maxPrimePowerWeight_prime_pow w₁ w₂ hp hnu]
    have hq : (0 : ℝ) < ((nu + 1 : ℕ) : ℝ) := by positivity
    calc
      min A₁ A₂ / (((nu + 1 : ℕ) : ℝ))
          ≤ A₁ / (((nu + 1 : ℕ) : ℝ)) :=
            div_le_div_of_nonneg_right (min_le_left _ _) hq.le
      _ ≤ w₁ (p ^ nu) := h₁.prime_pow_lower hp hnu
      _ ≤ max (w₁ (p ^ nu)) (w₂ (p ^ nu)) := le_max_left _ _
  · intro p nu hp hnu
    rw [maxPrimePowerWeight_prime_pow w₁ w₂ hp hnu]
    have hq : (0 : ℝ) < ((nu + 1 : ℕ) : ℝ) := by positivity
    apply max_le
    · calc
        w₁ (p ^ nu) ≤ B₁ / (((nu + 1 : ℕ) : ℝ)) :=
          h₁.prime_pow_upper hp hnu
        _ ≤ max B₁ B₂ / (((nu + 1 : ℕ) : ℝ)) :=
          div_le_div_of_nonneg_right (le_max_left _ _) hq.le
    · calc
        w₂ (p ^ nu) ≤ B₂ / (((nu + 1 : ℕ) : ℝ)) :=
          h₂.prime_pow_upper hp hnu
        _ ≤ max B₁ B₂ / (((nu + 1 : ℕ) : ℝ)) :=
          div_le_div_of_nonneg_right (le_max_right _ _) hq.le

theorem maxPrimePowerWeight_pos_relative
    {w₁ w₂ : ℕ → ℝ} {A₁ B₁ A₂ B₂ : ℝ}
    (h₁ : IsTauInverseRelativeType w₁ A₁ B₁)
    (_h₂ : IsTauInverseRelativeType w₂ A₂ B₂)
    {n : ℕ} (hn : n ≠ 0) :
    0 < maxPrimePowerWeight w₁ w₂ n := by
  classical
  rw [maxPrimePowerWeight, if_neg hn]
  change 0 < ∏ p ∈ n.factorization.support,
    (if n.factorization p = 0 then 1
      else max (w₁ (p ^ n.factorization p)) (w₂ (p ^ n.factorization p)))
  apply Finset.prod_pos
  intro p hpSupport
  have hpMem : p ∈ n.primeFactors := by
    simpa only [Nat.support_factorization] using hpSupport
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpMem
  have hi0 : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hpSupport
  rw [if_neg hi0]
  have hi : 1 ≤ n.factorization p := Nat.one_le_iff_ne_zero.mpr hi0
  have hlower := h₁.prime_pow_lower hpPrime hi
  have hq : (0 : ℝ) < (((n.factorization p + 1 : ℕ) : ℝ)) := by positivity
  exact (div_pos h₁.A_pos hq).trans_le (hlower.trans (le_max_left _ _))

theorem maxPrimePowerWeight_nonneg_relative
    {w₁ w₂ : ℕ → ℝ} {A₁ B₁ A₂ B₂ : ℝ}
    (h₁ : IsTauInverseRelativeType w₁ A₁ B₁)
    (h₂ : IsTauInverseRelativeType w₂ A₂ B₂)
    (n : ℕ) :
    0 ≤ maxPrimePowerWeight w₁ w₂ n := by
  by_cases hn : n = 0
  · subst n
    simp
  · exact (maxPrimePowerWeight_pos_relative h₁ h₂ hn).le

/-- Consumer theorem for the actual hybrid after one correction step. -/
theorem correctionHybrid_isTauInverseRelativeType
    (u v : ArithmeticFunction ℝ)
    (huOne : u 1 = 1) (hvOne : v 1 = 1)
    (huNonneg : ∀ n, 0 ≤ u n) (hvNonneg : ∀ n, 0 ≤ v n)
    {A B : ℝ} (huRel : IsTauInverseRelativeType u A B)
    (hvPowLe : ∀ {p : ℕ}, p.Prime → ∀ j : ℕ, v (p ^ j) ≤ 1) :
    IsTauInverseRelativeType
      (maxPrimePowerWeight (correctionWeight u v) u)
      (min (A / (1 + 8 * B)) A) (max (9 * B) B) :=
  maxPrimePowerWeight_isTauInverseRelativeType
    (correctionWeight_isTauInverseRelativeType u v huOne hvOne huNonneg
      hvNonneg huRel hvPowLe) huRel

theorem correctionHybrid_pos
    (u v : ArithmeticFunction ℝ)
    (huOne : u 1 = 1) (hvOne : v 1 = 1)
    (huNonneg : ∀ n, 0 ≤ u n) (hvNonneg : ∀ n, 0 ≤ v n)
    {A B : ℝ} (huRel : IsTauInverseRelativeType u A B)
    (hvPowLe : ∀ {p : ℕ}, p.Prime → ∀ j : ℕ, v (p ^ j) ≤ 1)
    {n : ℕ} (hn : n ≠ 0) :
    0 < maxPrimePowerWeight (correctionWeight u v) u n := by
  exact maxPrimePowerWeight_pos_relative
    (correctionWeight_isTauInverseRelativeType u v huOne hvOne huNonneg
      hvNonneg huRel hvPowLe) huRel hn

/-- The exact HR `hpow` inequality for the correction/input hybrid used in
the next shifted application. -/
theorem correctionHybrid_normalized_prime_power_ratio
    (u v z : ArithmeticFunction ℝ)
    (huOne : u 1 = 1) (hvOne : v 1 = 1)
    (huNonneg : ∀ n, 0 ≤ u n) (hvNonneg : ∀ n, 0 ≤ v n)
    (hzNonneg : ∀ n, 0 ≤ z n)
    {A B : ℝ} (huRel : IsTauInverseRelativeType u A B)
    (hvPowLe : ∀ {p : ℕ}, p.Prime → ∀ j : ℕ, v (p ^ j) ≤ 1)
    {p : ℕ} (hp : p.Prime)
    (hzPowLe : ∀ j : ℕ, z (p ^ j) ≤ 1)
    (i j : ℕ) :
    maxPrimePowerWeight (correctionWeight u v) u (p ^ (i + (j + 1))) *
          z (p ^ (j + 1)) /
        maxPrimePowerWeight (correctionWeight u v) u (p ^ i) ≤
      max (9 * B) B / min (A / (1 + 8 * B)) A := by
  let hc := correctionWeight_isTauInverseRelativeType u v huOne hvOne huNonneg
    hvNonneg huRel hvPowLe
  let hh := maxPrimePowerWeight_isTauInverseRelativeType hc huRel
  apply relative_normalized_prime_power_ratio
    (maxPrimePowerWeightAF (correctionWeight u v) u) z
  · exact maxPrimePowerWeight_one _ _
  · intro n
    exact maxPrimePowerWeight_nonneg_relative hc huRel n
  · exact hzNonneg
  · exact hh
  · exact hp
  · exact hzPowLe

end TauInvCorrection448

#print axioms TauInvCorrection448.prime_geometric_log_tail
#print axioms TauInvCorrection448.correctionWeight_isTauInverseType
#print axioms TauInvCorrection448.correctionWeight_meanType
#print axioms TauInvCorrection448.maxPrimePowerWeight_meanType
#print axioms TauInvCorrection448.correctionWeight_isTauInverseRelativeType
#print axioms TauInvCorrection448.relative_normalized_prime_power_ratio
#print axioms TauInvCorrection448.correctionHybrid_normalized_prime_power_ratio
