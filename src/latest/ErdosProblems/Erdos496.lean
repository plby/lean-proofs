/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős Problem 496

The problem as printed asks whether, for every irrational real `α` and every
positive `ε`, there are positive integers `x`, `y`, and `z` such that

`|(x : ℝ) ^ 2 + (y : ℝ) ^ 2 - α * (z : ℝ) ^ 2| < ε`.

The cited Oppenheim--Margulis theorem applies to *indefinite* quadratic forms,
which in this specialization requires `0 < α`.  The printed statement omits
that hypothesis and is false: take `α = -√2` and `ε = 1`.
-/

namespace Erdos496

/-- The existence claim in Problem 496 for fixed `α` and `ε`.

Natural numbers together with the three strict positivity hypotheses encode
the requested positive integers. -/
def HasApproximation (α ε : ℝ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    |(x : ℝ) ^ 2 + (y : ℝ) ^ 2 - α * (z : ℝ) ^ 2| < ε

/-- The universally quantified statement of Erdős Problem 496 exactly as printed. -/
def Erdos496Statement : Prop :=
  ∀ α : ℝ, Irrational α → ∀ ε : ℝ, 0 < ε → HasApproximation α ε

/-- For positive integers, the form with coefficient `-√2` has absolute value at least `2`. -/
lemma two_le_abs_form_neg_sqrt_two (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) :
    (2 : ℝ) ≤
      |(x : ℝ) ^ 2 + (y : ℝ) ^ 2 - (-Real.sqrt 2) * (z : ℝ) ^ 2| := by
  have hx_nat : 1 ≤ x := hx
  have hy_nat : 1 ≤ y := hy
  have hx_real : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx_nat
  have hy_real : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy_nat
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hz_sq : 0 ≤ (z : ℝ) ^ 2 := sq_nonneg (z : ℝ)
  have hinside :
      0 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 - (-Real.sqrt 2) * (z : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (x : ℝ), sq_nonneg (y : ℝ), mul_nonneg hsqrt hz_sq]
  rw [abs_of_nonneg hinside]
  nlinarith [sq_nonneg ((x : ℝ) - 1), sq_nonneg ((y : ℝ) - 1),
    mul_nonneg hsqrt hz_sq]

/-- The literal statement of Erdős Problem 496 is false.

The counterexample is the irrational number `-√2` at tolerance `1`.  For any
positive `x` and `y` (and, a fortiori, for positive `z`) the expression is at
least `2`, so it cannot be strictly less than `1`. -/
theorem erdos_496 : ¬ Erdos496Statement := by
  intro h
  have hirr : Irrational (-Real.sqrt 2) := irrational_sqrt_two.neg
  obtain ⟨x, y, z, hx, hy, _hz, hlt⟩ := h (-Real.sqrt 2) hirr 1 one_pos
  have hge := two_le_abs_form_neg_sqrt_two x y z hx hy
  linarith

/-- The integral ternary quadratic form occurring in Problem 496. -/
def integralForm (α : ℝ) (a b c : ℤ) : ℝ :=
  (a : ℝ) ^ 2 + (b : ℝ) ^ 2 - α * (c : ℝ) ^ 2

/-- The precise specialization of the Oppenheim--Margulis theorem needed here.

This is a proposition, not an additional assumption installed in the environment.  The corrected
Erdős theorem below takes a proof of this published deep result as an explicit argument.  The
quantified hypotheses say exactly that the diagonal form is indefinite (`0 < α`) and irrational. -/
def OppenheimMargulisSpecialization : Prop :=
  ∀ α : ℝ, 0 < α → Irrational α → ∀ δ : ℝ, 0 < δ →
    ∃ a b c : ℤ,
      (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
      0 < |integralForm α a b c| ∧
      |integralForm α a b c| < δ

/-- The intended positive-parameter version of Erdős Problem 496. -/
def PositiveErdos496Statement : Prop :=
  ∀ α : ℝ, 0 < α → Irrational α → ∀ ε : ℝ, 0 < ε → HasApproximation α ε

private lemma one_le_int_sq {a : ℤ} (ha : a ≠ 0) :
    (1 : ℝ) ≤ (a : ℝ) ^ 2 := by
  have ha_pos : (0 : ℤ) < a ^ 2 := sq_pos_of_ne_zero ha
  have ha_one : (1 : ℤ) ≤ a ^ 2 := by omega
  exact_mod_cast ha_one

private lemma one_le_int_sq_add_sq {a b : ℤ} (hab : a ≠ 0 ∨ b ≠ 0) :
    (1 : ℝ) ≤ (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
  rcases hab with ha | hb
  · nlinarith [one_le_int_sq ha, sq_nonneg (b : ℝ)]
  · nlinarith [one_le_int_sq hb, sq_nonneg (a : ℝ)]

@[simp] private lemma natAbs_cast_sq (a : ℤ) :
    ((a.natAbs : ℕ) : ℝ) ^ 2 = (a : ℝ) ^ 2 := by
  cases a with
  | ofNat n => simp
  | negSucc n =>
      simp [pow_two]
      ring

private lemma positive_natural_witness_of_nonzero_integers
    {α ε : ℝ} {a b c : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hq : |integralForm α a b c| < ε) :
    HasApproximation α ε := by
  refine ⟨a.natAbs, b.natAbs, c.natAbs,
    Int.natAbs_pos.mpr ha, Int.natAbs_pos.mpr hb, Int.natAbs_pos.mpr hc, ?_⟩
  simpa [integralForm] using hq

private lemma positive_natural_witness_of_first_zero
    {α ε : ℝ} {b c : ℤ}
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hq : 25 * |integralForm α 0 b c| < ε) :
    HasApproximation α ε := by
  refine ⟨(4 * b).natAbs, (3 * b).natAbs, (5 * c).natAbs,
    Int.natAbs_pos.mpr (mul_ne_zero (by norm_num) hb),
    Int.natAbs_pos.mpr (mul_ne_zero (by norm_num) hb),
    Int.natAbs_pos.mpr (mul_ne_zero (by norm_num) hc), ?_⟩
  have hscale :
      (((4 * b).natAbs : ℕ) : ℝ) ^ 2 + (((3 * b).natAbs : ℕ) : ℝ) ^ 2 -
          α * (((5 * c).natAbs : ℕ) : ℝ) ^ 2 =
        25 * integralForm α 0 b c := by
    simp only [natAbs_cast_sq]
    simp [integralForm]
    ring
  rw [hscale, abs_mul]
  norm_num at hq ⊢
  exact hq

private lemma positive_natural_witness_of_second_zero
    {α ε : ℝ} {a c : ℤ}
    (ha : a ≠ 0) (hc : c ≠ 0)
    (hq : 25 * |integralForm α a 0 c| < ε) :
    HasApproximation α ε := by
  refine ⟨(3 * a).natAbs, (4 * a).natAbs, (5 * c).natAbs,
    Int.natAbs_pos.mpr (mul_ne_zero (by norm_num) ha),
    Int.natAbs_pos.mpr (mul_ne_zero (by norm_num) ha),
    Int.natAbs_pos.mpr (mul_ne_zero (by norm_num) hc), ?_⟩
  have hscale :
      (((3 * a).natAbs : ℕ) : ℝ) ^ 2 + (((4 * a).natAbs : ℕ) : ℝ) ^ 2 -
          α * (((5 * c).natAbs : ℕ) : ℝ) ^ 2 =
        25 * integralForm α a 0 c := by
    simp only [natAbs_cast_sq]
    simp [integralForm]
    ring
  rw [hscale, abs_mul]
  norm_num at hq ⊢
  exact hq

/-- Oppenheim small values for the diagonal form yield witnesses whose three coordinates are
strictly positive.  The proof removes zero coordinates using the `3-4-5` Pythagorean rotation,
which multiplies the value of the form by `25`. -/
theorem hasApproximation_of_oppenheim_small_values
    {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε)
    (hsmall : ∀ δ : ℝ, 0 < δ →
      ∃ a b c : ℤ,
        (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
        0 < |integralForm α a b c| ∧
        |integralForm α a b c| < δ) :
    HasApproximation α ε := by
  let δ : ℝ := min (1 / 2) (min (α / 2) (ε / 25))
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨a, b, c, habc, _hq_pos, hqδ⟩ := hsmall δ hδ
  have hδ_half : δ ≤ (1 / 2 : ℝ) := min_le_left _ _
  have hδ_alpha : δ ≤ α / 2 :=
    (min_le_right (1 / 2 : ℝ) _).trans (min_le_left _ _)
  have hδ_epsilon : δ ≤ ε / 25 :=
    (min_le_right (1 / 2 : ℝ) _).trans (min_le_right _ _)
  have hq_half : |integralForm α a b c| < 1 / 2 := hqδ.trans_le hδ_half
  have hq_alpha : |integralForm α a b c| < α / 2 := hqδ.trans_le hδ_alpha
  have hq_epsilon : |integralForm α a b c| < ε / 25 := hqδ.trans_le hδ_epsilon
  have hc : c ≠ 0 := by
    intro hc
    subst c
    have hab : a ≠ 0 ∨ b ≠ 0 := by simpa using habc
    have hone := one_le_int_sq_add_sq hab
    have hform : integralForm α a b 0 = (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
      simp [integralForm]
    rw [hform, abs_of_nonneg (by positivity)] at hq_half
    linarith
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    simp only [not_or, not_ne_iff] at h
    rcases h with ⟨ha, hb⟩
    subst a
    subst b
    have hc_sq := one_le_int_sq hc
    have hform : |integralForm α 0 0 c| = α * (c : ℝ) ^ 2 := by
      simpa [integralForm] using
        (abs_of_nonneg (mul_nonneg hα.le (sq_nonneg (c : ℝ))))
    rw [hform] at hq_alpha
    nlinarith
  by_cases ha : a = 0
  · subst a
    have hb : b ≠ 0 := hab.resolve_left (by simp)
    apply positive_natural_witness_of_first_zero hb hc
    nlinarith
  · by_cases hb : b = 0
    · subst b
      apply positive_natural_witness_of_second_zero ha hc
      nlinarith
    · exact positive_natural_witness_of_nonzero_integers ha hb hc (by nlinarith)

/-- The corrected positive Erdős 496 theorem, conditional only on the exact published
Oppenheim--Margulis specialization stated above.

Keeping the deep input as an explicit proof argument makes the dependency kernel-visible and does
not introduce a project-local assumption. -/
theorem erdos_496_positive
    (hoppenheim : OppenheimMargulisSpecialization) :
    PositiveErdos496Statement := by
  intro α hα hα_irr ε hε
  exact hasApproximation_of_oppenheim_small_values hα hε
    (hoppenheim α hα hα_irr)

#print axioms erdos_496
#print axioms erdos_496_positive

end Erdos496
