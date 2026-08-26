import ErdosProblems.Erdos67b.LogPhaseSum
import Mathlib.NumberTheory.LSeries.Basic

/-!
# From logarithmic-phase block sums to Dirichlet-series blocks

This file is the finite, lossless summation-by-parts bridge used in the
high-height Dirichlet-series argument.  Its analytic input is deliberately
local: a bound for every raw prefix of one interval.  No assertion about
oscillatory sums is packaged as an unproved global proposition.

The final section separates a periodic Dirichlet character by its residue
classes.  Thus a uniform logarithmic-phase estimate in each residue class
immediately supplies the raw prefix estimate required by Abel summation.
-/

open scoped BigOperators

namespace Erdos67b.LSeriesLogPhaseBridge

noncomputable section

/-- The complex partial sum of `u` over the closed interval `[a,b]`. -/
def complexIntervalPartialSum (u : ℕ → ℂ) (a b : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc a b, u n

/-- Complex-valued finite Abel summation on a closed natural interval. -/
theorem sum_Icc_mul_eq_complexPartialSum
    (u : ℕ → ℂ) (w : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Finset.Icc a b, u n * (w n : ℂ) =
      complexIntervalPartialSum u a b * (w b : ℂ) +
        ∑ n ∈ Finset.Ico a b,
          complexIntervalPartialSum u a n * ((w n - w (n + 1) : ℝ) : ℂ) := by
  induction b with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      simp [complexIntervalPartialSum]
  | succ b ih =>
      by_cases hab' : a ≤ b
      · rw [Finset.sum_Icc_succ_top (by omega),
            Finset.sum_Ico_succ_top hab', ih hab']
        simp only [complexIntervalPartialSum,
          Finset.sum_Icc_succ_top (by omega)]
        push_cast
        ring
      · have ha : a = b + 1 := by omega
        subst a
        simp [complexIntervalPartialSum]

/-- The consecutive weight differences on `[a,b)` telescope. -/
theorem weight_add_sum_Ico_sub_succ (w : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    w b + ∑ n ∈ Finset.Ico a b, (w n - w (n + 1)) = w a := by
  induction b with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      simp
  | succ b ih =>
      by_cases hab' : a ≤ b
      · rw [Finset.sum_Ico_succ_top hab']
        calc
          w (b + 1) +
              ((∑ k ∈ Finset.Ico a b, (w k - w (k + 1))) +
                (w b - w (b + 1))) =
              w b + ∑ k ∈ Finset.Ico a b, (w k - w (k + 1)) := by ring
          _ = w a := ih hab'
      · have ha : a = b + 1 := by omega
        subst a
        simp

/-- If every raw prefix has norm at most `B`, multiplying by a nonnegative
decreasing real weight costs only the left endpoint weight. -/
theorem norm_sum_Icc_mul_le_of_prefix_bound
    (u : ℕ → ℂ) (w : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b)
    {B : ℝ} (hB : 0 ≤ B) (hwb : 0 ≤ w b)
    (hw : ∀ n ∈ Finset.Ico a b, w (n + 1) ≤ w n)
    (hprefix : ∀ n ∈ Finset.Icc a b,
      ‖complexIntervalPartialSum u a n‖ ≤ B) :
    ‖∑ n ∈ Finset.Icc a b, u n * (w n : ℂ)‖ ≤ B * w a := by
  rw [sum_Icc_mul_eq_complexPartialSum u w hab]
  calc
    ‖complexIntervalPartialSum u a b * (w b : ℂ) +
          ∑ n ∈ Finset.Ico a b,
            complexIntervalPartialSum u a n * ((w n - w (n + 1) : ℝ) : ℂ)‖ ≤
        ‖complexIntervalPartialSum u a b * (w b : ℂ)‖ +
          ‖∑ n ∈ Finset.Ico a b,
            complexIntervalPartialSum u a n *
              ((w n - w (n + 1) : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ B * w b + ∑ n ∈ Finset.Ico a b, B * (w n - w (n + 1)) := by
      apply add_le_add
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwb]
        exact mul_le_mul_of_nonneg_right
          (hprefix b (Finset.mem_Icc.mpr ⟨hab, le_rfl⟩)) hwb
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
        intro n hn
        have hdiff : 0 ≤ w n - w (n + 1) := sub_nonneg.mpr (hw n hn)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hdiff]
        exact mul_le_mul_of_nonneg_right
          (hprefix n (Finset.mem_Icc.mpr
            ⟨(Finset.mem_Ico.mp hn).1, (Finset.mem_Ico.mp hn).2.le⟩)) hdiff
    _ = B * (w b + ∑ n ∈ Finset.Ico a b, (w n - w (n + 1))) := by
      rw [← Finset.mul_sum]
      ring
    _ = B * w a := by rw [weight_add_sum_Ico_sub_succ w hab]

/-- Specialization of finite Abel summation to the weight `n⁻ˢ`. -/
theorem norm_sum_Icc_mul_rpow_neg_le_of_prefix_bound
    (u : ℕ → ℂ) {a b : ℕ} (ha : 0 < a) (hab : a ≤ b)
    {sigma B : ℝ} (hsigma : 0 ≤ sigma) (hB : 0 ≤ B)
    (hprefix : ∀ n ∈ Finset.Icc a b,
      ‖complexIntervalPartialSum u a n‖ ≤ B) :
    ‖∑ n ∈ Finset.Icc a b,
        u n * (((n : ℝ) ^ (-sigma) : ℝ) : ℂ)‖ ≤
      B * (a : ℝ) ^ (-sigma) := by
  apply norm_sum_Icc_mul_le_of_prefix_bound
    u (fun n ↦ (n : ℝ) ^ (-sigma)) hab hB
  · exact Real.rpow_nonneg (Nat.cast_nonneg b) _
  · intro n hn
    apply Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (neg_nonpos.mpr hsigma)
    · show 0 < (n : ℝ)
      exact_mod_cast (ha.trans_le (Finset.mem_Ico.mp hn).1)
    · show 0 < ((n + 1 : ℕ) : ℝ)
      exact_mod_cast Nat.zero_lt_succ n
    · exact_mod_cast Nat.le_succ n
  · exact hprefix

/-! ## Separating a Dirichlet character into residue classes -/

/-- The part of a finite sum lying in one residue class modulo `q`. -/
def residueClassSum {q : ℕ} (s : Finset ℕ) (a : ZMod q) (u : ℕ → ℂ) : ℂ :=
  (s.filter (fun n : ℕ ↦ (n : ZMod q) = a)).sum u

/-- Exact grouping of a character-twisted finite sum by residue classes. -/
theorem sum_mul_character_eq_sum_residueClassSum
    {q : ℕ} [NeZero q] (s : Finset ℕ) (u : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) :
    ∑ n ∈ s, u n * chi n =
      ∑ a : ZMod q, residueClassSum s a u * chi a := by
  classical
  calc
    ∑ n ∈ s, u n * chi n =
        ∑ a : ZMod q,
          (s.filter (fun n : ℕ ↦ (n : ZMod q) = a)).sum
            (fun n ↦ u n * chi n) :=
      (Finset.sum_fiberwise s (fun n : ℕ ↦ (n : ZMod q))
        (fun n ↦ u n * chi n)).symm
    _ = ∑ a : ZMod q, residueClassSum s a u * chi a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [residueClassSum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      have hna : (n : ZMod q) = a := (Finset.mem_filter.mp hn).2
      rw [← hna]

/-- Uniform raw bounds in every residue class give the character-twisted
raw bound, with the explicit loss `q`. -/
theorem norm_sum_mul_character_le_card_mul_of_residue_bounds
    {q : ℕ} [NeZero q] (s : Finset ℕ) (u : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) {B : ℝ} (hB : 0 ≤ B)
    (hresidue : ∀ a : ZMod q, ‖residueClassSum s a u‖ ≤ B) :
    ‖∑ n ∈ s, u n * chi n‖ ≤ q * B := by
  rw [sum_mul_character_eq_sum_residueClassSum s u chi]
  calc
    ‖∑ a : ZMod q, residueClassSum s a u * chi a‖ ≤
        ∑ a : ZMod q, ‖residueClassSum s a u * chi a‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _a : ZMod q, B := by
      apply Finset.sum_le_sum
      intro a ha
      rw [norm_mul]
      exact (mul_le_mul (hresidue a) (chi.norm_le_one a)
        (norm_nonneg _) hB).trans_eq (mul_one B)
    _ = q * B := by simp [mul_comm]

/-- Residue-class logarithmic-phase prefix bounds imply the weighted
Dirichlet-character block bound needed in the high-height argument. -/
theorem norm_character_logPhase_rpow_block_le_of_residue_prefix_bounds
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (t : ℝ)
    {a b : ℕ} (ha : 0 < a) (hab : a ≤ b)
    {sigma B : ℝ} (hsigma : 0 ≤ sigma) (hB : 0 ≤ B)
    (hresidue : ∀ n ∈ Finset.Icc a b, ∀ c : ZMod q,
      ‖residueClassSum (Finset.Icc a n) c
          (fun m ↦ LogPhaseSum.natLogTwist m t)‖ ≤ B) :
    ‖∑ n ∈ Finset.Icc a b,
        (LogPhaseSum.natLogTwist n t * chi n) *
          (((n : ℝ) ^ (-sigma) : ℝ) : ℂ)‖ ≤
      (q * B) * (a : ℝ) ^ (-sigma) := by
  apply norm_sum_Icc_mul_rpow_neg_le_of_prefix_bound
    (fun n ↦ LogPhaseSum.natLogTwist n t * chi n)
    ha hab hsigma (mul_nonneg (Nat.cast_nonneg q) hB)
  intro n hn
  unfold complexIntervalPartialSum
  exact norm_sum_mul_character_le_card_mul_of_residue_bounds
    (Finset.Icc a n) (fun m ↦ LogPhaseSum.natLogTwist m t) chi hB
    (hresidue n hn)

/-! ## Identification with Dirichlet-series terms -/

/-- At a positive integer, the Dirichlet-series term at `sigma + i*t`
splits into its logarithmic phase and its decreasing real weight. -/
theorem character_LSeries_term_eq_logPhase_mul_rpow
    {q n : ℕ} (chi : DirichletCharacter ℂ q) (t sigma : ℝ) (hn : 0 < n) :
    LSeries.term (fun m : ℕ ↦ chi m)
        ((sigma : ℂ) + Complex.I * (t : ℂ)) n =
      (LogPhaseSum.natLogTwist n t * chi n) *
        (((n : ℝ) ^ (-sigma) : ℝ) : ℂ) := by
  rw [LSeries.term_of_ne_zero hn.ne', div_eq_mul_inv,
    ← Complex.cpow_neg]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [show -((sigma : ℂ) + Complex.I * (t : ℂ)) =
      -(Complex.I * (t : ℂ)) + (-(sigma : ℝ) : ℂ) by
        push_cast
        ring,
    Complex.cpow_add _ _ hnC]
  have hreal :
      (n : ℂ) ^ (-(sigma : ℂ)) =
        (((n : ℝ) ^ (-sigma) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg]
    exact (Complex.ofReal_cpow (Nat.cast_nonneg n) (-sigma)).symm
  rw [hreal]
  unfold LogPhaseSum.natLogTwist LogPhaseSum.logPhase
  rw [show (((n : ℝ) : ℂ)) = (n : ℂ) by norm_cast]
  ring

/-- A raw prefix estimate for the character times logarithmic phase gives
the corresponding finite Dirichlet-series block estimate. -/
theorem norm_sum_character_LSeries_term_le_of_prefix_bound
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ)
    {a b : ℕ} (ha : 0 < a) (hab : a ≤ b)
    {sigma B : ℝ} (hsigma : 0 ≤ sigma) (hB : 0 ≤ B)
    (hprefix : ∀ n ∈ Finset.Icc a b,
      ‖complexIntervalPartialSum
          (fun m ↦ LogPhaseSum.natLogTwist m t * chi m) a n‖ ≤ B) :
    ‖∑ n ∈ Finset.Icc a b,
        LSeries.term (fun m : ℕ ↦ chi m)
          ((sigma : ℂ) + Complex.I * (t : ℂ)) n‖ ≤
      B * (a : ℝ) ^ (-sigma) := by
  rw [Finset.sum_congr rfl (fun n hn ↦
    character_LSeries_term_eq_logPhase_mul_rpow chi t sigma
      (ha.trans_le (Finset.mem_Icc.mp hn).1))]
  exact norm_sum_Icc_mul_rpow_neg_le_of_prefix_bound
    (fun n ↦ LogPhaseSum.natLogTwist n t * chi n)
    ha hab hsigma hB hprefix

/-- Fully separated version: it is enough to bound the raw logarithmic
phase in every residue class, for every prefix of the block. -/
theorem norm_sum_character_LSeries_term_le_of_residue_prefix_bounds
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (t : ℝ)
    {a b : ℕ} (ha : 0 < a) (hab : a ≤ b)
    {sigma B : ℝ} (hsigma : 0 ≤ sigma) (hB : 0 ≤ B)
    (hresidue : ∀ n ∈ Finset.Icc a b, ∀ c : ZMod q,
      ‖residueClassSum (Finset.Icc a n) c
          (fun m ↦ LogPhaseSum.natLogTwist m t)‖ ≤ B) :
    ‖∑ n ∈ Finset.Icc a b,
        LSeries.term (fun m : ℕ ↦ chi m)
          ((sigma : ℂ) + Complex.I * (t : ℂ)) n‖ ≤
      (q * B) * (a : ℝ) ^ (-sigma) := by
  rw [Finset.sum_congr rfl (fun n hn ↦
    character_LSeries_term_eq_logPhase_mul_rpow chi t sigma
      (ha.trans_le (Finset.mem_Icc.mp hn).1))]
  exact norm_character_logPhase_rpow_block_le_of_residue_prefix_bounds
    chi t ha hab hsigma hB hresidue

/-- Dyadic spelling of the preceding result.  This is the form consumed by
a blockwise high-height estimate. -/
theorem norm_sum_dyadic_character_LSeries_term_le_of_residue_prefix_bounds
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (t : ℝ)
    {A : ℕ} (hA : 0 < A) {sigma B : ℝ}
    (hsigma : 0 ≤ sigma) (hB : 0 ≤ B)
    (hresidue : ∀ n ∈ Finset.Icc A (2 * A), ∀ c : ZMod q,
      ‖residueClassSum (Finset.Icc A n) c
          (fun m ↦ LogPhaseSum.natLogTwist m t)‖ ≤ B) :
    ‖∑ n ∈ Finset.Icc A (2 * A),
        LSeries.term (fun m : ℕ ↦ chi m)
          ((sigma : ℂ) + Complex.I * (t : ℂ)) n‖ ≤
      (q * B) * (A : ℝ) ^ (-sigma) := by
  exact norm_sum_character_LSeries_term_le_of_residue_prefix_bounds
    chi t hA (by omega) hsigma hB hresidue

/-! ## Passage from finite blocks to an absolutely convergent L-series -/

/-- A shifted range is the corresponding closed interval.  The positivity
hypothesis removes the empty-range endpoint ambiguity. -/
theorem sum_range_nat_add_eq_sum_Icc
    (f : ℕ → ℂ) (a N : ℕ) (hN : 0 < N) :
    ∑ n ∈ Finset.range N, f (n + a) =
      ∑ n ∈ Finset.Icc a (a + N - 1), f n := by
  calc
    ∑ n ∈ Finset.range N, f (n + a) =
        ∑ n ∈ Finset.range ((a + N) - a), f (a + n) := by
      simp only [Nat.add_sub_cancel_left, add_comm]
    _ = ∑ n ∈ Finset.Ico a (a + N), f n :=
      (Finset.sum_Ico_eq_sum_range f a (a + N)).symm
    _ = ∑ n ∈ Finset.Icc a (a + N - 1), f n := by
      apply Finset.sum_congr
      · ext n
        simp only [Finset.mem_Ico, Finset.mem_Icc]
        omega
      · intros
        rfl

/-- A uniform estimate for all finite tails survives the limit defining a
summable series. -/
theorem norm_tsum_nat_add_le_of_Icc_bound
    (f : ℕ → ℂ) (hf : Summable f) {a : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hIcc : ∀ b, a ≤ b → ‖∑ n ∈ Finset.Icc a b, f n‖ ≤ B) :
    ‖∑' n : ℕ, f (n + a)‖ ≤ B := by
  have hshift : Summable (fun n : ℕ ↦ f (n + a)) :=
    (summable_nat_add_iff a).2 (by simpa [add_comm] using hf)
  have htend : Filter.Tendsto
      (fun N : ℕ ↦ ∑ n ∈ Finset.range N, f (n + a))
      Filter.atTop (nhds (∑' n : ℕ, f (n + a))) :=
    hshift.hasSum_iff_tendsto_nat.mp hshift.hasSum
  apply le_of_tendsto (tendsto_norm.comp htend)
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  change ‖∑ n ∈ Finset.range N, f (n + a)‖ ≤ B
  rw [sum_range_nat_add_eq_sum_Icc f a N (by omega)]
  exact hIcc (a + N - 1) (by omega)

/-- Finite-tail control gives an explicit approximation of a summable
series by its first `a` terms. -/
theorem norm_tsum_sub_sum_range_le_of_Icc_bound
    (f : ℕ → ℂ) (hf : Summable f) {a : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hIcc : ∀ b, a ≤ b → ‖∑ n ∈ Finset.Icc a b, f n‖ ≤ B) :
    ‖(∑' n : ℕ, f n) - ∑ n ∈ Finset.range a, f n‖ ≤ B := by
  have htail := norm_tsum_nat_add_le_of_Icc_bound f hf hB hIcc
  rw [← hf.sum_add_tsum_nat_add a]
  simpa only [add_sub_cancel_left] using htail

/-- Global raw prefix control for `chi(n)n⁻ⁱᵗ` controls the tail of the
Dirichlet L-series at `sigma+i*t`.  This is the exact limit version of the
finite Abel bridge above. -/
theorem norm_character_LSeries_sub_sum_range_le_of_prefix_bound
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ)
    {a : ℕ} (ha : 0 < a) {sigma B : ℝ} (hsigma : 1 < sigma)
    (hB : 0 ≤ B)
    (hprefix : ∀ n, a ≤ n →
      ‖complexIntervalPartialSum
          (fun m ↦ LogPhaseSum.natLogTwist m t * chi m) a n‖ ≤ B) :
    ‖LSeries (fun m : ℕ ↦ chi m)
          ((sigma : ℂ) + Complex.I * (t : ℂ)) -
        ∑ n ∈ Finset.range a,
          LSeries.term (fun m : ℕ ↦ chi m)
            ((sigma : ℂ) + Complex.I * (t : ℂ)) n‖ ≤
      B * (a : ℝ) ^ (-sigma) := by
  let s : ℂ := (sigma : ℂ) + Complex.I * (t : ℂ)
  have hs : 1 < s.re := by simp [s, hsigma]
  have hf : Summable (LSeries.term (fun m : ℕ ↦ chi m) s) := by
    exact LSeriesSummable_of_bounded_of_one_lt_re
      (fun n hn ↦ chi.norm_le_one n) hs
  have hIcc : ∀ b, a ≤ b →
      ‖∑ n ∈ Finset.Icc a b,
        LSeries.term (fun m : ℕ ↦ chi m) s n‖ ≤
          B * (a : ℝ) ^ (-sigma) := by
    intro b hab
    apply norm_sum_character_LSeries_term_le_of_prefix_bound
      chi t ha hab (by linarith) hB
    intro n hn
    exact hprefix n (Finset.mem_Icc.mp hn).1
  change ‖(∑' n : ℕ, LSeries.term (fun m : ℕ ↦ chi m) s n) -
      ∑ n ∈ Finset.range a,
        LSeries.term (fun m : ℕ ↦ chi m) s n‖ ≤ _
  exact norm_tsum_sub_sum_range_le_of_Icc_bound
    (LSeries.term (fun m : ℕ ↦ chi m) s) hf
    (mul_nonneg hB (Real.rpow_nonneg (Nat.cast_nonneg a) _)) hIcc

/-- Global residue-class prefix estimates imply the full L-series tail
estimate, with only the explicit factor `q` from grouping the classes. -/
theorem norm_character_LSeries_sub_sum_range_le_of_residue_prefix_bounds
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (t : ℝ)
    {a : ℕ} (ha : 0 < a) {sigma B : ℝ} (hsigma : 1 < sigma)
    (hB : 0 ≤ B)
    (hresidue : ∀ n, a ≤ n → ∀ c : ZMod q,
      ‖residueClassSum (Finset.Icc a n) c
          (fun m ↦ LogPhaseSum.natLogTwist m t)‖ ≤ B) :
    ‖LSeries (fun m : ℕ ↦ chi m)
          ((sigma : ℂ) + Complex.I * (t : ℂ)) -
        ∑ n ∈ Finset.range a,
          LSeries.term (fun m : ℕ ↦ chi m)
            ((sigma : ℂ) + Complex.I * (t : ℂ)) n‖ ≤
      (q * B) * (a : ℝ) ^ (-sigma) := by
  apply norm_character_LSeries_sub_sum_range_le_of_prefix_bound
    chi t ha hsigma (mul_nonneg (Nat.cast_nonneg q) hB)
  intro n hn
  unfold complexIntervalPartialSum
  exact norm_sum_mul_character_le_card_mul_of_residue_bounds
    (Finset.Icc a n) (fun m ↦ LogPhaseSum.natLogTwist m t) chi hB
    (hresidue n hn)

/-- The point `1 + 1/log Y + i*t` used in the truncated Euler-product
argument. -/
def nearOneLSeriesPoint (Y : ℕ) (t : ℝ) : ℂ :=
  ((1 + (Real.log (Y : ℝ))⁻¹ : ℝ) : ℂ) + Complex.I * (t : ℂ)

/-- Exact near-one specialization of the residue-class tail bridge.  The
cutoff `a` remains explicit, so the caller may take the integer cutoff near
`exp ((log Y)^(5/6))` without any hidden rounding convention. -/
theorem norm_character_LSeries_nearOne_sub_sum_range_le_of_residue_prefix_bounds
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (t : ℝ)
    {Y a : ℕ} (hY : 2 ≤ Y) (ha : 0 < a) {B : ℝ} (hB : 0 ≤ B)
    (hresidue : ∀ n, a ≤ n → ∀ c : ZMod q,
      ‖residueClassSum (Finset.Icc a n) c
          (fun m ↦ LogPhaseSum.natLogTwist m t)‖ ≤ B) :
    ‖LSeries (fun m : ℕ ↦ chi m) (nearOneLSeriesPoint Y t) -
        ∑ n ∈ Finset.range a,
          LSeries.term (fun m : ℕ ↦ chi m) (nearOneLSeriesPoint Y t) n‖ ≤
      (q * B) * (a : ℝ) ^ (-(1 + (Real.log (Y : ℝ))⁻¹)) := by
  have hlogY : 0 < Real.log (Y : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hsigma : 1 < 1 + (Real.log (Y : ℝ))⁻¹ := by
    have := inv_pos.mpr hlogY
    linarith
  simpa only [nearOneLSeriesPoint] using
    norm_character_LSeries_sub_sum_range_le_of_residue_prefix_bounds
      chi t ha hsigma hB hresidue

end

end Erdos67b.LSeriesLogPhaseBridge
