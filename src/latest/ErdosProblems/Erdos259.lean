/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 259.
https://www.erdosproblems.com/forum/thread/259

Informal authors:
- Yong-Gao Chen
- Imre Z. Ruzsa

Formal authors:
- Aristotle
- Stefano Rocca

URLs:
- https://www.erdosproblems.com/forum/thread/259#post-5683
- https://gist.githubusercontent.com/ster-oc/c7429943f6b3a634797dc8b2a3b01f2d/raw/8c6b5b7f08021f0aed2312542dd2e9ee7beaa6d6/Erdos259.lean
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/259.lean
-/
import Mathlib

namespace Erdos259

/-!
# Erdős Problem 259

This file proves that the Möbius series $\sum_{n=1}^{\infty} \mu(n)^2 \cdot n / 2^n$
is irrational (Erdős Problem 259), using the Chen–Ruzsa irrationality criterion.

## Main definitions

- `squarefreeSeq`: the increasing enumeration of squarefree natural numbers.
- `IsRFree`: a natural number is `r`-free if no perfect `r`-th power greater than 1 divides it.
- `IsSquarefull`: a natural number is squarefull if every prime divisor appears with
  exponent at least 2.

## Main statements

- `ChenRusza_Lemma1`: an irrationality criterion for series of the form
  `∑ b_n · l^{-a_n}`.
- `ChenRusza_Theorem4`: if `(a_n)` is a sequence of distinct positive integers, each
  either `r`-free or squarefull, then `∑ a_n · l^{-a_n}` is irrational for every `l ≥ 2`.
- `Erdos259`: the Möbius series `∑ μ(n)² · n / 2^n` is irrational.

## Tags

irrationality, Möbius function, squarefree, Erdős
-/

open scoped BigOperators
open ArithmeticFunction

noncomputable section

set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
set_option linter.flexible false
set_option linter.style.multiGoal false
set_option linter.style.refine false
set_option linter.style.whitespace false


/-! # Chapter 1: Definitions -/

/-- Definition 1.1: The increasing enumeration of squarefree natural numbers,
defined via `Nat.nth` applied to the predicate `Squarefree`. -/
def squarefreeSeq : ℕ → ℕ := Nat.nth (fun n => Squarefree n)

/-- A natural number is `r`-free if no perfect `r`-th power greater than 1 divides it. -/
def IsRFree (r : ℕ) (n : ℕ) : Prop := ∀ d : ℕ, d ^ r ∣ n → IsUnit d

/-- A natural number is squarefull if every prime divisor appears with exponent at least 2. -/
def IsSquarefull (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-! # Chapter 2: Chen–Ruzsa -/

/-! ## Helpers for Lemma 2.1 -/

/-- An integer-valued sequence tending to zero is eventually zero. -/
private lemma int_tendsto_zero_eventually_zero (f : ℕ → ℤ)
    (htend : Filter.Tendsto (fun n => (f n : ℝ)) Filter.atTop (nhds 0)) :
    ∀ᶠ n in Filter.atTop, f n = 0 := by
  norm_num [ Metric.tendsto_nhds ] at htend
  exact Filter.eventually_atTop.mpr (by
    rcases htend 1 zero_lt_one with ⟨N, hN⟩
    exact ⟨N, fun n hn => by
      norm_cast at hN
      simpa [sub_eq_iff_eq_add] using hN n hn⟩)

/-- If `∑ b_n / l^{a_n} = v / u` is rational and u > 0, then
`u * ∑_{a_n > C} b_n / l^{a_n - C}` is an integer for any C.
Summability is an implicit assumption in the mathematical statement. -/
private lemma rational_tail_integer
    (l : ℕ) (hl : l ≥ 2)
    (a : ℕ → ℕ) (b : ℕ → ℤ)
    (u : ℤ) (hu : 0 < u) (v : ℤ)
    (hS : Summable (fun n => (b n : ℝ) / (l : ℝ) ^ (a n)))
    (hrat : (∑' n, (b n : ℝ) / (l : ℝ) ^ (a n)) = (v : ℝ) / (u : ℝ))
    (C : ℕ) :
    ∃ m : ℤ, (u : ℝ) * (∑' n, if a n > C
      then (b n : ℝ) / (l : ℝ) ^ (a n - C) else 0) = (m : ℝ) := by
  by_contra h_contra
  -- The low part is a convergent series of integers.
  have h_low_part_int :
      ∃ m : ℤ,
        (∑' n, if a n ≤ C then (b n : ℝ) * l ^ (C - a n) else 0) = m := by
    have h_int_tendsto_zero_eventually_zero :
        ∀ f : ℕ → ℤ, Summable (fun n => (f n : ℝ)) →
          ∃ N, ∀ n ≥ N, f n = 0 := by
      intros f hf; exact (by
      have := hf.tendsto_atTop_zero
      have := int_tendsto_zero_eventually_zero f this; aesop;)
    have h_low_part_int :
        Summable (fun n =>
          if a n ≤ C then (b n : ℝ) * l ^ (C - a n) else 0) := by
      have h_low_part_int :
          Summable (fun n =>
            if a n ≤ C then (b n : ℝ) / l ^ (a n) * l ^ C else 0) := by
        have h_int_tendsto_zero_eventually_zero :
            Summable (fun n => (b n : ℝ) / l ^ (a n) * l ^ C) := by
          exact hS.mul_right _
        have h_abs_le :
            ∀ n,
              |(if a n ≤ C then (b n : ℝ) / l ^ (a n) * l ^ C else 0)|
                ≤ |(b n : ℝ) / l ^ (a n) * l ^ C| := by
          intro n; split_ifs <;> simp; positivity
        -- Apply the comparison test with the original series.
        have h_comparison :
            Summable (fun n =>
              |(if a n ≤ C then (b n : ℝ) / l ^ (a n) * l ^ C else 0)|) := by
          exact Summable.of_nonneg_of_le
            (fun n => abs_nonneg _) h_abs_le h_int_tendsto_zero_eventually_zero.abs
        exact h_comparison.of_abs
      convert h_low_part_int using 2 ; split_ifs <;> ring_nf
      rw [show (l : ℝ) ^ C = l ^ (C - a ‹_›) * l ^ a ‹_› by
        rw [← pow_add, Nat.sub_add_cancel ‹_›]]
      ring_nf
      norm_num [show l ≠ 0 by linarith]
    obtain ⟨N, hN⟩ := h_int_tendsto_zero_eventually_zero
      (fun n => if a n ≤ C then b n * l ^ (C - a n) else 0)
      (by exact_mod_cast h_low_part_int)
    rw [ tsum_eq_sum ]
    any_goals exact Finset.range N
    · exact ⟨∑ n ∈ Finset.range N,
          if a n ≤ C then b n * l ^ (C - a n) else 0, by
        push_cast
        rfl⟩
    · exact fun n hn => mod_cast hN n ( le_of_not_gt fun h => hn <| Finset.mem_range.mpr h )
  obtain ⟨ m, hm ⟩ := h_low_part_int
  -- Multiply both sides of the equation by $u * l^C$.
  have h_mul :
      u * l ^ C * (∑' n, (b n : ℝ) / l ^ (a n)) =
        u * (∑' n, if a n ≤ C
          then (b n : ℝ) * l ^ (C - a n) else 0)
        + u * (∑' n, if a n > C
          then (b n : ℝ) / l ^ (a n - C) else 0) := by
    rw [ ← mul_add, ← Summable.tsum_add ]
    · rw [← tsum_mul_left] ; rw [← tsum_mul_left] ; congr ; ext n
      split_ifs <;> simp_all [Nat.sub_eq_zero_of_le] ; ring_nf
      · linarith
      · field_simp
        rw [ mul_assoc, ← pow_add, Nat.add_sub_of_le ‹_›, mul_comm ]
      · field_simp
        rw [mul_right_comm, ← pow_add, Nat.add_sub_of_le (le_of_lt ‹_›)] ; ring_nf
    · have h_low_part_int :
          Summable (fun n =>
            if a n ≤ C then (b n : ℝ) / l ^ (a n) else 0) := by
        have h_abs :
            ∀ n,
              |(if a n ≤ C then (b n : ℝ) / l ^ (a n) else 0)|
                ≤ |(b n : ℝ) / l ^ (a n)| := by
          intro n; split_ifs <;> norm_num
        -- Apply the comparison test with the summable series ∑' n, |(b n : ℝ) / l ^ (a n)|.
        have h_comparison :
            Summable (fun n =>
              |(if a n ≤ C then (b n : ℝ) / l ^ (a n) else 0)|) := by
          exact Summable.of_nonneg_of_le (fun n => abs_nonneg _) h_abs hS.abs
        exact h_comparison.of_abs
      convert h_low_part_int.mul_left ( l ^ C : ℝ ) using 2 ; split_ifs <;> ring_nf
      rw [show (l : ℝ) ^ C = l ^ (C - a ‹_›) * l ^ a ‹_› by
        rw [← pow_add, Nat.sub_add_cancel ‹_›]]
      ring_nf
      norm_num [show l ≠ 0 by linarith]
    · contrapose! h_contra
      exact ⟨0, by
        rw [tsum_eq_zero_of_not_summable h_contra]
        norm_num⟩
  simp_all [ mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ]
  exact h_contra (v * l ^ C - m * u) (by
    push_cast
    nlinarith [mul_inv_cancel_left₀
      (by positivity : (u : ℝ) ≠ 0) (v * l ^ C)])

/-- The full integrality claim: if the series is rational, then u * E_k is an integer.
This combines rational_tail_integer with the d_k correction terms.

**Note:** The hypothesis `ha_inj` (injectivity of `a`) was added to the original statement
to ensure that the set `{n | C < a n ∧ a n ≤ C + t_val}` is finite, which is needed
for the algebraic manipulation of the correction terms. -/
private lemma ChenRusza_Lemma1_integrality
    (l : ℕ) (hl : l ≥ 2)
    (a : ℕ → ℕ) (ha_inj : Function.Injective a) (b : ℕ → ℤ)
    (u : ℤ) (hu : 0 < u) (v : ℤ)
    (hSum : Summable (fun n => (b n : ℝ) / (l : ℝ) ^ (a n)))
    (hrat : (∑' n, (b n : ℝ) / (l : ℝ) ^ (a n)) = (v : ℝ) / (u : ℝ))
    (C d_val t_val : ℕ) :
    ∃ m : ℤ, (u : ℝ) * ((∑' n, if a n > C
        then ((b n : ℝ) - (d_val : ℝ) * (l : ℝ) ^ t_val) / (l : ℝ) ^ (a n - C)
        else 0)
      + (∑' n, if a n > C + t_val
        then (d_val : ℝ) / (l : ℝ) ^ (a n - C - t_val)
        else 0)) = (m : ℝ) := by
  -- Let's simplify the expression inside the sum.
  have h_simplify :
      (∑' n, if a n > C
        then (b n - d_val * l ^ t_val : ℝ) / l ^ (a n - C)
        else 0)
        + (∑' n, if a n > C + t_val
          then (d_val : ℝ) / l ^ (a n - C - t_val)
          else 0)
      =
        (∑' n, if a n > C then (b n : ℝ) / l ^ (a n - C) else 0)
        - ∑' n, if C < a n ∧ a n ≤ C + t_val
          then (d_val : ℝ) * l ^ (t_val - (a n - C))
          else 0 := by
    rw [ ← Summable.tsum_add ]
    · rw [← Summable.tsum_sub]
      congr
      ext n
      split_ifs <;> ring_nf <;> norm_num at *
      any_goals omega
      · rw [show a n - C = (a n - C - t_val) + t_val by
          rw [tsub_add_cancel_of_le (Nat.le_sub_of_add_le <| by linarith)]]
        ring_nf
        simp [ show l ≠ 0 by linarith, mul_comm, mul_left_comm ]
      · field_simp
        rw [ mul_assoc, ← pow_add, Nat.add_sub_of_le (by omega ) ]
      · refine' .of_norm _
        refine' Summable.of_nonneg_of_le (fun n => by positivity) (fun n => _)
          (hSum.norm.mul_left (l ^ C : ℝ))
        split_ifs <;> simp_all [ div_eq_mul_inv, mul_left_comm ]
        · field_simp
          rw [ mul_assoc, ← pow_add, Nat.sub_add_cancel ( le_of_lt ‹_› ) ]
        · positivity
      · -- Since $a$ is injective, the set $\{n \mid C < a n \land a n ≤ C + t_val\}$ is finite.
        have h_finite : Set.Finite {n | C < a n ∧ a n ≤ C + t_val} := by
          exact Set.Finite.preimage (fun n => by aesop ) ( Set.finite_Ioc C ( C + t_val ) )
        refine' summable_of_ne_finset_zero _
        exacts [ h_finite.toFinset, fun n hn => if_neg <| by simpa using hn ]
    · have h_summable :
          Summable (fun n =>
            ((b n : ℝ) - d_val * l ^ t_val) / (l : ℝ) ^ (a n)) := by
        simp_all [ sub_div ]
        refine Summable.sub hSum ?_
        exact Summable.mul_left _ <| by
          simpa using
            summable_geometric_of_lt_one (by positivity)
              (inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr hl) |>
              Summable.comp_injective <| ha_inj
      rw [ ← summable_norm_iff ] at *
      refine' .of_nonneg_of_le (fun n => norm_nonneg _) (fun n => _)
        (h_summable.mul_left (l ^ C : ℝ))
      split_ifs <;> norm_num
      · rw [ mul_div, div_le_div_iff₀ ] <;> first | positivity | ring_nf
        rw [ ← pow_add, Nat.add_sub_of_le (by linarith ) ]
      · positivity
    · -- The second series is controlled by a geometric series with common ratio `1/l`.
      have h_geo_series : Summable (fun n => (d_val : ℝ) / l ^ (a n - C - t_val)) := by
        have h_geo_series : Summable (fun n => (1 : ℝ) / l ^ (a n - C - t_val)) := by
          have h_geo_series : Summable (fun n => (1 : ℝ) / l ^ (a n)) := by
            have h_geo_series : Summable (fun n => (1 : ℝ) / l ^ n) := by
              simpa using summable_geometric_of_lt_one (by positivity)
                (inv_lt_one_of_one_lt₀ (by norm_cast))
            exact h_geo_series.comp_injective ha_inj
          have h_geo_series : Summable (fun n => (1 : ℝ) / l ^ (a n - (C + t_val))) := by
            have h_shift :
                ∀ n,
                  (1 : ℝ) / l ^ (a n - (C + t_val)) ≤
                    (1 : ℝ) / l ^ (a n) * l ^ (C + t_val) := by
              intro n; by_cases h : a n ≥ C + t_val <;> simp_all [ pow_add ]
              · rw [inv_mul_eq_div, inv_eq_one_div, div_le_div_iff₀] <;>
                  norm_cast <;>
                  first | positivity | ring_nf
                rw [ ← pow_add, ← pow_add, add_tsub_cancel_of_le h ]
              · norm_num [ Nat.sub_eq_zero_of_le h.le ]
                rw [ inv_mul_eq_div, one_le_div (by positivity ) ]
                rw [ ← pow_add ] ; exact pow_le_pow_right₀ (by norm_cast; linarith ) h.le
            exact Summable.of_nonneg_of_le (fun n => by positivity) h_shift
              (h_geo_series.mul_right _)
          simpa only [ Nat.sub_sub ] using h_geo_series
        simpa using h_geo_series.mul_left _
      exact Summable.of_nonneg_of_le (fun n => by positivity)
        (fun n => by split_ifs <;> first | positivity | aesop) h_geo_series
  -- We'll use that $u \cdot \sum_{a_n > C} \frac{b_n}{l^{a_n-C}}$ is an integer.
  have h_int :
      ∃ m : ℤ,
        u * ∑' n, (if a n > C
          then (b n : ℝ) / l ^ (a n - C) else 0) = m := by
    convert rational_tail_integer l hl a b u hu v hSum hrat C using 1
  -- The correction term is an integer because its support is finite.
  have h_int2 :
      ∃ m : ℤ,
        u * ∑' n, (if C < a n ∧ a n ≤ C + t_val
          then (d_val : ℝ) * l ^ (t_val - (a n - C))
          else 0) = m := by
    -- The set is finite since `a` is injective.
    have h_finite : Set.Finite {n | C < a n ∧ a n ≤ C + t_val} := by
      exact Set.Finite.preimage (fun n => by aesop ) ( Set.finite_Icc ( C + 1 ) ( C + t_val ) )
    rw [ tsum_eq_sum ]
    any_goals exact h_finite.toFinset
    · exact ⟨ _, by norm_cast ⟩
    · aesop
  exact ⟨h_int.choose - h_int2.choose, by
    push_cast
    linear_combination' h_simplify * u + h_int.choose_spec - h_int2.choose_spec⟩

/- Lemma 2.1 (Chen–Ruzsa Lemma 1). An irrationality criterion for series of the form
`∑ b_n · l^{-a_n}`: if a certain tail expression is nonzero and tends to zero,
then the series is irrational. -/
theorem ChenRusza_Lemma1 (l : ℕ) (hl : l ≥ 2) (a : ℕ → ℕ) (ha_inj : Function.Injective a)
    (b : ℕ → ℤ) (hSummable : Summable (fun n => (b n : ℝ) / (l : ℝ) ^ (a n)))
    (c : ℕ → ℕ) (d : ℕ → ℕ) (t : ℕ → ℕ)
    (hS : ∀ k,
      (∑' n, if a n > c k
        then ((b n : ℝ) - (d k : ℝ) * (l : ℝ) ^ (t k)) / (l : ℝ) ^ (a n - c k)
        else 0)
      + (∑' n, if a n > c k + t k
        then (d k : ℝ) / (l : ℝ) ^ (a n - c k - t k)
        else 0) ≠ 0)
    (hTend : Filter.Tendsto (fun k =>
      (∑' n, if a n > c k
        then ((b n : ℝ) - (d k : ℝ) * (l : ℝ) ^ (t k)) / (l : ℝ) ^ (a n - c k)
        else 0)
      + (∑' n, if a n > c k + t k
        then (d k : ℝ) / (l : ℝ) ^ (a n - c k - t k)
        else 0))
      Filter.atTop (nhds 0)) :
    Irrational (∑' n, (b n : ℝ) / (l : ℝ) ^ (a n)) := by
  intro h
  obtain ⟨q, hq⟩ := h
  -- By ChenRusza_Lemma1_integrality, `q.den * E_k` is an integer for all `k`.
  have h_integrality :
      ∀ k, ∃ m : ℤ,
        (q.den : ℝ) *
          ((∑' n, if a n > c k
            then ((b n : ℝ) - (d k : ℝ) * (l : ℝ) ^ t k) /
              (l : ℝ) ^ (a n - c k)
            else 0)
          + (∑' n, if a n > c k + t k
            then (d k : ℝ) / (l : ℝ) ^ (a n - c k - t k)
            else 0)) = (m : ℝ) := by
    intro k
    convert ChenRusza_Lemma1_integrality l hl a ha_inj b q.den
      (Nat.cast_pos.mpr q.pos) q.num hSummable
      (by simpa [Rat.cast_def] using hq.symm) (c k) (d k) (t k) using 1
  choose m hm using h_integrality
  -- Since $m_k$ is an integer and $q.den \cdot E_k$ tends to zero, $m_k$ must also tend to zero.
  have h_mk_zero : Filter.Tendsto (fun k => (m k : ℝ)) Filter.atTop (nhds 0) := by
    simpa [ ← hm ] using hTend.const_mul _
  have := int_tendsto_zero_eventually_zero (fun k => m k ) h_mk_zero
  obtain ⟨ k, hk ⟩ := this.exists; specialize hm k; specialize hS k; simp_all

/- Lemma 2.2 (Chen–Ruzsa Lemma 3). For nonneg integers `a, b, r` and
a prime `q` not dividing `l`, there exists `n_r` with
`a * l^{n_r} + n_r + b ≡ 0 (mod q^r)` and `n_r ≡ 0 (mod q-1)`. -/
theorem ChenRusza_Lemma3 (l : ℕ)  (a b r : ℕ) (q : ℕ) (hq : q.Prime) (hql : ¬(q ∣ l)) :
    ∃ nr : ℕ, (a * l ^ nr + nr + b) % (q ^ r) = 0 ∧ nr % (q - 1) = 0 := by
  induction r with
  | zero => exact ⟨ 0, Nat.mod_one _, Nat.zero_mod _ ⟩
  | succ r ih =>
    obtain ⟨nr, hnr⟩ := ih
    obtain ⟨k, hk⟩ :
        ∃ k : ℕ,
          (a * l ^ (nr + k * (q - 1) * q ^ r)
              + (nr + k * (q - 1) * q ^ r) + b) %
            q ^ (r + 1) = 0 := by
      have h_euler : l ^ ((q - 1) * q ^ r) ≡ 1 [MOD q ^ (r + 1)] := by
        have h_euler : l ^ Nat.totient (q ^ (r + 1)) ≡ 1 [MOD q ^ (r + 1)] := by
          exact Nat.ModEq.pow_totient <| Nat.Coprime.gcd_eq_one <|
            Nat.Coprime.pow_right _ <| Nat.Coprime.symm <|
              hq.coprime_iff_not_dvd.mpr hql
        simp_all [ Nat.totient_prime_pow ]
        rwa [ Nat.mul_comm ]
      have h_subst :
          ∃ k : ℕ,
            (a * l ^ nr + nr + b + k * (q - 1) * q ^ r) %
              q ^ (r + 1) = 0 := by
        obtain ⟨m, hm⟩ : ∃ m : ℕ, a * l ^ nr + nr + b = m * q ^ r := by
          exact exists_eq_mul_left_of_dvd <| Nat.dvd_of_mod_eq_zero hnr.1
        obtain ⟨k, hk⟩ : ∃ k : ℕ, m + k * (q - 1) ≡ 0 [MOD q] := by
          haveI := Fact.mk hq; simp [ ← ZMod.natCast_eq_natCast_iff ]
          norm_num [ hq.pos ]
          exact ⟨ m, by ring ⟩
        use k
        rw [ Nat.mod_eq_zero_of_dvd ]
        convert Nat.mul_dvd_mul ( Nat.dvd_of_mod_eq_zero hk ) ( dvd_refl ( q ^ r ) ) using 1 ; ring
        linarith [hm]
      obtain ⟨ k, hk ⟩ := h_subst; use k; simp_all [ ← ZMod.val_natCast, pow_add, pow_mul' ]
      simp_all [ ← ZMod.natCast_eq_natCast_iff ]
      linear_combination' hk
    exact ⟨nr + k * (q - 1) * q ^ r, hk, Nat.mod_eq_zero_of_dvd <|
      dvd_add (Nat.dvd_of_mod_eq_zero hnr.2) <|
        dvd_mul_of_dvd_left (dvd_mul_left _ _) _⟩

/-! ## Helpers for Lemma 2.3 -/

/-- For any m > 0, there exists a prime p such that m ∣ (p + 1),
i.e. p ≡ -1 (mod m). Follows from Dirichlet's theorem. -/
private lemma exists_prime_neg_one_mod (m : ℕ) (hm : 1 < m) :
    ∃ p : ℕ, p.Prime ∧ m ∣ (p + 1) := by
  -- Dirichlet gives infinitely many primes congruent to `-1` modulo `m`.
  have h_dirichlet : Set.Infinite {p : ℕ | Nat.Prime p ∧ p ≡ -1 [ZMOD m]} := by
    convert Nat.infinite_setOf_prime_and_eq_mod (show IsUnit ( -1 : ZMod m ) from ?_ ) using 1
    · norm_num [ ← ZMod.intCast_eq_intCast_iff ]
    · exact ⟨ by linarith ⟩
    · exact isUnit_iff_exists_inv.mpr ⟨ -1, by ring ⟩
  exact Exists.elim h_dirichlet.nonempty fun p hp => ⟨p, hp.1, by
    simpa [← Int.natCast_dvd_natCast] using hp.2.symm.dvd⟩

/- Lemma 2.3. There exists a sequence of primes `p_0, p_1, …` such that
each `p_i` does not divide `2l`, consecutive primes satisfy
`p_{i+1} ≡ -1 (mod p_0 ⋯ p_i)`, and `gcd(p_i - 1, p_j) = 1` for all `i, j`. -/
theorem primeSequence_for_ChenRusza (l : ℕ) (hl : l ≥ 2) :
    ∃ p : ℕ → ℕ,
      (∀ i, (p i).Prime) ∧
      (∀ i, ¬(p i ∣ 2 * l)) ∧
      (∀ i, (∏ j ∈ Finset.range (i + 1), p j) ∣ (p (i + 1) + 1)) ∧
      (∀ i j, Nat.Coprime (p i - 1) (p j)) := by
  by_contra! H
  -- Define the sequence $p$ recursively.
  have hp_exists :
      ∃ p : ℕ → ℕ,
        (∀ i, Nat.Prime (p i)) ∧
        (∀ i, ¬p i ∣ 2 * l) ∧
        (∀ i, (∏ j ∈ Finset.range (i + 1), p j) ∣ (p (i + 1) + 1)) := by
    have h_rec :
        ∀ (P : ℕ), 0 < P →
          ∃ p : ℕ, Nat.Prime p ∧ ¬(p ∣ 2 * l) ∧ P ∣ (p + 1) := by
      intro P hP_pos
      obtain ⟨p, hp_prime, hp_div⟩ :
          ∃ p : ℕ, Nat.Prime p ∧ p ≡ -1 [ZMOD (P * (2 * l))] := by
        have := exists_prime_neg_one_mod ( P * ( 2 * l ) ) ?_
        · exact ⟨this.choose, this.choose_spec.1, Int.ModEq.symm <|
            Int.modEq_of_dvd <| by
              simpa [← Int.natCast_dvd_natCast] using this.choose_spec.2⟩
        · nlinarith
      refine' ⟨ p, hp_prime, _, _ ⟩
      · rintro ⟨ k, hk ⟩
        rcases k with ( _ | _ | k ) <;> simp_all [ Int.ModEq ]
        · subst hk; norm_num [ Int.emod_eq_emod_iff_emod_sub_eq_zero ] at hp_div
          exact Nat.not_prime_mul (by linarith ) (by linarith ) hp_prime
        · rw [ Int.emod_eq_emod_iff_emod_sub_eq_zero ] at hp_div ; norm_num at hp_div
          nlinarith [ Int.le_of_dvd (by positivity ) hp_div, show P > 0 by positivity ]
      · exact Int.natCast_dvd_natCast.mp (by
          simpa using hp_div.symm.dvd |> dvd_trans (dvd_mul_right _ _))
    choose! p hp₁ hp₂ hp₃ using h_rec
    use fun i => p ( Nat.recOn i 1 fun i hi => hi * p hi )
    refine' ⟨ fun i => hp₁ _ _, fun i => hp₂ _ _, fun i => _ ⟩
    · induction i <;> simp [ *, Nat.Prime.pos ]
    · induction i <;> simp [ *, Nat.Prime.pos ]
    · convert hp₃ (Nat.rec 1 (fun i hi => hi * p hi) (i + 1))
        (Nat.recOn (i + 1) (by norm_num) fun i hi =>
          Nat.mul_pos hi (Nat.Prime.pos (hp₁ _ hi))) using 1
      induction i <;> simp_all [ Finset.prod_range_succ ]
  obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := hp_exists
  specialize H p hp₁ hp₂ hp₃
  obtain ⟨i, j, hgcd⟩ := H
  refine' hgcd _
  rcases lt_trichotomy i j with hij | rfl | hij <;> simp_all
  · -- Since `p_i ∣ p_j + 1`, it follows that `p_i ∣ p_j - 1`.
    have h_div : p i ∣ (p j + 1) := by
      induction hij <;> simp_all [ Finset.prod_range_succ ]
      · exact dvd_of_mul_left_dvd ( hp₃ i )
      · exact dvd_trans
          (dvd_mul_of_dvd_left
            (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr ‹_›)) _)
          (hp₃ _)
    have := Nat.gcd_dvd_left (p i - 1) (p j)
    have := Nat.gcd_dvd_right (p i - 1) (p j)
    simp only [Nat.dvd_prime (hp₁ j)] at *
    simp_all
    have :=
      Nat.le_of_dvd (Nat.sub_pos_of_lt (Nat.Prime.one_lt (hp₁ i)))
        ‹p j ∣ p i - 1›
    (have := Nat.le_of_dvd (Nat.succ_pos _) h_div
     norm_num at *)
    cases this.eq_or_lt <;> simp_all
    · cases Nat.Prime.eq_two_or_odd (hp₁ i) <;>
        cases Nat.Prime.eq_two_or_odd (hp₁ j) <;>
        simp_all +arith [Nat.add_mod]
      exact hp₂ j (by norm_num [ * ] )
    · linarith [
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.Prime.ne_zero (hp₁ i)))]
  · exact hgcd (by simp [ Nat.one_le_iff_ne_zero, Nat.Prime.ne_zero ( hp₁ i ) ] )
  · -- Since $j < i$, we have $p_j \mid (p_i + 1)$.
    have h_div : p j ∣ (p i + 1) := by
      have h_div_pi : p j ∣ (∏ k ∈ Finset.range i, p k) := by
        exact Finset.dvd_prod_of_mem _ ( Finset.mem_range.mpr hij )
      exact dvd_trans h_div_pi (by cases i <;> simp_all [ Finset.prod_range_succ ] )
    -- The gcd divides the difference between `p_i + 1` and `p_i - 1`.
    have h_gcd : Nat.gcd (p i - 1) (p j) ∣ 2 := by
      have h_gcd : Nat.gcd (p i - 1) (p j) ∣ Nat.gcd (p i - 1) (p i + 1) := by
        exact Nat.dvd_gcd ( Nat.gcd_dvd_left _ _ ) ( Nat.dvd_trans ( Nat.gcd_dvd_right _ _ ) h_div )
      exact h_gcd.trans (by
        convert Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _) using 1
        rw [Nat.sub_eq_of_eq_add]
        linarith [
          Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr <| Nat.Prime.ne_zero <| hp₁ i)])
    have h_dvd := Nat.gcd_dvd_right (p i - 1) (p j)
    rw [ Nat.dvd_prime (hp₁ j) ] at h_dvd
    rcases h_dvd with h1 | h1
    · -- gcd = 1
      exact hgcd h1
    · exact hp₂ j (dvd_mul_of_dvd_left (h1 ▸ h_gcd) _)

/-- Helper: If p is prime and p^r | n with r ≥ 1, then n is not r-free. -/
private lemma not_rfree_of_prime_pow_dvd {r : ℕ} {n p : ℕ}
    (hp : p.Prime) (hdvd : p ^ r ∣ n) :
    ¬ IsRFree r n := fun h => hp.not_isUnit <| h p hdvd

/-- Helper: If p is prime, p | n, and p^2 ∤ n, then n is not squarefull. -/
private lemma not_squarefull_of_prime_dvd_sq_not {n p : ℕ}
    (hp : p.Prime) (hdvd : p ∣ n) (hndvd : ¬(p ^ 2 ∣ n)) :
    ¬ IsSquarefull n := fun h => hndvd <| h p hp hdvd

/-
Helper: For N integers starting at c+1, we can make each one neither r-free
nor squarefull by CRT using 2N distinct primes.
-/
private lemma consecutive_non_rfree_non_squarefull (r : ℕ) (N : ℕ) :
    ∃ c : ℕ,
      ∀ i : ℕ, 1 ≤ i → i ≤ N →
        ¬(IsRFree r (c + i) ∨ IsSquarefull (c + i)) := by
  -- Choose $2N$ distinct primes $q_1, \ldots, q_N, s_1, \ldots, s_N$ all ≥ 3.
  obtain ⟨q, hq⟩ :
      ∃ q : ℕ → ℕ,
        (∀ i, Nat.Prime (q i)) ∧
        (∀ i, 3 ≤ q i) ∧
        (∀ i j, i ≠ j → q i ≠ q j) := by
    use fun i => Nat.nth Nat.Prime ( i + 2 );
    refine' ⟨ fun i => Nat.prime_nth_prime _, fun i => _, fun i j hij => _ ⟩;
    · exact Nat.lt_of_le_of_lt (Nat.Prime.two_le <| Nat.prime_nth_prime _)
        (Nat.nth_strictMono Nat.infinite_setOf_prime <| Nat.lt_succ_self _);
    · exact fun h => hij <| by have := Nat.nth_injective ( Nat.infinite_setOf_prime ) h; aesop;
  obtain ⟨s, hs⟩ :
      ∃ s : ℕ → ℕ,
        (∀ i, Nat.Prime (s i)) ∧
        (∀ i, 3 ≤ s i) ∧
        (∀ i j, i ≠ j → s i ≠ s j) ∧
        (∀ i, s i ∉ Finset.image q (Finset.range N)) := by
    have h_inf_primes :
        Set.Infinite
          {p : ℕ | Nat.Prime p ∧ 3 ≤ p ∧ p ∉ Finset.image q (Finset.range N)} := by
      exact Set.Infinite.diff (Nat.infinite_setOf_prime.diff (Set.finite_le_nat 2))
        (Finset.finite_toSet (Finset.image q (Finset.range N))) |>
          Set.Infinite.mono fun p hp => by aesop;
    have := h_inf_primes.exists_gt;
    exact ⟨
      fun i => Nat.recOn i (Nat.find <| this 0) fun i hi => Nat.find <| this hi,
      fun i => Nat.recOn i (Nat.find_spec (this 0) |>.1.1) fun i hi =>
        Nat.find_spec (this _) |>.1.1,
      fun i => Nat.recOn i (Nat.find_spec (this 0) |>.1.2.1) fun i hi =>
        Nat.find_spec (this _) |>.1.2.1,
      fun i j hij => fun h => hij <| by
        simpa using StrictMono.injective
          (strictMono_nat_of_lt_succ fun i => Nat.find_spec (this _) |>.2) h,
      fun i => Nat.recOn i (Nat.find_spec (this 0) |>.1.2.2) fun i hi =>
        Nat.find_spec (this _) |>.1.2.2⟩;
  -- Use CRT to find `c` with the requested congruences for `i = 0, ..., N - 1`.
  obtain ⟨c, hc⟩ :
      ∃ c : ℕ, ∀ i ∈ Finset.range N,
        (c + (i + 1) ≡ 0 [MOD q i ^ r]) ∧
        (c + (i + 1) ≡ s i [MOD s i ^ 2]) := by
    -- Applying the Chinese Remainder Theorem.
    have h_crt :
        ∀ i ∈ Finset.range N,
          ∃ x, x ≡ - (i + 1) [ZMOD q i ^ r] ∧
            x ≡ s i - (i + 1) [ZMOD s i ^ 2] := by
      intro i hi
      have h_coprime : Nat.gcd (q i ^ r) (s i ^ 2) = 1 := by
        simp_all [ Nat.coprime_pow_primes ];
      have := Nat.chineseRemainder h_coprime;
      obtain ⟨k, hk₁, hk₂⟩ := this
        (Int.toNat (-(i + 1) % (q i ^ r)))
        (Int.toNat ((s i - (i + 1)) % (s i ^ 2)))
      use k
      simp_all [← Int.natCast_modEq_iff]
      simp_all [Int.ModEq,
        Int.emod_nonneg _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr
          (Nat.Prime.ne_zero (hq.1 i)))),
        Int.emod_nonneg _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr
          (Nat.Prime.ne_zero (hs.1 i))))];
    choose! x hx₁ hx₂ using h_crt;
    -- Let $c$ be a common solution to the system of congruences.
    obtain ⟨c, hc⟩ :
        ∃ c : ℤ, ∀ i ∈ Finset.range N,
          c ≡ x i [ZMOD (q i ^ r * s i ^ 2)] := by
      have h_crt :
          ∀ i ∈ Finset.range N, ∃ y : ℤ,
            y ≡ x i [ZMOD (q i ^ r * s i ^ 2)] ∧
            ∀ j ∈ Finset.range N, j ≠ i →
              y ≡ 0 [ZMOD (q j ^ r * s j ^ 2)] := by
        -- Let `y_i` be the CRT basis element for the `i`th modulus.
        intros i hi
        obtain ⟨y_i, hy_i⟩ :
            ∃ y_i : ℤ,
              y_i * (∏ j ∈ Finset.erase (Finset.range N) i,
                (q j ^ r * s j ^ 2)) ≡ 1 [ZMOD (q i ^ r * s i ^ 2)] := by
          have h_coprime :
              Nat.gcd
                (∏ j ∈ Finset.erase (Finset.range N) i, (q j ^ r * s j ^ 2))
                (q i ^ r * s i ^ 2) = 1 := by
            refine' Nat.Coprime.prod_left _;
            simp_all [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right, Nat.coprime_primes ];
            intro j hj₁ hj₂
            have := Nat.coprime_primes (hq.1 j) (hq.1 i)
            have := Nat.coprime_primes (hs.1 j) (hq.1 i)
            have := Nat.coprime_primes (hq.1 j) (hs.1 i)
            simp_all;
            exact ⟨⟨Nat.Coprime.pow _ _ ‹_›, Nat.Coprime.pow_right _ <|
              by tauto⟩, Nat.Coprime.pow_left _ ‹_›⟩;
          have := Nat.gcd_eq_gcd_ab
            (∏ j ∈ Finset.erase (Finset.range N) i, q j ^ r * s j ^ 2)
            (q i ^ r * s i ^ 2);
          exact ⟨Nat.gcdA _ _, Int.modEq_iff_dvd.mpr ⟨Nat.gcdB _ _, by
            push_cast at *
            linarith⟩⟩;
        use y_i * (∏ j ∈ Finset.erase (Finset.range N) i, (q j ^ r * s j ^ 2)) * x i;
        exact ⟨by simpa using hy_i.mul_right _, fun j hj hij =>
          Int.modEq_zero_iff_dvd.mpr <| dvd_mul_of_dvd_left
            (dvd_mul_of_dvd_right
              (mod_cast Finset.dvd_prod_of_mem _ <| by aesop) _) _⟩;
      choose! y hy₁ hy₂ using h_crt;
      use ∑ i ∈ Finset.range N, y i;
      intro i hi; simp_all only [Int.ModEq];
      rw [ Finset.sum_int_mod, Finset.sum_eq_single i ] <;> aesop;
    refine' ⟨Int.toNat (c % ∏ i ∈ Finset.range N, (q i ^ r * s i ^ 2)),
      fun i hi => ⟨_, _⟩⟩ <;> simp_all [← Int.natCast_modEq_iff];
    · rw [max_eq_left (Int.emod_nonneg _ <| Finset.prod_ne_zero_iff.mpr
        fun _ _ => mul_ne_zero
          (pow_ne_zero _ <| Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| hq.1 _)
          (pow_ne_zero _ <| Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| hs.1 _))];
      simp_all [ Int.ModEq ];
      rw [ Int.dvd_iff_emod_eq_zero ]
      simp [Finset.prod_eq_prod_diff_singleton_mul (Finset.mem_range.mpr hi),
        Int.add_emod]
      rw [ Int.emod_emod_of_dvd _ ( dvd_mul_of_dvd_right ( dvd_mul_right _ _ ) _ ) ] ; simp_all ;
      rw [ Int.dvd_iff_emod_eq_zero ]
      specialize hc i hi
      specialize hx₁ i hi
      specialize hx₂ i hi
      simp_all [ Int.emod_eq_emod_iff_emod_sub_eq_zero ] ;
      convert dvd_add ( dvd_trans ( dvd_mul_right _ _ ) hc ) hx₁ using 1 ; ring;
    · rw [max_eq_left (Int.emod_nonneg _ <| Finset.prod_ne_zero_iff.mpr
        fun _ _ => mul_ne_zero
          (pow_ne_zero _ <| Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| hq.1 _)
          (pow_ne_zero _ <| Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| hs.1 _))];
      simp_all [ Int.ModEq ];
      rw [Int.add_emod, Int.emod_emod_of_dvd _
        (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hi) |> dvd_trans (by norm_num))];
      have := hc i hi
      replace := congr_arg (· % (s i : ℤ) ^ 2) this
      norm_num [Int.add_emod, Int.mul_emod] at *
      aesop;
  use c;
  intro i hi₁ hi₂
  specialize hc (i - 1)
  rcases i <;> simp_all [Nat.modEq_zero_iff_dvd] ;
  constructor;
  · exact not_rfree_of_prime_pow_dvd ( hq.1 _ ) hc.1;
  · intro H
    have := H (s ‹_›) (hs.1 _)
    simp_all [Nat.ModEq, Nat.dvd_iff_mod_eq_zero] ;
    exact absurd
      (this (Nat.mod_eq_zero_of_dvd <| Nat.dvd_of_mod_eq_zero <| by
        rw [← Nat.mod_mod_of_dvd _ (dvd_pow_self _ two_ne_zero), hc.2]
        norm_num [Nat.mod_eq_of_lt (show s _ < s _ ^ 2 from
          lt_self_pow₀ (hs.1 _ |> Nat.Prime.one_lt) (by linarith))]))
      (by
        rw [Nat.mod_eq_of_lt (show s _ < s _ ^ 2 from
          lt_self_pow₀ (hs.1 _ |> Nat.Prime.one_lt) (by linarith))]
        exact Nat.ne_of_gt <| Nat.Prime.pos <| hs.1 _)

set_option maxHeartbeats 600000 in
/-- Helper: For any k ≥ 1, there exist h > 0 and M > 0 such that for any m divisible by M,
all numbers in (h·l^m, h·l^m + k] are neither r-free nor squarefull.
Uses CRT + Euler's theorem. -/
private lemma first_interval_periodic
    (r : ℕ) (l : ℕ) (hl : l ≥ 2) (k : ℕ) (hk : k ≥ 1) :
    ∃ h M : ℕ, 0 < h ∧ 0 < M ∧
      ∀ m : ℕ, M ∣ m →
        ∀ n : ℕ, h * l ^ m < n → n ≤ h * l ^ m + k →
          ¬(IsRFree r n ∨ IsSquarefull n) := by
  -- Let `p` be the sequence of primes from `primeSequence_for_ChenRusza l hl`.
  obtain ⟨p, hp_prime, hp_not_dvd_2l, hp_div, hp_coprime⟩ :
      ∃ p : ℕ → ℕ,
        (∀ i, Nat.Prime (p i)) ∧
        (∀ i, ¬(p i ∣ 2 * l)) ∧
        (∀ i, (∏ j ∈ Finset.range (i + 1), p j) ∣ (p (i + 1) + 1)) ∧
        (∀ i j, Nat.Coprime (p i - 1) (p j)) := primeSequence_for_ChenRusza l hl
  -- Choose 2k distinct primes from the sequence `p`.
  obtain ⟨P, Q, hPQ_distinct, hPQ_prime⟩ :
      ∃ P Q : Fin k → ℕ,
        (∀ i, Nat.Prime (P i)) ∧
        (∀ i, Nat.Prime (Q i)) ∧
        (∀ i, P i ≠ Q i) ∧
        (∀ i j, i ≠ j → P i ≠ P j) ∧
        (∀ i j, i ≠ j → Q i ≠ Q j) ∧
        (∀ i j, P i ≠ Q j) ∧
        (∀ i, ¬(P i ∣ 2 * l)) ∧
        (∀ i, ¬(Q i ∣ 2 * l)) := by
    -- Choose 2k distinct primes from the sequence `p`.
    obtain ⟨P, hP_distinct⟩ :
        ∃ P : Fin (2 * k) → ℕ,
          (∀ i, Nat.Prime (P i)) ∧
          (∀ i, ¬(P i ∣ 2 * l)) ∧
          (∀ i j, i ≠ j → P i ≠ P j) := by
      have h_inf_primes : Set.Infinite {q : ℕ | Nat.Prime q ∧ ¬(q ∣ 2 * l)} := by
        exact Set.Infinite.mono (by aesop_cat)
          (Nat.infinite_setOf_prime.diff
            (Set.finite_iff_bddAbove.mpr
              ⟨2 * l, fun q hq => Nat.le_of_dvd (by positivity) hq⟩))
      have := h_inf_primes.exists_subset_card_eq ( 2 * k )
      obtain ⟨t, ht⟩ := this
      exact ⟨fun i => t.orderEmbOfFin (by aesop) i,
        fun i => ht.1 (by aesop) |>.1,
        fun i => ht.1 (by aesop) |>.2,
        fun i j hij => by
          contrapose! hij
          aesop⟩
    use fun i => P ⟨i.val, by linarith [Fin.is_lt i]⟩
    use fun i => P ⟨i.val + k, by linarith [Fin.is_lt i]⟩
    refine ⟨fun i => hP_distinct.1 _, fun i => hP_distinct.1 _,
      fun i => hP_distinct.2.2 _ _ ?_,
      fun i j h => hP_distinct.2.2 _ _ ?_,
      fun i j h => hP_distinct.2.2 _ _ ?_,
      fun i j => hP_distinct.2.2 _ _ ?_,
      fun i => hP_distinct.2.1 _, fun i => hP_distinct.2.1 _⟩ <;>
      simp [Fin.ext_iff] <;> omega
  -- Choose `h` with the two required families of congruences.
  obtain ⟨h, hh⟩ :
      ∃ h : ℕ,
        (∀ i : Fin k, h ≡ -i.val - 1 [ZMOD P i ^ r]) ∧
        (∀ i : Fin k, h ≡ Q i - i.val - 1 [ZMOD Q i ^ 2]) ∧
        0 < h := by
    -- By CRT, there exists an integer `h` satisfying the congruences.
    obtain ⟨h, hh⟩ :
        ∃ h : ℤ,
          (∀ i : Fin k, h ≡ -i.val - 1 [ZMOD P i ^ r]) ∧
          (∀ i : Fin k, h ≡ Q i - i.val - 1 [ZMOD Q i ^ 2]) := by
      -- Applying the Chinese Remainder Theorem.
      have h_crt :
          ∀ i : Fin k, ∃ x : ℤ,
            x ≡ -↑↑i - 1 [ZMOD ↑(P i) ^ r] ∧
            x ≡ ↑(Q i) - ↑↑i - 1 [ZMOD ↑(Q i) ^ 2] ∧
            ∀ j : Fin k, j ≠ i →
              x ≡ 0 [ZMOD ↑(P j) ^ r] ∧
              x ≡ 0 [ZMOD ↑(Q j) ^ 2] := by
        intro i
        obtain ⟨x, hx⟩ :
            ∃ x : ℤ,
              x ≡ -↑↑i - 1 [ZMOD ↑(P i) ^ r] ∧
              x ≡ ↑(Q i) - ↑↑i - 1 [ZMOD ↑(Q i) ^ 2] := by
          -- Such an `x` exists because `P_i^r` and `Q_i^2` are coprime.
          have h_coprime : Nat.Coprime (P i ^ r) (Q i ^ 2) := by
            exact Nat.coprime_pow_primes _ _ (hPQ_distinct i)
              (hPQ_prime.1 i) (hPQ_prime.2.1 i)
          have := Nat.chineseRemainder h_coprime
          obtain ⟨x, hx₁, hx₂⟩ := this
            (Int.toNat ((-↑↑i - 1) % (P i ^ r)))
            (Int.toNat ((Q i - ↑↑i - 1) % (Q i ^ 2)))
          use x
          simp_all [← Int.natCast_modEq_iff]
          simp_all [Int.ModEq,
            Int.emod_nonneg _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr
              (Nat.Prime.ne_zero (hPQ_distinct i)))),
            Int.emod_nonneg _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr
              (Nat.Prime.ne_zero (hPQ_prime.1 i))))]
        -- Let `y` be the CRT basis inverse for the `i`th pair of moduli.
        obtain ⟨y, hy⟩ :
            ∃ y : ℤ,
              y * (∏ j ∈ Finset.univ.erase i, (P j : ℤ) ^ r) *
                (∏ j ∈ Finset.univ.erase i, (Q j : ℤ) ^ 2)
                ≡ 1 [ZMOD (P i : ℤ) ^ r * (Q i : ℤ) ^ 2] := by
          have h_coprime :
              Int.gcd
                ((∏ j ∈ Finset.univ.erase i, (P j : ℤ) ^ r) *
                  (∏ j ∈ Finset.univ.erase i, (Q j : ℤ) ^ 2))
                ((P i : ℤ) ^ r * (Q i : ℤ) ^ 2) = 1 := by
            simp_all [Int.gcd, Int.natAbs_mul, Nat.coprime_mul_iff_left,
              Nat.coprime_mul_iff_right]
            norm_cast ; simp_all [ Nat.coprime_prod_left_iff, Nat.coprime_primes ]
            exact ⟨
              ⟨fun j hj => Nat.coprime_pow_primes _ _ (hPQ_distinct j)
                (hPQ_distinct i) (hPQ_prime.2.2.1 j i hj),
              fun j hj => Nat.Coprime.pow_right _ <| Nat.Coprime.symm <|
                hPQ_distinct i |> Nat.Prime.coprime_iff_not_dvd |>.2 <| fun h =>
                  hPQ_prime.2.2.2.2.1 i j <| by
                    have := Nat.prime_dvd_prime_iff_eq (hPQ_distinct i)
                      (hPQ_prime.1 j)
                    tauto⟩,
              fun j hj => Nat.Coprime.pow_left _ <| Nat.Coprime.symm <|
                hPQ_prime.1 i |> Nat.Prime.coprime_iff_not_dvd |>.2 <| fun h =>
                  hPQ_prime.2.2.2.2.1 j i <| by
                    have := Nat.prime_dvd_prime_iff_eq (hPQ_prime.1 i)
                      (hPQ_distinct j)
                    tauto⟩
          have := Int.gcd_eq_gcd_ab
            ((∏ j ∈ Finset.univ.erase i, (P j : ℤ) ^ r) *
              ∏ j ∈ Finset.univ.erase i, (Q j : ℤ) ^ 2)
            ((P i : ℤ) ^ r * (Q i : ℤ) ^ 2)
          exact ⟨Int.gcdA _ _, Int.modEq_iff_dvd.mpr ⟨Int.gcdB _ _, by
            push_cast [h_coprime] at this
            linarith⟩⟩
        use x * y * (∏ j ∈ Finset.univ.erase i, (P j : ℤ) ^ r) *
          (∏ j ∈ Finset.univ.erase i, (Q j : ℤ) ^ 2)
        refine' ⟨ _, _, _ ⟩
        · simpa [ mul_assoc ] using hx.1.mul ( hy.of_dvd <| dvd_mul_right _ _ )
        · have := hy.of_dvd ( dvd_mul_left _ _ ) ; simp_all [ mul_assoc ]
          simpa using hx.2.mul this
        · intro j hj; simp_all [ mul_assoc, Int.ModEq ]
          exact ⟨
            dvd_mul_of_dvd_right
              (dvd_mul_of_dvd_right
                (dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ (by aesop)) _) _) _,
            dvd_mul_of_dvd_right
              (dvd_mul_of_dvd_right
                (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (by aesop)) _) _) _⟩
      choose f hf₁ hf₂ hf₃ using h_crt; use ∑ i, f i; simp_all
      simp_all [ Int.ModEq ]
      simp [ Finset.sum_int_mod ]
      constructor <;> intro i <;> rw [ Finset.sum_eq_single i ] <;> simp_all
      · exact fun j hj => hf₃ j i ( Ne.symm hj ) |>.1
      · exact fun j hj => hf₃ _ _ ( Ne.symm hj ) |>.2
    refine' ⟨
      Int.toNat
        (h % (∏ i : Fin k, (P i ^ r : ℤ) * (Q i ^ 2 : ℤ)) +
          ∏ i : Fin k, (P i ^ r : ℤ) * (Q i ^ 2 : ℤ)), _, _, _⟩ <;>
      simp_all [Int.ModEq]
    · intro i
      rw [max_eq_left (add_nonneg
        (Int.emod_nonneg _ <| Finset.prod_ne_zero_iff.mpr fun _ _ =>
          mul_ne_zero
            (pow_ne_zero _ <| Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <|
              hPQ_distinct _)
            (pow_ne_zero _ <| Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <|
              hPQ_prime.1 _))
        (Finset.prod_nonneg fun _ _ => mul_nonneg
          (pow_nonneg (Nat.cast_nonneg _) _)
          (pow_nonneg (Nat.cast_nonneg _) _)))]
      simp [← hh.1 i, Int.add_emod, Int.mul_emod,
        Finset.prod_eq_prod_diff_singleton_mul <| Finset.mem_univ i]
      rw [ Int.emod_emod_of_dvd _ ( dvd_mul_of_dvd_right ( dvd_mul_right _ _ ) _ ) ]
    · intro i
      rw [max_eq_left (add_nonneg
        (Int.emod_nonneg _ <| Finset.prod_ne_zero_iff.mpr fun _ _ =>
          mul_ne_zero
            (pow_ne_zero _ <| Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <|
              hPQ_distinct _)
            (pow_ne_zero _ <| Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <|
              hPQ_prime.1 _))
        (Finset.prod_nonneg fun _ _ => mul_nonneg
          (pow_nonneg (Nat.cast_nonneg _) _)
          (pow_nonneg (Nat.cast_nonneg _) _)))]
      simp [← hh.2 i, Int.add_emod, Int.mul_emod,
        Finset.prod_eq_prod_diff_singleton_mul <| Finset.mem_univ i]
      rw [ Int.emod_emod_of_dvd _ ( dvd_mul_of_dvd_right ( dvd_mul_left _ _ ) _ ) ]
    · exact add_pos_of_nonneg_of_pos
        (Int.emod_nonneg _ <| Finset.prod_ne_zero_iff.mpr fun i _ =>
          mul_ne_zero
            (pow_ne_zero _ <| Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <|
              hPQ_distinct i)
            (pow_ne_zero _ <| Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <|
              hPQ_prime.1 i))
        (Finset.prod_pos fun i _ => mul_pos
          (pow_pos (Nat.cast_pos.mpr <| Nat.Prime.pos <| hPQ_distinct i) _)
          (pow_pos (Nat.cast_pos.mpr <| Nat.Prime.pos <| hPQ_prime.1 i) _))
  -- Choose $M$ such that $l^M \equiv 1 \pmod{P_i^r}$ and $l^M \equiv 1 \pmod{Q_i^2}$ for each $i$.
  obtain ⟨M, hM⟩ :
      ∃ M : ℕ, 0 < M ∧
        (∀ i : Fin k, l ^ M ≡ 1 [ZMOD P i ^ r]) ∧
        (∀ i : Fin k, l ^ M ≡ 1 [ZMOD Q i ^ 2]) := by
    -- Euler's theorem gives the two prime-power congruences.
    have h_euler :
        ∀ i : Fin k,
          l ^ Nat.totient (P i ^ r) ≡ 1 [ZMOD P i ^ r] ∧
          l ^ Nat.totient (Q i ^ 2) ≡ 1 [ZMOD Q i ^ 2] := by
      intros i
      have h_coprime_P : Nat.Coprime l (P i ^ r) := by
        exact Nat.Coprime.pow_right _ <| Nat.Coprime.symm <|
          hPQ_distinct i |> Nat.Prime.coprime_iff_not_dvd |>.2 fun h =>
            hPQ_prime.2.2.2.2.2.1 i <| dvd_mul_of_dvd_right h _
      have h_coprime_Q : Nat.Coprime l (Q i ^ 2) := by
        exact Nat.Coprime.pow_right _ <| Nat.Coprime.symm <|
          hPQ_prime.1 i |> Nat.Prime.coprime_iff_not_dvd |>.2 fun h =>
            hPQ_prime.2.2.2.2.2.2 i <| dvd_mul_of_dvd_right h _
      exact ⟨
        by simpa [← Int.natCast_modEq_iff] using
          Nat.ModEq.pow_totient h_coprime_P,
        by simpa [← Int.natCast_modEq_iff] using
          Nat.ModEq.pow_totient h_coprime_Q⟩
    use ∏ i : Fin k, Nat.totient (P i ^ r) * Nat.totient (Q i ^ 2)
    refine' ⟨Finset.prod_pos fun i _ => mul_pos
      (Nat.totient_pos.mpr (pow_pos (Nat.Prime.pos (hPQ_distinct i)) _))
      (Nat.totient_pos.mpr (pow_pos (Nat.Prime.pos (hPQ_prime.1 i)) _)), _, _⟩
    · intro i
      specialize h_euler i
      have hdiv :
          Nat.totient (P i ^ r) ∣
            ∏ j : Fin k, Nat.totient (P j ^ r) * Nat.totient (Q j ^ 2) := by
        exact dvd_trans (dvd_mul_right _ _) (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
      obtain ⟨q, hq⟩ := hdiv
      rw [hq, pow_mul]
      simpa using h_euler.1.pow q
    · intro i
      specialize h_euler i
      have hdiv :
          Nat.totient (Q i ^ 2) ∣
            ∏ j : Fin k, Nat.totient (P j ^ r) * Nat.totient (Q j ^ 2) := by
        exact dvd_trans (dvd_mul_left _ _) (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
      obtain ⟨q, hq⟩ := hdiv
      rw [hq, pow_mul]
      simpa using h_euler.2.pow q
  refine' ⟨ h, M, hh.2.2, hM.1, fun m hm n hn₁ hn₂ => _ ⟩
  -- Let $i$ be such that $n = h * l^m + (i + 1)$.
  obtain ⟨i, hi⟩ : ∃ i : Fin k, n = h * l ^ m + (i.val + 1) := by
    exact ⟨ ⟨ n - h * l ^ m - 1, by omega ⟩, by norm_num; omega ⟩
  -- Then $n \equiv 0 \pmod{P_i^r}$ and $n \equiv Q_i \pmod{Q_i^2}$.
  have hn_mod_P : (P i) ^ r ∣ n := by
    have hn_mod_P : (P i) ^ r ∣ (h * l ^ m + (i.val + 1)) := by
      have h_cong : h * l ^ m + (i.val + 1) ≡ 0 [ZMOD (P i) ^ r] := by
        have h_cong : l ^ m ≡ 1 [ZMOD (P i) ^ r] := by
          obtain ⟨ c, rfl ⟩ := hm; simpa [ pow_mul ] using Int.ModEq.pow _ ( hM.2.1 i )
        exact Int.ModEq.add (Int.ModEq.mul (hh.1 i) h_cong) rfl |>
          Int.ModEq.trans <| Int.modEq_zero_iff_dvd.mpr <| by
            ring_nf
            norm_num
      exact_mod_cast Int.dvd_of_emod_eq_zero h_cong
    aesop
  have hn_mod_Q : (Q i) ∣ n ∧ ¬((Q i) ^ 2 ∣ n) := by
    have hn_mod_Q : n ≡ Q i [ZMOD (Q i) ^ 2] := by
      have hn_mod_Q : l ^ m ≡ 1 [ZMOD (Q i) ^ 2] := by
        obtain ⟨ c, rfl ⟩ := hm; simpa [ pow_mul ] using hM.2.2 i |> Int.ModEq.pow _
      simp_all
      convert Int.ModEq.add ( Int.ModEq.mul ( hh.2.1 i ) hn_mod_Q ) rfl using 1 ; ring
    rw [← Int.natCast_dvd_natCast]
    simp_all [Int.ModEq, Int.emod_eq_emod_iff_emod_sub_eq_zero]
    obtain ⟨a, ha⟩ := hn_mod_Q
    exact ⟨⟨a * Q i + 1, by linarith⟩, fun ⟨b, hb⟩ => by
      nlinarith [
        show a = b by nlinarith [Nat.Prime.one_lt (hPQ_prime.1 i)],
        Nat.Prime.one_lt (hPQ_prime.1 i)]⟩
  exact not_or.mpr ⟨not_rfree_of_prime_pow_dvd (hPQ_distinct i) hn_mod_P,
    not_squarefull_of_prime_dvd_sq_not (hPQ_prime.1 i) hn_mod_Q.1 hn_mod_Q.2⟩

/-- Helper: If p is prime, p ∤ l, and m ≡ n (mod p^s * (p-1)), then l^m ≡ l^n (mod p^s).
This follows from Euler's theorem. -/
private lemma euler_pow_cong (l p s m n : ℕ) (hp : p.Prime) (hpl : ¬(p ∣ l))
    (hs : s ≥ 1) (hmod : m ≡ n [MOD p ^ s * (p - 1)]) :
    l ^ m ≡ l ^ n [MOD p ^ s] := by
  -- By Euler's theorem, since $p \nmid l$, we have $l^{\varphi(p^s)} \equiv 1 \pmod{p^s}$.
  have h_euler : l ^ Nat.totient (p ^ s) ≡ 1 [MOD p ^ s] := by
    exact Nat.ModEq.pow_totient <| Nat.Coprime.gcd_eq_one <|
      Nat.Coprime.pow_right _ <| Nat.Coprime.symm <|
        hp.coprime_iff_not_dvd.mpr hpl
  -- Since $m \equiv n \pmod{p^s(p-1)}$, we have $m \equiv n \pmod{\varphi(p^s)}$.
  have h_mod : m ≡ n [MOD Nat.totient (p ^ s)] := by
    rw [ Nat.totient_prime_pow hp hs ]
    exact hmod.of_dvd <| mul_dvd_mul ( pow_dvd_pow _ <| Nat.pred_le _ ) dvd_rfl
  rw [← Nat.mod_add_div m (Nat.totient (p ^ s)),
    ← Nat.mod_add_div n (Nat.totient (p ^ s)), h_mod]
  simp_all [ ← ZMod.natCast_eq_natCast_iff, pow_add, pow_mul ]

/-- The prime sequence from `primeSequence_for_ChenRusza` is strictly increasing. -/
private lemma primeSeq_strictMono (p : ℕ → ℕ)
    (hp1 : ∀ i, (p i).Prime) (hp2 : ∀ i, ¬(p i ∣ 2 * l))
    (hp3 : ∀ i, (∏ j ∈ Finset.range (i + 1), p j) ∣ (p (i + 1) + 1)) :
    StrictMono p := by
  refine' strictMono_nat_of_lt_succ _
  intro n
  have := hp3 n
  rw [ Finset.prod_range_succ ] at this
  have h_prod_div : p n ∣ p (n + 1) + 1 := by
    exact dvd_of_mul_left_dvd this
  by_cases h_eq : p n = p (n + 1) + 1
  · cases Nat.Prime.eq_two_or_odd (hp1 n) <;>
      cases Nat.Prime.eq_two_or_odd (hp1 (n + 1)) <;>
      simp_all +arith [Nat.add_mod]
    · exact Nat.Prime.ne_one ( hp1 _ ) h_eq
    · exact hp2 ( n + 1 ) (by norm_num [ * ] )
  · cases lt_or_gt_of_ne h_eq <;> simp_all
    · cases lt_or_eq_of_le ‹_› <;> simp_all
      exact Nat.Prime.ne_one ( hp1 _ ) ‹_›
    · exact absurd (Nat.le_of_dvd (Nat.succ_pos _) this) (by
        nlinarith [Nat.Prime.two_le (hp1 n), Nat.Prime.two_le (hp1 (n + 1)),
          show ∏ x ∈ Finset.range n, p x > 0 from
            Finset.prod_pos fun i hi => Nat.Prime.pos (hp1 i)])

/-- Multi-modulus CRT with divisibility constraint.
Given pairwise coprime moduli and a modulus L coprime to all of them,
find m divisible by L satisfying all CRT conditions. -/
private lemma multi_crt (nn : ℕ) (mods targets : Fin nn → ℕ) (L : ℕ) (_ : 0 < L)
    (hmods : ∀ i, 0 < mods i) (hcop : ∀ i j, i ≠ j → Nat.Coprime (mods i) (mods j))
    (hcop_L : ∀ i, Nat.Coprime L (mods i)) :
    ∃ m : ℕ, L ∣ m ∧ ∀ i, m ≡ targets i [MOD mods i] := by
  revert hcop
  -- Let's choose any solution $m$ modulo the product of the moduli.
  intro hcop
  have h_exists : ∃ m, (∀ i, m ≡ targets i [MOD mods i]) ∧ m ≡ 0 [MOD L] := by
    induction nn with
    | zero => exact ⟨ 0, by simp [ Nat.modEq_zero_iff_dvd ] ⟩
    | succ nn ih =>
      obtain ⟨m, hm₁, hm₂⟩ := ih (fun i => mods i.succ)
        (fun i => targets i.succ) (fun i => hmods _) (fun i => hcop_L _)
        (fun i j hij => hcop _ _ (by simpa [Fin.ext_iff] using hij))
      -- CRT gives `x` with the first congruence and the recursive combined one.
      obtain ⟨x, hx₁, hx₂⟩ :
          ∃ x, x ≡ targets 0 [MOD mods 0] ∧
            x ≡ m [MOD L * ∏ i : Fin nn, mods i.succ] := by
        have h_crt : Nat.Coprime (mods 0) (L * ∏ i : Fin nn, mods i.succ) := by
          exact Nat.Coprime.mul_right (Nat.Coprime.symm (hcop_L 0))
            (Nat.Coprime.prod_right fun i _ =>
              hcop 0 i.succ (ne_of_lt (Fin.succ_pos i)))
        have := Nat.chineseRemainder h_crt
        exact ⟨ _, this _ _ |>.2 ⟩
      refine' ⟨ x, Fin.forall_fin_succ.mpr ⟨ hx₁, fun i => _ ⟩, _ ⟩
      · exact Eq.trans
          (hx₂.of_dvd <|
            dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ <| Finset.mem_univ _) _)
          (hm₁ i)
      · exact hx₂.of_dvd ( dvd_mul_right _ _ ) |> Nat.ModEq.trans <| hm₂
  exact ⟨h_exists.choose, Nat.dvd_of_mod_eq_zero h_exists.choose_spec.2,
    h_exists.choose_spec.1⟩

set_option maxHeartbeats 600000 in
/-- Given `h > 0` and `M > 0`, there exists `m` divisible by `M` such that
all numbers in `(h·l^m + m, h·l^m + m + k + h]` are neither `r`-free nor
squarefull. Uses `ChenRusza_Lemma3` and CRT. -/
private lemma second_interval_exists
    (r : ℕ) (hr : r ≥ 2) (l : ℕ) (hl : l ≥ 2)
    (h : ℕ) (hh : 0 < h) (M : ℕ) (hM : 0 < M) (k : ℕ) (hk : k ≥ 1) :
    ∃ m : ℕ, M ∣ m ∧
      ∀ n : ℕ, h * l ^ m + m < n → n ≤ h * l ^ m + m + k + h →
        ¬(IsRFree r n ∨ IsSquarefull n) := by
  obtain ⟨p, hp1, hp2, hp3, hp4⟩ := primeSequence_for_ChenRusza l hl
  -- Since p is strictly monotone, we can choose N₀ such that p(N₀ + i) > M for all i.
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ i, p (N₀ + i) > M := by
    have h_unbounded : Filter.Tendsto p Filter.atTop Filter.atTop := by
      have h_unbounded : StrictMono p := by
        apply primeSeq_strictMono p hp1 hp2 hp3
      exact h_unbounded.tendsto_atTop
    exact Filter.eventually_atTop.mp (h_unbounded.eventually_gt_atTop M) |>
      fun ⟨N₀, hN₀⟩ => ⟨N₀, fun i => hN₀ _ (Nat.le_add_right _ _)⟩
  -- Apply ChenRusza_Lemma3 to get nr and ns for each j.
  obtain ⟨nr, ns, hnr, hns⟩ :
      ∃ nr ns : Fin (k + h) → ℕ,
        (∀ j,
          (h * l ^ (nr j) + nr j + (j.val + 1)) %
              (p (N₀ + 2 * j) ^ r) = 0 ∧
            nr j % (p (N₀ + 2 * j) - 1) = 0) ∧
        (∀ j,
          (h * l ^ (ns j) + ns j +
                (j.val + 1 + p (N₀ + 2 * j + 1) ^ 2 -
                  p (N₀ + 2 * j + 1))) %
              (p (N₀ + 2 * j + 1) ^ 2) = 0 ∧
            ns j % (p (N₀ + 2 * j + 1) - 1) = 0) := by
    have hnr :
        ∀ j : Fin (k + h), ∃ nr : ℕ,
          (h * l ^ nr + nr + (j.val + 1)) % (p (N₀ + 2 * j) ^ r) = 0 ∧
          nr % (p (N₀ + 2 * j) - 1) = 0 := by
      intro j
      have := ChenRusza_Lemma3 l h (j + 1) r (p (N₀ + 2 * j)) (hp1 _)
        (fun h => hp2 _ <| dvd_mul_of_dvd_right h _)
      exact this
    have hns :
        ∀ j : Fin (k + h), ∃ ns : ℕ,
          (h * l ^ ns + ns +
                (j.val + 1 + p (N₀ + 2 * j + 1) ^ 2 -
                  p (N₀ + 2 * j + 1))) %
              (p (N₀ + 2 * j + 1) ^ 2) = 0 ∧
          ns % (p (N₀ + 2 * j + 1) - 1) = 0 := by
      intro j
      convert ChenRusza_Lemma3 l h
        (j.val + 1 + p (N₀ + 2 * j + 1) ^ 2 - p (N₀ + 2 * j + 1))
        2 (p (N₀ + 2 * j + 1)) (hp1 _) _ using 1
      exact fun h => hp2 ( N₀ + 2 * j + 1 ) ( dvd_mul_of_dvd_right h _ )
    exact ⟨fun j => Classical.choose (hnr j), fun j => Classical.choose (hns j),
      fun j => Classical.choose_spec (hnr j),
      fun j => Classical.choose_spec (hns j)⟩
  -- Apply multi_crt to get m with L | m and m ≡ nr j [MOD P j^r], m ≡ ns j [MOD Q j^2].
  obtain ⟨m, hm⟩ :
      ∃ m : ℕ,
        M * (∏ j : Fin (k + h),
          (p (N₀ + 2 * j) - 1) * (p (N₀ + 2 * j + 1) - 1)) ∣ m ∧
        ∀ j : Fin (k + h),
          m ≡ nr j [MOD p (N₀ + 2 * j) ^ r] ∧
          m ≡ ns j [MOD p (N₀ + 2 * j + 1) ^ 2] := by
    have h_crt :
        ∀ (mods : Fin (2 * (k + h)) → ℕ)
          (targets : Fin (2 * (k + h)) → ℕ) (L : ℕ),
          0 < L →
          (∀ i, 0 < mods i) →
          (∀ i j, i ≠ j → Nat.Coprime (mods i) (mods j)) →
          (∀ i, Nat.Coprime L (mods i)) →
          ∃ m : ℕ, L ∣ m ∧ ∀ i, m ≡ targets i [MOD mods i] := by
      apply multi_crt
    have := h_crt
      (fun i => if hi : i.val < k + h
        then p (N₀ + 2 * i.val) ^ r
        else p (N₀ + 2 * (i.val - (k + h)) + 1) ^ 2)
      (fun i => if hi : i.val < k + h
        then nr ⟨i.val, hi⟩
        else ns ⟨i.val - (k + h), by omega⟩)
      (M * ∏ j : Fin (k + h),
        (p (N₀ + 2 * j) - 1) * (p (N₀ + 2 * j + 1) - 1)) ?_ ?_ ?_ ?_
    · obtain ⟨ m, hm₁, hm₂ ⟩ := this
      refine' ⟨ m, hm₁, fun j => ⟨ _, _ ⟩ ⟩
      · simpa [ j.2 ] using hm₂ ⟨ j, by linarith [ Fin.is_lt j ] ⟩
      · convert hm₂ ⟨ k + h + j, by linarith [ Fin.is_lt j ] ⟩ using 1 ; simp [two_mul]
        simp
    · exact mul_pos hM (Finset.prod_pos fun _ _ => mul_pos
        (Nat.sub_pos_of_lt (Nat.Prime.one_lt (hp1 _)))
        (Nat.sub_pos_of_lt (Nat.Prime.one_lt (hp1 _))))
    · exact fun i => by
        by_cases hi : (i : ℕ) < k + h <;>
          simpa [hi] using pow_pos (Nat.Prime.pos (hp1 _)) _
    · intro i j hij
      by_cases hi : ( i : ℕ ) < k + h <;> by_cases hj : ( j : ℕ ) < k + h <;> simp [ hi, hj ]
      · refine' Nat.coprime_pow_primes _ _ ( hp1 _ ) ( hp1 _ ) _
        intro H
        have := primeSeq_strictMono p hp1 hp2 hp3
        have := this.injective H
        simp_all [ Fin.ext_iff ]
      · refine' Nat.Coprime.pow_left _ _
        refine' Nat.Coprime.symm ( hp1 _ |> Nat.Prime.coprime_iff_not_dvd |> Iff.mpr <| _ )
        intro H
        have := Nat.prime_dvd_prime_iff_eq
          (hp1 (N₀ + 2 * (j - (k + h)) + 1)) (hp1 (N₀ + 2 * i)) |>.1 H
        have := primeSeq_strictMono p hp1 hp2 hp3
        exact absurd ( this.injective ‹_› ) (by omega )
      · refine' Nat.Coprime.pow_right _ _
        refine' Nat.Coprime.symm _
        refine' Nat.Coprime.symm ( hp1 _ |> Nat.Prime.coprime_iff_not_dvd |> Iff.mpr <| _ )
        intro H
        have := Nat.prime_dvd_prime_iff_eq
          (hp1 (N₀ + 2 * (i - (k + h)) + 1)) (hp1 (N₀ + 2 * j)) |>.1 H
        have := primeSeq_strictMono p hp1 hp2 hp3
        exact absurd ( this.injective ‹_› ) (by omega )
      · rw [ Nat.coprime_primes ] <;> norm_num [ hp1 ]
        have h_distinct : StrictMono p := by
          apply primeSeq_strictMono p hp1 hp2 hp3
        exact h_distinct.injective.ne (by contrapose! hij; exact Fin.ext <| by omega )
    · intro i; simp [ Nat.coprime_mul_iff_left ]
      constructor
      · split_ifs
        · exact Nat.Coprime.pow_right _ <| Nat.Coprime.symm <| hp1 _ |>
            Nat.Prime.coprime_iff_not_dvd |> Iff.mpr <|
              Nat.not_dvd_of_pos_of_lt hM <| hN₀ _
        · refine' Nat.Coprime.pow_right _ _
          refine' Nat.Coprime.symm ( hp1 _ |> Nat.Prime.coprime_iff_not_dvd |> Iff.mpr <| _ )
          exact Nat.not_dvd_of_pos_of_lt hM ( hN₀ _ ) |> fun h => by simpa [ add_assoc ] using h
      · split_ifs
        · refine' Nat.Coprime.prod_left _
          intro j _; rw [ Nat.coprime_mul_iff_left ] ; simp [ *, Nat.Coprime ]
          exact ⟨ Nat.Coprime.pow_right _ ( hp4 _ _ ), Nat.Coprime.pow_right _ ( hp4 _ _ ) ⟩
        · refine' Nat.Coprime.prod_left _
          simp +zetaDelta at *
          intro j; rw [ Nat.coprime_mul_iff_left ] ; aesop
  refine' ⟨ m, dvd_of_mul_right_dvd hm.1, fun n hn₁ hn₂ => _ ⟩
  -- Let $j$ be such that $n = h * l^m + m + (j + 1)$.
  obtain ⟨j, hj⟩ : ∃ j : Fin (k + h), n = h * l ^ m + m + (j.val + 1) := by
    exact ⟨ ⟨ n - ( h * l ^ m + m ) - 1, by omega ⟩, by norm_num; omega ⟩
  -- Euler's theorem transfers the congruences from `m` to powers of `l`.
  have h_euler :
      l ^ m ≡ l ^ (nr j) [MOD p (N₀ + 2 * j) ^ r] ∧
      l ^ m ≡ l ^ (ns j) [MOD p (N₀ + 2 * j + 1) ^ 2] := by
    have h_euler :
        m ≡ nr j [MOD (p (N₀ + 2 * j) - 1) * p (N₀ + 2 * j) ^ r] ∧
        m ≡ ns j
          [MOD (p (N₀ + 2 * j + 1) - 1) * p (N₀ + 2 * j + 1) ^ 2] := by
      have h_euler :
          m ≡ nr j [MOD (p (N₀ + 2 * j) - 1)] ∧
          m ≡ ns j [MOD (p (N₀ + 2 * j + 1) - 1)] := by
        have h_euler :
            m ≡ 0 [MOD (p (N₀ + 2 * j) - 1)] ∧
            m ≡ 0 [MOD (p (N₀ + 2 * j + 1) - 1)] := by
          exact ⟨
            Nat.modEq_zero_iff_dvd.mpr
              (dvd_trans
                (dvd_mul_of_dvd_right
                  (Finset.dvd_prod_of_mem _ (Finset.mem_univ _) |>
                    dvd_trans (dvd_mul_right _ _)) _) hm.1),
            Nat.modEq_zero_iff_dvd.mpr
              (dvd_trans
                (dvd_mul_of_dvd_right
                  (Finset.dvd_prod_of_mem _ (Finset.mem_univ _) |>
                    dvd_trans (dvd_mul_left _ _)) _) hm.1)⟩
        simp_all [ Nat.ModEq ]
      have h_euler :
          Nat.Coprime (p (N₀ + 2 * j) - 1) (p (N₀ + 2 * j) ^ r) ∧
          Nat.Coprime
            (p (N₀ + 2 * j + 1) - 1) (p (N₀ + 2 * j + 1) ^ 2) := by
        exact ⟨ Nat.Coprime.pow_right _ ( hp4 _ _ ), Nat.Coprime.pow_right _ ( hp4 _ _ ) ⟩
      rw [ ← Nat.modEq_and_modEq_iff_modEq_mul, ← Nat.modEq_and_modEq_iff_modEq_mul ] ; aesop
      · exact h_euler.2
      · exact h_euler.1
    apply And.intro
    · apply euler_pow_cong
      · exact hp1 _
      · exact fun h => hp2 ( N₀ + 2 * j ) ( dvd_mul_of_dvd_right h _ )
      · linarith
      · simpa only [ mul_comm ] using h_euler.1
    · apply euler_pow_cong
      · exact hp1 _
      · exact fun h => hp2 ( N₀ + 2 * j + 1 ) ( dvd_mul_of_dvd_right h _ )
      · norm_num
      · simpa only [ mul_comm ] using h_euler.2
  -- Therefore, `n` satisfies the two prime-power congruences.
  have h_cong :
      n ≡ 0 [MOD p (N₀ + 2 * j) ^ r] ∧
      n ≡ p (N₀ + 2 * j + 1) [MOD p (N₀ + 2 * j + 1) ^ 2] := by
    simp_all [ ← ZMod.natCast_eq_natCast_iff ]
    have := hnr j; have := hns j; simp_all [ ← ZMod.val_natCast ]
    specialize hns j
    simp_all [Nat.cast_sub (show
      p (N₀ + 2 * j + 1) ≤ j + 1 + p (N₀ + 2 * j + 1) ^ 2 from by
        nlinarith only [Nat.Prime.two_le (hp1 (N₀ + 2 * j + 1))])]
    linear_combination' hns.1
  -- Therefore, $n$ is not $r$-free and not squarefull.
  have h_not_rfree : ¬IsRFree r n := by
    apply not_rfree_of_prime_pow_dvd (hp1 (N₀ + 2 * j)) (Nat.dvd_of_mod_eq_zero h_cong.left)
  have h_not_squarefull : ¬IsSquarefull n := by
    apply not_squarefull_of_prime_dvd_sq_not
    exact hp1 ( N₀ + 2 * j + 1 )
    · exact Nat.dvd_of_mod_eq_zero
        (h_cong.2.of_dvd (dvd_pow_self _ two_ne_zero) ▸
          Nat.mod_eq_zero_of_dvd (dvd_refl _))
    · rw [ Nat.dvd_iff_mod_eq_zero, h_cong.2 ]
      rw [ Nat.mod_eq_of_lt ] <;> nlinarith only [ Nat.Prime.one_lt ( hp1 ( N₀ + 2 * j + 1 ) ) ]
  exact not_or.mpr ⟨h_not_rfree, h_not_squarefull⟩

theorem forbiddenIntervals (r : ℕ) (hr : r ≥ 2) (l : ℕ) (hl : l ≥ 2)
    (k : ℕ) (hk : k ≥ 1) :
    ∃ h m : ℕ,
      (∀ n : ℕ, h * l ^ m < n → n ≤ h * l ^ m + k →
        ¬(IsRFree r n ∨ IsSquarefull n)) ∧
      (∀ n : ℕ, h * l ^ m + m < n → n ≤ h * l ^ m + m + k + h →
        ¬(IsRFree r n ∨ IsSquarefull n)) := by
  obtain ⟨h, M, hh, hM, hfirst⟩ := first_interval_periodic r l hl k hk
  obtain ⟨m, hdvd, hsecond⟩ := second_interval_exists r hr l hl h hh M hM k hk
  exact ⟨h, m, hfirst m hdvd, hsecond⟩

/-! ## Helpers for Theorem 2.5 -/

/-- Summability of `∑ a_n / l^{a_n}` for injective `a` with positive values. -/
private lemma summable_injective_div_pow (a : ℕ → ℕ) (ha_inj : Function.Injective a)
    (l : ℕ) (hl : l ≥ 2) : Summable (fun n => (a n : ℝ) / (l : ℝ) ^ (a n)) := by
  -- The series $\sum_{n=0}^{\infty} \frac{n}{l^n}$ converges by the ratio test.
  have h_series : Summable (fun n : ℕ => (n : ℝ) / (l : ℝ) ^ n) := by
    refine' summable_of_ratio_norm_eventually_le _ _
    exact 3 / 4
    · norm_num
    · norm_num [ pow_succ, ← div_div ]
      field_simp
      exact ⟨ 4, fun n hn => by norm_cast; nlinarith ⟩
  exact h_series.comp_injective ha_inj

/-- The tail sum `∑_{m > N} m / l^m` tends to 0 as `N → ∞`. -/
private lemma tendsto_tail_sum_div_pow (l : ℕ) (hl : l ≥ 2) :
    Filter.Tendsto (fun N => ∑' (m : ℕ), if m > N then (m : ℝ) / (l : ℝ) ^ m else 0)
      Filter.atTop (nhds 0) := by
  -- The series $\sum_{m=N+1}^{\infty} \frac{m}{l^m}$ is summable.
  have h_summable : Summable (fun m : ℕ => (m : ℝ) / (l : ℝ) ^ m) := by
    refine' summable_of_ratio_norm_eventually_le _ _
    exact 3 / 4
    · norm_num
    · norm_num [ pow_succ, mul_div_mul_comm ]
      field_simp
      exact ⟨ 8, fun n hn => by norm_cast; nlinarith ⟩
  convert tendsto_sum_nat_add fun n => ( n + 1 : ℝ ) / l ^ ( n + 1 ) using 1
  ext N; rw [ ← Summable.sum_add_tsum_nat_add N.succ ]
  · simp +arith [ Finset.sum_range_succ ]
    exact Finset.sum_eq_zero fun x hx => if_neg <| by linarith [ Finset.mem_range.mp hx ]
  · exact Summable.of_nonneg_of_le (fun m => by positivity)
      (fun m => by split_ifs <;> first | positivity | aesop) h_summable

/-- Monotonicity of tail sums: larger cutoff gives smaller tail. -/
private lemma tail_sum_mono (f : ℕ → ℝ) (hf : ∀ m, 0 ≤ f m)
    (N1 N2 : ℕ) (h : N1 ≤ N2) :
    (∑' m, if m > N2 then f m else 0) ≤ (∑' m, if m > N1 then f m else 0) := by
  by_cases h_summable :
      Summable (fun m : ℕ => (if m > N1 then f m else 0)) <;>
    by_cases h_summable' :
      Summable (fun m : ℕ => (if m > N2 then f m else 0)) <;>
    simp_all [tsum_eq_zero_of_not_summable]
  · exact Summable.tsum_le_tsum (fun m => by split_ifs <;> linarith [hf m])
      h_summable' h_summable
  · exact tsum_nonneg fun _ => by aesop
  · contrapose! h_summable
    rw [ ← summable_nat_add_iff ( N2 + 1 ) ] at *
    exact h_summable'.congr fun n => by split_ifs <;> linarith

/-- The geometric tail `h / l^{h+k}` tends to 0 as `k → ∞` uniformly in `h`. -/
private lemma tendsto_geom_tail (l : ℕ) (hl : l ≥ 2) :
    Filter.Tendsto (fun N => (N : ℝ) / (l : ℝ) ^ N) Filter.atTop (nhds 0) := by
  refine' squeeze_zero_norm' _ _
  refine' fun n => n / Real.exp ( n * Real.log l )
  · norm_num [ Real.rpow_def_of_pos (by positivity : 0 < ( l : ℝ ) ), mul_comm ]
    exact ⟨ 0, fun x hx => by rw [ abs_of_nonneg hx ] ⟩
  · -- Let $y = n \log l$, therefore the limit becomes $\lim_{y \to \infty} \frac{y}{e^y}$.
    suffices h_log : Filter.Tendsto (fun y : ℝ => y / Real.exp y) Filter.atTop (nhds 0) by
      have := h_log.comp
        (Filter.tendsto_id.atTop_mul_const
          (Real.log_pos (show (l : ℝ) > 1 by norm_cast)))
      convert this.div_const (Real.log l) using 2 <;>
        norm_num [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ne_of_gt,
          Real.log_pos (show (l : ℝ) > 1 by norm_cast)]
    simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1

/-
For an injective sequence of r-free/squarefull numbers, the shifted tsum is
bounded by the tail of `∑ m / l^m`.
-/
private lemma first_sum_bound (a : ℕ → ℕ) (ha_inj : Function.Injective a)
    (ha_cond : ∀ n, IsRFree r (a n) ∨ IsSquarefull (a n))
    (l : ℕ) (hl : l ≥ 2) (c k : ℕ)
    (hgap : ∀ n, c < n → n ≤ c + k → ¬(IsRFree r n ∨ IsSquarefull n)) :
    (∑' n, if a n > c then ((a n : ℝ) - c) / (l : ℝ) ^ (a n - c) else 0) ≤
    (∑' m, if m > k then (m : ℝ) / (l : ℝ) ^ m else 0) := by
  -- Define g : {n | a n > c} → ℕ by g(n) = a(n) - c. This is injective since a is injective.
  set g : {n // c < a n} → ℕ := fun n => a n - c
  have hg_inj : Function.Injective g := by
    exact fun x y hxy => Subtype.ext <| ha_inj <| by
      linarith [
        Nat.sub_add_cancel <| show c ≤ a x from le_of_lt x.2,
        Nat.sub_add_cancel <| show c ≤ a y from le_of_lt y.2];
  -- Finite partial sums are bounded by the corresponding image sum.
  have h_sum_bound :
      ∀ s : Finset {n // c < a n},
        ∑ n ∈ s, ((a n : ℝ) - c) / (l : ℝ) ^ (a n - c) ≤
          ∑ m ∈ Finset.image g s, (m : ℝ) / (l : ℝ) ^ m := by
    intros s
    rw [Finset.sum_image <| by tauto]
    exact Finset.sum_le_sum fun x hx => by rw [Nat.cast_sub <| le_of_lt <| x.2];
  -- The image lies in `{m | m > k}` by `hgap` and `ha_cond`.
  have h_image_bound :
      ∀ s : Finset {n // c < a n},
        ∑ m ∈ Finset.image g s, (m : ℝ) / (l : ℝ) ^ m ≤
          ∑' m : ℕ, if m > k then (m : ℝ) / (l : ℝ) ^ m else 0 := by
    intro s
    have h_image_subset : ∀ m ∈ Finset.image g s, m > k := by
      grind;
    have h_image_subset :
        ∑ m ∈ Finset.image g s, (m : ℝ) / (l : ℝ) ^ m ≤
          ∑ m ∈ Finset.image g s,
            if m > k then (m : ℝ) / (l : ℝ) ^ m else 0 := by
      exact Finset.sum_le_sum fun x hx => by rw [ if_pos ( h_image_subset x hx ) ] ;
    refine' le_trans h_image_subset ( Summable.sum_le_tsum _ _ _ );
    · exact fun _ _ => by positivity;
    · have h_summable : Summable (fun m : ℕ => (m : ℝ) / (l : ℝ) ^ m) := by
        refine' summable_of_ratio_norm_eventually_le _ _;
        exact 3 / 4;
        · norm_num;
        · norm_num [ pow_succ, div_eq_mul_inv ];
          refine' ⟨ 8, fun n hn => _ ⟩ ; rw [ abs_of_nonneg ( by positivity ) ] ; ring_nf;
          nlinarith only [
            show (l : ℝ) ≥ 2 by norm_cast,
            inv_pos.mpr (by positivity : 0 < (l : ℝ)),
            inv_mul_cancel₀ (by positivity : (l : ℝ) ≠ 0),
            pow_pos (inv_pos.mpr (by positivity : 0 < (l : ℝ))) n,
            show (n : ℝ) ≥ 8 by norm_cast,
            mul_le_mul_of_nonneg_right
              (show (l : ℝ) ⁻¹ ≤ 1 / 2 by
                rw [inv_le_comm₀] <;> norm_num <;> linarith)
              (pow_nonneg (inv_nonneg.mpr (by positivity : 0 ≤ (l : ℝ))) n)];
      exact Summable.of_nonneg_of_le (fun m => by split_ifs <;> positivity)
        (fun m => by split_ifs <;> first | positivity | aesop) h_summable;
  -- The sum over the subtype is equal to the sum over the conditional series.
  have h_subtype_sum :
      ∑' n : {n // c < a n}, ((a n : ℝ) - c) / (l : ℝ) ^ (a n - c) =
        ∑' n : ℕ,
          if a n > c then ((a n : ℝ) - c) / (l : ℝ) ^ (a n - c) else 0 := by
    convert tsum_subtype _ _ using 1;
    any_goals exact { n : ℕ | c < a n };
    any_goals exact fun n => ( a n - c : ℝ ) / l ^ ( a n - c );
    all_goals try infer_instance;
    · rfl;
    · simp [ Set.indicator ];
  refine' h_subtype_sum ▸ _;
  by_cases h_summable :
      Summable (fun n : {n // c < a n} =>
        ((a n : ℝ) - c) / (l : ℝ) ^ (a n - c));
  · refine' le_of_tendsto_of_tendsto' ( h_summable.hasSum ) tendsto_const_nhds _;
    exact fun s => le_trans ( h_sum_bound s ) ( h_image_bound s );
  · rw [ tsum_eq_zero_of_not_summable h_summable ] ; exact tsum_nonneg fun _ => by positivity;

/-
For an injective sequence of r-free/squarefull numbers, the second sum is bounded.
-/
private lemma second_sum_bound (a : ℕ → ℕ) (ha_inj : Function.Injective a)
    (ha_cond : ∀ n, IsRFree r (a n) ∨ IsSquarefull (a n))
    (l : ℕ) (hl : l ≥ 2) (c h_val m_val k : ℕ)
    (hgap : ∀ n, c + m_val < n → n ≤ c + m_val + k + h_val →
      ¬(IsRFree r n ∨ IsSquarefull n)) :
    (∑' n, if a n > c + m_val then (h_val : ℝ) / (l : ℝ) ^ (a n - c - m_val) else 0) ≤
    (h_val : ℝ) * (∑' m, if m > k + h_val then (1 : ℝ) / (l : ℝ) ^ m else 0) := by
  rw [ ← tsum_mul_left ];
  convert Summable.tsum_subtype_le _ _ _ _ using 1;
  any_goals try infer_instance;
  rotate_left;
  exact { n | ∃ m, a m > c + m_val ∧ n = a m - c - m_val };
  · exact fun _ => by positivity;
  · exact Summable.mul_left _ <|
      Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => by aesop) <|
        summable_geometric_of_lt_one (by positivity) <|
          inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr hl;
  · rw [ ← tsum_eq_tsum_of_ne_zero_bij ];
    use fun x => ⟨ a x - c - m_val, ⟨ x, by
      aesop ⟩ ⟩
    all_goals generalize_proofs at *;
    · intro x y hxy;
      grind;
    · intro x hx
      rcases x with ⟨val, hval⟩
      rcases hval with ⟨m, hm_gt, hval_eq⟩
      have hh_ne : (h_val : ℝ) ≠ 0 := by
        change (h_val : ℝ) *
          (if val > k + h_val then 1 / (l : ℝ) ^ val else 0) ≠ 0 at hx
        by_contra hzero
        simp [hzero] at hx
      refine ⟨⟨m, ?_⟩, ?_⟩
      · change (if a m > c + m_val
            then (h_val : ℝ) / (l : ℝ) ^ (a m - c - m_val) else 0) ≠ 0
        simp [hm_gt, hh_ne, show (l : ℝ) ≠ 0 by positivity]
      exact Subtype.ext hval_eq.symm
    · grind

/-- The first sum in E_k is nonneg. -/
private lemma first_sum_nonneg (a : ℕ → ℕ) (l : ℕ) (c : ℕ) :
    0 ≤ (∑' n, if a n > c then ((a n : ℝ) - c) / (l : ℝ) ^ (a n - c) else 0) := by
  exact tsum_nonneg fun n => by
    split_ifs <;> first
    | positivity
    | exact div_nonneg (sub_nonneg_of_le <| mod_cast by linarith) <| by positivity
/-- The second sum in E_k is nonneg. -/
private lemma second_sum_nonneg (a : ℕ → ℕ) (l : ℕ) (c h_val m_val : ℕ) :
    0 ≤ (∑' n, if a n > c + m_val
      then (h_val : ℝ) / (l : ℝ) ^ (a n - c - m_val) else 0) := by
  exact tsum_nonneg fun _ => by positivity
/-- There exists some `a n > c` for any `c`, since `a` is injective. -/
private lemma exists_gt_of_injective (a : ℕ → ℕ) (ha_inj : Function.Injective a) (c : ℕ) :
    ∃ n, a n > c := by
  contrapose! ha_inj
  exact fun hinj => absurd (Set.infinite_range_of_injective hinj)
    (Set.not_infinite.mpr <| Set.finite_iff_bddAbove.mpr ⟨c, by
      rintro x ⟨n, rfl⟩
      exact ha_inj n⟩)

/-- The first sum is positive when there's some `a n > c`. -/
private lemma first_sum_pos (a : ℕ → ℕ) (ha_inj : Function.Injective a)
    (l : ℕ) (hl : l ≥ 2) (c : ℕ) :
    0 < (∑' n, if a n > c then ((a n : ℝ) - c) / (l : ℝ) ^ (a n - c) else 0) := by
  by_contra h_contra
  obtain ⟨ n₀, hn₀ ⟩ := exists_gt_of_injective a ha_inj c
  refine' h_contra ( lt_of_lt_of_le _ ( Summable.le_tsum _ n₀ _ ) )
  · exact if_pos hn₀ ▸
      div_pos (sub_pos.mpr (Nat.cast_lt.mpr hn₀)) (pow_pos (by positivity) _)
  · have h_summable : Summable (fun n => (a n : ℝ) / (l : ℝ) ^ (a n)) := by
      exact summable_injective_div_pow a ha_inj l hl
    refine' .of_nonneg_of_le (fun n => _ ) (fun n => _ ) ( h_summable.mul_left ( l ^ c : ℝ ) )
    · split_ifs <;> first
      | positivity
      | exact div_nonneg (sub_nonneg_of_le <| mod_cast by linarith) <| by positivity
    · split_ifs <;> simp_all [ mul_div ]
      · rw [ div_le_div_iff₀ ] <;> try positivity
        rw [show (l : ℝ) ^ a n = l ^ c * l ^ (a n - c) by
          rw [← pow_add, Nat.add_sub_of_le (by linarith)]]
        nlinarith [
          show (a n : ℝ) ≥ c + 1 by exact_mod_cast by linarith,
          show (l : ℝ) ^ c > 0 by positivity,
          show (l : ℝ) ^ (a n - c) > 0 by positivity,
          mul_le_mul_of_nonneg_right
            (show (l : ℝ) ^ c ≥ 1 by
              exact one_le_pow₀ (by norm_cast; linarith))
            (show (l : ℝ) ^ (a n - c) ≥ 0 by positivity)]
      · positivity
  · intro j hj
    split_ifs <;> first
    | positivity
    | exact div_nonneg (sub_nonneg.2 <| Nat.cast_le.2 <| le_of_lt <|
        by linarith) <| by positivity
/-- `h * ∑_{m > k+h} 1/l^m → 0` as `k → ∞` (for any h depending on k). -/
private lemma tendsto_h_times_geom_tail (l : ℕ) (hl : l ≥ 2) (h_val : ℕ → ℕ) :
    Filter.Tendsto (fun k =>
      (h_val k : ℝ) * (∑' m, if m > k + h_val k then (1 : ℝ) / (l : ℝ) ^ m else 0))
      Filter.atTop (nhds 0) := by
  -- We need h_val(k) * ∑_{m > k + h_val(k)} 1/l^m → 0 as k → ∞.
  -- The geometric tail: ∑_{m > N} 1/l^m = l^{-(N+1)} / (1 - 1/l) = l^{-N} / (l-1).
  have h_geom_tail :
      ∀ N : ℕ,
        (∑' m, if m > N then (1 : ℝ) / (l : ℝ) ^ m else 0) =
          (1 : ℝ) / (l - 1) * (1 : ℝ) / (l : ℝ) ^ N := by
    intro N
    have h_sum :
        (∑' m, if m > N then (1 : ℝ) / (l : ℝ) ^ m else 0) =
          (∑' m, (1 : ℝ) / (l : ℝ) ^ (m + N + 1)) := by
      rw [ ←Summable.sum_add_tsum_nat_add N.succ ]
      · simp +arith [ Finset.sum_ite, Nat.succ_eq_add_one ]
        exact Finset.sum_eq_zero fun x hx => by
          linarith [Finset.mem_range.mp (Finset.mem_filter.mp hx |>.1),
            Finset.mem_filter.mp hx |>.2]
      · exact Summable.of_nonneg_of_le (fun n => by positivity) (fun n => by aesop)
          (summable_geometric_of_lt_one (by positivity)
            (inv_lt_one_of_one_lt₀ (by norm_cast) : (l : ℝ) ⁻¹ < 1))
    simp_all [ pow_add, tsum_mul_left ]
    have := tsum_geometric_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ (by norm_cast : (1 : ℝ) < l))
    simp_all [div_eq_mul_inv, mul_comm]
    field_simp
  -- So the expression is h_val(k) * l^{-(k + h_val(k))} / (l-1).
  suffices h_suff :
      Filter.Tendsto
        (fun k => (h_val k : ℝ) * (1 : ℝ) / (l : ℝ) ^ (k + h_val k))
        Filter.atTop (nhds 0) by
    convert h_suff.const_mul ( 1 / ( l - 1 : ℝ ) ) using 2 <;> push_cast [ h_geom_tail ] <;> ring
  -- Since `l ≥ 2`, compare with `(k + h_val k) * l ^ -(k + h_val k)`.
  suffices h_bound :
      Filter.Tendsto
        (fun k => (k + h_val k : ℝ) * (1 : ℝ) / (l : ℝ) ^ (k + h_val k))
        Filter.atTop (nhds 0) by
    exact squeeze_zero (fun k => by positivity ) (fun k => by gcongr ; linarith ) h_bound
  have := tendsto_geom_tail l hl
  convert this.comp
    (show Filter.Tendsto (fun k : ℕ => (k : ℝ) + h_val k)
        Filter.atTop Filter.atTop from
      Filter.tendsto_atTop_mono (fun k => by norm_num) tendsto_natCast_atTop_atTop)
    using 2
  norm_num
  norm_cast

/-- Theorem 2.5 (Chen–Ruzsa Theorem 4). If `(a_n)` is a sequence of distinct positive
integers, each either `r`-free or squarefull, then `∑ a_n · l^{-a_n}` is irrational
for every `l ≥ 2`. -/
theorem ChenRusza_Theorem4 (r : ℕ) (hr : r ≥ 2) (a : ℕ → ℕ)
    (ha_inj : Function.Injective a)
    (ha_cond : ∀ n, IsRFree r (a n) ∨ IsSquarefull (a n))
    (l : ℕ) (hl : l ≥ 2) :
    Irrational (∑' n, (a n : ℝ) / (l : ℝ) ^ (a n)) := by
  -- Extract parameters from forbiddenIntervals for each k
  have hFI : ∀ k, ∃ hv mv : ℕ, 0 < hv ∧
      (∀ n, hv * l ^ mv < n → n ≤ hv * l ^ mv + (k + 1) →
        ¬(IsRFree r n ∨ IsSquarefull n)) ∧
      (∀ n, hv * l ^ mv + mv < n → n ≤ hv * l ^ mv + mv + (k + 1) + hv →
        ¬(IsRFree r n ∨ IsSquarefull n)) := by
    intro k
    obtain ⟨hv, mv, hgap1, hgap2⟩ := forbiddenIntervals r hr l hl (k + 1) (by omega)
    refine ⟨hv, mv, ?_, hgap1, hgap2⟩
    -- h = 0 is impossible: 1 is r-free (IsRFree r 1)
    by_contra h0; push Not at h0; interval_cases hv; simp at hgap1
    exact (hgap1 1 (by omega) (by omega)).1 (fun d hd => by
      have : d ^ r = 1 := Nat.eq_one_of_dvd_one hd
      cases Nat.pow_eq_one.mp this with | inl h => rw [h]; exact isUnit_one | inr h => omega)
  choose hv mv hv_pos hgap1 hgap2 using hFI
  -- Define the parameter sequences
  set c_seq : ℕ → ℕ := fun k => hv k * l ^ mv k
  set d_seq : ℕ → ℕ := fun k => hv k
  set t_seq : ℕ → ℕ := fun k => mv k
  -- The E_k expression: since d_seq k * l^{t_seq k} = c_seq k,
  -- (a n - d_seq k * l^{t_seq k}) / l^{a n - c_seq k} = (a n - c_seq k) / l^{a n - c_seq k}
  have hEk_simp :
      ∀ k n,
        ((a n : ℝ) - ↑(d_seq k) * (↑l) ^ t_seq k) =
          ((a n : ℝ) - ↑(c_seq k)) := by
    intro k n; simp [c_seq, d_seq, t_seq]
  -- Show E_k ≠ 0
  have hEk_ne_zero : ∀ k,
      (∑' n, if a n > c_seq k
        then ((a n : ℝ) - ↑(d_seq k) * (↑l) ^ t_seq k) /
          (↑l) ^ (a n - c_seq k)
        else 0) +
      (∑' n, if a n > c_seq k + t_seq k
        then (↑(d_seq k) : ℝ) / (↑l) ^ (a n - c_seq k - t_seq k)
        else 0) ≠ 0 := by
    intro k
    apply ne_of_gt
    apply add_pos_of_pos_of_nonneg
    · have := first_sum_pos a ha_inj l hl (c_seq k)
      convert this using 2; ext n; split_ifs <;> simp_all
    · exact tsum_nonneg (fun _ => by positivity)
  -- Show E_k → 0
  have hEk_tendsto : Filter.Tendsto (fun k =>
      (∑' n, if a n > c_seq k
        then ((a n : ℝ) - ↑(d_seq k) * (↑l) ^ t_seq k) /
          (↑l) ^ (a n - c_seq k)
        else 0) +
      (∑' n, if a n > c_seq k + t_seq k
        then (↑(d_seq k) : ℝ) / (↑l) ^ (a n - c_seq k - t_seq k)
        else 0))
      Filter.atTop (nhds 0) := by
    have hrw : (fun k =>
        (∑' n, if a n > c_seq k
          then ((a n : ℝ) - ↑(d_seq k) * (↑l) ^ t_seq k) /
            (↑l) ^ (a n - c_seq k)
          else 0) +
        (∑' n, if a n > c_seq k + t_seq k
          then (↑(d_seq k) : ℝ) / (↑l) ^ (a n - c_seq k - t_seq k)
          else 0)) =
      (fun k =>
        (∑' n, if a n > c_seq k
          then ((a n : ℝ) - ↑(c_seq k)) / (↑l) ^ (a n - c_seq k)
          else 0) +
        (∑' n, if a n > c_seq k + t_seq k
          then (↑(d_seq k) : ℝ) / (↑l) ^ (a n - c_seq k - t_seq k)
          else 0)) := by
      funext k; congr 1; congr 1; ext n; split_ifs <;> simp [hEk_simp]
    rw [hrw]
    have hb1 :
        ∀ k,
          (∑' n, if a n > c_seq k
            then ((a n : ℝ) - (c_seq k)) / (↑l) ^ (a n - c_seq k)
            else 0) ≤
        ∑' m, if m > k then (m : ℝ) / (↑l) ^ m else 0 := by
      intro k
      exact le_trans (first_sum_bound a ha_inj ha_cond l hl (c_seq k) (k + 1) (hgap1 k))
        (tail_sum_mono (fun m => (m : ℝ) / (↑l) ^ m)
          (fun m => div_nonneg (Nat.cast_nonneg m) (pow_nonneg (Nat.cast_nonneg l) m))
          k (k + 1) (Nat.le_succ k))
    have hb2 :
        ∀ k,
          (∑' n, if a n > c_seq k + t_seq k
            then ((d_seq k : ℝ)) / (↑l) ^ (a n - c_seq k - t_seq k)
            else 0) ≤
        ((d_seq k : ℝ)) * ∑' m, if m > k + d_seq k then (1 : ℝ) / (↑l) ^ m else 0 := by
      intro k
      exact le_trans
        (second_sum_bound a ha_inj ha_cond l hl
          (c_seq k) (d_seq k) (t_seq k) (k + 1) (hgap2 k))
        (mul_le_mul_of_nonneg_left
          (tail_sum_mono (fun m => (1 : ℝ) / (↑l) ^ m)
            (fun m => div_nonneg zero_le_one (pow_nonneg (Nat.cast_nonneg l) m))
            (k + d_seq k) (k + 1 + d_seq k) (by omega))
          (Nat.cast_nonneg (d_seq k)))
    have h1 := squeeze_zero (fun k => first_sum_nonneg a l (c_seq k)) hb1
      (tendsto_tail_sum_div_pow l hl)
    have h2 := squeeze_zero
      (fun k => second_sum_nonneg a l (c_seq k) (d_seq k) (t_seq k)) hb2
      (tendsto_h_times_geom_tail l hl d_seq)
    convert h1.add h2 using 1; simp [add_zero]
  -- Apply ChenRusza_Lemma1
  exact ChenRusza_Lemma1 l hl a ha_inj (fun n => ↑(a n))
    (summable_injective_div_pow a ha_inj l hl) c_seq d_seq t_seq
    hEk_ne_zero hEk_tendsto

/-! # Chapter 3: Equivalence of the Möbius series -/

/-- Proposition 3.1. The Möbius series equals the squarefree-reindexed series. -/
theorem mobiusSeries_eq_squarefreeSeries :
    ∑' (n : ℕ), ((moebius n ^ 2 : ℤ) : ℝ) * (n : ℝ) / (2 : ℝ) ^ n =
      ∑' n, (squarefreeSeq n : ℝ) / (2 : ℝ) ^ (squarefreeSeq n) := by
  set f : ℕ → ℝ := fun n => if Squarefree n then (n : ℝ) / (2 : ℝ) ^ n else 0
  -- Since the Möbius series equals the sum of $f(n)$, the equivalence follows.
  have h_sum_f :
      ∑' (n : ℕ), ((moebius n ^ 2 : ℤ) : ℝ) * (n : ℝ) / (2 : ℝ) ^ n =
        ∑' n, f n := by
    refine' tsum_congr fun n => _
    simp [f, ArithmeticFunction.moebius]
    split_ifs <;> simp_all [ ← pow_mul ]
  convert h_sum_f using 1
  convert (Function.Injective.tsum_eq
    (show Function.Injective (Nat.nth (fun n => Squarefree n)) from ?_) ?_) using 1
  · refine' tsum_congr fun n => _
    exact Eq.symm (if_pos <|
      Nat.nth_mem_of_infinite
        (show Set.Infinite {n : ℕ | Squarefree n} from
          Nat.infinite_setOf_prime.mono fun x hx => hx.squarefree) _)
  · exact Nat.nth_injective <| Nat.infinite_setOf_prime.mono fun x hx => hx.squarefree
  · intro n hn; use Nat.count (fun n => Squarefree n ) n; aesop

/-! # Chapter 4: Erdős Problem 259 -/

/- Property 4.1. Every term of `squarefreeSeq` is 2-free. -/
theorem squarefreeSeq_terms_are_twoFree :
    ∀ n, IsRFree 2 (squarefreeSeq n) := by
  intro n d hd
  -- By definition of `squarefreeSeq`, `squarefreeSeq n` is squarefree.
  have h_squarefree : Squarefree (squarefreeSeq n) := by
    exact Nat.nth_mem_of_infinite
      (show Set.Infinite {n | Squarefree n} from
        Nat.infinite_setOf_prime.mono fun n hn => hn.squarefree) n
  have := h_squarefree d; simp_all [ sq ]

/-- Theorem 4.2 (Erdős Problem 259). The Möbius series
`∑_{n=1}^∞ μ(n)² · n / 2^n` is irrational. -/
theorem erdos_259 :
    Irrational
      (∑' (n : ℕ), ((moebius n ^ 2 : ℤ) : ℝ) * (n : ℝ) / (2 : ℝ) ^ n) := by
  rw [mobiusSeries_eq_squarefreeSeries]
  apply ChenRusza_Theorem4
  · exact Nat.le_refl 2
  · exact Nat.nth_injective
      (Nat.infinite_setOf_prime.mono fun _ hn => Irreducible.squarefree hn)
  · exact fun n => Or.inl (squarefreeSeq_terms_are_twoFree n)
  · exact Nat.le_refl 2

#print axioms erdos_259
-- 'Erdos259.erdos_259' depends on axioms: [propext, Classical.choice, Quot.sound]

end

end Erdos259
