/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 258.
https://www.erdosproblems.com/forum/thread/258

Formalization status:
- Conditional on: tao_teravainen

Informal authors:
- GPT-5.4 Pro
- Przemek Chojecki

Formal authors:
- Aristotle
- Przemek Chojecki
- Stefano Rocca

URLs:
- https://www.ulam.ai/research/erdos258.pdf
- https://www.ulam.ai/research/erdos258.tar.gz
- https://gist.githubusercontent.com/ster-oc/2b7adcf9d753cf6e29d782f7374cc57e/raw/689a8483895cbe147634dfbf2d7b1db93a3b5b5f/Erdos258.lean
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/258.lean
-/
import ErdosProblems.Axioms
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos258

/-!
# Erdős Problem 258 (original formalization by Przemek Chojecki)

This file gives a self-contained formal proof that for any sequence of positive
integers `(aₙ)` with `aₙ → ∞`, the Erdős–Straus series

  `S = ∑_{n ≥ 1} τ(n) / (a₁ a₂ ⋯ aₙ)`

is irrational, modulo the deep Tao–Teräväinen theorem from analytic number
theory (stated here without proof).

The proof strategy follows the note by Erdős–Straus and is organized into
four chapters:

1. **Definitions and basic lemmas** — partial products, series terms,
   summability.
2. **Tail irrationality lemma** — the core
   irrationality-by-clearing-denominators argument.
3. **Tao–Teräväinen theorem** — the analytic input.
4. **Main theorem** — combining the pieces.

## Main declarations

* `erdosSeries`: the Erdős–Straus series `∑_{n≥1} τ(n) / Q_n`.
* `tail_irrationality_lemma`: the core irrationality argument.
* `tao_teravainen`: the deep analytic input.
* `erdos_258`: the main theorem.
-/

open Nat Finset Filter
open scoped BigOperators Topology

noncomputable section

/-! ## Definitions and Basic Lemmas

We define the partial product `Q a n = a 1 * a 2 * ⋯ * a n` and the
Erdős–Straus series `∑_{n≥1} τ(n) / (a₁ a₂ ⋯ aₙ)`, then prove basic
properties such as positivity, divisibility, and summability.
-/

/-! ### Partial products -/

/-- `Q a n = a 1 * a 2 * ⋯ * a n`, with `Q a 0 = 1`. -/
def Q (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => Q a n * a (n + 1)

@[simp] lemma Q_zero (a : ℕ → ℕ) : Q a 0 = 1 := rfl
@[simp] lemma Q_succ (a : ℕ → ℕ) (n : ℕ) : Q a (n + 1) = Q a n * a (n + 1) := rfl

lemma Q_pos (a : ℕ → ℕ) (ha : ∀ n, 0 < a (n + 1)) (n : ℕ) : 0 < Q a n := by
  induction n with
  | zero => simp
  | succ n ih => simp [Nat.mul_pos ih (ha n)]

lemma Q_cast_pos (a : ℕ → ℕ) (ha : ∀ n, 0 < a (n + 1)) (n : ℕ) :
    (0 : ℝ) < (Q a n : ℝ) :=
  Nat.cast_pos.mpr (Q_pos a ha n)

lemma Q_cast_ne_zero (a : ℕ → ℕ) (ha : ∀ n, 0 < a (n + 1)) (n : ℕ) :
    (Q a n : ℝ) ≠ 0 :=
  ne_of_gt (Q_cast_pos a ha n)

/-- `Q a n ∣ Q a m` when `n ≤ m`. -/
lemma Q_dvd_Q (a : ℕ → ℕ) {n m : ℕ} (h : n ≤ m) : Q a n ∣ Q a m := by
  induction h with
  | refl => exact dvd_refl _
  | step _ ih => exact dvd_mul_of_dvd_left ih _

/-! ### Series terms -/

/-- Term `n` (0-indexed) of the Erdős–Straus series: `τ(n+1) / Q(n+1)`. -/
def erdosTerm (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((n + 1).divisors.card : ℝ) / (Q a (n + 1) : ℝ)

lemma erdosTerm_pos (a : ℕ → ℕ) (ha : ∀ n, 0 < a (n + 1)) (n : ℕ) :
    0 < erdosTerm a n := by
  exact div_pos
    (Nat.cast_pos.mpr <| Finset.card_pos.mpr ⟨1, by norm_num⟩)
    (Nat.cast_pos.mpr <| Q_pos a ha _)

lemma erdosTerm_nonneg (a : ℕ → ℕ) (ha : ∀ n, 0 < a (n + 1)) (n : ℕ) :
    0 ≤ erdosTerm a n :=
  le_of_lt (erdosTerm_pos a ha n)

/-- The Erdős–Straus series: `S = ∑_{n≥1} τ(n) / Q_n`. -/
def erdosSeries (a : ℕ → ℕ) : ℝ := ∑' n, erdosTerm a n

/-! ### Summability -/

/-- The Erdős–Straus series is summable when `a(n) → ∞`. -/
lemma erdosTerm_summable (a : ℕ → ℕ) (ha : ∀ n, 0 < a (n + 1))
    (ha_tendsto : Tendsto a atTop atTop) :
    Summable (erdosTerm a) := by
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, 2 ≤ a (n + 1) := by
    rcases Filter.eventually_atTop.mp (ha_tendsto.eventually_ge_atTop 2) with ⟨N, hN⟩
    exact ⟨N, fun n hn => hN _ (Nat.le_succ_of_le hn)⟩
  have h_bound :
      ∀ n ≥ N, erdosTerm a n ≤
        (n + 1 : ℝ) / (2 ^ (n - N)) / (Q a N : ℝ) := by
    have h_Q_bound : ∀ n ≥ N, Q a n ≥ 2 ^ (n - N) * Q a N := by
      intro n hn
      induction hn with
      | refl =>
          simp
      | step h ih =>
          rw [Q_succ, Nat.succ_sub h, Nat.pow_succ']
          nlinarith [hN _ h, ih]
    intro n hn
    rw [erdosTerm, div_div]
    gcongr
    · exact mul_pos (pow_pos (by norm_num) _) (Nat.cast_pos.mpr (Q_pos a ha N))
    · exact_mod_cast le_trans (Finset.card_filter_le _ _) (by norm_num)
    · exact_mod_cast
        h_Q_bound (n + 1) (by linarith) |>
          le_trans
            (Nat.mul_le_mul_right _
              (pow_le_pow_right₀ (by decide)
                (Nat.sub_le_sub_right (Nat.le_succ _) _)))
  have h_pseries : Summable (fun n : ℕ => (n + 1 : ℝ) / 2 ^ n) := by
    refine summable_of_ratio_norm_eventually_le (r := 3 / 4) ?_ ?_
    · norm_num
    · exact Filter.eventually_atTop.mpr ⟨4, fun n hn => by
        rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
        rw [div_le_iff₀ (by positivity)]
        induction hn <;> norm_num [pow_succ'] at *
        ring_nf at *
        nlinarith⟩
  rw [← summable_nat_add_iff N] at *
  refine .of_nonneg_of_le
    (fun n => erdosTerm_nonneg a ha _)
    (fun n => h_bound _ (Nat.le_add_left _ _)) ?_
  convert h_pseries.mul_right (2 ^ N / (Q a N : ℝ)) using 2
  · rfl
  · norm_num
    field_simp [pow_add, Q_cast_ne_zero a ha N, pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)]
    ring

/-! ### Auxiliary lemmas -/

/-- No integer lies in the open interval `(0, 1/2)`. -/
lemma no_int_in_Ioo_zero_half (z : ℤ) (h1 : (0 : ℝ) < z) (h2 : (z : ℝ) < 1 / 2) :
    False := by
  linarith [ show ( z : ℝ ) ≥ 1 by exact_mod_cast h1 ]

/-- `Nat.divisors n` is nonempty for `n ≥ 1`. -/
lemma divisors_card_pos (n : ℕ) (hn : 0 < n) : 0 < n.divisors.card := by
  exact Finset.card_pos.mpr ⟨ 1, by aesop ⟩

/-! ## Tail Irrationality Lemma

The core irrationality argument: if `Λ > 1` and for infinitely many `N`,
`τ(N + k) ≤ Λ^k` for all `k ≥ 1`, then the Erdős–Straus series is
irrational.

### Proof outline

Assume `S = A/B` is rational. Choose `M > Λ(2B+1)`. Since `aₙ → ∞`,
eventually `aₙ ≥ M`. Pick `N` (from the frequently condition) such that
both the divisor bound and the large-`a` bound hold simultaneously.

Define `I_N = B · Q_N · (S − partial_sum_N)`. Then:
- `I_N` is a positive integer (integrality by clearing denominators,
  positivity from tail > 0).
- `I_N < 1/2` (by bounding the tail with a geometric series).

This contradicts the fact that no integer lies in `(0, 1/2)`.
-/

/-! ### Tail splitting -/

/-- The tsum of a summable function splits as partial sum + shifted tail. -/
lemma tsum_eq_sum_add_tsum_shift {f : ℕ → ℝ} (hf : Summable f) (N : ℕ) :
    ∑' n, f n = (∑ n ∈ range N, f n) + ∑' n, f (N + n) := by
  rw [ ← hf.hasSum.tsum_eq, ← Summable.sum_add_tsum_nat_add N hf ];
  grind

/-- The shifted tail of a summable function with positive terms is positive. -/
lemma tsum_shift_pos {f : ℕ → ℝ} (hf : Summable f) (hf_pos : ∀ n, 0 < f n) (N : ℕ) :
    0 < ∑' n, f (N + n) := by
  exact lt_of_lt_of_le (hf_pos _)
    (Summable.le_tsum
      (hf.comp_injective (add_right_injective N)) 0
      (fun n _ => le_of_lt (hf_pos _)))

/-! ### Integrality of the clearing-denominators quantity -/

/-- When `b ∣ a`, the Nat division cast equals the real division. -/
private lemma nat_cast_div_eq {m n : ℕ} (h : n ∣ m) (hn : (n : ℝ) ≠ 0) :
    ((m / n : ℕ) : ℝ) = (m : ℝ) / (n : ℝ) := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (Nat.cast_ne_zero.mp hn))]
  push_cast; field_simp

/-- Each `Q(N) · erdosTerm a n` is a natural number (as a real) when
`n + 1 ≤ N`. -/
lemma Q_mul_erdosTerm_nat (a : ℕ → ℕ) (ha : ∀ n, 0 < a (n + 1))
    {n N : ℕ} (hn : n + 1 ≤ N) :
    ∃ m : ℕ, (Q a N : ℝ) * erdosTerm a n = (m : ℝ) := by
  unfold erdosTerm;
  use Q a N * (Nat.divisors (n+1)).card / Q a (n + 1);
  rw [ nat_cast_div_eq (dvd_mul_of_dvd_left (Q_dvd_Q a hn) _)
    (ne_of_gt <| Nat.cast_pos.mpr <| Q_pos a ha _) ];
  push_cast; ring

/-- The clearing-denominators quantity
`B · Q_N · (S − partial_sum_N)` is an integer, where `S = (r : ℝ)` for
some `r : ℚ`. -/
lemma clearing_denominators_is_int (a : ℕ → ℕ) (ha : ∀ n, 0 < a (n + 1))
    (r : ℚ) (hr : (r : ℝ) = erdosSeries a)
    (_hS : Summable (erdosTerm a)) (N : ℕ) :
    ∃ z : ℤ, (z : ℝ) = ↑r.den * ↑(Q a N) *
      (erdosSeries a - ∑ n ∈ range N, erdosTerm a n) := by
  have h1 : ∃ m : ℤ, ((r.den : ℝ) * (Q a N : ℝ) * (r : ℝ) = m) := by
    use r.num * Q a N
    simp +decide only [Int.cast_mul, Int.cast_natCast, Rat.cast_def]
    field_simp [Nat.cast_ne_zero.mpr r.pos.ne']
  have h2 :
      ∃ m : ℤ,
        ((r.den : ℝ) * (∑ n ∈ range N, (Q a N : ℝ) * erdosTerm a n) = m) := by
    have h_nat : ∀ n ∈ range N, ∃ m : ℕ, ((Q a N : ℝ) * erdosTerm a n = m) := by
      exact fun n hn =>
        Q_mul_erdosTerm_nat a ha (by linarith [Finset.mem_range.mp hn])
    choose! m hm using h_nat
    exact ⟨r.den * ∑ n ∈ Finset.range N, m n, by
      push_cast
      rw [Finset.sum_congr rfl hm]⟩
  obtain ⟨m₁, hm₁⟩ := h1
  obtain ⟨m₂, hm₂⟩ := h2
  use m₁ - m₂
  simp_all +decide [mul_sub]
  simp +decide [← hm₂, mul_assoc, Finset.mul_sum _ _ _]

/-! ### Tail bound -/

/-- The tail sum is bounded by a geometric series under the divisor and
growth bounds: `B · Q_N · tail_N < 1/2` when `M > Λ(2B + 1)` and the
bounds hold. -/
lemma tail_geometric_bound (a : ℕ → ℕ) (ha : ∀ n, 0 < a (n + 1))
    (hS : Summable (erdosTerm a))
    (B : ℕ) (hB : 0 < B)
    (N : ℕ) (M : ℕ) (Λ : ℝ) (hΛ : 1 < Λ)
    (hM : Λ * (2 * ↑B + 1) < ↑M)
    (ha_large : ∀ n, N < n → M ≤ a n)
    (hτ : ∀ k, 0 < k → ((N + k).divisors.card : ℝ) ≤ Λ ^ k) :
    ↑B * ↑(Q a N) *
        (erdosSeries a - ∑ n ∈ range N, erdosTerm a n) < 1 / 2 := by
  have hM_nat_pos : 0 < M := by
    exact Nat.pos_of_ne_zero (by
      rintro rfl
      norm_num at hM
      nlinarith)
  have hM_real_pos : (0 : ℝ) < M := by
    exact_mod_cast hM_nat_pos
  have hM_real_ne : (M : ℝ) ≠ 0 :=
    ne_of_gt hM_real_pos
  have h_tail :
      erdosSeries a - ∑ n ∈ range N, erdosTerm a n =
        ∑' n, erdosTerm a (N + n) := by
    rw [erdosSeries, ← Summable.sum_add_tsum_nat_add]
    exacts [by rw [add_sub_cancel_left]; ac_rfl, hS]
  have h_bound :
      ∑' n, erdosTerm a (N + n) ≤
        ∑' n, (Λ / (M : ℝ)) ^ (n + 1) / (Q a N : ℝ) := by
    apply Summable.tsum_le_tsum
    · intro n
      have h_term_bound :
          ((N + n + 1).divisors.card : ℝ) / (Q a (N + n + 1) : ℝ) ≤
            (Λ ^ (n + 1) : ℝ) / (Q a N * M ^ (n + 1)) := by
        gcongr
        · exact mul_pos
            (Nat.cast_pos.mpr (Q_pos a ha N))
            (pow_pos (Nat.cast_pos.mpr hM_nat_pos) _)
        · grind +locals
        · induction n with
          | zero =>
              norm_num [Nat.add_assoc, pow_succ, Q] at *
              exact mul_le_mul_of_nonneg_left
                (mod_cast ha_large _ (Nat.lt_succ_self _))
                (Nat.cast_nonneg _)
          | succ n _ =>
              norm_num [Nat.add_assoc, pow_succ, Q] at *
              nlinarith [
                show (M : ℝ) ≤ a (N + (n + 2)) by
                  exact_mod_cast ha_large _ (by linarith),
                show (0 : ℝ) ≤ Q a N * M ^ n by positivity,
                show (0 : ℝ) ≤ Q a (N + n) * a (N + (n + 1)) by positivity]
      calc
        erdosTerm a (N + n) =
            ((N + n + 1).divisors.card : ℝ) / (Q a (N + n + 1) : ℝ) := by
          simp [erdosTerm, Nat.add_assoc]
        _ ≤ (Λ ^ (n + 1) : ℝ) / (Q a N * M ^ (n + 1)) := h_term_bound
        _ = (Λ / (M : ℝ)) ^ (n + 1) / (Q a N : ℝ) := by
          rw [div_pow]
          field_simp [hM_real_ne, Q_cast_ne_zero a ha N, pow_ne_zero _ hM_real_ne]
    · exact hS.comp_injective (add_right_injective N)
    · exact Summable.mul_right _
        (summable_geometric_of_lt_one (by positivity)
          (by
            rw [div_lt_iff₀ hM_real_pos]
            nlinarith) |>
          Summable.comp_injective <| Nat.succ_injective)
  have h_geo_series :
      ∑' n, (Λ / (M : ℝ)) ^ (n + 1) / (Q a N : ℝ) =
        (Λ / (M : ℝ)) / (1 - Λ / (M : ℝ)) / (Q a N : ℝ) := by
    norm_num [_root_.pow_succ', div_eq_mul_inv, tsum_mul_right]
    exact Or.inl (by
      erw [← tsum_geometric_of_lt_one (by positivity) (by
        rw [mul_inv_lt_iff₀ hM_real_pos]
        nlinarith)]
      erw [← tsum_mul_left])
  have h_final_bound :
      (B : ℝ) * (Q a N : ℝ) *
          ((Λ / (M : ℝ)) / (1 - Λ / (M : ℝ)) / (Q a N : ℝ)) < 1 / 2 := by
    field_simp
    rw [div_lt_iff₀] <;>
      nlinarith [
        show (0 : ℝ) < Q a N by exact_mod_cast Q_pos a ha N,
        show (0 : ℝ) < Λ * Q a N by
          exact mul_pos (by positivity) (by exact_mod_cast Q_pos a ha N),
        mul_div_cancel₀ Λ hM_real_ne]
  exact h_tail.symm ▸
    lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left h_bound <| by positivity)
      (by
        rw [h_geo_series]
        exact h_final_bound)

/-! ### Main tail lemma -/

/-- **Tail Irrationality Lemma** (Lemma 1 of the note).
If `Λ > 1` and for infinitely many `N`, `τ(N + k) ≤ Λ^k` for all `k ≥ 1`,
then the Erdős–Straus series is irrational. -/
theorem tail_irrationality_lemma
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a (n + 1))
    (ha_tendsto : Tendsto a atTop atTop)
    (Λ : ℝ) (hΛ : 1 < Λ)
    (hbound : ∃ᶠ N in atTop, ∀ k, 0 < k →
      ((N + k).divisors.card : ℝ) ≤ Λ ^ k) :
    Irrational (erdosSeries a) := by
  by_contra h;
  obtain ⟨r, hr⟩ : ∃ r : ℚ, (r : ℝ) = erdosSeries a := by
    simpa [ eq_comm ] using Classical.not_not.1 h
  set B := r.den with hB_def
  have hB_pos : 0 < B := by
    exact r.pos;
  obtain ⟨M, hM⟩ : ∃ M : ℕ, Λ * (2 * B + 1) < M := by
    exact exists_nat_gt _;
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ n ≥ N₀, M ≤ a n := by
    exact Filter.eventually_atTop.mp ( ha_tendsto.eventually_ge_atTop M );
  obtain ⟨N₁, hN₁⟩ :
      ∃ N₁ ≥ N₀, ∀ k > 0, ((N₁ + k).divisors.card : ℝ) ≤ Λ ^ k := by
    exact Frequently.forall_exists_of_atTop hbound N₀;
  obtain ⟨z, hz⟩ :
      ∃ z : ℤ,
        (z : ℝ) = B * Q a N₁ *
          (erdosSeries a - ∑ n ∈ range N₁, erdosTerm a n) := by
    apply_rules [ clearing_denominators_is_int ];
    exact erdosTerm_summable a ha ha_tendsto;
  have hz_pos : 0 < z := by
    have h_tail_pos : 0 < erdosSeries a - ∑ n ∈ range N₁, erdosTerm a n := by
      have h_tail_pos : 0 < ∑' n, erdosTerm a (N₁ + n) := by
        apply tsum_shift_pos;
        · exact erdosTerm_summable a ha ha_tendsto;
        · exact fun n => erdosTerm_pos a ha n;
      have h_tail_pos :
          erdosSeries a =
            ∑ n ∈ range N₁, erdosTerm a n + ∑' n, erdosTerm a (N₁ + n) := by
        simpa [erdosSeries] using
          tsum_eq_sum_add_tsum_shift (erdosTerm_summable a ha ha_tendsto) N₁
      linarith;
    exact_mod_cast hz.symm ▸
      mul_pos
        (mul_pos (Nat.cast_pos.mpr hB_pos) (Nat.cast_pos.mpr (Q_pos a ha N₁)))
        h_tail_pos;
  have hz_lt_half :
      B * Q a N₁ *
        (erdosSeries a - ∑ n ∈ range N₁, erdosTerm a n) < 1 / 2 := by
    apply tail_geometric_bound a ha (erdosTerm_summable a ha ha_tendsto)
      B hB_pos N₁ M Λ hΛ hM
      (fun n hn => hN₀ n (by linarith)) hN₁.right;
  linarith [ show ( z : ℝ ) ≥ 1 by exact_mod_cast hz_pos ]

/-! ## Tao–Teräväinen Theorem

The Tao–Teräväinen theorem is a deep result from analytic number theory
asserting that there exist arbitrarily long strings of consecutive integers
whose number of prime factors grows at most linearly. Combined with the
elementary bound `τ(n) ≤ 2^{Ω(n)}`, this provides the exponential divisor
bound used in the tail irrationality lemma.

The elementary bound `τ(n) ≤ 2^{Ω(n)}`, where `Ω(n)` is the number of
prime factors with multiplicity, follows from
`τ(n) = ∏ (αᵢ + 1) ≤ ∏ 2^αᵢ`. This is the bridge between the
Tao–Teräväinen bound on `Ω` and the divisor bound used in the tail
irrationality lemma.
-/

/-
`τ(n) ≤ 2^{Ω(n)}`: the number of divisors is at most `2` to the power
of the number of prime factors counted with multiplicity.
-/
lemma divisors_card_le_two_pow_omega (n : ℕ) (hn : n ≠ 0) :
    n.divisors.card ≤ 2 ^ (n.factorization.sum fun _ k => k) := by
  rw [ Nat.card_divisors hn ];
  rw [ Finsupp.sum ];
  rw [ ← Finset.prod_pow_eq_pow_sum ];
  exact Finset.prod_le_prod' fun p hp => by
    induction n.factorization p <;> simp_all +decide [Nat.pow_succ']
    nlinarith

/-- There exists `Λ > 1` such that for infinitely many `N`,
`τ(N + k) ≤ Λ^k` for all `k ≥ 1`. -/
theorem tao_teravainen_divisors_le : ∃ Λ : ℝ, 1 < Λ ∧
    (∃ᶠ N in atTop, ∀ k, 0 < k → ((N + k).divisors.card : ℝ) ≤ Λ ^ k) := by
  obtain ⟨C, hC_pos, hC⟩ := tao_teravainen
  refine ⟨(2 : ℝ) ^ C, ?_, ?_⟩
  · rw [Real.one_lt_rpow_iff_of_pos (by norm_num : (0:ℝ) < 2)]
    left; exact ⟨by norm_num, hC_pos⟩
  · exact hC.mono fun N hN k hk => by
      have hNk_pos : 0 < N + k := Nat.pos_of_ne_zero (by omega)
      have hNk_ne : N + k ≠ 0 := Nat.pos_iff_ne_zero.mp hNk_pos
      set Ω := (N + k).factorization.sum fun _ k => k
      have hΩ := (hN k hk).2
      calc ((N + k).divisors.card : ℝ)
          ≤ ((2 ^ Ω : ℕ) : ℝ) := by
            exact_mod_cast divisors_card_le_two_pow_omega _ hNk_ne
        _ = (2 : ℝ) ^ (Ω : ℕ) := by push_cast; ring
        _ = (2 : ℝ) ^ (Ω : ℝ) := (Real.rpow_natCast 2 Ω).symm
        _ ≤ (2 : ℝ) ^ (C * k) := by
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast hΩ)
        _ = ((2 : ℝ) ^ C) ^ (k : ℝ) := Real.rpow_mul (by norm_num) C k
        _ = ((2 : ℝ) ^ C) ^ k := Real.rpow_natCast _ k

/-! ## Main Theorem

We combine the tail irrationality lemma with the Tao–Teräväinen theorem
to obtain the resolution of Erdős Problem #258: for any sequence of
positive integers `(aₙ)` tending to infinity, the series
`∑ τ(n)/(a₁ a₂ ⋯ aₙ)` is irrational.
-/

/-- **Erdős Problem #258**.
For any sequence of positive integers `(aₙ)` with `aₙ → ∞`,
the series `∑ τ(n)/(a₁a₂⋯aₙ)` is irrational. -/
theorem erdos_258 (a : ℕ → ℕ) (ha : ∀ n, 0 < a (n + 1))
    (ha_tendsto : Tendsto a atTop atTop) :
    Irrational (erdosSeries a) := by
  obtain ⟨Λ, hΛ, hbound⟩ := tao_teravainen_divisors_le
  exact tail_irrationality_lemma a ha ha_tendsto Λ hΛ hbound

#print axioms Erdos258.erdos_258
-- 'Erdos258.erdos_258' depends on axioms: [propext, tao_teravainen, Classical.choice, Quot.sound]

end

end Erdos258
