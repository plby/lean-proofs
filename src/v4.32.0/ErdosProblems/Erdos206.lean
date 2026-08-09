/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 206.
https://www.erdosproblems.com/forum/thread/206

Informal authors:
- Vjekoslav Kovač

Formal authors:
- Aristotle
- Matteo Del Vecchio

URLs:
- https://www.erdosproblems.com/forum/thread/206#post-5989
- https://gist.githubusercontent.com/madeve-unipi/0920783513a1a00af4a14660852df60e/raw/522569070c2ec3a0fc7d8dfd7f95f3de2b2e3103/Erdos206.lean
-/
/-
Authors: Matteo Del Vecchio, Aristotle (Harmonic)
Released under Apache 2.0 license.
-/

import Mathlib

namespace Erdos206

set_option linter.style.setOption false
set_option linter.flexible false

/-!
# Erdős Problem #206: Non-greedy Egyptian Underapproximations

We prove that the set of positive real numbers with eventually greedy best Egyptian
underapproximations has Lebesgue measure zero.

## Main result

* `Erdos206.EgyptianFractions.erdos_206`: The set of positive reals with eventually greedy
  best Egyptian underapproximations has Lebesgue measure zero. This answers a question of Erdős
  and Graham [EG80, p. 31] in the negative, and was formulated as Problem #206 on Bloom's
  website *Erdős problems*.

## Proof overview

The proof follows the approach of Kovač [1], reducing the problem to studying two-term
underapproximations. The key steps are:

1. **Lemma 1** (`non_greedy_measure_bound_strict`): For every integer `i ≥ 1000`, at least 1‰
   of the numbers in `(1/i, 1/(i-1)]` have non-greedy best two-term Egyptian
   underapproximations. This is proved by constructing explicit non-greedy pairs using the
   sequence `x_k = i(i+1)·(i(i+1)+2k)/(i(i+1)-2k)`.

2. **Inductive estimate** (`inductive_estimate`): The key bound
   `|X_{s,t+2}| ≤ (1999/2000) · |X_{s,t}|` for `100 ≤ s < t`, where `X_{s,t}` is the set of
   numbers in `(0, H_s]` admitting a compatible sequence giving best `n`-term approximations
   for all `n` from `s` to `t`.

3. **Main theorem** (`erdos_206`): By geometric decay, each `⋂_t X_{s,t}` has measure zero,
   and the set of eventually greedy numbers is contained in `⋃_s ⋂_t X_{s,t}`.

## References

[1] V. Kovač, *On eventually greedy best underapproximations by Egyptian fractions*
-/

open scoped BigOperators ENNReal
open Finset MeasureTheory Set

namespace EgyptianFractions

/-! ## §1. Core Definitions -/

/-- The Egyptian fraction sum: `∑_{m ∈ S} 1/m` for a finset of natural numbers. -/
noncomputable def egyptianSum (S : Finset ℕ) : ℝ :=
  S.sum (fun m => (1 : ℝ) / m)

/-- All elements of the finset are positive (valid denominators). -/
def ValidEgyptian (S : Finset ℕ) : Prop :=
  ∀ m ∈ S, 0 < m

/-- `S` is an Egyptian underapproximation of `x`: valid denominators and sum < x. -/
def IsUnderapprox (S : Finset ℕ) (x : ℝ) : Prop :=
  ValidEgyptian S ∧ egyptianSum S < x

/-- `S` achieves the best `n`-term Egyptian underapproximation of `x`. -/
def IsBestNTerm (S : Finset ℕ) (n : ℕ) (x : ℝ) : Prop :=
  S.card = n ∧ IsUnderapprox S x ∧
    ∀ T : Finset ℕ, T.card = n → IsUnderapprox T x → egyptianSum T ≤ egyptianSum S

/-- The `n`-th harmonic number: `H_n = ∑_{k=1}^{n} 1/k`. -/
noncomputable def harmonicNumber (n : ℕ) : ℝ :=
  (Finset.range n).sum (fun k => (1 : ℝ) / (↑k + 1))

/-- `x` has eventually greedy best Egyptian underapproximations. -/
def EventuallyGreedy (x : ℝ) : Prop :=
  x > 0 ∧ ∃ (m : ℕ → ℕ), StrictMono m ∧ (∀ k, 0 < m k) ∧
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      IsBestNTerm (Finset.image m (Finset.range n)) n x

/-- The set `X_{s,t}`: numbers in `(0, H_s]` with a compatible sequence
    giving best `n`-term underapproximations for all `n` from `s` to `t`. -/
def X_set (s t : ℕ) : Set ℝ :=
  {x : ℝ | 0 < x ∧ x ≤ harmonicNumber s ∧
    ∃ (m : ℕ → ℕ), StrictMono m ∧ (∀ k, 0 < m k) ∧
      ∀ n, s ≤ n → n ≤ t →
        IsBestNTerm (Finset.image m (Finset.range n)) n x}

/-! ## §2. Basic Properties of Definitions -/

lemma harmonicNumber_mono : Monotone harmonicNumber := by
  intro a b hab
  unfold harmonicNumber
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
  intro i _ _
  positivity

lemma X_set_subset_Ioc (s t : ℕ) :
    X_set s t ⊆ Set.Ioc 0 (harmonicNumber s) :=
  fun _ hx => ⟨hx.1, hx.2.1⟩

/-- `X_{s,t}` is antitone in `t`. -/
lemma X_set_antitone_t (s : ℕ) : Antitone (X_set s) := by
  intro t₁ t₂ h x hx
  exact ⟨hx.1, hx.2.1, hx.2.2.choose, hx.2.2.choose_spec.1,
    hx.2.2.choose_spec.2.1, fun n hs hn => hx.2.2.choose_spec.2.2 n hs (le_trans hn h)⟩

/-- `X_{s₁, t} ⊆ X_{s₂, t}` when `s₁ ≤ s₂`. -/
lemma X_set_mono_s (s₁ s₂ t : ℕ) (h : s₁ ≤ s₂) :
    X_set s₁ t ⊆ X_set s₂ t := by
  intro x hx
  refine ⟨hx.1, le_trans hx.2.1 (harmonicNumber_mono h), ?_⟩
  obtain ⟨m, hm_mono, hm_pos, hm_best⟩ := hx.2.2
  exact ⟨m, hm_mono, hm_pos, fun n hs hn => hm_best n (le_trans h hs) hn⟩

/-! ## §3. Lemma 1: Non-greedy Best 2-term Underapproximations

This section proves that for every `i ≥ 1000`, at least 1‰ of the numbers in `(1/i, 1/(i-1)]`
have non-greedy best two-term Egyptian underapproximations (with strict inequality).
-/

/-- The sequence `x_k = i(i+1)·(i(i+1)+2k)/(i(i+1)-2k)`. -/
noncomputable def x_seq (i : ℕ) (k : ℕ) : ℝ :=
  (i : ℝ) * (i + 1) * ((i : ℝ) * (i + 1) + 2 * k) / ((i : ℝ) * (i + 1) - 2 * k)

lemma x_seq_pos (i : ℕ) (k : ℕ) (hi : 1 ≤ i)
    (hk : 2 * (k : ℝ) < (i : ℝ) * (i + 1)) :
    0 < x_seq i k := by
  exact div_pos (mul_pos (by positivity) (by positivity)) (sub_pos.mpr hk)

lemma x_seq_ge (i : ℕ) (k : ℕ)
    (hk : 2 * (k : ℝ) < (i : ℝ) * (i + 1)) :
    (i : ℝ) * (i + 1) ≤ x_seq i k := by
  unfold x_seq
  rw [le_div_iff₀] <;> nlinarith

lemma good_interval_length (i : ℕ) (k : ℕ) (hi : 2 ≤ i)
    (hfrac : x_seq i k - ↑(Nat.floor (x_seq i k)) ≥ 1 / 3)
    (hbound : x_seq i k < 6 / 5 * (i : ℝ) ^ 2) :
    1 / ↑(Nat.floor (x_seq i k)) - 1 / x_seq i k ≥ 25 / (108 * (i : ℝ)^4) := by
  by_cases h : ⌊x_seq i k⌋₊ = 0 <;> simp_all +decide [ Nat.floor_eq_zero ]
  · contrapose! h
    refine le_trans ?_ ( x_seq_ge i k ?_ )
    · nlinarith only [ show ( i : ℝ ) ≥ 2 by norm_cast ]
    · contrapose! hfrac
      exact lt_of_le_of_lt
        ( div_nonpos_of_nonneg_of_nonpos ( by positivity ) ( by linarith ) )
        ( by positivity )
  · rw [ inv_sub_inv, div_le_div_iff₀ ] <;> try positivity
    · nlinarith [
        Nat.floor_le ( show 0 ≤ x_seq i k by positivity ),
        Nat.lt_floor_add_one ( x_seq i k ),
        pow_pos ( by positivity : 0 < ( i : ℝ ) ) 3,
        pow_pos ( by positivity : 0 < ( i : ℝ ) ) 4 ]
    · exact mul_pos ( Nat.cast_pos.mpr ( Nat.floor_pos.mpr h ) ) ( by positivity )
    · exact ne_of_gt <| Nat.cast_pos.mpr <| Nat.floor_pos.mpr h

lemma x_seq_diff_bounds (i : ℕ) (l : ℕ) (hi : 1000 ≤ i)
    (hl_lower : (i : ℝ) * (i + 1) / 100 ≤ l)
    (hl_upper : (l : ℝ) ≤ 3 * (i : ℝ) * (i + 1) / 200) :
    4 + 1/3 ≤ x_seq i (2 * l + 1) - x_seq i (2 * l) ∧
    x_seq i (2 * l + 1) - x_seq i (2 * l) ≤ 4 + 2/3 := by
  constructor
  · unfold x_seq
    rw [ div_sub_div, le_div_iff₀ ] <;> norm_num <;> ring_nf at *
    · nlinarith [ ( by norm_cast : ( 1000 : ℝ ) ≤ i ), pow_pos ( by positivity : 0 < ( i : ℝ ) ) 3 ]
    · nlinarith [ ( by norm_cast : ( 1000 : ℝ ) ≤ i ) ]
    · nlinarith [ ( by norm_cast : ( 1000 : ℝ ) ≤ i ) ]
    · nlinarith [ ( by norm_cast : ( 1000 : ℝ ) ≤ i ) ]
  · unfold x_seq
    rw [ div_sub_div, div_le_iff₀ ] <;> norm_num <;>
      try nlinarith [ ( by norm_cast : ( 1000 : ℝ ) ≤ i ) ]
    · nlinarith [
        ( by norm_cast : ( 1000 : ℝ ) ≤ i ),
        pow_pos ( by positivity : 0 < ( i : ℝ ) ) 3,
        pow_pos ( by positivity : 0 < ( i : ℝ ) ) 4,
        pow_pos ( by positivity : 0 < ( i : ℝ ) ) 5,
        pow_pos ( by positivity : 0 < ( i : ℝ ) ) 6 ]
    · exact mul_pos
        ( by nlinarith [ ( by norm_cast : ( 1000 : ℝ ) ≤ i ) ] )
        ( by nlinarith [ ( by norm_cast : ( 1000 : ℝ ) ≤ i ) ] )

lemma fractional_part_lower_bound (a b : ℝ) (ha : 0 ≤ a)
    (h_diff_lower : 4 + 1 / 3 ≤ b - a)
    (h_diff_upper : b - a ≤ 4 + 2 / 3) :
    a - ↑(Nat.floor a) ≥ 1 / 3 ∨ b - ↑(Nat.floor b) ≥ 1 / 3 := by
  by_contra h_contra
  have h_floor_eq : ⌊b⌋₊ = ⌊a⌋₊ + 4 := by
    exact
      (Nat.floor_eq_iff ( by linarith )).2
        ⟨ by
            push_cast
            linarith [ Nat.floor_le ha, not_or.mp h_contra ],
          by
            push_cast
            linarith [ Nat.lt_floor_add_one a, not_or.mp h_contra ] ⟩
  push Not at h_contra
  norm_num [h_floor_eq] at h_contra
  linarith [Nat.floor_le ha, Nat.lt_floor_add_one a]

lemma L_set_card_bound (i : ℕ) (hi : 1000 ≤ i) :
    (i : ℝ)^2 / 200 ≤
      (Finset.Icc (Nat.ceil ((i : ℝ) * (i + 1) / 100))
        (Nat.floor (3 * (i : ℝ) * (i + 1) / 200))).card := by
  norm_num [ Finset.card_map, Finset.card_range ]
  rw [ Nat.cast_sub ] <;> norm_num
  · nlinarith [
      Nat.lt_floor_add_one ( ( 3 : ℝ ) * i * ( i + 1 ) / 200 ),
      Nat.ceil_lt_add_one
        ( show 0 ≤ ( i : ℝ ) * ( i + 1 ) / 100 by positivity ),
      ( by norm_cast : ( 1000 : ℝ ) ≤ i ) ]
  · linarith [ Nat.lt_floor_add_one ( ( 3 : ℝ ) * i * ( i + 1 ) / 200 ) ]

lemma x_seq_upper_bound (i : ℕ) (l : ℕ) (hi : 1000 ≤ i)
    (hl_upper : (l : ℝ) ≤ 3 * (i : ℝ) * (i + 1) / 200) :
    x_seq i (2 * l + 1) < 6/5 * (i : ℝ)^2 := by
  unfold x_seq
  rw [ div_lt_iff₀ ] <;> norm_num <;>
    nlinarith [ ( by norm_cast : ( 1000 : ℝ ) ≤ i ), pow_two ( i - 1000 : ℝ ) ]

lemma total_measure_bound (i : ℕ) (hi : 1000 ≤ i) :
    (i : ℝ)^2 / 200 * (25 / (108 * (i : ℝ)^4)) ≥
      1/1000 * (1/((i : ℝ) - 1) - 1/i) := by
  field_simp
  nlinarith [
    show ( i : ℝ ) ≥ 1000 by norm_cast,
    div_mul_cancel₀ ( i : ℝ ) ( show ( i : ℝ ) - 1 ≠ 0 by
      linarith [ show ( i : ℝ ) ≥ 1000 by norm_cast ] ) ]

/-- `x_{k+1} - x_k > 1` for `k` in the relevant range, ensuring distinct floors. -/
lemma x_seq_diff_gt_one (i : ℕ) (k : ℕ)
    (hk : 2 * ((k : ℝ) + 1) < (i : ℝ) * (i + 1)) :
    x_seq i (k + 1) - x_seq i k > 1 := by
  unfold x_seq
  rw [gt_iff_lt, lt_sub_iff_add_lt', lt_div_iff₀] <;> norm_num
  · rw [div_add_one, div_mul_eq_mul_div, div_lt_iff₀] <;> nlinarith
  · exact_mod_cast hk

/-- The non-greedy pair is strictly better than any greedy pair. -/
lemma non_greedy_strict_inequality (i : ℕ) (k : ℕ) (hi : 1000 ≤ i)
    (hk : 2 * (k : ℝ) < (i : ℝ) * (i + 1))
    (x : ℝ)
    (hx_upper : x ≤ (1 : ℝ) / i + 1 / ↑(⌊x_seq i k⌋₊))
    (j : ℕ) (hj : 0 < j) (hj'' : (1 : ℝ) / i + 1 / j < x) :
    (1 : ℝ) / i + 1 / j < 1 / (i+1) + 1 / (i*(i+1)/2 + k) := by
  contrapose! hj''
  refine le_trans hx_upper ?_
  gcongr
  refine Nat.le_floor ?_
  contrapose! hj''
  rw [ div_add_div, div_add_div, div_lt_div_iff₀ ] <;> try positivity
  unfold x_seq at *
  rw [ div_lt_iff₀ ] at hj'' <;> nlinarith [ ( by norm_cast : ( 1000 : ℝ ) ≤ i ) ]

/-- Combined strict version of good interval predicate. -/
lemma good_interval_predicate_strict (i : ℕ) (k : ℕ) (hi : 1000 ≤ i)
    (hk : 2 * (k : ℝ) < (i : ℝ) * (i + 1))
    (x : ℝ) (hx_lower : (1 : ℝ) / i + 1 / x_seq i k < x)
    (hx_upper : x ≤ (1 : ℝ) / i + 1 / ↑(⌊x_seq i k⌋₊)) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ≠ b ∧ a ≠ i ∧ b ≠ i ∧
      (1 : ℝ) / a + 1 / b < x ∧
      ∀ j : ℕ, 0 < j → j ≠ i → (1 : ℝ) / i + 1 / j < x →
        (1 : ℝ)/i + 1/j < 1/a + 1/b := by
  refine ⟨ i + 1, i * ( i + 1 ) / 2 + k, ?_, ?_, ?_, ?_, ?_, ?_ ⟩ <;> norm_num [ Nat.succ_div ]
  · exact Or.inl ( by nlinarith only [ hi ] )
  · nlinarith [
      Nat.div_mul_cancel ( show 2 ∣ i * ( i + 1 ) from
        even_iff_two_dvd.mp ( by
          simp +arith +decide [ mul_add, parity_simps ] ) ) ]
  · nlinarith [ Nat.div_add_mod ( i * ( i + 1 ) ) 2, Nat.mod_lt ( i * ( i + 1 ) ) two_pos ]
  · refine ⟨ ?_, ?_ ⟩
    · convert hx_lower using 1
      norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_two_of_bodd ]
      ring_nf
      unfold x_seq
      ring_nf
      grind
    · intro j hj₁ hj₂ hj₃
      convert non_greedy_strict_inequality i k hi (mod_cast hk) x _ j hj₁ _ using 1
        <;> norm_num at * <;> try linarith
      rw [ Nat.cast_div ] <;> norm_cast
      exact even_iff_two_dvd.mp ( by
        simp +arith +decide [ mul_add, parity_simps ] )

set_option maxHeartbeats 800000 in
-- This construction combines long interval, disjointness, and measure estimates.
/-- **Lemma 1** (Kovač [1, Lemma 1], strict version): For `i ≥ 1000`, there exists a measurable
    set `E ⊆ (1/i, 1/(i-1)]` of measure `≥ 1/1000 · (1/(i-1) - 1/i)` such that every `x ∈ E`
    has a non-greedy best two-term Egyptian underapproximation with strict inequality. -/
lemma non_greedy_measure_bound_strict (i : ℕ) (hi : 1000 ≤ i) :
    ∃ E : Set ℝ, MeasurableSet E ∧
      E ⊆ Set.Ioc ((1 : ℝ)/i) (1/((i : ℝ) - 1)) ∧
      volume E ≥ ENNReal.ofReal (1/1000 * (1/((i : ℝ) - 1) - 1/i)) ∧
      ∀ x ∈ E, ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ≠ b ∧ a ≠ i ∧ b ≠ i ∧
        (1 : ℝ)/a + 1/b < x ∧
        ∀ j : ℕ, 0 < j → j ≠ i → (1 : ℝ)/i + 1/j < x →
          (1 : ℝ)/i + 1/j < 1/a + 1/b := by
  obtain ⟨L, hL⟩ :
      ∃ L : Finset ℕ,
        (i : ℝ)^2 / 200 ≤ L.card ∧
        ∀ l ∈ L,
          2 * (l : ℝ) < (i : ℝ) * (i + 1) ∧
          x_seq i l - ↑(Nat.floor (x_seq i l)) ≥ 1/3 ∧
          x_seq i l < 6/5 * (i : ℝ)^2 := by
    have h_k_exists :
        ∀ l ∈ Finset.Icc
            (Nat.ceil ((i : ℝ) * (i + 1) / 100))
            (Nat.floor (3 * (i : ℝ) * (i + 1) / 200)),
          ∃ k ∈ [2 * l, 2 * l + 1],
            x_seq i k - ↑(Nat.floor (x_seq i k)) ≥ 1/3 := by
      intro l hl
      obtain ⟨h_diff_lower, h_diff_upper⟩ :
          4 + 1/3 ≤ x_seq i (2 * l + 1) - x_seq i (2 * l) ∧
            x_seq i (2 * l + 1) - x_seq i (2 * l) ≤ 4 + 2/3 := by
        apply x_seq_diff_bounds i l hi
          (by
            exact Nat.le_of_ceil_le ( Finset.mem_Icc.mp hl |>.1 ))
          (by
            exact le_trans ( Nat.cast_le.mpr ( Finset.mem_Icc.mp hl |>.2 ) )
              ( Nat.floor_le ( by positivity ) ))
      have := fractional_part_lower_bound
        ( x_seq i ( 2 * l ) ) ( x_seq i ( 2 * l + 1 ) ) ?_ ?_ ?_ <;>
        norm_num at *
      · exact this
      · refine div_nonneg ?_ ?_ <;> norm_num
        · positivity
        · rw [Nat.le_floor_iff (by positivity)] at hl
          nlinarith [(by norm_cast : (1000 : ℝ) ≤ i)]
      · linarith
      · linarith
    choose! k hk₁ hk₂ using h_k_exists
    refine ⟨ Finset.image k
        ( Finset.Icc ⌈ ( i : ℝ ) * ( i + 1 ) / 100⌉₊
          ⌊3 * ( i : ℝ ) * ( i + 1 ) / 200⌋₊ ),
        ?_, ?_ ⟩ <;>
      norm_num
    · rw [ Finset.card_image_of_injOn ]
      · convert L_set_card_bound i hi using 1
      · norm_num +zetaDelta at *
        intro l hl l' hl' hkl
        cases hk₁ l ( Nat.le_of_ceil_le hl.1 ) hl.2 <;>
          cases hk₁ l' ( Nat.le_of_ceil_le hl'.1 ) hl'.2 <;>
          omega
    · rintro l x hx₁ hx₂ rfl
      refine ⟨ ?_,
        hk₂ x ( Finset.mem_Icc.mpr ⟨ Nat.ceil_le.mpr hx₁, hx₂ ⟩ ) |>
          le_trans <| le_rfl,
        ?_ ⟩
      · have := hk₁ x (Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hx₁, hx₂⟩)
        norm_num at this
        rw [ Nat.le_floor_iff ( by positivity ) ] at hx₂
        rcases this with ( h | h ) <;> rw [ h ] <;> push_cast <;>
          nlinarith [ ( by norm_cast : ( 1000 : ℝ ) ≤ i ) ]
      · have := x_seq_diff_bounds i x hi hx₁
          ( Nat.floor_le ( by positivity ) |> le_trans ( Nat.cast_le.mpr hx₂ ) )
        have := x_seq_upper_bound i x hi
          ( Nat.floor_le ( by positivity ) |> le_trans ( Nat.cast_le.mpr hx₂ ) )
        norm_num at *
        cases hk₁ x hx₁ hx₂ <;> simp_all +decide
        linarith
  refine ⟨ ⋃ l ∈ L,
      Set.Ioc ( 1 / ( i : ℝ ) + 1 / x_seq i l )
        ( 1 / ( i : ℝ ) + 1 / ⌊x_seq i l⌋₊ ),
      ?_, ?_, ?_, ?_ ⟩ <;>
    norm_num
  · exact MeasurableSet.iUnion fun l => MeasurableSet.iUnion fun hl => measurableSet_Ioc
  · intro l hl
    specialize hL
    have := hL.2 l hl
    norm_num at *
    refine Set.Ioc_subset_Ioc ?_ ?_ <;> norm_num at *
    · exact le_of_lt ( x_seq_pos i l ( by linarith ) ( by linarith ) )
    · have h_floor : ⌊x_seq i l⌋₊ ≥ i * (i + 1) := by
        exact Nat.le_floor <| by
          push_cast
          exact x_seq_ge i l (by linarith)
      field_simp
      rw [ add_div', div_le_div_iff₀ ] <;>
        nlinarith only [
          show ( i : ℝ ) ≥ 1000 by norm_cast,
          show ( ⌊x_seq i l⌋₊ : ℝ ) ≥ i * ( i + 1 ) by
            exact_mod_cast h_floor ]
  · -- Apply the measure bound.
    have h_measure_bound :
        volume (⋃ l ∈ L,
          Set.Ioc ((1 : ℝ) / i + 1 / x_seq i l)
            ((1 : ℝ) / i + 1 / ⌊x_seq i l⌋₊)) ≥
          ENNReal.ofReal (L.card * (25 / (108 * (i : ℝ)^4))) := by
      have h_measure :
          ∀ l ∈ L,
            volume (Set.Ioc (1 / (i : ℝ) + 1 / x_seq i l)
              (1 / (i : ℝ) + 1 / ⌊x_seq i l⌋₊)) ≥
              ENNReal.ofReal (25 / (108 * (i : ℝ)^4)) := by
        intro l hl
        have h_interval_length :
            1 / ⌊x_seq i l⌋₊ - 1 / x_seq i l ≥
              25 / (108 * (i : ℝ)^4) := by
          apply good_interval_length i l (by linarith)
            (hL.right l hl).right.left
            (hL.right l hl).right.right
        simp +zetaDelta at *
        exact ENNReal.ofReal_le_ofReal h_interval_length
      rw [ MeasureTheory.measure_biUnion_finset ]
      · exact le_trans
          ( by norm_num [ ENNReal.ofReal_mul ( Nat.cast_nonneg _ ) ] )
          ( Finset.sum_le_sum h_measure )
      · intros l hl l' hl' hll'
        cases lt_or_gt_of_ne hll' <;>
          simp_all +decide [ Set.disjoint_iff_inter_eq_empty, Set.Ioc_inter_Ioc ]
        · rw [ Set.Ioc_eq_empty_of_le ]
          simp +zetaDelta at *
          refine Or.inl ( Or.inr ?_ )
          gcongr
          · exact x_seq_pos i l ( by linarith ) ( by linarith [ hL.2 l hl ] )
          · have h_diff : x_seq i l' - x_seq i l > 1 := by
              have h_diff :
                  ∀ k : ℕ,
                    2 * (k + 1) < (i : ℝ) * (i + 1) →
                      x_seq i (k + 1) - x_seq i k > 1 :=
                fun k hk => x_seq_diff_gt_one i k hk
              have h_diff : ∀ k : ℕ, l < k → k ≤ l' → x_seq i k - x_seq i l > 1 := by
                intros k hk₁ hk₂
                induction hk₁ <;> norm_num at *
                · exact h_diff l ( by
                    linarith [ hL.2 l hl, hL.2 l' hl',
                      show ( l : ℝ ) + 1 ≤ l' by norm_cast ] )
                · rename_i k hk₁ hk₂
                  linarith [
                    h_diff k ( by
                      linarith [ hL.2 l' hl',
                        show ( k : ℝ ) + 1 ≤ l' by norm_cast ] ),
                    ‹k ≤ l' → 1 < x_seq i k - x_seq i l› ( by linarith ) ]
              exact h_diff l' ‹_› le_rfl
            exact le_trans ( by linarith ) ( Nat.sub_one_lt_floor _ |> le_of_lt )
        · rw [ Set.Ioc_eq_empty_of_le ]
          refine le_trans
            (show
              min
                ((i : ℝ)⁻¹ + (⌊x_seq i l⌋₊ : ℝ)⁻¹)
                ((i : ℝ)⁻¹ + (⌊x_seq i l'⌋₊ : ℝ)⁻¹) ≤
                  (i : ℝ)⁻¹ + (⌊x_seq i l⌋₊ : ℝ)⁻¹ from
              min_le_left _ _)
            ?_
          refine le_max_of_le_right ?_
          gcongr
          · exact x_seq_pos i l' ( by linarith ) ( by linarith [ hL.2 l' hl' ] )
          · have h_floor : x_seq i l - x_seq i l' > 1 := by
              have h_floor :
                  ∀ k : ℕ,
                    2 * (k + 1) < (i : ℝ) * (i + 1) →
                      x_seq i (k + 1) - x_seq i k > 1 :=
                fun k hk => x_seq_diff_gt_one i k hk
              have h_floor : ∀ k : ℕ, l' < k → k ≤ l → x_seq i k - x_seq i l' > 1 := by
                intros k hk₁ hk₂
                induction hk₁ <;> norm_num at *
                · exact h_floor l' ( by
                    linarith [ hL.2 l' hl', hL.2 l hl,
                      show ( l : ℝ ) ≥ l' + 1 by norm_cast ] )
                · rename_i k hk₁ hk₂
                  linarith [
                    h_floor k ( by
                      linarith [ hL.2 l hl,
                        show ( k : ℝ ) + 1 ≤ l by norm_cast ] ),
                    ‹k ≤ l → 1 < x_seq i k - x_seq i l'› ( by linarith ) ]
              exact h_floor l ‹_› le_rfl
            exact le_of_lt ( Nat.sub_one_lt_floor _ |> lt_of_le_of_lt ( by linarith ) )
      · exact fun _ _ => measurableSet_Ioc
    have h_total_measure_bound :
        ENNReal.ofReal (L.card * (25 / (108 * (i : ℝ)^4))) ≥
          ENNReal.ofReal (1 / 1000 * ((1 : ℝ) / (i - 1) - 1 / i)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      convert total_measure_bound i hi |> le_trans <|
        mul_le_mul_of_nonneg_right hL.1 (by positivity) using 1
    simpa [one_div, ENNReal.ofReal_mul] using h_total_measure_bound.trans h_measure_bound
  · intro x l hx₁ hl hx₂
    have := good_interval_predicate_strict i l hi ( hL.2 l hl |>.1 ) x
      ( by simpa using hx₁ ) ( by simpa using hx₂ )
    rcases this with ⟨a, b, ha, hb, hab, ha', hb', hx, hx'⟩
    exact ⟨a, ha, b, hb, hab, ha', hb', by simpa using hx,
      fun j hj hj' hj'' => by simpa using hx' j hj hj' <| by simpa using hj''⟩

/-! ## §4. Partition Properties and Existence of Best Approximation

Properties P1–P5 from the paper: the best `n`-term Egyptian underapproximation
defines a partition of `(0, ∞)` into intervals.
-/

/-- P1: If `S` is best for `x`, it is best for any `y ∈ (egyptianSum S, x]`. -/
lemma IsBestNTerm_of_Ioc (S : Finset ℕ) (n : ℕ) (x y : ℝ)
    (hS : IsBestNTerm S n x)
    (hy_lower : egyptianSum S < y) (hy_upper : y ≤ x) :
    IsBestNTerm S n y := by
  exact ⟨ hS.1, ⟨ hS.2.1.1, hy_lower ⟩,
    fun T hT hT' => hS.2.2 T hT ⟨ hT'.1, hT'.2.trans_le hy_upper ⟩ ⟩

/-- If all elements of `S` are greater than `S.card / σ`, then `egyptianSum S < σ`. -/
lemma min_element_le_of_sum_ge {S : Finset ℕ} {σ : ℝ}
    (hσ : 0 < σ) (hsum : egyptianSum S ≥ σ) (hne : S.Nonempty) :
    ∃ a ∈ S, (a : ℝ) ≤ S.card / σ := by
  contrapose! hsum
  have hsum_lt_sigma : ∑ a ∈ S, (1 : ℝ) / a < ∑ a ∈ S, (σ / S.card : ℝ) := by
    exact Finset.sum_lt_sum_of_nonempty hne fun x hx => by
      simpa using inv_strictAnti₀ ( by positivity ) ( hsum x hx )
  simp_all +decide [ egyptianSum ]
  rwa [ mul_div_cancel₀ _ ( Nat.cast_ne_zero.mpr hne.card_pos.ne' ) ] at hsum_lt_sigma

/-- For any `n ≥ 1`, `a₀`, and `x > 0`, valid `n`-term sets with elements `> a₀`
    and sum `< x` exist. -/
lemma valid_set_exists (n : ℕ) (a₀ : ℕ) (x : ℝ) (hx : 0 < x) :
    ∃ S : Finset ℕ, S.card = n ∧ (∀ m ∈ S, a₀ < m) ∧ ValidEgyptian S ∧ egyptianSum S < x := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∑ k ∈ Finset.range n, (1 : ℝ) / (a₀ + M + k + 1) < x := by
    have h_sum_zero :
        Filter.Tendsto
          (fun M : ℕ => ∑ k ∈ Finset.range n, (1 : ℝ) / (a₀ + M + k + 1))
          Filter.atTop (nhds 0) := by
      exact le_trans
        ( tendsto_finsetSum _ fun i hi =>
          tendsto_const_nhds.div_atTop <|
            Filter.tendsto_atTop_mono ( fun M => by linarith )
              tendsto_natCast_atTop_atTop )
        ( by norm_num )
    exact ( h_sum_zero.eventually ( gt_mem_nhds hx ) ) |> fun h => h.exists
  refine ⟨ Finset.image ( fun k : ℕ => a₀ + M + k + 1 ) ( Finset.range n ),
      ?_, ?_, ?_, ?_ ⟩ <;>
    norm_num [ Finset.card_image_of_injective, Function.Injective, * ]
  · grind
  · exact fun m hm => by
      obtain ⟨ k, hk, rfl ⟩ := Finset.mem_image.mp hm
      positivity
  · unfold egyptianSum
    rw [ Finset.sum_image ] <;> aesop

set_option maxHeartbeats 800000 in
-- This proof searches through the finite maximality construction for best approximants.
/-- The best `n`-term underapproximation with elements `> a₀` exists. -/
lemma exists_bestNTerm_above (n : ℕ) (x : ℝ) (hx : 0 < x) (a₀ : ℕ) :
    ∃ S : Finset ℕ, S.card = n ∧ (∀ m ∈ S, a₀ < m) ∧
      ValidEgyptian S ∧ egyptianSum S < x ∧
      ∀ T : Finset ℕ, T.card = n → (∀ m ∈ T, a₀ < m) →
        ValidEgyptian T → egyptianSum T < x → egyptianSum T ≤ egyptianSum S := by
  by_contra h
  induction n generalizing a₀ x with
  | zero =>
    simp_all +decide [ ValidEgyptian, egyptianSum ]
  | succ n ih =>
    obtain ⟨S₀, hS₀⟩ :
        ∃ S₀ : Finset ℕ,
          S₀.card = n + 1 ∧ (∀ m ∈ S₀, a₀ < m) ∧
            ValidEgyptian S₀ ∧ egyptianSum S₀ < x := by
      exact valid_set_exists _ _ _ hx
    set σ₀ := egyptianSum S₀
    set B := Nat.floor ((n + 1) / σ₀) with hB_def
    have hB_pos : 0 < σ₀ := by
      exact Finset.sum_pos
        ( fun m hm => one_div_pos.mpr <| Nat.cast_pos.mpr <| hS₀.2.2.1 m hm )
        ( Finset.card_pos.mp <| by linarith )
    have hT_a :
        ∀ a ∈ Finset.Icc (a₀ + 1) B, 1 / (a : ℝ) < x →
          ∃ T_a : Finset ℕ,
            T_a.card = n ∧
            (∀ m ∈ T_a, a < m) ∧
            ValidEgyptian T_a ∧
            egyptianSum T_a < x - 1 / (a : ℝ) ∧
            ∀ T : Finset ℕ,
              T.card = n →
              (∀ m ∈ T, a < m) →
              ValidEgyptian T →
              egyptianSum T < x - 1 / (a : ℝ) →
                egyptianSum T ≤ egyptianSum T_a := by
      intros a ha ha_lt_x
      specialize ih (x - 1 / (a : ℝ)) (by
      linarith) a
      generalize_proofs at *
      exact not_not.mp ih
    choose! T_a hT_a using hT_a
    obtain ⟨S, hS⟩ :
        ∃ S ∈
            Finset.image (fun a => insert a (T_a a))
              (Finset.filter (fun a => 1 / (a : ℝ) < x)
                (Finset.Icc (a₀ + 1) B)) ∪ {S₀},
          ∀ T ∈
              Finset.image (fun a => insert a (T_a a))
                (Finset.filter (fun a => 1 / (a : ℝ) < x)
                  (Finset.Icc (a₀ + 1) B)) ∪ {S₀},
            egyptianSum T ≤ egyptianSum S := by
      exact Finset.exists_max_image _ _
        ⟨ S₀, Finset.mem_union_right _ ( Finset.mem_singleton_self _ ) ⟩
    refine h ⟨ S, ?_, ?_, ?_, ?_, ?_ ⟩
    · grind
    · grind
    · simp +zetaDelta at *
      rcases hS.1 with ( rfl | ⟨ a, ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩, rfl ⟩ )
      · exact hS₀.2.2.1
      · exact fun m hm => by
          rcases Finset.mem_insert.mp hm with rfl | hm
          · exact Nat.lt_of_le_of_lt ( Nat.zero_le a₀ ) ha₁
          · exact hT_a a ha₁ ha₂ ha₃ |>.2.2.1 m hm
    · simp +zetaDelta at *
      rcases hS.1 with ( rfl | ⟨ a, ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩, rfl ⟩ ) <;> norm_num at *
      · linarith
      · rw [ egyptianSum ]
        rw [ Finset.sum_insert ]
        · have := hT_a a ha₁ ha₂ ha₃
          norm_num [egyptianSum] at *
          linarith
        · exact fun h => by
            linarith [ hT_a a ha₁ ha₂ ha₃ |>.2.1 a h ]
    · intro T hT₁ hT₂ hT₃ hT₄
      by_cases hT₅ : egyptianSum T < σ₀
      · exact le_trans hT₅.le ( hS.2 S₀ ( by norm_num ) )
      · obtain ⟨a, ha₁, ha₂⟩ : ∃ a ∈ T, ∀ m ∈ T, a ≤ m := by
          exact ⟨
            Nat.find <| Finset.card_pos.mp <| by linarith,
            Nat.find_spec <| Finset.card_pos.mp <| by linarith,
            fun m hm => Nat.find_min' _ hm ⟩
        have ha₃ : a ≤ B := by
          have ha₃ : (a : ℝ) ≤ (n + 1) / σ₀ := by
            have := min_element_le_of_sum_ge hB_pos ( by linarith ) ⟨ a, ha₁ ⟩
            exact
              le_trans ( mod_cast ha₂ _ this.choose_spec.1 ) this.choose_spec.2 |>
                le_trans <| by norm_num [ hT₁ ]
          exact Nat.le_floor ha₃
        have ha₄ : 1 / (a : ℝ) < x := by
          refine lt_of_le_of_lt ?_ hT₄
          exact le_trans ( by norm_num )
            ( Finset.single_le_sum
              ( fun m _ => one_div_nonneg.mpr ( Nat.cast_nonneg m ) ) ha₁ )
        have hT_minus_a : egyptianSum (T \ {a}) < x - 1 / (a : ℝ) := by
          unfold egyptianSum at *
          rw [Finset.sum_eq_sum_sdiff_singleton_add ha₁] at hT₄
          norm_num at *
          linarith
        have hT_minus_a : egyptianSum (T \ {a}) ≤ egyptianSum (T_a a) := by
          apply (hT_a a (Finset.mem_Icc.mpr ⟨by
          exact hT₂ a ha₁, ha₃⟩) ha₄).right.right.right.right
          · grind
          · grind +revert
          · exact fun m hm => hT₃ m <| Finset.mem_sdiff.mp hm |>.1
          · exact hT_minus_a
        have hT_minus_a : egyptianSum T = 1 / (a : ℝ) + egyptianSum (T \ {a}) := by
          unfold egyptianSum
          rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem ha₁]
        have hT_minus_a :
            egyptianSum (insert a (T_a a)) = 1 / (a : ℝ) + egyptianSum (T_a a) := by
          unfold egyptianSum
          simp +decide [ Finset.sum_insert,
            show a ∉ T_a a from fun h => by
              linarith [
                hT_a a ( Finset.mem_Icc.mpr
                  ⟨ by linarith [ hT₂ a ha₁ ], ha₃ ⟩ ) ha₄ |>.2.1 a h ] ]
        linarith [
          hS.2 ( insert a ( T_a a ) )
            ( Finset.mem_union_left _
              ( Finset.mem_image.mpr
                ⟨ a,
                  Finset.mem_filter.mpr
                    ⟨ Finset.mem_Icc.mpr ⟨ by linarith [ hT₂ a ha₁ ], ha₃ ⟩,
                      ha₄ ⟩,
                  rfl ⟩ ) ) ]

set_option maxHeartbeats 800000 in
-- This wrapper still unfolds the preceding best-approximation existence proof.
/-- For any `x > 0` and `n`, the best `n`-term underapproximation exists. -/
lemma exists_bestNTerm (n : ℕ) (x : ℝ) (hx : 0 < x) :
    ∃ S : Finset ℕ, IsBestNTerm S n x := by
  obtain ⟨S, hcard, _, hvalid, hsum, hbest⟩ := exists_bestNTerm_above n x hx 0
  exact ⟨S, hcard, ⟨hvalid, hsum⟩, fun T hT ⟨hTv, hTs⟩ =>
    hbest T hT (fun m hm => hTv m hm) hTv hTs⟩

set_option maxHeartbeats 800000 in
-- This argument compares two nested best-approximation problems.
/-- P2: If two numbers have the same best `(n+1)`-term sum, they have the same
    best `n`-term sum. -/
lemma IsBestNTerm_value_determines_prev (n : ℕ) (x y : ℝ)
    (hxy : x ≤ y)
    (S₁ : Finset ℕ) (S₂ : Finset ℕ)
    (hS₁ : IsBestNTerm S₁ (n + 1) x) (hS₂ : IsBestNTerm S₂ (n + 1) y)
    (heq : egyptianSum S₁ = egyptianSum S₂)
    (T₁ : Finset ℕ) (T₂ : Finset ℕ)
    (hT₁ : IsBestNTerm T₁ n x) (hT₂ : IsBestNTerm T₂ n y) :
    egyptianSum T₁ = egyptianSum T₂ := by
  by_contra hneq
  have hle : egyptianSum T₁ ≤ egyptianSum T₂ := by
    exact hT₂.2.2 T₁ hT₁.1 ⟨ fun m hm => hT₁.2.1.1 m hm, by linarith [ hT₁.2.1.2 ] ⟩
  have hge : egyptianSum T₂ ≥ x := by
    contrapose! hneq
    exact le_antisymm hle ( hT₁.2.2 T₂ hT₂.1 ( by exact ⟨ hT₂.2.1.1, hneq ⟩ ) )
  obtain ⟨M, hM₁, hM₂⟩ : ∃ M : ℕ, M ∉ T₂ ∧ egyptianSum T₂ + 1 / (M : ℝ) < y ∧ 0 < M := by
    obtain ⟨M, hM₁, hM₂⟩ : ∃ M : ℕ, M ∉ T₂ ∧ M > 1 / (y - egyptianSum T₂) ∧ 0 < M := by
      have hM₁ : ∃ M : ℕ, M ∉ T₂ ∧ M > Nat.ceil (1 / (y - egyptianSum T₂)) := by
        exact ⟨ Finset.sup T₂ id + ⌈1 / ( y - egyptianSum T₂ ) ⌉₊ + 1,
          fun h =>
            not_lt_of_ge ( Finset.le_sup ( f := id ) h )
              ( Nat.lt_succ_of_le ( Nat.le_add_right _ _ ) ),
          Nat.lt_succ_of_le ( Nat.le_add_left _ _ ) ⟩
      exact ⟨ hM₁.choose, hM₁.choose_spec.1,
        Nat.lt_of_ceil_lt hM₁.choose_spec.2, pos_of_gt hM₁.choose_spec.2 ⟩
    exact ⟨ M, hM₁, by rw [ gt_iff_lt, div_lt_iff₀ ] at hM₂ <;>
      nlinarith [ show ( M : ℝ ) ≥ 1 by exact_mod_cast hM₂.2,
        one_div_mul_cancel ( show ( M : ℝ ) ≠ 0 by exact_mod_cast hM₂.2.ne' ),
        hT₂.2.1.2 ], hM₂.2 ⟩
  have h_union : egyptianSum (T₂ ∪ {M}) > egyptianSum S₂ := by
    have h_union : egyptianSum (T₂ ∪ {M}) = egyptianSum T₂ + 1 / (M : ℝ) := by
      unfold egyptianSum
      simp +decide [*]
      ring
    exact h_union.symm ▸ lt_add_of_le_of_pos ( heq ▸ hge.trans' ( hS₁.2.1.2.le ) )
      ( by exact one_div_pos.mpr ( Nat.cast_pos.mpr hM₂.2 ) )
  have := hS₂.2.2 ( T₂ ∪ { M } ) ?_ ?_ <;> simp_all +decide
  · linarith
  · exact hT₂.1
  · constructor
    · exact fun m hm => by
        cases Finset.mem_insert.mp hm with
        | inl h => subst h; exact hM₂.2
        | inr h => exact hT₂.2.1.1 m h
    · simp_all +decide [ egyptianSum ]
      linarith

/-! ## §5. Gap Bound (Property P5)

For `t ≥ 2`, `x ∈ (0, H_t]`, the best `t`-term underapproximation `S` satisfies
`x - egyptianSum S ≤ 1/(t(t+1))`.
-/

/-- There exists a largest `k ∈ {0,...,n-1}` with `H_k < x`. -/
lemma exists_harmonic_prefix (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 0 < x)
    (hx_le : x ≤ harmonicNumber n) :
    ∃ l : ℕ, l ≤ n - 1 ∧ harmonicNumber l < x ∧
      (l + 1 ≤ n → x ≤ harmonicNumber (l + 1)) := by
  induction hn
  case refl =>
    exact ⟨0, by norm_num,
      by
        norm_num [harmonicNumber] at *
        linarith,
      by
        norm_num [harmonicNumber] at *
        linarith⟩
  case step n hn ih =>
    grind

/-- Greedy density: for any `δ ∈ (0, 1/(l+1)]`, there exist `t` distinct positive integers
    `≥ l+2` with reciprocal sum `< δ` and gap `≤ 1/((l+t)(l+t+1))`. -/
lemma greedy_density (t : ℕ) (ht : 1 ≤ t) (l : ℕ) (δ : ℝ) (hδ_pos : 0 < δ)
    (hδ_le : δ ≤ 1 / ((l : ℝ) + 1)) :
    ∃ S : Finset ℕ, S.card = t ∧ ValidEgyptian S ∧
      (∀ m ∈ S, l + 2 ≤ m) ∧
      egyptianSum S < δ ∧
      δ - egyptianSum S ≤ 1 / (((l : ℝ) + ↑t) * ((l : ℝ) + ↑t + 1)) := by
  induction ht generalizing l δ
  case refl =>
    refine ⟨ { ⌊δ⁻¹⌋₊ + 1 }, ?_, ?_, ?_, ?_, ?_ ⟩ <;> norm_num [ ValidEgyptian, egyptianSum ]
    · exact Nat.succ_le_succ ( Nat.le_floor <| by
        rw [ inv_eq_one_div ]
        rw [ le_div_iff₀ hδ_pos ]
        rw [ le_div_iff₀ ( by positivity : (0 : ℝ) < (l : ℝ) + 1 ) ] at hδ_le
        nlinarith [ show ((l + 1 : ℕ) : ℝ) = (l : ℝ) + 1 by norm_num ] )
    · exact inv_lt_of_inv_lt₀ hδ_pos <| Nat.lt_floor_add_one _
    · field_simp
      have := Nat.floor_le ( by positivity : 0 ≤ 1 / δ )
      rw [ le_div_iff₀ ] at * <;> nlinarith [ sq ( l : ℝ ) ]
  case step t ht ih =>
    obtain ⟨m₀, hm₀⟩ :
        ∃ m₀ : ℕ,
          m₀ ≥ l + 2 ∧ (1 : ℝ) / m₀ < δ ∧
            (δ - (1 : ℝ) / m₀) ≤ 1 / ((m₀ - 1 : ℝ) * m₀) := by
      use Nat.floor (1 / δ) + 1
      refine ⟨ ?_, ?_, ?_ ⟩
      · exact Nat.succ_le_succ (Nat.le_floor <| by
          rw [le_div_iff₀ hδ_pos]
          norm_num
          nlinarith [mul_div_cancel₀ 1 (by positivity : (l : ℝ) + 1 ≠ 0)])
      · simpa using inv_lt_of_inv_lt₀ hδ_pos <| Nat.lt_floor_add_one _
      · rcases n : ⌊1 / δ⌋₊ with ( _ | n ) <;> simp_all +decide
        · exact hδ_le.trans ( inv_le_one_of_one_le₀ <| by linarith )
        · rw [ Nat.floor_eq_iff ] at n <;> norm_num at * <;>
            nlinarith [
              inv_pos.2 hδ_pos,
              mul_inv_cancel₀ hδ_pos.ne',
              inv_pos.2 ( by
                linarith : 0 < ( ( Nat.cast : ℕ → ℝ ) ‹_› ) + 1 + 1 ),
              mul_inv_cancel₀ ( by
                linarith : ( ( Nat.cast : ℕ → ℝ ) ‹_› ) + 1 + 1 ≠ 0 ),
              inv_pos.2 ( by
                linarith : 0 < ( ( Nat.cast : ℕ → ℝ ) ‹_› ) + 1 ),
              mul_inv_cancel₀ ( by
                linarith : ( ( Nat.cast : ℕ → ℝ ) ‹_› ) + 1 ≠ 0 ) ]
    obtain ⟨S', hS'⟩ :
        ∃ S' : Finset ℕ,
          S'.card = t ∧ ValidEgyptian S' ∧
          (∀ m ∈ S', m ≥ m₀ + 1) ∧
          egyptianSum S' < δ - 1 / (m₀ : ℝ) ∧
          (δ - 1 / (m₀ : ℝ)) - egyptianSum S' ≤
            1 / ((m₀ - 1 + t : ℝ) * (m₀ - 1 + t + 1)) := by
      convert ih ( m₀ - 1 ) ( δ - 1 / ( m₀ : ℝ ) ) ( sub_pos.mpr hm₀.2.1 ) _ using 1
      · cases m₀ <;> aesop
      · rcases m₀ <;> norm_num at *
        exact hm₀.2.2.trans
          ( add_le_add_left
            ( mul_le_of_le_one_right ( by positivity )
              ( inv_le_one_of_one_le₀ ( by
                norm_cast
                linarith ) ) ) _ )
    refine ⟨ Insert.insert m₀ S', ?_, ?_, ?_, ?_, ?_ ⟩ <;> simp_all +decide [ ValidEgyptian ]
    · rw [ Finset.card_insert_of_notMem ( fun h => by linarith [ hS'.2.2.1 m₀ h ] ), hS'.1 ]
    · linarith
    · exact fun x hx => by
        linarith [ hS'.2.2.1 x hx ]
    · unfold egyptianSum at *
      grind
    · rw [ egyptianSum ]
      rw [ Finset.sum_insert ] <;> norm_num
      · refine le_trans hS'.2.2.2.2 ?_
        rw [ ← mul_inv ]
        rw [← mul_inv]
        ring_nf
        rw [add_comm]
        norm_num [egyptianSum]
        ring_nf
        norm_num [ add_comm, add_left_comm, add_assoc ]
        exact inv_anti₀ ( by positivity ) ( by
          nlinarith only [ show ( m₀ : ℝ ) ≥ l + 2 by
            norm_cast
            linarith ] )
      · exact fun h => by
          linarith [ hS'.2.2.1 m₀ h ]

/-- For any `x ∈ (0, H_t]` with `t ≥ 2`, there exists a `t`-term valid Egyptian fraction
    sum `< x` with gap `≤ 1/(t(t+1))`. -/
lemma exists_good_approx (t : ℕ) (ht : 2 ≤ t) (x : ℝ) (hx : 0 < x)
    (hx_le : x ≤ harmonicNumber t) :
    ∃ S : Finset ℕ, S.card = t ∧ IsUnderapprox S x ∧
      x - egyptianSum S ≤ 1 / ((t : ℝ) * (↑t + 1)) := by
  obtain ⟨l, hl⟩ :
      ∃ l : ℕ,
        l ≤ t - 1 ∧ harmonicNumber l < x ∧
          (l + 1 ≤ t → x ≤ harmonicNumber (l + 1)) :=
    exists_harmonic_prefix t (by linarith) x hx hx_le
  obtain ⟨S', hS'_card, hS'_valid, hS'_sum, hS'_gap⟩ :
      ∃ S' : Finset ℕ,
        S'.card = t - l ∧ ValidEgyptian S' ∧
        (∀ m ∈ S', l + 2 ≤ m) ∧
        egyptianSum S' < x - harmonicNumber l ∧
        x - harmonicNumber l - egyptianSum S' ≤
          1 / ((l + (t - l)) * (l + (t - l) + 1) : ℝ) := by
    convert greedy_density ( t - l )
      ( Nat.sub_pos_of_lt ( lt_of_le_of_lt hl.1 ( Nat.pred_lt ( ne_bot_of_gt ht ) ) ) )
      l ( x - harmonicNumber l ) _ _ using 1
    · rw [ Nat.cast_sub ( by omega ) ]
    · linarith
    · convert sub_le_sub_right (hl.2.2 (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hl.1
        (Nat.pred_lt (ne_bot_of_gt ht))))) (harmonicNumber l) using 1
      norm_num [harmonicNumber]
      norm_num [ Finset.sum_range_succ ]
  refine ⟨
    Finset.image ( fun k => k + 1 ) ( Finset.range l ) ∪ S',
    ?_, ?_, ?_ ⟩ <;>
    simp_all +decide
  · rw [ Finset.card_union_of_disjoint ]
    · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ]
      omega
    · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by
        obtain ⟨ k, hk₁, hk₂ ⟩ := Finset.mem_image.mp hx₁
        linarith [ Finset.mem_range.mp hk₁, hS'_sum x hx₂ ]
  · constructor
    · intro m hm
      aesop
    · rw [ egyptianSum, Finset.sum_union ]
      · convert add_lt_add_right hS'_gap.1 ( harmonicNumber l ) using 1
        · unfold harmonicNumber egyptianSum
          aesop
        · ring
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by
          obtain ⟨ k, hk₁, hk₂ ⟩ := Finset.mem_image.mp hx₁
          linarith [ Finset.mem_range.mp hk₁, hS'_sum x hx₂ ]
  · rw [ egyptianSum, Finset.sum_union ]
    · convert hS'_gap.2 using 1
      unfold egyptianSum harmonicNumber
      norm_num [add_comm, add_left_comm, add_assoc]
    · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by
        obtain ⟨ k, hk₁, hk₂ ⟩ := Finset.mem_image.mp hx₁
        linarith [ Finset.mem_range.mp hk₁, hS'_sum x hx₂ ]

/-- **Property P5**: For `x ∈ (0, H_t]` with best `t`-term sum `S`, the gap satisfies
    `x - egyptianSum S ≤ 1/(t(t+1))`. -/
theorem best_sum_gap_bound (t : ℕ) (ht : 2 ≤ t) (x : ℝ) (hx : 0 < x)
    (hx_le : x ≤ harmonicNumber t)
    (S : Finset ℕ) (hS : IsBestNTerm S t x) :
    x - egyptianSum S ≤ 1 / ((t : ℝ) * (↑t + 1)) := by
  obtain ⟨T, hT_card, hT_underapprox, hT_gap⟩ :
      ∃ T : Finset ℕ,
        T.card = t ∧ IsUnderapprox T x ∧
          x - egyptianSum T ≤ 1 / ((t : ℝ) * (t + 1)) := by
    exact exists_good_approx t ht x hx hx_le
  exact le_trans ( sub_le_sub_left ( hS.2.2 T hT_card hT_underapprox ) _ ) hT_gap

/-! ## §6. Best Approximation Functions, Fibers, and X_fiber

We define `bestNTermSum` and `bestNTermSet` as canonical choices, and study their properties.
-/

/-- The best `t`-term sum for `x` (as a real number). -/
noncomputable def bestNTermSum (t : ℕ) (x : ℝ) : ℝ :=
  if hx : 0 < x then
    (exists_bestNTerm t x hx).choose |>.sum (fun m => (1 : ℝ) / m)
  else 0

/-- A canonical best `t`-term set for `x`. -/
noncomputable def bestNTermSet (t : ℕ) (x : ℝ) : Finset ℕ :=
  if hx : 0 < x then
    (exists_bestNTerm t x hx).choose
  else ∅

lemma bestNTermSet_isBest (t : ℕ) (x : ℝ) (hx : 0 < x) :
    IsBestNTerm (bestNTermSet t x) t x := by
  unfold bestNTermSet
  rw [dif_pos hx]
  exact (exists_bestNTerm t x hx).choose_spec

lemma bestNTermSum_eq (t : ℕ) (x : ℝ) (hx : 0 < x) :
    bestNTermSum t x = egyptianSum (bestNTermSet t x) := by
  unfold bestNTermSum bestNTermSet egyptianSum
  rw [dif_pos hx, dif_pos hx]

lemma bestNTermSum_unique (t : ℕ) (x : ℝ) (hx : 0 < x)
    (S : Finset ℕ) (hS : IsBestNTerm S t x) :
    egyptianSum S = bestNTermSum t x := by
  rw [bestNTermSum_eq t x hx]
  exact le_antisymm
    ((bestNTermSet_isBest t x hx).2.2 S hS.1 hS.2.1)
    (hS.2.2 (bestNTermSet t x) (bestNTermSet_isBest t x hx).1
      (bestNTermSet_isBest t x hx).2.1)

/-- The best `t`-term sum is monotone in `x`. -/
lemma bestNTermSum_mono (t : ℕ) (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    bestNTermSum t x ≤ bestNTermSum t y := by
  rw [bestNTermSum_eq t x hx, bestNTermSum_eq t y (lt_of_lt_of_le hx hxy)]
  have hSx := bestNTermSet_isBest t x hx
  have hSy := bestNTermSet_isBest t y (lt_of_lt_of_le hx hxy)
  exact hSy.2.2 _ hSx.1 ⟨hSx.2.1.1, lt_of_lt_of_le hSx.2.1.2 hxy⟩

/-- The best `t`-term sum is strictly less than `x`. -/
lemma bestNTermSum_lt (t : ℕ) (x : ℝ) (hx : 0 < x) :
    bestNTermSum t x < x := by
  rw [bestNTermSum_eq t x hx]
  exact (bestNTermSet_isBest t x hx).2.1.2

/-- Best `t`-term sums for two points in the same "fiber" are equal. -/
lemma bestNTermSum_eq_of_fiber (t : ℕ) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y)
    (S : Finset ℕ) (hS_x : IsBestNTerm S t x) (hS_y : IsBestNTerm S t y) :
    bestNTermSum t x = bestNTermSum t y := by
  rw [← bestNTermSum_unique t x hx S hS_x, ← bestNTermSum_unique t y hy S hS_y]

/-- If `x` has a compatible sequence for levels `s` to `t`, then any `y ∈ (q, x]`
    (where `q` is the best `t`-term sum) also has one. -/
lemma X_set_downward_closed_in_fiber (s t : ℕ) (ht : s ≤ t)
    (x : ℝ) (hx : x ∈ X_set s t)
    (y : ℝ) (hy_pos : 0 < y)
    (hy_lower : bestNTermSum t x < y)
    (hy_upper : y ≤ x) :
    y ∈ X_set s t := by
  obtain ⟨ m, hm_mono, hm_pos, hm_best ⟩ := hx.2.2
  refine ⟨ hy_pos, hy_upper.trans hx.2.1, m, hm_mono, hm_pos, fun n hn₁ hn₂ => ?_ ⟩
  apply IsBestNTerm_of_Ioc
  · exact hm_best n hn₁ hn₂
  · refine lt_of_le_of_lt ?_ hy_lower
    have h_sum_le :
        egyptianSum (Finset.image m (Finset.range n)) ≤
          egyptianSum (Finset.image m (Finset.range t)) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        ( Finset.image_subset_image ( Finset.range_mono hn₂ ) )
        fun _ _ _ => one_div_nonneg.2 ( Nat.cast_nonneg _ )
    calc
      egyptianSum (Finset.image m (Finset.range n)) ≤
          egyptianSum (Finset.image m (Finset.range t)) := h_sum_le
      _ = bestNTermSum t x := by
        exact bestNTermSum_unique t x hx.1 _ (hm_best t (by linarith) (by linarith))
  · linarith

/-- If `bestNTermSum (n+1)` is the same at `x` and `y` (with `x ≤ y`),
    then `bestNTermSum n` is also the same. -/
lemma fiber_sums_step (n : ℕ) (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y)
    (heq : bestNTermSum (n + 1) x = bestNTermSum (n + 1) y) :
    bestNTermSum n x = bestNTermSum n y := by
  rw [bestNTermSum_eq n x hx, bestNTermSum_eq n y hy,
      bestNTermSum_eq (n+1) x hx, bestNTermSum_eq (n+1) y hy] at *
  exact IsBestNTerm_value_determines_prev n x y hxy
    _ _ (bestNTermSet_isBest (n+1) x hx) (bestNTermSet_isBest (n+1) y hy) heq
    _ _ (bestNTermSet_isBest n x hx) (bestNTermSet_isBest n y hy)

/-- If `bestNTermSum t` is the same at `x` and `y` (with `x ≤ y`),
    then `bestNTermSum n` is the same for all `n ≤ t`. -/
lemma fiber_sums_equal (t : ℕ) (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y)
    (heq_t : bestNTermSum t x = bestNTermSum t y) :
    ∀ n, n ≤ t → bestNTermSum n x = bestNTermSum n y := by
  intro n hn
  induction t with
  | zero => simp_all [Nat.le_zero.mp hn]
  | succ t ih =>
    rcases eq_or_lt_of_le hn with rfl | h
    · exact heq_t
    · exact ih (fiber_sums_step t x y hx hy hxy heq_t) (by omega)

/-! ### X_fiber: the fiber restricted to X_set -/

/-- The set of `x` in `X_set s t` with `bestNTermSum t x = q`. -/
noncomputable def X_fiber (s t : ℕ) (q : ℝ) : Set ℝ :=
  {x | x ∈ X_set s t ∧ bestNTermSum t x = q}

/-- The `sSup` of the fiber has `bestNTermSum t = q`. -/
lemma fiber_sup_bestNTermSum (s t : ℕ)
    (q : ℝ) (hne : (X_fiber s t q).Nonempty) :
    bestNTermSum t (sSup (X_fiber s t q)) = q := by
  refine le_antisymm ?_ ?_
  · by_contra h_contra
    obtain ⟨T, hT⟩ :
        ∃ T : Finset ℕ,
          T.card = t ∧ IsUnderapprox T (sSup (X_fiber s t q)) ∧
            egyptianSum T > q := by
      obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, IsBestNTerm T t (sSup (X_fiber s t q)) := by
        apply exists_bestNTerm
        exact lt_of_lt_of_le ( hne.choose_spec.1.1 )
          ( le_csSup
            ( show BddAbove ( X_fiber s t q ) from
              ⟨ harmonicNumber s, fun x hx => hx.1.2.1 ⟩ )
            hne.choose_spec )
      exact ⟨ T, hT.1, hT.2.1, by
        linarith [
          bestNTermSum_unique t ( sSup ( X_fiber s t q ) )
            ( show 0 < sSup ( X_fiber s t q ) from
              lt_of_lt_of_le ( hne.choose_spec.1.1 )
                ( le_csSup
                  ( show BddAbove ( X_fiber s t q ) from
                    ⟨ _, fun x hx => hx.1.2.1 ⟩ )
                  hne.choose_spec ) )
            T hT ] ⟩
    obtain ⟨x_k, hx_k⟩ : ∃ x_k ∈ X_fiber s t q, x_k > egyptianSum T := by
      exact exists_lt_of_lt_csSup hne ( hT.2.1.2 )
    have h_contra : egyptianSum T ≤ bestNTermSum t x_k := by
      have h_contra : IsBestNTerm (bestNTermSet t x_k) t x_k := by
        exact bestNTermSet_isBest t x_k ( by linarith [ hx_k.1.1.1 ] )
      have := h_contra.2.2 T hT.1
      convert this _
      · exact bestNTermSum_eq t x_k ( hx_k.1.1.1 )
      · exact ⟨ hT.2.1.1, hx_k.2 ⟩
    linarith [ hx_k.1.2 ]
  · obtain ⟨x₀, hx₀⟩ : ∃ x₀ ∈ X_fiber s t q, True := by
      exact ⟨ hne.choose, hne.choose_spec, trivial ⟩
    exact hx₀.1.2.symm ▸
      bestNTermSum_mono t x₀ ( sSup ( X_fiber s t q ) ) ( hx₀.1.1.1 )
        ( le_csSup
          ( show BddAbove ( X_fiber s t q ) from
            ⟨ harmonicNumber s, fun x hx => hx.1.2.1 ⟩ )
          hx₀.1 )

/-- The `sSup` of the fiber is in `X_set s t`. -/
lemma fiber_sup_mem_X_set (s t : ℕ)
    (q : ℝ) (hne : (X_fiber s t q).Nonempty) :
    sSup (X_fiber s t q) ∈ X_set s t := by
  obtain ⟨ x₀, hx₀ ⟩ := hne
  constructor
  · exact lt_of_lt_of_le ( hx₀.1.1 ) ( le_csSup ⟨ harmonicNumber s, fun x hx => hx.1.2.1 ⟩ hx₀ )
  · obtain ⟨ m, hm₁, hm₂, hm₃ ⟩ := hx₀.1.2.2
    refine ⟨ csSup_le ?_ ?_, m, hm₁, hm₂, fun n hn₁ hn₂ => ?_ ⟩
    · exact ⟨ x₀, hx₀ ⟩
    · exact fun x hx => hx.1.2.1
    · have h_sup : bestNTermSum n x₀ = bestNTermSum n (sSup (X_fiber s t q)) := by
        apply fiber_sums_equal
        any_goals exact t
        · exact hx₀.1.1
        · exact lt_of_lt_of_le hx₀.1.1 ( le_csSup ⟨ harmonicNumber s, fun x hx => hx.1.2.1 ⟩ hx₀ )
        · apply le_csSup
          · exact ⟨ harmonicNumber s, fun x hx => hx.1.2.1 ⟩
          · exact hx₀
        · rw [ hx₀.2, fiber_sup_bestNTermSum ]
          exact ⟨ x₀, hx₀ ⟩
        · linarith
      have h_sup :
          egyptianSum (Finset.image m (Finset.range n)) =
            bestNTermSum n (sSup (X_fiber s t q)) := by
        rw [ ← h_sup, bestNTermSum_unique ]
        · exact hx₀.1.1
        · exact hm₃ n hn₁ hn₂
      refine ⟨ ?_, ?_, ?_ ⟩
      · rw [ Finset.card_image_of_injective _ hm₁.injective, Finset.card_range ]
      · have h_sup : bestNTermSum n (sSup (X_fiber s t q)) < sSup (X_fiber s t q) := by
          apply bestNTermSum_lt
          exact lt_of_lt_of_le ( hx₀.1.1 )
            ( le_csSup
              ( show BddAbove ( X_fiber s t q ) from
                ⟨ harmonicNumber s, fun x hx => hx.1.2.1 ⟩ )
              hx₀ )
        exact ⟨ fun x hx => by
          obtain ⟨ k, hk₁, rfl ⟩ := Finset.mem_image.mp hx
          exact hm₂ k, by linarith ⟩
      · intro T hT₁ hT₂
        have h_sup : egyptianSum T ≤ bestNTermSum n (sSup (X_fiber s t q)) := by
          have h_sup : ∃ S : Finset ℕ, IsBestNTerm S n (sSup (X_fiber s t q)) := by
            apply exists_bestNTerm
            exact lt_of_lt_of_le ( hx₀.1.1 )
              ( le_csSup
                ( show BddAbove ( X_fiber s t q ) from
                  ⟨ harmonicNumber s, fun x hx => hx.1.2.1 ⟩ )
                hx₀ )
          exact h_sup.elim fun S hS => by
            have h_pos : 0 < sSup ( X_fiber s t q ) := by
              exact lt_of_lt_of_le ( show 0 < x₀ from hx₀.1.1 )
                ( le_csSup
                  ( show BddAbove ( X_fiber s t q ) from
                    ⟨ harmonicNumber s, fun x hx => hx.1.2.1 ⟩ )
                  hx₀ )
            exact
              (bestNTermSum_unique n _ h_pos _ hS).symm ▸ hS.2.2 _ hT₁ hT₂
        linarith

/-- The fiber `{x ∈ X_set | bestNTermSum t x = q}` equals `Ioc q r`
    where `r = sSup` of the fiber. -/
lemma X_fiber_eq_Ioc (s t : ℕ) (ht : s ≤ t)
    (q : ℝ) (hne : (X_fiber s t q).Nonempty) :
    X_fiber s t q = Set.Ioc q (sSup (X_fiber s t q)) := by
  ext x
  constructor <;> intro hx
  · exact ⟨ by
      linarith [ hx.2, bestNTermSum_lt t x ( hx.1.1 ) ],
      le_csSup ⟨ harmonicNumber s, fun y hy => hy.1.2.1 ⟩ hx ⟩
  · obtain ⟨y, hy⟩ : ∃ y ∈ X_fiber s t q, x ≤ y := by
      contrapose! hx
      exact fun h => by
        have hmem : sSup ( X_fiber s t q ) ∈ X_fiber s t q :=
          fiber_sup_mem_X_set s t q hne |> fun h =>
            ⟨ h, fiber_sup_bestNTermSum s t q hne ⟩
        exact not_le_of_gt ( hx _ hmem ) h.2
    have hx_in_X_set : x ∈ X_set s t := by
      apply X_set_downward_closed_in_fiber s t ht y hy.left.left x
      · linarith [
          hx.1,
          show 0 ≤ q from by
            obtain ⟨ z, hz ⟩ := hne
            linarith [ hz.1.1, hz.2,
              show 0 ≤ bestNTermSum t z from by
                unfold bestNTermSum
                split_ifs <;> positivity ] ]
      · exact hy.1.2.symm ▸ hx.1
      · linarith
    have h_bestNTermSum_eq : bestNTermSum t x = bestNTermSum t y := by
      apply bestNTermSum_eq_of_fiber
      any_goals exact bestNTermSet t y
      · exact hx_in_X_set.1
      · exact hy.1.1.1
      · have := bestNTermSet_isBest t y (by
        exact hy.1.1.1)
        apply IsBestNTerm_of_Ioc
        · exact this
        · have := bestNTermSum_eq t y (by
          exact hy.1.1.1)
          linarith [ hx.1, hy.1.2 ]
        · linarith
      · exact bestNTermSet_isBest t y ( by linarith [ hy.1.1.1 ] )
    exact ⟨ hx_in_X_set, h_bestNTermSum_eq.trans hy.1.2 ⟩

/-! ## §7. Sub-lemmas for the Contradiction Argument -/

lemma non_greedy_pair_gt_i (i a b : ℕ) (hi : 1000 ≤ i)
    (ha : 0 < a) (hb : 0 < b) (ha_ne : a ≠ i) (hb_ne : b ≠ i)
    (hsum : (1 : ℝ) / a + 1 / b < 1 / ((i : ℝ) - 1)) :
    i < a ∧ i < b := by
  constructor <;> contrapose! hsum
  · exact le_add_of_le_of_nonneg (one_div_le_one_div_of_le (by positivity)
      (by
        linarith [
          show (a : ℝ) + 1 ≤ i by
            norm_cast
            exact lt_of_le_of_ne hsum ha_ne]))
      (by positivity)
  · rcases i with (_ | _ | i) <;> norm_num at *
    rw [inv_eq_one_div, inv_eq_one_div, inv_eq_one_div, div_add_div, div_le_div_iff₀] <;>
      norm_cast <;> cases lt_or_gt_of_ne ha_ne <;> cases lt_or_gt_of_ne hb_ne <;> nlinarith

lemma non_greedy_contradiction (m : ℕ → ℕ) (hm : StrictMono m) (hm_pos : ∀ k, 0 < m k)
    (t : ℕ) (x : ℝ)
    (hbest_t2 : IsBestNTerm (Finset.image m (Finset.range (t + 2))) (t + 2) x)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (ha_gt : m t < a) (hb_gt : m t < b)
    (hsum_lt : egyptianSum (Finset.image m (Finset.range t)) + 1 / (a : ℝ) + 1 / b < x)
    (hbetter : 1 / (m t : ℝ) + 1 / (m (t + 1)) < 1 / (a : ℝ) + 1 / b) :
    False := by
  have h_contradiction : egyptianSum (Finset.image m (Finset.range (t + 2))) <
      egyptianSum (Finset.image m (Finset.range t) ∪ {a, b}) := by
    unfold egyptianSum
    rw [Finset.sum_union] <;> norm_num [Finset.sum_image, hm.injective.eq_iff, Finset.range_add_one]
    · grind
    · exact ⟨fun x hx => by linarith [hm.monotone hx.le],
        fun x hx => by linarith [hm.monotone hx.le]⟩
  contrapose! h_contradiction
  apply hbest_t2.2.2
  · rw [Finset.card_union_of_disjoint]
    · rw [Finset.card_image_of_injective _ hm.injective, Finset.card_insert_of_notMem,
          Finset.card_singleton] <;> aesop
    · simp +zetaDelta at *
      exact ⟨fun x hx => by linarith [hm.monotone (show x ≤ t by linarith)],
        fun x hx => by linarith [hm.monotone (show x ≤ t by linarith)]⟩
  · constructor
    · exact fun x hx => by aesop
    · rw [egyptianSum, Finset.sum_union] <;>
        simp_all +decide [Finset.disjoint_singleton_right]
      · convert hsum_lt using 1
        ring_nf!
        unfold egyptianSum
        ring_nf
      · exact ⟨fun x hx => by linarith [hm.monotone (show x ≤ t by linarith)],
          fun x hx => by linarith [hm.monotone (show x ≤ t by linarith)]⟩

/-- For a compatible sequence, if the gap `δ = x - q` satisfies `δ ≤ 1/(m(t)-1)` and
    there exists a non-greedy pair `(a, b)` beating the greedy one, contradiction. -/
lemma non_greedy_excludes_X_set_v2
    (s t : ℕ) (hst : s < t)
    (m : ℕ → ℕ) (hm : StrictMono m) (hm_pos : ∀ k, 0 < m k)
    (x : ℝ)
    (hbest : ∀ n, s ≤ n → n ≤ t + 2 →
      IsBestNTerm (Finset.image m (Finset.range n)) n x)
    (hmt : 1000 ≤ m t)
    (δ : ℝ) (hδ : δ = x - egyptianSum (Finset.image m (Finset.range t)))
    (hδ_ub : δ ≤ 1 / ((m t : ℝ) - 1))
    (hδ_in_E : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ≠ b ∧ a ≠ m t ∧ b ≠ m t ∧
      (1 : ℝ) / a + 1 / b < δ ∧
      ∀ j : ℕ, 0 < j → j ≠ m t → (1 : ℝ) / (m t) + 1 / j < δ →
        (1 : ℝ) / (m t) + 1 / j < 1 / a + 1 / b) :
    False := by
  obtain ⟨a, b, ha, hb, hab, ha', hb', h₁, h₂⟩ := hδ_in_E
  have h_sum_lt : (1 : ℝ)/a + 1/b < 1/((m t : ℝ) - 1) := by linarith
  have h_gt := non_greedy_pair_gt_i (m t) a b hmt ha hb ha' hb' h_sum_lt
  apply non_greedy_contradiction m hm hm_pos t x
    (hbest (t + 2) (by linarith) (by linarith)) a b ha hb hab h_gt.1 h_gt.2
  · linarith
  · apply h₂ (m (t + 1)) (hm_pos _) (ne_of_gt (hm (Nat.lt_succ_self _)))
    subst hδ
    have hbest_t2 := hbest (t + 2) (by linarith) (by linarith)
    have hbest_sum := hbest_t2.2.1.2
    simp only [egyptianSum] at hbest_sum ⊢
    simp only [Finset.sum_image hm.injective.injOn] at *
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at hbest_sum
    linarith

/-! ## §8. Per-interval Analysis

Core lemmas connecting compatible sequences to the partition structure,
and showing that non-greedy sets are avoided by `X_{s,t+2}`.
-/

/-- If `x ∈ X_{s,t+2}` and the gap `x - q ∈ (1/i, 1/(i-1)]` with `i ∉ S`,
    then the compatible sequence has `m(t) = i`. -/
lemma compatible_seq_mt_eq
    (s t : ℕ) (hst : s < t)
    (S : Finset ℕ) (hS_card : S.card = t) (hS_valid : ValidEgyptian S)
    (q : ℝ) (hq : q = egyptianSum S)
    (x : ℝ)
    (m : ℕ → ℕ) (hm : StrictMono m) (hm_pos : ∀ k, 0 < m k)
    (hm_best : ∀ n, s ≤ n → n ≤ t + 2 →
      IsBestNTerm (Finset.image m (Finset.range n)) n x)
    (hS_best : IsBestNTerm S t x)
    (i : ℕ) (hi_pos : 0 < i) (hi_notS : i ∉ S)
    (hi_gap : (1 : ℝ) / i < x - q)
    (hi_gap_ub : x - q ≤ 1 / ((i : ℝ) - 1)) :
    m t = i := by
  have h_m_t_le_i : (1 / (i : ℝ)) ≤ (1 / (m t : ℝ)) := by
    have := hm_best ( t + 1 ) ( by linarith ) ( by linarith )
    have := this.2.2 ( S ∪ { i } ) ?_ ?_ <;> simp_all +decide
    · simp_all +decide [ egyptianSum ]
      rw [ Finset.sum_image <| by
        intro a ha b hb hab
        exact hm.injective hab ] at this
      have := hS_best.2.2 ( Finset.image m ( Finset.range t ) ) ?_ ?_ <;>
        simp_all +decide [ Finset.sum_range_succ, IsBestNTerm ]
      · unfold egyptianSum at this
        simp_all +decide [Finset.sum_image, hm.injective.eq_iff]
        grind +qlia
      · rw [ Finset.card_image_of_injective _ hm.injective, Finset.card_range ]
      · grind
    · constructor <;> simp_all +decide [ ValidEgyptian ]
      unfold egyptianSum at *
      rw [Finset.sum_insert hi_notS]
      norm_num at *
      linarith
  have h_m_t_ge_i : (1 / (m t : ℝ)) < (1 / (i - 1 : ℝ)) := by
    have h_m_t_ge_i : egyptianSum (Finset.image m (Finset.range (t + 1))) < x := by
      exact hm_best ( t + 1 ) ( by linarith ) ( by linarith ) |>.2.1 |>.2
    have h_m_t_ge_i :
        egyptianSum (Finset.image m (Finset.range (t + 1))) =
          egyptianSum (Finset.image m (Finset.range t)) + 1 / (m t : ℝ) := by
      unfold egyptianSum
      simp +decide [Finset.sum_range_succ, hm.injective.eq_iff]
    grind +suggestions
  rcases i with ( _ | _ | i ) <;> norm_num at *
  · exact (not_lt_of_ge (Nat.cast_nonneg (m t)) h_m_t_ge_i).elim
  · rw [ inv_le_inv₀, inv_lt_inv₀ ] at * <;> norm_cast at * <;> linarith [ hm_pos t ]

/-- For `x ∈ X_{s,t+2}` with gap in `(1/i, 1/(i-1)]` and `i ∉ S` and `i ≥ 1000`,
    `x - q` avoids the non-greedy set `E`. -/
lemma sub_interval_avoidance
    (s t : ℕ) (hst : s < t)
    (S : Finset ℕ) (hS_card : S.card = t) (hS_valid : ValidEgyptian S)
    (q : ℝ) (hq : q = egyptianSum S)
    (x : ℝ) (hx_mem : x ∈ X_set s (t + 2))
    (hS_best : IsBestNTerm S t x)
    (i : ℕ) (hi : 1000 ≤ i) (hi_notS : i ∉ S)
    (hi_gap : (1 : ℝ) / i < x - q)
    (hi_gap_ub : x - q ≤ 1 / ((i : ℝ) - 1))
    (E : Set ℝ)
    (hE_nongr : ∀ y ∈ E, ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ≠ b ∧ a ≠ i ∧ b ≠ i ∧
      (1 : ℝ) / a + 1 / b < y ∧
      ∀ j : ℕ, 0 < j → j ≠ i → (1 : ℝ) / i + 1 / j < y →
        (1 : ℝ) / i + 1 / j < 1 / a + 1 / b) :
    x - q ∉ E := by
  obtain ⟨ m₀, hm₀_mono, hm₀_pos, hm₀_best ⟩ := hx_mem.2.2
  have hm₀_t :=
    compatible_seq_mt_eq s t hst S hS_card hS_valid q hq x
      m₀ hm₀_mono hm₀_pos hm₀_best hS_best i (by linarith)
      hi_notS hi_gap hi_gap_ub
  · contrapose! hm₀_t
    have := non_greedy_excludes_X_set_v2 s t hst m₀ hm₀_mono hm₀_pos x hm₀_best (by
    convert hi using 1
    apply compatible_seq_mt_eq s t hst S hS_card hS_valid q hq x
      m₀ hm₀_mono hm₀_pos hm₀_best hS_best i (by linarith)
      hi_notS hi_gap hi_gap_ub) (x - q) (by
    have := hS_best.2.2 ( Finset.image m₀ ( Finset.range t ) ) ?_ ?_ <;>
      simp_all +decide [ Finset.card_image_of_injective _ hm₀_mono.injective ]
    · exact le_antisymm
        ( by
          simpa [ hq ] using
            hm₀_best t ( by linarith ) ( by linarith ) |>.2.2 S
              ( by linarith ) hS_best.2.1 )
        this
    · exact hm₀_best t ( by linarith ) ( by linarith ) |>.2.1) (by
    convert hi_gap_ub using 1
    rw [ show m₀ t = i from compatible_seq_mt_eq s t hst S hS_card hS_valid q hq x
      m₀ hm₀_mono hm₀_pos hm₀_best hS_best i (by linarith) hi_notS hi_gap hi_gap_ub ]) (by
    convert hE_nongr _ hm₀_t using 1
    rw [ compatible_seq_mt_eq s t hst S hS_card hS_valid q hq x
      m₀ hm₀_mono hm₀_pos hm₀_best hS_best i (by linarith)
      hi_notS hi_gap hi_gap_ub ])
    contradiction

/-! ## §9. Avoided Set Construction

For each interval `(q, r]` in the partition of `X_{s,t}`, we construct a measurable subset
that is avoided by `X_{s,t+2}` and has measure `≥ (r-q)/2000`.
-/

/-- Telescoping sum lower bound for the avoided set measure. -/
lemma telescoping_sum_lower_bound
    (i₀ : ℕ) (hi₀ : 3 ≤ i₀)
    (S : Finset ℕ) :
    (1 : ℝ) / i₀ - (1 + S.card) / i₀ ^ 2 ≤
    ∑ i ∈ (Finset.Icc (i₀ + 1) (i₀ * i₀)) \ S,
      (1 / ((i : ℝ) - 1) - 1 / i) := by
  have h_telescope :
      ∑ i ∈ Finset.Icc (i₀ + 1) (i₀ * i₀),
        (1 / (i - 1 : ℝ) - 1 / (i : ℝ)) =
      1 / (i₀ : ℝ) - 1 / (i₀ * i₀ : ℝ) := by
    erw [ Finset.sum_Ico_eq_sum_range ]
    convert Finset.sum_range_sub' _ _ using 3 <;> push_cast <;> ring_nf
    rw [ Nat.cast_sub ] <;> push_cast <;> nlinarith
  have h_inter_sum_bound :
      ∑ i ∈ S ∩ Finset.Icc (i₀ + 1) (i₀ * i₀),
        (1 / (i - 1 : ℝ) - 1 / (i : ℝ)) ≤
      #S * (1 / (i₀ * (i₀ + 1) : ℝ)) := by
    refine le_trans
      ( Finset.sum_le_sum fun x hx =>
        show ( 1 / ( x - 1 : ℝ ) - 1 / x ) ≤
          1 / ( i₀ * ( i₀ + 1 ) : ℝ ) from ?_ )
      ?_
    · rw [ div_sub_div, div_le_div_iff₀ ] <;>
        nlinarith only [
          show ( x : ℝ ) ≥ i₀ + 1 by
            exact_mod_cast Finset.mem_Icc.mp ( Finset.mem_inter.mp hx |>.2 ) |>.1,
          show ( i₀ : ℝ ) ≥ 3 by norm_cast ]
    · norm_num
      exact mul_le_mul_of_nonneg_right
        ( mod_cast Finset.card_mono <| Finset.inter_subset_left ) <| by positivity
  have h_sum_bound :
      ∑ i ∈ Finset.Icc (i₀ + 1) (i₀ * i₀) \ S,
        (1 / (i - 1 : ℝ) - 1 / (i : ℝ)) ≥
      ∑ i ∈ Finset.Icc (i₀ + 1) (i₀ * i₀),
        (1 / (i - 1 : ℝ) - 1 / (i : ℝ)) -
      ∑ i ∈ S ∩ Finset.Icc (i₀ + 1) (i₀ * i₀),
        (1 / (i - 1 : ℝ) - 1 / (i : ℝ)) := by
    rw [← Finset.sum_sdiff (show S ∩ Finset.Icc (i₀ + 1) (i₀ * i₀) ⊆ Finset.Icc (i₀ + 1) (i₀ * i₀)
      from Finset.inter_subset_right)]
    simp_all only [one_div, sum_sub_distrib, mul_inv_rev, tsub_le_iff_right,
      sdiff_inter_self_right, add_sub_cancel_right, ge_iff_le, Std.le_refl]
  refine le_trans ?_ h_sum_bound
  refine le_trans ?_
    (show
      (∑ i ∈ Finset.Icc (i₀ + 1) (i₀ * i₀),
          (1 / (i - 1 : ℝ) - 1 / (i : ℝ))) -
        #S * (1 / (i₀ * (i₀ + 1) : ℝ)) ≤
      (∑ i ∈ Finset.Icc (i₀ + 1) (i₀ * i₀),
          (1 / (i - 1 : ℝ) - 1 / (i : ℝ))) -
        ∑ i ∈ S ∩ Finset.Icc (i₀ + 1) (i₀ * i₀),
          (1 / (i - 1 : ℝ) - 1 / (i : ℝ)) from
      sub_le_sub_left h_inter_sum_bound _)
  field_simp
  rw [h_telescope]
  ring_nf
  norm_num [sq, pow_three, mul_assoc, ne_of_gt (zero_lt_three.trans_le hi₀)]
  nlinarith [(by norm_cast : (3 : ℝ) ≤ i₀), mul_inv_cancel₀ (by positivity : (i₀ : ℝ) ≠ 0)]

/-- Key arithmetic bound for the avoided measure. -/
lemma avoided_measure_arithmetic
    (i₀ t : ℕ) (hi₀ : t * (t + 1) < i₀) (ht : 3 ≤ t) :
    (1 : ℝ) / (2000 * ((i₀ : ℝ) - 1)) ≤
    1 / 1000 * ((1 : ℝ) / i₀ - (1 + t) / i₀ ^ 2) := by
  field_simp
  rw [ div_le_div_iff₀ ] <;>
    nlinarith only [
      show ( i₀ : ℝ ) ≥ t * ( t + 1 ) + 1 by norm_cast,
      show ( t : ℝ ) ≥ 3 by norm_cast,
      sq ( t : ℝ ) ]

/-- Existence of `i₀` with required properties. -/
lemma i0_exists (t : ℕ) (ht : 100 < t) (rq : ℝ) (hrq : 0 < rq)
    (hgap : rq ≤ 1 / ((t : ℝ) * (t + 1))) :
    ∃ i₀ : ℕ, 3 ≤ i₀ ∧ t * (t + 1) < i₀ ∧ 1000 ≤ i₀ ∧
      (1 : ℝ) / i₀ < rq ∧ rq ≤ 1 / ((i₀ : ℝ) - 1) ∧
      (t : ℕ) ≤ i₀ - 2 := by
  refine ⟨ ⌊1 / rq⌋₊ + 1, ?_, ?_, ?_, ?_, ?_, ?_ ⟩ <;> norm_num at *
  any_goals
    rw [Nat.le_floor_iff (by positivity)]
    norm_num
    nlinarith [inv_pos.mpr hrq, mul_inv_cancel₀ (ne_of_gt hrq),
      inv_pos.mpr (by positivity : 0 < (t : ℝ) + 1),
      mul_inv_cancel₀ (ne_of_gt (by positivity : 0 < (t : ℝ) + 1)),
      inv_pos.mpr (by positivity : 0 < (t : ℝ)),
      mul_inv_cancel₀ (ne_of_gt (by positivity : 0 < (t : ℝ)))]
  · exact Nat.succ_le_succ ( Nat.le_floor <| by
      norm_num
      nlinarith [
        inv_pos.mpr hrq,
        mul_inv_cancel₀ hrq.ne',
        inv_pos.mpr ( by positivity : 0 < ( t : ℝ ) + 1 ),
        mul_inv_cancel₀ ( by positivity : ( t : ℝ ) + 1 ≠ 0 ),
        inv_pos.mpr ( by positivity : 0 < ( t : ℝ ) ),
        mul_inv_cancel₀ ( by positivity : ( t : ℝ ) ≠ 0 ),
        ( by norm_cast : ( 100 : ℝ ) < t ) ] )
  · exact Nat.succ_le_succ ( Nat.le_floor <| by
      norm_num
      nlinarith [
        inv_pos.2 hrq,
        mul_inv_cancel₀ hrq.ne',
        inv_pos.2 ( by positivity : 0 < ( t : ℝ ) + 1 ),
        mul_inv_cancel₀ ( by positivity : ( t : ℝ ) + 1 ≠ 0 ),
        inv_pos.2 ( by positivity : 0 < ( t : ℝ ) ),
        mul_inv_cancel₀ ( by positivity : ( t : ℝ ) ≠ 0 ),
        ( by norm_cast : ( 100 : ℝ ) < t ) ] )
  · exact inv_lt_of_inv_lt₀ hrq <| Nat.lt_floor_add_one _
  · exact le_trans ( by norm_num )
      ( inv_anti₀
        ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by
          nlinarith [
            inv_pos.mpr hrq,
            mul_inv_cancel₀ hrq.ne',
            show ( t : ℝ ) ≥ 101 by norm_cast,
            inv_pos.mpr ( by positivity : 0 < ( t : ℝ ) + 1 ),
            mul_inv_cancel₀ ( by positivity : ( t : ℝ ) + 1 ≠ 0 ),
            inv_pos.mpr ( by positivity : 0 < ( t : ℝ ) ),
            mul_inv_cancel₀ ( by positivity : ( t : ℝ ) ≠ 0 ) ] )
        <| Nat.floor_le <| inv_nonneg.mpr hrq.le )
  · refine Nat.le_sub_of_add_le ?_
    refine Nat.succ_le_succ ( Nat.le_floor ?_ )
    field_simp at *
    norm_num
    nlinarith [(by norm_cast : (100 : ℝ) < t)]

set_option maxHeartbeats 800000 in
-- This avoided-set construction combines the previous measure and interval estimates.
/-- Existence of an avoided measurable set with positive measure. -/
lemma exists_avoided_set
    (s t : ℕ) (hs : 100 ≤ s) (hst : s < t)
    (S : Finset ℕ) (hS_card : S.card = t) (hS_valid : ValidEgyptian S)
    (q r : ℝ) (hq : q = egyptianSum S) (hqr : q < r)
    (hgap : r - q ≤ 1 / ((t : ℝ) * (t + 1)))
    (hS_best : ∀ x, q < x → x ≤ r → IsBestNTerm S t x) :
    ∃ A : Set ℝ, MeasurableSet A ∧ A ⊆ Set.Ioc q r ∧
      (∀ x ∈ X_set s (t + 2) ∩ Set.Ioc q r, x ∉ A) ∧
      volume A ≥ ENNReal.ofReal ((r - q) / 2000) := by
  obtain ⟨ i₀, hi₀ ⟩ := i0_exists t ( by linarith ) ( r - q ) ( sub_pos.mpr hqr ) hgap
  obtain ⟨E, hE_meas, hE_sub, hE_nongr⟩ :
      ∃ E : ℕ → Set ℝ,
        (∀ i, MeasurableSet (E i)) ∧
        (∀ i, E i ⊆ Set.Ioc ((1 : ℝ) / i) (1 / ((i : ℝ) - 1))) ∧
        (∀ i, 1000 ≤ i →
          volume (E i) ≥
            ENNReal.ofReal (1 / 1000 * (1 / ((i : ℝ) - 1) - 1 / i))) ∧
        (∀ i, 1000 ≤ i →
          ∀ x ∈ E i,
            ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ≠ b ∧ a ≠ i ∧ b ≠ i ∧
              (1 : ℝ) / a + 1 / b < x ∧
              ∀ j : ℕ, 0 < j → j ≠ i → (1 : ℝ) / i + 1 / j < x →
                (1 : ℝ) / i + 1 / j < 1 / a + 1 / b) := by
    choose! E hE₁ hE₂ hE₃ hE₄ using non_greedy_measure_bound_strict
    use fun i => if 1000 ≤ i then E i else ∅
    aesop
  refine ⟨ ⋃ i ∈ Finset.Icc ( i₀ + 1 ) ( i₀ * i₀ ) \ S,
      ( fun x => x - q ) ⁻¹' ( E i ),
      ?_, ?_, ?_, ?_ ⟩
  · exact MeasurableSet.biUnion ( Finset.countable_toSet _ ) fun i hi =>
      measurable_id.sub_const q ( hE_meas i )
  · simp_all +decide [ Set.subset_def ]
    intro x i hi₁ hi₂ hi₃ hi₄
    have := hE_sub i _ hi₄
    constructor
    · linarith [ inv_pos.mpr ( by
        norm_cast
        linarith : 0 < ( i : ℝ ) ) ]
    · linarith [
        inv_anti₀ ( by
          norm_num
          linarith )
          ( show ( i : ℝ ) ≥ i₀ by
            norm_cast
            linarith ),
        inv_anti₀ ( by
          norm_num
          linarith )
          ( show ( i - 1 : ℝ ) ≥ i₀ by
            exact le_tsub_of_add_le_right ( by norm_cast ) ) ]
  · intro x hx hx_A
    simp only [Set.mem_iUnion] at hx_A
    obtain ⟨i, hi_mem, hx_Ei⟩ := hx_A
    have hi_notS := Finset.mem_sdiff.mp hi_mem |>.2
    have hi_Icc := Finset.mem_sdiff.mp hi_mem |>.1
    have hi_ge : 1000 ≤ i := by linarith [Finset.mem_Icc.mp hi_Icc |>.1]
    have hx_E := hE_sub i hx_Ei
    have hgap_ub : x - q ≤ 1 / ((i : ℝ) - 1) := hx_E.2
    apply sub_interval_avoidance s t hst S hS_card hS_valid q hq x hx.1
      (hS_best x hx.2.1 hx.2.2)
      i hi_ge hi_notS hx_E.1 hgap_ub
      (E i) (hE_nongr.2 i hi_ge)
    exact hx_Ei
  · have h_measure_sum :
        volume (⋃ i ∈ Finset.Icc (i₀ + 1) (i₀ * i₀) \ S,
          (fun x => x - q) ⁻¹' (E i)) =
        ∑ i ∈ Finset.Icc (i₀ + 1) (i₀ * i₀) \ S, volume (E i) := by
      rw [ MeasureTheory.measure_biUnion_finset ]
      · simp +decide [ sub_eq_add_neg ]
      · intros i hi j hj hij
        simp_all +decide [ Set.disjoint_left ]
        intro x hx₁ hx₂
        have := hE_sub i hx₁
        have := hE_sub j hx₂
        simp_all +decide [Set.subset_def]
        have := hE_sub i _ hx₁
        have := hE_sub j _ hx₂
        rcases lt_or_gt_of_ne hij with hij | hij <;> norm_num at *
        · linarith [
            inv_anti₀ ( by linarith ) ( show ( j : ℝ ) ≥ i + 1 by norm_cast ),
            inv_anti₀ ( by
              norm_num
              linarith )
              ( show ( j - 1 : ℝ ) ≥ i by
                linarith [ show ( j : ℝ ) ≥ i + 1 by norm_cast ] ) ]
        · linarith [
            inv_anti₀ ( by linarith ) ( show ( i : ℝ ) ≥ j + 1 by norm_cast ),
            inv_anti₀ ( by
              norm_num
              linarith )
              ( show ( i - 1 : ℝ ) ≥ j by
                exact le_tsub_of_add_le_right ( by norm_cast ) ) ]
      · exact fun i hi => measurable_id.sub_const q ( hE_meas i )
    have h_measure_sum :
        ∑ i ∈ Finset.Icc (i₀ + 1) (i₀ * i₀) \ S, volume (E i) ≥
          ENNReal.ofReal
            (1 / 1000 * ∑ i ∈ Finset.Icc (i₀ + 1) (i₀ * i₀) \ S,
              (1 / ((i : ℝ) - 1) - 1 / i)) := by
      rw [ ENNReal.ofReal_mul ( by norm_num ), ENNReal.ofReal_sum_of_nonneg ]
      · rw [ Finset.mul_sum _ _ _ ]
        gcongr
        rw [← ENNReal.ofReal_mul (by norm_num)]
        exact hE_nongr.1 _ (by linarith [Finset.mem_Icc.mp (Finset.mem_sdiff.mp ‹_› |>.1)])
      · exact fun i hi => sub_nonneg_of_le <|
          one_div_le_one_div_of_le
            ( by
              norm_num
              nlinarith [ Finset.mem_Icc.mp <| Finset.mem_sdiff.mp hi |>.1 ] )
            ( by linarith )
    have h_measure_sum :
        ∑ i ∈ Finset.Icc (i₀ + 1) (i₀ * i₀) \ S,
          (1 / ((i : ℝ) - 1) - 1 / i) ≥
        1 / (i₀ : ℝ) - (1 + t) / (i₀ : ℝ) ^ 2 := by
      have := telescoping_sum_lower_bound i₀ ( by linarith ) S
      simp_all only [one_div, sum_sub_distrib, mul_inv_rev, tsub_le_iff_right, ge_iff_le]
    have h_measure_sum : 1 / 1000 * (1 / (i₀ : ℝ) - (1 + t) / (i₀ : ℝ) ^ 2) ≥ (r - q) / 2000 := by
      have := avoided_measure_arithmetic i₀ t ( by linarith ) ( by linarith )
      refine le_trans ?_ this
      rw [ div_le_div_iff₀ ] <;>
        nlinarith [
          show ( i₀ : ℝ ) ≥ 1000 by exact_mod_cast hi₀.2.2.1,
          one_div_mul_cancel ( show ( i₀ : ℝ ) - 1 ≠ 0 by
            exact sub_ne_zero_of_ne ( by
              norm_cast
              linarith ) ) ]
    refine le_trans ?_ ( le_trans ‹_› ?_ )
    · exact ENNReal.ofReal_le_ofReal ( by linarith )
    · aesop

/-! ## §10. Per-interval Measure Bound and Aggregation -/

/-- Gap bound for the fiber at `q` within `X_set s t`. -/
lemma fiber_gap_bound (s t : ℕ) (ht : s ≤ t) (ht2 : 2 ≤ t)
    (q : ℝ) (hne : (X_fiber s t q).Nonempty) :
    sSup (X_fiber s t q) - q ≤ 1 / ((t : ℝ) * (t + 1)) := by
  have hr_mem := fiber_sup_mem_X_set s t q hne
  have hbest := bestNTermSet_isBest t _ hr_mem.1
  have hq_eq : q = egyptianSum (bestNTermSet t (sSup (X_fiber s t q))) := by
    have h1 := fiber_sup_bestNTermSum s t q hne
    have h2 := bestNTermSum_unique t _ hr_mem.1 _ hbest
    linarith
  linarith [best_sum_gap_bound t ht2 _ hr_mem.1
    (hr_mem.2.1.trans (harmonicNumber_mono ht)) _ hbest]

/-- `X_set s t` decomposes as a countable disjoint union of intervals `(q_j, r_j]`. -/
lemma X_set_eq_disjoint_union (s t : ℕ) (hs : 0 < s) (ht : s ≤ t) :
    ∃ (ι : Type) (_ : Countable ι)
      (S : ι → Finset ℕ) (q r : ι → ℝ),
      (∀ j, (S j).card = t) ∧
      (∀ j, ValidEgyptian (S j)) ∧
      (∀ j, q j = egyptianSum (S j)) ∧
      (∀ j, q j < r j) ∧
      (∀ j, r j ≤ harmonicNumber s) ∧
      (∀ j, r j - q j ≤ 1 / ((t : ℝ) * (t + 1))) ∧
      (∀ j, ∀ x, q j < x → x ≤ r j → IsBestNTerm (S j) t x) ∧
      (∀ j₁ j₂, j₁ ≠ j₂ → Disjoint (Set.Ioc (q j₁) (r j₁)) (Set.Ioc (q j₂) (r j₂))) ∧
      X_set s t = ⋃ j, Set.Ioc (q j) (r j) := by
  use {qv : ℝ | (X_fiber s t qv).Nonempty}
  refine ⟨ ?_, fun j => bestNTermSet t ( sSup ( X_fiber s t j ) ),
    fun j => egyptianSum ( bestNTermSet t ( sSup ( X_fiber s t j ) ) ),
    fun j => sSup ( X_fiber s t j ), ?_, ?_, ?_, ?_, ?_ ⟩
  any_goals tauto
  · refine Set.Countable.mono ?_
      ( show Set.Countable ( Set.range ( fun S : Finset ℕ => egyptianSum S ) ) from ?_ )
    · intro qv hqv
      obtain ⟨x, hx⟩ := hqv
      have hqv_eq : qv = bestNTermSum t x := by
        exact hx.2.symm
      use bestNTermSet t x
      rw [ hqv_eq, bestNTermSum_eq ]
      exact hx.1.1
    · exact Set.countable_range _
  · intro j
    have := fiber_sup_mem_X_set s t j.val j.prop
    exact bestNTermSet_isBest t _ this.1 |>.1
  · intro j
    have := bestNTermSet_isBest t ( sSup ( X_fiber s t j ) )
      ( show 0 < sSup ( X_fiber s t j ) from ?_ )
    · exact this.2.1.1
    · have := fiber_sup_mem_X_set s t j.val j.prop
      exact this.1
  · intro j
    have h_pos : 0 < sSup (X_fiber s t j.val) := by
      have := j.2
      obtain ⟨x, hx⟩ := this
      exact lt_of_lt_of_le hx.1.1
        (le_csSup ⟨harmonicNumber s, fun x hx => hx.1.2.1⟩ hx)
    have h_lt :
        egyptianSum (bestNTermSet t (sSup (X_fiber s t j.val))) <
          sSup (X_fiber s t j.val) := by
      exact bestNTermSum_lt t _ h_pos |> fun h => by
        simpa only [ bestNTermSum_eq t _ h_pos ] using h
    exact h_lt
  · refine ⟨ ?_, ?_, ?_, ?_, ?_ ⟩
    · exact fun j => csSup_le ( j.2 ) fun x hx => hx.1.2.1
    · intro j
      by_cases ht2 : 2 ≤ t
      · convert fiber_gap_bound s t ht ht2 j.val j.prop using 1
        have := fiber_sup_bestNTermSum s t j.val j.prop
        rw [ bestNTermSum_eq ] at this
        · simp_all only [mem_setOf_eq]
        · exact fiber_sup_mem_X_set s t j.val j.prop |>.1
      · interval_cases t <;> interval_cases s ; norm_num at *
        have h_fiber : ∀ x ∈ X_fiber 1 1 j.val, x ≤ 1 / 2 + egyptianSum (bestNTermSet 1 x) := by
          intro x hx
          have h_fiber : IsBestNTerm (bestNTermSet 1 x) 1 x := by
            exact bestNTermSet_isBest 1 x ( by linarith [ hx.1.1 ] )
          have := h_fiber.2.2
          contrapose! this
          use {2}
          unfold IsUnderapprox egyptianSum
          norm_num
          unfold egyptianSum at this
          norm_num at this
          have h_nonneg :
              (∑ y ∈ bestNTermSet 1 x, ( y : ℝ ) ⁻¹) ≥ 0 := by
            exact Finset.sum_nonneg fun _ _ =>
              inv_nonneg.2 ( Nat.cast_nonneg _ )
          exact ⟨
            ⟨ by
                unfold ValidEgyptian
                norm_num,
              by
                linarith [ h_nonneg ] ⟩,
            by
              linarith [ h_nonneg,
                show x ≤ 1 by
                  exact hx.1.2.1.trans ( by norm_num [ harmonicNumber ] ) ] ⟩
        refine le_trans
          (show sSup (X_fiber 1 1 j.val) ≤
              1 / 2 + egyptianSum (bestNTermSet 1 (sSup (X_fiber 1 1 j.val))) from ?_)
          ?_
        · refine csSup_le ?_ ?_
          · exact j.2
          · grind +suggestions
        · norm_num
    · intro j x hx₁ hx₂
      apply IsBestNTerm_of_Ioc
      · apply bestNTermSet_isBest
        refine lt_of_lt_of_le ?_ hx₂
        refine lt_of_le_of_lt ?_ hx₁
        exact Finset.sum_nonneg fun _ _ => by positivity
      · exact hx₁
      · exact hx₂
    · intro j₁ j₂ hj
      rw [ Set.disjoint_left ]
      intro x hx₁ hx₂
      have h_fiber_eq :
          X_fiber s t j₁.val = Set.Ioc j₁.val (sSup (X_fiber s t j₁.val)) ∧
            X_fiber s t j₂.val = Set.Ioc j₂.val (sSup (X_fiber s t j₂.val)) := by
        exact ⟨ X_fiber_eq_Ioc s t ht _ j₁.2, X_fiber_eq_Ioc s t ht _ j₂.2 ⟩
      have h_fiber_eq : x ∈ X_fiber s t j₁.val ∧ x ∈ X_fiber s t j₂.val := by
        have h_fiber_eq :
            egyptianSum (bestNTermSet t (sSup (X_fiber s t j₁.val))) = j₁.val ∧
              egyptianSum (bestNTermSet t (sSup (X_fiber s t j₂.val))) = j₂.val := by
          have h_fiber_eq :
              bestNTermSum t (sSup (X_fiber s t j₁.val)) = j₁.val ∧
                bestNTermSum t (sSup (X_fiber s t j₂.val)) = j₂.val := by
            exact ⟨ fiber_sup_bestNTermSum s t _ j₁.2,
              fiber_sup_bestNTermSum s t _ j₂.2 ⟩
          convert h_fiber_eq using 1
          · rw [ bestNTermSum_eq ]
            exact lt_of_lt_of_le
              ( show 0 < x from by
                linarith [ hx₁.1,
                  show 0 ≤
                      egyptianSum ( bestNTermSet t ( sSup ( X_fiber s t j₁.val ) ) )
                    from Finset.sum_nonneg fun _ _ => by positivity ] )
              hx₁.2
          · rw [ bestNTermSum_eq ]
            exact lt_of_lt_of_le
              ( show 0 < x from by
                linarith [ hx₂.1,
                  show 0 ≤
                      egyptianSum ( bestNTermSet t ( sSup ( X_fiber s t j₂.val ) ) )
                    from Finset.sum_nonneg fun _ _ =>
                      one_div_nonneg.mpr <| Nat.cast_nonneg _ ] )
              hx₂.2
        grind
      exact hj ( Subtype.ext <| by linarith [ h_fiber_eq.1.2, h_fiber_eq.2.2 ] )
    · ext x
      constructor
      · intro hx
        simp +zetaDelta at *
        refine ⟨ bestNTermSum t x, ?_, ?_, ?_ ⟩
        · have := fiber_sup_bestNTermSum s t ( bestNTermSum t x ) ?_
          · rw [ bestNTermSum_eq ] at this
            · exact this.symm ▸ bestNTermSum_lt t x hx.1
            · exact hx.1.trans_le
                ( le_csSup
                  ( show BddAbove ( X_fiber s t ( bestNTermSum t x ) ) from
                    ⟨ harmonicNumber s, fun y hy => hy.1.2.1 ⟩ )
                  ⟨ hx, rfl ⟩ )
          · exact ⟨ x, hx, rfl ⟩
        · exact ⟨ x, hx, rfl ⟩
        · exact le_csSup
            ( show BddAbove ( X_fiber s t ( bestNTermSum t x ) ) from
              ⟨ harmonicNumber s, fun y hy => hy.1.2.1 ⟩ )
            ⟨ hx, rfl ⟩
      · simp +zetaDelta at *
        intro q hx₁ hx₂ hx₃
        refine X_set_downward_closed_in_fiber s t ht ?_ ?_ ?_ ?_ ?_ ?_
        · exact sSup ( X_fiber s t q )
        · exact fiber_sup_mem_X_set s t q hx₂
        · exact lt_of_le_of_lt ( Finset.sum_nonneg fun _ _ => by positivity ) hx₁
        · have hpos := (fiber_sup_mem_X_set s t q hx₂).1
          simpa [bestNTermSum_eq t _ hpos] using hx₁
        · linarith

/-- Per-interval bound: `|X_{s,t+2} ∩ (q, r]| ≤ (1999/2000) · |(q, r]|`. -/
lemma per_interval_bound (s t : ℕ) (hs : 100 ≤ s) (hst : s < t)
    (S : Finset ℕ) (hS_card : S.card = t) (hS_valid : ValidEgyptian S)
    (q r : ℝ) (hq : q = egyptianSum S) (hqr : q < r)
    (hgap : r - q ≤ 1 / ((t : ℝ) * (t + 1)))
    (hS_best : ∀ x, q < x → x ≤ r → IsBestNTerm S t x) :
    volume (X_set s (t + 2) ∩ Set.Ioc q r) ≤
      ENNReal.ofReal (1999 / 2000) * volume (Set.Ioc q r) := by
  obtain ⟨A, hA_meas, hA_sub, hA_disj, hA_vol⟩ := exists_avoided_set s t hs hst S
    hS_card hS_valid q r hq hqr hgap hS_best
  have h_incl : X_set s (t + 2) ∩ Set.Ioc q r ⊆ Set.Ioc q r \ A := by
    intro x hx
    exact ⟨hx.2, hA_disj x hx⟩
  have h_vol_ne_top : volume A ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hA_sub) (by simp [Real.volume_Ioc]))
  calc volume (X_set s (t + 2) ∩ Set.Ioc q r)
      ≤ volume (Set.Ioc q r \ A) := measure_mono h_incl
    _ = volume (Set.Ioc q r) - volume A :=
        measure_sdiff hA_sub hA_meas.nullMeasurableSet h_vol_ne_top
    _ ≤ volume (Set.Ioc q r) - ENNReal.ofReal ((r - q) / 2000) :=
        tsub_le_tsub_left hA_vol _
    _ = ENNReal.ofReal (r - q) - ENNReal.ofReal ((r - q) / 2000) := by
        rw [Real.volume_Ioc]
    _ = ENNReal.ofReal (r - q - (r - q) / 2000) :=
        (ENNReal.ofReal_sub _ (by linarith)).symm
    _ = ENNReal.ofReal (1999 / 2000 * (r - q)) := by ring_nf
    _ = ENNReal.ofReal (1999 / 2000) * ENNReal.ofReal (r - q) :=
        ENNReal.ofReal_mul (by positivity)
    _ = ENNReal.ofReal (1999 / 2000) * volume (Set.Ioc q r) := by
        rw [Real.volume_Ioc]

/-! ## §11. The Inductive Estimate and Main Theorem -/

/-- **Inductive estimate** (Kovač [1, Lemma 2]):
    `|X_{s,t+2}| ≤ (1999/2000) · |X_{s,t}|` for `100 ≤ s < t`. -/
theorem inductive_estimate (s t : ℕ) (hs : 100 ≤ s) (hst : s < t) :
    volume (X_set s (t + 2)) ≤ (ENNReal.ofReal (1999 / 2000)) * volume (X_set s t) := by
  obtain ⟨ι, hι, S, q, r, hcard, hvalid, hq, hqr, hr, hgap, hbest, hdisj, heq⟩ :=
    X_set_eq_disjoint_union s t (by linarith) (by linarith)
  have hsub : X_set s (t + 2) ⊆ ⋃ j, Set.Ioc (q j) (r j) :=
    le_trans (X_set_antitone_t s (by linarith : t ≤ t + 2)) heq.le
  calc volume (X_set s (t + 2))
      ≤ volume (⋃ j, X_set s (t + 2) ∩ Set.Ioc (q j) (r j)) := by
        apply measure_mono
        intro x hx
        exact Set.mem_iUnion.mpr (Set.mem_iUnion.mp (hsub hx) |>.imp fun j hj => ⟨hx, hj⟩)
    _ ≤ ∑' j, volume (X_set s (t + 2) ∩ Set.Ioc (q j) (r j)) :=
        measure_iUnion_le _
    _ ≤ ∑' j, (ENNReal.ofReal (1999 / 2000)) * volume (Set.Ioc (q j) (r j)) := by
        apply ENNReal.tsum_le_tsum
        intro j
        exact per_interval_bound s t hs hst (S j) (hcard j) (hvalid j)
          (q j) (r j) (hq j) (hqr j) (hgap j) (hbest j)
    _ = (ENNReal.ofReal (1999 / 2000)) * ∑' j, volume (Set.Ioc (q j) (r j)) := by
        rw [ENNReal.tsum_mul_left]
    _ = (ENNReal.ofReal (1999 / 2000)) * volume (⋃ j, Set.Ioc (q j) (r j)) := by
        congr 1
        rw [measure_iUnion (fun j₁ j₂ hne => hdisj j₁ j₂ hne)
            (fun j => measurableSet_Ioc)]
    _ = (ENNReal.ofReal (1999 / 2000)) * volume (X_set s t) := by
        rw [heq]

/-- `EventuallyGreedy x` implies `x` is in `⋃_s ⋂_{t ≥ s+1} X_set s t`. -/
lemma eventuallyGreedy_subset :
    {x : ℝ | EventuallyGreedy x} ⊆ ⋃ s, ⋂ t ∈ Set.Ici (s + 1), X_set s t := by
  intro x hx
  obtain ⟨m, hm_mono, hm_pos, n₀, hm_best⟩ := hx.right
  obtain ⟨s, hs⟩ : ∃ s : ℕ, x ≤ harmonicNumber s ∧ n₀ ≤ s := by
    obtain ⟨s, hs⟩ : ∃ s : ℕ, harmonicNumber s > x := by
      have h_harmonic_unbounded : Filter.Tendsto harmonicNumber Filter.atTop Filter.atTop := by
        exact not_summable_iff_tendsto_nat_atTop_of_nonneg
          ( fun _ => by positivity ) |>.1
          ( by
            exact_mod_cast mt ( summable_nat_add_iff 1 |>.1 )
              Real.not_summable_one_div_natCast )
      exact ( h_harmonic_unbounded.eventually_gt_atTop x ) |> fun h => h.exists
    exact ⟨ s + n₀, le_trans hs.le <| harmonicNumber_mono <| by linarith, by linarith ⟩
  refine Set.mem_iUnion.mpr ⟨ s, Set.mem_iInter₂.mpr fun t ht =>
    ⟨ by linarith [ hx.1 ], hs.1, m, hm_mono, hm_pos,
      fun n hn₁ hn₂ => hm_best n ( by linarith ) ⟩ ⟩

/-- `X_{s,t}` has volume `≤ H_s`. -/
lemma X_set_volume_le_harmonic (s t : ℕ) :
    volume (X_set s t) ≤ ENNReal.ofReal (harmonicNumber s) := by
  calc volume (X_set s t)
      ≤ volume (Set.Ioc 0 (harmonicNumber s)) :=
        measure_mono (X_set_subset_Ioc s t)
    _ = ENNReal.ofReal (harmonicNumber s - 0) := Real.volume_Ioc
    _ = ENNReal.ofReal (harmonicNumber s) := by ring_nf

/-- Geometric decay: `volume(X_set s (s+1+2k)) ≤ c^k · H_s`. -/
lemma X_set_geometric_decay (s : ℕ) (hs : 100 ≤ s) (k : ℕ) :
    volume (X_set s (s + 1 + 2 * k)) ≤
      (ENNReal.ofReal (1999 / 2000)) ^ k * ENNReal.ofReal (harmonicNumber s) := by
  induction k with
  | zero =>
    simp
    exact X_set_volume_le_harmonic s (s + 1)
  | succ k ih =>
    have hst : s < s + 1 + 2 * k := by omega
    have heq : s + 1 + 2 * (k + 1) = (s + 1 + 2 * k) + 2 := by omega
    calc volume (X_set s (s + 1 + 2 * (k + 1)))
        = volume (X_set s ((s + 1 + 2 * k) + 2)) := by rw [heq]
      _ ≤ ENNReal.ofReal (1999 / 2000) * volume (X_set s (s + 1 + 2 * k)) :=
          inductive_estimate s (s + 1 + 2 * k) hs hst
      _ ≤ ENNReal.ofReal (1999 / 2000) *
            ((ENNReal.ofReal (1999 / 2000)) ^ k * ENNReal.ofReal (harmonicNumber s)) := by
          exact mul_le_mul_of_nonneg_left ih zero_le
      _ = (ENNReal.ofReal (1999 / 2000)) ^ (k + 1) * ENNReal.ofReal (harmonicNumber s) := by
          rw [pow_succ]
          ring

/-- The intersection `⋂_{t ≥ s+1} X_{s,t}` is monotone in `s`. -/
lemma iInter_X_set_mono_s (s₁ s₂ : ℕ) (h : s₁ ≤ s₂) :
    (⋂ t ∈ Set.Ici (s₁ + 1), X_set s₁ t) ⊆ ⋂ t ∈ Set.Ici (s₂ + 1), X_set s₂ t := by
  intro x hx
  simp only [Set.mem_iInter] at hx ⊢
  intro t ht
  have ht' : t ∈ Set.Ici (s₁ + 1) := Set.mem_Ici.mpr (by
    have := Set.mem_Ici.mp ht
    omega)
  exact X_set_mono_s s₁ s₂ t h (hx t ht')

/-- For `s ≥ 100`, the intersection `⋂_{t > s} X_{s,t}` has measure zero. -/
lemma X_set_iInter_measure_zero (s : ℕ) (hs : 100 ≤ s) :
    volume (⋂ t ∈ Set.Ici (s + 1), X_set s t) = 0 := by
  have h_subset : ∀ k : ℕ, (⋂ t ∈ Set.Ici (s + 1), X_set s t) ⊆ X_set s (s + 1 + 2 * k) := by
    exact fun k x hx => Set.mem_iInter₂.mp hx _ <| Set.mem_Ici.mpr <| Nat.le_add_right _ _
  have h_volume_le :
      ∀ k : ℕ,
        volume (⋂ t ∈ Set.Ici (s + 1), X_set s t) ≤
          (ENNReal.ofReal (1999 / 2000)) ^ k * ENNReal.ofReal (harmonicNumber s) := by
    exact fun k =>
      le_trans ( MeasureTheory.measure_mono ( h_subset k ) ) ( X_set_geometric_decay s hs k )
  have h_lim_zero :
      Filter.Tendsto
        (fun k : ℕ =>
          (ENNReal.ofReal (1999 / 2000)) ^ k * ENNReal.ofReal (harmonicNumber s))
        Filter.atTop (nhds 0) := by
    convert ENNReal.Tendsto.mul_const
        ( ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one _ ) _ using 1 <;>
      norm_num
  exact le_antisymm ( le_of_tendsto_of_tendsto' tendsto_const_nhds h_lim_zero h_volume_le ) bot_le

/-- For any `s`, the intersection `⋂_{t > s} X_{s,t}` has measure zero. -/
lemma X_set_iInter_measure_zero' (s : ℕ) :
    volume (⋂ t ∈ Set.Ici (s + 1), X_set s t) = 0 := by
  by_cases hs : 100 ≤ s
  · exact X_set_iInter_measure_zero s hs
  · apply le_antisymm _ zero_le
    calc volume (⋂ t ∈ Set.Ici (s + 1), X_set s t)
        ≤ volume (⋂ t ∈ Set.Ici (100 + 1), X_set 100 t) :=
          measure_mono (iInter_X_set_mono_s s 100 (by omega))
      _ = 0 := X_set_iInter_measure_zero 100 le_rfl

/-- **Erdős Problem #206** (Kovač [1, Theorem 1]): The set of positive reals with eventually
    greedy best Egyptian underapproximations has Lebesgue measure zero. -/
theorem erdos_206 : volume {x : ℝ | EventuallyGreedy x} = 0 := by
  apply le_antisymm _ zero_le
  calc volume {x : ℝ | EventuallyGreedy x}
      ≤ volume (⋃ s, ⋂ t ∈ Set.Ici (s + 1), X_set s t) :=
        measure_mono eventuallyGreedy_subset
    _ ≤ ∑' s, volume (⋂ t ∈ Set.Ici (s + 1), X_set s t) :=
        measure_iUnion_le _
    _ = 0 := by
        apply ENNReal.tsum_eq_zero.mpr
        exact X_set_iInter_measure_zero'

#print axioms erdos_206
-- 'Erdos206.EgyptianFractions.erdos_206' depends on axioms: [propext, Classical.choice, Quot.sound]

end EgyptianFractions

end Erdos206
