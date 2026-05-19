/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 264.
https://www.erdosproblems.com/forum/thread/264

Formalization status:
- Partial

Formal authors:
- Aristotle
- Pietro Monticone

URLs:
- https://www.erdosproblems.com/forum/thread/264#post-2258
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos264.md
- https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos264.lean
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/264.lean
-/
/-

This is a Lean formalization of a solution to parts of Erdős Problem
264.

https://www.erdosproblems.com/264

Aristotle from Harmonic proved the result itself, starting from the
formalization that was already available in the Formal Conjectures
project.  This process was operated by Pietro Monticone.


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/
import Mathlib

set_option linter.style.setOption false
set_option aesop.warn.nonterminal false
set_option linter.flexible false
set_option linter.style.cases false
set_option linter.style.induction false
set_option linter.style.maxHeartbeats false
set_option linter.style.multiGoal false
set_option linter.style.refine false
set_option linter.style.whitespace false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Erdos264

/--
A sequence $a_n$ of integers is called an irrationality sequence if
for every bounded sequence of integers $b_n$ with $a_n + b_n \neq 0$ and
$b_n \neq 0$ for all $n$, the sum
$$
  \sum \frac{1}{a_n + b_n}
$$
is irrational.
Note: there are other possible definitions of this concept.
-/
def IsIrrationalitySequence (a : ℕ → ℕ) : Prop :=
  ∀ b : ℕ → ℕ,
    BddAbove (Set.range b) →
      0 ∉ Set.range (a + b) →
        0 ∉ Set.range b →
          Irrational (∑' n, (1 : ℝ) / (a n + b n))

noncomputable section AristotleLemmas

/-
The gap between consecutive terms 1/(2^n+k) and 1/(2^n+k+1) is bounded
by the length of the tail sum interval.
-/
lemma gap_inequality (n : ℕ) (k : ℕ) (h_ge : 1 ≤ k) (h_le : k ≤ 3) :
  1 / (2^n + (k : ℝ)) - 1 / (2^n + (k : ℝ) + 1) ≤
  ∑' m, (1 / (2^(n + 1 + m) + 1 : ℝ) - 1 / (2^(n + 1 + m) + 4 : ℝ)) := by
    -- Let's simplify the general term of the series.
    have h_term :
        ∀ m : ℕ,
          (1 / (2 ^ (n + 1 + m) + 1 : ℝ) -
              1 / (2 ^ (n + 1 + m) + 4 : ℝ)) =
            3 / ((2 ^ (n + 1 + m) + 1) *
              (2 ^ (n + 1 + m) + 4) : ℝ) := by
      intro m; rw [ div_sub_div ] <;> ring_nf <;> positivity;
    -- We'll use the fact that the sum of a geometric series can be bounded.
    have h_geo_series :
        (∑' m : ℕ,
          3 / ((2 ^ (n + 1 + m) + 1) *
            (2 ^ (n + 1 + m) + 4) : ℝ)) ≥
          3 / ((2 ^ (n + 1) + 1) * (2 ^ (n + 1) + 4) : ℝ) *
            ∑' m : ℕ, (1 / 4 : ℝ) ^ m := by
      rw [ ← tsum_mul_left ] ; refine' Summable.tsum_le_tsum _ _ _ ; aesop;
      · field_simp;
        norm_num [ pow_add, pow_mul ];
        rw [
          show ( 4 : ℝ ) ^ i = ( 2 ^ i ) ^ 2 by
            norm_num [ sq, ← mul_pow ]
        ];
        nlinarith [
          show ( 2 ^ n : ℝ ) ≥ 1 by exact one_le_pow₀ ( by norm_num ),
          show ( 2 ^ i : ℝ ) ≥ 1 by exact one_le_pow₀ ( by norm_num ),
          mul_le_mul_of_nonneg_left
            ( show ( 2 ^ n : ℝ ) ≥ 1 by exact one_le_pow₀ ( by norm_num ) )
            ( show ( 0 : ℝ ) ≤ 2 ^ i by positivity ),
          mul_le_mul_of_nonneg_left
            ( show ( 2 ^ i : ℝ ) ≥ 1 by exact one_le_pow₀ ( by norm_num ) )
            ( show ( 0 : ℝ ) ≤ 2 ^ n by positivity )
        ];
      · exact Summable.mul_left _ ( summable_geometric_of_lt_one ( by norm_num ) ( by norm_num ) );
      · -- We can compare our series to a geometric series with ratio $1/4$.
        have h_compare :
            ∀ m : ℕ,
              (3 / ((2 ^ (n + 1 + m) + 1) *
                (2 ^ (n + 1 + m) + 4) : ℝ)) ≤
                3 / (4 ^ (n + 1 + m) : ℝ) := by
          intro m; rw [ div_le_div_iff₀ ] <;> norm_cast <;> ring_nf <;> norm_num;
          norm_num [ pow_mul', ← mul_pow ];
        exact Summable.of_nonneg_of_le ( fun m => by positivity ) h_compare ( by
          exact Summable.mul_left _ <| by
            simpa using summable_geometric_of_lt_one ( by norm_num )
              ( inv_lt_one_of_one_lt₀ <| by norm_num )
              |> Summable.comp_injective <| by
                intro m
                aesop );
    have h_rhs_lower :
        4 / (((2 : ℝ) ^ (n + 1) + 1) * ((2 : ℝ) ^ (n + 1) + 4)) ≤
          ∑' m, (1 / (2^(n + 1 + m) + 1 : ℝ) - 1 / (2^(n + 1 + m) + 4 : ℝ)) := by
      calc
        4 / (((2 : ℝ) ^ (n + 1) + 1) * ((2 : ℝ) ^ (n + 1) + 4))
            = 3 / (((2 : ℝ) ^ (n + 1) + 1) * ((2 : ℝ) ^ (n + 1) + 4)) *
              (∑' m : ℕ, (1 / 4 : ℝ) ^ m) := by
                norm_num [tsum_geometric_of_lt_one]
        _ ≤ ∑' m : ℕ, (3 / ((2 ^ (n + 1 + m) + 1) *
              (2 ^ (n + 1 + m) + 4) : ℝ)) := by
                simpa using h_geo_series
        _ = ∑' m, (1 / (2^(n + 1 + m) + 1 : ℝ) -
              1 / (2^(n + 1 + m) + 4 : ℝ)) := by
                exact tsum_congr fun m => (h_term m).symm
    refine le_trans ?_ h_rhs_lower
    interval_cases k <;> norm_num [pow_succ]
    · field_simp
      nlinarith [pow_pos (by positivity : (0 : ℝ) < 2) n]
    · field_simp
      nlinarith [pow_pos (by positivity : (0 : ℝ) < 2) n]
    · field_simp
      nlinarith [pow_pos (by positivity : (0 : ℝ) < 2) n]

/-
The set of sums S.
-/
def SumSet : Set ℝ :=
  { x : ℝ | ∃ b : ℕ → ℕ, (∀ n, 1 ≤ b n ∧ b n ≤ 4) ∧ x = ∑' n, (1 : ℝ) / (2^n + b n) }

/-
Inductive step: if z is in the range of tail sums at step n, we can choose
the next term b_n such that the remainder is in the range of tail sums at
step n+1.
-/
noncomputable def min_tail (n : ℕ) : ℝ := ∑' m, 1 / (2^(n + m) + 4 : ℝ)
noncomputable def max_tail (n : ℕ) : ℝ := ∑' m, 1 / (2^(n + m) + 1 : ℝ)

lemma inductive_step (n : ℕ) (z : ℝ) (hz : z ∈ Set.Icc (min_tail n) (max_tail n)) :
  ∃ (k : ℕ), k ∈ Finset.Icc 1 4 ∧
    z - 1 / (2^n + (k : ℝ)) ∈
      Set.Icc (min_tail (n + 1)) (max_tail (n + 1)) := by
    have h_gap_ineq :
        ∀ k ∈ ({1, 2, 3} : Finset ℕ),
          1 / (2 ^ n + (k : ℝ)) - 1 / (2 ^ n + (k : ℝ) + 1) ≤
            max_tail (n + 1) - min_tail (n + 1) := by
      -- Their difference is exactly the series starting from `n+1`.
      have h_diff :
          max_tail (n + 1) - min_tail (n + 1) =
            ∑' m, (1 / (2^(n + 1 + m) + 1 : ℝ) -
              1 / (2^(n + 1 + m) + 4 : ℝ)) := by
        unfold max_tail min_tail;
        rw [ Summable.tsum_sub ];
        · -- This is a convergent geometric-series tail.
          have h_geo_series : Summable (fun m : ℕ => (1 : ℝ) / 2^(n+1+m)) := by
            simpa using summable_geometric_two.comp_injective ( add_right_injective _ );
          exact Summable.of_nonneg_of_le
            ( fun m => by positivity )
            ( fun m => by gcongr ; norm_num )
            h_geo_series;
        · -- This is a convergent geometric-series tail.
          have h_geo_series : Summable (fun m : ℕ => (1 : ℝ) / (2^(n + 1 + m))) := by
            simpa using summable_geometric_two.comp_injective ( add_right_injective _ );
          exact Summable.of_nonneg_of_le
            ( fun m => by positivity )
            ( fun m => by gcongr ; norm_num )
            h_geo_series;
      exact fun k hk =>
        h_diff ▸ gap_inequality n k
          ( by fin_cases hk <;> norm_num )
          ( by fin_cases hk <;> norm_num ) |>
            le_trans ( by norm_num ) ;
    -- These are the one-term tail decompositions.
    have h_bounds :
        min_tail n = 1 / (2^n + 4 : ℝ) + min_tail (n + 1) ∧
          max_tail n = 1 / (2^n + 1 : ℝ) + max_tail (n + 1) := by
      unfold min_tail max_tail; aesop;
      · rw [ Summable.tsum_eq_zero_add ];
        · ac_rfl;
        · exact Summable.of_nonneg_of_le
            ( fun _ => by positivity )
            ( fun m => by
              simpa using inv_anti₀ ( by positivity )
                ( show ( 2 ^ ( n + m ) + 4 : ℝ ) ≥ 2 ^ ( n + m ) by linarith ) )
            ( by
              simpa using summable_geometric_two.comp_injective ( add_right_injective n ) );
      · rw [ Summable.tsum_eq_zero_add ];
        · ac_rfl;
        · exact Summable.of_nonneg_of_le
            ( fun m => by positivity )
            ( fun m => by
              simpa using inv_anti₀ ( by positivity )
                ( show ( 2 ^ ( n + m ) + 1 : ℝ ) ≥ 2 ^ ( n + m ) by norm_num ) )
            ( by
              simpa using summable_geometric_two.comp_injective ( add_right_injective n ) );
    norm_num [ add_assoc ] at *;
    exact ⟨
      if ( 2 ^ n + 1 : ℝ ) ⁻¹ + min_tail ( n + 1 ) ≤ z then 1
      else if ( 2 ^ n + 2 : ℝ ) ⁻¹ + min_tail ( n + 1 ) ≤ z then 2
      else if ( 2 ^ n + 3 : ℝ ) ⁻¹ + min_tail ( n + 1 ) ≤ z then 3
      else 4,
      by split_ifs <;> norm_num,
      by split_ifs <;> push_cast <;> linarith,
      by split_ifs <;> push_cast <;> linarith ⟩

set_option maxHeartbeats 0 in
/-
The set of sums S is an interval (OrdConnected).
-/
lemma SumSet_is_OrdConnected : Set.OrdConnected SumSet := by
  have h_interval :
      ∀ z, (∃ x y : ℝ, x ∈ SumSet ∧ y ∈ SumSet ∧ x ≤ z ∧ z ≤ y) →
        z ∈ SumSet := by
    intro z hz
    rcases hz with ⟨w, w_1, left, left_1, left_2, right⟩
    -- We show that `SumSet` is `OrdConnected`.
    have h_ord_connected :
        ∀ z,
          z ∈ Set.Icc (min_tail 0) (max_tail 0) →
            ∃ b : ℕ → ℕ, (∀ n, 1 ≤ b n ∧ b n ≤ 4) ∧
              z = ∑' n, (1 : ℝ) / (2^n + b n) := by
      intro z hz;
      -- We construct a sequence $b_n$ inductively.
      have h_seq :
          ∃ b : ℕ → ℕ, (∀ n, 1 ≤ b n ∧ b n ≤ 4) ∧
            ∀ n,
              z - ∑ i ∈ Finset.range n, (1 : ℝ) / (2^i + b i) ∈
                Set.Icc (min_tail n) (max_tail n) := by
        have h_seq :
            ∀ n,
              ∃ b : ℕ → ℕ, (∀ i, 1 ≤ b i ∧ b i ≤ 4) ∧
                ∀ i ≤ n,
                  z - ∑ j ∈ Finset.range i, (1 : ℝ) / (2^j + b j) ∈
                    Set.Icc (min_tail i) (max_tail i) := by
          -- We proceed by induction on $n$.
          intro n
          induction' n with n ih;
          · exact ⟨ fun _ => 1, fun _ => ⟨ by norm_num, by norm_num ⟩, by simpa using hz ⟩;
          · obtain ⟨ b, hb₁, hb₂ ⟩ := ih;
            obtain ⟨ k, hk₁, hk₂ ⟩ := inductive_step n
              ( z - ∑ j ∈ Finset.range n,
                  ( 1 : ℝ ) / ( 2 ^ j + ( b j : ℝ ) ) )
              ( hb₂ n le_rfl );
            use fun i => if i = n then k else b i;
            aesop;
            · cases a <;> simp_all +decide [ Finset.sum_range_succ ];
              · rw [
                  Finset.sum_congr rfl fun x hx => by
                    rw [ if_neg ( ne_of_lt ( Finset.mem_range.mp hx ) ) ]
                ];
                linarith;
              · rw [
                  Finset.sum_congr rfl fun x hx => by
                    rw [ if_neg ( by linarith [ Finset.mem_range.mp hx ] ) ]
                ];
                aesop;
            · field_simp;
              cases a <;> aesop;
              · rw [ Finset.sum_range_succ ];
                rw [ Finset.sum_congr rfl fun x hx => by aesop ] ; norm_num ; linarith;
              · convert hb₂ i a |>.2 using 1;
                exact congr rfl
                  ( Finset.sum_congr rfl fun x hx => by
                    rw [ if_neg ( by linarith [ Finset.mem_range.mp hx ] ) ] );
        choose f hf1 hf2 using h_seq;
        -- The finite sets $f n$ have a subsequence converging to a function $b$.
        obtain ⟨b, hb⟩ :
            ∃ b : ℕ → ℕ,
              ∃ (nk : ℕ → ℕ), StrictMono nk ∧
                ∀ i, Filter.Tendsto (fun k => f (nk k) i) Filter.atTop
                  (nhds (b i)) := by
          have h_compact : IsCompact (Set.pi Set.univ fun i : ℕ => Set.Icc 1 4 : Set (ℕ → ℕ)) := by
            exact isCompact_univ_pi fun _ => CompactIccSpace.isCompact_Icc;
          have := h_compact.isSeqCompact fun n =>
            show f n ∈ Set.pi Set.univ fun i => Set.Icc 1 4 from fun i _ => hf1 n i;
          exact ⟨ this.choose, this.choose_spec.2.choose,
            this.choose_spec.2.choose_spec.1,
            fun i => tendsto_pi_nhds.mp this.choose_spec.2.choose_spec.2 i ⟩;
        -- This limit function $b$ satisfies the required conditions.
        obtain ⟨nk, hnk_mono, hnk_conv⟩ := hb;
        use b;
        aesop;
        · obtain ⟨ a, ha ⟩ := hnk_conv n; specialize hf1 ( nk a ) n; aesop;
        · obtain ⟨ a, ha ⟩ := hnk_conv n; specialize hf1 ( nk a ) n; aesop;
        · -- The limiting function $b$ satisfies the required condition for $n$.
          have h_subseq :
              ∀ᶠ k in Filter.atTop,
                min_tail n ≤
                  z - ∑ x ∈ Finset.range n, (2 ^ x + (f (nk k) x : ℝ))⁻¹ := by
            -- Since $nk$ is strict, eventually `nk k ≥ n`.
            obtain ⟨N, hN⟩ : ∃ N, ∀ k ≥ N, nk k ≥ n := by
              exact ⟨ n, fun k hk => hk.trans ( hnk_mono.id_le _ ) ⟩;
            exact Filter.eventually_atTop.mpr ⟨ N, fun k hk => hf2 _ _ ( hN _ hk ) |>.1 ⟩;
          have h_subseq :
              Filter.Tendsto
                (fun k => ∑ x ∈ Finset.range n, (2 ^ x + (f (nk k) x : ℝ))⁻¹)
                Filter.atTop
                (nhds (∑ x ∈ Finset.range n, (2 ^ x + (b x : ℝ))⁻¹)) := by
            exact tendsto_finset_sum _ fun i hi =>
              tendsto_const_nhds.congr' <| by
                filter_upwards
                  [Filter.eventually_ge_atTop <| Classical.choose <| hnk_conv i] with k hk
                rw [ Classical.choose_spec ( hnk_conv i ) k hk ];
          exact le_of_tendsto_of_tendsto tendsto_const_nhds ( tendsto_const_nhds.sub h_subseq ) ‹_›;
        · have h_subseq :
              Filter.Tendsto
                (fun k => ∑ x ∈ Finset.range n, (2 ^ x + (f (nk k) x : ℝ))⁻¹)
                Filter.atTop
                (nhds (∑ x ∈ Finset.range n, (2 ^ x + (b x : ℝ))⁻¹)) := by
            exact tendsto_finset_sum _ fun i hi =>
              Filter.Tendsto.inv₀
                ( tendsto_const_nhds.add <| tendsto_const_nhds.congr' <| by
                  filter_upwards
                    [Filter.eventually_ge_atTop <| Classical.choose <| hnk_conv i] with k hk
                  rw [ Classical.choose_spec ( hnk_conv i ) k hk ] )
                ( by positivity );
          have h_subseq :
              Filter.Tendsto
                (fun k =>
                  max_tail n +
                    ∑ x ∈ Finset.range n, (2 ^ x + (f (nk k) x : ℝ))⁻¹)
                Filter.atTop
                (nhds
                  (max_tail n + ∑ x ∈ Finset.range n, (2 ^ x + (b x : ℝ))⁻¹)) := by
            exact tendsto_const_nhds.add h_subseq;
          exact le_of_tendsto_of_tendsto tendsto_const_nhds h_subseq
            ( Filter.eventually_atTop.mpr
              ⟨ n, fun k hk =>
                hf2 ( nk k ) n ( hnk_mono.id_le _ |> le_trans hk ) |>.2 ⟩ );
      -- The finite partial sums converge to `z`.
      obtain ⟨b, hb_bounds, hb_tail⟩ := h_seq;
      have h_sum :
          Filter.Tendsto
            (fun n => ∑ i ∈ Finset.range n, (1 : ℝ) / (2^i + b i))
            Filter.atTop (nhds z) := by
        have h_tail_zero :
            Filter.Tendsto (fun n => max_tail n) Filter.atTop (nhds 0) ∧
              Filter.Tendsto (fun n => min_tail n) Filter.atTop (nhds 0) := by
          have h_tail_zero :
              Filter.Tendsto (fun n => ∑' m, (1 : ℝ) / (2^(n + m) : ℝ))
                Filter.atTop (nhds 0) := by
            norm_num [ pow_add, tsum_mul_left ];
            norm_num [ tsum_mul_right ];
            exact tendsto_const_nhds.div_atTop ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two );
          refine' ⟨
            squeeze_zero
              ( fun n => tsum_nonneg fun m => by positivity )
              ( fun n =>
                Summable.tsum_le_tsum
                  ( fun m => by gcongr ; norm_num )
                  ( by
                    exact Summable.of_nonneg_of_le
                      ( fun m => by positivity )
                      ( fun m => by
                        simpa using inv_anti₀ ( by positivity ) ( by
                          norm_cast
                          linarith [ pow_pos ( zero_lt_two' ℕ ) ( n + m ) ] ) )
                      ( summable_geometric_two.comp_injective ( add_right_injective n ) ) )
                  ( by
                    exact Summable.of_nonneg_of_le
                      ( fun m => by positivity )
                      ( fun m => by simp )
                      ( summable_geometric_two.comp_injective ( add_right_injective n ) ) ) )
              h_tail_zero,
            squeeze_zero
              ( fun n => tsum_nonneg fun m => by positivity )
              ( fun n =>
                Summable.tsum_le_tsum
                  ( fun m => by gcongr ; norm_num )
                  ( by
                    exact Summable.of_nonneg_of_le
                      ( fun m => by positivity )
                      ( fun m => by
                        simpa using inv_anti₀ ( by positivity ) ( by
                          norm_cast
                          linarith [ pow_pos ( zero_lt_two' ℕ ) ( n + m ) ] ) )
                      ( summable_geometric_two.comp_injective ( add_right_injective n ) ) )
                  ( by
                    exact Summable.of_nonneg_of_le
                      ( fun m => by positivity )
                      ( fun m => by simp )
                      ( summable_geometric_two.comp_injective ( add_right_injective n ) ) ) )
              h_tail_zero ⟩;
        have h_tail_zero :
            Filter.Tendsto
              (fun n => z - ∑ i ∈ Finset.range n, (1 : ℝ) / (2^i + b i))
              Filter.atTop (nhds 0) := by
          exact tendsto_of_tendsto_of_tendsto_of_le_of_le
            h_tail_zero.2 h_tail_zero.1
            ( fun n => hb_tail n |>.1 ) ( fun n => hb_tail n |>.2 );
        simpa using h_tail_zero.const_sub z;
      refine' ⟨ b, hb_bounds, _ ⟩;
      exact tendsto_nhds_unique h_sum
        ( Summable.hasSum ( show Summable _ from by
            exact ( by
              by_contra h
              exact not_tendsto_atTop_of_tendsto_nhds h_sum <|
                by
                  exact not_summable_iff_tendsto_nat_atTop_of_nonneg
                    ( fun _ => by positivity ) |>.1 h ) ) |>
          HasSum.tendsto_sum_nat );
    -- The endpoint sums lie in `[min_tail 0, max_tail 0]`.
    have hw_range : w ∈ Set.Icc (min_tail 0) (max_tail 0) := by
      cases left ; aesop;
      · refine' Summable.tsum_le_tsum _ _ _;
        · norm_num +zetaDelta at *;
          exact fun n => inv_anti₀ ( by positivity ) ( by norm_cast; linarith [ left n ] );
        · simp +zetaDelta at *;
          -- This series is dominated by the convergent geometric series.
          have h_dominate : ∀ m : ℕ, (2^m + 4 : ℝ)⁻¹ ≤ (2^m : ℝ)⁻¹ := by
            exact fun m => inv_anti₀ ( by positivity ) ( by linarith );
          exact Summable.of_nonneg_of_le
            ( fun m => by positivity ) h_dominate
            ( by simpa using summable_geometric_two );
        · exact Summable.of_nonneg_of_le
            ( fun n => inv_nonneg.2 ( by positivity ) )
            ( fun n => by
              simpa using inv_anti₀ ( by positivity )
                ( show ( 2 ^ n + ( w_2 n : ℝ ) ) ≥ 2 ^ n by linarith ) )
            ( summable_geometric_two );
      · refine' Summable.tsum_le_tsum _ _ _;
        · exact fun n => by
            rw [ zero_add, inv_eq_one_div ];
            gcongr;
            norm_cast;
            linarith [ left n ] ;
        · -- Each term `(2^n + w_2 n)⁻¹` is bounded by `(2^n)⁻¹`.
          have h_bound : ∀ n, (2^n + w_2 n : ℝ)⁻¹ ≤ (2^n : ℝ)⁻¹ := by
            exact fun n => inv_anti₀ ( by positivity ) ( by
              linarith [ show ( w_2 n : ℝ ) ≥ 1 by exact_mod_cast left n |>.1 ] );
          exact Summable.of_nonneg_of_le
            ( fun n => inv_nonneg.2 ( by positivity ) ) h_bound
            ( by simpa using summable_geometric_two );
        · simp +zetaDelta at *;
          -- This is a convergent geometric series.
          have h_geo_series : Summable (fun m : ℕ => (2^m : ℝ)⁻¹) := by
            simpa using summable_geometric_two;
          exact Summable.of_nonneg_of_le
            ( fun m => by positivity )
            ( fun m => by
              rw [ inv_le_comm₀ ] <;> norm_num ;
              linarith [ pow_pos ( zero_lt_two' ℝ ) m ] )
            h_geo_series
    have hw1_range : w_1 ∈ Set.Icc (min_tail 0) (max_tail 0) := by
      cases left_1 ; aesop;
      · exact le_imp_le_of_le_of_le left_1 right left_2;
      · refine' Summable.tsum_le_tsum _ _ _;
        · norm_num +zetaDelta at *;
          exact fun n => inv_anti₀ ( by positivity ) ( by norm_cast; linarith [ left_3 n ] );
        · exact Summable.of_nonneg_of_le
            ( fun n => inv_nonneg.2 ( by positivity ) )
            ( fun n => by
              simpa using inv_anti₀ ( by positivity )
                ( show ( 2 ^ n + w_2 n : ℝ ) ≥ 2 ^ n by
                  norm_cast
                  linarith [ left_3 n ] ) )
            ( summable_geometric_two );
        · -- This series is dominated by the convergent geometric series.
          have h_dominate : ∀ m : ℕ, (1 : ℝ) / (2^(0 + m) + 1) ≤ 1 / 2^m := by
            exact fun m => by gcongr ; norm_num;
          exact Summable.of_nonneg_of_le
            ( fun m => by positivity ) h_dominate
            ( by simpa using summable_geometric_two );
    exact
      h_ord_connected z
        ⟨ by linarith [ hw_range.1 ], by linarith [ hw1_range.2 ] ⟩ |>
          fun ⟨ b, hb₁, hb₂ ⟩ => ⟨ b, hb₁, hb₂ ⟩;
  refine' ⟨ fun x hx y hy z hz => h_interval z ⟨ x, y, hx, hy, hz.1, hz.2 ⟩ ⟩

/-
The interval [min_tail 0, max_tail 0] is a subset of SumSet.
-/
lemma Icc_subset_SumSet : Set.Icc (min_tail 0) (max_tail 0) ⊆ SumSet := by
  intro z hz;
  -- Construct `b_n` and remainders `z_n` inside the tail intervals.
  have h_seq :
      ∃ b : ℕ → ℕ, (∀ n, 1 ≤ b n ∧ b n ≤ 4) ∧
        ∃ z_seq : ℕ → ℝ,
          (∀ n, z_seq n ∈ Set.Icc (min_tail n) (max_tail n)) ∧
            z_seq 0 = z ∧
              ∀ n, z_seq (n + 1) = z_seq n - (1 : ℝ) / (2^n + b n) := by
    choose! b hb using fun n z hz => inductive_step n z hz;
    use fun n =>
      b n (Nat.recOn n z fun n ih => ih - 1 / (2 ^ n + (b n ih : ℝ)));
    refine' ⟨ _, _ ⟩;
    · intro n;
      have h_seq :
          ∀ n,
            (Nat.recOn n z fun n ih => ih - 1 / (2 ^ n + (b n ih : ℝ))) ∈
              Set.Icc (min_tail n) (max_tail n) := by
        intro n; induction n <;> aesop;
      exact Finset.mem_Icc.mp ( hb n _ ( h_seq n ) |>.1 );
    · use fun n => Nat.recOn n z fun n ih => ih - 1 / ( 2 ^ n + ( b n ih : ℝ ) );
      exact ⟨ fun n => Nat.recOn n hz fun n ih => hb n _ ih |>.2, rfl, fun n => rfl ⟩;
  obtain ⟨ b, hb, z_seq, hz_seq, rfl, hz_seq' ⟩ := h_seq; use b; aesop;
  -- We need to show $z_n \to 0$ as $n \to \infty$.
  have h_zero : Filter.Tendsto z_seq Filter.atTop (nhds 0) := by
    -- Both tails are bounded by a geometric series tending to 0.
    have h_tail_bound : ∀ n, max_tail n ≤ 2 / 2^n ∧ min_tail n ≥ 0 := by
      intros n
      have h_tail_bound : max_tail n ≤ ∑' m, (1 : ℝ) / (2^(n + m)) := by
        refine' Summable.tsum_le_tsum _ _ _;
        · exact fun i => by gcongr ; norm_num;
        · exact Summable.of_nonneg_of_le
            ( fun m => by positivity )
            ( fun m => by
              simpa using inv_anti₀ ( by positivity )
                ( show ( 2 ^ ( n + m ) + 1 : ℝ ) ≥ 2 ^ ( n + m ) by linarith ) )
            ( by
              simpa using summable_geometric_two.comp_injective ( add_right_injective n ) );
        · simpa using summable_geometric_two.comp_injective ( add_right_injective n );
      norm_num [ pow_add, tsum_mul_left ] at *;
      exact ⟨
        h_tail_bound.trans <| by
          rw [
            tsum_mul_right,
            show ( ∑' m : ℕ, ( 2 ^ m : ℝ ) ⁻¹ ) = 2 by
              simpa using tsum_geometric_two
          ];
          ring_nf;
          norm_num,
        tsum_nonneg fun _ => by positivity ⟩;
    exact squeeze_zero
      ( fun n => h_tail_bound n |>.2.trans ( hz_seq n |>.1 ) )
      ( fun n => hz_seq n |>.2.trans ( h_tail_bound n |>.1 ) )
      ( tendsto_const_nhds.div_atTop
        ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two ) );
  -- By definition of $z_seq$, we have $z_seq 0 = \sum_{i=0}^{n-1} \frac{1}{2^i+b_i} + z_seq n$.
  have h_sum : ∀ n, z_seq 0 = ∑ i ∈ Finset.range n, (1 : ℝ) / (2^i + b i) + z_seq n := by
    exact fun n =>
      Nat.recOn n ( by norm_num ) fun n ih => by
        rw [ Finset.sum_range_succ, hz_seq' ];
        norm_num at *;
        linarith;
  -- By definition of $z_seq$, we have $z_seq 0 = \sum_{i=0}^{\infty} \frac{1}{2^i+b_i}$.
  have h_sum_inf :
      Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (1 : ℝ) / (2^i + b i))
        Filter.atTop (nhds (∑' i, (1 : ℝ) / (2^i + b i))) := by
    exact ( Summable.hasSum <| by
      exact Summable.of_nonneg_of_le
        ( fun i => by positivity )
        ( fun i => by
          simpa using inv_anti₀ ( by positivity ) <| show ( 2 ^ i + b i : ℝ ) ≥ 2 ^ i by
            norm_cast
            linarith [ hb i ] )
        summable_geometric_two ) |>
          HasSum.tendsto_sum_nat;
  simpa using tendsto_nhds_unique
    ( tendsto_const_nhds.congr fun n => by rw [ h_sum n ] )
    ( h_sum_inf.add h_zero )

/-
There exists a bounded sequence of positive integers b_n such that the sum of
1/(2^n + b_n) is rational.
-/
theorem exists_bounded_seq_rational_sum :
  ∃ (b : ℕ → ℕ) (q : ℚ), (∀ n, 1 ≤ b n) ∧ BddAbove (Set.range b) ∧
  ∑' n, (1 : ℝ) / (2^n + b n) = q := by
    -- Compare terms to show `min_tail 0 < max_tail 0`.
    have h_min_lt_max : min_tail 0 < max_tail 0 := by
      apply_rules [ Summable.tsum_lt_tsum ];
      exact fun n => one_div_le_one_div_of_le ( by positivity ) ( by linarith );
      any_goals exact Nat.zero;
      · norm_num;
      · -- Compare with the convergent geometric series.
        have h_comp : ∀ n : ℕ, (1 : ℝ) / (2 ^ n + 4) ≤ 1 / 2 ^ n := by
          exact fun n => by gcongr; norm_num;
        exact Summable.of_nonneg_of_le
          ( fun n => by positivity )
          ( fun n => by simpa using h_comp n )
          ( by simpa using summable_geometric_two );
      · -- Compare with the same geometric series.
        have h_comparison : ∀ n : ℕ, (1 : ℝ) / (2 ^ n + 1) ≤ (1 / 2) ^ n := by
          -- By simplifying, we can see that $1/(2^n + 1) \leq 1/2^n$ for all $n$.
          intro n
          field_simp;
          ring_nf; norm_num [ pow_mul', ← mul_pow ] ;
        exact Summable.of_nonneg_of_le
          ( fun n => by positivity )
          ( fun n => by simpa using h_comparison n )
          ( summable_geometric_two );
    -- Since `SumSet` is an interval containing the endpoint interval, choose rational `q`.
    obtain ⟨q, hq⟩ : ∃ q : ℚ, (q : ℝ) ∈ SumSet := by
      exact Exists.elim ( exists_rat_btwn h_min_lt_max ) fun q hq =>
        ⟨ q, Icc_subset_SumSet ⟨ hq.1.le, hq.2.le ⟩ ⟩;
    cases' hq with b hb; use b, q; aesop;
    exact ⟨ 4, Set.forall_mem_range.mpr fun n => left n |>.2 ⟩

end AristotleLemmas

/--
Is $2^n$ an example of an irrationality sequence? Kovač and Tao proved that it is not [KoTa24]

[KoTa24] Kovač, V. and Tao T., On several irrationality problems for
Ahmes series. arXiv:2406.17593 (2024).
-/
theorem erdos_264.parts.i : ¬IsIrrationalitySequence (2 ^ ·) := by
  -- Apply the theorem to obtain the sequence b_n and the rational q.
  obtain ⟨b, q, hb, hq⟩ := exists_bounded_seq_rational_sum;
  -- Since $b_n \ge 1$, we have $b_n \neq 0$ for all $n$.
  have hb_ne_zero : ∀ n, b n ≠ 0 := by
    exact fun n => ne_of_gt <| hb n;
  unfold IsIrrationalitySequence; aesop;

noncomputable section AristotleLemmas

/-
If two sequences satisfy a specific recurrence and one is bounded while the
other grows doubly exponentially, we get a contradiction.
-/
theorem erdos_264_algebraic_contradiction
    (a b : ℕ → ℕ)
    (ha : ∀ n, a (n + 1) = (a n)^2)
    (ha_grow : Filter.Tendsto a Filter.atTop Filter.atTop)
    (hb_bounded : BddAbove (Set.range b))
    (hb_pos : ∀ n, b n ≠ 0)
    (h_rec : ∀ᶠ n in Filter.atTop, a (n + 1) + b (n + 1) = (a n + b n)^2 - (a n + b n) + 1) :
    False := by
      -- Since $a_n \to \infty$, we have $b_{n+1} \geq a_n + 1$ for sufficiently large $n$.
      have h_b_ge_a : ∃ N, ∀ n ≥ N, b (n + 1) ≥ a n + 1 := by
        aesop;
        refine' ⟨ w, fun n hn ↦ _ ⟩ ;
        specialize h n hn ;
        rw [
          tsub_add_eq_add_tsub ( by
            nlinarith only [ Nat.pos_of_ne_zero ( hb_pos n ) ] )
        ] at h;
        rw [ eq_tsub_iff_add_eq_of_le ] at h <;>
          nlinarith only [
            h,
            Nat.pos_of_ne_zero ( hb_pos n ),
            Nat.pos_of_ne_zero ( hb_pos ( n + 1 ) )
          ];
      rcases h_b_ge_a with ⟨N, hN⟩
      rcases hb_bounded with ⟨B, hB⟩
      have h_event :
          ∀ᶠ n in Filter.atTop, B < a n ∧ N ≤ n :=
        (ha_grow.eventually_gt_atTop B).and (Filter.eventually_ge_atTop N)
      rcases Filter.eventually_atTop.mp h_event with ⟨M, hM⟩
      rcases hM M le_rfl with ⟨haM, hNM⟩
      have hbM : b (M + 1) ≤ B := hB (Set.mem_range_self (M + 1))
      have hlow : a M + 1 ≤ b (M + 1) := hN M hNM
      omega

/-
Algebraic helper lemma: if a sequence $K_n$ defined by a recurrence involving
$x_n$ and $P_n$ is eventually stable and non-zero, then $x_n$ satisfies a
specific quadratic recurrence.
-/
theorem Kn_constant_implies_recurrence
    (x : ℕ → ℤ)
    (P : ℕ → ℤ)
    (K : ℕ → ℤ)
    (Q C : ℤ)
    (N : ℕ)
    (hP0 : P 0 = 1)
    (hP_succ : ∀ n, P (n + 1) = P n * x n)
    (hK_rec : ∀ n, K (n + 1) = x n * K n - Q * P n)
    (hK_const : ∀ n ≥ N, K n = C)
    (hC_ne_zero : C ≠ 0) :
    ∀ n ≥ N, x (n + 1) = (x n)^2 - x n + 1 := by
  intro n hn
  have hn1 : n + 1 ≥ N := Nat.le_trans hn (Nat.le_succ n)
  have hn2 : n + 2 ≥ N := Nat.le_trans hn (by omega)
  have h_sub : C = x n * C - Q * P n := by
    calc
      C = K (n + 1) := (hK_const (n + 1) hn1).symm
      _ = x n * K n - Q * P n := hK_rec n
      _ = x n * C - Q * P n := by rw [hK_const n hn]
  have h_sub2 : C = x (n + 1) * C - Q * (P n * x n) := by
    calc
      C = K (n + 2) := (hK_const (n + 2) hn2).symm
      _ = x (n + 1) * K (n + 1) - Q * P (n + 1) := hK_rec (n + 1)
      _ = x (n + 1) * C - Q * (P n * x n) := by
        rw [hK_const (n + 1) hn1, hP_succ n]
  have h_qp : Q * P n = C * (x n - 1) := by
    nlinarith [h_sub]
  have h_sub2' : C = x (n + 1) * C - (Q * P n) * x n := by
    calc
      C = x (n + 1) * C - Q * (P n * x n) := h_sub2
      _ = x (n + 1) * C - (Q * P n) * x n := by ring_nf
  have h_sub2'' : C = x (n + 1) * C - (C * (x n - 1)) * x n := by
    simpa [h_qp] using h_sub2'
  have h_mul : C * (x (n + 1) - (x n)^2 + x n - 1) = 0 := by
    nlinarith [h_sub2'']
  have h_factor : x (n + 1) - (x n)^2 + x n - 1 = 0 := by
    exact mul_eq_zero.mp h_mul |>.resolve_left hC_ne_zero
  nlinarith

set_option maxHeartbeats 0 in
/-
If $a_n$ grows doubly exponentially and $b_n$ is bounded, then
$(a_n + b_n) \sum_{k=n}^\infty \frac{1}{a_k + b_k} \to 1$.
-/
theorem sum_recip_asymptotic
    (a b : ℕ → ℕ)
    (ha : ∀ n, a (n + 1) = (a n)^2)
    (ha_pos : ∀ n, 1 < a n)
    (hb_bounded : BddAbove (Set.range b))
    (hx_pos : ∀ n, a n + b n ≠ 0) :
    Filter.Tendsto
      (fun n => (a n + b n : ℝ) * ∑' k, (1 : ℝ) / (a (n + k) + b (n + k)))
      Filter.atTop (nhds 1) := by
      -- First, show that $a_{n+1} \geq \frac{1}{2} a_n^2$ for all $n$.
      have h_a_growth : ∀ n, (a (n + 1) : ℝ) ≥ (1 / 2) * (a n)^2 := by
        exact fun n => by rw [ ha ] ; norm_num ; nlinarith;
      -- Bound the tail using the growth of `a` and boundedness of `b`.
      have h_tail_bound :
          ∀ n,
            ∑' k, (1 : ℝ) / ((a (n + k + 1) : ℝ) + (b (n + k + 1) : ℝ)) ≤
              2 / (a n : ℝ) ^ 2 * (1 / (1 - 1 / (a n : ℝ) ^ 2)) := by
        -- Using the inequality from h_a_growth, we can bound each term in the sum.
        have h_term_bound :
            ∀ n k,
              (1 : ℝ) / ((a (n + k + 1) : ℝ) + (b (n + k + 1) : ℝ)) ≤
                2 / (a n : ℝ) ^ (2 ^ (k + 1)) := by
          -- We proceed by induction on $k$.
          intro n k
          induction' k with k ih generalizing n;
          · rw [ div_le_div_iff₀ ] <;> norm_num <;>
              specialize h_a_growth n <;>
              norm_cast at * <;> aesop;
            · nlinarith;
            · exact Or.inl ( sq_pos_of_pos ( pos_of_gt ( ha_pos n ) ) );
            · grind;
          · have := ih ( n + 1 ) ; simp_all +decide [ Nat.add_assoc, pow_succ, pow_mul ] ;
            convert this using 1 <;> ring_nf;
        intro n
        have h_sum_le :
            ∑' k, (1 : ℝ) / ((a (n + k + 1) : ℝ) + (b (n + k + 1) : ℝ)) ≤
              ∑' k, (2 : ℝ) / (a n : ℝ) ^ (2 * (k + 1)) := by
          refine' Summable.tsum_le_tsum ( fun k => le_trans ( h_term_bound n k ) _ ) _ _;
          · gcongr;
            · exact_mod_cast pow_pos ( zero_lt_one.trans ( ha_pos n ) ) _;
            · exact_mod_cast ha_pos n |> Nat.one_le_of_lt;
            · exact Nat.recOn k ( by norm_num ) fun n ihn => by
                norm_num [ Nat.pow_succ' ] at ihn ⊢ ;
                linarith;
          · refine' Summable.of_nonneg_of_le
              ( fun k => by positivity ) ( fun k => h_term_bound n k ) _;
            ring_nf;
            exact Summable.mul_right _
              ( Summable.comp_injective
                ( summable_geometric_of_lt_one ( by positivity )
                  ( inv_lt_one_of_one_lt₀ ( mod_cast ha_pos n ) ) )
                fun x y hxy => by simpa using hxy );
          · ring_nf;
            simpa only [ pow_mul' ] using Summable.mul_right _
              ( Summable.mul_left _
                ( summable_geometric_of_lt_one ( by positivity )
                  ( pow_lt_one₀ ( by positivity )
                    ( inv_lt_one_of_one_lt₀ ( mod_cast ha_pos n ) ) ( by norm_num ) ) ) );
        convert h_sum_le using 1;
        norm_num [ pow_add, pow_mul ];
        norm_num [ div_eq_mul_inv, tsum_mul_left ];
        have := tsum_geometric_of_lt_one ( by positivity )
          ( inv_lt_one_of_one_lt₀
            ( one_lt_pow₀ ( show ( a n : ℝ ) > 1 by exact mod_cast ha_pos n )
              two_ne_zero ) ) ;
        simp_all +decide [ mul_assoc, tsum_mul_left ] ;
      -- Using the tail bound, we can replace the tail sum with the bound from h_tail_bound.
      have h_split_sum :
          ∀ n,
            (a n + b n : ℝ) *
                (∑' k, (1 : ℝ) / ((a (n + k)) + (b (n + k)))) =
              1 + (a n + b n : ℝ) *
                (∑' k, (1 : ℝ) / ((a (n + k + 1)) + (b (n + k + 1)))) := by
        intro n; rw [ Summable.tsum_eq_zero_add ] ; aesop;
        · rw [
            mul_add,
            mul_inv_cancel₀ ( by norm_cast; linarith [ ha_pos n, Nat.zero_le ( b n ) ] )
          ];
          simp +decide [ ← add_assoc, ha ];
        · have h_summable : Summable (fun k => (1 : ℝ) / ((a (n + k)) : ℝ)) := by
            have h_summable : Summable (fun k => (1 : ℝ) / ((a k) : ℝ)) := by
              have h_exp_growth : ∀ k, (a k : ℝ) ≥ 2 ^ (2 ^ k) := by
                intro k; induction k <;> aesop;
                convert pow_le_pow_left₀ ( by positivity ) a_1 2 using 1 ; ring_nf
              exact Summable.of_nonneg_of_le
                ( fun k => by positivity )
                ( fun k => by
                  simpa using inv_anti₀ ( by positivity ) ( h_exp_growth k ) )
                ( by
                  simpa using summable_geometric_two.comp_injective
                    ( Nat.pow_right_injective ( by decide ) ) );
            exact h_summable.comp_injective ( add_right_injective n );
          simp +zetaDelta at *;
          exact Summable.of_nonneg_of_le
            ( fun k =>
              inv_nonneg.2 ( add_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) )
            ( fun k =>
              inv_anti₀ ( Nat.cast_pos.2 ( pos_of_gt ( ha_pos _ ) ) )
                ( le_add_of_nonneg_right ( Nat.cast_nonneg _ ) ) )
            h_summable;
      -- Use the tail bound to show that the product tends to 0.
      have h_tail_zero :
          Filter.Tendsto
            (fun n =>
              (a n + b n : ℝ) *
                (2 / (a n : ℝ) ^ 2 * (1 / (1 - 1 / (a n : ℝ) ^ 2))))
            Filter.atTop (nhds 0) := by
        -- We can factor out $1 / (a n)^2$ and use the fact that $a_n$ grows doubly exponentially.
        have h_factor :
            Filter.Tendsto
              (fun n =>
                (1 : ℝ) / (a n : ℝ) *
                  (2 * (1 + b n / (a n : ℝ)) *
                    (1 / (1 - 1 / (a n : ℝ) ^ 2))))
              Filter.atTop (nhds 0) := by
          -- Since $a_n$ grows doubly exponentially, we have $a_n \to \infty$.
          have h_a_inf : Filter.Tendsto a Filter.atTop Filter.atTop := by
            refine' Filter.tendsto_atTop_mono _ tendsto_natCast_atTop_atTop;
            exact fun n =>
              Nat.recOn n ( by norm_num ) fun n ih => by
                rw [ ha ];
                nlinarith only [ ih, ha_pos n ] ;
          -- Since $b_n$ is bounded, we have $b_n / a_n \to 0$.
          have h_b_div_a_zero :
              Filter.Tendsto (fun n => (b n : ℝ) / (a n : ℝ)) Filter.atTop (nhds 0) := by
            exact squeeze_zero
              ( fun _ => by positivity )
              ( fun n =>
                mul_le_mul_of_nonneg_right
                  ( Nat.cast_le.mpr <| hb_bounded.choose_spec <| Set.mem_range_self _ )
                  ( inv_nonneg.mpr <| Nat.cast_nonneg _ ) )
              ( tendsto_const_nhds.div_atTop <|
                tendsto_natCast_atTop_atTop.comp h_a_inf );
          simpa using Filter.Tendsto.mul
            ( tendsto_inv_atTop_zero.comp ( tendsto_natCast_atTop_atTop.comp h_a_inf ) )
            ( Filter.Tendsto.mul
              ( tendsto_const_nhds.mul ( tendsto_const_nhds.add h_b_div_a_zero ) )
              ( Filter.Tendsto.inv₀
                ( tendsto_const_nhds.sub
                  ( tendsto_inv_atTop_nhds_zero_nat.pow 2 |>
                    Filter.Tendsto.comp <| h_a_inf ) )
                ( by norm_num ) ) );
        convert h_factor using 2 ; ring_nf;
        simpa [ sq, mul_assoc, ne_of_gt ( zero_lt_one.trans ( ha_pos _ ) ) ] using by ring_nf;
      simpa only [ h_split_sum, add_zero ] using tendsto_const_nhds.add
        ( squeeze_zero
          ( fun n => mul_nonneg ( by positivity ) ( tsum_nonneg fun _ => by positivity ) )
          ( fun n => mul_le_mul_of_nonneg_left ( h_tail_bound n ) ( by positivity ) )
          h_tail_zero )

set_option maxHeartbeats 0 in
/-
If $a_n$ grows doubly exponentially and $b_n$ is bounded, then the sequence
$P_n / x_n$ converges to a non-zero limit.
-/
theorem product_ratio_convergence
    (a b : ℕ → ℕ)
    (ha : ∀ n, a (n + 1) = (a n)^2)
    (ha_pos : ∀ n, 1 < a n)
    (hb_bounded : BddAbove (Set.range b))
    (hx_pos : ∀ n, a n + b n ≠ 0) :
    ∃ L : ℝ, L ≠ 0 ∧
      Filter.Tendsto
        (fun n => (∏ k ∈ Finset.range n, (a k + b k : ℝ)) / (a n + b n : ℝ))
        Filter.atTop (nhds L) := by
      -- A product with terms converging summably to 1 has a non-zero limit.
      have h_prod_conv :
          ∃ L : ℝ, L ≠ 0 ∧
            Filter.Tendsto
              (fun n =>
                ∏ k ∈ Finset.range n,
                  (1 + 2 * (b k : ℝ) / (a k : ℝ) +
                    (b k : ℝ)^2 / (a k : ℝ)^2) /
                    (1 + (b (k + 1) : ℝ) / (a (k + 1) : ℝ)))
              Filter.atTop (nhds L) := by
        have h_prod_conv :
            Summable
              (fun k =>
                |1 - (1 + 2 * (b k : ℝ) / (a k : ℝ) +
                  (b k : ℝ)^2 / (a k : ℝ)^2) /
                    (1 + (b (k + 1) : ℝ) / (a (k + 1) : ℝ))|) := by
          -- The quotient errors decay rapidly because `a` grows doubly exponentially.
          have h_decay :
              Summable (fun k => (b k : ℝ) / (a k : ℝ)) ∧
                Summable (fun k => (b (k + 1) : ℝ) / (a (k + 1) : ℝ)) ∧
                  Summable (fun k => (b k : ℝ)^2 / (a k : ℝ)^2) := by
            -- Since $a_k$ grows doubly exponentially, we have $a_k \geq 2^{2^k}$.
            have h_ak_exp : ∀ k, (a k : ℝ) ≥ 2 ^ (2 ^ k) := by
              intro k; norm_cast; induction k <;> aesop;
              convert Nat.pow_le_pow_left a_1 2 using 1 ; ring_nf;
            -- Since $b_k$ is bounded, we have $b_k \leq M$ for some $M$.
            obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ k, (b k : ℝ) ≤ M := by
              exact ⟨ hb_bounded.choose, fun k => mod_cast hb_bounded.choose_spec ⟨ k, rfl ⟩ ⟩;
            -- Compare to summable doubly-exponential tails.
            have h_bound :
                ∀ k,
                  (b k : ℝ) / (a k : ℝ) ≤ M / (2 ^ (2 ^ k) : ℝ) ∧
                    (b k : ℝ)^2 / (a k : ℝ)^2 ≤
                      M^2 / (2 ^ (2 ^ (k + 1)) : ℝ) := by
              intro k; constructor <;> gcongr <;> norm_cast at * <;> aesop;
              · exact le_trans ( Nat.cast_nonneg _ ) ( hM k );
              · simpa only [ ← ha ] using h_ak_exp ( k + 1 );
            refine' ⟨
              Summable.of_nonneg_of_le
                ( fun k => div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) )
                ( fun k => h_bound k |>.1 ) _,
              Summable.of_nonneg_of_le
                ( fun k => div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) )
                ( fun k => h_bound ( k + 1 ) |>.1 ) _,
              Summable.of_nonneg_of_le
                ( fun k => div_nonneg ( sq_nonneg _ ) ( sq_nonneg _ ) )
                ( fun k => h_bound k |>.2 ) _ ⟩;
            · exact Summable.mul_left _ <| by
                simpa using summable_geometric_two.comp_injective <|
                  Nat.pow_right_injective <| by decide;
            · exact Summable.mul_left _ <| by
                simpa using summable_geometric_two.comp_injective <| by aesop_cat;
            · exact Summable.mul_left _ <| by
                simpa using summable_geometric_two.comp_injective <| by
                  intro m n h
                  simpa using h;
          -- Bound each product term by a summable expression.
          have h_bound :
              ∀ k,
                |1 - (1 + 2 * (b k : ℝ) / (a k : ℝ) +
                  (b k : ℝ)^2 / (a k : ℝ)^2) /
                    (1 + (b (k + 1) : ℝ) / (a (k + 1) : ℝ))| ≤
                  |2 * (b k : ℝ) / (a k : ℝ) + (b k : ℝ)^2 / (a k : ℝ)^2 -
                    (b (k + 1) : ℝ) / (a (k + 1) : ℝ)| /
                      (1 + (b (k + 1) : ℝ) / (a (k + 1) : ℝ)) := by
            intro k; rw [ one_sub_div ( by positivity ) ] ; norm_num [ abs_div, abs_mul ] ;
            rw [
              abs_of_nonneg
                ( by positivity :
                  ( 0 : ℝ ) ≤ 1 + ( b ( k + 1 ) : ℝ ) / a ( k + 1 ) )
            ];
            rw [ ← abs_neg ];
            ring_nf;
            norm_num;
          have h_quot_summable :
              Summable
                (fun k =>
                  |2 * (b k : ℝ) / (a k : ℝ) +
                    (b k : ℝ)^2 / (a k : ℝ)^2 -
                      (b (k + 1) : ℝ) / (a (k + 1) : ℝ)|) := by
            exact Summable.abs ( by
              simpa [ mul_div_assoc ] using
                Summable.sub ( Summable.add ( h_decay.1.mul_left 2 ) h_decay.2.2 )
                  h_decay.2.1 );
          refine' Summable.of_nonneg_of_le ( fun k => abs_nonneg _ ) ( fun k => h_bound k ) _;
          refine' .of_nonneg_of_le
            ( fun k =>
              div_nonneg ( abs_nonneg _ )
                ( add_nonneg zero_le_one
                  ( div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ) )
            ( fun k =>
              div_le_self ( abs_nonneg _ ) ( by
                linarith [ show ( 0 : ℝ ) ≤ b ( k + 1 ) / a ( k + 1 ) by positivity ] ) )
            h_quot_summable;
        have h_prod_conv :
            Summable
              (fun k =>
                |(1 + 2 * (b k : ℝ) / (a k : ℝ) +
                  (b k : ℝ)^2 / (a k : ℝ)^2) /
                    (1 + (b (k + 1) : ℝ) / (a (k + 1) : ℝ)) - 1|) := by
          simpa only [ abs_sub_comm ] using h_prod_conv;
        have h_prod_conv :
            Summable
              (fun k =>
                Real.log ((1 + 2 * (b k : ℝ) / (a k : ℝ) +
                  (b k : ℝ)^2 / (a k : ℝ)^2) /
                    (1 + (b (k + 1) : ℝ) / (a (k + 1) : ℝ)))) := by
          have h_log_conv :
              ∀ᶠ k in Filter.atTop,
                |Real.log ((1 + 2 * (b k : ℝ) / (a k : ℝ) +
                  (b k : ℝ)^2 / (a k : ℝ)^2) /
                    (1 + (b (k + 1) : ℝ) / (a (k + 1) : ℝ)))| ≤
                  2 * |(1 + 2 * (b k : ℝ) / (a k : ℝ) +
                    (b k : ℝ)^2 / (a k : ℝ)^2) /
                      (1 + (b (k + 1) : ℝ) / (a (k + 1) : ℝ)) - 1| := by
            have h_log_conv :
                ∀ᶠ k in Filter.atTop,
                  |(1 + 2 * (b k : ℝ) / (a k : ℝ) +
                    (b k : ℝ)^2 / (a k : ℝ)^2) /
                      (1 + (b (k + 1) : ℝ) / (a (k + 1) : ℝ)) - 1| < 1 / 2 := by
              exact h_prod_conv.tendsto_atTop_zero.eventually ( gt_mem_nhds <| by norm_num );
            filter_upwards [ h_log_conv ] with k hk;
            rw [ abs_le ];
            constructor <;>
              cases abs_cases
                ((1 + 2 * ( b k : ℝ ) / ( a k : ℝ ) +
                    ( b k : ℝ ) ^ 2 / ( a k : ℝ ) ^ 2) /
                  (1 + ( b ( k + 1 ) : ℝ ) / ( a ( k + 1 ) : ℝ )) - 1) <;>
              nlinarith [
                Real.log_le_sub_one_of_pos
                  ( show 0 <
                    (1 + 2 * ( b k : ℝ ) / ( a k : ℝ ) +
                        ( b k : ℝ ) ^ 2 / ( a k : ℝ ) ^ 2) /
                      (1 + ( b ( k + 1 ) : ℝ ) / ( a ( k + 1 ) : ℝ )) by
                    positivity ),
                Real.log_inv
                  ((1 + 2 * ( b k : ℝ ) / ( a k : ℝ ) +
                      ( b k : ℝ ) ^ 2 / ( a k : ℝ ) ^ 2) /
                    (1 + ( b ( k + 1 ) : ℝ ) / ( a ( k + 1 ) : ℝ ))),
                Real.log_le_sub_one_of_pos
                  ( show 0 <
                    ((1 + 2 * ( b k : ℝ ) / ( a k : ℝ ) +
                          ( b k : ℝ ) ^ 2 / ( a k : ℝ ) ^ 2) /
                        (1 + ( b ( k + 1 ) : ℝ ) / ( a ( k + 1 ) : ℝ )))⁻¹ by
                    positivity ),
                mul_inv_cancel₀
                  ( show
                    ((1 + 2 * ( b k : ℝ ) / ( a k : ℝ ) +
                          ( b k : ℝ ) ^ 2 / ( a k : ℝ ) ^ 2) /
                        (1 + ( b ( k + 1 ) : ℝ ) / ( a ( k + 1 ) : ℝ ))) ≠ 0 by
                    positivity )
              ];
          -- Apply the comparison test with the summable difference series.
          have h_summable_log :
              Summable
                (fun k =>
                  |Real.log ((1 + 2 * (b k : ℝ) / (a k : ℝ) +
                    (b k : ℝ)^2 / (a k : ℝ)^2) /
                      (1 + (b (k + 1) : ℝ) / (a (k + 1) : ℝ)))|) := by
            rw [ Filter.eventually_atTop ] at h_log_conv;
            obtain ⟨ N, hN ⟩ := h_log_conv;
            rw [ ← summable_nat_add_iff N ];
            exact Summable.of_nonneg_of_le
              ( fun n => abs_nonneg _ )
              ( fun n => hN _ ( by linarith ) )
              ( Summable.mul_left _
                ( h_prod_conv.comp_injective ( add_left_injective N ) ) );
          exact h_summable_log.of_abs;
        have h_prod_conv :
            Filter.Tendsto
              (fun n =>
                Real.exp
                  (∑ k ∈ Finset.range n,
                    Real.log ((1 + 2 * (b k : ℝ) / (a k : ℝ) +
                      (b k : ℝ)^2 / (a k : ℝ)^2) /
                        (1 + (b (k + 1) : ℝ) / (a (k + 1) : ℝ)))))
              Filter.atTop
              (nhds
                (Real.exp
                  (∑' k,
                    Real.log ((1 + 2 * (b k : ℝ) / (a k : ℝ) +
                      (b k : ℝ)^2 / (a k : ℝ)^2) /
                        (1 + (b (k + 1) : ℝ) / (a (k + 1) : ℝ)))))) := by
          exact Real.continuous_exp.continuousAt.tendsto.comp h_prod_conv.hasSum.tendsto_sum_nat;
        exact ⟨ _, ne_of_gt <| Real.exp_pos _, h_prod_conv.congr fun n => by
          rw [
            Real.exp_sum,
            Finset.prod_congr rfl fun _ _ =>
              Real.exp_log <| div_pos ( by positivity ) <| by
                exact add_pos_of_pos_of_nonneg zero_lt_one <|
                  div_nonneg ( Nat.cast_nonneg _ ) <| Nat.cast_nonneg _
          ] ⟩;
      -- Rewrite `x_k^2 / x_{k+1}` using the recurrence for `a`.
      have h_xk_sq_xkp1 :
          ∀ n,
            ((a n + b n : ℝ) ^ 2) / ((a (n + 1) + b (n + 1) : ℝ)) =
              (1 + 2 * (b n : ℝ) / (a n : ℝ) +
                (b n : ℝ)^2 / (a n : ℝ)^2) /
                  (1 + (b (n + 1) : ℝ) / (a (n + 1) : ℝ)) := by
        -- By definition of $a$, we know that $a (n + 1) = a n^2$.
        intro n
        rw [ha n]
        field_simp;
        rw [ div_eq_iff ] <;> norm_num <;> ring_nf;
        · simpa [
            sq, mul_assoc, mul_comm, mul_left_comm,
            ne_of_gt ( show 0 < a n from pos_of_gt ( ha_pos n ) )
          ] using by ring_nf;
        · exact ne_of_gt
            ( add_pos_of_pos_of_nonneg
              ( sq_pos_of_pos ( Nat.cast_pos.mpr ( pos_of_gt ( ha_pos n ) ) ) )
              ( Nat.cast_nonneg _ ) );
      choose L hL using h_prod_conv;
      -- By definition of $P_n$, we can rewrite the product as $P_n / x_n$.
      have h_prod_eq :
          ∀ n,
            (∏ k ∈ Finset.range n, ((a k : ℝ) + (b k : ℝ))) /
                ((a n : ℝ) + (b n : ℝ)) =
              (1 / ((a 0 : ℝ) + (b 0 : ℝ))) *
                (∏ k ∈ Finset.range n,
                  ((a k + b k : ℝ) ^ 2) / ((a (k + 1) + b (k + 1) : ℝ))) := by
        intro n
        induction' n with n ih;
        · norm_num;
        · rw [ Finset.prod_range_succ, Finset.prod_range_succ ];
          rw [ ← mul_assoc, ← ih ];
          simp +decide [
            div_eq_mul_inv, sq, mul_assoc, mul_comm, mul_left_comm,
            ne_of_gt
              ( show 0 < ( a n : ℝ ) + b n from
                mod_cast Nat.pos_of_ne_zero ( hx_pos n ) )
          ];
      use (1 / ((a 0 : ℝ) + (b 0 : ℝ))) * L;
      simp_all +decide [
        ne_of_gt
          ( show 0 < ( a 0 : ℝ ) + b 0 from
            mod_cast Nat.pos_of_ne_zero ( by aesop ) )
      ];
      exact hL.2.const_mul _

end AristotleLemmas

set_option maxHeartbeats 0 in
/--
One example is $2^{2^n}$.
-/
theorem erdos_264.variants.example : IsIrrationalitySequence (fun n ↦ 2 ^ (2 ^ n)) := by
  intro b hb hb₀ hb₁;
  -- Let $x_n = a_n + b_n$.
  set x : ℕ → ℕ := fun n => 2 ^ (2 ^ n) + b n;
  -- Let $S = \sum_{n=0}^\infty \frac{1}{x_n} = P/Q$.
  by_contra h_contra
  obtain ⟨P, Q, hQ_pos, hS⟩ : ∃ P Q : ℕ, Q > 0 ∧ (∑' n, (1 : ℝ) / x n) = P / Q := by
    unfold Irrational at h_contra
    simp +zetaDelta at *
    obtain ⟨y, hy⟩ := h_contra
    have hy_nonneg : 0 ≤ y := by
      exact_mod_cast
        hy.symm ▸ tsum_nonneg fun _ => inv_nonneg.mpr (by positivity)
    exact
      ⟨y.num.natAbs, y.den, Nat.cast_pos.mpr y.pos, by
        simpa [abs_of_nonneg (Rat.num_nonneg.mpr hy_nonneg), Rat.cast_def]
          using hy.symm⟩
  -- Define $P_n = \prod_{k=0}^{n-1} x_k$ and $K_n = Q P_n \sum_{k=n}^\infty \frac{1}{x_k}$.
  set P_n : ℕ → ℕ := fun n => ∏ k ∈ Finset.range n, x k
  set K_n : ℕ → ℤ := fun n => Q * P_n n * (∑' k, (1 : ℝ) / x (n + k)) |> Int.floor;
  -- We show $K_n$ is an integer for all $n$.
  have hK_int : ∀ n, K_n n = Q * P_n n * (∑' k, (1 : ℝ) / x (n + k)) := by
    -- By definition of $K_n$, we know that $K_n$ is an integer.
    intros n
    have hK_int_def : ∃ m : ℤ, Q * P_n n * (∑' k, (1 : ℝ) / x (n + k)) = m := by
      use P * P_n n - Q * ∑ k ∈ Finset.range n, P_n n / x k;
      have h_split_sum :
          ∑' k, (1 : ℝ) / x k =
            (∑ k ∈ Finset.range n, (1 : ℝ) / x k) +
              ∑' k, (1 : ℝ) / x (n + k) := by
        rw [ ← Summable.sum_add_tsum_nat_add ];
        congr! 2;
        · ac_rfl;
        · aesop;
          exact
            Summable.of_nonneg_of_le
              (fun _ => by positivity)
              (fun n => by
                simpa using
                  inv_anti₀ (by positivity)
                    (show (2 ^ 2 ^ n + b n : ℝ) ≥ 2 ^ 2 ^ n by
                      exact le_add_of_nonneg_right (Nat.cast_nonneg _)))
              (by
                simpa using
                  summable_geometric_two.comp_injective
                    (Nat.pow_right_injective (by decide)))
      rw [ eq_div_iff ] at hS <;> norm_cast at * <;> aesop;
      rw [ ← hS ] ; ring_nf;
      norm_num [ Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, Finset.sum_mul ];
      have hsum :
          (∑ i ∈ Finset.range n, (Q : ℝ) *
              (((∏ x ∈ Finset.range n, (b x + 2 ^ 2 ^ x)) : ℕ) : ℝ) *
                (((b i + 2 ^ 2 ^ i : ℕ) : ℝ)⁻¹)) =
            (∑ i ∈ Finset.range n, (Q : ℝ) *
              (((∏ x ∈ Finset.range n, (b x + 2 ^ 2 ^ x)) / (b i + 2 ^ 2 ^ i) : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [ Nat.cast_div ( Finset.dvd_prod_of_mem _ hi ) ( by positivity ) ]
        ring_nf
      have hprod :
          (∏ j ∈ Finset.range n, (↑(b j) + 2 ^ 2 ^ j : ℝ)) =
            (((∏ j ∈ Finset.range n, (b j + 2 ^ 2 ^ j : ℕ)) : ℕ) : ℝ) := by
        norm_num
      rw [ hprod, ← hsum ]
      norm_num
      ring_nf
    aesop;
  -- We show $K_n$ converges to a non-zero limit.
  have hK_limit :
      ∃ L : ℝ, L ≠ 0 ∧
        Filter.Tendsto (fun n => K_n n : ℕ → ℝ) Filter.atTop (nhds L) := by
    -- By `product_ratio_convergence`, $P_n/x_n$ goes to $L \ne 0$.
    obtain ⟨L, hL_ne_zero, hL⟩ :
        ∃ L : ℝ, L ≠ 0 ∧
          Filter.Tendsto (fun n => (P_n n : ℝ) / x n) Filter.atTop (nhds L) := by
      have := product_ratio_convergence ( fun n => 2 ^ 2 ^ n ) b ?_ ?_ ?_ ?_ <;> aesop;
      ring_nf;
    -- By `sum_recip_asymptotic`, the term in parenthesis goes to 1.
    have h_sum_recip_asymptotic :
        Filter.Tendsto
          (fun n => (x n : ℝ) * (∑' k, (1 : ℝ) / x (n + k)))
          Filter.atTop (nhds 1) := by
      convert sum_recip_asymptotic ( fun n => 2 ^ 2 ^ n ) b _ _ _ _ using 1 <;> norm_num;
      · norm_cast;
      · exact fun n => by ring_nf;
      · exact hb;
    have := hL.mul h_sum_recip_asymptotic;
    simp_all +decide [ ← mul_assoc, div_mul_cancel₀ ];
    exact
      ⟨Q * L, mul_ne_zero (Nat.cast_ne_zero.mpr hQ_pos.ne') hL_ne_zero, by
        simpa only [mul_assoc] using this.const_mul _⟩
  -- Since $K_n$ is an integer sequence, it is eventually equal to some
  -- non-zero $C$.
  obtain ⟨C, hC⟩ : ∃ C : ℤ, C ≠ 0 ∧ ∀ᶠ n in Filter.atTop, K_n n = C := by
    -- Since $K_n$ is an integer sequence and converges to $L \neq 0$, it must
    -- eventually be fixed.
    obtain ⟨C, hC⟩ : ∃ C : ℤ, ∀ᶠ n in Filter.atTop, K_n n = C := by
      -- Since $K_n$ is an integer sequence and converges to a non-zero limit,
      -- it must eventually stabilize. This follows from discreteness of ℤ.
      have hK_const :
          ∀ {L : ℝ}, L ≠ 0 →
            Filter.Tendsto (fun n => K_n n : ℕ → ℝ) Filter.atTop (nhds L) →
              ∃ C : ℤ, ∀ᶠ n in Filter.atTop, K_n n = C := by
        intros L hL hK_limit
        have hK_const : ∃ C : ℤ, ∀ᶠ n in Filter.atTop, K_n n = C := by
          have h_discrete : ∀ᶠ n in Filter.atTop, |(K_n n : ℝ) - L| < 1 / 2 := by
            exact hK_limit.eventually ( Metric.ball_mem_nhds _ <| by norm_num )
          obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp h_discrete;
          exact
            ⟨K_n N,
              Filter.eventually_atTop.mpr
                ⟨N, fun n hn =>
                  Int.le_antisymm
                    (Int.le_of_lt_add_one <| by
                      rw [← @Int.cast_lt ℝ]
                      push_cast
                      linarith [
                        abs_lt.mp <| hN n hn,
                        abs_lt.mp <| hN N le_rfl])
                    (Int.le_of_lt_add_one <| by
                      rw [← @Int.cast_lt ℝ]
                      push_cast
                      linarith [
                        abs_lt.mp <| hN n hn,
                        abs_lt.mp <| hN N le_rfl])⟩⟩
        exact hK_const;
      exact hK_const hK_limit.choose_spec.1 hK_limit.choose_spec.2;
    refine' ⟨ C, _, hC ⟩;
    obtain ⟨L, hL_ne_zero, hL_tendsto⟩ := hK_limit
    have := hL_tendsto.congr' (by
      filter_upwards [hC] with n hn
      rw [hn])
    aesop
  -- We apply `Kn_constant_implies_recurrence` to get $x_{n+1} = x_n^2 - x_n + 1$ eventually.
  have hx_recurrence : ∀ᶠ n in Filter.atTop, x (n + 1) = x n ^ 2 - x n + 1 := by
    -- By definition of $K_n$, we know that $K_{n+1} = x_n K_n - Q P_n$.
    have hK_recurrence : ∀ n, K_n (n + 1) = x n * K_n n - Q * P_n n := by
      intro n; rw [ ← @Int.cast_inj ℝ ] ; aesop;
      rw [
        show
            (∑' k : ℕ, (2 ^ 2 ^ (n + k) + (b (n + k) : ℝ))⁻¹) =
              (2 ^ 2 ^ n + (b n : ℝ))⁻¹ +
                (∑' k : ℕ,
                  (2 ^ 2 ^ (n + 1 + k) + (b (n + 1 + k) : ℝ))⁻¹) from
          ?_]
      · have hx_pos : 0 < (2 ^ 2 ^ n + b n : ℝ) := by positivity
        simp +decide [
          Finset.prod_range_succ, mul_add, add_mul, mul_assoc, mul_comm,
          mul_left_comm, ne_of_gt hx_pos]
      · rw [ Summable.tsum_eq_zero_add ];
        · ac_rfl;
        · have h_summable : Summable (fun k => (2 ^ 2 ^ k + (b k : ℝ))⁻¹) := by
            exact
              Summable.of_nonneg_of_le
                (fun _ => by positivity)
                (fun n => by
                  exact
                    inv_anti₀ (by positivity)
                      (show (2 ^ 2 ^ n + (b n : ℝ)) ≥ 2 ^ 2 ^ n by
                        exact le_add_of_nonneg_right (Nat.cast_nonneg _)))
                (by
                  simpa using
                    summable_geometric_two.comp_injective
                      (Nat.pow_right_injective (by decide)))
          exact h_summable.comp_injective ( add_right_injective n );
    -- Since $K_n$ eventually equals $C \ne 0$, we have
    -- $C = x_n C - Q P_n$ for all sufficiently large $n$.
    obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, K_n n = C := by
      exact Filter.eventually_atTop.mp hC.2
    have h_eq : ∀ n ≥ N, C = x n * C - Q * P_n n := by
      exact fun n hn => by
        simpa [hN n hn, hN (n + 1) (Nat.le_succ_of_le hn)] using
          hK_recurrence n
    -- Since $P_n$ grows doubly exponentially, we have $P_{n+1} = x_n P_n$.
    have hP_recurrence : ∀ n, P_n (n + 1) = x n * P_n n := by
      exact fun n => Finset.prod_range_succ_comm _ _;
    -- Since $P_n$ grows doubly exponentially, we have $P_{n+1} = x_n P_n$
    -- and $P_n \neq 0$ for all $n$.
    have hP_ne_zero : ∀ n, P_n n ≠ 0 := by
      exact fun n => Finset.prod_ne_zero_iff.mpr fun i hi => by positivity;
    -- Since $P_n$ grows doubly exponentially, we have $P_{n+1} = x_n P_n$
    -- and $P_n \neq 0$ for all $n$, so the recurrence holds eventually.
    have hx_recurrence_eventually : ∀ᶠ n in Filter.atTop, x (n + 1) = x n ^ 2 - x n + 1 := by
      have h_eq_eventually :
          ∀ᶠ n in Filter.atTop,
            C = x n * C - Q * P_n n ∧
              C = x (n + 1) * C - Q * P_n (n + 1) := by
        exact
          Filter.eventually_atTop.mpr
            ⟨N, fun n hn =>
              ⟨h_eq n hn, h_eq (n + 1) (Nat.le_succ_of_le hn)⟩⟩
      filter_upwards [ h_eq_eventually, Filter.eventually_ge_atTop N ] with n hn hn';
      norm_num [ hP_recurrence ] at hn ⊢;
      exact
        eq_comm.mp (by
          nlinarith [
            show 0 < Q * P_n n from
              mul_pos hQ_pos (Nat.pos_of_ne_zero (hP_ne_zero n)),
            Nat.sub_add_cancel
              (show x n ^ 2 ≥ x n from Nat.le_self_pow (by norm_num) _)])
    exact hx_recurrence_eventually;
  -- Finally, we apply `erdos_264_algebraic_contradiction` to get a contradiction.
  apply erdos_264_algebraic_contradiction
      (fun n => 2 ^ (2 ^ n))
      b
      (fun n => by
        ring_nf)
      (by
        exact
          tendsto_pow_atTop_atTop_of_one_lt one_lt_two |>
            Filter.Tendsto.comp <|
              tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
      (by
        exact hb)
      (by
        aesop)
      (by
        aesop)

#print axioms erdos_264.parts.i
-- 'Erdos264.erdos_264.parts.i' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms erdos_264.variants.example
-- 'Erdos264.erdos_264.variants.example' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos264
