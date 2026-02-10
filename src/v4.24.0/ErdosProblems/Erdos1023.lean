/-

This is a Lean formalization of a solution to Erdős Problem 1023.
https://www.erdosproblems.com/forum/thread/1023

The original proof was found by: Kleitman and Hunter (see above)

[Kl71] Kleitman, Daniel, Collections of subsets containing no two sets
and their union. Proceedings of the LA Meeting AMS (1971), 153-155.


Kleitman's proof was auto-formalized by Aristotle (from Harmonic).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
Formalized the definitions and theorems from the paper "Union-free families and Kleitman's asymptotic bound", including the main result `kleitman_asymptotic` which establishes that the size of a union-free family is asymptotically bounded by the central binomial coefficient. The formalization covers the Erdős-Ko-Rado lemma, Kleitman's chain inequality, the linear programming bound, weak duality, and the construction of the dual feasible solution.
-/

import Mathlib

import ErdosProblems.Erdos447

namespace Erdos1023

set_option linter.mathlibStandardSet false

open scoped Nat
open scoped Classical
open Asymptotics Filter

set_option maxHeartbeats 0

/-
1. An analogue of `UnionFree` where we forbid *any* member of the family from being
   the union of a (nonempty) subfamily of *other* members.

   Concretely: for every `C ∈ F` and every nonempty `G ⊆ F.erase C`,
   we have `⋃₀ G ≠ C`.  (Here `G.sup id` is the union of all sets in `G`.)
-/
def UnionFreeMany {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ C ∈ F, ∀ G ⊆ F.erase C, G.Nonempty → G.sup id ≠ C

/-
2. An analogue of `MaxUnionFree` in this setting (this is the `F(n)` from the statement):
   the maximum size of a family of subsets of `{0,1,...,n-1}` such that no member
   is the union of other members.
-/
noncomputable def MaxUnionFreeMany (n : ℕ) : ℕ := by
  classical
  exact
    ((Finset.univ : Finset (Finset (Finset (Fin n)))).filter UnionFreeMany).sup Finset.card

/-
3. Analogue of `erdos_447` in this setting (stated, not proved).
-/
theorem kleitman_bound_many :
    (fun n => (MaxUnionFreeMany n : ℝ)) ~[Filter.atTop] (fun n => (n.choose (n / 2) : ℝ)) := by
  refine' Asymptotics.IsEquivalent.trans _ _;
  exact fun n => MaxUnionFreeMany n;
  · rfl;
  · refine' Asymptotics.isEquivalent_of_tendsto_one _ _;
    · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn h using absurd h <| Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.choose_pos <| Nat.div_le_self _ _;
    · have h_max_union_free_many : ∀ n, MaxUnionFreeMany n ≤ Erdos447.MaxUnionFree n := by
        intro n;
        have h_max_union_free_many : ∀ F : Finset (Finset (Fin n)), UnionFreeMany F → Erdos447.UnionFree F := by
          intro F hF hC D hD E hE hCDE hCDE';
          contrapose! hF;
          simp_all +decide [ UnionFreeMany ];
          use hE, hCDE, {hC, hD};
          simp_all +decide [ Finset.subset_iff ];
        exact Finset.sup_le fun F hF => Finset.le_sup ( f := Finset.card ) ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h_max_union_free_many F <| Finset.mem_filter.mp hF |>.2 ⟩ );
      have h_max_union_free_many : ∀ n, MaxUnionFreeMany n ≥ (Nat.choose n (n / 2) : ℝ) := by
        intro n
        have h_max_union_free_many : (Nat.choose n (n / 2) : ℝ) ≤ MaxUnionFreeMany n := by
          have h_family : ∃ F : Finset (Finset (Fin n)), F.card = Nat.choose n (n / 2) ∧ UnionFreeMany F := by
            use Finset.univ.filter (fun s => s.card = n / 2);
            constructor;
            · rw [ show ( Finset.univ.filter fun s : Finset ( Fin n ) => Finset.card s = n / 2 ) = Finset.powersetCard ( n / 2 ) ( Finset.univ : Finset ( Fin n ) ) by ext; simp +decide [ Finset.mem_powersetCard ], Finset.card_powersetCard, Finset.card_fin ];
            · intro C hC G hG hG_nonempty hG_union
              have h_card : G.sup id = C := by
                exact hG_union;
              have h_card : ∀ s ∈ G, s ⊆ C := by
                exact fun s hs => h_card ▸ Finset.le_sup ( f := id ) hs;
              have h_card : ∀ s ∈ G, s = C := by
                intros s hs
                have h_card_eq : s.card = C.card := by
                  have := hG hs; aesop;
                exact Finset.eq_of_subset_of_card_le ( h_card s hs ) ( by linarith );
              exact absurd ( hG ( hG_nonempty.choose_spec ) ) ( by simp +decide [ h_card _ hG_nonempty.choose_spec ] )
          obtain ⟨ F, hF₁, hF₂ ⟩ := h_family; exact_mod_cast hF₁ ▸ Finset.le_sup ( f := Finset.card ) ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hF₂ ⟩ ) ;
        exact_mod_cast h_max_union_free_many;
      have h_max_union_free_many : Filter.Tendsto (fun n => (Erdos447.MaxUnionFree n : ℝ) / (Nat.choose n (n / 2) : ℝ)) Filter.atTop (nhds 1) := by
        have := Erdos447.erdos_447;
        rw [ Asymptotics.IsEquivalent ] at this;
        rw [ Asymptotics.isLittleO_iff_tendsto' ] at this;
        · simpa using this.add_const 1 |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Pi.sub_apply, sub_div, div_self <| Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.choose_pos <| Nat.div_le_self _ _ ] ; ring );
        · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn h using absurd h <| Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.choose_pos <| Nat.div_le_self _ _;
      refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_max_union_free_many _ _;
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ Pi.div_apply ] ; exact one_le_div ( Nat.cast_pos.mpr <| Nat.choose_pos <| Nat.div_le_self _ _ ) |>.2 <| by aesop;
      · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using div_le_div_of_nonneg_right ( by aesop ) ( Nat.cast_nonneg _ )

/-
4. State `F(n) ∼ c * 2^n / n^{1/2}` for the specific constant `c = sqrt(2/pi)`.

   We write `n^{1/2}` as `Real.sqrt (n : ℝ)` in Lean.
-/
theorem many_sqrt_two_div_pi :
    (fun n => (MaxUnionFreeMany n : ℝ)) ~[Filter.atTop]
      (fun n =>
        (Real.sqrt ((2 : ℝ) / Real.pi)) * ((2 : ℝ) ^ n) / Real.sqrt (n : ℝ)) := by
  have := kleitman_bound_many ; norm_num at this;
  have h_stirling : (fun n => (Nat.choose n (n / 2) : ℝ)) ~[Filter.atTop] (fun n => 2 ^ n / Real.sqrt (Real.pi * n / 2)) := by
    have h_stirling : Filter.Tendsto (fun n : ℕ => (Nat.choose n (n / 2) : ℝ) * Real.sqrt (Real.pi * n / 2) / 2 ^ n) Filter.atTop (nhds 1) := by
      have h_stirling : Filter.Tendsto (fun n : ℕ => (Nat.choose (2 * n) n : ℝ) * Real.sqrt (Real.pi * n) / 2 ^ (2 * n)) Filter.atTop (nhds 1) := by
        have h_stirling : Filter.Tendsto (fun n : ℕ => (Nat.factorial (2 * n) : ℝ) / (2 ^ (2 * n) * (Nat.factorial n) ^ 2) * Real.sqrt (Real.pi * n)) Filter.atTop (nhds 1) := by
          have h_stirling_approx : ∀ n : ℕ, (Nat.factorial (2 * n) : ℝ) / (2 ^ (2 * n) * (Nat.factorial n) ^ 2) = (∏ k ∈ Finset.range n, (2 * k + 1) / (2 * k + 2 : ℝ)) := by
            intro n
            induction' n with n ih;
            · norm_num;
            · rw [ Finset.prod_range_succ, ← ih ];
              field_simp [Nat.factorial_succ, Nat.mul_succ]
              ring_nf;
              rw [ show 2 + n * 2 = n * 2 + 2 by ring, show 1 + n = n + 1 by ring ] ; norm_num [ Nat.factorial_succ ] ; ring;
          have h_wallis : Filter.Tendsto (fun n : ℕ => (∏ k ∈ Finset.range n, (2 * k + 1) / (2 * k + 2 : ℝ)) ^ 2 * (2 * n + 1)) Filter.atTop (nhds (2 / Real.pi)) := by
            have h_wallis : Filter.Tendsto (fun n : ℕ => (∏ k ∈ Finset.range n, (2 * k + 1) / (2 * k + 2 : ℝ)) ^ 2 * (2 * n + 1)) Filter.atTop (nhds (2 / Real.pi)) := by
              have h_wallis_prod : Filter.Tendsto (fun n : ℕ => (∏ k ∈ Finset.range n, (2 * k + 2) ^ 2 / ((2 * k + 1) * (2 * k + 3) : ℝ))) Filter.atTop (nhds (Real.pi / 2)) := by
                convert Real.tendsto_prod_pi_div_two using 1;
                exact funext fun n => Finset.prod_congr rfl fun _ _ => by rw [ div_mul_div_comm ] ; ring;
              convert h_wallis_prod.inv₀ ( by positivity ) using 2 ; norm_num [ Finset.prod_pow ];
              · field_simp;
                induction ‹_› <;> norm_num [ Finset.prod_range_succ ] at *;
                rename_i n ih; rw [ ← ih ] ; ring;
              · norm_num [ div_eq_mul_inv ];
            convert h_wallis using 1;
          have h_sqrt : Filter.Tendsto (fun n : ℕ => Real.sqrt ((∏ k ∈ Finset.range n, (2 * k + 1) / (2 * k + 2 : ℝ)) ^ 2 * (2 * n + 1)) * Real.sqrt (Real.pi / (2 + 1 / (n : ℝ)))) Filter.atTop (nhds 1) := by
            convert Filter.Tendsto.mul ( Filter.Tendsto.sqrt h_wallis ) ( Filter.Tendsto.sqrt ( tendsto_const_nhds.div ( tendsto_const_nhds.add ( tendsto_one_div_atTop_nhds_zero_nat ) ) _ ) ) using 2 <;> norm_num;
            rw [ div_self <| ne_of_gt <| Real.sqrt_pos.mpr <| Real.pi_pos ];
          refine h_sqrt.congr' ?_;
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn;
          rw [ h_stirling_approx n ];
          field_simp [mul_comm, mul_assoc, mul_left_comm];
          rw [ ← Real.sqrt_mul ( by exact mul_nonneg ( sq_nonneg _ ) ( by positivity ) ) ];
          rw [ show ( ∏ x ∈ Finset.range n, ( 2 * ( x : ℝ ) + 1 ) / ( 2 * ( x + 1 ) ) ) ^ 2 * ( 2 * n + 1 ) * ( n * Real.pi / ( 2 * n + 1 ) ) = ( ( ∏ x ∈ Finset.range n, ( 2 * ( x : ℝ ) + 1 ) / ( 2 * ( x + 1 ) ) ) ^ 2 ) * ( n * Real.pi ) by rw [ mul_assoc, mul_div_cancel₀ _ ( by positivity ) ] ] ; rw [ Real.sqrt_mul ( sq_nonneg _ ), Real.sqrt_sq ( Finset.prod_nonneg fun _ _ => by positivity ) ];
        convert h_stirling using 2 ; norm_num [ two_mul, Nat.cast_choose ] ; ring;
      have h_stirling : Filter.Tendsto (fun n : ℕ => (Nat.choose (2 * n + 1) (n) : ℝ) * Real.sqrt (Real.pi * (2 * n + 1) / 2) / 2 ^ (2 * n + 1)) Filter.atTop (nhds 1) := by
        have h_stirling : Filter.Tendsto (fun n : ℕ => (Nat.choose (2 * n + 1) n : ℝ) / (2 * Nat.choose (2 * n) n)) Filter.atTop (nhds 1) := by
          have h_stirling : ∀ n : ℕ, (Nat.choose (2 * n + 1) n : ℝ) = (Nat.choose (2 * n) n : ℝ) * (2 * n + 1) / (n + 1) := by
            intro n; rw [ eq_div_iff ] <;> norm_cast ; induction' n with n ih <;> norm_num [ Nat.choose ] at *;
            have := Nat.succ_mul_choose_eq ( 2 * ( n + 1 ) ) n; have := Nat.succ_mul_choose_eq ( 2 * ( n + 1 ) ) ( n + 1 ) ; norm_num [ Nat.mul_succ, Nat.choose_succ_succ ] at * ; linarith;
          -- Simplify the expression inside the limit.
          suffices h_simplify : Filter.Tendsto (fun n : ℕ => (2 * n + 1 : ℝ) / (2 * (n + 1))) Filter.atTop (nhds 1) by
            convert h_simplify using 2 ; rw [ h_stirling ] ; ring_nf;
            -- Combine and simplify the terms on the left-hand side.
            field_simp
            ring_nf;
            exact mul_inv_cancel₀ ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.choose_pos <| by linarith );
          rw [ Metric.tendsto_nhds ] ; norm_num;
          exact fun ε hε => ⟨ Nat.ceil ( ε⁻¹ * 2 ), fun n hn => abs_lt.mpr ⟨ by nlinarith [ Nat.ceil_le.mp hn, inv_mul_cancel₀ hε.ne', mul_div_cancel₀ ( ( 2 * n + 1 : ℝ ) ) ( by positivity : ( 2 * ( n + 1 ) : ℝ ) ≠ 0 ) ], by nlinarith [ Nat.ceil_le.mp hn, inv_mul_cancel₀ hε.ne', mul_div_cancel₀ ( ( 2 * n + 1 : ℝ ) ) ( by positivity : ( 2 * ( n + 1 ) : ℝ ) ≠ 0 ) ] ⟩ ⟩;
        have h_stirling : Filter.Tendsto (fun n : ℕ => (Nat.choose (2 * n + 1) n : ℝ) / (2 * Nat.choose (2 * n) n) * (Real.sqrt (Real.pi * (2 * n + 1) / 2) / Real.sqrt (Real.pi * n)) * (Nat.choose (2 * n) n * Real.sqrt (Real.pi * n) / 2 ^ (2 * n))) Filter.atTop (nhds 1) := by
          have h_stirling : Filter.Tendsto (fun n : ℕ => (Real.sqrt (Real.pi * (2 * n + 1) / 2) / Real.sqrt (Real.pi * n))) Filter.atTop (nhds 1) := by
            have h_stirling : Filter.Tendsto (fun n : ℕ => Real.sqrt ((2 * n + 1) / (2 * n))) Filter.atTop (nhds 1) := by
              ring_nf;
              exact le_trans ( Filter.Tendsto.sqrt ( Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with n hn; aesop ) ) ( tendsto_inverse_atTop_nhds_zero_nat.mul tendsto_const_nhds ) ) ) ( by norm_num );
            convert h_stirling using 2 ; rw [ ← Real.sqrt_div ( by positivity ) ] ; ring_nf ; norm_num [ Real.pi_pos.ne' ];
            norm_num [ mul_assoc, mul_comm Real.pi _, Real.pi_ne_zero ];
          simpa using Filter.Tendsto.mul ( Filter.Tendsto.mul ‹Filter.Tendsto ( fun n : ℕ => ( Nat.choose ( 2 * n + 1 ) n : ℝ ) / ( 2 * Nat.choose ( 2 * n ) n ) ) Filter.atTop ( nhds 1 ) › h_stirling ) ‹Filter.Tendsto ( fun n : ℕ => ( Nat.choose ( 2 * n ) n : ℝ ) * Real.sqrt ( Real.pi * n ) / 2 ^ ( 2 * n ) ) Filter.atTop ( nhds 1 ) ›;
        refine h_stirling.congr' ?_;
        filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn;
        field_simp [mul_comm, mul_assoc, mul_left_comm];
        rw [ div_eq_iff ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.choose_pos <| by linarith ) ] ; ring;
      rw [ Filter.tendsto_atTop' ] at *;
      intro s hs; rcases ‹∀ s ∈ nhds 1, ∃ a, ∀ b ≥ a, ( Nat.choose ( 2 * b ) b : ℝ ) * Real.sqrt ( Real.pi * b ) / 2 ^ ( 2 * b ) ∈ s› s hs with ⟨ a, ha ⟩ ; rcases h_stirling s hs with ⟨ b, hb ⟩ ; refine' ⟨ 2 * a + 2 * b, fun n hn => _ ⟩ ; rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> norm_num at *;
      · convert ha k ( by linarith ) using 1 ; ring_nf;
        norm_num [ mul_assoc, mul_comm, mul_left_comm ];
      · convert hb k ( by linarith ) using 1 ; norm_num [ Nat.add_div ];
    rw [ Asymptotics.isEquivalent_iff_exists_eq_mul ];
    refine' ⟨ _, h_stirling, _ ⟩;
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ Pi.mul_apply, div_mul_div_cancel₀ ( by positivity ), mul_div_cancel_right₀ _ ( by positivity ) ] ;
  convert this.trans h_stirling using 2 ; norm_num ; ring_nf;
  norm_num ; ring

/-
5. Existential version: there exists a constant `c > 0` such that
   `F(n) ∼ c * 2^n / n^{1/2}`.
-/
theorem erdos_1023 :
    ∃ c : ℝ, 0 < c ∧
      (fun n => (MaxUnionFreeMany n : ℝ)) ~[Filter.atTop]
        (fun n => c * ((2 : ℝ) ^ n) / Real.sqrt (n : ℝ)) := by
  -- By definition of $c$, we know that $c = \sqrt{2 / \pi}$.
  use Real.sqrt (2 / Real.pi);
  convert many_sqrt_two_div_pi using 1 ; norm_num [ mul_div_assoc ];
  exact fun _ => Real.pi_pos

#print axioms erdos_1023
-- 'Erdos1023.erdos_1023' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1023
