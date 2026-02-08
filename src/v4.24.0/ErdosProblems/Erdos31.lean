/-

This is a Lean formalization of a solution to Erdős Problem 31.
https://www.erdosproblems.com/31

The original human proof was found by: G. G. Lorentz

G. G. Lorentz, On a problem of additive number theory. Proc. Amer. Math. Soc. 5 (1954), 838-841.

Wouter van Doorn posted a nice explanation of this proof at
https://www.erdosproblems.com/forum/thread/31#post-1779

ChatGPT 5.1 Pro from OpenAI explained this proof in more detail,
resulting in a 9-page LaTeX file.

The LaTeX file output from the previous step was auto-formalized into
Lean by Aristotle from Harmonic.

The final theorem statement was written by hand by Boris Alexeev, but
using primitives from the Formal Conjectures project organized by
Google DeepMind.

The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/

import Mathlib

namespace Erdos31

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

#check Real.log_zero
#check div_zero

noncomputable def counting_function (A : Set ℕ) (x : ℝ) : ℕ :=
  ((Finset.Icc 1 (Nat.floor x)).filter (· ∈ A)).card

def has_density_zero (B : Set ℕ) : Prop :=
  Filter.Tendsto (fun n : ℕ ↦ (counting_function B n : ℝ) / n) Filter.atTop (nhds 0)

#check harmonic
#check harmonic_le_one_add_log

open scoped Pointwise

lemma double_counting_bound {A : Set ℕ} [DecidablePred (· ∈ A)] {J U : Finset ℕ} {s k : ℕ}
    (hs : ∀ b ∈ J, (U.filter (fun u ↦ u ∈ A + ({b} : Set ℕ))).card ≤ s)
    (hk : ∀ u ∈ U, k ≤ (Finset.filter (fun a ↦ a ∈ A ∧ u - a ∈ J) (Finset.range (u + 1))).card) :
    U.card * k ≤ J.card * s := by
  -- By summing the inequalities from hk over all u in U, we get that the total number of pairs (u, a) is at least U.card * k.
  have h_sum : ∑ u ∈ U, (Finset.filter (fun a => a ∈ A ∧ u - a ∈ J) (Finset.range (u + 1))).card ≥ U.card * k := by
    exact le_trans ( by norm_num ) ( Finset.sum_le_sum hk );
  -- By interchanging the order of summation, we can rewrite the left-hand side.
  have h_interchange : ∑ u ∈ U, (Finset.filter (fun a => a ∈ A ∧ u - a ∈ J) (Finset.range (u + 1))).card = ∑ b ∈ J, ∑ u ∈ U, (if u ∈ A + {b} then 1 else 0) := by
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
    refine' Finset.card_bij ( fun y hy => x - y ) _ _ _ <;> aesop;
    · exact ⟨ a_1, left_1, Nat.add_sub_of_le ( Nat.le_of_lt_succ left ) ⟩;
    · -- Since $x - a₁ = x - a₂$, we can subtract $x$ from both sides to get $-a₁ = -a₂$, which simplifies to $a₁ = a₂$.
      linarith [Nat.sub_add_cancel (by linarith : a₁ ≤ x), Nat.sub_add_cancel (by linarith : a₂ ≤ x)];
    · exact ⟨ w, ⟨ by linarith, left_1, by simpa using left ⟩, by simp +decide ⟩;
  aesop;
  exact h_sum.trans ( le_trans ( Finset.sum_le_sum hs ) ( by norm_num ) )


lemma greedy_sum_bound {x : ℕ → ℕ} {m K : ℕ} {C : ℝ}
    (h_mono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ m → x j ≤ x i)
    (h_pos : ∀ i, 1 ≤ i → i ≤ m → 1 ≤ x i)
    (h_bound : ∀ s, 1 ≤ s → s ≤ K → (∑ j ∈ (Finset.Icc 1 m).filter (fun j ↦ x j ≤ s), (x j : ℝ)) ≤ C * s)
    (hK : 1 ≤ K) :
    (m : ℝ) ≤ 2 * (∑ j ∈ Finset.Icc 1 m, (x j : ℝ)) / K + C * Real.log K := by
  -- For $j \in S_{>K}$, $x_j \ge K+1 > K$.
  let S_gt_K := Finset.filter (fun j => K < x j) (Finset.Icc 1 m)
  have hS_gt_K_bound : (∑ j ∈ S_gt_K, (x j : ℝ)) ≥ S_gt_K.card * (K + 1 : ℝ) := by
    -- Since each term in the sum is at least $K + 1$, the sum is at least the number of terms times $(K + 1)$.
    have h_sum_ge_card : ∑ j ∈ S_gt_K, (x j : ℝ) ≥ ∑ j ∈ S_gt_K, (K + 1 : ℝ) := by
      exact Finset.sum_le_sum fun i hi => mod_cast Finset.mem_filter.mp hi |>.2;
    -- The sum of a constant function over a finite set is the constant times the cardinality of the set.
    simp [Finset.sum_const, nsmul_one] at h_sum_ge_card;
    linarith;
  -- For $S_{\le K}$, let $K_s = |\{j \in S \mid x_j = s\}|$.
  let K_s := fun s => (Finset.filter (fun j => x j = s) (Finset.Icc 1 m)).card
  have hK_s_card : (Finset.card (Finset.filter (fun j => x j ≤ K) (Finset.Icc 1 m))) = ∑ s ∈ Finset.Icc 1 K, K_s s := by
    rw [ ← Finset.card_biUnion ];
    · congr with j ; aesop;
    · exact fun a ha b hb hab => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hab <| by aesop;
  -- Using $R_s \le C s$, the sum is bounded by $C \sum_{s=1}^{K-1} \frac{1}{s+1} + \frac{R_K}{K}$.
  have h_sum_bound : ∑ s ∈ Finset.Icc 1 K, K_s s ≤ C * (∑ s ∈ Finset.Icc 1 (K-1), (1 / (s + 1 : ℝ))) + (∑ j ∈ Finset.filter (fun j => x j ≤ K) (Finset.Icc 1 m), (x j : ℝ)) / K := by
    -- Using $R_s \le C s$, we have $K_s = (R_s - R_{s-1}) / s$.
    have hK_s_bound : ∀ s ∈ Finset.Icc 1 K, K_s s ≤ (∑ j ∈ Finset.filter (fun j => x j ≤ s) (Finset.Icc 1 m), (x j : ℝ)) / s - (∑ j ∈ Finset.filter (fun j => x j ≤ s - 1) (Finset.Icc 1 m), (x j : ℝ)) / s := by
      intros s hs
      have hK_s_eq : ∑ j ∈ Finset.filter (fun j => x j ≤ s) (Finset.Icc 1 m), (x j : ℝ) - ∑ j ∈ Finset.filter (fun j => x j ≤ s - 1) (Finset.Icc 1 m), (x j : ℝ) = ∑ j ∈ Finset.filter (fun j => x j = s) (Finset.Icc 1 m), (x j : ℝ) := by
        rw [ sub_eq_iff_eq_add', ← Finset.sum_union ];
        · rcongr j ; aesop <;> omega;
        · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith [ Nat.sub_add_cancel ( Finset.mem_Icc.mp hs |>.1 ) ] ;
      rw [ ← sub_div, le_div_iff₀ ] <;> aesop;
      rw [ Finset.sum_congr rfl fun i hi => show ( x i : ℝ ) = s by aesop ] ; norm_num;
    -- Summing this:
    have h_sum_bound : ∑ s ∈ Finset.Icc 1 K, K_s s ≤ (∑ s ∈ Finset.Icc 1 (K-1), (∑ j ∈ Finset.filter (fun j => x j ≤ s) (Finset.Icc 1 m), (x j : ℝ)) / (s : ℝ) - ∑ s ∈ Finset.Icc 1 (K-1), (∑ j ∈ Finset.filter (fun j => x j ≤ s) (Finset.Icc 1 m), (x j : ℝ)) / (s + 1 : ℝ)) + (∑ j ∈ Finset.filter (fun j => x j ≤ K) (Finset.Icc 1 m), (x j : ℝ)) / K := by
      simp +zetaDelta at *;
      convert Finset.sum_le_sum fun i hi => hK_s_bound i ( Finset.mem_Icc.mp hi |>.1 ) ( Finset.mem_Icc.mp hi |>.2 ) using 1;
      erw [ Finset.sum_Ico_eq_sub _ _, Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ];
      erw [ Finset.sum_Ico_eq_sub _ _, Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ];
      cases K <;> norm_num [ Finset.sum_range_succ' ] at *;
      have := Finset.sum_range_sub ( fun i => ( ∑ j ∈ Finset.filter ( fun j => x j ≤ i + 1 ) ( Finset.Icc 1 m ), ( x j : ℝ ) ) / ( i + 1 : ℝ ) ) ‹_›; aesop;
      rw [ show ( Finset.filter ( fun j => x j = 0 ) ( Finset.Icc 1 m ) ) = ∅ from Finset.eq_empty_of_forall_not_mem fun j hj => by linarith [ h_pos j ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hj |>.1 ) |>.1 ) ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hj |>.1 ) |>.2 ), Finset.mem_filter.mp hj |>.2 ] ] ; norm_num ; linarith;
    -- Using $R_s \le C s$, we have $\sum_{s=1}^{K-1} \frac{R_s}{s} - \sum_{s=1}^{K-1} \frac{R_s}{s+1} \le C \sum_{s=1}^{K-1} \frac{1}{s+1}$.
    have h_sum_bound' : ∑ s ∈ Finset.Icc 1 (K-1), (∑ j ∈ Finset.filter (fun j => x j ≤ s) (Finset.Icc 1 m), (x j : ℝ)) / (s : ℝ) - ∑ s ∈ Finset.Icc 1 (K-1), (∑ j ∈ Finset.filter (fun j => x j ≤ s) (Finset.Icc 1 m), (x j : ℝ)) / (s + 1 : ℝ) ≤ C * ∑ s ∈ Finset.Icc 1 (K-1), (1 / (s + 1 : ℝ)) := by
      rw [ Finset.mul_sum _ _ _ ];
      rw [ ← Finset.sum_sub_distrib ];
      gcongr ; aesop;
      have := h_bound i left ( right.trans ( Nat.pred_le _ ) );
      rw [ div_le_iff₀ ] <;> nlinarith [ show ( i : ℝ ) ≥ 1 by norm_cast, inv_mul_cancel_left₀ ( by positivity : ( i : ℝ ) + 1 ≠ 0 ) C, div_mul_cancel₀ ( ∑ j ∈ Finset.filter ( fun j => x j ≤ i ) ( Finset.Icc 1 m ), ( x j : ℝ ) ) ( by positivity : ( i : ℝ ) + 1 ≠ 0 ) ];
    linarith;
  -- Using $\sum_{s=1}^{K-1} \frac{1}{s+1} \le \log K$, we get:
  have h_log_bound : ∑ s ∈ Finset.Icc 1 (K-1), (1 / (s + 1 : ℝ)) ≤ Real.log K := by
    have h_log_bound : ∀ n : ℕ, 1 ≤ n → ∑ s ∈ Finset.Icc 1 n, (1 / (s + 1 : ℝ)) ≤ Real.log (n + 1) := by
      intro n hn; induction hn <;> aesop;
      · have := Real.log_two_gt_d9 ; norm_num at * ; linarith;
      · norm_num [ Finset.sum_Ioc_succ_top, Nat.Icc_succ_left ] at *;
        refine le_trans ( add_le_add_right a_ih _ ) ?_;
        rw [ Real.le_log_iff_exp_le ( by positivity ) ];
        rw [ Real.exp_add, Real.exp_log ( by positivity ) ];
        nlinarith [ Real.exp_pos ( ( m_1 + 1 + 1 : ℝ ) ⁻¹ ), Real.exp_neg ( ( m_1 + 1 + 1 : ℝ ) ⁻¹ ), mul_inv_cancel₀ ( by positivity : ( m_1 + 1 + 1 : ℝ ) ≠ 0 ), mul_inv_cancel₀ ( by positivity : Real.exp ( ( m_1 + 1 + 1 : ℝ ) ⁻¹ ) ≠ 0 ), Real.add_one_le_exp ( ( m_1 + 1 + 1 : ℝ ) ⁻¹ ), Real.add_one_le_exp ( - ( ( m_1 + 1 + 1 : ℝ ) ⁻¹ ) ) ];
    rcases K with ( _ | _ | K ) <;> aesop;
    exact_mod_cast h_log_bound _ le_add_self;
  -- Combining the bounds for $S_{>K}$ and $S_{\le K}$, we get:
  have h_combined_bound : (Finset.card (Finset.Icc 1 m)) ≤ (Finset.card S_gt_K) + (C * Real.log K) + (∑ j ∈ Finset.filter (fun j => x j ≤ K) (Finset.Icc 1 m), (x j : ℝ)) / K := by
    have h_combined_bound : (Finset.card (Finset.Icc 1 m)) = (Finset.card S_gt_K) + (Finset.card (Finset.filter (fun j => x j ≤ K) (Finset.Icc 1 m))) := by
      rw [ ← Finset.card_union_of_disjoint ( Finset.disjoint_filter.mpr fun _ _ _ => by linarith ), Finset.filter_union_right ] ; aesop;
      rw [ Finset.filter_true_of_mem fun i hi => lt_or_le _ _, Nat.card_Icc ] ; norm_num;
    simp_all +decide [ add_assoc ];
    exact le_trans h_sum_bound <| add_le_add ( mul_le_mul_of_nonneg_left h_log_bound <| show 0 ≤ C by specialize h_bound 1 le_rfl hK; norm_num at h_bound; linarith [ show ( 0 :ℝ ) ≤ ∑ j ∈ Finset.filter ( fun j => x j ≤ 1 ) ( Finset.Icc 1 ( S_gt_K.card + ∑ s ∈ Finset.Icc 1 K, K_s s ) ), ( x j :ℝ ) from Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ ] ) le_rfl;
  -- Using the bound for $S_{>K}$, we get:
  have h_final_bound : (Finset.card S_gt_K) ≤ (∑ j ∈ Finset.filter (fun j => x j > K) (Finset.Icc 1 m), (x j : ℝ)) / K := by
    rw [ le_div_iff₀ ] <;> first | positivity | aesop;
    exact le_trans ( mul_le_mul_of_nonneg_left ( by norm_num ) ( Nat.cast_nonneg _ ) ) hS_gt_K_bound;
  -- Using the bound for $S_{\le K}$, we get:
  have h_final_bound' : (∑ j ∈ Finset.filter (fun j => x j ≤ K) (Finset.Icc 1 m), (x j : ℝ)) / K ≤ (∑ j ∈ Finset.Icc 1 m, (x j : ℝ)) / K := by
    gcongr ; aesop;
  norm_num [ two_mul, add_div ] at *;
  linarith [ show ( ∑ j ∈ Finset.filter ( fun j => K < x j ) ( Finset.Icc 1 m ), ( x j : ℝ ) ) / K ≤ ( ∑ j ∈ Finset.Icc 1 m, ( x j : ℝ ) ) / K from by exact div_le_div_of_nonneg_right ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ]


lemma sum_by_parts_harmonic {K : ℕ} {f : ℕ → ℝ} (h0 : f 0 = 0) :
    ∑ s ∈ Finset.Icc 1 K, (f s - f (s - 1)) / s = f K / K + ∑ s ∈ Finset.Icc 1 (K - 1), f s * (1 / s - 1 / (s + 1)) := by
  induction K <;> aesop;
  cases n <;> norm_num [ Finset.sum_Ioc_succ_top, Nat.Icc_succ_left ] at * ; linarith;
  linear_combination a


open scoped Pointwise

lemma greedy_step_bound {I J : Finset ℕ} {A : Set ℕ} [DecidablePred (· ∈ A)] {k s : ℕ}
    (h_cover : ∀ u ∈ I, k ≤ (J.filter (fun b ↦ u ∈ A + {b})).card)
    (h_max : ∀ b ∈ J, (I.filter (fun u ↦ u ∈ A + {b})).card ≤ s) :
    I.card * k ≤ J.card * s := by
  -- By summing h_cover over all u in I, we get I.card * k ≤ sum_{u in I} (number of b in J such that u is in A + {b}).
  have h_sum_cover : I.card * k ≤ ∑ u ∈ I, (Finset.filter (fun b => u ∈ A + {b}) J).card := by
    -- Apply the sum_le_sum function to the inequality h_cover.
    apply Finset.card_nsmul_le_sum;
    assumption;
  -- By commutativity of summation, we can rewrite the sum as ∑ b in J, (Finset.filter (fun u => u ∈ A + {b}) I).card.
  have h_sum_comm : ∑ u ∈ I, (Finset.filter (fun b => u ∈ A + {b}) J).card = ∑ b ∈ J, (Finset.filter (fun u => u ∈ A + {b}) I).card := by
    simp +decide only [Finset.card_filter];
    rw [ Finset.sum_comm ];
  exact h_sum_cover.trans ( h_sum_comm.le.trans ( Finset.sum_le_card_nsmul _ _ _ fun x hx => h_max x hx ) )


open scoped Pointwise

lemma exists_greedy_list_unsorted {I J : Finset ℕ} {A : Set ℕ} [DecidablePred (· ∈ A)] (k : ℕ) (hk : 1 ≤ k)
    (h_cover : ∀ u ∈ I, k ≤ (J.filter (fun b ↦ u ∈ A + {b})).card) :
    ∃ (B : Finset ℕ) (L : List ℕ),
      B ⊆ J ∧
      (I : Set ℕ) ⊆ A + (B : Set ℕ) ∧
      B.card = L.length ∧
      L.sum = I.card ∧
      (∀ x ∈ L, 1 ≤ x) ∧
      (∀ s, (L.filter (· ≤ s)).sum ≤ (J.card * s) / k) := by
  revert h_cover hk A I J k;
  intro I;
  induction' I using Finset.strongInduction with I ih;
  intro J A _ k hk h_cover
  by_cases hI : I = ∅;
  · use ∅, ∅; aesop;
  · -- Choose $b \in J$ maximizing $|(A+b) \cap I|$.
    obtain ⟨b, hb⟩ : ∃ b ∈ J, ∀ b' ∈ J, (Finset.filter (fun u => u ∈ A + {b'}) I).card ≤ (Finset.filter (fun u => u ∈ A + {b}) I).card := by
      apply_rules [ Finset.exists_max_image ];
      exact Exists.elim ( Finset.nonempty_of_ne_empty hI ) fun x hx => by obtain ⟨ y, hy ⟩ := Finset.card_pos.mp ( by linarith [ h_cover x hx ] ) ; exact ⟨ y, by aesop ⟩ ;
    -- Let $S = (A+b) \cap I$ and $s_{new} = |S|$.
    set S := Finset.filter (fun u => u ∈ A + {b}) I
    set s_new := S.card;
    -- Let $I' = I \setminus S$. Then $|I'| < |I|$.
    set I' := I \ S;
    -- By the induction hypothesis, there exist $B'$ and $L'$ for $I'$.
    obtain ⟨B', L', hB', hI', hB'_card, hL'_sum, hL'_pos, hL'_bound⟩ : ∃ B' : Finset ℕ, ∃ L' : List ℕ, B' ⊆ J \ {b} ∧ (I' : Set ℕ) ⊆ A + B' ∧ B'.card = L'.length ∧ L'.sum = I'.card ∧ (∀ x ∈ L', 1 ≤ x) ∧ ∀ s, (L'.filter (fun x => x ≤ s)).sum ≤ (J \ {b}).card * s / k := by
      apply ih I';
      ·
        -- Since $S$ is non-empty, $I'$ is a proper subset of $I$.
        have hS_nonempty : S.Nonempty := by
          -- Since $I$ is nonempty, there exists some $u \in I$.
          obtain ⟨u, hu⟩ : ∃ u ∈ I, ∃ b' ∈ J, u ∈ A + {b'} := by
            obtain ⟨ u, hu ⟩ := Finset.nonempty_iff_ne_empty.mpr hI; exact ⟨ u, hu, by obtain ⟨ b', hb' ⟩ := Finset.card_pos.mp ( by linarith [ h_cover u hu ] ) ; aesop ⟩ ;
          aesop;
          contrapose! right;
          exact ⟨ w, left_2, by rw [ Finset.card_eq_zero.mpr <| Finset.not_nonempty_iff_eq_empty.mp right ] ; exact Finset.card_pos.mpr ⟨ _, Finset.mem_filter.mpr ⟨ left_1, w_1, left_3, rfl ⟩ ⟩ ⟩;
        grind
      · exact?;
      · intro u hu; specialize h_cover u; aesop;
        convert h_cover using 2 ; ext ; aesop;
    norm_num +zetaDelta at *;
    -- Let's define B and L as described.
    refine' ⟨ Insert.insert b B', _, _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff, Set.subset_def ];
    · intro x hx; specialize hI' x hx; contrapose! hI'; simp_all +decide [ Set.mem_add ] ;
    · refine' ⟨ ( s_new : ℕ ) :: L', _, _, _, _ ⟩ <;> simp_all +decide [ Finset.card_sdiff, Finset.subset_iff ];
      · rw [ Finset.card_insert_of_notMem fun h => hB' h |>.2 rfl, hB'_card ];
      · simp +zetaDelta at *;
        -- Since the first set is a subset of I, their intersection is just the first set itself.
        have h_inter : {u ∈ I | ∃ x ∈ A, x + b = u} ∩ I = {u ∈ I | ∃ x ∈ A, x + b = u} := by
          aesop;
        rw [ h_inter, add_tsub_cancel_of_le ( Finset.card_le_card fun x hx => by aesop ) ];
      · contrapose! hI; aesop;
        -- Since $b \in J$, by the hypothesis $h_cover$, every element in $I$ must be covered by at least $k$ elements of $J$, including $b$. This contradicts $hI$, which states that no element in $I$ can be written as $x_1 + b$ for any $x_1 \in A$.
        have h_contradiction : ∀ x ∈ I, ∃ x_1 ∈ A, x_1 + b = x := by
          intro x hx; specialize h_cover x hx; contrapose! h_cover; simp_all +decide [ Finset.ext_iff, Set.ext_iff ] ;
          rw [ Finset.card_eq_zero.mpr ] <;> aesop;
          exact absurd ( right _ a ) ( by rw [ show { u ∈ I | ∃ x ∈ A, x + b = u } = ∅ by ext; aesop ] ; exact Nat.not_le_of_gt ( Finset.card_pos.mpr ⟨ _, Finset.mem_filter.mpr ⟨ hx, x_2, a_1, rfl ⟩ ⟩ ) ) ;
        exact Finset.eq_empty_of_forall_notMem fun x hx => by obtain ⟨ y, hy, hy' ⟩ := h_contradiction x hx; exact hI hx y hy hy';
      · intro s; by_cases hs : s_new ≤ s <;> simp_all +decide [ List.filter_cons ] ;
        · -- Since $s_new \leq s$, we can replace $s_new$ with $s$ in the inequality.
          have h_replace : I.card ≤ J.card * s / k := by
            -- Since each element in I is covered by at least k elements in J, the total number of covers is at least k * I.card.
            have h_total_covers : k * I.card ≤ J.card * S.card := by
              have h_replace : k * I.card ≤ ∑ b ∈ J, (I.filter (fun u => u ∈ A + ({b} : Set ℕ))).card := by
                have h_replace : k * I.card ≤ ∑ u ∈ I, (J.filter (fun b => u ∈ A + ({b} : Set ℕ))).card := by
                  simpa [ mul_comm ] using Finset.sum_le_sum fun u hu => h_cover u hu;
                convert h_replace using 1;
                simp +decide only [Finset.card_filter];
                exact Finset.sum_comm;
              norm_num +zetaDelta at *;
              exact h_replace.trans ( Finset.sum_le_card_nsmul _ _ _ fun x hx => hb.2 x hx );
            exact Nat.le_div_iff_mul_le hk |>.2 <| by nlinarith [ show S.card ≤ s from hs ] ;
          rw [ show ( { u ∈ I | ∃ x ∈ A, x + b = u } ∩ I ) = S from ?_ ] at hL'_sum ; aesop;
          · -- Since the filtered list is a subset of L', its sum is less than or equal to the sum of L'.
            have h_filter_le_L' : (List.filter (fun x => x ≤ s) L').sum ≤ L'.sum := by
              have h_filter_le_L' : ∀ {L : List ℕ}, (∀ x ∈ L, 1 ≤ x) → (List.filter (fun x => x ≤ s) L).sum ≤ L.sum := by
                intros L hL; induction L <;> aesop;
                by_cases h : head ≤ s <;> simp_all +decide [ List.filter_cons ] ; linarith;
              exact h_filter_le_L' hL'_pos;
            linarith [ Nat.sub_add_cancel ( show Finset.card ( Finset.filter ( fun u => ∃ x ∈ A, x + b = u ) I ) ≤ I.card from Finset.card_filter_le _ _ ) ];
          · ext; aesop;
        · refine le_trans ( hL'_bound s ) ?_;
          gcongr ; aesop

lemma greedy_list_bound {L : List ℕ} {K : ℕ} {C : ℝ}
    (h_pos : ∀ x ∈ L, 1 ≤ x)
    (h_bound : ∀ s, 1 ≤ s → s ≤ K → ((L.filter (· ≤ s)).sum : ℝ) ≤ C * s)
    (hK : 1 ≤ K) :
    (L.length : ℝ) ≤ 2 * (L.sum : ℝ) / K + C * Real.log K := by
  -- Let $L'$ be $L$ sorted in descending order.
  set L' : List ℕ := L.mergeSort (fun x y => x ≥ y);
  -- Since $L'$ is a permutation of $L$, it has the same length, sum, and elements.
  have h_perm : L'.length = L.length ∧ L'.sum = L.sum ∧ (∀ x ∈ L', 1 ≤ x) ∧ (∀ s : ℕ, 1 ≤ s → s ≤ K → (List.filter (· ≤ s) L').sum ≤ C * s) := by
    have h_perm : List.Perm L' L := by
      exact?;
    aesop;
    · exact h_perm.sum_eq;
    · have := h_perm.filter ( fun x => x ≤ s ) ; aesop;
      exact le_trans ( by simpa using List.Perm.sum_eq ( this.map _ ) |> le_of_eq ) ( h_bound s a a_1 );
  -- Define $x : \mathbb{N} \to \mathbb{N}$ by $x_i = L'.get? (i-1) |>.getD 0$.
  set x : ℕ → ℕ := fun i => if hi : i - 1 < L'.length then L'.get! (i - 1) else 0;
  -- Apply the greedy_sum_bound lemma to the function x.
  have h_greedy : (L'.length : ℝ) ≤ 2 * (∑ i ∈ Finset.Icc 1 L'.length, (x i : ℝ)) / K + C * Real.log K := by
    apply greedy_sum_bound;
    · aesop;
      · have h_sorted : List.Sorted (fun x y => x ≥ y) L' := by
          exact?;
        have h_sorted : ∀ i j, i < j → i < L'.length → j < L'.length → L'.get! i ≥ L'.get! j := by
          intro i j hij hi hj; have := List.pairwise_iff_get.mp h_sorted; aesop;
          exact this ⟨ i, by aesop ⟩ ⟨ j, by aesop ⟩ hij;
        cases lt_or_eq_of_le a_1 <;> aesop;
        exact h_sorted _ _ ( by omega ) ( by omega ) ( by omega );
      · omega;
    · aesop;
      · convert left_1 _ _;
        exact List.mem_mergeSort.mp ( List.getElem_mem _ );
      · omega;
    · intro s hs hs'; convert h_perm.2.2.2 s hs hs' using 1;
      have h_filter_eq : Finset.filter (fun j => x j ≤ s) (Finset.Icc 1 L'.length) = Finset.image (fun i => i + 1) (Finset.filter (fun i => L'.get! i ≤ s) (Finset.range L'.length)) := by
        -- To prove the equality of sets, we show each set is a subset of the other.
        apply Finset.ext
        intro j
        simp [x];
        -- To prove the equivalence, we split it into two implications.
        apply Iff.intro;
        · exact fun h => ⟨ j - 1, ⟨ by omega, by split_ifs at h <;> omega ⟩, Nat.succ_pred_eq_of_pos h.1.1 ⟩;
        · bound
      rw [ h_filter_eq, Finset.sum_image ] <;> norm_num;
      have h_filter_eq : ∀ (l : List ℕ), (∑ i ∈ Finset.filter (fun i => l.get! i ≤ s) (Finset.range l.length), (l.get! i : ℝ)) = (List.map Nat.cast (List.filter (fun x => x ≤ s) l)).sum := by
        intro l; induction l <;> aesop;
        rw [ Finset.sum_filter, Finset.sum_range_succ' ] ; aesop;
        · rw [ add_comm, ← tail_ih, Finset.sum_filter ];
        · rw [ ← tail_ih, Finset.sum_filter ];
      convert h_filter_eq L' using 1;
      simp +zetaDelta at *;
      exact Finset.sum_congr rfl fun x hx => if_pos <| Finset.mem_range.mp <| Finset.mem_filter.mp hx |>.1;
    · linarith;
  -- Since $x$ is defined as the elements of $L'$, we have $\sum_{i=1}^{m} x_i = \sum_{i=1}^{m} L'.get! (i-1) = L'.sum$.
  have h_sum_x : ∑ i ∈ Finset.Icc 1 L'.length, (x i : ℝ) = L'.sum := by
    erw [ Finset.sum_Ico_eq_sum_range ];
    simp +arith +decide [ add_comm 1, Finset.sum_range, List.get! ];
    rw [ ← List.sum_ofFn ];
    congr;
    refine' List.ext_get _ _ <;> aesop;
  aesop


lemma cons_greedy_list {L' : List ℕ} {K s_new : ℕ} {C : ℝ}
    (h_pos : ∀ x ∈ L', 1 ≤ x)
    (h_bound : ∀ s, 1 ≤ s → s ≤ K → ((L'.filter (· ≤ s)).sum : ℝ) ≤ C * s)
    (h_s_new : 1 ≤ s_new)
    (h_max : ∀ x ∈ L', x ≤ s_new)
    (h_total : (s_new : ℝ) + L'.sum ≤ C * s_new) :
    ∀ s, 1 ≤ s → s ≤ K → (((s_new :: L').filter (· ≤ s)).sum : ℝ) ≤ C * s := by
  -- Let's split into cases based on whether $s_{new} \leq s$ or not.
  intros s hs hsK
  by_cases h_s_new_le_s : s_new ≤ s;
  · convert h_total.trans _ using 1 ; ring_nf at * ; aesop;
    · -- Since every element in $L'$ is less than or equal to $s$, the filter condition is always true, so the filtered list is just $L'$ itself.
      have h_filter_eq : List.filter (fun x => x ≤ s) L' = L' := by
        exact List.filter_eq_self.mpr fun x hx => by simpa using le_trans ( h_max x hx ) h_s_new_le_s;
      rw [h_filter_eq];
    · gcongr ; norm_cast at * ; linarith [ show 0 ≤ C by nlinarith [ show ( s_new : ℝ ) ≥ 1 by norm_cast, show ( s : ℝ ) ≥ 1 by norm_cast, show ( List.sum ( List.map Nat.cast L' ) : ℝ ) ≥ 0 by exact List.sum_nonneg ( by aesop ) ] ] ;
  · specialize h_bound s hs hsK ; aesop


open scoped Pointwise

def max_gain (I J : Finset ℕ) (A : Set ℕ) [DecidablePred (· ∈ A)] : ℕ :=
  (J.image (fun b ↦ (I.filter (fun u ↦ u ∈ A + {b})).card)).max.getD 0

open scoped Pointwise

lemma exists_greedy_list {I J : Finset ℕ} {A : Set ℕ} [DecidablePred (· ∈ A)] (k : ℕ) (hk : 1 ≤ k)
    (h_cover : ∀ u ∈ I, k ≤ (J.filter (fun b ↦ u ∈ A + {b})).card) :
    ∃ (B : Finset ℕ) (L : List ℕ),
      B ⊆ J ∧
      (I : Set ℕ) ⊆ A + (B : Set ℕ) ∧
      B.card = L.length ∧
      L.sum = I.card ∧
      L.Sorted (· ≥ ·) ∧
      (∀ x ∈ L, 1 ≤ x) ∧
      (∀ s, (L.filter (· ≤ s)).sum ≤ (J.card * s) / k) := by
  -- Let $L_{unsorted}$ be a list satisfying the conditions.
  obtain ⟨B_unsorted, L_unsorted, hB_unsorted, hL_unsorted⟩ : ∃ (B_unsorted : Finset ℕ) (L_unsorted : List ℕ),
    B_unsorted ⊆ J ∧ (I : Set ℕ) ⊆ A + B_unsorted ∧ B_unsorted.card = L_unsorted.length ∧ L_unsorted.sum = I.card ∧ (∀ x ∈ L_unsorted, 1 ≤ x) ∧ (∀ s, (L_unsorted.filter (· ≤ s)).sum ≤ (J.card * s) / k) := by
      -- Apply the exists_greedy_list_unsorted lemma with the given h_cover.
      apply exists_greedy_list_unsorted k hk h_cover;
  -- Let $L = L_{unsorted}.mergeSort (\ge)$.
  obtain ⟨L_sorted, hL_sorted⟩ : ∃ (L_sorted : List ℕ), List.Sorted (fun x1 x2 => x1 ≥ x2) L_sorted ∧ List.Perm L_sorted L_unsorted := by
    refine' ⟨ L_unsorted.mergeSort ( fun x1 x2 => x1 ≥ x2 ), _, _ ⟩;
    · exact?;
    · exact?;
  -- Since $L_sorted$ is a permutation of $L_unsorted$, their sums and filters are the same.
  have h_sum_eq : L_sorted.sum = L_unsorted.sum := by
    exact hL_sorted.2.sum_eq
  have h_filter_eq : ∀ s, (L_sorted.filter (· ≤ s)).sum = (L_unsorted.filter (· ≤ s)).sum := by
    intro s; have := hL_sorted.2.filter ( fun x => x ≤ s ) ; aesop;
    -- Since the lists are permutations of each other, their sums are equal.
    apply List.Perm.sum_eq; assumption;
  use B_unsorted, L_sorted;
  aesop;
  · rw [ right_1.length_eq ];
  · exact left_4 x ( right_1.subset a )


open scoped Pointwise

lemma greedy_cover_size {I J : Finset ℕ} {A : Set ℕ} [DecidablePred (· ∈ A)] (k : ℕ) (hk : 1 ≤ k)
    (h_cover : ∀ u ∈ I, k ≤ (J.filter (fun b ↦ u ∈ A + {b})).card) :
    ∃ B : Finset ℕ, B ⊆ J ∧ (I : Set ℕ) ⊆ A + (B : Set ℕ) ∧
    (B.card : ℝ) ≤ 2 * (I.card : ℝ) / k + (J.card : ℝ) / k * Real.log k := by
  -- Apply the exists_greedy_list lemma to obtain the set B and the list L.
  obtain ⟨B, L, hB_sub, hI_cover, hB_card, hL_sum, hL_sorted, hL_pos, hL_bound⟩ := exists_greedy_list k hk h_cover;
  refine' ⟨ B, hB_sub, hI_cover, _ ⟩;
  convert greedy_list_bound _ _ _ using 1;
  -- The first part follows directly from hB_card.
  rw [hB_card];
  rw [ hL_sum ];
  · grind;
  · intro s hs₁ hs₂; rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> norm_cast ; nlinarith [ hL_bound s, Nat.div_mul_le_self ( J.card * s ) k ] ;
  · linarith


open scoped Pointwise

lemma local_construction (A : Set ℕ) (hA : A.Infinite) :
    ∀ᶠ l in Filter.atTop, ∃ B_l : Finset ℕ,
      (∀ b ∈ B_l, 2^l < b ∧ b < 2^(l+2)) ∧
      (∀ n ∈ Finset.Ioc (2^(l+1)) (2^(l+2)), n ∈ A + (B_l : Set ℕ)) ∧
      (B_l.card : ℝ) < 7 * 2^(l-1) * Real.log (counting_function A (2^l)) / (counting_function A (2^l)) := by
  -- Let's choose any $l$ such that $A(2^l)$ is large enough.
  obtain ⟨l₀, hl₀⟩ : ∃ l₀ : ℕ, ∀ l ≥ l₀, Real.log (counting_function A (2 ^ l)) > 8 ∧ counting_function A (2 ^ l) ≥ 1 := by
    have h_log_growth : Filter.Tendsto (fun l => Real.log (counting_function A (2 ^ l))) Filter.atTop Filter.atTop := by
      -- Since $A$ is infinite, the counting function $A(x)$ tends to infinity as $x$ tends to infinity.
      have h_counting_inf : Filter.Tendsto (fun x => counting_function A x) Filter.atTop Filter.atTop := by
        have h_inf : Filter.Tendsto (fun x : ℕ => (Finset.filter (· ∈ A) (Finset.Icc 1 x)).card) Filter.atTop Filter.atTop := by
          refine' Filter.tendsto_atTop_atTop.mpr _;
          -- Since $A$ is infinite, for any $b$, there exists an $i$ such that the set $\{x \in A \mid x \leq i\}$ has at least $b$ elements.
          have h_inf : ∀ b : ℕ, ∃ i : ℕ, (Finset.filter (· ∈ A) (Finset.Icc 1 i)).card ≥ b := by
            intro b
            obtain ⟨s, hs⟩ : ∃ s : Finset ℕ, s.card = b ∧ ∀ x ∈ s, x ∈ A ∧ 1 ≤ x := by
              have := hA.diff ( Set.finite_le_nat 0 ) ; cases' this.exists_subset_card_eq b with s hs; use s; aesop;
              · exact left a |>.1;
              · exact Nat.pos_of_ne_zero ( left a |>.2 );
            exact ⟨ s.sup id, by exact le_trans ( by aesop ) ( Finset.card_mono <| show s ⊆ Finset.filter ( fun x => x ∈ A ) ( Finset.Icc 1 ( s.sup id ) ) from fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hs.2 x hx |>.2, Finset.le_sup ( f := id ) hx ⟩, hs.2 x hx |>.1 ⟩ ) ⟩;
          exact fun b => by obtain ⟨ i, hi ⟩ := h_inf b; exact ⟨ i, fun a ha => hi.trans ( Finset.card_mono <| Finset.filter_subset_filter _ <| Finset.Icc_subset_Icc_right ha ) ⟩ ;
        rw [ Filter.tendsto_atTop_atTop ] at * ; aesop;
        obtain ⟨ i, hi ⟩ := h_inf b; use i; intro a ha; specialize hi ( Nat.floor a ) ( Nat.le_floor ha ) ; aesop;
      exact Real.tendsto_log_atTop.comp <| tendsto_natCast_atTop_atTop.comp <| h_counting_inf.comp <| tendsto_pow_atTop_atTop_of_one_lt one_lt_two |> Filter.Tendsto.comp <| Filter.tendsto_id;
    -- Since the logarithm of the counting function tends to infinity, there exists an l₀ such that for all l ≥ l₀, the logarithm is greater than 8.
    obtain ⟨l₀, hl₀⟩ : ∃ l₀ : ℕ, ∀ l ≥ l₀, Real.log (counting_function A (2 ^ l)) > 8 := by
      simpa using h_log_growth.eventually_gt_atTop 8;
    exact ⟨ l₀, fun l hl => ⟨ hl₀ l hl, Nat.pos_of_ne_zero fun h => by have := hl₀ l hl; norm_num [ h ] at this ⟩ ⟩;
  -- For any $l \geq l₀$, we can apply the greedy_cover_size lemma with $I = (2^{l+1}, 2^{l+2}]$, $J = (2^l, 2^{l+2})$, and $k = A(2^l)$.
  have h_apply_greedy : ∀ l ≥ l₀, ∃ B_l : Finset ℕ, B_l ⊆ Finset.Ioo (2 ^ l) (2 ^ (l + 2)) ∧ ((Finset.Ioc (2 ^ (l + 1)) (2 ^ (l + 2)) : Set ℕ) ⊆ (A : Set ℕ) + (B_l : Set ℕ)) ∧ (B_l.card : ℝ) ≤ 2 * (2 ^ (l + 1) : ℝ) / (counting_function A (2 ^ l) : ℝ) + (3 * 2 ^ l : ℝ) / (counting_function A (2 ^ l) : ℝ) * Real.log (counting_function A (2 ^ l)) := by
    -- For any $u \in I$, there are at least $k$ elements $b \in J$ such that $u \in A + \{b\}$.
    have h_cover : ∀ l ≥ l₀, ∀ u ∈ Finset.Ioc (2 ^ (l + 1)) (2 ^ (l + 2)), (Finset.filter (fun b => u ∈ A + {b}) (Finset.Ioo (2 ^ l) (2 ^ (l + 2)))).card ≥ counting_function A (2 ^ l) := by
      intro l hl u hu
      have h_b : Finset.filter (fun b => u ∈ A + {b}) (Finset.Ioo (2 ^ l) (2 ^ (l + 2))) ⊇ Finset.image (fun a => u - a) (Finset.filter (fun a => a ∈ A) (Finset.Icc 1 (2 ^ l))) := by
        intro b hb; aesop;
        · exact lt_tsub_iff_left.mpr ( by ring_nf at *; linarith );
        · omega;
        · exact ⟨ w, right_2, add_tsub_cancel_of_le ( by ring_nf at *; linarith ) ⟩;
      refine le_trans ?_ ( Finset.card_mono h_b );
      rw [ Finset.card_image_of_injOn ];
      · unfold counting_function; aesop;
        -- Since $2^l$ is an integer, $\lfloor 2^l \rfloor = 2^l$.
        norm_cast;
        erw [ Nat.floor_natCast ];
      · intro x hx y hy; aesop;
        rw [ tsub_right_inj ] at a <;> linarith [ pow_succ' 2 l, pow_succ' 2 ( l + 1 ) ];
    -- Apply the greedy_cover_size lemma with $I = \text{Finset.Ioc}(2^{l+1}, 2^{l+2})$, $J = \text{Finset.Ioo}(2^l, 2^{l+2})$, and $k = \text{counting\_function } A (2^l)$.
    intros l hl
    obtain ⟨B_l, hB_l⟩ := greedy_cover_size (counting_function A (2 ^ l)) (hl₀ l hl).right (fun u hu => h_cover l hl u hu);
    refine' ⟨ B_l, hB_l.1, hB_l.2.1, hB_l.2.2.trans _ ⟩ ; norm_num [ pow_succ' ] ; ring_nf ; norm_num;
    nlinarith [ inv_pos.mpr ( show 0 < ( counting_function A ( 2 ^ l ) : ℝ ) by exact Nat.cast_pos.mpr ( hl₀ l hl |>.2 ) ), mul_inv_cancel₀ ( ne_of_gt ( show 0 < ( counting_function A ( 2 ^ l ) : ℝ ) by exact Nat.cast_pos.mpr ( hl₀ l hl |>.2 ) ) ), Real.log_nonneg ( show ( counting_function A ( 2 ^ l ) : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( hl₀ l hl |>.2 ) ), pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( show l ≥ 0 by norm_num ) ];
  -- By simplifying the expression from h_apply_greedy and using the fact that log(A(2^l)) > 8 for l ≥ l₀, we can show that the cardinality of B_l is less than the desired bound.
  have h_simplify : ∀ l ≥ l₀, 2 * (2 ^ (l + 1) : ℝ) / (counting_function A (2 ^ l) : ℝ) + (3 * 2 ^ l : ℝ) / (counting_function A (2 ^ l) : ℝ) * Real.log (counting_function A (2 ^ l)) < 7 * (2 ^ (l - 1) : ℝ) * Real.log (counting_function A (2 ^ l)) / (counting_function A (2 ^ l) : ℝ) := by
    -- By simplifying, we can see that the inequality holds because $Real.log (counting_function A (2^l)) > 8$ for $l ≥ l₀$.
    intros l hl
    have h_log : Real.log (counting_function A (2 ^ l)) > 8 := by
      exact hl₀ l hl |>.1;
    -- By dividing both sides of the inequality by $2^l$, we can simplify it to $4 + 3 * \log(counting_function A (2^l)) < (7/2) * \log(counting_function A (2^l))$, which is exactly h_simplified.
    have h_div : (4 * 2^l + 3 * 2^l * Real.log (counting_function A (2 ^ l))) / (counting_function A (2 ^ l) : ℝ) < (7 / 2) * 2^l * Real.log (counting_function A (2 ^ l)) / (counting_function A (2 ^ l) : ℝ) := by
      -- By multiplying both sides of the inequality $4 + 3 * \log(counting_function A (2^l)) < (7/2) * \log(counting_function A (2^l))$ by $2^l$, we preserve the inequality.
      have h_mul : 4 * 2^l + 3 * 2^l * Real.log (counting_function A (2^l)) < (7 / 2) * 2^l * Real.log (counting_function A (2^l)) := by
        nlinarith [ pow_pos ( zero_lt_two' ℝ ) l ];
      gcongr;
      -- Since $counting_function A (2^l) \geq 1$ for $l \geq l₀$, we have $0 < counting_function A (2^l)$.
      apply Nat.cast_pos.mpr; exact hl₀ l hl |>.2;
    convert h_div using 1 <;> ring;
    cases l <;> norm_num [ pow_succ' ] at * ; ring;
    · unfold counting_function at * ; aesop;
      -- Since the cardinality of the set {x ∈ {1} | x ∈ A} is at least 1, 1 must be in A.
      by_cases h1 : 1 ∈ A <;> simp_all +decide [ Finset.filter_singleton ];
    · ring
  filter_upwards [ Filter.eventually_ge_atTop l₀ ] with l hl using by rcases h_apply_greedy l hl with ⟨ B_l, hB_l₁, hB_l₂, hB_l₃ ⟩ ; exact ⟨ B_l, fun b hb => Finset.mem_Ioo.mp ( hB_l₁ hb ), fun n hn => hB_l₂ ( Finset.mem_coe.mpr hn ), lt_of_le_of_lt hB_l₃ ( h_simplify l hl ) ⟩ ;


lemma log_div_self_antitone : AntitoneOn (fun x : ℝ ↦ Real.log x / x) (Set.Ici (Real.exp 1)) := by
  -- To prove the antitone property, we can use the fact that the derivative of $f(x) = \frac{\log x}{x}$ is $f'(x) = \frac{1 - \log x}{x^2}$, which is non-positive for $x \geq e$.
  have h_deriv_nonpos : ∀ x > .exp 1, deriv (fun x : ℝ => (Real.log x) / x) x ≤ 0 := by
    -- Let's compute the derivative of $f(x) = \frac{\log x}{x}$ using the quotient rule.
    have h_deriv : ∀ x > 0, deriv (fun x : ℝ => Real.log x / x) x = (1 - Real.log x) / x^2 := by
      exact fun x x_pos => by simp +decide [ x_pos.ne' ] ;
    exact fun x hx => h_deriv x ( lt_trans ( by positivity ) hx ) ▸ div_nonpos_of_nonpos_of_nonneg ( sub_nonpos_of_le ( Real.log_exp 1 ▸ Real.log_le_log ( by positivity ) hx.le ) ) ( sq_nonneg _ );
  -- Since the derivative is non-positive, the function is decreasing.
  intros x hx y hy hxy
  by_contra h_contra;
  have := exists_deriv_eq_slope ( f := fun x => Real.log x / x ) ( show x < y from lt_of_le_of_ne hxy ( by aesop_cat ) ) ; aesop;
  exact absurd ( this ( by exact continuousOn_of_forall_continuousAt fun z hz => DifferentiableAt.continuousAt ( by exact DifferentiableAt.div ( Real.differentiableAt_log ( by linarith [ hz.1, Real.exp_pos 1 ] ) ) differentiableAt_id ( by linarith [ hz.1, Real.exp_pos 1 ] ) ) ) ( by exact fun z hz => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.div ( Real.differentiableAt_log ( by linarith [ hz.1, Real.exp_pos 1 ] ) ) differentiableAt_id ( by linarith [ hz.1, Real.exp_pos 1 ] ) ) ) ) ( by rintro ⟨ c, ⟨ hxc, hcy ⟩, hcd ⟩ ; nlinarith [ h_deriv_nonpos c ( by linarith ), mul_div_cancel₀ ( Real.log y / y - Real.log x / x ) ( sub_ne_zero_of_ne <| ne_of_gt <| hxc.trans hcy ) ] )


lemma counting_function_mono {A : Set ℕ} : Monotone (counting_function A) := by
  intro x y hxy;
  exact Finset.card_mono ( Finset.filter_subset_filter _ <| Finset.Icc_subset_Icc_right <| Nat.floor_mono hxy )


lemma counting_function_tendsto_atTop {A : Set ℕ} (hA : A.Infinite) : Filter.Tendsto (counting_function A) Filter.atTop Filter.atTop := by
  -- Given that $A$ is infinite, for any natural number $k$, there exists an $m$ such that $A ∩ [1, m]$ has at least $k$ elements.
  have h_exists_subset : ∀ k : ℕ, ∃ m : ℕ, ((Finset.Icc 1 m).filter (· ∈ A)).card ≥ k := by
    intro k;
    -- Since $A$ is infinite, we can find $k$ elements in $A$ that are all greater than or equal to $1$.
    obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S.card = k ∧ ∀ x ∈ S, x ∈ A ∧ 1 ≤ x := by
      have := hA.diff ( Set.finite_le_nat 0 ) ; cases' this.exists_subset_card_eq k with S hS; use S; aesop;
      · exact left a |>.1;
      · exact Nat.pos_of_ne_zero fun h => by simpa [ h ] using left a;
    exact ⟨ Finset.sup S id, by simpa [ hS.1 ] using Finset.card_mono <| fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hS.2 x hx |>.2, Finset.le_sup ( f := id ) hx ⟩, hS.2 x hx |>.1 ⟩ ⟩;
  -- By definition of counting function, if for every $k$ there exists an $m$ such that the cardinality of the filter is at least $k$, then the counting function tends to infinity.
  have h_unbounded : ∀ k : ℕ, ∃ x : ℕ, counting_function A x ≥ k := by
    -- By definition of counting function, if for every $k$ there exists an $m$ such that the cardinality of the filter is at least $k$, then the counting function tends to infinity. Hence, we can conclude that the counting function tends to infinity.
    intros k
    obtain ⟨m, hm⟩ := h_exists_subset k
    use m
    simp [counting_function, hm];
  refine' Filter.tendsto_atTop_atTop.mpr _;
  intro k; rcases h_unbounded k with ⟨ x, hx ⟩ ; use x; intros a ha; exact le_trans hx <| counting_function_mono ha;


lemma card_dyadic_interval (l : ℕ) (hl : 1 ≤ l) :
  (Finset.Ico (2^(l-1)) (2^l)).card = 2^(l-1) := by
  cases l <;> norm_num [ pow_succ' ] at *;
  exact Nat.sub_eq_of_eq_add <| by ring;


open scoped Pointwise

lemma eventually_counting_ge_3 {A : Set ℕ} (hA : A.Infinite) :
    ∀ᶠ l in Filter.atTop, 3 ≤ counting_function A (2^(l-1)) := by
  -- Since $A$ is infinite, the counting function $counting\_function A$ tends to infinity.
  have h_count_inf : Filter.Tendsto (counting_function A) Filter.atTop Filter.atTop := by
    exact?;
  simp +zetaDelta at *;
  -- Since the counting function tends to infinity, there exists some $M$ such that for all $m \geq M$, $counting\_function A m \geq 3$.
  obtain ⟨M, hM⟩ : ∃ M, ∀ m ≥ M, 3 ≤ counting_function A m := by
    exact Filter.eventually_atTop.mp ( h_count_inf.eventually_ge_atTop 3 ) |> fun ⟨ M, hM ⟩ ↦ ⟨ M, fun m hm ↦ hM m hm ⟩;
  -- Choose $a$ such that $2^{a-1} \geq M$.
  obtain ⟨a, ha⟩ : ∃ a, 2^(a-1) ≥ M := by
    exact ⟨ ⌈M⌉₊ + 1, le_trans ( Nat.le_ceil _ ) ( mod_cast Nat.le_of_lt ( Nat.recOn ⌈M⌉₊ ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at * ; linarith ) ) ⟩;
  exact ⟨ a, fun b hb => hM _ <| le_trans ha <| mod_cast Nat.pow_le_pow_right ( by decide ) <| Nat.sub_le_sub_right hb 1 ⟩


open scoped Pointwise

lemma dyadic_term_bound {A : Set ℕ} (hA : A.Infinite) :
  ∀ᶠ (l : ℕ) in Filter.atTop, ∀ k ∈ Finset.Ico (2^(l-1) : ℕ) (2^l : ℕ),
    Real.log (counting_function A (k : ℝ)) / (counting_function A (k : ℝ) : ℝ) ≥
    Real.log (counting_function A (2^l : ℝ)) / (counting_function A (2^l : ℝ) : ℝ) := by
  simp +zetaDelta at *;
  -- Since $A$ is infinite, there exists some $N$ such that for all $l \geq N$, $A(2^{l-1}) \geq 3$.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ l ≥ N, 3 ≤ counting_function A (2^(l-1)) := by
    convert eventually_counting_ge_3 hA;
    norm_num [ Filter.eventually_atTop ];
  -- Let $a = N + 1$.
  use N + 1;
  intros b hb k hk₁ hk₂; have := hN b ( by linarith ) ; aesop;
  -- Since $counting_function A$ is monotone, we have $counting_function A (2^{b-1}) \leq counting_function A k \leq counting_function A (2^b)$.
  have h_monotone : counting_function A (2^(b-1)) ≤ counting_function A k ∧ counting_function A k ≤ counting_function A (2^b) := by
    constructor <;> refine' Finset.card_mono _ <;> aesop;
    · intro x hx; aesop;
      exact right_1.trans ( Nat.floor_le_of_le ( mod_cast hk₁ ) );
    · exact fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1, Nat.le_floor <| mod_cast Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2.trans hk₂.le ⟩, Finset.mem_filter.mp hx |>.2 ⟩;
  -- Since $f(x) = \frac{\log x}{x}$ is antitone on $[3, \infty)$, we have $f(counting_function A k) \geq f(counting_function A (2^b))$.
  have h_antitone : ∀ x y : ℝ, 3 ≤ x → x ≤ y → Real.log x / x ≥ Real.log y / y := by
    -- Let's choose any $x, y \in [3, \infty)$ with $x \leq y$.
    intro x y hx hy
    have h_deriv_neg : ∀ x : ℝ, 3 ≤ x → deriv (fun x => Real.log x / x) x ≤ 0 := by
      intro x hx; norm_num [ show x ≠ 0 by linarith ];
      exact div_nonpos_of_nonpos_of_nonneg ( sub_nonpos_of_le ( by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith ) ) ) ( sq_nonneg _ );
    by_contra h_contra;
    have := exists_deriv_eq_slope ( fun x => Real.log x / x ) ( show x < y from hy.lt_of_ne ( by rintro rfl; norm_num at h_contra ) ) ; aesop;
    exact absurd ( this ( by exact continuousOn_of_forall_continuousAt fun z hz => DifferentiableAt.continuousAt ( by exact DifferentiableAt.div ( Real.differentiableAt_log ( by linarith [ hz.1 ] ) ) differentiableAt_id ( by linarith [ hz.1 ] ) ) ) ( by exact fun z hz => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.div ( Real.differentiableAt_log ( by linarith [ hz.1 ] ) ) differentiableAt_id ( by linarith [ hz.1 ] ) ) ) ) ( by rintro ⟨ c, ⟨ hxc, hcy ⟩, hcd ⟩ ; rw [ eq_div_iff ] at hcd <;> nlinarith [ h_deriv_neg c ( by linarith ) ] );
  exact h_antitone _ _ ( mod_cast by linarith ) ( mod_cast by linarith )


open scoped Pointwise

lemma dyadic_sum_bound {A : Set ℕ} (hA : A.Infinite) :
  ∀ᶠ l in Filter.atTop,
    (2^(l-1) : ℝ) * (Real.log (counting_function A (2^l)) / (counting_function A (2^l) : ℝ)) ≤
    ∑ k ∈ Finset.Ico (2^(l-1) : ℕ) (2^l : ℕ), Real.log (counting_function A k) / (counting_function A k : ℝ) := by
  -- Apply the dyadic_term_bound to each term in the sum.
  have h_sum_bound : ∀ᶠ l in Filter.atTop, ∀ k ∈ Finset.Ico (2^(l-1) : ℕ) (2^l : ℕ), Real.log (counting_function A (k : ℝ)) / (counting_function A (k : ℝ) : ℝ) ≥ Real.log (counting_function A (2^l : ℝ)) / (counting_function A (2^l : ℝ) : ℝ) := by
    exact?;
  filter_upwards [ h_sum_bound, Filter.eventually_gt_atTop 0 ] with l hl hl';
  convert Finset.sum_le_sum hl ; aesop


open scoped Pointwise

lemma sum_dyadic_bound {A : Set ℕ} (hA : A.Infinite) :
    ∃ l₀, ∀ n, ∑ l ∈ Finset.Ico l₀ (Nat.log 2 n + 1), (2^(l-1) : ℝ) * Real.log (counting_function A (2^l)) / counting_function A (2^l) ≤
    ∑ k ∈ Finset.Icc 1 n, Real.log (counting_function A k) / counting_function A k := by
  obtain ⟨ l₀, hl₀ ⟩ := Filter.eventually_atTop.mp ( dyadic_sum_bound hA );
  use l₀ + 1;
  intro n
  have h_sum_bound : ∑ l ∈ Finset.Ico (l₀ + 1) (Nat.log 2 n + 1), ∑ k ∈ Finset.Ico (2^(l-1) : ℕ) (2^l : ℕ), Real.log (counting_function A k) / (counting_function A k : ℝ) ≤ ∑ k ∈ Finset.Icc 1 n, Real.log (counting_function A k) / (counting_function A k : ℝ) := by
    -- The union of the dyadic intervals is a subset of [1, n], so the sum over the union is less than or equal to the sum over [1, n].
    have h_union_subset : Finset.biUnion (Finset.Ico (l₀ + 1) (Nat.log 2 n + 1)) (fun l => Finset.Ico (2^(l-1) : ℕ) (2^l : ℕ)) ⊆ Finset.Icc 1 n := by
      -- Each interval [2^(l-1), 2^l) is contained within [1, n] because 2^(l-1) ≥ 1 and 2^l ≤ n for l in the given range.
      intros x hx
      aesop;
      · linarith [ Nat.one_le_pow ( w - 1 ) 2 zero_lt_two ];
      · exact right.le.trans ( Nat.pow_le_of_le_log ( by aesop ) ( by omega ) );
    rw [ ← Finset.sum_biUnion ];
    · exact Finset.sum_le_sum_of_subset_of_nonneg h_union_subset fun _ _ _ => div_nonneg ( Real.log_natCast_nonneg _ ) ( Nat.cast_nonneg _ );
    · -- For any two distinct $l$ and $m$ in the range, the intervals $[2^{l-1}, 2^l)$ and $[2^{m-1}, 2^m)$ are disjoint because $2^l \leq 2^{m-1}$ when $l < m$.
      intros l hl m hm hlm;
      cases lt_or_gt_of_ne hlm <;> [ exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Ico.mp hx₁, Finset.mem_Ico.mp hx₂, pow_le_pow_right₀ ( show 1 ≤ 2 by norm_num ) ( show l ≤ m - 1 from Nat.le_sub_one_of_lt ‹_› ) ] ; ; exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Ico.mp hx₁, Finset.mem_Ico.mp hx₂, pow_le_pow_right₀ ( show 1 ≤ 2 by norm_num ) ( show m ≤ l - 1 from Nat.le_sub_one_of_lt ‹_› ) ] ];
  exact le_trans ( Finset.sum_le_sum fun x hx => by simpa only [ mul_div_assoc ] using hl₀ x ( by linarith [ Finset.mem_Ico.mp hx ] ) ) h_sum_bound


open scoped Pointwise

theorem Lorentz_theorem (A : Set ℕ) (hA : A.Infinite) :
    ∃ B : Set ℕ, (∀ᶠ n in Filter.atTop, n ∈ A + B) ∧
    ∃ C > 0, ∀ n : ℕ, (counting_function B n : ℝ) ≤ C * ∑ k ∈ Finset.Icc 1 n, Real.log (counting_function A k) / (counting_function A k) := by
  norm_num +zetaDelta at *;
  -- Using `local_construction`, we can obtain sets $B_l$ for $l \geq l_0$.
  obtain ⟨l₀, hB⟩ : ∃ l₀, ∀ l ≥ l₀, ∃ B_l : Finset ℕ,
    (∀ b ∈ B_l, (2^l < b ∧ b < 2^(l+2))) ∧
    (∀ n ∈ Finset.Ioc (2^(l+1)) (2^(l+2)), (n ∈ A + (B_l : Set ℕ))) ∧
    (B_l.card : ℝ) < 7 * 2^(l-1) * (Real.log (counting_function A (2^l))) / (counting_function A (2^l)) := by
      -- Apply the local_construction lemma to obtain the required l₀ and B_l.
      apply Filter.eventually_atTop.mp (local_construction A hA);
  obtain ⟨ l₁, h₁ ⟩ := sum_dyadic_bound hA;
  -- Let $B = \bigcup_{l \geq l₀} B_l$.
  obtain ⟨B, hB⟩ : ∃ B : Set ℕ, (∀ᶠ n in Filter.atTop, n ∈ A + B) ∧ (∀ n, (B ∩ Finset.Icc 1 n).toFinset.card ≤ 7 * ∑ l ∈ Finset.Ico (max l₀ l₁) (Nat.log 2 n + 1), (2^(l-1) : ℝ) * Real.log (counting_function A (2^l)) / (counting_function A (2^l))) := by
    choose! B_hB₁ B_hB₂ B_hB₃ using hB;
    refine' ⟨ ⋃ l ≥ max l₀ l₁, B_hB₁ l, _, _ ⟩ <;> aesop;
    · use 2^(max l₀ l₁ + 2) + 1;
      intro b hb
      obtain ⟨l, hl₁, hl₂⟩ : ∃ l ≥ max l₀ l₁, 2^(l+1) < b ∧ b ≤ 2^(l+2) := by
        -- Let $l$ be such that $2^{l+1} < b \leq 2^{l+2}$.
        obtain ⟨l, hl⟩ : ∃ l, 2^(l+1) < b ∧ b ≤ 2^(l+2) := by
          -- Let $l$ be such that $2^l \leq b < 2^{l+1}$.
          obtain ⟨l, hl⟩ : ∃ l, 2^l ≤ b ∧ b < 2^(l+1) := by
            exact ⟨ Nat.log 2 b, Nat.pow_le_of_le_log ( by linarith [ Nat.one_le_pow ( Max.max l₀ l₁ + 2 ) 2 zero_lt_two ] ) ( by linarith ), Nat.lt_pow_of_log_lt ( by linarith ) ( by linarith ) ⟩;
          -- Let $l' = l - 1$. Then $2^{l'+1} = 2^l$, which is less than or equal to $b$. But we need $2^{l'+1} < b$. Since $b$ is strictly less than $2^{l+1}$, and $2^l$ is less than or equal to $b$, but not necessarily strictly less. So this might not work.
          by_cases h_eq : b = 2^l;
          · use l - 2;
            rcases l with ( _ | _ | l ) <;> simp_all +decide [ pow_succ' ];
            linarith [ Nat.one_le_pow ( Max.max l₀ l₁ ) 2 zero_lt_two ];
          · exact ⟨ l - 1, by cases l <;> norm_num [ pow_succ' ] at * <;> omega, by cases l <;> norm_num [ pow_succ' ] at * <;> omega ⟩;
        refine' ⟨ l, _, hl ⟩;
        contrapose! hb;
        exact Nat.lt_succ_of_le ( le_trans hl.2 ( pow_le_pow_right₀ ( by decide ) ( by linarith ) ) );
      exact B_hB₃ l ( le_trans ( le_max_left _ _ ) hl₁ ) |>.1 b hl₂.1 hl₂.2 |> fun ⟨ a, ha, b, hb, hab ⟩ => ⟨ a, ha, b, Set.mem_iUnion₂.mpr ⟨ l, ⟨ le_trans ( le_max_left _ _ ) hl₁, le_trans ( le_max_right _ _ ) hl₁ ⟩, hb ⟩, hab ⟩;
    · -- By definition of $B$, we know that every element in $B \cap \{1, \ldots, n\}$ is in some $B_l$ for $l \geq \max(l₀, l₁)$.
      have hB_subset : (Finset.filter (fun a => ∃ i, (l₀ ≤ i ∧ l₁ ≤ i) ∧ a ∈ B_hB₁ i) (Finset.Icc 1 n)).card ≤ ∑ l ∈ Finset.Ico (max l₀ l₁) (Nat.log 2 n + 1), (B_hB₁ l).card := by
        have hB_subset : Finset.filter (fun a => ∃ i, (l₀ ≤ i ∧ l₁ ≤ i) ∧ a ∈ B_hB₁ i) (Finset.Icc 1 n) ⊆ Finset.biUnion (Finset.Ico (max l₀ l₁) (Nat.log 2 n + 1)) (fun l => B_hB₁ l) := by
          intro a ha; aesop;
          refine' ⟨ w, ⟨ ⟨ left_1, right_2 ⟩, _ ⟩, right ⟩;
          exact Nat.lt_succ_of_le ( Nat.le_log_of_pow_le ( by norm_num ) ( by linarith [ B_hB₂ _ left_1 _ right ] ) );
        exact le_trans ( Finset.card_le_card hB_subset ) ( Finset.card_biUnion_le );
      refine' le_trans ( Nat.cast_le.mpr hB_subset ) _;
      push_cast [ Finset.mul_sum _ _ _ ];
      exact Finset.sum_le_sum fun i hi => by have := B_hB₃ i ( le_trans ( le_max_left _ _ ) ( Finset.mem_Ico.mp hi |>.1 ) ) ; ring_nf at this ⊢; linarith;
  refine' ⟨ B, _, 7, by norm_num, _ ⟩;
  · exact Filter.eventually_atTop.mp hB.1;
  · intro n; specialize hB; specialize h₁ n; aesop;
    refine le_trans ?_ ( mul_le_mul_of_nonneg_left h₁ <| by norm_num );
    -- Since the sum from l₁ to Nat.log 2 n includes the sum from max l₀ l₁ to Nat.log 2 n, we can conclude the inequality.
    have h_sum_ge : ∑ l ∈ Finset.Ico l₁ (Nat.log 2 n + 1), (2^(l-1) : ℝ) * Real.log (counting_function A (2^l)) / (counting_function A (2^l)) ≥ ∑ l ∈ Finset.Ico (max l₀ l₁) (Nat.log 2 n + 1), (2^(l-1) : ℝ) * Real.log (counting_function A (2^l)) / (counting_function A (2^l)) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.Ico_subset_Ico ( le_max_right _ _ ) le_rfl ) fun _ _ _ => div_nonneg ( mul_nonneg ( pow_nonneg zero_le_two _ ) ( Real.log_natCast_nonneg _ ) ) ( Nat.cast_nonneg _ );
    refine le_trans ?_ ( mul_le_mul_of_nonneg_left h_sum_ge <| by norm_num );
    unfold counting_function; aesop;


open scoped Pointwise

lemma local_construction_lemma (A : Set ℕ) (hA : A.Infinite) :
    ∀ᶠ l in Filter.atTop, ∃ B_l : Finset ℕ,
      (∀ b ∈ B_l, 2^l < b ∧ b < 2^(l+2)) ∧
      (∀ n ∈ Finset.Ioc (2^(l+1)) (2^(l+2)), n ∈ A + (B_l : Set ℕ)) ∧
      (B_l.card : ℝ) < 7 * 2^(l-1) * Real.log (counting_function A (2^l)) / (counting_function A (2^l)) := by
  -- Apply the local_construction lemma to obtain the required B_l.
  apply local_construction A hA


open scoped Pointwise

lemma local_covering {A : Set ℕ} {l : ℕ} {u : ℕ} (hu : u ∈ Finset.Ioc (2^(l+1)) (2^(l+2))) :
    (Finset.filter (fun b ↦ u ∈ A + {b}) (Finset.Ioo (2^l) (2^(l+2)))).card ≥ counting_function A (2^l) := by
  -- Let $S = A \cap \{1, \dots, 2^l\}$. Then $|S| = A(2^l)$.
  set S := Finset.filter (fun a => a ∈ A) (Finset.Icc 1 (2 ^ l))
  have hS_card : S.card = counting_function A (2 ^ l) := by
    -- By definition of $S$, we know that $S$ contains exactly the elements of $A$ that are less than or equal to $2^l$.
    have hS_eq : S = Finset.filter (fun a => a ∈ A) (Finset.Icc 1 (2 ^ l)) := by
      rfl;
    -- By definition of $S$, we know that $S$ contains exactly the elements of $A$ that are less than or equal to $2^l$. Therefore, the cardinality of $S$ is equal to the counting function of $A$ at $2^l$.
    simp [hS_eq, counting_function];
    -- Since $2^l$ is an integer, the floor of $2^l$ is just $2^l$ itself.
    norm_cast;
    erw [ Nat.floor_natCast ];
  -- For each $a \in S$, let $b = u - a$. Since $u > 2^{l+1}$ and $a \leq 2^l$, $b > 2^l$. Also, since $u \leq 2^{l+2}$, $b < 2^{l+2}$. So $b \in (2^l, 2^{l+2})$.
  have h_b_in_interval : ∀ a ∈ S, u - a ∈ Finset.Ioo (2 ^ l) (2 ^ (l + 2)) := by
    aesop <;> omega;
  -- The map $a \mapsto u - a$ is injective, so the cardinality of the image of $S$ under this map is at least $|S|$.
  have h_inj_map : (Finset.image (fun a => u - a) S).card ≥ S.card := by
    rw [ Finset.card_image_of_injOn fun x hx y hy hxy => by rw [ tsub_right_inj ] at hxy <;> linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ), Finset.mem_Icc.mp ( Finset.mem_filter.mp hy |>.1 ), Finset.mem_Ioc.mp hu, pow_succ' 2 l ] ];
  refine hS_card ▸ h_inj_map.trans ( Finset.card_le_card ?_ ) ; intro ; aesop;
  exact ⟨ w, right_2, add_tsub_cancel_of_le <| by ring_nf at *; linarith ⟩


open scoped Pointwise

lemma counting_union_bound {B : ℕ → Finset ℕ} {L : ℕ}
    (hB : ∀ l, B l ⊆ Finset.Ioo (2^l) (2^(l+2))) :
    ∀ n : ℕ, (counting_function (⋃ l ≥ L, (B l : Set ℕ)) n : ℝ) ≤ ∑ l ∈ Finset.Ico L (Nat.log 2 n + 1), (B l).card := by
  -- Let $S = \bigcup_{l \ge L} B_l$.
  intro n
  simp [counting_function];
  -- The set {x ∈ Finset.Icc 1 n | ∃ i, L ≤ i ∧ x ∈ B i} is a subset of the union of B l for l in the range L to Nat.log 2 n.
  have h_subset : {x ∈ Finset.Icc 1 n | ∃ i, L ≤ i ∧ x ∈ B i} ⊆ Finset.biUnion (Finset.Ico L (Nat.log 2 n + 1)) (fun l => B l) := by
    intro x hx; aesop;
    exact ⟨ w, ⟨ left_1, Nat.lt_succ_of_le ( Nat.le_log_of_pow_le ( by norm_num ) ( by linarith [ Finset.mem_Ioo.mp ( hB _ right ) ] ) ) ⟩, right ⟩;
  exact_mod_cast le_trans ( Finset.card_le_card h_subset ) ( Finset.card_biUnion_le )


#check Lorentz_theorem
#check counting_union_bound

open scoped Pointwise

theorem Lorentz_theorem_proven (A : Set ℕ) (hA : A.Infinite) :
    ∃ B : Set ℕ, (∀ᶠ n in Filter.atTop, n ∈ A + B) ∧
    ∃ C > 0, ∀ n : ℕ, (counting_function B n : ℝ) ≤ C * ∑ k ∈ Finset.Icc 1 n, Real.log (counting_function A k) / (counting_function A k) := by
  -- Apply the Lorentz theorem to obtain the set B and the constant C.
  obtain ⟨B, hB⟩ := Lorentz_theorem A hA;
  use B


open scoped Pointwise

lemma lorentz_covering {A : Set ℕ} {L : ℕ} {B : ℕ → Finset ℕ}
    (h_cover : ∀ l ≥ L, ∀ n ∈ Finset.Ioc (2^(l+1)) (2^(l+2)), n ∈ A + (B l : Set ℕ)) :
    ∀ n > 2^(L+1), n ∈ A + (⋃ l ≥ L, (B l : Set ℕ)) := by
  intro n hn
  obtain ⟨l, hl⟩ : ∃ l ≥ L, n ∈ Finset.Ioc (2^(l+1)) (2^(l+2)) := by
    -- Let $l = \lfloor \log_2 (n-1) \rfloor$. Then $2^l \le n-1 < 2^{l+1}$.
    obtain ⟨l, hl⟩ : ∃ l, 2^l ≤ n-1 ∧ n-1 < 2^(l+1) := by
      -- By definition of logarithm, there exists an l such that 2^l ≤ n-1 < 2^(l+1).
      use Nat.log 2 (n - 1);
      exact ⟨ Nat.pow_le_of_le_log ( Nat.sub_ne_zero_of_lt ( lt_of_le_of_lt ( Nat.one_le_pow _ _ ( by decide ) ) hn ) ) ( by linarith ), Nat.lt_pow_of_log_lt ( by decide ) ( by linarith ) ⟩;
    rcases lt_trichotomy l L <;> aesop;
    · exact False.elim <| hn.not_le <| by rw [ tsub_lt_iff_left ] at right <;> linarith [ pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ( by linarith : l + 1 ≤ L ), pow_succ' 2 L ] ;
    · omega;
    · exact ⟨ l - 1, Nat.le_pred_of_lt h_2, by cases l <;> norm_num [ pow_succ' ] at * ; omega, by cases l <;> norm_num [ pow_succ' ] at * ; omega ⟩;
  exact Set.mem_of_subset_of_mem ( Set.add_subset_add Set.Subset.rfl <| Set.subset_iUnion₂_of_subset l hl.1 <| Set.Subset.refl _ ) ( h_cover l hl.1 n hl.2 )


open scoped Pointwise

theorem Erdos_Straus_conjecture (A : Set ℕ) (hA : A.Infinite) :
    ∃ B : Set ℕ, has_density_zero B ∧ (∀ᶠ n in Filter.atTop, n ∈ A + B) := by
  -- Apply the Lorentz theorem to obtain the set B.
  obtain ⟨B, hB⟩ := Lorentz_theorem_proven A hA;
  -- Let's choose any $C > 0$ such that the inequality holds.
  obtain ⟨C, hC_pos, hC⟩ := hB.right;
  -- We need to show that $\frac{B(n)}{n} \to 0$ as $n \to \infty$.
  have h_density_zero : Filter.Tendsto (fun n : ℕ => (counting_function B n : ℝ) / n) Filter.atTop (nhds 0) := by
    -- Since $A$ is infinite, $A(k) \to \infty$ as $k \to \infty$.
    have h_A_inf : Filter.Tendsto (fun k : ℕ => (counting_function A k : ℝ)) Filter.atTop Filter.atTop := by
      have h_A_inf : Filter.Tendsto (fun k : ℕ => (counting_function A k : ℝ)) Filter.atTop Filter.atTop := by
        have h_A_inf_aux : Filter.Tendsto (counting_function A) Filter.atTop Filter.atTop := by
          exact?
        rw [ Filter.tendsto_atTop_atTop ] at *;
        exact fun x => by rcases h_A_inf_aux ⌈x⌉₊ with ⟨ i, hi ⟩ ; exact ⟨ ⌈i⌉₊, fun n hin => le_trans ( Nat.le_ceil _ ) ( mod_cast hi n ( Nat.le_of_ceil_le hin ) ) ⟩ ;
      convert h_A_inf using 1;
    -- Since $A$ is infinite, $\frac{\log A(k)}{A(k)} \to 0$ as $k \to \infty$.
    have h_log_A_inf : Filter.Tendsto (fun k : ℕ => (Real.log (counting_function A k)) / (counting_function A k)) Filter.atTop (nhds 0) := by
      -- We can use the substitution $y = \frac{1}{x}$ to transform the limit into $\lim_{y \to 0^+} y \log(1/y)$.
      have h_subst : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) := by
        norm_num +zetaDelta at *;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
      exact h_subst.comp ( Filter.map_mono h_A_inf ) |> fun h => h.congr ( by intros; simp +decide ; ring );
    -- By the properties of limits, if the average of the first n terms of a sequence tends to 0, then the limit of the sequence divided by n also tends to 0.
    have h_avg_zero : Filter.Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (Real.log (counting_function A k)) / (counting_function A k)) / (n : ℝ)) Filter.atTop (nhds 0) := by
      have h_avg_zero : ∀ {u : ℕ → ℝ}, Filter.Tendsto u Filter.atTop (nhds 0) → Filter.Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, u (k + 1)) / (n : ℝ)) Filter.atTop (nhds 0) := by
        intro u hu; rw [ Metric.tendsto_nhds ] at *; aesop;
        -- Given that $|u_k| < \epsilon$ for all $k \geq N$, we can bound the sum $\sum_{k=1}^n u_k$.
        obtain ⟨N, hN⟩ : ∃ N, ∀ k ≥ N, |u k| < ε / 2 := hu (ε / 2) (half_pos a);
        -- We can bound the sum $\sum_{k=1}^n u_k$ by splitting it into two parts: the sum up to $N$ and the sum from $N$ to $n$.
        have h_split_sum : ∀ n ≥ N, |∑ k ∈ Finset.range n, u (k + 1)| ≤ |∑ k ∈ Finset.range N, u (k + 1)| + ∑ k ∈ Finset.Ico N n, |u (k + 1)| := by
          -- By splitting the sum into two parts, we can apply the triangle inequality to the second part.
          intros n hn
          have h_split : ∑ k ∈ Finset.range n, u (k + 1) = ∑ k ∈ Finset.range N, u (k + 1) + ∑ k ∈ Finset.Ico N n, u (k + 1) := by
            rw [ Finset.sum_range_add_sum_Ico _ hn ];
          -- Applying the triangle inequality to the sum of the second part, we get |∑ k ∈ Finset.Ico N n, u (k + 1)| ≤ ∑ k ∈ Finset.Ico N n, |u (k + 1)|.
          have h_triangle : |∑ k ∈ Finset.Ico N n, u (k + 1)| ≤ ∑ k ∈ Finset.Ico N n, |u (k + 1)| := by
            exact Finset.abs_sum_le_sum_abs _ _;
          -- Applying the triangle inequality to the sum of the two parts, we get |∑ k ∈ Finset.range N, u (k + 1) + ∑ k ∈ Finset.Ico N n, u (k + 1)| ≤ |∑ k ∈ Finset.range N, u (k + 1)| + |∑ k ∈ Finset.Ico N n, u (k + 1)|.
          have h_triangle : |∑ k ∈ Finset.range N, u (k + 1) + ∑ k ∈ Finset.Ico N n, u (k + 1)| ≤ |∑ k ∈ Finset.range N, u (k + 1)| + |∑ k ∈ Finset.Ico N n, u (k + 1)| := by
            exact?;
          grind
        refine' ⟨ N + ⌈ ( |∑ k ∈ Finset.range N, u ( k + 1)| + 1 ) / ( ε / 2 ) ⌉₊ + 1, fun n hn => _ ⟩ ; rw [ div_lt_iff₀ ] <;> nlinarith [ Nat.le_ceil ( ( |∑ k ∈ Finset.range N, u ( k + 1)| + 1 ) / ( ε / 2 ) ), mul_div_cancel₀ ( |∑ k ∈ Finset.range N, u ( k + 1)| + 1 ) ( by linarith : ( ε / 2 ) ≠ 0 ), show ( n : ℝ ) ≥ N + ⌈ ( |∑ k ∈ Finset.range N, u ( k + 1)| + 1 ) / ( ε / 2 ) ⌉₊ + 1 by exact_mod_cast hn, h_split_sum n ( by linarith ), show ( ∑ k ∈ Finset.Ico N n, |u ( k + 1 )| ) ≤ ( n - N ) * ( ε / 2 ) by exact le_trans ( Finset.sum_le_sum fun i hi => le_of_lt ( hN _ ( by linarith [ Finset.mem_Ico.mp hi ] ) ) ) ( by simp +decide [ Nat.cast_sub ( show N ≤ n by linarith ) ] ) ];
      convert h_avg_zero h_log_A_inf using 2 ; erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ];
    refine' squeeze_zero ( fun n => by positivity ) ( fun n => by simpa [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] using mul_le_mul_of_nonneg_right ( hC n ) ( inv_nonneg.mpr ( Nat.cast_nonneg n ) ) ) ( by simpa [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] using h_avg_zero.const_mul C );
  exact ⟨ B, h_density_zero, hB.1 ⟩


open scoped Pointwise

lemma cesaro_mean_zero {u : ℕ → ℝ} (h : Filter.Tendsto u Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n, u k) / n) Filter.atTop (nhds 0) := by
  rw [ Metric.tendsto_nhds ] at * ; aesop;
  obtain ⟨ N, hN ⟩ := h ( ε / 2 ) ( half_pos a );
  -- We can bound the sum $\sum_{k=1}^n u_k$ by splitting it into two parts: the sum up to $N$ and the sum from $N+1$ to $n$.
  have h_split : ∀ n ≥ N, |∑ k ∈ Finset.Icc 1 n, u k| ≤ |∑ k ∈ Finset.Icc 1 N, u k| + ∑ k ∈ Finset.Icc (N + 1) n, |u k| := by
    intro n hn; erw [ Finset.sum_Ico_eq_sub _ ( by linarith ), Finset.sum_Ico_eq_sub _ ( by linarith ) ] ; aesop;
    erw [ Finset.sum_Ico_eq_sub _ _ ] <;> try linarith;
    induction hn <;> norm_num [ Finset.sum_range_succ ] at *;
    cases abs_cases ( ∑ k ∈ Finset.range ‹_›, u k + u ‹_› + u ( ‹_› + 1 ) - u 0 ) <;> cases abs_cases ( ∑ k ∈ Finset.range ‹_›, u k + u ‹_› - u 0 ) <;> cases abs_cases ( u ( ‹_› + 1 ) ) <;> linarith;
  -- We can bound the sum $\sum_{k=N+1}^n |u_k|$ by $(n - N) \cdot \frac{\epsilon}{2}$.
  have h_bound : ∀ n ≥ N, ∑ k ∈ Finset.Icc (N + 1) n, |u k| ≤ (n - N) * (ε / 2) := by
    exact fun n hn => le_trans ( Finset.sum_le_sum fun i hi => le_of_lt ( hN i ( by linarith [ Finset.mem_Icc.mp hi ] ) ) ) ( by simp +decide [ hn ] );
  refine' ⟨ N + ⌈ ( |∑ k ∈ Finset.Icc 1 N, u k| + 1 ) / ( ε / 2 ) ⌉₊ + 1, fun n hn => _ ⟩ ; rw [ div_lt_iff₀ ] <;> nlinarith [ Nat.le_ceil ( ( |∑ k ∈ Finset.Icc 1 N, u k| + 1 ) / ( ε / 2 ) ), mul_div_cancel₀ ( |∑ k ∈ Finset.Icc 1 N, u k| + 1 ) ( ne_of_gt <| half_pos a ), h_split n <| by linarith, h_bound n <| by linarith, show ( n : ℝ ) ≥ N + ⌈ ( |∑ k ∈ Finset.Icc 1 N, u k| + 1 ) / ( ε / 2 ) ⌉₊ + 1 by exact_mod_cast hn ]


lemma log_div_self_tendsto_zero : Filter.Tendsto (fun x : ℝ ↦ Real.log x / x) Filter.atTop (nhds 0) := by
  -- Let $y = \frac{1}{x}$, so we can rewrite the limit as $\lim_{y \to 0^+} y \log(1/y)$.
  suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
    exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
  -- We can use the fact that the limit of $y \log(y)$ as $y \to 0^+$ is $0$.
  have h_log_y : Filter.Tendsto (fun y : ℝ => y * Real.log y) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.tendsto 0 );
  simpa [ mul_comm ] using h_log_y.neg.congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by simp +decide [ Real.log_div, hx.out.ne' ] )
variable {β : Type*} [Preorder β]

variable (S : Set β) (a b : β)

abbrev Set.interIio (S : Set β) (b : β) : Set β :=
  S ∩ Set.Iio b

noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  (Set.interIio (S ∩ A) b).ncard / (Set.interIio A b).ncard

open scoped Topology

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Filter.Tendsto (fun (b : β) => partialDensity S A b) Filter.atTop (𝓝 α)

theorem erdos_31 (A : Set ℕ) (hA : A.Infinite) :
    ∃ B : Set ℕ, HasDensity B 0 ∧
      ∃ n0 : ℕ, ∀ n ≥ n0, n ∈ A + B := by
  -- By combining the results from the local construction lemma and the density zero property, we can conclude the proof.
  obtain ⟨B, hB_density, hB_cover⟩ := Erdos_Straus_conjecture A hA;
  -- Combine the hypotheses to conclude the existence of B.
  use B;
  unfold HasDensity at *; aesop;
  unfold partialDensity; aesop;
  convert hB_density using 2;
  unfold has_density_zero; norm_num [ Set.ncard_eq_toFinset_card' ] ;
  unfold counting_function; norm_num [ Set.ncard_eq_toFinset_card' ] ;
  -- The difference between the two sums is just the term for $k = 0$, which is zero since $0 \notin B$.
  have h_diff : ∀ n : ℕ, (Finset.filter (fun a => a ∈ B) (Finset.Iio (n + 1))).card = (Finset.filter (fun a => a ∈ B) (Finset.Icc 1 n)).card + (if 0 ∈ B then 1 else 0) := by
    intro n; rw [ Finset.card_filter, Finset.card_filter ] ; rw [ Finset.sum_eq_sum_diff_singleton_add ( show 0 ∈ Finset.Iio ( n + 1 ) from by norm_num ) ] ; aesop;
  rw [ ← Filter.tendsto_add_atTop_iff_nat 1 ] ; aesop;
  · rw [ Metric.tendsto_nhds ] at * ; aesop;
    obtain ⟨ N, hN ⟩ := a ε a_1;
    exact ⟨ N + 1, fun n hn => lt_of_le_of_lt ( by rw [ div_le_div_iff₀ ] <;> norm_cast <;> nlinarith [ show Finset.card ( Finset.filter ( fun a => a ∈ B ) ( Finset.Icc 1 n ) ) ≤ n from le_trans ( Finset.card_filter_le _ _ ) ( by simpa ) ] ) ( hN n ( by linarith ) ) ⟩;
  · rw [ Metric.tendsto_nhds ] at * ; aesop;
    obtain ⟨ N, hN ⟩ := a ( ε / 2 ) ( half_pos a_1 ) ; exact ⟨ N + 1, fun n hn => by have := hN n ( by linarith ) ; rw [ div_lt_iff₀ ] at * <;> cases abs_cases ( ( n : ℝ ) + 1 ) <;> nlinarith [ show ( n : ℝ ) ≥ N + 1 by norm_cast ] ⟩ ;
  · have h_diff : Filter.Tendsto (fun n : ℕ => ((Finset.filter (fun a => a ∈ B) (Finset.Icc 1 n)).card : ℝ) / (n + 1)) Filter.atTop (nhds 0) := by
      refine' squeeze_zero_norm' _ a;
      filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; gcongr ; linarith;
    simpa [ add_div ] using h_diff.add ( tendsto_one_div_add_atTop_nhds_zero_nat );
  · refine' squeeze_zero_norm' _ a;
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; gcongr ; linarith;
