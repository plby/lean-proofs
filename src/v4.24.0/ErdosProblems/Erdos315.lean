/-

This is a Lean formalization of a solution to Erdős Problem 315.
https://www.erdosproblems.com/forum/thread/315

The original proof was found by: Kamio and Li & Tang

[Ka25] Y. Kamio, Asymptotic analysis of infinite decompositions of a
unit fraction into unit fractions. arXiv:2503.02317 (2025).

[LiTa25] Z. Li and Q. Tang, On a conjecture of Erdős and Graham about
the Sylvester's sequence. arXiv:2503.12277 (2025).


Kamio's proof was auto-formalized by Aristotle (from Harmonic).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We formalized the main theorem of the paper, proving that for any sequence of positive integers $a_i$ summing to $1/n$ and distinct from the generalized Sylvester sequence, the limit inferior of $a_i^{2^{-i}}$ is strictly less than the constant $c_n$. We utilized a shifting argument to reduce the general case to the case where the first term differs from the Sylvester sequence, and handled the limit inferior properties carefully.
-/

import Mathlib

namespace Erdos315


/-
Definition of the generalized Sylvester sequence s_i(n). Note that we use 0-based indexing where index 0 corresponds to s_1 in the paper.
-/
def generalized_sylvester (n : ℕ) : ℕ → ℕ
| 0 => n + 1
| (i + 1) => (generalized_sylvester n i)^2 - (generalized_sylvester n i) + 1

/-
Definition of the sequence s_i(n)^(2^-i) and its limit c_n. Note that we adjusted the exponent to match the 0-based indexing of generalized_sylvester.
-/
noncomputable def sylvester_seq_pow (n : ℕ) (i : ℕ) : ℝ :=
  (generalized_sylvester n i : ℝ) ^ ((1/2 : ℝ) ^ (i + 1))

noncomputable def c (n : ℕ) : ℝ :=
  limUnder Filter.atTop (sylvester_seq_pow n)

/-
The terms of the generalized Sylvester sequence are always positive.
-/
lemma generalized_sylvester_pos (n k : ℕ) : 0 < generalized_sylvester n k := by
  induction' k with k ih <;> [ exact Nat.succ_pos _; exact Nat.pos_of_ne_zero ( by ( erw [ show generalized_sylvester n ( k + 1 ) = ( generalized_sylvester n k ) ^ 2 - ( generalized_sylvester n k ) + 1 from rfl ] ; exact ne_of_gt <| Nat.succ_pos _ ) ) ]

/-
Product formula for the generalized Sylvester sequence: s_j(n) - 1 = n * product_{i<j} s_i(n).
-/
theorem prop_syl_2 (n : ℕ) (j : ℕ) :
  generalized_sylvester n j - 1 = n * ∏ i ∈ Finset.range j, generalized_sylvester n i := by
    induction j <;> simp_all +decide [ Finset.prod_range_succ ];
    · exact Nat.sub_eq_of_eq_add <| by rfl;
    · rw [ show generalized_sylvester n ( _ + 1 ) = ( generalized_sylvester n _ ) ^ 2 - ( generalized_sylvester n _ ) + 1 from rfl ];
      rw [ tsub_eq_of_eq_add ];
      zify at *;
      rw [ Nat.cast_sub ] at * <;> push_cast at * <;> nlinarith [ generalized_sylvester_pos n ‹_› ]

/-
Sum of reciprocals identity: sum_{i<j} 1/s_i(n) + 1/(s_j(n) - 1) = 1/n.
-/
theorem prop_syl_1 (n : ℕ) (hn : 0 < n) (j : ℕ) :
  (∑ i ∈ Finset.range j, (1 : ℝ) / generalized_sylvester n i) + 1 / (generalized_sylvester n j - 1 : ℝ) = 1 / n := by
    induction' j with j ih;
    · norm_num [ generalized_sylvester ];
    · -- Substitute the identity $1/(s_{j+1}(n) - 1) = 1/(s_j(n) - 1) - 1/s_j(n)$ into the equation.
      have h_identity : (1 / (generalized_sylvester n (j + 1) - 1) : ℝ) = (1 / (generalized_sylvester n j - 1) : ℝ) - (1 / (generalized_sylvester n j) : ℝ) := by
        rw [ div_sub_div, div_eq_div_iff ] <;> norm_num [ generalized_sylvester ];
        · rw [ Nat.cast_sub ] <;> push_cast <;> nlinarith only [ show generalized_sylvester n j > 0 from generalized_sylvester_pos n j ];
        · exact ne_of_gt <| Nat.sub_pos_of_lt <| by nlinarith only [ show generalized_sylvester n j > 1 from Nat.recOn j ( by exact Nat.succ_lt_succ hn ) fun i hi => by { rw [ show generalized_sylvester n ( i + 1 ) = ( generalized_sylvester n i ) ^ 2 - ( generalized_sylvester n i ) + 1 from rfl ] ; exact Nat.succ_lt_succ <| Nat.sub_pos_of_lt <| by nlinarith only [ hi ] } ] ;
        · exact ⟨ sub_ne_zero_of_ne <| mod_cast ne_of_gt <| show 1 < generalized_sylvester n j from Nat.recOn j ( by exact Nat.succ_lt_succ hn ) fun i hi => by { rw [ show generalized_sylvester n ( i + 1 ) = ( generalized_sylvester n i ) ^ 2 - ( generalized_sylvester n i ) + 1 from rfl ] ; exact Nat.succ_lt_succ <| Nat.sub_pos_of_lt <| by nlinarith only [ hi ] }, by exact ne_of_gt <| generalized_sylvester_pos n j ⟩;
        · exact sub_ne_zero_of_ne ( ne_of_gt ( mod_cast Nat.one_lt_cast.mpr ( show 1 < generalized_sylvester n j from Nat.recOn j ( by exact Nat.succ_lt_succ hn ) fun i hi => by exact Nat.succ_lt_succ ( Nat.le_sub_of_add_le ( by nlinarith only [ hi, show generalized_sylvester n i > 1 from hi ] ) ) ) ) );
        · exact ne_of_gt <| generalized_sylvester_pos _ _;
      rw [ Finset.sum_range_succ, h_identity ] ; linear_combination ih

/-
Identity for the generalized Sylvester sequence: s_{k+l}(n) = s_l(s_k(n)-1).
-/
theorem prop_syl_3 (n k l : ℕ) :
  generalized_sylvester n (k + l) = generalized_sylvester (generalized_sylvester n k - 1) l := by
    induction' l with l ih generalizing k;
    · exact Eq.symm ( Nat.sub_add_cancel ( generalized_sylvester_pos n k ) );
    · -- By definition of generalized_sylvester, we have:
      have h_def : ∀ n k, generalized_sylvester n (k + 1) = (generalized_sylvester n k)^2 - generalized_sylvester n k + 1 := by
        exact fun n k => rfl;
      grind

/-
The limit c_n exists.
-/
theorem c_exists (n : ℕ) : Filter.Tendsto (sylvester_seq_pow n) Filter.atTop (nhds (c n)) := by
  convert tendsto_nhds_limUnder _;
  have h_decreasing : ∀ i, sylvester_seq_pow n (i + 1) ≤ sylvester_seq_pow n i := by
    intro i
    unfold sylvester_seq_pow
    have h_sylvester_ineq : (generalized_sylvester n (i + 1) : ℝ) ≤ (generalized_sylvester n i : ℝ) ^ 2 := by
      norm_cast;
      exact Nat.le_of_lt_succ ( by rw [ show generalized_sylvester n ( i + 1 ) = ( generalized_sylvester n i ) ^ 2 - ( generalized_sylvester n i ) + 1 from rfl ] ; linarith [ Nat.sub_add_cancel ( show ( generalized_sylvester n i ) ^ 2 ≥ ( generalized_sylvester n i ) from Nat.le_self_pow ( by norm_num ) _ ), Nat.sub_add_cancel ( show ( generalized_sylvester n i ) ^ 2 ≥ ( generalized_sylvester n i ) from Nat.le_self_pow ( by norm_num ) _ ), generalized_sylvester_pos n i ] );
    exact le_trans ( Real.rpow_le_rpow ( by positivity ) h_sylvester_ineq ( by positivity ) ) ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring_nf; norm_num )
  have h_bounded : BddBelow (Set.range (sylvester_seq_pow n)) := by
    exact ⟨ 0, Set.forall_mem_range.mpr fun i => Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ⟩
  have h_converges : Filter.Tendsto (sylvester_seq_pow n) Filter.atTop (nhds (sInf (Set.range (sylvester_seq_pow n)))) := by
    apply_rules [ tendsto_atTop_ciInf ];
    exact antitone_nat_of_succ_le h_decreasing
  use sInf (Set.range (sylvester_seq_pow n))

/-
Identity for the limit constant: c_n^{2^k} = c_{s_k(n)-1}.
-/
theorem prop_syl_4 (n k : ℕ) :
  c n ^ (2 ^ k) = c (generalized_sylvester n k - 1) := by
    -- Taking the limit as $j$ tends to infinity, we have:
    have h_lim : Filter.Tendsto (fun j => (generalized_sylvester n (j + k) : ℝ) ^ ((1 / 2 : ℝ) ^ (j + k + 1 : ℕ) * (2 ^ k : ℝ))) Filter.atTop (nhds (c (generalized_sylvester n k - 1))) := by
      have h_lim : Filter.Tendsto (fun j => (generalized_sylvester (generalized_sylvester n k - 1) j : ℝ) ^ ((1 / 2 : ℝ) ^ (j + 1 : ℕ))) Filter.atTop (nhds (c (generalized_sylvester n k - 1))) := by
        convert c_exists _ using 1;
      convert h_lim using 2 ; norm_num [ prop_syl_3 ] ; ring_nf;
      rw [ ← prop_syl_3 ] ; norm_num;
      rw [ ← prop_syl_3 ] ; norm_num [ mul_assoc, ← mul_pow ];
      ring_nf;
    have h_lim_eq : Filter.Tendsto (fun j => (generalized_sylvester n j : ℝ) ^ ((1 / 2 : ℝ) ^ (j + 1 : ℕ) * (2 ^ k : ℝ))) Filter.atTop (nhds (c (generalized_sylvester n k - 1))) := by
      rw [ ← Filter.tendsto_add_atTop_iff_nat k ] ; aesop;
    convert tendsto_nhds_unique _ h_lim_eq using 1;
    have h_lim_eq : Filter.Tendsto (fun j => ((generalized_sylvester n j : ℝ) ^ ((1 / 2 : ℝ) ^ (j + 1 : ℕ))) ^ (2 ^ k : ℝ)) Filter.atTop (nhds (c n ^ (2 ^ k : ℝ))) := by
      convert Filter.Tendsto.rpow ( c_exists n ) tendsto_const_nhds _ using 1 ; norm_num;
    convert h_lim_eq using 2 ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; ring_nf;
    norm_cast

/-
Base case (n=2) for the sum-product inequality lemma.
-/
lemma sum_ge_of_prod_ge_prod_two (x0 x1 y0 y1 : ℝ)
  (hx0 : 0 < x0)
  (h_mono_y : y1 ≤ y0)
  (h_prod0 : x0 ≥ y0)
  (h_prod1 : x0 * x1 ≥ y0 * y1) :
  x0 + x1 ≥ y0 + y1 := by
    nlinarith

/-
Weak majorization inequality for the exponential function: if partial sums of u are >= partial sums of v, and sequences are decreasing, then sum of exp(u) >= sum of exp(v).
-/
lemma exp_sum_ge_exp_sum (n : ℕ) (u v : ℕ → ℝ)
  (h_mono_u : ∀ i j, i < j → j < n → u j ≤ u i)
  (h_mono_v : ∀ i j, i < j → j < n → v j ≤ v i)
  (h_sum : ∀ k < n, ∑ i ∈ Finset.range (k + 1), u i ≥ ∑ i ∈ Finset.range (k + 1), v i) :
  ∑ i ∈ Finset.range n, Real.exp (u i) ≥ ∑ i ∈ Finset.range n, Real.exp (v i) := by
    -- Applying the summation by parts formula for sequences, we get $\sum_{i=0}^{n-1} a_i b_i = \sum_{i=0}^{n-2} S_i (b_i - b_{i+1}) + S_{n-1} b_{n-1}$ where $S_i = \sum_{j=0}^i a_j$.
    have h_summation_parts (a b : ℕ → ℝ) : ∑ i ∈ Finset.range n, a i * b i = ∑ i ∈ Finset.range (n - 1), (∑ j ∈ Finset.range (i + 1), a j) * (b i - b (i + 1)) + (∑ j ∈ Finset.range n, a j) * b (n - 1) := by
      exact Nat.recOn n ( by norm_num ) fun n ih => by cases n <;> simp_all +decide [ Finset.sum_range_succ ] ; linarith;
    -- Applying the inequality $e^{x} - e^{y} \geq e^{y}(x - y)$ to each term in the sum.
    have h_exp_ineq : ∀ i < n, Real.exp (u i) - Real.exp (v i) ≥ Real.exp (v i) * (u i - v i) := by
      intro i hi; rw [ show Real.exp ( u i ) = Real.exp ( v i ) * Real.exp ( u i - v i ) by rw [ ← Real.exp_add, add_sub_cancel ] ] ; nlinarith [ Real.exp_pos ( v i ), Real.exp_pos ( u i - v i ), Real.add_one_le_exp ( u i - v i ) ] ;
    -- Applying the inequality $e^{x} - e^{y} \geq e^{y}(x - y)$ to each term in the sum, we get $\sum_{i=0}^{n-1} (e^{u_i} - e^{v_i}) \geq \sum_{i=0}^{n-1} e^{v_i} (u_i - v_i)$.
    have h_sum_exp_ineq : ∑ i ∈ Finset.range n, (Real.exp (u i) - Real.exp (v i)) ≥ ∑ i ∈ Finset.range n, Real.exp (v i) * (u i - v i) := by
      exact Finset.sum_le_sum fun i hi => h_exp_ineq i <| Finset.mem_range.mp hi;
    -- Applying the summation by parts formula to the sum $\sum_{i=0}^{n-1} e^{v_i} (u_i - v_i)$.
    have h_summation_parts_exp_v : ∑ i ∈ Finset.range n, Real.exp (v i) * (u i - v i) = ∑ i ∈ Finset.range (n - 1), (∑ j ∈ Finset.range (i + 1), (u j - v j)) * (Real.exp (v i) - Real.exp (v (i + 1))) + (∑ j ∈ Finset.range n, (u j - v j)) * Real.exp (v (n - 1)) := by
      convert h_summation_parts ( fun i => u i - v i ) ( fun i => Real.exp ( v i ) ) using 1;
      ac_rfl;
    -- Since $\sum_{j=0}^{i} (u_j - v_j) \geq 0$ for all $i < n$, we have $\sum_{i=0}^{n-1} (\sum_{j=0}^{i} (u_j - v_j)) * (e^{v_i} - e^{v_{i+1}}) \geq 0$.
    have h_nonneg : ∑ i ∈ Finset.range (n - 1), (∑ j ∈ Finset.range (i + 1), (u j - v j)) * (Real.exp (v i) - Real.exp (v (i + 1))) ≥ 0 := by
      exact Finset.sum_nonneg fun i hi => mul_nonneg ( by simpa using h_sum i ( Nat.lt_of_lt_of_le ( Finset.mem_range.mp hi ) ( Nat.pred_le _ ) ) ) ( sub_nonneg.mpr ( Real.exp_le_exp.mpr ( h_mono_v _ _ ( Nat.lt_succ_self _ ) ( Nat.lt_pred_iff.mp ( Finset.mem_range.mp hi ) ) ) ) );
    rcases n <;> simp_all +decide [ Finset.sum_range_succ ];
    nlinarith [ h_sum _ ( Nat.lt_succ_self _ ), Real.exp_pos ( v ‹_› ) ]

/-
Helper lemma for Lemma 6: If partial products of x are >= partial products of y, and sequences are decreasing and positive, then sum of x >= sum of y. This is proven by transforming to the log domain and using the exponential majorization lemma.
-/
lemma sum_ge_of_prod_ge_prod (n : ℕ) (x y : ℕ → ℝ)
  (hx_pos : ∀ i < n, 0 < x i) (hy_pos : ∀ i < n, 0 < y i)
  (hx_mono : ∀ i j, i < j → j < n → x j ≤ x i)
  (hy_mono : ∀ i j, i < j → j < n → y j ≤ y i)
  (h_prod : ∀ k < n, ∏ i ∈ Finset.range (k + 1), x i ≥ ∏ i ∈ Finset.range (k + 1), y i) :
  ∑ i ∈ Finset.range n, x i ≥ ∑ i ∈ Finset.range n, y i := by
    -- By log-majorization, we can apply the exponential majorization lemma.
    have h_exp : ∑ i ∈ Finset.range n, Real.exp (Real.log (x i)) ≥ ∑ i ∈ Finset.range n, Real.exp (Real.log (y i)) := by
      apply exp_sum_ge_exp_sum;
      · exact fun i j hij hj => Real.log_le_log ( hx_pos _ hj ) ( hx_mono _ _ hij hj );
      · exact fun i j hij hjn => Real.log_le_log ( hy_pos _ hjn ) ( hy_mono _ _ hij hjn );
      · intro k hk; have := h_prod k hk; rw [ ← Real.log_prod _ _ fun i hi => ne_of_gt ( hx_pos i <| by linarith [ Finset.mem_range.mp hi ] ), ← Real.log_prod _ _ fun i hi => ne_of_gt ( hy_pos i <| by linarith [ Finset.mem_range.mp hi ] ) ] ; exact Real.log_le_log ( Finset.prod_pos fun i hi => hy_pos i <| by linarith [ Finset.mem_range.mp hi ] ) this;
    exact le_trans ( Finset.sum_le_sum fun i hi => by rw [ Real.exp_log ( hy_pos i ( Finset.mem_range.mp hi ) ) ] ) ( h_exp.trans ( Finset.sum_le_sum fun i hi => by rw [ Real.exp_log ( hx_pos i ( Finset.mem_range.mp hi ) ) ] ) )

/-
Lemma 6 from the paper: Comparison lemma for sums of sequences. Assumes C > 0.
-/
lemma pac_sou (C : ℝ) (t : ℕ) (u_seq v_seq : ℕ → ℝ)
  (hC_pos : 0 < C)
  (hu_pos : ∀ i, 0 < u_seq i) (hv_pos : ∀ i, 0 < v_seq i)
  (hu_mono : Antitone u_seq) (hv_mono : Antitone v_seq)
  (h_eq : ∀ k ≥ t, ∑ i ∈ Finset.range k, u_seq i + C * ∏ i ∈ Finset.range k, u_seq i = C)
  (h_le : ∀ k ≥ t, ∑ i ∈ Finset.range k, v_seq i + C * ∏ i ∈ Finset.range k, v_seq i ≤ C)
  (h_init : ∀ i < t, v_seq i ≤ u_seq i) :
  ∀ k, ∑ i ∈ Finset.range k, v_seq i ≤ ∑ i ∈ Finset.range k, u_seq i := by
    -- Let's choose any $k$ greater than $t$ and derive a contradiction.
    by_contra h_contra;
    -- Let's choose the smallest $k \geq t$ such that $\sum_{i=0}^{k-1} v_i > \sum_{i=0}^{k-1} u_i$.
    obtain ⟨k, hk_ge_t, hk_gt⟩ : ∃ k ≥ t, (∑ i ∈ Finset.range k, v_seq i) > (∑ i ∈ Finset.range k, u_seq i) ∧ ∀ j < k, j ≥ t → (∑ i ∈ Finset.range j, v_seq i) ≤ (∑ i ∈ Finset.range j, u_seq i) := by
      have h_exists_k : ∃ k ≥ t, (∑ i ∈ Finset.range k, v_seq i) > (∑ i ∈ Finset.range k, u_seq i) := by
        simp +zetaDelta at *;
        exact h_contra.imp fun k hk => ⟨ le_of_not_gt fun hk' => hk.not_ge <| Finset.sum_le_sum fun i hi => h_init i <| by linarith [ Finset.mem_range.mp hi ], hk ⟩;
      exact ⟨ Nat.find h_exists_k, Nat.find_spec h_exists_k |>.1, Nat.find_spec h_exists_k |>.2, by aesop ⟩;
    -- Since $v_k > u_k$, there must exist some $m$ such that $\prod_{i=m}^{k-1} v_i < \prod_{i=m}^{k-1} u_i$.
    obtain ⟨m, hm₁, hm₂⟩ : ∃ m < k, (∏ i ∈ Finset.Ico m k, v_seq i) < (∏ i ∈ Finset.Ico m k, u_seq i) ∧ ∀ j, m < j → j < k → (∏ i ∈ Finset.Ico j k, v_seq i) ≥ (∏ i ∈ Finset.Ico j k, u_seq i) := by
      have hm_exists : ∃ m < k, (∏ i ∈ Finset.Ico m k, v_seq i) < (∏ i ∈ Finset.Ico m k, u_seq i) := by
        exact ⟨ 0, Nat.pos_of_ne_zero ( by rintro rfl; norm_num at * ), by have := h_eq k hk_ge_t; have := h_le k hk_ge_t; norm_num [ Finset.prod_range_succ ] at *; nlinarith ⟩;
      obtain ⟨m, hm₁⟩ : ∃ m < k, (∏ i ∈ Finset.Ico m k, v_seq i) < (∏ i ∈ Finset.Ico m k, u_seq i) ∧ ∀ j, m < j → j < k → (∏ i ∈ Finset.Ico j k, v_seq i) ≥ (∏ i ∈ Finset.Ico j k, u_seq i) := by
        have h_max : ∃ m ∈ Finset.filter (fun m => (∏ i ∈ Finset.Ico m k, v_seq i) < (∏ i ∈ Finset.Ico m k, u_seq i)) (Finset.range k), ∀ j ∈ Finset.filter (fun m => (∏ i ∈ Finset.Ico m k, v_seq i) < (∏ i ∈ Finset.Ico m k, u_seq i)) (Finset.range k), m ≥ j := by
          exact ⟨ Finset.max' ( Finset.filter ( fun m => ∏ i ∈ Finset.Ico m k, v_seq i < ∏ i ∈ Finset.Ico m k, u_seq i ) ( Finset.range k ) ) ⟨ hm_exists.choose, Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr hm_exists.choose_spec.1, hm_exists.choose_spec.2 ⟩ ⟩, Finset.max'_mem _ _, fun j hj => Finset.le_max' _ _ hj ⟩
        obtain ⟨ m, hm₁, hm₂ ⟩ := h_max; exact ⟨ m, Finset.mem_range.mp ( Finset.mem_filter.mp hm₁ |>.1 ), Finset.mem_filter.mp hm₁ |>.2, fun j hj₁ hj₂ => not_lt.1 fun hj₃ => not_lt_of_ge ( hm₂ j ( Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr hj₂, hj₃ ⟩ ) ) hj₁ ⟩ ;
      use m;
    -- Applying the helper lemma `sum_ge_of_prod_ge_prod` to the sequences $u$ and $v$ restricted to the range $[m, k-1]$.
    have h_sum_ge : ∑ i ∈ Finset.Ico m k, v_seq i ≤ ∑ i ∈ Finset.Ico m k, u_seq i := by
      have h_sum_ge : ∀ j ∈ Finset.Ico m k, (∏ i ∈ Finset.Ico m (j + 1), v_seq i) ≤ (∏ i ∈ Finset.Ico m (j + 1), u_seq i) := by
        intro j hj;
        by_cases hjk : j + 1 < k;
        · have := hm₂.2 ( j + 1 ) ( by linarith [ Finset.mem_Ico.mp hj ] ) hjk;
          have h_prod_le : (∏ i ∈ Finset.Ico m k, v_seq i) = (∏ i ∈ Finset.Ico m (j + 1), v_seq i) * (∏ i ∈ Finset.Ico (j + 1) k, v_seq i) ∧ (∏ i ∈ Finset.Ico m k, u_seq i) = (∏ i ∈ Finset.Ico m (j + 1), u_seq i) * (∏ i ∈ Finset.Ico (j + 1) k, u_seq i) := by
            exact ⟨ by rw [ Finset.prod_Ico_consecutive ] <;> linarith [ Finset.mem_Ico.mp hj ], by rw [ Finset.prod_Ico_consecutive ] <;> linarith [ Finset.mem_Ico.mp hj ] ⟩;
          nlinarith [ show 0 < ∏ i ∈ Finset.Ico m ( j + 1 ), v_seq i from Finset.prod_pos fun i hi => hv_pos i, show 0 < ∏ i ∈ Finset.Ico m ( j + 1 ), u_seq i from Finset.prod_pos fun i hi => hu_pos i, show 0 < ∏ i ∈ Finset.Ico ( j + 1 ) k, v_seq i from Finset.prod_pos fun i hi => hv_pos i, show 0 < ∏ i ∈ Finset.Ico ( j + 1 ) k, u_seq i from Finset.prod_pos fun i hi => hu_pos i ];
        · norm_num [ show j + 1 = k by linarith [ Finset.mem_Ico.mp hj ] ] at * ; linarith;
      have h_sum_ge : ∀ j ∈ Finset.Ico m k, (∏ i ∈ Finset.range (j - m + 1), v_seq (m + i)) ≤ (∏ i ∈ Finset.range (j - m + 1), u_seq (m + i)) := by
        intro j hj; convert h_sum_ge j hj using 1 <;> simp +decide [ Finset.prod_Ico_eq_prod_range ] ;
        · rw [ Nat.sub_add_comm ( by linarith [ Finset.mem_Ico.mp hj ] ) ];
        · rw [ Nat.sub_add_comm ( by linarith [ Finset.mem_Ico.mp hj ] ) ];
      have h_sum_ge : ∑ i ∈ Finset.range (k - m), v_seq (m + i) ≤ ∑ i ∈ Finset.range (k - m), u_seq (m + i) := by
        apply sum_ge_of_prod_ge_prod;
        · exact fun i hi => hu_pos _;
        · exact fun i hi => hv_pos _;
        · exact fun i j hij hj => hu_mono <| by linarith;
        · exact fun i j hij hj => hv_mono <| by linarith;
        · intro j hj; specialize h_sum_ge ( m + j ) ( Finset.mem_Ico.mpr ⟨ by linarith, by linarith [ Nat.sub_add_cancel hm₁.le ] ⟩ ) ; aesop;
      simpa only [ Finset.sum_Ico_eq_sum_range, add_comm ] using h_sum_ge;
    -- By the induction hypothesis, we have $\sum_{i=0}^{m-1} v_i \leq \sum_{i=0}^{m-1} u_i$.
    have h_ind : ∑ i ∈ Finset.range m, v_seq i ≤ ∑ i ∈ Finset.range m, u_seq i := by
      by_cases hm : m < t;
      · exact Finset.sum_le_sum fun i hi => h_init i <| by linarith [ Finset.mem_range.mp hi ] ;
      · exact hk_gt.2 m hm₁ ( by linarith );
    exact hk_gt.1.not_ge ( by rw [ ← Finset.sum_range_add_sum_Ico _ hm₁.le, ← Finset.sum_range_add_sum_Ico _ hm₁.le ] ; linarith )

/-
Definition of l and the comparison sequence u_i for n > 1. Note 0-based indexing: u_0 corresponds to u_1 in paper.
-/
def l_val (n : ℕ) : ℕ := n * (n + 1)^2 * (n + 2) / 2

noncomputable def u_seq_general (n : ℕ) (i : ℕ) : ℝ :=
  if i = 0 then 1 / (n + 2 : ℝ)
  else if i = 1 then 2 / ((n + 1 : ℝ) ^ 2)
  else 1 / (generalized_sylvester (l_val n) (i - 2) : ℝ)

/-
The comparison sequence u_i satisfies the conditions of Lemma 6 (pac_sou) for n >= 2.
-/
lemma u_seq_satisfies_pac_sou (n : ℕ) (hn : 2 ≤ n) :
  let u := u_seq_general n
  let C := 1 / (n : ℝ)
  (∀ i, 0 < u i) ∧
  Antitone u ∧
  (∀ k ≥ 2, ∑ i ∈ Finset.range k, u i + C * ∏ i ∈ Finset.range k, u i = C) := by
    refine' ⟨ _, _, _ ⟩;
    · unfold u_seq_general;
      intro i; split_ifs <;> first | positivity | exact one_div_pos.mpr <| Nat.cast_pos.mpr <| generalized_sylvester_pos _ _;
    · refine' antitone_nat_of_succ_le _;
      intro i_general;
      rcases i_general with ( _ | _ | i_general ) <;> unfold u_seq_general <;> norm_num;
      · rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_cast <;> nlinarith;
      · rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_cast <;> norm_num [ generalized_sylvester ];
        unfold l_val;
        nlinarith [ Nat.div_add_mod ( n * ( n + 1 ) ^ 2 * ( n + 2 ) ) 2, Nat.mod_lt ( n * ( n + 1 ) ^ 2 * ( n + 2 ) ) two_pos, pow_pos ( by linarith : 0 < n ) 3 ];
      · gcongr <;> norm_num;
        · exact generalized_sylvester_pos _ _;
        · simp +arith +decide [ generalized_sylvester ];
          nlinarith [ Nat.sub_add_cancel ( show generalized_sylvester ( l_val n ) i_general ≤ generalized_sylvester ( l_val n ) i_general ^ 2 from Nat.le_self_pow ( by norm_num ) _ ) ];
    · intro k hk;
      -- We'll use induction to prove that the equation holds for all $k \geq 2$.
      induction' hk with k ih;
      · unfold u_seq_general ; norm_num [ Finset.sum_range_succ, Finset.prod_range_succ ] ; ring_nf;
        -- Combine and simplify the terms on the left-hand side.
        field_simp
        ring;
      · -- For the inductive step, we need to show that $u_k = C \prod_{i=0}^{k-1} u_i (1 - u_k)$.
        have h_ind_step : u_seq_general n k = (1 / (n : ℝ)) * (∏ i ∈ Finset.range k, u_seq_general n i) * (1 - u_seq_general n k) := by
          rcases k with ( _ | _ | k ) <;> norm_num [ Finset.sum_range_succ', Finset.prod_range_succ', u_seq_general ] at *;
          -- By definition of $generalized_sylvester$, we know that $generalized_sylvester (l_val n) k - 1 = l_val n * \prod_{i=0}^{k-1} generalized_sylvester (l_val n) i$.
          have h_sylvester : ∀ k, (generalized_sylvester (l_val n) k - 1 : ℝ) = l_val n * (∏ i ∈ Finset.range k, (generalized_sylvester (l_val n) i : ℝ)) := by
            intro k; norm_cast; induction k <;> simp_all +decide [ Finset.prod_range_succ ] ;
            · rw [ Int.subNatNat_eq_coe ] ; norm_num [ generalized_sylvester ];
            · simp_all +decide [ Int.subNatNat_eq_coe, generalized_sylvester ];
              rw [ Nat.cast_sub ] <;> push_cast <;> nlinarith [ show 0 < generalized_sylvester ( l_val n ) ‹_› from generalized_sylvester_pos _ _ ];
          field_simp;
          rw [ div_eq_div_iff ];
          · rw [ one_sub_div ] <;> norm_num;
            · rw [ h_sylvester ] ; ring_nf!;
              norm_num [ show generalized_sylvester ( l_val n ) k ≠ 0 from ne_of_gt ( mod_cast generalized_sylvester_pos _ _ ) ] ; ring_nf!;
              rw [ show l_val n = n * ( n + 1 ) ^ 2 * ( n + 2 ) / 2 from rfl ] ; rw [ Nat.cast_div ] <;> norm_num ; ring;
              norm_num [ ← even_iff_two_dvd, mul_add, parity_simps ];
              exact Or.inl <| Nat.even_or_odd n;
            · exact ne_of_gt <| generalized_sylvester_pos _ _;
          · exact ne_of_gt <| Nat.cast_pos.mpr <| generalized_sylvester_pos _ _;
          · exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| ne_of_gt <| generalized_sylvester_pos _ _;
        rw [ Finset.sum_range_succ, Finset.prod_range_succ ];
        grind

/-
If partial sums of v are <= partial sums of u, and total sums are equal, then v_k >= u_k for infinitely many k.
-/
lemma infinitely_often_ge_of_sum_le_sum_eq (u v : ℕ → ℝ)
  (h_sum_le : ∀ k, ∑ i ∈ Finset.range k, v i ≤ ∑ i ∈ Finset.range k, u i)
  (h_sum_eq : ∑' i, v i = ∑' i, u i)
  (hu_summable : Summable u) (hv_summable : Summable v) :
  ∀ N, ∃ k ≥ N, v k ≥ u k := by
    intro N;
    contrapose! h_sum_eq;
    rw [ ← Summable.sum_add_tsum_nat_add N ];
    · rw [ show ( ∑' i : ℕ, u i ) = ∑ i ∈ Finset.range N, u i + ∑' i : ℕ, u ( i + N ) from ?_ ];
      · refine' ne_of_lt ( add_lt_add_of_le_of_lt ( h_sum_le N ) ( _ ) );
        apply_rules [ Summable.tsum_lt_tsum ];
        · exact fun n => le_of_lt ( h_sum_eq _ ( Nat.le_add_left _ _ ) );
        · linarith;
        · exact hv_summable.comp_injective ( add_left_injective N );
        · exact hu_summable.comp_injective ( add_left_injective N );
      · rw [ ← Summable.sum_add_tsum_nat_add ];
        exact hu_summable;
    · exact hv_summable

/-
Definition of the lower bound sequence (s_i(n)-1)^(2^-i). Note the exponent adjustment for 0-based indexing.
-/
noncomputable def lower_seq (n : ℕ) (i : ℕ) : ℝ :=
  ((generalized_sylvester n i : ℝ) - 1) ^ ((1/2 : ℝ) ^ (i + 1))

/-
The sequence s_i(n)^(2^{-(i+1)}) is strictly decreasing.
-/
lemma upper_seq_decreasing (n : ℕ) (hn : 0 < n) :
  StrictAnti (sylvester_seq_pow n) := by
    -- We need to show that $s_{i+1}^{2^{-(i+2)}} < s_i^{2^{-(i+1)}}$.
    have h_ineq : ∀ i, ((generalized_sylvester n (i + 1) : ℝ) ^ ((1 / 2 : ℝ) ^ (i + 2))) < ((generalized_sylvester n i : ℝ) ^ ((1 / 2 : ℝ) ^ (i + 1))) := by
      -- Raising both sides to the power $2^{i+2}$, we get $s_{i+1} < s_i^2$.
      have h_exp : ∀ i, ((generalized_sylvester n (i + 1) : ℝ)) < ((generalized_sylvester n i : ℝ)) ^ 2 := by
        intro i; norm_cast; rw [ show generalized_sylvester n ( i + 1 ) = ( generalized_sylvester n i ) ^ 2 - generalized_sylvester n i + 1 from rfl ] ; nlinarith [ Nat.sub_add_cancel ( show generalized_sylvester n i ≤ ( generalized_sylvester n i ) ^ 2 from Nat.le_self_pow ( by norm_num ) _ ), show 1 < generalized_sylvester n i from Nat.recOn i ( by exact Nat.succ_lt_succ hn ) fun i hi => by rw [ show generalized_sylvester n ( i + 1 ) = ( generalized_sylvester n i ) ^ 2 - generalized_sylvester n i + 1 from rfl ] ; nlinarith [ Nat.sub_add_cancel ( show generalized_sylvester n i ≤ ( generalized_sylvester n i ) ^ 2 from Nat.le_self_pow ( by norm_num ) _ ) ] ] ;
      -- Applying the property of exponents that $(a^b)^c = a^{bc}$, we can rewrite the inequality.
      intro i
      have : ((generalized_sylvester n (i + 1) : ℝ)) ^ ((1 / 2 : ℝ) ^ (i + 2)) < ((generalized_sylvester n i : ℝ) ^ 2) ^ ((1 / 2 : ℝ) ^ (i + 2)) := by
        exact Real.rpow_lt_rpow ( Nat.cast_nonneg _ ) ( h_exp i ) ( by positivity );
      exact this.trans_eq ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; ring_nf );
    exact strictAnti_nat_of_succ_lt fun i => h_ineq i

/-
The sequence (s_i(n)-1)^(2^{-(i+1)}) is strictly increasing.
-/
lemma lower_seq_increasing (n : ℕ) (hn : 0 < n) :
  StrictMono (lower_seq n) := by
    refine' strictMono_nat_of_lt_succ _;
    intro i;
    -- We need to show that $(s_{i+1}-1)^{2^{-(i+2)}} > (s_i-1)^{2^{-(i+1)}}$.
    have h_exp : ((generalized_sylvester n (i + 1) - 1) : ℝ) > ((generalized_sylvester n i - 1) : ℝ) ^ 2 := by
      -- By definition of $generalized_sylvester$, we have $generalized_sylvester n (i + 1) = (generalized_sylvester n i)^2 - generalized_sylvester n i + 1$.
      have h_def : generalized_sylvester n (i + 1) = (generalized_sylvester n i : ℝ)^2 - (generalized_sylvester n i : ℝ) + 1 := by
        norm_cast;
        rw [ Int.subNatNat_eq_coe ] ; push_cast ; ring_nf!;
        rw [ add_comm 1 i ] ; exact eq_add_of_sub_eq' ( by rw [ show generalized_sylvester n ( i + 1 ) = ( generalized_sylvester n i : ℕ ) ^ 2 - ( generalized_sylvester n i : ℕ ) + 1 from rfl ] ; rw [ Nat.cast_add, Nat.cast_sub <| Nat.le_self_pow ( by norm_num ) _ ] ; push_cast ; ring ) ;
      linarith [ show ( generalized_sylvester n i : ℝ ) > 1 from mod_cast Nat.recOn i ( by exact Nat.succ_lt_succ hn ) fun i hi => by { exact Nat.succ_lt_succ ( Nat.sub_pos_of_lt ( by nlinarith only [ hi ] ) ) } ];
    -- Raising both sides to the power of $2^{-(i+2)}$, we get $(s_{i+1}-1)^{2^{-(i+2)}} > (s_i-1)^{2^{-(i+1)}}$.
    have h_exp_pow : ((generalized_sylvester n (i + 1) - 1) : ℝ) ^ ((1 / 2 : ℝ) ^ (i + 2)) > ((generalized_sylvester n i - 1) : ℝ) ^ ((1 / 2 : ℝ) ^ (i + 1)) := by
      refine' lt_of_le_of_lt _ ( Real.rpow_lt_rpow ( _ ) h_exp ( by positivity ) );
      · rw [ ← Real.rpow_natCast _ 2, ← Real.rpow_mul ( sub_nonneg_of_le <| mod_cast Nat.one_le_iff_ne_zero.mpr <| ne_of_gt <| generalized_sylvester_pos _ _ ) ] ; ring_nf ; norm_num;
      · positivity;
    exact h_exp_pow

/-
The lower bound sequence converges to c_n.
-/
lemma lower_seq_tendsto_c (n : ℕ) (hn : 0 < n) :
  Filter.Tendsto (lower_seq n) Filter.atTop (nhds (c n)) := by
    -- We show that the ratio `lower_seq n i / sylvester_seq_pow n i` tends to 1.
    have h_lower_over_upper_tendsto_one (n : ℕ) (hn : 0 < n) : Filter.Tendsto (fun i => lower_seq n i / sylvester_seq_pow n i) Filter.atTop (nhds 1) := by
      -- We show that the ratio `((generalized_sylvester n i - 1) / generalized_sylvester n i) ^ (1/2^(i+1))` tends to 1.
      have h_ratio_tendsto_one (n : ℕ) (hn : 0 < n) : Filter.Tendsto (fun i => ((generalized_sylvester n i - 1 : ℝ) / generalized_sylvester n i) ^ (1 / 2 ^ (i + 1) : ℝ)) Filter.atTop (nhds 1) := by
        -- We'll use that `generalized_sylvester n i` grows very rapidly to show that `1 / generalized_sylvester n i` tends to 0.
        have h_one_over_sylvester_zero (n : ℕ) (hn : 0 < n) : Filter.Tendsto (fun i => 1 / (generalized_sylvester n i : ℝ)) Filter.atTop (nhds 0) := by
          -- We'll use that `generalized_sylvester n i` grows very rapidly to show that `1 / generalized_sylvester n i` tends to 0.
          have h_sylvester_growth : ∀ i, generalized_sylvester n i ≥ i + 2 := by
            intro i;
            induction' i with i ih;
            · exact Nat.succ_le_succ hn;
            · exact Nat.succ_le_of_lt ( by erw [ show generalized_sylvester n ( i + 1 ) = ( generalized_sylvester n i ) ^ 2 - ( generalized_sylvester n i ) + 1 from rfl ] ; nlinarith [ Nat.sub_add_cancel ( show ( generalized_sylvester n i ) ^ 2 ≥ ( generalized_sylvester n i ) from Nat.le_self_pow ( by norm_num ) _ ) ] );
          exact tendsto_const_nhds.div_atTop <| tendsto_natCast_atTop_atTop.comp <| Filter.tendsto_atTop_mono ( fun i => by linarith [ h_sylvester_growth i ] ) tendsto_natCast_atTop_atTop;
        convert Filter.Tendsto.rpow ( h_one_over_sylvester_zero n hn |> Filter.Tendsto.const_sub 1 ) ( tendsto_inv_atTop_zero.comp ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 1 ) ) _ using 2 <;> norm_num;
        rw [ sub_div, inv_eq_one_div, div_self ( Nat.cast_ne_zero.mpr <| ne_of_gt <| generalized_sylvester_pos _ _ ) ];
        grind;
      simp_all +decide [ lower_seq, sylvester_seq_pow ];
      refine' Filter.Tendsto.congr' _ ( h_ratio_tendsto_one n hn );
      filter_upwards [ Filter.eventually_gt_atTop 0 ] with i hi using Real.div_rpow ( sub_nonneg.mpr <| mod_cast Nat.one_le_iff_ne_zero.mpr <| ne_of_gt <| generalized_sylvester_pos n i ) ( Nat.cast_nonneg _ ) _
    -- This follows from the fact that `generalized_sylvester n i` grows very rapidly.;
    convert Filter.Tendsto.mul ( c_exists n ) ( h_lower_over_upper_tendsto_one n hn ) using 1 <;> norm_num [ mul_comm ];
    exact funext fun i => by rw [ mul_div_cancel₀ _ ( ne_of_gt ( by exact Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( generalized_sylvester_pos _ _ ) ) _ ) ) ] ;

/-
Bounds for the limit constant c_n: sqrt(n) < c_n < sqrt(n+1).
-/
lemma c_bounds (n : ℕ) (hn : 0 < n) : Real.sqrt n < c n ∧ c n < Real.sqrt (n + 1) := by
  constructor;
  · -- By definition of $c_n$, we know that $c_n > \sqrt{n}$.
    have h_lower_bound : Filter.Tendsto (lower_seq n) Filter.atTop (nhds (c n)) := by
      exact lower_seq_tendsto_c n hn;
    -- Since $lower\_seq n$ is strictly increasing and converges to $c n$, we have $lower\_seq n 0 < c n$.
    have h_lower_bound_0 : lower_seq n 0 < c n := by
      exact lt_of_lt_of_le ( lower_seq_increasing n hn |> StrictMono.lt_iff_lt |> Iff.mpr <| Nat.zero_lt_one ) <| le_of_tendsto_of_tendsto tendsto_const_nhds h_lower_bound <| Filter.eventually_atTop.mpr ⟨ 1, fun k hk => lower_seq_increasing n hn |> StrictMono.monotone <| by linarith ⟩;
    convert h_lower_bound_0 using 1 ; unfold lower_seq ; norm_num [ generalized_sylvester ];
    rw [ Real.sqrt_eq_rpow ];
  · -- Since $sylvester_seq_pow n$ is strictly decreasing and converges to $c n$, we have $c n < sylvester_seq_pow n 0$.
    have h_c_lt_sylvester_seq_pow_n_0 : c n < sylvester_seq_pow n 0 := by
      have := @upper_seq_decreasing n hn;
      exact lt_of_le_of_lt ( le_of_tendsto ( c_exists n ) ( Filter.eventually_atTop.mpr ⟨ 1, fun k hk => this.antitone hk ⟩ ) ) ( this ( Nat.zero_lt_one ) );
    convert h_c_lt_sylvester_seq_pow_n_0 using 1 ; norm_num [ sylvester_seq_pow ];
    rw [ ← Real.sqrt_eq_rpow, show ( generalized_sylvester n 0 : ℝ ) = n + 1 by exact_mod_cast rfl ]

/-
Corrected definition of the comparison sequence u_i for n > 1. u_i = 1/s_{i-2}(l) for i >= 2.
-/
noncomputable def u_seq (n : ℕ) (i : ℕ) : ℝ :=
  if i = 0 then 1 / (n + 2 : ℝ)
  else if i = 1 then 2 / ((n + 1 : ℝ) ^ 2)
  else 1 / (generalized_sylvester (l_val n) (i - 2) : ℝ)

/-
The comparison sequence u_i satisfies the conditions of Lemma 6.
-/
lemma u_seq_satisfies_pac_sou_correct (n : ℕ) (hn : 2 ≤ n) :
  let u := u_seq_general n
  let C := 1 / (n : ℝ)
  (∀ i, 0 < u i) ∧
  Antitone u ∧
  (∀ k ≥ 2, ∑ i ∈ Finset.range k, u i + C * ∏ i ∈ Finset.range k, u i = C) := by
    convert u_seq_satisfies_pac_sou n hn using 1

/-
Base case equation for u_seq (k=2).
-/
lemma u_base_case (n : ℕ) (hn : 0 < n) :
  u_seq n 0 + u_seq n 1 + (1 / (n : ℝ)) * u_seq n 0 * u_seq n 1 = 1 / (n : ℝ) := by
    unfold u_seq; norm_num; ring_nf;
    -- Combine and simplify the terms on the left-hand side.
    field_simp
    ring

/-
Monotonicity of the comparison sequence u_seq.
-/
lemma u_seq_antitone (n : ℕ) (hn : 2 ≤ n) :
  Antitone (u_seq n) := by
    convert u_seq_satisfies_pac_sou_correct n hn |>.2.1 using 1

/-
Key identity: C * u_0 * u_1 = 1/l.
-/
lemma u_prod_init_eq_inv_l (n : ℕ) (hn : 0 < n) :
  (1 / (n : ℝ)) * u_seq n 0 * u_seq n 1 = 1 / (l_val n : ℝ) := by
    unfold u_seq l_val;
    rw [ Nat.cast_div ] <;> norm_num <;> ring_nf;
    · grind;
    · norm_num [ ← even_iff_two_dvd, parity_simps ]

/-
Helper lemma: Product of u_seq terms relates to Sylvester sequence product.
-/
lemma u_prod_eq_syl_prod (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k ≥ 2) :
  (1 / (n : ℝ)) * ∏ i ∈ Finset.range k, u_seq n i = 1 / (l_val n * ∏ j ∈ Finset.range (k - 2), (generalized_sylvester (l_val n) j : ℝ)) := by
    -- We split the product into the initial part (i=0, 1) and the rest (i >= 2).
    have h_split : (∏ i ∈ Finset.range k, u_seq n i) = (u_seq n 0) * (u_seq n 1) * (∏ j ∈ Finset.range (k - 2), (1 / (generalized_sylvester (l_val n) j : ℝ))) := by
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ Finset.prod_range_succ' ];
      rw [ Finset.prod_congr rfl fun i hi => show u_seq n ( i + 1 + 1 ) = ( ( generalized_sylvester ( l_val n ) i : ℝ ) ) ⁻¹ from ?_ ] ; ring_nf!;
      · norm_num [ mul_assoc, mul_comm, mul_left_comm, Finset.prod_mul_distrib ];
      · unfold u_seq; aesop;
    simp_all +decide [ mul_assoc, mul_comm ];
    convert congr_arg ( · * ( ∏ x ∈ Finset.range ( k - 2 ), ( generalized_sylvester ( l_val n ) x : ℝ ) ) ⁻¹ ) ( u_prod_init_eq_inv_l n hn ) using 1 ; ring;
    ring

/-
Inductive step equation for u_seq.
-/
lemma u_inductive_step_eq (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (hk : k ≥ 2) :
  u_seq n k / (1 - u_seq n k) = (1 / (n : ℝ)) * ∏ i ∈ Finset.range k, u_seq n i := by
    -- Substitute the value of $u_k$ and simplify the left-hand side.
    have h_lhs : u_seq n k / (1 - u_seq n k) = 1 / (generalized_sylvester (l_val n) (k - 2) - 1 : ℝ) := by
      rcases k with ( _ | _ | k ) <;> norm_num [ u_seq ] at *;
      rw [ inv_eq_one_div, div_div, mul_sub, mul_one, mul_div_cancel₀ _ ( Nat.cast_ne_zero.mpr <| ne_of_gt <| generalized_sylvester_pos _ _ ) ] ; ring;
    -- Using `u_prod_eq_syl_prod` with index k (range k), RHS = 1 / (l * prod_{j=0}^{k-3} s_j(l)).
    have h_rhs : (1 / (n : ℝ)) * ∏ i ∈ Finset.range k, u_seq n i = 1 / (l_val n * ∏ j ∈ Finset.range (k - 2), (generalized_sylvester (l_val n) j : ℝ)) := by
      convert u_prod_eq_syl_prod n ( by linarith ) k hk using 1;
    -- Using `prop_syl_2` applied to n=l and j=k-2, we get s_{k-2}(l) - 1 = l * prod_{j=0}^{k-3} s_j(l).
    have h_syl_prod : (generalized_sylvester (l_val n) (k - 2) : ℝ) - 1 = (l_val n : ℝ) * ∏ j ∈ Finset.range (k - 2), (generalized_sylvester (l_val n) j : ℝ) := by
      convert congr_arg ( ( ↑ ) : ℕ → ℝ ) ( prop_syl_2 ( l_val n ) ( k - 2 ) ) using 1;
      · rw [ Nat.cast_sub ] <;> norm_num ; exact Nat.one_le_iff_ne_zero.mpr <| ne_of_gt <| generalized_sylvester_pos _ _;
      · norm_cast;
    grind

/-
The comparison sequence u_i satisfies the conditions of Lemma 6 for n >= 2.
-/
lemma u_seq_satisfies_pac_sou_final (n : ℕ) (hn : 2 ≤ n) :
  let u := u_seq n
  let C := 1 / (n : ℝ)
  (∀ i, 0 < u i) ∧
  Antitone u ∧
  (∀ k ≥ 2, ∑ i ∈ Finset.range k, u i + C * ∏ i ∈ Finset.range k, u i = C) := by
    apply u_seq_satisfies_pac_sou_correct n hn

/-
Bounds for the limit constant c_n: sqrt(n) < c_n < sqrt(n+1). Renamed to avoid collision.
-/
lemma c_bounds_thm (n : ℕ) (hn : 0 < n) : Real.sqrt n < c n ∧ c n < Real.sqrt (n + 1) := by
  convert c_bounds n hn using 1

/-
Arithmetic inequality: floor(n(n+2)/2) + 1 >= (n+1)^2/2.
-/
lemma nat_ceil_div_two_ge (n : ℕ) :
  (n * (n + 2) / 2 + 1 : ℝ) ≥ (n + 1 : ℝ) ^ 2 / 2 := by
    grind

/-
Inequality: l < s_3(n) - 1 for n >= 2.
-/
lemma l_lt_s3_sub_one (n : ℕ) (hn : 2 ≤ n) :
  l_val n < generalized_sylvester n 3 - 1 := by
    -- By definition of $l_val$, we have $l_val n = n * (n + 1) ^ 2 * (n + 2) / 2$.
    have h_l_val : l_val n = n * (n + 1) ^ 2 * (n + 2) / 2 := by
      rfl;
    -- By definition of $generalized_sylvester$, we have $generalized_sylvester n 1 = (generalized_sylvester n 0)^2 - generalized_sylvester n 0 + 1$.
    have h_gen_syl_1 : generalized_sylvester n 1 = (generalized_sylvester n 0)^2 - generalized_sylvester n 0 + 1 := by
      rfl
    simp_all +decide [ generalized_sylvester ];
    zify [ Nat.succ_mul, sq ];
    norm_num [ add_assoc ];
    exact Int.ediv_lt_of_lt_mul ( by positivity ) ( by nlinarith only [ hn, pow_pos ( by positivity : 0 < ( n : ℤ ) ) 3, pow_pos ( by positivity : 0 < ( n : ℤ ) ) 4, pow_pos ( by positivity : 0 < ( n : ℤ ) ) 5, pow_pos ( by positivity : 0 < ( n : ℤ ) ) 6 ] )

/-
Definition of the comparison sequence for n=1 and verification that it satisfies the conditions of Lemma 6.
-/
noncomputable def u_seq_one (i : ℕ) : ℝ :=
  if i = 0 then 1/3
  else if i = 1 then 1/3
  else if i = 2 then 3/10
  else 1 / (generalized_sylvester 30 (i - 3) : ℝ)

lemma u_seq_one_satisfies_pac_sou :
  let u := u_seq_one
  let C := 1
  (∀ i, 0 < u i) ∧
  Antitone u ∧
  (∀ k ≥ 3, ∑ i ∈ Finset.range k, u i + C * ∏ i ∈ Finset.range k, u i = C) := by
    unfold u_seq_one;
    refine' ⟨ _, _, _ ⟩;
    · intro i; norm_num; split_ifs <;> norm_num;
      exact generalized_sylvester_pos 30 (i - 3);
    · refine' antitone_nat_of_succ_le _;
      rintro ( _ | _ | _ | n ) <;> norm_num [ generalized_sylvester ];
      simp +arith +decide
      gcongr;
      · exact Nat.cast_pos.mpr ( generalized_sylvester_pos _ _ );
      · exact Nat.le_of_lt_succ ( by rw [ show generalized_sylvester 30 ( n + 1 ) = ( generalized_sylvester 30 n ) ^ 2 - ( generalized_sylvester 30 n ) + 1 from rfl ] ; nlinarith [ Nat.sub_add_cancel ( show ( generalized_sylvester 30 n ) ^ 2 ≥ ( generalized_sylvester 30 n ) from Nat.le_self_pow ( by norm_num ) _ ), show generalized_sylvester 30 n > 1 from Nat.recOn n ( by decide ) fun n ihn => by { rw [ show generalized_sylvester 30 ( n + 1 ) = ( generalized_sylvester 30 n ) ^ 2 - ( generalized_sylvester 30 n ) + 1 from rfl ] ; exact Nat.succ_lt_succ ( Nat.sub_pos_of_lt ( by nlinarith ) ) } ] );
    · intro k hk;
      induction hk <;> norm_num [ Finset.sum_range_succ, Finset.prod_range_succ ] at *;
      rename_i k hk ih;
      rcases k with ( _ | _ | _ | k ) <;> norm_num [ Finset.sum_range_succ', Finset.prod_range_succ' ] at *;
      simp_all +decide [ Nat.succ_inj ];
      -- Substitute the induction hypothesis into the equation.
      have h_sub : (∏ x ∈ Finset.range k, (generalized_sylvester 30 x : ℝ))⁻¹ = (generalized_sylvester 30 k - 1 : ℝ)⁻¹ * 30 := by
        have h_sub : (∑ i ∈ Finset.range k, (1 / (generalized_sylvester 30 i : ℝ))) + (1 / (generalized_sylvester 30 k - 1 : ℝ)) = 1 / 30 := by
          convert prop_syl_1 30 ( by norm_num ) k using 1;
        grind;
      nlinarith [ inv_pos.mpr ( show 0 < ( generalized_sylvester 30 k : ℝ ) by exact Nat.cast_pos.mpr ( generalized_sylvester_pos _ _ ) ), inv_pos.mpr ( show 0 < ( generalized_sylvester 30 k - 1 : ℝ ) by exact sub_pos.mpr ( mod_cast Nat.le_trans ( by decide ) ( show generalized_sylvester 30 k ≥ 2 from Nat.recOn k ( by decide ) fun n ihn => by { rw [ show generalized_sylvester 30 ( n + 1 ) = ( generalized_sylvester 30 n ) ^ 2 - ( generalized_sylvester 30 n ) + 1 from rfl ] ; nlinarith only [ ihn, Nat.sub_add_cancel ( show ( generalized_sylvester 30 n ) ^ 2 ≥ ( generalized_sylvester 30 n ) from Nat.le_self_pow ( by decide ) _ ) ] } ) ) ), mul_inv_cancel₀ ( show ( generalized_sylvester 30 k : ℝ ) ≠ 0 by exact Nat.cast_ne_zero.mpr ( ne_of_gt ( generalized_sylvester_pos _ _ ) ) ), mul_inv_cancel₀ ( show ( generalized_sylvester 30 k - 1 : ℝ ) ≠ 0 by exact sub_ne_zero.mpr ( ne_of_gt ( mod_cast Nat.le_trans ( by decide ) ( show generalized_sylvester 30 k ≥ 2 from Nat.recOn k ( by decide ) fun n ihn => by { rw [ show generalized_sylvester 30 ( n + 1 ) = ( generalized_sylvester 30 n ) ^ 2 - ( generalized_sylvester 30 n ) + 1 from rfl ] ; nlinarith only [ ihn, Nat.sub_add_cancel ( show ( generalized_sylvester 30 n ) ^ 2 ≥ ( generalized_sylvester 30 n ) from Nat.le_self_pow ( by decide ) _ ) ] } ) ) ) ) ]

/-
The sequence c_n is strictly increasing.
-/
lemma c_strict_mono (n m : ℕ) (hn : 0 < n) (hnm : n < m) : c n < c m := by
  -- By the bounds we have, we know that $\sqrt{n} < c_n < \sqrt{n+1}$ and $\sqrt{m} < c_m < \sqrt{m+1}$.
  have h_bounds_n : Real.sqrt n < c n ∧ c n < Real.sqrt (n + 1) := by
    exact c_bounds n hn
  have h_bounds_m : Real.sqrt m < c m ∧ c m < Real.sqrt (m + 1) := by
    exact c_bounds_thm m ( by linarith );
  -- Since $n < m$, we have $\sqrt{n+1} \leq \sqrt{m}$.
  have h_sqrt_le : Real.sqrt (n + 1) ≤ Real.sqrt m := by
    exact Real.sqrt_le_sqrt <| mod_cast Nat.succ_le_of_lt hnm;
  linarith [ Real.sqrt_nonneg n, Real.sqrt_nonneg m ]

/-
The sequence of reciprocals satisfies the sum-product inequality condition of Lemma 6.
-/
lemma v_satisfies_pac_sou_condition (n : ℕ) (hn : 0 < n) (a : ℕ → ℕ)
  (h_pos : ∀ i, 0 < a i)
  (h_sum : ∑' i, (1 : ℝ) / a i = 1 / n) :
  let v := fun i => 1 / (a i : ℝ)
  let C := 1 / (n : ℝ)
  ∀ k, ∑ i ∈ Finset.range k, v i + C * ∏ i ∈ Finset.range k, v i ≤ C := by
    -- Let $q = 1/n - S_k$. We know $q * n * \prod_{i<k} a_i$ is an integer.
    set q := fun k => 1 / (n : ℝ) - ∑ i ∈ Finset.range k, (1 / (a i) : ℝ)
    have hq_int : ∀ k, ∃ m : ℤ, q k * n * ∏ i ∈ Finset.range k, (a i : ℝ) = m := by
      intro k
      use (∏ i ∈ Finset.range k, (a i : ℤ)) - n * (∑ i ∈ Finset.range k, (∏ j ∈ Finset.erase (Finset.range k) i, (a j : ℤ)));
      simp +zetaDelta at *;
      simp +decide [ sub_mul, mul_assoc, Finset.mul_sum _ _ _, Finset.sum_mul, hn.ne' ];
      refine Finset.sum_congr rfl fun i hi => ?_;
      rw [ inv_mul_eq_div, div_eq_iff ( Nat.cast_ne_zero.mpr <| ne_of_gt <| h_pos i ) ] ; rw [ ← Finset.mul_prod_erase _ _ hi ] ; ring;
    -- Since $q > 0$, we have $q \geq 1 / (n * \prod_{i<k} a_i)$.
    have hq_ge : ∀ k, q k ≥ 1 / (n * ∏ i ∈ Finset.range k, (a i : ℝ)) := by
      intro k
      obtain ⟨m, hm⟩ := hq_int k
      have hq_pos : q k > 0 := by
        refine' sub_pos_of_lt ( h_sum ▸ _ );
        refine' lt_of_lt_of_le _ ( Summable.sum_le_tsum ( Finset.range ( k + 1 ) ) ( fun _ _ => by positivity ) _ );
        · simpa [ Finset.sum_range_succ ] using by linarith [ h_pos k ] ;
        · exact ( by contrapose! h_sum; rw [ tsum_eq_zero_of_not_summable h_sum ] ; positivity )
      have hm_pos : m ≥ 1 := by
        exact_mod_cast hm ▸ mul_pos ( mul_pos hq_pos ( Nat.cast_pos.mpr hn ) ) ( Finset.prod_pos fun _ _ => Nat.cast_pos.mpr ( h_pos _ ) )
      have hq_ge : q k ≥ 1 / (n * ∏ i ∈ Finset.range k, (a i : ℝ)) := by
        rw [ ge_iff_le, div_le_iff₀ ] <;> nlinarith [ show ( m : ℝ ) ≥ 1 by exact_mod_cast hm_pos, show ( n : ℝ ) > 0 by positivity, show ( ∏ i ∈ Finset.range k, ( a i : ℝ ) ) > 0 by exact Finset.prod_pos fun _ _ => Nat.cast_pos.mpr ( h_pos _ ) ]
      exact hq_ge;
    simp +zetaDelta at *;
    grind

/-
For n=1, the reciprocal sequence is bounded by the comparison sequence for the first 3 terms.
-/
lemma v_le_u_base_case_one (a : ℕ → ℕ)
  (h_pos : ∀ i, 0 < a i)
  (h_mono : Monotone a)
  (h_sum : ∑' i, (1 : ℝ) / a i = 1)
  (h_neq : a 0 ≠ 2) :
  ∀ i < 3, 1 / (a i : ℝ) ≤ u_seq_one i := by
    -- Since $a_0 \neq 2$ and $a$ is monotone, we have $a_0 \geq 3$, $a_1 \geq 3$, and $a_2 \geq 4$.
    have ha0 : a 0 ≥ 3 := by
      by_cases ha0 : a 0 = 1;
      · have h_contra : ∑' i, (1 : ℝ) / a i ≥ ∑ i ∈ Finset.range 2, (1 : ℝ) / a i := by
          exact Summable.sum_le_tsum ( Finset.range 2 ) ( fun _ _ => by positivity ) ( by exact ( show Summable _ from by { by_contra h; rw [ tsum_eq_zero_of_not_summable h ] at h_sum; norm_num at h_sum } ) );
        norm_num [ Finset.sum_range_succ, ha0, h_sum ] at h_contra;
        norm_num at * ; linarith [ inv_pos.mpr ( show 0 < ( a 1 : ℝ ) by exact_mod_cast h_pos 1 ) ];
      · exact Nat.lt_of_le_of_ne ( Nat.succ_le_of_lt ( lt_of_le_of_ne ( h_pos 0 ) ( Ne.symm ha0 ) ) ) ( Ne.symm h_neq )
    have ha1 : a 1 ≥ 3 := by
      linarith [ h_mono zero_le_one ]
    have ha2 : a 2 ≥ 4 := by
      by_contra ha2_lt_4
      have ha2_eq_3 : a 2 = 3 := by
        linarith [ h_mono ( show 0 ≤ 1 by norm_num ), h_mono ( show 1 ≤ 2 by norm_num ) ]
      have ha_eq_3 : ∀ i, a i = 3 := by
        intro i; induction' i using Nat.strong_induction_on with i ih; rcases i with ( _ | _ | _ | i ) <;> simp_all +arith +decide;
        · linarith [ h_mono ( show 0 ≤ 1 by norm_num ), h_mono ( show 1 ≤ 2 by norm_num ) ];
        · linarith [ h_mono ( show 1 ≤ 2 by norm_num ) ];
        · have := h_sum ▸ Summable.sum_le_tsum ( Finset.range ( i + 4 ) ) ( fun _ _ => inv_nonneg.2 ( Nat.cast_nonneg _ ) ) ( show Summable _ from by { by_contra h; rw [ tsum_eq_zero_of_not_summable h ] at h_sum; norm_num at h_sum } ) ; norm_num [ Finset.sum_range_succ, ih ] at this;
          exact absurd this ( by linarith [ show ( ∑ i ∈ Finset.range i, ( a i : ℝ ) ⁻¹ ) ≥ 0 by exact Finset.sum_nonneg fun _ _ => inv_nonneg.2 ( Nat.cast_nonneg _ ), inv_pos.2 ( show 0 < ( a ( i + 3 ) : ℝ ) by exact Nat.cast_pos.2 ( h_pos _ ) ) ] )
      aesop;
    intro i hi; interval_cases i <;> norm_num [ u_seq_one ];
    · rw [ inv_le_comm₀ ] <;> norm_num <;> linarith [ show ( a 0 : ℝ ) ≥ 3 by norm_cast ];
    · rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_cast <;> linarith;
    · rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_cast ; linarith;
      grind

/-
The limit of the comparison sequence term raised to the appropriate power is c_30^(1/8).
-/
lemma limit_u_seq_one :
  Filter.Tendsto (fun i => (u_seq_one i) ^ (-((1/2 : ℝ) ^ (i + 1)))) Filter.atTop (nhds (c 30 ^ (1/8 : ℝ))) := by
    -- Let's simplify the expression inside the limit.
    have h_simplify : Filter.Tendsto (fun j => (1 / (generalized_sylvester 30 j : ℝ)) ^ (-(1 / 2 : ℝ) ^ (j + 4))) Filter.atTop (nhds ((c 30) ^ (1 / 8 : ℝ))) := by
      -- Recognize that $(1 / (generalized_sylvester 30 j : ℝ)) ^ (-(1 / 2 : ℝ) ^ (j + 4))$ can be rewritten using the properties of exponents.
      suffices h_exp : Filter.Tendsto (fun j => ((generalized_sylvester 30 j : ℝ) ^ ((1 / 2 : ℝ) ^ (j + 1))) ^ (1 / 8 : ℝ)) Filter.atTop (nhds ((c 30) ^ (1 / 8 : ℝ))) by
        convert h_exp using 2 ; norm_num [ Real.rpow_neg_eq_inv_rpow ] ; ring_nf;
        rw [ ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; ring_nf;
      exact Filter.Tendsto.rpow ( c_exists 30 ) tendsto_const_nhds ( Or.inl <| ne_of_gt <| lt_of_lt_of_le ( by norm_num ) <| le_of_tendsto_of_tendsto' tendsto_const_nhds ( c_exists 30 ) fun j => Real.one_le_rpow ( mod_cast generalized_sylvester_pos _ _ ) <| by positivity );
    refine h_simplify.comp ( Filter.tendsto_sub_atTop_nat 3 ) |> Filter.Tendsto.congr' ?_;
    filter_upwards [ Filter.eventually_gt_atTop 3 ] with i hi ; rcases i with ( _ | _ | _ | _ | i ) <;> norm_num [ Nat.succ_div ] at *;
    unfold u_seq_one ; aesop

/-
Inequality relating c_30 and c_1.
-/
lemma c_30_lt_c_1_pow_8 : c 30 < c 1 ^ 8 := by
  -- By definition of $c$, we know that $c_1^8 = c_{s_3(1)-1}$.
  have hc1_8 : c 1 ^ 8 = c (generalized_sylvester 1 3 - 1) := by
    convert prop_syl_4 1 3 using 1;
  rw [ hc1_8 ];
  refine' c_strict_mono _ _ _ _ <;> norm_num [ generalized_sylvester ]

/-
Partial sums of reciprocals are bounded by partial sums of the comparison sequence for n=1.
-/
lemma sum_v_le_sum_u_one (a : ℕ → ℕ)
  (h_pos : ∀ i, 0 < a i)
  (h_mono : Monotone a)
  (h_sum : ∑' i, (1 : ℝ) / a i = 1)
  (h_neq : a 0 ≠ 2) :
  ∀ k, ∑ i ∈ Finset.range k, (1 / (a i : ℝ)) ≤ ∑ i ∈ Finset.range k, u_seq_one i := by
    -- By Lemma 6, it suffices to show that for all k, v_k ≤ u_k for i < 3.
    apply pac_sou;
    any_goals exact zero_lt_one;
    any_goals exact u_seq_one_satisfies_pac_sou.1;
    any_goals exact u_seq_one_satisfies_pac_sou.2.1;
    any_goals exact fun i => one_div_pos.mpr ( Nat.cast_pos.mpr ( h_pos i ) );
    exact fun i j hij => one_div_le_one_div_of_le ( Nat.cast_pos.mpr ( h_pos _ ) ) ( Nat.cast_le.mpr ( h_mono hij ) );
    any_goals exact u_seq_one_satisfies_pac_sou.2.2;
    · intro k hk; have := v_satisfies_pac_sou_condition 1 zero_lt_one a h_pos ( by aesop ) k; aesop;
    · exact fun i a_1 => v_le_u_base_case_one a h_pos h_mono h_sum h_neq i a_1

/-
The comparison sequence for n=1 is summable and sums to 1.
-/
lemma u_seq_one_summable_and_sum_eq_one :
  Summable u_seq_one ∧ ∑' i, u_seq_one i = 1 := by
    have := u_seq_one_satisfies_pac_sou;
    -- Since the partial sums of $u_seq_one$ are bounded and increasing, they converge to 1.
    have h_summable : Summable u_seq_one := by
      have h_summable : BddAbove (Set.range (fun k => ∑ i ∈ Finset.range k, u_seq_one i)) := by
        exact ⟨ 1, Set.forall_mem_range.mpr fun k => if hk : 3 ≤ k then by linarith [ this.2.2 k hk, show 0 ≤ ∏ i ∈ Finset.range k, u_seq_one i from Finset.prod_nonneg fun _ _ => le_of_lt ( this.1 _ ) ] else by interval_cases k <;> norm_num [ Finset.sum_range_succ, u_seq_one ] ⟩;
      exact summable_iff_not_tendsto_nat_atTop_of_nonneg ( fun _ => le_of_lt ( this.1 _ ) ) |>.2 fun h => absurd ( h.eventually ( Filter.eventually_gt_atTop h_summable.choose ) ) fun h' => by obtain ⟨ k, hk ⟩ := h'.exists; linarith [ h_summable.choose_spec ( Set.mem_range_self k ) ] ; ;
    have h_limit : Filter.Tendsto (fun k => ∑ i ∈ Finset.range k, u_seq_one i) Filter.atTop (nhds 1) := by
      have h_limit : Filter.Tendsto (fun k => ∑ i ∈ Finset.range k, u_seq_one i + ∏ i ∈ Finset.range k, u_seq_one i) Filter.atTop (nhds 1) := by
        exact tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ge_atTop 3 ] with k hk; aesop );
      have h_prod_zero : Filter.Tendsto (fun k => ∏ i ∈ Finset.range k, u_seq_one i) Filter.atTop (nhds 0) := by
        have h_prod_le : ∀ k ≥ 3, ∏ i ∈ Finset.range k, u_seq_one i ≤ u_seq_one 2 ^ (k - 2) := by
          intros k hk
          have h_prod_le : ∏ i ∈ Finset.Ico 2 k, u_seq_one i ≤ u_seq_one 2 ^ (k - 2) := by
            exact le_trans ( Finset.prod_le_prod ( fun _ _ => le_of_lt ( this.1 _ ) ) fun _ _ => this.2.1 ( show 2 ≤ _ from by linarith [ Finset.mem_Ico.mp ‹_› ] ) ) ( by norm_num );
          rw [ ← Finset.prod_range_mul_prod_Ico _ ( by linarith : 2 ≤ k ) ];
          exact le_trans ( mul_le_of_le_one_left ( Finset.prod_nonneg fun _ _ => le_of_lt ( this.1 _ ) ) ( by norm_num [ Finset.prod_range_succ, u_seq_one ] ) ) h_prod_le
        have h_prod_zero : Filter.Tendsto (fun k => u_seq_one 2 ^ (k - 2)) Filter.atTop (nhds 0) := by
          exact tendsto_pow_atTop_nhds_zero_of_lt_one ( by norm_num [ u_seq_one ] ) ( by norm_num [ u_seq_one ] ) |> Filter.Tendsto.comp <| Filter.tendsto_sub_atTop_nat 2;
        exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 3, fun k hk => by rw [ Real.norm_of_nonneg ( Finset.prod_nonneg fun _ _ => le_of_lt ( this.1 _ ) ) ] ; exact h_prod_le k hk ⟩ ) h_prod_zero;
      simpa using h_limit.sub h_prod_zero;
    exact ⟨ h_summable, tendsto_nhds_unique ( h_summable.hasSum.tendsto_sum_nat ) h_limit ⟩

/-
The liminf of the sequence is bounded by c_30^(1/8).
-/
lemma liminf_le_c30_pow_8 (a : ℕ → ℕ)
  (h_pos : ∀ i, 0 < a i)
  (h_mono : Monotone a)
  (h_sum : ∑' i, (1 : ℝ) / a i = 1)
  (h_neq : a 0 ≠ 2) :
  Filter.liminf (fun i => (a i : ℝ) ^ ((1/2 : ℝ) ^ (i + 1))) Filter.atTop ≤ c 30 ^ (1/8 : ℝ) := by
    -- By Lemma~\ref{lem:sum_v_le_sum_u_one}, for infinitely many k, (a k : ℝ) ^ ((1/2 : ℝ) ^ (k + 1)) ≤ u_seq_one k ^ (-(1/2 : ℝ) ^ (k + 1)).
    have h_inf_often : ∀ N, ∃ k ≥ N, (a k : ℝ) ^ ((1/2 : ℝ) ^ (k + 1)) ≤ (u_seq_one k) ^ (-(1/2 : ℝ) ^ (k + 1)) := by
      have h_inf_often : ∀ N, ∃ k ≥ N, (1 / (a k : ℝ)) ≥ (u_seq_one k) := by
        intro N
        have h_sum_eq := u_seq_one_summable_and_sum_eq_one
        have h_sum_eq' := h_sum
        have h_inf_often : ∀ N, ∃ k ≥ N, (1 / (a k : ℝ)) ≥ (u_seq_one k) := by
          intro N
          have h_sum_le : ∀ k, ∑ i ∈ Finset.range k, (1 / (a i : ℝ)) ≤ ∑ i ∈ Finset.range k, (u_seq_one i) := by
            exact fun k => sum_v_le_sum_u_one a h_pos h_mono h_sum h_neq k
          have h_sum_eq : ∑' i, (1 / (a i : ℝ)) = ∑' i, (u_seq_one i) := by
            linarith
          apply_rules [ infinitely_often_ge_of_sum_le_sum_eq ];
          · tauto;
          · exact ( by contrapose! h_sum; rw [ tsum_eq_zero_of_not_summable h_sum ] at *; linarith );
        exact h_inf_often N;
      intro N; obtain ⟨ k, hk₁, hk₂ ⟩ := h_inf_often N; use k, hk₁; rw [ Real.rpow_neg_eq_inv_rpow ] ;
      exact Real.rpow_le_rpow ( Nat.cast_nonneg _ ) ( by simpa using inv_anti₀ ( show 0 < u_seq_one k from by
                                                                                  unfold u_seq_one; split_ifs <;> norm_num;
                                                                                  exact
                                                                                    generalized_sylvester_pos
                                                                                      30 (k - 3) ) hk₂ ) ( by positivity );
    -- By Lemma~\ref{lem:limit_u_seq_one}, u_seq_one k ^ (-(1/2 : ℝ) ^ (k + 1)) converges to c 30 ^ (1/8).
    have h_limit : Filter.Tendsto (fun i => (u_seq_one i) ^ (-(1/2 : ℝ) ^ (i + 1))) Filter.atTop (nhds (c 30 ^ (1/8 : ℝ))) := by
      convert limit_u_seq_one using 1;
    refine' csSup_le _ _ <;> norm_num;
    · exact ⟨ 0, ⟨ 0, fun _ _ => by positivity ⟩ ⟩;
    · intro b x hx; contrapose! h_inf_often;
      exact Filter.eventually_atTop.mp ( h_limit.eventually ( gt_mem_nhds h_inf_often ) ) |> fun ⟨ N, hN ⟩ ↦ ⟨ Max.max x N, fun n hn ↦ lt_of_lt_of_le ( hN n ( le_of_max_le_right hn ) ) ( hx n ( le_of_max_le_left hn ) ) ⟩

/-
The base case of the main theorem for n=1.
-/
lemma main_theorem_base_case_n_eq_1 (a : ℕ → ℕ)
  (h_pos : ∀ i, 0 < a i)
  (h_mono : Monotone a)
  (h_sum : ∑' i, (1 : ℝ) / a i = 1)
  (h_neq : a 0 ≠ 2) :
  Filter.liminf (fun i => (a i : ℝ) ^ ((1/2 : ℝ) ^ (i + 1))) Filter.atTop < c 1 := by
    -- By combining the results from Lemma c_30_lt_c_1_pow_8 and Lemma liminf_le_c30_pow_8, we get the desired inequality.
    have h_final : Filter.liminf (fun i => (a i : ℝ) ^ ((1/2 : ℝ) ^ (i + 1))) Filter.atTop ≤ c 30 ^ (1/8 : ℝ) ∧ c 30 ^ (1/8 : ℝ) < c 1 := by
      apply And.intro;
      · apply_rules [ liminf_le_c30_pow_8 ];
      · exact lt_of_lt_of_le ( Real.rpow_lt_rpow ( by exact le_of_lt ( show 0 < c 30 from lt_of_le_of_lt ( Real.sqrt_nonneg _ ) ( c_bounds_thm 30 ( by decide ) |>.1 ) ) ) ( c_30_lt_c_1_pow_8 ) ( by norm_num ) ) ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by exact le_of_lt ( show 0 < c 1 from lt_of_le_of_lt ( Real.sqrt_nonneg _ ) ( c_bounds_thm 1 ( by decide ) |>.1 ) ) ) ] ; norm_num );
    exact lt_of_le_of_lt h_final.left h_final.right

/-
Refined version of Lemma 6 with weaker initial condition.
-/
lemma pac_sou_refined (C : ℝ) (t : ℕ) (u_seq v_seq : ℕ → ℝ)
  (hC_pos : 0 < C)
  (hu_pos : ∀ i, 0 < u_seq i) (hv_pos : ∀ i, 0 < v_seq i)
  (hu_mono : Antitone u_seq) (hv_mono : Antitone v_seq)
  (h_eq : ∀ k ≥ t, ∑ i ∈ Finset.range k, u_seq i + C * ∏ i ∈ Finset.range k, u_seq i = C)
  (h_le : ∀ k ≥ t, ∑ i ∈ Finset.range k, v_seq i + C * ∏ i ∈ Finset.range k, v_seq i ≤ C)
  (h_init : ∀ i < t - 1, v_seq i ≤ u_seq i) :
  ∀ k, ∑ i ∈ Finset.range k, v_seq i ≤ ∑ i ∈ Finset.range k, u_seq i := by
    by_contra h_contra;
    -- Let's obtain the smallest $k$ such that $\sum_{i=0}^{k-1} v_i > \sum_{i=0}^{k-1} u_i$.
    obtain ⟨k, hk⟩ : ∃ k, (∑ i ∈ Finset.range k, v_seq i) > (∑ i ∈ Finset.range k, u_seq i) ∧ ∀ j < k, (∑ i ∈ Finset.range j, v_seq i) ≤ (∑ i ∈ Finset.range j, u_seq i) := by
      exact ⟨ Nat.find ( by push_neg at h_contra; exact h_contra ), Nat.find_spec ( by push_neg at h_contra; exact h_contra ), fun j hj => le_of_not_gt fun h => Nat.find_min ( by push_neg at h_contra; exact h_contra ) hj h ⟩;
    -- Let $m$ be the largest index $\leq k$ such that $\prod_{j=m}^k v_j < \prod_{j=m}^k u_j$.
    obtain ⟨m, hm⟩ : ∃ m ≤ k, (∏ i ∈ Finset.Ico m k, v_seq i) < (∏ i ∈ Finset.Ico m k, u_seq i) ∧ ∀ l, m < l → l ≤ k → (∏ i ∈ Finset.Ico l k, v_seq i) ≥ (∏ i ∈ Finset.Ico l k, u_seq i) := by
      have hm_exists : ∃ m ≤ k, (∏ i ∈ Finset.Ico m k, v_seq i) < (∏ i ∈ Finset.Ico m k, u_seq i) := by
        have h_prod_lt : C * (∏ i ∈ Finset.range k, v_seq i) < C * (∏ i ∈ Finset.range k, u_seq i) := by
          by_cases hk_ge_t : k ≥ t;
          · linarith [ h_eq k hk_ge_t, h_le k hk_ge_t ];
          · rcases k with ( _ | k ) <;> simp_all +decide [ Finset.sum_range_succ ];
            grind;
        exact ⟨ 0, Nat.zero_le _, by simpa using h_prod_lt |> fun h => by nlinarith ⟩;
      obtain ⟨m, hm⟩ : ∃ m ≤ k, (∏ i ∈ Finset.Ico m k, v_seq i) < (∏ i ∈ Finset.Ico m k, u_seq i) ∧ ∀ l, m < l → l ≤ k → (∏ i ∈ Finset.Ico l k, v_seq i) ≥ (∏ i ∈ Finset.Ico l k, u_seq i) := by
        have h_max : ∃ m ∈ Finset.filter (fun m => (∏ i ∈ Finset.Ico m k, v_seq i) < (∏ i ∈ Finset.Ico m k, u_seq i)) (Finset.Iic k), ∀ l ∈ Finset.filter (fun m => (∏ i ∈ Finset.Ico m k, v_seq i) < (∏ i ∈ Finset.Ico m k, u_seq i)) (Finset.Iic k), m ≥ l := by
          exact ⟨ Finset.max' _ ⟨ hm_exists.choose, Finset.mem_filter.mpr ⟨ Finset.mem_Iic.mpr hm_exists.choose_spec.1, hm_exists.choose_spec.2 ⟩ ⟩, Finset.max'_mem _ _, fun l hl => Finset.le_max' _ _ hl ⟩
        obtain ⟨ m, hm₁, hm₂ ⟩ := h_max; exact ⟨ m, Finset.mem_Iic.mp ( Finset.mem_filter.mp hm₁ |>.1 ), Finset.mem_filter.mp hm₁ |>.2, fun l hl₁ hl₂ => not_lt.1 fun hl₃ => not_lt_of_ge ( hm₂ l ( Finset.mem_filter.mpr ⟨ Finset.mem_Iic.mpr hl₂, hl₃ ⟩ ) ) hl₁ ⟩ ;
      use m;
    -- Apply sum_ge_of_prod_ge_prod to the shifted sequences x_i = u_{m+i}, y_i = v_{m+i} for length n = k - m + 1.
    have h_sum_ge : ∑ i ∈ Finset.range (k - m), v_seq (m + i) ≤ ∑ i ∈ Finset.range (k - m), u_seq (m + i) := by
      apply sum_ge_of_prod_ge_prod;
      · exact fun i hi => hu_pos _;
      · exact fun i hi => hv_pos _;
      · exact fun i j hij hj => hu_mono <| by linarith;
      · exact fun i j hij hj => hv_mono ( by linarith );
      · intro l hl; specialize hm; have := hm.2.2 ( m + l + 1 ) ( by linarith ) ( by linarith [ Nat.sub_add_cancel hm.1 ] ) ; simp_all +decide [ Finset.prod_Ico_eq_prod_range ] ;
        have h_prod_le : ∏ i ∈ Finset.range (k - m), v_seq (m + i) = (∏ i ∈ Finset.range (l + 1), v_seq (m + i)) * (∏ i ∈ Finset.range (k - (m + l + 1)), v_seq (m + l + 1 + i)) ∧ ∏ i ∈ Finset.range (k - m), u_seq (m + i) = (∏ i ∈ Finset.range (l + 1), u_seq (m + i)) * (∏ i ∈ Finset.range (k - (m + l + 1)), u_seq (m + l + 1 + i)) := by
          constructor <;> rw [ ← Nat.add_sub_of_le ( show l + 1 ≤ k - m from by omega ) ] <;> simp +decide [ add_assoc, Finset.prod_range_add ];
          · simp +decide only [tsub_tsub, mul_assoc];
          · rw [ mul_assoc, show k - m - ( l + 1 ) = k - ( m + ( l + 1 ) ) by omega ];
        nlinarith [ show 0 < ∏ i ∈ Finset.range ( k - ( m + l + 1 ) ), v_seq ( m + l + 1 + i ) from Finset.prod_pos fun _ _ => hv_pos _, show 0 < ∏ i ∈ Finset.range ( l + 1 ), u_seq ( m + i ) from Finset.prod_pos fun _ _ => hu_pos _, show 0 < ∏ i ∈ Finset.range ( k - ( m + l + 1 ) ), u_seq ( m + l + 1 + i ) from Finset.prod_pos fun _ _ => hu_pos _ ];
    -- Split the sum into two parts: from 0 to m-1 and from m to k-1.
    have h_split_sum : ∑ i ∈ Finset.range k, v_seq i = ∑ i ∈ Finset.range m, v_seq i + ∑ i ∈ Finset.Ico m k, v_seq i ∧ ∑ i ∈ Finset.range k, u_seq i = ∑ i ∈ Finset.range m, u_seq i + ∑ i ∈ Finset.Ico m k, u_seq i := by
      exact ⟨ by rw [ Finset.sum_range_add_sum_Ico _ hm.1 ], by rw [ Finset.sum_range_add_sum_Ico _ hm.1 ] ⟩;
    simp_all +decide [ Finset.sum_Ico_eq_sum_range ];
    linarith [ hk.2 m ( lt_of_le_of_ne hm.1 ( by rintro rfl; norm_num at * ) ) ]

/-
Helper lemma: existence of a partition point p such that suffix sum of v is <= suffix sum of u, and prefix product of v is >= prefix product of u.
-/
lemma exists_partition_sum_le (n : ℕ) (u v : ℕ → ℝ)
  (hu_pos : ∀ i < n, 0 < u i) (hv_pos : ∀ i < n, 0 < v i)
  (hu_mono : ∀ i j, i < j → j < n → u j ≤ u i)
  (hv_mono : ∀ i j, i < j → j < n → v j ≤ v i)
  (h_prod : ∏ i ∈ Finset.range n, v i < ∏ i ∈ Finset.range n, u i) :
  ∃ p < n, (∑ i ∈ Finset.Ico p n, v i ≤ ∑ i ∈ Finset.Ico p n, u i) ∧ (∏ i ∈ Finset.range p, v i ≥ ∏ i ∈ Finset.range p, u i) := by
    -- By definition of $R_k$, we know that $R_n > 1 = R_0$, so the minimum must occur at $p < n$.
    obtain ⟨p, hp⟩ : ∃ p ≤ n, (∏ i ∈ Finset.range p, u i) / (∏ i ∈ Finset.range p, v i) ≤ (∏ i ∈ Finset.range n, u i) / (∏ i ∈ Finset.range n, v i) ∧ (∀ q ≤ n, (∏ i ∈ Finset.range q, u i) / (∏ i ∈ Finset.range q, v i) ≥ (∏ i ∈ Finset.range p, u i) / (∏ i ∈ Finset.range p, v i)) := by
      -- The set of ratios is finite, so it must attain a minimum.
      obtain ⟨p, hp⟩ : ∃ p ∈ Finset.range (n + 1), ∀ q ∈ Finset.range (n + 1), (∏ i ∈ Finset.range p, u i) / (∏ i ∈ Finset.range p, v i) ≤ (∏ i ∈ Finset.range q, u i) / (∏ i ∈ Finset.range q, v i) := by
        exact Finset.exists_min_image _ _ ⟨ _, Finset.mem_range.mpr <| Nat.lt_succ_self _ ⟩;
      exact ⟨ p, Finset.mem_range_succ_iff.mp hp.1, hp.2 n ( Finset.mem_range.mpr ( Nat.lt_succ_self _ ) ), fun q hq => hp.2 q ( Finset.mem_range.mpr ( Nat.lt_succ_of_le hq ) ) ⟩;
    refine' ⟨ p, lt_of_le_of_ne hp.1 _, _, _ ⟩;
    · rintro rfl; simp_all +decide [ div_eq_mul_inv ] ;
      specialize hp 0 ; norm_num at hp;
      rw [ ← div_eq_mul_inv, div_le_iff₀ ] at hp <;> nlinarith [ show 0 < ∏ i ∈ Finset.range p, v i from Finset.prod_pos fun i hi => hv_pos i ( Finset.mem_range.mp hi ) ];
    · -- By definition of $R_k$, we know that for any $k \geq p$, $\prod_{i=p}^{k-1} u_i \geq \prod_{i=p}^{k-1} v_i$.
      have h_prod_ge : ∀ k ≥ p, k ≤ n → (∏ i ∈ Finset.Ico p k, u i) ≥ (∏ i ∈ Finset.Ico p k, v i) := by
        intros k hk₁ hk₂
        have h_prod_ge : (∏ i ∈ Finset.range k, u i) / (∏ i ∈ Finset.range k, v i) ≥ (∏ i ∈ Finset.range p, u i) / (∏ i ∈ Finset.range p, v i) := by
          exact hp.2.2 k hk₂;
        rw [ ge_iff_le, div_le_div_iff₀ ] at h_prod_ge;
        · rw [ ← Finset.prod_range_mul_prod_Ico _ hk₁, ← Finset.prod_range_mul_prod_Ico _ hk₁ ] at *;
          nlinarith [ show 0 < ( ∏ i ∈ Finset.range p, u i ) * ( ∏ i ∈ Finset.range p, v i ) from mul_pos ( Finset.prod_pos fun i hi => hu_pos i ( by linarith [ Finset.mem_range.mp hi ] ) ) ( Finset.prod_pos fun i hi => hv_pos i ( by linarith [ Finset.mem_range.mp hi ] ) ) ];
        · exact Finset.prod_pos fun i hi => hv_pos i ( by linarith [ Finset.mem_range.mp hi ] );
        · exact Finset.prod_pos fun i hi => hv_pos i ( by linarith [ Finset.mem_range.mp hi ] );
      have := sum_ge_of_prod_ge_prod ( n - p ) ( fun i => u ( p + i ) ) ( fun i => v ( p + i ) ) ?_ ?_ ?_ ?_ ?_ <;> simp_all +decide [ Finset.sum_Ico_eq_sum_range ];
      · exact fun i hi => hu_pos _ ( by linarith [ Nat.sub_add_cancel hp.1 ] );
      · exact fun i hi => hv_pos _ ( by linarith [ Nat.sub_add_cancel hp.1 ] );
      · grind;
      · grind;
      · intro k hk; specialize h_prod_ge ( p + k + 1 ) ( by linarith ) ( by linarith [ Nat.sub_add_cancel hp.1 ] ) ; simp_all +decide [ Finset.prod_Ico_eq_prod_range ] ;
        simp_all +decide [ add_assoc, Finset.prod_range_succ ];
    · contrapose! hp;
      intro hp_le_n hp_div_le_div
      use 0
      simp
      rwa [ one_lt_div ( Finset.prod_pos fun i hi => hv_pos i ( by linarith [ Finset.mem_range.mp hi ] ) ) ]

/-
Helper lemma: existence of a partition point p such that suffix sum of v is <= suffix sum of u, and prefix product of v is >= prefix product of u.
-/
lemma exists_partition_sum_le_of_prod_lt (n : ℕ) (u v : ℕ → ℝ)
  (hu_pos : ∀ i < n, 0 < u i) (hv_pos : ∀ i < n, 0 < v i)
  (hu_mono : ∀ i j, i < j → j < n → u j ≤ u i)
  (hv_mono : ∀ i j, i < j → j < n → v j ≤ v i)
  (h_prod : ∏ i ∈ Finset.range n, v i < ∏ i ∈ Finset.range n, u i) :
  ∃ p < n, (∑ i ∈ Finset.Ico p n, v i ≤ ∑ i ∈ Finset.Ico p n, u i) ∧ (∏ i ∈ Finset.range p, v i ≥ ∏ i ∈ Finset.range p, u i) := by
    convert exists_partition_sum_le n u v hu_pos hv_pos hu_mono hv_mono h_prod using 1

/-
Helper lemma: existence of a partition point p such that suffix sum of v is <= suffix sum of u, and prefix product of v is >= prefix product of u.
-/
lemma exists_partition_sum_le_v2 (n : ℕ) (u v : ℕ → ℝ)
  (hu_pos : ∀ i < n, 0 < u i) (hv_pos : ∀ i < n, 0 < v i)
  (hu_mono : ∀ i j, i < j → j < n → u j ≤ u i)
  (hv_mono : ∀ i j, i < j → j < n → v j ≤ v i)
  (h_prod : ∏ i ∈ Finset.range n, v i < ∏ i ∈ Finset.range n, u i) :
  ∃ p < n, (∑ i ∈ Finset.Ico p n, v i ≤ ∑ i ∈ Finset.Ico p n, u i) ∧ (∏ i ∈ Finset.range p, v i ≥ ∏ i ∈ Finset.range p, u i) := by
    convert exists_partition_sum_le_of_prod_lt n u v hu_pos hv_pos hu_mono hv_mono h_prod using 1

/-
Helper lemma: existence of a partition point p such that suffix sum of v is <= suffix sum of u, and prefix product of v is >= prefix product of u.
-/
lemma exists_partition_sum_le_v3 (n : ℕ) (u v : ℕ → ℝ)
  (hu_pos : ∀ i < n, 0 < u i) (hv_pos : ∀ i < n, 0 < v i)
  (hu_mono : ∀ i j, i < j → j < n → u j ≤ u i)
  (hv_mono : ∀ i j, i < j → j < n → v j ≤ v i)
  (h_prod : ∏ i ∈ Finset.range n, v i < ∏ i ∈ Finset.range n, u i) :
  ∃ p < n, (∑ i ∈ Finset.Ico p n, v i ≤ ∑ i ∈ Finset.Ico p n, u i) ∧ (∏ i ∈ Finset.range p, v i ≥ ∏ i ∈ Finset.range p, u i) := by
    exact exists_partition_sum_le_v2 n u v hu_pos hv_pos hu_mono hv_mono h_prod

/-
Helper lemma: existence of a partition point p such that suffix sum of v is <= suffix sum of u, and prefix product of v is >= prefix product of u.
-/
lemma exists_partition_sum_le_v4 (n : ℕ) (u v : ℕ → ℝ)
  (hu_pos : ∀ i < n, 0 < u i) (hv_pos : ∀ i < n, 0 < v i)
  (hu_mono : ∀ i j, i < j → j < n → u j ≤ u i)
  (hv_mono : ∀ i j, i < j → j < n → v j ≤ v i)
  (h_prod : ∏ i ∈ Finset.range n, v i < ∏ i ∈ Finset.range n, u i) :
  ∃ p < n, (∑ i ∈ Finset.Ico p n, v i ≤ ∑ i ∈ Finset.Ico p n, u i) ∧ (∏ i ∈ Finset.range p, v i ≥ ∏ i ∈ Finset.range p, u i) := by
    convert exists_partition_sum_le_v3 n u v hu_pos hv_pos hu_mono hv_mono h_prod using 1

/-
Base case inequality for the general case n >= 2.
-/
lemma v_le_u_base_case_general (n : ℕ) (hn : 2 ≤ n) (a : ℕ → ℕ)
  (h_pos : ∀ i, 0 < a i)
  (h_sum : ∑' i, (1 : ℝ) / a i = 1 / n)
  (h_neq : a 0 ≠ n + 1) :
  1 / (a 0 : ℝ) ≤ u_seq n 0 := by
    -- Since $\sum_{i=0}^{\infty} \frac{1}{a_i} = \frac{1}{n}$, we have $\frac{1}{a_0} \leq \frac{1}{n}$.
    have h_a0_le_n : (a 0 : ℝ) ≥ n := by
      have h_a0_ge_n : (1 / (a 0 : ℝ)) ≤ 1 / n := by
        exact h_sum ▸ Summable.le_tsum ( show Summable fun i : ℕ => ( 1 : ℝ ) / a i from by by_contra h; rw [ tsum_eq_zero_of_not_summable h ] at h_sum; exact absurd h_sum ( by positivity ) ) 0 ( fun i _ => by positivity );
      rw [ div_le_div_iff₀ ] at h_a0_ge_n <;> norm_cast at * <;> linarith [ h_pos 0 ];
    by_cases h : a 0 = n <;> simp_all +decide [ u_seq ];
    · have h_contra : ∑' i, (1 / (a i) : ℝ) > (1 / (a 0) : ℝ) := by
        refine' lt_of_lt_of_le _ ( Summable.sum_le_tsum ( Finset.range 2 ) ( fun _ _ => by positivity ) _ ) <;> norm_num [ Finset.sum_range_succ, h ];
        · exact h_pos 1;
        · exact ( by contrapose! h_sum; rw [ tsum_eq_zero_of_not_summable h_sum ] ; positivity );
      aesop;
    · gcongr ; norm_cast ; cases lt_or_gt_of_ne h <;> cases lt_or_gt_of_ne h_neq <;> linarith [ show a 0 ≥ n + 2 from by omega ] ;

/-
The limit of the comparison sequence term for n >= 2 is c_l^(1/4).
-/
lemma limit_u_seq_general (n : ℕ) :
  Filter.Tendsto (fun i => (u_seq n i) ^ (-((1/2 : ℝ) ^ (i + 1)))) Filter.atTop (nhds (c (l_val n) ^ (1/4 : ℝ))) := by
    -- For i ≥ 2, u_seq n i = 1 / s_{i-2}(l).
    have h_u_seq_eq : ∀ i ≥ 2, u_seq n i = 1 / (generalized_sylvester (l_val n) (i - 2) : ℝ) := by
      unfold u_seq; aesop;
    -- Let j = i-2. Then i+1 = j+3 and the exponent is 2^{-(j+3)} = 2^{-(j+1)} * 2^{-2} = 2^{-(j+1)} * (1/4).
    have h_subst : Filter.Tendsto (fun j => (generalized_sylvester (l_val n) j : ℝ) ^ ((1 / 2 : ℝ) ^ (j + 1) / 4)) Filter.atTop (nhds (c (l_val n) ^ (1 / 4 : ℝ))) := by
      have h_lim : Filter.Tendsto (fun j => (generalized_sylvester (l_val n) j : ℝ) ^ ((1 / 2 : ℝ) ^ (j + 1))) Filter.atTop (nhds (c (l_val n))) := by
        convert c_exists ( l_val n ) using 1;
      convert h_lim.rpow_const _ using 1 <;> norm_num;
      exact funext fun x => by rw [ ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; ring_nf;
    have h_subst : Filter.Tendsto (fun i => (generalized_sylvester (l_val n) (i - 2) : ℝ) ^ ((1 / 2 : ℝ) ^ (i - 1) / 4)) Filter.atTop (nhds (c (l_val n) ^ (1 / 4 : ℝ))) := by
      rw [ ← Filter.tendsto_add_atTop_iff_nat 2 ] ; aesop;
    refine h_subst.congr' ?_;
    filter_upwards [ Filter.eventually_ge_atTop 2 ] with i hi ; rw [ h_u_seq_eq i hi ] ; norm_num [ Real.rpow_neg, Real.div_rpow ] ; ring_nf;
    rw [ Real.inv_rpow ( Nat.cast_nonneg _ ) ] ; rw [ ← Real.rpow_neg ( Nat.cast_nonneg _ ) ] ; rcases i with ( _ | _ | i ) <;> norm_num [ pow_succ' ] at * ; ring_nf;
    rw [ ← Real.rpow_neg ( Nat.cast_nonneg _ ) ] ; ring_nf

/-
The comparison sequence for n >= 2 is summable and sums to 1/n.
-/
lemma u_seq_general_summable_and_sum_eq (n : ℕ) (hn : 2 ≤ n) :
  Summable (u_seq n) ∧ ∑' i, u_seq n i = 1 / (n : ℝ) := by
    -- By definition of $u_seq$, we know that it satisfies the conditions of Lemma 6.
    have h_u_seq_cond : ∀ k ≥ 2, ∑ i ∈ Finset.range k, u_seq n i + (1 / (n : ℝ)) * ∏ i ∈ Finset.range k, u_seq n i = (1 / (n : ℝ)) := by
      exact u_seq_satisfies_pac_sou_final n hn |>.2.2;
    -- Since $u_i > 0$, the sum is increasing and bounded above by $1/n$, hence it converges.
    have h_u_seq_summable : Summable (u_seq n) := by
      have h_u_seq_summable : BddAbove (Set.range (fun k => ∑ i ∈ Finset.range k, u_seq n i)) := by
        use 1 / n;
        rintro x ⟨ k, rfl ⟩ ; specialize h_u_seq_cond k ; rcases k with ( _ | _ | k ) <;> norm_num at *;
        · unfold u_seq; norm_num; gcongr ; norm_cast ; linarith;
        · exact h_u_seq_cond ▸ le_add_of_nonneg_right ( mul_nonneg ( inv_nonneg.2 ( Nat.cast_nonneg _ ) ) ( Finset.prod_nonneg fun _ _ => le_of_lt ( show 0 < u_seq n _ from by unfold u_seq; split_ifs <;> first | positivity | exact one_div_pos.2 <| Nat.cast_pos.2 <| generalized_sylvester_pos _ _ ) ) );
      exact summable_iff_not_tendsto_nat_atTop_of_nonneg ( fun i => by unfold u_seq; positivity ) |>.2 fun h => by exact absurd ( h.eventually ( Filter.eventually_gt_atTop h_u_seq_summable.choose ) ) fun h' => by obtain ⟨ k, hk ⟩ := h'.exists; linarith [ h_u_seq_summable.choose_spec ( Set.mem_range_self k ) ] ;
    -- Since the product of $u_i$ tends to zero, the sum of $u_i$ must converge to $1/n$.
    have h_u_seq_limit : Filter.Tendsto (fun k => ∏ i ∈ Finset.range k, u_seq n i) Filter.atTop (nhds 0) := by
      -- Since $u_i$ tends to zero, the product $\prod_{i=0}^{k-1} u_i$ also tends to zero.
      have h_u_seq_zero : Filter.Tendsto (fun i => u_seq n i) Filter.atTop (nhds 0) := by
        convert h_u_seq_summable.tendsto_atTop_zero;
      -- Since $u_i$ tends to zero, there exists some $N$ such that for all $i \geq N$, $|u_i| < \frac{1}{2}$.
      obtain ⟨N, hN⟩ : ∃ N, ∀ i ≥ N, |u_seq n i| < 1 / 2 := by
        simpa using Metric.tendsto_atTop.mp h_u_seq_zero ( 1 / 2 ) ( by norm_num );
      -- For $k \geq N$, we can bound the product $\prod_{i=0}^{k-1} u_i$ by $\prod_{i=0}^{N-1} u_i \cdot \left(\frac{1}{2}\right)^{k-N}$.
      have h_prod_bound : ∀ k ≥ N, |∏ i ∈ Finset.range k, u_seq n i| ≤ |∏ i ∈ Finset.range N, u_seq n i| * (1 / 2) ^ (k - N) := by
        intro k hk; rw [ ← Nat.add_sub_of_le hk ] ; simp +decide [ Finset.prod_range_add, abs_mul ] ;
        exact mul_le_mul_of_nonneg_left ( by rw [ Finset.abs_prod ] ; exact le_trans ( Finset.prod_le_prod ( fun _ _ => abs_nonneg _ ) fun _ _ => le_of_lt ( hN _ ( by linarith ) ) ) ( by norm_num ) ) ( abs_nonneg _ );
      exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ N, h_prod_bound ⟩ ) ( by simpa using tendsto_const_nhds.mul ( tendsto_pow_atTop_nhds_zero_of_lt_one ( by norm_num ) ( by norm_num : ( 1 : ℝ ) / 2 < 1 ) |> Filter.Tendsto.comp <| Filter.tendsto_sub_atTop_nat N ) );
    have h_u_seq_sum_limit : Filter.Tendsto (fun k => ∑ i ∈ Finset.range k, u_seq n i) Filter.atTop (nhds (1 / (n : ℝ))) := by
      have h_u_seq_sum_limit : Filter.Tendsto (fun k => ∑ i ∈ Finset.range k, u_seq n i + (1 / (n : ℝ)) * ∏ i ∈ Finset.range k, u_seq n i) Filter.atTop (nhds (1 / (n : ℝ))) := by
        exact tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ge_atTop 2 ] with k hk; rw [ h_u_seq_cond k hk ] );
      simpa using h_u_seq_sum_limit.sub ( h_u_seq_limit.const_mul ( 1 / n : ℝ ) );
    exact ⟨ h_u_seq_summable, tendsto_nhds_unique ( h_u_seq_summable.hasSum.tendsto_sum_nat ) h_u_seq_sum_limit ⟩

/-
Inequality l < s_3(n) - 1 for n >= 2.
-/
lemma l_lt_s2_sub_one (n : ℕ) (hn : 2 ≤ n) :
  l_val n < generalized_sylvester n 2 - 1 := by
    -- By definition of $l_val$, we have $l_val n = n * (n + 1)^2 * (n + 2) / 2$.
    have h_l_val : l_val n = n * (n + 1)^2 * (n + 2) / 2 := by
      rfl;
    -- By definition of $s_3$, we have $s_3(n) - 1 = n * (n+1) * (n^2 + n + 1)$.
    have h_s3 : generalized_sylvester n 2 - 1 = n * (n + 1) * (n^2 + n + 1) := by
      -- By definition of $s_3$, we have $s_3(n) - 1 = n * (n+1) * (n^2 + n + 1)$ using the product formula.
      have h_s3 : generalized_sylvester n 2 - 1 = n * ∏ i ∈ Finset.range 2, generalized_sylvester n i := by
        exact prop_syl_2 n 2;
      simp_all +decide [ Finset.prod_range_succ ];
      rw [ show generalized_sylvester n 0 = n + 1 from rfl, show generalized_sylvester n 1 = ( n + 1 ) ^ 2 - ( n + 1 ) + 1 from rfl ] ; zify ; ring_nf;
      grind;
    exact h_l_val.symm ▸ h_s3.symm ▸ Nat.div_lt_of_lt_mul ( by nlinarith only [ hn, pow_pos ( zero_lt_two.trans_le hn ) 3 ] )

/-
Main theorem for n >= 2 without shifting (assuming a_1 != n+1).
-/
theorem main_theorem_no_shift_n_ge_2 (n : ℕ) (hn : 2 ≤ n) (a : ℕ → ℕ)
  (h_pos : ∀ i, 0 < a i)
  (h_mono : Monotone a)
  (h_sum : ∑' i, (1 : ℝ) / a i = 1 / n)
  (h_neq : a 0 ≠ n + 1) :
  Filter.liminf (fun i => (a i : ℝ) ^ ((1/2 : ℝ) ^ (i + 1))) Filter.atTop < c n := by
    -- By Lemma 6, $\sum_{i=0}^k v_i \le \sum_{i=0}^k u_i$ for all $k$.
    have h_sum_le : ∀ k, (∑ i ∈ Finset.range k, (1 / (a i : ℝ))) ≤ (∑ i ∈ Finset.range k, (u_seq n i)) := by
      -- Apply the lemma pac_sou_refined with the given conditions.
      apply pac_sou_refined;
      exact one_div_pos.mpr ( by positivity : 0 < ( n : ℝ ) );
      any_goals exact u_seq_satisfies_pac_sou_final n hn |>.1;
      any_goals exact u_seq_satisfies_pac_sou_final n hn |>.2.1;
      any_goals exact u_seq_satisfies_pac_sou_final n hn |>.2.2;
      · exact fun i => one_div_pos.mpr ( Nat.cast_pos.mpr ( h_pos i ) );
      · exact fun i j hij => one_div_le_one_div_of_le ( Nat.cast_pos.mpr ( h_pos _ ) ) ( Nat.cast_le.mpr ( h_mono hij ) );
      · intro k hk;
        convert v_satisfies_pac_sou_condition n ( by positivity ) a h_pos h_sum k using 1;
      · have := v_le_u_base_case_general n hn a h_pos h_sum h_neq; aesop;
    -- Since $\sum v_i = \sum u_i = 1/n$, we have $v_i \ge u_i$ for infinitely many $i$.
    have h_inf_ge : ∀ N, ∃ k ≥ N, (1 / (a k : ℝ)) ≥ (u_seq n k) := by
      have h_sum_eq : ∑' i, (1 / (a i : ℝ)) = ∑' i, (u_seq n i) := by
        have := u_seq_general_summable_and_sum_eq n hn; aesop;
      apply_rules [ infinitely_often_ge_of_sum_le_sum_eq ];
      · exact ( u_seq_general_summable_and_sum_eq n hn ) |>.1;
      · exact ( by contrapose! h_sum; rw [ tsum_eq_zero_of_not_summable h_sum ] ; positivity );
    -- Thus $\liminf a_i^{2^{-(i+1)}} \le \lim u_i^{-2^{-(i+1)}} = c_l^{1/4}$.
    have h_liminf_le : Filter.liminf (fun i => (a i : ℝ) ^ ((1/2 : ℝ) ^ (i + 1))) Filter.atTop ≤ (c (l_val n)) ^ (1/4 : ℝ) := by
      -- By definition of $u_seq$, we know that $\lim_{i \to \infty} u_i^{-2^{-(i+1)}} = c_l^{1/4}$.
      have h_lim_u : Filter.Tendsto (fun i => (u_seq n i) ^ (-((1/2 : ℝ) ^ (i + 1)))) Filter.atTop (nhds ((c (l_val n)) ^ (1/4 : ℝ))) := by
        convert limit_u_seq_general n using 1;
      refine' le_of_forall_pos_le_add fun ε ε_pos => _;
      -- Since $u_i^{-2^{-(i+1)}}$ converges to $c_l^{1/4}$, there exists $N$ such that for all $i \geq N$, $u_i^{-2^{-(i+1)}} \leq c_l^{1/4} + \epsilon$.
      obtain ⟨N, hN⟩ : ∃ N, ∀ i ≥ N, (u_seq n i) ^ (-((1/2 : ℝ) ^ (i + 1))) ≤ (c (l_val n)) ^ (1/4 : ℝ) + ε := by
        exact Filter.eventually_atTop.mp ( h_lim_u.eventually ( ge_mem_nhds <| lt_add_of_pos_right _ ε_pos ) );
      refine' csSup_le _ _ <;> norm_num;
      · exact ⟨ 0, ⟨ 0, fun _ _ => by positivity ⟩ ⟩;
      · intro b x hx; obtain ⟨ k, hk₁, hk₂ ⟩ := h_inf_ge ( Max.max N x ) ; specialize hx k ( le_trans ( le_max_right _ _ ) hk₁ ) ; specialize hN k ( le_trans ( le_max_left _ _ ) hk₁ ) ; norm_num at *;
        refine' le_trans hx ( le_trans _ hN );
        rw [ Real.rpow_neg_eq_inv_rpow ];
        gcongr;
        exact le_trans ( by norm_num ) ( inv_anti₀ ( show 0 < u_seq n k from by unfold u_seq; split_ifs <;> first | positivity | exact one_div_pos.mpr <| Nat.cast_pos.mpr <| generalized_sylvester_pos _ _ ) hk₂ );
    -- We know $c_n^4 = c_{s_3(n)-1}$.
    have h_c_n_pow : (c n) ^ 4 = c (generalized_sylvester n 2 - 1) := by
      have := prop_syl_4 n 2; norm_num at *; aesop;
    -- And $l < s_3(n)-1$.
    have h_l_lt_s2_sub_one : l_val n < generalized_sylvester n 2 - 1 := by
      exact l_lt_s2_sub_one n hn;
    -- Thus $c_l < c_{s_3(n)-1} = c_n^4$.
    have h_c_l_lt_c_n_pow : c (l_val n) < c (generalized_sylvester n 2 - 1) := by
      apply_rules [ c_strict_mono ];
      exact Nat.div_pos ( by nlinarith [ Nat.pow_le_pow_left hn 2 ] ) zero_lt_two;
    refine lt_of_le_of_lt h_liminf_le ?_;
    exact lt_of_lt_of_le ( Real.rpow_lt_rpow ( show 0 ≤ c ( l_val n ) from le_of_tendsto_of_tendsto' tendsto_const_nhds ( c_exists _ ) fun i => by exact Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) h_c_l_lt_c_n_pow ( by norm_num ) ) ( by rw [ ← h_c_n_pow, ← Real.rpow_natCast, ← Real.rpow_mul ( show 0 ≤ c n from le_of_tendsto_of_tendsto' tendsto_const_nhds ( c_exists _ ) fun i => by exact Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ] ; norm_num )

/-
Main theorem without shifting for any n >= 1.
-/
theorem main_theorem_no_shift (n : ℕ) (hn : 1 ≤ n) (a : ℕ → ℕ)
  (h_pos : ∀ i, 0 < a i)
  (h_mono : Monotone a)
  (h_sum : ∑' i, (1 : ℝ) / a i = 1 / n)
  (h_neq : a 0 ≠ n + 1) :
  Filter.liminf (fun i => (a i : ℝ) ^ ((1/2 : ℝ) ^ (i + 1))) Filter.atTop < c n := by
    rcases eq_or_lt_of_le hn with rfl | hn' <;> norm_num at *;
    · convert main_theorem_base_case_n_eq_1 a h_pos h_mono _ h_neq using 1;
      aesop;
    · convert main_theorem_no_shift_n_ge_2 n hn' a h_pos h_mono _ h_neq using 1 ; aesop

/-
If the first k terms of a match the Sylvester sequence, the sum of the remaining reciprocals is 1/(s_k(n)-1).
-/
lemma sum_shift_lemma (n k : ℕ) (hn : 1 ≤ n) (a : ℕ → ℕ)
  (h_sum : ∑' i, (1 : ℝ) / a i = 1 / n)
  (h_prefix : ∀ i < k, a i = generalized_sylvester n i) :
  ∑' j, (1 : ℝ) / a (j + k) = 1 / (generalized_sylvester n k - 1 : ℝ) := by
    -- Split the sum into two parts: the sum up to k-1 and the sum from k onwards.
    have h_split : ∑' i, (1 : ℝ) / (a i) = (∑ i ∈ Finset.range k, (1 : ℝ) / (a i)) + ∑' j, (1 : ℝ) / (a (j + k)) := by
      rw [ ← Summable.sum_add_tsum_nat_add ];
      exact ( by contrapose! h_sum; rw [ tsum_eq_zero_of_not_summable h_sum ] ; positivity );
    -- By the identity from prop_syl_1, we know that $\sum_{i=0}^{k-1} \frac{1}{s_i(n)} = \frac{1}{n} - \frac{1}{s_k(n)-1}$.
    have h_identity : ∑ i ∈ Finset.range k, (1 : ℝ) / (generalized_sylvester n i) = 1 / (n : ℝ) - 1 / (generalized_sylvester n k - 1 : ℝ) := by
      convert eq_sub_of_add_eq ( prop_syl_1 n hn k ) using 1;
    rw [ Finset.sum_congr rfl fun i hi => by rw [ h_prefix i ( Finset.mem_range.mp hi ) ] ] at h_split ; linarith;

/-
The infimum of the p-th powers of a set of non-negative numbers is the p-th power of the infimum.
-/
lemma csInf_image_rpow {S : Set ℝ} (hS_nonempty : S.Nonempty) (hS_nonneg : ∀ x ∈ S, 0 ≤ x) (p : ℝ) (hp : 0 < p) :
  sInf ((fun x => x ^ p) '' S) = (sInf S) ^ p := by
    -- Let $m = \inf S$. Since $S$ is non-empty and bounded below by $0$, $m$ exists and is non-negative.
    set m := sInf S with hm
    have hm_nonneg : 0 ≤ m := by
      exact le_csInf hS_nonempty hS_nonneg;
    -- Since $m$ is the infimum of $S$, for any $\epsilon > 0$, there exists an $x \in S$ such that $x < m + \epsilon$.
    have h_eps : ∀ ε > 0, ∃ x ∈ S, x < m + ε := by
      exact fun ε ε_pos => by simpa using exists_lt_of_csInf_lt ( hS_nonempty ) ( lt_add_of_pos_right m ε_pos ) ;
    refine' le_antisymm ( le_of_forall_pos_le_add fun ε ε_pos => _ ) ( le_csInf ( Set.Nonempty.image _ hS_nonempty ) fun x hx => _ );
    · -- Choose $\delta$ such that $(m + \delta)^p < m^p + \epsilon$.
      obtain ⟨δ, δ_pos, hδ⟩ : ∃ δ > 0, (m + δ) ^ p < m ^ p + ε := by
        have h_cont : Filter.Tendsto (fun δ => (m + δ) ^ p) (nhdsWithin 0 (Set.Ioi 0)) (nhds (m ^ p)) := by
          exact tendsto_nhdsWithin_of_tendsto_nhds ( ContinuousAt.tendsto ( by exact ContinuousAt.rpow ( continuousAt_const.add continuousAt_id ) continuousAt_const <| Or.inr <| by linarith ) |> fun h => h.trans <| by norm_num );
        have := h_cont.eventually ( gt_mem_nhds <| show m ^ p < m ^ p + ε by linarith ) ; have := this.and self_mem_nhdsWithin; obtain ⟨ δ, hδ₁, hδ₂ ⟩ := this.exists; exact ⟨ δ, hδ₂, hδ₁ ⟩ ;
      exact le_trans ( csInf_le ⟨ 0, Set.forall_mem_image.2 fun x hx => Real.rpow_nonneg ( hS_nonneg x hx ) _ ⟩ ⟨ Classical.choose ( h_eps δ δ_pos ), Classical.choose_spec ( h_eps δ δ_pos ) |>.1, rfl ⟩ ) ( by simpa using Real.rpow_le_rpow ( by linarith [ hS_nonneg _ ( Classical.choose_spec ( h_eps δ δ_pos ) |>.1 ) ] ) ( le_of_lt ( Classical.choose_spec ( h_eps δ δ_pos ) |>.2 ) ) hp.le |> le_trans <| by linarith );
    · rcases hx with ⟨ y, hy, rfl ⟩ ; exact Real.rpow_le_rpow ( by positivity ) ( csInf_le ⟨ 0, fun z hz => hS_nonneg z hz ⟩ hy ) ( by positivity ) ;

/-
The supremum of the p-th powers of a set of non-negative numbers is the p-th power of the supremum.
-/
lemma csSup_image_rpow {S : Set ℝ} (hS_nonempty : S.Nonempty) (hS_nonneg : ∀ x ∈ S, 0 ≤ x) (hS_bdd : BddAbove S) (p : ℝ) (hp : 0 < p) :
  sSup ((fun x => x ^ p) '' S) = (sSup S) ^ p := by
    refine' csSup_eq_of_forall_le_of_forall_lt_exists_gt _ _ _;
    · exact hS_nonempty.image _;
    · rintro _ ⟨ x, hx, rfl ⟩ ; exact Real.rpow_le_rpow ( hS_nonneg x hx ) ( le_csSup hS_bdd hx ) hp.le;
    · -- Since $w < \sup S^p$, there exists some $x \in S$ such that $x^p > w$.
      intro w hw
      obtain ⟨x, hxS, hxw⟩ : ∃ x ∈ S, x ^ p > w := by
        contrapose! hw;
        exact le_trans ( Real.rpow_le_rpow ( by exact Real.sSup_nonneg ( by aesop ) ) ( show sSup S ≤ w ^ ( 1 / p ) by exact le_trans ( csSup_le hS_nonempty fun x hx => show x ≤ w ^ ( 1 / p ) by exact le_trans ( show x ≤ ( x ^ p ) ^ ( 1 / p ) by rw [ ← Real.rpow_mul ( hS_nonneg x hx ), mul_one_div_cancel hp.ne', Real.rpow_one ] ) ( Real.rpow_le_rpow ( by exact Real.rpow_nonneg ( hS_nonneg x hx ) _ ) ( hw x hx ) ( by positivity ) ) ) ( by norm_num [ ← Real.rpow_mul ( show 0 ≤ w by exact le_trans ( Real.rpow_nonneg ( hS_nonneg _ hS_nonempty.some_mem ) _ ) ( hw _ hS_nonempty.some_mem ) ) ] ) ) ( by positivity ) ) ( by norm_num [ ← Real.rpow_mul ( show 0 ≤ w by exact le_trans ( Real.rpow_nonneg ( hS_nonneg _ hS_nonempty.some_mem ) _ ) ( hw _ hS_nonempty.some_mem ) ), hp.ne' ] );
      exact ⟨ _, ⟨ x, hxS, rfl ⟩, hxw ⟩

/-
The infimum of the p-th powers of a function is the p-th power of the infimum.
-/
lemma ciInf_rpow {ι : Type*} [Nonempty ι] {f : ι → ℝ} (hf_nonneg : ∀ i, 0 ≤ f i) (p : ℝ) (hp : 0 < p) :
  ⨅ i, f i ^ p = (⨅ i, f i) ^ p := by
    have h_inf_image_rpow : ∀ {S : Set ℝ}, S.Nonempty → (∀ x ∈ S, 0 ≤ x) → sInf ((fun x => x ^ p) '' S) = (sInf S) ^ p := by
      exact fun {S} a a_1 => csInf_image_rpow a a_1 p hp;
    convert h_inf_image_rpow ( show Set.Nonempty ( Set.range f ) from Set.range_nonempty f ) ( fun x hx => by rcases hx with ⟨ i, rfl ⟩ ; exact hf_nonneg i ) using 1;
    rw [ @ciInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
    · exact fun i => csInf_le ⟨ 0, Set.forall_mem_image.2 fun x hx => Real.rpow_nonneg ( by rcases hx with ⟨ j, rfl ⟩ ; exact hf_nonneg j ) _ ⟩ ⟨ f i, Set.mem_range_self i, rfl ⟩;
    · exact fun w hw => by rcases exists_lt_of_csInf_lt ( Set.Nonempty.image _ ⟨ _, Set.mem_range_self ( Classical.arbitrary ι ) ⟩ ) hw with ⟨ y, ⟨ x, ⟨ i, rfl ⟩, rfl ⟩, hy ⟩ ; exact ⟨ i, hy ⟩ ;

/-
The supremum of the p-th powers of a function is the p-th power of the supremum.
-/
lemma ciSup_rpow {ι : Type*} [Nonempty ι] {f : ι → ℝ} (hf_nonneg : ∀ i, 0 ≤ f i) (hf_bdd : BddAbove (Set.range f)) (p : ℝ) (hp : 0 < p) :
  ⨆ i, f i ^ p = (⨆ i, f i) ^ p := by
    convert csSup_image_rpow _ _ _ _ hp using 1;
    · rw [ @ciSup_eq_of_forall_le_of_forall_lt_exists_gt ];
      · exact fun i => le_csSup ( by rcases hf_bdd with ⟨ M, hM ⟩ ; exact ⟨ M ^ p, Set.forall_mem_image.2 fun x hx => by rcases hx with ⟨ j, rfl ⟩ ; exact Real.rpow_le_rpow ( hf_nonneg _ ) ( hM ⟨ j, rfl ⟩ ) hp.le ⟩ ) ( Set.mem_image_of_mem _ ( Set.mem_range_self _ ) );
      · exact fun w hw => by simpa using exists_lt_of_lt_csSup ( Set.Nonempty.image _ <| Set.range_nonempty _ ) hw;
    · exact Set.range_nonempty _;
    · aesop;
    · exact hf_bdd

/-
Equivalence of eventually inequalities for powers.
-/
lemma eventually_le_rpow_iff {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n) (p : ℝ) (hp : 0 < p) (y : ℝ) (hy : 0 ≤ y) :
  (∀ᶠ n in Filter.atTop, y ≤ u n ^ p) ↔ ∀ᶠ n in Filter.atTop, y ^ (1/p) ≤ u n := by
    constructor <;> intro h <;> filter_upwards [ h ] with n hn;
    · exact le_trans ( Real.rpow_le_rpow hy hn ( by positivity ) ) ( by rw [ ← Real.rpow_mul ( hu n ), mul_one_div_cancel hp.ne', Real.rpow_one ] );
    · exact le_trans ( by rw [ ← Real.rpow_mul hy, one_div_mul_cancel hp.ne', Real.rpow_one ] ) ( Real.rpow_le_rpow ( by positivity ) hn hp.le )

/-
Characterization of liminf as the supremum of partial infimums.
-/
lemma liminf_eq_ciSup_sInf_Ici {u : ℕ → ℝ} (h_bdd_below : ∃ b, ∀ n, b ≤ u n) (h_bdd_above : ∃ B, ∀ n, sInf (u '' Set.Ici n) ≤ B) :
  Filter.liminf u Filter.atTop = ⨆ n, sInf (u '' Set.Ici n) := by
    refine' csSup_eq_of_forall_le_of_forall_lt_exists_gt _ _ _ <;> norm_num [ Filter.eventually_atTop ];
    · exact ⟨ h_bdd_below.choose, ⟨ 0, fun n hn => h_bdd_below.choose_spec n ⟩ ⟩;
    · exact fun a n hn => le_trans ( by exact le_csInf ( Set.Nonempty.image _ <| Set.nonempty_Ici ) <| Set.forall_mem_image.2 fun m hm => hn m hm ) <| le_ciSup ( show BddAbove <| Set.range fun n => sInf ( u '' Set.Ici n ) from ⟨ h_bdd_above.choose, Set.forall_mem_range.2 fun n => h_bdd_above.choose_spec n ⟩ ) n;
    · intro w hw;
      rcases exists_lt_of_lt_ciSup hw with ⟨ n, hn ⟩;
      exact ⟨ _, ⟨ n, fun m mn => ( csInf_le ( show BddBelow ( u '' Set.Ici n ) from ⟨ h_bdd_below.choose, Set.forall_mem_image.2 fun m hm => h_bdd_below.choose_spec m ⟩ ) <| Set.mem_image_of_mem _ mn ) ⟩, hn ⟩

/-
The partial infimum is an eventual lower bound.
-/
lemma partial_inf_le_eventually_lower_bound {u : ℕ → ℝ} (n : ℕ) (h_bdd_below : ∃ b, ∀ k, b ≤ u k) :
  sInf (u '' Set.Ici n) ∈ {x | ∀ᶠ k in Filter.atTop, x ≤ u k} := by
    exact Filter.eventually_atTop.mpr ⟨ n, fun k hk => csInf_le ⟨ h_bdd_below.choose, Set.forall_mem_image.mpr fun x hx => h_bdd_below.choose_spec x ⟩ ⟨ k, hk, rfl ⟩ ⟩

/-
For a non-negative sequence with bounded partial infimums, liminf (u^p) = (liminf u)^p for p > 0.
-/
lemma liminf_rpow {u : ℕ → ℝ} (hu_pos : ∀ n, 0 ≤ u n) (p : ℝ) (hp : 0 < p)
  (h_bdd : ∃ B, ∀ n, sInf (u '' Set.Ici n) ≤ B) :
  Filter.liminf (fun n => u n ^ p) Filter.atTop = (Filter.liminf u Filter.atTop) ^ p := by
    convert liminf_eq_ciSup_sInf_Ici _ _ using 2;
    · convert ( ciSup_rpow _ _ _ _ ) |> Eq.symm using 1;
      rw [ liminf_eq_ciSup_sInf_Ici ];
      any_goals tauto;
      · congr! 2;
        convert csInf_image_rpow _ _ _ _ using 1;
        · exact congr_arg _ ( by ext; aesop );
        · exact ⟨ _, Set.mem_image_of_mem _ ( Set.mem_Ici.mpr le_rfl ) ⟩;
        · grind;
        · exact hp;
      · exact fun n => le_csInf ( Set.Nonempty.image _ <| Set.nonempty_Ici ) <| Set.forall_mem_image.2 fun x hx => hu_pos x;
      · exact ⟨ h_bdd.choose, Set.forall_mem_range.mpr h_bdd.choose_spec ⟩;
    · exact ⟨ 0, fun n => Real.rpow_nonneg ( hu_pos n ) _ ⟩;
    · use ( h_bdd.choose + 1 ) ^ p;
      intro n;
      by_cases h_exists : ∃ m ∈ Set.Ici n, u m ≤ h_bdd.choose + 1;
      · exact le_trans ( csInf_le ⟨ 0, Set.forall_mem_image.2 fun m hm => Real.rpow_nonneg ( hu_pos m ) _ ⟩ ⟨ h_exists.choose, h_exists.choose_spec.1, rfl ⟩ ) ( Real.rpow_le_rpow ( hu_pos _ ) h_exists.choose_spec.2 ( by positivity ) );
      · have := h_bdd.choose_spec n;
        contrapose! this;
        exact lt_of_lt_of_le ( by linarith ) ( le_csInf ( Set.Nonempty.image _ <| Set.nonempty_Ici ) <| Set.forall_mem_image.2 fun m hm => le_of_not_ge fun h => h_exists ⟨ m, hm, h ⟩ )

/-
The liminf of the shifted sequence raised to the appropriate power relates to the original liminf raised to 2^k.
-/
lemma liminf_shift_pow (a : ℕ → ℕ) (k : ℕ)
  (h_bdd : ∃ B, ∀ n, sInf ((fun i => (a i : ℝ) ^ ((1/2 : ℝ) ^ (i + 1))) '' Set.Ici n) ≤ B) :
  Filter.liminf (fun j => (a (j + k) : ℝ) ^ ((1/2 : ℝ) ^ (j + 1))) Filter.atTop =
  (Filter.liminf (fun i => (a i : ℝ) ^ ((1/2 : ℝ) ^ (i + 1))) Filter.atTop) ^ (2 ^ k : ℝ) := by
    have h_liminf_shifted : Filter.liminf (fun j => ((a (j + k) : ℝ) ^ (1 / 2 : ℝ) ^ (j + k + 1)) ^ (2 ^ k)) Filter.atTop = ((Filter.liminf (fun i => (a i : ℝ) ^ (1 / 2 : ℝ) ^ (i + 1)) Filter.atTop)) ^ (2 ^ k) := by
      have h_liminf_shifted : Filter.liminf (fun i => ((a i : ℝ) ^ (1 / 2 : ℝ) ^ (i + 1))) Filter.atTop ^ (2 ^ k) = Filter.liminf (fun i => ((a i : ℝ) ^ (1 / 2 : ℝ) ^ (i + 1)) ^ (2 ^ k)) Filter.atTop := by
        convert ( liminf_rpow _ _ _ _ ) |> Eq.symm using 1;
        rotate_left 1;
        rotate_left;
        use fun i => ( a i : ℝ ) ^ ( 1 / 2 : ℝ ) ^ ( i + 1 );
        exacts [ fun n => Real.rpow_nonneg ( Nat.cast_nonneg _ ) _, 2 ^ k, by positivity, h_bdd, by norm_cast, by norm_cast ];
      rw [ h_liminf_shifted, Filter.liminf_eq, Filter.liminf_eq ];
      congr! 3;
      simp +zetaDelta at *;
      exact ⟨ fun ⟨ N, hN ⟩ => ⟨ N + k, fun n hn => by convert hN ( n - k ) ( Nat.le_sub_of_add_le hn ) using 1; rw [ Nat.sub_add_cancel ( by linarith ) ] ⟩, fun ⟨ N, hN ⟩ => ⟨ N + k, fun n hn => by convert hN ( n + k ) ( by linarith ) using 1 ⟩ ⟩;
    convert h_liminf_shifted using 3 ; norm_num [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; ring_nf;
    · norm_num [ Real.rpow_add, Real.rpow_neg ] ; ring_nf;
      norm_num [ mul_assoc ];
      norm_num [ ← mul_assoc, ← mul_pow ];
    · norm_cast

/-
For any $n \ge 1$ and $k \ge 0$, the generalized Sylvester sequence term $s_k(n)$ is at least 2.
-/
lemma generalized_sylvester_ge_two (n k : ℕ) (hn : 1 ≤ n) : 2 ≤ generalized_sylvester n k := by
  induction' k with k ih <;> norm_num [ *, generalized_sylvester ] at * ; nlinarith [ ( by norm_cast : ( 1 : ℝ ) ≤ n ) ] ;
  nlinarith [ Nat.sub_add_cancel ( by nlinarith : generalized_sylvester n k ≤ generalized_sylvester n k ^ 2 ) ]

/-
The limit inferior of a non-negative sequence is non-negative.
-/
lemma liminf_nonneg {u : ℕ → ℝ} (h : ∀ n, 0 ≤ u n) : 0 ≤ Filter.liminf u Filter.atTop := by
  by_contra h_neg; simp_all +decide [ Filter.liminf_eq ] ; (
  exact h_neg.not_ge <| le_trans ( by norm_num ) <| le_csSup ( show BddAbove { a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → a ≤ u b } from by exact ( by by_contra h; rw [ Real.sSup_of_not_bddAbove h ] at h_neg; linarith ) ) ⟨ 0, fun n hn => h n ⟩)

/-
If the first $k$ terms of $a$ match the generalized Sylvester sequence but the $k$-th term does not, then the shifted sequence $a_{j+k}$ satisfies the strict inequality condition with respect to the constant $c_{s_k(n)-1}$.
-/
lemma shifted_main_result (n k : ℕ) (hn : 1 ≤ n) (a : ℕ → ℕ)
  (h_pos : ∀ i, 0 < a i)
  (h_mono : Monotone a)
  (h_sum : ∑' i, (1 : ℝ) / a i = 1 / n)
  (hk_eq : ∀ j < k, a j = generalized_sylvester n j)
  (hk_ne : a k ≠ generalized_sylvester n k) :
  Filter.liminf (fun j => (a (j + k) : ℝ) ^ ((1/2 : ℝ) ^ (j + 1))) Filter.atTop < c (generalized_sylvester n k - 1) := by
    convert main_theorem_no_shift ( generalized_sylvester n k - 1 ) _ _ _ _ _ _ using 1 <;> norm_num at *;
    · exact Nat.le_sub_one_of_lt ( generalized_sylvester_ge_two n k hn );
    · exact fun i => h_pos _;
    · exact fun i j hij => h_mono ( by simpa using hij );
    · convert sum_shift_lemma n k hn a _ _ using 11;
      · aesop_cat;
      · aesop;
      · rw [ Nat.cast_sub ] <;> norm_num ; linarith [ generalized_sylvester_ge_two n k hn ];
      · aesop;
      · assumption;
    · rw [ Nat.sub_add_cancel ( by linarith [ generalized_sylvester_ge_two n k hn ] ) ] ; aesop

/-
If the sequence of partial infimums of a real-valued sequence is not bounded above, then its limit inferior is 0 (in Lean's Real).
-/
lemma liminf_eq_zero_of_not_bdd {u : ℕ → ℝ} (h : ¬ ∃ B, ∀ n, sInf (u '' Set.Ici n) ≤ B) : Filter.liminf u Filter.atTop = 0 := by
  norm_num [ Filter.liminf_eq ];
  rw [ Real.sSup_of_not_bddAbove ];
  contrapose! h;
  obtain ⟨ M, hM ⟩ := h;
  use Max.max M 0;
  intro n;
  by_cases h_exists : ∃ m, ∀ k ≥ n, m ≤ u k;
  · have := hM ⟨ n, fun k hk => show sInf ( u '' Set.Ici n ) ≤ u k from csInf_le ⟨ h_exists.choose, Set.forall_mem_image.2 fun x hx => h_exists.choose_spec x hx ⟩ <| Set.mem_image_of_mem _ hk ⟩ ; aesop;
  · rw [ Real.sInf_of_not_bddBelow ] <;> norm_num;
    exact fun ⟨ m, hm ⟩ => h_exists ⟨ m, fun k hk => hm ⟨ k, hk, rfl ⟩ ⟩

/-
Main Theorem: Let $n$ be a positive integer, and let $a_1 \leq a_2 \leq \cdots$ be a sequence of positive integers. Assume that $a_i \neq s_i(n)$ for some $i$, and that $\frac{1}{n} = \sum_{i=1}^\infty \frac{1}{a_i}$. Then $\liminf_{i\to\infty} a_i^{2^{-i}} < c_n$.
-/
theorem main_theorem (n : ℕ) (hn : 1 ≤ n) (a : ℕ → ℕ)
  (h_pos : ∀ i, 0 < a i)
  (h_mono : Monotone a)
  (h_sum : ∑' i, (1 : ℝ) / a i = 1 / n)
  (h_neq : ∃ i, a i ≠ generalized_sylvester n i) :
  Filter.liminf (fun i => (a i : ℝ) ^ ((1/2 : ℝ) ^ (i + 1))) Filter.atTop < c n := by
  -- 1. Define k
  have h_ex_k : ∃ k, a k ≠ generalized_sylvester n k := h_neq
  let k := Nat.find h_ex_k
  have hk_ne : a k ≠ generalized_sylvester n k := Nat.find_spec h_ex_k
  have hk_eq : ∀ j < k, a j = generalized_sylvester n j := fun j hj => by
    have := Nat.find_min h_ex_k hj
    push_neg at this
    exact this
  -- 2. Case split on boundedness
  by_cases h_bdd : ∃ B, ∀ m, sInf ((fun i => (a i : ℝ) ^ ((1/2 : ℝ) ^ (i + 1))) '' Set.Ici m) ≤ B
  · -- Case bounded
    -- Apply shifted result
    have h_shifted_lt : Filter.liminf (fun j => (a (j + k) : ℝ) ^ ((1/2 : ℝ) ^ (j + 1))) Filter.atTop < c (generalized_sylvester n k - 1) :=
      shifted_main_result n k hn a h_pos h_mono h_sum hk_eq hk_ne
    -- Relate liminfs
    have h_shift_eq : Filter.liminf (fun j => (a (j + k) : ℝ) ^ ((1/2 : ℝ) ^ (j + 1))) Filter.atTop =
        (Filter.liminf (fun i => (a i : ℝ) ^ ((1/2 : ℝ) ^ (i + 1))) Filter.atTop) ^ (2 ^ k : ℝ) :=
      liminf_shift_pow a k h_bdd
    -- Relate constants
    have h_c_eq : c (generalized_sylvester n k - 1) = c n ^ (2 ^ k : ℝ) := by
      rw [← prop_syl_4 n k]
      norm_cast
    rw [h_shift_eq, h_c_eq] at h_shifted_lt
    -- Remove powers
    have h_pow_pos : 0 < (2 : ℝ) ^ k := by positivity
    rw [← Real.rpow_lt_rpow_iff _ _ h_pow_pos]
    · exact h_shifted_lt
    · apply liminf_nonneg
      intro i
      apply Real.rpow_nonneg
      apply Nat.cast_nonneg
    · apply le_of_lt
      exact lt_of_le_of_lt (Real.sqrt_nonneg _) (c_bounds n (by linarith)).1
  · -- Case unbounded
    have h_lim_zero : Filter.liminf (fun i => (a i : ℝ) ^ ((1/2 : ℝ) ^ (i + 1))) Filter.atTop = 0 :=
      liminf_eq_zero_of_not_bdd h_bdd
    rw [h_lim_zero]
    apply lt_of_le_of_lt (Real.sqrt_nonneg _) (c_bounds n (by linarith)).1

/-
Definition of the usual Sylvester sequence s_i. Note that we use 0-based indexing where index 0 corresponds to s_1 in the paper.
-/
def sylvester : ℕ → ℕ
| 0 => 2
| (i + 1) => (sylvester i)^2 - (sylvester i) + 1

/-
Definition of the Vardi constant.
-/
noncomputable def usual_sylvester_seq_pow (i : ℕ) : ℝ :=
  (sylvester i : ℝ) ^ ((1/2 : ℝ) ^ (i + 1))

noncomputable def vardi_constant : ℝ :=
  limUnder Filter.atTop usual_sylvester_seq_pow

/-
Erdős 315: Let $a_1 \leq a_2 \leq \cdots$ be a sequence of positive integers. Assume that $a_i \neq s_i(0)$ for some $i$, and that $1 = \sum_{i=1}^\infty \frac{1}{a_i}$. Then $\liminf_{i\to\infty} a_i^{2^{-i}} < c_1$, where $c_1$ is the Vardi constant.
-/
theorem erdos_315 (a : ℕ → ℕ)
  (h_pos : ∀ i, 0 < a i)
  (h_mono : Monotone a)
  (h_sum : ∑' i, (1 : ℝ) / a i = 1)
  (h_neq : ∃ i, a i ≠ sylvester i) :
  Filter.liminf (fun i => (a i : ℝ) ^ ((1/2 : ℝ) ^ (i + 1))) Filter.atTop < vardi_constant := by
  convert main_theorem 1 ( by norm_num ) a h_pos h_mono _ using 1;
  · rw [ show c 1 = vardi_constant from ?_ ];
    · rw [ show generalized_sylvester 1 = sylvester from ?_ ];
      · aesop;
      · funext i; induction' i with i ih; simp [sylvester];
        · rfl;
        · -- By definition of generalized_sylvester, we have generalized_sylvester 1 (i + 1) = (generalized_sylvester 1 i)^2 - generalized_sylvester 1 i + 1.
          have h_gen_sylvester_succ : generalized_sylvester 1 (i + 1) = (generalized_sylvester 1 i)^2 - generalized_sylvester 1 i + 1 := by
            rfl;
          aesop;
    · unfold c vardi_constant;
      congr! 2;
      funext i; simp [sylvester_seq_pow, usual_sylvester_seq_pow];
      congr! 2;
      induction i <;> simp +decide [ *, generalized_sylvester ];
      exact rfl;
  · aesop

#print axioms erdos_315
-- 'erdos_315' depends on axioms: [propext, Classical.choice, Quot.sound]
