/-

This is a Lean formalization of a solution to Erdős Problem 337.
https://www.erdosproblems.com/337


Aristotle auto-formalized the proof by Ruzsa and Turjányi.


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/

import Mathlib

namespace Erdos337


open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0

noncomputable section

/-
Definitions of iterated sumset, counting function, basis of order h, and thin basis property.
-/

/-- The k-fold sumset kA = {a_1 + ... + a_k | a_i ∈ A} -/
def iterated_sumset (A : Set ℕ) : ℕ → Set ℕ
| 0 => {0}
| (k + 1) => A + iterated_sumset A k

/-- The counting function A(x) = |A ∩ [1, x]| -/
noncomputable def count_in_range (A : Set ℕ) (x : ℝ) : ℕ :=
  (A ∩ Set.Icc 1 ⌊x⌋₊).ncard

/-- A set A is a basis of order h if hA contains all sufficiently large integers -/
def is_basis_of_order (A : Set ℕ) (h : ℕ) : Prop :=
  ∃ N₀, Set.Ici N₀ ⊆ iterated_sumset A h

/-- A basis B is thin if B(x) ≤ C x^(1/h) -/
def is_thin_basis (B : Set ℕ) (h : ℕ) (C : ℝ) : Prop :=
  is_basis_of_order B h ∧ ∀ x : ℝ, x ≥ 1 → (count_in_range B x : ℝ) ≤ C * x^(1 / (h : ℝ))

/-
Structure encapsulating a thin basis of order h.
-/
structure ThinBasis (h : ℕ) where
  B : Set ℕ
  is_basis : is_basis_of_order B h
  C : ℝ
  C_pos : C > 0
  thin_condition : ∀ x : ℝ, x ≥ 1 → (count_in_range B x : ℝ) ≤ C * x^(1 / (h : ℝ))

/-
Structure defining the properties of the sequence d_n.
-/
open scoped Pointwise

structure ValidSequence (h : ℕ) (r : ℝ) (C : ℝ) where
  d : ℕ → ℕ
  d_pos : ∀ n, 0 < d n
  d_strict_mono : StrictMono d
  d_one_gt_one : 1 < d 0
  cond_sum : ∀ n, 1 ≤ n → (∑ k ∈ Finset.range n, (d k : ℝ)^r) ≤ (1/4) * (d n : ℝ)^(1 / (h : ℝ))
  cond_B : ∀ n, C * (d n : ℝ)^(1 / (h : ℝ)) ≤ (1/4) * (d n : ℝ)^r
  cond_half : ∀ n, (d n : ℝ)^r ≤ (1/2) * (d n : ℝ)

/-
Lemma: For any S, there exists a large enough D such that any d >= D satisfies the growth conditions.
-/
theorem exists_next_d (h : ℕ) (r : ℝ) (C : ℝ) (S : ℝ)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) (C_pos : C > 0) :
  ∃ D : ℕ, ∀ d : ℕ, d ≥ D →
    (d : ℝ)^r ≤ (1/2) * (d : ℝ) ∧
    S ≤ (1/4) * (d : ℝ)^(1 / (h : ℝ)) ∧
    C * (d : ℝ)^(1 / (h : ℝ)) ≤ (1/4) * (d : ℝ)^r := by
      -- Let's choose D such that for all d ≥ D, the conditions on d^r and d^(1/h) hold.
      obtain ⟨D₁, hD₁⟩ : ∃ D₁ : ℕ, ∀ d ≥ D₁, (d : ℝ)^r ≤ (1 / 2) * (d : ℝ) := by
        -- Since $r < 1$, we have $d^r \leq \frac{1}{2}d$ for sufficiently large $d$.
        have h_lim : Filter.Tendsto (fun d : ℕ => (d : ℝ)^r / d) Filter.atTop (nhds 0) := by
          have h_lim : Filter.Tendsto (fun d : ℕ => (d : ℝ)^(r - 1)) Filter.atTop (nhds 0) := by
            simpa using tendsto_rpow_neg_atTop ( show 0 < - ( r - 1 ) by linarith ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop;
          refine h_lim.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with d hd using by rw [ Real.rpow_sub_one ( by positivity ) ] );
        have := h_lim.eventually ( gt_mem_nhds <| show 0 < 1 / 2 by norm_num ) ; aesop;
        exact ⟨ w + 1, fun d hd => by have := h_1 d ( by linarith ) ; rw [ div_lt_iff₀ ( by norm_cast; linarith ) ] at this; linarith ⟩;
      -- Let's choose D such that for all d ≥ D, the conditions on d^(1/h) hold.
      obtain ⟨D₂, hD₂⟩ : ∃ D₂ : ℕ, ∀ d ≥ D₂, (d : ℝ)^(1 / (h : ℝ)) ≥ 4 * S := by
        have h_lim_inf : Filter.Tendsto (fun d : ℕ => (d : ℝ)^(1 / (h : ℝ))) Filter.atTop Filter.atTop := by
          exact tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop;
        exact Filter.eventually_atTop.mp ( h_lim_inf.eventually_ge_atTop ( 4 * S ) );
      -- Let's choose D such that for all d ≥ D, the conditions on C * d^(1/h) hold.
      obtain ⟨D₃, hD₃⟩ : ∃ D₃ : ℕ, ∀ d ≥ D₃, C * (d : ℝ)^(1 / (h : ℝ)) ≤ (1 / 4) * (d : ℝ)^r := by
        have h_lim : Filter.Tendsto (fun d : ℕ => C * (d : ℝ)^(1 / (h : ℝ)) / (d : ℝ)^r) Filter.atTop (nhds 0) := by
          norm_num +zetaDelta at *;
          -- We can rewrite the limit expression using the properties of exponents.
          suffices h_exp : Filter.Tendsto (fun d : ℕ => C * (d : ℝ)^(1 / (h : ℝ) - r)) Filter.atTop (nhds 0) by
            refine h_exp.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with d hd using by rw [ Real.rpow_sub ( by positivity ) ] ; ring );
          simpa using tendsto_const_nhds.mul ( tendsto_rpow_neg_atTop ( show 0 < - ( 1 / ( h : ℝ ) - r ) by norm_num; nlinarith [ inv_mul_cancel₀ ( by positivity : ( h : ℝ ) ≠ 0 ), ( by norm_cast : ( 3 : ℝ ) ≤ h ) ] ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
        have := h_lim.eventually ( gt_mem_nhds <| show 0 < 1 / 4 by norm_num ) ; aesop;
        exact ⟨ w + 1, fun d hd => by have := h_1 d ( by linarith ) ; rw [ div_lt_iff₀ ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _ ) ] at this; linarith ⟩;
      exact ⟨ Max.max D₁ ( Max.max D₂ D₃ ), fun d hd => ⟨ hD₁ d ( le_trans ( le_max_left _ _ ) hd ), by linarith [ hD₂ d ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hd ) ], hD₃ d ( le_trans ( le_max_of_le_right ( le_max_right _ _ ) ) hd ) ⟩ ⟩

/-
Theorem: There exists a valid sequence d_n.
-/
theorem exists_valid_sequence (h : ℕ) (h_ge_3 : h ≥ 3) (r : ℝ) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) (C : ℝ) (C_pos : C > 0) :
  ∃ S : ValidSequence h r C, True := by
    simp +zetaDelta at *;
    -- Apply the next_d lemma to construct the sequence.
    have next_d_step : ∀ S : ℕ, ∃ d : ℕ, d > S ∧ (d : ℝ)^r ≤ (1/2) * (d : ℝ) ∧ C * (d : ℝ)^(1 / (h : ℝ)) ≤ (1/4) * (d : ℝ)^r ∧ S ≤ (1/4) * (d : ℝ)^(1 / (h : ℝ)) := by
      intro S; have := exists_next_d h r C S; aesop;
      exact ⟨ w + S + 1, by linarith, h_1 _ ( by linarith ) |>.1, h_1 _ ( by linarith ) |>.2.2, h_1 _ ( by linarith ) |>.2.1 ⟩;
    choose f hf1 hf2 hf3 hf4 using next_d_step;
    use fun n => Nat.recOn n ( f 1 ) fun n ih => f ih;
    all_goals intros; induction ‹ℕ› <;> aesop;
    · linarith [ hf1 1 ];
    · linarith [ hf1 ( Nat.rec ( f 1 ) ( fun n ih => f ih ) n ) ];
    · exact strictMono_nat_of_lt_succ fun n => hf1 _;
    · rw [ Finset.sum_range_succ ];
      rcases n <;> aesop;
      · have := hf4 ( f 1 ) ; norm_num at * ; linarith [ hf2 1, hf3 1 ] ;
      · have := hf4 ( f ( Nat.rec ( f 1 ) ( fun n ih => f ih ) n ) );
        refine le_trans ( add_le_add a ( hf2 _ ) ) ?_;
        nlinarith [ show ( f ( Nat.rec ( f 1 ) ( fun n ih => f ih ) n ) : ℝ ) ≥ 1 by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ( by linarith [ hf1 ( Nat.rec ( f 1 ) ( fun n ih => f ih ) n ) ] ), show ( f ( Nat.rec ( f 1 ) ( fun n ih => f ih ) n ) : ℝ ) ^ ( ( h : ℝ ) ⁻¹ ) ≤ ( f ( Nat.rec ( f 1 ) ( fun n ih => f ih ) n ) : ℝ ) by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( mod_cast Nat.one_le_iff_ne_zero.mpr ( by linarith [ hf1 ( Nat.rec ( f 1 ) ( fun n ih => f ih ) n ) ] ) ) ( inv_le_one_of_one_le₀ ( by norm_cast; linarith ) ) ) ( by norm_num ) ]

/-
Definitions of L_n, I_n, and the constructed set A.
-/
open scoped Pointwise

def L (r : ℝ) (dn : ℕ) : ℕ := ⌊(dn : ℝ)^r⌋₊

def I (dn : ℕ) (Ln : ℕ) : Set ℕ := Set.Icc (dn - Ln + 1) dn

def constructed_A (B : Set ℕ) (d : ℕ → ℕ) (r : ℝ) : Set ℕ :=
  B ∪ (⋃ n, I (d n) (L r (d n)))

/-
Step 3: A is a basis of order h because B is a subset of A and B is a basis of order h.
-/
theorem step3_basis (h : ℕ) (B : Set ℕ) (d : ℕ → ℕ) (r : ℝ)
  (h_basis : is_basis_of_order B h) :
  is_basis_of_order (constructed_A B d r) h := by
    -- Since $B \subseteq A$, we have $hB \subseteq hA$.
    have hB_subset_hA : ∀ n, iterated_sumset B n ⊆ iterated_sumset (constructed_A B d r) n := by
      intro n;
      induction' n with n ih;
      · aesop;
      · -- By definition of iterated sumset, we have $B + iterated_sumset B n \subseteq constructed_A B d r + iterated_sumset (constructed_A B d r) n$.
        have h_sumset_subset : B + iterated_sumset B n ⊆ constructed_A B d r + iterated_sumset (constructed_A B d r) n := by
          exact Set.add_subset_add ( Set.subset_def.mpr fun x hx => by exact Set.mem_union_left _ hx ) ih;
        exact h_sumset_subset;
    obtain ⟨ N₀, hN₀ ⟩ := h_basis; use N₀; exact Set.Subset.trans hN₀ ( hB_subset_hA h ) ;

/-
Lemma: The sum of lengths of intervals I_k up to n is bounded by 2 * d_n^r.
-/
open scoped Pointwise

open Filter

theorem sum_L_bound (h : ℕ) (r : ℝ) (C : ℝ) (S : ValidSequence h r C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) (C_pos : C > 0) :
  ∀ᶠ n in atTop, (∑ k ∈ Finset.range (n + 1), (L r (S.d k) : ℝ)) ≤ 2 * (S.d n : ℝ)^r := by
    -- By definition of $L$, we know that $L r (S.d k) \leq (S.d k : ℝ)^r$ for all $k$.
    have h_L_le : ∀ k, (L r (S.d k) : ℝ) ≤ (S.d k : ℝ)^r := by
      exact fun k => by exact_mod_cast Nat.floor_le ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ;
    -- By definition of $d$, we know that $\sum_{k=0}^{n-1} (d k : ℝ)^r \leq \frac{1}{4} (d n : ℝ)^{1/h}$ for all $n$.
    have h_sum_le : ∀ n, (∑ k ∈ Finset.range n, (S.d k : ℝ)^r) ≤ (1 / 4) * (S.d n : ℝ)^(1 / h : ℝ) := by
      intro n; induction' n with n ih <;> norm_num [ Finset.sum_range_succ ] ; aesop;
      · positivity;
      · have := S.cond_sum ( n + 1 ) ; norm_num [ Finset.sum_range_succ ] at * ; linarith;
    -- By definition of $d$, we know that $(d n : ℝ)^{1/h} \leq (d n : ℝ)^r$ for sufficiently large $n$.
    have h_exp_le : ∀ᶠ n in Filter.atTop, (S.d n : ℝ)^(1 / h : ℝ) ≤ (S.d n : ℝ)^r := by
      refine' Filter.eventually_atTop.mpr ⟨ 1, fun n hn => _ ⟩;
      exact Real.rpow_le_rpow_of_exponent_le ( mod_cast Nat.one_le_iff_ne_zero.mpr <| ne_of_gt <| S.d_pos n ) <| by nlinarith [ show ( h : ℝ ) ≥ 3 by norm_cast, one_div_mul_cancel <| show ( h : ℝ ) ≠ 0 by positivity ] ;
    filter_upwards [ h_exp_le, Filter.eventually_gt_atTop 0 ] with n hn hn' ; norm_num [ Finset.sum_range_succ ] at *;
    linarith [ h_sum_le n, show ( ∑ k ∈ Finset.range n, ( L r ( S.d k ) : ℝ ) ) ≤ ∑ k ∈ Finset.range n, ( S.d k : ℝ ) ^ r from Finset.sum_le_sum fun _ _ => h_L_le _, h_L_le n ]

/-
For large n, d_{n+1} > 2 * d_n.
-/
theorem d_super_growth (h : ℕ) (r : ℝ) (C : ℝ) (S : ValidSequence h r C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) :
  ∀ᶠ n in atTop, 2 * S.d n < S.d (n + 1) := by
    -- From `cond_sum`, we have $d_n^r \le \sum_{k \le n} d_k^r \le \frac{1}{4} d_{n+1}^{1/h}$.
    have h_cond_sum : ∀ n, (S.d n : ℝ)^r ≤ (1/4) * (S.d (n + 1) : ℝ)^(1 / (h : ℝ)) := by
      have := S.cond_sum;
      intro n; specialize this ( n + 1 ) ; simp_all ( config := { decide := Bool.true } ) [ Finset.sum_range_succ ] ;
      exact le_trans ( le_add_of_nonneg_left <| Finset.sum_nonneg fun _ _ => Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) this;
    -- Raising to power $h$, $4^h d_n^{rh} \le d_{n+1}$.
    have h_pow_h : ∀ n, (4 : ℝ)^h * (S.d n : ℝ)^(r * h) ≤ (S.d (n + 1) : ℝ) := by
      intro n
      have : (4 : ℝ)^h * (S.d n : ℝ)^(r * h) ≤ (4 : ℝ)^h * ((1/4) * (S.d (n + 1) : ℝ)^(1 / (h : ℝ)))^h := by
        rw [ Real.rpow_mul ] <;> norm_cast <;> aesop;
        exact pow_le_pow_left₀ ( by positivity ) ( h_cond_sum n ) _;
      convert this using 1 ; ring;
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ), inv_mul_cancel₀ ( by positivity ), Real.rpow_one, mul_assoc, ← mul_pow ] ; norm_num;
    -- Since $r > 1 - 1/h$, $rh > h - 1 \ge 2$.
    have h_rh_gt_2 : r * h > 2 := by
      nlinarith [ show ( h : ℝ ) ≥ 3 by norm_cast, one_div_mul_cancel ( by positivity : ( h : ℝ ) ≠ 0 ) ];
    -- Since $d_n \to \infty$, there exists $N$ such that for all $n \geq N$, $(S.d n : ℝ)^{rh - 1} > 2$.
    obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, (S.d n : ℝ)^(r * h - 1) > 2 := by
      have h_lim_inf : Filter.Tendsto (fun n => (S.d n : ℝ)^(r * h - 1)) Filter.atTop Filter.atTop := by
        exact tendsto_rpow_atTop ( by linarith ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop.comp <| S.d_strict_mono.tendsto_atTop;
      simpa using h_lim_inf.eventually_gt_atTop 2;
    -- For $n \geq N$, we have $4^h * (S.d n : ℝ)^{rh} > 2 * (S.d n : ℝ)$.
    have h_ineq : ∀ n ≥ N, (4 : ℝ)^h * (S.d n : ℝ)^(r * h) > 2 * (S.d n : ℝ) := by
      intro n hn; have := hN n hn; rw [ Real.rpow_sub ] at this <;> aesop;
      · rw [ lt_div_iff₀ ] at this <;> nlinarith [ show ( 4 : ℝ ) ^ h > 1 by exact one_lt_pow₀ ( by norm_num ) ( by linarith ), show ( S.d n : ℝ ) > 0 by exact Nat.cast_pos.mpr ( S.d_pos n ) ];
      · exact S.d_pos n;
    filter_upwards [ Filter.eventually_ge_atTop N ] with n hn using by exact_mod_cast h_ineq n hn |> lt_of_lt_of_le <| h_pow_h n;

/-
For large x, if d_n <= x < d_{n+1}, then for all k >= n+2, I_k is disjoint from [1, x].
-/
theorem intervals_disjoint_large (h : ℕ) (r : ℝ) (C : ℝ) (S : ValidSequence h r C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) :
  ∀ᶠ x in atTop, ∀ n, S.d n ≤ x ∧ x < S.d (n + 1) →
    ∀ k ≥ n + 2, Disjoint (I (S.d k) (L r (S.d k))) (Set.Icc 1 ⌊x⌋₊) := by
      -- By `d_super_growth`, for large enough $x$, $d_k > 2 * d_{n+1}$.
      have h_dk_gt_2dn_plus_1 : ∀ᶠ x in atTop, ∀ n, S.d n ≤ x ∧ x < S.d (n + 1) → ∀ k ≥ n + 2, 2 * S.d (n + 1) < S.d k := by
        have h_dk_gt_2dn_plus_1 : ∀ᶠ n in atTop, 2 * S.d (n + 1) < S.d (n + 2) := by
          have := d_super_growth h r C S h_ge_3 hr1 hr2; aesop;
          exact ⟨ w, fun n hn => h_1 _ ( by linarith ) ⟩;
        aesop;
        use S.d w;
        bound;
        induction a_3 <;> aesop;
        · contrapose! h_1;
          exact ⟨ n, le_of_not_lt fun h => by linarith [ S.d_strict_mono.monotone h ], h_1 ⟩;
        · linarith [ S.d_strict_mono ( Nat.lt_succ_self m ) ];
      filter_upwards [ h_dk_gt_2dn_plus_1 ] with x hx;
      intros n hn k hk; specialize hx n hn k hk; unfold I; aesop;
      -- By `cond_half`, $L_k \le d_k^r \le d_k/2$.
      have h_cond_half : L r (S.d k) ≤ (S.d k : ℝ) / 2 := by
        have := S.cond_half k; unfold L at *; aesop;
        exact le_trans ( Nat.floor_le ( by positivity ) ) ( this.trans ( by ring_nf; norm_num ) );
      rw [ Set.disjoint_left ] ; aesop;
      rw [ le_div_iff₀ ] at h_cond_half <;> norm_cast at * ; linarith [ Nat.sub_add_cancel <| show L r ( S.d k ) ≤ S.d k from Nat.floor_le_of_le <| by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( mod_cast Nat.one_le_iff_ne_zero.mpr <| ne_of_gt <| S.d_pos _ ) <| show r ≤ 1 by linarith ) <| by norm_num ]

/-
For large n, 2 * d_n^r + d_{n+1}^r <= 2 * (d_{n+1} - d_{n+1}^r)^r.
-/
theorem final_inequality (h : ℕ) (r : ℝ) (C : ℝ) (S : ValidSequence h r C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) :
  ∀ᶠ n in atTop, 2 * (S.d n : ℝ)^r + (S.d (n + 1) : ℝ)^r ≤ 2 * ((S.d (n + 1) : ℝ) - (S.d (n + 1) : ℝ)^r)^r := by
    -- Divide by $d_{n+1}^r$.
    have h_div : ∀ᶠ n in atTop, 2 * ((S.d n : ℝ) / (S.d (n + 1)))^r + 1 ≤ 2 * (1 - (S.d (n + 1) : ℝ)^(r - 1))^r := by
      -- Since $d_n^r \leq \frac{1}{4} d_{n+1}^{1/h}$, we have $\frac{d_n^r}{d_{n+1}^r} \leq \frac{1}{4} d_{n+1}^{1/h - r}$.
      have h_frac_bound : ∀ᶠ n in atTop, ((S.d n : ℝ) / (S.d (n + 1)))^r ≤ (1 / 4) * (S.d (n + 1))^(1 / (h : ℝ) - r) := by
        -- From `cond_sum`, $d_n^r \le \frac{1}{4} d_{n+1}^{1/h}$.
        have h_cond_sum : ∀ n, (S.d n : ℝ)^r ≤ (1 / 4) * (S.d (n + 1))^(1 / (h : ℝ)) := by
          intro n; have := S.cond_sum ( n + 1 ) ( Nat.succ_pos n ) ; aesop;
          exact le_trans ( Finset.single_le_sum ( fun a _ => Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ( Finset.mem_range.mpr ( Nat.lt_succ_self _ ) ) ) this;
        refine Filter.eventually_atTop.mpr ⟨ 0, fun n hn => ?_ ⟩ ; rw [ Real.div_rpow ( by positivity ) ( by positivity ) ] ; aesop;
        rw [ Real.rpow_sub ( Nat.cast_pos.mpr <| S.d_pos _ ) ] ; convert div_le_div_of_nonneg_right ( h_cond_sum n ) ( Real.rpow_nonneg ( Nat.cast_nonneg <| S.d ( n + 1 ) ) r ) using 1 ; ring;
      -- Since $r > 1/h$, the exponent $1/h - r$ is negative, so $(S.d (n + 1))^{1/h - r} \to 0$ as $n \to \infty$.
      have h_exp_zero : Filter.Tendsto (fun n => (S.d (n + 1) : ℝ)^(1 / (h : ℝ) - r)) Filter.atTop (nhds 0) := by
        have h_exp_zero : Filter.Tendsto (fun n => (S.d (n + 1) : ℝ)) Filter.atTop Filter.atTop := by
          exact tendsto_natCast_atTop_atTop.comp ( S.d_strict_mono.tendsto_atTop.comp ( Filter.tendsto_add_atTop_nat 1 ) );
        simpa using tendsto_rpow_neg_atTop ( show 0 < - ( 1 / ( h : ℝ ) - r ) by linarith [ show ( 1 : ℝ ) / h < r by rw [ div_lt_iff₀ ] at * <;> nlinarith [ show ( h : ℝ ) ≥ 3 by norm_cast, one_div_mul_cancel ( show ( h : ℝ ) ≠ 0 by positivity ) ] ] ) |> Filter.Tendsto.comp <| h_exp_zero;
      -- Since $r < 1$, we have $(1 - (S.d (n + 1))^{r - 1})^r \to 1$ as $n \to \infty$.
      have h_one_minus_exp_one : Filter.Tendsto (fun n => (1 - (S.d (n + 1) : ℝ)^(r - 1))^r) Filter.atTop (nhds 1) := by
        have h_one_minus_exp_one : Filter.Tendsto (fun n => (S.d (n + 1) : ℝ)^(r - 1)) Filter.atTop (nhds 0) := by
          have h_exp_zero : Filter.Tendsto (fun n => (S.d (n + 1) : ℝ)) Filter.atTop Filter.atTop := by
            exact tendsto_natCast_atTop_atTop.comp ( S.d_strict_mono.tendsto_atTop.comp ( Filter.tendsto_add_atTop_nat 1 ) );
          simpa using tendsto_rpow_neg_atTop ( by linarith : 0 < - ( r - 1 ) ) |> Filter.Tendsto.comp <| h_exp_zero;
        convert Filter.Tendsto.rpow ( tendsto_const_nhds.sub h_one_minus_exp_one ) tendsto_const_nhds _ using 2 <;> norm_num;
      have := h_one_minus_exp_one.eventually ( lt_mem_nhds <| show 1 > 3 / 4 by norm_num ) ; aesop;
      exact Filter.eventually_atTop.mp ( h_exp_zero.eventually ( gt_mem_nhds <| show 0 < 1 / 4 by norm_num ) ) |> fun ⟨ N, hN ⟩ ↦ ⟨ Max.max w ( Max.max w_1 N ), fun n hn ↦ by linarith [ h_1 n ( le_trans ( le_max_left _ _ ) hn ), h_2 n ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hn ), hN n ( le_trans ( le_max_of_le_right ( le_max_right _ _ ) ) hn ) ] ⟩;
    filter_upwards [ h_div, Filter.eventually_gt_atTop 0 ] with n hn hn';
    convert mul_le_mul_of_nonneg_right hn ( Real.rpow_nonneg ( Nat.cast_nonneg ( S.d ( n + 1 ) ) ) r ) using 1 <;> norm_num [ Real.div_rpow ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ), Real.rpow_sub ( Nat.cast_pos.mpr <| S.d_pos _ ) ] ; ring;
    · rw [ mul_inv_cancel_right₀ ( ne_of_gt ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( S.d_pos _ ) ) _ ) ) ];
    · rw [ show ( S.d ( n + 1 ) : ℝ ) - S.d ( n + 1 ) ^ r = ( 1 - S.d ( n + 1 ) ^ r / S.d ( n + 1 ) ) * S.d ( n + 1 ) by rw [ sub_mul, div_mul_cancel₀ _ ( Nat.cast_ne_zero.mpr <| ne_of_gt <| S.d_pos _ ) ] ; ring ] ; rw [ Real.mul_rpow ( sub_nonneg.mpr <| div_le_one_of_le₀ ( by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( mod_cast S.d_pos _ ) hr2.le ) <| by norm_num ) <| Nat.cast_nonneg _ ) <| Nat.cast_nonneg _ ] ; ring

/-
Algebraic bounds for the two cases in the proof of intervals_bound.
-/
theorem algebraic_step (h : ℕ) (r : ℝ) (C : ℝ) (S : ValidSequence h r C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) :
  ∀ᶠ n in atTop, ∀ x, S.d n ≤ x ∧ x < S.d (n + 1) →
    (x < S.d (n + 1) - L r (S.d (n + 1)) + 1 → 2 * (S.d n : ℝ)^r ≤ 2 * x^r) ∧
    (x ≥ S.d (n + 1) - L r (S.d (n + 1)) + 1 → 2 * (S.d n : ℝ)^r + (S.d (n + 1) : ℝ)^r ≤ 2 * x^r) := by
      have := final_inequality h r C S h_ge_3 hr1 hr2;
      filter_upwards [ this, Filter.eventually_gt_atTop 0 ] ; aesop;
      · exact Real.rpow_le_rpow ( Nat.cast_nonneg _ ) ( mod_cast left ) ( by linarith [ show ( 0 : ℝ ) ≤ r by exact le_trans ( sub_nonneg.2 <| inv_le_one_of_one_le₀ <| by norm_cast; linarith ) hr1.le ] );
      · refine le_trans a_1 ?_;
        gcongr;
        · exact sub_nonneg_of_le ( by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( mod_cast Nat.one_le_iff_ne_zero.mpr <| ne_of_gt <| S.d_pos _ ) <| show r ≤ 1 by linarith ) <| by norm_num );
        · nlinarith [ inv_mul_cancel₀ ( by positivity : ( h : ℝ ) ≠ 0 ), ( by norm_cast : ( 3 : ℝ ) ≤ h ) ];
        · contrapose! a_3;
          exact Nat.lt_succ_of_le ( Nat.le_sub_of_add_le <| by rw [ ← @Nat.cast_le ℝ ] ; push_cast; linarith [ show ( L r ( S.d ( a + 1 ) ) : ℝ ) ≤ ( S.d ( a + 1 ) : ℝ ) ^ r by exact Nat.floor_le <| by exact Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ] )

/-
Decomposition of the cardinality of the union of intervals intersected with [1, x].
-/
theorem card_decomposition (h : ℕ) (r : ℝ) (C : ℝ) (S : ValidSequence h r C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) :
  ∀ᶠ x in atTop, ∀ n, S.d n ≤ x ∧ x < S.d (n + 1) →
    (Set.ncard ((⋃ k, I (S.d k) (L r (S.d k))) ∩ Set.Icc 1 ⌊x⌋₊) : ℝ) ≤
    (∑ k ∈ Finset.range (n + 1), (L r (S.d k) : ℝ)) + (Set.ncard (I (S.d (n + 1)) (L r (S.d (n + 1))) ∩ Set.Icc 1 ⌊x⌋₊) : ℝ) := by
      -- By `intervals_disjoint_large`, for $k \ge n+2$, $I_k \cap [1, x] = \emptyset$.
      have h_disjoint : ∀ᶠ x in atTop, ∀ n, S.d n ≤ x ∧ x < S.d (n + 1) → ∀ k ≥ n + 2, Disjoint (I (S.d k) (L r (S.d k))) (Set.Icc 1 ⌊x⌋₊) := by
        apply_rules [ intervals_disjoint_large ];
      filter_upwards [ h_disjoint ] with x hx;
      intro n hn
      have h_union : (⋃ k, I (S.d k) (L r (S.d k))) ∩ Set.Icc 1 ⌊x⌋₊ = (⋃ k ∈ Finset.range (n + 2), (I (S.d k) (L r (S.d k)))) ∩ Set.Icc 1 ⌊x⌋₊ := by
        ext; aesop;
        · by_cases h_cases : w_1 ≤ n + 1;
          · exact ⟨ w_1, Nat.lt_succ_of_le h_cases, h_2 ⟩;
          · exact False.elim <| Set.disjoint_left.mp ( hx n left right w_1 <| by linarith ) h_2 <| by aesop;
        · use w_1;
      -- By subadditivity of cardinality, we have:
      have h_subadd : Set.ncard ((⋃ k ∈ Finset.range (n + 2), (I (S.d k) (L r (S.d k)))) ∩ Set.Icc 1 ⌊x⌋₊) ≤ ∑ k ∈ Finset.range (n + 2), Set.ncard ((I (S.d k) (L r (S.d k))) ∩ Set.Icc 1 ⌊x⌋₊) := by
        induction' ( Finset.range ( n + 2 ) ) using Finset.induction <;> aesop;
        refine' le_trans _ ( add_le_add_left a_2 _ );
        convert Set.ncard_union_le _ _ using 2 ; aesop;
      -- For $k \le n$, we have $I_k \subseteq [1, x]$.
      have h_subset : ∀ k ≤ n, Set.ncard ((I (S.d k) (L r (S.d k))) ∩ Set.Icc 1 ⌊x⌋₊) = L r (S.d k) := by
        intro k hk
        have h_subset : I (S.d k) (L r (S.d k)) ⊆ Set.Icc 1 ⌊x⌋₊ := by
          intro y hy
          aesop;
          · linarith [ Set.mem_Icc.mp hy, show S.d k ≥ 1 from Nat.one_le_iff_ne_zero.mpr <| ne_of_gt <| S.d_pos k ];
          · linarith [ Set.mem_Icc.mp hy, show S.d k ≤ S.d n from monotone_nat_of_le_succ ( fun n => S.d_strict_mono.monotone n.le_succ ) hk ];
        rw [ Set.inter_eq_left.mpr h_subset ];
        unfold I; norm_num [ Set.ncard_eq_toFinset_card' ] ;
        rw [ tsub_eq_of_eq_add ] ; linarith [ Nat.sub_add_cancel ( show L r ( S.d k ) ≤ S.d k from Nat.floor_le_of_le ( by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( mod_cast Nat.one_le_iff_ne_zero.mpr <| ne_of_gt <| S.d_pos k ) <| show r ≤ 1 from hr2.le ) <| by norm_num ) ) ];
      rw [ Finset.sum_range_succ ] at h_subadd ; aesop;
      exact_mod_cast h_subadd.trans ( add_le_add_right ( Finset.sum_le_sum fun i hi => by rw [ h_subset i ( Finset.mem_range_succ_iff.mp hi ) ] ) _ )

/-
The number of elements of A in [1, x] coming from the intervals I_n is at most 2 * x^r for large x.
-/
theorem intervals_bound (h : ℕ) (r : ℝ) (C : ℝ) (S : ValidSequence h r C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) (C_pos : C > 0) :
  ∀ᶠ x in atTop, (Set.ncard ((⋃ n, I (S.d n) (L r (S.d n))) ∩ Set.Icc 1 ⌊x⌋₊) : ℝ) ≤ 2 * x^r := by
    -- Let's choose any $N$ such that for all $n \geq N$, the conditions from `sum_L_bound`, `algebraic_step`, and `card_decomposition` hold.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (∀ n ≥ N, (∑ k ∈ Finset.range (n + 1), (L r (S.d k) : ℝ)) ≤ 2 * (S.d n : ℝ)^r) ∧ (∀ n ≥ N, ∀ x, S.d n ≤ x ∧ x < S.d (n + 1) →
      (x < S.d (n + 1) - L r (S.d (n + 1)) + 1 → 2 * (S.d n : ℝ)^r ≤ 2 * x^r) ∧
      (x ≥ S.d (n + 1) - L r (S.d (n + 1)) + 1 → 2 * (S.d n : ℝ)^r + (S.d (n + 1) : ℝ)^r ≤ 2 * x^r)) ∧ (∀ᶠ x in atTop, ∀ n, S.d n ≤ x ∧ x < S.d (n + 1) →
      (Set.ncard ((⋃ k, I (S.d k) (L r (S.d k))) ∩ Set.Icc 1 ⌊x⌋₊) : ℝ) ≤ (∑ k ∈ Finset.range (n + 1), (L r (S.d k) : ℝ)) + (Set.ncard (I (S.d (n + 1)) (L r (S.d (n + 1))) ∩ Set.Icc 1 ⌊x⌋₊) : ℝ)) := by
        obtain ⟨ N₁, hN₁ ⟩ := Filter.eventually_atTop.mp ( sum_L_bound h r C S h_ge_3 hr1 hr2 C_pos );
        obtain ⟨ N₂, hN₂ ⟩ := Filter.eventually_atTop.mp ( algebraic_step h r C S h_ge_3 hr1 hr2 ) ; obtain ⟨ N₃, hN₃ ⟩ := Filter.eventually_atTop.mp ( card_decomposition h r C S h_ge_3 hr1 hr2 ) ; use Max.max N₁ ( Max.max N₂ N₃ ) ; aesop;
    rcases Filter.eventually_atTop.mp hN.2.2 with ⟨ M, hM ⟩ ; refine' Filter.eventually_atTop.mpr ⟨ M + S.d N + 1, fun x hx => _ ⟩ ; specialize hM ( ⌊x⌋₊ ) ( Nat.le_floor <| by linarith ) ; aesop;
    -- Let's choose any $n$ such that $S.d n \leq \lfloor x \rfloor < S.d (n + 1)$.
    obtain ⟨n, hn⟩ : ∃ n, S.d n ≤ ⌊x⌋₊ ∧ ⌊x⌋₊ < S.d (n + 1) ∧ N ≤ n := by
      -- Since $S.d$ is strictly increasing and unbounded, there exists some $n$ such that $S.d n \leq \lfloor x \rfloor < S.d (n + 1)$.
      obtain ⟨n, hn⟩ : ∃ n, S.d n ≤ ⌊x⌋₊ ∧ ⌊x⌋₊ < S.d (n + 1) := by
        have h_unbounded : ∀ M : ℕ, ∃ n, S.d n > M := by
          exact fun M => ⟨ _, S.d_strict_mono.id_le _ ⟩;
        contrapose! h_unbounded;
        exact ⟨ ⌊x⌋₊, fun n => Nat.recOn n ( by linarith [ show S.d 0 ≤ ⌊x⌋₊ from Nat.le_floor <| by linarith [ show ( S.d 0 : ℝ ) ≤ x from by linarith [ show ( S.d 0 : ℝ ) ≤ M + S.d N + 1 by norm_cast; linarith [ S.d_pos N, S.d_strict_mono.monotone <| show 0 ≤ N from Nat.zero_le _ ] ] ] ] ) h_unbounded ⟩;
      refine' ⟨ n, hn.1, hn.2, _ ⟩ ; contrapose! hx ; aesop;
      exact lt_of_not_ge fun h => right.not_le <| Nat.le_floor <| by linarith [ show ( S.d N : ℝ ) ≥ S.d ( n + 1 ) from mod_cast S.d_strict_mono.monotone <| by linarith ] ;
    -- By combining the results from `hM`, `left`, and `left_1`, we can conclude the proof.
    have h_final : (Set.ncard ((⋃ k, I (S.d k) (L r (S.d k))) ∩ Set.Icc 1 ⌊x⌋₊) : ℝ) ≤ 2 * (S.d n : ℝ)^r + (if ⌊x⌋₊ < S.d (n + 1) - L r (S.d (n + 1)) + 1 then 0 else (S.d (n + 1) : ℝ)^r) := by
      bound;
      · refine le_trans ( hM n left_2 left_3 ) ?_;
        refine' add_le_add ( left n right ) _;
        rw [ Set.ncard_def ] ; aesop;
        exact Or.inl <| Set.eq_empty_of_forall_not_mem fun y hy => by linarith [ hy.1.1, hy.1.2, hy.2.1, hy.2.2, Nat.sub_add_cancel <| show L r ( S.d ( n + 1 ) ) ≤ S.d ( n + 1 ) from Nat.floor_le_of_le <| by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( mod_cast Nat.one_le_iff_ne_zero.mpr <| ne_of_gt <| S.d_pos _ ) hr2.le ) <| by norm_num ] ;
      · refine le_trans ( hM n left_2 left_3 ) ?_;
        refine' add_le_add ( left n right ) _;
        refine' le_trans ( Nat.cast_le.mpr <| Set.ncard_le_ncard <| show I ( S.d ( n + 1 ) ) ( L r ( S.d ( n + 1 ) ) ) ∩ Set.Icc 1 ⌊x⌋₊ ⊆ Set.Icc ( S.d ( n + 1 ) - L r ( S.d ( n + 1 ) ) + 1 ) ( S.d ( n + 1 ) ) from fun y hy => by aesop ) _ ; norm_num [ Set.ncard_eq_toFinset_card' ];
        rw [ Nat.cast_sub ] <;> norm_num;
        · rw [ show ( L r ( S.d ( n + 1 ) ) : ℝ ) = ⌊ ( S.d ( n + 1 ) : ℝ ) ^ r⌋₊ by rfl ] ; linarith [ Nat.floor_le ( Real.rpow_nonneg ( Nat.cast_nonneg ( S.d ( n + 1 ) ) ) r ), Nat.lt_floor_add_one ( ( S.d ( n + 1 ) : ℝ ) ^ r ) ] ;
        · exact Nat.floor_le_of_le ( by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( mod_cast Nat.one_le_iff_ne_zero.mpr <| ne_of_gt <| S.d_pos _ ) hr2.le ) <| by norm_num );
    split_ifs at h_final <;> aesop;
    · refine le_trans h_final ?_;
      gcongr;
      · exact le_trans ( sub_nonneg.2 <| inv_le_one_of_one_le₀ <| by norm_cast; linarith ) hr1.le;
      · exact le_trans ( Nat.cast_le.mpr left_2 ) ( Nat.floor_le ( by linarith ) );
    · specialize left_1 n right ⌊x⌋₊ left_2 left_3 ; aesop;
      refine le_trans h_final <| le_trans left_1 ?_;
      gcongr;
      · exact le_trans ( sub_nonneg.2 <| inv_le_one_of_one_le₀ <| by norm_cast; linarith ) hr1.le;
      · exact Nat.floor_le ( by linarith )

/-
For large n, if d_n <= x < d_{n+1}, then the number of elements of A in [1, x] coming from intervals is at most 2 * x^r.
-/
theorem intervals_bound_aux (h : ℕ) (r : ℝ) (C : ℝ) (S : ValidSequence h r C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) (C_pos : C > 0) :
  ∀ᶠ n in atTop, ∀ x, S.d n ≤ x ∧ x < S.d (n + 1) →
    (Set.ncard ((⋃ k, I (S.d k) (L r (S.d k))) ∩ Set.Icc 1 ⌊x⌋₊) : ℝ) ≤ 2 * x^r := by
      aesop;
      -- Apply the lemma `intervals_bound` to obtain the required bound.
      have := @intervals_bound;
      norm_num at *;
      obtain ⟨ a, ha ⟩ := this h r C S h_ge_3 hr1 hr2 C_pos;
      use ⌈a⌉₊ + 1;
      intro b hb x hx₁ hx₂; specialize ha x ( Nat.le_of_ceil_le ( by linarith [ show x ≥ b by linarith [ show S.d b ≥ b from Nat.recOn b ( by linarith [ S.d_one_gt_one ] ) fun n ihn => by linarith [ S.d_strict_mono n.lt_succ_self ] ] ] ) ) ; aesop;

/-
The number of elements of A in [1, x] coming from the intervals I_n is at most 2 * x^r for large x.
-/
theorem intervals_bound_final (h : ℕ) (r : ℝ) (C : ℝ) (S : ValidSequence h r C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) (C_pos : C > 0) :
  ∀ᶠ x in atTop, (Set.ncard ((⋃ n, I (S.d n) (L r (S.d n))) ∩ Set.Icc 1 ⌊x⌋₊) : ℝ) ≤ 2 * x^r := by
    exact?

/-
For sufficiently large x, A(x) <= C * x^(1/h) + 2 * x^r.
-/
theorem A_upper_bound (h : ℕ) (r : ℝ) (TB : ThinBasis h) (S : ValidSequence h r TB.C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) :
  ∀ᶠ x in atTop, (count_in_range (constructed_A TB.B S.d r) x : ℝ) ≤ TB.C * x^(1 / (h : ℝ)) + 2 * x^r := by
    -- By `TB.thin_condition`, $B(x) \le C x^{1/h}$.
    have h_B_bound : ∀ᶠ x in atTop, (Set.ncard (TB.B ∩ Set.Icc 1 ⌊x⌋₊) : ℝ) ≤ TB.C * x^(1 / h : ℝ) := by
      exact Filter.eventually_atTop.mpr ⟨ 1, fun x hx => by simpa using TB.thin_condition x hx ⟩;
    have h_union_bound : ∀ x : ℝ, x ≥ 1 → (Set.ncard ((TB.B ∪ (⋃ n, I (S.d n) (L r (S.d n)))) ∩ Set.Icc 1 ⌊x⌋₊) : ℝ) ≤ (Set.ncard (TB.B ∩ Set.Icc 1 ⌊x⌋₊) : ℝ) + (Set.ncard ((⋃ n, I (S.d n) (L r (S.d n))) ∩ Set.Icc 1 ⌊x⌋₊) : ℝ) := by
      intro x hx;
      norm_cast;
      convert Set.ncard_union_le _ _ using 2 ; aesop;
    filter_upwards [ h_B_bound, Filter.eventually_ge_atTop 1, intervals_bound_final h r TB.C S h_ge_3 hr1 hr2 ( TB.C_pos ) ] with x hx₁ hx₂ hx₃ using le_trans ( h_union_bound x hx₂ ) ( add_le_add hx₁ hx₃ )

/-
For large n, A(d_n) >= 1/2 * d_n^r.
-/
theorem A_dn_lower_bound (h : ℕ) (r : ℝ) (TB : ThinBasis h) (S : ValidSequence h r TB.C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) :
  ∀ᶠ n in atTop, (count_in_range (constructed_A TB.B S.d r) (S.d n) : ℝ) ≥ (1/2) * (S.d n : ℝ)^r := by
    -- Since $I_n$ is contained within $[1, S.d n]$ and $I_n$ has length $L_r(S.d n)$, we have $|A(d_n)| \geq L_r(S.d n)$.
    have h_interval : ∀ n, (count_in_range (constructed_A TB.B S.d r) (S.d n) : ℝ) ≥ (L r (S.d n) : ℝ) := by
      intro n
      have h_interval : (Set.ncard ((I (S.d n) (L r (S.d n))) ∩ Set.Icc 1 (S.d n))) = (L r (S.d n)) := by
        unfold I L; aesop;
        rw [ show ( Set.Icc ( S.d n - ⌊ ( S.d n : ℝ ) ^ r⌋₊ + 1 ) ( S.d n ) ∩ Set.Icc 1 ( S.d n ) ) = Set.Icc ( S.d n - ⌊ ( S.d n : ℝ ) ^ r⌋₊ + 1 ) ( S.d n ) from ?_ ];
        · norm_num [ Set.ncard_eq_toFinset_card' ];
          rw [ tsub_eq_of_eq_add ];
          linarith [ Nat.sub_add_cancel ( show ⌊ ( S.d n : ℝ ) ^ r⌋₊ ≤ S.d n from Nat.floor_le_of_le ( by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( mod_cast Nat.one_le_iff_ne_zero.mpr <| ne_of_gt <| S.d_pos n ) hr2.le ) <| by norm_num ) ) ];
        · grind;
      refine' mod_cast h_interval ▸ _;
      fapply Set.ncard_le_ncard;
      · intro x hx; unfold constructed_A; aesop;
      · exact Set.finite_iff_bddAbove.mpr ⟨ ⌊ ( S.d n : ℝ ) ⌋₊, fun x hx => hx.2.2 ⟩;
    -- Since $S.d n$ grows large, we have $(S.d n : ℝ) ^ r \geq 2$.
    have h_large : ∀ᶠ n in Filter.atTop, (S.d n : ℝ) ^ r ≥ 2 := by
      have h_large : Filter.Tendsto (fun n => (S.d n : ℝ) ^ r) Filter.atTop Filter.atTop := by
        exact tendsto_rpow_atTop ( by linarith [ show ( 0 : ℝ ) < r by exact lt_of_le_of_lt ( sub_nonneg.mpr <| div_le_self zero_le_one <| mod_cast by linarith ) hr1 ] ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop.comp <| S.d_strict_mono.tendsto_atTop;
      exact h_large.eventually_ge_atTop 2;
    filter_upwards [ h_large ] with n hn using le_trans ( by linarith [ show ( L r ( S.d n ) : ℝ ) ≥ ( S.d n : ℝ ) ^ r - 1 by exact le_trans ( by norm_num ) ( Nat.sub_one_lt_floor _ |> le_of_lt ) ] ) ( h_interval n )

/-
For n >= 1, the sum of d_k^r for k <= n is at most 1/4 * d_n^(1/h) + d_n^r.
-/
theorem sum_bound_at_n (h : ℕ) (r : ℝ) (C : ℝ) (S : ValidSequence h r C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) :
  ∀ n ≥ 1, (∑ k ∈ Finset.range (n + 1), (S.d k : ℝ)^r) ≤ (1/4) * (S.d n : ℝ)^(1 / (h : ℝ)) + (S.d n : ℝ)^r := by
    intro n hn; rw [ Finset.sum_range_succ ] ; linarith [ S.cond_sum n hn ] ;

/-
For large n, (C + 1/4) * d_n^(1/h) <= d_n^r.
-/
theorem asymptotic_inequality (h : ℕ) (r : ℝ) (TB : ThinBasis h) (S : ValidSequence h r TB.C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) :
  ∀ᶠ n in atTop, (TB.C + 1/4) * (S.d n : ℝ)^(1 / (h : ℝ)) ≤ (S.d n : ℝ)^r := by
    -- We can divide both sides by $d_n^{1/h}$ to get $(C + 1/4) \leq d_n^{r - 1/h}$.
    suffices h_divided : ∀ᶠ n in atTop, (TB.C + 1 / 4 : ℝ) ≤ (S.d n : ℝ) ^ (r - 1 / h : ℝ) by
      filter_upwards [ h_divided, Filter.eventually_gt_atTop 0 ] with n hn hn' ; rw [ Real.rpow_sub ( Nat.cast_pos.mpr <| S.d_pos n ) ] at * ; aesop;
      rwa [ le_div_iff₀ ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( S.d_pos n ) ) _ ) ] at hn;
    have h_exp_growth : Filter.Tendsto (fun n => (S.d n : ℝ) ^ (r - 1 / h : ℝ)) Filter.atTop Filter.atTop := by
      exact tendsto_rpow_atTop ( by nlinarith [ show ( h : ℝ ) ≥ 3 by norm_cast, one_div_mul_cancel ( by positivity : ( h : ℝ ) ≠ 0 ) ] ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop.comp <| S.d_strict_mono.tendsto_atTop;
    exact h_exp_growth.eventually_ge_atTop _

/-
For large n, the intersection of the union of intervals with [1, d_n] is contained in the union of the first n+1 intervals.
-/
theorem intervals_subset_dn (h : ℕ) (r : ℝ) (C : ℝ) (S : ValidSequence h r C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) :
  ∀ᶠ n in atTop, (⋃ k, I (S.d k) (L r (S.d k))) ∩ Set.Icc 1 (S.d n) ⊆ ⋃ k ∈ Finset.range (n + 1), I (S.d k) (L r (S.d k)) := by
    -- For large $n$, if $k > n$, then $I_k$ starts after $d_n$, so $I_k \cap [1, d_n] = \emptyset$.
    have h_I_k_empty : ∀ᶠ n in atTop, ∀ k > n, Disjoint (I (S.d k) (L r (S.d k))) (Set.Icc 1 (S.d n)) := by
      -- If $k > n$, then $k \ge n+1$. By `d_super_growth`, $d_{n+1} > 2 d_n$. Also $d_k \ge d_{n+1}$.
      have h_dk_gt_2dn : ∀ᶠ n in atTop, ∀ k > n, 2 * S.d n < S.d k := by
        have := d_super_growth h r C S h_ge_3 hr1 hr2;
        aesop;
        use w;
        intro b hb k hk; induction hk <;> aesop;
        linarith [ h_1 m ( by linarith ) ];
      have h_I_k_empty : ∀ᶠ n in atTop, ∀ k > n, S.d k - L r (S.d k) + 1 > S.d n := by
        filter_upwards [ h_dk_gt_2dn, Filter.eventually_gt_atTop 0 ] with n hn hn' k hk;
        have := S.cond_half k;
        exact Nat.lt_succ_of_le ( Nat.le_sub_of_add_le <| by rw [ ← @Nat.cast_le ℝ ] ; push_cast ; linarith [ show ( S.d k : ℝ ) ≥ 2 * S.d n + 1 by exact_mod_cast hn k hk, show ( L r ( S.d k ) : ℝ ) ≤ ( S.d k : ℝ ) ^ r by exact_mod_cast Nat.floor_le <| by positivity ] );
      filter_upwards [ h_I_k_empty ] with n hn k hk using Set.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Set.mem_Icc.mp hx₂, Set.mem_Icc.mp hx₁, hn k hk ] ;
    filter_upwards [ h_I_k_empty ] with n hn x hx ; aesop;
    exact ⟨ w_1, Nat.lt_succ_of_le ( le_of_not_gt fun h => Set.disjoint_left.mp ( hn _ h ) h_2 ⟨ left, right ⟩ ), h_2 ⟩

/-
For large n, A(d_n) <= (C + 1/4) * d_n^(1/h) + d_n^r.
-/
theorem A_dn_intermediate_bound (h : ℕ) (r : ℝ) (TB : ThinBasis h) (S : ValidSequence h r TB.C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) :
  ∀ᶠ n in atTop, (count_in_range (constructed_A TB.B S.d r) (S.d n) : ℝ) ≤ (TB.C + 1/4) * (S.d n : ℝ)^(1 / (h : ℝ)) + (S.d n : ℝ)^r := by
    -- Apply the bounds to get the desired inequality.
    have h_aux : ∀ᶠ n in atTop, (Set.ncard ((⋃ k, I (S.d k) (L r (S.d k))) ∩ Set.Icc 1 (S.d n)) : ℝ) ≤ ∑ k ∈ Finset.range (n + 1), (L r (S.d k) : ℝ) ∧ (∑ k ∈ Finset.range (n + 1), (S.d k : ℝ)^r) ≤ (1/4) * (S.d n : ℝ)^(1 / (h : ℝ)) + (S.d n : ℝ)^r := by
      have h_aux : ∀ᶠ n in atTop, (Set.ncard ((⋃ k, I (S.d k) (L r (S.d k))) ∩ Set.Icc 1 (S.d n)) : ℝ) ≤ ∑ k ∈ Finset.range (n + 1), (L r (S.d k) : ℝ) := by
        have h_aux : ∀ᶠ n in atTop, (⋃ k, I (S.d k) (L r (S.d k))) ∩ Set.Icc 1 (S.d n) ⊆ ⋃ k ∈ Finset.range (n + 1), I (S.d k) (L r (S.d k)) := by
          bound;
          exact?;
        filter_upwards [ h_aux ] with n hn;
        have h_aux : (Set.ncard ((⋃ k, I (S.d k) (L r (S.d k))) ∩ Set.Icc 1 (S.d n)) : ℝ) ≤ ∑ k ∈ Finset.range (n + 1), (Set.ncard (I (S.d k) (L r (S.d k))) : ℝ) := by
          have h_aux : (Set.ncard ((⋃ k, I (S.d k) (L r (S.d k))) ∩ Set.Icc 1 (S.d n)) : ℝ) ≤ (Set.ncard (⋃ k ∈ Finset.range (n + 1), I (S.d k) (L r (S.d k))) : ℝ) := by
            gcongr;
            exact Set.Finite.biUnion ( Finset.finite_toSet _ ) fun _ _ => Set.finite_Icc _ _;
          refine le_trans h_aux ?_;
          induction' ( Finset.range ( n + 1 ) ) using Finset.induction <;> aesop;
          exact le_trans ( mod_cast Set.ncard_union_le _ _ ) ( add_le_add_left a_2 _ );
        refine le_trans h_aux ?_;
        gcongr ; aesop;
        unfold I; norm_num [ Set.ncard_eq_toFinset_card' ] ;
        omega;
      filter_upwards [ h_aux, Filter.eventually_ge_atTop 1 ] with n hn hn' using ⟨ hn, sum_bound_at_n h r TB.C S h_ge_3 hr1 hr2 n hn' ⟩;
    -- By definition of $count_in_range$, we know that
    have h_count : ∀ᶠ n in atTop, (count_in_range (constructed_A TB.B S.d r) (S.d n) : ℝ) ≤ (count_in_range TB.B (S.d n) : ℝ) + (Set.ncard ((⋃ k, I (S.d k) (L r (S.d k))) ∩ Set.Icc 1 (S.d n)) : ℝ) := by
      refine Filter.Eventually.of_forall fun n => ?_ ; norm_cast ; aesop;
      unfold count_in_range constructed_A; aesop;
      convert Set.ncard_union_le _ _ using 2 ; aesop;
    -- By definition of $count_in_range$, we know that $count_in_range TB.B (S.d n) \leq TB.C * (S.d n : ℝ)^(1 / (h : ℝ))$.
    have h_count_TB : ∀ᶠ n in atTop, (count_in_range TB.B (S.d n) : ℝ) ≤ TB.C * (S.d n : ℝ)^(1 / (h : ℝ)) := by
      exact Filter.eventually_atTop.mpr ⟨ 1, fun n hn => TB.thin_condition _ <| mod_cast Nat.one_le_iff_ne_zero.mpr <| Nat.ne_of_gt <| S.d_pos n ⟩;
    filter_upwards [ h_aux, h_count, h_count_TB ] with n hn hn' hn'';
    linarith [ show ( ∑ k ∈ Finset.range ( n + 1 ), ( L r ( S.d k ) : ℝ ) ) ≤ ∑ k ∈ Finset.range ( n + 1 ), ( S.d k : ℝ ) ^ r by exact Finset.sum_le_sum fun i hi => by exact_mod_cast Nat.floor_le ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ]

/-
For large n, A(d_n) <= 2 * d_n^r.
-/
theorem A_dn_upper_bound (h : ℕ) (r : ℝ) (TB : ThinBasis h) (S : ValidSequence h r TB.C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) :
  ∀ᶠ n in atTop, (count_in_range (constructed_A TB.B S.d r) (S.d n) : ℝ) ≤ 2 * (S.d n : ℝ)^r := by
    have := A_dn_intermediate_bound h r TB S h_ge_3 hr1 hr2;
    filter_upwards [ this, asymptotic_inequality h r TB S h_ge_3 hr1 hr2 ] with n hn hn' using le_trans hn <| by linarith;

/-
The number of integers s in [1, d_n] such that there exists a in I_n with a <= s is at most L_n.
-/
theorem S1_card_bound (h : ℕ) (r : ℝ) (C : ℝ) (S : ValidSequence h r C)
  (n : ℕ) :
  Set.ncard {s ∈ Set.Icc 1 (S.d n) | ∃ a ∈ I (S.d n) (L r (S.d n)), a ≤ s} ≤ L r (S.d n) := by
    -- Let $m = \min I_n = d_n - L_n + 1$.
    set m := S.d n - L r (S.d n) + 1 with hm;
    -- Thus $K \subseteq [m, d_n]$.
    have h_subset : {s | s ∈ Set.Icc 1 (S.d n) ∧ ∃ a ∈ I (S.d n) (L r (S.d n)), a ≤ s} ⊆ Set.Icc m (S.d n) := by
      exact fun x hx => ⟨ by obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ := hx.2; linarith, by obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ := hx.2; linarith [ hx.1.2 ] ⟩;
    refine' le_trans ( Set.ncard_le_ncard h_subset ) _;
    norm_num [ Set.ncard_eq_toFinset_card' ];
    omega

/-
For large n, A(d_n - L_n) <= (C + 1/4) * d_n^(1/h).
-/
theorem A_dn_minus_Ln_bound (h : ℕ) (r : ℝ) (TB : ThinBasis h) (S : ValidSequence h r TB.C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) :
  ∀ᶠ n in atTop, (count_in_range (constructed_A TB.B S.d r) ((S.d n) - L r (S.d n)) : ℝ) ≤ (TB.C + 1/4) * (S.d n : ℝ)^(1 / (h : ℝ)) := by
    -- By Lemma `intervals_subset_dn`, for large $n$, the intersection of the union of intervals with $[1, d_n - L_n]$ is contained in the union of the first $n-1$ intervals.
    have intervals_subset_dn_minus_L : ∀ᶠ n in atTop, (⋃ k, I (S.d k) (L r (S.d k))) ∩ Set.Icc 1 (Nat.floor ((S.d n : ℝ) - (L r (S.d n) : ℝ))) ⊆ ⋃ k ∈ Finset.range n, I (S.d k) (L r (S.d k)) := by
      have := intervals_subset_dn h r TB.C S h_ge_3 hr1 hr2;
      norm_num +zetaDelta at *;
      obtain ⟨ a, ha ⟩ := this; use a + 1; intros b hb; specialize ha b ( by linarith ) ; simp_all +decide [ Set.subset_def ] ;
      intro x y hx hy hxy; specialize ha x y hx hy ( le_trans hxy ( Nat.sub_le _ _ ) ) ; aesop;
      cases lt_or_eq_of_le ( Nat.le_of_lt_succ left ) <;> aesop;
      exact ⟨ y, lt_of_le_of_lt ( show y ≤ a by exact le_of_not_lt fun h => by have := S.d_strict_mono h; linarith [ hx.1, hx.2, right.1, right.2, Nat.sub_add_cancel ( show L r ( S.d w ) ≤ S.d w from Nat.floor_le_of_le <| by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( mod_cast Nat.one_le_iff_ne_zero.mpr <| ne_of_gt <| S.d_pos _ ) hr2.le ) <| by norm_num ) ] ) hb, hx ⟩;
    have big_step : ∀ᶠ n in atTop, (count_in_range (constructed_A TB.B S.d r) ((S.d n : ℝ) - (L r (S.d n) : ℝ))) ≤ TB.C * ((S.d n : ℝ) - (L r (S.d n) : ℝ))^(1 / h : ℝ) + (∑ k ∈ Finset.range n, (L r (S.d k) : ℝ)) := by
      -- By definition of $count_in_range$, we know that
      have h_count_def : ∀ᶠ n in atTop, (count_in_range (constructed_A TB.B S.d r) ((S.d n : ℝ) - (L r (S.d n) : ℝ))) ≤ (count_in_range TB.B ((S.d n : ℝ) - (L r (S.d n) : ℝ))) + (Set.ncard ((⋃ k, I (S.d k) (L r (S.d k))) ∩ Set.Icc 1 (Nat.floor ((S.d n : ℝ) - (L r (S.d n) : ℝ))))) := by
        refine Filter.Eventually.of_forall fun n => ?_;
        unfold count_in_range constructed_A;
        convert Set.ncard_union_le _ _ using 2 ; ext ; aesop;
      have h_count_bound : ∀ᶠ n in atTop, (count_in_range TB.B ((S.d n : ℝ) - (L r (S.d n) : ℝ))) ≤ TB.C * ((S.d n : ℝ) - (L r (S.d n) : ℝ))^(1 / h : ℝ) := by
        refine' Filter.eventually_atTop.mpr ⟨ 1, fun n hn => _ ⟩ ; aesop;
        convert TB.thin_condition _ _ using 1;
        · norm_num;
        · have := S.cond_half n; aesop;
          rw [ show L r ( S.d n ) = ⌊ ( S.d n : ℝ ) ^ r⌋₊ by rfl ];
          linarith [ show ( S.d n : ℝ ) ≥ 2 by exact_mod_cast Nat.succ_le_of_lt ( lt_of_le_of_lt ( Nat.succ_le_of_lt ( show 0 < S.d 0 from S.d_pos 0 ) ) ( S.d_strict_mono hn ) ), Nat.floor_le ( Real.rpow_nonneg ( Nat.cast_nonneg ( S.d n ) ) r ) ];
      have h_intervals_bound : ∀ᶠ n in atTop, (Set.ncard ((⋃ k, I (S.d k) (L r (S.d k))) ∩ Set.Icc 1 (Nat.floor ((S.d n : ℝ) - (L r (S.d n) : ℝ))))) ≤ (∑ k ∈ Finset.range n, (L r (S.d k) : ℝ)) := by
        filter_upwards [ intervals_subset_dn_minus_L ] with n hn;
        have h_intervals_bound : (Set.ncard ((⋃ k, I (S.d k) (L r (S.d k))) ∩ Set.Icc 1 (Nat.floor ((S.d n : ℝ) - (L r (S.d n) : ℝ))))) ≤ (∑ k ∈ Finset.range n, (Set.ncard (I (S.d k) (L r (S.d k))))) := by
          have h_intervals_bound : (Set.ncard ((⋃ k, I (S.d k) (L r (S.d k))) ∩ Set.Icc 1 (Nat.floor ((S.d n : ℝ) - (L r (S.d n) : ℝ))))) ≤ (Set.ncard (⋃ k ∈ Finset.range n, I (S.d k) (L r (S.d k)))) := by
            apply_rules [ Set.ncard_le_ncard ];
            exact Set.Finite.biUnion ( Finset.finite_toSet _ ) fun k hk => Set.finite_Icc _ _;
          refine le_trans h_intervals_bound ?_;
          induction' ( Finset.range n : Finset ℕ ) using Finset.induction <;> aesop;
          exact le_trans ( Set.ncard_union_le _ _ ) ( add_le_add_left a_2 _ );
        refine' le_trans ( Nat.cast_le.mpr h_intervals_bound ) _;
        norm_num [ Set.ncard_eq_toFinset_card' ];
        gcongr ; aesop;
        unfold I; norm_num [ Set.ncard_eq_toFinset_card' ] ;
        omega;
      filter_upwards [ h_count_def, h_count_bound, h_intervals_bound ] with n hn hn' hn'' using le_trans ( mod_cast hn ) ( add_le_add hn' hn'' );
    -- By Lemma `sum_bound_at_n`, we know that $\sum_{k < n} L_k \le \frac14 d_n^{1/h}$.
    have sum_bound_at_n' : ∀ n ≥ 1, (∑ k ∈ Finset.range n, (L r (S.d k) : ℝ)) ≤ (1 / 4) * (S.d n : ℝ)^(1 / h : ℝ) := by
      intros n hn
      have sum_bound_at_n' : (∑ k ∈ Finset.range n, (L r (S.d k) : ℝ)) ≤ (∑ k ∈ Finset.range n, (S.d k : ℝ)^r) := by
        exact Finset.sum_le_sum fun i hi => Nat.floor_le ( by exact Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ );
      have := S.cond_sum n hn; norm_num at * ; linarith;
    -- Since $d_n - L_n < d_n$, we have $(d_n - L_n)^{1/h} \le d_n^{1/h}$.
    have h_ineq : ∀ᶠ n in atTop, ((S.d n : ℝ) - (L r (S.d n) : ℝ))^(1 / h : ℝ) ≤ (S.d n : ℝ)^(1 / h : ℝ) := by
      filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using Real.rpow_le_rpow ( sub_nonneg.mpr <| Nat.cast_le.mpr <| Nat.floor_le_of_le <| by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( mod_cast Nat.one_le_iff_ne_zero.mpr <| ne_of_gt <| S.d_pos n ) hr2.le ) <| by norm_num ) ( sub_le_self _ <| Nat.cast_nonneg _ ) <| by positivity;
    filter_upwards [ big_step, h_ineq, Filter.eventually_ge_atTop 1 ] with n hn hn' hn'' using le_trans hn ( by nlinarith [ sum_bound_at_n' n hn'', show ( 0 :ℝ ) ≤ TB.C by exact le_of_lt TB.C_pos ] )

/-
For large n, A(d_n) <= 2 * d_n^r.
-/
theorem A_dn_upper_bound_final (h : ℕ) (r : ℝ) (TB : ThinBasis h) (S : ValidSequence h r TB.C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) :
  ∀ᶠ n in atTop, (count_in_range (constructed_A TB.B S.d r) (S.d n) : ℝ) ≤ 2 * (S.d n : ℝ)^r := by
    exact A_dn_upper_bound h r TB S h_ge_3 hr1 hr2

/-
If s is a sum of k elements from S and s <= M, then s is a sum of k elements from S intersected with [1, M].
-/
theorem iterated_sumset_subset_lemma (S : Set ℕ) (k M : ℕ) (hS : ∀ x ∈ S, 1 ≤ x) :
  iterated_sumset S k ∩ Set.Icc 1 M ⊆ iterated_sumset (S ∩ Set.Icc 1 M) k := by
    induction' k with k ih <;> simp_all ( config := { decide := Bool.true } ) [ Set.subset_def, Finset.card_univ ];
    · bound;
    · intros x hx hx₁ hx₂;
      -- Since $s \in kS$ and $s \leq M$, by the induction hypothesis, $s \in k(S \cap [1, M])$.
      obtain ⟨a, haS, s, hs⟩ : ∃ a ∈ S, ∃ s ∈ iterated_sumset S k, x = a + s := by
        cases hx ; aesop;
      by_cases hs_pos : 1 ≤ s <;> aesop;
      · exact Set.add_mem_add ( Set.mem_inter haS ⟨ hS a haS, by linarith ⟩ ) ( ih s left hs_pos ( by linarith ) );
      · induction' k with k ih <;> simp_all ( config := { decide := Bool.true } ) [ iterated_sumset ];
        cases left ; aesop;
        linarith [ hS 0 left ]

/-
Set inclusion helper lemma for S2 bound.
-/
theorem S2_set_inclusion (A : Set ℕ) (M L : ℕ) (I : Set ℕ) (hI : I = Set.Icc (M - L + 1) M) :
  (A \ I) ∩ Set.Icc 1 M ⊆ A ∩ Set.Icc 1 (M - L) := by
    grind +ring

/-
Monotonicity of iterated sumset.
-/
theorem iterated_sumset_mono (S T : Set ℕ) (k : ℕ) (h : S ⊆ T) :
  iterated_sumset S k ⊆ iterated_sumset T k := by
    -- We proceed by induction on $k$.
    induction' k with k ih;
    · exact?;
    · exact Set.add_subset_add h ih

/-
If s is a sum of k elements from A \ I and s <= M, then s is a sum of k elements from A intersected with [1, M-L].
-/
theorem S2_subset_lemma (A : Set ℕ) (M L k : ℕ) (I : Set ℕ) (hI : I = Set.Icc (M - L + 1) M) (hA : ∀ x ∈ A, 1 ≤ x) :
  iterated_sumset (A \ I) k ∩ Set.Icc 1 M ⊆ iterated_sumset (A ∩ Set.Icc 1 (M - L)) k := by
    intro x hx;
    have h_subset : x ∈ iterated_sumset ((A \ I) ∩ Set.Icc 1 M) k := by
      apply_rules [ iterated_sumset_subset_lemma ];
      grind;
    have h_subset : (A \ I) ∩ Set.Icc 1 M ⊆ A ∩ Set.Icc 1 (M - L) := by
      intro x hx; aesop ; omega;
    exact iterated_sumset_mono _ _ _ h_subset ‹_›

/-
The cardinality of the k-fold sumset of A is at most |A|^k.
-/
theorem card_iterated_sumset_le (A : Set ℕ) (k : ℕ) :
  (iterated_sumset A k).ncard ≤ (A.ncard) ^ k := by
    induction' k with k ih generalizing A <;> simp_all +decide [ pow_succ, iterated_sumset ];
    by_cases hA : A.Finite <;> by_cases hB : iterated_sumset A k |> Set.Finite <;> simp_all +decide [ Set.ncard_def ];
    · rw [ mul_comm ];
      have h_card_sumset : ∀ (A B : Set ℕ), Set.Finite A → Set.Finite B → (A + B).encard.toNat ≤ A.encard.toNat * B.encard.toNat := by
        intros A B hA hB; have := hA.exists_finset_coe; have := hB.exists_finset_coe; aesop;
        rw [ Set.encard_eq_coe_toFinset_card ] ; aesop;
        exact Finset.card_add_le;
      exact le_trans ( h_card_sumset _ _ hA hB ) ( Nat.mul_le_mul_left _ ( ih _ ) );
    · contrapose! hB;
      refine' Nat.recOn k _ _ <;> aesop;
      · exact Set.finite_singleton 0;
      · exact Set.Finite.add hA n_ih;
    · norm_num [ Set.encard_eq_top_iff.mpr hA ];
      contrapose! hA;
      aesop;
      exact Set.Finite.subset ( right.preimage fun x => by aesop ) fun x hx => Set.add_mem_add hx right_1.choose_spec;
    · rw [ Set.encard_eq_top_iff.mpr ];
      · norm_num;
      · refine Set.infinite_of_forall_exists_gt ?_;
        exact fun n => by rcases Set.Infinite.exists_gt hA n with ⟨ m, hm₁, hm₂ ⟩ ; rcases Set.Infinite.exists_gt hB m with ⟨ n, hn₁, hn₂ ⟩ ; exact ⟨ m + n, Set.add_mem_add hm₁ hn₁, by linarith ⟩ ;

/-
Decomposition of sumset based on whether elements are in I or not.
-/
theorem sumset_decomposition (A : Set ℕ) (I : Set ℕ) (k : ℕ) :
  iterated_sumset A k ⊆ iterated_sumset (A \ I) k ∪ {s | ∃ a ∈ A ∩ I, a ≤ s} := by
    intro s;
    induction' k with k ih generalizing s <;> simp_all +decide [ iterated_sumset ];
    simp_all +decide [ Set.mem_add ];
    grind

/-
Bound for A_{h-1}(d_n) in terms of L_n and A(d_n - L_n).
-/
theorem Ah_minus_1_bound (h : ℕ) (r : ℝ) (TB : ThinBasis h) (S : ValidSequence h r TB.C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) (hB_pos : ∀ x ∈ TB.B, 1 ≤ x) :
  ∀ᶠ n in atTop, (count_in_range (iterated_sumset (constructed_A TB.B S.d r) (h - 1)) (S.d n) : ℝ) ≤
    (L r (S.d n) : ℝ) + (count_in_range (constructed_A TB.B S.d r) ((S.d n) - L r (S.d n)) : ℝ)^(h - 1) := by
      -- Apply the decomposition lemma to the set $A$ and the interval $I_n$.
      have h_decomp : ∀ᶠ n in Filter.atTop, (Set.ncard ((iterated_sumset (constructed_A TB.B S.d r) (h - 1)) ∩ Set.Icc 1 (S.d n))) ≤ (Set.ncard ({s ∈ Set.Icc 1 (S.d n) | ∃ a ∈ I (S.d n) (L r (S.d n)), a ≤ s})) + (Set.ncard (iterated_sumset ((constructed_A TB.B S.d r) ∩ Set.Icc 1 ((S.d n) - L r (S.d n))) (h - 1))) := by
        have h_decomp : ∀ᶠ n in Filter.atTop, (Set.ncard ((iterated_sumset (constructed_A TB.B S.d r) (h - 1)) ∩ Set.Icc 1 (S.d n))) ≤ (Set.ncard ((iterated_sumset ((constructed_A TB.B S.d r) \ I (S.d n) (L r (S.d n))) (h - 1)) ∩ Set.Icc 1 (S.d n))) + (Set.ncard ({s ∈ Set.Icc 1 (S.d n) | ∃ a ∈ I (S.d n) (L r (S.d n)), a ≤ s})) := by
          refine' Filter.eventually_atTop.mpr ⟨ 0, fun n hn => _ ⟩;
          have h_decomp : (Set.ncard ((iterated_sumset (constructed_A TB.B S.d r) (h - 1)) ∩ Set.Icc 1 (S.d n))) ≤ (Set.ncard (((iterated_sumset (constructed_A TB.B S.d r \ I (S.d n) (L r (S.d n))) (h - 1)) ∪ {s | ∃ a ∈ I (S.d n) (L r (S.d n)), a ≤ s}) ∩ Set.Icc 1 (S.d n))) := by
            apply_rules [ Set.ncard_le_ncard ];
            · intro x hx;
              have := sumset_decomposition ( constructed_A TB.B S.d r ) ( I ( S.d n ) ( L r ( S.d n ) ) ) ( h - 1 );
              specialize this hx.1; aesop;
            · exact Set.Finite.subset ( Set.finite_Icc 1 ( S.d n ) ) fun x hx => hx.2;
          refine le_trans h_decomp ?_;
          convert Set.ncard_union_le _ _ using 2 ; ext ; aesop;
        filter_upwards [ h_decomp, Filter.eventually_ge_atTop 1 ] with n hn hn';
        refine le_trans hn ?_;
        rw [ add_comm ];
        gcongr;
        · have h_finite : Set.Finite (constructed_A TB.B S.d r ∩ Set.Icc 1 (S.d n - L r (S.d n))) := by
            exact Set.finite_iff_bddAbove.mpr ⟨ S.d n - L r ( S.d n ), fun x hx => hx.2.2 ⟩;
          have h_finite : ∀ k, Set.Finite (iterated_sumset (constructed_A TB.B S.d r ∩ Set.Icc 1 (S.d n - L r (S.d n))) k) := by
            intro k;
            induction' k with k ih;
            · exact Set.finite_singleton 0;
            · exact Set.Finite.add h_finite ih;
          exact h_finite _;
        · apply_rules [ S2_subset_lemma ];
          unfold constructed_A; aesop;
          unfold I at h_2; aesop;
          exact Nat.one_le_iff_ne_zero.mpr ( by aesop_cat );
      -- Apply the cardinality bounds from h_card_bounds.
      have h_card_bounds_applied : ∀ᶠ n in Filter.atTop, (Set.ncard ((iterated_sumset (constructed_A TB.B S.d r) (h - 1)) ∩ Set.Icc 1 (S.d n))) ≤ (L r (S.d n)) + (Set.ncard ((constructed_A TB.B S.d r) ∩ Set.Icc 1 ((S.d n) - L r (S.d n)))) ^ (h - 1) := by
        filter_upwards [ h_decomp, Filter.eventually_gt_atTop 0 ] with n hn hn' ; aesop;
        refine le_trans hn ?_;
        apply_rules [ add_le_add, S1_card_bound, card_iterated_sumset_le ];
      norm_num +zetaDelta at *;
      obtain ⟨ a, ha ⟩ := h_card_bounds_applied; use a; intros n hn; specialize ha n hn; unfold count_in_range; norm_cast; aesop;

/-
Bound for the cardinality of the second part of the sumset decomposition.
-/
theorem S2_card_bound (h : ℕ) (r : ℝ) (TB : ThinBasis h) (S : ValidSequence h r TB.C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) (hB_pos : ∀ x ∈ TB.B, 1 ≤ x) :
  ∀ᶠ n in atTop, (count_in_range (iterated_sumset ((constructed_A TB.B S.d r) \ I (S.d n) (L r (S.d n))) (h - 1)) (S.d n) : ℝ) ≤
    (count_in_range (constructed_A TB.B S.d r) ((S.d n) - L r (S.d n)) : ℝ)^(h - 1) := by
      have h_subset : ∀ᶠ n in atTop, (Set.ncard ((iterated_sumset (constructed_A TB.B S.d r \ I (S.d n) (L r (S.d n))) (h - 1)) ∩ Set.Icc 1 (S.d n) : Set ℕ)) ≤ (Set.ncard ((iterated_sumset (constructed_A TB.B S.d r ∩ Set.Icc 1 (S.d n - L r (S.d n))) (h - 1)) : Set ℕ)) := by
        refine' Filter.Eventually.of_forall fun n => _;
        apply Set.ncard_le_ncard;
        · apply_rules [ S2_subset_lemma ];
          unfold constructed_A; aesop;
          unfold I at h_1; aesop;
          omega;
        · -- The set `constructed_A TB.B S.d r ∩ Set.Icc 1 (S.d n - L r (S.d n))` is finite because it is a subset of a finite set.
          have h_finite : Set.Finite (constructed_A TB.B S.d r ∩ Set.Icc 1 (S.d n - L r (S.d n))) := by
            exact Set.finite_iff_bddAbove.mpr ⟨ _, fun x hx => hx.2.2 ⟩;
          -- The sumset of a finite set is finite.
          have h_sumset_finite : ∀ (S : Set ℕ), Set.Finite S → ∀ k : ℕ, Set.Finite (iterated_sumset S k) := by
            intro S hS k; induction' k with k ih <;> simp_all +decide [ iterated_sumset ] ;
            exact hS.add ih;
          exact h_sumset_finite _ h_finite _;
      refine Filter.Eventually.mono h_subset ?_;
      unfold count_in_range; aesop;
      refine' le_trans ( Nat.cast_le.mpr a ) _;
      exact_mod_cast card_iterated_sumset_le _ _

/-
Bound for A_{h-1}(d_n) in terms of L_n and A(d_n - L_n).
-/
theorem Ah_minus_1_bound_final (h : ℕ) (r : ℝ) (TB : ThinBasis h) (S : ValidSequence h r TB.C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) (hB_pos : ∀ x ∈ TB.B, 1 ≤ x) :
  ∀ᶠ n in atTop, (count_in_range (iterated_sumset (constructed_A TB.B S.d r) (h - 1)) (S.d n) : ℝ) ≤
    (L r (S.d n) : ℝ) + (count_in_range (constructed_A TB.B S.d r) ((S.d n) - L r (S.d n)) : ℝ)^(h - 1) := by
      convert Ah_minus_1_bound h r TB S h_ge_3 hr1 hr2 hB_pos using 1

/-
For large n, A_{h-1}(d_n) <= 2 * d_n^r.
-/
theorem Ah_minus_1_upper_bound (h : ℕ) (r : ℝ) (TB : ThinBasis h) (S : ValidSequence h r TB.C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) (hB_pos : ∀ x ∈ TB.B, 1 ≤ x) :
  ∀ᶠ n in atTop, (count_in_range (iterated_sumset (constructed_A TB.B S.d r) (h - 1)) (S.d n) : ℝ) ≤ 2 * (S.d n : ℝ)^r := by
    -- Apply the bounds from Ah_minus_1_bound and A_dn_minus_Ln_bound.
    have h_combined : ∀ᶠ n in atTop, (count_in_range (iterated_sumset (constructed_A TB.B S.d r) (h - 1)) (S.d n) : ℝ) ≤ (L r (S.d n) : ℝ) + ((TB.C + 1/4) * (S.d n : ℝ)^(1 / (h : ℝ)))^(h - 1) := by
      bound;
      filter_upwards [ A_dn_minus_Ln_bound h r TB S h_ge_3 hr1 hr2, Ah_minus_1_bound h r TB S h_ge_3 hr1 hr2 hB_pos ] with n hn hn';
      exact hn'.trans ( add_le_add_left ( pow_le_pow_left₀ ( Nat.cast_nonneg _ ) hn _ ) _ );
    -- Since $r > 1 - 1/h$, we have $(h-1)/h < r$.
    have h_exp : (h - 1 : ℝ) / h < r := by
      rw [ div_lt_iff₀ ] <;> nlinarith [ show ( h : ℝ ) ≥ 3 by norm_cast, one_div_mul_cancel ( by positivity : ( h : ℝ ) ≠ 0 ) ];
    -- Since $(h-1)/h < r$, we have $(TB.C + 1/4)^{h-1} * (S.d n : ℝ)^{(h-1)/h} \leq (S.d n : ℝ)^r$ for large $n$.
    have h_exp_bound : ∀ᶠ n in atTop, ((TB.C + 1/4) * (S.d n : ℝ)^(1 / (h : ℝ)))^(h - 1) ≤ (S.d n : ℝ)^r := by
      -- Since $(h-1)/h < r$, we have $(TB.C + 1/4)^{h-1} * (S.d n : ℝ)^{(h-1)/h} \leq (S.d n : ℝ)^r$ for large $n$ by the properties of exponents.
      have h_exp_bound : ∀ᶠ n in atTop, ((TB.C + 1/4)^(h - 1) : ℝ) * (S.d n : ℝ)^((h - 1) / h : ℝ) ≤ (S.d n : ℝ)^r := by
        have h_exp_bound : ∀ᶠ n in atTop, ((TB.C + 1/4)^(h - 1) : ℝ) ≤ (S.d n : ℝ)^(r - (h - 1) / h : ℝ) := by
          have h_exp_bound : Filter.Tendsto (fun n => (S.d n : ℝ)^(r - (h - 1) / h : ℝ)) Filter.atTop Filter.atTop := by
            exact tendsto_rpow_atTop ( by linarith ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop.comp <| S.d_strict_mono.tendsto_atTop;
          exact h_exp_bound.eventually_ge_atTop _;
        filter_upwards [ h_exp_bound, Filter.eventually_gt_atTop 0 ] with n hn hn' using le_trans ( mul_le_mul_of_nonneg_right hn <| by positivity ) <| by rw [ ← Real.rpow_add <| Nat.cast_pos.mpr <| S.d_pos n ] ; ring_nf; norm_num;
      convert h_exp_bound using 3;
      rw [ mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg _ ) ] ; ring;
      rw [ Nat.cast_pred ( by linarith ) ] ; ring;
    filter_upwards [ h_combined, h_exp_bound, Filter.eventually_ge_atTop 0 ] with n hn hn' hn'';
    linarith [ show ( L r ( S.d n ) : ℝ ) ≤ ( S.d n : ℝ ) ^ r by exact_mod_cast Nat.floor_le ( by exact Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ]

/-
Checking the type of Filter.liminf and Filter.atTop.
-/
#check Filter.liminf

#check Filter.atTop

/-
The limit inferior of the ratio A_{h-1}(x)/A(x) is at most 4.
-/
noncomputable def ratio_fun (A : Set ℕ) (h : ℕ) (x : ℝ) : ℝ :=
  (count_in_range (iterated_sumset A (h - 1)) x : ℝ) / (count_in_range A x : ℝ)

theorem liminf_ratio_le_four (h : ℕ) (r : ℝ) (TB : ThinBasis h) (S : ValidSequence h r TB.C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) (hB_pos : ∀ x ∈ TB.B, 1 ≤ x) :
  Filter.liminf (ratio_fun (constructed_A TB.B S.d r) h) Filter.atTop ≤ 4 := by
    by_contra h_contra;
    -- By the definition of limit inferior, there exists some $N$ such that for all $x \geq N$, $\frac{A_{h-1}(x)}{A(x)} > 4$.
    obtain ⟨N, hN⟩ : ∃ N : ℝ, ∀ x ≥ N, (count_in_range (iterated_sumset (constructed_A TB.B S.d r) (h - 1)) x : ℝ) / (count_in_range (constructed_A TB.B S.d r) x : ℝ) > 4 := by
      rw [ Filter.liminf_eq ] at h_contra ; aesop;
      have := exists_lt_of_lt_csSup ( show { a : ℝ | ∃ a_1 : ℝ, ∀ b : ℝ, a_1 ≤ b → a ≤ ratio_fun ( constructed_A TB.B S.d r ) h b }.Nonempty from by exact Set.nonempty_iff_ne_empty.2 <| by rintro h; rw [ h ] at h_contra; norm_num at h_contra ) h_contra; aesop;
      exact ⟨ w_1, fun x hx => right.trans_le <| h_1 x hx ⟩;
    -- Choose $n$ large enough such that $d_n \geq N$.
    obtain ⟨n, hn⟩ : ∃ n : ℕ, S.d n ≥ N ∧ (count_in_range (iterated_sumset (constructed_A TB.B S.d r) (h - 1)) (S.d n) : ℝ) ≤ 2 * (S.d n : ℝ)^r ∧ (count_in_range (constructed_A TB.B S.d r) (S.d n) : ℝ) ≥ (1/2) * (S.d n : ℝ)^r := by
      have h_exists_n : ∀ᶠ n in atTop, S.d n ≥ N ∧ (count_in_range (iterated_sumset (constructed_A TB.B S.d r) (h - 1)) (S.d n) : ℝ) ≤ 2 * (S.d n : ℝ)^r ∧ (count_in_range (constructed_A TB.B S.d r) (S.d n) : ℝ) ≥ (1/2) * (S.d n : ℝ)^r := by
        have h_exists_n : ∀ᶠ n in atTop, S.d n ≥ N := by
          have h_exists_n : Filter.Tendsto (fun n => S.d n : ℕ → ℝ) Filter.atTop Filter.atTop := by
            exact tendsto_natCast_atTop_atTop.comp S.d_strict_mono.tendsto_atTop;
          exact h_exists_n.eventually_ge_atTop N;
        filter_upwards [ h_exists_n, Ah_minus_1_upper_bound h r TB S h_ge_3 hr1 hr2 hB_pos, A_dn_lower_bound h r TB S h_ge_3 hr1 hr2 ] with n hn hn' hn'' using ⟨ hn, hn', hn'' ⟩;
      exact h_exists_n.exists;
    have := hN ( S.d n ) hn.1;
    rw [ gt_iff_lt, lt_div_iff₀ ] at this <;> nlinarith [ show 0 < ( S.d n : ℝ ) ^ r by exact Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( S.d_pos n ) ) _ ]

/-
A(x) is little-o of x as x tends to infinity.
-/
theorem A_is_o_x (h : ℕ) (r : ℝ) (TB : ThinBasis h) (S : ValidSequence h r TB.C)
  (h_ge_3 : h ≥ 3) (hr1 : 1 - 1/(h : ℝ) < r) (hr2 : r < 1) :
  Asymptotics.IsLittleO Filter.atTop (fun x => (count_in_range (constructed_A TB.B S.d r) x : ℝ)) (fun x => x) := by
    -- By `A_upper_bound`, for large $x$, $A(x) \le C x^{1/h} + 2 x^r$. Since $r < 1$ and $1/h < 1$ (as $h \ge 3$), both terms are $o(x)$. Thus $A(x) = o(x)$.
    have h_o : ∀ᶠ x in Filter.atTop, (count_in_range (constructed_A TB.B S.d r) x : ℝ) ≤ TB.C * x^(1 / (h : ℝ)) + 2 * x^r := by
      exact A_upper_bound h r TB S h_ge_3 hr1 hr2;
    have h_o : ∀ᶠ x in Filter.atTop, (count_in_range (constructed_A TB.B S.d r) x : ℝ) ≤ 2 * (TB.C + 2) * x^r := by
      filter_upwards [ h_o, Filter.eventually_gt_atTop 1 ] with x hx₁ hx₂;
      nlinarith [ show ( TB.C : ℝ ) ≥ 0 by exact le_of_lt TB.C_pos, show x ^ ( 1 / ( h : ℝ ) ) ≤ x ^ r by exact Real.rpow_le_rpow_of_exponent_le hx₂.le ( by rw [ div_eq_mul_inv ] ; nlinarith [ show ( h : ℝ ) ≥ 3 by norm_cast, mul_inv_cancel₀ ( by positivity : ( h : ℝ ) ≠ 0 ), one_div_mul_cancel ( by positivity : ( h : ℝ ) ≠ 0 ) ] ), show x ^ r > 0 by positivity ];
    rw [ Asymptotics.isLittleO_iff_tendsto' ];
    · -- Since $r < 1$, we have $x^r / x \to 0$ as $x \to \infty$.
      have h_frac_zero : Filter.Tendsto (fun x : ℝ => x^r / x) Filter.atTop (nhds 0) := by
        have h_frac_zero : Filter.Tendsto (fun x : ℝ => x^(r - 1)) Filter.atTop (nhds 0) := by
          simpa using tendsto_rpow_neg_atTop ( by linarith : 0 < - ( r - 1 ) );
        refine h_frac_zero.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Real.rpow_sub_one hx.ne' ] );
      refine' squeeze_zero_norm' _ ( by simpa using h_frac_zero.const_mul ( 2 * ( TB.C + 2 ) ) );
      filter_upwards [ h_o, Filter.eventually_gt_atTop 0 ] with x hx₁ hx₂ using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ mul_div ] ; gcongr;
    · filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx hx' using absurd hx' hx.ne'

/-
Formalized the construction of a counterexample to the Erdős-Graham question, following the paper by Ruzsa and Turjányi.
The main result is `corollary_conditional`, which establishes the existence of a set $A$ with density 0 and bounded sumset ratio, conditional on the existence of a thin basis of order 3 (a classical result by Cassels).
The construction relies on `Theorem 3.1`, formalized as `A_is_o_x` and `liminf_ratio_le_four`.
The existence of a thin basis is assumed as a hypothesis in `corollary_conditional` since its proof is classical but non-trivial to formalize from scratch.
-/

/-
Conditional on the existence of a thin basis of order 3 (with positive elements), there exists a set A which is a basis of order 3, has density 0, and bounded sumset ratio.
-/
theorem corollary_conditional (TB : ThinBasis 3) (hB_pos : ∀ x ∈ TB.B, 1 ≤ x) :
  ∃ A : Set ℕ, is_basis_of_order A 3 ∧
  Asymptotics.IsLittleO Filter.atTop (fun x => (count_in_range A x : ℝ)) (fun x => x) ∧
  Filter.liminf (ratio_fun A 3) Filter.atTop ≤ 4 := by
    -- Let's choose $r = 0.8$ and apply the `exists_valid_sequence` theorem.
    set r : ℝ := 0.8
    have hr1 : 1 - 1 / (3 : ℝ) < r := by
      norm_num
    have hr2 : r < 1 := by
      norm_num
    obtain ⟨S, hS⟩ : ∃ S : ValidSequence 3 r TB.C, True := by
      exact ⟨ Classical.choose ( exists_valid_sequence 3 ( by norm_num ) r hr1 hr2 TB.C TB.C_pos ), trivial ⟩;
    -- Let's construct the set $A$ using the sequence $S$ and the thin basis $TB$.
    use constructed_A TB.B S.d r;
    exact ⟨ step3_basis 3 _ _ _ TB.is_basis, A_is_o_x 3 r TB S ( by norm_num ) hr1 hr2, liminf_ratio_le_four 3 r TB S ( by norm_num ) hr1 hr2 hB_pos ⟩

/-
We have formalized the construction of a thin basis of order 3 for the natural numbers, following the provided mathematical text.
The main result is `exists_thin_basis_order_three_positive`, which asserts the existence of a set `B` of positive integers that is a basis of order 3 and has counting function `B(x) = O(x^(1/3))`.
The construction proceeds by first defining sets `A_0, A_1, A_2` based on binary expansions, proving they form a basis for `N_0` (`A_constructed_is_basis`) and are thin (`A_constructed_is_thin`).
Then `B` is defined as `A + {1}`, and it is shown to be a basis for `N` (`B_constructed_is_basis`) and thin (`B_constructed_is_thin`).
All intermediate lemmas and theorems from the text have been formalized.
-/


/-
Definitions of W_i, A_i, and A from the construction.
-/
def W (i : ℕ) : Set ℕ := { j | j % 3 = i }

def A_part (i : ℕ) : Set ℕ := { n | ∀ j, Nat.testBit n j → j ∈ W i }

def A_constructed : Set ℕ := A_part 0 ∪ A_part 1 ∪ A_part 2

/-
The set A constructed is an additive basis of order 3 for N_0.
-/
theorem A_constructed_is_basis : iterated_sumset A_constructed 3 = Set.univ := by
  -- We need to show that for any non-negative integer $n$, there exist $a_0 \in A_0$, $a_1 \in A_1$, and $a_2 \in A_2$ such that $n = a_0 + a_1 + a_2$.
  have h_decomp : ∀ n : ℕ, ∃ a0 ∈ A_part 0, ∃ a1 ∈ A_part 1, ∃ a2 ∈ A_part 2, n = a0 + a1 + a2 := by
    intro n;
    -- Let's construct $a_0$, $a_1$, and $a_2$ by splitting the binary representation of $n$ into three parts.
    obtain ⟨a0, a1, a2, ha⟩ : ∃ a0 a1 a2 : ℕ, n = a0 + a1 + a2 ∧ (∀ j, Nat.testBit a0 j → j % 3 = 0) ∧ (∀ j, Nat.testBit a1 j → j % 3 = 1) ∧ (∀ j, Nat.testBit a2 j → j % 3 = 2) := by
      induction' n using Nat.binaryRec with b n ih;
      · exact ⟨ 0, 0, 0, rfl, by norm_num, by norm_num, by norm_num ⟩;
      · obtain ⟨ a0, a1, a2, rfl, ha0, ha1, ha2 ⟩ := ih;
        use if b then 2 * a2 + 1 else 2 * a2, 2 * a0, 2 * a1;
        split_ifs <;> simp_all +decide [ Nat.testBit, Nat.shiftRight_eq_div_pow ];
        · aesop;
          · ring;
          · rcases j with ( _ | j ) <;> norm_num [ Nat.add_div, Nat.mul_div_assoc, Nat.pow_succ', ← Nat.div_div_eq_div_mul ] at *;
            specialize ha2 j a; omega;
          · rcases j with ( _ | j ) <;> simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
            norm_num [ Nat.add_mod, ha0 j a ];
          · rcases j with ( _ | j ) <;> simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
            grind;
        · refine' ⟨ by ring, _, _, _ ⟩ <;> intro j hj <;> rcases j with ( _ | j ) <;> simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
          · specialize ha2 j hj; omega;
          · specialize ha0 j hj; omega;
          · specialize ha1 j hj ; omega;
    unfold A_part; aesop;
  -- By definition of union, we have $A \supseteq A_0 \cup A_1 \cup A_2$.
  have h_union : A_constructed ⊇ A_part 0 ∪ A_part 1 ∪ A_part 2 := by
    exact fun x hx => by aesop;
  norm_num +zetaDelta at *;
  -- Apply the definition of iterated sumset
  ext n
  simp [iterated_sumset];
  rcases h_decomp n with ⟨ a0, ha0, a1, ha1, a2, ha2, rfl ⟩ ; exact ⟨ a0, h_union.1.1 ha0, a1 + a2, Set.add_mem_add ( h_union.1.2 ha1 ) ( h_union.2 ha2 ), by ring ⟩ ;

/-
Elements of A_i bounded by x are sums of powers of 2 with exponents in J_i(x).
-/
def J (i : ℕ) (x : ℝ) : Finset ℕ :=
  (Finset.range (Nat.log 2 (Nat.floor x) + 1)).filter (fun j => j ∈ W i)

theorem A_part_subset_powerset (i : ℕ) (x : ℝ) (hx : x ≥ 1) :
  ∀ a ∈ A_part i, a ≤ x →
  ∃ s ⊆ J i x, a = s.sum (fun j => 2^j) := by
    intro a ha hx' ; use Finset.filter ( fun j ↦ Nat.testBit a j = Bool.true ) ( Finset.range ( Nat.log 2 ( Nat.floor x ) + 1 ) ) ; aesop;
    · intro j hj; unfold J; aesop;
    · -- Apply the theorem that states a number is equal to the sum of 2^j for the positions where the binary digit is 1.
      have h_binary_expansion : a = ∑ j ∈ Finset.range (Nat.log 2 a + 1), (if Nat.testBit a j then 2 ^ j else 0) := by
        -- By definition of binary representation, the sum of 2^j for the positions where the binary digit is 1 is equal to a.
        have h_binary : ∀ n : ℕ, n = ∑ j ∈ Finset.range (Nat.log 2 n + 1), (if (n.testBit j) then 2 ^ j else 0) := by
          intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> simp +arith +decide [ Finset.sum_range_succ', Nat.testBit ] ;
          have := ih ( ( n + 2 ) / 2 ) ( Nat.div_lt_of_lt_mul <| by linarith ) ; norm_num [ Nat.pow_succ', Nat.mul_mod, Nat.div_add_mod ] at *;
          rw [ show Nat.log 2 ( n + 2 ) = Nat.log 2 ( n / 2 + 1 ) + 1 from ?_ ];
          · norm_num [ Nat.testBit, Nat.shiftRight_eq_div_pow ] at *;
            norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ] at *;
            norm_num [ Finset.sum_ite ] at *;
            rw [ ← Finset.mul_sum _ _ _ ] ; split_ifs <;> omega;
          · rw [ Nat.log_eq_iff ] <;> norm_num;
            exact ⟨ by rw [ pow_succ' ] ; linarith [ Nat.div_mul_le_self n 2, Nat.pow_log_le_self 2 ( show n / 2 + 1 ≠ 0 by norm_num ) ], by rw [ pow_succ' ] ; linarith [ Nat.div_add_mod n 2, Nat.mod_lt n two_pos, Nat.lt_pow_of_log_lt ( by norm_num ) ( show Nat.log 2 ( n / 2 + 1 ) < Nat.log 2 ( n / 2 + 1 ) + 1 by norm_num ) ] ⟩;
        exact h_binary a;
      rw [ Finset.sum_filter ];
      refine' Eq.trans h_binary_expansion ( Finset.sum_subset _ _ ) <;> simp +contextual [ Finset.subset_iff ];
      · exact fun n hn => lt_of_lt_of_le hn ( Nat.succ_le_succ ( Nat.log_mono_right <| Nat.le_floor <| mod_cast hx' ) );
      · intro j hj₁ hj₂; rw [ Nat.testBit_eq_false_of_lt ] ; linarith [ Nat.lt_pow_of_log_lt one_lt_two hj₂ ] ;

/-
The cardinality of J_i(x) is at most (log_2 x)/3 + 1.
-/
theorem card_J_le (i : ℕ) (x : ℝ) (hx : x ≥ 1) :
  (J i x).card ≤ (Nat.log 2 (Nat.floor x)) / 3 + 1 := by
    refine' le_trans ( Finset.card_le_card _ ) _;
    exact Finset.image ( fun j => j * 3 + i % 3 ) ( Finset.range ( Nat.log 2 ⌊x⌋₊ / 3 + 1 ) );
    · intro j hj; aesop;
      unfold J at hj; aesop;
      unfold W at right; aesop;
      exact ⟨ j / 3, by omega, by omega ⟩;
    · exact Finset.card_image_le.trans ( by norm_num )

/-
The counting function of A_i is bounded by 2^|J_i(x)|.
-/
theorem card_A_part_le_two_pow_card_J (i : ℕ) (x : ℝ) (hx : x ≥ 1) :
  count_in_range (A_part i) x ≤ 2 ^ (J i x).card := by
    -- By the previous steps, each element of $A_i \cap [1, x]$ is in the range of the function $f : \mathcal{P}(J_i(x)) \to \mathbb{N}$ defined by $f(s) = \sum_{j \in s} 2^j$.
    have h_image : A_part i ∩ Set.Icc 1 (Nat.floor x) ⊆ Set.image (fun s : Finset ℕ => s.sum (fun j => 2^j)) (Finset.powerset (J i x)) := by
      intro a ha;
      obtain ⟨s, hs⟩ := A_part_subset_powerset i x hx a ha.left (by
      exact le_trans ( Nat.cast_le.mpr ha.2.2 ) ( Nat.floor_le ( by positivity ) ));
      aesop;
    have h_card_image : (Set.ncard (A_part i ∩ Set.Icc 1 (Nat.floor x))) ≤ (Finset.card (Finset.powerset (J i x))) := by
      have h_card_image : Set.ncard (A_part i ∩ Set.Icc 1 (Nat.floor x)) ≤ Finset.card (Finset.image (fun s : Finset ℕ => s.sum (fun j => 2^j)) (Finset.powerset (J i x))) := by
        rw [ ← Set.ncard_coe_finset ];
        apply_rules [ Set.ncard_le_ncard ];
        · aesop;
        · exact Finset.finite_toSet _;
      exact h_card_image.trans ( Finset.card_image_le );
    simp_all +decide [ count_in_range ]

/-
2^(n/3) <= (2^n)^(1/3) for natural n.
-/
lemma two_pow_div_three_le (n : ℕ) : (2 : ℝ) ^ (n / 3) ≤ ((2 : ℝ) ^ n) ^ (1/3 : ℝ) := by
  rw [ Real.le_rpow_iff_log_le ] <;> norm_num;
  nlinarith [ Real.log_pos one_lt_two, show ( n : ℝ ) / 3 ≥ ↑ ( n / 3 ) by exact Nat.cast_div_le .. ]

/-
2^(floor(log2(floor(x)))/3) <= x^(1/3) for x >= 1.
-/
lemma two_pow_div_three_le_x_pow_third (x : ℝ) (hx : x ≥ 1) :
  (2 : ℝ) ^ ((Nat.log 2 (Nat.floor x)) / 3) ≤ x ^ (1/3 : ℝ) := by
    have := two_pow_div_three_le ( Nat.log 2 ⌊x⌋₊ );
    exact le_trans this ( Real.rpow_le_rpow ( by positivity ) ( by exact le_trans ( mod_cast Nat.pow_log_le_self 2 <| Nat.ne_of_gt <| Nat.floor_pos.mpr hx ) <| Nat.floor_le <| by positivity ) <| by positivity )

/-
2^(n/3 + 1) <= 2 * (2^n)^(1/3).
-/
lemma two_pow_bound (n : ℕ) : (2 : ℝ) ^ (n / 3 + 1) ≤ 2 * ((2 : ℝ) ^ n) ^ (1/3 : ℝ) := by
  rw [ pow_succ' ];
  norm_num [ ← Real.rpow_natCast, ← Real.rpow_mul ];
  rw [ mul_one_div, le_div_iff₀ ] <;> norm_cast ; linarith [ Nat.div_mul_le_self n 3 ]

/-
2^(log2(floor(x))) <= x for x >= 1.
-/
lemma two_pow_log_le_self (x : ℝ) (hx : x ≥ 1) :
  (2 : ℝ) ^ (Nat.log 2 (Nat.floor x)) ≤ x := by
    exact le_trans ( mod_cast Nat.pow_log_le_self 2 <| Nat.ne_of_gt <| Nat.floor_pos.mpr hx ) <| Nat.floor_le <| by positivity;

/-
2^(floor(log2(floor(x)))/3 + 1) <= 2 * x^(1/3) for x >= 1.
-/
lemma bound_helper (x : ℝ) (hx : x ≥ 1) :
  (2 : ℝ) ^ ((Nat.log 2 (Nat.floor x)) / 3 + 1) ≤ 2 * x^((1 : ℝ)/3) := by
  let n := Nat.log 2 (Nat.floor x)
  have h1 : (2 : ℝ) ^ (n / 3 + 1) ≤ 2 * ((2 : ℝ) ^ n) ^ ((1 : ℝ)/3) := two_pow_bound n
  have h2 : (2 : ℝ) ^ n ≤ x := two_pow_log_le_self x hx
  have h3 : ((2 : ℝ) ^ n) ^ ((1 : ℝ)/3) ≤ x ^ ((1 : ℝ)/3) := by
    apply Real.rpow_le_rpow
    · norm_num
    · exact h2
    · norm_num
  have h4 : 2 * ((2 : ℝ) ^ n) ^ ((1 : ℝ)/3) ≤ 2 * x ^ ((1 : ℝ)/3) := by
    apply mul_le_mul_of_nonneg_left h3
    norm_num
  exact le_trans h1 h4

/-
The counting function of A_i is bounded by 2 * x^(1/3).
-/
theorem A_part_bound_explicit (i : ℕ) (x : ℝ) (hx : x ≥ 1) :
  (count_in_range (A_part i) x : ℝ) ≤ 2 * x^((1 : ℝ)/3) := by
  have h1 : (count_in_range (A_part i) x : ℝ) ≤ (2 : ℝ) ^ (J i x).card := by
    have := card_A_part_le_two_pow_card_J i x hx
    norm_cast
  have h2 : (J i x).card ≤ (Nat.log 2 (Nat.floor x)) / 3 + 1 := card_J_le i x hx
  have h3 : (2 : ℝ) ^ (J i x).card ≤ (2 : ℝ) ^ ((Nat.log 2 (Nat.floor x)) / 3 + 1) := by
    apply pow_le_pow_right₀
    · norm_num
    · exact h2
  have h4 : (2 : ℝ) ^ ((Nat.log 2 (Nat.floor x)) / 3 + 1) ≤ 2 * x^((1 : ℝ)/3) := bound_helper x hx
  exact le_trans h1 (le_trans h3 h4)

/-
A_constructed is a thin basis of order 3.
-/
theorem A_constructed_is_thin : ∃ C > 0, ∀ x : ℝ, x ≥ 1 → (count_in_range A_constructed x : ℝ) ≤ C * x^((1 : ℝ)/3) := by
  use 6;
  refine' ⟨ by norm_num, fun x hx => _ ⟩;
  have h_subadd : (count_in_range (A_part 0 ∪ A_part 1 ∪ A_part 2) x : ℝ) ≤ (count_in_range (A_part 0) x : ℝ) + (count_in_range (A_part 1) x : ℝ) + (count_in_range (A_part 2) x : ℝ) := by
    norm_cast;
    unfold count_in_range;
    convert Set.ncard_union_le _ _ |> le_trans <| add_le_add_right ( Set.ncard_union_le _ _ ) _ using 2 ; ext ; aesop;
  exact h_subadd.trans ( by linarith! [ A_part_bound_explicit 0 x hx, A_part_bound_explicit 1 x hx, A_part_bound_explicit 2 x hx ] )

/-
Definition of B as the set of elements of A shifted by 1.
-/
def B_constructed : Set ℕ := (A_constructed).image (· + 1)

/-
B_constructed is a basis of order 3.
-/
theorem B_constructed_is_basis : is_basis_of_order B_constructed 3 := by
  -- Since $A$ is a basis of order 3 for $\mathbb{N}_0$, $n-3 = a_1 + a_2 + a_3$ for some $a_i \in A$.
  have h_basis : ∀ n ≥ 3, ∃ a₁ a₂ a₃ : ℕ, a₁ ∈ A_constructed ∧ a₂ ∈ A_constructed ∧ a₃ ∈ A_constructed ∧ n = a₁ + a₂ + a₃ + 3 := by
    intro n hn
    obtain ⟨a₁, a₂, a₃, ha₁, ha₂, ha₃, hn_eq⟩ : ∃ a₁ a₂ a₃ : ℕ, a₁ ∈ A_constructed ∧ a₂ ∈ A_constructed ∧ a₃ ∈ A_constructed ∧ n - 3 = a₁ + a₂ + a₃ := by
      have := A_constructed_is_basis;
      rw [ Set.ext_iff ] at this;
      specialize this ( n - 3 ) ; simp_all +decide [ iterated_sumset ] ;
      rw [ Set.mem_add ] at this; aesop;
      rw [ Set.mem_add ] at left_1 ; aesop;
      exact ⟨ w, left, w_2, left_1, w_3, left_2, by linarith ⟩;
    exact ⟨ a₁, a₂, a₃, ha₁, ha₂, ha₃, by omega ⟩;
  use 3;
  rintro n ( hn : 3 ≤ n ) ; specialize h_basis n hn ; aesop;
  simp_all +decide [ iterated_sumset ];
  exact ⟨ w + 1, ⟨ _, left, rfl ⟩, w_1 + 1 + ( w_2 + 1 ), ⟨ w_1 + 1, ⟨ _, left_1, rfl ⟩, w_2 + 1, ⟨ _, left_2, rfl ⟩, rfl ⟩, by ring ⟩

/-
0 is in A_constructed.
-/
lemma zero_mem_A_constructed : 0 ∈ A_constructed := by
  unfold A_constructed;
  unfold A_part; aesop;

/-
B_constructed is a thin basis of order 3.
-/
theorem B_constructed_is_thin : ∃ C > 0, ∀ x : ℝ, x ≥ 1 → (count_in_range B_constructed x : ℝ) ≤ C * x^((1 : ℝ)/3) := by
  -- By definition of $B_constructed$, we have $B_constructed(x) \leq A(x) + 1$.
  have hB_le_A_plus_one : ∀ x : ℝ, x ≥ 1 → (count_in_range B_constructed x : ℝ) ≤ (count_in_range A_constructed x : ℝ) + 1 := by
    unfold count_in_range; aesop;
    -- Since $B_constructed = A_constructed.image (fun x => x + 1)$, we have $B_constructed \cap [1, \lfloor x \rfloor] = (A_constructed \cap [0, \lfloor x \rfloor - 1]).image (fun x => x + 1)$.
    have hB_eq : B_constructed ∩ Set.Icc 1 ⌊x⌋₊ = (A_constructed ∩ Set.Icc 0 (⌊x⌋₊ - 1)).image (fun x => x + 1) := by
      ext ; aesop;
      · cases left ; aesop;
        exact Nat.le_sub_one_of_lt right;
      · exact Set.mem_image_of_mem _ left;
      · exact Nat.succ_le_of_lt ( right_1.trans_lt ( Nat.pred_lt ( ne_bot_of_gt ( Nat.floor_pos.mpr a ) ) ) );
    rw [ hB_eq, Set.ncard_image_of_injective _ Nat.succ_injective ];
    norm_cast;
    rw [ show A_constructed ∩ Set.Icc 0 ( ⌊x⌋₊ - 1 ) = ( A_constructed ∩ Set.Icc 1 ( ⌊x⌋₊ - 1 ) ) ∪ ( if 0 ∈ A_constructed then { 0 } else ∅ ) from ?_, @Set.ncard_union_eq ];
    · split_ifs <;> simp_all +decide [ Set.ncard_eq_toFinset_card' ];
      · exact Finset.card_mono <| Finset.filter_subset_filter _ <| Finset.Icc_subset_Icc_right <| Nat.pred_le _;
      · exact le_add_of_le_of_nonneg ( Finset.card_mono <| Finset.filter_subset_filter _ <| Finset.Icc_subset_Icc_right <| Nat.pred_le _ ) zero_le_one;
    · aesop;
    · exact Set.finite_iff_bddAbove.mpr ⟨ _, fun y hy => hy.2.2 ⟩;
    · split_ifs <;> norm_num;
    · ext ( _ | n ) <;> aesop;
  have := A_constructed_is_thin;
  obtain ⟨ C, hC₀, hC ⟩ := this; exact ⟨ C + 1, by linarith, fun x hx => by nlinarith [ hB_le_A_plus_one x hx, hC x hx, show ( x : ℝ ) ^ ( 1 / 3 : ℝ ) ≥ 1 by exact Real.one_le_rpow hx ( by norm_num ) ] ⟩ ;

/-
Elements of B_constructed are positive.
-/
lemma B_constructed_subset_positive : ∀ b ∈ B_constructed, 1 ≤ b := by
  rintro _ ⟨ a, ha, rfl ⟩ ; linarith

/-
There exists a thin basis of order 3 consisting of positive integers.
-/
theorem exists_thin_basis_order_three_positive :
  ∃ (TB : ThinBasis 3), (∀ b ∈ TB.B, 1 ≤ b) := by
  obtain ⟨C, hC_pos, h_thin⟩ := B_constructed_is_thin
  let TB : ThinBasis 3 := {
    B := B_constructed
    is_basis := B_constructed_is_basis
    C := C
    C_pos := hC_pos
    thin_condition := by
      intro x hx
      norm_num
      exact h_thin x hx
  }
  use TB
  exact B_constructed_subset_positive

theorem not_erdos_337a : ∃ A : Set ℕ, is_basis_of_order A 3 ∧
  Asymptotics.IsLittleO Filter.atTop (fun x => (count_in_range A x : ℝ)) (fun x => x) ∧
  Filter.liminf (ratio_fun A 3) Filter.atTop ≤ 4 := by
  -- Let's choose any thin basis TB of order 3 with positive elements.
  obtain ⟨TB, hTB_pos⟩ : ∃ (TB : ThinBasis 3), (∀ b ∈ TB.B, 1 ≤ b) := by
    exact?;
  -- Apply the corollary_conditional theorem to TB and hTB_pos.
  apply corollary_conditional TB hTB_pos

/--
Erdős Problem 337:

Let $A\subseteq \mathbb{N}$ be an additive basis (of any finite order)
such that $\lvert A\cap \{1,\ldots,N\}\rvert=o(N)$. Is it true
that \[\lim_{N\to \infty}\frac{\lvert (A+A)\cap
\{1,\ldots,N\}\rvert}{\lvert A\cap \{1,\ldots,N\}\rvert}=\infty?\]
-/
def erdos_337 : Prop :=
  ∀ A : Set ℕ,
    (∃ k : ℕ, is_basis_of_order A k) →
    Asymptotics.IsLittleO Filter.atTop
      (fun x => (count_in_range A x : ℝ))
      (fun x => x) →
    Filter.Tendsto
      (fun x =>
        (count_in_range (A + A) x : ℝ) /
        (count_in_range A x : ℝ))
      Filter.atTop
      Filter.atTop

/-- Negation of Erdős 337. -/
theorem not_erdos_337 : ¬ erdos_337 := by
  -- Let's choose specific values for h, r, and C.
  set h := 3
  set r : ℝ := 3 / 4
  set C := 1;
  -- Let's choose any thin basis of order 3 with positive elements using `exists_thin_basis_order_three_positive`.
  obtain ⟨TB, hTB⟩ : ∃ TB : ThinBasis h, (∀ b ∈ TB.B, 1 ≤ b) := exists_thin_basis_order_three_positive;
  -- Let's choose a valid sequence `S` with `h=3` and `r=3/4`.
  obtain ⟨S, hS⟩ : ∃ S : ValidSequence h r TB.C, True := by
    refine' ⟨ _, trivial ⟩;
    exact Exists.choose ( exists_valid_sequence h ( by norm_num ) r ( by norm_num ) ( by norm_num ) TB.C TB.C_pos );
  -- Define `A` as `constructed_A TB.B S.d r`.
  set A : Set ℕ := constructed_A TB.B S.d r;
  -- We claim `A` is a counterexample to `erdos_337`.
  have hA_basis : is_basis_of_order A h := by
    exact step3_basis h TB.B S.d r TB.is_basis
  have hA_density : Asymptotics.IsLittleO Filter.atTop (fun x => (count_in_range A x : ℝ)) (fun x => x) := by
    -- Apply the lemma A_is_o_x with the given h, r, TB, and S.
    apply A_is_o_x h r TB S (by norm_num) (by norm_num) (by norm_num)
  have hA_ratio : ¬Filter.Tendsto (fun x => (count_in_range (iterated_sumset A (h - 1)) x : ℝ) / (count_in_range A x : ℝ)) Filter.atTop Filter.atTop := by
    -- Assume for contradiction that the ratio tends to infinity.
    by_contra h_contra
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℝ, ∀ x ≥ N₀, (count_in_range (iterated_sumset A (h - 1)) x : ℝ) / (count_in_range A x : ℝ) ≥ 5 := by
      exact Filter.eventually_atTop.mp ( h_contra.eventually_ge_atTop 5 ) |> fun ⟨ N₀, hN₀ ⟩ => ⟨ N₀, fun x hx => hN₀ x hx ⟩;
    -- Let's choose a large enough `n` such that `S.d n ≥ N₀` and `S.d n` is sufficiently large.
    obtain ⟨n, hn₁, hn₂⟩ : ∃ n : ℕ, S.d n ≥ N₀ ∧ (count_in_range (iterated_sumset A (h - 1)) (S.d n) : ℝ) ≤ 2 * (S.d n : ℝ)^r ∧ (count_in_range A (S.d n) : ℝ) ≥ (1/2) * (S.d n : ℝ)^r := by
      have h_exists_n : ∀ᶠ n in Filter.atTop, (count_in_range (iterated_sumset A (h - 1)) (S.d n) : ℝ) ≤ 2 * (S.d n : ℝ)^r ∧ (count_in_range A (S.d n) : ℝ) ≥ (1/2) * (S.d n : ℝ)^r := by
        have h_exists_n : ∀ᶠ n in Filter.atTop, (count_in_range (iterated_sumset A (h - 1)) (S.d n) : ℝ) ≤ 2 * (S.d n : ℝ)^r := by
          have := Ah_minus_1_upper_bound h r TB S ( by norm_num ) ( by norm_num ) ( by norm_num ) hTB; aesop;
        exact h_exists_n.and ( A_dn_lower_bound h r TB S ( by norm_num ) ( by norm_num ) ( by norm_num ) ) |> fun h => h.mono fun n hn => ⟨ hn.1, hn.2 ⟩;
      have h_exists_n : ∀ᶠ n in Filter.atTop, (S.d n : ℝ) ≥ N₀ := by
        have h_exists_n : Filter.Tendsto (fun n => (S.d n : ℝ)) Filter.atTop Filter.atTop := by
          exact tendsto_natCast_atTop_atTop.comp S.d_strict_mono.tendsto_atTop;
        exact h_exists_n.eventually_ge_atTop N₀;
      exact Exists.elim ( Filter.eventually_atTop.mp ( h_exists_n.and ‹∀ᶠ n in Filter.atTop, ( count_in_range ( iterated_sumset A ( h - 1 ) ) ( S.d n : ℝ ) : ℝ ) ≤ 2 * ( S.d n : ℝ ) ^ r ∧ ( count_in_range A ( S.d n : ℝ ) : ℝ ) ≥ 1 / 2 * ( S.d n : ℝ ) ^ r› ) ) fun n hn => ⟨ n, hn n le_rfl |>.1, hn n le_rfl |>.2 ⟩;
    have := hN₀ ( S.d n ) hn₁;
    rw [ ge_iff_le, le_div_iff₀ ] at this <;> nlinarith [ show ( 0 : ℝ ) < ( S.d n : ℝ ) ^ r by exact Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| S.d_pos n ) _ ];
  contrapose! hA_ratio;
  convert hA_ratio A ⟨ h, hA_basis ⟩ hA_density using 1;
  simp +zetaDelta at *;
  norm_num [ iterated_sumset ]
