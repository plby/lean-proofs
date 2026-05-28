/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 355.
https://www.erdosproblems.com/forum/thread/355

Informal authors:
- Wouter van Doorn
- Vjekoslav Kovač

Formal authors:
- Aristotle
- Wouter van Doorn

URLs:
- https://www.erdosproblems.com/forum/thread/355#post-4741
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem355.lean
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/355.lean
-/
/-
Solving Erdős Problem #355 (https://www.erdosproblems.com/355), Vjekoslav Kovač and I proved that there exists a lacunary sequence of positive integers whose reciprocal sums represent all rational numbers in an interval.

W. van Doorn and V. Kovač, Lacunary sequences whose reciprocal sums represent all rationals in an interval. arXiv:2509.24971 (2025).

Below you can find a formalization of the main results of our paper, obtained by Aristotle from Harmonic (aristotle-harmonic@harmonic.fun).

More precisely, for a parameter $λ > 1$, let us say that a sequence $A = \{a_1 < a_2 < \cdots\}$ of positive integers is $λ$-lacunary if $a_{i+1} \ge λ a_i$ for all $i$. Let's further define $P(A^{-1})}$ to be the set of all rationals that can be written as a finite sum of reciprocals of elements in $A$, and define $R(λ)$ to be the least upper bound on the length $\beta - \alpha$ of an interval $(\alpha, \beta)$ for which there exists a $λ$-lacunary sequence of positive integers $A$ such that $P(A^{-1})$ contains all rational numbers from $(\alpha, \beta)$. Then at the end of the Lean-file below the following four theorems are proven.

Theorem 1. For all $λ \in (1, 2)$ there exists a $λ$-lacunary sequence $A = \{a_1 < a_2 < \cdots\}$ of positive integers with $\frac{a_{i+1}}{a_i} \to 2$ such that $P(A^{-1})$ contains every rational in the interval $[0, 2]$.

Theorem 2. For all $λ \in (1, 2)$ we have $R(λ) = \sum_{i=1}^{\infty} \frac{1}{b_i}$.

Theorem 3. For all $Λ \ge 2$ and all $λ$ with $1 < λ < Λ/(Λ-1)$, there exists a $λ$-lacunary sequence $A = \{a_1 < a_2 < \cdots\}$ of positive integers for which infinitely many indices $i$ exist with $a_{i+1} > Λ a_i$, and such that $P(A^{-1})$ contains every positive rational smaller than $\frac{1}{a_i}$.

Theorem 4. If $A$ is a set of positive integers with $2A ⊆ A$ and such that $A$ contains a multiple of each odd integer, then $P(A^{-1})$ contains every positive rational smaller than $\sum_{a \in A} \frac{1}{a}$.

At the very end of the file you can find the statement of Erdős Problem #355 taken from the Formal Conjectures project by Google DeepMind, which we also prove.

https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/355.lean

-/

import Mathlib

set_option linter.style.setOption false
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.induction false
set_option linter.style.refine false
set_option linter.style.multiGoal false
set_option linter.style.cases false
set_option linter.style.whitespace false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 50000000
-- Several generated distance-graph arguments time out at the default heartbeat limit.
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

noncomputable section

namespace Erdos355

open Set Filter Topology
open scoped BigOperators

/-
Basic definitions of e.g. lacunarity, the function $R(λ)$, and the assumption on $S$ for Theorem 4. These definitions are sufficient in order to understand the statements of our results at the end.
-/

/-
For a parameter $λ  > 1$, we say that a sequence $n_1, n_2, \ldots$ is $λ$-lacunary if $n_{i+1} \ge λ n_i$ for all $i ≥ 1$. It is simply said to be lacunary if it is $λ$-lacunary for some $λ > 1$.
-/
def IsLambdaLacunary (lambda : ℝ) (seq : ℕ → ℝ) : Prop :=
  ∀ i, seq (i + 1) / seq i ≥ lambda

def IsLacunary (a : ℕ → ℕ) : Prop :=
  ∃ lambda_val > 1, ∀ i ≥ 1, (a (i + 1) : ℝ) / a i ≥ lambda_val

/-
Given a sequence, SubsetSums is the set of finite sums of elements of the sequence.
-/
def SubsetSums (seq : ℕ → ℝ) : Set ℝ :=
  { s | ∃ t : Finset ℕ, s = ∑ i ∈ t, seq i }

/-
$R(λ)$ is the supremum of lengths of intervals filled by $λ$-lacunary sequences.
-/
def FillsInterval (lambda : ℝ) (alpha beta : ℝ) : Prop :=
  ∃ n : ℕ → ℕ,
    (∀ i, 0 < n i) ∧
    IsLambdaLacunary lambda (fun i => n i) ∧
    Set.Ioo alpha beta ∩ {x | ∃ q : ℚ, x = q} ⊆ SubsetSums (fun i => (1 : ℝ) / n i)

noncomputable def R_lambda (lambda : ℝ) : ℝ :=
  sSup {len | ∃ alpha beta, beta - alpha = len ∧ FillsInterval lambda alpha beta}

/-
The property S_cond requires a set $S$ to contain $2S$, as well as a multiple of every odd integer.
-/
def S_cond (S : Set ℕ) : Prop :=
  (∀ s ∈ S, s > 0) ∧ (∀ s ∈ S, 2 * s ∈ S) ∧ (∀ k, Odd k → ∃ s ∈ S, k ∣ s)

/-
Definition of the target interval $[0, \sum f_i)$ which is $[0, \infty)$ if the sum diverges.
-/
noncomputable def TargetInterval (f : ℕ → ℝ) : Set ℝ :=
  if Summable f then Set.Ico 0 (∑' i, f i) else Set.Ici 0

/-
The set $S$ $x_m$-densely fills in the segment $[a, b]$, i.e., it divides this segment into sub-intervals of length at most $x_m$.
-/
def DenselyFills (S : Set ℝ) (a b δ : ℝ) : Prop :=
  S ⊆ Icc a b ∧ a ∈ S ∧ b ∈ S ∧
  ∀ x ∈ Icc a b, ∃ s1 ∈ S, ∃ s2 ∈ S, s1 ≤ x ∧ x ≤ s2 ∧ s2 - s1 ≤ δ

/-
If a set $S$ $\delta$-densely fills $[0, U]$ and $x \le U + \delta$, then the union of $S$ and $S+x$ $\delta$-densely fills $[0, U+x]$.
-/
lemma densely_fills_union (S : Set ℝ) (U x δ : ℝ)
  (hS : DenselyFills S 0 U δ)
  (hx : 0 < x)
  (h_gap : x ≤ U + δ) :
  DenselyFills (S ∪ {s + x | s ∈ S}) 0 (U + x) δ := by
  obtain ⟨ hS_sub, hS0, hSU, hS_dense ⟩ := hS;
  refine' ⟨ _, _, _, _ ⟩;
  · exact Set.union_subset ( hS_sub.trans ( Set.Icc_subset_Icc_right ( by linarith ) ) ) ( Set.image_subset_iff.mpr fun s hs => ⟨ by linarith [ Set.mem_Icc.mp ( hS_sub hs ) ], by linarith [ Set.mem_Icc.mp ( hS_sub hs ) ] ⟩ );
  · exact Or.inl hS0;
  · exact Or.inr ⟨ U, hSU, rfl ⟩;
  · intro y hy
    by_cases hy_case : y ≤ U ∨ y ≥ x;
    · cases hy_case <;> simp_all +decide [ Set.subset_def ];
      · rcases hS_dense y hy.1 ‹_› with ⟨ s1, hs1, s2, hs2, h1, h2, h3 ⟩ ; exact ⟨ s1, Or.inl hs1, s2, Or.inl hs2, h1, h2, h3 ⟩;
      · obtain ⟨ s1, hs1, s2, hs2, hs1_le, hs2_le, hs2_le' ⟩ := hS_dense ( y - x ) ( by linarith ) ( by linarith ) ; exact ⟨ s1 + x, Or.inr ⟨ s1, hs1, rfl ⟩, s2 + x, Or.inr ⟨ s2, hs2, rfl ⟩, by linarith, by linarith, by linarith ⟩ ;
    · exact ⟨ U, Or.inl hSU, x, Or.inr ⟨ 0, hS0, by ring ⟩, by push Not at hy_case; linarith, by push Not at hy_case; linarith, by push Not at hy_case; linarith ⟩

/-
Suppose that $x_1>x_2>\cdots>x_m>0$ are real numbers satisfying
\[ x_i \leqslant \sum_{j=i+1}^{m}x_j + x_m \]
for all $i$ with $1 \le i \le m-1$. Then the set
\[ \Big\{ \sum_{i\in T}x_i : T\subseteq\{1,2,\ldots,m\} \Big\} \]
$x_m$-densely fills in the segment
$[0,\sum_{i=1}^{m}x_i]$,
i.e., it divides this segment into sub-intervals of length at most $x_m$.
-/
lemma lm_reals (m : ℕ) (hm : m ≥ 1) (x : ℕ → ℝ)
  (h_pos : ∀ i ∈ Finset.Icc 1 m, 0 < x i)
  (h_dec : ∀ i ∈ Finset.Icc 1 (m - 1), x (i + 1) < x i)
  (h_cond : ∀ i ∈ Finset.Icc 1 (m - 1), x i ≤ (∑ j ∈ Finset.Icc (i + 1) m, x j) + x m) :
  DenselyFills { s | ∃ t ⊆ Finset.Icc 1 m, s = ∑ i ∈ t, x i } 0 (∑ i ∈ Finset.Icc 1 m, x i) (x m) := by
  induction' m with m ih generalizing x;
  · contradiction;
  · have h_ind : DenselyFills {s | ∃ t ⊆ Finset.Icc 2 (m + 1), s = ∑ i ∈ t, x i} 0 (∑ i ∈ Finset.Icc 2 (m + 1), x i) (x (m + 1)) := by
      by_cases hm : m ≥ 1;
      · convert ih hm ( fun i => x ( i + 1 ) ) _ _ _ using 1;
        · ext s
          constructor
          intro hs
          obtain ⟨t, ht_sub, ht_sum⟩ := hs
          use Finset.image (fun i => i - 1) t
          simp [ht_sum];
          · exact ⟨ Finset.image_subset_iff.mpr fun i hi => Finset.mem_Icc.mpr ⟨ Nat.le_sub_one_of_lt <| Finset.mem_Icc.mp ( ht_sub hi ) |>.1, Nat.sub_le_of_le_add <| by linarith [ Finset.mem_Icc.mp ( ht_sub hi ) |>.2 ] ⟩, by rw [ Finset.sum_image <| by intros i hi j hj hij; linarith [ Nat.sub_add_cancel <| show 1 ≤ i from by linarith [ Finset.mem_Icc.mp ( ht_sub hi ) |>.1 ], Nat.sub_add_cancel <| show 1 ≤ j from by linarith [ Finset.mem_Icc.mp ( ht_sub hj ) |>.1 ] ] ] ; exact Finset.sum_congr rfl fun i hi => by rw [ Nat.sub_add_cancel <| show 1 ≤ i from by linarith [ Finset.mem_Icc.mp ( ht_sub hi ) |>.1 ] ] ⟩;
          · rintro ⟨ t, ht, rfl ⟩ ; use Finset.image ( fun i => i + 1 ) t; simp_all +decide [ Finset.subset_iff ] ;
        · erw [ Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, add_left_comm, Finset.sum_range_succ' ];
        · exact fun i hi => h_pos _ <| Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hi ], by linarith [ Finset.mem_Icc.mp hi ] ⟩;
        · exact fun i hi => h_dec _ <| Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hi ], Nat.succ_le_of_lt <| Nat.lt_of_le_of_lt ( Finset.mem_Icc.mp hi |>.2 ) <| Nat.pred_lt <| ne_bot_of_gt hm ⟩;
        · intro i hi
          specialize h_cond ( i + 1 )
          have icc_succ : ∀ a b : ℕ, Finset.Icc (a + 1) b = Finset.Ioc a b := fun a b => by
            ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
          rcases m with ( _ | m ) <;> simp_all +decide [Finset.sum_Ioc_succ_top] ;
          convert h_cond using 2 ; rw [ show Finset.Ioc ( i + 1 ) ( m + 1 ) = Finset.image ( fun k => k + 1 ) ( Finset.Ioc i m ) from ?_, Finset.sum_image <| by intros a ha b hb hab; linarith ] ; aesop;
      · interval_cases m ; norm_num [ DenselyFills ];
        linarith [ h_pos 1 ( by norm_num ) ];
    have h_union : DenselyFills ({s | ∃ t ⊆ Finset.Icc 2 (m + 1), s = ∑ i ∈ t, x i} ∪ {s + x 1 | s ∈ {s | ∃ t ⊆ Finset.Icc 2 (m + 1), s = ∑ i ∈ t, x i}}) 0 (∑ i ∈ Finset.Icc 1 (m + 1), x i) (x (m + 1)) := by
      convert densely_fills_union _ _ _ _ h_ind _ _ using 1;
      · erw [ Finset.Icc_eq_cons_Ioc, Finset.sum_cons, add_comm ] <;> norm_num [ (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
      · exact h_pos 1 <| by norm_num;
      · rcases m with ( _ | m ) <;> aesop;
    convert h_union using 1;
    ext s;
    constructor;
    · rintro ⟨ t, ht, rfl ⟩;
      by_cases h1 : 1 ∈ t;
      · exact Or.inr ⟨ ∑ i ∈ t.erase 1, x i, ⟨ t.erase 1, fun i hi => Finset.mem_Icc.mpr ⟨ Nat.lt_of_le_of_ne ( Finset.mem_Icc.mp ( ht ( Finset.mem_of_mem_erase hi ) ) |>.1 ) ( Ne.symm <| by aesop ), Finset.mem_Icc.mp ( ht ( Finset.mem_of_mem_erase hi ) ) |>.2 ⟩, rfl ⟩, by rw [ Finset.sum_erase_add _ _ h1 ] ⟩;
      · exact Or.inl ⟨ t, fun i hi => Finset.mem_Icc.mpr ⟨ Nat.lt_of_le_of_ne ( Finset.mem_Icc.mp ( ht hi ) |>.1 ) ( Ne.symm <| by rintro rfl; exact h1 hi ), Finset.mem_Icc.mp ( ht hi ) |>.2 ⟩, rfl ⟩;
    · rintro ( ⟨ t, ht, rfl ⟩ | ⟨ s, ⟨ t, ht, rfl ⟩, rfl ⟩ );
      · exact ⟨ t, Finset.Subset.trans ht ( Finset.Icc_subset_Icc ( by norm_num ) le_rfl ), rfl ⟩;
      · use Insert.insert 1 t;
        simp_all +decide [ Finset.subset_iff ];
        exact ⟨ fun a ha => by linarith [ ht ha ], by rw [ Finset.sum_insert ( show 1∉t from fun h => by linarith [ ht h ] ) ] ; ring ⟩

/-
The finite sequence $1/n_0, \dots, 1/n_{m_K}$ satisfies the condition of `lm_reals`.
-/
lemma finite_seq_satisfies_condition (n : ℕ → ℕ) (m : ℕ → ℕ) (K : ℕ)
  (h_m_mono : StrictMono m)
  (h_ineq_0 : ∀ i < m 0, (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i (m 0), (1 : ℝ) / n j) + (1 : ℝ) / n (m 0))
  (h_ineq_k : ∀ k : ℕ, ∀ i, m k ≤ i → i < m (k + 1) →
    (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i (m (k + 1)), (1 : ℝ) / n j) + (1 : ℝ) / n (m (k + 1))) :
  ∀ i < m K, (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i (m K), (1 : ℝ) / n j) + (1 : ℝ) / n (m K) := by
  induction' K with K ih;
  · assumption;
  · intro i hi;
    by_cases hi' : i < m K;
    · refine le_trans ( ih i hi' ) ?_;
      rw [ show ( Finset.Ioc i ( m ( K + 1 ) ) ) = Finset.Ioc i ( m K ) ∪ Finset.Ioc ( m K ) ( m ( K + 1 ) ) from ?_, Finset.sum_union ] <;> norm_num [ h_m_mono.le_iff_le ];
      · have := h_ineq_k K ( m K ) le_rfl ( h_m_mono K.lt_succ_self ) ; norm_num at * ; linarith;
      · rw [ Finset.Ioc_union_Ioc_eq_Ioc ] <;> linarith [ h_m_mono K.lt_succ_self ];
    · exact h_ineq_k K i ( le_of_not_gt hi' ) hi

/-
If a set $S$ of multiples of $\delta$ densely fills $[0, U]$, then it contains all multiples of $\delta$ in $[0, U]$.
-/
lemma dense_and_divisible_implies_all_multiples (S : Set ℝ) (U δ : ℝ)
  (h_dense : DenselyFills S 0 U δ)
  (h_div : ∀ s ∈ S, ∃ k : ℤ, s = k * δ)
  (h_delta_pos : 0 < δ) :
  {x ∈ Set.Icc 0 U | ∃ k : ℤ, x = k * δ} ⊆ S := by
  intro x hx
  obtain ⟨hx_bounds, k, hk⟩ := hx
  obtain ⟨s1, hs1, s2, hs2, hs1_le_x, hx_le_s2, hs2_s1_le_delta⟩ := h_dense.2.2.2 x hx_bounds
  obtain ⟨k₁, rfl⟩ := h_div s1 hs1
  obtain ⟨k₂, rfl⟩ := h_div s2 hs2
  have h_eq : k₁ * δ = x ∨ k₂ * δ = x := by
    rcases lt_trichotomy k₁ k with hk₁ | rfl | hk₁
    · right
      have hcast : (k₁ : ℝ) + 1 ≤ k := by exact_mod_cast hk₁
      nlinarith
    · left
      linarith
    · exfalso
      have hcast : (k : ℝ) + 1 ≤ k₁ := by exact_mod_cast hk₁
      nlinarith
  rcases h_eq with h | h
  · rw [← h]; exact hs1
  · rw [← h]; exact hs2

/-
The finite subset sums contain all multiples of $1/n_{m_K}$ in the range.
-/
lemma finite_subset_sums_contain_multiples (n : ℕ → ℕ) (m : ℕ → ℕ) (K : ℕ)
  (h_n_pos : ∀ i, 0 < n i)
  (h_n_mono : StrictMono n)
  (h_m_mono : StrictMono m)
  (h_div_m : ∀ k : ℕ, ∀ j < m k, n j ∣ n (m k))
  (h_ineq_0 : ∀ i < m 0, (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i (m 0), (1 : ℝ) / n j) + (1 : ℝ) / n (m 0))
  (h_ineq_k : ∀ k : ℕ, ∀ i, m k ≤ i → i < m (k + 1) →
    (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i (m (k + 1)), (1 : ℝ) / n j) + (1 : ℝ) / n (m (k + 1))) :
  let M := m K
  let S := { s | ∃ t ⊆ Finset.range (M + 1), s = ∑ i ∈ t, (1 : ℝ) / n i }
  let U := ∑ i ∈ Finset.range (M + 1), (1 : ℝ) / n i
  let δ := (1 : ℝ) / n M
  {x ∈ Set.Icc 0 U | ∃ k : ℤ, x = k * δ} ⊆ S := by
  intros M S U δ hS
  have h_dense : DenselyFills S 0 U δ := by
    have h_apply_lm_reals : DenselyFills { s | ∃ t ⊆ Finset.Icc 1 (M + 1), s = ∑ i ∈ t, (1 : ℝ) / n (i - 1) } 0 (∑ i ∈ Finset.Icc 1 (M + 1), (1 : ℝ) / n (i - 1)) ((1 : ℝ) / n M) := by
      apply_rules [ lm_reals ];
      · linarith;
      · exact fun i hi => one_div_pos.mpr <| Nat.cast_pos.mpr <| h_n_pos _;
      · intro i hi; gcongr <;> aesop;
      · have h_apply_finite_seq : ∀ i < M, (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i M, (1 : ℝ) / n j) + (1 : ℝ) / n M := by
          apply_rules [ finite_seq_satisfies_condition ];
        have icc_succ : ∀ a b : ℕ, Finset.Icc (a + 1) b = Finset.Ioc a b := fun a b => by
          ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
        intro i hi; rcases i with ( _ | i ) <;> simp_all +decide [Finset.sum_Ioc_succ_top] ;
        have h_apply := h_apply_finite_seq i ( Nat.lt_of_succ_le hi );
        refine le_trans h_apply ?_;
        rw [ Finset.Ioc_eq_cons_Ioo ( by linarith ), Finset.sum_cons ] ; norm_num [ add_comm, add_left_comm, add_assoc ];
        rw [ show ( Finset.Ioc ( i + 1 ) M : Finset ℕ ) = Finset.image ( fun x => x + 1 ) ( Finset.Ioo i M ) from ?_, Finset.sum_image ] <;> norm_num [ add_comm, add_left_comm, Finset.sum_Ioc_succ_top ];
        exact Eq.symm (Finset.Ioo_add_one_right_eq_Ioc (i + 1) M);
    convert h_apply_lm_reals using 1;
    · ext; simp [S, Finset.Icc];
      constructor <;> rintro ⟨ t, ht, rfl ⟩;
      · use t.image (fun i => i + 1);
        simp_all +decide [ Finset.subset_iff ];
        exact fun x hx => Finset.mem_Icc.mpr ⟨ by linarith [ ht hx ], by linarith [ ht hx ] ⟩;
      · use t.image (fun x => x - 1);
        simp_all +decide [ Finset.subset_iff ];
        exact ⟨ fun x hx => (Finset.mem_Icc.mp ( ht hx )).2, by rw [ Finset.sum_image <| by intros a ha b hb hab; linarith [ Nat.sub_add_cancel <| show 1 ≤ a from Finset.mem_Icc.mp ( ht ha ) |>.1, Nat.sub_add_cancel <| show 1 ≤ b from Finset.mem_Icc.mp ( ht hb ) |>.1 ] ] ⟩;
    · erw [ Finset.sum_Ico_eq_sum_range ] ; ac_rfl;
  have h_div : ∀ s ∈ S, ∃ k : ℤ, s = k * δ := by
    intro s hs
    obtain ⟨t, ht_sub, ht_eq⟩ := hs
    have h_div : ∀ i ∈ t, ∃ k : ℤ, (1 / (n i : ℝ)) = k * δ := by
      intro i hi
      have h_div_i : n i ∣ n M := by
        by_cases hiM : i < m K;
        · exact h_div_m K i hiM;
        · rw [ show i = m K from le_antisymm ( Finset.mem_range_succ_iff.mp ( ht_sub hi ) ) ( not_lt.mp hiM ) ]
      obtain ⟨k, hk⟩ := h_div_i
      use k
      field_simp [hk];
      rw [ mul_div, div_eq_div_iff ] <;> norm_cast <;> nlinarith [ h_n_pos i, h_n_pos M ];
    choose! k hk using h_div; exact ⟨ ∑ i ∈ t, k i, by push_cast; rw [ ht_eq, Finset.sum_mul _ _ _ ] ; exact Finset.sum_congr rfl fun i hi => hk i hi ⟩ ;
  exact fun h => dense_and_divisible_implies_all_multiples S U δ h_dense h_div ( by exact one_div_pos.mpr <| Nat.cast_pos.mpr <| h_n_pos _ ) ⟨ h.1, h.2 ⟩

/-
The main proposition, which states that under the given conditions, the set of subset sums of $1/n_i$ is exactly the set of rational numbers in the interval $[0, \sum 1/n_i)$.
-/
lemma prop_general (n : ℕ → ℕ) (m : ℕ → ℕ)
  (h_n_pos : ∀ i, 0 < n i)
  (h_n_mono : StrictMono n)
  (h_m_mono : StrictMono m)
  (h_div : ∀ k > 0, ∃ i, k ∣ n i)
  (h_div_m : ∀ k : ℕ, ∀ j < m k, n j ∣ n (m k))
  (h_ineq_0 : ∀ i < m 0, (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i (m 0), (1 : ℝ) / n j) + (1 : ℝ) / n (m 0))
  (h_ineq_k : ∀ k : ℕ, ∀ i, m k ≤ i → i < m (k + 1) →
    (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i (m (k + 1)), (1 : ℝ) / n j) + (1 : ℝ) / n (m (k + 1))) :
  SubsetSums (fun i => (1 : ℝ) / n i) =
    (TargetInterval (fun i => (1 : ℝ) / n i)) ∩ {x | ∃ q : ℚ, x = q} := by
  apply Set.eq_of_subset_of_subset;
  · unfold TargetInterval SubsetSums;
    by_cases h : Summable ( fun i => ( n i : ℝ ) ⁻¹ ) <;> simp_all +decide [ Set.subset_def ];
    · refine' fun x s hx => ⟨ ⟨ Finset.sum_nonneg fun _ _ => inv_nonneg.2 <| Nat.cast_nonneg _, _ ⟩, ⟨ ∑ i ∈ s, ( n i : ℚ ) ⁻¹, by push_cast; rfl ⟩ ⟩;
      refine' lt_of_lt_of_le _ ( Summable.sum_le_tsum ( s ∪ { s.sup id + 1 } ) ( fun _ _ => inv_nonneg.2 <| Nat.cast_nonneg _ ) h );
      rw [ Finset.sum_union ] <;> norm_num [ h_n_pos ];
      exact fun h => not_lt_of_ge ( Finset.le_sup ( f := id ) h ) ( Nat.lt_succ_self _ );
    · exact fun x t hx => ⟨ Finset.sum_nonneg fun _ _ => inv_nonneg.2 <| Nat.cast_nonneg _, ⟨ ∑ i ∈ t, ( n i : ℚ ) ⁻¹, by push_cast; rfl ⟩ ⟩;
  · intro x hx
    obtain ⟨K1, hK1⟩ : ∃ K1, x ≤ ∑ i ∈ Finset.range (m K1 + 1), (1 : ℝ) / n i := by
      by_cases h_summable : Summable (fun i => (1 : ℝ) / n i);
      · have h_summable : Filter.Tendsto (fun K => ∑ i ∈ Finset.range (m K + 1), (1 : ℝ) / n i) Filter.atTop (nhds (∑' i, (1 : ℝ) / n i)) := by
          exact h_summable.hasSum.tendsto_sum_nat.comp <| Filter.tendsto_atTop_mono ( fun K => Nat.le_succ _ ) <| h_m_mono.tendsto_atTop;
        exact Filter.Eventually.exists ( h_summable.eventually ( le_mem_nhds <| show x < ∑' i : ℕ, 1 / ( n i : ℝ ) from hx.1 |> fun h => by unfold TargetInterval at h; aesop ) ) |> fun ⟨ K, hK ⟩ => ⟨ K, hK ⟩;
      · have h_unbounded : Filter.Tendsto (fun K => ∑ i ∈ Finset.range (m K + 1), (1 : ℝ) / n i) Filter.atTop Filter.atTop := by
          exact not_summable_iff_tendsto_nat_atTop_of_nonneg ( fun _ => by positivity ) |>.1 h_summable |> Filter.Tendsto.comp <| Filter.tendsto_atTop_mono ( fun K => Nat.le_succ _ ) <| h_m_mono.tendsto_atTop;
        exact ( h_unbounded.eventually_ge_atTop x ) |> fun h => h.exists
    obtain ⟨d, hd⟩ : ∃ d : ℕ, d > 0 ∧ ∃ q : ℚ, x = q ∧ q.den = d := by
      exact ⟨ hx.2.choose.den, Nat.cast_pos.mpr hx.2.choose.pos, hx.2.choose, hx.2.choose_spec, rfl ⟩
    obtain ⟨i0, hi0⟩ : ∃ i0, d ∣ n i0 := by
      exact h_div d hd.1 |> fun ⟨ i, hi ⟩ => ⟨ i, hi ⟩
    obtain ⟨K, hK⟩ : ∃ K ≥ K1, m K > i0 := by
      -- Since $m$ is strictly monotone, it is unbounded. Therefore, there exists some $K$ such that $m K > i0$.
      obtain ⟨K, hK⟩ : ∃ K, m K > i0 := by
        exact ⟨ _, h_m_mono.id_le _ ⟩;
      exact ⟨ _, le_max_left _ _, hK.trans_le <| h_m_mono.monotone <| le_max_right _ _ ⟩
    have h_div_mk : d ∣ n (m K) := by
      exact dvd_trans hi0 ( h_div_m K i0 hK.2 )
    have h_q_mult : ∃ k : ℤ, x = k * (1 : ℝ) / n (m K) := by
      obtain ⟨q, hq⟩ : ∃ q : ℚ, x = q ∧ q.den = d := hd.right
      obtain ⟨k, hk⟩ : ∃ k : ℤ, q = k / d := by
        exact ⟨ q.num, by simpa [ hq.2 ] using q.num_div_den.symm ⟩
      use k * (n (m K) / d);
      simp_all +decide [ne_of_gt, mul_assoc, mul_comm, div_eq_mul_inv]
    have h_q_sum : x ∈ { s | ∃ t ⊆ Finset.range (m K + 1), s = ∑ i ∈ t, (1 : ℝ) / n i } := by
      have h_q_sum : {x ∈ Set.Icc 0 (∑ i ∈ Finset.range (m K + 1), (1 : ℝ) / n i) | ∃ k : ℤ, x = k * (1 : ℝ) / n (m K)} ⊆ { s | ∃ t ⊆ Finset.range (m K + 1), s = ∑ i ∈ t, (1 : ℝ) / n i } := by
        convert finite_subset_sums_contain_multiples n m K h_n_pos h_n_mono h_m_mono h_div_m h_ineq_0 h_ineq_k using 1;
        simp +decide only [mul_one_div];
        norm_num;
      apply h_q_sum; exact ⟨⟨by
      unfold TargetInterval at hx; aesop;, by
        exact hK1.trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( by linarith [ h_m_mono.monotone hK.1 ] ) ) fun _ _ _ => by positivity )⟩, h_q_mult⟩;
    exact (by
    exact ⟨ h_q_sum.choose, h_q_sum.choose_spec.2 ⟩)

/-
If $n_{i+1} \le 2n_i$, then $1/n_i \le \sum_{j=i+1}^M 1/n_j + 1/n_M$.
-/
lemma remark_cond (n : ℕ → ℕ) (M : ℕ)
  (h_n_pos : ∀ i, 0 < n i)
  (h_n_growth : ∀ i, n (i + 1) ≤ 2 * n i)
  (i : ℕ) (hi : i < M) :
  (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i M, (1 : ℝ) / n j) + (1 : ℝ) / n M := by
  induction' hi with k hk ih <;> norm_num [ Finset.sum_Ioc_succ_top ] at *;
  · field_simp;
    rw [ div_le_div_iff₀ ] <;> norm_cast <;> linarith [ h_n_pos i, h_n_pos ( i + 1 ), h_n_growth i ];
  · rw [ Finset.sum_Ioc_succ_top ] <;> try linarith;
    linarith [ show ( n k : ℝ ) ⁻¹ ≤ ( n ( k + 1 ) : ℝ ) ⁻¹ + ( n ( k + 1 ) : ℝ ) ⁻¹ by rw [ inv_eq_one_div, inv_eq_one_div, ← add_div, div_le_div_iff₀ ] <;> norm_cast <;> linarith [ h_n_pos k, h_n_pos ( k + 1 ), h_n_growth k ] ]

/-
Any rational number in the target interval is a subset sum.
-/
lemma target_subset_subset_sums (n : ℕ → ℕ) (m : ℕ → ℕ)
  (h_n_pos : ∀ i, 0 < n i)
  (h_n_mono : StrictMono n)
  (h_m_mono : StrictMono m)
  (h_div : ∀ k > 0, ∃ i, k ∣ n i)
  (h_div_m : ∀ k : ℕ, ∀ j < m k, n j ∣ n (m k))
  (h_ineq_0 : ∀ i < m 0, (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i (m 0), (1 : ℝ) / n j) + (1 : ℝ) / n (m 0))
  (h_ineq_k : ∀ k : ℕ, ∀ i, m k ≤ i → i < m (k + 1) →
    (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i (m (k + 1)), (1 : ℝ) / n j) + (1 : ℝ) / n (m (k + 1))) :
  (TargetInterval (fun i => (1 : ℝ) / n i)) ∩ {x | ∃ q : ℚ, x = q} ⊆ SubsetSums (fun i => (1 : ℝ) / n i) := by
  have := prop_general n m h_n_pos h_n_mono h_m_mono h_div h_div_m h_ineq_0 h_ineq_k ; aesop;

/-
If $Q$ is a power of 2, the lemma holds.
-/
lemma lemma_divisors_power_of_two (lambda : ℝ) (Q : ℕ)
  (h_lambda : 1 < lambda ∧ lambda < 2)
  (h_Q_pos : 0 < Q)
  (h_pow2 : ∃ k : ℕ, Q = 2 ^ k) :
  ∃ N : ℕ, Q ∣ N ∧ ∃ d : ℕ → ℕ, ∃ M : ℕ,
    d 0 = 1 ∧ d M = N ∧
    (∀ j ≤ M, d j ∣ N) ∧
    (StrictMonoOn d (Set.Icc 0 M)) ∧
    (∀ j < M, lambda ≤ (d (j + 1) : ℝ) / d j ∧ (d (j + 1) : ℝ) / d j ≤ 2) := by
  obtain ⟨k, rfl⟩ := h_pow2;
  refine' ⟨ _, dvd_rfl, fun j => 2 ^ j, k, _, _, _, _, _ ⟩ <;> norm_num [ StrictMonoOn ];
  · exact fun j hj => pow_dvd_pow _ hj;
  · exact fun a ha b hb hab => pow_lt_pow_right₀ ( by norm_num ) hab;
  · norm_num [ pow_succ' ];
    exact fun _ _ => h_lambda.2.le

/-
If $Q$ is not a power of 2, then $\log_2 Q$ is irrational.
-/
lemma irrational_logb_two_of_not_pow_two (Q : ℕ) (hQ : Q > 0) (h_not_pow2 : ¬ ∃ k : ℕ, Q = 2 ^ k) :
  Irrational (Real.logb 2 Q) := by
    -- Assume for contradiction that $\log_2 Q$ is rational. Then there exist positive integers $p$ and $q$ with $\gcd(p, q) = 1$ such that $\log_2 Q = p/q$.
    by_contra h_contra
    obtain ⟨p, q, hq_pos, hgcd, h_eq⟩ : ∃ p q : ℕ, 0 < q ∧ Nat.gcd p q = 1 ∧ Real.logb 2 Q = p / q := by
      unfold Irrational at h_contra;
      norm_num +zetaDelta at *;
      obtain ⟨ y, hy ⟩ := h_contra; exact ⟨ y.num.natAbs, y.den, Nat.cast_pos.mpr y.pos, y.reduced, by simpa [ abs_of_nonneg ( Rat.num_nonneg.mpr ( show 0 ≤ y by exact_mod_cast hy.symm ▸ Real.logb_nonneg one_lt_two ( Nat.one_le_cast.mpr hQ ) ) ), Rat.cast_def ] using hy.symm ⟩ ;
    -- Then we have $Q^q = 2^p$.
    have h_exp : Q^q = 2^p := by
      rw [ eq_div_iff ( by positivity ) ] at h_eq;
      rw [ ← @Nat.cast_inj ℝ ] ; push_cast ; rw [ ← Real.rpow_natCast _ p, ← h_eq, Real.rpow_mul ] <;> norm_num [ hQ ];
    have : Q ∣ 2 ^ p := h_exp ▸ dvd_pow_self _ hq_pos.ne'; ( erw [ Nat.dvd_prime_pow ( by decide ) ] at this; aesop; )

/-
The fractional parts of natural multiples of an irrational number are dense in $[0, 1]$.
-/
lemma dense_fract_of_irrational (alpha : ℝ) (h_irr : Irrational alpha) :
  ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → ∃ n : ℕ, a < Int.fract (n * alpha) ∧ Int.fract (n * alpha) < b := by
    -- Consider the circle group $S^1 = \mathbb{R}/\mathbb{Z}$, which is `AddCircle 1`.
    set G : Type := AddCircle (1 : ℝ);
    -- The element corresponding to $\alpha$ is $x = \alpha \pmod 1$.
    set x : G := QuotientAddGroup.mk alpha;
    -- Since $\alpha$ is irrational, $\alpha/1$ is irrational.
    have h_alpha_irr : Irrational (alpha / 1) := by
      simpa using h_irr;
    -- By `AddCircle.denseRange_zsmul_coe_iff`, the set $\{n x \mid n \in \mathbb{Z}\}$ is dense in $S^1$.
    have h_dense_z : DenseRange (fun n : ℤ => n • x) := by
      convert AddCircle.denseRange_zsmul_coe_iff.mpr _;
      exact h_alpha_irr;
    -- By `denseRange_zsmul_iff_nsmul`, the set $\{n x \mid n \in \mathbb{N}\}$ is dense in $S^1$.
    have h_dense_n : DenseRange (fun n : ℕ => n • x) := by
      convert denseRange_zsmul_iff_nsmul.mp h_dense_z;
    intro a b ha hb hb1
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (QuotientAddGroup.mk (n * alpha) : G) ∈ Metric.ball (QuotientAddGroup.mk (a + (b - a) / 2)) ((b - a) / 2) := by
      have := h_dense_n.exists_dist_lt ( QuotientAddGroup.mk ( a + ( b - a ) / 2 ) ) ( by linarith : 0 < ( b - a ) / 2 );
      obtain ⟨ n, hn ⟩ := this;
      use n;
      convert hn using 1;
      rw [ dist_comm ] ; aesop;
    erw [ Metric.mem_ball, dist_eq_norm ] at hn;
    erw [ QuotientAddGroup.norm_lt_iff ] at hn;
    obtain ⟨ m, hm₁, hm₂ ⟩ := hn;
    erw [ QuotientAddGroup.eq ] at hm₁;
    obtain ⟨ k, hk ⟩ := hm₁;
    norm_num [ Norm.norm ] at *;
    exact ⟨ n, by linarith [ abs_lt.mp hm₂, Int.fract_add_floor ( ( n : ℝ ) * alpha ), show ( Int.floor ( ( n : ℝ ) * alpha ) : ℝ ) = k by exact_mod_cast Int.floor_eq_iff.mpr ⟨ by linarith [ abs_lt.mp hm₂ ], by linarith [ abs_lt.mp hm₂ ] ⟩ ], by linarith [ abs_lt.mp hm₂, Int.fract_add_floor ( ( n : ℝ ) * alpha ), show ( Int.floor ( ( n : ℝ ) * alpha ) : ℝ ) = k by exact_mod_cast Int.floor_eq_iff.mpr ⟨ by linarith [ abs_lt.mp hm₂ ], by linarith [ abs_lt.mp hm₂ ] ⟩ ] ⟩

/-
If $Q$ is not a power of 2, we can find powers $a, b$ such that $Q^b / 2^a \in [\lambda, 2]$.
-/
lemma exists_powers_in_range (lambda : ℝ) (Q : ℕ)
  (h_lambda : 1 < lambda ∧ lambda < 2)
  (h_Q_pos : 0 < Q)
  (h_not_pow2 : ¬ ∃ k : ℕ, Q = 2 ^ k) :
  ∃ a b : ℕ, lambda ≤ (Q : ℝ) ^ b / 2 ^ a ∧ (Q : ℝ) ^ b / 2 ^ a ≤ 2 := by
    -- By `dense_fract_of_irrational`, there exists $b \in \mathbb{N}$ such that $\{b \alpha\} \in (x, 1)$.
    obtain ⟨b, hb⟩ : ∃ b : ℕ, b > 0 ∧ Int.fract (b * Real.logb 2 Q) ∈ Set.Ioo (Real.logb 2 lambda) 1 := by
      -- By `dense_fract_of_irrational`, since $Q$ is not a power of 2, $\log_2 Q$ is irrational, and the fractional parts of its multiples are dense in $[0, 1]$.
      have h_irr : Irrational (Real.logb 2 Q) := by
        apply irrational_logb_two_of_not_pow_two Q h_Q_pos h_not_pow2
      have h_dense : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → ∃ n : ℕ, a < Int.fract (n * Real.logb 2 Q) ∧ Int.fract (n * Real.logb 2 Q) < b := by
        exact fun a b a_1 a_2 a_3 =>
          dense_fract_of_irrational (Real.logb 2 ↑Q) h_irr a b a_1 a_2 a_3
      have h_exists_b : ∃ b : ℕ, b > 0 ∧ Int.fract (b * Real.logb 2 Q) ∈ Set.Ioo (Real.logb 2 lambda) 1 := by
        obtain ⟨ b, hb₁, hb₂ ⟩ := h_dense ( Real.logb 2 lambda ) 1 ( Real.logb_nonneg ( by norm_num ) ( by linarith ) ) ( by rw [ Real.logb_lt_iff_lt_rpow ] <;> norm_num <;> linarith ) ( by norm_num ) ; exact ⟨ b, Nat.pos_of_ne_zero fun h => by norm_num [ h ] at hb₁ ; linarith [ Real.logb_pos one_lt_two h_lambda.1 ], hb₁, hb₂ ⟩ ;
      exact h_exists_b;
    use ⌊b * Real.logb 2 Q⌋₊, b;
    -- By definition of fractional part, we have $b \log_2 Q = \lfloor b \log_2 Q \rfloor + \{b \log_2 Q\}$.
    have h_frac : b * Real.logb 2 Q = ⌊b * Real.logb 2 Q⌋₊ + Int.fract (b * Real.logb 2 Q) := by
      convert Eq.symm ( Int.floor_add_fract ( ( b : ℝ ) * Real.logb 2 Q ) ) using 1;
      exact congrArg₂ _ ( mod_cast Int.toNat_of_nonneg <| Int.floor_nonneg.2 <| mul_nonneg ( Nat.cast_nonneg _ ) <| Real.logb_nonneg ( by norm_num ) <| Nat.one_le_cast.2 h_Q_pos ) rfl;
    -- Exponentiating both sides of $b \log_2 Q = \lfloor b \log_2 Q \rfloor + \{b \log_2 Q\}$, we get $Q^b = 2^{\lfloor b \log_2 Q \rfloor} \cdot 2^{\{b \log_2 Q\}}$.
    have h_exp : (Q : ℝ) ^ b = 2 ^ ⌊b * Real.logb 2 Q⌋₊ * 2 ^ (Int.fract (b * Real.logb 2 Q)) := by
      rw [ ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add ] <;> norm_num [ h_Q_pos ];
      rw [ ← h_frac, mul_comm, Real.rpow_mul ] <;> norm_num [ h_Q_pos ];
    rw [ h_exp, mul_div_cancel_left₀ _ ( by positivity ) ];
    exact ⟨ by rw [ ← Real.logb_le_iff_le_rpow ( by linarith ) ( by linarith ) ] ; linarith [ hb.2.1 ], by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( by linarith ) hb.2.2.le ) ( by norm_num ) ⟩

/-
For every $\lambda\in(1,2)$ and every $Q\in\mathbb{N}$, there exists a positive integer $N$ divisible by $Q$ and for which some subsequence of its divisors satisfies the lacunary condition.
-/
lemma lm_divisors (lambda : ℝ) (Q : ℕ)
  (h_lambda : 1 < lambda ∧ lambda < 2)
  (h_Q_pos : 0 < Q) :
  ∃ N : ℕ, Q ∣ N ∧ ∃ d : ℕ → ℕ, ∃ M : ℕ,
    d 0 = 1 ∧ d M = N ∧
    (∀ j ≤ M, d j ∣ N) ∧
    (StrictMonoOn d (Set.Icc 0 M)) ∧
    (∀ j < M, lambda ≤ (d (j + 1) : ℝ) / d j ∧ (d (j + 1) : ℝ) / d j ≤ 2) := by
      -- Distinguish two cases: $Q$ is a power of 2 or it is not.
      by_cases h_pow2 : ∃ k : ℕ, Q = 2 ^ k;
      · exact lemma_divisors_power_of_two lambda Q h_lambda h_Q_pos h_pow2;
      · obtain ⟨a, b, h_lambda_le, h_le_two⟩ : ∃ a b : ℕ, lambda ≤ (Q : ℝ) ^ b / 2 ^ a ∧ (Q : ℝ) ^ b / 2 ^ a ≤ 2 := by
          exact exists_powers_in_range lambda Q h_lambda h_Q_pos h_pow2;
        refine' ⟨ 2 ^ a * Q ^ b, _, _ ⟩;
        · rcases b with ( _ | b ) <;> simp_all +decide [ pow_succ', dvd_mul_of_dvd_right ];
          linarith [ inv_le_one_of_one_le₀ ( one_le_pow₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) : ( 1 : ℝ ) ≤ 2 ^ a ) ];
        · refine' ⟨ fun j => if j ≤ a then 2 ^ j else 2 ^ ( j - ( a + 1 ) ) * Q ^ b, a + ( a + 1 ), _, _, _, _, _ ⟩ <;> norm_num [ StrictMonoOn ];
          · intro j hj; split_ifs <;> simp_all +decide ;
            · exact dvd_mul_of_dvd_left ( pow_dvd_pow _ ‹_› ) _;
            · exact mul_dvd_mul ( pow_dvd_pow _ ( Nat.sub_le_of_le_add <| by linarith ) ) dvd_rfl;
          · intro i hi j hj hij; split_ifs <;> try linarith [ pow_lt_pow_right₀ ( by norm_num : ( 1 : ℕ ) < 2 ) hij ] ;
            · refine' lt_of_le_of_lt ( pow_le_pow_right₀ ( by norm_num ) ‹i ≤ a› ) _;
              rw [ le_div_iff₀ ( by positivity ) ] at *;
              exact_mod_cast ( by nlinarith [ pow_pos ( zero_lt_two' ℝ ) a, pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( show j - ( a + 1 ) ≥ 0 by norm_num ), pow_pos ( show 0 < ( Q : ℝ ) by positivity ) b ] : ( 2 : ℝ ) ^ a < 2 ^ ( j - ( a + 1 ) ) * Q ^ b );
            · exact mul_lt_mul_of_pos_right ( pow_lt_pow_right₀ ( by norm_num ) ( by omega ) ) ( pow_pos h_Q_pos _ );
          · intro j hj; split_ifs <;> norm_num [ pow_succ', mul_assoc, mul_div_mul_left ] at *;
            · linarith;
            · linarith;
            · norm_num [ show j = a by linarith ] at * ; aesop;
            · simp_all +decide [ Nat.succ_sub ( by linarith : a + 1 ≤ j ), mul_div_mul_right, ne_of_gt ( pow_pos ( by positivity : 0 < ( Q : ℝ ) ) _ ) ];
              norm_num [ pow_succ', div_eq_mul_inv ];
              linarith

/-
Definition of $\lambda_k = \max(\lambda, 2 - 1/(k+1))$.
-/
def lambda_seq (lambda : ℝ) (k : ℕ) : ℝ := max lambda (2 - 1 / (k + 1))

/-
Definition of $Q_k$ as the product of the first $k$ primes.
-/
def Q_seq (k : ℕ) : ℕ := ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

/-
Bounds for $\lambda_k$.
-/
lemma lambda_seq_bounds (lambda : ℝ) (h : 1 < lambda ∧ lambda < 2) (k : ℕ) :
  1 < lambda_seq lambda k ∧ lambda_seq lambda k < 2 := by
    exact ⟨ lt_max_of_lt_left h.1, max_lt h.2 ( by linarith [ div_pos zero_lt_one ( by linarith : 0 < ( k : ℝ ) + 1 ) ] ) ⟩

/-
$Q_k$ is positive.
-/
lemma Q_seq_pos (k : ℕ) (_hk : k ≥ 1) : 0 < Q_seq k := by
  exact Finset.prod_pos fun i hi => Nat.Prime.pos <| by aesop;

/-
Definitions of $N_k, d_k, M_k$ using `Classical.choose`.
-/
noncomputable def step_data (lambda : ℝ) (k : ℕ) : ℕ × (ℕ → ℕ) × ℕ :=
  let l := lambda_seq lambda k
  let Q := Q_seq k
  if h : 1 < l ∧ l < 2 ∧ 0 < Q then
    let ex := lm_divisors l Q ⟨h.1, h.2.1⟩ h.2.2
    let N := Classical.choose ex
    let spec_N := Classical.choose_spec ex
    let ex_d := spec_N.2
    let d := Classical.choose ex_d
    let spec_d := Classical.choose_spec ex_d
    let M := Classical.choose spec_d
    (N, d, M)
  else
    (1, fun _ => 1, 1)

noncomputable def N_at (lambda : ℝ) (k : ℕ) := (step_data lambda k).1
noncomputable def d_at (lambda : ℝ) (k : ℕ) := (step_data lambda k).2.1
noncomputable def M_at (lambda : ℝ) (k : ℕ) := (step_data lambda k).2.2

/-
Properties of $N_k, d_k, M_k$.
-/
lemma step_data_props (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (k : ℕ) :
  let N := N_at lambda k
  let d := d_at lambda k
  let M := M_at lambda k
  let l := lambda_seq lambda k
  let Q := Q_seq k
  Q ∣ N ∧
  d 0 = 1 ∧ d M = N ∧
  (∀ j ≤ M, d j ∣ N) ∧
  (StrictMonoOn d (Set.Icc 0 M)) ∧
  (∀ j < M, l ≤ (d (j + 1) : ℝ) / d j ∧ (d (j + 1) : ℝ) / d j ≤ 2) := by
    convert Classical.choose_spec ( lm_divisors ( lambda_seq lambda k ) ( Q_seq k ) ?_ ?_ ) using 1;
    any_goals exact lambda_seq_bounds _ h_lambda _;
    field_simp;
    any_goals exact Finset.prod_pos fun i hi => Nat.Prime.pos ( by simp );
    · unfold N_at;
      unfold step_data;
      simp +zetaDelta at *;
      split_ifs <;> simp_all +decide [lambda_seq_bounds];
      exact absurd ‹Q_seq k = 0› ( ne_of_gt ( Q_seq_pos k ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num [ Q_seq ] at * ) ) ) );
    · constructor <;> intro h;
      · convert Classical.choose_spec ( Classical.choose_spec ( lm_divisors ( lambda_seq lambda k ) ( Q_seq k ) ( lambda_seq_bounds _ h_lambda _ ) ( Finset.prod_pos fun i hi => Nat.Prime.pos ( by simp ) ) ) |> And.right ) using 1;
        constructor <;> rintro ⟨ M, hM ⟩;
        · convert Classical.choose_spec ( Classical.choose_spec ( lm_divisors ( lambda_seq lambda k ) ( Q_seq k ) ( lambda_seq_bounds _ h_lambda _ ) ( Finset.prod_pos fun i hi => Nat.Prime.pos ( by simp ) ) ) |> And.right ) using 1;
        · exact ⟨ _, _, hM ⟩;
      · convert Classical.choose_spec ( Classical.choose_spec h ) using 1;
        · unfold d_at;
          unfold step_data;
          simp +zetaDelta at *;
          split_ifs <;> simp_all +decide [ lambda_seq_bounds ];
          · congr! 2;
            ext; simp [exists_and_left];
          · exact absurd ‹_› ( ne_of_gt ( Q_seq_pos k ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num [ Q_seq ] at * ) ) ) );
        · simp +decide [ N_at, d_at, M_at, step_data ];
          split_ifs <;> simp +decide [ * ];
          · congr!;
            all_goals simp +decide [exists_and_left] ;
          · exact False.elim <| ‹¬ ( 1 < lambda_seq lambda k ∧ lambda_seq lambda k < 2 ∧ 0 < Q_seq k ) › ⟨ lambda_seq_bounds _ h_lambda _ |>.1, lambda_seq_bounds _ h_lambda _ |>.2, Q_seq_pos _ <| Nat.pos_of_ne_zero <| by rintro rfl; exact absurd ‹¬ ( 1 < lambda_seq lambda 0 ∧ lambda_seq lambda 0 < 2 ∧ 0 < Q_seq 0 ) › <| by norm_num [ lambda_seq, Q_seq ] ; constructor <;> linarith ⟩

/-
$M_k$ is positive for $k \ge 1$.
-/
lemma M_at_pos (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (k : ℕ) (hk : k ≥ 1) :
  0 < M_at lambda k := by
    apply Nat.pos_of_ne_zero
    intro h_contra
    have h_eq : d_at lambda k 0 = d_at lambda k (M_at lambda k) := by
      rw [h_contra]
    have h_contra : 1 = N_at lambda k := by
      have := step_data_props lambda h_lambda k; aesop;
    have h_contra' : 2 ≤ N_at lambda k := by
      have := step_data_props lambda h_lambda k; norm_num at *; (
      exact absurd ( this.1 ) ( by rw [ ← h_contra ] ; exact Nat.not_dvd_of_pos_of_lt ( by positivity ) ( by exact lt_of_lt_of_le ( by norm_num [ Q_seq ] ) ( show Q_seq k ≥ 2 from Nat.le_trans ( by norm_num [ Q_seq ] ) ( Finset.prod_le_prod_of_subset_of_one_le' ( Finset.range_mono hk ) fun _ _ _ => Nat.Prime.pos ( by aesop ) ) ) ) ) ;);
    linarith [h_contra, h_contra']

/-
Definition of $m_k$ and its monotonicity.
-/
noncomputable def m_seq (lambda : ℝ) : ℕ → ℕ
| 0 => 1
| 1 => 2
| (k + 2) => m_seq lambda (k + 1) + M_at lambda (k + 2)

lemma m_seq_zero (lambda : ℝ) : m_seq lambda 0 = 1 := by rfl
lemma m_seq_one (lambda : ℝ) : m_seq lambda 1 = 2 := by rfl
lemma m_seq_succ (lambda : ℝ) (k : ℕ) : m_seq lambda (k + 2) = m_seq lambda (k + 1) + M_at lambda (k + 2) := by rfl

lemma m_seq_strictMono (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  StrictMono (m_seq lambda) := by
    refine' strictMono_nat_of_lt_succ _;
    intro n;
    induction n <;> simp_all +decide [ m_seq ];
    exact M_at_pos _ h_lambda _ ( Nat.le_add_left _ _ )

/-
$m_k \ge k$ for all $k$.
-/
lemma m_seq_ge_k (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (k : ℕ) :
  m_seq lambda k ≥ k := by
    induction' k with k ih <;> norm_num [ *, m_seq_one ];
    induction' k with k ih <;> norm_num [ *, m_seq_zero, m_seq_one ];
    linarith! [ m_seq_succ lambda k, M_at_pos lambda h_lambda ( k + 2 ) ( by linarith ) ]

/-
Definition of `k_of_index` and its specification.
-/
noncomputable def k_of_index (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (i : ℕ) : ℕ :=
  let P := fun k => m_seq lambda k ≥ i
  have h : ∃ k, P k := ⟨i, m_seq_ge_k lambda h_lambda i⟩
  have : DecidablePred P := Classical.decPred P
  Nat.find h

lemma k_of_index_spec (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (i : ℕ) :
  let k := k_of_index lambda h_lambda i
  m_seq lambda k ≥ i ∧ ∀ j < k, m_seq lambda j < i := by
    -- By definition of $k_of_index$, we know that $m_seq \lambda k \geq i$ and for all $j < k$, $m_seq \lambda j < i$. This follows directly from the properties of the \\Classical eks' function.
    unfold k_of_index;
    simp +zetaDelta at *;
    grind

/-
`k_of_index` is positive for $i > 1$.
-/
lemma k_of_index_pos (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (i : ℕ) (hi : i > 1) :
  k_of_index lambda h_lambda i ≥ 1 := by
    -- Assume that `k_of_index ... < 1`. Then `k_of_index ... = 0`.
    by_contra h_contra
    have h_zero : k_of_index lambda h_lambda i = 0 := by
      linarith;
    -- By definition of `k_of_index`, we have `m_seq lambda 0 ≥ i`.
    have h_m_seq_zero : (m_seq lambda 0) ≥ i := by
      exact h_zero ▸ k_of_index_spec _ _ _ |>.1;
    linarith [ show m_seq lambda 0 = 1 from m_seq_zero _ ]

/-
Definition of `n_seq`.
-/
noncomputable def n_seq (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (n : ℕ) : ℕ :=
  if _h : n < 2 then 1
  else
    let k := k_of_index lambda h_lambda n
    let prev_m := m_seq lambda (k - 1)
    let j := n - prev_m
    let d := d_at lambda k j
    d * n_seq lambda h_lambda prev_m
termination_by n
decreasing_by
  have _hn : n ≥ 2 := by linarith
  have hk : k_of_index lambda h_lambda n ≥ 1 := k_of_index_pos lambda h_lambda n (by linarith)
  let k := k_of_index lambda h_lambda n
  have h_spec := k_of_index_spec lambda h_lambda n
  have h_lt := h_spec.2 (k - 1) (by omega)
  exact h_lt

/-
$n_i > 0$ for all $i$.
-/
lemma n_seq_pos (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (n : ℕ) :
  0 < n_seq lambda h_lambda n := by
    induction' n using Nat.strong_induction_on with n ih;
    unfold n_seq; split_ifs <;> simp_all +decide;
    refine' ⟨ _, ih _ _ ⟩;
    · have := step_data_props lambda h_lambda ( k_of_index lambda h_lambda n );
      refine' Nat.pos_of_dvd_of_pos ( this.2.2.2.1 _ _ ) _;
      · have := k_of_index_spec lambda h_lambda n;
        rcases k : k_of_index lambda h_lambda n with ( _ | _ | k ) <;> simp_all +decide [ m_seq ];
        · linarith [ show M_at lambda 1 ≥ 1 from M_at_pos lambda h_lambda 1 ( by norm_num ) ];
        · linarith;
      · refine' Nat.pos_of_ne_zero _;
        intro h; have := this.2.2.1; simp_all +decide ;
        have := ‹d_at lambda ( k_of_index lambda h_lambda n ) 0 = 1 ∧ StrictMonoOn ( d_at lambda ( k_of_index lambda h_lambda n ) ) ( Icc 0 ( M_at lambda ( k_of_index lambda h_lambda n ) ) ) ∧ ∀ j < M_at lambda ( k_of_index lambda h_lambda n ), _›.2.1 ( show 0 ∈ Icc 0 ( M_at lambda ( k_of_index lambda h_lambda n ) ) from ⟨ by norm_num, Nat.zero_le _ ⟩ ) ( show M_at lambda ( k_of_index lambda h_lambda n ) ∈ Icc 0 ( M_at lambda ( k_of_index lambda h_lambda n ) ) from ⟨ Nat.zero_le _, le_rfl ⟩ ) ; aesop;
    · exact k_of_index_spec lambda h_lambda n |>.2 _ ( Nat.pred_lt ( ne_bot_of_gt ( k_of_index_pos lambda h_lambda n ‹_› ) ) )

/-
$m_k - m_{k-1} \le M_k$.
-/
lemma m_seq_diff_le_M (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (k : ℕ) (hk : k ≥ 1) :
  m_seq lambda k - m_seq lambda (k - 1) ≤ M_at lambda k := by
    rcases k with ( _ | _ | k ) <;> simp_all +decide [ m_seq_succ ];
    rw [ show m_seq lambda 1 = 2 by exact m_seq_one _, show m_seq lambda 0 = 1 by exact m_seq_zero _ ] ; linarith [ show M_at lambda 1 ≥ 1 from M_at_pos _ h_lambda 1 le_rfl ] ;

/-
The ratio $n_{i+1}/n_i$ is bounded by $\lambda_k$ and 2.
-/
lemma n_seq_ratio_properties (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (i : ℕ) (hi : i ≥ 1) :
  let k := k_of_index lambda h_lambda (i + 1)
  let l := lambda_seq lambda k
  l ≤ (n_seq lambda h_lambda (i + 1) : ℝ) / n_seq lambda h_lambda i ∧
  (n_seq lambda h_lambda (i + 1) : ℝ) / n_seq lambda h_lambda i ≤ 2 := by
    -- Let $k = k\_of\_index(i+1)$.
    set k := k_of_index lambda h_lambda (i + 1);
    -- So $m_{k-1} < i+1 \le m_k$.
    have h_mk : m_seq lambda (k - 1) < i + 1 ∧ i + 1 ≤ m_seq lambda k := by
      exact ⟨ k_of_index_spec _ _ _ |>.2 _ ( Nat.sub_lt ( Nat.pos_of_ne_zero ( by
        exact Nat.ne_of_gt ( k_of_index_pos _ _ _ ( by linarith ) ) ) ) zero_lt_one ), k_of_index_spec _ _ _ |>.1 ⟩;
    -- Case 1: $i+1$ is not a boundary, i.e., $m_{k-1} < i < i+1 \le m_k$.
    by_cases h_boundary : i = m_seq lambda (k - 1);
    · -- Since $i = m_{k-1}$, we have $n_{i+1} = d^{(k)}_1 n_{m_{k-1}}$.
      have h_n_i_plus_1 : n_seq lambda h_lambda (i + 1) = d_at lambda k 1 * n_seq lambda h_lambda (m_seq lambda (k - 1)) := by
        rw [ n_seq ];
        grind +ring;
      -- By `step_data_props`, we know that $d^{(k)}_1$ is in $[\lambda_k, 2]$.
      have h_d_k1 : lambda_seq lambda k ≤ (d_at lambda k 1 : ℝ) ∧ (d_at lambda k 1 : ℝ) ≤ 2 := by
        have := step_data_props lambda h_lambda k;
        have := this.2.2.2.2.2 0 ( Nat.pos_of_ne_zero ?_ ) <;> norm_num at *;
        · norm_num [ ‹Q_seq k ∣ N_at lambda k ∧ d_at lambda k 0 = 1 ∧ d_at lambda k ( M_at lambda k ) = N_at lambda k ∧ ( ∀ j ≤ M_at lambda k, d_at lambda k j ∣ N_at lambda k ) ∧ StrictMonoOn ( d_at lambda k ) ( Icc 0 ( M_at lambda k ) ) ∧ ∀ j < M_at lambda k, lambda_seq lambda k ≤ ( d_at lambda k ( j + 1 ) : ℝ ) / ( d_at lambda k j : ℝ ) ∧ ( d_at lambda k ( j + 1 ) : ℝ ) / ( d_at lambda k j : ℝ ) ≤ 2›.2.1 ] at this ⊢ ; exact ⟨ this.1, by exact_mod_cast this.2 ⟩ ;
        · linarith [ M_at_pos lambda h_lambda k ( Nat.pos_of_ne_zero ( by rintro h; norm_num [ h ] at * ; linarith ) ) ];
      simp_all +decide [ ne_of_gt ( n_seq_pos _ _ _ ) ];
    · -- Since $i \neq m_{k-1}$, we have $k\_of\_index(i) = k$.
      have h_k_eq : k_of_index lambda h_lambda i = k := by
        have h_k_eq : ∀ j < k, m_seq lambda j < i := by
          intros j hj_lt_k
          have h_j_lt_i : m_seq lambda j < i + 1 := by
            exact lt_of_le_of_lt ( m_seq_strictMono _ h_lambda |> StrictMono.monotone <| Nat.le_sub_one_of_lt hj_lt_k ) h_mk.1
          have h_j_lt_i' : m_seq lambda j < i := by
            exact lt_of_le_of_ne ( Nat.le_of_lt_succ h_j_lt_i ) ( Ne.symm <| by rintro h; exact h_boundary <| by linarith [ show m_seq lambda j ≤ m_seq lambda ( k - 1 ) from by exact monotone_nat_of_le_succ ( fun n => by exact m_seq_strictMono _ h_lambda |> StrictMono.monotone |> fun h => h ( Nat.le_succ _ ) ) ( Nat.le_sub_one_of_lt hj_lt_k ) ] )
          exact h_j_lt_i';
        refine' le_antisymm _ _ <;> contrapose! h_k_eq;
        · exact absurd ( k_of_index_spec lambda h_lambda i |>.2 _ h_k_eq ) ( by linarith );
        · exact ⟨ k_of_index lambda h_lambda i, h_k_eq, k_of_index_spec lambda h_lambda i |>.1 ⟩;
      -- By definition of $n_seq$, we have $n_{i+1} = d^{(k)}_{i+1-m_{k-1}} n_{m_{k-1}}$ and $n_i = d^{(k)}_{i-m_{k-1}} n_{m_{k-1}}$.
      have h_n_seq_def : n_seq lambda h_lambda (i + 1) = d_at lambda k (i + 1 - m_seq lambda (k - 1)) * n_seq lambda h_lambda (m_seq lambda (k - 1)) ∧ n_seq lambda h_lambda i = d_at lambda k (i - m_seq lambda (k - 1)) * n_seq lambda h_lambda (m_seq lambda (k - 1)) := by
        constructor <;> rw [ n_seq ] <;> simp +decide [h_k_eq];
        · grind;
        · intro hi'; interval_cases i ; simp_all +decide ;
          rcases k with ( _ | _ | k ) <;> simp_all +decide [ m_seq ];
          linarith [ show m_seq lambda ( k + 1 ) ≥ 2 from Nat.recOn k ( by linarith! [ m_seq_zero lambda, m_seq_one lambda ] ) fun n ihn => by linarith! [ m_seq_succ lambda n, M_at_pos lambda h_lambda ( n + 2 ) ( by linarith ) ] ];
      -- By definition of $d_at$, we know that $d^{(k)}_{j+1}/d^{(k)}_j \in [\lambda_k, 2]$ for all $j < M_k$.
      have h_d_at_ratio : ∀ j < M_at lambda k, lambda_seq lambda k ≤ (d_at lambda k (j + 1) : ℝ) / (d_at lambda k j) ∧ (d_at lambda k (j + 1) : ℝ) / (d_at lambda k j) ≤ 2 := by
        exact step_data_props lambda h_lambda k |>.2.2.2.2.2;
      have h_j_lt_M : i - m_seq lambda (k - 1) < M_at lambda k := by
        have h_j_lt_M : m_seq lambda k - m_seq lambda (k - 1) ≤ M_at lambda k := by
          apply m_seq_diff_le_M;
          · tauto;
          · exact Nat.pos_of_ne_zero ( by rintro h; simp_all +decide [ m_seq ] );
        omega;
      simp_all +decide [ Nat.sub_add_comm ( show m_seq lambda ( k - 1 ) ≤ i from Nat.le_of_lt_succ h_mk.1 ) ];
      convert h_d_at_ratio ( i - m_seq lambda ( k - 1 ) ) h_j_lt_M using 1 <;> rw [ mul_div_mul_right _ _ <| Nat.cast_ne_zero.mpr <| ne_of_gt <| n_seq_pos _ _ _ ]

/-
$\lambda_k \to 2$.
-/
lemma lambda_seq_tendsto (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  Filter.Tendsto (lambda_seq lambda) Filter.atTop (nhds 2) := by
    have h_two_minus_one_div : Filter.Tendsto (fun k => 2 - 1 / (k + 1 : ℝ)) Filter.atTop (nhds 2) := by
      exact le_trans ( tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <| Filter.tendsto_id.atTop_add tendsto_const_nhds ) <| by norm_num;
    convert h_two_minus_one_div.comp tendsto_natCast_atTop_atTop |> Filter.Tendsto.max ( tendsto_const_nhds ) using 1 ; norm_num [ lambda_seq ];
    linarith

/-
Formula for `n_seq` within a step.
-/
lemma n_seq_formula (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (k : ℕ) (i : ℕ)
  (hk : k ≥ 1) (hi_lower : m_seq lambda (k - 1) ≤ i) (hi_upper : i ≤ m_seq lambda k) :
  n_seq lambda h_lambda i = d_at lambda k (i - m_seq lambda (k - 1)) * n_seq lambda h_lambda (m_seq lambda (k - 1)) := by
    rcases eq_or_lt_of_le hi_lower with ( rfl | hi_lower );
    · have := step_data_props lambda h_lambda k; aesop;
    · have h_k_of_index : k_of_index lambda h_lambda i = k := by
        refine' le_antisymm _ _ <;> contrapose! hi_lower;
        · -- Since $k < k_of_index lambda h_lambda i$, we have $m_seq lambda k < i$ by the definition of $k_of_index$.
          have h_m_seq_lt_i : m_seq lambda k < i := by
            exact k_of_index_spec _ _ _ |>.2 _ hi_lower;
          linarith;
        · have := k_of_index_spec lambda h_lambda i;
          exact this.1.trans ( m_seq_strictMono _ h_lambda |> StrictMono.monotone <| Nat.le_pred_of_lt hi_lower );
      rw [ n_seq ];
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ m_seq ];
      · have hmk_gt : 1 < m_seq lambda (k + 1) := by
          have := m_seq_strictMono lambda h_lambda (show 0 < k + 1 by omega)
          simpa [m_seq_zero] using this
        omega

/-
Definition of `final_n` and its positivity.
-/
noncomputable def final_n (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (i : ℕ) : ℕ :=
  n_seq lambda h_lambda (i + 1)

lemma final_n_pos (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (i : ℕ) :
  0 < final_n lambda h_lambda i := by
    convert n_seq_pos _ _ _ using 1

/-
`final_n` is $\lambda$-lacunary.
-/
lemma final_n_is_lacunary (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  IsLambdaLacunary lambda (fun i => final_n lambda h_lambda i) := by
    intro i;
    have := n_seq_ratio_properties lambda h_lambda ( i + 1 ) ( by linarith );
    unfold lambda_seq at this; aesop;

/-
`k_of_index` tends to infinity.
-/
lemma k_of_index_tendsto_atTop (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  Filter.Tendsto (k_of_index lambda h_lambda) Filter.atTop Filter.atTop := by
    refine' Filter.tendsto_atTop_atTop.mpr _;
    -- Let $b$ be any natural number. We need to find an $i$ such that for all $a \geq i$, $b \leq k\_of\_index(a)$.
    intro b
    use m_seq lambda b + 1
    intro a ha
    have h_k_of_index : b ≤ k_of_index lambda h_lambda a := by
      contrapose! ha;
      have := k_of_index_spec lambda h_lambda a;
      exact Nat.lt_succ_of_le ( this.1.trans ( by exact monotone_nat_of_le_succ ( fun n => by linarith [ m_seq_strictMono lambda h_lambda |> StrictMono.monotone <| Nat.le_succ n ] ) ha.le ) )
    exact h_k_of_index

/-
The ratio of `final_n` tends to 2.
-/
lemma final_n_ratio_tendsto (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  Filter.Tendsto (fun i => (final_n lambda h_lambda (i + 1) : ℝ) / final_n lambda h_lambda i) Filter.atTop (nhds 2) := by
    -- By `n_seq_ratio_properties` (applied to $i+1 \ge 1$), $\lambda_{k_i} \le r_i \le 2$, where $k_i = k\_of\_index(i+2)$.
    have h_bound : Filter.Tendsto (fun i => lambda_seq lambda (k_of_index lambda h_lambda (i + 2))) Filter.atTop (nhds 2) := by
      refine' lambda_seq_tendsto _ h_lambda |> Filter.Tendsto.comp <| k_of_index_tendsto_atTop _ h_lambda |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 2;
    refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' h_bound tendsto_const_nhds _ _;
    · refine' Filter.Eventually.of_forall fun i => _;
      have := n_seq_ratio_properties ( lambda := lambda ) ( h_lambda := h_lambda ) ( i + 1 ) ( by linarith ) ; aesop;
    · refine' Filter.Eventually.of_forall _;
      intro i; have := n_seq_ratio_properties lambda h_lambda ( i + 1 ) ( by linarith ) ; aesop;

/-
Definition of `final_m` and its strict monotonicity.
-/
noncomputable def final_m (lambda : ℝ) (k : ℕ) : ℕ :=
  m_seq lambda (k + 1) - 1

lemma final_m_strictMono (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  StrictMono (final_m lambda) := by
  intro a b h
  dsimp [final_m]
  have h_mono := m_seq_strictMono lambda h_lambda
  have h_lt := h_mono (Nat.succ_lt_succ h)
  have h_ge : m_seq lambda (a + 1) ≥ 1 := by
    calc m_seq lambda (a + 1) ≥ a + 1 := m_seq_ge_k lambda h_lambda (a + 1)
         _ ≥ 1 := Nat.succ_le_succ (Nat.zero_le a)
  exact Nat.pred_lt_pred (Nat.ne_of_gt h_ge) h_lt

/-
$n_i \le 2^i$.
-/
lemma final_n_le_two_pow (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (i : ℕ) :
  final_n lambda h_lambda i ≤ 2 ^ i := by
    induction' i with i ih;
    · unfold final_n n_seq; aesop;
    · -- By definition of `final_n`, we have `final_n (i + 1) = n_seq (i + 2)`.
      unfold final_n;
      -- By definition of `n_seq`, we have `n_seq (i + 2) ≤ 2 * n_seq (i + 1)`.
      have h_n_seq_le : (n_seq lambda h_lambda (i + 2) : ℝ) ≤ 2 * (n_seq lambda h_lambda (i + 1) : ℝ) := by
        convert n_seq_ratio_properties lambda h_lambda ( i + 1 ) ( by linarith ) |> And.right |> fun x => mul_le_mul_of_nonneg_right x ( Nat.cast_nonneg ( n_seq lambda h_lambda ( i + 1 ) ) ) using 1 ; ring_nf! ; norm_num [ ne_of_gt ( n_seq_pos _ _ _ ) ] ;
      rw [ pow_succ' ] ; norm_cast at * ; linarith! [ show final_n lambda h_lambda i = n_seq lambda h_lambda ( i + 1 ) from rfl ] ;

/-
$n_{m_k}$ divides $n_{m_{k+1}}$.
-/
lemma n_seq_div_prev_m_seq (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (k : ℕ) :
  n_seq lambda h_lambda (m_seq lambda k) ∣ n_seq lambda h_lambda (m_seq lambda (k + 1)) := by
    -- Apply the formula for `n_seq` within a step.
    have h_formula : n_seq lambda h_lambda (m_seq lambda (k + 1)) = d_at lambda (k + 1) (m_seq lambda (k + 1) - m_seq lambda k) * n_seq lambda h_lambda (m_seq lambda k) := by
      apply n_seq_formula;
      · linarith;
      · exact m_seq_strictMono _ ⟨ h_lambda.1, h_lambda.2 ⟩ |> StrictMono.monotone <| Nat.le_succ _;
      · rfl;
    exact h_formula.symm ▸ dvd_mul_left _ _


/-
The sequence `final_n` is strictly increasing.
-/
lemma final_n_strictMono (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  StrictMono (final_n lambda h_lambda) := by
    -- By definition of `final_n`, we know that `final_n i = n_seq (i + 1)`.
    unfold final_n;
    -- By definition of `final_n`, we know that `final_n i = n_seq (i + 1)`. We need to show that this sequence is strictly increasing.
    have h_final_inc : ∀ i, n_seq lambda h_lambda (i + 1) < n_seq lambda h_lambda (i + 2) := by
      intro i
      have h_ratio : (n_seq lambda h_lambda (i + 2) : ℝ) / (n_seq lambda h_lambda (i + 1) : ℝ) > 1 := by
        have := n_seq_ratio_properties lambda h_lambda ( i + 1 ) ( by linarith );
        exact lt_of_lt_of_le ( lt_max_of_lt_left h_lambda.1 ) this.1;
      exact_mod_cast ( by rw [ gt_iff_lt, lt_div_iff₀ ( Nat.cast_pos.mpr ( n_seq_pos _ _ _ ) ) ] at h_ratio; linarith : ( n_seq lambda h_lambda ( i + 1 ) : ℝ ) < n_seq lambda h_lambda ( i + 2 ) );
    exact strictMono_nat_of_lt_succ h_final_inc

/-
For every $k$, the term $n_{m_k}$ is divisible by all preceding terms $n_j$.
-/
lemma final_n_div_m (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (k : ℕ) :
  ∀ j < final_m lambda k, final_n lambda h_lambda j ∣ final_n lambda h_lambda (final_m lambda k) := by
    intro j hj;
    -- By Lemma 3, $n_{m_k}$ is divisible by all preceding terms $n_j$ for $j < m_k$.
    have h_div : ∀ k j, j < m_seq lambda (k + 1) → n_seq lambda h_lambda j ∣ n_seq lambda h_lambda (m_seq lambda (k + 1)) := by
      intros k j hj
      induction' k with k ih generalizing j;
      · rcases j with ( _ | _ | j ) <;> simp_all +arith +decide [ m_seq ];
        · unfold n_seq; aesop;
        · unfold n_seq; aesop;
      · by_cases hj' : j < m_seq lambda (k + 1);
        · exact dvd_trans ( ih j hj' ) ( n_seq_div_prev_m_seq _ _ _ );
        · -- Since $j \geq m_seq lambda (k + 1)$, we can write $j = m_seq lambda (k + 1) + t$ for some $t$.
          obtain ⟨t, ht⟩ : ∃ t, j = m_seq lambda (k + 1) + t := by
            exact Nat.exists_eq_add_of_le <| le_of_not_gt hj';
          -- By definition of `n_seq`, we have `n_seq lambda h_lambda (m_seq lambda (k + 1) + t) = d_at lambda (k + 2) t * n_seq lambda h_lambda (m_seq lambda (k + 1))`.
          have h_n_seq_def : n_seq lambda h_lambda (m_seq lambda (k + 1) + t) = d_at lambda (k + 2) t * n_seq lambda h_lambda (m_seq lambda (k + 1)) := by
            convert n_seq_formula _ _ _ _ _ _ _ using 1 <;> norm_num [ ht ];
            rotate_left;
            exact k + 2;
            · linarith;
            · exact Nat.le_add_right _ _;
            · linarith;
            · norm_num [ Nat.add_sub_cancel_left ];
          have h_n_seq_def' : n_seq lambda h_lambda (m_seq lambda (k + 2)) = d_at lambda (k + 2) (M_at lambda (k + 2)) * n_seq lambda h_lambda (m_seq lambda (k + 1)) := by
            convert n_seq_formula lambda h_lambda ( k + 2 ) ( m_seq lambda ( k + 2 ) ) ( by linarith ) ( by
              exact m_seq_strictMono _ h_lambda |> StrictMono.monotone <| Nat.le_succ _ ) ( by
              norm_num +zetaDelta at * ) using 1
            generalize_proofs at *; (
            simp +decide [ m_seq_succ ]);
          have := step_data_props lambda h_lambda (k + 2);
          simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
          exact Nat.mod_eq_zero_of_dvd ( mul_dvd_mul ( Nat.dvd_of_mod_eq_zero ( this.2.2.2.1 t ( by linarith [ show t < M_at lambda ( k + 2 ) from by linarith [ show m_seq lambda ( k + 2 ) = m_seq lambda ( k + 1 ) + M_at lambda ( k + 2 ) from m_seq_succ _ _ ] ] ) ) ) ( dvd_refl _ ) );
    unfold final_n
    generalize_proofs at *; (
    unfold final_m; (
    rw [ Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr <| by
      exact ne_of_gt <| Nat.recOn k ( by linarith! [ m_seq_one lambda ] ) fun n ihn => by linarith! [ m_seq_succ lambda n, M_at_pos lambda h_lambda ( n + 2 ) ( by linarith ) ] ; ) ] ; exact h_div k _ <| by
      exact Nat.add_lt_of_lt_sub hj))

/-
The product of `Q_seq`s divides `final_n`.
-/
def super_Q (k : ℕ) : ℕ := ∏ j ∈ Finset.range k, Q_seq (j + 1)

lemma super_Q_dvd_final_n (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (k : ℕ) :
  super_Q k ∣ final_n lambda h_lambda (final_m lambda (k - 1)) := by
    rcases k with ( _ | k ) <;> simp_all +decide [ super_Q, final_n ];
    -- By definition of `n_seq`, we know that `n_seq lambda h_lambda (m_seq lambda (k + 1))` is divisible by `∏ j ∈ Finset.range (k + 1), Q_seq (j + 1)`.
    have h_div : ∀ k, (∏ j ∈ Finset.range (k + 1), Q_seq (j + 1)) ∣ n_seq lambda h_lambda (m_seq lambda (k + 1)) := by
      intro k;
      induction' k with k ih;
      · unfold n_seq Q_seq m_seq; norm_num;
        rw [ show k_of_index lambda h_lambda 2 = 1 from _ ] ; norm_num [ m_seq ];
        · unfold n_seq; norm_num [ m_seq ] ;
          have := step_data_props lambda h_lambda 1;
          rcases k : M_at lambda 1 with ( _ | _ | k ) <;> simp_all +decide [ StrictMonoOn ];
          · linarith [ M_at_pos lambda h_lambda 1 ( by norm_num ) ];
          · unfold Q_seq at this; aesop;
          · have := this.2.2.2.2.2 0; norm_num at this;
            unfold lambda_seq at this; norm_num at this;
            norm_num [ ‹Q_seq 1 ∣ N_at lambda 1 ∧ d_at lambda 1 0 = 1 ∧ d_at lambda 1 ( _ + 1 + 1 ) = N_at lambda 1 ∧ _› ] at this ⊢;
            exact ⟨ 1, by norm_num; exact le_antisymm ( mod_cast this.2 ) ( mod_cast by exact Nat.le_of_not_lt fun h => by interval_cases d_at lambda 1 1 <;> norm_num at * ) ⟩;
        · unfold k_of_index;
          simp +decide [ Nat.find_eq_iff, m_seq ];
      · have h_div : n_seq lambda h_lambda (m_seq lambda (k + 2)) = N_at lambda (k + 2) * n_seq lambda h_lambda (m_seq lambda (k + 1)) := by
          rw [ n_seq_formula ];
          rotate_left;
          exact k + 2;
          · linarith;
          · exact m_seq_strictMono _ h_lambda |> StrictMono.monotone <| Nat.le_succ _;
          · norm_num;
          · have := step_data_props lambda h_lambda ( k + 2 );
            simp_all +decide [ m_seq_succ ];
        simp_all +decide [ Finset.prod_range_succ ];
        convert Nat.mul_dvd_mul ( step_data_props ( lambda ) h_lambda ( k + 2 ) |>.1 ) ih using 1 ; ring;
    convert h_div k using 1;
    exact congr_arg _ ( Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr <| by linarith [ m_seq_strictMono lambda h_lambda ( show k + 1 > 0 from Nat.succ_pos _ ) ] ) )

/-
Every positive integer divides `super_Q k` for some `k`.
-/
lemma q_dvd_super_Q (q : ℕ) (hq : q > 0) :
  ∃ k, q ∣ super_Q k := by
    -- Let $q = \prod_{i=1}^k p_i^{a_i}$ be the prime factorization of $q$.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ∀ p ∈ Nat.primeFactors q, p ≤ Nat.nth Nat.Prime (k - 1) := by
      use ( Finset.sup ( Nat.primeFactors q ) ( fun p => Nat.count ( Nat.Prime ) p ) ) + 1;
      norm_num +zetaDelta at *;
      intro p pp dp _; refine' le_trans _ ( Nat.nth_monotone _ <| Finset.le_sup <| Nat.mem_primeFactors.mpr ⟨ pp, dp, by aesop ⟩ ) ; aesop;
      exact Nat.infinite_setOf_prime;
    -- Choose $k$ large enough such that $k > \max_{i=1}^k a_i$.
    obtain ⟨k', hk'⟩ : ∃ k' : ℕ, ∀ p ∈ Nat.primeFactors q, Nat.factorization q p ≤ k' - Nat.count (Nat.Prime) p := by
      use ∑ p ∈ q.primeFactors, q.factorization p + ∑ p ∈ q.primeFactors, Nat.count Nat.Prime p + 1;
      exact fun p hp => le_tsub_of_add_le_left <| by linarith [ Finset.single_le_sum ( fun x _ => Nat.zero_le ( q.factorization x ) ) hp, Finset.single_le_sum ( fun x _ => Nat.zero_le ( Nat.count Nat.Prime x ) ) hp ] ;
    refine' ⟨ k + k', _ ⟩;
    have h_div : ∀ p ∈ Nat.primeFactors q, Nat.factorization q p ≤ ∑ j ∈ Finset.range (k + k'), Nat.factorization (Q_seq (j + 1)) p := by
      intros p hp
      have h_factorization : ∀ j ≥ Nat.count (Nat.Prime) p, Nat.factorization (Q_seq (j + 1)) p ≥ 1 := by
        intros j hj
        have h_prime_factor_count : p ∈ Finset.image (fun i => Nat.nth Nat.Prime i) (Finset.range (j + 1)) := by
          refine' Finset.mem_image.mpr ⟨ Nat.count Nat.Prime p, Finset.mem_range.mpr ( by linarith ), _ ⟩;
          rw [ Nat.nth_count ] ; aesop;
        obtain ⟨ i, hi, rfl ⟩ := Finset.mem_image.mp h_prime_factor_count; simp +decide [ Q_seq ] ;
        rw [ Nat.factorization_prod ] <;> norm_num [ Nat.Prime.ne_zero ];
        rw [ Finset.sum_eq_add_sum_diff_singleton_of_mem hi ] ; aesop;
      refine le_trans ( hk' p hp ) ?_;
      refine' le_trans _ ( Finset.sum_le_sum_of_subset <| Finset.range_mono <| show k + k' ≥ Nat.count Nat.Prime p + ( k' - Nat.count Nat.Prime p ) from _ );
      · rw [ Finset.sum_range_add ];
        exact le_add_of_nonneg_of_le ( Nat.zero_le _ ) ( le_trans ( by norm_num ) ( Finset.sum_le_sum fun _ _ => h_factorization _ ( by linarith ) ) );
      · rw [ add_tsub_cancel_of_le ];
        · linarith;
        · contrapose! hk';
          exact ⟨ p, hp, by rw [ Nat.sub_eq_zero_of_le hk'.le ] ; exact Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp hp ) ⟩;
    rw [ ← Nat.factorization_le_iff_dvd ];
    · intro p; by_cases hp : Nat.Prime p <;> by_cases hp' : p ∣ q <;> simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd ] ;
      unfold super_Q; rw [ Nat.factorization_prod ] ; aesop;
      exact fun x hx => Finset.prod_ne_zero_iff.mpr fun i hi => Nat.Prime.ne_zero <| by aesop;
    · positivity;
    · exact Finset.prod_ne_zero_iff.mpr fun i hi => Finset.prod_ne_zero_iff.mpr fun j hj => Nat.Prime.ne_zero <| by aesop;

/-
Every positive integer divides some term of the sequence `final_n`.
-/
lemma final_n_div_all (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (q : ℕ) (hq : q > 0) :
  ∃ i, q ∣ final_n lambda h_lambda i := by
    -- By `super_Q_dvd_final_n`, we know that `super_Q k ∣ final_n (final_m (k - 1))`.
    obtain ⟨k, hk⟩ : ∃ k, q ∣ super_Q k := q_dvd_super_Q q hq
    have h_div : super_Q k ∣ final_n lambda h_lambda (final_m lambda (k - 1)) := by
      exact super_Q_dvd_final_n lambda h_lambda k;
    exact ⟨ _, dvd_trans hk h_div ⟩

/-
There exists an index `i` such that `final_n i < 2^i`.
-/
lemma exists_final_n_lt_two_pow (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  ∃ i, final_n lambda h_lambda i < 2 ^ i := by
    -- By `final_n_div_all`, there exists an index `i` such that `3 ∣ final_n i`.
    obtain ⟨i, hi⟩ : ∃ i, 3 ∣ final_n lambda h_lambda i := by
      exact final_n_div_all lambda h_lambda 3 ( by norm_num ) |> fun ⟨ i, hi ⟩ => ⟨ i, hi ⟩;
    by_contra h_contra
    push Not at h_contra
    have h_eq : final_n lambda h_lambda i = 2 ^ i := by
      exact le_antisymm ( final_n_le_two_pow _ _ _ ) ( h_contra _ )
    have h_false : 3 ∣ 2 ^ i := by
      exact h_eq ▸ hi
    exact absurd h_false (by
    norm_num [ Nat.Prime.dvd_iff_one_le_factorization ])

/-
The sum of reciprocals of `final_n` converges.
-/
lemma final_n_summable (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  Summable (fun i => (1 : ℝ) / final_n lambda h_lambda i) := by
    -- By induction, we can show that $final_n i \geq \lambda^i$ for all $i$.
    have h_exp_growth : ∀ i, (final_n lambda h_lambda i : ℝ) ≥ lambda ^ i := by
      -- We use induction to prove that $n_{i+1} \ge \lambda n_i$.
      have h_inductive_step : ∀ i, (final_n lambda h_lambda (i + 1) : ℝ) ≥ lambda * (final_n lambda h_lambda i : ℝ) := by
        have := final_n_is_lacunary lambda h_lambda;
        exact fun i => by have := this i; rw [ ge_iff_le, le_div_iff₀ ( Nat.cast_pos.mpr <| final_n_pos _ _ _ ) ] at this; linarith;
      intro i; induction i <;> simp_all +decide [pow_succ'] ;
      · exact Nat.one_le_of_lt ( final_n_pos _ _ _ ) |> le_trans <| Nat.le_refl _;
      · exact le_trans ( mul_le_mul_of_nonneg_left ‹_› ( by linarith ) ) ( h_inductive_step _ );
    -- Since $1/\lambda < 1$, the geometric series $\sum (1/\lambda)^i$ converges.
    have h_geo_series : Summable (fun i => (1 / lambda : ℝ) ^ i) := by
      exact summable_geometric_of_lt_one ( by exact one_div_nonneg.mpr ( by linarith ) ) ( by rw [ div_lt_iff₀ ] <;> linarith );
    exact h_geo_series.of_nonneg_of_le ( fun i => by positivity ) fun i => by simpa using inv_anti₀ ( pow_pos ( by linarith ) _ ) ( h_exp_growth i ) ;

/-
The sum of reciprocals of `final_n` is strictly greater than 2.
-/
lemma final_n_sum_gt_two (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  ∑' i, (1 : ℝ) / final_n lambda h_lambda i > 2 := by
    obtain ⟨ k, hk ⟩ := exists_final_n_lt_two_pow lambda h_lambda;
    -- We have if `final_n i < 2^i` for some `i`, then the sum of reciprocals is strictly greater than `2`.
    have h_sum_gt : ∑' i, (1 : ℝ) / (final_n lambda h_lambda i) > ∑' i, (1 : ℝ) / (2 ^ i) := by
      apply_rules [ Summable.tsum_lt_tsum ];
      · intro n; exact (by
        simp +zetaDelta at *;
        gcongr;
        · exact Nat.cast_pos.mpr ( final_n_pos _ _ _ );
        · exact_mod_cast final_n_le_two_pow _ _ _);
      · gcongr ; norm_cast ; linarith [ final_n_pos lambda h_lambda k ];
        norm_cast;
      · simpa using summable_geometric_two;
      · convert final_n_summable lambda h_lambda using 1;
    exact h_sum_gt.trans_le' ( by simpa using by ring_nf; rw [ tsum_geometric_of_lt_one ] <;> norm_num )

/-
Lemma 5: Any finite increasing sequence can be extended to a larger sequence ending in a multiple of $Q$ and all previous terms, with lacunary growth in the extension.
-/
lemma lm_divisors2 (lambda : ℝ) (Q : ℕ) (K : ℕ) (n : ℕ → ℕ)
  (h_lambda : 1 < lambda ∧ lambda < 2)
  (h_Q_pos : 0 < Q)
  (h_K : K ≥ 1)
  (h_n_mono : StrictMonoOn n (Set.Icc 0 (K - 1)))
  (h_n_pos : ∀ i < K, 0 < n i) :
  ∃ M ≥ K, ∃ n' : ℕ → ℕ,
    (∀ i < K, n' i = n i) ∧
    Q ∣ n' (M - 1) ∧
    (∀ i < M, n' i ∣ n' (M - 1)) ∧
    StrictMonoOn n' (Set.Icc 0 (M - 1)) ∧
    (∀ j, K - 1 ≤ j → j < M - 1 → lambda ≤ (n' (j + 1) : ℝ) / n' j ∧ (n' (j + 1) : ℝ) / n' j ≤ 2) := by
      rcases K with ( _ | K ) <;> simp_all +decide [ StrictMonoOn ];
      obtain ⟨N, d, M, hd₀, hd₁, hd₂⟩ : ∃ N : ℕ, ∃ d : ℕ → ℕ, ∃ M : ℕ,
        (∏ i ∈ Finset.range K, n i) * Q ∣ N ∧
        d 0 = 1 ∧ d M = N ∧
        (∀ j ≤ M, d j ∣ N) ∧
        (StrictMonoOn d (Set.Icc 0 M)) ∧
        (∀ j < M, lambda ≤ (d (j + 1) : ℝ) / d j ∧ (d (j + 1) : ℝ) / d j ≤ 2) := by
          convert lm_divisors ( lambda ) ( ( ∏ i ∈ Finset.range K, n i ) * Q ) _ _ using 1 <;> norm_num [ h_lambda, h_Q_pos, h_n_mono, h_n_pos ];
          exact fun i hi => h_n_pos i ( Nat.le_of_lt hi );
      refine' ⟨ K + M + 1, by linarith, fun i => if i < K then n i else d ( i - K ) * n K, _, _, _, _, _ ⟩;
      · intro i hi
        by_cases hik : i < K
        · simp [hik]
        · have hiK : i = K := by omega
          subst i
          simp [hd₁]
      · rw [show K + M + 1 - 1 = K + M by omega]
        simp [show ¬ K + M < K by omega, hd₂.1]
        exact dvd_mul_of_dvd_left ( dvd_of_mul_left_dvd hd₀ ) _;
      · intro i hi
        rw [show K + M + 1 - 1 = K + M by omega]
        by_cases hik : i < K
        · simp [hik, show ¬ K + M < K by omega, hd₂.1]
          refine' dvd_mul_of_dvd_left _ _;
          exact dvd_trans ( dvd_mul_of_dvd_left ( Finset.dvd_prod_of_mem _ ( Finset.mem_range.mpr hik ) ) _ ) hd₀;
        · have hiM : i - K ≤ M := by omega
          simp [hik, show ¬ K + M < K by omega, hd₂.1]
          exact mul_dvd_mul ( hd₂.2.1 _ hiM ) dvd_rfl;
      · intro a ha b hb hab
        rw [show K + M + 1 - 1 = K + M by omega] at ha hb
        dsimp
        split_ifs <;> try linarith [ h_n_mono ( by linarith ) ( by linarith ) hab ] ;
        · -- Since $a < K$, we have $n a < n K$ by the strict monotonicity of $n$ on $[0, K]$.
          have h_n_lt : n a < n K := by
            exact h_n_mono ( by linarith ) ( by linarith ) ( by linarith );
          by_cases h : b - K = 0 <;> simp_all +decide [ Nat.sub_eq_iff_eq_add ];
          exact lt_of_lt_of_le h_n_lt ( le_mul_of_one_le_left ( Nat.zero_le _ ) ( Nat.one_le_iff_ne_zero.mpr <| by intro t; have := hd₂.2.2.1 ( show 0 ∈ Set.Icc 0 M from ⟨ by norm_num, by linarith ⟩ ) ( show b - K ∈ Set.Icc 0 M from ⟨ Nat.zero_le _, Nat.sub_le_of_le_add <| by linarith ⟩ ) ( Nat.sub_pos_of_lt <| lt_of_le_of_ne ‹_› <| Ne.symm h ) ; aesop ) );
        · exact mul_lt_mul_of_pos_right ( hd₂.2.2.1 ⟨ by omega, by omega ⟩ ⟨ by omega, by omega ⟩ ( by omega ) ) ( h_n_pos _ ( by omega ) );
      · intro j hj₁ hj₂
        have h_nK_pos : 0 < n K := h_n_pos K le_rfl
        simp [show ¬ j < K by omega, show ¬ (j + 1 < K) by omega,
          Nat.succ_sub ( by omega : K ≤ j ), mul_div_mul_right, ne_of_gt h_nK_pos];
        exact hd₂.2.2.2 (j - K) ( by omega )

/-
The sequence $a_i$ is defined by $a_1=1$ and $a_{i+1} = \lceil \lambda a_i \rceil$.
-/
noncomputable def a_seq (lambda : ℝ) : ℕ → ℕ
| 0 => 1
| (n + 1) => Nat.ceil (lambda * (a_seq lambda n))

/-
$a_i$ is positive for all $i$.
-/
lemma a_seq_pos (lambda : ℝ) (h_lambda : 1 < lambda) (i : ℕ) :
  0 < a_seq lambda i := by
    induction' i with i ih <;> [ exact Nat.zero_lt_one; exact Nat.ceil_pos.mpr ( mul_pos ( by linarith ) ( Nat.cast_pos.mpr ih ) ) ]

/-
Any $\lambda$-lacunary sequence satisfies $n_i \ge a_i$.
-/
lemma n_ge_a_seq (lambda : ℝ) (n : ℕ → ℕ)
  (h_lambda : 1 < lambda)
  (h_n_pos : ∀ i, 0 < n i)
  (h_lac : IsLambdaLacunary lambda (fun i => n i)) :
  ∀ i, n i ≥ a_seq lambda i := by
    intro i; induction' i using Nat.strong_induction_on with i IH; rcases i with ( _ | i ) <;> simp_all +decide [ IsLambdaLacunary ] ;
    · exact h_n_pos 0;
    · have := h_lac i; rw [ le_div_iff₀ ( Nat.cast_pos.mpr ( h_n_pos _ ) ) ] at this; norm_num [ a_seq ] at *;
      exact le_trans ( mul_le_mul_of_nonneg_left ( mod_cast IH i ( le_rfl ) ) ( by positivity ) ) this

lemma R_lambda_le (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  R_lambda lambda ≤ ∑' i, (1 : ℝ) / a_seq lambda i := by
    refine' csSup_le _ _ <;> norm_num +zetaDelta at *;
    · refine' ⟨ 0, ⟨ 0, 0, _, _ ⟩ ⟩ <;> norm_num [ FillsInterval ];
      exact ⟨ fun i => 2 ^ i, fun i => by positivity, fun i => by norm_num [ pow_succ' ] ; nlinarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) i.zero_le ] ⟩;
    · rintro b x y rfl ⟨ n, hn₁, hn₂, hn₃ ⟩
      generalize_proofs at *;
      -- Since $n_i \ge a_i$, we have $1/n_i \le 1/a_i$, thus $\sum 1/n_i \le \sum 1/a_i$.
      have h_sum_le : Summable (fun i => (1 : ℝ) / n i) := by
        have h_sum_le : ∀ i, (1 : ℝ) / n i ≤ (1 : ℝ) / a_seq lambda i := by
          exact fun i => one_div_le_one_div_of_le ( Nat.cast_pos.mpr ( a_seq_pos _ h_lambda.1 _ ) ) ( mod_cast n_ge_a_seq _ _ h_lambda.1 hn₁ hn₂ _ ) ;
        generalize_proofs at *; (
        -- Since $\sum 1/a_i$ is a geometric series with ratio $1/\lambda < 1$, it converges.
        have h_geo_series : Summable (fun i => (1 : ℝ) / a_seq lambda i) := by
          have h_ratio : ∀ i, (1 : ℝ) / a_seq lambda (i + 1) ≤ (1 / lambda) * (1 / a_seq lambda i) := by
            intro i
            have h_a_seq : a_seq lambda (i + 1) ≥ lambda * a_seq lambda i := by
              exact Nat.le_ceil _ |> le_trans ( by norm_num ) ;
            generalize_proofs at *; (
            rw [ div_mul_div_comm, div_le_div_iff₀ ] <;> nlinarith [ show ( a_seq lambda i : ℝ ) > 0 from Nat.cast_pos.mpr ( a_seq_pos lambda h_lambda.1 i ) ] ;)
          refine' summable_of_ratio_norm_eventually_le _ _ <;> norm_num at *;
          exacts [ lambda⁻¹, inv_lt_one_of_one_lt₀ h_lambda.1, ⟨ 0, fun i hi => h_ratio i ⟩ ]
        generalize_proofs at *; (
        exact Summable.of_nonneg_of_le ( fun i => by positivity ) h_sum_le h_geo_series))
      have h_le : ∑' i, (1 : ℝ) / n i ≤ ∑' i, (1 : ℝ) / a_seq lambda i := by
        apply_rules [ Summable.tsum_le_tsum ];
        · exact fun i => one_div_le_one_div_of_le ( Nat.cast_pos.mpr ( a_seq_pos _ h_lambda.1 _ ) ) ( mod_cast n_ge_a_seq _ _ h_lambda.1 hn₁ hn₂ _ );
        · have h_le : ∀ i, (1 : ℝ) / a_seq lambda i ≤ (1 / lambda) ^ i := by
            intro i
            have h_ai_ge_lambda_i : (a_seq lambda i : ℝ) ≥ lambda ^ i := by
              induction' i with i ih <;> norm_num [ *, pow_succ' ] at *;
              · exact Nat.one_le_iff_ne_zero.mpr ( by norm_num [ show a_seq lambda 0 = 1 from rfl ] );
              · exact le_trans ( mul_le_mul_of_nonneg_left ih <| by linarith ) <| Nat.le_ceil _ |> le_trans ( by norm_num [ a_seq ] ) ;
            generalize_proofs at *; (
            simpa using inv_anti₀ ( pow_pos ( by linarith ) _ ) h_ai_ge_lambda_i |> le_trans <| by norm_num;)
          generalize_proofs at *; (
          exact Summable.of_nonneg_of_le ( fun i => by positivity ) h_le ( summable_geometric_of_lt_one ( by exact one_div_nonneg.mpr ( by linarith ) ) ( by rw [ div_lt_iff₀ ] <;> linarith ) ))
      generalize_proofs at *; (
      -- Since $(x, y) \cap \mathbb{Q} \subseteq P(1/n)$, we have $(x, y) \subseteq \overline{P(1/n)}$.
      have h_subset_closure : Set.Ioo x y ⊆ closure (SubsetSums (fun i => (1 : ℝ) / n i)) := by
        intro z hz
        have h_rat : ∀ ε > 0, ∃ q : ℚ, x < q ∧ q < y ∧ |q - z| < ε := by
          intro ε ε_pos
          obtain ⟨q, hq⟩ : ∃ q : ℚ, z < q ∧ q < min (z + ε) y := by
            exact exists_rat_btwn ( lt_min ( lt_add_of_pos_right _ ε_pos ) hz.2 ) |> fun ⟨ q, hq₁, hq₂ ⟩ => ⟨ q, hq₁, hq₂ ⟩
          generalize_proofs at *; (
          exact ⟨ q, by linarith [ hz.1 ], by linarith [ hq.2, min_le_right ( z + ε ) y ], abs_lt.mpr ⟨ by linarith [ hq.1, min_le_left ( z + ε ) y ], by linarith [ hq.2, min_le_left ( z + ε ) y ] ⟩ ⟩)
        generalize_proofs at *; (
        exact mem_closure_iff_nhds_basis ( Metric.nhds_basis_ball ) |>.2 fun ε hε => by rcases h_rat ε hε with ⟨ q, hq₁, hq₂, hq₃ ⟩ ; exact ⟨ q, hn₃ ⟨ ⟨ hq₁, hq₂ ⟩, q, rfl ⟩, by simpa using hq₃ ⟩ ;)
      generalize_proofs at *; (
      -- Since $P(1/n) \subseteq [0, \sum 1/n_i]$, we have $\overline{P(1/n)} \subseteq [0, \sum 1/n_i]$.
      have h_closure_subset : closure (SubsetSums (fun i => (1 : ℝ) / n i)) ⊆ Set.Icc 0 (∑' i, (1 : ℝ) / n i) := by
        refine' closure_minimal _ ( isClosed_Icc );
        intro s hs; rcases hs with ⟨ t, rfl ⟩ ; exact ⟨ Finset.sum_nonneg fun _ _ => by positivity, Summable.sum_le_tsum _ ( fun _ _ => by positivity ) h_sum_le ⟩ ;
      generalize_proofs at *; (
      by_cases hxy : x < y <;> simp_all +decide [ Set.subset_def ];
      · -- Since $y$ is the upper bound of the interval $(x, y)$, and the closure of the subset sums is contained within $[0, \sum 1/n_i]$, we have $y \leq \sum 1/n_i$.
        have hy_le_sum : y ≤ ∑' i, (1 : ℝ) / n i := by
          have hy_le_sum : ∀ᶠ z in nhdsWithin y (Set.Iio y), z ≤ ∑' i, (1 : ℝ) / n i := by
            filter_upwards [ Ioo_mem_nhdsLT hxy ] with z hz using by simpa using h_closure_subset z ( h_subset_closure z hz.1 hz.2 ) |>.2;
          generalize_proofs at *; (
          exact le_of_tendsto ( Filter.tendsto_id.mono_left <| nhdsWithin_le_nhds ) hy_le_sum |> le_trans <| by norm_num;)
        generalize_proofs at *; (
        norm_num at * ; linarith [ h_closure_subset x ( show x ∈ closure ( SubsetSums fun i => ( n i : ℝ ) ⁻¹ ) from by
                                                          have hx_closure : Filter.Tendsto (fun ε => x + ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds x) := by
                                                            exact tendsto_nhdsWithin_of_tendsto_nhds ( by norm_num [ Filter.Tendsto ] ) ;
                                                          generalize_proofs at *; (
                                                          exact mem_closure_of_tendsto hx_closure ( Filter.eventually_of_mem ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, sub_pos.mpr hxy ⟩ ) fun ε hε => h_subset_closure _ ( by linarith [ hε.1 ] ) ( by linarith [ hε.2 ] ) ) |> fun h => by simpa using h;) ) ] ;);
      · linarith [ show 0 ≤ ∑' i : ℕ, ( a_seq lambda i : ℝ ) ⁻¹ from tsum_nonneg fun _ => inv_nonneg.2 <| Nat.cast_nonneg _ ])))

/-
The sequence $a_i$ satisfies $\lambda \le a_{i+1}/a_i \le 2$.
-/
lemma a_seq_growth (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (i : ℕ) :
  lambda ≤ (a_seq lambda (i + 1) : ℝ) / a_seq lambda i ∧ (a_seq lambda (i + 1) : ℝ) / a_seq lambda i ≤ 2 := by
    -- By definition of $a_seq$, we know that $a_{i+1} \geq \lambda a_i$ and $a_{i+1} \leq 2 a_i$.
    have h_bounds : lambda * a_seq lambda i ≤ a_seq lambda (i + 1) ∧ a_seq lambda (i + 1) ≤ 2 * a_seq lambda i := by
      constructor;
      · exact Nat.le_ceil _;
      · exact Nat.ceil_le.mpr ( by norm_num; nlinarith [ show ( a_seq lambda i : ℝ ) ≥ 1 by exact_mod_cast a_seq_pos _ h_lambda.1 i ] );
    exact ⟨ by rw [ le_div_iff₀ ( Nat.cast_pos.mpr <| a_seq_pos _ h_lambda.1 _ ) ] ; linarith, by rw [ div_le_iff₀ ( Nat.cast_pos.mpr <| a_seq_pos _ h_lambda.1 _ ) ] ; exact_mod_cast h_bounds.2 ⟩

/-
The sequence $a_i$ is strictly increasing.
-/
lemma a_seq_strictMono (lambda : ℝ) (h_lambda : 1 < lambda) : StrictMono (a_seq lambda) := by
  refine' strictMono_nat_of_lt_succ _;
  intro n
  have h_ceil : a_seq lambda (n + 1) = Nat.ceil (lambda * a_seq lambda n) := by
    rfl
  have h_gt : lambda * a_seq lambda n > a_seq lambda n := by
    exact lt_mul_of_one_lt_left ( Nat.cast_pos.mpr ( a_seq_pos _ h_lambda _ ) ) h_lambda
  have h_ceil_gt : a_seq lambda (n + 1) > a_seq lambda n := by
    exact h_ceil.symm ▸ Nat.lt_ceil.mpr ( mod_cast h_gt )
  exact h_ceil_gt

/-
Construction of the base extended sequence for Theorem 2.
-/
noncomputable def base_data (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) : ℕ × (ℕ → ℕ) :=
  let n := a_seq lambda
  have h_mono : StrictMonoOn n (Set.Icc 0 (K - 1)) := by
    apply StrictMono.strictMonoOn
    apply a_seq_strictMono lambda h_lambda.1
  have h_pos : ∀ i < K, 0 < n i := fun i _ => a_seq_pos lambda h_lambda.1 i
  let ex := lm_divisors2 lambda 1 K n h_lambda Nat.one_pos hK h_mono h_pos
  let M := Classical.choose ex
  let spec_M := Classical.choose_spec ex
  let ex_n' := spec_M.2
  let n' := Classical.choose ex_n'
  (M, n')

/-
Helper definitions for Theorem 2.
-/
noncomputable def base_M (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) : ℕ :=
  (base_data lambda K h_lambda hK).1

noncomputable def base_n (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) : ℕ → ℕ :=
  (base_data lambda K h_lambda hK).2

/-
Definition of the indices $m_k$ for Theorem 2.
-/
noncomputable def m_seq_thm2 (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) : ℕ → ℕ
| 0 => base_M lambda K h_lambda hK - 1
| (k + 1) => m_seq_thm2 lambda K h_lambda hK k + M_at lambda (k + 1)

lemma m_seq_thm2_strictMono (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) :
  StrictMono (m_seq_thm2 lambda K h_lambda hK) := by
    refine' strictMono_nat_of_lt_succ _;
    intro n
    simp [m_seq_thm2];
    apply M_at_pos lambda h_lambda (n + 1) (by linarith)

/-
Definition of the index function $k(i)$ for Theorem 2.
-/
noncomputable def k_of_index_thm2 (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) (i : ℕ) : ℕ :=
  if i ≤ base_M lambda K h_lambda hK - 1 then 0
  else
    let P := fun k => m_seq_thm2 lambda K h_lambda hK k ≥ i
    have h : ∃ k, P k := by
      use i
      have h_mono := m_seq_thm2_strictMono lambda K h_lambda hK
      exact StrictMono.id_le h_mono i
    Nat.find h

/-
Properties of the index function $k(i)$ for large $i$.
-/
lemma k_of_index_thm2_spec_high (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) (i : ℕ)
  (hi : i > base_M lambda K h_lambda hK - 1) :
  let k := k_of_index_thm2 lambda K h_lambda hK i
  m_seq_thm2 lambda K h_lambda hK k ≥ i ∧ m_seq_thm2 lambda K h_lambda hK (k - 1) < i := by
    unfold k_of_index_thm2;
    split_ifs <;> simp_all +decide;
    · linarith;
    · refine' ⟨ _, _ ⟩;
      · exact Nat.find_spec ( _ : ∃ k, m_seq_thm2 lambda K h_lambda hK k ≥ i );
      · have := Nat.find_min ( show ∃ k, m_seq_thm2 lambda K h_lambda hK k ≥ i from by exact ⟨ i, by exact Nat.recOn i ( by norm_num ) fun n ihn => by linarith! [ m_seq_thm2_strictMono lambda K h_lambda hK n.lt_succ_self ] ⟩ ) ( show Nat.find ( show ∃ k, m_seq_thm2 lambda K h_lambda hK k ≥ i from by exact ⟨ i, by exact Nat.recOn i ( by norm_num ) fun n ihn => by linarith! [ m_seq_thm2_strictMono lambda K h_lambda hK n.lt_succ_self ] ⟩ ) - 1 < Nat.find ( show ∃ k, m_seq_thm2 lambda K h_lambda hK k ≥ i from by exact ⟨ i, by exact Nat.recOn i ( by norm_num ) fun n ihn => by linarith! [ m_seq_thm2_strictMono lambda K h_lambda hK n.lt_succ_self ] ⟩ ) from Nat.sub_lt ( Nat.pos_of_ne_zero ( by aesop ) ) zero_lt_one ) ; aesop;

/-
Definition of the sequence $n_i$ for Theorem 2.
-/
noncomputable def n_seq_thm2 (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) (i : ℕ) : ℕ :=
  if _h : i ≤ base_M lambda K h_lambda hK - 1 then
    base_n lambda K h_lambda hK i
  else
    let k := k_of_index_thm2 lambda K h_lambda hK i
    let prev_m := m_seq_thm2 lambda K h_lambda hK (k - 1)
    let j := i - prev_m
    let d := d_at lambda k
    d j * n_seq_thm2 lambda K h_lambda hK prev_m
termination_by i
decreasing_by
  have _h_not_le : ¬ (i ≤ base_M lambda K h_lambda hK - 1) := _h
  have hi : i > base_M lambda K h_lambda hK - 1 := by linarith
  have h_spec := k_of_index_thm2_spec_high lambda K h_lambda hK i hi
  exact h_spec.2

/-
For $i$ in the base range, $n_i$ agrees with the base sequence.
-/
lemma n_seq_thm2_eq_base (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) (i : ℕ)
  (hi : i ≤ base_M lambda K h_lambda hK - 1) :
  n_seq_thm2 lambda K h_lambda hK i = base_n lambda K h_lambda hK i := by
    -- By definition of $n_seq_thm2$, if $i \leq base_M - 1$, then $n_seq_thm2 i = base_n i$.
    rw [n_seq_thm2]
    simp [hi]

/-
The sequence $n_i$ consists of positive integers.
-/
lemma n_seq_thm2_pos (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) (i : ℕ) :
  0 < n_seq_thm2 lambda K h_lambda hK i := by
    by_contra h_contra
    have h_neg : ∀ i, n_seq_thm2 lambda K h_lambda hK i = 0 → False := by
      intro i hi; induction' i using Nat.strongRecOn with i ih; unfold n_seq_thm2 at hi; split_ifs at hi <;> simp_all +decide ;
      · unfold base_n at hi;
        unfold base_data at hi; simp_all +decide ;
        have := Classical.choose_spec ( show ∃ n' : ℕ → ℕ, ( ∀ i < K, n' i = a_seq lambda i ) ∧ 1 ∣ n' ( base_M lambda K h_lambda hK - 1 ) ∧ ( ∀ i < base_M lambda K h_lambda hK, n' i ∣ n' ( base_M lambda K h_lambda hK - 1 ) ) ∧ StrictMonoOn n' ( Set.Icc 0 ( base_M lambda K h_lambda hK - 1 ) ) ∧ ( ∀ j, K - 1 ≤ j → j < base_M lambda K h_lambda hK - 1 → lambda ≤ ( n' ( j + 1 ) : ℝ ) / n' j ∧ ( n' ( j + 1 ) : ℝ ) / n' j ≤ 2 ) from by
                                          have := Classical.choose_spec ( show ∃ n' : ℕ → ℕ, ( ∀ i < K, n' i = a_seq lambda i ) ∧ 1 ∣ n' ( base_M lambda K h_lambda hK - 1 ) ∧ ( ∀ i < base_M lambda K h_lambda hK, n' i ∣ n' ( base_M lambda K h_lambda hK - 1 ) ) ∧ StrictMonoOn n' ( Set.Icc 0 ( base_M lambda K h_lambda hK - 1 ) ) ∧ ( ∀ j, K - 1 ≤ j → j < base_M lambda K h_lambda hK - 1 → lambda ≤ ( n' ( j + 1 ) : ℝ ) / n' j ∧ ( n' ( j + 1 ) : ℝ ) / n' j ≤ 2 ) from by
                                            have := Classical.choose_spec ( show ∃ M : ℕ, K ≤ M ∧ ∃ n' : ℕ → ℕ, ( ∀ i < K, n' i = a_seq lambda i ) ∧ 1 ∣ n' ( M - 1 ) ∧ ( ∀ i < M, n' i ∣ n' ( M - 1 ) ) ∧ StrictMonoOn n' ( Set.Icc 0 ( M - 1 ) ) ∧ ( ∀ j, K - 1 ≤ j → j < M - 1 → lambda ≤ ( n' ( j + 1 ) : ℝ ) / n' j ∧ ( n' ( j + 1 ) : ℝ ) / n' j ≤ 2 ) from by
                                                                              have := lm_divisors2 lambda 1 K ( fun i => a_seq lambda i ) h_lambda Nat.one_pos hK ( show StrictMonoOn ( fun i => a_seq lambda i ) ( Set.Icc 0 ( K - 1 ) ) from by
                                                                                                                                                                      exact fun i hi j hj hij => a_seq_strictMono lambda h_lambda.1 hij |> lt_of_le_of_lt ( by aesop ) |> lt_of_lt_of_le <| le_rfl; ) ( fun i hi => a_seq_pos lambda h_lambda.1 i ) ; simp_all +decide [ StrictMonoOn ] ; )
                                            exact this.2 ) ; simp_all +decide [ StrictMonoOn ] ;
                                          exact ⟨ _, this ⟩ ) ; simp_all +decide [ StrictMonoOn ] ;
        have hbase0 : base_n lambda K h_lambda hK 0 = a_seq lambda 0 := this.1 0 (by linarith)
        by_cases hi0 : i = 0
        · subst i
          change base_n lambda K h_lambda hK 0 = 0 at hi
          norm_num [a_seq] at hbase0
          omega
        · have hmono := this.2.2.1
            (show 0 ≤ base_M lambda K h_lambda hK - 1 from by linarith)
            (show i ≤ base_M lambda K h_lambda hK - 1 from by linarith)
            (Nat.pos_of_ne_zero hi0)
          change base_n lambda K h_lambda hK i = 0 at hi
          change base_n lambda K h_lambda hK 0 < base_n lambda K h_lambda hK i at hmono
          norm_num [a_seq] at hbase0
          omega
      · refine' hi.elim _ _ <;> simp_all +decide ;
        · have := step_data_props lambda h_lambda (k_of_index_thm2 lambda K h_lambda hK i);
          exact Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos ( this.2.2.2.1 _ ( by
            have := k_of_index_thm2_spec_high lambda K h_lambda hK i ( by linarith ) ; simp_all +decide ;
            cases k : k_of_index_thm2 lambda K h_lambda hK i <;> simp_all +decide [m_seq_thm2] ; linarith [ m_seq_thm2_strictMono lambda K h_lambda hK ( Nat.lt_succ_self ‹_› ) ] ; ) ) ( Nat.pos_of_ne_zero ( by
            intro h; have := this.2.2.1; simp_all +decide ;
            have := ‹d_at lambda ( k_of_index_thm2 lambda K h_lambda hK i ) 0 = 1 ∧ StrictMonoOn ( d_at lambda ( k_of_index_thm2 lambda K h_lambda hK i ) ) ( Icc 0 ( M_at lambda ( k_of_index_thm2 lambda K h_lambda hK i ) ) ) ∧ _›.2.1 ( show 0 ∈ Icc 0 ( M_at lambda ( k_of_index_thm2 lambda K h_lambda hK i ) ) from ⟨ by norm_num, Nat.zero_le _ ⟩ ) ( show M_at lambda ( k_of_index_thm2 lambda K h_lambda hK i ) ∈ Icc 0 ( M_at lambda ( k_of_index_thm2 lambda K h_lambda hK i ) ) from ⟨ Nat.zero_le _, le_rfl ⟩ ) ; aesop; ) ) );
        · have := k_of_index_thm2_spec_high lambda K h_lambda hK i ( by linarith ) ; aesop;
    exact h_neg i (by
    exact Nat.eq_zero_of_not_pos h_contra)

/-
The sequence $n_i$ is strictly increasing.
-/
lemma n_seq_thm2_strictMono (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) :
  StrictMono (n_seq_thm2 lambda K h_lambda hK) := by
    -- If $i$ is the last of base range, $n_{i+1}$ is the first of the next block, which is a multiple of $n_i$ by a factor $> 1$.
    have h_last_base : ∀ i, i = base_M lambda K h_lambda hK - 1 → n_seq_thm2 lambda K h_lambda hK (i + 1) > n_seq_thm2 lambda K h_lambda hK i := by
      intro i hi
      have h_k : k_of_index_thm2 lambda K h_lambda hK (i + 1) = 1 := by
        simp [k_of_index_thm2, hi];
        simp +decide [ Nat.find_eq_iff ];
        constructor <;> norm_num [ m_seq_thm2 ];
        exact M_at_pos _ h_lambda 1 ( by linarith ) |> Nat.one_le_of_lt;
      have h_prev_m : m_seq_thm2 lambda K h_lambda hK (k_of_index_thm2 lambda K h_lambda hK (i + 1) - 1) = i := by
        aesop
      have h_j : i + 1 - m_seq_thm2 lambda K h_lambda hK (k_of_index_thm2 lambda K h_lambda hK (i + 1) - 1) = 1 := by
        rw [ h_prev_m, Nat.add_sub_cancel_left ]
      have h_d : d_at lambda 1 1 > 1 := by
        have := step_data_props lambda h_lambda 1; simp_all +decide [ StrictMonoOn ] ;
        have := this.2.2.2.2.1 ( show 0 ≤ M_at lambda 1 from Nat.zero_le _ ) ( show 1 ≤ M_at lambda 1 from Nat.succ_le_of_lt ( M_at_pos _ h_lambda 1 ( by linarith ) ) ) ; aesop;
      have h_n : n_seq_thm2 lambda K h_lambda hK (i + 1) = d_at lambda 1 1 * n_seq_thm2 lambda K h_lambda hK i := by
        rw [ n_seq_thm2 ] ; aesop ( simp_config := { singlePass := true } ) ;
      have h_final : n_seq_thm2 lambda K h_lambda hK (i + 1) > n_seq_thm2 lambda K h_lambda hK i := by
        nlinarith [ n_seq_thm2_pos lambda K h_lambda hK i ]
      exact h_final;
    -- If $i$ is inside a block, it follows from monotonicity of $d_k$.
    have h_block : ∀ i, base_M lambda K h_lambda hK - 1 < i → i < m_seq_thm2 lambda K h_lambda hK (k_of_index_thm2 lambda K h_lambda hK i) → n_seq_thm2 lambda K h_lambda hK (i + 1) > n_seq_thm2 lambda K h_lambda hK i := by
      intros i hi₁ hi₂
      have h_block : n_seq_thm2 lambda K h_lambda hK (i + 1) = d_at lambda (k_of_index_thm2 lambda K h_lambda hK i) (i + 1 - m_seq_thm2 lambda K h_lambda hK (k_of_index_thm2 lambda K h_lambda hK i - 1)) * n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK (k_of_index_thm2 lambda K h_lambda hK i - 1)) := by
        have h_block : k_of_index_thm2 lambda K h_lambda hK (i + 1) = k_of_index_thm2 lambda K h_lambda hK i := by
          have h_block : m_seq_thm2 lambda K h_lambda hK (k_of_index_thm2 lambda K h_lambda hK i - 1) < i + 1 ∧ i + 1 ≤ m_seq_thm2 lambda K h_lambda hK (k_of_index_thm2 lambda K h_lambda hK i) := by
            have h_block : m_seq_thm2 lambda K h_lambda hK (k_of_index_thm2 lambda K h_lambda hK i - 1) < i := by
              exact k_of_index_thm2_spec_high _ _ _ _ _ hi₁ |>.2
            generalize_proofs at *; (
            exact ⟨ Nat.lt_succ_of_lt h_block, Nat.succ_le_of_lt hi₂ ⟩)
          generalize_proofs at *; (
          apply le_antisymm
          generalize_proofs at *; (
          -- Since $m_seq_thm2$ is strictly monotonic, if $i + 1 \leq m_seq_thm2 (k_of_index_thm2 i)$, then the smallest $k$ for $i + 1$ must be $\leq k_of_index_thm2 i$.
          have h_mono : ∀ k, i + 1 ≤ m_seq_thm2 lambda K h_lambda hK k → k_of_index_thm2 lambda K h_lambda hK (i + 1) ≤ k := by
            intros k hk
            have h_mono : k_of_index_thm2 lambda K h_lambda hK (i + 1) ≤ k := by
              have h_def : k_of_index_thm2 lambda K h_lambda hK (i + 1) = Nat.find (show ∃ k, m_seq_thm2 lambda K h_lambda hK k ≥ i + 1 from ⟨k, hk⟩) := by
                                                                                      exact if_neg ( by linarith ) |> fun h => h.trans ( by rfl ) ;
              exact h_def.symm ▸ Nat.find_min' _ hk
            generalize_proofs at *; (exact h_mono)
          generalize_proofs at *; (
          grind))
          generalize_proofs at *; (
          apply Nat.le_of_not_lt; intro h_lt; (
          have := k_of_index_thm2_spec_high lambda K h_lambda hK ( i + 1 ) ( by linarith ) ; simp_all +decide ; (
          have hprev := k_of_index_thm2_spec_high lambda K h_lambda hK i hi₁
          have hle : m_seq_thm2 lambda K h_lambda hK (k_of_index_thm2 lambda K h_lambda hK (i + 1)) ≤
              m_seq_thm2 lambda K h_lambda hK (k_of_index_thm2 lambda K h_lambda hK i - 1) := by
            exact m_seq_thm2_strictMono _ _ _ _ |> StrictMono.monotone <| Nat.le_sub_one_of_lt h_lt
          omega ;))))
        generalize_proofs at *; (
        rw [ n_seq_thm2 ] ; simp +decide [ h_block ] ; ring_nf;
        exact fun h => False.elim <| hi₁.not_ge <| by omega;)
      have h_block' : n_seq_thm2 lambda K h_lambda hK i = d_at lambda (k_of_index_thm2 lambda K h_lambda hK i) (i - m_seq_thm2 lambda K h_lambda hK (k_of_index_thm2 lambda K h_lambda hK i - 1)) * n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK (k_of_index_thm2 lambda K h_lambda hK i - 1)) := by
        rw [ n_seq_thm2 ] ; aesop;
      simp_all +decide;
      refine' mul_lt_mul_of_pos_right _ _;
      · refine' step_data_props _ _ _ |>.2.2.2.2.1 _ _ _;
        · tauto;
        · rcases k : k_of_index_thm2 lambda K h_lambda hK i with ( _ | k ) <;> simp_all +decide ;
          · omega;
          · linarith! [ show m_seq_thm2 lambda K h_lambda hK ( ‹_› + 1 ) = m_seq_thm2 lambda K h_lambda hK ‹_› + M_at lambda ( ‹_› + 1 ) from rfl ];
        · have h_diff : m_seq_thm2 lambda K h_lambda hK (k_of_index_thm2 lambda K h_lambda hK i) = m_seq_thm2 lambda K h_lambda hK (k_of_index_thm2 lambda K h_lambda hK i - 1) + M_at lambda (k_of_index_thm2 lambda K h_lambda hK i) := by
            rcases k : k_of_index_thm2 lambda K h_lambda hK i with ( _ | k ) <;> simp_all +decide [ m_seq_thm2 ];
            grind;
          grind;
        · rw [ tsub_lt_tsub_iff_right ] <;> norm_num;
          exact Nat.le_of_lt ( k_of_index_thm2_spec_high _ _ _ _ _ hi₁ |>.2 );
      · exact n_seq_thm2_pos _ _ _ _ _;
    -- If $i$ is the last of a block, $n_{i+1}$ is the first of the next block, which is a multiple of $n_i$ by a factor $> 1$.
    have h_last_block : ∀ i, base_M lambda K h_lambda hK - 1 < i → i = m_seq_thm2 lambda K h_lambda hK (k_of_index_thm2 lambda K h_lambda hK i) → n_seq_thm2 lambda K h_lambda hK (i + 1) > n_seq_thm2 lambda K h_lambda hK i := by
      intros i hi₁ hi₂
      have h_next_block : k_of_index_thm2 lambda K h_lambda hK (i + 1) = k_of_index_thm2 lambda K h_lambda hK i + 1 := by
        refine' le_antisymm _ _;
        · unfold k_of_index_thm2 at *;
          split_ifs at * <;> try linarith;
          refine' Nat.find_min' _ _;
          exact Nat.succ_le_of_lt ( lt_of_le_of_lt ( by linarith ) ( m_seq_thm2_strictMono _ _ _ _ ( Nat.lt_succ_self _ ) ) );
        · refine' Nat.succ_le_of_lt ( Nat.lt_of_not_ge fun h => _ );
          have := k_of_index_thm2_spec_high lambda K h_lambda hK ( i + 1 ) ( by linarith );
          linarith [ this.1, this.2, show m_seq_thm2 lambda K h_lambda hK ( k_of_index_thm2 lambda K h_lambda hK ( i + 1 ) ) ≤ m_seq_thm2 lambda K h_lambda hK ( k_of_index_thm2 lambda K h_lambda hK i ) from by exact monotone_nat_of_le_succ ( fun n => by exact le_of_lt ( m_seq_thm2_strictMono lambda K h_lambda hK ( Nat.lt_succ_self n ) ) ) h ];
      have h_next_block : n_seq_thm2 lambda K h_lambda hK (i + 1) = d_at lambda (k_of_index_thm2 lambda K h_lambda hK i + 1) 1 * n_seq_thm2 lambda K h_lambda hK i := by
        rw [ n_seq_thm2 ];
        simp +decide [ h_next_block, hi₂.symm ];
        exact fun h => False.elim <| h.not_gt <| by linarith;
      have h_d_gt_one : 1 < d_at lambda (k_of_index_thm2 lambda K h_lambda hK i + 1) 1 := by
        have := step_data_props lambda h_lambda (k_of_index_thm2 lambda K h_lambda hK i + 1)
        have := this.2.2.2.2.1 ( show 0 ∈ Set.Icc 0 ( M_at lambda ( k_of_index_thm2 lambda K h_lambda hK i + 1 ) ) from ⟨ by norm_num, Nat.zero_le _ ⟩ ) ( show 1 ∈ Set.Icc 0 ( M_at lambda ( k_of_index_thm2 lambda K h_lambda hK i + 1 ) ) from ⟨ by norm_num, Nat.one_le_iff_ne_zero.mpr <| by
                                                                                                                                                            exact ne_of_gt ( M_at_pos lambda h_lambda _ ( Nat.succ_pos _ ) ) ⟩ ) ; norm_num at * ; linarith;
      nlinarith [ n_seq_thm2_pos lambda K h_lambda hK i ];
    refine' strictMono_nat_of_lt_succ fun i => _;
    by_cases hi : i ≤ base_M lambda K h_lambda hK - 1;
    · by_cases hi' : i < base_M lambda K h_lambda hK - 1;
      · have h_base_mono : StrictMonoOn (base_n lambda K h_lambda hK) (Set.Icc 0 (base_M lambda K h_lambda hK - 1)) := by
          have := Classical.choose_spec ( lm_divisors2 lambda 1 K ( a_seq lambda ) h_lambda Nat.one_pos hK ( by
            exact fun x hx y hy hxy => a_seq_strictMono _ h_lambda.1 hxy ) ( by
            exact fun i hi => a_seq_pos lambda h_lambda.1 i ) );
          exact this.2.choose_spec.2.2.2.1;
        rw [ n_seq_thm2_eq_base, n_seq_thm2_eq_base ] <;> try linarith;
        exact h_base_mono ⟨ by linarith, by linarith ⟩ ⟨ by linarith, by omega ⟩ ( by linarith );
      · exact h_last_base i ( le_antisymm hi ( not_lt.mp hi' ) );
    · by_cases hi' : i < m_seq_thm2 lambda K h_lambda hK ( k_of_index_thm2 lambda K h_lambda hK i );
      · exact h_block i ( not_le.mp hi ) hi';
      · convert h_last_block i ( not_le.mp hi ) _ using 1;
        unfold k_of_index_thm2 at *;
        split_ifs at * ; linarith [ Nat.find_spec ( show ∃ k, m_seq_thm2 lambda K h_lambda hK k ≥ i from ⟨ i, by exact Nat.le_induction ( by norm_num ) ( fun k hk ih => by linarith [ m_seq_thm2_strictMono lambda K h_lambda hK k.lt_succ_self ] ) i ( show i ≥ 0 from Nat.zero_le i ) ⟩ ) ]

/-
The sequence $n_i$ satisfies the growth condition $\lambda \le n_{i+1}/n_i \le 2$.
-/
lemma n_seq_thm2_growth (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) (i : ℕ) :
  lambda ≤ (n_seq_thm2 lambda K h_lambda hK (i + 1) : ℝ) / n_seq_thm2 lambda K h_lambda hK i ∧
  (n_seq_thm2 lambda K h_lambda hK (i + 1) : ℝ) / n_seq_thm2 lambda K h_lambda hK i ≤ 2 := by
    by_cases hi : i ≤ base_M lambda K h_lambda hK - 1 ∧ i + 1 ≤ base_M lambda K h_lambda hK - 1;
    · -- By definition of `base_n`, we know that `base_n i` and `base_n (i + 1)` satisfy the required properties.
      have h_base_n : ∀ i < base_M lambda K h_lambda hK - 1, lambda ≤ (base_n lambda K h_lambda hK (i + 1) : ℝ) / base_n lambda K h_lambda hK i ∧ (base_n lambda K h_lambda hK (i + 1) : ℝ) / base_n lambda K h_lambda hK i ≤ 2 := by
        have := Classical.choose_spec ( show ∃ M : ℕ,
            M ≥ K ∧
              ∃ n' : ℕ → ℕ,
                ( ∀ i < K, n' i = a_seq lambda i ) ∧
                  1 ∣ n' ( M - 1 ) ∧
                    ( ∀ i < M, n' i ∣ n' ( M - 1 ) ) ∧
                      StrictMonoOn n' ( Set.Icc 0 ( M - 1 ) ) ∧
                        ( ∀ j, K - 1 ≤ j → j < M - 1 → lambda ≤ ( n' ( j + 1 ) : ℝ ) / n' j ∧ ( n' ( j + 1 ) : ℝ ) / n' j ≤ 2 ) from by
                          apply_rules [ lm_divisors2 ] ; aesop;
                          · exact fun x hx y hy hxy => a_seq_strictMono _ h_lambda.1 hxy;
                          · exact fun i hi => a_seq_pos _ h_lambda.1 _ );
        have := Classical.choose_spec this.2;
        intro i hi
        by_cases hi_base : i < K - 1;
        · convert a_seq_growth lambda h_lambda i using 1;
          · rw [ show base_n lambda K h_lambda hK i = a_seq lambda i from _, show base_n lambda K h_lambda hK ( i + 1 ) = a_seq lambda ( i + 1 ) from _ ];
            · exact this.1 _ ( by omega );
            · exact this.1 i ( Nat.lt_of_lt_of_le hi_base ( Nat.pred_le _ ) );
          · rw [ show base_n lambda K h_lambda hK ( i + 1 ) = a_seq lambda ( i + 1 ) from this.1 ( i + 1 ) ( by omega ), show base_n lambda K h_lambda hK i = a_seq lambda i from this.1 i ( by omega ) ];
        · exact this.2.2.2.2 i ( by linarith ) hi;
      convert h_base_n i ( Nat.lt_of_succ_le hi.2 ) using 1;
      · rw [ n_seq_thm2_eq_base, n_seq_thm2_eq_base ] <;> aesop;
      · rw [ n_seq_thm2_eq_base, n_seq_thm2_eq_base ] <;> aesop;
    · by_cases hi : i < base_M lambda K h_lambda hK - 1 <;> simp_all +decide;
      · linarith;
      · -- By definition of $k_of_index_thm2$, we know that $m_seq_thm2 k \geq i$ and $m_seq_thm2 (k - 1) < i$.
        set k := k_of_index_thm2 lambda K h_lambda hK (i + 1)
        have hk : m_seq_thm2 lambda K h_lambda hK k ≥ i + 1 ∧ m_seq_thm2 lambda K h_lambda hK (k - 1) < i + 1 := by
          apply k_of_index_thm2_spec_high
          generalize_proofs at *; (
          exact Nat.lt_succ_of_le ( Nat.sub_le_of_le_add <| by linarith ) ;)
        generalize_proofs at *; (
        by_cases hi : i = m_seq_thm2 lambda K h_lambda hK (k - 1) <;> simp_all +decide; (
        -- By definition of $n_seq_thm2$, we know that $n_{i+1} = d_k(1) \cdot n_i$.
        have h_n_succ : n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK (k - 1) + 1) = d_at lambda k 1 * n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK (k - 1)) := by
          rw [n_seq_thm2];
          split_ifs <;> simp_all +decide; (
          omega;);
          grind
        generalize_proofs at *; (
        have := step_data_props lambda h_lambda k; simp_all +decide ;
        have := this.2.2.2.2.2 0 ( Nat.pos_of_ne_zero ( by
          intro h; simp_all +decide [ StrictMonoOn ] ;
          rcases k with ( _ | _ | k ) <;> simp_all +decide [ m_seq_thm2 ] ) ) ; simp_all +decide ;
        rw [ mul_div_cancel_right₀ _ ( Nat.cast_ne_zero.mpr <| ne_of_gt <| n_seq_thm2_pos _ _ _ _ _ ) ] ; exact ⟨ le_trans ( by exact le_max_left _ _ ) this.1, le_trans ( Nat.cast_le.mpr this.2 ) ( by norm_num ) ⟩ ;));
        -- Since $i$ is not equal to $m_seq_thm2 (k - 1)$, we have $i > m_seq_thm2 (k - 1)$.
        have hi_gt : i > m_seq_thm2 lambda K h_lambda hK (k - 1) := by
          exact lt_of_le_of_ne ( by omega ) ( Ne.symm hi ) ;
        generalize_proofs at *; (
        have hk_eq : k_of_index_thm2 lambda K h_lambda hK i = k := by
          refine' le_antisymm _ _ <;> simp_all +decide [ k_of_index_thm2 ];
          · split_ifs <;> simp_all +decide ;
            exact ⟨ k, le_rfl, by linarith ⟩;
          · split_ifs <;> simp_all +decide ;
            · exact absurd ‹_› ( by linarith [ Nat.sub_add_cancel ( show 1 ≤ base_M lambda K h_lambda hK from Nat.one_le_iff_ne_zero.mpr <| by
                                                                      grind +ring ), show m_seq_thm2 lambda K h_lambda hK ( k - 1 ) ≥ base_M lambda K h_lambda hK - 1 from by
                                                                                                                                                          exact Nat.recOn ( k - 1 ) ( by norm_num [ m_seq_thm2 ] ) fun n ihn => by rw [ m_seq_thm2 ] ; exact Nat.le_trans ihn ( Nat.le_add_right _ _ ) ; ; ] );
            · intro m hm; exact lt_of_le_of_lt ( monotone_nat_of_le_succ ( fun n => by
                exact m_seq_thm2_strictMono lambda K h_lambda hK |> StrictMono.monotone |> fun h => h <| Nat.le_succ _; ) ( Nat.le_sub_one_of_lt hm ) ) hi_gt;
        generalize_proofs at *; (
        have h_ratio : n_seq_thm2 lambda K h_lambda hK (i + 1) = d_at lambda k (i + 1 - m_seq_thm2 lambda K h_lambda hK (k - 1)) * n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK (k - 1)) ∧ n_seq_thm2 lambda K h_lambda hK i = d_at lambda k (i - m_seq_thm2 lambda K h_lambda hK (k - 1)) * n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK (k - 1)) := by
          apply And.intro
          generalize_proofs at *; (
          rw [ n_seq_thm2 ];
          split_ifs <;> norm_num at * ; omega;
          rfl)
          generalize_proofs at *; (
          rw [n_seq_thm2];
          split_ifs <;> simp_all +decide;
          have h_contra : m_seq_thm2 lambda K h_lambda hK (k - 1) ≥ base_M lambda K h_lambda hK - 1 := by
            exact Nat.recOn ( k - 1 ) ( by norm_num [ m_seq_thm2 ] ) fun n ihn => by linarith! [ m_seq_thm2_strictMono lambda K h_lambda hK ( Nat.lt_succ_self n ) ] ;
          generalize_proofs at *; (
          omega))
        generalize_proofs at *; (
        have h_ratio : lambda ≤ (d_at lambda k (i + 1 - m_seq_thm2 lambda K h_lambda hK (k - 1)) : ℝ) / (d_at lambda k (i - m_seq_thm2 lambda K h_lambda hK (k - 1)) : ℝ) ∧ (d_at lambda k (i + 1 - m_seq_thm2 lambda K h_lambda hK (k - 1)) : ℝ) / (d_at lambda k (i - m_seq_thm2 lambda K h_lambda hK (k - 1)) : ℝ) ≤ 2 := by
          have h_ratio : ∀ j < M_at lambda k, lambda ≤ (d_at lambda k (j + 1) : ℝ) / (d_at lambda k j) ∧ (d_at lambda k (j + 1) : ℝ) / (d_at lambda k j) ≤ 2 := by
            intros j hj
            have := step_data_props lambda h_lambda k
            generalize_proofs at *; (
            exact ⟨ le_trans ( by exact le_max_left _ _ ) ( this.2.2.2.2.2 j hj |>.1 ), this.2.2.2.2.2 j hj |>.2 ⟩)
          generalize_proofs at *; (
          convert h_ratio ( i - m_seq_thm2 lambda K h_lambda hK ( k - 1 ) ) _ using 1 <;> norm_num [ Nat.sub_add_comm hi_gt.le ];
          rw [ tsub_lt_iff_left ] <;> try linarith!;
          rcases k <;> simp_all +decide [ m_seq_thm2 ] ; linarith! [ m_seq_diff_le_M lambda h_lambda ‹_› ( by linarith ) ] ;)
        generalize_proofs at *; (
        simp_all +decide [ mul_div_mul_right, ne_of_gt ( n_seq_thm2_pos _ _ _ _ _ ) ])))))

/-
$n_{m_k}$ divides $n_{m_{k+1}}$.
-/
lemma n_seq_thm2_div_prev_m (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) (k : ℕ) :
  n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK k) ∣ n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK (k + 1)) := by
    rw [ n_seq_thm2, n_seq_thm2 ];
    split_ifs <;> simp_all +decide [ m_seq_thm2 ];
    · rename_i h₁ h₂;
      contrapose! h₂;
      refine' lt_add_of_le_of_pos _ ( Nat.pos_of_ne_zero _ );
      · exact Nat.recOn k ( by norm_num [ m_seq_thm2 ] ) fun n ihn => by rw [ m_seq_thm2 ] ; exact le_trans ihn ( Nat.le_add_right _ _ ) ;
      · exact ne_of_gt ( M_at_pos _ h_lambda _ ( Nat.succ_pos _ ) );
    · rw [ show k_of_index_thm2 lambda K h_lambda hK ( m_seq_thm2 lambda K h_lambda hK k + M_at lambda ( k + 1 ) ) = k + 1 from ?_ ];
      · unfold n_seq_thm2; aesop;
      · refine' le_antisymm _ _ <;> norm_num [ k_of_index_thm2 ];
        · split_ifs <;> norm_num [ Nat.find_eq_iff ] at * ; aesop;
        · split_ifs <;> norm_num at * ; linarith [ Nat.find_spec ( show ∃ k, m_seq_thm2 lambda K h_lambda hK k ≥ m_seq_thm2 lambda K h_lambda hK k + M_at lambda ( k + 1 ) from ⟨ k + 1, by linarith [ show M_at lambda ( k + 1 ) > 0 from Nat.pos_of_ne_zero ( by
          grind ) ] ⟩ ) ];
          intro m hm; linarith [ show m_seq_thm2 lambda K h_lambda hK m ≤ m_seq_thm2 lambda K h_lambda hK k from by exact monotone_nat_of_le_succ ( fun n => by exact Nat.le_add_right _ _ ) hm ] ;
    · linarith [ Nat.zero_le ( M_at lambda ( k + 1 ) ) ];
    · have h_eq : k_of_index_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK k) = k ∧ k_of_index_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK k + M_at lambda (k + 1)) = k + 1 := by
        constructor;
        · unfold k_of_index_thm2;
          rw [ if_neg ( by linarith ) ];
          simp +decide [ Nat.find_eq_iff ];
          exact fun n hn => m_seq_thm2_strictMono lambda K h_lambda hK hn;
        · refine' le_antisymm _ _ <;> simp_all +decide [ k_of_index_thm2 ];
          · split_ifs <;> simp_all +decide ;
            exact ⟨ k + 1, le_rfl, by simp +decide [ m_seq_thm2 ] ⟩;
          · split_ifs <;> simp_all +decide ;
            · grind;
            · intro m hm; exact lt_add_of_le_of_pos ( monotone_nat_of_le_succ ( fun n => by exact le_of_lt ( m_seq_thm2_strictMono _ _ _ _ |> StrictMono.lt_iff_lt |>.2 <| Nat.lt_succ_self _ ) ) hm ) <| Nat.pos_of_ne_zero <| by
                exact ne_of_gt <| M_at_pos _ h_lambda _ <| Nat.succ_pos _;
      rcases k <;> simp_all +decide [ m_seq_thm2 ];
      rw [ show n_seq_thm2 lambda K h_lambda hK ( m_seq_thm2 lambda K h_lambda hK _ + M_at lambda ( _ + 1 ) ) = d_at lambda ( _ + 1 ) ( M_at lambda ( _ + 1 ) ) * n_seq_thm2 lambda K h_lambda hK ( m_seq_thm2 lambda K h_lambda hK _ ) from ?_ ];
      any_goals tauto;
      · exact dvd_mul_left _ _;
      · rw [ n_seq_thm2 ] ; aesop

/-
Base case for divisibility: elements in the base range divide the last element of the base range.
-/
lemma n_seq_thm2_base_div (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) :
  ∀ j < m_seq_thm2 lambda K h_lambda hK 0, n_seq_thm2 lambda K h_lambda hK j ∣ n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK 0) := by
    unfold m_seq_thm2;
    -- By definition of `base_n`, we know that `base_n j` divides `base_n (base_M - 1)` for all `j < base_M - 1`.
    intros j hj
    have h_base_div : base_n lambda K h_lambda hK j ∣ base_n lambda K h_lambda hK (base_M lambda K h_lambda hK - 1) := by
      unfold base_M at hj;
      unfold base_M base_data at *;
      have := Classical.choose_spec ( lm_divisors2 lambda 1 K ( a_seq lambda ) h_lambda Nat.one_pos hK ( by
        exact fun i hi j hj hij => a_seq_strictMono _ h_lambda.1 hij ) ( by
        exact fun i hi => a_seq_pos lambda h_lambda.1 i ) );
      convert this.2.choose_spec.2.2.1 j _ using 1;
      exact lt_of_lt_of_le hj ( Nat.pred_le _ );
    unfold n_seq_thm2;
    grind

/-
Divisibility within a block: $n_j$ divides the last element of the block.
-/
lemma n_seq_thm2_div_within_block (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) (k : ℕ) :
  ∀ j, m_seq_thm2 lambda K h_lambda hK k ≤ j → j ≤ m_seq_thm2 lambda K h_lambda hK (k + 1) →
  n_seq_thm2 lambda K h_lambda hK j ∣ n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK (k + 1)) := by
    intro j hj₁ hj₂
    by_cases hk : k_of_index_thm2 lambda K h_lambda hK j = k + 1;
    · -- Substitute the formulas for $n_j$ and $n_{m_{k+1}}$.
      have h_subst : n_seq_thm2 lambda K h_lambda hK j = d_at lambda (k + 1) (j - m_seq_thm2 lambda K h_lambda hK k) * n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK k) ∧ n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK (k + 1)) = d_at lambda (k + 1) (M_at lambda (k + 1)) * n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK k) := by
        apply And.intro;
        · rw [n_seq_thm2] at *; simp_all +decide ; (
          unfold k_of_index_thm2 at hk; aesop;);
        · rw [ n_seq_thm2 ];
          split_ifs <;> simp_all +decide [ m_seq_thm2 ];
          · have h_contra : m_seq_thm2 lambda K h_lambda hK k ≥ base_M lambda K h_lambda hK - 1 := by
              exact Nat.recOn k ( by norm_num [ m_seq_thm2 ] ) fun n ihn => by rw [ m_seq_thm2 ] ; exact le_add_of_le_of_nonneg ihn ( Nat.zero_le _ ) ;
            linarith [ show M_at lambda ( k + 1 ) > 0 from M_at_pos lambda h_lambda ( k + 1 ) ( by linarith ) ];
          · rw [ show k_of_index_thm2 lambda K h_lambda hK ( m_seq_thm2 lambda K h_lambda hK k + M_at lambda ( k + 1 ) ) = k + 1 from ?_ ] ; simp +decide ; ring_nf;
            unfold k_of_index_thm2; simp +decide [add_comm] ;
            split_ifs <;> simp +decide [ Nat.find_eq_iff ] at *;
            · grind;
            · exact ⟨ by rw [ show m_seq_thm2 lambda K h_lambda hK ( k + 1 ) = m_seq_thm2 lambda K h_lambda hK k + M_at lambda ( k + 1 ) from rfl ], fun n hn => lt_of_le_of_lt ( m_seq_thm2_strictMono lambda K h_lambda hK |> StrictMono.monotone <| hn ) <| Nat.lt_add_of_pos_right <| Nat.pos_of_ne_zero <| by
                                exact ne_of_gt <| M_at_pos _ h_lambda _ <| Nat.succ_pos _ ⟩;
      -- By `step_data_props`, $d_{k+1, j-m_k} \mid d_{k+1, M_{k+1}}$.
      have h_div : d_at lambda (k + 1) (j - m_seq_thm2 lambda K h_lambda hK k) ∣ d_at lambda (k + 1) (M_at lambda (k + 1)) := by
        have := step_data_props lambda h_lambda ( k + 1 );
        convert this.2.2.2.1 ( j - m_seq_thm2 lambda K h_lambda hK k ) ( Nat.sub_le_of_le_add <| by linarith [ show m_seq_thm2 lambda K h_lambda hK ( k + 1 ) = m_seq_thm2 lambda K h_lambda hK k + M_at lambda ( k + 1 ) from rfl ] ) using 1 ; aesop;
      exact h_subst.1.symm ▸ h_subst.2.symm ▸ mul_dvd_mul h_div dvd_rfl;
    · -- If $j = m_k$, then $n_{m_k} \mid n_{m_{k+1}}$ by `n_seq_thm2_div_prev_m`.
      by_cases hj : j = m_seq_thm2 lambda K h_lambda hK k ∨ j = m_seq_thm2 lambda K h_lambda hK (k + 1);
      · cases hj <;> simp_all +decide [ n_seq_thm2_div_prev_m ];
      · contrapose! hk; simp_all +decide [ not_or ] ;
        refine' le_antisymm _ _ <;> simp_all +decide [ k_of_index_thm2 ];
        · split_ifs <;> simp_all +decide ;
          exact ⟨ k + 1, le_rfl, hj₂ ⟩;
        · split_ifs <;> simp_all +decide ;
          · exact hj.1 ( le_antisymm ( by linarith [ show m_seq_thm2 lambda K h_lambda hK k ≥ base_M lambda K h_lambda hK - 1 from Nat.le_induction ( by tauto ) ( fun n hn ih => by linarith! [ m_seq_thm2_strictMono lambda K h_lambda hK <| Nat.lt_succ_self n ] ) k <| Nat.zero_le k ] ) hj₁ );
          · intro m hm; exact lt_of_le_of_lt ( m_seq_thm2_strictMono _ _ _ _ |> StrictMono.monotone <| hm ) ( lt_of_le_of_ne hj₁ <| by tauto ) ;

/-
$n_{m_k}$ is divisible by all preceding terms.
-/
lemma n_seq_thm2_div_all_prev (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) (k : ℕ) :
  ∀ j < m_seq_thm2 lambda K h_lambda hK k, n_seq_thm2 lambda K h_lambda hK j ∣ n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK k) := by
    induction' k with k ih;
    · exact fun j a => n_seq_thm2_base_div lambda K h_lambda hK j a;
    · intro j hj
      by_cases hj' : j < m_seq_thm2 lambda K h_lambda hK k;
      · exact dvd_trans ( ih j hj' ) ( n_seq_thm2_div_prev_m _ _ _ _ _ );
      · apply n_seq_thm2_div_within_block;
        · linarith;
        · linarith

/-
The cumulative product of $Q_k$ divides $n_{m_k}$.
-/
def super_Q_thm2 (k : ℕ) : ℕ := ∏ j ∈ Finset.range k, Q_seq (j + 1)

lemma super_Q_thm2_dvd_n_seq (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) (k : ℕ) :
  super_Q_thm2 k ∣ n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK k) := by
    induction' k with k ih;
    · exact one_dvd _;
    · -- By definition of $super_Q_thm2$, we have $super_Q_thm2 (k + 1) = Q_seq (k + 1) * super_Q_thm2 k$.
      have h_super_Q_succ : super_Q_thm2 (k + 1) = Q_seq (k + 1) * super_Q_thm2 k := by
        exact Finset.prod_range_succ _ _ |> Eq.trans <| by ac_rfl;
      -- By definition of $n_seq_thm2$, we have $n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK (k + 1)) = d_at lambda (k + 1) (M_at lambda (k + 1)) * n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK k)$.
      have h_n_seq_succ : n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK (k + 1)) = d_at lambda (k + 1) (M_at lambda (k + 1)) * n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK k) := by
        rw [ n_seq_thm2 ];
        split_ifs <;> simp_all +decide [ m_seq_thm2 ];
        · have h_contra : m_seq_thm2 lambda K h_lambda hK k ≥ base_M lambda K h_lambda hK - 1 := by
            exact Nat.recOn k ( by norm_num [ m_seq_thm2 ] ) fun n ihn => by rw [ m_seq_thm2 ] ; exact Nat.le_trans ihn ( Nat.le_add_right _ _ ) ;
          linarith [ show M_at lambda ( k + 1 ) > 0 from M_at_pos lambda h_lambda ( k + 1 ) ( by linarith ) ];
        · rw [ show k_of_index_thm2 lambda K h_lambda hK ( m_seq_thm2 lambda K h_lambda hK k + M_at lambda ( k + 1 ) ) = k + 1 from ?_ ] ; norm_num [ Nat.sub_sub ];
          have := k_of_index_thm2_spec_high lambda K h_lambda hK ( m_seq_thm2 lambda K h_lambda hK k + M_at lambda ( k + 1 ) ) ( by linarith );
          refine' le_antisymm _ _ <;> contrapose! this;
          · intro h;
            exact h.2.not_ge ( by exact le_trans ( by aesop ) ( show m_seq_thm2 lambda K h_lambda hK ( k + 1 ) ≤ m_seq_thm2 lambda K h_lambda hK ( k_of_index_thm2 lambda K h_lambda hK ( m_seq_thm2 lambda K h_lambda hK k + M_at lambda ( k + 1 ) ) - 1 ) from by exact monotone_nat_of_le_succ ( fun n => by exact m_seq_thm2_strictMono lambda K h_lambda hK |> StrictMono.monotone <| Nat.le_succ _ ) <| Nat.le_pred_of_lt this ) );
          · simp +zetaDelta at *;
            exact fun h => absurd h ( not_le_of_gt ( lt_of_le_of_lt ( m_seq_thm2_strictMono _ _ _ _ |> StrictMono.monotone <| this ) <| Nat.lt_add_of_pos_right <| Nat.pos_of_ne_zero <| by
              exact ne_of_gt ( M_at_pos _ h_lambda _ ( Nat.succ_pos _ ) ) ) );
      -- By definition of $d_at$, we know that $Q_seq (k + 1)$ divides $d_at lambda (k + 1) (M_at lambda (k + 1))$.
      have h_d_at_div : Q_seq (k + 1) ∣ d_at lambda (k + 1) (M_at lambda (k + 1)) := by
        have := step_data_props lambda h_lambda ( k + 1 ) ; aesop;
      exact h_super_Q_succ.symm ▸ h_n_seq_succ.symm ▸ mul_dvd_mul h_d_at_div ih

/-
Every positive integer divides `super_Q_thm2 k` for some $k$.
-/
lemma q_dvd_super_Q_thm2 (q : ℕ) (hq : q > 0) : ∃ k, q ∣ super_Q_thm2 k := by
  have := @q_dvd_super_Q;
  exact this q hq

/-
Every positive integer divides some term of the sequence $n_i$.
-/
lemma n_seq_thm2_div_every_nat (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) (q : ℕ) (hq : q > 0) :
  ∃ i, q ∣ n_seq_thm2 lambda K h_lambda hK i := by
    -- By `q_dvd_super_Q`, there exists $k$ such that $q \mid \text{super\_Q } k$.
    obtain ⟨k, hk⟩ : ∃ k, q ∣ super_Q_thm2 k := q_dvd_super_Q_thm2 q hq;
    use m_seq_thm2 lambda K h_lambda hK k;
    exact dvd_trans hk (super_Q_thm2_dvd_n_seq lambda K h_lambda hK k);

/-
The sequence $n_i$ satisfies the inequality condition for filling intervals.
-/
lemma n_seq_thm2_ineq (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) :
  (∀ i < m_seq_thm2 lambda K h_lambda hK 0, (1 : ℝ) / n_seq_thm2 lambda K h_lambda hK i ≤ (∑ j ∈ Finset.Ioc i (m_seq_thm2 lambda K h_lambda hK 0), (1 : ℝ) / n_seq_thm2 lambda K h_lambda hK j) + (1 : ℝ) / n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK 0)) ∧
  (∀ k : ℕ, ∀ i, m_seq_thm2 lambda K h_lambda hK k ≤ i → i < m_seq_thm2 lambda K h_lambda hK (k + 1) →
    (1 : ℝ) / n_seq_thm2 lambda K h_lambda hK i ≤ (∑ j ∈ Finset.Ioc i (m_seq_thm2 lambda K h_lambda hK (k + 1)), (1 : ℝ) / n_seq_thm2 lambda K h_lambda hK j) + (1 : ℝ) / n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK (k + 1))) := by
      apply And.intro;
      · intro i hi
        have h_ineq : (n_seq_thm2 lambda K h_lambda hK (i + 1) : ℝ) ≤ 2 * (n_seq_thm2 lambda K h_lambda hK i : ℝ) := by
          have := n_seq_thm2_growth lambda K h_lambda hK i; rw [ div_le_iff₀ ( Nat.cast_pos.mpr <| n_seq_thm2_pos _ _ _ _ _ ) ] at this; linarith;
        have h_ineq : (1 : ℝ) / (n_seq_thm2 lambda K h_lambda hK i) ≤ (∑ j ∈ Finset.Ioc i (m_seq_thm2 lambda K h_lambda hK 0), (1 : ℝ) / (n_seq_thm2 lambda K h_lambda hK j)) + (1 : ℝ) / (n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK 0)) := by
          have := remark_cond (fun j => n_seq_thm2 lambda K h_lambda hK j) (m_seq_thm2 lambda K h_lambda hK 0)
          apply this (fun i => n_seq_thm2_pos lambda K h_lambda hK i) (fun i => by
            have := n_seq_thm2_growth lambda K h_lambda hK i; rw [ div_le_iff₀, le_div_iff₀ ] at this <;> norm_cast at * <;> linarith [ n_seq_thm2_pos lambda K h_lambda hK i, n_seq_thm2_pos lambda K h_lambda hK ( i + 1 ) ] ;) i hi;
        convert h_ineq using 1;
      · intro k i hi₁ hi₂; rw [ div_le_iff₀ ];
        · -- Since $n_{i+1} \leq 2n_i$, we have $\frac{1}{n_i} \leq \sum_{j=i+1}^M \frac{1}{n_j} + \frac{1}{n_M}$.
          have h_ineq : (1 : ℝ) / n_seq_thm2 lambda K h_lambda hK i ≤ (∑ j ∈ Finset.Ioc i (m_seq_thm2 lambda K h_lambda hK (k + 1)), (1 : ℝ) / n_seq_thm2 lambda K h_lambda hK j) + (1 : ℝ) / n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK (k + 1)) := by
            have h_ratio : (n_seq_thm2 lambda K h_lambda hK (i + 1) : ℝ) / n_seq_thm2 lambda K h_lambda hK i ≤ 2 := by
              exact n_seq_thm2_growth lambda K h_lambda hK i |>.2
            have h_ineq : (1 : ℝ) / n_seq_thm2 lambda K h_lambda hK i ≤ (∑ j ∈ Finset.Ioc i (m_seq_thm2 lambda K h_lambda hK (k + 1)), (1 : ℝ) / n_seq_thm2 lambda K h_lambda hK j) + (1 : ℝ) / n_seq_thm2 lambda K h_lambda hK (m_seq_thm2 lambda K h_lambda hK (k + 1)) := by
              have := remark_cond (fun i => n_seq_thm2 lambda K h_lambda hK i) (m_seq_thm2 lambda K h_lambda hK (k + 1)) (fun i => n_seq_thm2_pos lambda K h_lambda hK i) (fun i => by
                have := n_seq_thm2_growth lambda K h_lambda hK i; rw [ div_le_iff₀ ] at this <;> norm_cast at * <;> linarith [ n_seq_thm2_pos lambda K h_lambda hK i ] ;) i (by
              linarith)
              convert this using 1
            generalize_proofs at *; (
            convert h_ineq using 1);
          rwa [ div_le_iff₀ ( Nat.cast_pos.mpr <| n_seq_thm2_pos _ _ _ _ _ ) ] at h_ineq;
        · exact_mod_cast n_seq_thm2_pos _ _ _ _ _

/-
The sequence $n_i$ fills the target interval with rational sums.
-/
lemma n_seq_thm2_fills (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) :
  SubsetSums (fun i => (1 : ℝ) / n_seq_thm2 lambda K h_lambda hK i) =
    (TargetInterval (fun i => (1 : ℝ) / n_seq_thm2 lambda K h_lambda hK i)) ∩ {x | ∃ q : ℚ, x = q} := by
      convert prop_general _ _ _ _ _ _ _ _ _ using 1 <;> norm_num [ * ];
      exact m_seq_thm2 lambda K h_lambda hK
      generalize_proofs at *; (
      exact fun i => n_seq_thm2_pos lambda K h_lambda hK i);
      exact n_seq_thm2_strictMono lambda K h_lambda hK;
      · exact m_seq_thm2_strictMono lambda K h_lambda hK;
      · exact fun k a => n_seq_thm2_div_every_nat lambda K h_lambda hK k a;
      · exact fun k j a => n_seq_thm2_div_all_prev lambda K h_lambda hK k j a;
      · exact fun i hi => by simpa using n_seq_thm2_ineq lambda K h_lambda hK |>.1 i hi;
      · intro k i hi₁ hi₂; have := n_seq_thm2_ineq lambda K h_lambda hK; aesop;

/-
The sequence $1/n_i$ is summable.
-/
lemma n_seq_thm2_summable (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) :
  Summable (fun i => (1 : ℝ) / n_seq_thm2 lambda K h_lambda hK i) := by
    -- We'll use the comparison test. Since \( \frac{1}{n_i} \leq \frac{1}{\lambda^i} \), and \( \sum_{i=0}^{\infty} \frac{1}{\lambda^i} \) converges.
    have h_le : ∀ i, (1 : ℝ) / n_seq_thm2 lambda K h_lambda hK i ≤ 1 / lambda ^ i := by
      intro i
      have h_ge : n_seq_thm2 lambda K h_lambda hK i ≥ lambda ^ i := by
        induction' i with i ih <;> norm_num [ *, pow_succ' ] at *;
        · exact n_seq_thm2_pos _ _ _ _ _;
        · have := n_seq_thm2_growth lambda K h_lambda hK i; rw [ le_div_iff₀ ( Nat.cast_pos.mpr <| n_seq_thm2_pos _ _ _ _ _ ) ] at this; nlinarith;
      exact (by
      exact one_div_le_one_div_of_le ( pow_pos ( zero_lt_one.trans h_lambda.1 ) _ ) h_ge);
    exact Summable.of_nonneg_of_le ( fun i => by positivity ) h_le ( by simpa using summable_geometric_of_lt_one ( by norm_num; linarith ) ( inv_lt_one_of_one_lt₀ h_lambda.1 ) )

/-
The sequence $1/a_i$ is summable.
-/
lemma a_seq_summable (lambda : ℝ) (h_lambda : 1 < lambda) :
  Summable (fun i => (1 : ℝ) / a_seq lambda i) := by
    -- We know $a_{i+1} \geq \lambda a_i$. Since $a_0 = 1$, we have $a_i \geq \lambda^i$.
    have h_ai_ge : ∀ i, (a_seq lambda i : ℝ) ≥ lambda ^ i := by
      intro i
      induction' i with i ih
      · simp [a_seq];
      rw [ pow_succ' ];
      exact le_trans ( mul_le_mul_of_nonneg_left ih <| by positivity ) ( Nat.le_ceil _ );
    exact Summable.of_nonneg_of_le ( fun i => one_div_nonneg.2 <| Nat.cast_nonneg _ ) ( fun i => one_div_le_one_div_of_le ( by positivity ) <| h_ai_ge i ) <| by simpa using summable_geometric_of_lt_one ( by positivity ) <| inv_lt_one_of_one_lt₀ h_lambda;

/-
Properties of `base_M` and `base_n`.
-/
lemma base_data_props (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) :
  let M := base_M lambda K h_lambda hK
  let n' := base_n lambda K h_lambda hK
  M ≥ K ∧
  (∀ i < K, n' i = a_seq lambda i) ∧
  1 ∣ n' (M - 1) ∧
  (∀ i < M, n' i ∣ n' (M - 1)) ∧
  StrictMonoOn n' (Set.Icc 0 (M - 1)) ∧
  (∀ j, K - 1 ≤ j → j < M - 1 → lambda ≤ (n' (j + 1) : ℝ) / n' j ∧ (n' (j + 1) : ℝ) / n' j ≤ 2) := by
    have := Classical.choose_spec (lm_divisors2 lambda 1 K (a_seq lambda) h_lambda (by
    decide +revert) hK (by
    exact fun i hi j hj hij => a_seq_strictMono _ h_lambda.1 hij) (by
    exact fun i hi => a_seq_pos _ h_lambda.1 i |> Nat.cast_pos.mp |> fun h => by simpa using h;));
    convert this using 1;
    constructor <;> intro h;
    · exact this.2;
    · convert Classical.choose_spec h using 1

/-
`n_seq_thm2` agrees with `a_seq` for `i < K`.
-/
lemma n_seq_thm2_eq_a_seq (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) (i : ℕ) (hi : i < K) :
  n_seq_thm2 lambda K h_lambda hK i = a_seq lambda i := by
    convert base_data_props lambda K h_lambda hK |>.2.1 i hi using 1;
    rw [ n_seq_thm2_eq_base ];
    exact Nat.le_sub_one_of_lt ( lt_of_lt_of_le hi ( base_data_props _ _ _ _ |>.1 ) )

/-
The sum of reciprocals of `n_seq_thm2` is at least the partial sum of reciprocals of `a_seq`.
-/
lemma n_seq_thm2_sum_ge (lambda : ℝ) (K : ℕ) (h_lambda : 1 < lambda ∧ lambda < 2) (hK : K ≥ 1) :
  ∑' i, (1 : ℝ) / n_seq_thm2 lambda K h_lambda hK i ≥ ∑ i ∈ Finset.range K, (1 : ℝ) / a_seq lambda i := by
    -- Since $n_i = a_i$ for $i < K$, we can replace the sum over $i < K$ with the sum of reciprocals of $a_i$.
    have h_sum_eq : ∑ i ∈ Finset.range K, (1 : ℝ) / n_seq_thm2 lambda K h_lambda hK i = ∑ i ∈ Finset.range K, (1 : ℝ) / a_seq lambda i := by
      exact Finset.sum_congr rfl fun i hi => by rw [ n_seq_thm2_eq_a_seq _ _ _ _ _ ( Finset.mem_range.mp hi ) ] ;
    refine' h_sum_eq ▸ Summable.sum_le_tsum _ _ _;
    · exact fun _ _ => by positivity;
    · exact n_seq_thm2_summable lambda K h_lambda hK

/-
$R(\lambda) \ge \sum_{i=0}^{K-1} 1/a_i$.
-/
lemma R_lambda_ge_partial_sum (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) (K : ℕ) (hK : K ≥ 1) :
  R_lambda lambda ≥ ∑ i ∈ Finset.range K, (1 : ℝ) / a_seq lambda i := by
    refine' le_trans ( n_seq_thm2_sum_ge _ _ _ _ ) _;
    grind;
    grind +ring;
    refine' le_csSup _ _ <;> norm_num +zetaDelta at *;
    · -- Since any interval filled by the sequence must be within the interval [0, S], the length of such an interval can't exceed S. Therefore, S is an upper bound for the set of lengths.
      have h_upper_bound : ∀ alpha beta, FillsInterval lambda alpha beta → beta - alpha ≤ ∑' i, (1 : ℝ) / a_seq lambda i := by
        intros alpha beta h_fills
        obtain ⟨n, hn_pos, hn_lac, hn_subset⟩ := h_fills
        have h_sum_le : ∀ s ∈ SubsetSums (fun i => (1 : ℝ) / n i), s ≤ ∑' i, (1 : ℝ) / a_seq lambda i := by
          intros s hs
          obtain ⟨t, ht⟩ := hs
          have h_sum_le : ∑ i ∈ t, (1 : ℝ) / n i ≤ ∑' i, (1 : ℝ) / a_seq lambda i := by
            have h_sum_le : ∀ i, (1 : ℝ) / n i ≤ (1 : ℝ) / a_seq lambda i := by
              exact fun i => one_div_le_one_div_of_le ( Nat.cast_pos.mpr ( a_seq_pos _ h_lambda.1 _ ) ) ( mod_cast n_ge_a_seq _ _ h_lambda.1 hn_pos hn_lac _ ) ;
            generalize_proofs at *; (
            exact le_trans ( Finset.sum_le_sum fun _ _ => h_sum_le _ ) ( Summable.sum_le_tsum _ ( fun _ _ => by positivity ) ( by exact a_seq_summable _ h_lambda.1 ) ) |> le_trans <| by norm_num;)
          generalize_proofs at *; (
          grind +ring)
        generalize_proofs at *; (
        have h_interval_subset : Set.Ioo alpha beta ∩ {x | ∃ q : ℚ, x = q} ⊆ Set.Icc 0 (∑' i, (1 : ℝ) / a_seq lambda i) := by
          exact fun x hx => ⟨ by rcases hn_subset hx with ⟨ t, rfl ⟩ ; exact Finset.sum_nonneg fun _ _ => by positivity, h_sum_le x ( hn_subset hx ) ⟩ ;
        generalize_proofs at *; (
        by_cases h : alpha < beta <;> simp_all +decide [ Set.subset_def ];
        · -- Since the interval (alpha, beta) is contained within [0, S], we have beta ≤ S.
          have h_beta_le_S : beta ≤ ∑' i, (1 : ℝ) / a_seq lambda i := by
            have h_beta_le_S : ∀ x ∈ Set.Ioo alpha beta, x ≤ ∑' i, (1 : ℝ) / a_seq lambda i := by
              intros x hx
              generalize_proofs at *; (
              -- Since $x$ is in the interval $(\alpha, \beta)$, we can find a rational number $q$ such that $x < q < \beta$.
              obtain ⟨q, hq⟩ : ∃ q : ℚ, x < q ∧ q < beta := by
                exact exists_rat_btwn hx.2 |> fun ⟨ q, hq₁, hq₂ ⟩ => ⟨ q, hq₁, hq₂ ⟩
              generalize_proofs at *; (
              have := h_interval_subset q ( by linarith [ hx.1 ] ) ( by linarith [ hx.2 ] ) q rfl; norm_num at *; linarith;))
            generalize_proofs at *; (
            contrapose! h_beta_le_S
            generalize_proofs at *; (
            by_cases h₂ : alpha < ∑' i, (1 : ℝ) / a_seq lambda i <;> simp_all +decide ; (
            exact ⟨ ( ∑' i : ℕ, ( a_seq lambda i : ℝ ) ⁻¹ + beta ) / 2, ⟨ by linarith, by linarith ⟩, by linarith ⟩);
            exact ⟨ ( alpha + beta ) / 2, ⟨ by linarith, by linarith ⟩, by linarith ⟩))
          generalize_proofs at *; (
          by_cases h_alpha_neg : alpha < 0 <;> simp_all +decide;
          · contrapose! h_interval_subset;
            -- Since $\alpha < 0$, we can choose a negative rational number $x$ such that $\alpha < x < \min(\beta, 0)$.
            obtain ⟨x, hx₁, hx₂⟩ : ∃ x : ℚ, alpha < x ∧ x < min beta 0 := by
              exact exists_rat_btwn ( lt_min h ( by linarith ) ) |> fun ⟨ x, hx₁, hx₂ ⟩ => ⟨ x, hx₁, hx₂ ⟩ ;
            generalize_proofs at *; (
            exact ⟨ x, hx₁, hx₂.trans_le ( min_le_left _ _ ), x, rfl, fun hx₃ => by linarith [ show ( x : ℝ ) ≥ 0 by exact_mod_cast hx₃, min_le_right beta 0 ] ⟩);
          · linarith [ h_sum_le _ ( show ( 0 : ℝ ) ∈ SubsetSums ( fun i => ( n i : ℝ ) ⁻¹ ) from ⟨ ∅, by norm_num ⟩ ) ]);
        · exact le_add_of_nonneg_of_le ( tsum_nonneg fun _ => inv_nonneg.2 ( Nat.cast_nonneg _ ) ) h))
      generalize_proofs at *; (
      exact ⟨ _, by rintro x ⟨ alpha, beta, rfl, h ⟩ ; exact h_upper_bound alpha beta h ⟩);
    · use 0, ∑' i, (1 : ℝ) / n_seq_thm2 lambda K h_lambda hK i, by
        grind
      generalize_proofs at *;
      use fun i => n_seq_thm2 lambda K h_lambda hK i
      generalize_proofs at *;
      refine' ⟨ _, _, _ ⟩
      all_goals generalize_proofs at *;
      · exact fun i => n_seq_thm2_pos _ _ _ _ _;
      · exact fun i => n_seq_thm2_growth _ _ _ _ _ |>.1.trans' ( by norm_num ) |> le_trans <| le_rfl;
      · have := n_seq_thm2_fills lambda K h_lambda hK
        generalize_proofs at *;
        simp_all +decide [ TargetInterval ] ; (
        grind)

/-
$R(\lambda) \ge \sum_{i=0}^\infty 1/a_i$.
-/
lemma R_lambda_ge (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  R_lambda lambda ≥ ∑' i, (1 : ℝ) / a_seq lambda i := by
    -- Apply the fact that if the partial sums are bounded above by $R(\lambda)$, then the infinite sum is also bounded above by $R(\lambda)$.
    have h_partial_sums_bounded : ∀ K : ℕ, ∑ i ∈ Finset.range K, (1 : ℝ) / a_seq lambda i ≤ R_lambda lambda := by
      intro K; exact (by
      have := @R_lambda_ge_partial_sum lambda h_lambda ( K + 1 ) ( by linarith ) ; simp_all +decide [ Finset.sum_range_succ ] ;
      exact le_trans ( le_add_of_nonneg_right <| by positivity ) this);
    exact le_of_tendsto_of_tendsto' ( Summable.hasSum ( a_seq_summable _ h_lambda.1 ) |> HasSum.tendsto_sum_nat ) tendsto_const_nhds h_partial_sums_bounded |> le_trans ( by norm_num ) ;

/-
Existence of $\varepsilon$ for Theorem 3.
-/
lemma exists_epsilon_thm3 (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) :
  ∃ epsilon ∈ Set.Ioo 0 1, lambda + epsilon < 2 ∧ 1 / (lambda + epsilon) + 1 / (Lambda + epsilon) > 1 := by
    -- By continuity of $x \mapsto 1/x$, we can find $\varepsilon > 0$ small enough such that the strict inequality is preserved.
    obtain ⟨epsilon, hepsilon⟩ : ∃ epsilon > 0, epsilon < 1 ∧ lambda + epsilon < 2 ∧ (1 / (lambda + epsilon)) + (1 / (Lambda + epsilon)) > 1 := by
      -- By continuity of $x \mapsto 1/x$, we can find $\varepsilon > 0$ small enough such that the strict inequality is preserved. Let's choose $\epsilon$ such that $0 < \epsilon < \min(1, 2 - \lambda)$.
      obtain ⟨epsilon, hepsilon_pos, hepsilon_lt⟩ : ∃ epsilon > 0, epsilon < min 1 (2 - lambda) ∧ (1 / (lambda + epsilon)) + (1 / (Lambda + epsilon)) > 1 := by
        have h_cont : Filter.Tendsto (fun epsilon : ℝ => (1 / (lambda + epsilon)) + (1 / (Lambda + epsilon))) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((1 / lambda) + (1 / Lambda))) := by
          exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.div ( tendsto_const_nhds.add ( Filter.tendsto_id.mono_left inf_le_left ) ) ( by linarith ) ) ( tendsto_const_nhds.div ( tendsto_const_nhds.add ( Filter.tendsto_id.mono_left inf_le_left ) ) ( by linarith ) ) ) ( by norm_num );
        have := h_cont.eventually ( lt_mem_nhds <| show 1 / lambda + 1 / Lambda > 1 from ?_ ) ; have := this.and ( Ioo_mem_nhdsGT <| show 0 < Min.min 1 ( 2 -lambda ) from ?_ ) ; ( have := this.exists; aesop; );
        · exact lt_min zero_lt_one ( by rw [ lt_div_iff₀ ] at h_lambda <;> nlinarith );
        · rw [ lt_div_iff₀ ] at h_lambda <;> norm_num at * <;> nlinarith [ inv_pos.2 ( by linarith : 0 < lambda ), inv_pos.2 ( by linarith : 0 < Lambda ), mul_inv_cancel₀ ( ne_of_gt ( by linarith : 0 < lambda ) ), mul_inv_cancel₀ ( ne_of_gt ( by linarith : 0 < Lambda ) ) ] ;
      exact ⟨ epsilon, hepsilon_pos, lt_of_lt_of_le hepsilon_lt.1 ( min_le_left _ _ ), by linarith [ min_le_right 1 ( 2 -lambda ) ], hepsilon_lt.2 ⟩;
    aesop

/-
Existence of $U$ for Theorem 3.
-/
lemma exists_U_thm3 (Lambda : ℝ) (lambda : ℝ) (epsilon : ℝ)
  (h_Lambda : Lambda ≥ 2)
  (h_lambda : 1 < lambda)
  (h_epsilon : epsilon > 0)
  (h_sum_gt_one : 1 / (lambda + epsilon) + 1 / (Lambda + epsilon) > 1) :
  ∃ U : ℕ, (lambda + epsilon) ^ (-(U : ℤ) - 1) < (Lambda + epsilon) * (1 / (lambda + epsilon) + 1 / (Lambda + epsilon) - 1) := by
    -- Since $\lambda > 1$ and $\varepsilon > 0$, we have $0 < 1 / (\lambda + \varepsilon) < 1$.
    have h_frac : 0 < 1 / (lambda + epsilon) ∧ 1 / (lambda + epsilon) < 1 := by
      exact ⟨ by positivity, by rw [ div_lt_iff₀ ] <;> linarith ⟩;
    -- Since $0 < 1 / (\lambda + \varepsilon) < 1$, the sequence $(1 / (\lambda + \varepsilon))^n$ tends to $0$ as $n \to \infty$.
    have h_seq_zero : Filter.Tendsto (fun n : ℕ => (1 / (lambda + epsilon)) ^ n) Filter.atTop (nhds 0) := by
      exact tendsto_pow_atTop_nhds_zero_of_lt_one h_frac.1.le h_frac.2
    generalize_proofs at *; (
    -- Since $(1 / (\lambda + \varepsilon))^n$ tends to $0$ as $n \to \infty$, there exists $U$ such that $(1 / (\lambda + \varepsilon))^{U+1} < C$.
    obtain ⟨U, hU⟩ : ∃ U : ℕ, (1 / (lambda + epsilon)) ^ (U + 1) < (Lambda + epsilon) * ((1 / (lambda + epsilon)) + (1 / (Lambda + epsilon)) - 1) := by
      exact ( h_seq_zero.comp ( Filter.tendsto_add_atTop_nat 1 ) ) |> fun h => h.eventually ( gt_mem_nhds <| mul_pos ( by linarith ) <| sub_pos.mpr h_sum_gt_one ) |> fun h => h.exists
    generalize_proofs at *; (
    exact ⟨ U, by convert hU using 1 ; group ⟩ ;))

/-
Definitions of constants $\varepsilon, U, m_0$ for Theorem 3.
-/
def epsilon_thm3 (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) : ℝ :=
  Classical.choose (exists_epsilon_thm3 Lambda lambda h_Lambda h_lambda)

lemma epsilon_thm3_spec (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) :
  let epsilon := epsilon_thm3 Lambda lambda h_Lambda h_lambda
  epsilon ∈ Set.Ioo 0 1 ∧ lambda + epsilon < 2 ∧ 1 / (lambda + epsilon) + 1 / (Lambda + epsilon) > 1 :=
  Classical.choose_spec (exists_epsilon_thm3 Lambda lambda h_Lambda h_lambda)

def U_thm3 (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) : ℕ :=
  let epsilon := epsilon_thm3 Lambda lambda h_Lambda h_lambda
  let h_spec := epsilon_thm3_spec Lambda lambda h_Lambda h_lambda
  Classical.choose (exists_U_thm3 Lambda lambda epsilon h_Lambda h_lambda.1 h_spec.1.1 h_spec.2.2)

lemma U_thm3_spec (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) :
  let epsilon := epsilon_thm3 Lambda lambda h_Lambda h_lambda
  let U := U_thm3 Lambda lambda h_Lambda h_lambda
  (lambda + epsilon) ^ (-(U : ℤ) - 1) < (Lambda + epsilon) * (1 / (lambda + epsilon) + 1 / (Lambda + epsilon) - 1) :=
  let epsilon := epsilon_thm3 Lambda lambda h_Lambda h_lambda
  let h_spec := epsilon_thm3_spec Lambda lambda h_Lambda h_lambda
  Classical.choose_spec (exists_U_thm3 Lambda lambda epsilon h_Lambda h_lambda.1 h_spec.1.1 h_spec.2.2)

def m0_thm3 (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) : ℕ :=
  let epsilon := epsilon_thm3 Lambda lambda h_Lambda h_lambda
  2 + Nat.floor (Real.logb 2 (1 / epsilon))

/-
Definitions for the jump and geometric extension.
-/
def jump_val (Lambda : ℝ) (val : ℕ) : ℕ := Nat.floor (Lambda * val) + 1

def geo_seq (lambda : ℝ) (start_val : ℕ) : ℕ → ℕ
| 0 => start_val
| (j + 1) => Nat.ceil (lambda * geo_seq lambda start_val j)

def extend_temp (Lambda : ℝ) (lambda : ℝ) (_U : ℕ) (m_prev : ℕ) (n_prev : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < m_prev then n_prev i
  else
    let jump := jump_val Lambda (n_prev (m_prev - 1))
    let j := i - m_prev
    geo_seq lambda jump j

/-
Properties of `extend_temp`.
-/
lemma extend_temp_props (Lambda : ℝ) (lambda : ℝ) (U : ℕ) (m_prev : ℕ) (n_prev : ℕ → ℕ)
  (h_Lambda : Lambda ≥ 2)
  (h_lambda : 1 < lambda)
  (h_m_prev : m_prev ≥ 1)
  (h_n_prev_pos : ∀ i < m_prev, 0 < n_prev i)
  (h_n_prev_mono : StrictMonoOn n_prev (Set.Icc 0 (m_prev - 1))) :
  let n_temp := extend_temp Lambda lambda U m_prev n_prev
  let K := m_prev + 1 + U
  (∀ i < m_prev, n_temp i = n_prev i) ∧
  (∀ i < K, 0 < n_temp i) ∧
  StrictMonoOn n_temp (Set.Icc 0 (K - 1)) := by
    have h_geo_seq_strict_mono : StrictMono (fun j => geo_seq lambda (jump_val Lambda (n_prev (m_prev - 1)) ) j) := by
      refine' strictMono_nat_of_lt_succ fun j => _;
      exact Nat.lt_ceil.mpr ( lt_mul_of_one_lt_left ( Nat.cast_pos.mpr <| show 0 < geo_seq lambda ( jump_val Lambda ( n_prev ( m_prev - 1 ) ) ) j from Nat.recOn j ( Nat.cast_pos.mpr <| show 0 < jump_val Lambda ( n_prev ( m_prev - 1 ) ) from Nat.succ_pos _ ) fun j ih => Nat.ceil_pos.mpr <| mul_pos ( by linarith ) <| Nat.cast_pos.mpr ih ) h_lambda );
    refine' ⟨ _, _, _ ⟩;
    · unfold extend_temp; aesop;
    · intro i hi; by_cases hi' : i < m_prev <;> simp_all +decide [ extend_temp ] ;
      split_ifs <;> simp_all +decide;
      exact Nat.recOn ( i - m_prev ) ( Nat.succ_pos _ ) fun j ih => Nat.ceil_pos.mpr ( mul_pos ( zero_lt_one.trans h_lambda ) ( Nat.cast_pos.mpr ih ) );
    · intro i hi j hj hij;
      by_cases hi' : i < m_prev <;> by_cases hj' : j < m_prev <;> simp_all +decide [ extend_temp ];
      · exact h_n_prev_mono ⟨ by linarith, by omega ⟩ ⟨ by linarith, by omega ⟩ hij;
      · split_ifs <;> try linarith;
        refine' lt_of_lt_of_le _ ( h_geo_seq_strict_mono.monotone ( Nat.zero_le _ ) );
        refine' lt_of_le_of_lt _ ( show jump_val Lambda ( n_prev ( m_prev - 1 ) ) > n_prev ( m_prev - 1 ) from _ );
        · exact h_n_prev_mono.le_iff_le ( by constructor <;> omega ) ( by constructor <;> omega ) |>.2 ( by omega );
        · exact Nat.lt_succ_of_le ( Nat.le_floor <| by nlinarith [ show ( n_prev ( m_prev - 1 ) : ℝ ) ≥ 1 by exact_mod_cast h_n_prev_pos _ ( Nat.sub_lt h_m_prev zero_lt_one ) ] );
      · linarith;
      · rw [ if_neg ( by linarith ), if_neg ( by linarith ) ] ; exact h_geo_seq_strict_mono ( by omega ) ;

/-
$\lambda < 2$ given the conditions.
-/
lemma lambda_lt_two (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : lambda < Lambda / (Lambda - 1)) : lambda < 2 := by
  exact h_lambda.trans_le ( by rw [ div_le_iff₀ ] <;> linarith )

/-
Definition of `Thm3Data` and `init_thm3_data`.
-/
structure Thm3Data (Lambda : ℝ) (lambda : ℝ) where
  m : ℕ
  n : ℕ → ℕ
  h_m : m ≥ 1
  h_pos : ∀ i < m, 0 < n i
  h_mono : StrictMonoOn n (Set.Icc 0 (m - 1))

noncomputable def init_thm3_data (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) : Thm3Data Lambda lambda :=
  let m0 := m0_thm3 Lambda lambda h_Lambda h_lambda
  let n0 := fun i => 2 ^ i
  { m := m0
    n := n0
    h_m := by
      dsimp [m0, m0_thm3]
      linarith [Nat.zero_le (Nat.floor (Real.logb 2 (1 / epsilon_thm3 Lambda lambda h_Lambda h_lambda)))]
    h_pos := fun i _ => pow_pos (by norm_num) i
    h_mono := fun i hi j hj hij => by
      dsimp [n0]
      exact Nat.pow_lt_pow_right (by norm_num) hij
  }

/-
$2^{m_0-1} > 1/\epsilon$.
-/
lemma two_pow_m0_sub_one_gt_one_div_epsilon (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) :
  let epsilon := epsilon_thm3 Lambda lambda h_Lambda h_lambda
  let m0 := m0_thm3 Lambda lambda h_Lambda h_lambda
  (2 : ℝ) ^ (m0 - 1) > 1 / epsilon := by
    norm_num [ m0_thm3 ] at *;
    rw [ ← Real.log_lt_log_iff ( inv_pos.mpr <| epsilon_thm3_spec Lambda lambda h_Lambda h_lambda |>.1 |>.1 ) ( by positivity ), Real.log_inv ] ; norm_num [ Real.log_rpow ];
    have := Nat.lt_floor_add_one ( -Real.logb 2 ( epsilon_thm3 Lambda lambda h_Lambda h_lambda ) ) ; rw [ Real.logb ] at * ; ( rw [ div_eq_mul_inv ] at * ; nlinarith [ inv_pos.mpr ( Real.log_pos one_lt_two ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos one_lt_two ) ) ] ; )

/-
Stronger version of Lemma 5.
-/
lemma lm_divisors2_strong (lambda : ℝ) (Q : ℕ) (K : ℕ) (n : ℕ → ℕ)
  (h_lambda : 1 < lambda ∧ lambda < 2)
  (h_Q_pos : 0 < Q)
  (h_K : K ≥ 1)
  (h_n_mono : StrictMonoOn n (Set.Icc 0 (K - 1)))
  (h_n_pos : ∀ i < K, 0 < n i) :
  ∃ M ≥ K, ∃ n' : ℕ → ℕ,
    (∀ i < K, n' i = n i) ∧
    (n (K - 1) * Q) ∣ n' (M - 1) ∧
    (∀ i < M, n' i ∣ n' (M - 1)) ∧
    StrictMonoOn n' (Set.Icc 0 (M - 1)) ∧
    (∀ j, K - 1 ≤ j → j < M - 1 → lambda ≤ (n' (j + 1) : ℝ) / n' j ∧ (n' (j + 1) : ℝ) / n' j ≤ 2) := by
      have := @lm_divisors2
      generalize_proofs at *; (
      contrapose! this with h_contra
      generalize_proofs at *; (
      exact ⟨lambda, n (K - 1) * Q, K, n, h_lambda, Nat.mul_pos (h_n_pos (K - 1) (Nat.sub_lt h_K zero_lt_one)) h_Q_pos, h_K, h_n_mono, h_n_pos, fun x hx x_1 hx_1 hx_2 hx_3 hx_4 => by obtain ⟨ j, hj₁, hj₂, hj₃ ⟩ := h_contra x hx x_1 hx_1 hx_2 hx_3 hx_4; exact ⟨ j, hj₁, hj₂, hj₃ ⟩⟩;))

/-
The cumulative product of primorials is eventually divisible by any positive integer.
-/
def super_Q_strong (k : ℕ) : ℕ := ∏ j ∈ Finset.range k, Q_seq (j + 1)

lemma q_dvd_super_Q_strong (q : ℕ) (hq : q > 0) : ∃ k, q ∣ super_Q_strong k := by
  exact q_dvd_super_Q_thm2 q hq

/-
Definition of `step_thm3_strong_v2` with stronger divisibility requirement, and its properties.
-/
noncomputable def step_thm3_strong_v2 (Lambda : ℝ) (lambda : ℝ) (U : ℕ) (k : ℕ) (m_prev : ℕ) (n_prev : ℕ → ℕ)
  (h_Lambda : Lambda ≥ 2)
  (h_lambda : 1 < lambda ∧ lambda < 2)
  (h_m_prev : m_prev ≥ 1)
  (h_n_prev_pos : ∀ i < m_prev, 0 < n_prev i)
  (h_n_prev_mono : StrictMonoOn n_prev (Set.Icc 0 (m_prev - 1))) :
  ℕ × (ℕ → ℕ) :=
  let n_temp := extend_temp Lambda lambda U m_prev n_prev
  let K := m_prev + 1 + U
  let Q := Q_seq (k + 1) * n_prev (m_prev - 1)
  let h_temp_props := extend_temp_props Lambda lambda U m_prev n_prev h_Lambda h_lambda.1 h_m_prev h_n_prev_pos h_n_prev_mono
  let ex := lm_divisors2_strong lambda Q K n_temp h_lambda (mul_pos (Q_seq_pos (k + 1) (by omega)) (h_n_prev_pos (m_prev - 1) (by omega))) (by omega) h_temp_props.2.2 h_temp_props.2.1
  let M := Classical.choose ex
  let spec := Classical.choose_spec ex
  let n_next := Classical.choose spec.2
  (M, n_next)

lemma step_thm3_strong_v2_props (Lambda : ℝ) (lambda : ℝ) (U : ℕ) (k : ℕ) (m_prev : ℕ) (n_prev : ℕ → ℕ)
  (h_Lambda : Lambda ≥ 2)
  (h_lambda : 1 < lambda ∧ lambda < 2)
  (h_m_prev : m_prev ≥ 1)
  (h_n_prev_pos : ∀ i < m_prev, 0 < n_prev i)
  (h_n_prev_mono : StrictMonoOn n_prev (Set.Icc 0 (m_prev - 1))) :
  let res := step_thm3_strong_v2 Lambda lambda U k m_prev n_prev h_Lambda h_lambda h_m_prev h_n_prev_pos h_n_prev_mono
  let m_next := res.1
  let n_next := res.2
  let K := m_prev + 1 + U
  let Q := Q_seq (k + 1) * n_prev (m_prev - 1)
  m_next ≥ K ∧
  (∀ i < K, n_next i = extend_temp Lambda lambda U m_prev n_prev i) ∧
  (extend_temp Lambda lambda U m_prev n_prev (K - 1) * Q) ∣ n_next (m_next - 1) ∧
  (∀ i < m_next, n_next i ∣ n_next (m_next - 1)) ∧
  StrictMonoOn n_next (Set.Icc 0 (m_next - 1)) ∧
  (∀ j, K - 1 ≤ j → j < m_next - 1 → lambda ≤ (n_next (j + 1) : ℝ) / n_next j ∧ (n_next (j + 1) : ℝ) / n_next j ≤ 2) := by
    exact Classical.choose_spec ( _ : ∃ M ≥ m_prev + 1 + U, ∃ n_next : ℕ → ℕ, ( ∀ i < m_prev + 1 + U, n_next i = extend_temp Lambda lambda U m_prev n_prev i ) ∧ extend_temp Lambda lambda U m_prev n_prev ( m_prev + 1 + U - 1 ) * ( Q_seq ( k + 1 ) * n_prev ( m_prev - 1 ) ) ∣ n_next ( M - 1 ) ∧ ( ∀ i < M, n_next i ∣ n_next ( M - 1 ) ) ∧ StrictMonoOn n_next ( Set.Icc 0 ( M - 1 ) ) ∧ ∀ j, m_prev + 1 + U - 1 ≤ j → j < M - 1 → lambda ≤ ( n_next ( j + 1 ) : ℝ ) / n_next j ∧ ( n_next ( j + 1 ) : ℝ ) / n_next j ≤ 2 ) |> fun h => ⟨ h.1, h.2.choose_spec.1, h.2.choose_spec.2.1, h.2.choose_spec.2.2.1, h.2.choose_spec.2.2.2.1, h.2.choose_spec.2.2.2.2 ⟩

/-
Definitions of the v2 sequence using `step_thm3_strong_v2`.
-/
noncomputable def next_thm3_data_v2 (Lambda : ℝ) (lambda : ℝ) (U : ℕ) (k : ℕ)
  (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < 2)
  (prev : Thm3Data Lambda lambda) : Thm3Data Lambda lambda :=
  let res := step_thm3_strong_v2 Lambda lambda U k prev.m prev.n h_Lambda h_lambda prev.h_m prev.h_pos prev.h_mono
  let m_next := res.1
  let n_next := res.2
  let props := step_thm3_strong_v2_props Lambda lambda U k prev.m prev.n h_Lambda h_lambda prev.h_m prev.h_pos prev.h_mono
  { m := m_next
    n := n_next
    h_m := by
      linarith [ props.1, prev.h_m ]
    h_pos := by
      intros i hi
      have h_pos : n_next i ≥ n_next 0 := by
        simp +zetaDelta at *; (have := props.2.2.2.2.1; (
        exact this.le_iff_le ( by norm_num ) ( by constructor <;> omega ) |>.2 ( by omega ) ;))
      have h_pos0 : 0 < n_next 0 := by
        have h_n_next_zero : n_next 0 = prev.n 0 := by
          convert props.2.1 0 ( by linarith [ prev.h_m ] ) using 1
          generalize_proofs at *; (
          exact Eq.symm ( if_pos ( by linarith [ prev.h_m ] ) ))
        generalize_proofs at *;
        exact h_n_next_zero.symm ▸ prev.h_pos 0 (by linarith [prev.h_m])
      linarith [h_pos, h_pos0]
    h_mono := by
      apply props.2.2.2.2.1
  }

noncomputable def thm3_seq_v2 (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) : ℕ → Thm3Data Lambda lambda
| 0 => init_thm3_data Lambda lambda h_Lambda h_lambda
| k + 1 =>
  let U := U_thm3 Lambda lambda h_Lambda h_lambda
  let h_l := h_lambda
  have h_l' : 1 < lambda ∧ lambda < 2 := ⟨h_l.1, lambda_lt_two Lambda lambda h_Lambda h_l.2⟩
  next_thm3_data_v2 Lambda lambda U k h_Lambda h_l' (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k)

noncomputable def m_seq_thm3_final_v2 (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) (k : ℕ) : ℕ :=
  (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m

noncomputable def n_seq_thm3_final_v2 (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) (i : ℕ) : ℕ :=
  let seq := thm3_seq_v2 Lambda lambda h_Lambda h_lambda
  let P := fun k => (seq k).m > i
  if h : ∃ k, P k then
    (seq (Nat.find h)).n i
  else
    1

/-
The cumulative product of primorials is eventually divisible by any positive integer.
-/
lemma q_dvd_super_Q_strong_proved (q : ℕ) (hq : q > 0) : ∃ k, q ∣ super_Q_strong k := by
  exact q_dvd_super_Q_strong q hq

/-
Recurrence relation for divisibility of the last term of each block in the v2 sequence.
-/
lemma n_seq_thm3_final_v2_div_recurrence (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) (k : ℕ) :
  (n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k - 1) * Q_seq (k + 1)) ∣ n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (k + 1) - 1) := by
    have h_div : ∀ k, ∃ d, (thm3_seq_v2 Lambda lambda h_Lambda h_lambda (k + 1)).n ((thm3_seq_v2 Lambda lambda h_Lambda h_lambda (k + 1)).m - 1) = d * (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n ((thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m - 1) * Q_seq (k + 1) := by
      intro k
      obtain ⟨d, hd⟩ : ∃ d, (thm3_seq_v2 Lambda lambda h_Lambda h_lambda (k + 1)).n ((thm3_seq_v2 Lambda lambda h_Lambda h_lambda (k + 1)).m - 1) = d * (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n ((thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m - 1) * Q_seq (k + 1) := by
        have := step_thm3_strong_v2_props Lambda lambda (U_thm3 Lambda lambda h_Lambda h_lambda) k (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n h_Lambda ⟨h_lambda.left, lambda_lt_two Lambda lambda h_Lambda h_lambda.right⟩ (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).h_m (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).h_pos (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).h_mono
        obtain ⟨ d, hd ⟩ := this.2.2.1
        generalize_proofs at *; (
        exact ⟨ d * extend_temp Lambda lambda ( U_thm3 Lambda lambda h_Lambda h_lambda ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).m ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).n ( ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).m + 1 + U_thm3 Lambda lambda h_Lambda h_lambda - 1 ), by linarith! ⟩)
      generalize_proofs at *; (
      use d)
    generalize_proofs at *; (
    have h_div : ∀ k i, i < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m → (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n i = n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda i := by
      intros k i hi
      generalize_proofs at *; (
      have h_div : ∀ k i, i < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m → (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n i = n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda i := by
        intros k i hi
        have h_exists : ∃ k', (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k').m > i := by
          exact ⟨ k, hi ⟩
        obtain ⟨ k', hk' ⟩ := Nat.findX h_exists
        generalize_proofs at *; (
        have h_eq : k' ≤ k := by
          exact le_of_not_gt fun h => hk'.2 _ h hi;
        generalize_proofs at *; (
        have h_eq : ∀ j, k' ≤ j → j ≤ k → (thm3_seq_v2 Lambda lambda h_Lambda h_lambda j).n i = (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k').n i := by
          intros j hj₁ hj₂
          induction' hj₁ with j hj ih
          generalize_proofs at *; (
          rfl);
          rw [ ← ih ( Nat.le_of_succ_le hj₂ ), thm3_seq_v2 ];
          have := step_thm3_strong_v2_props Lambda lambda ( U_thm3 Lambda lambda h_Lambda h_lambda ) j ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda j ).m ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda j ).n h_Lambda ⟨ h_lambda.1, lambda_lt_two Lambda lambda h_Lambda h_lambda.2 ⟩ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda j ).h_m ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda j ).h_pos ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda j ).h_mono
          generalize_proofs at *; (
          convert this.2.1 i _ using 1
          generalize_proofs at *; (
          exact Eq.symm ( if_pos ( by linarith [ show ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda j ).m ≥ i + 1 from by linarith [ show ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda j ).m ≥ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k' ).m from by exact Nat.le_induction ( by linarith ) ( fun n hn ih => by linarith [ show ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda ( n + 1 ) ).m > ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n ).m from by
                                                                                                                                                                                                                                                                                                                                    have := step_thm3_strong_v2_props Lambda lambda ( U_thm3 Lambda lambda h_Lambda h_lambda ) n ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n ).m ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n ).n h_Lambda ⟨ h_lambda.1, lambda_lt_two Lambda lambda h_Lambda h_lambda.2 ⟩ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n ).h_m ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n ).h_pos ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n ).h_mono
                                                                                                                                                                                                                                                                                                                                    generalize_proofs at *; (
                                                                                                                                                                                                                                                                                                                                    exact Nat.lt_of_lt_of_le ( by linarith [ show U_thm3 Lambda lambda h_Lambda h_lambda ≥ 0 from Nat.zero_le _ ] ) this.1) ] ) j hj ] ] ) ));
          linarith [ show ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda j ).m ≥ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k' ).m from by
                      exact Nat.le_induction ( by norm_num ) ( fun n hn ih => by linarith [ show ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda ( n + 1 ) ).m > ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n ).m from by
                                                                                              have := step_thm3_strong_v2_props Lambda lambda ( U_thm3 Lambda lambda h_Lambda h_lambda ) n ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n ).m ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n ).n h_Lambda ⟨ h_lambda.1, lambda_lt_two Lambda lambda h_Lambda h_lambda.2 ⟩ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n ).h_m ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n ).h_pos ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n ).h_mono
                                                                                              generalize_proofs at *; (
                                                                                              exact Nat.lt_of_lt_of_le ( by linarith [ show U_thm3 Lambda lambda h_Lambda h_lambda ≥ 0 from Nat.zero_le _ ] ) this.1) ] ) j hj ])
        generalize_proofs at *; (
        have h_eq : (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n i = (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k').n i := by
          exact h_eq k ( by linarith ) ( by linarith ) ▸ rfl
        generalize_proofs at *; (
        convert h_eq using 1
        generalize_proofs at *; (
        unfold n_seq_thm3_final_v2; aesop;)))))
      generalize_proofs at *; (
      exact h_div k i hi ▸ rfl))
    generalize_proofs at *; (
    obtain ⟨ d, hd ⟩ := ‹∀ k : ℕ, ∃ d : ℕ, ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda ( k + 1 ) ).n ( ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda ( k + 1 ) ).m - 1 ) = d * ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).n ( ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).m - 1 ) * Q_seq ( k + 1 ) › k; simp_all +decide [ mul_assoc ] ;
    convert hd.symm ▸ dvd_mul_left _ _ using 1
    generalize_proofs at *; (
    exact h_div k _ ( Nat.sub_lt ( by linarith [ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).h_m ] ) zero_lt_one ) ▸ rfl);
    exact h_div _ _ ( Nat.sub_lt ( by linarith [ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda ( k + 1 ) ).h_m ] ) zero_lt_one ) ▸ rfl))

/-
Consistency of the v2 sequence: terms are preserved in the next step.
-/
lemma thm3_seq_v2_consistent (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) (k : ℕ) (i : ℕ)
  (hi : i < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m) :
  (thm3_seq_v2 Lambda lambda h_Lambda h_lambda (k + 1)).n i = (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n i := by
    convert step_thm3_strong_v2_props Lambda lambda ( U_thm3 Lambda lambda h_Lambda h_lambda ) k ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).m ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).n h_Lambda ⟨ h_lambda.1, lambda_lt_two Lambda lambda h_Lambda h_lambda.2 ⟩ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |>.h_m ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |>.h_pos ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |>.h_mono ) |>.2.1 i ( by linarith ) using 1;
    unfold extend_temp; aesop;

/-
The term at index $m_k-1$ in the v2 sequence is divisible by the cumulative primorial product.
-/
lemma super_Q_strong_dvd_n_v2 (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) (k : ℕ) :
  super_Q_strong k ∣ n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k - 1) := by
    induction' k with k ih;
    · exact one_dvd _;
    · exact dvd_trans ( by unfold super_Q_strong; simp +decide [ Finset.prod_range_succ ] ) ( dvd_trans ( mul_dvd_mul ih ( dvd_refl _ ) ) ( n_seq_thm3_final_v2_div_recurrence _ _ _ _ _ ) ) ;

/-
Every positive integer divides some term of the v2 sequence.
-/
lemma thm3_div_all_v2 (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) (q : ℕ) (hq : q > 0) :
  ∃ i, q ∣ n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda i := by
    -- By `super_Q_strong_dvd_n_v2`, we know that `super_Q_strong k` divides `n(m_k-1)`.
    have h_div : ∀ k, super_Q_strong k ∣ n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k - 1) := by
      exact fun k => super_Q_strong_dvd_n_v2 Lambda lambda h_Lambda h_lambda k;
    obtain ⟨ k, hk ⟩ := q_dvd_super_Q_strong_proved q hq;
    exact ⟨ _, dvd_trans hk ( h_div k ) ⟩

/-
The term at index `special_m_v2 k` is divisible by all preceding terms.
-/
noncomputable def special_m_v2 (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) (k : ℕ) : ℕ :=
  m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k - 1

lemma thm3_seq_v2_div_m (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) (k : ℕ) :
  ∀ j < special_m_v2 Lambda lambda h_Lambda h_lambda k, n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda j ∣ n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (special_m_v2 Lambda lambda h_Lambda h_lambda k) := by
    -- By definition of `special_m_v2`, we know that `special_m_v2 k = m_k - 1`.
    set m_k := m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k
    have h_special_m_v2 : special_m_v2 Lambda lambda h_Lambda h_lambda k = m_k - 1 := by
      exact rfl
    generalize_proofs at *; (
    -- By definition of `n_seq_thm3_final_v2`, we know that `n_seq_thm3_final_v2 j` is equal to `n_seq_thm3_final_v2 (special_m_v2 k)` for all `j < special_m_v2 k`.
    intro j hj
    have h_eq : n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda j = (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n j := by
      -- Since $j < m_k - 1$, we can apply the definition of `n_seq_thm3_final_v2` with $k$.
      have h_exists_k : ∃ k', j < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k').m := by
        exact ⟨ k, lt_of_lt_of_le hj ( Nat.pred_le _ ) ⟩
      generalize_proofs at *; (
      obtain ⟨k', hk'⟩ : ∃ k', j < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k').m ∧ k' ≤ k := by
        exact ⟨ k, by simpa only [ h_special_m_v2 ] using hj.trans_le ( Nat.sub_le _ _ ), le_rfl ⟩
      generalize_proofs at *; (
      have h_consistent : ∀ k' k, k' ≤ k → ∀ j, j < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k').m → (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n j = (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k').n j := by
        intros k' k hk' j hj
        induction' hk' with k' hk' ih generalizing j
        generalize_proofs at *; (
        rfl);
        rw [ thm3_seq_v2_consistent Lambda lambda h_Lambda h_lambda k' j ] ; aesop
        generalize_proofs at *; (
        exact lt_of_lt_of_le hj ( Nat.le_induction ( by tauto ) ( fun k hk ih => by linarith [ show ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda ( k + 1 ) ).m > ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).m from by
                                                                                                exact step_thm3_strong_v2_props Lambda lambda ( U_thm3 Lambda lambda h_Lambda h_lambda ) k ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).m ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).n h_Lambda ⟨ h_lambda.1, lambda_lt_two Lambda lambda h_Lambda h_lambda.2 ⟩ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).h_m ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).h_pos ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).h_mono |>.1 |> Nat.lt_of_lt_of_le ( by linarith [ show ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).m ≥ 1 from Nat.succ_le_of_lt ( by linarith [ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).h_m ] ) ] ) |> Nat.lt_of_lt_of_le <| Nat.le_refl _; ] ) _ hk' ))
      generalize_proofs at *; (
      have h_exists_k : ∃ k', j < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k').m ∧ ∀ k'', k'' < k' → ¬(j < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k'').m) := by
        exact ⟨ Nat.find h_exists_k, Nat.find_spec h_exists_k, fun k'' hk'' => Nat.find_min h_exists_k hk'' ⟩
      generalize_proofs at *; (
      obtain ⟨ k', hk₁, hk₂ ⟩ := h_exists_k
      generalize_proofs at *; (
      have h_exists_k : n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda j = (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k').n j := by
        rw [ n_seq_thm3_final_v2 ];
        split_ifs <;> simp_all +decide;
        rw [ show Nat.find ( show ∃ k, j < ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).m from ⟨ k', hk₁ ⟩ ) = k' from le_antisymm ( Nat.find_min' _ hk₁ ) ( Nat.le_of_not_lt fun h => by linarith [ hk₂ _ h, Nat.find_spec ( show ∃ k, j < ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).m from ⟨ k', hk₁ ⟩ ) ] ) ]
      generalize_proofs at *; (
      grind))))))
    generalize_proofs at *; (
    have h_eq : n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (special_m_v2 Lambda lambda h_Lambda h_lambda k) = (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n (m_k - 1) := by
      have h_eq : n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (m_k - 1) = (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n (m_k - 1) := by
        have h_exists_k : ∃ k', (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k').m > m_k - 1 := by
          exact ⟨ k, Nat.sub_lt ( by exact Nat.pos_of_ne_zero ( by
            grind +ring ) ) zero_lt_one ⟩
        obtain ⟨ k', hk' ⟩ := Nat.findX h_exists_k
        generalize_proofs at *; (
        have h_eq : n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (m_k - 1) = (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k').n (m_k - 1) := by
          rw [n_seq_thm3_final_v2];
          split_ifs <;> simp_all +decide;
          rw [ show Nat.find ‹∃ k, ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).m > m_k - 1› = k' from _ ];
          exact le_antisymm ( Nat.find_min' _ hk'.1 ) ( Nat.le_of_not_lt fun h => by linarith [ hk'.2 _ h, Nat.find_spec ‹∃ k, ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).m > m_k - 1› ] )
        generalize_proofs at *; (
        have h_eq : k' = k := by
          apply le_antisymm
          generalize_proofs at *; (
          exact le_of_not_gt fun h => hk'.2 _ h <| Nat.lt_of_lt_of_le ( Nat.sub_lt ( Nat.pos_of_ne_zero <| by
            grind +ring ) zero_lt_one ) <| by
            exact le_rfl);
          contrapose! hk';
          intro h
          generalize_proofs at *; (
          have h_contra : (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k').m ≤ (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m - 1 := by
            have h_contra : ∀ k', k' < k → (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k').m ≤ (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m - 1 := by
              intros k' hk'
              have h_contra : (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k').m < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m := by
                have h_contra : StrictMono (fun k => (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m) := by
                  exact strictMono_nat_of_lt_succ fun k => by
                    exact step_thm3_strong_v2_props Lambda lambda ( U_thm3 Lambda lambda h_Lambda h_lambda ) k ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.m ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.n ) h_Lambda ⟨ h_lambda.1, lambda_lt_two Lambda lambda h_Lambda h_lambda.2 ⟩ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.h_m ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.h_pos ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.h_mono ) |>.1.trans_lt' ( by linarith [ thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.h_m ] ) ;
                generalize_proofs at *; (exact h_contra hk')
              generalize_proofs at *; (exact Nat.le_sub_one_of_lt h_contra)
            generalize_proofs at *; (
            exact h_contra k' hk')
          generalize_proofs at *; (
          exact False.elim <| h.not_ge h_contra))
        generalize_proofs at *; (aesop)))
      generalize_proofs at *; (
      rw [h_special_m_v2, h_eq])
    generalize_proofs at *; (
    have h_div : ∀ i < m_k, (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n i ∣ (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n (m_k - 1) := by
      have h_div : ∀ k, ∀ i < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m, (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n i ∣ (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n ((thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m - 1) := by
        intro k i hi; induction' k with k ih generalizing i <;> simp_all +decide [ thm3_seq_v2 ] ;
        · exact pow_dvd_pow _ ( Nat.le_sub_one_of_lt hi );
        · apply (step_thm3_strong_v2_props Lambda lambda (U_thm3 Lambda lambda h_Lambda h_lambda) k (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n h_Lambda ⟨h_lambda.1, lambda_lt_two Lambda lambda h_Lambda h_lambda.2⟩ (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).h_m (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).h_pos (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).h_mono).2.2.2.1 i hi
      generalize_proofs at *; (
      exact h_div k)
    generalize_proofs at *; (
    grind +ring))))

/-
The v2 sequence is strictly increasing.
-/
lemma n_seq_thm3_final_v2_mono (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) :
  StrictMono (n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda) := by
    have h_m_seq_growth : ∀ k, (thm3_seq_v2 Lambda lambda h_Lambda h_lambda (k + 1)).m > (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m := by
      intro k
      simp [thm3_seq_v2] at *; (
      exact step_thm3_strong_v2_props Lambda lambda ( U_thm3 Lambda lambda h_Lambda h_lambda ) k ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).m ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).n h_Lambda ⟨ h_lambda.1, lambda_lt_two Lambda lambda h_Lambda h_lambda.2 ⟩ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |>.h_m ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |>.h_pos ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |>.h_mono ) |>.1 |> lt_of_lt_of_le ( by linarith [ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |>.h_m ) ] ) ;);
    have h_m_seq_tendsto_atTop : Filter.Tendsto (fun k => (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m) Filter.atTop Filter.atTop := by
      exact Filter.tendsto_atTop_mono ( fun k => Nat.recOn k ( by norm_num ) fun k ih => by linarith [ h_m_seq_growth k ] ) tendsto_natCast_atTop_atTop
    generalize_proofs at *; (
    have h_n_seq_mono : ∀ k i, i < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m → (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n i = n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda i := by
      intros k i hi
      generalize_proofs at *; (
      apply Eq.symm; exact (by
        have h_exists_k : ∃ k, (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m > i := by
          exact ⟨ k, hi ⟩
        obtain ⟨k', hk'⟩ : ∃ k', (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k').m > i ∧ ∀ j < k', (thm3_seq_v2 Lambda lambda h_Lambda h_lambda j).m ≤ i := by
          exact ⟨ Nat.find h_exists_k, Nat.find_spec h_exists_k, fun j hj => not_lt.1 fun contra => Nat.find_min h_exists_k hj contra ⟩
        generalize_proofs at *; (
        have h_eq : ∀ j ≥ k', (thm3_seq_v2 Lambda lambda h_Lambda h_lambda j).n i = (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k').n i := by
          intro j hj
          induction' hj with j hj ih
          generalize_proofs at *; (
          rfl);
          convert thm3_seq_v2_consistent Lambda lambda h_Lambda h_lambda j i _ using 1
          generalize_proofs at *; (
          exact ih.symm ▸ rfl);
          exact lt_of_lt_of_le hk'.1 ( by exact monotone_nat_of_le_succ ( fun k => le_of_lt ( h_m_seq_growth k ) ) hj )
        generalize_proofs at *; (
        have h_eq : n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda i = (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k').n i := by
          unfold n_seq_thm3_final_v2; aesop;
        generalize_proofs at *; (
        exact h_eq.trans ( by rw [ ‹∀ j ≥ k', ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda j ).n i = ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k' ).n i› k ( Nat.le_of_not_lt fun h => by linarith [ hk'.2 k h ] ) ] ) ;)))
      ))
    generalize_proofs at *; (
    have h_n_seq_mono : ∀ k, StrictMonoOn (fun i => (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n i) (Set.Icc 0 ((thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m - 1)) := by
      exact fun k => (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).h_mono
    generalize_proofs at *; (
    have h_n_seq_mono : ∀ i j, i < j → ∃ k, i < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m ∧ j < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m := by
      exact fun i j hij => by rcases Filter.eventually_atTop.mp ( h_m_seq_tendsto_atTop.eventually_gt_atTop j ) with ⟨ k, hk ⟩ ; exact ⟨ k, by linarith [ hk k le_rfl ], by linarith [ hk k le_rfl ] ⟩ ; ;
    generalize_proofs at *; (
    intro i j hij; obtain ⟨ k, hk₁, hk₂ ⟩ := h_n_seq_mono i j hij; have := ‹∀ k : ℕ, StrictMonoOn ( fun i => ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.n ) i ) ( Icc 0 ( ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.m ) - 1 ) ) › k; have := this ( show i ∈ Icc 0 ( ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.m ) - 1 ) from ⟨ Nat.zero_le _, Nat.le_sub_one_of_lt hk₁ ⟩ ) ( show j ∈ Icc 0 ( ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.m ) - 1 ) from ⟨ Nat.zero_le _, Nat.le_sub_one_of_lt hk₂ ⟩ ) hij; aesop;))))

lemma n_seq_thm3_final_v2_eq_pre (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) (k : ℕ) (i : ℕ)
  (hi : i < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m) :
  n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda i = (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n i := by
    unfold n_seq_thm3_final_v2;
    simp +zetaDelta at *;
    split_ifs with h;
    · have h_mono : StrictMono (fun k => (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m) := by
        refine' strictMono_nat_of_lt_succ _;
        intro n
        generalize_proofs at *; (
        exact step_thm3_strong_v2_props Lambda lambda ( U_thm3 Lambda lambda h_Lambda h_lambda ) n ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n |> Thm3Data.m ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n |> Thm3Data.n ) h_Lambda ⟨ h_lambda.1, lambda_lt_two Lambda lambda h_Lambda h_lambda.2 ⟩ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n |> Thm3Data.h_m ) ( fun i hi => ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n |> Thm3Data.h_pos ) i hi ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n |> Thm3Data.h_mono ) |>.1 |> lt_of_lt_of_le ( by omega ) ;);
      have h_find_le_k : Nat.find h ≤ k := by
        exact Nat.find_min' h hi;
      have h_eq : ∀ j, Nat.find h ≤ j → j ≤ k → (thm3_seq_v2 Lambda lambda h_Lambda h_lambda j).n i = (thm3_seq_v2 Lambda lambda h_Lambda h_lambda (Nat.find h)).n i := by
        intros j hj₁ hj₂
        induction' hj₁ with j hj₁ ih;
        · rfl;
        · rw [ ← ih ( Nat.le_of_succ_le hj₂ ), thm3_seq_v2_consistent ];
          exact Nat.find_spec h |> fun x => lt_of_lt_of_le x ( h_mono.monotone hj₁ );
      rw [ h_eq k h_find_le_k le_rfl ];
    · exact False.elim <| h ⟨ k, hi ⟩

/-
The v2 sequence has large jumps at indices $m_k$.
-/
lemma thm3_seq_v2_large_jumps (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) (k : ℕ) :
  let m_k := m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k
  (n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda m_k : ℝ) > Lambda * n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (m_k - 1) := by
    have hstep := step_thm3_strong_v2_props Lambda lambda (U_thm3 Lambda lambda h_Lambda h_lambda) k
      (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m
      (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n
      h_Lambda ⟨h_lambda.1, lambda_lt_two Lambda lambda h_Lambda h_lambda.2⟩
      (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).h_m
      (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).h_pos
      (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).h_mono
    have hprev :
        n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda ((thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m - 1) =
          (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n ((thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m - 1) := by
      exact n_seq_thm3_final_v2_eq_pre Lambda lambda h_Lambda h_lambda k _ (Nat.sub_lt (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).h_m zero_lt_one)
    have hnext_m : (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda (k + 1)).m := by
      rw [thm3_seq_v2]
      exact lt_of_lt_of_le (by omega) hstep.1
    have hcurr :
        n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m =
          (thm3_seq_v2 Lambda lambda h_Lambda h_lambda (k + 1)).n (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m := by
      exact n_seq_thm3_final_v2_eq_pre Lambda lambda h_Lambda h_lambda (k + 1) _ hnext_m
    dsimp [m_seq_thm3_final_v2]
    rw [hprev, hcurr]
    have hjump :
        (thm3_seq_v2 Lambda lambda h_Lambda h_lambda (k + 1)).n (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m =
          jump_val Lambda ((thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n ((thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m - 1)) := by
      convert hstep.2.1 (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m (by omega) using 1
      simp [extend_temp, geo_seq]
    rw [hjump, jump_val]
    exact_mod_cast Nat.lt_of_floor_lt (Nat.lt_succ_self _)

/-
The final v2 sequence agrees with the sequence at step `k` for indices within the range of step `k`.
-/
lemma n_seq_thm3_final_v2_eq (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) (k : ℕ) (i : ℕ)
  (hi : i < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m) :
  n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda i = (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n i := by
    unfold n_seq_thm3_final_v2;
    simp +zetaDelta at *;
    split_ifs with h;
    · -- By definition of `thm3_seq_v2`, we know that `thm3_seq_v2` is strictly increasing.
      have h_mono : StrictMono (fun k => (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m) := by
        refine' strictMono_nat_of_lt_succ _;
        intro n
        generalize_proofs at *; (
        exact step_thm3_strong_v2_props Lambda lambda ( U_thm3 Lambda lambda h_Lambda h_lambda ) n ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n |> Thm3Data.m ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n |> Thm3Data.n ) h_Lambda ⟨ h_lambda.1, lambda_lt_two Lambda lambda h_Lambda h_lambda.2 ⟩ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n |> Thm3Data.h_m ) ( fun i hi => ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n |> Thm3Data.h_pos ) i hi ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n |> Thm3Data.h_mono ) |>.1 |> lt_of_lt_of_le ( by omega ) ;);
      -- Since `Nat.find h` is the smallest `k` such that `i < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m`, and `k` is such that `i < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m`, it must be that `Nat.find h ≤ k`.
      have h_find_le_k : Nat.find h ≤ k := by
        exact Nat.find_min' h hi;
      have h_eq : ∀ j, Nat.find h ≤ j → j ≤ k → (thm3_seq_v2 Lambda lambda h_Lambda h_lambda j).n i = (thm3_seq_v2 Lambda lambda h_Lambda h_lambda (Nat.find h)).n i := by
        intros j hj₁ hj₂
        induction' hj₁ with j hj₁ ih;
        · rfl;
        · rw [ ← ih ( Nat.le_of_succ_le hj₂ ), thm3_seq_v2_consistent ];
          exact Nat.find_spec h |> fun x => lt_of_lt_of_le x ( h_mono.monotone hj₁ );
      rw [ h_eq k h_find_le_k le_rfl ];
    · exact False.elim <| h ⟨ k, hi ⟩

/-
The ratio of consecutive terms in the v2 sequence is at least $\lambda$.
-/
lemma thm3_seq_v2_lacunary_lower (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) (i : ℕ) :
  lambda ≤ (n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (i + 1) : ℝ) / n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda i := by
    -- By the properties of the sequence, we have that for any $i$, $n_{i+1} \geq \lambda n_i$ because the sequence is strictly monotonic and each term is a multiple of the previous term.
    have h_ratio : ∀ k i, i < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m - 1 → (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n (i + 1) ≥ lambda * (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n i := by
      intro k
      induction' k with k ih;
      · -- For the base case when $k = 0$, the sequence is just $[1]$, so there are no $i$ to check.
        simp [thm3_seq_v2, init_thm3_data] at *;
        intro i hi; rw [ pow_succ' ] ; nlinarith [ show ( 2 : ℝ ) ^ i > 0 by positivity, show ( 2 : ℝ ) ^ i ≥ 1 by exact one_le_pow₀ ( by norm_num ), lambda_lt_two Lambda lambda h_Lambda h_lambda.2 ] ;
      · intro i hi
        have h_ratio : (thm3_seq_v2 Lambda lambda h_Lambda h_lambda (k + 1)).n (i + 1) ≥ lambda * (thm3_seq_v2 Lambda lambda h_Lambda h_lambda (k + 1)).n i := by
          have := @step_thm3_strong_v2_props Lambda lambda ( U_thm3 Lambda lambda h_Lambda h_lambda ) k ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.m ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.n ) h_Lambda ⟨ h_lambda.1, by
            exact lambda_lt_two Lambda lambda h_Lambda h_lambda.2 |> lt_of_lt_of_le <| by norm_num; ⟩ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.h_m ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.h_pos ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.h_mono )
          generalize_proofs at *; (
          by_cases hi' : i < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m + 1 + U_thm3 Lambda lambda h_Lambda h_lambda - 1 <;> simp_all +decide ; (
          have h_ratio : (extend_temp Lambda lambda (U_thm3 Lambda lambda h_Lambda h_lambda) (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n) (i + 1) ≥ lambda * (extend_temp Lambda lambda (U_thm3 Lambda lambda h_Lambda h_lambda) (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n) i := by
            by_cases hi'' : i < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m <;> simp_all +decide ; (
            by_cases hi''' : i + 1 < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m <;> simp_all +decide [ extend_temp ] ; (
            exact ih i ( Nat.lt_pred_iff.mpr hi''' ));
            cases hi'''.eq_or_lt <;> first | linarith | simp_all +decide ; (
            unfold geo_seq; norm_num [ jump_val ] ; ring_nf ; (
            nlinarith [ Nat.lt_floor_add_one ( ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.n ) i * Lambda ), show ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.n ) i ≥ 1 from mod_cast ‹∀ i < ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.m ), 0 < ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.n ) i› i ( by linarith ) ])));
            rw [ extend_temp ] ; split_ifs <;> try linarith;
            rw [ extend_temp ] ; split_ifs <;> try linarith;
            rw [ show i + 1 - ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.m ) = ( i - ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.m ) ) + 1 by omega ] ; simp +decide [ *, geo_seq ] ; ring_nf ;
            exact Nat.le_ceil _ |> le_trans ( by norm_num ) ;
          generalize_proofs at *; (
          convert h_ratio.le using 1 <;> norm_num [ next_thm3_data_v2 ] ; ring_nf!;
          · rw [ add_comm ] ; exact Or.inl <| this.2.1 i <| by omega;
          · convert this.2.1 ( i + 1 ) _ using 1 ; ring_nf!; omega;));
          convert this.2.2.2.2.2 i hi' ( by
            exact hi ) |> And.left |> fun x => mul_le_mul_of_nonneg_right x <| Nat.cast_nonneg _ using 1
          generalize_proofs at *; (
          rw [ div_mul_eq_mul_div, eq_div_iff ] <;> norm_cast;
          exact ne_of_gt ( by exact ( thm3_seq_v2 ( Lambda ) ( lambda ) h_Lambda h_lambda ( k + 1 ) |> Thm3Data.h_pos ) _ ( by omega ) ) ;))
        exact h_ratio;
    obtain ⟨k, hk⟩ : ∃ k, i + 1 < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m := by
      have h_seq_growth : Filter.Tendsto (fun k => (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m) Filter.atTop Filter.atTop := by
        -- By the properties of the sequence, we have that for any $k$, $m_{k+1} > m_k$.
        have h_m_growth : ∀ k, (thm3_seq_v2 Lambda lambda h_Lambda h_lambda (k + 1)).m > (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m := by
          intro k
          generalize_proofs at *; (exact (by
          exact step_thm3_strong_v2_props Lambda lambda ( U_thm3 Lambda lambda h_Lambda h_lambda ) k ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).m ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).n h_Lambda ⟨ h_lambda.1, lambda_lt_two Lambda lambda h_Lambda h_lambda.2 ⟩ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |>.h_m ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |>.h_pos ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |>.h_mono ) |>.1 |> lt_of_lt_of_le ( by linarith [ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |>.h_m ) ] ) ;))
        generalize_proofs at *; (
        exact Filter.tendsto_atTop_mono ( fun k => Nat.recOn k ( by norm_num ) fun k ih => by linarith [ h_m_growth k ] ) tendsto_natCast_atTop_atTop)
      generalize_proofs at *; (exact Filter.eventually_atTop.mp (h_seq_growth.eventually_gt_atTop (i + 1)) |> fun ⟨k, hk⟩ => ⟨k, hk k le_rfl⟩;)
    generalize_proofs at *; (
    rw [ n_seq_thm3_final_v2_eq, n_seq_thm3_final_v2_eq ] <;> try omega
    generalize_proofs at *; (
    rw [ le_div_iff₀ ] <;> linarith [ h_ratio k i ( Nat.lt_pred_iff.mpr hk ), show ( ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).n i : ℝ ) > 0 from mod_cast ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).h_pos i ( by omega ) ]))

/-
The terms of the v2 sequence starting from index $m_0-1$ are all strictly greater than $1/\epsilon$.
-/
lemma thm3_seq_v2_gt_epsilon (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) (i : ℕ)
  (hi : i ≥ m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda 0 - 1) :
  (n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda i : ℝ) > 1 / epsilon_thm3 Lambda lambda h_Lambda h_lambda := by
    have h_n_m0_minus_one : (n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda 0 - 1) : ℝ) > 1 / epsilon_thm3 Lambda lambda h_Lambda h_lambda := by
      -- By definition of `n_seq_thm3_final_v2`, we know that `n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda 0 - 1)` is equal to `2 ^ (m0_thm3 Lambda lambda h_Lambda h_lambda - 1)`.
      have h_n_eq : n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda 0 - 1) = 2 ^ (m0_thm3 Lambda lambda h_Lambda h_lambda - 1) := by
        rw [ n_seq_thm3_final_v2_eq ];
        case k => exact 0;
        · unfold m_seq_thm3_final_v2; aesop;
        · exact Nat.pred_lt ( ne_bot_of_gt ( init_thm3_data Lambda lambda h_Lambda h_lambda |>.h_m ) );
      have := two_pow_m0_sub_one_gt_one_div_epsilon Lambda lambda h_Lambda h_lambda; aesop;
    exact h_n_m0_minus_one.trans_le ( mod_cast n_seq_thm3_final_v2_mono Lambda lambda h_Lambda h_lambda |> fun h => h.monotone hi )

/-
Algebraic inequality for the jump condition.
-/
lemma jump_ineq_lemma (Lambda epsilon x : ℝ) (h_eps : epsilon > 0) (hx : x > 1 / epsilon) :
  ⌊Lambda * x⌋ + 1 < (Lambda + epsilon) * x := by
    rw [ gt_iff_lt, div_lt_iff₀ ] at hx <;> linarith [ Int.floor_le ( Lambda * x ), Int.lt_floor_add_one ( Lambda * x ) ] ;

/-
The term at the jump index $m_k$ is equal to $\lfloor \Lambda n(m_k-1) \rfloor + 1$.
-/
lemma thm3_seq_v2_at_jump_eq (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) (k : ℕ) :
  let m_k := m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k
  let n := n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda
  n m_k = Nat.floor (Lambda * n (m_k - 1)) + 1 := by
    convert n_seq_thm3_final_v2_eq Lambda lambda h_Lambda h_lambda ( k + 1 ) _ _ using 1 <;> norm_num [ m_seq_thm3_final_v2 ];
    · rw [ n_seq_thm3_final_v2_eq ];
      convert Eq.symm ( step_thm3_strong_v2_props Lambda lambda ( U_thm3 Lambda lambda h_Lambda h_lambda ) k ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.m ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.n ) h_Lambda ⟨ h_lambda.1, lambda_lt_two Lambda lambda h_Lambda h_lambda.2 ⟩ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.h_m ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.h_pos ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.h_mono ) |>.2.1 _ _ ) using 1;
      any_goals exact k;
      · unfold extend_temp; aesop;
      · linarith [ show 0 ≤ U_thm3 Lambda lambda h_Lambda h_lambda from Nat.zero_le _ ];
      · exact Nat.pred_lt ( ne_bot_of_gt ( Thm3Data.h_m ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ) ) );
    · -- By definition of `thm3_seq_v2`, we know that `m_seq_thm3_final_v2` is strictly increasing.
      have h_m_seq_inc : StrictMono (m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda) := by
        have h_m_seq_mono : ∀ k, (thm3_seq_v2 Lambda lambda h_Lambda h_lambda (k + 1)).m > (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m := by
          intro k
          generalize_proofs at *; (
          exact step_thm3_strong_v2_props Lambda lambda ( U_thm3 Lambda lambda h_Lambda h_lambda ) k ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).m ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).n h_Lambda ⟨ h_lambda.1, lambda_lt_two Lambda lambda h_Lambda h_lambda.2 ⟩ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |>.h_m ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |>.h_pos ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |>.h_mono ) |>.1 |> lt_of_lt_of_le ( by linarith [ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |>.h_m ) ] ) ;)
        generalize_proofs at *; (exact strictMono_nat_of_lt_succ h_m_seq_mono)
      generalize_proofs at *; (exact h_m_seq_inc (Nat.lt_succ_self k))

/-
The term at the jump index $m_k$ is bounded by $(\Lambda + \epsilon)$ times the previous term.
-/
lemma thm3_seq_v2_jump_bound (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) (k : ℕ) :
  let epsilon := epsilon_thm3 Lambda lambda h_Lambda h_lambda
  let m_k := m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k
  let n := n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda
  (n m_k : ℝ) < (Lambda + epsilon) * n (m_k - 1) := by
    have h_floor : ⌊Lambda * n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k - 1)⌋ + 1 < (Lambda + epsilon_thm3 Lambda lambda h_Lambda h_lambda) * n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k - 1) := by
      have := thm3_seq_v2_gt_epsilon Lambda lambda h_Lambda h_lambda ( m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k - 1 ) ?_ <;> norm_num at *;
      · convert jump_ineq_lemma Lambda ( epsilon_thm3 Lambda lambda h_Lambda h_lambda ) ( n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda ( m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k - 1 ) ) _ _ using 1;
        · exact epsilon_thm3_spec Lambda lambda h_Lambda h_lambda |>.1.1;
        · simpa using this.trans_le' ( by norm_num );
      · rw [ Nat.sub_add_cancel ];
        · induction' k with k ih <;> norm_num [ m_seq_thm3_final_v2 ] at *;
          have := @step_thm3_strong_v2_props Lambda lambda ( U_thm3 Lambda lambda h_Lambda h_lambda ) k ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.m ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.n ) h_Lambda ⟨ h_lambda.1, lambda_lt_two Lambda lambda h_Lambda h_lambda.2 ⟩ ( by
            exact Nat.one_le_of_lt ( Thm3Data.h_m ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ) ) ) ( by
            exact fun i hi => ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.h_pos ) i hi ) ( by
            exact ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).h_mono )
          generalize_proofs at *; (
          exact le_trans ( by omega ) this.1);
        · exact ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).h_m;
    convert h_floor using 1 ; norm_num [ thm3_seq_v2_at_jump_eq Lambda lambda h_Lambda h_lambda k ];
    exact_mod_cast Int.toNat_of_nonneg <| Int.floor_nonneg.2 <| mul_nonneg ( by positivity ) <| Nat.cast_nonneg _;

/-
The sequence satisfies the geometric recurrence $n_{i+1} = \lceil \lambda n_i \rceil$ in the geometric part of the block.
-/
lemma thm3_seq_v2_geo_recurrence (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) (k : ℕ) (j : ℕ) (hj : j < U_thm3 Lambda lambda h_Lambda h_lambda) :
  let m_k := m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k
  let n := n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda
  n (m_k + j + 1) = Nat.ceil (lambda * n (m_k + j)) := by
    -- By definition of `n_seq_thm3_final_v2`, we know that for `k + 1`, the sequence at `m_k + j + 1` is equal to the `geo_seq` with `lambda` and the jump.
    have h_geo_bound : let m_k := m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k; let n := n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda; n (m_k + j + 1) = Nat.ceil (lambda * n (m_k + j)) := by
      have h_seq_step : let m_k := m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k; let n := n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda; n (m_k + j) = (thm3_seq_v2 Lambda lambda h_Lambda h_lambda (k + 1)).n (m_k + j) ∧ n (m_k + j + 1) = (thm3_seq_v2 Lambda lambda h_Lambda h_lambda (k + 1)).n (m_k + j + 1) := by
        have h_seq_step : let m_k := m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k; let n := n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda; m_k + j + 1 < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda (k + 1)).m := by
          have := step_thm3_strong_v2_props Lambda lambda ( U_thm3 Lambda lambda h_Lambda h_lambda ) k ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.m ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.n ) h_Lambda ( ⟨ h_lambda.1, lambda_lt_two Lambda lambda h_Lambda h_lambda.2 ⟩ ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.h_m ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.h_pos ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.h_mono ) ; simp_all +decide [ Nat.succ_add ] ; (
          linarith! [ Nat.sub_add_cancel ( show 1 ≤ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda ( k + 1 ) |> Thm3Data.m ) from Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( by linarith! ) ) ) ] ;)
        generalize_proofs at *; (
        exact ⟨ n_seq_thm3_final_v2_eq _ _ _ _ _ _ ( by linarith ), n_seq_thm3_final_v2_eq _ _ _ _ _ _ ( by linarith ) ⟩)
      -- By definition of `thm3_seq_v2`, we know that for `k + 1`, the sequence at `m_k + j + 1` is equal to the `geo_seq` with `lambda` and the jump.
      have h_geo_seq : let m_k := m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k; let n := (thm3_seq_v2 Lambda lambda h_Lambda h_lambda (k + 1)).n; n (m_k + j + 1) = Nat.ceil (lambda * n (m_k + j)) := by
        have h_geo_seq_def := step_thm3_strong_v2_props Lambda lambda (U_thm3 Lambda lambda h_Lambda h_lambda) k (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n h_Lambda ⟨h_lambda.1, lambda_lt_two Lambda lambda h_Lambda h_lambda.2⟩ (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).h_m (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).h_pos (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).h_mono
        have h_geo_seq_def : ∀ i < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m + 1 + U_thm3 Lambda lambda h_Lambda h_lambda, (thm3_seq_v2 Lambda lambda h_Lambda h_lambda (k + 1)).n i = extend_temp Lambda lambda (U_thm3 Lambda lambda h_Lambda h_lambda) (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n i := by
          exact h_geo_seq_def.2.1
        generalize_proofs at *; (
        have h_geo_seq_def : ∀ j < U_thm3 Lambda lambda h_Lambda h_lambda, extend_temp Lambda lambda (U_thm3 Lambda lambda h_Lambda h_lambda) (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n ((thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m + j + 1) = Nat.ceil (lambda * extend_temp Lambda lambda (U_thm3 Lambda lambda h_Lambda h_lambda) (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n ((thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m + j)) := by
          unfold extend_temp; simp +decide [ *, Nat.add_assoc ] ; (
          exact fun j a => rfl)
        generalize_proofs at *; (
        convert h_geo_seq_def j hj using 1
        generalize_proofs at *; (
        exact ‹∀ i < ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).m + 1 + U_thm3 Lambda lambda h_Lambda h_lambda, ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda ( k + 1 ) ).n i = extend_temp Lambda lambda ( U_thm3 Lambda lambda h_Lambda h_lambda ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).m ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).n i› _ ( by linarith! [ show m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k = ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).m from rfl ] ) |> Eq.trans <| by rfl;);
        rename_i h; specialize h ( m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k + j ) ( by linarith [ show m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k = ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).m from rfl ] ) ; aesop;))
      generalize_proofs at *; (
      aesop ( simp_config := { singlePass := true } ) ;)
    generalize_proofs at *; (
    exact h_geo_bound)

/-
The geometric growth is bounded by $\lambda + \epsilon$.
-/
lemma thm3_seq_v2_geo_bound (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) (k : ℕ) (j : ℕ) (hj : j < U_thm3 Lambda lambda h_Lambda h_lambda) :
  let epsilon := epsilon_thm3 Lambda lambda h_Lambda h_lambda
  let m_k := m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k
  let n := n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda
  (n (m_k + j + 1) : ℝ) < (lambda + epsilon) * n (m_k + j) := by
    -- By definition of `epsilon_thm3`, we know that `1 < epsilon * n(m_k + j)`.
    have h_epsilon_mul_n : 1 < epsilon_thm3 Lambda lambda h_Lambda h_lambda * (n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k + j) : ℝ) := by
      have h_eps : 1 < epsilon_thm3 Lambda lambda h_Lambda h_lambda * (n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k + j)) := by
        have h_i : m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k + j ≥ m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda 0 - 1 := by
          refine' Nat.le_trans _ ( Nat.le_add_right _ _ ) ; induction' k with k ih <;> simp_all +decide [ m_seq_thm3_final_v2 ] ; (
          -- By definition of `thm3_seq_v2`, we know that the m component is strictly increasing.
          have h_m_inc : ∀ k, (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda (k + 1)).m := by
            intro k; exact (by
            exact step_thm3_strong_v2_props Lambda lambda ( U_thm3 Lambda lambda h_Lambda h_lambda ) k ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.m ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.n ) h_Lambda ⟨ h_lambda.1, lambda_lt_two Lambda lambda h_Lambda h_lambda.2 ⟩ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.h_m ) ( fun i hi => ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.h_pos ) i hi ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.h_mono ) |>.1 |> lt_of_lt_of_le ( by linarith [ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.h_m ) ] ) ;)
          generalize_proofs at *; (
          linarith [ h_m_inc k ])) ;
        have h_eps : epsilon_thm3 Lambda lambda h_Lambda h_lambda > 0 := by
          unfold epsilon_thm3
          generalize_proofs at *; (
          exact Classical.choose_spec ‹∃ x ∈ Ioo 0 1, lambda + x < 2 ∧ 1 / (lambda + x) + 1 / (Lambda + x) > 1› |>.1 |>.1)
        generalize_proofs at *; (
        have := thm3_seq_v2_gt_epsilon Lambda lambda h_Lambda h_lambda ( m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k + j ) h_i; nlinarith [ mul_div_cancel₀ 1 h_eps.ne' ] ;)
      generalize_proofs at *; (
      convert h_eps using 1)
    generalize_proofs at *; (
    -- By definition of `n_seq_thm3_final_v2`, we know that `n(m_k+j+1) = Nat.ceil (lambda * n(m_k+j))`.
    have h_n_succ : n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k + j + 1) = Nat.ceil (lambda * n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k + j)) := by
      exact thm3_seq_v2_geo_recurrence Lambda lambda h_Lambda h_lambda k j hj
    generalize_proofs at *; (
    simp +zetaDelta at *; (
    rw [ h_n_succ ] ; exact lt_of_le_of_lt ( Nat.ceil_lt_add_one ( mul_nonneg ( by linarith ) ( Nat.cast_nonneg _ ) ) |> le_of_lt ) ( by linarith ) ;)))

/-
The terms in the geometric part of the sequence are bounded by the explicit geometric formula.
-/
lemma thm3_seq_v2_upper_bound_explicit (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) (k : ℕ) (j : ℕ) (hj : j ≤ U_thm3 Lambda lambda h_Lambda h_lambda) :
  let epsilon := epsilon_thm3 Lambda lambda h_Lambda h_lambda
  let m_k := m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k
  let n := n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda
  (n (m_k + j) : ℝ) < (Lambda + epsilon) * (lambda + epsilon) ^ j * n (m_k - 1) := by
    induction' j with j ih generalizing k <;> simp_all +decide [ pow_succ' ];
    · convert thm3_seq_v2_jump_bound Lambda lambda h_Lambda h_lambda k using 1;
    · have h_geo_bound : let epsilon := epsilon_thm3 Lambda lambda h_Lambda h_lambda
        let m_k := m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k
        let n := n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda
        (n (m_k + j + 1) : ℝ) < (lambda + epsilon) * n (m_k + j) := by
          apply thm3_seq_v2_geo_bound; linarith;
      generalize_proofs at *; (
      have := ih k ( Nat.le_of_succ_le hj ) ; simp_all +decide [ mul_assoc ] ; ring_nf at *; nlinarith;)

/-
Helper lemma for the geometric sum inequality.
-/
lemma sum_geometric_ineq_aux (L l e : ℝ) (U : ℕ)
  (h_pos : L + e > 0)
  (h_r_pos : l + e > 0)
  (h_r_lt_one : 1 / (l + e) < 1)
  (h_cond : (l + e) ^ (-(U + 1 : ℤ)) < (L + e) * (1 / (l + e) + 1 / (L + e) - 1)) :
  (1 / (L + e)) * ∑ j ∈ Finset.range (U + 1), (1 / (l + e)) ^ j > 1 := by
    -- By multiplying both sides of the inequality by $(L + e)$, we obtain the desired result.
    field_simp at *; (
    rw [ geom_sum_eq ];
    · rw [ lt_div_iff_of_neg ] <;> norm_cast at * <;> norm_num at *;
      · nlinarith [ mul_inv_cancel₀ ( ne_of_gt h_r_pos ), mul_inv_cancel₀ ( ne_of_gt ( pow_pos h_r_pos ( U + 1 ) ) ) ];
      · exact inv_lt_one_of_one_lt₀ h_r_lt_one;
    · rw [ Ne.eq_def, div_eq_iff ] <;> linarith);

/-
The sum of the geometric series is large enough (using the auxiliary lemma).
-/
lemma sum_geometric_ineq (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) :
  let epsilon := epsilon_thm3 Lambda lambda h_Lambda h_lambda
  let U := U_thm3 Lambda lambda h_Lambda h_lambda
  (1 / (Lambda + epsilon)) * ∑ j ∈ Finset.range (U + 1), (1 / (lambda + epsilon)) ^ j > 1 := by
    apply sum_geometric_ineq_aux;
    · unfold epsilon_thm3
      generalize_proofs at *;
      linarith [ Classical.choose_spec ‹∃ x ∈ Ioo 0 1, lambda + x < 2 ∧ 1 / ( lambda + x ) + 1 / ( Lambda + x ) > 1› |>.1.1 ];
    · unfold epsilon_thm3;
      generalize_proofs at *; (
      linarith [ Classical.choose_spec ‹∃ x ∈ Ioo 0 1, lambda + x < 2 ∧ 1 / ( lambda + x ) + 1 / ( Lambda + x ) > 1› |>.1.1 ]);
    · -- Since $\lambda > 1$ and $\epsilon > 0$, their sum $\lambda + \epsilon$ is greater than 1.
      have h_sum_gt_one : lambda + epsilon_thm3 Lambda lambda h_Lambda h_lambda > 1 := by
        unfold epsilon_thm3
        generalize_proofs at *; (
        linarith [ Classical.choose_spec ‹∃ x ∈ Ioo 0 1, lambda + x < 2 ∧ 1 / ( lambda + x ) + 1 / ( Lambda + x ) > 1› |>.1.1 ]);
      exact div_lt_self zero_lt_one h_sum_gt_one;
    · convert U_thm3_spec Lambda lambda h_Lambda h_lambda using 1 ; ring_nf

/-
The sum of reciprocals of the terms after the jump is strictly greater than the reciprocal of the term before the jump.
-/
lemma thm3_sum_ineq_v2 (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) (k : ℕ) :
  let m_k := m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k
  let n := n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda
  let U := U_thm3 Lambda lambda h_Lambda h_lambda
  (1 : ℝ) / n (m_k - 1) < ∑ j ∈ Finset.range (U + 1), (1 : ℝ) / n (m_k + j) := by
    -- Let's obtain the definitions of `m_k`, `n`, and `U`.
    set m_k := m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k
    set n := n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda
    set U := U_thm3 Lambda lambda h_Lambda h_lambda;
    -- By `thm3_seq_v2_upper_bound_explicit`, we have $1 / n (m_k + j) > 1 / ((Lambda + epsilon) * (lambda + epsilon)^j * n (m_k - 1))$ for each $j$.
    have h_term_bound : ∀ j ∈ Finset.range (U + 1), (1 : ℝ) / n (m_k + j) > 1 / ((Lambda + (epsilon_thm3 Lambda lambda h_Lambda h_lambda)) * (lambda + (epsilon_thm3 Lambda lambda h_Lambda h_lambda)) ^ j * n (m_k - 1)) := by
      intro j hj
      have h_term_bound : (n (m_k + j) : ℝ) < (Lambda + (epsilon_thm3 Lambda lambda h_Lambda h_lambda)) * (lambda + (epsilon_thm3 Lambda lambda h_Lambda h_lambda)) ^ j * n (m_k - 1) := by
        apply_rules [ thm3_seq_v2_upper_bound_explicit ];
        linarith [ Finset.mem_range.mp hj ]
      exact (by
      -- Since $n (m_k + j)$ is positive, taking reciprocals reverses the inequality.
      have h_pos : 0 < n (m_k + j) := by
        have h_pos : StrictMono (n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda) := by
          exact n_seq_thm3_final_v2_mono Lambda lambda h_Lambda h_lambda
        generalize_proofs at *; (
        exact Nat.pos_of_ne_zero fun h => by have := h_pos ( show m_k + j > 0 from Nat.pos_of_ne_zero ( by aesop ) ) ; aesop;)
      generalize_proofs at *; (
      exact one_div_lt_one_div_of_lt ( by positivity ) h_term_bound |> lt_of_le_of_lt ( by norm_num ) |> lt_of_lt_of_le <| le_rfl;));
    -- By `sum_geometric_ineq`, we have $\frac{1}{\Lambda+\epsilon} \sum_{j=0}^U (\frac{1}{\lambda+\epsilon})^j > 1$.
    have h_sum_geometric : (1 / (Lambda + (epsilon_thm3 Lambda lambda h_Lambda h_lambda))) * ∑ j ∈ Finset.range (U + 1), (1 / (lambda + (epsilon_thm3 Lambda lambda h_Lambda h_lambda))) ^ j > 1 := by
      convert sum_geometric_ineq Lambda lambda h_Lambda h_lambda using 1;
    refine' lt_of_le_of_lt _ ( Finset.sum_lt_sum_of_nonempty ( by norm_num ) h_term_bound ) ; simp_all +decide [mul_assoc,
      mul_comm] ;
    simp_all +decide [ ← mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] ; nlinarith [ inv_nonneg.2 ( show ( 0 : ℝ ) ≤ n ( m_k - 1 ) by positivity ) ] ;

/-
Local version of Remark 1: if the growth condition holds locally, the sum inequality holds locally.
-/
lemma remark_cond_local (n : ℕ → ℕ) (M : ℕ) (i : ℕ)
  (h_pos : ∀ j, i ≤ j → j ≤ M → 0 < n j)
  (h_growth : ∀ j, i ≤ j → j < M → n (j + 1) ≤ 2 * n j)
  (hi : i < M) :
  (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i M, (1 : ℝ) / n j) + (1 : ℝ) / n M := by
    -- Let's choose any $j$ such that $i \leq j < M$.
    have h_inductive_step : ∀ j, i ≤ j → j < M → (1 / (n j : ℝ)) ≤ (1 / (n (j + 1) : ℝ)) + (1 / (n (j + 1) : ℝ)) := by
      intro j hj₁ hj₂; rw [ ← add_div, div_le_div_iff₀ ] <;> norm_cast <;> linarith [ h_pos j hj₁ ( by linarith ), h_pos ( j + 1 ) ( by linarith ) ( by linarith ), h_growth j hj₁ hj₂ ] ;
    generalize_proofs at *; (
    -- By induction on $j$ from $i$ to $M-1$, we can show that $1/n_i \leq \sum_{j=i}^{M-1} 1/n_{j+1} + 1/n_M$.
    have h_induction : ∀ j, i ≤ j → j ≤ M → (1 / (n i : ℝ)) ≤ (∑ k ∈ Finset.Ioc i j, (1 / (n k : ℝ))) + (1 / (n j : ℝ)) := by
      -- We proceed by induction on $j$.
      intro j hj₁ hj₂
      induction' hj₁ with j hj ih
      generalize_proofs at *; (
      norm_num +zetaDelta at *);
      rw [ Finset.sum_Ioc_succ_top ] <;> try linarith! [ Nat.succ_le_succ hj ] ; ; linarith! [ ih ( Nat.le_of_succ_le hj₂ ), h_inductive_step j hj ( Nat.lt_of_succ_le hj₂ ) ] ;
    generalize_proofs at *; (
    exact h_induction M hi.le le_rfl |> le_trans <| by norm_num;))

/-
Define the final sequence of block end indices and prove it is strictly increasing.
-/
noncomputable def final_M_seq (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) (k : ℕ) : ℕ :=
  m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k - 1

lemma final_M_seq_strictMono (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) :
  StrictMono (final_M_seq Lambda lambda h_Lambda h_lambda) := by
    refine' strictMono_nat_of_lt_succ _;
    intro n
    unfold final_M_seq
    generalize_proofs at *; (
    refine' lt_tsub_iff_left.mpr _;
    rw [ add_tsub_cancel_of_le ];
    · have := step_thm3_strong_v2_props Lambda lambda ( U_thm3 Lambda lambda h_Lambda h_lambda ) n ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n |> Thm3Data.m ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n |> Thm3Data.n ) ?_ ?_ ?_ ?_ ?_ <;> norm_num at * <;> try linarith [ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n |> Thm3Data.h_m ) ] ;
      any_goals intro i hi; exact ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n |> Thm3Data.h_pos ) i hi
      all_goals generalize_proofs at *;
      · exact lt_of_lt_of_le ( Nat.lt_succ_self _ ) ( this.1.trans' ( Nat.le_add_right _ _ ) ) |> lt_of_lt_of_le <| le_rfl;
      · exact ⟨ h_lambda.1, by rw [ lt_div_iff₀ ] at h_lambda <;> nlinarith ⟩;
      · exact ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n |> Thm3Data.h_mono );
    · exact Nat.one_le_iff_ne_zero.mpr ( by exact ne_of_gt <| by { exact Nat.pos_of_ne_zero <| by { exact ne_of_gt <| by { exact Nat.pos_of_ne_zero <| by { exact ne_of_gt <| by { exact Nat.pos_of_ne_zero <| by { exact ne_of_gt <| by { exact (thm3_seq_v2 Lambda lambda h_Lambda h_lambda n).h_m } } } } } } } ))

/-
The inequality condition holds at the jump indices for the final sequence.
-/
lemma thm3_seq_v2_ineq_jump_all (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) (k : ℕ) :
  let M := final_M_seq Lambda lambda h_Lambda h_lambda
  let n := n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda
  (1 : ℝ) / n (M k) ≤ (∑ j ∈ Finset.Ioc (M k) (M (k + 1)), (1 : ℝ) / n j) + (1 : ℝ) / n (M (k + 1)) := by
    -- By definition of $U$, we know that $m_{k+1} \geq m_k + 1 + U$.
    have h_m_k1_ge_m_k_plus_1_plus_U : ∀ k, m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (k + 1) ≥ m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k + 1 + U_thm3 Lambda lambda h_Lambda h_lambda := by
      -- By definition of `step_thm3_strong_v2`, the new sequence is constructed by extending the previous sequence with a geometric sequence of length `U+1`.
      intros k
      simp [m_seq_thm3_final_v2];
      have := step_thm3_strong_v2_props Lambda lambda ( U_thm3 Lambda lambda h_Lambda h_lambda ) k ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.m ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.n ) h_Lambda ⟨ h_lambda.1, by linarith [ lambda_lt_two Lambda lambda h_Lambda h_lambda.2 ] ⟩ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.h_m ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.h_pos ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.h_mono ) ; aesop;
    generalize_proofs at *; (
    -- By definition of $U$, we know that $m_{k+1} \geq m_k + 1 + U$, so $m_k+U \leq m_{k+1}-1$.
    have h_m_k_plus_U_le_m_k1_minus_1 : ∀ k, m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k + U_thm3 Lambda lambda h_Lambda h_lambda ≤ m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (k + 1) - 1 := by
      exact fun k => Nat.le_sub_one_of_lt ( by linarith [ h_m_k1_ge_m_k_plus_1_plus_U k ] ) ;
    generalize_proofs at *; (
    -- By definition of $U$, we know that $1/n(m_k-1) < \sum_{j=0}^U 1/n(m_k+j)$.
    have h_sum_ineq : 1 / (n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k - 1) : ℝ) < ∑ j ∈ Finset.range (U_thm3 Lambda lambda h_Lambda h_lambda + 1), 1 / (n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k + j) : ℝ) := by
      exact thm3_sum_ineq_v2 Lambda lambda h_Lambda h_lambda k
    generalize_proofs at *; (
    -- By definition of $U$, we know that $m_k+U \leq m_{k+1}-1$, so the sum on the RHS is over $j \in \{m_k, \dots, m_k+U\}$.
    have h_sum_range : Finset.Ioc (m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k - 1) (m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda (k + 1) - 1) ⊇ Finset.image (fun j => m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k + j) (Finset.range (U_thm3 Lambda lambda h_Lambda h_lambda + 1)) := by
      exact Finset.image_subset_iff.mpr fun x hx => Finset.mem_Ioc.mpr ⟨ by linarith [ Finset.mem_range.mp hx, Nat.sub_add_cancel ( show 1 ≤ m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k from Nat.pos_of_ne_zero ( by
                                                                                                                                      induction k <;> simp_all +decide [ m_seq_thm3_final_v2 ];
                                                                                                                                      · exact ne_of_gt ( init_thm3_data Lambda lambda h_Lambda h_lambda |>.h_m );
                                                                                                                                      · linarith [ h_m_k1_ge_m_k_plus_1_plus_U ‹_›, h_m_k_plus_U_le_m_k1_minus_1 ‹_›, Nat.zero_le ( U_thm3 Lambda lambda h_Lambda h_lambda ) ] ) ) ], by linarith [ Finset.mem_range.mp hx, h_m_k_plus_U_le_m_k1_minus_1 k ] ⟩
    generalize_proofs at *; (
    refine' le_add_of_le_of_nonneg ( le_trans h_sum_ineq.le _ ) ( by positivity ) ; (
    exact le_trans ( by rw [ Finset.sum_image ( by intros a ha b hb hab; linarith ) ] ) ( Finset.sum_le_sum_of_subset_of_nonneg h_sum_range fun _ _ _ => by positivity ) ;)))))

/-
The ratio of consecutive terms is at most 2 in the smooth intervals for all blocks.
-/
lemma thm3_seq_v2_ratio_le_two_smooth_all (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) (k : ℕ) :
  let M := final_M_seq Lambda lambda h_Lambda h_lambda
  let n := n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda
  ∀ i, M k < i → i < M (k + 1) → (n (i + 1) : ℝ) / n i ≤ 2 := by
    intro M n i hi_lt hi_ge
    have h_step : let res := step_thm3_strong_v2 Lambda lambda (U_thm3 Lambda lambda h_Lambda h_lambda) k (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n h_Lambda ⟨h_lambda.left, lambda_lt_two Lambda lambda h_Lambda h_lambda.right⟩ (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).h_m (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).h_pos (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).h_mono
      let m_next := res.1
      let n_next := res.2
      ∀ i, (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m ≤ i → i < m_next - 1 → (n_next (i + 1) : ℝ) / n_next i ≤ 2 := by
        intros res m_next n_next i hi_le hi_lt
        generalize_proofs at *; (
        have := step_thm3_strong_v2_props Lambda lambda (U_thm3 Lambda lambda h_Lambda h_lambda) k (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n h_Lambda ⟨h_lambda.left, lambda_lt_two Lambda lambda h_Lambda h_lambda.right⟩ (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).h_m (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).h_pos (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).h_mono
        generalize_proofs at *; (
        by_cases hi : i < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m + 1 + U_thm3 Lambda lambda h_Lambda h_lambda - 1 <;> simp_all +decide ;
        · have h_ratio : (n_next (i + 1) : ℝ) / n_next i = (Nat.ceil (lambda * n_next i) : ℝ) / n_next i := by
            have h_ratio : n_next (i + 1) = Nat.ceil (lambda * n_next i) := by
              have := this.2.1 (i + 1) (by
              linarith [ Nat.sub_add_cancel ( show 1 ≤ ( step_thm3_strong_v2 Lambda lambda ( U_thm3 Lambda lambda h_Lambda h_lambda ) k ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).m ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).n h_Lambda ‹_› ‹_› ‹_› ‹_› ).1 from Nat.one_le_iff_ne_zero.mpr <| by aesop_cat ) ])
              convert this using 1
              generalize_proofs at *; (
              have h_ratio : n_next i = extend_temp Lambda lambda (U_thm3 Lambda lambda h_Lambda h_lambda) (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).m (thm3_seq_v2 Lambda lambda h_Lambda h_lambda k).n i := by
                grind
              generalize_proofs at *; (
              unfold extend_temp at * ; simp_all +decide ;
              split_ifs <;> simp_all +decide [ Nat.succ_sub ] ; ring_nf
              generalize_proofs at *; (
              linarith [ Nat.sub_add_cancel ( show 1 ≤ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).m from by linarith ) ]);
              · grind;
              · linarith [ Nat.sub_add_cancel ( by linarith : ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k ).m ≤ i ) ];
              · exact rfl))
            generalize_proofs at *; (
            rw [h_ratio])
          generalize_proofs at *; (
          by_cases hi_pos : 0 < n_next i <;> simp_all +decide [ div_le_iff₀ ];
          exact_mod_cast Nat.ceil_le.mpr ( by norm_num; nlinarith [ show ( n_next i : ℝ ) ≥ 1 by exact_mod_cast hi_pos ] ) ;);
        · grind))
    generalize_proofs at *; (
    -- By definition of `n_seq_thm3_final_v2`, we know that `n i = n_next i` for `i` in the range of `next_thm3_data_v2`.
    have h_n_eq : n i = (thm3_seq_v2 Lambda lambda h_Lambda h_lambda (k + 1)).n i ∧ n (i + 1) = (thm3_seq_v2 Lambda lambda h_Lambda h_lambda (k + 1)).n (i + 1) := by
      apply And.intro (n_seq_thm3_final_v2_eq Lambda lambda h_Lambda h_lambda (k + 1) i (by
      exact hi_ge.trans_le ( Nat.sub_le _ _ ) |> lt_of_lt_of_le <| Nat.le_refl _;)) (n_seq_thm3_final_v2_eq Lambda lambda h_Lambda h_lambda (k + 1) (i + 1) (by
      exact Nat.succ_lt_of_lt_pred ( by simpa [ M ] using hi_ge ) ;))
    generalize_proofs at *; (
    -- Substitute `n i` and `n (i + 1)` with their counterparts from `thm3_seq_v2` using `h_n_eq`.
    rw [h_n_eq.left, h_n_eq.right] at *;
    generalize_proofs at *; (
    convert h_step i _ _ using 1 <;> norm_num [ M ] at * <;> linarith! [ Nat.sub_add_cancel ( show 1 ≤ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda k |> Thm3Data.m ) from by linarith ) ] ;)))

/-
The inequality condition holds for the smooth intervals for all blocks.
-/
lemma thm3_seq_v2_ineq_smooth_all (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) (k : ℕ) :
  let M := final_M_seq Lambda lambda h_Lambda h_lambda
  let n := n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda
  ∀ i, M k < i → i < M (k + 1) →
    (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i (M (k + 1)), (1 : ℝ) / n j) + (1 : ℝ) / n (M (k + 1)) := by
      intros M n i hi1 hi2
      apply le_trans (remark_cond_local n (M (k + 1)) i
        (fun j hj => by
          exact fun j => by have := n_seq_thm3_final_v2_mono Lambda lambda h_Lambda h_lambda; exact Nat.cast_pos.mp ( lt_of_lt_of_le ( Nat.cast_pos.mpr ( show 0 < n 0 from by
                                                                                                                                                            -- By definition of `n_seq_thm3_final_v2`, we know that `n 0` is the first element of the sequence, which is `1`.
                                                                                                                                                            have h_n0 : n 0 = 1 := by
                                                                                                                                                              convert n_seq_thm3_final_v2_eq Lambda lambda h_Lambda h_lambda 0 0 _ using 1
                                                                                                                                                              generalize_proofs at *; (
                                                                                                                                                              exact ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda 0 ).h_m.trans_lt' ( by norm_num ) ;)
                                                                                                                                                            exact h_n0.symm ▸ by norm_num; ) ) ( this.monotone ( Nat.zero_le _ ) ) ) ;)
        (fun j hj hj' => by
          have := thm3_seq_v2_ratio_le_two_smooth_all Lambda lambda h_Lambda h_lambda k j (by
          linarith! [ hi1, hi2, hj, hj' ]) (by
          exact hj')
          generalize_proofs at *; (
          exact_mod_cast ( div_le_iff₀ ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by
            exact ne_of_gt <| Nat.pos_of_ne_zero <| by intro h; have := n_seq_thm3_final_v2_mono Lambda lambda h_Lambda h_lambda ( show j > 0 from by linarith ) ; aesop; ) |>.1 this ) ;))
        (by
        linarith)) (by
        norm_num +zetaDelta at *)

/-
The inequality condition holds for the initial block.
-/
lemma thm3_seq_v2_ineq_initial (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) :
  let M0 := final_M_seq Lambda lambda h_Lambda h_lambda 0
  let n := n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda
  ∀ i < M0, (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i M0, (1 : ℝ) / n j) + (1 : ℝ) / n M0 := by
    -- Let's choose any $i < M0$.
    intro M0 n i hi
    by_cases h_case : i < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda 0).m - 1;
    · -- For $i < m_0 - 1$, we use the fact that $n_i = 2^i$.
      have h_exp : ∀ i < (thm3_seq_v2 Lambda lambda h_Lambda h_lambda 0).m, n i = 2 ^ i := by
        intro i hi
        have h_exp : n i = (thm3_seq_v2 Lambda lambda h_Lambda h_lambda 0).n i := by
          exact n_seq_thm3_final_v2_eq Lambda lambda h_Lambda h_lambda 0 i hi
        generalize_proofs at *; (
        exact h_exp);
      -- Applying the lemma `remark_cond_local` to the interval $[i, m_0-1]$.
      have h_remark : (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i ((thm3_seq_v2 Lambda lambda h_Lambda h_lambda 0).m - 1), (1 : ℝ) / n j) + (1 : ℝ) / n ((thm3_seq_v2 Lambda lambda h_Lambda h_lambda 0).m - 1) := by
        apply_rules [ remark_cond_local ];
        · exact fun j hj₁ hj₂ => h_exp j ( lt_of_le_of_lt hj₂ ( Nat.pred_lt ( ne_bot_of_gt ( show 0 < ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda 0 |> Thm3Data.m ) from by linarith [ show 0 < ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda 0 |> Thm3Data.m ) from by linarith [ show 0 < ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda 0 |> Thm3Data.m ) from by exact ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda 0 |> Thm3Data.h_m ) ] ] ) ) ) ) ▸ pow_pos ( by norm_num ) _;
        · intro j hj₁ hj₂; rw [ h_exp j ( by omega ), h_exp ( j + 1 ) ( by omega ) ] ; ring_nf; norm_num;
      exact h_remark;
    · exact False.elim (h_case hi)

/-
The sequence satisfies the inequality conditions required for Proposition 1.
-/
lemma thm3_seq_v2_satisfies_ineq (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) :
  let M := final_M_seq Lambda lambda h_Lambda h_lambda
  let n := n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda
  (∀ i < M 0, (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i (M 0), (1 : ℝ) / n j) + (1 : ℝ) / n (M 0)) ∧
  (∀ k : ℕ, ∀ i, M k ≤ i → i < M (k + 1) →
    (1 : ℝ) / n i ≤ (∑ j ∈ Finset.Ioc i (M (k + 1)), (1 : ℝ) / n j) + (1 : ℝ) / n (M (k + 1))) := by
      refine' ⟨ _, _ ⟩;
      · convert thm3_seq_v2_ineq_initial Lambda lambda h_Lambda h_lambda using 1;
      · intro k i hi₁ hi₂;
        by_cases hi₃ : i = final_M_seq Lambda lambda h_Lambda h_lambda k;
        · convert thm3_seq_v2_ineq_jump_all Lambda lambda h_Lambda h_lambda k using 1 ; aesop ( simp_config := { singlePass := true } ) ;
          rw [ hi₃ ];
        · exact thm3_seq_v2_ineq_smooth_all Lambda lambda h_Lambda h_lambda k i ( lt_of_le_of_ne hi₁ ( Ne.symm hi₃ ) ) hi₂

/-
The set S is infinite.
-/

lemma S_infinite (S : Set ℕ) (hS : S_cond S) : S.Infinite := by
  cases' hS with z hz
  generalize_proofs at *; (
  -- Suppose $S$ is finite. Let $M = \max S$. Let $k$ be an odd number greater than $M$.
  by_contra h_finite
  obtain ⟨M, hM⟩ : ∃ M, ∀ s ∈ S, s ≤ M := by
    exact Set.Finite.bddAbove <| Classical.not_not.mp h_finite
  generalize_proofs at *; (
  obtain ⟨ s, hs ⟩ := hz.2 ( 2 * M + 1 ) ( by simp +decide [ parity_simps ] ) ; linarith [ hM s hs.1, Nat.le_of_dvd ( z s hs.1 ) hs.2 ] ;))

/-
The sequence enumerating S satisfies the growth condition n_{i+1} <= 2n_i.
-/
noncomputable def enum_S (S : Set ℕ) (i : ℕ) : ℕ := Nat.nth (· ∈ S) i

lemma enum_S_growth (S : Set ℕ) (hS : S_cond S) (i : ℕ) :
  enum_S S (i + 1) ≤ 2 * enum_S S i := by
    have h_enum_le : enum_S S i ∈ S ∧ 2 * enum_S S i ∈ S := by
      have h_enum_le : ∀ i, enum_S S i ∈ S := by
        exact fun i => Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite S hS ) _;
      generalize_proofs at *; (
      exact ⟨ h_enum_le i, hS.2.1 _ ( h_enum_le i ) ⟩)
    generalize_proofs at *; (
    have h_enum_le : ∀ x ∈ S, x > enum_S S i → enum_S S (i + 1) ≤ x := by
      intros x hx hx_gt
      have h_enum_le : enum_S S (i + 1) ≤ x := by
        have h_enum_le : Nat.nth (fun x => x ∈ S) (i + 1) ≤ x := by
          rw [ Nat.nth_eq_sInf ];
          refine' Nat.sInf_le ⟨ hx, _ ⟩
          generalize_proofs at *; (
          intro k hk; exact lt_of_le_of_lt ( Nat.nth_monotone ( show { x | x ∈ S }.Infinite from S_infinite S hS ) ( Nat.le_of_lt_succ hk ) ) hx_gt;)
        exact h_enum_le
      exact h_enum_le
    generalize_proofs at *; (
    exact h_enum_le _ ( by tauto ) ( by linarith [ show 0 < enum_S S i from Nat.pos_of_ne_zero fun hi => by have := hS.1 _ ( by tauto ) ; aesop ] )))

/-
For any odd integer k and bound C, S contains a multiple of k greater than C.
-/
lemma exists_multiple_gt (S : Set ℕ) (hS : S_cond S) (k : ℕ) (hk : Odd k) (C : ℕ) :
  ∃ s ∈ S, k ∣ s ∧ s > C := by
    have := hS.2.2 k hk; cases' this with s hs; use 2^ (C + 1) * s; simp_all +decide ;
    refine' ⟨ _, dvd_mul_of_dvd_right hs.2 _, _ ⟩;
    · exact Nat.recOn ( C + 1 ) ( by simpa using hs.1 ) fun n ihn => by simpa only [ pow_succ', mul_assoc ] using hS.2.1 _ ihn;
    · -- Since $s$ is a positive integer, we have $2^{C+1} \cdot s > C$.
      have h_exp : 2 ^ (C + 1) > C := by
        exact Nat.recOn C ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at ihn ⊢ ; linarith;
      have h_mul : 2 ^ (C + 1) * s > C * s := by
        exact Nat.mul_lt_mul_of_pos_right h_exp ( Nat.pos_of_ne_zero ( by rintro rfl; exact absurd ( hS.1 0 hs.1 ) ( by norm_num ) ) )
      have h_final : C * s ≥ C := by
        exact Nat.le_mul_of_pos_right _ ( Nat.pos_of_ne_zero ( by rintro rfl; have := hS.1 0; aesop ) )
      linarith [h_mul, h_final]

/-
S is closed under multiplication by powers of 2.
-/
lemma pow_two_mul_mem_S (S : Set ℕ) (hS : S_cond S) (s : ℕ) (hs : s ∈ S) (k : ℕ) :
  2 ^ k * s ∈ S := by
    induction' k with k ih <;> simp_all +decide [ pow_succ', mul_assoc ];
    exact hS.2.1 _ ih

/-
Definitions of L, k, l for Theorem 4 and proof that l is odd.
-/
def L_val_thm4 (S : Set ℕ) (K : ℕ) (b : ℕ) : ℕ :=
  Nat.lcm (Finset.lcm (Finset.range K) (fun i => enum_S S i)) b

def k_val_thm4 (S : Set ℕ) (K : ℕ) (b : ℕ) : ℕ :=
  (L_val_thm4 S K b).factorization 2

def l_val_thm4 (S : Set ℕ) (K : ℕ) (b : ℕ) : ℕ :=
  (L_val_thm4 S K b) / 2 ^ (k_val_thm4 S K b)

lemma l_val_thm4_odd (S : Set ℕ) (K : ℕ) (b : ℕ) (hS : S_cond S) (hb : b > 0) :
  Odd (l_val_thm4 S K b) := by
    -- By definition of $l_val_thm4$, we know that $l_val_thm4 S K b$ is the odd part of $L_val S K b$, which is not divisible by 2.
    have h_odd : Odd (l_val_thm4 S K b) := by
      have h_not_div : ¬(2 ∣ l_val_thm4 S K b) := by
        unfold l_val_thm4
        generalize_proofs at *; (
        rw [ Nat.dvd_div_iff_mul_dvd ];
        · rw [ ← pow_succ, Nat.Prime.pow_dvd_iff_le_factorization ] <;> norm_num [ k_val_thm4, L_val_thm4 ];
          exact ⟨ fun x hx => Nat.ne_of_gt <| Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite S hS ) x |> fun h => hS.1 _ h, hb.ne' ⟩;
        · exact Nat.ordProj_dvd _ _)
      grind +ring
    generalize_proofs at *; (
    exact h_odd)

/-
Corrected definitions (v2) using L_val_thm4.
-/
noncomputable def J_idx_v2 (S : Set ℕ) (K : ℕ) (b : ℕ) (hS : S_cond S) (hb : b > 0) : ℕ :=
  let l := l_val_thm4 S K b
  let C := enum_S S K
  let h_odd := l_val_thm4_odd S K b hS hb
  let P := fun j => l ∣ enum_S S j ∧ enum_S S j > C
  Nat.find (show ∃ j, P j from by
    obtain ⟨s, hs, hdiv, hgt⟩ := exists_multiple_gt S hS l h_odd C
    use Nat.count (· ∈ S) s
    have h_eq : enum_S S (Nat.count (· ∈ S) s) = s := by
      unfold enum_S
      rw [Nat.nth_count hs]
    dsimp [P]
    rw [h_eq]
    exact ⟨hdiv, hgt⟩
  )

noncomputable def m_val_v2 (S : Set ℕ) (K : ℕ) (b : ℕ) (hS : S_cond S) (hb : b > 0) : ℕ :=
  let nJ := enum_S S (J_idx_v2 S K b hS hb)
  let nK := enum_S S (K - 1)
  Nat.ceil (Real.logb 2 ((nJ : ℝ) / (nK : ℝ)))

/-
m_val_v2 is at least 1.
-/
lemma m_val_v2_pos (S : Set ℕ) (K : ℕ) (b : ℕ) (hS : S_cond S) (hb : b > 0) (hK : K ≥ 1) :
  1 ≤ m_val_v2 S K b hS hb := by
    refine' Nat.ceil_pos.mpr ( Real.logb_pos _ _ ) <;> norm_num [ hK ];
    rw [ one_lt_div ] <;> norm_cast;
    · unfold J_idx_v2;
      refine' Nat.nth_strictMono _ _;
      · exact S_infinite {x | x ∈ S} hS;
      · simp +zetaDelta at *;
        intro m hm₁ hm₂; exact Nat.nth_monotone ( show Set.Infinite S from S_infinite S hS ) ( by omega ) ;
    · exact Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite S hS ) _ |> fun x => hS.1 _ x

/-
Definitions of J_idx_v3, m_val_v3, extended_seq_v3, and M_val_v3.
-/
noncomputable def J_idx_v3 (S : Set ℕ) (K : ℕ) (b : ℕ) (hS : S_cond S) (hb : b > 0) : ℕ :=
  let l := l_val_thm4 S K b
  let C := enum_S S K
  let h_odd := l_val_thm4_odd S K b hS hb
  let P := fun j => l ∣ enum_S S j ∧ enum_S S j > C
  Nat.find (show ∃ j, P j from by
    obtain ⟨s, hs, hdiv, hgt⟩ := exists_multiple_gt S hS l h_odd C
    use Nat.count (· ∈ S) s
    have h_eq : enum_S S (Nat.count (· ∈ S) s) = s := by
      unfold enum_S
      rw [Nat.nth_count hs]
    dsimp only [P]
    rw [h_eq]
    exact ⟨hdiv, hgt⟩
  )

noncomputable def m_val_v3 (S : Set ℕ) (K : ℕ) (b : ℕ) (hS : S_cond S) (hb : b > 0) : ℕ :=
  let nJ := enum_S S (J_idx_v3 S K b hS hb)
  let nK := enum_S S (K - 1)
  Nat.ceil (Real.logb 2 ((nJ : ℝ) / (nK : ℝ)))

noncomputable def extended_seq_v3 (S : Set ℕ) (K : ℕ) (b : ℕ) (hS : S_cond S) (hb : b > 0) (i : ℕ) : ℕ :=
  let m := m_val_v3 S K b hS hb
  let J := J_idx_v3 S K b hS hb
  let n := enum_S S
  if i < K then n i
  else if i < K + m - 1 then
    2 ^ (i - K + 1) * n (K - 1)
  else
    2 ^ (i - (K + m - 1)) * n J

noncomputable def M_val_v3 (S : Set ℕ) (K : ℕ) (b : ℕ) (hS : S_cond S) (hb : b > 0) : ℕ :=
  let m := m_val_v3 S K b hS hb
  let k := k_val_thm4 S K b
  K + k + 2 * m - 1

/-
m_val_v3 is at least 1.
-/
lemma m_val_v3_pos (S : Set ℕ) (K : ℕ) (b : ℕ) (hS : S_cond S) (hb : b > 0) (hK : K ≥ 1) :
  1 ≤ m_val_v3 S K b hS hb := by
    convert m_val_v2_pos S K b hS hb hK using 1

/-
Formula for the last element of the extended sequence (v3).
-/
lemma last_elem_eq_v3 (S : Set ℕ) (K : ℕ) (b : ℕ) (hS : S_cond S) (hb : b > 0) (hK : K ≥ 1) :
  let M := M_val_v3 S K b hS hb
  let m := m_val_v3 S K b hS hb
  let k := k_val_thm4 S K b
  let J := J_idx_v3 S K b hS hb
  extended_seq_v3 S K b hS hb (M - 1) = 2 ^ (k + m - 1) * enum_S S J := by
    unfold extended_seq_v3 M_val_v3;
    simp +zetaDelta at *;
    split_ifs <;> try omega;
    · exact absurd ‹_› ( by rw [ tsub_tsub, tsub_lt_iff_left ] <;> linarith [ show k_val_thm4 S K b ≥ 0 from Nat.zero_le _, show m_val_v3 S K b hS hb ≥ 1 from m_val_v3_pos S K b hS hb hK ] );
    · rw [ show K + k_val_thm4 S K b + 2 * m_val_v3 S K b hS hb - 1 - 1 - ( K + m_val_v3 S K b hS hb - 1 ) = k_val_thm4 S K b + m_val_v3 S K b hS hb - 1 from by omega ]

/-
The last element of the extended sequence (v3) is a multiple of L.
-/
lemma last_elem_dvd_L_v3 (S : Set ℕ) (K : ℕ) (b : ℕ) (hS : S_cond S) (hb : b > 0) (hK : K ≥ 1) :
  let M := M_val_v3 S K b hS hb
  L_val_thm4 S K b ∣ extended_seq_v3 S K b hS hb (M - 1) := by
    convert Nat.dvd_trans ?_ ( dvd_mul_right _ _ ) using 1;
    rotate_left;
    rotate_left;
    exact 2 ^ ( k_val_thm4 S K b + m_val_v3 S K b hS hb - 1 ) * l_val_thm4 S K b;
    exact ( enum_S S ( J_idx_v3 S K b hS hb ) ) / l_val_thm4 S K b;
    · convert last_elem_eq_v3 S K b hS hb hK using 1;
      rw [ mul_assoc, Nat.mul_div_cancel' ];
      exact Nat.find_spec ( _ : ∃ j, l_val_thm4 S K b ∣ enum_S S j ∧ enum_S S j > enum_S S K ) |>.1;
    · rw [ ← Nat.mul_div_cancel' ( Nat.ordProj_dvd ( L_val_thm4 S K b ) 2 ) ];
      refine' mul_dvd_mul _ _;
      · exact pow_dvd_pow _ ( Nat.le_sub_one_of_lt ( Nat.lt_add_of_pos_right ( m_val_v3_pos S K b hS hb hK ) ) );
      · rfl

/-
Case 1: i < K implies n'_i divides the last element (v3).
-/
lemma extended_seq_divides_last_case1_v3 (S : Set ℕ) (K : ℕ) (b : ℕ) (hS : S_cond S) (hb : b > 0) (hK : K ≥ 1) (i : ℕ) (hi : i < K) :
  let M := M_val_v3 S K b hS hb
  extended_seq_v3 S K b hS hb i ∣ extended_seq_v3 S K b hS hb (M - 1) := by
    -- For $i < K$, $n'_i = n_i$ and $n_i$ divides $L$ by definition of $L$.
    have h_div_L : let L := L_val_thm4 S K b; (enum_S S i : ℕ) ∣ L := by
      refine' Nat.dvd_trans _ ( Finset.dvd_lcm ( Finset.mem_range.mpr hi ) ) |> Nat.dvd_trans <| Nat.dvd_lcm_left _ _;
      norm_num +zetaDelta at *;
    convert Nat.dvd_trans h_div_L ( last_elem_dvd_L_v3 S K b hS hb hK ) using 1;
    unfold extended_seq_v3; aesop;

/-
Case 2: K <= i < K + m - 1 implies n'_i divides the last element (v3).
-/
lemma extended_seq_divides_last_case2_v3 (S : Set ℕ) (K : ℕ) (b : ℕ) (hS : S_cond S) (hb : b > 0) (hK : K ≥ 1) (i : ℕ)
  (hi_ge : i ≥ K) (hi_lt : i < K + m_val_v3 S K b hS hb - 1) :
  let M := M_val_v3 S K b hS hb
  extended_seq_v3 S K b hS hb i ∣ extended_seq_v3 S K b hS hb (M - 1) := by
    -- By definition of $extended_seq_v3$, we know that $extended_seq_v3 S K b hS hb i$ divides $2^{i-K+1} n_{K-1}$.
    have h_div1 : extended_seq_v3 S K b hS hb i ∣ 2^(i-K+1) * enum_S S (K - 1) := by
      rw [extended_seq_v3];
      rw [ if_neg ( by linarith ), if_pos hi_lt ]
    generalize_proofs at *; (
    -- By definition of $extended_seq_v3$, we know that $2^{i-K+1} n_{K-1}$ divides $2^{k+m-1} n_J$.
    have h_div2 : 2^(i-K+1) * enum_S S (K - 1) ∣ 2^(k_val_thm4 S K b + m_val_v3 S K b hS hb - 1) * enum_S S (J_idx_v3 S K b hS hb) := by
      have h_div2 : enum_S S (K - 1) ∣ 2^(k_val_thm4 S K b) * l_val_thm4 S K b := by
        have h_div2 : enum_S S (K - 1) ∣ L_val_thm4 S K b := by
          refine' Finset.dvd_lcm ( Finset.mem_range.mpr ( Nat.sub_lt hK zero_lt_one ) ) |> dvd_trans _ |> dvd_trans <| Nat.dvd_lcm_left _ _; aesop;
        generalize_proofs at *; (
        convert h_div2 using 1
        generalize_proofs at *; (
        exact Nat.mul_div_cancel' ( Nat.ordProj_dvd _ _ )))
      generalize_proofs at *; (
      have h_div3 : l_val_thm4 S K b ∣ enum_S S (J_idx_v3 S K b hS hb) := by
        exact Nat.find_spec ( _ : ∃ j, l_val_thm4 S K b ∣ enum_S S j ∧ enum_S S j > enum_S S K ) |>.1
      generalize_proofs at *; (
      refine' dvd_trans _ ( mul_dvd_mul_left _ h_div3 );
      refine' dvd_trans ( mul_dvd_mul_left _ h_div2 ) _;
      rw [ ← mul_assoc, ← pow_add ] ; exact mul_dvd_mul ( pow_dvd_pow _ <| by omega ) dvd_rfl;))
    generalize_proofs at *; (
    convert dvd_trans h_div1 h_div2 using 1
    generalize_proofs at *; (
    exact last_elem_eq_v3 S K b hS hb hK)))

/-
Helper lemma for divisibility in Case 2.
-/
lemma helper_div_v3 (A B l k m i K : ℕ) (hA : A ∣ 2^k * l) (hB : l ∣ B) (hi : i < K + m - 1) (hi_ge : i ≥ K) :
  2^(i - K + 1) * A ∣ 2^(k + m - 1) * B := by
    -- Since $l \mid B$, we have $2^{i-K+1} A \mid 2^{i-K+1+k} B$.
    have h_div : 2 ^ (i - K + 1) * A ∣ 2 ^ (i - K + 1 + k) * B := by
      convert Nat.mul_dvd_mul_left ( 2 ^ ( i - K + 1 ) ) ( hA.trans ( mul_dvd_mul_left _ hB ) ) using 1 ; ring;
    convert Nat.dvd_trans h_div ( mul_dvd_mul ( pow_dvd_pow _ _ ) dvd_rfl ) using 1 ; omega;

/-
Case 3: i >= K + m - 1 implies n'_i divides the last element (v3).
-/
lemma extended_seq_divides_last_case3_v3 (S : Set ℕ) (K : ℕ) (b : ℕ) (hS : S_cond S) (hb : b > 0) (hK : K ≥ 1) (i : ℕ)
  (hi_ge : i ≥ K + m_val_v3 S K b hS hb - 1) (hi_lt : i < M_val_v3 S K b hS hb) :
  let M := M_val_v3 S K b hS hb
  extended_seq_v3 S K b hS hb i ∣ extended_seq_v3 S K b hS hb (M - 1) := by
    convert helper_div_v3 _ _ _ _ _ _ _ _ _ using 1;
    rotate_left;
    exact K;
    exact 0;
    exact 0;
    exact 0;
    exact 0
    exact 0
    exact 0
    norm_num
    norm_num
    simp [extended_seq_v3] at *;
    split_ifs <;> try omega;
    · linarith [ m_val_v3_pos S K b hS hb hK ];
    · linarith [ m_val_v3_pos S K b hS hb hK ];
    · exact mul_dvd_mul ( pow_dvd_pow _ ( by omega ) ) dvd_rfl

/-
The extended sequence (v3) consists of positive integers.
-/
lemma extended_seq_pos_v3 (S : Set ℕ) (K : ℕ) (b : ℕ) (hS : S_cond S) (hb : b > 0) (i : ℕ) :
  0 < extended_seq_v3 S K b hS hb i := by
    unfold extended_seq_v3; split_ifs <;> simp_all +decide ; (
    have := hS.1 ( enum_S S i ) ( Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite S hS ) i ) ; aesop;);
    have := hS.1 ( enum_S S ( K - 1 ) ) ( Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite S hS ) _ ) ; have := hS.1 ( enum_S S ( J_idx_v3 S K b hS hb ) ) ( Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite S hS ) _ ) ; aesop;

/-
The extended sequence (v3) satisfies the growth condition n'_{i+1} <= 2n'_i.
-/
lemma extended_seq_growth_v3 (S : Set ℕ) (K : ℕ) (b : ℕ) (hS : S_cond S) (hb : b > 0) (hK : K ≥ 1) (i : ℕ) :
  extended_seq_v3 S K b hS hb (i + 1) ≤ 2 * extended_seq_v3 S K b hS hb i := by
    by_cases hi : i < K - 1 <;> simp_all +decide [ extended_seq_v3 ];
    · split_ifs <;> try omega;
      exact enum_S_growth S hS i;
    · split_ifs <;> try omega;
      · cases hi.eq_or_lt <;> first | linarith | aesop;
      · rw [ show i + 1 - K = i - K + 1 by omega ] ; ring_nf; norm_num;
      · norm_num [ show i = K - 1 by omega ] at *;
        rcases K with ( _ | K ) <;> simp_all +decide ;
        interval_cases _ : m_val_v3 S ( K + 1 ) b hS hb <;> simp_all +decide ;
        · exact absurd ‹_› ( ne_of_gt ( m_val_v3_pos S ( K + 1 ) b hS hb ( by linarith ) ) );
        · unfold m_val_v3 at *;
          rw [ Nat.ceil_eq_iff ] at * <;> norm_num at *;
          rw [ Real.logb_le_iff_le_rpow, Real.rpow_one ] at * <;> norm_cast at *;
          · rw [ div_le_iff₀ ] at * <;> norm_cast at * ; linarith [ show 0 < enum_S S K from Nat.pos_of_ne_zero fun h => by have := hS.1 _ ( show enum_S S K ∈ S from Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite S hS ) _ ) ; aesop ];
            exact Nat.pos_of_ne_zero fun h => by have := hS.1 _ ( show enum_S S K ∈ S from Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite S hS ) _ ) ; aesop;
          · exact div_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by intro t; norm_num [ t ] at * ) ) ) ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by intro t; norm_num [ t ] at * ) ) );
      · simp_all +decide ;
        have h_enum_bound : enum_S S (J_idx_v3 S K b hS hb) ≤ 2 ^ m_val_v3 S K b hS hb * enum_S S (K - 1) := by
          have h_enum_S_J : Real.logb 2 (enum_S S (J_idx_v3 S K b hS hb) / enum_S S (K - 1)) ≤ m_val_v3 S K b hS hb := by
            exact Nat.le_ceil _
          generalize_proofs at *; (
          have hdiv_pos : (0 : ℝ) < ↑(enum_S S (J_idx_v3 S K b hS hb)) / ↑(enum_S S (K - 1)) :=
            div_pos
              ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by intro t; have := hS.1 _ ( show enum_S S ( J_idx_v3 S K b hS hb ) ∈ S from Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite S hS ) _ ) ; aesop ) ) )
              ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by intro t; have := hS.1 _ ( show enum_S S ( K - 1 ) ∈ S from Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite S hS ) _ ) ; aesop ) ) );
          rw [ Real.logb_le_iff_le_rpow (by norm_num) hdiv_pos ] at h_enum_S_J; norm_num at h_enum_S_J;
          · rw [ div_le_iff₀ ] at h_enum_S_J <;> norm_cast at * ; linarith [ show 0 < enum_S S ( K - 1 ) from Nat.pos_of_ne_zero fun h => by have := hS.1 _ ( show enum_S S ( K - 1 ) ∈ S from Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite S hS ) _ ) ; aesop ] )
        generalize_proofs at *; (
        refine le_trans h_enum_bound ?_ ; ring_nf ; norm_num [ mul_assoc, mul_comm, mul_left_comm ] ; (
        exact Nat.mul_le_mul_left _ ( by rw [ show 4 = 2 ^ 2 by norm_num ] ; rw [ ← pow_add ] ; exact pow_le_pow_right₀ ( by norm_num ) ( by omega ) ) ;));
      · rw [ show i + 1 - ( K + m_val_v3 S K b hS hb - 1 ) = ( i - ( K + m_val_v3 S K b hS hb - 1 ) ) + 1 by omega, pow_succ' ] ; ring_nf ; norm_num;

/-
Every element of the extended sequence divides the last element (v3).
-/
lemma extended_seq_divides_last_v3 (S : Set ℕ) (K : ℕ) (b : ℕ) (hS : S_cond S) (hb : b > 0) (hK : K ≥ 1) (i : ℕ)
  (hi : i < M_val_v3 S K b hS hb) :
  extended_seq_v3 S K b hS hb i ∣ extended_seq_v3 S K b hS hb (M_val_v3 S K b hS hb - 1) := by
  let M := M_val_v3 S K b hS hb
  let m := m_val_v3 S K b hS hb
  by_cases h1 : i < K
  · apply extended_seq_divides_last_case1_v3 S K b hS hb hK i h1
  · by_cases h2 : i < K + m - 1
    · apply extended_seq_divides_last_case2_v3 S K b hS hb hK i (le_of_not_gt h1) h2
    · apply extended_seq_divides_last_case3_v3 S K b hS hb hK i (le_of_not_gt h2) hi

/-
Lemma adapting lm_reals to 0-based indexing.
-/
lemma finite_seq_fills (x : ℕ → ℝ) (m : ℕ) (hm : m ≥ 1)
  (h_pos : ∀ i < m, 0 < x i)
  (h_dec : ∀ i < m - 1, x (i + 1) < x i)
  (h_cond : ∀ i < m - 1, x i ≤ (∑ j ∈ Finset.Icc (i + 1) (m - 1), x j) + x (m - 1)) :
  DenselyFills { s | ∃ t ⊆ Finset.range m, s = ∑ i ∈ t, x i } 0 (∑ i ∈ Finset.range m, x i) (x (m - 1)) := by
    have h_shift : DenselyFills { s | ∃ t ⊆ Finset.Icc 1 m, s = ∑ i ∈ t, x (i - 1) } 0 (∑ i ∈ Finset.Icc 1 m, x (i - 1)) (x (m - 1)) := by
      convert lm_reals m hm _ _ _ _ using 1 <;> norm_num [ Finset.Icc_eq_empty_of_lt, hm ];
      · exact fun i hi₁ hi₂ => h_pos _ ( Nat.lt_of_lt_of_le ( Nat.pred_lt ( ne_bot_of_gt hi₁ ) ) hi₂ );
      · exact fun i hi₁ hi₂ => by cases i <;> aesop;
      · intro i hi₁ hi₂; specialize h_cond ( i - 1 ) ( by omega ) ; rcases i with ( _ | i ) <;> simp_all +decide ;
        erw [ Finset.sum_Ico_eq_sum_range ] at * ; simp_all +decide [add_comm, add_left_comm] ;
    convert h_shift using 1;
    · ext; constructor <;> rintro ⟨ t, ht, rfl ⟩;
      · use t.image (fun i => i + 1);
        exact ⟨ Finset.image_subset_iff.mpr fun i hi => Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_range.mp ( ht hi ) ], by linarith [ Finset.mem_range.mp ( ht hi ) ] ⟩, by rw [ Finset.sum_image ( by aesop ) ] ; exact Finset.sum_congr rfl fun i hi => by aesop ⟩;
      · exact ⟨ Finset.image ( fun i => i - 1 ) t, Finset.image_subset_iff.mpr fun i hi => Finset.mem_range.mpr ( Nat.lt_of_lt_of_le ( Nat.pred_lt ( ne_bot_of_gt ( Finset.mem_Icc.mp ( ht hi ) |>.1 ) ) ) ( Finset.mem_Icc.mp ( ht hi ) |>.2 ) ), by rw [ Finset.sum_image ( fun i hi j hj hij => by linarith [ Nat.sub_add_cancel ( show 1 ≤ i from Finset.mem_Icc.mp ( ht hi ) |>.1 ), Nat.sub_add_cancel ( show 1 ≤ j from Finset.mem_Icc.mp ( ht hj ) |>.1 ) ] ) ] ⟩;
    · erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ]

/-
All elements of the extended sequence (v3) are in S.
-/
lemma extended_seq_mem_S_v3 (S : Set ℕ) (K : ℕ) (b : ℕ) (hS : S_cond S) (hb : b > 0) (i : ℕ) :
  extended_seq_v3 S K b hS hb i ∈ S := by
    by_cases hi : i < K;
    · unfold extended_seq_v3;
      convert Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite S hS ) i using 1 ; aesop;
    · simp [extended_seq_v3, hi];
      split_ifs <;> [ exact pow_two_mul_mem_S _ hS _ ( show enum_S S ( K - 1 ) ∈ S from Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite _ hS ) _ ) _ ; exact pow_two_mul_mem_S _ hS _ ( show enum_S S ( J_idx_v3 S K b hS hb ) ∈ S from Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite _ hS ) _ ) _ ]

/-
The reciprocal of the extended sequence densely fills the interval.
-/
lemma recip_extended_seq_fills (S : Set ℕ) (K : ℕ) (b : ℕ) (hS : S_cond S) (hb : b > 0) (hK : K ≥ 1) :
  let M := M_val_v3 S K b hS hb
  let x := fun i => (1 : ℝ) / extended_seq_v3 S K b hS hb i
  DenselyFills { s | ∃ t ⊆ Finset.range M, s = ∑ i ∈ t, x i } 0 (∑ i ∈ Finset.range M, x i) (x (M - 1)) := by
    apply finite_seq_fills;
    · exact Nat.sub_pos_of_lt ( by linarith [ m_val_v3_pos S K b hS hb hK, k_val_thm4 S K b, Nat.zero_le ( k_val_thm4 S K b ) ] ) |> Nat.one_le_of_lt;
    · exact fun i hi => one_div_pos.mpr ( Nat.cast_pos.mpr ( extended_seq_pos_v3 S K b hS hb i ) );
    · intro i hi
      have h_inc : StrictMono (extended_seq_v3 S K b hS hb) := by
        have h_enum_strictMono : StrictMono (enum_S S) := by
          apply strictMono_nat_of_lt_succ; intro i; exact (by
          unfold enum_S; exact Nat.nth_strictMono ( show Set.Infinite S from S_infinite S hS ) ( Nat.lt_succ_self _ ) ;)
        generalize_proofs at *; (
        apply_rules [ strictMono_nat_of_lt_succ ];
        intro n; unfold extended_seq_v3; split_ifs <;> norm_num [ h_enum_strictMono.lt_iff_lt ] ;
        · split_ifs <;> simp_all +decide ;
          · cases eq_or_lt_of_le ‹K ≤ n + 1› <;> first | linarith | simp_all +decide ;
            linarith [ h_enum_strictMono.monotone ( Nat.zero_le n ), show 0 < enum_S S n from Nat.pos_of_ne_zero fun h => by have := hS.1 ( enum_S S n ) ( by unfold enum_S; exact Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite S hS ) _ ) ; aesop ];
          · exact lt_of_lt_of_le ( h_enum_strictMono <| show n < J_idx_v3 S K b hS hb from by
                                                          linarith [ show J_idx_v3 S K b hS hb ≥ K from Nat.find_spec ( _ : ∃ j, l_val_thm4 S K b ∣ enum_S S j ∧ enum_S S j > enum_S S K ) |>.2 |> fun h => h_enum_strictMono.lt_iff_lt.mp h |> Nat.le_of_lt ] ) ( Nat.le_mul_of_pos_left _ <| by positivity );
        · grind;
        · split_ifs <;> try omega;
          · exact mul_lt_mul_of_pos_right ( pow_lt_pow_right₀ ( by norm_num ) ( by omega ) ) ( Nat.cast_pos.mpr ( h_enum_strictMono.monotone ( Nat.zero_le _ ) |> lt_of_lt_of_le ( Nat.pos_of_ne_zero ( by
              exact Nat.ne_of_gt ( Nat.pos_of_ne_zero fun h => by have := hS.1 ( enum_S S 0 ) ( Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite S hS ) 0 ) ; aesop ) ; ) ) ) );
          · -- Since $n = K + m_val_v3 S K b hS hb - 2$, we can substitute this into the inequality.
            have hn_eq : n = K + m_val_v3 S K b hS hb - 2 := by
              omega
            generalize_proofs at *; (
            rcases k : m_val_v3 S K b hS hb with ( _ | _ | k ) <;> simp_all +decide [ Nat.sub_sub ] ; ring_nf ; norm_num [ h_enum_strictMono.lt_iff_lt ] ;
            have h_enum_bound : enum_S S (J_idx_v3 S K b hS hb) > 2 ^ (m_val_v3 S K b hS hb - 1) * enum_S S (K - 1) := by
              have h_enum_bound : m_val_v3 S K b hS hb - 1 < Real.logb 2 ((enum_S S (J_idx_v3 S K b hS hb) : ℝ) / (enum_S S (K - 1) : ℝ)) := by
                have h_enum_bound : m_val_v3 S K b hS hb = Nat.ceil (Real.logb 2 ((enum_S S (J_idx_v3 S K b hS hb) : ℝ) / (enum_S S (K - 1) : ℝ))) := by
                  exact rfl
                generalize_proofs at *; (
                exact h_enum_bound.symm ▸ Nat.ceil_lt_add_one ( Real.logb_nonneg ( by norm_num ) ( by rw [ le_div_iff₀ ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by
                  exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| by intro h; have := h_enum_strictMono.monotone ( show K - 1 ≥ 0 from Nat.zero_le _ ) ; aesop; ) ] ; norm_cast; linarith [ h_enum_strictMono.monotone <| show K - 1 ≤ J_idx_v3 S K b hS hb from Nat.le_of_lt_succ <| by
                                                                                                                                                                                                                                        have h_enum_bound : J_idx_v3 S K b hS hb ≥ K := by
                                                                                                                                                                                                                                          exact Nat.find_spec ( _ : ∃ j, l_val_thm4 S K b ∣ enum_S S j ∧ enum_S S j > enum_S S K ) |>.2 |> fun h => h_enum_strictMono.lt_iff_lt.mp h |> Nat.le_of_lt;
                                                                                                                                                                                                                                        generalize_proofs at *; (
                                                                                                                                                                                                                                        exact Nat.lt_succ_of_le ( Nat.sub_le_of_le_add <| by linarith ) ;) ] ) ) |> fun h => by linarith;)
              generalize_proofs at *; (
              rw [ Real.lt_logb_iff_rpow_lt ] at h_enum_bound <;> norm_cast at * <;> simp_all +decide ;
              · rw [ lt_div_iff₀ ] at h_enum_bound <;> norm_cast at * <;> simp_all +decide [ Int.subNatNat_eq_coe ] ;
                · exact_mod_cast h_enum_bound;
                · exact Nat.pos_of_ne_zero ( by intro t; norm_num [ t ] at h_enum_bound; exact absurd h_enum_bound ( by norm_cast; norm_num ) ) ;
              · exact div_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by intro t; norm_num [ t ] at h_enum_bound; linarith ) ) ) ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by intro t; norm_num [ t ] at h_enum_bound; linarith ) ) ))
            generalize_proofs at *; (
            simp_all +decide [add_comm 1, add_assoc] ; ring_nf at * ; aesop ( simp_config := { decide := true } ) ;));
          · exact mul_lt_mul_of_pos_right ( pow_lt_pow_right₀ ( by norm_num ) ( by omega ) ) ( Nat.cast_pos.mpr ( h_enum_strictMono.monotone ( Nat.zero_le _ ) |> lt_of_lt_of_le ( Nat.pos_of_ne_zero ( by
              exact Nat.ne_of_gt ( hS.1 _ ( Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite S hS ) 0 ) ) ) ) ) ))
      exact one_div_lt_one_div_of_lt (Nat.cast_pos.mpr <| extended_seq_pos_v3 S K b hS hb i) (Nat.cast_lt.mpr <| h_inc <| by linarith);
    · intro i hi
      generalize_proofs at *; (
      -- Applying the lemma `sum_recip_step_v3`.
      have h_sum_recip : ∑ j ∈ Finset.Icc (i + 1) (M_val_v3 S K b hS hb - 1), (1 : ℝ) / (extended_seq_v3 S K b hS hb j) ≥ (1 : ℝ) / (extended_seq_v3 S K b hS hb i) - (1 : ℝ) / (extended_seq_v3 S K b hS hb (M_val_v3 S K b hS hb - 1)) := by
        have h_sum_recip : ∀ j ∈ Finset.Icc (i + 1) (M_val_v3 S K b hS hb - 1), (1 : ℝ) / (extended_seq_v3 S K b hS hb j) ≥ (1 : ℝ) / (extended_seq_v3 S K b hS hb (j - 1)) - (1 : ℝ) / (extended_seq_v3 S K b hS hb j) := by
          intros j hj
          have h_ineq : (extended_seq_v3 S K b hS hb j : ℝ) ≤ 2 * (extended_seq_v3 S K b hS hb (j - 1) : ℝ) := by
            have h_ineq : extended_seq_v3 S K b hS hb j ≤ 2 * extended_seq_v3 S K b hS hb (j - 1) := by
              have h_growth : ∀ i, extended_seq_v3 S K b hS hb (i + 1) ≤ 2 * extended_seq_v3 S K b hS hb i := by
                exact fun i => extended_seq_growth_v3 S K b hS hb hK i
              cases j <;> aesop
            generalize_proofs at *; (
            exact_mod_cast h_ineq)
          generalize_proofs at *; (
          rw [ div_sub_div, ge_iff_le, div_le_div_iff₀ ] <;> nlinarith [ show ( extended_seq_v3 S K b hS hb j : ℝ ) > 0 from Nat.cast_pos.mpr ( extended_seq_pos_v3 S K b hS hb j ), show ( extended_seq_v3 S K b hS hb ( j - 1 ) : ℝ ) > 0 from Nat.cast_pos.mpr ( extended_seq_pos_v3 S K b hS hb ( j - 1 ) ) ] ;)
        generalize_proofs at *; (
        have h_sum_recip : ∑ j ∈ Finset.Icc (i + 1) (M_val_v3 S K b hS hb - 1), (1 : ℝ) / (extended_seq_v3 S K b hS hb j) ≥ ∑ j ∈ Finset.Icc (i + 1) (M_val_v3 S K b hS hb - 1), ((1 : ℝ) / (extended_seq_v3 S K b hS hb (j - 1)) - (1 : ℝ) / (extended_seq_v3 S K b hS hb j)) := by
          exact Finset.sum_le_sum h_sum_recip
        generalize_proofs at *; (
        convert h_sum_recip using 1
        generalize_proofs at *; (
        erw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, add_left_comm, Finset.sum_range_succ' ] ; ring_nf;
        rw [ show 1 + ( M_val_v3 S K b hS hb - 1 ) - ( 1 + i ) = ( M_val_v3 S K b hS hb - 1 ) - i by omega ] ; have := Finset.sum_range_sub' ( fun x => ( extended_seq_v3 S K b hS hb ( i + x ) : ℝ ) ⁻¹ ) ( ( M_val_v3 S K b hS hb - 1 ) - i ) ; simp_all +decide [ add_comm, add_left_comm ] ; ring_nf;
        rw [ Nat.add_sub_of_le ( by omega ) ])))
      generalize_proofs at *; (
      linarith))

/-
Existence of K such that partial sum exceeds q.
-/
lemma exists_K_sufficient (S : Set ℕ) (q : ℝ) (hq : q ∈ TargetInterval (fun i => (1 : ℝ) / (Nat.nth (· ∈ S) i))) :
  ∃ K : ℕ, K ≥ 1 ∧ q < ∑ i ∈ Finset.range K, (1 : ℝ) / (Nat.nth (· ∈ S) i) := by
    -- Since the partial sums converge to $S$, for any $q < S$, there exists some $K$ such that the partial sum up to $K$ is greater than $q$.
    obtain ⟨K, hK⟩ : ∃ K, q < ∑ i ∈ Finset.range K, 1 / (Nat.nth (fun x => x ∈ S) i : ℝ) := by
      by_cases h_sum : Summable (fun i => 1 / (Nat.nth (fun x => x ∈ S) i : ℝ)) <;> simp_all +decide [ TargetInterval ];
      · exact ( h_sum.hasSum.tendsto_sum_nat.eventually ( lt_mem_nhds hq.2 ) ) |> fun h => h.exists;
      · exact ( by simpa using not_summable_iff_tendsto_nat_atTop_of_nonneg ( fun _ => inv_nonneg.2 <| Nat.cast_nonneg _ ) |>.1 h_sum |> fun h => h.eventually_gt_atTop q |> fun h => h.exists ) ;
    exact ⟨ K + 1, by linarith, hK.trans_le <| Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono <| Nat.le_succ _ ) fun _ _ _ => one_div_nonneg.mpr <| Nat.cast_nonneg _ ⟩

/-
Forward inclusion of Theorem 4.
-/
lemma thm04_forward (S : Set ℕ) (hS : S_cond S) :
  SubsetSums (fun i => (1 : ℝ) / (Nat.nth (· ∈ S) i)) ⊆
    (TargetInterval (fun i => (1 : ℝ) / (Nat.nth (· ∈ S) i))) ∩ {x | ∃ q : ℚ, x = q} := by
      intro x hx
      obtain ⟨t, ht⟩ := hx
      have h_sum : x = ∑ i ∈ t, (1 : ℝ) / Nat.nth (· ∈ S) i := by
        exact ht
      have h_rational : ∃ q : ℚ, x = q := by
        exact ⟨ ∑ i ∈ t, 1 / ( Nat.nth ( fun x => x ∈ S ) i : ℚ ), by push_cast; exact h_sum ⟩
      have h_interval : x ∈ TargetInterval (fun i => (1 : ℝ) / Nat.nth (· ∈ S) i) := by
        apply Set.mem_setOf_eq.mpr
        generalize_proofs at *; (
        split_ifs <;> simp_all +decide [ Summable ];
        · refine' ⟨ _, _ ⟩ <;> try positivity;
          have h_sum_lt_total : ∑ i ∈ t, (1 : ℝ) / Nat.nth (· ∈ S) i < ∑ i ∈ t ∪ {t.sup id + 1}, (1 : ℝ) / Nat.nth (· ∈ S) i := by
            rw [ Finset.sum_union ] <;> norm_num
            generalize_proofs at *; (
            have := hS.1 ( Nat.nth ( fun x => x ∈ S ) ( t.sup id + 1 ) ) ( Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite S hS ) _ ) ; aesop;);
            exact fun h => not_lt_of_ge ( Finset.le_sup ( f := id ) h ) ( Nat.lt_succ_self _ )
          generalize_proofs at *; (
          exact lt_of_lt_of_le ( by simpa using h_sum_lt_total ) ( Summable.sum_le_tsum ( t ∪ { t.sup id + 1 } ) ( fun _ _ => by positivity ) ( by obtain ⟨ a, ha ⟩ := ‹∃ a, HasSum _ a›; exact ha.summable ) ) |> lt_of_lt_of_le <| le_rfl;);
        · change 0 ≤ ∑ x ∈ t, ((Nat.nth (fun x => x ∈ S) x : ℝ))⁻¹
          exact Finset.sum_nonneg fun i _ => inv_nonneg.mpr (Nat.cast_nonneg _))
      exact ⟨h_interval, h_rational⟩

/-
If $q$ is small enough, it is a subset sum of the extended sequence.
-/
lemma q_in_subset_sums_extended (S : Set ℕ) (hS : S_cond S) (q : ℚ) (hq_nonneg : 0 ≤ q) (K : ℕ) (hK : K ≥ 1)
  (h_sum : (q : ℝ) < ∑ i ∈ Finset.range K, (1 : ℝ) / (Nat.nth (· ∈ S) i)) :
  let b := q.den
  let hb := Nat.pos_of_ne_zero q.den_nz
  let n' := extended_seq_v3 S K b hS hb
  let M := M_val_v3 S K b hS hb
  (q : ℝ) ∈ { s | ∃ t ⊆ Finset.range M, s = ∑ i ∈ t, (1 : ℝ) / n' i } := by
    apply dense_and_divisible_implies_all_multiples;
    apply recip_extended_seq_fills S K q.den hS (Nat.cast_pos.mpr q.pos) hK;
    · intro s hs
      obtain ⟨t, ht_sub, ht_eq⟩ := hs
      use ∑ i ∈ t, (extended_seq_v3 S K q.den hS (Nat.cast_pos.mpr q.pos) (M_val_v3 S K q.den hS (Nat.cast_pos.mpr q.pos) - 1) : ℕ) / (extended_seq_v3 S K q.den hS (Nat.cast_pos.mpr q.pos) i : ℕ);
      simp_all +decide [div_eq_mul_inv, Finset.sum_mul];
      refine' Finset.sum_congr rfl fun x hx => _;
      field_simp;
      rw [ div_eq_div_iff ] <;> norm_cast <;> norm_num [ Nat.ne_of_gt ( extended_seq_pos_v3 S K q.den hS ( Nat.cast_pos.mpr q.pos ) _ ) ];
      rw [ Nat.div_mul_cancel ( extended_seq_divides_last_v3 S K q.den hS ( Nat.cast_pos.mpr q.pos ) hK x ( Finset.mem_range.mp ( ht_sub hx ) ) ) ];
    · exact one_div_pos.mpr ( Nat.cast_pos.mpr ( extended_seq_pos_v3 S K q.den hS q.pos _ ) );
    · apply And.intro;
      · refine' ⟨ _, le_trans h_sum.le _ ⟩ <;> norm_num at *;
        · exact hq_nonneg;
        · refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono <| show K ≤ M_val_v3 S K q.den hS q.pos from _ ) fun _ _ _ => inv_nonneg.2 <| Nat.cast_nonneg _ );
          · refine' Finset.sum_le_sum fun i hi => _ ; unfold extended_seq_v3 ; aesop;
          · exact le_tsub_of_add_le_left ( by linarith [ show k_val_thm4 S K q.den ≥ 0 from Nat.zero_le _, show m_val_v3 S K q.den hS q.pos ≥ 1 from m_val_v3_pos S K q.den hS q.pos hK ] );
      · -- Since $L \mid n'_{M-1}$ and $b \mid L$, we have $b \mid n'_{M-1}$.
        have h_b_div_n_last : (q.den : ℕ) ∣ extended_seq_v3 S K q.den hS (Nat.cast_pos.mpr q.pos) (M_val_v3 S K q.den hS (Nat.cast_pos.mpr q.pos) - 1) := by
          apply dvd_trans (dvd_lcm_right _ _) (last_elem_dvd_L_v3 S K q.den hS (Nat.cast_pos.mpr q.pos) hK);
        obtain ⟨ k, hk ⟩ := h_b_div_n_last; use q.num * k; simp +decide [ *, Rat.cast_def ] ; ring_nf;
        by_cases hk : k = 0 <;> simp_all +decide [ mul_assoc ];
        exact absurd ‹extended_seq_v3 S K q.den hS ( Nat.cast_pos.mpr q.pos ) ( M_val_v3 S K q.den hS ( Nat.cast_pos.mpr q.pos ) - 1 ) = 0› ( ne_of_gt ( extended_seq_pos_v3 S K q.den hS ( Nat.cast_pos.mpr q.pos ) _ ) )

/-
The extended sequence is strictly increasing.
-/
lemma extended_seq_v3_strictMono (S : Set ℕ) (K : ℕ) (b : ℕ) (hS : S_cond S) (hb : b > 0) (hK : K ≥ 1) :
  StrictMono (extended_seq_v3 S K b hS hb) := by
    refine' strictMono_nat_of_lt_succ _;
    intro n; exact (by
    by_cases hn : n < K <;> by_cases hn' : n < K + m_val_v3 S K b hS hb - 1 <;> simp +decide [ *, extended_seq_v3 ] at *;
    · split_ifs <;> try linarith [ show enum_S S ( n + 1 ) > enum_S S n from Nat.nth_strictMono ( show Set.Infinite S from S_infinite S hS ) ( by linarith ) ] ;
      · rcases K with ( _ | _ | K ) <;> simp_all +arith +decide ;
        · -- Since $enum_S S 0$ is the first element of the sequence and $S$ contains positive integers, we have $enum_S S 0 > 0$.
          have h_enum_pos : 0 < enum_S S 0 := by
            exact Nat.pos_of_ne_zero fun h => by have := hS.1 ( enum_S S 0 ) ( Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite S hS ) 0 ) ; aesop;
          linarith [h_enum_pos];
        · rw [ show n = K + 1 by linarith ] ; exact lt_of_le_of_lt ( Nat.le_refl _ ) ( by linarith [ show enum_S S ( K + 1 ) < 2 * enum_S S ( K + 1 ) from lt_mul_of_one_lt_left ( Nat.pos_of_ne_zero ( by
                                                                                                      exact Nat.ne_of_gt ( Nat.pos_of_ne_zero ( by intro t; have := hS.1 ( enum_S S ( K + 1 ) ) ( by unfold enum_S; exact Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite S hS ) _ ) ; aesop ) ) ; ) ) ( by norm_num ) ] ) ;
      · have h_enum_lt : enum_S S n < enum_S S (J_idx_v3 S K b hS hb) := by
          have h_enum_lt : enum_S S n ≤ enum_S S K := by
            apply_rules [ Nat.nth_monotone ];
            · exact S_infinite S hS |> Set.Infinite.mono fun x hx => hx;
            · grind
          generalize_proofs at *; (
          exact lt_of_le_of_lt h_enum_lt ( Nat.find_spec ( _ : ∃ j, l_val_thm4 S K b ∣ enum_S S j ∧ enum_S S j > enum_S S K ) |>.2 ) |> lt_of_lt_of_le <| le_rfl;);
        exact h_enum_lt;
    · linarith [ show m_val_v3 S K b hS hb ≥ 1 from m_val_v3_pos S K b hS hb hK ];
    · split_ifs <;> try omega;
      · rw [ show n + 1 - K = n - K + 1 by omega ] ; gcongr <;> norm_num;
        exact Nat.nth_mem_of_infinite ( S_infinite S hS ) _ |> fun x => hS.1 _ x |> fun y => y.trans_le' <| by norm_num;
      · have h_exp : 2 ^ (m_val_v3 S K b hS hb - 1) * enum_S S (K - 1) < enum_S S (J_idx_v3 S K b hS hb) := by
          have h_exp : (enum_S S (J_idx_v3 S K b hS hb) : ℝ) > 2 ^ (m_val_v3 S K b hS hb - 1) * (enum_S S (K - 1) : ℝ) := by
            have h_bound : (enum_S S (J_idx_v3 S K b hS hb) : ℝ) / (enum_S S (K - 1) : ℝ) > 2 ^ (m_val_v3 S K b hS hb - 1) := by
              have h_bound : (m_val_v3 S K b hS hb : ℝ) - 1 < Real.logb 2 ((enum_S S (J_idx_v3 S K b hS hb) : ℝ) / (enum_S S (K - 1) : ℝ)) := by
                have h_bound : (m_val_v3 S K b hS hb : ℝ) = Nat.ceil (Real.logb 2 ((enum_S S (J_idx_v3 S K b hS hb) : ℝ) / (enum_S S (K - 1) : ℝ))) := by
                  exact rfl
                generalize_proofs at *; (
                exact h_bound.symm ▸ sub_lt_iff_lt_add.mpr ( Nat.ceil_lt_add_one <| Real.logb_nonneg ( by norm_num ) <| by rw [ le_div_iff₀ <| Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by
                  exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| by intro t; have := hS.1 ( enum_S S ( K - 1 ) ) ( Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite S hS ) _ ) ; aesop; ] ; norm_cast ; linarith [ show enum_S S ( J_idx_v3 S K b hS hb ) ≥ enum_S S ( K - 1 ) from by
                                                                                                                                                                                                                              have h_bound : J_idx_v3 S K b hS hb ≥ K - 1 := by
                                                                                                                                                                                                                                have h_bound : enum_S S (J_idx_v3 S K b hS hb) > enum_S S K := by
                                                                                                                                                                                                                                  exact Nat.find_spec ( _ : ∃ j, l_val_thm4 S K b ∣ enum_S S j ∧ enum_S S j > enum_S S K ) |>.2
                                                                                                                                                                                                                                generalize_proofs at *; (
                                                                                                                                                                                                                                exact Nat.le_of_not_lt fun h => h_bound.not_ge <| Nat.nth_monotone ( show { x | x ∈ S }.Infinite from S_infinite S hS ) <| by omega;)
                                                                                                                                                                                                                              generalize_proofs at *; (
                                                                                                                                                                                                                              exact Nat.nth_monotone ( show Set.Infinite S from S_infinite S hS ) h_bound |> le_trans ( by aesop ) ;) ] ) |> lt_of_lt_of_le <| by norm_num;)
              generalize_proofs at *; (
              rw [ Real.lt_logb_iff_rpow_lt ] at h_bound <;> norm_cast at * <;> norm_num at *;
              · rw [ Int.subNatNat_of_le ] at h_bound <;> norm_cast at * ; linarith [ m_val_v3_pos S K b hS hb hK ] ;
              · exact div_pos ( Nat.cast_pos.mpr ( show 0 < enum_S S ( J_idx_v3 S K b hS hb ) from Nat.pos_of_ne_zero fun h => by have := hS.1 _ ( show enum_S S ( J_idx_v3 S K b hS hb ) ∈ S from by
                                                                                                                                                    exact Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite S hS ) _ |> fun h => by simpa [ enum_S ] using h; ) ; aesop ) ) ( Nat.cast_pos.mpr ( show 0 < enum_S S ( K - 1 ) from Nat.pos_of_ne_zero fun h => by have := hS.1 _ ( show enum_S S ( K - 1 ) ∈ S from by
                                                                                                                                                                                                                                                                                                                                  exact Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite S hS ) _ |> fun h => by simpa [ enum_S ] using h; ) ; aesop ) ))
            generalize_proofs at *; (
            rwa [ gt_iff_lt, lt_div_iff₀ ( Nat.cast_pos.mpr <| by
              exact Nat.pos_of_ne_zero fun h => by have := hS.1 _ ( show enum_S S ( K - 1 ) ∈ S from Nat.nth_mem_of_infinite ( show Set.Infinite S from S_infinite S hS ) _ ) ; aesop; ) ] at h_bound)
          generalize_proofs at *; (
          exact_mod_cast h_exp.lt;)
        generalize_proofs at *; (
        refine' lt_of_le_of_lt _ h_exp;
        exact Nat.mul_le_mul_right _ ( pow_le_pow_right₀ (show (1 : ℕ) ≤ 2 by decide) ( by omega ) ));
    · split_ifs <;> try linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ K + m_val_v3 S K b hS hb ) ] ;
      gcongr <;> norm_num [ Nat.succ_sub ];
      · exact Nat.pos_of_ne_zero ( by intro h; have := hS.1 _ ( show enum_S S ( J_idx_v3 S K b hS hb ) ∈ S from Nat.nth_mem_of_infinite ( show Set.Infinite S from by exact S_infinite S hS ) _ ) ; aesop ) ;
      · linarith);

/-
If a finite sequence consists of distinct elements of S, its subset sums are subset sums of S.
-/
lemma subset_sums_subseq (n' : ℕ → ℕ) (M : ℕ) (S : Set ℕ)
  (h_vals : ∀ i < M, n' i ∈ S)
  (h_mono : StrictMonoOn n' (Set.Iio M)) :
  { s | ∃ t ⊆ Finset.range M, s = ∑ i ∈ t, (1 : ℝ) / n' i } ⊆ SubsetSums (fun i => (1 : ℝ) / (Nat.nth (· ∈ S) i)) := by
    intro s hs
    obtain ⟨t, ht_sub, ht_eq⟩ := hs
    have h_subset : ∀ i ∈ t, ∃ j ∈ Set.univ, n' i = Nat.nth (fun x => x ∈ S) j := by
      intro i hi
      obtain ⟨j, hj⟩ : ∃ j, n' i = Nat.nth (fun x => x ∈ S) j := by
        have h_seq : ∀ n ∈ S, ∃ j, n = Nat.nth (fun x => x ∈ S) j := by
          intro n hn; use Nat.count (fun x => x ∈ S) n; rw [Nat.nth_count]; aesop;
        generalize_proofs at *; (exact h_seq (n' i) (h_vals i (Finset.mem_range.mp (ht_sub hi)))) ;
      use j
      aesop
    generalize_proofs at *; simp_all +decide [ Finset.subset_iff ] ; (
    choose! f hf using h_subset; use t.image f; simp_all +decide ; (
    rw [ Finset.sum_image ] ; intros i hi j hj hij ; have := hf i hi ; have := hf j hj ; have := h_mono.eq_iff_eq ( ht_sub hi ) ( ht_sub hj ) ; aesop;);)

/-
Reverse inclusion for Theorem 4.
-/
lemma thm04_reverse (S : Set ℕ) (hS : S_cond S) :
  (TargetInterval (fun i => (1 : ℝ) / (Nat.nth (· ∈ S) i))) ∩ {x | ∃ q : ℚ, x = q} ⊆ SubsetSums (fun i => (1 : ℝ) / (Nat.nth (· ∈ S) i)) := by
    intro q hq
    generalize_proofs at *;
    -- Since $q$ is rational and positive, we can apply `exists_K_sufficient`.
    obtain ⟨K, hK⟩ : ∃ K : ℕ, K ≥ 1 ∧ q < ∑ i ∈ Finset.range K, (1 : ℝ) / (Nat.nth (· ∈ S) i) := by
      apply exists_K_sufficient S q hq.left
    generalize_proofs at *; (
    obtain ⟨q_rat, hq_rat⟩ : ∃ q_rat : ℚ, q = q_rat ∧ 0 ≤ q_rat := by
      unfold TargetInterval at hq; aesop;
    generalize_proofs at *; (
    -- By `q_in_subset_sums_extended`, $q$ is a subset sum of $1/n'$.
    have h_subset_sum : (q_rat : ℝ) ∈ { s | ∃ t ⊆ Finset.range (M_val_v3 S K q_rat.den hS (Nat.pos_of_ne_zero q_rat.den_nz) ), s = ∑ i ∈ t, (1 : ℝ) / (extended_seq_v3 S K q_rat.den hS (Nat.pos_of_ne_zero q_rat.den_nz) i) } := by
      convert q_in_subset_sums_extended S hS q_rat hq_rat.2 K hK.1 _ using 1
      generalize_proofs at *; (
      aesop)
    generalize_proofs at *; (
    -- By `subset_sums_subseq`, since $n'$ consists of elements of $S$ (by `extended_seq_mem_S_v3`) and is strictly increasing (by `extended_seq_v3_strictMono`), the subset sum of $1/n'$ is a subset sum of $S$.
    have h_subset_sum_S : { s | ∃ t ⊆ Finset.range (M_val_v3 S K q_rat.den hS (Nat.pos_of_ne_zero q_rat.den_nz) ), s = ∑ i ∈ t, (1 : ℝ) / (extended_seq_v3 S K q_rat.den hS (Nat.pos_of_ne_zero q_rat.den_nz) i) } ⊆ SubsetSums (fun i => (1 : ℝ) / (Nat.nth (· ∈ S) i)) := by
      apply subset_sums_subseq
      generalize_proofs at *;
      · exact fun i a => extended_seq_mem_S_v3 S K q_rat.den hS (Nat.pos_of_ne_zero q_rat.den_nz) i;
      · exact fun i hi j hj hij => extended_seq_v3_strictMono S K q_rat.den hS ( Nat.pos_of_ne_zero q_rat.den_nz ) hK.1 |> fun h => h hij |> fun h' => by aesop;
    generalize_proofs at *; (
    exact hq_rat.1 ▸ h_subset_sum_S h_subset_sum))))

/-
Theorem 1: For every $λ \in (1, 2)$, there exists a $λ$-lacunary sequence of positive integers with limit ratio $2$ such that finite sums of its reciprocals contain all rationals in $[0, 2]$.
-/
theorem Theorem_1 (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  ∃ n : ℕ → ℕ,
    (∀ i, 0 < n i) ∧
    IsLambdaLacunary lambda (fun i => n i) ∧
    Filter.Tendsto (fun i => (n (i + 1) : ℝ) / n i) Filter.atTop (nhds 2) ∧
    Set.Icc 0 2 ∩ {x : ℝ | ∃ q : ℚ, x = q} ⊆ SubsetSums (fun i => (1 : ℝ) / n i) := by
      use final_n lambda h_lambda;
      refine' ⟨ _, _, _, _ ⟩;
      · exact fun i => final_n_pos lambda h_lambda i;
      · exact final_n_is_lacunary lambda h_lambda;
      · exact final_n_ratio_tendsto lambda h_lambda;
      · intro x hx
        obtain ⟨hx_range, ⟨q, hq⟩⟩ := hx
        have h_sum : x ∈ TargetInterval (fun i => (1 : ℝ) / final_n lambda h_lambda i) := by
          have h_sum : x < ∑' i, (1 : ℝ) / final_n lambda h_lambda i := by
            exact lt_of_le_of_lt hx_range.2 ( by simpa using final_n_sum_gt_two lambda h_lambda );
          unfold TargetInterval; aesop;
        have h_rational : ∃ q : ℚ, x = q := by
          use q
        have h_subset_sum : x ∈ SubsetSums (fun i => (1 : ℝ) / final_n lambda h_lambda i) := by
          apply target_subset_subset_sums (final_n lambda h_lambda) (final_m lambda) (fun i => by
            exact final_n_pos lambda h_lambda i) (fun i => by
            exact fun j hj => final_n_strictMono _ _ hj) (final_m_strictMono lambda h_lambda) (fun k => by
            exact fun hk => final_n_div_all _ _ _ hk.nat_succ_le |> fun ⟨ i, hi ⟩ => ⟨ i, hi ⟩) (fun k j hj => by
            apply_rules [ final_n_div_m ]) (fun k => by
            intro hk
            have h_sum : (1 : ℝ) / final_n lambda h_lambda k ≤ (∑ j ∈ Finset.Ioc k (final_m lambda 0), (1 : ℝ) / final_n lambda h_lambda j) + (1 : ℝ) / final_n lambda h_lambda (final_m lambda 0) := by
              convert remark_cond _ _ _ _ _ _ using 1;
              · exact fun i => final_n_pos lambda h_lambda i;
              · intro i
                have h_ratio : (final_n lambda h_lambda (i + 1) : ℝ) / final_n lambda h_lambda i ≤ 2 := by
                  have := n_seq_ratio_properties lambda h_lambda ( i + 1 ) ( by linarith ) ; aesop;
                exact_mod_cast (by
                rwa [ div_le_iff₀ ( Nat.cast_pos.mpr ( final_n_pos _ _ _ ) ) ] at h_ratio : (final_n lambda h_lambda (i + 1) : ℝ) ≤ 2 * final_n lambda h_lambda i);
              · exact hk
            exact h_sum) (fun k i hi => by
            intro hi';
            have h_ratio : ∀ i, final_n lambda h_lambda (i + 1) ≤ 2 * final_n lambda h_lambda i := by
              intro i
              have h_ratio : (final_n lambda h_lambda (i + 1) : ℝ) / final_n lambda h_lambda i ≤ 2 := by
                have := n_seq_ratio_properties lambda h_lambda ( i + 1 ) ( by linarith ) ; aesop;
              rw [ div_le_iff₀ ] at h_ratio <;> norm_cast at * ; linarith [ final_n_pos lambda h_lambda i ];
            have := remark_cond ( fun i => final_n lambda h_lambda i ) ( final_m lambda ( k + 1 ) ) ( fun i => by
              exact final_n_pos lambda h_lambda i ) ( fun i => by
              exact h_ratio i ) i ( by
              linarith );
            convert this using 1);
          exact ⟨ h_sum, h_rational ⟩
        exact h_subset_sum

/-
Theorem 2: $R(λ) = \sum_{i=1}^\infty 1/a_i$.
-/
theorem Theorem_2 (lambda : ℝ) (h_lambda : 1 < lambda ∧ lambda < 2) :
  R_lambda lambda = ∑' i, (1 : ℝ) / a_seq lambda i := by
  apply le_antisymm
  · exact R_lambda_le lambda h_lambda
  · exact R_lambda_ge lambda h_lambda

/-
Theorem 3: For every $Λ \ge 2$ and every $1 < λ < \frac{Λ}{Λ-1}$, there exists a $λ$-lacunary sequence of positive integers such that the ratio of two consecutive elements is infinitely often larger than $Λ$, while finite sums of its reciprocals contain all rationals in the largest possible interval.
-/
theorem Theorem_3 (Lambda : ℝ) (lambda : ℝ) (h_Lambda : Lambda ≥ 2) (h_lambda : 1 < lambda ∧ lambda < Lambda / (Lambda - 1)) :
  ∃ n : ℕ → ℕ,
    IsLambdaLacunary lambda (fun i => n i) ∧
    (∀ i, 0 < n i) ∧
    (Set.Infinite {i | (n (i + 1) : ℝ) > Lambda * n i}) ∧
    SubsetSums (fun i => (1 : ℝ) / n i) ⊇ (TargetInterval (fun i => (1 : ℝ) / n i)) ∩ {x | ∃ q : ℚ, x = q} := by
      refine' ⟨ n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda, _, _, _, _ ⟩ <;> norm_num at *;
      · intro i; specialize h_lambda; have := thm3_seq_v2_lacunary_lower Lambda lambda h_Lambda h_lambda i; aesop;
      · intro i
        have h_mono : StrictMono (n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda) := by
          exact n_seq_thm3_final_v2_mono Lambda lambda h_Lambda h_lambda
        have h_pos : 0 < n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda 0 := by
          have h_pos : n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda 0 = (thm3_seq_v2 Lambda lambda h_Lambda h_lambda 0).n 0 := by
            convert n_seq_thm3_final_v2_eq Lambda lambda h_Lambda h_lambda 0 0 ( by linarith [ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda 0 ).h_m ] ) using 1
          generalize_proofs at *;
          exact h_pos.symm ▸ (thm3_seq_v2 Lambda lambda h_Lambda h_lambda 0).h_pos 0 (by linarith [(thm3_seq_v2 Lambda lambda h_Lambda h_lambda 0).h_m]) |> fun h => by linarith;
        exact lt_of_lt_of_le h_pos (h_mono.monotone (Nat.zero_le i));
      · refine' Set.infinite_of_forall_exists_gt _;
        intro a
        obtain ⟨k, hk⟩ : ∃ k, a < m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k - 1 := by
          have h_unbounded : Filter.Tendsto (m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda) Filter.atTop Filter.atTop := by
            refine' Filter.tendsto_atTop_mono _ tendsto_natCast_atTop_atTop;
            intro n; induction' n with n ih <;> norm_num [ m_seq_thm3_final_v2 ] at *;
            exact Nat.succ_le_of_lt ( lt_of_le_of_lt ih ( by exact ( show ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n ).m < ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda ( n + 1 ) ).m from by { exact ( step_thm3_strong_v2_props Lambda lambda ( U_thm3 Lambda lambda h_Lambda h_lambda ) n ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n |> Thm3Data.m ) ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n |> Thm3Data.n ) h_Lambda ( by exact ⟨ h_lambda.1, by exact lambda_lt_two Lambda lambda h_Lambda h_lambda.2 ⟩ ) ( by exact ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n |> Thm3Data.h_m ) ) ( by exact ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n |> Thm3Data.h_pos ) ) ( by exact ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda n |> Thm3Data.h_mono ) ) |>.1 ) |> lt_of_lt_of_le ( by linarith ) } ) ) ) ;
          exact Filter.Eventually.exists ( h_unbounded.eventually_gt_atTop ( a + 1 ) ) |> fun ⟨ k, hk ⟩ => ⟨ k, lt_tsub_iff_right.mpr hk ⟩ ;
        use m_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda k - 1
        simp [hk];
        convert thm3_seq_v2_large_jumps Lambda lambda h_Lambda h_lambda k using 1 ; ring_nf!; (
        rw [ add_tsub_cancel_of_le ( Nat.one_le_iff_ne_zero.mpr <| by aesop_cat ) ]);
      · -- Apply the general.prop_general lemma with the given parameters.
        have := prop_general (n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda) (final_M_seq Lambda lambda h_Lambda h_lambda) (by
        intro i
        have h_pos : 0 < n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda i := by
          have h_pos : StrictMono (n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda) := by
            exact n_seq_thm3_final_v2_mono Lambda lambda h_Lambda h_lambda
          generalize_proofs at *; (
          induction' i with i ih <;> [ exact Nat.pos_of_ne_zero ( by
            have h_pos : n_seq_thm3_final_v2 Lambda lambda h_Lambda h_lambda 0 = (thm3_seq_v2 Lambda lambda h_Lambda h_lambda 0).n 0 := by
              apply n_seq_thm3_final_v2_eq
              generalize_proofs at *; (
              exact Nat.succ_pos _ |> Nat.lt_of_le_of_lt ( Nat.le_refl _ ) |> Nat.lt_of_lt_of_le <| by exact ( init_thm3_data Lambda lambda h_Lambda h_lambda ) |>.h_m;)
            generalize_proofs at *; (
            exact h_pos.symm ▸ Nat.ne_of_gt ( by exact ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda 0 ).h_pos 0 ( by linarith [ ( thm3_seq_v2 Lambda lambda h_Lambda h_lambda 0 ).h_m ] ) )) ) ; exact lt_of_le_of_lt ( Nat.zero_le _ ) ( h_pos ( Nat.lt_succ_self _ ) ) ])
        exact h_pos) (by
        exact n_seq_thm3_final_v2_mono Lambda lambda h_Lambda h_lambda) (by
        exact final_M_seq_strictMono Lambda lambda h_Lambda h_lambda) (by
        exact fun k hk => by obtain ⟨ i, hi ⟩ := thm3_div_all_v2 Lambda lambda h_Lambda h_lambda k hk; exact ⟨ i, hi ⟩ ;) (by
        intro k j hj
        apply thm3_seq_v2_div_m Lambda lambda h_Lambda h_lambda k j hj) (by
        convert thm3_seq_v2_ineq_initial Lambda lambda h_Lambda h_lambda using 1) (by
        exact fun k i hi₁ hi₂ => by have := thm3_seq_v2_satisfies_ineq Lambda lambda h_Lambda h_lambda; aesop;);
        aesop

/-
Theorem 4: If $2S ⊆ S$ and $S$ contains a multiple of every odd integer, then finite sums of the reciprocals of $S$ contain all rationals in the largest possible interval.
-/
theorem Theorem_4 (S : Set ℕ) (hS : S_cond S) :
  SubsetSums (fun i => (1 : ℝ) / (Nat.nth (· ∈ S) i)) =
    (TargetInterval (fun i => (1 : ℝ) / (Nat.nth (· ∈ S) i))) ∩ {x | ∃ q : ℚ, x = q} := by
      -- Apply the forward direction of the equivalence to conclude the proof.
      apply Set.eq_of_subset_of_subset; exact (thm04_forward S hS) ; exact (thm04_reverse S hS)

/-
Statement taken from the Formal Conjectures project.
-/
set_option linter.deprecated false in
theorem erdos_355 :
    ∃ A : ℕ → ℕ, IsLacunary A ∧ ∃ u v : ℝ, u < v ∧ ∀ q : ℚ, ↑q ∈ Set.Ioo u v →
      q ∈ {∑ a ∈ A', (1 / a : ℚ) | (A' : Finset ℕ) (_ : A'.toSet ⊆ Set.range A)} := by
        -- Let's choose any sequence $A$ that satisfies the conditions.
        obtain ⟨A, hA⟩ : ∃ A : ℕ → ℕ, IsLacunary A ∧ (∀ q : ℚ, 0 ≤ q → q ≤ 1 → ∃ A' : Finset ℕ, (∀ a ∈ A', a ∈ Set.range A) ∧ (∑ a ∈ A', (1 : ℚ) / a) = q) := by
          obtain ⟨A, hA⟩ : ∃ A : ℕ → ℕ, IsLacunary A ∧ (∀ q : ℚ, 0 ≤ q → q ≤ 1 → ∃ A' : Finset ℕ, (∀ a ∈ A', a ∈ Set.range A) ∧ (∑ a ∈ A', (1 : ℚ) / a) = q) := by
            have := Theorem_1 1.5 ⟨by norm_num, by norm_num⟩
            obtain ⟨ n, hn ⟩ := this
            generalize_proofs at *; (
            refine' ⟨ n, _, _ ⟩ <;> simp_all +decide [ IsLacunary, IsLambdaLacunary ];
            · exact ⟨ 1.5, by norm_num, fun i hi => hn.2.1 i ⟩;
            · intro q hq_nonneg hq_le_one
              obtain ⟨A', hA'⟩ : ∃ A' : Finset ℕ, (∑ a ∈ A', (1 : ℝ) / (n a)) = q := by
                have := hn.2.2.2 ⟨ ⟨ by norm_num; linarith [ show ( q : ℝ ) ≥ 0 by exact_mod_cast hq_nonneg ], by linarith [ show ( q : ℝ ) ≤ 1 by exact_mod_cast hq_le_one ] ⟩, q, rfl ⟩ ; unfold SubsetSums at this; aesop;
              generalize_proofs at *; (
              use Finset.image (fun a => n a) A';
              rw [ Finset.sum_image ] <;> norm_num [ ← @Rat.cast_inj ℝ ] at * ; aesop;
              -- Since $n$ is strictly increasing, it is injective.
              have h_inj : StrictMono n := by
                exact strictMono_nat_of_lt_succ fun i => by have := hn.2.1 i; rw [ le_div_iff₀ ( Nat.cast_pos.mpr ( hn.1 i ) ) ] at this; exact_mod_cast ( by nlinarith [ show ( n i : ℝ ) > 0 from Nat.cast_pos.mpr ( hn.1 i ) ] : ( n i : ℝ ) < n ( i + 1 ) ) ;
              generalize_proofs at *; (exact h_inj.injective.injOn)))
          generalize_proofs at *; (
          use A);
        refine' ⟨ A, hA.1, 0, 1, _, _ ⟩ <;> norm_num;
        exact fun q hq₁ hq₂ => by obtain ⟨ A', hA₁, hA₂ ⟩ := hA.2 q hq₁.le ( mod_cast hq₂.le ) ; exact ⟨ A', fun x hx => hA₁ x hx, by simpa using hA₂ ⟩ ;

#print axioms Theorem_1
-- 'Erdos355.Theorem_1' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Theorem_2
-- 'Erdos355.Theorem_2' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Theorem_3
-- 'Erdos355.Theorem_3' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Theorem_4
-- 'Erdos355.Theorem_4' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms erdos_355
-- 'Erdos355.erdos_355' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos355
