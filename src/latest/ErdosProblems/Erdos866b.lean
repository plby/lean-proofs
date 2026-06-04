/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 866.
https://www.erdosproblems.com/forum/thread/866

Formalization status:
- Partial

Informal authors:
- Wouter van Doorn
- ChatGPT

Formal authors:
- Aristotle
- Wouter van Doorn

URLs:
- https://www.erdosproblems.com/forum/thread/866#post-6229
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem866.lean
-/
/-
For an integer $k ≥ 3$ we define $g_k(n)$ as the smallest integer such that for any set $A ⊆ {1, 2, …, 2n}$ with $|A| ≥ n + g_k(n)$ there exist distinct integers $b_1, b_2, …, b_k$ such that all $\binom{k}{2}$ pairwise sums are in $A$. We further let $h_k(n)$ be the analogous function where we require the $b_i$ to be positive integers. We note that the $b_i$ in these definitions need not be in $A$ themselves.

Since at most one of the $b_i$ can be non-positive (as otherwise we have a negative sum), we note that, in general,

$g_k(n) ≤ h_k(n) ≤ g_{k+1}(n)$ for all $k$ and $n$.

Estimating $g_k(n)$ is Erdős problem #866 (https://www.erdosproblems.com/866), while Choi, Erdős, and Szemerédi had already proven the following estimates for $h$:

$h_3(n) = 2$ for all $n ≥ 4$.
$h_4(n) = O(1)$.
$h_5(n) ≍ \log n$.
$h_6(n) ≍ \sqrt n$.
$h_k(n) ≤ 2^k n^{1-1/2^k}$ for all large enough $n$.

Choi, S. L. G. and Erdős, P. and Szemerédi, E., Some additive and multiplicative problems in number theory. Acta Arith., 37--50 (1975).

With some help from ChatGPT and Aristotle from Harmonic (aristotle-harmonic@harmonic.fun), I was able to obtain the following bounds:

$g_3(n) = 1$ for all $n ≥ 3$.
$g_4(n) = 3$ for all $n ≥ 2$.
$h_4(n) ≤ 2270$ for all $n$.
$g_5(n) < 1.2 · 10^8$ for all $n$.
$g_k(n) ≤ h_k(n) < 4 n^{1-1/2^{k-2}}$ for all large enough $n$.

You can find formalizations of the proofs of all these (in)equalities below, which were obtained by Aristotle. In the proofs I also had to use explicit upper bounds on the size of Sidon sets and weak Sidon sets by O'Bryant and Ruzsa, so their results are included in the formalization as well.

O'Bryant, K. On the Size of Finite Sidon Sets. Ukr. Math. J. 76, 1352–1368 (2025).
I.Z. Ruzsa, Solving a linear equation in a set of integers I. Acta. Arith. 65, 259-283 (1993).

Lean version: leanprover/lean4:v4.28.0
Mathlib version: 8f9d9cff6bd728b17a24e163c9402775d9e6a365
-/

import Mathlib

namespace Erdos866b

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.refine false
set_option linter.flexible false
set_option linter.style.multiGoal false
set_option linter.style.whitespace false

set_option maxHeartbeats 8000000
-- Several generated Sidon-set and pairwise-sum estimates time out at the default heartbeat limit.
set_option maxRecDepth 4096

open Finset
open scoped Pointwise

attribute [local instance] Classical.propDecidable

/-- There exist k distinct integers whose pairwise sums are all in A. -/
def HasPairwiseSums (A : Finset ℤ) (k : ℕ) : Prop :=
  ∃ b : Fin k → ℤ, Function.Injective b ∧ ∀ i j : Fin k, i < j → b i + b j ∈ A

/-- There exist k distinct positive integers whose pairwise sums are all in A. -/
def HasPosPairwiseSums (A : Finset ℤ) (k : ℕ) : Prop :=
  ∃ b : Fin k → ℤ, Function.Injective b ∧ (∀ i : Fin k, 0 < b i) ∧
    ∀ i j : Fin k, i < j → b i + b j ∈ A

/-- g_k(n) is the smallest m such that any A ⊆ {1,...,2n} with |A| ≥ n+m
    contains the pairwise sums of k distinct integers. -/
noncomputable def gFun (k n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (A : Finset ℤ), A ⊆ Icc (1 : ℤ) (2 * ↑n) →
    n + m ≤ A.card → HasPairwiseSums A k}

/-- h_k(n) is the smallest m such that any A ⊆ {1,...,2n} with |A| ≥ n+m
    contains the pairwise sums of k distinct positive integers. -/
noncomputable def hFun (k n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (A : Finset ℤ), A ⊆ Icc (1 : ℤ) (2 * ↑n) →
    n + m ≤ A.card → HasPosPairwiseSums A k}

/-! ## Utility for proving sInf equalities -/

lemma sInf_eq_of_mem_of_forall_lt_not_mem {S : Set ℕ} {m : ℕ}
    (hm : m ∈ S) (hlt : ∀ k < m, k ∉ S) :
    sInf S = m := by
  apply le_antisymm
  · exact Nat.sInf_le hm
  · exact le_csInf ⟨m, hm⟩ (fun k hk => by
      by_contra h
      push Not at h
      exact hlt k h hk)

/-! ## g_k(n) ≤ h_k(n) ≤ g_{k+1}(n) -/

/-- HasPosPairwiseSums implies HasPairwiseSums -/
lemma HasPosPairwiseSums.toHasPairwiseSums {A : Finset ℤ} {k : ℕ}
    (h : HasPosPairwiseSums A k) : HasPairwiseSums A k := by
  obtain ⟨b, hb_inj, _, hb_sum⟩ := h
  exact ⟨b, hb_inj, hb_sum⟩

/-
The gFun set is contained in the hFun set, giving gFun ≤ hFun
-/
lemma gFun_le_hFun (k n : ℕ) : gFun k n ≤ hFun k n := by
  refine' le_csInf _ _;
  · use 2 * n + 1;
    intro A hA hcard; have := Finset.card_le_card hA; norm_num at *; linarith;
  · intro m hm
    have h_superset : ∀ A ⊆ Finset.Icc 1 (2 * n : ℤ), n + m ≤ A.card → HasPairwiseSums A k := by
      exact fun A hA hA' => HasPosPairwiseSums.toHasPairwiseSums ( hm A hA hA' );
    exact Nat.sInf_le h_superset

/-
If k+1 distinct integers have pairwise sums in A ⊆ {1,...,2n},
    then at least k of them are positive, giving HasPosPairwiseSums A k.
-/
lemma HasPairwiseSums_succ_to_HasPosPairwiseSums {A : Finset ℤ} {k : ℕ}
    (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n))
    (h : HasPairwiseSums A (k + 1)) : HasPosPairwiseSums A k := by
  obtain ⟨ b, hb₁, hb₂ ⟩ := h;
  -- Since there can be at most one non-positive element in $b$, we can remove it and still have $k$ positive elements.
  obtain ⟨i, hi⟩ : ∃ i : Fin (k + 1), ∀ j : Fin (k + 1), j ≠ i → 0 < b j := by
    have h_nonpos : Finset.card (Finset.filter (fun i => b i ≤ 0) Finset.univ) ≤ 1 := by
      have h_neg_set : ∀ i j, i ≠ j → (b i ≤ 0 ∧ b j ≤ 0) → False := by
        intro i j hij h; cases lt_or_gt_of_ne hij <;> linarith [ Finset.mem_Icc.mp ( hA ( hb₂ _ _ ‹_› ) ) ] ;
      exact Finset.card_le_one.mpr fun i hi j hj => Classical.not_not.1 fun hij => h_neg_set i j hij ⟨ Finset.mem_filter.mp hi |>.2, Finset.mem_filter.mp hj |>.2 ⟩;
    interval_cases _ : Finset.card ( Finset.filter ( fun i => b i ≤ 0 ) Finset.univ ) <;> simp_all +decide [ Finset.card_eq_one ];
    obtain ⟨ i, hi ⟩ := ‹_›; use i; intro j hj; rw [ Finset.ext_iff ] at hi; specialize hi j; aesop;
  use fun j => b (Fin.succAbove i j);
  refine' ⟨ _, _, _ ⟩ <;> simp_all +decide [ Fin.succAbove_ne, Function.Injective ];
  exact fun a₁ a₂ h => by have := hb₁ h; aesop;

/-
h_k(n) ≤ g_{k+1}(n)
-/
lemma hFun_le_gFun_succ (k n : ℕ) : hFun k n ≤ gFun (k + 1) n := by
  refine' le_csInf _ _;
  · use 2 * n + 1;
    intro A hA hA'; have := Finset.card_le_card hA; simp_all +decide ;
    grind;
  · intro m hm;
    refine' Nat.sInf_le _;
    exact fun A hA hA' => HasPairwiseSums_succ_to_HasPosPairwiseSums hA ( hm A hA hA' )

/-- g_k(n) ≤ h_k(n) ≤ g_{k+1}(n) -/
theorem gFun_le_hFun_le_gFun_succ (k n : ℕ) :
    gFun k n ≤ hFun k n ∧ hFun k n ≤ gFun (k + 1) n :=
  ⟨gFun_le_hFun k n, hFun_le_gFun_succ k n⟩


/-! ## Theorem g3: g₃(n) = 1 for all n ≥ 3 -/

/-
Upper bound: any A ⊆ {1,...,2n} with |A| ≥ n+1 has pairwise sums of 3 distinct integers.
-/
lemma g3_upper (n : ℕ) (hn : 3 ≤ n) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n)) (hcard : n + 1 ≤ A.card) :
    HasPairwiseSums A 3 := by
      -- By the pigeonhole principle, there exists at least one pair {2k-1, 2k} such that both elements are in A.
      obtain ⟨k, hk⟩ : ∃ k ∈ Finset.range n, (2 * k + 1 : ℤ) ∈ A ∧ (2 * k + 2 : ℤ) ∈ A := by
        contrapose hcard;
        -- If no such pair exists, then A can contain at most one element from each pair {2k-1, 2k}.
        have hA_subset : A ⊆ Finset.image (fun k : ℕ => 2 * k + 1 : ℕ → ℤ) (Finset.range n) ∪ Finset.image (fun k : ℕ => 2 * k + 2 : ℕ → ℤ) (Finset.range n) := by
          intro x hx; have := hA hx; rcases Int.even_or_odd' x with ⟨ k, rfl | rfl ⟩ <;> simp_all +decide ;
          · exact Or.inr ⟨ Int.toNat ( k - 1 ), by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k - 1 ) ], by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k - 1 ) ] ⟩;
          · exact Or.inl ⟨ Int.toNat k, by linarith [ Int.toNat_of_nonneg this.1 ], by rw [ Int.toNat_of_nonneg this.1 ] ⟩;
        have hA_card : A.card ≤ Finset.card (Finset.image (fun k : ℕ => if (2 * k + 1 : ℤ) ∈ A then 2 * k + 1 else 2 * k + 2 : ℕ → ℤ) (Finset.range n)) := by
          refine Finset.card_le_card ?_;
          intro x hx; specialize hA_subset hx; aesop;
        exact not_le_of_gt ( lt_of_le_of_lt hA_card ( lt_of_le_of_lt ( Finset.card_image_le ) ( by simp ) ) );
      by_cases h_odd : ∀ x ∈ A, x % 2 = 0 ∨ x = 2 * k + 1;
      · -- Since there are $n$ even integers in $\{1, \ldots, 2n\}$ and $A$ contains at least $n$ even integers, $A$ must contain all even integers in $\{1, \ldots, 2n\}$.
        have h_all_even : Finset.image (fun x : ℕ => 2 * x : ℕ → ℤ) (Finset.Icc 1 n) ⊆ A := by
          have h_all_even : Finset.card (A.filter (fun x => x % 2 = 0)) ≥ n := by
            have h_even_count : Finset.card (A.filter (fun x => x % 2 = 0)) + Finset.card (A.filter (fun x => x % 2 ≠ 0)) = A.card := by
              rw [ Finset.card_filter_add_card_filter_not ];
            linarith [ show Finset.card ( Finset.filter ( fun x => x % 2 ≠ 0 ) A ) ≤ 1 by exact Finset.card_le_one.mpr fun x hx y hy => by cases h_odd x ( Finset.filter_subset _ _ hx ) <;> cases h_odd y ( Finset.filter_subset _ _ hy ) <;> aesop ];
          have h_all_even : Finset.filter (fun x => x % 2 = 0) A = Finset.image (fun x : ℕ => 2 * x : ℕ → ℤ) (Finset.Icc 1 n) := by
            refine' Finset.eq_of_subset_of_card_le ( fun x hx => _ ) _ <;> simp_all +decide [ Finset.subset_iff ];
            · exact ⟨ Int.toNat ( x / 2 ), ⟨ by linarith [ Int.ediv_mul_cancel hx.2, hA hx.1, Int.toNat_of_nonneg ( Int.ediv_nonneg ( show 0 ≤ x by linarith [ hA hx.1 ] ) zero_le_two ) ], by linarith [ Int.ediv_mul_cancel hx.2, hA hx.1, Int.toNat_of_nonneg ( Int.ediv_nonneg ( show 0 ≤ x by linarith [ hA hx.1 ] ) zero_le_two ) ] ⟩, by rw [ Int.toNat_of_nonneg ( Int.ediv_nonneg ( show 0 ≤ x by linarith [ hA hx.1 ] ) zero_le_two ) ] ; rw [ mul_comm, Int.ediv_mul_cancel hx.2 ] ⟩;
            · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ] ; linarith;
          exact h_all_even ▸ Finset.filter_subset _ _;
        refine' ⟨ fun i => if i = 0 then 0 else if i = 1 then 2 else 4, _, _ ⟩ <;> simp +decide [ Fin.forall_fin_succ ];
        exact ⟨ ⟨ h_all_even <| Finset.mem_image.mpr ⟨ 1, by norm_num; linarith, by norm_num ⟩, h_all_even <| Finset.mem_image.mpr ⟨ 2, by norm_num; linarith, by norm_num ⟩ ⟩, h_all_even <| Finset.mem_image.mpr ⟨ 3, by norm_num; linarith, by norm_num ⟩ ⟩;
      · -- Otherwise, there exists another odd integer $2j+1 \neq 2k+1$ in $A$.
        obtain ⟨j, hj⟩ : ∃ j ∈ Finset.range n, (2 * j + 1 : ℤ) ∈ A ∧ (2 * j + 1 : ℤ) ≠ 2 * k + 1 := by
          push Not at h_odd;
          obtain ⟨ x, hx₁, hx₂, hx₃ ⟩ := h_odd; use ( Int.toNat ( x / 2 ) ) ; have := hA hx₁; simp_all +decide ;
          grind +ring;
        -- Consider the three integers $j$, $j+1$, and $2k+1-j$.
        use ![j, j + 1, 2 * k + 1 - j];
        simp_all +decide [ Fin.forall_fin_succ, Function.Injective ];
        grind

/-
Lower bound: odd numbers in {1,...,2n} form a set of size n with no 3 distinct integers
    having all pairwise sums in the set.
-/
lemma g3_lower (n : ℕ) :
    ∃ A : Finset ℤ, A ⊆ Icc (1 : ℤ) (2 * ↑n) ∧ n ≤ A.card ∧ ¬HasPairwiseSums A 3 := by
      -- Let's construct the set $A$ as the image of the function $(fun i => 2 * i + 1)$ over the interval $[0, n-1]$.
      use Finset.image (fun i : ℕ => 2 * i + 1 : ℕ → ℤ) (Finset.range n);
      rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
      constructor;
      · exact Finset.image_subset_iff.mpr fun i hi => Finset.mem_Icc.mpr ⟨ by linarith, by linarith [ Finset.mem_range.mp hi ] ⟩;
      · rintro ⟨ b, hb ⟩;
        simp_all +decide [ Fin.forall_fin_succ, Function.Injective ];
        omega

/-- g₃(n) = 1 for all n ≥ 3. -/
theorem g3 (n : ℕ) (hn : 3 ≤ n) : gFun 3 n = 1 := by
  unfold gFun
  apply sInf_eq_of_mem_of_forall_lt_not_mem
  · -- 1 ∈ S: upper bound
    intro A hA hcard
    exact g3_upper n hn A hA hcard
  · -- ∀ k < 1, k ∉ S: lower bound (only k = 0)
    intro k hk
    simp only [Set.mem_setOf_eq, not_forall]
    interval_cases k
    obtain ⟨A, hAsub, hAcard, hAneg⟩ := g3_lower n
    exact ⟨A, hAsub, by omega, hAneg⟩

#print axioms g3
-- 'Erdos866b.g3' depends on axioms: [propext, Classical.choice, Quot.sound]

/-! ## Remark g3small: g₃(1) = 2 and g₃(2) = 2 -/

lemma g3small_1_upper (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) 2) (hcard : 3 ≤ A.card) :
    HasPairwiseSums A 3 := by
  have h1 := card_le_card hA
  have h2 : (Icc (1:ℤ) 2).card = 2 := by decide
  omega

lemma g3small_1_lower :
    ∃ A : Finset ℤ, A ⊆ Icc (1 : ℤ) 2 ∧ 2 ≤ A.card ∧ ¬HasPairwiseSums A 3 := by
      use {1, 2};
      unfold HasPairwiseSums;
      simp +decide [ Fin.forall_fin_succ, Function.Injective ];
      omega

lemma g3small_2_upper (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) 4) (hcard : 4 ≤ A.card) :
    HasPairwiseSums A 3 := by
  -- A = {1,2,3,4}. Take b = (0, 1, 2), sums are 1, 2, 3.
  have hA4 : A = Icc (1 : ℤ) 4 := by
    apply eq_of_subset_of_card_le hA
    have : (Icc (1:ℤ) 4).card = 4 := by decide
    omega
  refine ⟨![0, 1, 2], ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one,
      Finset.mem_Icc]

lemma g3small_2_lower :
    ∃ A : Finset ℤ, A ⊆ Icc (1 : ℤ) 4 ∧ 3 ≤ A.card ∧ ¬HasPairwiseSums A 3 := by
      -- Consider the set $A = \{2, 3, 4\}$.
      use {2, 3, 4};
      simp +decide;
      rintro ⟨ b, hb₁, hb₂ ⟩;
      simp_all +decide [ Fin.forall_fin_succ, Function.Injective ];
      omega

/-- g₃(1) = 2 and g₃(2) = 2. -/
theorem g3small : gFun 3 1 = 2 ∧ gFun 3 2 = 2 := by
  constructor
  · unfold gFun
    apply sInf_eq_of_mem_of_forall_lt_not_mem
    · intro A hA hcard; exact g3small_1_upper A hA hcard
    · intro k hk
      simp only [Set.mem_setOf_eq, not_forall]
      obtain ⟨A, h1, h2, h3⟩ := g3small_1_lower
      interval_cases k
      · exact ⟨A, h1, by omega, h3⟩
      · exact ⟨A, h1, h2, h3⟩
  · unfold gFun
    apply sInf_eq_of_mem_of_forall_lt_not_mem
    · intro A hA hcard; exact g3small_2_upper A hA hcard
    · intro k hk
      simp only [Set.mem_setOf_eq, not_forall]
      obtain ⟨A, h1, h2, h3⟩ := g3small_2_lower
      interval_cases k
      · exact ⟨A, h1, by omega, h3⟩
      · exact ⟨A, h1, h2, h3⟩

/-! ## Theorem g3nonnegative -/

/-
Base case of g3nonnegative for n = 3
-/
lemma g3nonnegative_base (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) 6) (hcard : 4 ≤ A.card) :
    ∃ b : Fin 3 → ℤ, StrictMono b ∧ (∀ i : Fin 3, 0 ≤ b i) ∧
      ∀ i j : Fin 3, i < j → b i + b j ∈ A := by
        -- By examining all possible subsets of {1, 2, 3, 4, 5, 6} with at least 4 elements, we can verify that each one contains three distinct integers whose pairwise sums are all in the subset.
        have h_examine : ∀ A : Finset ℤ, A ⊆ (Finset.Icc 1 6) → 4 ≤ A.card → ∃ b : Fin 3 → ℤ, StrictMono b ∧ (∀ i, 0 ≤ b i) ∧ ∀ i j, i < j → b i + b j ∈ A := by
          intros A hA hcard; have h_examine : ∃ b₁ ∈ Finset.Icc 0 5, ∃ b₂ ∈ Finset.Icc 0 6, ∃ b₃ ∈ Finset.Icc 0 7, b₁ < b₂ ∧ b₂ < b₃ ∧ b₁ + b₂ ∈ A ∧ b₁ + b₃ ∈ A ∧ b₂ + b₃ ∈ A := by
            decide +revert;
          obtain ⟨ b₁, hb₁, b₂, hb₂, b₃, hb₃, h₁₂, h₂₃, h₁₂', h₁₃', h₂₃' ⟩ := h_examine; use fun i ↦ if i = 0 then b₁ else if i = 1 then b₂ else b₃; simp_all +decide [ Fin.forall_fin_succ, StrictMono ] ;
          grind +splitIndPred;
        exact h_examine A hA hcard

/-
If 1 ∉ A, shifting argument for g3nonnegative induction step
-/
lemma g3nonneg_shift (n : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * (↑n + 1))) (hcard : (n + 1) + 1 ≤ A.card)
    (h1 : (1 : ℤ) ∉ A)
    (ih : ∀ A' : Finset ℤ, A' ⊆ Icc (1 : ℤ) (2 * ↑n) → n + 1 ≤ A'.card →
      ∃ b : Fin 3 → ℤ, StrictMono b ∧ (∀ i : Fin 3, 0 ≤ b i) ∧
        ∀ i j : Fin 3, i < j → b i + b j ∈ A') :
    ∃ b : Fin 3 → ℤ, StrictMono b ∧ (∀ i : Fin 3, 0 ≤ b i) ∧
      ∀ i j : Fin 3, i < j → b i + b j ∈ A := by
        -- Define A' = (A.image (· - 2)).erase 0.
        set A' := (A.image (· - 2)).erase 0;
        -- Apply the induction hypothesis to A' to get b' with sums in A'.
        obtain ⟨b', hb'_mono, hb'_nonneg, hb'_sums⟩ : ∃ b' : Fin 3 → ℤ, StrictMono b' ∧ (∀ i, 0 ≤ b' i) ∧ ∀ i j, i < j → b' i + b' j ∈ A' := by
          apply ih;
          · grind;
          · have h_card_erase : (A.image (· - 2)).card ≥ n + 1 := by
              rw [ Finset.card_image_of_injective _ ( sub_left_injective ) ] ; linarith;
            by_cases h0 : 0 ∈ A.image (· - 2);
            · rw [ Finset.card_erase_of_mem h0 ];
              rw [ Finset.card_image_of_injective _ ( sub_left_injective ) ] at * ; omega;
            · aesop;
        use fun i => b' i + 1;
        simp_all +decide [ Fin.forall_fin_succ, StrictMono ];
        grind

/-
If 1 ∈ A and A has consecutive elements m, m+1 with m ≥ 2
-/
lemma g3nonneg_consec (A : Finset ℤ) (m : ℤ)
    (h1 : (1 : ℤ) ∈ A) (hm : 2 ≤ m) (hm_in : m ∈ A) (hm1_in : m + 1 ∈ A) :
    ∃ b : Fin 3 → ℤ, StrictMono b ∧ (∀ i : Fin 3, 0 ≤ b i) ∧
      ∀ i j : Fin 3, i < j → b i + b j ∈ A := by
        exists fun i => if i = 0 then 0 else if i = 1 then 1 else m;
        simp +decide [ Fin.forall_fin_succ, StrictMono ];
        grind

/-
If 1 ∈ A and no consecutive pair m, m+1 with m ≥ 2, then take (0,2,4)
-/
lemma g3nonneg_no_consec (n : ℕ) (hn : 3 ≤ n) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * (↑n + 1))) (hcard : (n + 1) + 1 ≤ A.card)
    (h1 : (1 : ℤ) ∈ A)
    (hno_consec : ¬∃ m : ℤ, 2 ≤ m ∧ m ∈ A ∧ m + 1 ∈ A) :
    ∃ b : Fin 3 → ℤ, StrictMono b ∧ (∀ i : Fin 3, 0 ≤ b i) ∧
      ∀ i j : Fin 3, i < j → b i + b j ∈ A := by
        -- Since 1 ∈ A and no consecutive pair m, m+1 with m ≥ 2 exists in A, we claim A must contain {2,4,6}.
        have h_two_four_six : 2 ∈ A ∧ 4 ∈ A ∧ 6 ∈ A := by
          have h2 : 2 ∈ A := by
            contrapose! hcard;
            -- If 2 ∉ A, then the elements of A \ {1} are non-consecutive and in {3,...,2n+2}. The max number of non-consecutive elements in {3,...,2n+2} is at most n (pair them as {3,4}, {5,6},...).
            have h_non_consecutive : Finset.card (A.erase 1) ≤ Finset.card (Finset.image (fun x => (x - 1) / 2) (A.erase 1)) := by
              rw [ Finset.card_image_of_injOn ];
              intros x hx y hy hxy;
              grind +qlia;
            -- The image of the function (x - 1) / 2 over A.erase 1 is a subset of {1, 2, ..., n}.
            have h_image_subset : Finset.image (fun x => (x - 1) / 2) (A.erase 1) ⊆ Finset.Icc 1 (n : ℤ) := by
              grind;
            have := Finset.card_le_card h_image_subset; simp_all +decide ;
            grind
          have h4 : 4 ∈ A := by
            by_contra h4_not_in_A;
            -- If 4 ∉ A, then A ∩ {3,4} = ∅, and A ⊆ {1,2} ∪ {5,...,2n+2} with non-consecutive constraint on {5,...,2n+2}. This gives |A| ≤ 2 + (n-1) = n+1 < n+2, contradiction.
            have h_card : A.card ≤ 2 + (n - 1) := by
              have h_card : A.card ≤ ({1, 2} : Finset ℤ).card + (Finset.filter (fun x => x ∈ A) (Finset.Icc (5 : ℤ) (2 * n + 2))).card := by
                have h_card : A ⊆ ({1, 2} : Finset ℤ) ∪ (Finset.filter (fun x => x ∈ A) (Finset.Icc (5 : ℤ) (2 * n + 2))) := by
                  intro x hx; specialize hA hx; rcases x with ⟨ _ | _ | _ | _ | _ | x ⟩ <;> simp_all +decide ;
                  · exact hno_consec 2 ( by norm_num ) h2 ( by norm_num [ * ] );
                  · grind +splitImp;
                  · tauto;
                exact le_trans ( Finset.card_le_card h_card ) ( Finset.card_union_le _ _ );
              -- Since $A$ has no consecutive elements in the range $\{5, 6, \ldots, 2n+2\}$, the maximum number of elements in this range is $n-1$.
              have h_max_elements : (Finset.filter (fun x => x ∈ A) (Finset.Icc (5 : ℤ) (2 * n + 2))).card ≤ n - 1 := by
                -- Since there are no consecutive elements in $A \cap \{5, 6, \ldots, 2n+2\}$, we can pair each element with the next one.
                have h_pair : Finset.card (Finset.image (fun x => x + 1) (Finset.filter (fun x => x ∈ A) (Finset.Icc (5 : ℤ) (2 * n + 2)))) + Finset.card (Finset.filter (fun x => x ∈ A) (Finset.Icc (5 : ℤ) (2 * n + 2))) ≤ Finset.card (Finset.Icc (5 : ℤ) (2 * n + 3)) := by
                  rw [ ← Finset.card_union_of_disjoint ];
                  · refine Finset.card_le_card ?_;
                    grind;
                  · norm_num [ Finset.disjoint_left ];
                    grind;
                rw [ Finset.card_image_of_injective _ ( add_left_injective _ ) ] at h_pair ; norm_num at * ; omega;
              grind +qlia;
            omega
          have h6 : 6 ∈ A := by
            contrapose! hcard;
            -- If 6∉A, then A can contain at most one element from each pair {2k+1, 2k+2} for k ≥ 3.
            have h_pairs : (A \ {1, 2, 4}).card ≤ (Finset.Icc (7 : ℤ) (2 * n + 2)).card / 2 := by
              have h_pairs : (A \ {1, 2, 4}).card ≤ Finset.card (Finset.image (fun x => (x + 1) / 2) (A \ {1, 2, 4})) := by
                rw [ Finset.card_image_of_injOn ];
                intros x hx y hy; simp_all +decide;
                intro h; have := hno_consec x; have := hno_consec y; rcases Int.even_or_odd' x with ⟨ k, rfl | rfl ⟩ <;> rcases Int.even_or_odd' y with ⟨ l, rfl | rfl ⟩ <;> simp_all +decide ;
                · omega;
                · grind;
                · grind;
                · grind;
              have h_pairs_image : Finset.image (fun x => (x + 1) / 2) (A \ {1, 2, 4}) ⊆ Finset.Icc (4 : ℤ) (n + 1) := by
                simp_all +decide [ Finset.subset_iff ];
                rintro x y hy hy1 hy2 hy4 rfl; constructor <;> contrapose! hno_consec;
                · have : y ≤ 7 := Int.le_of_lt_add_one ( by omega ) ; ( have : y ≥ 1 := hA hy |>.1; interval_cases y <;> simp_all +decide ; );
                  · exact ⟨ 2, by norm_num, h2, hy ⟩;
                  · exact ⟨ 4, by norm_num, h4, hy ⟩;
                · grind;
              have := Finset.card_mono h_pairs_image; simp_all +decide ;
              omega;
            rw [ Finset.card_sdiff ] at h_pairs ; simp_all +decide [ Finset.subset_iff ];
            omega
          exact ⟨h2, h4, h6⟩;
        exact ⟨ fun i => if i = 0 then 0 else if i = 1 then 2 else 4, by decide, by decide, by simp +decide [ *, Fin.forall_fin_succ ] ⟩

/-- For n ≥ 3, any A ⊆ {1,...,2n} with |A| ≥ n+1 has nonnegative 0 ≤ b₁ < b₂ < b₃
    with pairwise sums in A. -/
theorem g3nonnegative (n : ℕ) (hn : 3 ≤ n) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n)) (hcard : n + 1 ≤ A.card) :
    ∃ b : Fin 3 → ℤ, StrictMono b ∧ (∀ i : Fin 3, 0 ≤ b i) ∧
      ∀ i j : Fin 3, i < j → b i + b j ∈ A := by
  induction n, hn using Nat.le_induction generalizing A with
  | base => exact g3nonnegative_base A (by simpa using hA) (by omega)
  | succ n hn ih =>
    by_cases h1 : (1 : ℤ) ∈ A
    · by_cases hc : ∃ m : ℤ, 2 ≤ m ∧ m ∈ A ∧ m + 1 ∈ A
      · obtain ⟨m, hm1, hm2, hm3⟩ := hc
        exact g3nonneg_consec A m h1 hm1 hm2 hm3
      · exact g3nonneg_no_consec n hn A hA hcard h1 hc
    · exact g3nonneg_shift n A hA hcard h1 ih

/-! ## Theorem h3: h₃(n) = 3 for all n ≥ 2 -/

lemma HasPosPairwiseSums_of_triple {A : Finset ℤ}
    {a b c : ℤ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a < b) (hbc : b < c) (htri : c < a + b) (heven : Even (a + b + c))
    (_hapos : 0 < a) : HasPosPairwiseSums A 3 := by
  refine ⟨fun i ↦ if i.val = 0 then (a + b - c) / 2 else if i.val = 1 then (a + c - b) / 2
    else (b + c - a) / 2, ?_, ?_, ?_⟩ <;> simp_all +decide [Function.Injective]
  · omega
  · grind
  · grind +ring

/-! ## Lower bound -/

lemma not_HasPosPairwiseSums_of_no_large_even {A : Finset ℤ}
    (hA : ∀ x ∈ A, Odd x ∨ x = 2) : ¬HasPosPairwiseSums A 3 := by
  rintro ⟨b, hb⟩; simp_all +decide [Fin.forall_fin_succ]; grind

lemma h3_lower (n : ℕ) (hn : 4 ≤ n) :
    ∀ k < 2, k ∉ {m : ℕ | ∀ (A : Finset ℤ), A ⊆ Icc (1 : ℤ) (2 * ↑n) →
      n + m ≤ A.card → HasPosPairwiseSums A 3} := by
  intro k hk_lt hk_mem; contrapose! hk_mem; simp_all +decide [Set.mem_setOf_eq]
  use Finset.image (fun i : ℕ => 2 * i + 1 : ℕ → ℤ) (Finset.range n) ∪ {2}
  constructor <;> norm_num [Finset.subset_iff]
  · linarith
  · rw [Finset.card_insert_of_notMem] <;>
      norm_num [Finset.card_image_of_injective, Function.Injective]
    interval_cases k <;> simp_all +decide
    · apply not_HasPosPairwiseSums_of_no_large_even; intro x hx; aesop
    · apply not_HasPosPairwiseSums_of_no_large_even; intro x hx; aesop
    · omega

/-! ## Upper bound: new approach via two largest odd elements -/

/-
Case 1: When A has at most 2 odd elements, all even numbers in {2,...,2n} are in A,
    so (2n-4, 2n-2, 2n) forms a valid triple.
-/
lemma hps_few_odds {A : Finset ℤ} {n : ℕ} (hn : 4 ≤ n)
    (hA : A ⊆ Icc 1 (2 * ↑n)) (hcard : (n : ℤ) + 2 ≤ A.card)
    (hfew : (A.filter (fun x => ¬Even x)).card ≤ 2) :
    HasPosPairwiseSums A 3 := by
  -- Since $A$ has at most 2 odd elements, $A$ contains at least $n$ even elements.
  have h_even_card : (A.filter Even).card ≥ n := by
    rw [ Finset.filter_not, Finset.card_sdiff ] at hfew ; norm_cast at *;
    rw [ Finset.inter_eq_left.mpr ( Finset.filter_subset _ _ ) ] at hfew ; omega;
  -- Since there are exactly $n$ even numbers in $\{1, \dots, 2n\}$, and $A$ contains at least $n$ even numbers, $A$ must contain all even numbers in $\{1, \dots, 2n\}$.
  have h_even_all : A.filter Even = Finset.image (fun k : ℕ => 2 * k : ℕ → ℤ) (Finset.Icc 1 n) := by
    refine' Finset.eq_of_subset_of_card_le _ _;
    · intro x hx; have := hA ( Finset.mem_filter.mp hx |>.1 ) ; simp_all +decide [ Int.even_iff ];
      exact ⟨ Int.toNat ( x / 2 ), ⟨ by linarith [ Int.ediv_mul_cancel hx.2, Int.toNat_of_nonneg ( by linarith [ Int.ediv_mul_cancel hx.2 ] : 0 ≤ x / 2 ) ], by linarith [ Int.ediv_mul_cancel hx.2, Int.toNat_of_nonneg ( by linarith [ Int.ediv_mul_cancel hx.2 ] : 0 ≤ x / 2 ) ] ⟩, by linarith [ Int.ediv_mul_cancel hx.2, Int.toNat_of_nonneg ( by linarith [ Int.ediv_mul_cancel hx.2 ] : 0 ≤ x / 2 ) ] ⟩;
    · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ] ; linarith;
  -- In particular, $2n-4$, $2n-2$, and $2n$ are in $A$.
  have h_even_elements : (2 * n - 4 : ℤ) ∈ A ∧ (2 * n - 2 : ℤ) ∈ A ∧ (2 * n : ℤ) ∈ A := by
    replace h_even_all := Finset.ext_iff.mp h_even_all; have := h_even_all ( 2 * n - 4 ) ; have := h_even_all ( 2 * n - 2 ) ; have := h_even_all ( 2 * n ) ; simp_all +decide ;
    exact ⟨ by exact ( h_even_all _ ) |>.2 ⟨ n - 2, ⟨ by omega, by omega ⟩, by omega ⟩ |>.1, ⟨ n - 1, ⟨ by omega, by omega ⟩, by omega ⟩, by linarith ⟩;
  convert HasPosPairwiseSums_of_triple h_even_elements.1 h_even_elements.2.1 h_even_elements.2.2 _ _ _ _ _ using 1 <;> norm_num;
  · linarith;
  · grind;
  · grind

/-
Extract two largest odd elements from A when there are ≥ 3 odd elements.
-/
lemma exists_consec_odds {A : Finset ℤ} {n : ℕ}
    (hA : A ⊆ Icc 1 (2 * ↑n))
    (hmany : 3 ≤ (A.filter (fun x => ¬Even x)).card) :
    ∃ o₁ o₂ : ℤ, o₁ ∈ A ∧ o₂ ∈ A ∧ Odd o₁ ∧ Odd o₂ ∧
    3 ≤ o₁ ∧ o₁ < o₂ ∧ o₂ ≤ 2 * ↑n - 1 ∧
    (∀ x ∈ A, Odd x → x ≤ o₂) ∧
    (∀ x ∈ A, Odd x → x ≤ o₁ ∨ x = o₂) := by
  -- Let's obtain the two largest odd elements in A.
  obtain ⟨o₂, ho₂⟩ : ∃ o₂ : ℤ, o₂ ∈ A ∧ Odd o₂ ∧ (∀ x ∈ A, Odd x → x ≤ o₂) := by
    obtain ⟨o₂, ho₂⟩ : ∃ o₂ : ℤ, o₂ ∈ (A.filter (fun x => ¬Even x)) ∧ ∀ x ∈ (A.filter (fun x => ¬Even x)), x ≤ o₂ := by
      exact ⟨ Finset.max' _ <| Finset.card_pos.mp <| pos_of_gt hmany, Finset.max'_mem _ _, fun x hx => Finset.le_max' _ _ hx ⟩;
    aesop;
  -- Let's obtain the second largest odd element in A.
  obtain ⟨o₁, ho₁⟩ : ∃ o₁ : ℤ, o₁ ∈ A ∧ Odd o₁ ∧ o₁ < o₂ ∧ (∀ x ∈ A, Odd x → x < o₂ → x ≤ o₁) := by
    obtain ⟨o₁, ho₁⟩ : ∃ o₁ : ℤ, o₁ ∈ A ∧ Odd o₁ ∧ o₁ < o₂ := by
      obtain ⟨ x, hx ⟩ := Finset.exists_mem_ne ( lt_of_lt_of_le ( by decide ) hmany ) o₂;
      exact ⟨ x, Finset.mem_filter.mp hx.1 |>.1, by simpa using Finset.mem_filter.mp hx.1 |>.2, lt_of_le_of_ne ( ho₂.2.2 x ( Finset.mem_filter.mp hx.1 |>.1 ) ( by simpa using Finset.mem_filter.mp hx.1 |>.2 ) ) hx.2 ⟩;
    exact ⟨ Finset.max' ( A.filter fun x => Odd x ∧ x < o₂ ) ⟨ o₁, by aesop ⟩, Finset.mem_filter.mp ( Finset.max'_mem ( A.filter fun x => Odd x ∧ x < o₂ ) ⟨ o₁, by aesop ⟩ ) |>.1, Finset.mem_filter.mp ( Finset.max'_mem ( A.filter fun x => Odd x ∧ x < o₂ ) ⟨ o₁, by aesop ⟩ ) |>.2.1, Finset.mem_filter.mp ( Finset.max'_mem ( A.filter fun x => Odd x ∧ x < o₂ ) ⟨ o₁, by aesop ⟩ ) |>.2.2, fun x hx hx' hx'' => Finset.le_max' _ _ ( by aesop ) ⟩;
  contrapose! hmany;
  -- Since $o₁ < 3$, the only possible odd elements in $A$ are $1$ and $3$.
  have h_odd_elements : {x ∈ A | ¬Even x} ⊆ {1, o₂} := by
    grind;
  exact lt_of_le_of_lt ( Finset.card_le_card h_odd_elements ) ( by exact lt_of_le_of_lt ( Finset.card_insert_le _ _ ) ( by norm_num ) )

/-
Counting argument: given two consecutive largest odd elements o₁ < o₂ in A,
    there exists an even element e ∈ A in the range (o₂-o₁, o₁+o₂).
-/
lemma good_even_exists {A : Finset ℤ} {n : ℕ} (hn : 4 ≤ n)
    (hA : A ⊆ Icc 1 (2 * ↑n)) (hcard : (n : ℤ) + 2 ≤ A.card)
    {o₁ o₂ : ℤ} (ho1A : o₁ ∈ A) (ho2A : o₂ ∈ A)
    (ho1 : Odd o₁) (ho2 : Odd o₂)
    (ho1_ge : 3 ≤ o₁) (hlt : o₁ < o₂) (ho2_le : o₂ ≤ 2 * ↑n - 1)
    (hmax : ∀ x ∈ A, Odd x → x ≤ o₂)
    (hconsec : ∀ x ∈ A, Odd x → x ≤ o₁ ∨ x = o₂) :
    ∃ e ∈ A, Even e ∧ o₂ - o₁ < e ∧ e < o₁ + o₂ := by
  -- Assume there's no good even in A. Then all good even numbers are in C.
  by_contra hnone;
  -- Define D and G, and show D ∪ G ⊆ C.
  set D := Finset.filter (fun x => ¬Even x) (Finset.Icc (o₁ + 2) (2 * n - 1)) \ {o₂} with hD
  set G := Finset.filter (fun x => Even x) (Finset.Icc (o₂ - o₁ + 2) (min (o₁ + o₂ - 1) (2 * n))) with hG
  have hDG_subset_C : D ∪ G ⊆ Finset.Icc 1 (2 * n) \ A := by
    grind;
  -- Show |D ∪ G| > n - 2.
  have hDG_card : (D ∪ G).card > n - 2 := by
    -- Calculate the cardinality of D and G.
    have hD_card : D.card = (2 * n - o₁ - 3) / 2 := by
      rw [ Finset.card_sdiff ] ; norm_num;
      rw [ Finset.card_eq_of_bijective ];
      case f => exact fun i hi => o₁ + 2 + 2 * i;
      any_goals exact ( Int.toNat ( ( 2 * n - o₁ - 3 ) / 2 ) + 1 );
      · grind;
      · simp +zetaDelta at *;
        intro a ha₁ ha₂ ha₃; obtain ⟨ k, rfl ⟩ := ha₃; use Int.toNat ( k - ( o₁ / 2 + 1 ) ) ; norm_num;
        grind;
      · grind +revert;
      · aesop
    have hG_card : G.card ≥ (o₁ + 1) / 2 := by
      have hG_card : G.card ≥ Finset.card (Finset.image (fun k : ℤ => 2 * k) (Finset.Icc ((o₂ - o₁ + 2 + 1) / 2) ((min (o₁ + o₂ - 1) (2 * n)) / 2))) := by
        refine Finset.card_le_card ?_;
        simp +decide [ Finset.subset_iff ];
        rintro x k hk₁ hk₂ rfl; exact Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by omega, by omega ⟩, even_two_mul _ ⟩ ;
      rw [ Finset.card_image_of_injective ] at hG_card <;> norm_num [ Function.Injective ] at *;
      omega;
    rw [ Finset.card_union_of_disjoint ];
    · grind;
    · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by have := Finset.mem_filter.mp ( Finset.mem_sdiff.mp hx₁ |>.1 ) ; have := Finset.mem_filter.mp hx₂; aesop;
  have := Finset.card_mono hDG_subset_C;
  rw [ Finset.card_sdiff ] at this;
  rw [ Finset.inter_eq_left.mpr hA ] at this ; norm_num at * ; omega

/-
Given a "good" even element and two odd elements, construct HasPosPairwiseSums A 3.
-/
lemma hps_of_good_even {A : Finset ℤ}
    {o₁ o₂ e : ℤ} (ho1A : o₁ ∈ A) (ho2A : o₂ ∈ A) (heA : e ∈ A)
    (ho1_odd : Odd o₁) (ho2_odd : Odd o₂) (he_even : Even e)
    (ho1_ge : 3 ≤ o₁) (hlt : o₁ < o₂)
    (he_lb : o₂ - o₁ < e) (he_ub : e < o₁ + o₂) :
    HasPosPairwiseSums A 3 := by
  by_cases h_case1 : e ≤ o₁;
  · convert HasPosPairwiseSums_of_triple heA ho1A ho2A _ _ _ _ _ using 1 <;> try linarith;
    · grind +splitImp;
    · grind;
  · by_cases h_case2 : e < o₂;
    · convert HasPosPairwiseSums_of_triple ho1A heA ho2A _ _ _ _ _ using 1 <;> try linarith;
      grind;
    · convert HasPosPairwiseSums_of_triple ho1A ho2A heA _ _ _ _ _ using 1 <;> try linarith;
      · grind;
      · grind

/-- Main upper bound: any A ⊆ {1,...,2n} with |A| ≥ n+2 contains pairwise sums of 3 positive integers. -/
lemma h3_upper (n : ℕ) (hn : 4 ≤ n) :
    (2 : ℕ) ∈ {m : ℕ | ∀ (A : Finset ℤ), A ⊆ Icc (1 : ℤ) (2 * ↑n) →
      n + m ≤ A.card → HasPosPairwiseSums A 3} := by
  intro A hA hcard
  by_cases hfew : (A.filter (fun x => ¬Even x)).card ≤ 2
  · exact hps_few_odds hn hA (by omega) hfew
  · push Not at hfew
    obtain ⟨o₁, o₂, ho1A, ho2A, ho1, ho2, ho1_ge, hlt_o, ho2_le, hmax, hconsec⟩ :=
      exists_consec_odds hA (by omega)
    obtain ⟨e, heA, he_even, he_lb, he_ub⟩ :=
      good_even_exists hn hA (by omega) ho1A ho2A ho1 ho2 ho1_ge hlt_o ho2_le hmax hconsec
    exact hps_of_good_even ho1A ho2A heA ho1 ho2 he_even ho1_ge hlt_o he_lb he_ub

theorem h3 (n : ℕ) (hn : 4 ≤ n) : hFun 3 n = 2 := by
  unfold hFun
  exact sInf_eq_of_mem_of_forall_lt_not_mem (h3_upper n hn) (h3_lower n hn)

#print axioms h3
-- 'Erdos866b.h3' depends on axioms: [propext, Classical.choice, Quot.sound]

/-! ## Theorem g4: g₄(n) = 3 for all n ≥ 2 -/

/-
Upper bound for g₄: any A ⊆ {1,...,2n} with |A| ≥ n+3 has pairwise sums of 4 distinct integers.
-/
lemma g4_upper (n : ℕ) (hn : 3 ≤ n) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n)) (hcard : n + 3 ≤ A.card) :
    HasPairwiseSums A 4 := by
      -- Let $a_1, a_2, a_3$ be three distinct even integers such that $A$ contains $\{a_i, 2n+1-a_i\}$ for all $1 \le i \le 3$.
      obtain ⟨a1, a2, a3, ha1, ha2, ha3, hA1, hA2, hA3⟩ : ∃ a1 a2 a3 : ℤ, a1 ∈ A ∧ a2 ∈ A ∧ a3 ∈ A ∧ 2 * n + 1 - a1 ∈ A ∧ 2 * n + 1 - a2 ∈ A ∧ 2 * n + 1 - a3 ∈ A ∧ a1 ≠ a2 ∧ a1 ≠ a3 ∧ a2 ≠ a3 ∧ Even a1 ∧ Even a2 ∧ Even a3 := by
        -- Since $|A| \geq n+3$, by pigeonhole at least 3 pairs have both elements in $A$. Let $a_1 < a_2 < a_3$ be the smaller elements of these pairs.
        obtain ⟨S, hS⟩ : ∃ S : Finset ℤ, S ⊆ Finset.image (fun k => k) (Finset.Icc 1 n) ∧ S.card ≥ 3 ∧ ∀ k ∈ S, k ∈ A ∧ (2 * n + 1 - k) ∈ A := by
          have h_pairs : (Finset.filter (fun k => k ∈ A ∧ (2 * n + 1 - k) ∈ A) (Finset.Icc 1 n)).card ≥ 3 := by
            have h_pigeonhole : ∑ k ∈ Finset.Icc 1 (n : ℤ), (if k ∈ A then 1 else 0) + ∑ k ∈ Finset.Icc 1 (n : ℤ), (if 2 * n + 1 - k ∈ A then 1 else 0) ≥ n + 3 := by
              have h_pigeonhole : ∑ k ∈ Finset.Icc 1 (2 * n : ℤ), (if k ∈ A then 1 else 0) ≥ n + 3 := by
                simp +zetaDelta at *;
                rwa [ Finset.inter_eq_right.mpr hA ];
              convert h_pigeonhole using 1;
              rw [ show ( Finset.Icc 1 ( 2 * n : ℤ ) ) = Finset.Icc 1 ( n : ℤ ) ∪ Finset.image ( fun k : ℤ => 2 * n + 1 - k ) ( Finset.Icc 1 ( n : ℤ ) ) from ?_, Finset.sum_union ];
              · rw [ Finset.sum_image ] ; aesop;
              · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by obtain ⟨ k, hk₁, hk₂ ⟩ := Finset.mem_image.mp hx₂; linarith [ Finset.mem_Icc.mp hx₁, Finset.mem_Icc.mp hk₁ ] ;
              · ext k
                simp;
                exact ⟨ fun h => if h' : k ≤ n then Or.inl ⟨ h.1, h' ⟩ else Or.inr ⟨ 2 * n + 1 - k, ⟨ by linarith, by linarith ⟩, by ring ⟩, fun h => h.elim ( fun h => ⟨ h.1, by linarith ⟩ ) fun ⟨ a, ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ => ⟨ by linarith, by linarith ⟩ ⟩;
            have h_pigeonhole : ∑ k ∈ Finset.Icc 1 (n : ℤ), (if k ∈ A then 1 else 0) + ∑ k ∈ Finset.Icc 1 (n : ℤ), (if 2 * n + 1 - k ∈ A then 1 else 0) ≤ ∑ k ∈ Finset.Icc 1 (n : ℤ), (if k ∈ A ∧ 2 * n + 1 - k ∈ A then 2 else 1) := by
              rw [ ← Finset.sum_add_distrib ] ; exact Finset.sum_le_sum fun x hx => by aesop;
            simp_all +decide [ Finset.sum_ite ];
            have h_pigeonhole : #({x ∈ Icc 1 ↑n | x ∈ A → 2 * ↑n + 1 - x ∉ A}) ≤ n - #({x ∈ Icc 1 ↑n | x ∈ A ∧ 2 * ↑n + 1 - x ∈ A}) := by
              rw [ show ( Finset.filter ( fun x => x ∈ A → 2 * ↑n + 1 - x ∉ A ) ( Finset.Icc 1 ↑n ) ) = Finset.Icc 1 ↑n \ ( Finset.filter ( fun x => x ∈ A ∧ 2 * ↑n + 1 - x ∈ A ) ( Finset.Icc 1 ↑n ) ) by ext; aesop, Finset.card_sdiff ] ; norm_num;
              rw [ Finset.inter_eq_left.mpr ] <;> norm_num;
              omega;
            omega;
          grind;
        -- Since $S$ contains at least 3 elements, we can choose three distinct elements $a_1, a_2, a_3$ from $S$.
        obtain ⟨a1, a2, a3, ha1, ha2, ha3, h_distinct⟩ : ∃ a1 a2 a3 : ℤ, a1 ∈ S ∧ a2 ∈ S ∧ a3 ∈ S ∧ a1 ≠ a2 ∧ a1 ≠ a3 ∧ a2 ≠ a3 ∧ (Even a1 ∨ Even (2 * n + 1 - a1)) ∧ (Even a2 ∨ Even (2 * n + 1 - a2)) ∧ (Even a3 ∨ Even (2 * n + 1 - a3)) := by
          obtain ⟨ s, hs ⟩ := Finset.two_lt_card.1 hS.2.1;
          grind;
        grind +locals;
      -- Define $b_1, b_2, b_3, b_4$ as follows:
      set b1 := (a1 + a2 - a3) / 2
      set b2 := (a1 + a3 - a2) / 2
      set b3 := (a2 + a3 - a1) / 2
      set b4 := (4 * n + 2 - a1 - a2 - a3) / 2;
      -- Verify that $b_1, b_2, b_3, b_4$ are distinct integers and their pairwise sums are in $A$.
      have hb_distinct : b1 ≠ b2 ∧ b1 ≠ b3 ∧ b1 ≠ b4 ∧ b2 ≠ b3 ∧ b2 ≠ b4 ∧ b3 ≠ b4 := by
        grind
      have hb_sums : b1 + b2 ∈ A ∧ b1 + b3 ∈ A ∧ b1 + b4 ∈ A ∧ b2 + b3 ∈ A ∧ b2 + b4 ∈ A ∧ b3 + b4 ∈ A := by
        grind
      use ![b1, b2, b3, b4];
      simp_all +decide [ Fin.forall_fin_succ, Function.Injective ];
      grind

/-
Lower bound for g₄: there exists A ⊆ {1,...,2n} with |A| = n+2 and no pairwise sums of 4 integers.
-/
lemma g4_lower (n : ℕ) (hn : 2 ≤ n) :
    ∃ A : Finset ℤ, A ⊆ Icc (1 : ℤ) (2 * ↑n) ∧ n + 2 ≤ A.card ∧ ¬HasPairwiseSums A 4 := by
      revert hn;
      intro hn
      use Finset.filter (fun x => x % 2 = 1 ∨ x = 2 * n - 2 ∨ x = 2 * n) (Finset.Icc 1 (2 * n));
      refine' ⟨ _, _, _ ⟩;
      · exact Finset.filter_subset _ _;
      · rw [ show ( Finset.filter ( fun x : ℤ => x % 2 = 1 ∨ x = 2 * ↑n - 2 ∨ x = 2 * ↑n ) ( Icc 1 ( 2 * ↑n ) ) ) = Finset.image ( fun x : ℕ => 2 * x + 1 : ℕ → ℤ ) ( Finset.range n ) ∪ { ( 2 * n - 2 : ℤ ), ( 2 * n : ℤ ) } from ?_ ];
        · rw [ Finset.card_union_of_disjoint ] <;> norm_num [ Finset.card_image_of_injective, Function.Injective ];
          exact ⟨ fun x hx => by omega, fun x hx => by omega ⟩;
        · ext;
          constructor;
          · simp +zetaDelta at *;
            rintro h₁ h₂ ( h₃ | rfl | rfl ) <;> [ exact Or.inr ( Or.inr ⟨ Int.toNat ( ( ‹_› : ℤ ) / 2 ), by omega, by omega ⟩ ) ; exact Or.inl rfl ; exact Or.inr ( Or.inl rfl ) ];
          · grind;
      · rintro ⟨ b, hb₁, hb₂ ⟩;
        simp_all +decide [ Fin.forall_fin_succ ];
        grind

/-- g₄(n) = 3 for all n ≥ 2. -/
theorem g4 (n : ℕ) (hn : 2 ≤ n) : gFun 4 n = 3 := by
  unfold gFun
  apply sInf_eq_of_mem_of_forall_lt_not_mem
  · -- 3 ∈ S: upper bound
    intro A hA hcard
    by_cases hn3 : 3 ≤ n
    · exact g4_upper n hn3 A hA hcard
    · -- n = 2: |A| ≥ 5 but A ⊆ {1,2,3,4} has at most 4 elements
      exfalso
      have h1 := card_le_card hA
      have h2 : (Icc (1:ℤ) (2 * ↑n)).card = 2 * n := by
        have : n = 2 := by omega
        subst this; decide
      omega
  · -- ∀ k < 3, k ∉ S
    intro k hk
    simp only [Set.mem_setOf_eq, not_forall]
    obtain ⟨A, hAsub, hAcard, hAneg⟩ := g4_lower n hn
    interval_cases k
    · exact ⟨A, hAsub, by omega, hAneg⟩
    · exact ⟨A, hAsub, by omega, hAneg⟩
    · exact ⟨A, hAsub, hAcard, hAneg⟩

#print axioms g4
-- 'Erdos866b.g4' depends on axioms: [propext, Classical.choice, Quot.sound]

/-! # Weak Sidon Sets -/

/-- A weak Sidon set has no four distinct elements a, b, c, d with a + b = c + d. -/
def IsWeakSidonSet (S : Finset ℤ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    a + b ≠ c + d

noncomputable def diffRepr (A : Finset ℤ) (d : ℤ) : ℕ :=
  (A.filter (fun x => x - d ∈ A)).card

lemma diffRepr_le_two (A : Finset ℤ) (d : ℤ) (hd : d ≠ 0) (hA : IsWeakSidonSet A) :
    diffRepr A d ≤ 2 := by
  contrapose! hA;
  obtain ⟨x₁, x₂, x₃, hx₁, hx₂, hx₃, h_distinct⟩ : ∃ x₁ x₂ x₃ : ℤ, x₁ ∈ A ∧ x₁ - d ∈ A ∧ x₂ ∈ A ∧ x₂ - d ∈ A ∧ x₃ ∈ A ∧ x₃ - d ∈ A ∧ x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃ := by
    have := Finset.two_lt_card.mp hA;
    rcases this with ⟨ a, ha, b, hb, c, hc, hab, hac, hbc ⟩ ; use a, b, c; aesop;
  grind +locals

/-
The number of positive integers d with δ_A(d) ≥ 2 is at most |A|.
-/
lemma card_double_diffs_le (A : Finset ℤ) (hA : IsWeakSidonSet A)
    (S : Finset ℤ) (hS : ∀ d ∈ S, 0 < d ∧ 2 ≤ diffRepr A d) :
    S.card ≤ A.card := by
  -- We construct an injection from S into A.
  have h_inj : ∀ d ∈ S, ∃ w ∈ A, w - d ∈ A ∧ ∀ x ∈ A, x - d ∈ A → w ≤ x := by
    intros d hd; specialize hS d hd; simp_all +decide [ diffRepr ] ;
    exact ⟨ Finset.min' ( A.filter fun x => x - d ∈ A ) ( Finset.card_pos.mp ( pos_of_gt hS.2 ) ), Finset.mem_filter.mp ( Finset.min'_mem ( A.filter fun x => x - d ∈ A ) ( Finset.card_pos.mp ( pos_of_gt hS.2 ) ) ) |>.1, Finset.mem_filter.mp ( Finset.min'_mem ( A.filter fun x => x - d ∈ A ) ( Finset.card_pos.mp ( pos_of_gt hS.2 ) ) ) |>.2, fun x hx hx' => Finset.min'_le _ _ <| by aesop ⟩;
  choose! f hf₁ hf₂ hf₃ using h_inj;
  -- We claim that the map $d \mapsto f(d)$ is injective on $S$.
  have h_inj : ∀ d₁ d₂, d₁ ∈ S → d₂ ∈ S → d₁ ≠ d₂ → f d₁ ≠ f d₂ := by
    intros d₁ d₂ hd₁ hd₂ hne h_eq
    have h_contradiction : (f d₁ + d₁) ∈ A ∧ (f d₁ - d₁) ∈ A ∧ (f d₁ + d₂) ∈ A ∧ (f d₁ - d₂) ∈ A := by
      have h_contradiction : (f d₁ + d₁) ∈ A ∧ (f d₁ - d₁) ∈ A ∧ (f d₁ + d₂) ∈ A ∧ (f d₁ - d₂) ∈ A := by
        have h1 : (f d₁ + d₁) ∈ A := by
          have h_contradiction : ∃ x ∈ A, x - d₁ ∈ A ∧ x ≠ f d₁ := by
            have := hS d₁ hd₁;
            contrapose! this;
            exact fun _ => lt_of_le_of_lt ( Finset.card_le_one.mpr fun x hx y hy => by linarith [ this x ( Finset.mem_filter.mp hx |>.1 ) ( Finset.mem_filter.mp hx |>.2 ), this y ( Finset.mem_filter.mp hy |>.1 ) ( Finset.mem_filter.mp hy |>.2 ) ] ) ( by norm_num );
          obtain ⟨ x, hx₁, hx₂, hx₃ ⟩ := h_contradiction; specialize hf₃ d₁ hd₁ x hx₁ hx₂;
          have := hA ( f d₁ ) ( hf₁ d₁ hd₁ ) ( x - d₁ ) hx₂ x hx₁ ( f d₁ - d₁ ) ( hf₂ d₁ hd₁ ) ; simp_all +decide [ add_comm, sub_eq_iff_eq_add ] ;
          grind +ring
        have h2 : (f d₁ - d₁) ∈ A := by
          exact hf₂ d₁ hd₁
        have h3 : (f d₁ + d₂) ∈ A := by
          have h3 : ∃ x ∈ A, x - d₂ ∈ A ∧ x ≠ f d₂ := by
            have h3 : (A.filter (fun x => x - d₂ ∈ A)).card ≥ 2 := by
              exact hS d₂ hd₂ |>.2;
            exact Exists.elim ( Finset.exists_mem_ne h3 ( f d₂ ) ) fun x hx => ⟨ x, Finset.mem_filter.mp hx.1 |>.1, Finset.mem_filter.mp hx.1 |>.2, hx.2 ⟩;
          obtain ⟨ x, hx₁, hx₂, hx₃ ⟩ := h3;
          have := hA ( f d₂ ) ( hf₁ d₂ hd₂ ) ( x - d₂ ) hx₂ ( f d₂ - d₂ ) ( hf₂ d₂ hd₂ ) x hx₁; simp_all +decide ;
          grind +ring
        have h4 : (f d₁ - d₂) ∈ A := by
          grind
        exact ⟨h1, h2, h3, h4⟩;
      exact h_contradiction;
    have := hA ( f d₁ + d₁ ) h_contradiction.1 ( f d₁ - d₁ ) h_contradiction.2.1 ( f d₁ + d₂ ) h_contradiction.2.2.1 ( f d₁ - d₂ ) h_contradiction.2.2.2; simp_all +decide [ sub_eq_iff_eq_add ] ;
    exact absurd ( this ( by linarith [ hS d₁ hd₁, hS d₂ hd₂ ] ) ( by contrapose! hne; linarith [ hS d₁ hd₁, hS d₂ hd₂ ] ) ( by contrapose! hne; linarith [ hS d₁ hd₁, hS d₂ hd₂ ] ) ( by contrapose! hne; linarith [ hS d₁ hd₁, hS d₂ hd₂ ] ) ) ( by linarith [ hS d₁ hd₁, hS d₂ hd₂ ] );
  exact Finset.card_le_card ( show S.image f ⊆ A from Finset.image_subset_iff.mpr hf₁ ) |> le_trans ( by rw [ Finset.card_image_of_injOn fun x hx y hy hxy => by contrapose! hxy; exact h_inj x y hx hy hxy ] )

/-
Energy bound: the coincidence count for weak Sidon A and B = [1,n].
-/
lemma energy_bound (A : Finset ℤ) (n : ℕ) (hA : IsWeakSidonSet A) (hn : 0 < n) :
    ∑ a ∈ A, ∑ a' ∈ A, max 0 ((n : ℤ) - |a - a'|) ≤
      ↑n * (3 * ↑A.card + ↑n - 1) := by
  revert hn hA;
  -- For a ≠ a': We need to bound Σ_{a≠a'} max(0, n - |a-a'|).
  intro hA hn
  have h_diff : ∑ a ∈ A, ∑ a' ∈ A, (if a = a' then 0 else max 0 (n - |a - a'|)) ≤ ∑ d ∈ Finset.Icc (-n : ℤ) n \ {0}, max 0 (n - |d|) * (diffRepr A d) := by
    have h_diff : ∑ a ∈ A, ∑ a' ∈ A, (if a = a' then 0 else max 0 (n - |a - a'|)) = ∑ d ∈ Finset.Icc (-n : ℤ) n \ {0}, ∑ a ∈ A, ∑ a' ∈ A, (if a - a' = d then max 0 (n - |d|) else 0) := by
      have h_diff : ∑ a ∈ A, ∑ a' ∈ A, (if a = a' then 0 else max 0 (n - |a - a'|)) = ∑ a ∈ A, ∑ a' ∈ A, ∑ d ∈ Finset.Icc (-n : ℤ) n \ {0}, (if a - a' = d then max 0 (n - |d|) else 0) := by
        refine' Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun a' ha' => _;
        by_cases h : a = a' <;> simp +decide [ h ];
        exact fun h' => not_lt.1 fun contra => h <| by cases abs_cases ( a - a' ) <;> linarith [ h' ( by linarith ) ( by linarith ) ] ;
      rw [ h_diff, Finset.sum_comm ];
      rw [ Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.sum_comm ];
      rw [ Finset.sum_comm ];
    rw [h_diff];
    refine' Finset.sum_le_sum fun d hd => _;
    simp +decide [ Finset.sum_ite, mul_comm ];
    simp +decide [ mul_comm, diffRepr ];
    simp +decide [ ← Finset.mul_sum _ _ _, sub_eq_iff_eq_add ];
    rw [ Finset.sum_congr rfl fun x hx => Nat.cast_inj.mpr <| show # ( Finset.filter ( fun y => x = d + y ) A ) = if x - d ∈ A then 1 else 0 from ?_ ] ; aesop;
    split_ifs <;> simp_all +decide;
    · exact Finset.card_eq_one.mpr ⟨ x - d, by ext y; aesop ⟩;
    · exact fun y hy hxy => ‹x - d ∉ A› <| by convert hy using 1; linarith;
  -- Now consider the term $\sum_{d \in \text{Finset.Icc}(-n, n) \setminus \{0\}} \max(0, n - |d|) \cdot \text{diffRepr}(A, d)$.
  have h_term : ∑ d ∈ Finset.Icc (-n : ℤ) n \ {0}, max 0 (n - |d|) * (diffRepr A d) ≤ ∑ d ∈ Finset.Icc (-n : ℤ) n \ {0}, max 0 (n - |d|) + ∑ d ∈ Finset.Icc (-n : ℤ) n \ {0}, max 0 (n - |d|) * (if diffRepr A d = 2 then 1 else 0) := by
    have h_term : ∀ d ∈ Finset.Icc (-n : ℤ) n \ {0}, diffRepr A d ≤ 1 + (if diffRepr A d = 2 then 1 else 0) := by
      intro d hd; split_ifs <;> simp_all +decide ;
      exact Nat.le_of_lt_succ ( lt_of_le_of_ne ( diffRepr_le_two A d hd.2 hA ) ‹_› );
    rw [ ← Finset.sum_add_distrib ];
    exact Finset.sum_le_sum fun x hx => by specialize h_term x hx; split_ifs at * <;> nlinarith [ show ( 0 : ℤ ) ≤ max 0 ( n - |x| ) by positivity ] ;
  -- Now consider the term $\sum_{d \in \text{Finset.Icc}(-n, n) \setminus \{0\}} \max(0, n - |d|) \cdot \mathbf{1}_{\{\text{diffRepr}(A, d) = 2\}}$.
  have h_term2 : ∑ d ∈ Finset.Icc (-n : ℤ) n \ {0}, max 0 (n - |d|) * (if diffRepr A d = 2 then 1 else 0) ≤ 2 * A.card * n := by
    -- The number of positive integers $d$ with $\delta_A(d) \geq 2$ is at most $|A|$.
    have h_card_double_diffs : (Finset.filter (fun d => diffRepr A d = 2) (Finset.Icc (-n : ℤ) n \ {0})).card ≤ 2 * A.card := by
      have h_card_double_diffs : (Finset.filter (fun d => diffRepr A d = 2) (Finset.Icc (-n : ℤ) n \ {0})).card ≤ (Finset.filter (fun d => diffRepr A d ≥ 2) (Finset.Icc 1 n)).card + (Finset.filter (fun d => diffRepr A d ≥ 2) (Finset.Icc 1 n)).card := by
        have h_card_double_diffs : (Finset.filter (fun d => diffRepr A d = 2) (Finset.Icc (-n : ℤ) n \ {0})).card ≤ (Finset.filter (fun d => diffRepr A d ≥ 2) (Finset.Icc 1 n)).card + (Finset.filter (fun d => diffRepr A d ≥ 2) (Finset.Icc (-n : ℤ) (-1))).card := by
          refine' le_trans ( Finset.card_mono _ ) ( Finset.card_union_le _ _ );
          simp +contextual [ Finset.subset_iff ];
          bv_omega;
        convert h_card_double_diffs using 2;
        rw [ Finset.card_filter, Finset.card_filter ];
        apply Finset.sum_bij (fun x hx => -x);
        · exact fun x hx => Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hx ], by linarith [ Finset.mem_Icc.mp hx ] ⟩;
        · grind;
        · exact fun x hx => ⟨ -x, Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hx ], by linarith [ Finset.mem_Icc.mp hx ] ⟩, by ring ⟩;
        · intro x hx; unfold diffRepr; simp +decide ;
          rw [ show { x_1 ∈ A | x_1 - x ∈ A } = Finset.image ( fun y => y + x ) ( { x_1 ∈ A | x_1 + x ∈ A } ) from ?_, Finset.card_image_of_injective _ ( add_left_injective x ) ];
          ext; simp;
          grind;
      have := card_double_diffs_le A hA ( Finset.filter ( fun d => diffRepr A d ≥ 2 ) ( Finset.Icc 1 ( n : ℤ ) ) ) ?_ <;> simp_all +decide [ two_mul ];
      · grind;
      · grind;
    simp_all +decide [ Finset.sum_ite ];
    refine' le_trans ( Finset.sum_le_sum fun x hx => show Max.max 0 ( n - |x| ) ≤ n by exact max_le ( by linarith ) ( sub_le_self _ <| abs_nonneg _ ) ) _ ; norm_num [ mul_assoc, mul_comm, mul_left_comm, h_card_double_diffs ];
    exact mul_le_mul_of_nonneg_left ( mod_cast by linarith ) ( Nat.cast_nonneg _ );
  -- Now consider the term $\sum_{d \in \text{Finset.Icc}(-n, n) \setminus \{0\}} \max(0, n - |d|)$.
  have h_term1 : ∑ d ∈ Finset.Icc (-n : ℤ) n \ {0}, max 0 (n - |d|) ≤ n * (n - 1) := by
    -- We can split the sum into two parts: one over positive $d$ and one over negative $d$.
    have h_split : ∑ d ∈ Finset.Icc (-n : ℤ) n \ {0}, max 0 (n - |d|) = ∑ d ∈ Finset.Icc 1 n, (n - d) + ∑ d ∈ Finset.Icc 1 n, (n - d) := by
      have h_split : Finset.Icc (-n : ℤ) n \ {0} = Finset.image (fun d : ℕ => d : ℕ → ℤ) (Finset.Icc 1 n) ∪ Finset.image (fun d : ℕ => -d : ℕ → ℤ) (Finset.Icc 1 n) := by
        ext d;
        simp +zetaDelta at *;
        constructor;
        · exact fun h => if hd : d > 0 then Or.inl ⟨ Int.natAbs d, ⟨ by omega, by omega ⟩, by omega ⟩ else Or.inr ⟨ Int.natAbs d, ⟨ by omega, by omega ⟩, by omega ⟩;
        · rintro ( ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ | ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ) <;> exact ⟨ ⟨ by linarith, by linarith ⟩, by linarith ⟩;
      rw [ h_split, Finset.sum_union ] <;> norm_num;
      · exact congrArg₂ ( · + · ) ( Finset.sum_congr rfl fun x hx => by rw [ max_eq_right ] <;> linarith [ Finset.mem_Icc.mp hx, Nat.sub_add_cancel ( show x ≤ n from Finset.mem_Icc.mp hx |>.2 ) ] ) ( Finset.sum_congr rfl fun x hx => by rw [ max_eq_right ] <;> linarith [ Finset.mem_Icc.mp hx, Nat.sub_add_cancel ( show x ≤ n from Finset.mem_Icc.mp hx |>.2 ) ] );
      · norm_num [ Finset.disjoint_left ];
        intros; omega;
    -- We can simplify the sum $\sum_{d=1}^{n} (n - d)$ to $\frac{n(n-1)}{2}$.
    have h_sum_pos : ∑ d ∈ Finset.Icc 1 n, (n - d) = n * (n - 1) / 2 := by
      erw [ Finset.sum_Ico_eq_sum_range ];
      convert Finset.sum_range_id n using 1;
      conv_rhs => rw [ ← Finset.sum_range_reflect ] ;
      exact Finset.sum_congr rfl fun x hx => by rw [ Nat.sub_sub ] ;
    cases n <;> norm_num at * ; linarith [ Nat.div_mul_le_self ( Nat.succ ‹_› * ‹_› ) 2 ];
  simp_all +decide [ Finset.sum_ite, Finset.filter_ne ];
  linarith

/-
Cauchy-Schwarz for the fiber sum:
    (|A| · n)² ≤ |A + [1,n]| · Σ_{a,a'} max(0, n - |a-a'|)
-/
lemma cauchy_schwarz_fiber (A : Finset ℤ) (n : ℕ) (hn : 0 < n) :
    ((A.card : ℤ) * n) ^ 2 ≤
      (A + Finset.Icc (1 : ℤ) n).card *
        ∑ a ∈ A, ∑ a' ∈ A, max 0 ((n : ℤ) - |a - a'|) := by
  -- Let $\sigma(u)$ be the number of pairs $(a, b) \in A \times [1, n]$ such that $a + b = u$.
  set sigma : ℤ → ℕ := fun u => ((A ×ˢ (Finset.Icc 1 (n : ℤ))).filter (fun (ab : ℤ × ℤ) => ab.1 + ab.2 = u)).card;
  -- By definition of $sigma$, we know that $\sum_{u \in A + B} \sigma(u)^2$ is the number of quadruples $(a, a', b, b') \in A \times A \times [1, n] \times [1, n]$ such that $a + b = a' + b'$.
  have h_sigma_sq : (∑ u ∈ (A + Finset.Icc 1 (n : ℤ)), (sigma u : ℚ) ^ 2) = (∑ a ∈ A, ∑ a' ∈ A, max 0 ((n : ℤ) - |a - a'|)) := by
    -- By definition of $sigma$, we know that $\sigma(u)^2$ counts the number of pairs $(a, b) \in A \times [1, n]$ such that $a + b = u$.
    have h_sigma_sq_count : ∀ a a' : ℤ, a ∈ A → a' ∈ A → (∑ u ∈ (A + Finset.Icc 1 (n : ℤ)), (if a + 1 ≤ u ∧ u ≤ a + n ∧ a' + 1 ≤ u ∧ u ≤ a' + n then 1 else 0) : ℚ) = max 0 ((n : ℤ) - |a - a'|) := by
      intros a a' ha ha'
      have h_sigma_sq_count : Finset.filter (fun u => a + 1 ≤ u ∧ u ≤ a + n ∧ a' + 1 ≤ u ∧ u ≤ a' + n) (A + Finset.Icc 1 (n : ℤ)) = Finset.Icc (max (a + 1) (a' + 1)) (min (a + n) (a' + n)) := by
        ext; simp [Finset.mem_add];
        grind;
      simp_all +decide;
      cases max_cases a a' <;> cases min_cases a a' <;> cases abs_cases ( a - a' : ℚ ) <;> simp +decide [ * ] <;> ring_nf;
      all_goals norm_cast at *; omega;
    have h_sigma_sq_count : ∀ u ∈ (A + Finset.Icc 1 (n : ℤ)), (sigma u : ℚ) ^ 2 = (∑ a ∈ A, ∑ a' ∈ A, (if a + 1 ≤ u ∧ u ≤ a + n ∧ a' + 1 ≤ u ∧ u ≤ a' + n then 1 else 0) : ℚ) := by
      intros u hu
      have h_sigma_sq_count : (sigma u : ℚ) = (∑ a ∈ A, (if a + 1 ≤ u ∧ u ≤ a + n then 1 else 0) : ℚ) := by
        simp +zetaDelta at *;
        refine' Finset.card_bij ( fun x hx => x.1 ) _ _ _ <;> simp_all +decide [ Finset.mem_filter, Finset.mem_product ];
        · intros; subst_vars; exact ⟨ by linarith, by linarith ⟩ ;
        · intros; subst_vars; linarith;
        · exact fun b hb hb' hb'' => ⟨ u - b, ⟨ by linarith, by linarith ⟩, by ring ⟩;
      rw [ h_sigma_sq_count, sq, Finset.sum_mul ];
      exact Finset.sum_congr rfl fun x hx => by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun y hy => by split_ifs <;> aesop;
    rw [ Finset.sum_congr rfl h_sigma_sq_count, Finset.sum_comm ];
    rw [ Finset.sum_congr rfl fun x hx => Finset.sum_comm ] ; aesop;
  -- By definition of $sigma$, we know that $\sum_{u \in A + B} \sigma(u) = |A| \cdot n$.
  have h_sigma_sum : (∑ u ∈ (A + Finset.Icc 1 (n : ℤ)), (sigma u : ℚ)) = (A.card * n : ℚ) := by
    rw_mod_cast [ ← Finset.card_eq_sum_card_fiberwise ];
    · norm_num;
    · exact fun x hx => Finset.add_mem_add ( Finset.mem_product.mp hx |>.1 ) ( Finset.mem_product.mp hx |>.2 );
  -- By Cauchy-Schwarz inequality, we have $(\sum_{u \in A + B} \sigma(u))^2 \leq |A + B| \cdot \sum_{u \in A + B} \sigma(u)^2$.
  have h_cauchy_schwarz : (∑ u ∈ (A + Finset.Icc 1 (n : ℤ)), (sigma u : ℚ)) ^ 2 ≤ (A + Finset.Icc 1 (n : ℤ)).card * (∑ u ∈ (A + Finset.Icc 1 (n : ℤ)), (sigma u : ℚ) ^ 2) := by
    exact sq_sum_le_card_mul_sum_sq;
  rw [ ← @Int.cast_le ℚ ] ; aesop

/-
Sumset card bound: |A + [1,n]| ≤ N + n - 1 for A ⊆ [1,N].
-/
lemma sumset_card_bound (A : Finset ℤ) (N n : ℕ) (hn : 0 < n)
    (hAN : ∀ a ∈ A, 1 ≤ a ∧ a ≤ ↑N) :
    (A + Finset.Icc (1 : ℤ) n).card ≤ N + n - 1 := by
  refine' le_trans ( Finset.card_le_card _ ) _;
  exact Finset.Icc 2 ( N + n );
  · exact Finset.add_subset_iff.mpr fun x hx y hy => Finset.mem_Icc.mpr ⟨ by linarith [ hAN x hx, Finset.mem_Icc.mp hy ], by linarith [ hAN x hx, Finset.mem_Icc.mp hy ] ⟩;
  · cases N <;> cases n <;> norm_num ; omega

/-
The key sumset inequality.
-/
lemma weak_sidon_key_ineq (A : Finset ℤ) (N n : ℕ)
    (hA : IsWeakSidonSet A) (hAN : ∀ a ∈ A, 1 ≤ a ∧ a ≤ ↑N)
    (hn : 0 < n) :
    A.card ^ 2 * n ≤ (N + n - 1) * (3 * A.card + n - 1) := by
  -- By combining the inequalities from lemmas cauchy_schwarz_fiber, energy_bound, and sumset_card_bound,
  have h_combined : ((A.card : ℤ) * n) ^ 2 ≤ (N + n - 1) * n * (3 * A.card + n - 1) := by
    have h_combined : ((A.card : ℤ) * n) ^ 2 ≤ ((A + Finset.Icc (1 : ℤ) n).card) * n * (3 * A.card + n - 1) := by
      convert cauchy_schwarz_fiber A n hn |> le_trans <| mul_le_mul_of_nonneg_left ( energy_bound A n hA hn ) <| Nat.cast_nonneg _ using 1 ; ring;
    refine le_trans h_combined ?_;
    have h_card_bound : ((A + Finset.Icc (1 : ℤ) n).card : ℤ) ≤ N + n - 1 := by
      exact le_trans ( Nat.cast_le.mpr ( sumset_card_bound A N n hn hAN ) ) ( by omega );
    gcongr;
    linarith;
  cases N <;> cases n <;> norm_num at * ; nlinarith;
  nlinarith

/-- Any weak Sidon set $A ⊆ [1,N]$ satisfies $|A| \leq N^{1/2} + 4N^{1/4} + 11$. -/
theorem weak_sidon_bound (A : Finset ℤ) (N : ℕ) (hA : IsWeakSidonSet A)
    (hAN : ∀ a ∈ A, 1 ≤ a ∧ a ≤ ↑N) :
    (A.card : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) + 4 * (N : ℝ) ^ ((1 : ℝ) / 4) + 11 := by
  by_cases h_card : A.card < 16
  · rcases N with ( _ | _ | N ) <;> norm_num at *
    · exact le_trans ( Finset.card_le_one.mpr fun x hx y hy => by linarith [ hAN x hx, hAN y hy ] ) ( by norm_num )
    · linarith
    · refine le_trans ( Nat.cast_le.mpr ( Nat.le_of_lt_succ h_card ) ) ?_; norm_num
      rw [ ← Real.sqrt_eq_rpow ] ; nlinarith [ Real.sqrt_nonneg ( N + 1 + 1 : ℝ ), Real.mul_self_sqrt ( show 0 ≤ ( N:ℝ ) + 1 + 1 by positivity ), show ( ( N:ℝ ) + 1 + 1 ) ^ ( 1 / 4:ℝ ) ≥ 1 by exact Real.one_le_rpow ( by linarith ) ( by norm_num ) ]
  · set u := Nat.sqrt (A.card)
    have hu_ge_4 : 4 ≤ u := Nat.le_sqrt.2 ( by linarith )
    have hu_sq : u^2 ≤ A.card ∧ A.card < (u + 1)^2 :=
      ⟨ Nat.sqrt_le' _, Nat.lt_succ_sqrt' _ ⟩
    have hN_ge : (N : ℝ) ≥ u^4 - 4 * u^3 + 3 * u^2 + u := by
      have h_ineq : (A.card : ℝ) ^ 2 * (A.card * (u - 3) + 1) ≤ (N + A.card * (u - 3)) * (A.card * u) := by
        have := weak_sidon_key_ineq A N ( A.card * ( u - 3 ) + 1 ) hA hAN ( by nlinarith only [ hu_ge_4, hu_sq ] )
        norm_cast
        grind +splitImp
      have h_N_ge : (A.card : ℝ) * (A.card - u) * (u - 3) + A.card ≤ N * u := by
        nlinarith only [ h_ineq, show ( 0 : ℝ ) < #A by norm_cast; linarith ]
      have h_N_ge2 : (A.card : ℝ) ≥ u^2 := by exact_mod_cast hu_sq.1
      have h_N_ge3 : (A.card : ℝ) * (A.card - u) * (u - 3) ≥ u^2 * (u^2 - u) * (u - 3) := by
        gcongr
        · linarith [ show ( u : ℝ ) ≥ 4 by norm_cast ]
        · nlinarith only [ show ( u : ℝ ) ≥ 4 by norm_cast ]
      nlinarith only [ h_N_ge3, h_N_ge, h_N_ge2, show ( u : ℝ ) ≥ 4 by norm_cast ]
    have h_sqrt_N_ge : (N : ℝ) ^ (1 / 2 : ℝ) ≥ u^2 - 2 * u - 2 := by
      rw [ ← Real.sqrt_eq_rpow, ge_iff_le, Real.le_sqrt ] <;> nlinarith only [ show ( u : ℝ ) ≥ 4 by norm_cast, hN_ge ]
    have hN_fourth_root_ge : (N : ℝ) ^ (1 / 4 : ℝ) ≥ u - 2 := by
      have hN_fourth_root_ge : (N : ℝ) ≥ (u - 2) ^ 4 := by
        nlinarith only [ sq ( u - 2 : ℝ ), hN_ge, show ( u : ℝ ) ≥ 4 by norm_cast ]
      exact le_trans ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by linarith [ show ( u : ℝ ) ≥ 4 by norm_cast ] ) ] ; norm_num ) ( Real.rpow_le_rpow ( by exact pow_nonneg ( by linarith [ show ( u : ℝ ) ≥ 4 by norm_cast ] ) _ ) hN_fourth_root_ge ( by norm_num ) )
    linarith [ show ( A.card : ℝ ) ≤ u ^ 2 + 2 * u by norm_cast; linarith ]

/-! ## Theorem h4upper: h₄(n) ≤ 2270 -/

/-
If the complement B of A in [1, 2n] satisfies 3|B| + 6 < n,
    then A contains 5 consecutive integers (giving HasPosPairwiseSums A 4).
-/
lemma has_pps_of_small_compl (A : Finset ℤ) (n : ℕ) (hn : 4 ≤ n)
    (hB_small : (Finset.Icc (1 : ℤ) (2 * ↑n) \ A).card * 3 + 3 < n) :
    HasPosPairwiseSums A 4 := by
      -- Consider disjoint windows W_k = [6k+3, 6k+7] for k = 0, 1, 2, .... Each window has 5 elements and consecutive windows are disjoint.
      set B_compl := Finset.Icc (1 : ℤ) (2 * n) \ A
      have hwindows : ∃ k : ℕ, 0 ≤ k ∧ k ≤ (n - 4) / 3 ∧ ∀ x : ℤ, 6 * k + 3 ≤ x ∧ x ≤ 6 * k + 7 → x ∉ B_compl := by
        contrapose! hB_small;
        -- Since B_compl contains at least one element from each window, the number of elements in B_compl is at least the number of windows.
        have hB_card : B_compl.card ≥ (n - 4) / 3 + 1 := by
          choose! f hf₁ hf₂ using hB_small;
          have hB_card : B_compl.card ≥ Finset.card (Finset.image f (Finset.Icc 0 ((n - 4) / 3))) := by
            exact Finset.card_le_card <| Finset.image_subset_iff.mpr fun k hk => hf₂ k ( Finset.mem_Icc.mp hk |>.1 ) ( Finset.mem_Icc.mp hk |>.2 );
          rwa [ Finset.card_image_of_injOn fun x hx y hy hxy => by linarith [ hf₁ x ( Finset.mem_Icc.mp hx |>.1 ) ( Finset.mem_Icc.mp hx |>.2 ), hf₁ y ( Finset.mem_Icc.mp hy |>.1 ) ( Finset.mem_Icc.mp hy |>.2 ) ], Nat.card_Icc ] at hB_card;
        omega;
      obtain ⟨ k, hk₁, hk₂, hk₃ ⟩ := hwindows; use fun a => if a = 0 then 3 * k + 1 else if a = 1 then 3 * k + 2 else if a = 2 then 3 * k + 3 else 3 * k + 4; simp_all +decide [ Fin.forall_fin_succ ] ;
      simp_all +decide [ Function.Injective, Fin.forall_fin_succ ];
      simp +zetaDelta at *;
      exact ⟨ ⟨ by linarith, by linarith, by linarith ⟩, ⟨ hk₃ _ ( by linarith ) ( by linarith ) ( by linarith ) ( by omega ), hk₃ _ ( by linarith ) ( by linarith ) ( by linarith ) ( by omega ), hk₃ _ ( by linarith ) ( by linarith ) ( by linarith ) ( by omega ) ⟩, ⟨ hk₃ _ ( by linarith ) ( by linarith ) ( by linarith ) ( by omega ), hk₃ _ ( by linarith ) ( by linarith ) ( by linarith ) ( by omega ) ⟩, hk₃ _ ( by linarith ) ( by linarith ) ( by linarith ) ( by omega ) ⟩

lemma weak_sidon_compl_small (A : Finset ℤ) (n : ℕ) (hn : 2270 ≤ n)
    (hws : IsWeakSidonSet (Finset.Icc (1 : ℤ) (2 * ↑n) \ A)) :
    (Finset.Icc (1 : ℤ) (2 * ↑n) \ A).card * 3 + 3 < n := by
      have h_card_B : (Finset.Icc (1 : ℤ) (2 * n) \ A).card ≤ (2 * n : ℝ) ^ ((1 : ℝ) / 2) + 4 * (2 * n : ℝ) ^ ((1 : ℝ) / 4) + 11 := by
        have := weak_sidon_bound ( Finset.Icc 1 ( 2 * n ) \ A ) ( 2 * n ) hws ; aesop;
      have h_ineq : 3 * ((2 * n : ℝ) ^ ((1 : ℝ) / 2) + 4 * (2 * n : ℝ) ^ ((1 : ℝ) / 4) + 11) + 3 < n := by
        set y : ℝ := (2 * n : ℝ) ^ ((1 : ℝ) / 4)
        have hy4 : y ^ 4 = 2 * n := by
          rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num;
        rw [ show ( 2 * n : ℝ ) ^ ( 1 / 2 : ℝ ) = y ^ 2 by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num ] ; nlinarith [ show ( n : ℝ ) ≥ 2270 by norm_cast, pow_pos ( show 0 < y by positivity ) 3, pow_pos ( show 0 < y by positivity ) 2, pow_pos ( show 0 < y by positivity ) 1 ] ;
      exact_mod_cast ( by linarith : ( Finset.card ( Finset.Icc 1 ( 2 * n : ℤ ) \ A ) : ℝ ) * 3 + 3 < n )

/-
Pigeonhole: find a valid b₃ with correct parity whose 4 cross-sums are in A.
-/
lemma exists_valid_b3 (A : Finset ℤ) (n t : ℕ) (m : ℤ)
    (hA : A ⊆ Finset.Icc 1 (2 * ↑n))
    (hm_lb : 4 * (↑t : ℤ) + 3 ≤ m)
    (hm_ub : m + 4 * (↑t : ℤ) + 3 ≤ ↑n)
    (h_miss : ((Finset.Icc (1 : ℤ) (2 * ↑n)).filter (fun x => ¬ Even x) \ A).card ≤ t) :
    ∃ b₃ : ℤ, m - 4 * ↑t - 2 ≤ b₃ ∧ b₃ ≤ m - 2 ∧
      (m - 1 + b₃ ∈ A) ∧ (m + 1 + b₃ ∈ A) ∧
      (3 * m - 1 - b₃ ∈ A) ∧ (3 * m + 1 - b₃ ∈ A) := by
        revert A m hm_lb hm_ub h_miss;
        intro A m hA hm₁ hm₂ hB;
        -- Let's count the number of bad $b_3$ values.
        have h_bad_count : Finset.card (Finset.filter (fun b₃ => ∃ i ∈ ({1, 2, 3, 4} : Finset ℕ), (let s_i := if i = 1 then m - 1 + b₃ else if i = 2 then m + 1 + b₃ else if i = 3 then 3 * m - 1 - b₃ else 3 * m + 1 - b₃; ¬Even s_i ∧ 1 ≤ s_i ∧ s_i ≤ 2 * n ∧ s_i ∉ A)) (Finset.Icc (m - 4 * t - 2) (m - 2))) ≤ 2 * t := by
          -- Each missing odd can make at most 2 candidate $b_3$ values bad.
          have h_missing_odd_bound : ∀ (s : ℤ), ¬Even s ∧ 1 ≤ s ∧ s ≤ 2 * n ∧ s ∉ A → Finset.card (Finset.filter (fun b₃ => ∃ i ∈ ({1, 2, 3, 4} : Finset ℕ), (let s_i := if i = 1 then m - 1 + b₃ else if i = 2 then m + 1 + b₃ else if i = 3 then 3 * m - 1 - b₃ else 3 * m + 1 - b₃; s_i = s)) (Finset.Icc (m - 4 * t - 2) (m - 2))) ≤ 2 := by
            intro s hs
            simp;
            rw [ show { b₃ ∈ Finset.Icc ( m - 4 * t - 2 ) ( m - 2 ) | m - 1 + b₃ = s ∨ m + 1 + b₃ = s ∨ 3 * m - 1 - b₃ = s ∨ 3 * m + 1 - b₃ = s } = { s - ( m - 1 ), s - ( m + 1 ), 3 * m - 1 - s, 3 * m + 1 - s } ∩ Finset.Icc ( m - 4 * t - 2 ) ( m - 2 ) from ?_ ];
            · grind +locals;
            · grind;
          have h_bad_count : Finset.card (Finset.filter (fun b₃ => ∃ s ∈ ({x ∈ Icc 1 (2 * n : ℤ) | ¬Even x} \ A), ∃ i ∈ ({1, 2, 3, 4} : Finset ℕ), (let s_i := if i = 1 then m - 1 + b₃ else if i = 2 then m + 1 + b₃ else if i = 3 then 3 * m - 1 - b₃ else 3 * m + 1 - b₃; s_i = s)) (Finset.Icc (m - 4 * t - 2) (m - 2))) ≤ 2 * t := by
            have h_bad_count : Finset.card (Finset.biUnion ({x ∈ Icc 1 (2 * n : ℤ) | ¬Even x} \ A) (fun s => Finset.filter (fun b₃ => ∃ i ∈ ({1, 2, 3, 4} : Finset ℕ), (let s_i := if i = 1 then m - 1 + b₃ else if i = 2 then m + 1 + b₃ else if i = 3 then 3 * m - 1 - b₃ else 3 * m + 1 - b₃; s_i = s)) (Finset.Icc (m - 4 * t - 2) (m - 2)))) ≤ 2 * t := by
              refine' le_trans ( Finset.card_biUnion_le ) _;
              refine' le_trans ( Finset.sum_le_sum fun x hx => h_missing_odd_bound x _ ) _;
              · grind +qlia;
              · simpa [ mul_comm ] using Nat.mul_le_mul_left 2 hB;
            convert h_bad_count using 2 ; ext ; simp +decide [ Finset.mem_biUnion ];
            exact ⟨ fun ⟨ h₁, s, hs₁, hs₂ ⟩ => ⟨ s, hs₁, h₁, hs₂ ⟩, fun ⟨ s, hs₁, h₁, hs₂ ⟩ => ⟨ h₁, s, hs₁, hs₂ ⟩ ⟩;
          convert h_bad_count using 2;
          grind;
        contrapose! h_bad_count;
        refine' lt_of_lt_of_le _ ( Finset.card_mono _ );
        rotate_left;
        exact Finset.Icc ( m - 4 * t - 2 ) ( m - 2 ) |> Finset.filter ( fun x => x % 2 = m % 2 );
        · intro x hx; simp_all +decide [ Int.even_iff ] ;
          grind +ring;
        · rw [ show ( Finset.filter ( fun x => x % 2 = m % 2 ) ( Finset.Icc ( m - 4 * t - 2 ) ( m - 2 ) ) ) = Finset.image ( fun x : ℕ => m - 2 - 2 * x ) ( Finset.range ( 2 * t + 1 ) ) from ?_, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
          ext;
          constructor;
          · simp +zetaDelta at *;
            exact fun h₁ h₂ h₃ => ⟨ Int.toNat ( ( m - 2 - ‹ℤ› ) / 2 ), by omega, by omega ⟩;
          · grind

/-
Case 1 helper: Given a central even element 2m in A with m in [4t+3, n-4t-3]
    and at most t missing odd integers, construct HasPosPairwiseSums A 4.
-/
lemma has_pps_central_even (A : Finset ℤ) (n t : ℕ) (m : ℤ)
    (hA : A ⊆ Finset.Icc 1 (2 * ↑n))
    (hm : (2 * m) ∈ A)
    (hm_lb : 4 * (↑t : ℤ) + 3 ≤ m)
    (hm_ub : m + 4 * (↑t : ℤ) + 3 ≤ ↑n)
    (h_miss : ((Finset.Icc (1 : ℤ) (2 * ↑n)).filter (fun x => ¬ Even x) \ A).card ≤ t) :
    HasPosPairwiseSums A 4 := by
      -- Use exists_valid_b3 to get b₃ with the 4 sums in A.
      obtain ⟨b₃, hb₃_range, hb₃_sums⟩ : ∃ b₃ : ℤ, m - 4 * ↑t - 2 ≤ b₃ ∧ b₃ ≤ m - 2 ∧ (m - 1 + b₃ ∈ A) ∧ (m + 1 + b₃ ∈ A) ∧ (3 * m - 1 - b₃ ∈ A) ∧ (3 * m + 1 - b₃ ∈ A) := by
        exact exists_valid_b3 A n t m hA hm_lb hm_ub h_miss
      use ![b₃, m - 1, m + 1, 2 * m - b₃];
      simp +decide [ Fin.forall_fin_succ, Function.Injective, * ];
      refine' ⟨ _, _, _, _ ⟩;
      · omega;
      · exact ⟨ by linarith, by linarith, by linarith, by linarith ⟩;
      · exact ⟨ by convert hb₃_sums.2.1 using 1; ring, by convert hb₃_sums.2.2.1 using 1; ring ⟩;
      · exact ⟨ ⟨ by convert hm using 1; ring, by convert hb₃_sums.2.2.2.1 using 1; ring ⟩, by convert hb₃_sums.2.2.2.2 using 1; ring ⟩

/-! ### Helper lemmas for Case 2 (ceslemgeneral for k=4) -/

/-
Direct witness construction: from 4 even elements with equal pairwise sum
    in a set S ⊆ A₀ where S has a shift d with S+d ⊆ A₀ and S∩(S+d)=∅,
    construct HasPosPairwiseSums A₀ 4.
-/
lemma has_pps_four_of_equal_sums_and_shift
    (A₀ : Finset ℤ)
    (a₁ a₂ a₃ a₄ d : ℤ)
    (ha_ord : a₁ < a₂ ∧ a₂ < a₃ ∧ a₃ < a₄)
    (hsum : a₁ + a₄ = a₂ + a₃)
    (hS : a₁ ∈ A₀ ∧ a₂ ∈ A₀ ∧ a₃ ∈ A₀ ∧ a₄ ∈ A₀)
    (heven₁ : Even a₁)
    (hpos : 0 < a₁)
    (hd : 0 < d)
    (hSd : a₁ + d ∈ A₀ ∧ a₂ + d ∈ A₀ ∧ a₃ + d ∈ A₀)
    (hne1 : d ≠ a₂ - a₁) (hne2 : d ≠ a₃ - a₁) :
    HasPosPairwiseSums A₀ 4 := by
      -- Use witness b = ![a₁/2, a₂ - a₁/2, a₃ - a₁/2, a₁/2 + d].
      use ![a₁ / 2, a₂ - a₁ / 2, a₃ - a₁ / 2, a₁ / 2 + d];
      simp +decide [ Fin.forall_fin_succ, Function.Injective ];
      constructor;
      · grind;
      · grind

/-
For any finset G of integers and d > 0, there exists S ⊆ G
    with 2·|S| ≥ |G| + 1 (so |S| ≥ ⌈(|G|+1)/2⌉) and no two elements of S differ by d.
-/
lemma exists_shift_independent_subset (G : Finset ℤ) (d : ℤ) (hd : 0 < d) :
    ∃ S : Finset ℤ, S ⊆ G ∧ 2 * S.card ≥ G.card ∧
      ∀ x ∈ S, x + d ∉ S := by
        induction G using Finset.strongInduction generalizing d
        rename_i G ih
        by_cases hG : G.Nonempty;
        · -- Let $x = \min G$.
          obtain ⟨x, hx⟩ : ∃ x ∈ G, ∀ y ∈ G, y ≥ x := by
            exact ⟨ Finset.min' G hG, Finset.min'_mem _ _, fun y hy => Finset.min'_le _ _ hy ⟩;
          by_cases hxd : x + d ∈ G;
          · -- Apply the induction hypothesis to $G' = (G.erase x).erase (x + d)$.
            obtain ⟨S', hS'⟩ : ∃ S' ⊆ (G.erase x).erase (x + d), 2 * S'.card ≥ (G.erase x).card - 1 ∧ ∀ x ∈ S', x + d ∉ S' := by
              convert ih ( ( G.erase x ).erase ( x + d ) ) _ d hd using 1;
              · grind;
              · grind;
            use insert x S';
            grind;
          · obtain ⟨ S, hS₁, hS₂, hS₃ ⟩ := ih ( G.erase x ) ( Finset.erase_ssubset hx.1 ) d hd;
            use S ∪ { x };
            grind;
        · aesop

/-
Stronger pigeonhole: uses R/2 bins (even differences only).
-/
lemma pigeonhole_differences_strong (A₀ : Finset ℤ) (hA₀ : 2 ≤ A₀.card)
    (heven : ∀ a ∈ A₀, Even a)
    (R : ℕ) (hR : ∀ a ∈ A₀, ∀ b ∈ A₀, |a - b| ≤ R) (hR_pos : 0 < R) :
    ∃ d : ℤ, 0 < d ∧ Even d ∧ d ≤ R ∧
      R * (A₀.filter (fun x => x + d ∈ A₀)).card ≥
        A₀.card * (A₀.card - 1) := by
          by_contra! h_contra;
          -- Consider the set of pairs (a, b) with a < b and b - a even.
          set pairs := Finset.filter (fun p => p.1 < p.2 ∧ Even (p.2 - p.1)) (A₀ ×ˢ A₀);
          -- By the pigeonhole principle, there must be at least one difference $d$ that appears at least $\frac{|pairs|}{R/2}$ times.
          obtain ⟨d, hd_even, hd_pos, hd_le_R, hd_count⟩ : ∃ d : ℤ, 0 < d ∧ Even d ∧ d ≤ R ∧ (Finset.filter (fun p => p.2 - p.1 = d) pairs).card ≥ (pairs.card : ℚ) / (R / 2) := by
            have h_pigeonhole : ∃ d ∈ Finset.image (fun p => p.2 - p.1) (pairs.filter (fun p => p.2 - p.1 > 0)), (Finset.filter (fun p => p.2 - p.1 = d) pairs).card ≥ (pairs.card : ℚ) / (Finset.card (Finset.image (fun p => p.2 - p.1) (pairs.filter (fun p => p.2 - p.1 > 0)))) := by
              have h_pigeonhole : ∑ d ∈ Finset.image (fun p => p.2 - p.1) (pairs.filter (fun p => p.2 - p.1 > 0)), (Finset.filter (fun p => p.2 - p.1 = d) pairs).card = pairs.card := by
                rw [ ← Finset.card_eq_sum_card_fiberwise ];
                exact fun p hp => Finset.mem_image.mpr ⟨ p, Finset.mem_filter.mpr ⟨ hp, by linarith [ Finset.mem_filter.mp hp ] ⟩, rfl ⟩;
              by_cases h_empty : Finset.image (fun p => p.2 - p.1) (pairs.filter (fun p => p.2 - p.1 > 0)) = ∅;
              · simp_all +decide [ Finset.ext_iff ];
                obtain ⟨ a, ha, b, hb, hab ⟩ := Finset.one_lt_card.mp hA₀;
                cases lt_or_gt_of_ne hab <;> [ exact False.elim ( h_empty _ _ _ ( Finset.mem_filter.mpr ⟨ Finset.mem_product.mpr ⟨ ha, hb ⟩, ‹_›, by simp +decide [ *, parity_simps ] ⟩ ) ‹_› rfl ) ; exact False.elim ( h_empty _ _ _ ( Finset.mem_filter.mpr ⟨ Finset.mem_product.mpr ⟨ hb, ha ⟩, ‹_›, by simp +decide [ *, parity_simps ] ⟩ ) ‹_› rfl ) ];
              · contrapose! h_pigeonhole;
                have := Finset.sum_lt_sum_of_nonempty ( Finset.nonempty_of_ne_empty h_empty ) h_pigeonhole; simp_all +decide [ mul_div_cancel₀ ] ;
                exact ne_of_lt ( mod_cast this );
            -- Since the image of the difference map is contained in {2, 4, ..., R}, which has at most R/2 elements, we have:
            have h_image_card : Finset.card (Finset.image (fun p => p.2 - p.1) (pairs.filter (fun p => p.2 - p.1 > 0))) ≤ R / 2 := by
              have h_image_card : Finset.image (fun p => p.2 - p.1) (pairs.filter (fun p => p.2 - p.1 > 0)) ⊆ Finset.image (fun k : ℕ => 2 * k : ℕ → ℤ) (Finset.Icc 1 (R / 2)) := by
                simp +decide [ Finset.subset_iff ];
                rintro _ a b hp _ rfl; obtain ⟨ k, hk ⟩ := heven a ( by aesop ) ; obtain ⟨ l, hl ⟩ := heven b ( by aesop ) ; simp_all +decide [ parity_simps ] ;
                exact ⟨ Int.toNat ( l - k ), ⟨ by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ l - k ) ], by rw [ Nat.le_div_iff_mul_le zero_lt_two ] ; linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ l - k ), abs_le.mp ( hR _ ( by aesop : k + k ∈ A₀ ) _ ( by aesop : l + l ∈ A₀ ) ) ] ⟩, by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ l - k ) ] ⟩;
              exact le_trans ( Finset.card_le_card h_image_card ) ( Finset.card_image_le.trans ( by simp ) );
            obtain ⟨ d, hd₁, hd₂ ⟩ := h_pigeonhole;
            refine' ⟨ d, _, _, _, hd₂.trans' _ ⟩;
            · grind;
            · aesop;
            · obtain ⟨ p, hp₁, hp₂ ⟩ := Finset.mem_image.mp hd₁; linarith [ abs_le.mp ( hR _ ( Finset.mem_product.mp ( Finset.mem_filter.mp ( Finset.mem_filter.mp hp₁ |>.1 ) |>.1 ) |>.1 ) _ ( Finset.mem_product.mp ( Finset.mem_filter.mp ( Finset.mem_filter.mp hp₁ |>.1 ) |>.1 ) |>.2 ) ) ] ;
            · gcongr;
              · exact Nat.cast_pos.mpr ( Finset.card_pos.mpr ⟨ d, hd₁ ⟩ );
              · rw [ le_div_iff₀ ] <;> norm_cast ; linarith [ Nat.div_mul_le_self R 2 ];
          -- Since $pairs$ contains all pairs $(a, b)$ with $a < b$ and $b - a$ even, we have $pairs.card \geq A₀.card * (A₀.card - 1) / 2$.
          have h_pairs_card : pairs.card ≥ A₀.card * (A₀.card - 1) / 2 := by
            have h_pairs_card : pairs.card ≥ Finset.card (Finset.powersetCard 2 A₀) := by
              have h_pairs_card : Finset.card (Finset.image (fun p => ({p.1, p.2} : Finset ℤ)) pairs) ≥ Finset.card (Finset.powersetCard 2 A₀) := by
                refine Finset.card_le_card ?_;
                intro x hx; rw [ Finset.mem_powersetCard ] at hx; rcases Finset.card_eq_two.mp hx.2 with ⟨ a, b, ha, hb, hab ⟩ ; simp_all +decide [ Finset.subset_iff ] ;
                cases lt_or_gt_of_ne ha <;> [ exact ⟨ a, b, Finset.mem_filter.mpr ⟨ Finset.mem_product.mpr ⟨ hx.1, hx.2 ⟩, by linarith, by simp +decide [ *, parity_simps ] ⟩, rfl ⟩ ; exact ⟨ b, a, Finset.mem_filter.mpr ⟨ Finset.mem_product.mpr ⟨ hx.2, hx.1 ⟩, by linarith, by simp +decide [ *, parity_simps ] ⟩, by rw [ Finset.pair_comm ] ⟩ ];
              exact h_pairs_card.trans ( Finset.card_image_le );
            simp_all +decide [ Nat.choose_two_right ];
          -- Since $pairs$ contains all pairs $(a, b)$ with $a < b$ and $b - a$ even, we have $pairs.card \geq A₀.card * (A₀.card - 1) / 2$. Therefore, $R * (Finset.filter (fun x => x + d ∈ A₀) A₀).card \geq A₀.card * (A₀.card - 1)$.
          have h_final : R * (Finset.filter (fun x => x + d ∈ A₀) A₀).card ≥ pairs.card * 2 := by
            have h_final : (Finset.filter (fun p => p.2 - p.1 = d) pairs).card ≤ (Finset.filter (fun x => x + d ∈ A₀) A₀).card := by
              have h_final : Finset.filter (fun p => p.2 - p.1 = d) pairs ⊆ Finset.image (fun x => (x, x + d)) (Finset.filter (fun x => x + d ∈ A₀) A₀) := by
                simp +contextual [ Finset.subset_iff ];
                grind;
              exact le_trans ( Finset.card_le_card h_final ) ( Finset.card_image_le );
            rw [ ge_iff_le, div_le_iff₀ ] at hd_count <;> norm_cast at *;
            · rw [ mul_div, le_div_iff₀ ] at hd_count <;> norm_cast at * ; nlinarith;
            · exact div_pos ( Nat.cast_pos.mpr hR_pos ) zero_lt_two;
          exact not_lt_of_ge h_final ( lt_of_lt_of_le ( h_contra d hd_even hd_pos hd_le_R ) ( by nlinarith [ Nat.div_mul_cancel ( show 2 ∣ #A₀ * ( #A₀ - 1 ) from even_iff_two_dvd.mp ( Nat.even_mul_pred_self _ ) ) ] ) )

/-
Case 1: when |A₀| ≤ 3473 (t ≤ 433), a central even element exists.
-/
lemma has_pps_large_n_case1 (A : Finset ℤ) (n : ℕ) (hn : 3404 ≤ n)
    (hA : A ⊆ Finset.Icc 1 (2 * ↑n))
    (hcard : n + 2270 ≤ A.card)
    (hA₀_card : (A.filter Even).card ≤ 2593) :
    HasPosPairwiseSums A 4 := by
      obtain ⟨t, ht⟩ : ∃ t : ℕ, (A.filter Even).card = 2270 + t ∧ t ≤ 323 := by
        have hA₀_card_ge : (A.filter Even).card ≥ (A.card - n) := by
          have h_odd_count : (A.filter (fun x => ¬Even x)).card ≤ n := by
            -- The set of odd numbers in A is a subset of {1, 3, 5, ..., 2n-1}, which has exactly n elements.
            have h_odd_subset : (A.filter (fun x => ¬Even x)) ⊆ Finset.image (fun k : ℕ => 2 * k + 1 : ℕ → ℤ) (Finset.range n) := by
              exact fun x hx => by rcases Int.odd_iff.mpr ( show x % 2 = 1 from Int.emod_two_ne_zero.mp fun con => by simp_all +decide [ Int.even_iff ] ) with ⟨ k, rfl ⟩ ; exact Finset.mem_image.mpr ⟨ Int.toNat k, Finset.mem_range.mpr <| by linarith [ Int.toNat_of_nonneg <| show 0 ≤ k from by linarith [ Finset.mem_Icc.mp <| hA <| Finset.mem_filter.mp hx |>.1 ], Finset.mem_Icc.mp <| hA <| Finset.mem_filter.mp hx |>.1 ], by linarith [ Int.toNat_of_nonneg <| show 0 ≤ k from by linarith [ Finset.mem_Icc.mp <| hA <| Finset.mem_filter.mp hx |>.1 ] ] ⟩ ;
            exact le_trans ( Finset.card_le_card h_odd_subset ) ( Finset.card_image_le.trans ( by simp ) );
          rw [ show # ( filter Even A ) = #A - # ( filter ( fun x => ¬Even x ) A ) by rw [ tsub_eq_of_eq_add ] ; rw [ ← Finset.card_union_of_disjoint ( Finset.disjoint_filter.mpr <| by aesop ) ] ; congr ; ext x ; by_cases hx : Even x <;> aesop ] ; omega;
        exact ⟨ ( Finset.filter Even A |> Finset.card ) - 2270, by omega, by omega ⟩;
      -- Step 2: Show ∃ even element 2m ∈ A₀ with 4t+3 ≤ m ≤ n-4t-3.
      obtain ⟨m, hm⟩ : ∃ m : ℤ, (2 * m) ∈ A.filter Even ∧ 4 * t + 3 ≤ m ∧ m ≤ n - 4 * t - 3 := by
        have h_even_count : (Finset.filter (fun x => x ∈ A.filter Even) (Finset.Icc 1 (8 * t + 4))).card ≤ 4 * t + 2 := by
          refine' le_trans ( Finset.card_le_card _ ) _;
          exact Finset.image ( fun x : ℕ => 2 * x : ℕ → ℤ ) ( Finset.Icc 1 ( 4 * t + 2 ) );
          · simp +decide [ Finset.subset_iff ];
            exact fun x hx₁ hx₂ hx₃ hx₄ => by obtain ⟨ k, rfl ⟩ := hx₄; exact ⟨ k.natAbs, ⟨ by omega, by omega ⟩, by omega ⟩ ;
          · exact Finset.card_image_le.trans ( by norm_num )
        have h_even_count' : (Finset.filter (fun x => x ∈ A.filter Even) (Finset.Icc (2 * n - 8 * t - 4) (2 * n))).card ≤ 4 * t + 3 := by
          have h_even_count' : (Finset.filter (fun x => x ∈ A.filter Even) (Finset.Icc (2 * n - 8 * t - 4) (2 * n))).card ≤ Finset.card (Finset.image (fun x => x / 2) (Finset.filter (fun x => x ∈ A.filter Even) (Finset.Icc (2 * n - 8 * t - 4) (2 * n)))) := by
            rw [ Finset.card_image_of_injOn ];
            exact fun x hx y hy hxy => by linarith [ Int.ediv_mul_cancel ( show 2 ∣ x from even_iff_two_dvd.mp ( by aesop ) ), Int.ediv_mul_cancel ( show 2 ∣ y from even_iff_two_dvd.mp ( by aesop ) ) ] ;
          refine le_trans h_even_count' ?_;
          refine' le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr _ ) _;
          exact Finset.Icc ( n - 4 * t - 2 ) n;
          · simp +zetaDelta at *;
            exact fun x hx₁ hx₂ hx₃ hx₄ => ⟨ by linarith [ Int.ediv_mul_cancel ( even_iff_two_dvd.mp hx₄ ) ], by linarith [ Int.ediv_mul_cancel ( even_iff_two_dvd.mp hx₄ ) ] ⟩;
          · norm_num [ Int.card_Icc ] ; omega
        have h_even_count'' : (Finset.filter (fun x => x ∈ A.filter Even) (Finset.Icc (8 * t + 6) (2 * n - 8 * t - 6))).card > 0 := by
          have h_even_count'' : (Finset.filter (fun x => x ∈ A.filter Even) (Finset.Icc 1 (2 * n))).card = (Finset.filter (fun x => x ∈ A.filter Even) (Finset.Icc 1 (8 * t + 4))).card + (Finset.filter (fun x => x ∈ A.filter Even) (Finset.Icc (8 * t + 6) (2 * n - 8 * t - 6))).card + (Finset.filter (fun x => x ∈ A.filter Even) (Finset.Icc (2 * n - 8 * t - 4) (2 * n))).card := by
            rw [ ← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint ];
            · congr with x;
              grind;
            · norm_num [ Finset.disjoint_left ];
              grind;
            · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_Icc.mp ( Finset.mem_filter.mp hx₂ |>.1 ) ] ;
          linarith [ show Finset.card ( Finset.filter ( fun x => x ∈ Finset.filter Even A ) ( Finset.Icc 1 ( 2 * n ) ) ) = Finset.card ( Finset.filter Even A ) from by rw [ Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr <| Finset.filter_subset _ _ |> Finset.Subset.trans <| hA ] ];
        obtain ⟨ x, hx ⟩ := Finset.card_pos.mp h_even_count''; use x / 2; simp_all +decide [parity_simps] ;
        grind;
      apply has_pps_central_even;
      any_goals tauto;
      · aesop;
      · grind;
      · have h_missing_odds : ((Finset.Icc (1 : ℤ) (2 * ↑n)).filter (fun x => ¬ Even x) \ A).card ≤ n - ((A.filter (fun x => ¬ Even x)).card) := by
          rw [ Finset.card_sdiff ];
          rw [ Finset.inter_filter ];
          rw [ Finset.inter_eq_left.mpr hA ];
          rw [ show ( Finset.filter ( fun x => ¬Even x ) ( Finset.Icc 1 ( 2 * n : ℤ ) ) ) = Finset.image ( fun x : ℕ => 2 * x + 1 : ℕ → ℤ ) ( Finset.range n ) from ?_, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
          ext;
          simp +zetaDelta at *;
          exact ⟨ fun h => by obtain ⟨ k, rfl ⟩ := h.2; exact ⟨ Int.toNat k, by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k ) ], by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k ) ] ⟩, by rintro ⟨ k, hk, rfl ⟩ ; exact ⟨ ⟨ by linarith, by linarith ⟩, by simp +decide [ parity_simps ] ⟩ ⟩;
        have h_odd_card : (A.filter (fun x => ¬ Even x)).card + (A.filter Even).card = A.card := by
          rw [ add_comm, Finset.card_filter_add_card_filter_not ];
        omega

/-
Given S ⊆ A₀ ⊆ A with S not weak Sidon, each x ∈ S has x+d ∈ A₀,
    and no two elements of S differ by d, construct HasPosPairwiseSums A 4.
-/
lemma has_pps_from_shifted_non_sidon
    (A A₀ : Finset ℤ) (hA₀ : A₀ ⊆ A)
    (S : Finset ℤ) (hS : S ⊆ A₀) (d : ℤ) (hd : 0 < d)
    (hSd : ∀ x ∈ S, x + d ∈ A₀)
    (hS_shift : ∀ x ∈ S, x + d ∉ S)
    (heven : ∀ a ∈ S, Even a) (hpos : ∀ a ∈ S, 0 < a)
    (h_not_ws : ¬ IsWeakSidonSet S) :
    HasPosPairwiseSums A 4 := by
      -- Since S is not weak Sidon, there exist a₁, a₂, a₃, a₄ ∈ S, all pairwise distinct, with a₁ + a₂ = a₃ + a₄.
      obtain ⟨a₁, a₂, a₃, a₄, ha₁, ha₂, ha₃, ha₄, habcd⟩ : ∃ a₁ a₂ a₃ a₄, a₁ ∈ S ∧ a₂ ∈ S ∧ a₃ ∈ S ∧ a₄ ∈ S ∧ a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₁ ≠ a₄ ∧ a₂ ≠ a₃ ∧ a₂ ≠ a₄ ∧ a₃ ≠ a₄ ∧ a₁ + a₂ = a₃ + a₄ := by
        contrapose! h_not_ws; unfold IsWeakSidonSet at *; aesop;
      -- WLOG a₁ < a₃ ≤ a₄ < a₂ (reorder so that a₁ is smallest and a₂ is largest among the equal-sum pair).
      wlog h_order : a₁ < a₃ ∧ a₃ < a₄ ∧ a₄ < a₂ generalizing a₁ a₂ a₃ a₄;
      · by_cases h_cases : a₁ < a₃ ∧ a₃ < a₄ ∧ a₄ < a₂ ∨ a₁ < a₄ ∧ a₄ < a₃ ∧ a₃ < a₂ ∨ a₂ < a₃ ∧ a₃ < a₄ ∧ a₄ < a₁ ∨ a₂ < a₄ ∧ a₄ < a₃ ∧ a₃ < a₁;
        · grind +ring;
        · grind +locals;
      · apply has_pps_four_of_equal_sums_and_shift;
        any_goals tauto;
        · grind;
        · grind

/-
Contrapositive of the intermediate bound from weak_sidon_bound:
    if |A| ≥ 16 and N * (u+3) < |A| * u * (|A| - u - 3) + |A| (u = Nat.sqrt |A|),
    then A is not a weak Sidon set.
-/
lemma not_weak_sidon_of_card_large (A : Finset ℤ) (N : ℕ)
    (hAN : ∀ a ∈ A, 1 ≤ a ∧ a ≤ ↑N)
    (h16 : 16 ≤ A.card)
    (hN : N * (Nat.sqrt A.card + 10) <
        A.card * (Nat.sqrt A.card + 7) * (A.card - Nat.sqrt A.card - 10) + A.card) :
    ¬ IsWeakSidonSet A := by
      intro hA
      have h_ineq : A.card ^ 2 * (A.card * (Nat.sqrt A.card + 7) + 1) ≤ (N + A.card * (Nat.sqrt A.card + 7)) * (3 * A.card + A.card * (Nat.sqrt A.card + 7)) := by
        apply weak_sidon_key_ineq A N (A.card * (Nat.sqrt A.card + 7) + 1) hA hAN (by positivity)
      have h_div : A.card * (Nat.sqrt A.card + 7) * (A.card - Nat.sqrt A.card - 10) + A.card ≤ N * (Nat.sqrt A.card + 10) := by
        rw [ Nat.sub_sub, mul_tsub ]
        nlinarith [ Nat.sub_add_cancel ( show #A * (Nat.sqrt #A + 7) * #A ≥ #A * (Nat.sqrt #A + 7) * ( Nat.sqrt #A + 10 ) from Nat.mul_le_mul_left _ <| by nlinarith only [ Nat.sqrt_le #A, h16 ] ) ]
      linarith

/-! ### Ceslemgeneral k=4 chain: concentrated even elements → HasPosPairwiseSums -/

lemma not_weak_sidon_of_even_range (S : Finset ℤ)
    (hne : S.Nonempty)
    (heven : ∀ a ∈ S, Even a)
    (h16 : 16 ≤ S.card)
    (hR : ((S.sup' hne id - S.inf' hne id) / 2 + 1) * (↑(Nat.sqrt S.card) + 10) <
        (↑S.card : ℤ) * (↑(Nat.sqrt S.card) + 7) * (↑S.card - ↑(Nat.sqrt S.card) - 10) + ↑S.card) :
    ¬ IsWeakSidonSet S := by
      -- Define the mapping from S to a set of positive integers.
      set T := S.image (fun x => (x - S.inf' hne id) / 2 + 1) with hT_def;
      have hT_nonempty : T.Nonempty := by
        exact ⟨ _, Finset.mem_image_of_mem _ hne.choose_spec ⟩
      have hT_card : T.card = S.card := by
        rw [ Finset.card_image_of_injOn ];
        intro x hx y hy; have := heven x hx; have := heven y hy; simp_all +decide [ parity_simps ] ;
        intro h; have := heven x hx; have := heven y hy; rw [ Int.even_iff ] at *; omega;
      have hT_pos : ∀ x ∈ T, 1 ≤ x := by
        simp +zetaDelta at *;
        exact fun x hx => Int.ediv_nonneg ( sub_nonneg.mpr <| Finset.inf'_le _ hx ) zero_le_two
      have hT_le : ∀ x ∈ T, x ≤ ((S.sup' hne id - S.inf' hne id) / 2 + 1) := by
        simp +zetaDelta at *;
        exact fun x hx => Int.ediv_le_ediv ( by norm_num ) ( by linarith [ Finset.le_sup' ( fun x => x ) hx ] )
      have hT_not_weak_sidon : ¬IsWeakSidonSet T := by
        convert not_weak_sidon_of_card_large T ( Int.toNat ( ( S.sup' hne id - S.inf' hne id ) / 2 + 1 ) ) _ _ _ using 1;
        · grind;
        · grind;
        · rw [ ← @Nat.cast_lt ℤ ] ; simp_all +decide [ mul_assoc ];
          rw [ Nat.sub_sub, Nat.cast_sub ] <;> norm_num;
          · rw [ max_eq_left ] <;> linarith [ Int.ediv_nonneg ( show 0 ≤ ( S.sup' hne fun x => x ) - S.inf' hne fun x => x from sub_nonneg.mpr <| Finset.inf'_le _ <| Finset.max'_mem _ hne ) zero_le_two ];
          · nlinarith only [ h16, Nat.sqrt_le ( Finset.card S ) ];
      contrapose! hT_not_weak_sidon;
      intro a ha b hb c hc d hd hab hbc hcd hca hdb hca'; obtain ⟨ x, hx, rfl ⟩ := Finset.mem_image.mp ha; obtain ⟨ y, hy, rfl ⟩ := Finset.mem_image.mp hb; obtain ⟨ z, hz, rfl ⟩ := Finset.mem_image.mp hc; obtain ⟨ w, hw, rfl ⟩ := Finset.mem_image.mp hd; simp_all +decide [ IsWeakSidonSet ] ;
      grind +suggestions

lemma ceslem_k4_chain (A A₁ : Finset ℤ)
    (hA₁_sub : A₁ ⊆ A)
    (heven : ∀ a ∈ A₁, Even a)
    (hpos : ∀ a ∈ A₁, 0 < a)
    (h2 : 2 ≤ A₁.card)
    (R : ℕ)
    (hR : ∀ a ∈ A₁, ∀ b ∈ A₁, |a - b| ≤ R)
    (hR_pos : 0 < R)
    (h_card_bound : A₁.card * (A₁.card - 1) ≥ 32 * R)
    (h_sidon : ∀ s : ℕ, A₁.card * (A₁.card - 1) ≤ 2 * R * s →
        16 ≤ s →
        ((R : ℤ) / 2 + 1) * (↑(Nat.sqrt s) + 10) <
        (↑s : ℤ) * (↑(Nat.sqrt s) + 7) * (↑s - ↑(Nat.sqrt s) - 10) + ↑s) :
    HasPosPairwiseSums A 4 := by
      -- Apply pigeonhole_differences_strong to get d with many pairs.
      obtain ⟨d, hd_pos, hd_even, hd_le_R, hd_card⟩ : ∃ d : ℤ, 0 < d ∧ Even d ∧ d ≤ R ∧ R * (A₁.filter (fun x => x + d ∈ A₁)).card ≥ A₁.card * (A₁.card - 1) := by
        apply pigeonhole_differences_strong A₁ h2 heven R hR hR_pos;
      -- Apply exists_shift_independent_subset to get S with |S| ≥ filter/2.
      obtain ⟨S, hS_sub, hS_card, hS_shift⟩ : ∃ S : Finset ℤ, S ⊆ A₁.filter (fun x => x + d ∈ A₁) ∧ 2 * S.card ≥ (A₁.filter (fun x => x + d ∈ A₁)).card ∧ ∀ x ∈ S, x + d ∉ S := by
        exact exists_shift_independent_subset _ _ hd_pos;
      -- Show |S| ≥ 16 from h_card_bound.
      have hS_card_ge_16 : 16 ≤ S.card := by
        nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ Finset.card A₁ ) ];
      apply has_pps_from_shifted_non_sidon A A₁ hA₁_sub S (by
      exact fun x hx => Finset.mem_filter.mp ( hS_sub hx ) |>.1) d hd_pos (by
      exact fun x hx => Finset.mem_filter.mp ( hS_sub hx ) |>.2) (by
      assumption) (by
      exact fun x hx => heven x <| Finset.mem_filter.mp ( hS_sub hx ) |>.1) (by
      exact fun x hx => hpos x <| Finset.mem_filter.mp ( hS_sub hx ) |>.1) (by
      apply not_weak_sidon_of_even_range S (by
      exact Finset.card_pos.mp ( pos_of_gt hS_card_ge_16 )) (by
      exact fun x hx => heven x <| Finset.mem_filter.mp ( hS_sub hx ) |>.1) hS_card_ge_16 (by
      all_goals generalize_proofs at *;
      refine' lt_of_le_of_lt _ ( h_sidon _ _ hS_card_ge_16 );
      · gcongr;
        refine' Int.ediv_le_ediv ( by norm_num ) _;
        have h_range_S : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ R := by
          exact fun x hx y hy => hR x ( Finset.mem_filter.mp ( hS_sub hx ) |>.1 ) y ( Finset.mem_filter.mp ( hS_sub hy ) |>.1 );
        have h_range_S : ∀ x ∈ S, ∀ y ∈ S, x - y ≤ R := by
          exact fun x hx y hy => le_of_abs_le <| h_range_S x hx y hy;
        exact h_range_S _ ( Finset.max'_mem _ ‹_› ) _ ( Finset.min'_mem _ ‹_› );
      · nlinarith))

private lemma numerical_ceslem_part1 (t : ℕ) (ht : 324 ≤ t)
    (s : ℕ) (hs : (t + 2269) * (t + 2269) ≤ (64 * t + 32) * s + 1) :
    16 ≤ s := by
  nlinarith

private lemma numerical_ceslem_part2_odd (t : ℕ)
    (s : ℕ) (hs : (t + 2270) * (t + 2270) ≤ (64 * t + 32) * s + 1) :
    (4 * (t : ℤ) + 3) * (↑(Nat.sqrt s) + 10) <
        (↑s : ℤ) * (↑(Nat.sqrt s) + 7) * (↑s - ↑(Nat.sqrt s) - 10) + ↑s := by
  by_cases h_sqrt : Nat.sqrt s ≥ 18
  · have ht_bound : t ≤ 64 * s := by nlinarith only [hs]
    nlinarith only [hs, ht_bound, h_sqrt, Nat.sqrt_le s, Nat.lt_succ_sqrt s,
        mul_le_mul_right h_sqrt s]
  · have h_s_bound : s ≤ 324 := by
      have hsqrt_lt : Nat.sqrt s < 18 := Nat.lt_of_not_ge h_sqrt
      have hsucc_le : (Nat.sqrt s).succ ≤ 18 := by omega
      have hs_lt : s < 18 * 18 :=
        lt_of_lt_of_le (Nat.lt_succ_sqrt s) (Nat.mul_le_mul hsucc_le hsucc_le)
      omega
    interval_cases s <;> norm_num at hs ⊢ <;> nlinarith

private lemma numerical_ceslem_part2_even (k : ℕ)
    (s : ℕ) (hs : (k + 1135) * (k + 1134) ≤ (32 * k + 8) * s) :
    (8 * (k : ℤ) + 3) * (↑(Nat.sqrt s) + 10) <
        (↑s : ℤ) * (↑(Nat.sqrt s) + 7) * (↑s - ↑(Nat.sqrt s) - 10) + ↑s := by
  by_cases h_sqrt : Nat.sqrt s ≥ 18
  · have ht_bound : k ≤ 32 * s := by nlinarith only [hs]
    nlinarith only [hs, ht_bound, h_sqrt, Nat.sqrt_le s, Nat.lt_succ_sqrt s,
        mul_le_mul_right h_sqrt s]
  · have h_s_bound : s ≤ 324 := by
      have hsqrt_lt : Nat.sqrt s < 18 := Nat.lt_of_not_ge h_sqrt
      have hsucc_le : (Nat.sqrt s).succ ≤ 18 := by omega
      have hs_lt : s < 18 * 18 :=
        lt_of_lt_of_le (Nat.lt_succ_sqrt s) (Nat.mul_le_mul hsucc_le hsucc_le)
      omega
    by_contra h_goal; push Not at h_goal
    zify at hs
    interval_cases s <;> norm_num at hs h_goal <;> first
      | done
      | nlinarith
      | (nlinarith [mul_nonneg (show (k : ℤ) - 3073 ≥ 0 from by clear hs; omega)
                              (show (k : ℤ) - 418 ≥ 0 from by clear hs; omega)])
      | (nlinarith [mul_nonneg (show (k : ℤ) - 3110 ≥ 0 from by clear hs; omega)
                              (show (k : ℤ) - 413 ≥ 0 from by clear hs; omega)])
      | (nlinarith [mul_nonneg (show (k : ℤ) - 3147 ≥ 0 from by clear hs; omega)
                              (show (k : ℤ) - 408 ≥ 0 from by clear hs; omega)])

lemma numerical_ceslem_bound_v2 (t : ℕ) (ht : 324 ≤ t)
    (s : ℕ) (hs : (t + 2269) * (t + 2269) ≤ (64 * t + 32) * s + 1)
    (hs_odd : ¬Even t → (t + 2270) * (t + 2270) ≤ (64 * t + 32) * s + 1) :
    16 ≤ s ∧
    ((4 * (t : ℤ) + 3) * (↑(Nat.sqrt s) + 10) <
        (↑s : ℤ) * (↑(Nat.sqrt s) + 7) * (↑s - ↑(Nat.sqrt s) - 10) + ↑s) := by
  refine ⟨numerical_ceslem_part1 t ht s hs, ?_⟩
  by_cases ht_parity : Even t
  · obtain ⟨k, rfl⟩ := ht_parity
    have h_rw : (4 * (↑(k + k) : ℤ) + 3) = 8 * (↑k : ℤ) + 3 := by push_cast; ring
    rw [h_rw]
    apply numerical_ceslem_part2_even k s
    nlinarith only [hs]
  · exact numerical_ceslem_part2_odd t s (hs_odd ht_parity)

/-
For n ≥ 4559 and B not weak Sidon, HasPosPairwiseSums A 4.
-/
lemma has_pps_large_n (A : Finset ℤ) (n : ℕ) (hn : 3404 ≤ n)
    (hA : A ⊆ Finset.Icc 1 (2 * ↑n))
    (hcard : n + 2270 ≤ A.card) :
    HasPosPairwiseSums A 4 := by
      by_cases h_even : (A.filter Even).card ≤ 2593;
      · exact has_pps_large_n_case1 A n hn hA hcard h_even;
      · set t := (A.filter Even).card - 2270;
        -- Step B: Split on central even element: ∃ m : ℤ, (2*m) ∈ A.filter Even ∧ 4*(t:ℤ)+3 ≤ m ∧ m+4*(t:ℤ)+3 ≤ n.
        by_cases h_central : ∃ m : ℤ, (2 * m) ∈ A.filter Even ∧ 4 * (t : ℤ) + 3 ≤ m ∧ m + 4 * (t : ℤ) + 3 ≤ n;
        · obtain ⟨ m, hm₁, hm₂, hm₃ ⟩ := h_central;
          apply has_pps_central_even A n t m hA;
          · exact Finset.mem_filter.mp hm₁ |>.1;
          · linarith;
          · linarith;
          · have h_odd_count : ((Finset.Icc (1 : ℤ) (2 * n)).filter (fun x => ¬ Even x) \ A).card = n - (A.filter (fun x => ¬ Even x)).card := by
              rw [ Finset.card_sdiff ];
              rw [ show { x ∈ Icc 1 ( 2 * n : ℤ ) | ¬Even x } = Finset.image ( fun k : ℕ => 2 * k + 1 : ℕ → ℤ ) ( Finset.range n ) from ?_, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
              · congr with x ; simp +decide [ parity_simps ];
                exact fun hx => ⟨ fun ⟨ a, ha, ha' ⟩ => ha'.symm ▸ ⟨ a, by ring ⟩, fun hx => by obtain ⟨ k, rfl ⟩ := hx; exact ⟨ Int.toNat k, by linarith [ Int.toNat_of_nonneg ( by linarith [ Finset.mem_Icc.mp ( hA hx ) ] : ( 0 : ℤ ) ≤ k ), Finset.mem_Icc.mp ( hA hx ) ], by linarith [ Int.toNat_of_nonneg ( by linarith [ Finset.mem_Icc.mp ( hA hx ) ] : ( 0 : ℤ ) ≤ k ) ] ⟩ ⟩;
              · -- To prove equality of finite sets, we show each set is a subset of the other.
                apply Finset.ext
                intro x
                simp [Finset.mem_image, Finset.mem_filter];
                exact ⟨ fun hx => by obtain ⟨ k, rfl ⟩ := hx.2; exact ⟨ Int.toNat k, by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k ) ], by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k ) ] ⟩, by rintro ⟨ k, hk₁, rfl ⟩ ; exact ⟨ ⟨ by linarith, by linarith ⟩, by simp +decide [ parity_simps ] ⟩ ⟩;
            have h_odd_count : (A.filter (fun x => ¬ Even x)).card + (A.filter Even).card = A.card := by
              rw [ add_comm, Finset.card_filter_add_card_filter_not ];
            omega;
        · -- Define A_left := (A.filter Even).filter (fun x => x ≤ 8*t+4) and A_right := (A.filter Even).filter (fun x => x ≥ 2*n-8*t-4).
          set A_left := (A.filter Even).filter (fun x => x ≤ 8 * (t : ℤ) + 4)
          set A_right := (A.filter Even).filter (fun x => x ≥ 2 * (n : ℤ) - 8 * (t : ℤ) - 4);
          -- Since every even element is either ≤ 8t+4 or ≥ 2n-8t-4, we have #A_left + #A_right ≥ #(A.filter Even) = t+2270.
          have h_card_left_right : A_left.card + A_right.card ≥ (A.filter Even).card := by
            rw [ ← Finset.card_union_add_card_inter ];
            rw [ show A_left ∪ A_right = filter Even A from ?_ ];
            · exact Nat.le_add_right _ _;
            · ext x;
              contrapose! h_central;
              use x / 2;
              grind;
          -- WLOG #A_left ≥ (t+2270+1)/2 or #A_right ≥ (t+2270+1)/2. Let A₁ be the bigger one.
          obtain ⟨A₁, hA₁⟩ : ∃ A₁ : Finset ℤ, A₁ ⊆ A.filter Even ∧ A₁.card ≥ (t + 2270 + 1) / 2 ∧ (∀ a ∈ A₁, Even a) ∧ (∀ a ∈ A₁, 0 < a) ∧ (∀ a b : ℤ, a ∈ A₁ → b ∈ A₁ → |a - b| ≤ 8 * (t : ℤ) + 4) := by
            by_cases h_left : A_left.card ≥ (t + 2270 + 1) / 2;
            · grind +qlia;
            · refine' ⟨ A_right, _, _, _, _, _ ⟩;
              · exact Finset.filter_subset _ _;
              · omega;
              · grind +splitImp;
              · exact fun x hx => by linarith [ Finset.mem_Icc.mp ( hA ( Finset.mem_filter.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1 ) ) ] ;
              · grind;
          apply ceslem_k4_chain A A₁;
          grind +extAll;
          any_goals exact 8 * t + 4;
          any_goals omega;
          · exact hA₁.2.2.1;
          · exact hA₁.2.2.2.1;
          · exact fun a ha b hb => mod_cast hA₁.2.2.2.2 a b ha hb;
          · have h_card_bound : A₁.card ≥ (t + 2270 + 1) / 2 := by
              lia;
            nlinarith only [ h_card_bound, Nat.div_add_mod ( t + 2270 + 1 ) 2, Nat.mod_lt ( t + 2270 + 1 ) two_pos, Nat.sub_add_cancel ( show 1 ≤ #A₁ from by linarith [ Nat.div_pos ( show t + 2270 + 1 ≥ 2 by linarith [ Nat.sub_add_cancel ( show 2270 ≤ # ( filter Even A ) from by linarith ) ] ) zero_lt_two ] ), Nat.sub_add_cancel ( show 2270 ≤ # ( filter Even A ) from by linarith ) ];
          · intros s hs hs';
            have h_card_A₁ : A₁.card ≥ (t + 2270 + 1) / 2 := by linarith;
            have h_card_A₁_sq : (A₁.card : ℤ) * (A₁.card - 1) ≥ ((t + 2270 + 1) / 2 : ℤ) * ((t + 2270 + 1) / 2 - 1) := by
              gcongr;
              · exact sub_nonneg_of_le ( by omega );
              · norm_cast;
              · norm_cast;
            have := numerical_ceslem_bound_v2 t (by omega) s (by
              zify at *;
              rw [ Nat.cast_sub ] at hs <;> push_cast at *;
              · nlinarith only [ hs, h_card_A₁_sq, Int.mul_ediv_add_emod ( ( t : ℤ ) + 2270 + 1 ) 2, Int.emod_nonneg ( ( t : ℤ ) + 2270 + 1 ) two_ne_zero, Int.emod_lt_of_pos ( ( t : ℤ ) + 2270 + 1 ) two_pos ];
              · omega ) (by
              intro ht_odd;
              have h_rem : ((t : ℤ) + 2270 + 1) % 2 = 0 := by
                have : (t : ℤ) % 2 = 1 := by exact_mod_cast (Nat.odd_iff.mp (Nat.not_even_iff_odd.mp ht_odd));
                omega;
              zify at *;
              rw [ Nat.cast_sub ] at hs <;> push_cast at *;
              · nlinarith only [ hs, h_card_A₁_sq, Int.mul_ediv_add_emod ( ( t : ℤ ) + 2270 + 1 ) 2, h_rem ];
              · omega );
            lia

lemma has_pps_not_weak_sidon (A : Finset ℤ) (n : ℕ) (hn : 2270 ≤ n)
    (hA : A ⊆ Finset.Icc 1 (2 * ↑n))
    (hcard : n + 2270 ≤ A.card) :
    HasPosPairwiseSums A 4 := by
  by_cases hn_small : n ≤ 3403
  · -- For n ≤ 3403, complement is small enough for consecutive window approach
    apply has_pps_of_small_compl A n (by omega)
    have h1 : (Finset.Icc (1 : ℤ) (2 * ↑n) \ A).card + A.card =
        (Finset.Icc (1 : ℤ) (2 * ↑n)).card := Finset.card_sdiff_add_card_eq_card hA
    simp [Int.card_Icc] at h1; omega
  · exact has_pps_large_n A n (by omega) hA hcard

/-- If A ⊆ [1,2n] has |A| ≥ n + 2270 then HasPosPairwiseSums A 4,
    regardless of whether the complement is weak Sidon. -/
lemma has_pps_of_large (A : Finset ℤ) (n : ℕ) (hn : 2270 ≤ n)
    (hA : A ⊆ Finset.Icc 1 (2 * ↑n))
    (hcard : n + 2270 ≤ A.card) :
    HasPosPairwiseSums A 4 := by
  by_cases hws : IsWeakSidonSet (Finset.Icc (1 : ℤ) (2 * ↑n) \ A)
  · exact has_pps_of_small_compl A n (by omega) (weak_sidon_compl_small A n hn hws)
  · exact has_pps_not_weak_sidon A n hn hA hcard

/-- Main theorem: h₄(n) ≤ 2270 for all positive n. -/
theorem h4upper (n : ℕ) (hn : 0 < n) : hFun 4 n ≤ 2270 := by
  unfold hFun
  apply Nat.sInf_le
  intro A hA hcard
  by_cases hn_small : n ≤ 2269
  · exfalso
    have : A.card ≤ (Finset.Icc (1 : ℤ) (2 * ↑n)).card := Finset.card_le_card hA
    simp [Int.card_Icc] at this; omega
  · push Not at hn_small
    exact has_pps_of_large A n (by omega) hA hcard

#print axioms h4upper
-- 'Erdos866b.h4upper' depends on axioms: [propext, Classical.choice, Quot.sound]

/-! ## Theorem h5lower: h₅(n) > ⌊log₂ n⌋ -/

/-- The set A₅ for the h₅ lower bound: odd integers ∪ even powers of 2 in {1,...,2n} -/
noncomputable def A5set (n : ℕ) : Finset ℤ :=
  (Icc (1:ℤ) (2*↑n)).filter (fun x => x % 2 = 1) ∪
  (Finset.Icc 1 (Nat.log 2 (2*n))).image (fun k : ℕ => (2:ℤ)^k)

/-
A5set is a subset of {1,...,2n}
-/
lemma A5set_subset (n : ℕ) : A5set n ⊆ Icc (1:ℤ) (2*↑n) := by
  refine Finset.union_subset ( Finset.filter_subset _ _ ) ( Finset.image_subset_iff.mpr ?_ );
  exact fun x hx => Finset.mem_Icc.mpr ⟨ mod_cast Nat.one_le_pow _ _ ( by decide ), mod_cast Nat.pow_le_of_le_log ( by aesop ) ( by linarith [ Finset.mem_Icc.mp hx ] ) ⟩

/-
The cardinality of A5set is ≥ n + Nat.log 2 n + 1 for n ≥ 1.
-/
lemma h5lower_card (n : ℕ) (hn : 1 ≤ n) : n + Nat.log 2 n + 1 ≤ (A5set n).card := by
  rw [ show A5set n = ( Finset.Icc 1 ( 2 * n : ℤ ) |> Finset.filter ( fun x ↦ x % 2 = 1 ) ) ∪ ( Finset.image ( fun k : ℕ ↦ 2 ^ k : ℕ → ℤ ) ( Finset.Icc 1 ( Nat.log 2 ( 2 * n ) ) ) ) from rfl, Finset.card_union_of_disjoint ];
  · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
    refine' add_lt_add_of_le_of_lt _ _;
    · rw [ Finset.card_eq_of_bijective ];
      use fun i hi => 2 * i + 1;
      · simp +zetaDelta at *;
        exact fun a ha₁ ha₂ ha₃ => ⟨ Int.toNat ( a / 2 ), by linarith [ Int.emod_add_mul_ediv a 2, Int.toNat_of_nonneg ( Int.ediv_nonneg ( by linarith : 0 ≤ a ) zero_le_two ) ], by linarith [ Int.emod_add_mul_ediv a 2, Int.toNat_of_nonneg ( Int.ediv_nonneg ( by linarith : 0 ≤ a ) zero_le_two ) ] ⟩;
      · grind;
      · aesop;
    · refine' Nat.le_log_of_pow_le ( by decide ) _;
      rw [ pow_succ' ] ; linarith [ Nat.pow_log_le_self 2 ( by linarith : n ≠ 0 ) ];
  · rw [ Finset.disjoint_right ] ; aesop

/-
A5set has no 5 distinct positive integers with all pairwise sums in it.
-/
lemma h5lower_no_pos_pairwise (n : ℕ) : ¬HasPosPairwiseSums (A5set n) 5 := by
  intros h;
  -- Among the 5 numbers, there are at least 3 with the same parity.
  obtain ⟨b, hb_ne, hb_parity⟩ : ∃ b : Fin 5 → ℤ, StrictMono b ∧ (∀ i, 0 < b i) ∧ (∀ i j : Fin 5, i < j → b i + b j ∈ (A5set n : Set ℤ)) ∧ (∃ i j k : Fin 5, i < j ∧ j < k ∧ (b i) % 2 = (b j) % 2 ∧ (b j) % 2 = (b k) % 2) := by
    obtain ⟨b, hb⟩ : ∃ b : Fin 5 → ℤ, StrictMono b ∧ (∀ i, 0 < b i) ∧ (∀ i j : Fin 5, i < j → b i + b j ∈ (A5set n : Set ℤ)) := by
      obtain ⟨ b, hb₁, hb₂ ⟩ := h;
      -- Since $b$ is injective, we can order its values.
      obtain ⟨σ, hσ⟩ : ∃ σ : Fin 5 ≃ Fin 5, StrictMono (fun i => b (σ i)) := by
        have h_order : ∃ (c : Fin 5 → ℤ), StrictMono c ∧ ∀ i, c i ∈ Set.range b := by
          exact ⟨ fun i => Finset.orderEmbOfFin ( Finset.image b Finset.univ ) ( by simp [ Finset.card_image_of_injective _ hb₁ ] ) i, by simp +decide [ StrictMono ], fun i => Finset.mem_image.mp ( Finset.orderEmbOfFin_mem ( Finset.image b Finset.univ ) ( by simp [ Finset.card_image_of_injective _ hb₁ ] ) i ) |> Exists.imp fun x hx => hx.2 ⟩;
        obtain ⟨ c, hc₁, hc₂ ⟩ := h_order;
        choose f hf using hc₂;
        have h_inj : Function.Injective f := by
          exact fun i j hij => hc₁.injective <| by have := hf i; aesop;
        exact ⟨ Equiv.ofBijective f ⟨ h_inj, Finite.injective_iff_surjective.mp h_inj ⟩, by simpa [ hf ] using hc₁ ⟩;
      use fun i => b (σ i);
      simp_all +decide [ StrictMono ];
      exact fun i j hij => if hij' : σ i < σ j then hb₂.2 _ _ hij' else by rw [ add_comm ] ; exact hb₂.2 _ _ ( lt_of_le_of_ne ( le_of_not_gt hij' ) ( Ne.symm <| by intro t; have := hσ hij; aesop ) ) ;
    refine' ⟨ b, hb.1, hb.2.1, hb.2.2, _ ⟩;
    by_contra! h;
    have := h 0 1 2 ( by decide ) ( by decide ) ; have := h 0 1 3 ( by decide ) ( by decide ) ; have := h 0 1 4 ( by decide ) ( by decide ) ; have := h 0 2 3 ( by decide ) ( by decide ) ; have := h 0 2 4 ( by decide ) ( by decide ) ; have := h 0 3 4 ( by decide ) ( by decide ) ; have := h 1 2 3 ( by decide ) ( by decide ) ; have := h 1 2 4 ( by decide ) ( by decide ) ; have := h 1 3 4 ( by decide ) ( by decide ) ; have := h 2 3 4 ( by decide ) ( by decide ) ;
    grind;
  -- Since $b_i + b_j$ is in $A5set$, it must be a power of 2.
  obtain ⟨i, j, k, hij, hjk, h_parity⟩ := hb_parity.right.right
  have h_power_of_two : ∃ p q r : ℕ, b i + b j = 2 ^ p ∧ b i + b k = 2 ^ q ∧ b j + b k = 2 ^ r := by
    have h_power_of_two : ∀ x ∈ (A5set n : Set ℤ), x % 2 = 0 → ∃ p : ℕ, x = 2 ^ p := by
      unfold A5set;
      aesop;
    simp +zetaDelta at *;
    exact ⟨ h_power_of_two _ ( hb_parity.2.1 _ _ hij ) ( Int.dvd_of_emod_eq_zero ( by omega ) ), h_power_of_two _ ( hb_parity.2.1 _ _ ( hij.trans hjk ) ) ( Int.dvd_of_emod_eq_zero ( by omega ) ), h_power_of_two _ ( hb_parity.2.1 _ _ hjk ) ( Int.dvd_of_emod_eq_zero ( by omega ) ) ⟩;
  obtain ⟨ p, q, r, hp, hq, hr ⟩ := h_power_of_two;
  -- Since $p < q < r$, we have $2^r \geq 2^{q+1}$.
  have h_exp : 2 ^ r ≥ 2 ^ (q + 1) := by
    exact pow_le_pow_right₀ ( by decide ) ( Nat.succ_le_of_lt ( Nat.lt_of_not_ge fun h => by linarith [ hb_ne hij, hb_ne hjk, pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) h ] ) );
  ring_nf at *; linarith [ hb_parity.1 i, hb_parity.1 j, hb_parity.1 k, hb_ne hij, hb_ne hjk, pow_pos ( zero_lt_two' ℤ ) p, pow_pos ( zero_lt_two' ℤ ) q ] ;

/-- h₅(n) > ⌊log₂ n⌋ for all n ∈ ℕ. -/
theorem h5lower (n : ℕ) : Nat.log 2 n < hFun 5 n := by
  unfold hFun
  have hne : ({m : ℕ | ∀ A ⊆ Icc (1:ℤ) (2*↑n), n + m ≤ A.card → HasPosPairwiseSums A 5} : Set ℕ).Nonempty := by
    exact ⟨2*n+1, fun A hA hcard => by
      exfalso; have := card_le_card hA
      have : (Icc (1:ℤ) (2*↑n)).card = 2*n := by rw [Int.card_Icc]; omega
      omega⟩
  apply Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
  apply le_csInf hne
  intro m hm
  by_contra h
  push Not at h
  have hAsub := A5set_subset n
  have hAcard : n + m ≤ (A5set n).card := by
    by_cases hn1 : n = 0
    · subst hn1
      have hm0 : m = 0 := by
        have : Nat.log 2 0 = 0 := by decide
        omega
      subst hm0; exact Nat.zero_le _
    · have := h5lower_card n (by omega); omega
  exact h5lower_no_pos_pairwise n (hm _ hAsub hAcard)

/-! ## Theorem g5lower: g₅(n) ≥ 4 for n ≥ 3 -/

/-
The counterexample set for g₅ lower bound: odd integers ∪ {2n-4, 2n-2, 2n}.
-/
lemma g5lower_counterexample (n : ℕ) (hn : 3 ≤ n) :
    ∃ A : Finset ℤ, A ⊆ Icc (1 : ℤ) (2 * ↑n) ∧ n + 3 ≤ A.card ∧ ¬HasPairwiseSums A 5 := by
      constructor;
      -- Show that the chosen set is a subset of {1,...,2n}.
      have h_subset : (Finset.filter (fun x : ℤ => x % 2 = 1 ∨ x = 2 * n - 4 ∨ x = 2 * n - 2 ∨ x = 2 * n) (Finset.Icc 1 (2 * n))) ⊆ Finset.Icc 1 (2 * n) := by
        exact Finset.filter_subset _ _;
      refine ⟨ h_subset, ?_, fun ⟨ b, hb ⟩ => ?_ ⟩;
      · rw [ show ( Finset.filter ( fun x : ℤ => x % 2 = 1 ∨ x = 2 * ↑n - 4 ∨ x = 2 * ↑n - 2 ∨ x = 2 * ↑n ) ( Finset.Icc 1 ( 2 * ↑n ) ) ) = Finset.image ( fun x : ℕ => 2 * x + 1 : ℕ → ℤ ) ( Finset.range n ) ∪ { ( 2 * n - 4 : ℤ ), ( 2 * n - 2 : ℤ ), ( 2 * n : ℤ ) } from ?_ ];
        · rw [ Finset.card_union_of_disjoint ] <;> norm_num [ Finset.card_image_of_injective, Function.Injective ];
          exact ⟨ fun x hx => by omega, fun x hx => by omega, fun x hx => by omega ⟩;
        · ext;
          simp +zetaDelta at *;
          constructor;
          · rintro ⟨ ⟨ h₁, h₂ ⟩, h₃ | h₃ | h₃ | h₃ ⟩ <;> first | exact Or.inl h₃ | exact Or.inr <| Or.inl h₃ | exact Or.inr <| Or.inr <| Or.inl h₃ | exact Or.inr <| Or.inr <| Or.inr <| ⟨ Int.toNat ( ( ‹_› - 1 ) / 2 ), by omega, by omega ⟩ ;
          · rintro ( rfl | rfl | rfl | ⟨ a, ha, rfl ⟩ ) <;> omega;
      · -- By contradiction, assume there exist 5 distinct integers $b_1, b_2, b_3, b_4, b_5$ such that their pairwise sums are all in $A$.
        obtain ⟨hb_inj, hb_sum⟩ := hb;
        -- Since $b$ is injective and consists of distinct integers, we can order them as $b_0 < b_1 < b_2 < b_3 < b_4$.
        obtain ⟨b_sorted, hb_sorted⟩ : ∃ b_sorted : Fin 5 → ℤ, StrictMono b_sorted ∧ ∀ i, b_sorted i ∈ Finset.image b Finset.univ := by
          have h_order : ∃ b_sorted : Finset ℤ, b_sorted.card = 5 ∧ ∀ x ∈ b_sorted, x ∈ Finset.image b Finset.univ := by
            exact ⟨ Finset.image b Finset.univ, by rw [ Finset.card_image_of_injective _ hb_inj ] ; decide, fun x hx => by aesop ⟩;
          obtain ⟨ b_sorted, hb_sorted₁, hb_sorted₂ ⟩ := h_order; exact ⟨ fun i => b_sorted.orderEmbOfFin ( by aesop ) i, by aesop_cat, fun i => hb_sorted₂ _ <| by aesop ⟩ ;
        -- Since $b_sorted$ is strictly monotone, we have $b_sorted i + b_sorted j \in A$ for all $i < j$.
        have hb_sorted_sum : ∀ i j : Fin 5, i < j → b_sorted i + b_sorted j ∈ Finset.filter (fun x : ℤ => x % 2 = 1 ∨ x = 2 * n - 4 ∨ x = 2 * n - 2 ∨ x = 2 * n) (Finset.Icc 1 (2 * n)) := by
          simp +zetaDelta at *;
          intro i j hij; obtain ⟨ a, ha ⟩ := hb_sorted.2 i; obtain ⟨ b, hb ⟩ := hb_sorted.2 j; simp_all +decide ;
          by_cases hab : a < b;
          · simpa only [ ← ha, ← hb ] using hb_sum a b hab;
          · have := hb_sum b a ( lt_of_le_of_ne ( le_of_not_gt hab ) ( Ne.symm <| by rintro rfl; exact hij.ne <| hb_sorted.1.injective <| by aesop ) ) ; simp_all +decide [ add_comm ] ;
        have := hb_sorted_sum 0 1 ( by decide ) ; have := hb_sorted_sum 1 2 ( by decide ) ; have := hb_sorted_sum 2 3 ( by decide ) ; have := hb_sorted_sum 3 4 ( by decide ) ; have := hb_sorted_sum 0 2 ( by decide ) ; have := hb_sorted_sum 0 3 ( by decide ) ; have := hb_sorted_sum 0 4 ( by decide ) ; have := hb_sorted_sum 1 3 ( by decide ) ; have := hb_sorted_sum 1 4 ( by decide ) ; have := hb_sorted_sum 2 4 ( by decide ) ; norm_num at * ;
        have := hb_sorted.1 ( show 0 < 1 from by decide ) ; have := hb_sorted.1 ( show 1 < 2 from by decide ) ; have := hb_sorted.1 ( show 2 < 3 from by decide ) ; have := hb_sorted.1 ( show 3 < 4 from by decide ) ; norm_num at * ; omega;

/-- g₅(n) ≥ 4 for all n ≥ 3. -/
theorem g5lower (n : ℕ) (hn : 3 ≤ n) : 4 ≤ gFun 5 n := by
  unfold gFun
  apply le_csInf
  · exact ⟨2 * n + 1, fun A hA hcard => by
      exfalso; have := card_le_card hA
      have : (Icc (1:ℤ) (2 * ↑n)).card = 2 * n := by
        rw [Int.card_Icc]; omega
      omega⟩
  · intro m hm
    by_contra h
    push Not at h
    obtain ⟨A, hAsub, hAcard, hAneg⟩ := g5lower_counterexample n hn
    exact hAneg (hm A hAsub (by omega))

/-! ## Theorem g5special -/

/-
If A contains all odd integers in {1,...,2n} and |A| ≥ n+4,
    then A has 5 distinct integers with pairwise sums in A.
-/
theorem g5special (n : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n))
    (hodd : ∀ x : ℤ, x ∈ Icc (1 : ℤ) (2 * ↑n) → x % 2 = 1 → x ∈ A)
    (hcard : n + 4 ≤ A.card) :
    HasPairwiseSums A 5 := by
      obtain ⟨a₁, a₂, a₃, a₄, ha₁, ha₂, ha₃, ha₄, ha₁a₂, ha₂a₃, ha₃a₄⟩ : ∃ a₁ a₂ a₃ a₄ : ℤ, a₁ ∈ A ∧ a₂ ∈ A ∧ a₃ ∈ A ∧ a₄ ∈ A ∧ a₁ % 2 = 0 ∧ a₂ % 2 = 0 ∧ a₃ % 2 = 0 ∧ a₄ % 2 = 0 ∧ a₁ < a₂ ∧ a₂ < a₃ ∧ a₃ < a₄ := by
        have h_even_count : (A.filter (fun x => x % 2 = 0)).card ≥ 4 := by
          have h_odd_count : (A.filter (fun x => x % 2 = 1)).card = n := by
            rw [ show { x ∈ A | x % 2 = 1 } = Finset.image ( fun x : ℕ => 2 * x + 1 : ℕ → ℤ ) ( Finset.range n ) from ?_, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
            ext x; simp;
            exact ⟨ fun hx => ⟨ Int.toNat ( x / 2 ), by linarith [ Int.emod_add_mul_ediv x 2, Int.toNat_of_nonneg ( Int.ediv_nonneg ( show 0 ≤ x by linarith [ Finset.mem_Icc.mp ( hA hx.1 ) ] ) zero_le_two ), Finset.mem_Icc.mp ( hA hx.1 ) ], by linarith [ Int.emod_add_mul_ediv x 2, Int.toNat_of_nonneg ( Int.ediv_nonneg ( show 0 ≤ x by linarith [ Finset.mem_Icc.mp ( hA hx.1 ) ] ) zero_le_two ) ] ⟩, by rintro ⟨ a, ha, rfl ⟩ ; exact ⟨ hodd _ ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ) ( by norm_num [ Int.add_emod ] ), by norm_num [ Int.add_emod ] ⟩ ⟩;
          have h_even_count : (A.filter (fun x => x % 2 = 0)).card + (A.filter (fun x => x % 2 = 1)).card = A.card := by
            rw [ Finset.card_filter, Finset.card_filter ];
            simpa only [ ← Finset.sum_add_distrib ] using Finset.card_eq_sum_ones A ▸ by congr; ext x; aesop;
          linarith;
        -- Since there are at least 4 even numbers in A, we can select 4 distinct even numbers from A.
        obtain ⟨s, hs⟩ : ∃ s : Fin 4 → ℤ, (∀ i, s i ∈ A ∧ s i % 2 = 0) ∧ StrictMono s := by
          obtain ⟨ s, hs ⟩ := Finset.exists_subset_card_eq h_even_count;
          exact ⟨ fun i => s.orderEmbOfFin ( by aesop ) i, fun i => ⟨ Finset.mem_filter.mp ( hs.1 <| by aesop ) |>.1, Finset.mem_filter.mp ( hs.1 <| by aesop ) |>.2 ⟩, by aesop_cat ⟩;
        exact ⟨ s 0, s 1, s 2, s 3, hs.1 0 |>.1, hs.1 1 |>.1, hs.1 2 |>.1, hs.1 3 |>.1, hs.1 0 |>.2, hs.1 1 |>.2, hs.1 2 |>.2, hs.1 3 |>.2, hs.2 ( by decide ), hs.2 ( by decide ), hs.2 ( by decide ) ⟩;
      -- Case 1: $a₂ + a₃ \leq 2n$.
      by_cases h_case1 : a₂ + a₃ ≤ 2 * n;
      · -- Define:
        set b₁ := (a₁ + a₂ - a₃) / 2
        set b₂ := (a₁ + a₃ - a₂) / 2
        set b₃ := (a₂ + a₃ - a₁) / 2
        set b₄ := 1 - b₁
        set b₅ := a₃ - b₄;
        -- We need to show that $b₁, b₂, b₃, b₄, b₅$ are distinct and their pairwise sums are in $A$.
        have h_distinct : b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₁ ≠ b₄ ∧ b₁ ≠ b₅ ∧ b₂ ≠ b₃ ∧ b₂ ≠ b₄ ∧ b₂ ≠ b₅ ∧ b₃ ≠ b₄ ∧ b₃ ≠ b₅ ∧ b₄ ≠ b₅ := by
          grind;
        have h_sums : ∀ i j : Fin 5, i < j → (if i = 0 then b₁ else if i = 1 then b₂ else if i = 2 then b₃ else if i = 3 then b₄ else b₅) + (if j = 0 then b₁ else if j = 1 then b₂ else if j = 2 then b₃ else if j = 3 then b₄ else b₅) ∈ A := by
          grind +locals;
        use ![b₁, b₂, b₃, b₄, b₅];
        simp_all +decide [ Function.Injective, Fin.forall_fin_succ ];
        grind;
      · -- Case 3: $a₂ + a₃ > 2n$ and $a₃ = 2n-2$.
        by_cases h_case3 : a₃ = 2 * n - 2;
        · -- Define $b₁, b₂, b₃, b₄, b₅$ as follows:
          set b₁ := (a₂ + a₃ - a₄) / 2
          set b₂ := (a₂ + a₄ - a₃) / 2
          set b₃ := (a₃ + a₄ - a₂) / 2
          set b₄ := a₁ + b₃ - (2 * n - 1)
          set b₅ := (2 * n - 1) - b₃;
          -- We need to verify that the pairwise sums of $b₁, b₂, b₃, b₄, b₅$ are in $A$.
          have hb_sums : ∀ i j : Fin 5, i < j → (if i = 0 then b₁ else if i = 1 then b₂ else if i = 2 then b₃ else if i = 3 then b₄ else b₅) + (if j = 0 then b₁ else if j = 1 then b₂ else if j = 2 then b₃ else if j = 3 then b₄ else b₅) ∈ A := by
            grind;
          have hb_distinct : b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₁ ≠ b₄ ∧ b₁ ≠ b₅ ∧ b₂ ≠ b₃ ∧ b₂ ≠ b₄ ∧ b₂ ≠ b₅ ∧ b₃ ≠ b₄ ∧ b₃ ≠ b₅ ∧ b₄ ≠ b₅ := by
            grind;
          use ![b₁, b₂, b₃, b₄, b₅];
          simp +decide [ Function.Injective, Fin.forall_fin_succ, * ];
          simp_all +decide [ Fin.forall_fin_succ, eq_comm ];
        · -- Case 2: $a₂ + a₃ > 2n$ and $a₃ < 2n-2$.
          use ![ (a₂ + a₃ - a₄) / 2, (a₂ + a₄ - a₃) / 2, (a₃ + a₄ - a₂) / 2, (a₂ + (a₃ + a₄ - a₂) / 2 - (2 * n - 1)), (2 * n - 1) - (a₃ + a₄ - a₂) / 2 ];
          constructor;
          · simp +decide [ Function.Injective, Fin.forall_fin_succ ];
            have := hA ha₂; have := hA ha₃; have := hA ha₄; norm_num at *; omega;
          · simp +decide [ Fin.forall_fin_succ ];
            refine' ⟨ _, _, _, ha₂ ⟩;
            · grind;
            · grind;
            · grind

/-! ## Sidon bound -/

section SidonBound

open Real

/-- A Sidon set (B₂ set) is a finite set of integers where all pairwise sums are distinct:
    a + b = c + d with a,b,c,d ∈ S implies {a,b} = {c,d} as multisets. -/
def IsSidonSet (S : Finset ℤ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The spread of a nonempty finite set of integers: max − min. -/
noncomputable def spreadZ (S : Finset ℤ) (hne : S.Nonempty) : ℤ :=
  S.max' hne - S.min' hne

lemma spreadZ_pos (S : Finset ℤ) (hcard : 2 ≤ S.card) :
    1 ≤ spreadZ S (Finset.card_pos.mp (by omega)) := by
  exact ( show 1 ≤ S.max' _ - S.min' _ from by obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.one_lt_card.mp hcard; cases lt_or_gt_of_ne hxy <;> linarith! [ Finset.min'_le _ _ hx, Finset.le_max' _ _ hx, Finset.min'_le _ _ hy, Finset.le_max' _ _ hy ] )

/-
Key intermediate counting bound: for a Sidon set with t elements and spread y,
    for any positive integer T, t² · T ≤ (y + T)(T + t − 1).
-/
lemma sidon_T_bound (S : Finset ℤ) (hS : IsSidonSet S) (T : ℕ) (hT : 1 ≤ T)
    (hcard : 2 ≤ S.card) :
    (S.card : ℤ) ^ 2 * T ≤
    (spreadZ S (Finset.card_pos.mp (by omega)) + T) * (T + S.card - 1) := by
  -- Let $y = \max(S) - \min(S)$ and WLOG assume $S.min' = 0$ (shift doesn't change the Sidon property or the spread). Let $y = \max(S)$.
  set y := spreadZ S (Finset.card_pos.mp (by omega))
  set S_shifted := S.image (fun x => x - Finset.min' S (Finset.card_pos.mp (by omega)));
  -- By the properties of the shifted set, we have $|S_shifted| = |S|$ and $S_shifted \subseteq \{0, 1, ..., y\}$.
  have hS_shifted_card : S_shifted.card = S.card := by
    exact Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy;
  have hS_shifted_subset : S_shifted ⊆ Finset.Icc 0 y := by
    exact Finset.image_subset_iff.mpr fun x hx => Finset.mem_Icc.mpr ⟨ sub_nonneg.mpr <| Finset.min'_le _ _ hx, sub_le_sub_right ( Finset.le_max' _ _ hx ) _ ⟩;
  -- Define for $j = 1,...,y+T$, the count $Y_j = |S \cap \{z | j-T \le z < j\}|$.
  set Y := fun j : ℤ => (S_shifted.filter (fun z => j - T ≤ z ∧ z < j)).card with hY_def;
  have hY_sum : ∑ j ∈ Finset.Icc 1 (y + T), Y j = S.card * T := by
    have hY_sum : ∑ j ∈ Finset.Icc 1 (y + T), Y j = ∑ z ∈ S_shifted, ∑ j ∈ Finset.Icc 1 (y + T), (if j - T ≤ z ∧ z < j then 1 else 0) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; aesop;
    -- For each $z \in S_shifted$, the inner sum $\sum_{j=1}^{y+T} \mathbf{1}_{j-T \leq z < j}$ counts the number of integers $j$ such that $j-T \leq z < j$, which is exactly $T$.
    have h_inner_sum : ∀ z ∈ S_shifted, ∑ j ∈ Finset.Icc 1 (y + T), (if j - T ≤ z ∧ z < j then 1 else 0) = T := by
      intros z hz
      have h_inner_sum_eq : Finset.filter (fun j => j - T ≤ z ∧ z < j) (Finset.Icc 1 (y + T)) = Finset.Icc (z + 1) (z + T) := by
        ext j; simp [ Finset.mem_Icc];
        exact ⟨ fun h => ⟨ h.2.2, h.2.1 ⟩, fun h => ⟨ ⟨ by linarith [ Finset.mem_Icc.mp ( hS_shifted_subset hz ) ], by linarith [ Finset.mem_Icc.mp ( hS_shifted_subset hz ) ] ⟩, h.2, h.1 ⟩ ⟩;
      simp_all +decide ;
    rw [ hY_sum, Finset.sum_congr rfl h_inner_sum, Finset.sum_const, hS_shifted_card, smul_eq_mul, mul_comm ];
  have hY_sum_sq : ∑ j ∈ Finset.Icc 1 (y + T), Y j ^ 2 ≤ S.card * T + T * (T - 1) := by
    -- By the properties of the Sidon set, we have $\sum_{j=1}^{y+T} \binom{Y_j}{2} \leq \sum_{d=1}^{T-1} (T-d)$.
    have hY_binom : ∑ j ∈ Finset.Icc 1 (y + T), Nat.choose (Y j) 2 ≤ ∑ d ∈ Finset.Icc 1 (T - 1), (T - d) := by
      -- For each unordered pair {a,b} ⊂ S_shifted with a < b and d = b-a ≤ T-1, they co-occur in T-d windows.
      have h_pair_count : ∀ a ∈ S_shifted, ∀ b ∈ S_shifted, a < b → b - a ≤ T - 1 → ∑ j ∈ Finset.Icc 1 (y + T), (if a ∈ Finset.filter (fun z => j - T ≤ z ∧ z < j) S_shifted ∧ b ∈ Finset.filter (fun z => j - T ≤ z ∧ z < j) S_shifted then 1 else 0) = T - (b - a) := by
        intros a ha b hb hab hba
        have h_window_count : Finset.filter (fun j : ℤ => a ∈ Finset.filter (fun z => j - T ≤ z ∧ z < j) S_shifted ∧ b ∈ Finset.filter (fun z => j - T ≤ z ∧ z < j) S_shifted) (Finset.Icc 1 (y + T)) = Finset.Icc (b + 1) (a + T) := by
          grind;
        simp_all +decide ;
        rw [ max_eq_left ] <;> linarith;
      -- By the properties of the Sidon set, we can count the number of pairs {a, b} with a < b and b - a ≤ T - 1.
      have h_pair_count : ∑ j ∈ Finset.Icc 1 (y + T), Nat.choose (Y j) 2 = ∑ a ∈ S_shifted, ∑ b ∈ S_shifted, if a < b ∧ b - a ≤ T - 1 then (T - (b - a)) else 0 := by
        have h_pair_count : ∀ j ∈ Finset.Icc 1 (y + T), Nat.choose (Y j) 2 = ∑ a ∈ S_shifted, ∑ b ∈ S_shifted, if a < b ∧ a ∈ Finset.filter (fun z => j - T ≤ z ∧ z < j) S_shifted ∧ b ∈ Finset.filter (fun z => j - T ≤ z ∧ z < j) S_shifted then 1 else 0 := by
          intros j hj
          have h_pair_count : Nat.choose (Y j) 2 = ∑ a ∈ Finset.filter (fun z => j - T ≤ z ∧ z < j) S_shifted, ∑ b ∈ Finset.filter (fun z => j - T ≤ z ∧ z < j) S_shifted, if a < b then 1 else 0 := by
            have h_pair_count : ∀ (s : Finset ℤ), Nat.choose s.card 2 = ∑ a ∈ s, ∑ b ∈ s, if a < b then 1 else 0 := by
              intros s
              induction s using Finset.induction
              · rfl;
              · rename_i a s ha ih
                simp_all +decide [ Finset.sum_insert ha, Nat.choose_succ_succ ];
                simp +decide [ Finset.sum_add_distrib];
                rw [ ← add_assoc, ← Finset.card_union_of_disjoint ];
                · congr with x ; aesop;
                · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
            exact h_pair_count _;
          simp_all +decide;
          rw [ Finset.sum_filter ];
          congr! 1;
          split_ifs <;> simp_all +decide [ Finset.filter_filter, and_comm, and_left_comm, and_assoc ];
          rw [ Finset.card_eq_zero.mpr ] ; aesop;
        push_cast [ Finset.sum_congr rfl h_pair_count ];
        rw [ Finset.sum_comm, Finset.sum_congr rfl ];
        intro a ha; rw [ Finset.sum_comm ] ; refine' Finset.sum_congr rfl fun b hb => _ ; by_cases hab : a < b <;> by_cases hba : b - a ≤ T - 1 <;> simp +decide [ hab, hba ] ;
        · convert ‹∀ a ∈ S_shifted, ∀ b ∈ S_shifted, a < b → b - a ≤ ↑T - 1 → ( ∑ j ∈ Icc 1 ( y + ↑T ), if a ∈ { z ∈ S_shifted | j - ↑T ≤ z ∧ z < j } ∧ b ∈ { z ∈ S_shifted | j - ↑T ≤ z ∧ z < j } then 1 else 0 ) = ↑T - ( b - a ) › a ha b hb hab hba using 1;
          simp +decide ;
        · intros; linarith;
      -- Since $S_shifted$ is a Sidon set, the differences $b - a$ are distinct for distinct pairs $(a, b)$.
      have h_diff_distinct : ∀ a ∈ S_shifted, ∀ b ∈ S_shifted, a < b → b - a ≤ T - 1 → ∀ c ∈ S_shifted, ∀ d ∈ S_shifted, c < d → d - c ≤ T - 1 → (b - a = d - c) → (a = c ∧ b = d) := by
        intros a ha b hb hab hba c hc d hd hcd hcd' h_eq
        have h_sidon : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, ∀ w ∈ S, x + y = z + w → (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
          exact hS;
        simp +zetaDelta at *;
        grind +revert;
      -- Since the differences $b - a$ are distinct for distinct pairs $(a, b)$, we can bound the sum by considering the maximum possible value of $T - (b - a)$ for each $d$.
      have h_diff_bound : ∑ a ∈ S_shifted, ∑ b ∈ S_shifted, (if a < b ∧ b - a ≤ T - 1 then (T - (b - a)) else 0) ≤ ∑ d ∈ Finset.Icc 1 (T - 1), (T - d) := by
        have h_diff_bound : ∑ a ∈ S_shifted, ∑ b ∈ S_shifted, (if a < b ∧ b - a ≤ T - 1 then (T - (b - a)) else 0) ≤ ∑ d ∈ Finset.image (fun p : ℤ × ℤ => p.2 - p.1) (Finset.filter (fun p : ℤ × ℤ => p.1 < p.2 ∧ p.2 - p.1 ≤ T - 1) (S_shifted ×ˢ S_shifted)), (T - d) := by
          rw [ Finset.sum_image ];
          · rw [ Finset.sum_image ];
            · rw [ Finset.sum_filter ];
              rw [ Finset.sum_product ];
              rw [ Finset.sum_image ];
              exact fun x hx y hy hxy => by simpa using hxy;
            · intros p hp q hq h_eq;
              specialize h_diff_distinct p.1 ( Finset.mem_product.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1 ) p.2 ( Finset.mem_product.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2 ) ( Finset.mem_filter.mp hp |>.2.1 ) ( Finset.mem_filter.mp hp |>.2.2 ) q.1 ( Finset.mem_product.mp ( Finset.mem_filter.mp hq |>.1 ) |>.1 ) q.2 ( Finset.mem_product.mp ( Finset.mem_filter.mp hq |>.1 ) |>.2 ) ( Finset.mem_filter.mp hq |>.2.1 ) ( Finset.mem_filter.mp hq |>.2.2 ) ; aesop;
          · exact fun x hx y hy hxy => by simpa using hxy;
        refine le_trans h_diff_bound ?_;
        refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg _ _ ) _;
        exact Finset.Icc 1 ( T - 1 );
        · grind;
        · exact fun _ _ _ => sub_nonneg_of_le <| by linarith [ Finset.mem_Icc.mp ‹_› ] ;
        · rcases T with ( _ | _ | T ) <;> norm_num at *;
          refine' le_of_eq _;
          refine' Finset.sum_bij ( fun x hx => Int.toNat x ) _ _ _ _ <;> norm_num;
          · exact fun a ha₁ ha₂ => ⟨ by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ a ) ], ha₂ ⟩;
          · exact fun a₁ ha₁ ha₂ a₂ ha₃ ha₄ h => by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ a₁ ), Int.toNat_of_nonneg ( by linarith : 0 ≤ a₂ ) ] ;
          · exact fun b hb₁ hb₂ => ⟨ b, ⟨ mod_cast hb₁, mod_cast hb₂ ⟩, rfl ⟩;
          · intro a ha₁ ha₂; rw [ Nat.cast_sub ] <;> norm_num ; linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ a ) ] ;
            linarith;
      exact_mod_cast h_pair_count.le.trans h_diff_bound;
    -- By the properties of binomial coefficients, we have $\sum_{j=1}^{y+T} \binom{Y_j}{2} = \frac{1}{2} \sum_{j=1}^{y+T} Y_j^2 - \frac{1}{2} \sum_{j=1}^{y+T} Y_j$.
    have hY_binom_eq : ∑ j ∈ Finset.Icc 1 (y + T), Nat.choose (Y j) 2 = (1 / 2 : ℚ) * (∑ j ∈ Finset.Icc 1 (y + T), Y j ^ 2) - (1 / 2 : ℚ) * (∑ j ∈ Finset.Icc 1 (y + T), Y j) := by
      push_cast [ Finset.mul_sum _ _ _, Finset.sum_mul ];
      rw [ ← Finset.sum_sub_distrib ] ; congr ; ext ; induction Y ‹_› <;> norm_num [ Nat.choose ] at * ; linarith;
    -- By the properties of the sum of the first $T-1$ natural numbers, we have $\sum_{d=1}^{T-1} (T-d) = \frac{T(T-1)}{2}$.
    have h_sum_nat : ∑ d ∈ Finset.Icc 1 (T - 1), (T - d) = T * (T - 1) / 2 := by
      erw [ Finset.sum_Ico_eq_sum_range ];
      convert Finset.sum_range_id T using 1 ; cases T <;> simp +arith +decide [add_comm,
        Finset.sum_range_succ'];
      rw [ ← Finset.sum_range_reflect ];
      exact Finset.sum_congr rfl fun x hx => by rw [ tsub_tsub, tsub_tsub_cancel_of_le ] <;> linarith [ Finset.mem_range.mp hx ] ;
    rw [ ← @Nat.cast_le ℚ ] at * ; norm_num at *;
    rw [ ← @Nat.cast_inj ℚ ] at * ; norm_num at *;
    rw [ Nat.cast_div ] at * <;> norm_num at *;
    · grind +revert;
    · exact even_iff_two_dvd.mp ( Nat.even_mul_pred_self _ );
  -- By Cauchy-Schwarz inequality, we have $(\sum_{j=1}^{y+T} Y_j)^2 \leq (y+T) \sum_{j=1}^{y+T} Y_j^2$.
  have h_cauchy_schwarz : (∑ j ∈ Finset.Icc 1 (y + T), Y j) ^ 2 ≤ (y + T) * ∑ j ∈ Finset.Icc 1 (y + T), Y j ^ 2 := by
    have h_cauchy_schwarz : ∀ (u v : Finset ℤ) (f g : ℤ → ℝ), (∑ j ∈ u, f j * g j) ^ 2 ≤ (∑ j ∈ u, f j ^ 2) * (∑ j ∈ u, g j ^ 2) := by
      exact fun u v f g => sum_mul_sq_le_sq_mul_sq u f g;
    convert h_cauchy_schwarz ( Finset.Icc 1 ( y + T ) ) ( Finset.Icc 1 ( y + T ) ) ( fun _ => 1 ) ( fun j => Y j ) using 1 ; norm_num;
    rw [ ← Int.toNat_of_nonneg ( by linarith [ show 0 ≤ y by exact sub_nonneg_of_le <| Finset.min'_le _ _ <| Finset.max'_mem _ <| Finset.card_pos.mp <| by linarith ] : 0 ≤ y + T ) ] ; norm_cast;
  rcases T with ( _ | T ) <;> simp_all +decide [ pow_succ' ];
  nlinarith [ show 0 ≤ y by exact sub_nonneg_of_le <| Finset.min'_le _ _ <| Finset.max'_mem _ <| Finset.card_pos.mp <| pos_of_gt hcard ]

/-
Algebraic identity: with u = √t and T = u³ - u² + ε (where ε ∈ (0,1]),
    t²·T ≥ (t²-2t√t+t+√t-1+T)(T+t-1), with difference = (1-ε)(u+ε-1) ≥ 0.
-/
lemma sidon_algebra_identity (t : ℕ) (ht : 2 ≤ t) (T : ℕ)
    (hε_le : (T : ℝ) ≤ ↑t * sqrt ↑t - ↑t + 1)
    (hε_ge : ↑t * sqrt ↑t - ↑t < (T : ℝ)) :
    ((t : ℝ) ^ 2 - 2 * ↑t * sqrt ↑t + ↑t + sqrt ↑t - 1 + ↑T) * (↑T + ↑t - 1) ≤
    (↑t) ^ 2 * ↑T := by
  -- Set $u := \sqrt{t}$ and $\epsilon := T - (u^3 - u^2)$.
  set u : ℝ := Real.sqrt t
  set ε : ℝ := T - (u^3 - u^2);
  -- We have $u \geq \sqrt{2}$ and $\epsilon \in (0, 1]$.
  have hu_ge_sqrt2 : u ≥ Real.sqrt 2 := by
    exact Real.sqrt_le_sqrt <| mod_cast ht
  have hε_pos : 0 < ε := by
    nlinarith [ Real.sqrt_nonneg t, Real.sq_sqrt ( Nat.cast_nonneg t ) ]
  have hε_le1 : ε ≤ 1 := by
    nlinarith [ Real.sqrt_nonneg t, Real.sq_sqrt ( Nat.cast_nonneg t ) ];
  -- Substitute $u$ and $\epsilon$ into the inequality.
  suffices h_ineq : (u^4 - u^3 + u - 1 + ε) * (u^3 + ε - 1) ≤ u^4 * (u^3 - u^2 + ε) by
    convert h_ineq using 1 <;> ring_nf;
    · grind;
    · grind;
  nlinarith [ show 1 ≤ u by exact Real.le_sqrt_of_sq_le ( by norm_cast; linarith ), show 0 ≤ ( Real.sqrt 2 : ℝ ) - 1 by nlinarith only [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ], Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, mul_le_mul_of_nonneg_left hε_le1 <| show 0 ≤ u by positivity, mul_le_mul_of_nonneg_left hε_pos.le <| show 0 ≤ u by positivity ]

/-
Key intermediate bound: a Sidon set with t elements and spread y satisfies
    y ≥ t² − 2t√t + t + √t − 1.
-/
lemma sidon_counting (S : Finset ℤ) (hS : IsSidonSet S) (hcard : 2 ≤ S.card) :
    (S.card : ℝ) ^ 2 - 2 * ↑S.card * sqrt ↑S.card + ↑S.card + sqrt ↑S.card - 1
    ≤ ↑(spreadZ S (Finset.card_pos.mp (by omega : 0 < S.card))) := by
  by_contra h_contra
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : ℕ, 1 ≤ T₀ ∧ (T₀ : ℝ) ≤ S.card * (Real.sqrt S.card) - S.card + 1 ∧ (S.card * (Real.sqrt S.card) - S.card) < (T₀ : ℝ) := by
    exact ⟨ ⌊ ( S.card : ℝ ) * Real.sqrt S.card - S.card⌋₊ + 1, by linarith, by push_cast; linarith [ Nat.floor_le ( show 0 ≤ ( S.card : ℝ ) * Real.sqrt S.card - S.card by exact sub_nonneg.mpr <| by exact le_mul_of_one_le_right ( by positivity ) <| Real.le_sqrt_of_sq_le <| mod_cast by linarith ) ], by push_cast; linarith [ Nat.lt_floor_add_one ( ( S.card : ℝ ) * Real.sqrt S.card - S.card ) ] ⟩;
  have hT₀_bound : ((S.card : ℝ) ^ 2 - 2 * S.card * Real.sqrt S.card + S.card + Real.sqrt S.card - 1 + T₀) * (T₀ + S.card - 1) ≤ (S.card : ℝ) ^ 2 * T₀ := by
    apply sidon_algebra_identity; assumption; exact_mod_cast hT₀.right.left; exact_mod_cast hT₀.right.right;
  have hT₀_bound_int : (S.card : ℤ) ^ 2 * T₀ ≤ (spreadZ S (Finset.card_pos.mp (by omega)) + T₀) * (T₀ + S.card - 1) := by
    convert sidon_T_bound S hS T₀ hT₀.1 hcard using 1;
  norm_num [ ← @Int.cast_le ℝ ] at * ; nlinarith [ ( by norm_cast : ( 2 : ℝ ) ≤ #S ) ] ;

/-
Monotonicity: f(t) = t² − 2t√t + t + √t is nondecreasing for t ≥ 0.
-/
lemma f_sidon_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a ^ 2 - 2 * a * sqrt a + a + sqrt a ≤
    b ^ 2 - 2 * b * sqrt b + b + sqrt b := by
  -- We'll use the fact that $u = \sqrt{a}$ and $v = \sqrt{b}$ satisfy $u \leq v$ (since $a \leq b$).
  set u := Real.sqrt a
  set v := Real.sqrt b
  have huv : u ≤ v := by
    exact Real.sqrt_le_sqrt hab;
  -- Substitute $a = u^2$ and $b = v^2$ into the inequality.
  have h_sub : (u^2)^2 - 2 * u^2 * u + u^2 + u ≤ (v^2)^2 - 2 * v^2 * v + v^2 + v := by
    -- Since $u \leq v$ and $u, v \geq 0$, we have $v^3 + v^2u + vu^2 + u^3 - 2v^2 - 2vu - 2u^2 + v + u + 1 \geq 0$.
    have h_nonneg : v^3 + v^2 * u + v * u^2 + u^3 - 2 * v^2 - 2 * v * u - 2 * u^2 + v + u + 1 ≥ 0 := by
      nlinarith [ sq_nonneg ( v - 1 ), sq_nonneg ( u - 1 ), sq_nonneg ( v - u ), Real.sqrt_nonneg a, Real.sqrt_nonneg b ];
    nlinarith [ Real.sqrt_nonneg a, Real.sqrt_nonneg b ];
  rwa [ Real.sq_sqrt ha, Real.sq_sqrt ( by linarith ) ] at h_sub

/-
Algebraic lemma: y < f(√y + y^{1/4} + 1/2) for y ≥ 1,
    where f(t) = t² − 2t√t + t + √t − 1.
-/
lemma algebra_sidon (y : ℝ) (hy : 1 ≤ y) :
    let s := sqrt y + sqrt (sqrt y) + 1/2
    y < s ^ 2 - 2 * s * sqrt s + s + sqrt s - 1 := by
  -- Set $u := y^{1/4}$, so $u \geq 1$ and $u^4 = y$.
  set u := Real.sqrt (Real.sqrt y)
  have hu : u ≥ 1 := by
    exact Real.le_sqrt_of_sq_le <| Real.le_sqrt_of_sq_le <| by linarith;
  have hu4 : u^4 = y := by
    nlinarith [ Real.mul_self_sqrt ( show 0 ≤ y by positivity ), Real.mul_self_sqrt ( show 0 ≤ √y by positivity ) ];
  -- We need $2u^3 + 3u^2 + 2u - 1/4 > 2u(u+1)\cdot\sqrt{s}$.
  have hineq : 2 * u^3 + 3 * u^2 + 2 * u - 1 / 4 > 2 * u * (u + 1) * Real.sqrt (u^2 + u + 1 / 2) := by
    -- Square both sides to remove the square root.
    suffices hsq : (2 * u^3 + 3 * u^2 + 2 * u - 1 / 4)^2 > 4 * u^2 * (u + 1)^2 * (u^2 + u + 1 / 2) by
      contrapose! hsq;
      convert pow_le_pow_left₀ ( by nlinarith ) hsq 2 using 1 ; nlinarith [ Real.mul_self_sqrt ( show 0 ≤ u ^ 2 + u + 1 / 2 by positivity ) ];
    nlinarith [ sq_nonneg ( u - 1 ), mul_le_mul_of_nonneg_left hu ( sq_nonneg ( u - 1 ) ) ];
  rw [ show ( Real.sqrt y : ℝ ) = u ^ 2 by rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> nlinarith [ Real.sqrt_nonneg y, Real.sq_sqrt <| show 0 ≤ y by positivity ] ] ; ring_nf at *;
  linarith

/-- **Sidon bound (Lindström)**: A Sidon set S ⊂ ℤ with |S| ≥ 2 satisfies
    |S| < √(spread) + (spread)^{1/4} + 1/2. -/
theorem Sidonbound (S : Finset ℤ) (hS : IsSidonSet S) (hcard : 2 ≤ S.card) :
    let hne : S.Nonempty := Finset.card_pos.mp (by omega)
    (S.card : ℝ) < sqrt ↑(spreadZ S hne) +
    sqrt (sqrt ↑(spreadZ S hne)) + 1 / 2 := by
  intro hne
  set y : ℝ := ↑(spreadZ S hne)
  set t : ℝ := ↑S.card
  set s : ℝ := sqrt y + sqrt (sqrt y) + 1 / 2
  -- y ≥ 1 since S has at least 2 distinct integer elements
  have hy : 1 ≤ y := by
    change (1 : ℝ) ≤ ↑(spreadZ S hne)
    exact_mod_cast spreadZ_pos S hcard
  -- f(t) ≤ y (counting bound)
  have h_count : t ^ 2 - 2 * t * sqrt t + t + sqrt t - 1 ≤ y := sidon_counting S hS hcard
  -- y < f(s) (algebraic lemma)
  have h_alg : y < s ^ 2 - 2 * s * sqrt s + s + sqrt s - 1 := algebra_sidon y hy
  -- Suppose for contradiction: s ≤ t
  by_contra h_not
  push Not at h_not
  -- f(s) ≤ f(t) by monotonicity
  have hs_nn : 0 ≤ s := by positivity
  have h_mono := f_sidon_mono hs_nn h_not
  -- Chain: y < f(s) ≤ f(t) ≤ y, contradiction
  linarith

end SidonBound

/-! ## Theorem g5upper: g₅(n) < 1.2 * 10^8 -/

/-- f_k(x) for k ≥ 3, as defined in the paper.
    f_3(x) = √(x/2) + (x/2)^(1/4) + 1/2
    f_k(x) = √(2x f_{k-1}(x) + 1/4) + 1/2  for k ≥ 4
    For k < 3, we set f_k(x) = 0. -/
noncomputable def fFun : ℕ → ℝ → ℝ
  | 0, _ | 1, _ | 2, _ => 0
  | 3, x => Real.sqrt (x / 2) + (x / 2) ^ ((1:ℝ)/4) + 1/2
  | n + 4, x => Real.sqrt (2 * x * fFun (n + 3) x + 1/4) + 1/2

/-
Base case of ceslemgeneral for k = 3: If A₀ is a nonempty set of even integers ≥ 2
    with |A₀| > f_3(max A₀ - min A₀), then there is a repeated difference,
    and we can construct 3 distinct integers with pairwise sums in A₀.
-/
lemma ceslemgeneral_base (A₀ : Finset ℤ) (hne : A₀.Nonempty)
    (heven : ∀ a ∈ A₀, 2 ∣ a)
    (hpos : ∀ a ∈ A₀, 2 ≤ a)
    (hrange : 2 ≤ A₀.max' hne - A₀.min' hne)
    (hcard : (A₀.card : ℝ) > fFun 3 (↑(A₀.max' hne - A₀.min' hne))) :
    HasPairwiseSums A₀ 3 := by
      -- Since $|A_0| > f_3(range)$ and $f_3(range) > \sqrt{2}$, we have $|A_0| \geq 3$.
      have hA₀_card : 3 ≤ (A₀.card : ℝ) := by
        contrapose! hcard;
        norm_cast at *;
        interval_cases _ : #A₀ <;> norm_num [ fFun ];
        · exact False.elim <| hne.ne_empty <| Finset.card_eq_zero.mp ‹_›;
        · rw [ Finset.card_eq_one ] at * ; aesop;
        · refine' le_trans _ ( add_le_add_three ( one_le_div ( Real.sqrt_pos.mpr zero_lt_two ) |>.2 <| Real.sqrt_le_sqrt <| show ( A₀.max' hne : ℝ ) - A₀.min' hne ≥ 2 by exact_mod_cast hrange ) ( Real.one_le_rpow _ _ ) le_rfl ) <;> norm_num;
          rw [ le_div_iff₀ ] <;> norm_cast;
      obtain ⟨a₁, a₂, a₃, ha₁, ha₂, ha₃, ha_distinct⟩ : ∃ a₁ a₂ a₃ : ℤ, a₁ ∈ A₀ ∧ a₂ ∈ A₀ ∧ a₃ ∈ A₀ ∧ a₁ < a₂ ∧ a₂ < a₃ := by
        -- Since $A₀$ has at least 3 elements, we can choose any three distinct elements from $A₀$.
        obtain ⟨s, hs⟩ : ∃ s : Fin 3 → ℤ, (∀ i, s i ∈ A₀) ∧ StrictMono s := by
          exact ⟨ fun i => A₀.orderEmbOfFin rfl ⟨ i, by norm_cast at hA₀_card; linarith [ Fin.is_lt i ] ⟩, fun i => by simp +decide, by simp +decide [ StrictMono ] ⟩;
        exact ⟨ s 0, s 1, s 2, hs.1 0, hs.1 1, hs.1 2, hs.2 ( by decide ), hs.2 ( by decide ) ⟩;
      -- Define $b₁ = (a₁ + a₂ - a₃) / 2$, $b₂ = (a₁ + a₃ - a₂) / 2$, and $b₃ = (a₂ + a₃ - a₁) / 2$.
      obtain ⟨b₁, b₂, b₃, hb₁, hb₂, hb₃⟩ : ∃ b₁ b₂ b₃ : ℤ, b₁ + b₂ = a₁ ∧ b₁ + b₃ = a₂ ∧ b₂ + b₃ = a₃ := by
        use (a₁ + a₂ - a₃) / 2, (a₁ + a₃ - a₂) / 2, (a₂ + a₃ - a₁) / 2;
        grind;
      use ![b₁, b₂, b₃];
      simp +decide [ Fin.forall_fin_succ, Function.Injective, * ];
      grind

/-! ## Subset sums containing b'_0: ceslemprelim machinery -/

/-- HasSubsetSumsContaining A k: there exist b_0, …, b_{k-1} with
    b_i ≠ 0 for i ≥ 1, b_i pairwise distinct for i ≥ 1, and
    every subset sum that includes b_0 lies in A. -/
def HasSubsetSumsContaining (A : Finset ℤ) : (k : ℕ) → Prop
  | 0 => True
  | k + 1 => ∃ b : Fin (k + 1) → ℤ,
    (∀ i : Fin (k + 1), 1 ≤ i.val → b i ≠ 0) ∧
    (∀ i j : Fin (k + 1), 1 ≤ i.val → 1 ≤ j.val → i ≠ j → b i ≠ b j) ∧
    (∀ S : Finset (Fin (k + 1)), (0 : Fin (k + 1)) ∈ S → ∑ i ∈ S, b i ∈ A)

/-
fFun k x ≥ 1 for k ≥ 3 and x ≥ 2 (early copy).
-/
private lemma fFun_ge_one_early (k : ℕ) (hk : 3 ≤ k) (x : ℝ) (hx : 2 ≤ x) :
    1 ≤ fFun k x := by
  rcases k with ( _ | _ | _ | k ) <;> norm_num at *;
  induction k <;> norm_num [ *, fFun ] at *
  · exact le_add_of_le_of_nonneg ( le_add_of_le_of_nonneg ( by rw [ one_le_div ( Real.sqrt_pos.mpr zero_lt_two ) ] ; exact Real.sqrt_le_sqrt hx ) ( by positivity ) ) ( by positivity );
  · rename_i k ih
    exact le_add_of_le_of_nonneg ( Real.le_sqrt_of_sq_le ( by nlinarith ) ) ( by norm_num )

/-
fFun is monotone for k ≥ 3 and x ≥ 2 (early copy).
-/
private lemma fFun_mono_early (k : ℕ) (hk : 3 ≤ k) (x y : ℝ)
    (hx : 2 ≤ x) (hxy : x ≤ y) : fFun k x ≤ fFun k y := by
  induction k using Nat.strong_induction_on generalizing x y
  rename_i k ih
  rcases k with ( _ | _ | _ | _ | k ) <;> simp_all +decide;
  · exact add_le_add ( add_le_add ( Real.sqrt_le_sqrt <| by gcongr ) <| Real.rpow_le_rpow ( by positivity ) ( by gcongr ) <| by positivity ) le_rfl;
  · refine' add_le_add ( Real.sqrt_le_sqrt _ ) le_rfl;
    gcongr;
    · exact le_trans ( by norm_num ) ( fFun_ge_one_early _ ( by linarith ) _ hx );
    · linarith;
    · grind +suggestions

/-
Base case of ceslemprelim: k = 3. The set A₀/2 is not Sidon,
    giving a repeated difference that yields the subset-sum triple.
-/
lemma ceslemprelim_base3 (A₀ : Finset ℤ) (hne : A₀.Nonempty)
    (heven : ∀ a ∈ A₀, 2 ∣ a) (hpos : ∀ a ∈ A₀, 2 ≤ a)
    (hrange : 2 ≤ A₀.max' hne - A₀.min' hne)
    (hcard : (A₀.card : ℝ) > fFun 3 (↑(A₀.max' hne - A₀.min' hne))) :
    HasSubsetSumsContaining A₀ 3 := by
  have h_not_sidon : ¬IsSidonSet (A₀.image (fun x => x / 2)) := by
    have h_not_sidon : (A₀.image (fun x => x / 2)).card > Real.sqrt ((A₀.max' hne - A₀.min' hne) / 2) + ( (A₀.max' hne - A₀.min' hne) / 2 ) ^ (1 / 4 : ℝ) + 1 / 2 := by
      rw [ Finset.card_image_of_injOn ];
      · convert hcard using 1;
        norm_num [ fFun ];
      · exact fun x hx y hy hxy => by linarith [ Int.ediv_mul_cancel ( heven x hx ), Int.ediv_mul_cancel ( heven y hy ) ] ;
    contrapose! h_not_sidon;
    convert Sidonbound ( A₀.image ( fun x => x / 2 ) ) h_not_sidon _ |> le_of_lt using 1;
    rw [ show spreadZ ( image ( fun x => x / 2 ) A₀ ) ( Finset.card_pos.mp <| by
          exact Finset.card_pos.mpr ⟨ _, Finset.mem_image_of_mem _ hne.choose_spec ⟩ ) = ( A₀.max' hne - A₀.min' hne ) / 2 from ?_ ]
    generalize_proofs at *;
    · rw [ Int.cast_div ] <;> norm_num;
      · norm_num [ Real.sqrt_eq_rpow, ← Real.rpow_mul ];
        rw [ Real.div_rpow ( by exact sub_nonneg_of_le <| mod_cast Finset.min'_le _ _ <| Finset.max'_mem _ _ ) ( by norm_num ), ← Real.rpow_mul ( by exact sub_nonneg_of_le <| mod_cast Finset.min'_le _ _ <| Finset.max'_mem _ _ ) ] ; norm_num;
      · exact dvd_sub ( heven _ ( Finset.max'_mem _ hne ) ) ( heven _ ( Finset.min'_mem _ hne ) );
    · all_goals generalize_proofs at *;
      unfold spreadZ;
      rw [ show ( image ( fun x => x / 2 ) A₀ ).max' ‹_› = A₀.max' hne / 2 from ?_, show ( image ( fun x => x / 2 ) A₀ ).min' ‹_› = A₀.min' hne / 2 from ?_ ];
      · rw [ Int.sub_ediv_of_dvd ] ; norm_num [ heven _ ( Finset.max'_mem _ hne ), heven _ ( Finset.min'_mem _ hne ) ];
      · refine' le_antisymm _ _ <;> simp +decide [ Finset.min' ];
        · exact ⟨ _, Finset.min'_mem _ hne, Int.ediv_le_ediv ( by norm_num ) ( Finset.min'_le _ _ <| Finset.min'_mem _ hne ) ⟩;
        · exact fun x hx => Int.ediv_le_ediv ( by norm_num ) ( Finset.inf'_le _ hx );
      · refine' le_antisymm _ _;
        · simp +decide [ Finset.max' ];
          exact fun x hx => Int.ediv_le_ediv ( by norm_num ) ( Finset.le_sup' ( fun x => x ) hx );
        · exact Finset.le_max' ( image ( fun x => x / 2 ) A₀ ) _ ( Finset.mem_image_of_mem _ ( Finset.max'_mem _ hne ) );
    · rw [ Finset.card_image_of_injOn ];
      · contrapose! hcard; interval_cases _ : Finset.card A₀ <;> simp_all +decide ;
        · grind;
        · rw [ Finset.card_eq_one ] at * ; aesop;
      · exact fun x hx y hy hxy => by linarith [ Int.ediv_mul_cancel ( heven x hx ), Int.ediv_mul_cancel ( heven y hy ) ] ;
  have h_diff : ∃ p₁ p₂ q₁ q₂ : ℤ, p₁ ∈ A₀ ∧ p₂ ∈ A₀ ∧ q₁ ∈ A₀ ∧ q₂ ∈ A₀ ∧ p₁ < q₁ ∧ p₂ < q₂ ∧ q₁ - p₁ = q₂ - p₂ ∧ (p₁, q₁) ≠ (p₂, q₂) := by
    contrapose! h_not_sidon;
    intros a ha b hb c hc d hd habcd;
    obtain ⟨ x, hx, rfl ⟩ := Finset.mem_image.mp ha; obtain ⟨ y, hy, rfl ⟩ := Finset.mem_image.mp hb; obtain ⟨ z, hz, rfl ⟩ := Finset.mem_image.mp hc; obtain ⟨ w, hw, rfl ⟩ := Finset.mem_image.mp hd; simp_all +decide [ ← even_iff_two_dvd, parity_simps ] ;
    grind;
  obtain ⟨ p₁, p₂, q₁, q₂, hp₁, hp₂, hq₁, hq₂, hp₁q₁, hp₂q₂, h_eq, h_ne ⟩ := h_diff;
  by_cases h_cases : p₁ < p₂;
  · use ![p₂, p₁ - p₂, q₂ - p₂];
    simp +decide [Fin.forall_fin_succ];
    refine' ⟨ ⟨ by linarith, by linarith ⟩, ⟨ by linarith, by linarith ⟩, _ ⟩;
    intro S hS; fin_cases S <;> simp_all +decide ;
    convert hq₁ using 1 ; linarith;
  · -- Since $p₁ \geq p₂$, we have $p₁ > p₂$.
    have h_cases_gt : p₁ > p₂ := by
      grind;
    use ![p₁, p₂ - p₁, q₁ - p₁];
    simp +decide [Fin.forall_fin_succ];
    refine' ⟨ ⟨ by linarith, by linarith ⟩, ⟨ by linarith, by linarith ⟩, _ ⟩;
    intro S hS; fin_cases S <;> simp_all +decide ;
    convert hq₁ using 1 ; linarith

/-
Stronger pigeonhole: some d has |B_d| > 2 · f_{k-1}(range).
-/
lemma ceslemgeneral_pigeonhole_strong (k : ℕ) (hk : 4 ≤ k)
    (A₀ : Finset ℤ) (hne : A₀.Nonempty)
    (heven : ∀ a ∈ A₀, 2 ∣ a)
    (hrange : 2 ≤ A₀.max' hne - A₀.min' hne)
    (hcard : (A₀.card : ℝ) > fFun k (↑(A₀.max' hne - A₀.min' hne))) :
    ∃ d : ℤ, 2 ≤ d ∧ d ≤ A₀.max' hne - A₀.min' hne ∧ (2 : ℤ) ∣ d ∧
      ((A₀.filter (fun a => a + d ∈ A₀)).card : ℝ) >
        2 * fFun (k - 1) (↑(A₀.max' hne - A₀.min' hne)) := by
  contrapose! hcard;
  -- By summing over all even $d$ in the range, we get that the total number of pairs is at most $(range/2) * 2 * fFun(k-1)(range)$.
  have h_sum : (∑ d ∈ Finset.Icc 2 (A₀.max' hne - A₀.min' hne), if 2 ∣ d then (Finset.filter (fun a => a + d ∈ A₀) A₀).card else 0) ≤ (A₀.max' hne - A₀.min' hne) * fFun (k - 1) (A₀.max' hne - A₀.min' hne) := by
    push_cast [ Finset.sum_ite ];
    refine' le_trans ( add_le_add ( Finset.sum_le_sum fun x hx => hcard x ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1 ) ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2 ) ( Finset.mem_filter.mp hx |>.2 ) ) le_rfl ) _ ; norm_num;
    -- The number of even numbers in the interval [2, range] is at most range/2.
    have h_even_count : (Finset.filter (fun x => 2 ∣ x) (Finset.Icc 2 (A₀.max' hne - A₀.min' hne))).card ≤ (A₀.max' hne - A₀.min' hne) / 2 := by
      rw [ show ( Finset.filter ( fun x => 2 ∣ x ) ( Finset.Icc 2 ( A₀.max' hne - A₀.min' hne ) ) ) = Finset.image ( fun x : ℤ => 2 * x ) ( Finset.Icc 1 ( ( A₀.max' hne - A₀.min' hne ) / 2 ) ) from ?_ ];
      · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
        omega;
      · ext;
        simp +zetaDelta at *;
        exact ⟨ fun h => ⟨ ‹_› / 2, ⟨ by omega, by omega ⟩, by omega ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by omega, by omega ⟩, by omega ⟩ ⟩;
    rw [ Int.le_ediv_iff_mul_le ] at h_even_count <;> norm_num at *;
    rw [ ← mul_assoc ] ; gcongr ; norm_cast;
    · rcases k with ( _ | _ | _ | _ | k ) <;> norm_num [ fFun ] at *;
      exact le_trans ( by norm_num ) ( fFun_ge_one_early _ ( by linarith ) _ ( by norm_cast ) );
    · norm_cast;
  -- On the other hand, the total number of pairs is also equal to $\binom{|A₀|}{2}$.
  have h_total_pairs : (∑ d ∈ Finset.Icc 2 (A₀.max' hne - A₀.min' hne), if 2 ∣ d then (Finset.filter (fun a => a + d ∈ A₀) A₀).card else 0) = (A₀.card * (A₀.card - 1)) / 2 := by
    have h_total_pairs : (∑ d ∈ Finset.Icc 2 (A₀.max' hne - A₀.min' hne), if 2 ∣ d then (Finset.filter (fun a => a + d ∈ A₀) A₀).card else 0) = Finset.card (Finset.filter (fun p => p.1 < p.2) (A₀ ×ˢ A₀)) := by
      have h_total_pairs : Finset.filter (fun p => p.1 < p.2) (A₀ ×ˢ A₀) = Finset.biUnion (Finset.filter (fun d => 2 ∣ d) (Finset.Icc 2 (A₀.max' hne - A₀.min' hne))) (fun d => Finset.image (fun a => (a, a + d)) (Finset.filter (fun a => a + d ∈ A₀) A₀)) := by
        ext ⟨a, b⟩; simp [Finset.mem_biUnion, Finset.mem_image];
        constructor;
        · intro h;
          use b - a;
          exact ⟨ ⟨ ⟨ by obtain ⟨ ha, hb ⟩ := h.1; obtain ⟨ ⟨ ha, hb ⟩, hab ⟩ := h; exact by obtain ⟨ k, hk ⟩ := heven a ha; obtain ⟨ l, hl ⟩ := heven b hb; omega, by obtain ⟨ ha, hb ⟩ := h.1; exact by linarith [ Finset.le_max' _ _ ha, Finset.le_max' _ _ hb, Finset.min'_le _ _ ha, Finset.min'_le _ _ hb ] ⟩, by obtain ⟨ ha, hb ⟩ := h.1; exact by obtain ⟨ k, hk ⟩ := heven a ha; obtain ⟨ l, hl ⟩ := heven b hb; omega ⟩, ⟨ h.1.1, by simpa using h.1.2 ⟩, by ring ⟩;
        · grind;
      rw [ h_total_pairs, Finset.card_biUnion ];
      · rw [ Finset.sum_filter ] ; exact Finset.sum_congr rfl fun x hx => by rw [ Finset.card_image_of_injective ] ; aesop_cat;
      · intros d hd d' hd' hdd'; simp_all +decide [ Finset.disjoint_left ] ;
        intros; subst_vars; omega;
    have h_total_pairs : Finset.card (Finset.filter (fun p => p.1 < p.2) (A₀ ×ˢ A₀)) = Finset.card (Finset.powersetCard 2 A₀) := by
      refine' Finset.card_bij ( fun p hp => { p.1, p.2 } ) _ _ _ <;> simp_all +decide [ Finset.subset_iff ];
      · exact fun a b ha hb hab => Finset.card_pair hab.ne;
      · simp +contextual [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
        intros; omega;
      · intro b hb hb'; rw [ Finset.card_eq_two ] at hb'; obtain ⟨ a, b, hab, rfl ⟩ := hb'; cases lt_trichotomy a b <;> aesop;
    simp_all +decide [ Nat.choose_two_right ];
  -- By combining the results from h_sum and h_total_pairs, we get the desired inequality.
  have h_combined : (A₀.card * (A₀.card - 1)) / 2 ≤ (A₀.max' hne - A₀.min' hne) * fFun (k - 1) (A₀.max' hne - A₀.min' hne) := by
    rcases n : Finset.card A₀ with ( _ | _ | n ) <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero, Nat.mod_two_of_bodd ];
  rcases k with ( _ | _ | _ | _ | k ) <;> norm_num [ fFun ] at *;
  rw [ ← sub_le_iff_le_add ];
  exact Real.le_sqrt_of_sq_le ( by linarith! )

/-
Given B with |B| > 2M and d > 0, there exists S ⊆ B with |S| > M
    and S ∩ (S + d) = ∅  (i.e., ∀ a ∈ S, a + d ∉ S).
-/
lemma disjoint_half_subset (B : Finset ℤ) (d : ℤ) (hd : 0 < d)
    (M : ℝ) (hB : (B.card : ℝ) > 2 * M) :
    ∃ S : Finset ℤ, S ⊆ B ∧ (S.card : ℝ) > M ∧ (∀ a ∈ S, a + d ∉ S) := by
  -- Let's define the sets $S_{\text{even}}$ and $S_{\text{odd}}$ as the even and odd indexed elements of $B$ respectively.
  set S_even := B.filter (fun a => (a / d) % 2 = 0)
  set S_odd := B.filter (fun a => (a / d) % 2 = 1);
  by_cases h_even : (S_even.card : ℝ) > M;
  · refine' ⟨ S_even, Finset.filter_subset _ _, h_even, _ ⟩ ; intro a ha ; simp_all +decide ;
    simp +zetaDelta at *;
    rw [ Int.add_ediv_of_dvd_right ] <;> norm_num [ hd.ne', ha.2 ];
    exact fun _ => by rw [ Int.add_emod, Int.emod_eq_zero_of_dvd ha.2 ] ; norm_num;
  · refine' ⟨ S_odd, _, _, _ ⟩;
    · exact Finset.filter_subset _ _;
    · -- Since $S_{\text{even}} \cup S_{\text{odd}} = B$, we have $|S_{\text{even}}| + |S_{\text{odd}}| = |B|$.
      have h_union : S_even.card + S_odd.card = B.card := by
        rw [ Finset.card_filter, Finset.card_filter ] ; rw [ ← Finset.sum_add_distrib ] ; exact Finset.card_eq_sum_ones _ ▸ by congr ; ext x ; aesop;
      push_cast [ ← @Nat.cast_inj ℝ ] at * ; linarith;
    · -- If $a \in S_{\text{odd}}$, then $(a / d) \% 2 = 1$. Therefore, $((a + d) / d) \% 2 = (a / d + 1) \% 2 = 0$, which means $a + d \notin S_{\text{odd}}$.
      intros a ha
      simp [S_odd] at ha ⊢;
      intro h; rw [ Int.add_ediv_of_dvd_right ] <;> norm_num [ ha.2, hd.ne' ] ;
      exact Int.dvd_of_emod_eq_zero ( by rw [ Int.add_emod, ha.2 ] ; norm_num )

/-
Extension step for ceslemprelim: given HasSubsetSumsContaining S (k-1)
    with S ⊆ B_d and S ∩ (S+d) = ∅, extend to HasSubsetSumsContaining A₀ k.
-/
lemma ceslemprelim_extend (k : ℕ) (hk : 4 ≤ k)
    (A₀ S : Finset ℤ) (d : ℤ)
    (hS_sub : S ⊆ A₀) (hd_pos : 2 ≤ d)
    (hS_shift : ∀ a ∈ S, a + d ∈ A₀)
    (hS_disj : ∀ a ∈ S, a + d ∉ S)
    (hSSC : HasSubsetSumsContaining S (k - 1)) :
    HasSubsetSumsContaining A₀ k := by
  rcases k with ( _ | _ | k ) <;> norm_num at *;
  obtain ⟨ b, hb₁, hb₂, hb₃ ⟩ := hSSC;
  refine' ⟨ Fin.snoc b d, _, _, _ ⟩ <;> simp_all +decide [ Fin.snoc ];
  · grind;
  · intro i j hi hj hij; split_ifs <;> simp_all +decide [ Fin.castLT ] ;
    · exact hb₂ _ _ hi hj ( by simpa [ Fin.ext_iff ] using hij );
    · contrapose! hS_disj;
      use b ⟨0, by linarith⟩, by
        simpa using hb₃ { 0 } ( by simp +decide ), by
        convert hb₃ { 0, ⟨ i, by linarith ⟩ } ( by simp +decide ) using 1 ; simp +decide [*];
        grind;
    · contrapose! hS_disj;
      use b 0;
      exact ⟨ by simpa using hb₃ { 0 } ( by simp +decide ), by simpa [ hS_disj, Finset.sum_pair ( show ( 0 : Fin ( k + 1 ) ) ≠ ⟨ j, by linarith ⟩ from by aesop ) ] using hb₃ { 0, ⟨ j, by linarith ⟩ } ( by simp +decide ) ⟩;
    · exact hij ( Fin.ext <| by linarith [ Fin.is_lt i, Fin.is_lt j ] );
  · intro T hT;
    by_cases hT_last : Fin.last (k + 1) ∈ T;
    · convert hS_shift _ ( hb₃ ( Finset.univ.filter fun i => Fin.castSucc i ∈ T ) ( by simpa ) ) using 1;
      rw [ Finset.sum_eq_sum_diff_singleton_add hT_last ];
      rw [ show T \ { Fin.last ( k + 1 ) } = Finset.image ( fun i : Fin ( k + 1 ) => Fin.castSucc i ) ( Finset.filter ( fun i : Fin ( k + 1 ) => Fin.castSucc i ∈ T ) Finset.univ ) from ?_, Finset.sum_image ] <;> norm_num [ Fin.ext_iff ];
      · exact Finset.sum_congr rfl fun x hx => if_pos <| Nat.le_of_lt_succ <| Fin.is_lt x;
      · ext i; simp [Finset.mem_image];
        exact ⟨ fun hi => ⟨ ⟨ i.val, lt_of_le_of_ne ( Fin.le_last _ ) ( by simpa [ Fin.ext_iff ] using hi.2 ) ⟩, by simpa [ Fin.ext_iff ] using hi.1, rfl ⟩, by rintro ⟨ a, ha₁, rfl ⟩ ; exact ⟨ ha₁, ne_of_lt ( Fin.castSucc_lt_last _ ) ⟩ ⟩;
    · -- Since $T$ does not contain the last element, we can map $T$ to a subset of $\text{Fin}(k+1)$.
      obtain ⟨T', hT'⟩ : ∃ T' : Finset (Fin (k + 1)), T = Finset.image (fun i => Fin.castSucc i) T' := by
        use Finset.univ.filter (fun i => Fin.castSucc i ∈ T);
        ext i; simp [Finset.mem_image];
        induction i using Fin.lastCases <;> aesop;
      simp_all +decide [ Finset.sum_image ];
      rw [ Finset.sum_congr rfl fun i hi => if_pos <| Nat.le_of_lt_succ <| Fin.is_lt i ] ; exact hS_sub <| hb₃ T' hT

/-
Two distinct even naturals ≥ 2 differ by at least 2.
-/
private lemma even_range_ge_two (S : Finset ℤ) (hne : S.Nonempty)
    (heven : ∀ a ∈ S, (2 : ℤ) ∣ a) (hcard : 2 ≤ S.card) :
    2 ≤ S.max' hne - S.min' hne := by
  -- Let $m$ be the minimum element of $S$ and $M$ be the maximum element of $S$.
  obtain ⟨m, hm⟩ : ∃ m ∈ S, ∀ a ∈ S, m ≤ a := by
    exact ⟨ Finset.min' _ hne, Finset.min'_mem _ hne, fun a ha => Finset.min'_le _ _ ha ⟩
  obtain ⟨M, hM⟩ : ∃ M ∈ S, ∀ a ∈ S, a ≤ M := by
    exact ⟨ Finset.max' _ hne, Finset.max'_mem _ hne, fun a ha => Finset.le_max' _ _ ha ⟩;
  -- Since S has at least two elements, there exists some element a in S such that a ≠ m.
  obtain ⟨a, ha₁, ha₂⟩ : ∃ a ∈ S, a ≠ m := by
    exact Finset.exists_mem_ne hcard m;
  -- Since S has at least two elements, there exists some element a in S such that a ≠ m. Given that all elements of S are even and at least 2, the smallest possible difference between any two distinct elements is 2.
  have h_diff : 2 ≤ a - m := by
    grind;
  exact le_trans h_diff ( by linarith [ hm.2 a ha₁, hM.2 a ha₁, Finset.min'_le _ _ hm.1, Finset.le_max' _ _ hm.1, Finset.min'_le _ _ hM.1, Finset.le_max' _ _ hM.1 ] )

/-- Main ceslemprelim theorem by induction on k ≥ 3. -/
theorem ceslemprelim (k : ℕ) (hk : 3 ≤ k) (A₀ : Finset ℤ) (hne : A₀.Nonempty)
    (heven : ∀ a ∈ A₀, 2 ∣ a)
    (hpos : ∀ a ∈ A₀, 2 ≤ a)
    (hrange : 2 ≤ A₀.max' hne - A₀.min' hne)
    (hcard : (A₀.card : ℝ) > fFun k (↑(A₀.max' hne - A₀.min' hne))) :
    HasSubsetSumsContaining A₀ k := by
  induction k, hk using Nat.le_induction generalizing A₀ with
  | base => exact ceslemprelim_base3 A₀ hne heven hpos hrange hcard
  | succ k hk ih =>
    -- Get d with |B_d| > 2 * f_k(range)
    obtain ⟨d, hd_lb, hd_ub, hd_even, hBd_card⟩ :=
      ceslemgeneral_pigeonhole_strong (k + 1) (by omega) A₀ hne heven hrange hcard
    set B_d := A₀.filter (fun a => a + d ∈ A₀) with hBd_def
    -- Get disjoint S ⊆ B_d with |S| > f_k(range)
    obtain ⟨S, hS_sub_Bd, hS_card, hS_disj⟩ :=
      disjoint_half_subset B_d d (by omega)
        (fFun k (↑(A₀.max' hne - A₀.min' hne)))
        (by rwa [Nat.add_sub_cancel] at hBd_card)
    -- S ⊆ A₀, even, positive
    have hS_sub_A₀ : S ⊆ A₀ := hS_sub_Bd.trans (Finset.filter_subset _ _)
    have hS_even : ∀ a ∈ S, (2 : ℤ) ∣ a := fun a ha => heven a (hS_sub_A₀ ha)
    have hS_pos : ∀ a ∈ S, (2 : ℤ) ≤ a := fun a ha => hpos a (hS_sub_A₀ ha)
    have hS_ne : S.Nonempty := by
      by_contra h
      simp only [Finset.not_nonempty_iff_eq_empty] at h
      rw [h, Finset.card_empty, Nat.cast_zero] at hS_card
      linarith [fFun_ge_one_early k (by omega) (↑(A₀.max' hne - A₀.min' hne))
        (by exact_mod_cast hrange)]
    have hS_card_ge_2 : 2 ≤ S.card := by
      by_contra h; push Not at h
      have : (S.card : ℝ) ≤ 1 := by exact_mod_cast (by omega : S.card ≤ 1)
      linarith [fFun_ge_one_early k (by omega) (↑(A₀.max' hne - A₀.min' hne))
        (by exact_mod_cast hrange)]
    have hS_range : 2 ≤ S.max' hS_ne - S.min' hS_ne :=
      even_range_ge_two S hS_ne hS_even hS_card_ge_2
    -- S has card > f_k(range of S) since range S ≤ range A₀
    have hS_range_le : (S.max' hS_ne - S.min' hS_ne : ℤ) ≤
        A₀.max' hne - A₀.min' hne := by
      have h1 := Finset.max'_subset hS_ne hS_sub_A₀
      have h2 := Finset.min'_subset hS_ne hS_sub_A₀
      omega
    have hS_card_bound : (S.card : ℝ) >
        fFun k (↑(S.max' hS_ne - S.min' hS_ne)) := by
      calc (S.card : ℝ)
          > fFun k (↑(A₀.max' hne - A₀.min' hne)) := hS_card
        _ ≥ fFun k (↑(S.max' hS_ne - S.min' hS_ne)) := by
            apply fFun_mono_early k (by omega)
            · exact_mod_cast hS_range
            · exact_mod_cast hS_range_le
    -- Apply IH
    have hSSC : HasSubsetSumsContaining S k := ih S hS_ne hS_even hS_pos hS_range hS_card_bound
    -- Extension: S ⊆ B_d means ∀ a ∈ S, a + d ∈ A₀
    have hS_shift : ∀ a ∈ S, a + d ∈ A₀ := by
      intro a ha; exact (Finset.mem_filter.mp (hS_sub_Bd ha)).2
    exact ceslemprelim_extend (k + 1) (by omega) A₀ S d hS_sub_A₀ hd_lb hS_shift hS_disj
      (by rwa [Nat.add_sub_cancel])

/-
If HasSubsetSumsContaining A k (k ≥ 3) and A has only even elements,
    then HasPairwiseSums A k.
-/
lemma subsetsums_to_pairwise (A : Finset ℤ) (k : ℕ) (hk : 3 ≤ k)
    (heven : ∀ a ∈ A, (2 : ℤ) ∣ a)
    (hSSC : HasSubsetSumsContaining A k) :
    HasPairwiseSums A k := by
  rcases k with ( _ | _ | k ) <;> simp_all +decide [ HasSubsetSumsContaining ];
  -- Define c : Fin (k + 2) → ℤ by:
  -- - c 0 = b 0 / 2
  -- - c i = b 0 / 2 + b i  for i ≥ 1
  obtain ⟨b, hb⟩ := hSSC
  use fun i => if i = 0 then b 0 / 2 else b 0 / 2 + b i;
  constructor;
  · intro i j hij;
    grind;
  · intro i j hij; rcases i with ⟨ _ | i, hi ⟩ <;> rcases j with ⟨ _ | j, hj ⟩ <;> norm_num at *;
    · convert hb.2.2 { 0, ⟨ j + 1, hj ⟩ } _ using 1 <;> norm_num;
      linarith [ Int.ediv_mul_cancel ( show 2 ∣ b 0 from by simpa using heven _ ( hb.2.2 { 0 } ( by simp +decide ) ) ) ];
    · convert hb.2.2 { 0, ⟨ i + 1, hi ⟩, ⟨ j + 1, hj ⟩ } ( by simp +decide ) using 1 ; simp +decide [Finset.sum_singleton,
      hij.ne] ; ring_nf;
      linarith [ Int.ediv_mul_cancel ( show 2 ∣ b 0 from heven _ ( hb.2.2 { 0 } ( by simp +decide ) |> fun x => by simpa using x ) ) ]

lemma ceslemgeneral_step (k : ℕ) (hk : 4 ≤ k)
    (_ih : ∀ (A₀ : Finset ℤ) (hne : A₀.Nonempty),
      (∀ a ∈ A₀, 2 ∣ a) → (∀ a ∈ A₀, 2 ≤ a) →
      2 ≤ A₀.max' hne - A₀.min' hne →
      (A₀.card : ℝ) > fFun (k - 1) (↑(A₀.max' hne - A₀.min' hne)) →
      HasPairwiseSums A₀ (k - 1))
    (A₀ : Finset ℤ) (hne : A₀.Nonempty)
    (heven : ∀ a ∈ A₀, 2 ∣ a)
    (hpos : ∀ a ∈ A₀, 2 ≤ a)
    (hrange : 2 ≤ A₀.max' hne - A₀.min' hne)
    (hcard : (A₀.card : ℝ) > fFun k (↑(A₀.max' hne - A₀.min' hne))) :
    HasPairwiseSums A₀ k := by
  exact subsetsums_to_pairwise A₀ k (by omega) heven
    (ceslemprelim k (by omega) A₀ hne heven hpos hrange hcard)

/-- Lemma ceslemgeneral: If A₀ is a nonempty set of even integers ≥ 2 with
    |A₀| > f_k(max A₀ - min A₀), then A₀ contains k distinct integers
    whose pairwise sums are all in A₀. -/
theorem ceslemgeneral (k : ℕ) (hk : 3 ≤ k) (A₀ : Finset ℤ) (hne : A₀.Nonempty)
    (heven : ∀ a ∈ A₀, 2 ∣ a)
    (hpos : ∀ a ∈ A₀, 2 ≤ a)
    (hrange : 2 ≤ A₀.max' hne - A₀.min' hne)
    (hcard : (A₀.card : ℝ) > fFun k (↑(A₀.max' hne - A₀.min' hne))) :
    HasPairwiseSums A₀ k := by
  induction k, hk using Nat.le_induction generalizing A₀ with
  | base => exact ceslemgeneral_base A₀ hne heven hpos hrange hcard
  | succ k hk ih =>
    exact ceslemgeneral_step (k + 1) (by omega)
      (fun A₀' hne' h1 h2 h3 h4 => by
        simp only [Nat.add_sub_cancel] at h4
        exact ih A₀' hne' h1 h2 h3 h4)
      A₀ hne heven hpos hrange hcard

/-- If A has many even elements (≥ r) in an interval of length x,
    and r > f_5(x), then A contains 5 distinct integers with pairwise sums in A. -/
lemma g5upper_case_even (A : Finset ℤ) (A₀ : Finset ℤ)
    (hA₀_sub : A₀ ⊆ A)
    (hne : A₀.Nonempty)
    (heven : ∀ a ∈ A₀, 2 ∣ a)
    (hpos : ∀ a ∈ A₀, 2 ≤ a)
    (hrange : 2 ≤ A₀.max' hne - A₀.min' hne)
    (hcard : (A₀.card : ℝ) > fFun 5 (↑(A₀.max' hne - A₀.min' hne))) :
    HasPairwiseSums A 5 := by
  obtain ⟨b, hb_inj, hb_sums⟩ := ceslemgeneral 5 (by omega) A₀ hne heven hpos hrange hcard
  exact ⟨b, hb_inj, fun i j hij => hA₀_sub (hb_sums i j hij)⟩

/-
Monotonicity of f_k: if 2 ≤ x ≤ y then f_k(x) ≤ f_k(y) for k ≥ 3.
-/
lemma fFun_mono (k : ℕ) (hk : 3 ≤ k) (x y : ℝ) (hx : 2 ≤ x) (hxy : x ≤ y) :
    fFun k x ≤ fFun k y := by
  induction k using Nat.strong_induction_on
  rename_i k ih
  rcases k with ( _ | _ | _ | k ) <;> simp_all +decide [ fFun ];
  rcases k with ( _ | k ) <;> simp_all +decide [ fFun ];
  · gcongr;
  · -- Since $fFun (k + 3) x \geq 1$ for $x \geq 2$, we have $fFun (k + 3) x - 1 \geq 0$.
    have h_f_ge_one : 1 ≤ fFun (k + 3) x := by
      induction k with
      | zero =>
        norm_num [ *, fFun ] at *
        exact le_add_of_le_of_nonneg ( le_add_of_le_of_nonneg ( by rw [ one_le_div ( Real.sqrt_pos.mpr zero_lt_two ) ] ; exact Real.sqrt_le_sqrt hx ) ( by positivity ) ) ( by positivity );
      | succ k ih =>
        norm_num [ *, fFun ] at *
        rename_i h
        specialize h ( fun m hm₁ hm₂ => ih m ( by linarith ) hm₂ ) ; nlinarith [ Real.sqrt_nonneg ( 2 * x * fFun ( k + 3 ) x + 1 / 4 ), Real.mul_self_sqrt ( show 0 ≤ 2 * x * fFun ( k + 3 ) x + 1 / 4 by nlinarith [ show 0 ≤ fFun ( k + 3 ) x by linarith ] ) ] ;
    exact Real.sqrt_le_sqrt <| by nlinarith [ ih ( k + 3 ) ( by linarith ) ( by linarith ) ] ;

/-
Sublinearity of f_k: f_k(2x) < 2 f_k(x) for k ≥ 3 and x ≥ 1
-/
lemma fFun_sublinear (k : ℕ) (hk : 3 ≤ k) (x : ℝ) (hx : 1 ≤ x) :
    fFun k (2 * x) < 2 * fFun k x := by
  induction hk
  · -- By simplifying, we can see that both sides of the inequality are equal when $x \geq 1$.
    simp [fFun] at *;
    rw [ Real.div_rpow ( by positivity ) ( by positivity ) ] ; ring_nf;
    gcongr <;> norm_num;
    · nlinarith [ Real.sqrt_nonneg x, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, Real.sq_sqrt ( show 0 ≤ x by positivity ), inv_pos.2 ( Real.sqrt_pos.2 zero_lt_two ), mul_inv_cancel₀ ( ne_of_gt ( Real.sqrt_pos.2 zero_lt_two ) ), mul_pos ( Real.sqrt_pos.2 zero_lt_two ) ( Real.sqrt_pos.2 ( show 0 < x by positivity ) ) ];
    · rw [ mul_assoc ];
      exact lt_mul_of_one_lt_right ( by positivity ) ( by rw [ ← div_eq_inv_mul ] ; rw [ one_lt_div ( by positivity ) ] ; exact lt_of_lt_of_le ( Real.rpow_lt_rpow_of_exponent_lt ( by norm_num ) ( show ( 1 : ℝ ) / 4 < 1 by norm_num ) ) ( by norm_num ) );
  · rename_i k hk ih
    rcases k with ( _ | _ | _ | k ) <;> norm_num [ fFun ] at *;
    rw [ ← lt_sub_iff_add_lt ];
    rw [ Real.sqrt_lt' ] <;> ring_nf;
    · rw [ show 3 + k = k + 3 by ring ];
      rw [ mul_comm x 2 ] at *;
      nlinarith [ Real.sqrt_nonneg ( 1 / 4 + x * fFun ( k + 3 ) x * 2 ), Real.mul_self_sqrt ( show 0 ≤ 1 / 4 + x * fFun ( k + 3 ) x * 2 by nlinarith [ show 0 ≤ fFun ( k + 3 ) x by exact Nat.recOn k ( by exact add_nonneg ( add_nonneg ( Real.sqrt_nonneg _ ) ( Real.rpow_nonneg ( by positivity ) _ ) ) ( by positivity ) ) fun n ihn => by rw [ show fFun ( n + 4 ) x = Real.sqrt ( 2 * x * fFun ( n + 3 ) x + 1 / 4 ) + 1 / 2 by rfl ] ; positivity ] ) ];
    · positivity

/-
Helper: 2^(5/8) ≤ 31/20.
-/
lemma rpow_two_five_eighth_le : (2:ℝ) ^ ((5:ℝ)/8) ≤ 31/20 := by
  rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_rpow ] <;> norm_num;
  rw [ div_mul_eq_mul_div, div_le_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.log_le_log ]

/-
Algebraic inequality: 7w^8 - 8w^7 + 1 ≥ 0 for w ≥ 0.
Factors as (1-w)²(7w⁶+6w⁵+5w⁴+4w³+3w²+2w+1).
-/
lemma poly_nonneg (w : ℝ) (hw : 0 ≤ w) :
    0 ≤ 7 * w ^ 8 - 8 * w ^ 7 + 1 := by
      nlinarith [ mul_nonneg hw ( sq_nonneg ( w - 1 ) ), mul_nonneg hw ( sq_nonneg ( w ^ 2 - 1 ) ), mul_nonneg hw ( sq_nonneg ( w ^ 3 - 1 ) ), mul_nonneg hw ( sq_nonneg ( w ^ 4 - 1 ) ), mul_nonneg hw ( sq_nonneg ( w ^ 5 - 1 ) ) ]

/-
fFun 4 x ≤ 2^(1/4)·x^(3/4) + √x + 1/2 for x ≥ 1.
-/
lemma fFun4_tight_bound (x : ℝ) (hx : 1 ≤ x) :
    fFun 4 x ≤ (2:ℝ) ^ ((1:ℝ)/4) * x ^ ((3:ℝ)/4) + Real.sqrt x + 1 / 2 := by
      have h_fFun4 : fFun 4 x = Real.sqrt (2 * x * fFun 3 x + 1 / 4) + 1 / 2 := by
        rfl;
      have h_expand : 2 * x * fFun 3 x = Real.sqrt 2 * x ^ (3 / 2 : ℝ) + 2 ^ (3 / 4 : ℝ) * x ^ (5 / 4 : ℝ) + x := by
        rw [ show fFun 3 x = Real.sqrt ( x / 2 ) + ( x / 2 ) ^ ( 1 / 4 : ℝ ) + 1 / 2 by rfl ] ; ring_nf;
        norm_num [ Real.sqrt_eq_rpow, Real.mul_rpow, Real.div_rpow, hx.trans' ] ; ring_nf;
        rw [ show ( 3 / 2 : ℝ ) = 1 + 1 / 2 by norm_num, show ( 5 / 4 : ℝ ) = 1 + 1 / 4 by norm_num, Real.rpow_add, Real.rpow_add ] <;> norm_num <;> ring_nf <;> try positivity;
        rw [ show ( 3 / 4 : ℝ ) = 1 - 1 / 4 by norm_num, Real.rpow_sub ] <;> norm_num ; ring_nf;
        norm_num [ ← Real.sqrt_eq_rpow ];
        rw [ ← Real.sqrt_div_self ] ; ring;
      rw [ h_fFun4, h_expand ];
      -- We'll use that $2^{3/4} \cdot (\sqrt{2} - 1) \cdot x^{5/4} \geq 1/4$ for $x \geq 1$.
      have h_ineq : 2 ^ (3 / 4 : ℝ) * (Real.sqrt 2 - 1) * x ^ (5 / 4 : ℝ) ≥ 1 / 4 := by
        refine le_trans ?_ ( mul_le_mul_of_nonneg_left ( Real.one_le_rpow hx ( by norm_num ) ) ( by exact mul_nonneg ( Real.rpow_nonneg zero_le_two _ ) ( sub_nonneg.mpr ( Real.le_sqrt_of_sq_le ( by norm_num ) ) ) ) );
        rw [ show ( 2 : ℝ ) ^ ( 3 / 4 : ℝ ) = 2 ^ ( 1 / 2 : ℝ ) * 2 ^ ( 1 / 4 : ℝ ) by rw [ ← Real.rpow_add ] <;> norm_num ] ; ring_nf ; norm_num;
        rw [ ← Real.sqrt_eq_rpow ] ; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, show ( 1 : ℝ ) ≤ 2 ^ ( 1 / 4 : ℝ ) by exact Real.one_le_rpow ( by norm_num ) ( by norm_num ), mul_le_mul_of_nonneg_left ( show ( 1 : ℝ ) ≤ 2 ^ ( 1 / 4 : ℝ ) by exact Real.one_le_rpow ( by norm_num ) ( by norm_num ) ) ( Real.sqrt_nonneg 2 ) ];
      norm_num [ Real.sqrt_eq_rpow, ← Real.rpow_mul ( by positivity : 0 ≤ x ) ] at *;
      rw [ ← Real.sqrt_eq_rpow, Real.sqrt_le_left ] <;> ring_nf at * <;> norm_num at *;
      · norm_num [ sq, mul_assoc, ← Real.rpow_add ( by positivity : 0 < x ) ] at *;
        rw [ show ( 3 / 4 : ℝ ) = 1 / 2 + 1 / 4 by norm_num, Real.rpow_add ] at * <;> norm_num at * ; ring_nf at * ; norm_num at *;
        norm_num [ sq, ← Real.rpow_add ] at * ; linarith;
      · positivity

/-
Algebraic inequality: 5w^8 - 8w^5 + 3 ≥ 0 for w ≥ 0.
Decomposes as 4w²(w³-1)² + (w⁴-1)² + 2(w²-1)².
-/
lemma poly_nonneg58 (w : ℝ) (hw : 0 ≤ w) :
    0 ≤ 5 * w ^ 8 - 8 * w ^ 5 + 3 := by
  nlinarith [mul_nonneg (mul_nonneg hw hw) (sq_nonneg (w^3 - 1)),
             sq_nonneg (w^4 - 1), sq_nonneg (w^2 - 1)]

/-
f₅(x) ≤ 2^(5/8)·x^(7/8) + (√5/2)·x^(5/8) + 1/2 for x ≥ 1.
-/
lemma fFun5_tight_bound_v2 (x : ℝ) (hx : 1 ≤ x) :
    fFun 5 x ≤ (2:ℝ) ^ ((5:ℝ)/8) * x ^ ((7:ℝ)/8) + Real.sqrt 5 / 2 * x ^ ((5:ℝ)/8) + 1 / 2 := by
  have h_step : 2 * x * fFun 4 x + 1 / 4 ≤ (2 ^ ((5:ℝ)/8) * x ^ ((7:ℝ)/8) + (Real.sqrt 5 / 2) * x ^ ((5:ℝ)/8)) ^ 2 := by
    have h_step : 2 * x * fFun 4 x + 1 / 4 ≤ 2 ^ ((5:ℝ)/4) * x ^ ((7:ℝ)/4) + 2 * x ^ ((3:ℝ)/2) + x + 1 / 4 := by
      have h_step : fFun 4 x ≤ 2 ^ ((1:ℝ)/4) * x ^ ((3:ℝ)/4) + Real.sqrt x + 1 / 2 := by
        exact fFun4_tight_bound x hx;
      convert add_le_add_right ( mul_le_mul_of_nonneg_left h_step ( show ( 0 : ℝ ) ≤ 2 * x by positivity ) ) ( 1 / 4 : ℝ ) using 1 ; ring;
      rw [ show ( 5 / 4 : ℝ ) = 1 + 1 / 4 by norm_num, show ( 7 / 4 : ℝ ) = 3 / 4 + 1 by norm_num, show ( 3 / 2 : ℝ ) = 1 + 1 / 2 by norm_num, Real.sqrt_eq_rpow, Real.rpow_add, Real.rpow_add, Real.rpow_add ] <;> norm_num <;> ring_nf <;> linarith;
    -- Combine like terms and simplify the inequality.
    have h_simplify : Real.sqrt 5 * 2 ^ ((5:ℝ)/8) * x ^ ((3:ℝ)/2) + (5 / 4) * x ^ ((5:ℝ)/4) ≥ 2 * x ^ ((3:ℝ)/2) + x + 1 / 4 := by
      -- We'll use that $Real.sqrt 5 * 2 ^ ((5:ℝ)/8) > 2$ and $5 / 4 > 1$ to conclude the proof.
      have h_sqrt5_gt2 : Real.sqrt 5 * 2 ^ ((5:ℝ)/8) > 2 := by
        nlinarith only [ show 1 < Real.sqrt 5 by norm_num [ Real.lt_sqrt ], show 1 < ( 2 : ℝ ) ^ ( 5 / 8 : ℝ ) by exact Real.one_lt_rpow ( by norm_num ) ( by norm_num ), Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ];
      nlinarith [ show x ^ ( 3 / 2 : ℝ ) ≥ 1 by exact Real.one_le_rpow hx ( by norm_num ), show x ^ ( 5 / 4 : ℝ ) ≥ x by exact le_trans ( by norm_num ) ( Real.rpow_le_rpow_of_exponent_le hx ( show ( 5 : ℝ ) / 4 ≥ 1 by norm_num ) ) ];
    convert h_step.trans _ using 1 ; ring_nf at * ; norm_num at *;
    convert add_le_add_left h_simplify ( 2 ^ ( 5 / 4 : ℝ ) * x ^ ( 7 / 4 : ℝ ) ) using 1 ; ring_nf at * ; norm_num at *;
    norm_num [ sq, mul_assoc, mul_left_comm, ← Real.rpow_add ( by positivity : 0 < x ), ← Real.rpow_add ( by positivity : 0 < ( 2 : ℝ ) ) ] ; ring_nf;
    rw [ show ( 3 / 2 : ℝ ) = 7 / 8 + 5 / 8 by norm_num, Real.rpow_add ( by positivity ) ] ; ring;
  -- Apply the square root to both sides of h_step.
  have h_sqrt : Real.sqrt (2 * x * fFun 4 x + 1 / 4) ≤ 2 ^ ((5:ℝ)/8) * x ^ ((7:ℝ)/8) + (Real.sqrt 5 / 2) * x ^ ((5:ℝ)/8) := by
    exact Real.sqrt_le_iff.mpr ⟨ by positivity, h_step ⟩;
  convert add_le_add_right h_sqrt ( 1 / 2 ) using 1;
  · exact show Real.sqrt ( 2 * x * fFun 4 x + 1 / 4 ) + 1 / 2 = 1 / 2 + Real.sqrt ( 2 * x * fFun 4 x + 1 / 4 ) from add_comm _ _;
  · ring

/-- Rational bound: √5/2 ≤ 28/25. -/
lemma sqrt5_half_le : Real.sqrt 5 / 2 ≤ 28 / 25 := by
  have : Real.sqrt 5 ≤ 56/25 := by
    rw [Real.sqrt_le_left] <;> nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)]
  linarith

/-- Combined rational tight bound for fFun 5 (version 3, with x^(5/8) term). -/
lemma fFun_5_rational_v3 (x : ℝ) (hx : 1 ≤ x) :
    fFun 5 x ≤ (31:ℝ)/20 * x^((7:ℝ)/8) + (28:ℝ)/25 * x^((5:ℝ)/8) + 1/2 := by
  have h := fFun5_tight_bound_v2 x hx
  have h1 : (2:ℝ) ^ ((5:ℝ)/8) ≤ 31/20 := rpow_two_five_eighth_le
  have h2 : Real.sqrt 5 / 2 ≤ 28/25 := sqrt5_half_le
  have hx78 : (0:ℝ) ≤ x ^ ((7:ℝ)/8) := by positivity
  have hx58 : (0:ℝ) ≤ x ^ ((5:ℝ)/8) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 hx78, mul_le_mul_of_nonneg_right h2 hx58]

/-
For all x ≥ 0: (31/20)·x^(7/8) ≤ (5611/67500)·x + K₁ where K₁ = (23625/1448)^7 * 31/160.
-/
lemma rpow78_le_young_new (x : ℝ) (hx : 0 ≤ x) :
    (31:ℝ)/20 * x ^ ((7:ℝ)/8) ≤ 5611 * x / 67500 + ((23625:ℝ)/1448)^7 * 31/160 := by
  set u : ℝ := x ^ (1 / 8 : ℝ)
  set w : ℝ := 1448 * u / 23625
  have h_sub : ((23625:ℝ)^7*31/(1448^7*160)) * (7 * w ^ 8 - 8 * w ^ 7 + 1) ≥ 0 := by
    exact mul_nonneg (by positivity) (poly_nonneg w (by positivity))
  norm_num +zetaDelta at *
  ring_nf at *
  norm_num only [← Real.rpow_natCast, ← Real.rpow_mul hx] at *
  norm_num at * ; linarith

/-
For all x ≥ 0: (28/25)·x^(5/8) ≤ (7/33750)·x + 637875/2.
-/
lemma rpow58_le_young (x : ℝ) (hx : 0 ≤ x) :
    (28:ℝ)/25 * x ^ ((5:ℝ)/8) ≤ 7 * x / 33750 + (637875:ℝ)/2 := by
  set u : ℝ := x ^ (1 / 8 : ℝ)
  set w : ℝ := u / 15
  have h_sub : ((212625:ℝ)/2) * (5 * w ^ 8 - 8 * w ^ 5 + 3) ≥ 0 := by
    exact mul_nonneg (by positivity) (poly_nonneg58 w (by positivity))
  norm_num +zetaDelta at *
  ring_nf at *
  norm_num only [← Real.rpow_natCast, ← Real.rpow_mul hx] at *
  norm_num at * ; linarith

/-
For all x ≥ 1, f_5(x) < x/12 + (120000000-1)/2 - 2.
-/
lemma key_ineq (x : ℝ) (hx : 1 ≤ x) :
    fFun 5 x < x / 12 + (120000000 - 1) / 2 - 2 := by
  have h1 := fFun_5_rational_v3 x hx
  have h2 := rpow78_le_young_new x (by linarith)
  have h3 := rpow58_le_young x (by linarith)
  -- 5611/67500 + 7/33750 = 1/12
  have h_eps : (5611:ℝ)/67500 + 7/33750 = 1/12 := by norm_num
  -- K₁ + K₂ + 1/2 < (120000000-1)/2 - 2
  have h4 : ((23625:ℝ)/1448)^7 * 31/160 + (637875:ℝ)/2 + 1/2 < (120000000 - 1) / 2 - 2 := by norm_num
  linarith

/-
Combined bound: f_5(2n) < n/6 + (120000000-1) - 4 for n ≥ 1.
-/
lemma fFun5_bound_2n (n : ℝ) (hn : 1 ≤ n) :
    fFun 5 (2 * n) < n / 6 + (120000000 - 1) - 4 := by
  calc fFun 5 (2 * n) < 2 * fFun 5 n := fFun_sublinear 5 (by omega) n hn
    _ < 2 * (n / 12 + (120000000 - 1) / 2 - 2) := by linarith [key_ineq n hn]
    _ = n / 6 + (120000000 - 1) - 4 := by ring

/-
The core upper bound: any A ⊆ {1,...,2n} with |A| ≥ n + c
    contains 5 distinct integers with all pairwise sums in A, where c = 120000000-1.

Case when even elements have enough density to apply CES lemma directly.
-/
lemma g5upper_aux_ces (n : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n))
    (hn : 120000000 - 1 ≤ n)
    (heven_count : n / 6 + (120000000 - 1) ≤ (A.filter (fun x => Even x)).card) :
    HasPairwiseSums A 5 := by
  have hA₀_sub : Finset.filter (fun x => Even x) A ⊆ A := by
    exact Finset.filter_subset _ _
  have hA₀_nonempty : (Finset.filter (fun x => Even x) A).Nonempty := by
    exact Finset.card_pos.mp ( by omega )
  have hA₀_even : ∀ a ∈ Finset.filter (fun x => Even x) A, 2 ∣ a := by
    exact fun x hx => even_iff_two_dvd.mp <| Finset.mem_filter.mp hx |>.2
  have hA₀_pos : ∀ a ∈ Finset.filter (fun x => Even x) A, 2 ≤ a := by
    exact fun x hx => by obtain ⟨ k, rfl ⟩ := hA₀_even x hx; linarith [ show k > 0 from by linarith [ Finset.mem_Icc.mp ( hA ( hA₀_sub hx ) ) ] ] ;
  have hA₀_range : 2 ≤ (Finset.filter (fun x => Even x) A).max' hA₀_nonempty - (Finset.filter (fun x => Even x) A).min' hA₀_nonempty := by
    -- Since the set A₀ has at least 2 elements, the spread must be at least the difference between the two smallest elements.
    have hA₀_card_ge_two : 2 ≤ (Finset.filter (fun x => Even x) A).card := by
      omega;
    exact even_range_ge_two ({x ∈ A | Even x}) hA₀_nonempty hA₀_even hA₀_card_ge_two
  have hA₀_card : (Finset.filter (fun x => Even x) A).card > fFun 5 (((Finset.filter (fun x => Even x) A).max' hA₀_nonempty) - ((Finset.filter (fun x => Even x) A).min' hA₀_nonempty)) := by
    -- We have $fFun 5 (spread) \leq fFun 5 (2n)$ by $fFun_mono$, and $fFun 5 (2n) < n/6 + c - 4$ by $fFun5_bound_2n$.
    have h_bound : fFun 5 (((Finset.filter (fun x => Even x) A).max' hA₀_nonempty) - ((Finset.filter (fun x => Even x) A).min' hA₀_nonempty)) ≤ fFun 5 (2 * n) := by
      apply fFun_mono;
      · norm_num;
      · exact_mod_cast hA₀_range;
      · norm_cast;
        exact le_trans ( sub_le_self _ <| by linarith [ hA₀_pos _ <| Finset.min'_mem _ hA₀_nonempty ] ) <| Finset.max'_mem _ hA₀_nonempty |> fun x => Finset.mem_Icc.mp ( hA <| hA₀_sub x ) |>.2
    have h_final_bound : fFun 5 (2 * n) < n / 6 + (120000000 - 1) - 4 := by
      have := fFun5_bound_2n n;
      exact this <| mod_cast hn.trans' <| by norm_num;
    refine lt_of_le_of_lt h_bound <| h_final_bound.trans_le ?_;
    rw [ sub_le_iff_le_add ];
    rw [ div_add', div_le_iff₀ ] <;> norm_cast;
    grind;
  apply g5upper_case_even;
  any_goals assumption;
  aesop

/-
Counting: at most |A₀|-c odd elements of [1,2n] are missing from A,
    where A₀ is the even part and |A| ≥ n+c.
-/
lemma missing_odds_le (n : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n))
    (hcard : n + 120000000-1 ≤ A.card)
    (heven_gt : 120000000-1 < (A.filter (fun x => Even x)).card) :
    ((Icc (1:ℤ) (2*↑n)).filter (fun x => ¬Even x) \ A).card
      ≤ (A.filter (fun x => Even x)).card - (120000000-1) := by
  rw [ Finset.card_sdiff ];
  rw [ Finset.inter_comm ];
  rw [ show { x ∈ Icc 1 ( 2 * ( n : ℤ ) ) | ¬Even x } ∩ A = A.filter ( fun x => ¬Even x ) from ?_ ];
  · have h_odd_count : (Finset.filter (fun x => ¬Even x) (Finset.Icc (1:ℤ) (2 * n))).card = n := by
      rw [ show ( Finset.filter ( fun x : ℤ => ¬Even x ) ( Finset.Icc 1 ( 2 * n ) ) ) = Finset.image ( fun k : ℕ => 2 * k + 1 : ℕ → ℤ ) ( Finset.range n ) from ?_, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
      -- To prove equality of finite sets, we show each set is a subset of the other.
      apply Finset.ext
      intro x
      simp [Finset.mem_image, Finset.mem_filter];
      exact ⟨ fun hx => by obtain ⟨ k, rfl ⟩ := hx.2; exact ⟨ Int.toNat k, by linarith [ Int.toNat_of_nonneg ( by linarith : ( 0 : ℤ ) ≤ k ) ], by linarith [ Int.toNat_of_nonneg ( by linarith : ( 0 : ℤ ) ≤ k ) ] ⟩, by rintro ⟨ k, hk, rfl ⟩ ; exact ⟨ ⟨ by linarith, by linarith ⟩, by simp +decide [ parity_simps ] ⟩ ⟩;
    have h_card_filter : (A.filter (fun x => Even x)).card + (A.filter (fun x => ¬Even x)).card = A.card := by
      rw [ Finset.card_filter_add_card_filter_not ];
    omega;
  · grind

/-
Pigeonhole for the pair construction: among 3t+1 candidates,
    at most 3t are blocked by t missing odds, so a good one exists.
-/
lemma exists_good_p (b₁ b₂ b₃ S : ℤ)
    (M : Finset ℤ) (t : ℕ) (hM : M.card ≤ t)
    (candidates : Finset ℤ)
    (h_cand_card : 3 * t + 1 ≤ candidates.card)
    (h_cand_lt : ∀ p ∈ candidates, 2 * p < S) :
    ∃ p ∈ candidates,
      (∀ z ∈ M, b₁ + p ≠ z) ∧ (∀ z ∈ M, b₂ + p ≠ z) ∧ (∀ z ∈ M, b₃ + p ≠ z) ∧
      (∀ z ∈ M, b₁ + (S - p) ≠ z) ∧ (∀ z ∈ M, b₂ + (S - p) ≠ z) ∧
      (∀ z ∈ M, b₃ + (S - p) ≠ z) := by
  -- The total number of blocked candidates is at most $6t$, which is less than or equal to $3t + 1$.
  have h_blocked_card : (Finset.biUnion M (fun z => ({z - b₁, z - b₂, z - b₃, S + b₁ - z, S + b₂ - z, S + b₃ - z} : Finset ℤ))).card ≤ 6 * t := by
    exact le_trans ( Finset.card_biUnion_le ) ( le_trans ( Finset.sum_le_sum fun x hx => show Finset.card _ ≤ 6 by exact le_trans ( Finset.card_insert_le _ _ ) <| by linarith [ Finset.card_insert_le ( x - b₁ ) { x - b₂, x - b₃, S + b₁ - x, S + b₂ - x, S + b₃ - x }, Finset.card_insert_le ( x - b₂ ) { x - b₃, S + b₁ - x, S + b₂ - x, S + b₃ - x }, Finset.card_insert_le ( x - b₃ ) { S + b₁ - x, S + b₂ - x, S + b₃ - x }, Finset.card_insert_le ( S + b₁ - x ) { S + b₂ - x, S + b₃ - x }, Finset.card_insert_le ( S + b₂ - x ) { S + b₃ - x }, Finset.card_singleton ( S + b₃ - x ) ] ) ( by norm_num; linarith ) );
  contrapose! h_blocked_card;
  refine' lt_of_lt_of_le _ ( Finset.card_mono _ );
  rotate_left;
  exact Finset.image ( fun p => S - p ) candidates ∪ Finset.image ( fun p => p ) candidates;
  · simp_all +decide [ Finset.subset_iff ];
    grind +splitImp;
  · rw [ Finset.card_union_of_disjoint ];
    · rw [ Finset.card_image_of_injective, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ] ; linarith;
    · norm_num [ Finset.disjoint_left ];
      exact fun p hp hp' => by linarith [ h_cand_lt p hp, h_cand_lt ( S - p ) hp' ] ;

/-
Pair construction (low half): given 3 even elements in [6t+2, n] and ≤ t missing odds,
    construct 5 elements with all pairwise sums in A.
-/
lemma g5_from_evens_low (n : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n))
    (a₁ a₂ a₃ : ℤ)
    (ha₁A : a₁ ∈ A) (ha₂A : a₂ ∈ A) (ha₃A : a₃ ∈ A)
    (ha_even₁ : Even a₁) (ha_even₂ : Even a₂) (ha_even₃ : Even a₃)
    (ha₁₂ : a₁ < a₂) (ha₂₃ : a₂ < a₃)
    (t : ℕ) (ht : 1 ≤ t)
    (ha₁_lb : (6 : ℤ) * ↑t + 2 ≤ a₁) (ha₃_ub : a₃ ≤ ↑n)
    (h6tn : (6 : ℤ) * ↑t + 6 ≤ ↑n)
    (hmissing : ((Icc (1:ℤ) (2*↑n)).filter (fun x => ¬Even x) \ A).card ≤ t) :
    HasPairwiseSums A 5 := by
  -- same as g5_from_evens_high but with the pair summing to a₃ instead of a₁.
  set b₁ : ℤ := (a₁ + a₂ - a₃) / 2
  set b₂ : ℤ := (a₁ + a₃ - a₂) / 2
  set b₃ : ℤ := (a₂ + a₃ - a₁) / 2;
  obtain ⟨p, hp⟩ : ∃ p : ℤ, p ∈ Finset.filter (fun p : ℤ => ¬Even (p + b₁)) (Finset.Icc (a₃ / 2 - 6 * t - 2) (a₃ / 2 - 1)) ∧ (∀ z ∈ Finset.filter (fun x : ℤ => ¬Even x) (Finset.Icc 1 (2 * n)) \ A, b₁ + p ≠ z) ∧ (∀ z ∈ Finset.filter (fun x : ℤ => ¬Even x) (Finset.Icc 1 (2 * n)) \ A, b₂ + p ≠ z) ∧ (∀ z ∈ Finset.filter (fun x : ℤ => ¬Even x) (Finset.Icc 1 (2 * n)) \ A, b₃ + p ≠ z) ∧ (∀ z ∈ Finset.filter (fun x : ℤ => ¬Even x) (Finset.Icc 1 (2 * n)) \ A, b₁ + (a₃ - p) ≠ z) ∧ (∀ z ∈ Finset.filter (fun x : ℤ => ¬Even x) (Finset.Icc 1 (2 * n)) \ A, b₂ + (a₃ - p) ≠ z) ∧ (∀ z ∈ Finset.filter (fun x : ℤ => ¬Even x) (Finset.Icc 1 (2 * n)) \ A, b₃ + (a₃ - p) ≠ z) := by
    set candidates := Finset.filter (fun p : ℤ => ¬Even (p + b₁)) (Finset.Icc (a₃ / 2 - 6 * t - 2) (a₃ / 2 - 1));
    apply exists_good_p b₁ b₂ b₃ a₃ ((Finset.Icc (1 : ℤ) (2 * n)).filter (fun x => ¬Even x) \ A) t hmissing candidates;
    · rw [ show candidates = Finset.image ( fun k : ℤ => a₃ / 2 - 6 * t - 2 + 2 * k + ( if Even ( ( a₃ / 2 - 6 * t - 2 ) + b₁ ) then 1 else 0 ) ) ( Finset.Icc 0 ( 3 * t ) ) from ?_ ];
      · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
      · ext; simp [candidates];
        constructor;
        · intro h;
          use ( ‹_› - ( a₃ / 2 - 6 * t - 2 ) - if Even ( a₃ / 2 - 6 * t - 2 + b₁ ) then 1 else 0 ) / 2;
          grind;
        · grind;
    · grind;
  use ![b₁, b₂, b₃, p, a₃ - p];
  simp_all +decide [ Fin.forall_fin_succ, Function.Injective, Finset.mem_filter ];
  constructor;
  · refine' ⟨ _, _, _, _, _ ⟩;
    · grind;
    · grind;
    · grind;
    · grind;
    · grind;
  · constructor;
    · grind;
    · grind

/-
Pair construction (high half): given 3 even elements in [n, 2n-6t-2] and ≤ t missing odds,
    construct 5 elements with all pairwise sums in A.
-/
lemma g5_from_evens_high (n : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n))
    (a₁ a₂ a₃ : ℤ)
    (ha₁A : a₁ ∈ A) (ha₂A : a₂ ∈ A) (ha₃A : a₃ ∈ A)
    (ha_even₁ : Even a₁) (ha_even₂ : Even a₂) (ha_even₃ : Even a₃)
    (ha₁₂ : a₁ < a₂) (ha₂₃ : a₂ < a₃)
    (t : ℕ) (ht : 1 ≤ t)
    (ha₁_lb : (↑n : ℤ) ≤ a₁) (ha₃_ub : a₃ ≤ 2 * ↑n - 6 * ↑t - 2)
    (h6tn : (6 : ℤ) * ↑t + 6 ≤ ↑n)
    (hmissing : ((Icc (1:ℤ) (2*↑n)).filter (fun x => ¬Even x) \ A).card ≤ t) :
    HasPairwiseSums A 5 := by
  -- same as lma_iv_upper but with the pair summing to a₁ instead of a₃.
  set b₁ : ℤ := (a₁ + a₂ - a₃) / 2
  set b₂ : ℤ := (a₁ + a₃ - a₂) / 2
  set b₃ : ℤ := (a₂ + a₃ - a₁) / 2;
  obtain ⟨p, hp⟩ : ∃ p : ℤ, p ∈ Finset.filter (fun p : ℤ => ¬Even (p + b₁)) (Finset.Icc (a₁ / 2 - 6 * t - 2) (a₁ / 2 - 1)) ∧ (∀ z ∈ Finset.filter (fun x : ℤ => ¬Even x) (Finset.Icc 1 (2 * n)) \ A, b₁ + p ≠ z) ∧ (∀ z ∈ Finset.filter (fun x : ℤ => ¬Even x) (Finset.Icc 1 (2 * n)) \ A, b₂ + p ≠ z) ∧ (∀ z ∈ Finset.filter (fun x : ℤ => ¬Even x) (Finset.Icc 1 (2 * n)) \ A, b₃ + p ≠ z) ∧ (∀ z ∈ Finset.filter (fun x : ℤ => ¬Even x) (Finset.Icc 1 (2 * n)) \ A, b₁ + (a₁ - p) ≠ z) ∧ (∀ z ∈ Finset.filter (fun x : ℤ => ¬Even x) (Finset.Icc 1 (2 * n)) \ A, b₂ + (a₁ - p) ≠ z) ∧ (∀ z ∈ Finset.filter (fun x : ℤ => ¬Even x) (Finset.Icc 1 (2 * n)) \ A, b₃ + (a₁ - p) ≠ z) := by
    -- Let's choose the set of candidates.
    set candidates := Finset.filter (fun p : ℤ => ¬Even (p + b₁)) (Finset.Icc (a₁ / 2 - 6 * t - 2) (a₁ / 2 - 1));
    -- Apply the lemma exists_good_p with the given parameters.
    apply exists_good_p b₁ b₂ b₃ a₁ ((Finset.Icc (1 : ℤ) (2 * n)).filter (fun x => ¬Even x) \ A) t hmissing candidates;
    · rw [ show candidates = Finset.image ( fun k : ℤ => a₁ / 2 - 6 * t - 2 + 2 * k + ( if Even ( ( a₁ / 2 - 6 * t - 2 ) + b₁ ) then 1 else 0 ) ) ( Finset.Icc 0 ( 3 * t ) ) from ?_ ];
      · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
      · ext; simp [candidates];
        constructor;
        · intro h;
          use ( ‹_› - ( a₁ / 2 - 6 * t - 2 ) - if Even ( a₁ / 2 - 6 * t - 2 + b₁ ) then 1 else 0 ) / 2;
          grind;
        · grind;
    · grind;
  use ![b₁, b₂, b₃, p, a₁ - p];
  simp_all +decide [ Fin.forall_fin_succ, Function.Injective, Finset.mem_filter ];
  constructor;
  · refine' ⟨ _, _, _, _, _ ⟩;
    · grind;
    · grind;
    · grind;
    · grind;
    · grind;
  · constructor;
    · grind;
    · grind

/-- Concentrated subcase: if A has a large subset of even elements
    concentrated in a short interval, use g5upper_case_even. -/
lemma g5upper_conc_edge (A : Finset ℤ)
    (t : ℕ) (ht : 1 ≤ t)
    (E : Finset ℤ) (hE_sub : E ⊆ A)
    (hE_even : ∀ x ∈ E, 2 ∣ x) (hE_pos : ∀ x ∈ E, (2 : ℤ) ≤ x)
    (hE_ne : E.Nonempty)
    (hE_spread : 2 ≤ E.max' hE_ne - E.min' hE_ne)
    (hE_spread_bound : E.max' hE_ne - E.min' hE_ne ≤ 6 * (↑t : ℤ))
    (hE_card : (t : ℝ) / 2 + (120000000 - 1) / 2 - 2 ≤ ↑E.card) :
    HasPairwiseSums A 5 := by
  apply g5upper_case_even A E hE_sub hE_ne hE_even hE_pos hE_spread
  -- Need: (↑E.card : ℝ) > fFun 5 (↑(E.max' hE_ne - E.min' hE_ne))
  calc fFun 5 (↑(E.max' hE_ne - E.min' hE_ne))
      ≤ fFun 5 (6 * ↑t) := by
        apply fFun_mono 5 (by omega) _ _ (by exact_mod_cast hE_spread) (by exact_mod_cast hE_spread_bound)
    _ < 6 * ↑t / 12 + (120000000 - 1) / 2 - 2 := key_ineq _ (by norm_cast; linarith)
    _ = ↑t / 2 + (120000000 - 1) / 2 - 2 := by ring
    _ ≤ ↑E.card := hE_card

lemma nat_div2_cast_ge (n : ℕ) : ((↑n : ℝ) - 1) / 2 ≤ ↑(n / 2) := by
  rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> norm_num ; ring_nf;
  · linarith;
  · omega

/-
Concentrated subcase of the hard case.
-/
lemma g5upper_hard_concentrated (n : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n))
    (t : ℕ) (ht : 1 ≤ t)
    (A₀ : Finset ℤ) (hA₀_def : A₀ = A.filter (fun x => Even x))
    (ht_card : t + (120000000 - 1) ≤ A₀.card)
    (A_mid : Finset ℤ)
    (hA_mid_def : A_mid = A₀.filter (fun x => 6 * (↑t : ℤ) + 2 ≤ x ∧ x ≤ 2 * ↑n - 6 * ↑t - 2))
    (hmid : A_mid.card < 5) :
    HasPairwiseSums A 5 := by
  -- Define edge sets
  set E_low := A₀.filter (fun x => x < 6 * (↑t : ℤ) + 2) with hE_low_def
  set E_high := A₀.filter (fun x => 2 * (↑n : ℤ) - 6 * ↑t - 2 < x) with hE_high_def
  -- Count: A₀ ⊆ E_low ∪ A_mid ∪ E_high
  have h_count : A₀.card ≤ E_low.card + A_mid.card + E_high.card := by
    -- Since $E_{\text{low}}$, $A_{\text{mid}}$, and $E_{\text{high}}$ are disjoint and their union is $A₀$, we can apply the cardinality addition principle.
    have h_union : A₀ = E_low ∪ A_mid ∪ E_high := by
      grind;
    grind
  -- Edge sum bound
  have h_sum : t + 120000000 - 5 ≤ E_low.card + E_high.card := by omega
  -- Pigeonhole: one edge has ≥ (t + 120000000 - 4) / 2 elements
  by_cases hlow : (t + 120000000 - 4) / 2 ≤ E_low.card
  · -- Low edge case
    have hE_sub : E_low ⊆ A := (Finset.filter_subset _ _).trans (hA₀_def ▸ Finset.filter_subset _ _)
    have hE_even : ∀ x ∈ E_low, 2 ∣ x := by
      intro x hx
      have hx' := hA₀_def ▸ Finset.filter_subset _ _ hx
      exact (Finset.mem_filter.mp hx').2.two_dvd
    have hE_pos : ∀ x ∈ E_low, (2 : ℤ) ≤ x := by
      intro x hx
      have h1 := (Finset.mem_Icc.mp (hA (hE_sub hx))).1
      obtain ⟨k, rfl⟩ := hE_even x hx
      omega
    have hE_ne : E_low.Nonempty := Finset.card_pos.mp (by omega)
    have hE_spread : 2 ≤ E_low.max' hE_ne - E_low.min' hE_ne := by
      by_contra h
      push Not at h
      have hall : ∀ x ∈ E_low, x = E_low.min' hE_ne := by
        intro x hx
        have h1 := Finset.min'_le E_low x hx
        have h2 := Finset.le_max' E_low x hx
        obtain ⟨k, hk⟩ := hE_even x hx
        obtain ⟨m, hm⟩ := hE_even _ (Finset.min'_mem _ _)
        omega
      have : E_low.card ≤ 1 := Finset.card_le_one.mpr (fun x hx y hy => by rw [hall x hx, hall y hy])
      omega
    have hE_spread_bound : E_low.max' hE_ne - E_low.min' hE_ne ≤ 6 * (↑t : ℤ) := by
      have hmax : E_low.max' hE_ne ≤ 6 * (↑t : ℤ) := by
        have hm := (Finset.mem_filter.mp (Finset.max'_mem E_low hE_ne)).2
        obtain ⟨k, hk⟩ := hE_even _ (Finset.max'_mem _ _)
        omega
      linarith [hE_pos (E_low.min' hE_ne) (Finset.min'_mem E_low hE_ne)]
    have hE_card : (t : ℝ) / 2 + (120000000 - 1) / 2 - 2 ≤ ↑E_low.card := by
      have h1 : (((t + 120000000 - 4) / 2 : ℕ) : ℝ) ≤ (E_low.card : ℝ) := by exact_mod_cast hlow
      have h2 := nat_div2_cast_ge (t + 120000000 - 4)
      push_cast at h1 h2 ⊢
      linarith
    exact g5upper_conc_edge A t ht E_low hE_sub hE_even hE_pos hE_ne hE_spread hE_spread_bound hE_card
  · -- High edge case
    push Not at hlow
    have hhigh : (t + 120000000 - 4) / 2 ≤ E_high.card := by omega
    have hE_sub : E_high ⊆ A := (Finset.filter_subset _ _).trans (hA₀_def ▸ Finset.filter_subset _ _)
    have hE_even : ∀ x ∈ E_high, 2 ∣ x := by
      intro x hx
      have hx' := hA₀_def ▸ Finset.filter_subset _ _ hx
      exact (Finset.mem_filter.mp hx').2.two_dvd
    have hE_pos : ∀ x ∈ E_high, (2 : ℤ) ≤ x := by
      intro x hx
      have h1 := (Finset.mem_Icc.mp (hA (hE_sub hx))).1
      obtain ⟨k, rfl⟩ := hE_even x hx
      omega
    have hE_ne : E_high.Nonempty := Finset.card_pos.mp (by omega)
    have hE_spread : 2 ≤ E_high.max' hE_ne - E_high.min' hE_ne := by
      by_contra h
      push Not at h
      have hall : ∀ x ∈ E_high, x = E_high.min' hE_ne := by
        intro x hx
        have h1 := Finset.min'_le E_high x hx
        have h2 := Finset.le_max' E_high x hx
        obtain ⟨k, hk⟩ := hE_even x hx
        obtain ⟨m, hm⟩ := hE_even _ (Finset.min'_mem _ _)
        omega
      have : E_high.card ≤ 1 := Finset.card_le_one.mpr (fun x hx y hy => by rw [hall x hx, hall y hy])
      omega
    have hE_spread_bound : E_high.max' hE_ne - E_high.min' hE_ne ≤ 6 * (↑t : ℤ) := by
      have hmax : E_high.max' hE_ne ≤ 2 * (↑n : ℤ) :=
        (Finset.mem_Icc.mp (hA (hE_sub (Finset.max'_mem _ _)))).2
      have hmin : 2 * (↑n : ℤ) - 6 * ↑t ≤ E_high.min' hE_ne := by
        have hm := (Finset.mem_filter.mp (Finset.min'_mem E_high hE_ne)).2
        obtain ⟨k, hk⟩ := hE_even _ (Finset.min'_mem _ _)
        omega
      linarith
    have hE_card : (t : ℝ) / 2 + (120000000 - 1) / 2 - 2 ≤ ↑E_high.card := by
      have h1 : (((t + 120000000 - 4) / 2 : ℕ) : ℝ) ≤ (E_high.card : ℝ) := by exact_mod_cast hhigh
      have h2 := nat_div2_cast_ge (t + 120000000 - 4)
      push_cast at h1 h2 ⊢
      linarith
    exact g5upper_conc_edge A t ht E_high hE_sub hE_even hE_pos hE_ne hE_spread hE_spread_bound hE_card

/-- The hard case of g5upper: t ≥ 1 extra even elements beyond c = 120000000-1. -/
lemma g5upper_hard_case (n : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n))
    (hcard : n + 120000000-1 ≤ A.card)
    (heven_lt : (A.filter (fun x => Even x)).card < n / 6 + (120000000-1))
    (heven_gt : 120000000-1 < (A.filter (fun x => Even x)).card) :
    HasPairwiseSums A 5 := by
  set t := (A.filter (fun x => Even x)).card - (120000000 - 1)
  have ht : 1 ≤ t := Nat.sub_pos_of_lt heven_gt
  have h6tn : (6 : ℤ) * ↑t + 6 ≤ ↑n := by omega
  have hmissing : ((Icc (1:ℤ) (2*↑n)).filter (fun x => ¬Even x) \ A).card ≤ t :=
    missing_odds_le n A hA hcard heven_gt
  set A₀ := A.filter (fun x => Even x)
  set A_mid := A₀.filter (fun x => 6 * (↑t : ℤ) + 2 ≤ x ∧ x ≤ 2 * ↑n - 6 * ↑t - 2)
  by_cases hmid : A_mid.card ≥ 5
  · -- Spread case: ≥ 5 evens in middle range. Find 3 in one half.
    obtain ⟨b, hbm, hbs⟩ : ∃ b : Fin 5 → ℤ, (∀ i, b i ∈ A_mid) ∧ StrictMono b :=
      ⟨fun i => A_mid.orderEmbOfFin rfl ⟨i, by omega⟩,
       fun i => by simp +decide, by simp +decide [StrictMono]⟩
    by_cases hle : b 2 ≤ ↑n
    · exact g5_from_evens_low n A hA (b 0) (b 1) (b 2)
        (Finset.mem_filter.mp (Finset.mem_filter.mp (hbm 0) |>.1) |>.1)
        (Finset.mem_filter.mp (Finset.mem_filter.mp (hbm 1) |>.1) |>.1)
        (Finset.mem_filter.mp (Finset.mem_filter.mp (hbm 2) |>.1) |>.1)
        (Finset.mem_filter.mp (hbm 0 |> Finset.mem_filter.mp |>.1) |>.2)
        (Finset.mem_filter.mp (hbm 1 |> Finset.mem_filter.mp |>.1) |>.2)
        (Finset.mem_filter.mp (hbm 2 |> Finset.mem_filter.mp |>.1) |>.2)
        (hbs (by decide)) (hbs (by decide)) t ht
        (Finset.mem_filter.mp (hbm 0) |>.2.1) hle h6tn hmissing
    · push Not at hle
      exact g5_from_evens_high n A hA (b 2) (b 3) (b 4)
        (Finset.mem_filter.mp (Finset.mem_filter.mp (hbm 2) |>.1) |>.1)
        (Finset.mem_filter.mp (Finset.mem_filter.mp (hbm 3) |>.1) |>.1)
        (Finset.mem_filter.mp (Finset.mem_filter.mp (hbm 4) |>.1) |>.1)
        (Finset.mem_filter.mp (hbm 2 |> Finset.mem_filter.mp |>.1) |>.2)
        (Finset.mem_filter.mp (hbm 3 |> Finset.mem_filter.mp |>.1) |>.2)
        (Finset.mem_filter.mp (hbm 4 |> Finset.mem_filter.mp |>.1) |>.2)
        (hbs (by decide)) (hbs (by decide)) t ht
        (by linarith) (Finset.mem_filter.mp (hbm 4) |>.2.2) h6tn hmissing
  · -- Concentrated case: ≤ 4 evens in middle. Use g5upper_case_even on an edge.
    push Not at hmid
    have htcard : t + (120000000 - 1) ≤ A₀.card := le_of_eq (Nat.sub_add_cancel (le_of_lt heven_gt))
    exact g5upper_hard_concentrated n A hA t ht A₀ rfl htcard A_mid rfl hmid

/-
The case t=0: all odds are in A, use g5special.
-/
lemma g5upper_all_odds (n : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n))
    (hcard : n + 120000000-1 ≤ A.card)
    (hn : 120000000-1 ≤ n)
    (ht0 : (A.filter (fun x => Even x)).card = 120000000-1) :
    HasPairwiseSums A 5 := by
  -- Since $|A| = n + 120000000 - 1$, we have $|A \setminus A₀| = n$.
  have hA_odd_card : (A.filter (fun x => ¬Even x)).card = n := by
    have hA_odd_card : (A.filter (fun x => ¬Even x)).card + (A.filter (fun x => Even x)).card = A.card := by
      rw [ add_comm, Finset.card_filter_add_card_filter_not ];
    have hA_odd_card : (A.filter (fun x => ¬Even x)).card ≤ n := by
      have hA_odd_card : (A.filter (fun x => ¬Even x)).card ≤ Finset.card (Finset.image (fun k : ℕ => 2 * k + 1 : ℕ → ℤ) (Finset.range n)) := by
        refine Finset.card_le_card ?_;
        intro x hx; have := hA ( Finset.mem_filter.mp hx |>.1 ) ; simp_all +decide [ parity_simps ] ;
        exact hx.2.elim fun k hk => ⟨ Int.toNat k, by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k ) ], by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k ) ] ⟩;
      exact hA_odd_card.trans ( Finset.card_image_le.trans ( by simp ) );
    grind;
  convert g5special n A hA _ _;
  · have hA_odd_subset : A.filter (fun x => ¬Even x) = Finset.image (fun k : ℕ => 2 * k + 1 : ℕ → ℤ) (Finset.range n) := by
      refine' Finset.eq_of_subset_of_card_le _ _;
      · intro x hx; have := hA ( Finset.mem_filter.mp hx |>.1 ) ; simp_all +decide [ parity_simps ] ;
        rcases hx.2 with ⟨ k, rfl ⟩ ; exact ⟨ Int.toNat k, by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k ) ], by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ k ) ] ⟩ ;
      · grind;
    simp_all +decide [ Finset.ext_iff ];
    exact fun x hx₁ hx₂ hx₃ => by obtain ⟨ k, hk₁, rfl ⟩ := Int.odd_iff.mpr hx₃; exact hA_odd_subset _ |>.2 ⟨ k.natAbs, by linarith [ abs_of_nonneg ( by linarith : 0 ≤ k ) ], by simp +decide [ abs_of_nonneg ( by linarith : 0 ≤ k ) ] ⟩ |>.1;
  · omega

/-
Even elements count is at least c when |A| ≥ n+c.
-/
lemma even_count_ge_c (n : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n))
    (hcard : n + 120000000-1 ≤ A.card) :
    120000000-1 ≤ (A.filter (fun x => Even x)).card := by
  -- The number of odd elements in A is at most n (since odd elements of Icc 1 (2n) are exactly {1,3,...,2n-1}, which has n elements, and A ⊆ Icc 1 (2n)).
  have h_odd_le_n : (A.filter (fun x => ¬Even x)).card ≤ n := by
    -- The set of odd numbers in $A$ is a subset of $\{1, 3, 5, \ldots, 2n-1\}$, which has exactly $n$ elements.
    have h_odd_subset : (A.filter (fun x => ¬Even x)) ⊆ Finset.image (fun k : ℕ => 2 * k + 1 : ℕ → ℤ) (Finset.range n) := by
      intro x hx; simp_all +decide [ Finset.subset_iff ];
      obtain ⟨ k, rfl ⟩ := hx.2; exact ⟨ Int.toNat k, by linarith [ Int.toNat_of_nonneg ( by linarith [ hA hx.1 ] : ( 0 : ℤ ) ≤ k ), hA hx.1 ], by linarith [ Int.toNat_of_nonneg ( by linarith [ hA hx.1 ] : ( 0 : ℤ ) ≤ k ) ] ⟩ ;
    exact le_trans ( Finset.card_le_card h_odd_subset ) ( Finset.card_image_le.trans ( by simp ) );
  rw [ Finset.filter_not ] at h_odd_le_n;
  grind

/-- The remaining case of g5upper_aux: few even elements (< n/6 + c). -/
lemma g5upper_aux_few_evens (n : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n))
    (hcard : n + 120000000-1 ≤ A.card)
    (hn : 120000000-1 ≤ n)
    (hec : (A.filter (fun x => Even x)).card < n / 6 + (120000000-1)) :
    HasPairwiseSums A 5 := by
  have hge := even_count_ge_c n A hA hcard
  by_cases ht0 : (A.filter (fun x => Even x)).card = 120000000-1
  · exact g5upper_all_odds n A hA hcard hn ht0
  · exact g5upper_hard_case n A hA hcard hec (Nat.lt_of_le_of_ne hge (Ne.symm ht0))

lemma g5upper_aux (n : ℕ) (A : Finset ℤ)
    (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n))
    (hcard : n + 120000000-1 ≤ A.card) :
    HasPairwiseSums A 5 := by
  by_cases hn : n < 120000000-1
  · exfalso
    have h1 := Finset.card_le_card hA
    have h2 : (Icc (1:ℤ) (2*↑n)).card = 2*n := by rw [Int.card_Icc]; omega
    omega
  · push Not at hn
    by_cases hec : n / 6 + (120000000 - 1) ≤ (A.filter (fun x => Even x)).card
    · exact g5upper_aux_ces n A hA hn hec
    · push Not at hec
      exact g5upper_aux_few_evens n A hA hcard hn hec

/-- g₅(n) < 1.2 * 10^8 for all n ∈ ℕ. -/
theorem g5upper (n : ℕ) : gFun 5 n < 120000000 := by
  unfold gFun
  have hmem : (120000000 - 1 : ℕ) ∈ {m : ℕ | ∀ (A : Finset ℤ), A ⊆ Icc (1 : ℤ) (2 * ↑n) →
      n + m ≤ A.card → HasPairwiseSums A 5} := by
    intro A hA hcard
    exact g5upper_aux n A hA (by omega)
  exact lt_of_le_of_lt (Nat.sInf_le hmem) (by norm_num)

#print axioms g5upper
-- 'Erdos866b.g5upper' depends on axioms: [propext, Classical.choice, Quot.sound]


/-! ## h_k(n) ≤ 4n^{1-1/2^{k-2}} for all large enough n -/

/-- F_k(x) for k ≥ 3, the positive version of f_k.
    F_3(x) = 2√(x/2) + 4(x/2)^(1/4) + 11
    F_k(x) = √(2x F_{k-1}(x) + 1/4) + 1/2  for k ≥ 4
    For k < 3, we set F_k(x) = 0. -/
noncomputable def fFunPos : ℕ → ℝ → ℝ
  | 0, _ | 1, _ | 2, _ => 0
  | 3, x => 2 * Real.sqrt (x / 2) + 4 * (x / 2) ^ ((1:ℝ)/4) + 11
  | n + 4, x => Real.sqrt (2 * x * fFunPos (n + 3) x + 1/4) + 1/2

/-- HasPosSubsetSumsContaining A k: there exist b_0, …, b_{k-1} all positive with
    b_i pairwise distinct for i ≥ 1, and every subset sum that includes b_0 lies in A. -/
def HasPosSubsetSumsContaining (A : Finset ℤ) : (k : ℕ) → Prop
  | 0 => True
  | k + 1 => ∃ b : Fin (k + 1) → ℤ,
    (∀ i : Fin (k + 1), 0 < b i) ∧
    (∀ i j : Fin (k + 1), 1 ≤ i.val → 1 ≤ j.val → i ≠ j → b i ≠ b j) ∧
    (∀ S : Finset (Fin (k + 1)), (0 : Fin (k + 1)) ∈ S → ∑ i ∈ S, b i ∈ A)

lemma pos_subsetsums_to_pairwise (A : Finset ℤ) (k : ℕ) (hk : 3 ≤ k)
    (heven : ∀ a ∈ A, (2 : ℤ) ∣ a)
    (hSSC : HasPosSubsetSumsContaining A k) :
    HasPosPairwiseSums A k := by
  rcases k with ( _ | _ | k ) <;> simp_all +decide [ HasPosSubsetSumsContaining ];
  obtain ⟨ b, hb₁, hb₂, hb₃ ⟩ := hSSC;
  have hb_pos : 0 < b 0 := hb₁ 0;
  have hb_even : 2 ∣ b 0 := by
    simpa using heven _ ( hb₃ { 0 } ( by simp +decide ) );
  use fun i => if i = 0 then b 0 / 2 else b 0 / 2 + b i; (
  refine' ⟨ _, _, _ ⟩;
  · intro i j; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp_all +decide ;
    · exact fun h => absurd h ( ne_of_gt ( hb₁ j ) );
    · linarith [ hb₁ i ];
    · exact fun h => Classical.not_not.1 fun hi' => hb₂ i j ( Fin.pos_iff_ne_zero.2 hi ) ( Fin.pos_iff_ne_zero.2 hj ) hi' h;
  · grind +ring;
  · intro i j hij; convert hb₃ { 0, i, j } ( by aesop ) using 1; simp +decide ; ring_nf;
    grind);

lemma ceslemprelim_pos_base3 (A₀ : Finset ℤ) (hne : A₀.Nonempty)
    (heven : ∀ a ∈ A₀, 2 ∣ a) (hpos : ∀ a ∈ A₀, 2 ≤ a)
    (hrange : 2 ≤ A₀.max' hne - A₀.min' hne)
    (hcard : (A₀.card : ℝ) > fFunPos 3 (↑(A₀.max' hne - A₀.min' hne))) :
    HasPosSubsetSumsContaining A₀ 3 := by
  -- Let's denote the spread as `N` and the halves of the elements as `B`.
  set N := (A₀.max' hne - A₀.min' hne) / 2
  set B := A₀.image (fun x => x / 2);
  -- Since $|B| > 2\sqrt{N} + 4N^{1/4} + 11$, there exist at least 3 pairs in $B$ with the same difference.
  have h_pairs : ∃ Δ : ℤ, 0 < Δ ∧ (B.filter (fun x => x + Δ ∈ B)).card ≥ 3 := by
    have h_pairs : ∑ Δ ∈ Finset.Icc 1 N, (B.filter (fun x => x + Δ ∈ B)).card ≥ (B.card : ℝ) * ((B.card : ℝ) - 1) / 2 := by
      have h_pairs : ∑ Δ ∈ Finset.Icc 1 N, (B.filter (fun x => x + Δ ∈ B)).card ≥ (∑ x ∈ B, ∑ y ∈ B, if x < y then 1 else 0) := by
        have h_pairs : ∀ x ∈ B, ∀ y ∈ B, x < y → ∃ Δ ∈ Finset.Icc 1 N, x + Δ = y := by
          intros x hx y hy hxy
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
          have h_diff : 1 ≤ (b / 2) - (a / 2) ∧ (b / 2) - (a / 2) ≤ N := by
            exact ⟨ by linarith, Int.le_ediv_of_mul_le ( by norm_num ) ( by linarith [ Int.ediv_mul_cancel ( heven a ha ), Int.ediv_mul_cancel ( heven b hb ), Finset.min'_le _ _ ha, Finset.le_max' _ _ ha, Finset.min'_le _ _ hb, Finset.le_max' _ _ hb ] ) ⟩;
          exact ⟨ b / 2 - a / 2, Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩, by ring ⟩;
        have h_pairs : ∀ x ∈ B, ∀ y ∈ B, x < y → ∑ Δ ∈ Finset.Icc 1 N, (if x + Δ = y then 1 else 0) ≥ 1 := by
          intro x hx y hy hxy; obtain ⟨ Δ, hΔ₁, hΔ₂ ⟩ := h_pairs x hx y hy hxy; exact le_trans ( by aesop ) ( Finset.single_le_sum ( fun Δ _ => by positivity ) hΔ₁ ) ;
        have h_pairs : ∑ x ∈ B, ∑ y ∈ B, (if x < y then 1 else 0) ≤ ∑ Δ ∈ Finset.Icc 1 N, ∑ x ∈ B, ∑ y ∈ B, (if x + Δ = y then 1 else 0) := by
          have h_pairs : ∑ x ∈ B, ∑ y ∈ B, (if x < y then 1 else 0) ≤ ∑ x ∈ B, ∑ y ∈ B, ∑ Δ ∈ Finset.Icc 1 N, (if x + Δ = y then 1 else 0) := by
            exact Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => by specialize h_pairs x hx y hy; aesop;
          convert h_pairs using 1;
          exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm );
        refine le_trans h_pairs ?_;
        simp +decide;
      have h_pairs : ∑ x ∈ B, ∑ y ∈ B, (if x < y then 1 else 0) = (B.card * (B.card - 1)) / 2 := by
        have h_pairs : ∑ x ∈ B, ∑ y ∈ B, (if x < y then 1 else 0) = ∑ x ∈ B, ∑ y ∈ B, (if x > y then 1 else 0) := by
          rw [ Finset.sum_comm ];
        have h_pairs : ∑ x ∈ B, ∑ y ∈ B, (if x < y then 1 else 0) + ∑ x ∈ B, ∑ y ∈ B, (if x > y then 1 else 0) + ∑ x ∈ B, ∑ y ∈ B, (if x = y then 1 else 0) = B.card * B.card := by
          simp +decide only [← sum_add_distrib];
          rw [ Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_ ];
          rotate_left;
          use fun x y => 1;
          · grind;
          · norm_num;
        simp_all +decide;
        exact Eq.symm ( Nat.div_eq_of_eq_mul_left zero_lt_two ( by nlinarith only [ Nat.sub_add_cancel ( show 1 ≤ Finset.card B from Finset.card_pos.mpr ⟨ _, Finset.mem_image_of_mem _ ( Finset.min'_mem _ hne ) ⟩ ), h_pairs ] ) );
      rcases k : Finset.card B with ( _ | _ | k ) <;> simp_all +decide;
      · exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _;
      · rw [ div_le_iff₀ ] <;> norm_cast ; nlinarith [ Nat.div_mul_cancel ( show 2 ∣ ( ‹_› + 1 + 1 ) * ( ‹_› + 1 ) from Nat.dvd_of_mod_eq_zero ( by norm_num [ Nat.add_mod, Nat.mod_two_of_bodd ] ) ) ];
    have h_card_B : (B.card : ℝ) > 2 * Real.sqrt N + 4 * N ^ ((1:ℝ)/4) + 11 := by
      rw [ Finset.card_image_of_injOn ];
      · refine lt_of_le_of_lt ?_ hcard;
        rw [ show ( A₀.max' hne - A₀.min' hne : ℤ ) = 2 * N by rw [ Int.mul_ediv_cancel' ] ; exact even_iff_two_dvd.mp ( by exact even_iff_two_dvd.mpr ( by exact Int.dvd_of_emod_eq_zero ( by rw [ Int.sub_emod, Int.emod_eq_zero_of_dvd ( heven _ <| Finset.max'_mem _ _ ), Int.emod_eq_zero_of_dvd ( heven _ <| Finset.min'_mem _ _ ) ] ; norm_num ) ) ) ] ; norm_num [ fFunPos ];
      · exact fun x hx y hy hxy => by linarith [ Int.ediv_mul_cancel ( heven x hx ), Int.ediv_mul_cancel ( heven y hy ) ] ;
    contrapose! h_pairs;
    refine' lt_of_le_of_lt ( Nat.cast_le.mpr <| Finset.sum_le_sum fun x hx => Nat.le_of_lt_succ <| h_pairs x <| Finset.mem_Icc.mp hx |>.1 ) _ ; norm_num;
    rcases N with ( _ | _ | N ) <;> norm_num at *;
    · rename_i k;
      rcases k with ( _ | _ | k ) <;> norm_num at *;
      · exact mul_pos ( Nat.cast_pos.mpr ( pos_of_gt h_card_B ) ) ( sub_pos.mpr ( Nat.one_lt_cast.mpr ( lt_of_le_of_lt ( by norm_num ) h_card_B ) ) );
      · nlinarith [ show ( B.card : ℝ ) ≥ 18 by exact_mod_cast h_card_B ];
      · nlinarith [ show 1 ≤ Real.sqrt ( k + 1 + 1 ) by exact Real.le_sqrt_of_sq_le ( by linarith ), show 1 ≤ ( k + 1 + 1 : ℝ ) ^ ( 1 / 4 : ℝ ) by exact Real.one_le_rpow ( by linarith ) ( by norm_num ), Real.mul_self_sqrt ( show 0 ≤ ( k : ℝ ) + 1 + 1 by linarith ) ];
    · norm_num [ Real.rpow_def_of_neg ] at h_card_B;
      nlinarith [ show 0 < Real.cos ( 1 / 4 * Real.pi ) by exact Real.cos_pos_of_mem_Ioo ⟨ by linarith [ Real.pi_pos ], by linarith [ Real.pi_pos ] ⟩ ];
    · exact mul_pos ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ⟨ _, Finset.mem_image_of_mem _ ( Finset.min'_mem _ hne ) ⟩ ) ) ( sub_pos.mpr ( Nat.one_lt_cast.mpr ( Finset.one_lt_card.mpr ⟨ _, Finset.mem_image_of_mem _ ( Finset.min'_mem _ hne ), _, Finset.mem_image_of_mem _ ( Finset.max'_mem _ hne ), by linarith [ hpos _ ( Finset.min'_mem _ hne ), hpos _ ( Finset.max'_mem _ hne ), Int.ediv_mul_cancel ( heven _ ( Finset.min'_mem _ hne ) ), Int.ediv_mul_cancel ( heven _ ( Finset.max'_mem _ hne ) ) ] ⟩ ) ) );
  -- Let's obtain such a Δ and the corresponding pairs in B.
  obtain ⟨Δ, hΔ_pos, hΔ_pairs⟩ := h_pairs
  obtain ⟨a₁, a₂, a₃, ha₁, ha₂, ha₃, ha₁₂, ha₂₃⟩ : ∃ a₁ a₂ a₃ : ℤ, a₁ ∈ B ∧ a₂ ∈ B ∧ a₃ ∈ B ∧ a₁ < a₂ ∧ a₂ < a₃ ∧ a₁ + Δ ∈ B ∧ a₂ + Δ ∈ B ∧ a₃ + Δ ∈ B := by
    obtain ⟨ s, hs ⟩ := Finset.exists_subset_card_eq hΔ_pairs;
    -- Since $s$ is a subset of $\{x \in B \mid x + \Delta \in B\}$ with cardinality 3, we can choose any three elements from $s$.
    obtain ⟨a₁, a₂, a₃, ha₁, ha₂, ha₃⟩ : ∃ a₁ a₂ a₃ : ℤ, a₁ ∈ s ∧ a₂ ∈ s ∧ a₃ ∈ s ∧ a₁ < a₂ ∧ a₂ < a₃ := by
      rcases Finset.card_eq_three.mp hs.2 with ⟨ a₁, a₂, a₃, ha₁, ha₂, ha₃ ⟩ ; cases lt_trichotomy a₁ a₂ <;> cases lt_trichotomy a₂ a₃ <;> cases lt_trichotomy a₁ a₃ <;> aesop;
    exact ⟨ a₁, a₂, a₃, Finset.mem_filter.mp ( hs.1 ha₁ ) |>.1, Finset.mem_filter.mp ( hs.1 ha₂ ) |>.1, Finset.mem_filter.mp ( hs.1 ha₃.1 ) |>.1, ha₃.2.1, ha₃.2.2, Finset.mem_filter.mp ( hs.1 ha₁ ) |>.2, Finset.mem_filter.mp ( hs.1 ha₂ ) |>.2, Finset.mem_filter.mp ( hs.1 ha₃.1 ) |>.2 ⟩;
  -- Consider two cases: $a₂ \neq a₁ + Δ$ or $a₂ = a₁ + Δ$.
  by_cases h_case : a₂ = a₁ + Δ;
  · use ![2 * a₁, 2 * (a₃ - a₁), 2 * Δ];
    simp_all +decide [ Fin.forall_fin_succ ];
    refine' ⟨ ⟨ _, _ ⟩, ⟨ _, _ ⟩, _ ⟩ <;> try linarith;
    · grind;
    · intro S hS; fin_cases S <;> simp_all +decide ;
      · grind;
      · grind;
      · grind;
      · obtain ⟨ x, hx, hx' ⟩ := Finset.mem_image.mp ha₃; obtain ⟨ y, hy, hy' ⟩ := Finset.mem_image.mp ha₂₃.2.2.2; use by convert hy using 1; linarith [ Int.ediv_mul_cancel ( heven _ hx ), Int.ediv_mul_cancel ( heven _ hy ) ] ;
  · -- In this case, we can choose $b₀ = 2a₁$, $b₁ = 2(a₂ - a₁)$, and $b₂ = 2Δ$.
    use ![2 * a₁, 2 * (a₂ - a₁), 2 * Δ];
    simp_all +decide [Fin.forall_fin_succ];
    refine' ⟨ _, _, _ ⟩;
    · grind;
    · grind;
    · intro S hS; fin_cases S <;> simp_all +decide ;
      · rw [ Finset.mem_image ] at ha₁; obtain ⟨ x, hx, rfl ⟩ := ha₁; specialize heven x hx; obtain ⟨ k, hk ⟩ := heven; aesop;
      · rw [ Finset.mem_image ] at ha₂; obtain ⟨ x, hx, rfl ⟩ := ha₂; convert hx using 1; linarith [ Int.ediv_mul_cancel ( heven x hx ) ] ;
      · grind;
      · grind +revert

private lemma fFunPos_ge_one_early (k : ℕ) (hk : 3 ≤ k) (x : ℝ) (hx : 2 ≤ x) :
    1 ≤ fFunPos k x := by
  induction k, Nat.succ_le_iff.mpr hk using Nat.le_induction with
  | base =>
    unfold fFunPos
    norm_num at *
    exact le_add_of_nonneg_of_le ( by positivity ) ( by norm_num );
  | succ k hk ih =>
    unfold fFunPos
    norm_num at *
    rcases k with ( _ | _ | _ | k ) <;> norm_num at *;
    exact le_add_of_le_of_nonneg ( Real.le_sqrt_of_sq_le ( by nlinarith ) ) ( by norm_num )

private lemma fFunPos_mono_early (k : ℕ) (hk : 3 ≤ k) (x y : ℝ)
    (hx : 2 ≤ x) (hxy : x ≤ y) :
    fFunPos k x ≤ fFunPos k y := by
  induction k, Nat.succ_le_iff.mpr hk using Nat.le_induction generalizing x y with
  | base =>
    unfold fFunPos; norm_num; gcongr;
  | succ k hk ih =>
    rcases k with ( _ | _ | _ | k ) <;> norm_num [ fFunPos ] at *;
    gcongr;
    · exact le_trans ( by norm_num ) ( fFunPos_ge_one_early _ ( by linarith ) _ ( by linarith ) );
    · linarith;
    · solve_by_elim

lemma ceslemgeneral_pos_pigeonhole_strong (k : ℕ) (hk : 4 ≤ k)
    (A₀ : Finset ℤ) (hne : A₀.Nonempty)
    (heven : ∀ a ∈ A₀, 2 ∣ a)
    (hrange : 2 ≤ A₀.max' hne - A₀.min' hne)
    (hcard : (A₀.card : ℝ) > fFunPos k (↑(A₀.max' hne - A₀.min' hne))) :
    ∃ d : ℤ, 2 ≤ d ∧ d ≤ A₀.max' hne - A₀.min' hne ∧ (2 : ℤ) ∣ d ∧
      ((A₀.filter (fun a => a + d ∈ A₀)).card : ℝ) >
        2 * fFunPos (k - 1) (↑(A₀.max' hne - A₀.min' hne)) := by
  revert A₀ hne heven hrange hcard;
  intro A₀ hne heven hrange hcard
  have h_pigeonhole : ∑ d ∈ Finset.filter (fun d => 2 ∣ d ∧ 2 ≤ d ∧ d ≤ A₀.max' hne - A₀.min' hne) (Finset.Icc 2 (A₀.max' hne - A₀.min' hne)), (Finset.filter (fun a => a + d ∈ A₀) A₀).card ≥ A₀.card * (A₀.card - 1) / 2 := by
    have h_pigeonhole : ∑ d ∈ Finset.filter (fun d => 2 ∣ d ∧ 2 ≤ d ∧ d ≤ A₀.max' hne - A₀.min' hne) (Finset.Icc 2 (A₀.max' hne - A₀.min' hne)), (Finset.filter (fun a => a + d ∈ A₀) A₀).card ≥ Finset.card (Finset.filter (fun p => p.1 < p.2) (A₀ ×ˢ A₀)) := by
      have h_pigeonhole : Finset.filter (fun p => p.1 < p.2) (A₀ ×ˢ A₀) ⊆ Finset.biUnion (Finset.filter (fun d => 2 ∣ d ∧ 2 ≤ d ∧ d ≤ A₀.max' hne - A₀.min' hne) (Finset.Icc 2 (A₀.max' hne - A₀.min' hne))) (fun d => Finset.image (fun a => (a, a + d)) (Finset.filter (fun a => a + d ∈ A₀) A₀)) := by
        intro p hp; simp_all +decide ;
        refine' ⟨ p.2 - p.1, _, p.1, _, _ ⟩ <;> simp_all +decide [ ← even_iff_two_dvd, parity_simps ];
        exact ⟨ by obtain ⟨ m, hm ⟩ := heven p.1 hp.1.1; obtain ⟨ n, hn ⟩ := heven p.2 hp.1.2; omega, by linarith [ Finset.le_max' _ _ hp.1.1, Finset.le_max' _ _ hp.1.2, Finset.min'_le _ _ hp.1.1, Finset.min'_le _ _ hp.1.2 ] ⟩;
      refine le_trans ( Finset.card_le_card h_pigeonhole ) ?_;
      exact le_trans ( Finset.card_biUnion_le ) ( Finset.sum_le_sum fun x hx => Finset.card_image_le );
    have h_pigeonhole : Finset.card (Finset.filter (fun p => p.1 < p.2) (A₀ ×ˢ A₀)) = Finset.card (Finset.powersetCard 2 A₀) := by
      refine' Finset.card_bij ( fun p hp => { p.1, p.2 } ) _ _ _ <;> simp +contextual [ Finset.mem_powersetCard ];
      · grind;
      · simp +contextual [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
        intros; omega;
      · intro b hb hb'; rw [ Finset.card_eq_two ] at hb'; obtain ⟨ a, b, hab, rfl ⟩ := hb'; cases lt_trichotomy a b <;> aesop;
    simp_all +decide [ Nat.choose_two_right ];
  contrapose! hcard;
  have h_sum_bound : ∑ d ∈ Finset.filter (fun d => 2 ∣ d ∧ 2 ≤ d ∧ d ≤ A₀.max' hne - A₀.min' hne) (Finset.Icc 2 (A₀.max' hne - A₀.min' hne)), (Finset.filter (fun a => a + d ∈ A₀) A₀).card ≤ (A₀.max' hne - A₀.min' hne) * fFunPos (k - 1) (A₀.max' hne - A₀.min' hne) := by
    have h_sum_bound : ∑ d ∈ Finset.filter (fun d => 2 ∣ d ∧ 2 ≤ d ∧ d ≤ A₀.max' hne - A₀.min' hne) (Finset.Icc 2 (A₀.max' hne - A₀.min' hne)), (Finset.filter (fun a => a + d ∈ A₀) A₀).card ≤ (Finset.filter (fun d => 2 ∣ d ∧ 2 ≤ d ∧ d ≤ A₀.max' hne - A₀.min' hne) (Finset.Icc 2 (A₀.max' hne - A₀.min' hne))).card * 2 * fFunPos (k - 1) (A₀.max' hne - A₀.min' hne) := by
      push_cast [ mul_assoc ];
      convert Finset.sum_le_card_nsmul _ _ _ _ using 2;
      · ext; norm_num;
      · infer_instance;
      · aesop;
    refine le_trans h_sum_bound ?_;
    gcongr;
    · rcases k with ( _ | _ | _ | k ) <;> norm_num [ fFunPos ] at *;
      exact le_trans ( by norm_num ) ( fFunPos_ge_one_early _ ( by linarith ) _ ( by norm_cast ) );
    · rw [ show ( Finset.filter ( fun d => 2 ∣ d ∧ 2 ≤ d ∧ d ≤ A₀.max' hne - A₀.min' hne ) ( Finset.Icc 2 ( A₀.max' hne - A₀.min' hne ) ) ) = Finset.image ( fun d => 2 * d ) ( Finset.Icc 1 ( ( A₀.max' hne - A₀.min' hne ) / 2 ) ) from ?_, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
      · norm_cast;
        grind;
      · ext; simp [Finset.mem_image];
        exact ⟨ fun h => ⟨ ‹_› / 2, ⟨ by omega, by omega ⟩, by omega ⟩, by rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by omega, by omega ⟩, by omega, by omega, by omega ⟩ ⟩;
  rcases k with ( _ | _ | _ | _ | k ) <;> norm_num [ fFunPos ] at *;
  rw [ ← @Nat.cast_le ℝ ] at * ; norm_num at *;
  rw [ Nat.cast_div ] at * <;> norm_num at *;
  · rw [ Nat.cast_sub ] at * <;> norm_num at *;
    · rw [ ← sub_le_iff_le_add ];
      exact Real.le_sqrt_of_sq_le ( by linarith! );
    · assumption;
  · exact even_iff_two_dvd.mp ( Nat.even_mul_pred_self _ )

lemma ceslemprelim_pos_extend (k : ℕ) (hk : 4 ≤ k)
    (A₀ S : Finset ℤ) (d : ℤ)
    (hS_sub : S ⊆ A₀)
    (hd_lb : 1 ≤ d)
    (hS_shift : ∀ a ∈ S, a + d ∈ A₀)
    (hS_disj : ∀ a ∈ S, a + d ∉ S)
    (hSSC : HasPosSubsetSumsContaining S (k - 1)) :
    HasPosSubsetSumsContaining A₀ k := by
  rcases k with ( _ | _ | _ | _ | k ) <;> norm_num [ HasPosSubsetSumsContaining ] at *;
  obtain ⟨ b, hb₁, hb₂, hb₃ ⟩ := hSSC;
  refine' ⟨ Fin.snoc b ( d ), _, _, _ ⟩ <;> simp_all +decide;
  · intro i; induction i using Fin.lastCases <;> simp +decide [ * ] ;
    linarith;
  · intro i j hi hj hij; cases i using Fin.lastCases <;> cases j using Fin.lastCases <;> simp_all +decide [ Fin.snoc ] ;
    · contrapose! hS_disj;
      use b 0;
      have := hb₃ { 0 } ; have := hb₃ { 0, ‹_› } ; simp_all +decide ;
      convert hb₃ { 0, ‹_› } ( by simp +decide ) using 1 ; rw [ Finset.sum_pair ] ; aesop;
    · contrapose! hS_disj;
      rename_i i;
      use ∑ j ∈ Finset.univ.filter (fun j => j.val < i.val), b j;
      convert hb₃ ( Finset.univ.filter ( fun j => j.val < i.val ) ∪ { i } ) _ using 1;
      · rw [ Finset.sum_union ] <;> aesop;
      · grind;
  · intro T hT;
    by_cases h : Fin.last ( k + 3 ) ∈ T <;> simp_all +decide [ Fin.snoc ];
    · convert hS_shift _ ( hb₃ ( Finset.univ.filter fun i => Fin.castSucc i ∈ T ) ( by aesop ) ) using 1;
      rw [ Finset.sum_eq_sum_diff_singleton_add h ];
      rw [ show ( T \ { Fin.last ( k + 3 ) } : Finset ( Fin ( k + 3 + 1 ) ) ) = Finset.image ( Fin.castSucc ) ( Finset.filter ( fun i : Fin ( k + 3 ) => Fin.castSucc i ∈ T ) Finset.univ ) from ?_, Finset.sum_image ] <;> norm_num;
      ext i; simp [Finset.mem_image];
      exact ⟨ fun hi => ⟨ ⟨ i.val, lt_of_le_of_ne ( Fin.le_last _ ) ( by simpa [ Fin.ext_iff ] using hi.2 ) ⟩, by simpa [ Fin.ext_iff ] using hi.1, rfl ⟩, by rintro ⟨ a, ha₁, rfl ⟩ ; exact ⟨ ha₁, ne_of_lt ( Fin.castSucc_lt_last _ ) ⟩ ⟩;
    · -- Since $T$ does not contain the last element, we can map $T$ to a subset of $\text{Fin}(k + 3)$ by removing the last element.
      obtain ⟨T', hT'⟩ : ∃ T' : Finset (Fin (k + 3)), T = Finset.image (fun i => Fin.castSucc i) T' := by
        use Finset.filter (fun i => Fin.castSucc i ∈ T) (Finset.univ : Finset (Fin (k + 3)));
        ext i; simp [Finset.mem_image];
        induction i using Fin.lastCases <;> aesop;
      aesop

theorem ceslemprelim_pos (k : ℕ) (hk : 3 ≤ k) (A₀ : Finset ℤ) (hne : A₀.Nonempty)
    (heven : ∀ a ∈ A₀, 2 ∣ a)
    (hpos : ∀ a ∈ A₀, 2 ≤ a)
    (hrange : 2 ≤ A₀.max' hne - A₀.min' hne)
    (hcard : (A₀.card : ℝ) > fFunPos k (↑(A₀.max' hne - A₀.min' hne))) :
    HasPosSubsetSumsContaining A₀ k := by
  revert A₀;
  induction hk
  · exact fun A₀ hne heven hpos hrange hcard =>
    ceslemprelim_pos_base3 A₀ hne heven hpos hrange hcard;
  · rename_i k hk ih
    intro A₀ hne heven hpos hrange hcard
    obtain ⟨d, hd1, hd2, hd3, hd4⟩ := ceslemgeneral_pos_pigeonhole_strong (k + 1) (by linarith [Nat.succ_le_succ hk]) A₀ hne heven hrange hcard
    obtain ⟨S, hS_sub, hS_card, hS_disj⟩ := disjoint_half_subset (A₀.filter (fun a => a + d ∈ A₀)) d (by linarith) (fFunPos k (A₀.max' hne - A₀.min' hne)) (by
    grind +qlia);
    apply ceslemprelim_pos_extend (k + 1) (by linarith [Nat.succ_le_iff.mp hk]) A₀ S d;
    · exact fun x hx => Finset.mem_filter.mp ( hS_sub hx ) |>.1;
    · linarith;
    · exact fun x hx => Finset.mem_filter.mp ( hS_sub hx ) |>.2;
    · assumption;
    · apply ih S;
      exact fun a ha => heven a <| Finset.mem_filter.mp ( hS_sub ha ) |>.1;
      exact fun a ha => hpos a <| Finset.mem_filter.mp ( hS_sub ha ) |>.1;
      any_goals exact Finset.nonempty_of_ne_empty ( by rintro rfl; norm_num at hS_card; linarith [ show ( 0 : ℝ ) < fFunPos k ( A₀.max' hne - A₀.min' hne ) from by
                                                                                                    exact lt_of_lt_of_le zero_lt_one ( fFunPos_ge_one_early k hk _ ( by norm_cast ) ) ] );
      · all_goals generalize_proofs at *;
        have hS_card_ge_two : 2 ≤ S.card := by
          contrapose! hS_card; interval_cases _ : Finset.card S <;> simp_all +decide ;
          exact fFunPos_ge_one_early k hk _ ( by linarith [ show ( A₀.max' hne : ℝ ) - A₀.min' hne ≥ 2 by exact_mod_cast hrange ] );
        have hS_card_ge_two : ∃ a b : ℤ, a ∈ S ∧ b ∈ S ∧ a < b ∧ b - a ≥ 2 := by
          obtain ⟨ a, ha, b, hb, hab ⟩ := Finset.one_lt_card.mp hS_card_ge_two;
          cases lt_or_gt_of_ne hab <;> [ exact ⟨ a, b, ha, hb, ‹_›, by obtain ⟨ k, hk ⟩ := heven a ( Finset.mem_filter.mp ( hS_sub ha ) |>.1 ) ; obtain ⟨ l, hl ⟩ := heven b ( Finset.mem_filter.mp ( hS_sub hb ) |>.1 ) ; omega ⟩ ; exact ⟨ b, a, hb, ha, ‹_›, by obtain ⟨ k, hk ⟩ := heven a ( Finset.mem_filter.mp ( hS_sub ha ) |>.1 ) ; obtain ⟨ l, hl ⟩ := heven b ( Finset.mem_filter.mp ( hS_sub hb ) |>.1 ) ; omega ⟩ ];
        obtain ⟨ a, b, ha, hb, hab, h ⟩ := hS_card_ge_two; linarith [ Finset.min'_le _ _ ha, Finset.le_max' _ _ hb ] ;
      · all_goals generalize_proofs at *;
        refine' lt_of_le_of_lt _ hS_card;
        apply_rules [ fFunPos_mono_early ];
        · norm_cast;
          have hS_card_ge_two : 2 ≤ S.card := by
            contrapose! hS_card; interval_cases _ : Finset.card S <;> simp_all +decide ;
            exact fFunPos_ge_one_early k hk _ ( by linarith [ show ( A₀.max' hne : ℝ ) - A₀.min' hne ≥ 2 by exact_mod_cast hrange ] );
          have hS_card_ge_two : ∃ a b : ℤ, a ∈ S ∧ b ∈ S ∧ a < b ∧ b - a ≥ 2 := by
            obtain ⟨ a, ha, b, hb, hab ⟩ := Finset.one_lt_card.mp hS_card_ge_two;
            cases lt_or_gt_of_ne hab <;> [ exact ⟨ a, b, ha, hb, ‹_›, by obtain ⟨ k, hk ⟩ := heven a ( Finset.mem_filter.mp ( hS_sub ha ) |>.1 ) ; obtain ⟨ l, hl ⟩ := heven b ( Finset.mem_filter.mp ( hS_sub hb ) |>.1 ) ; omega ⟩ ; exact ⟨ b, a, hb, ha, ‹_›, by obtain ⟨ k, hk ⟩ := heven a ( Finset.mem_filter.mp ( hS_sub ha ) |>.1 ) ; obtain ⟨ l, hl ⟩ := heven b ( Finset.mem_filter.mp ( hS_sub hb ) |>.1 ) ; omega ⟩ ];
          obtain ⟨ a, b, ha, hb, hab, h ⟩ := hS_card_ge_two; exact le_trans h ( by linarith [ Finset.le_max' _ _ ha, Finset.le_max' _ _ hb, Finset.min'_le _ _ ha, Finset.min'_le _ _ hb ] ) ;
        · norm_cast;
          exact sub_le_sub ( Finset.max'_mem _ _ |> fun x => Finset.mem_filter.mp ( hS_sub x ) |>.1 |> fun y => Finset.le_max' _ _ y ) ( Finset.min'_mem _ _ |> fun x => Finset.mem_filter.mp ( hS_sub x ) |>.1 |> fun y => Finset.min'_le _ _ y )

theorem ceslemgeneral_pos (k : ℕ) (hk : 3 ≤ k) (A₀ : Finset ℤ) (hne : A₀.Nonempty)
    (heven : ∀ a ∈ A₀, 2 ∣ a)
    (hpos : ∀ a ∈ A₀, 2 ≤ a)
    (hrange : 2 ≤ A₀.max' hne - A₀.min' hne)
    (hcard : (A₀.card : ℝ) > fFunPos k (↑(A₀.max' hne - A₀.min' hne))) :
    HasPosPairwiseSums A₀ k := by
  exact pos_subsetsums_to_pairwise A₀ k hk heven
    (ceslemprelim_pos k hk A₀ hne heven hpos hrange hcard)

/-- The upper bound for the positive version.
    boundPos_n n x = 2^(1 - 1/2^(n+1)) * x^(1 - 1/2^(n+1)) + 15 * x^(1 - 3/2^(n+2)) -/
noncomputable def boundPos_n (n : ℕ) (x : ℝ) : ℝ :=
  (2 : ℝ) ^ ((1:ℝ) - 1 / (2:ℝ) ^ (n + 1)) *
    x ^ ((1:ℝ) - 1 / (2:ℝ) ^ (n + 1)) +
  15 * x ^ ((1:ℝ) - 3 / (2:ℝ) ^ (n + 2))

theorem fFunPos_le_boundPos_base (x : ℝ) (hx : 1 ≤ x) :
    fFunPos 3 x ≤ boundPos_n 0 x := by
  -- By definition of $fFunPos$, we know that $fFunPos 3 x = \sqrt{x/2} + (x/2)^{1/4} + 11$.
  unfold boundPos_n
  simp [fFunPos];
  norm_num [ ← Real.sqrt_eq_rpow ];
  rw [ show ( x / 2 : ℝ ) ^ ( 1 / 4 : ℝ ) = ( x ^ ( 1 / 4 : ℝ ) ) / ( 2 ^ ( 1 / 4 : ℝ ) ) by rw [ Real.div_rpow ( by positivity ) ( by positivity ) ] ] ; ring_nf ; norm_num;
  rw [ ← Real.sqrt_div_self ] ; ring_nf;
  rw [ ← Real.rpow_neg ] <;> norm_num;
  nlinarith [ show x ^ ( 1 / 4 : ℝ ) ≥ 1 by exact Real.one_le_rpow hx ( by norm_num ), show ( 2 : ℝ ) ^ ( - ( 1 / 4 : ℝ ) ) ≤ 1 by rw [ Real.rpow_le_one_iff_of_pos ] <;> norm_num ]

theorem fFunPos_le_boundPos_step (n : ℕ)
    (ih : ∀ x : ℝ, 1 ≤ x → fFunPos (n + 3) x ≤ boundPos_n n x)
    (x : ℝ) (hx : 1 ≤ x) :
    fFunPos (n + 4) x ≤ boundPos_n (n + 1) x := by
  -- Apply the induction hypothesis to replace `fFunPos (n + 3) x` with `boundPos_n n x` in the expression for `fFunPos (n + 4) x`.
  have h_ind : fFunPos (n + 4) x ≤ Real.sqrt (2 * x * boundPos_n n x + 1/4) + 1/2 := by
    refine' add_le_add ( Real.sqrt_le_sqrt _ ) le_rfl;
    gcongr ; aesop;
  refine le_trans h_ind ?_;
  rw [ show boundPos_n ( n + 1 ) x = ( 2 : ℝ ) ^ ( ( 1 : ℝ ) - 1 / ( 2 : ℝ ) ^ ( n + 2 ) ) * x ^ ( ( 1 : ℝ ) - 1 / ( 2 : ℝ ) ^ ( n + 2 ) ) + 15 * x ^ ( ( 1 : ℝ ) - 3 / ( 2 : ℝ ) ^ ( n + 3 ) ) by rfl ];
  -- By simplifying, we can see that the inequality holds.
  have h_simp : 2 * (2 : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (n + 2)) * x ^ (1 - 1 / (2 : ℝ) ^ (n + 2)) * (15 * x ^ (1 - 3 / (2 : ℝ) ^ (n + 3))) ≥ (2 : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (n + 2)) * x ^ (1 - 1 / (2 : ℝ) ^ (n + 2)) + 15 * x ^ (1 - 3 / (2 : ℝ) ^ (n + 3)) := by
    have h_simp : (2 : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (n + 2)) * x ^ (1 - 1 / (2 : ℝ) ^ (n + 2)) ≥ 1 := by
      exact one_le_mul_of_one_le_of_one_le ( Real.one_le_rpow ( by norm_num ) ( sub_nonneg.2 <| div_le_self ( by norm_num ) <| one_le_pow₀ <| by norm_num ) ) ( Real.one_le_rpow hx <| sub_nonneg.2 <| div_le_self ( by norm_num ) <| one_le_pow₀ <| by norm_num );
    nlinarith [ show ( 15 : ℝ ) * x ^ ( 1 - 3 / ( 2 : ℝ ) ^ ( n + 3 ) ) ≥ 15 by exact le_mul_of_one_le_right ( by norm_num ) ( Real.one_le_rpow hx ( sub_nonneg.mpr <| by rw [ div_le_iff₀ <| by positivity ] ; linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( by linarith : n + 3 ≥ 3 ) ] ) ) ];
  rw [ ← le_sub_iff_add_le' ];
  rw [ le_sub_comm, Real.sqrt_le_left ];
  · rw [ show boundPos_n n x = ( 2 : ℝ ) ^ ( ( 1 : ℝ ) - 1 / ( 2 : ℝ ) ^ ( n + 1 ) ) * x ^ ( ( 1 : ℝ ) - 1 / ( 2 : ℝ ) ^ ( n + 1 ) ) + 15 * x ^ ( ( 1 : ℝ ) - 3 / ( 2 : ℝ ) ^ ( n + 2 ) ) by rfl ] ; ring_nf at * ; norm_num at *;
    norm_num [ sq, mul_assoc, ← Real.rpow_add ( by positivity : 0 < x ), ← Real.rpow_add ( by positivity : 0 < ( 2 : ℝ ) ) ] at * ; ring_nf at * ; norm_num at *;
    norm_num [ Real.rpow_add ( by positivity : 0 < ( 2 : ℝ ) ), Real.rpow_add ( by positivity : 0 < x ) ] at * ; ring_nf at * ; norm_num at *;
    nlinarith [ show 0 < x ^ 2 * 2 ^ ( - ( ( 1 / 2 : ℝ ) ^ n * ( 1 / 4 ) ) ) * x ^ ( - ( ( 1 / 2 : ℝ ) ^ n * ( 5 / 8 ) ) ) by positivity, show 0 < x ^ 2 * x ^ ( - ( ( 1 / 2 : ℝ ) ^ n * ( 3 / 4 ) ) ) by positivity ];
  · exact sub_nonneg_of_le ( by exact le_trans ( by norm_num ) ( add_le_add ( one_le_mul_of_one_le_of_one_le ( Real.one_le_rpow ( by norm_num ) ( by exact sub_nonneg.mpr <| div_le_self zero_le_one <| one_le_pow₀ <| by norm_num ) ) <| Real.one_le_rpow hx <| by exact sub_nonneg.mpr <| div_le_self zero_le_one <| one_le_pow₀ <| by norm_num ) <| one_le_mul_of_one_le_of_one_le ( by norm_num ) <| Real.one_le_rpow hx <| by exact sub_nonneg.mpr <| by rw [ div_le_iff₀ <| by positivity ] ; linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) <| show n + 3 ≥ 3 by linarith ] ) )

private theorem fFunPos_le_boundPos_n_aux (m : ℕ) :
    ∀ x : ℝ, 1 ≤ x → fFunPos (m + 3) x ≤ boundPos_n m x := by
  induction m with
  | zero => exact fun y hy => fFunPos_le_boundPos_base y hy
  | succ n ih => exact fun y hy => fFunPos_le_boundPos_step n ih y hy

noncomputable def boundPos (k : ℕ) (x : ℝ) : ℝ :=
  2 ^ ((1:ℝ) - 1 / 2 ^ ((k:ℝ) - 2)) * x ^ ((1:ℝ) - 1 / 2 ^ ((k:ℝ) - 2)) +
  15 * x ^ ((1:ℝ) - 3 / 2 ^ ((k:ℝ) - 1))

theorem boundPos_eq_boundPos_n (k : ℕ) (hk : 3 ≤ k) (x : ℝ) :
    boundPos k x = boundPos_n (k - 3) x := by
  unfold boundPos_n boundPos; rcases k with ( _ | _ | _ | k ) <;> norm_num at *;
  ring_nf;
  norm_cast ; norm_num ; ring_nf;
  norm_num [ Rat.divInt_eq_div ] ; ring_nf

theorem fFunPos_le_boundPos (k : ℕ) (hk : 3 ≤ k) (x : ℝ) (hx : 1 ≤ x) :
    fFunPos k x ≤ boundPos k x := by
  rw [boundPos_eq_boundPos_n k hk x]
  have := fFunPos_le_boundPos_n_aux (k - 3) x hx
  simp only [Nat.sub_add_cancel hk] at this
  exact this

theorem ceslemgeneral_pos_with_bound (k : ℕ) (hk : 3 ≤ k)
    (A₀ : Finset ℤ) (hne : A₀.Nonempty)
    (heven : ∀ a ∈ A₀, 2 ∣ a) (hpos : ∀ a ∈ A₀, 2 ≤ a)
    (hrange : 2 ≤ A₀.max' hne - A₀.min' hne)
    (n : ℕ) (hn : 1 ≤ n)
    (hrange_le : A₀.max' hne - A₀.min' hne ≤ ↑n)
    (hcard : (A₀.card : ℝ) > boundPos k (↑n)) :
    HasPosPairwiseSums A₀ k := by
  convert ceslemgeneral_pos k hk A₀ hne heven hpos hrange _ using 1;
  refine' lt_of_le_of_lt _ hcard;
  refine' le_trans _ ( boundPos_eq_boundPos_n k hk n ▸ fFunPos_le_boundPos_n_aux ( k - 3 ) _ _ );
  · rw [ Nat.sub_add_cancel hk ];
    refine' fFunPos_mono_early k hk _ _ _ _ <;> norm_cast;
  · norm_cast

theorem hk_upper_aux (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (hn : 1 ≤ n)
    (A : Finset ℤ) (hA : A ⊆ Icc (1 : ℤ) (2 * ↑n))
    (hcard : (A.card : ℝ) > ↑n + boundPos k (2 * ↑n)) :
    HasPosPairwiseSums A k := by
  -- Let $E$ be the set of even elements in $A$.
  set E := A.filter (fun x => Even x) with hE_def;
  have hE_card : (E.card : ℝ) > boundPos k (2 * n) := by
    -- Since $A$ contains at most $n$ odd elements, we have $|E| \geq |A| - n$.
    have hE_card_ge : (E.card : ℝ) ≥ (A.card : ℝ) - n := by
      have hE_card : (A.filter (fun x => ¬Even x)).card ≤ n := by
        have h_odd_subset : (A.filter (fun x => ¬Even x)) ⊆ Finset.image (fun x : ℕ => 2 * x + 1) (Finset.range n) := by
          intro x hx; specialize hA ( Finset.mem_filter.mp hx |>.1 ) ; simp_all +decide [ parity_simps ] ;
          rcases hx.2 with ⟨ m, rfl ⟩ ; exact ⟨ Int.toNat m, by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ m ) ], by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ m ) ] ⟩ ;
        exact le_trans ( Finset.card_le_card h_odd_subset ) ( Finset.card_image_le.trans ( by simp ) );
      exact sub_le_iff_le_add.mpr ( mod_cast by linarith [ show Finset.card E + Finset.card ( Finset.filter ( fun x => ¬Even x ) A ) = Finset.card A from by rw [ Finset.card_filter_add_card_filter_not ] ] ) ;
    generalize_proofs at *; (
    linarith);
  have hE_nonempty : E.Nonempty := by
    by_contra hE_empty;
    exact absurd hE_card ( by rw [ show E = ∅ by ext; aesop ] ; norm_num; linarith [ show 0 ≤ boundPos k ( 2 * n ) by exact add_nonneg ( mul_nonneg ( Real.rpow_nonneg zero_le_two _ ) ( Real.rpow_nonneg ( by positivity ) _ ) ) ( mul_nonneg ( by positivity ) ( Real.rpow_nonneg ( by positivity ) _ ) ) ] )
  have hE_even : ∀ a ∈ E, 2 ∣ a := by
    exact fun x hx => even_iff_two_dvd.mp <| Finset.mem_filter.mp hx |>.2
  have hE_pos : ∀ a ∈ E, 2 ≤ a := by
    exact fun x hx => by linarith [ Finset.mem_Icc.mp ( hA ( Finset.mem_filter.mp hx |>.1 ) ), Int.le_of_dvd ( by linarith [ Finset.mem_Icc.mp ( hA ( Finset.mem_filter.mp hx |>.1 ) ) ] ) ( hE_even x hx ) ] ;
  have hE_range : 2 ≤ E.max' hE_nonempty - E.min' hE_nonempty := by
    have hE_card_ge_two : 2 ≤ E.card := by
      contrapose! hE_card; interval_cases _ : Finset.card E <;> norm_num at *;
      · grind;
      · refine' le_add_of_le_of_nonneg _ _ <;> norm_num [ boundPos ];
        · exact one_le_mul_of_one_le_of_one_le ( Real.one_le_rpow ( by norm_num ) ( sub_nonneg.mpr <| inv_le_one_of_one_le₀ <| Real.one_le_rpow ( by norm_num ) <| by linarith [ show ( k : ℝ ) ≥ 3 by norm_cast ] ) ) ( Real.one_le_rpow ( by linarith [ show ( n : ℝ ) ≥ 1 by norm_cast ] ) ( sub_nonneg.mpr <| inv_le_one_of_one_le₀ <| Real.one_le_rpow ( by norm_num ) <| by linarith [ show ( k : ℝ ) ≥ 3 by norm_cast ] ) );
        · positivity;
    obtain ⟨a, ha, b, hb, hab⟩ : ∃ a ∈ E, ∃ b ∈ E, a < b := by
      obtain ⟨ a, ha, b, hb, hab ⟩ := Finset.one_lt_card.mp hE_card_ge_two; exact hab.lt_or_gt.elim ( fun h => ⟨ a, ha, b, hb, h ⟩ ) fun h => ⟨ b, hb, a, ha, h ⟩ ;
    have h_diff : b - a ≥ 2 := by
      exact Int.le_of_dvd ( by linarith ) ( Int.dvd_sub ( hE_even b hb ) ( hE_even a ha ) );
    exact le_trans h_diff ( sub_le_sub ( Finset.le_max' _ _ hb ) ( Finset.min'_le _ _ ha ) )
  have hE_spread : E.max' hE_nonempty - E.min' hE_nonempty ≤ 2 * n := by
    exact le_trans ( sub_le_sub ( Finset.mem_Icc.mp ( hA ( Finset.max'_mem _ _ |> Finset.mem_filter.mp |>.1 ) ) |>.2 ) ( Finset.mem_Icc.mp ( hA ( Finset.min'_mem _ _ |> Finset.mem_filter.mp |>.1 ) ) |>.1 ) ) ( by linarith );
  have := ceslemgeneral_pos_with_bound k hk E hE_nonempty hE_even hE_pos hE_range (2 * n) (by linarith) hE_spread (by
  aesop);
  obtain ⟨ B, hB₁, hB₂, hB₃ ⟩ := this;
  exact ⟨ B, hB₁, hB₂, fun i j hij => Finset.mem_filter.mp ( hB₃ i j hij ) |>.1 ⟩

theorem hk_upper (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (hn : 1 ≤ n) :
    hFun k n ≤ Nat.ceil (boundPos k (2 * ↑n)) + 1 := by
  refine' Nat.sInf_le _;
  intro A hA hcard;
  have := hk_upper_aux k hk n hn A hA;
  exact this ( by push_cast [ ← @Nat.cast_le ℝ ] at *; linarith [ Nat.le_ceil ( boundPos k ( 2 * n ) ) ] )

/-
For every k ≥ 3, there exists N such that for all n ≥ N,
  g_k(n) ≤ h_k(n) < 4n^{1-1/2^{k-2}}
-/
theorem generalupper (k : ℕ) (hk : 3 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      gFun k n ≤ hFun k n ∧
      (hFun k n : ℝ) < 4 * (↑n : ℝ) ^ ((1:ℝ) - 1 / 2 ^ ((k:ℝ) - 2)) := by
  set e : ℝ := 1 - 1 / (2 ^ (k - 2) : ℝ)
  set d : ℝ := 2 ^ (1 - 1 / (2 ^ (k - 2) : ℝ));
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → boundPos k (2 * (n : ℝ)) + 2 < 4 * (n : ℝ) ^ e := by
    have h_limit : Filter.Tendsto (fun n : ℕ => (boundPos k (2 * (n : ℝ)) + 2) / (n : ℝ) ^ e) Filter.atTop (nhds (d^2)) := by
      have h_boundPos : ∀ n : ℕ, n ≥ 1 → boundPos k (2 * n) = d^2 * (n : ℝ) ^ e + 15 * (2 * n : ℝ) ^ (1 - 3 / (2 ^ (k - 1) : ℝ)) := by
        intro n hn
        simp [boundPos];
        rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ] ; ring_nf;
        rcases k with ( _ | _ | k ) <;> norm_num [ Real.rpow_add, Real.rpow_neg ] at * ; ring_nf at * ; aesop ( simp_config := { decide := true } ) ;
      suffices h_simplify'' : Filter.Tendsto (fun n : ℕ => d^2 + 15 * (2 : ℝ) ^ (1 - 3 / (2 ^ (k - 1) : ℝ)) * (n : ℝ) ^ (1 - 3 / (2 ^ (k - 1) : ℝ) - e) + 2 / (n : ℝ) ^ e) Filter.atTop (nhds (d^2)) by
        refine h_simplify''.congr' ?_;
        filter_upwards [ Filter.eventually_ge_atTop 1 ] with n hn ; rw [ h_boundPos n hn ] ; rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ] ; ring_nf;
        norm_num [ ne_of_gt ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr hn ) _ ) ] ; ring_nf;
        rw [ mul_assoc, ← Real.rpow_neg ( by positivity ), ← Real.rpow_add ( by positivity ) ] ; ring_nf;
      have h_exp : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - 3 / (2 ^ (k - 1) : ℝ) - e)) Filter.atTop (nhds 0) := by
        convert tendsto_rpow_neg_atTop ( show 0 < - ( 1 - 3 / ( 2 ^ ( k - 1 ) : ℝ ) - e ) from neg_pos_of_neg ?_ ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop using 2 ; ring_nf! ; norm_num [ Nat.succ_eq_add_one, pow_add ] at *;
        rcases k with ( _ | _ | k ) <;> norm_num [ pow_succ' ] at *;
        simp +zetaDelta at *;
        rw [ inv_eq_one_div, div_lt_div_iff₀ ] <;> linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) hk ];
      simpa using Filter.Tendsto.add ( tendsto_const_nhds.add ( h_exp.const_mul _ ) ) ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.comp ( tendsto_rpow_atTop ( show 0 < e by exact sub_pos.mpr <| by rw [ div_lt_iff₀ <| by positivity ] ; linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 2 ) ( show k - 2 ≥ 1 by exact Nat.sub_pos_of_lt <| by linarith ) ] ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ) ) );
    have h_lt_four : d^2 < 4 := by
      exact lt_of_lt_of_le ( pow_lt_pow_left₀ ( Real.rpow_lt_rpow_of_exponent_lt ( by norm_num ) ( show ( 1 - 1 / ( 2:ℝ ) ^ ( k-2 ) ) < 1 from sub_lt_self _ <| by positivity ) ) ( by positivity ) ( by positivity ) ) <| by norm_num;
    rcases Metric.tendsto_atTop.mp h_limit ( 4 - d ^ 2 ) ( sub_pos.mpr h_lt_four ) with ⟨ N₀, hN₀ ⟩;
    exact ⟨ N₀ + 1, fun n hn => by
      have hlt := abs_lt.mp ( hN₀ n ( by linarith ) )
      have hpos : 0 < ( n : ℝ ) ^ e := Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith ) ) _
      rw [ div_eq_mul_inv ] at hlt
      nlinarith [ inv_pos.mpr hpos, mul_inv_cancel₀ ( ne_of_gt hpos ) ] ⟩;
  use N₀ + 1;
  intros n hn
  refine ⟨ gFun_le_hFun k n, ?_ ⟩
  have h_ceil : (hFun k n : ℝ) ≤ boundPos k (2 * (n : ℝ)) + 2 := by
    have := hk_upper k hk n ( by linarith );
    exact le_trans ( Nat.cast_le.mpr this ) ( by push_cast; linarith [ Nat.ceil_lt_add_one ( show 0 ≤ boundPos k ( 2 * ( n : ℝ ) ) by exact add_nonneg ( mul_nonneg ( Real.rpow_nonneg ( by norm_num ) _ ) ( Real.rpow_nonneg ( by linarith ) _ ) ) ( mul_nonneg ( by norm_num ) ( Real.rpow_nonneg ( by linarith ) _ ) ) ) ] );
  calc (hFun k n : ℝ) ≤ boundPos k (2 * (n : ℝ)) + 2 := h_ceil
    _ < 4 * (n : ℝ) ^ e := hN₀ n ( by linarith )
    _ = 4 * (↑n : ℝ) ^ ((1:ℝ) - 1 / 2 ^ ((k:ℝ) - 2)) := by
        congr 1; norm_cast;
        rw [ Int.subNatNat_of_le ( by linarith ) ] ; norm_cast;
        grind

#print axioms generalupper
-- 'Erdos866b.generalupper' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos866b
