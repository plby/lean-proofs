/-

This is a Lean formalization of a solution to Erdős Problem 350.
https://www.erdosproblems.com/350

The original human proof was found by: Ryavec

Benkoski, S. J., and Erdős, P. On weird and pseudoperfect numbers. Math. Comput. 28 (1974), 617–623.

ChatGPT from OpenAI explained some proof of this result (not
necessarily the original human proof, instead prioritizing clarity).

The LaTeX file output from the previous step was auto-formalized into
Lean by Aristotle from Harmonic.

The final theorem statement is from the Formal Conjectures project
organized by Google DeepMind.

The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/
import Mathlib

namespace Erdos350

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

open Finset

/-- A finite subset of integers has distinct subset sums if all its subsets have distinct sums. -/
def HasDistinctSubsetSums (A : Finset ℕ) : Prop :=
  ∀ S T, S ⊆ A → T ⊆ A → ∑ x ∈ S, x = ∑ x ∈ T, x → S = T

open Finset

/-- A sequence has distinct subset sums if all its subsets have distinct sums. -/
def HasDistinctSubsetSumsSeq {m : ℕ} (a : Fin m → ℕ) : Prop :=
  ∀ S T : Finset (Fin m), ∑ i ∈ S, a i = ∑ i ∈ T, a i → S = T

lemma sum_ge_two_pow_sub_one {m : ℕ} {a : Fin m → ℕ} (h_distinct : HasDistinctSubsetSumsSeq a) (k : ℕ) (hk : k ≤ m) :
  ∑ i ∈ Finset.univ.filter (fun j => j.val < k), a i ≥ 2^k - 1 := by
    have := h_distinct;
    -- Since the sequence has distinct subset sums, the image of the powerset of {0, ..., k-1} under the sum map has cardinality 2^k.
    have h_card : Finset.card (Finset.image (fun S : Finset (Fin m) => ∑ x ∈ S, a x) (Finset.powerset (Finset.univ.filter (fun j => j.val < k)))) = 2 ^ k := by
      rw [ Finset.card_image_of_injOn ];
      · -- The set {j : Fin m | j.val < k} is equivalent to the set {0, 1, ..., k-1} in Fin m, which has cardinality k.
        have h_card : Finset.card (Finset.filter (fun j : Fin m => j.val < k) Finset.univ) = Finset.card (Finset.range k) := by
          refine' Finset.card_bij ( fun x hx => x ) _ _ _ <;> aesop;
          exact ⟨ ⟨ b, by linarith ⟩, a_1, rfl ⟩;
        aesop;
      · -- Since the sequence has distinct subset sums, if two subsets have the same sum, they must be the same subset. Therefore, the function is injective on this set.
        intros S hS T hT h_eq;
        have := @this ( Finset.univ.filter fun i : Fin m => i.val < k ) ; aesop;
    -- All subset sums are in the range [0, ∑ i in {j | j.val < k}, a i].
    have h_range : Finset.image (fun S : Finset (Fin m) => ∑ x ∈ S, a x) (Finset.powerset (Finset.univ.filter (fun j => j.val < k))) ⊆ Finset.Icc 0 (∑ i ∈ Finset.univ.filter (fun j => j.val < k), a i) := by
      exact Finset.image_subset_iff.mpr fun S hS => Finset.mem_Icc.mpr ⟨ Nat.zero_le _, Finset.sum_le_sum_of_subset <| Finset.mem_powerset.mp hS ⟩;
    have := Finset.card_le_card h_range; aesop;

open Finset

/-- The set of differences between elements of a set. -/
def diff_set (U : Finset ℕ) : Finset ℕ :=
  (U.product U).image (fun x => if x.1 ≥ x.2 then x.1 - x.2 else x.2 - x.1)

lemma not_mem_diff_set_of_distinct_sums {m : ℕ} {a : Fin m → ℕ} (h_distinct : HasDistinctSubsetSumsSeq a) (k : Fin m) :
  let U := (powerset (univ.filter (· < k))).image (fun S => ∑ j ∈ S, a j)
  a k ∉ diff_set U := by
    bound;
    -- Assume $a_k \in \text{diff\_set}(U)$, then there exist subsets $S, T \subseteq \{a_0, ..., a_{k-1}\}$ such that $a_k = \sum_{j \in S} a_j - \sum_{j \in T} a_j$.
    obtain ⟨S, T, hST⟩ : ∃ S T : Finset (Fin m), S ⊆ Finset.univ.filter (fun j => j.val < k) ∧ T ⊆ Finset.univ.filter (fun j => j.val < k) ∧ a k = ∑ j ∈ S, a j - ∑ j ∈ T, a j := by
      unfold diff_set at a_1;
      norm_num +zetaDelta at *;
      rcases a_1 with ⟨ a_2, b, ⟨ ⟨ S, hS₁, rfl ⟩, ⟨ T, hT₁, rfl ⟩ ⟩, h ⟩ ; split_ifs at h <;> [ exact ⟨ S, hS₁, T, hT₁, h.symm ⟩ ; exact ⟨ T, hT₁, S, hS₁, h.symm ⟩ ] ;
    -- Then $\sum_{j \in S} a_j = \sum_{j \in T} a_j + a_k$, which implies $\sum_{j \in S} a_j = \sum_{j \in T \cup \{k\}} a_j$.
    have h_sum_eq : ∑ j ∈ S, a j = ∑ j ∈ T ∪ {k}, a j := by
      rw [ Finset.sum_union ] <;> aesop;
      · rw [ Nat.add_sub_of_le ];
        exact le_of_not_lt fun h => by rw [ tsub_eq_zero_iff_le.mpr h.le ] at right; linarith [ show a k > 0 from Nat.pos_of_ne_zero fun h => by have := h_distinct { k } ∅ ; aesop ] ;
      · simpa using left_1 a_2;
    -- Since $S$ and $T \cup \{k\}$ are subsets of the first $k$ elements and their sums are equal, by the distinct subset sums property, we must have $S = T \cup \{k\}$.
    have h_eq : S = T ∪ {k} := by
      -- Apply the distinct subset sums property to conclude that S = T ∪ {k}.
      apply h_distinct; exact h_sum_eq;
    grind

open Finset

lemma sum_inv_le_sum_inv_of_sum_ge {n : ℕ} {a b : Fin n → ℚ}
  (ha_pos : ∀ i, 0 < a i) (hb_pos : ∀ i, 0 < b i)
  (ha_mono : StrictMono a) (hb_mono : StrictMono b)
  (h_sum : ∀ k : Fin n, ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), a i ≥ ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), b i) :
  ∑ i, 1 / a i ≤ ∑ i, 1 / b i := by
    -- By Abel's lemma, we can express the sum of (1/b_i - 1/a_i) as a telescoping series.
    have h_telescope : ∑ i, (1 / b i - 1 / a i) = ∑ i, ((a i - b i) / (a i * b i)) := by
      exact Finset.sum_congr rfl fun i _ => by rw [ div_sub_div ] <;> ring <;> linarith [ ha_pos i, hb_pos i ] ;
    -- Applying Abel's lemma, we can express the sum $\sum_{i=0}^{n-1} w_i (a_i - b_i)$ as $\sum_{i=0}^{n-1} s_i (w_i - w_{i+1}) + w_n s_n$, where $w_i = 1/(a_i b_i)$ and $s_i = \sum_{j=0}^i (a_j - b_j)$.
    set w : Fin (n + 1) → ℚ := fun i => if h : i.val < n then 1 / (a ⟨i.val, h⟩ * b ⟨i.val, h⟩) else 0
    set s : Fin (n + 1) → ℚ := fun i => ∑ j ∈ Finset.univ.filter (fun k => k.val < i.val), (a j - b j);
    -- By Abel's lemma, we can express the sum $\sum_{i=0}^{n-1} w_i (a_i - b_i)$ as $\sum_{i=0}^{n-1} s_i (w_i - w_{i+1}) + w_n s_n$.
    -- By the properties of the sequences $a$ and $b$, we have that $s_i \geq 0$ for all $i$.
    have h_s_nonneg : ∀ i : Fin (n + 1), 0 ≤ s i := by
      -- By definition of $s$, we know that $s_i = \sum_{j=0}^{i-1} (a_j - b_j)$.
      intro i
      simp [s];
      -- Consider two cases: $i.val = 0$ and $i.val > 0$.
      by_cases hi : i.val = 0;
      · aesop;
      · -- Since $i \neq 0$, we have $i.val \geq 1$. Let $k = i.val - 1$, then $k \in \{0, 1, \ldots, n-1\}$.
        obtain ⟨k, hk⟩ : ∃ k : Fin n, i.val = k.val + 1 := by
          exact ⟨ ⟨ i - 1, by omega ⟩, by cases i using Fin.inductionOn <;> trivial ⟩;
        simp_all +decide [ Finset.sum_ite, Nat.lt_succ_iff ];
    -- Since $s_i \geq 0$ for all $i$, the sum $\sum_{i=1}^n \frac{a_i - b_i}{a_i b_i}$ is non-negative.
    have h_sum_nonneg : 0 ≤ ∑ i : Fin n, (a i - b i) / (a i * b i) := by
      -- Since $s_i \geq 0$ for all $i$, the sum $\sum_{i=1}^n s_i (w_i - w_{i+1})$ is non-negative.
      have h_sum_nonneg : 0 ≤ ∑ i : Fin n, s (⟨i.val + 1, by linarith [Fin.is_lt i]⟩) * (w (⟨i.val, by linarith [Fin.is_lt i]⟩) - w (⟨i.val + 1, by linarith [Fin.is_lt i]⟩)) := by
        -- Since $w$ is non-increasing, each term $(w ⟨i.val, by linarith [Fin.is_lt i]⟩ - w ⟨i.val + 1, by linarith [Fin.is_lt i]⟩)$ is non-negative.
        have h_w_noninc : ∀ i : Fin n, w ⟨i.val, by linarith [Fin.is_lt i]⟩ ≥ w ⟨i.val + 1, by linarith [Fin.is_lt i]⟩ := by
          aesop;
          · exact mul_le_mul ( inv_anti₀ ( hb_pos _ ) ( hb_mono.monotone ( Nat.le_succ _ ) ) ) ( inv_anti₀ ( ha_pos _ ) ( ha_mono.monotone ( Nat.le_succ _ ) ) ) ( inv_nonneg.2 ( le_of_lt ( ha_pos _ ) ) ) ( inv_nonneg.2 ( le_of_lt ( hb_pos _ ) ) );
          · linarith [ ha_pos i ];
        exact Finset.sum_nonneg fun i _ => mul_nonneg ( h_s_nonneg _ ) ( sub_nonneg.mpr ( h_w_noninc i ) );
      -- By definition of $s$, we can split the sum into two parts: the sum of $s_i w_i$ and the sum of $-s_i w_{i+1}$.
      have h_split : ∑ i : Fin n, s (⟨i.val + 1, by linarith [Fin.is_lt i]⟩) * (w (⟨i.val, by linarith [Fin.is_lt i]⟩) - w (⟨i.val + 1, by linarith [Fin.is_lt i]⟩)) = ∑ i : Fin n, s (⟨i.val + 1, by linarith [Fin.is_lt i]⟩) * w (⟨i.val, by linarith [Fin.is_lt i]⟩) - ∑ i : Fin n, s (⟨i.val + 1, by linarith [Fin.is_lt i]⟩) * w (⟨i.val + 1, by linarith [Fin.is_lt i]⟩) := by
        simp +decide only [mul_sub, sum_sub_distrib];
      have h_telescope : ∑ i : Fin n, s (⟨i.val + 1, by linarith [Fin.is_lt i]⟩) * w (⟨i.val, by linarith [Fin.is_lt i]⟩) - ∑ i : Fin n, s (⟨i.val + 1, by linarith [Fin.is_lt i]⟩) * w (⟨i.val + 1, by linarith [Fin.is_lt i]⟩) = ∑ i : Fin n, s (⟨i.val, by linarith [Fin.is_lt i]⟩) * w (⟨i.val, by linarith [Fin.is_lt i]⟩) - ∑ i : Fin n, s (⟨i.val + 1, by linarith [Fin.is_lt i]⟩) * w (⟨i.val + 1, by linarith [Fin.is_lt i]⟩) + ∑ i : Fin n, (a i - b i) / (a i * b i) := by
        have h_telescope : ∀ i : Fin n, s (⟨i.val + 1, by linarith [Fin.is_lt i]⟩) * w (⟨i.val, by linarith [Fin.is_lt i]⟩) = s (⟨i.val, by linarith [Fin.is_lt i]⟩) * w (⟨i.val, by linarith [Fin.is_lt i]⟩) + (a i - b i) / (a i * b i) := by
          simp +zetaDelta at *;
          intro i; rw [ show ( Finset.filter ( fun x : Fin n => ( x : ℕ ) < i + 1 ) Finset.univ : Finset ( Fin n ) ) = Finset.filter ( fun x : Fin n => ( x : ℕ ) < i ) Finset.univ ∪ { i } from ?_, Finset.sum_union ] <;> norm_num ; ring;
          ext x; simp +decide [ Nat.lt_succ_iff ] ;
          exact le_iff_eq_or_lt;
        simp +decide only [h_telescope, sum_add_distrib, add_sub_right_comm];
      have h_telescope : ∑ i : Fin n, s (⟨i.val, by linarith [Fin.is_lt i]⟩) * w (⟨i.val, by linarith [Fin.is_lt i]⟩) - ∑ i : Fin n, s (⟨i.val + 1, by linarith [Fin.is_lt i]⟩) * w (⟨i.val + 1, by linarith [Fin.is_lt i]⟩) = 0 := by
        have h_telescope : ∑ i : Fin n, s (⟨i.val, by linarith [Fin.is_lt i]⟩) * w (⟨i.val, by linarith [Fin.is_lt i]⟩) = ∑ i : Fin (n + 1), s i * w i - s (Fin.last n) * w (Fin.last n) := by
          norm_num +zetaDelta at *;
          simp +decide [ Fin.sum_univ_castSucc ];
        rw [ h_telescope ];
        norm_num [ Fin.sum_univ_succ ];
        norm_num +zetaDelta at *;
      linarith;
    norm_num at *; linarith;

theorem reciprocal_sum_lt_two {A : Finset ℕ} (hA : HasDistinctSubsetSums A) (hpos : ∀ a ∈ A, 0 < a) :
  ∑ a ∈ A, (1 : ℚ) / a < 2 := by
    -- Apply the lemma sum_ge_two_pow_sub_one to get the required inequality for the sums.
    have h_sum_ge : ∀ k : Fin A.card, ∑ i ∈ Finset.univ.filter (fun j => j.val < k.val + 1), (A.orderEmbOfFin rfl i : ℚ) ≥ 2^(k.val + 1) - 1 := by
      simp +zetaDelta at *;
      -- Apply the lemma sum_ge_two_pow_sub_one with k = k.val + 1.
      intros k
      have := sum_ge_two_pow_sub_one (by
      intro S T hST; have := @hA ( Finset.image ( fun i => A.orderEmbOfFin ( by aesop ) i ) S ) ( Finset.image ( fun i => A.orderEmbOfFin ( by aesop ) i ) T ) ; aesop;
      have := this ( Finset.image_subset_iff.mpr fun i _ => Finset.orderEmbOfFin_mem _ _ _ ) ( Finset.image_subset_iff.mpr fun i _ => Finset.orderEmbOfFin_mem _ _ _ ) ; rw [ Finset.image_injective ( by aesop_cat ) this ] ; : HasDistinctSubsetSumsSeq (fun i => A.orderEmbOfFin rfl i)) (k.val + 1)
      aesop;
      exact_mod_cast this ( Nat.succ_le_of_lt k.2 );
    -- By `sum_inv_le_sum_inv_of_sum_ge`, we have $\sum \frac{1}{a_i} \le \sum \frac{1}{2^i}$.
    have h_sum_inv_le : (∑ a ∈ Finset.image (fun i => (A.orderEmbOfFin rfl i : ℕ)) (Finset.univ : Finset (Fin A.card)), (1 / (a : ℚ))) ≤ (∑ i ∈ Finset.range A.card, (1 / (2 ^ i : ℚ))) := by
      have h_sum_inv_le : (∑ i ∈ Finset.univ, (1 / ((A.orderEmbOfFin rfl i) : ℚ))) ≤ (∑ i ∈ Finset.range A.card, (1 / (2 ^ i : ℚ))) := by
        rw [ Finset.sum_range ];
        apply sum_inv_le_sum_inv_of_sum_ge;
        · -- Since $A$ consists of positive integers, and $orderEmbOfFin$ is an order embedding, each element in the image of $orderEmbOfFin$ is also positive.
          intro i
          apply Nat.cast_pos.mpr
          apply hpos
          apply Finset.orderEmbOfFin_mem;
        · simp +zetaDelta at *;
        · exact fun i j hij => Nat.cast_lt.mpr ( by simpa using hij );
        ·
          -- The exponential function with base 2 is strictly increasing, so if $i < j$, then $2^i < 2^j$.
          have h_exp_mono : StrictMono (fun i : ℕ => (2 : ℚ) ^ i) := by
            -- The exponential function with base 2 is strictly monotone.
            apply pow_right_strictMono₀; norm_num;
          -- Since the exponential function with base 2 is strictly monotone on ℕ, and Fin #A is a finite type, the function (fun i : Fin #A => (2 : ℚ) ^ (i.val)) is strictly monotone.
          intros i j hij; exact h_exp_mono (by simpa using hij)
        · intro k; specialize h_sum_ge k; simp_all +decide [ Finset.sum_ite ] ;
          -- The sum of $2^i$ from $i=0$ to $k$ is $2^{k+1} - 1$.
          have h_sum_2_pow : ∑ i ∈ Finset.range (k.val + 1), (2^i : ℚ) = 2^(k.val + 1) - 1 := by
            rw [ geom_sum_eq ] <;> norm_num;
          convert sub_le_sub_right h_sum_ge 1 using 1;
          · rw [ ← h_sum_2_pow, Finset.range_eq_Ico ] ; refine' Finset.sum_bij ( fun i hi => i ) _ _ _ _ <;> aesop;
            · exact Nat.lt_succ_of_le ha;
            · exact ⟨ ⟨ b, by linarith [ Fin.is_lt k ] ⟩, Nat.le_of_lt_succ a, rfl ⟩;
          · norm_num [ Finset.sum_filter, Nat.lt_succ_iff ];
      rw [ Finset.sum_image ] <;> aesop;
    rw [ Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i _ => Finset.mem_coe.mpr <| Finset.orderEmbOfFin_mem _ _ _ ) ( by rw [ Finset.card_image_of_injective ] <;> aesop_cat ) ] at h_sum_inv_le ; aesop;
    exact h_sum_inv_le.trans_lt ( by ring_nf; rw [ geom_sum_eq ] <;> ring <;> norm_num )

/--The predicate that all (finite) subsets of `A` have distinct sums, decidable version-/
def DecidableDistinctSubsetSums {M : Type*} [AddCommMonoid M] [DecidableEq M] (A : Finset M) : Prop :=
  ∀ X ⊆ A, ∀ Y ⊆ A, X ≠ Y → X.sum id ≠ Y.sum id

/--
If `A ⊂ ℕ` is a finite set of integers all of whose subset sums are distinct then `∑ n ∈ A, 1/n < 2`.
Proved by Ryavec.
-/
theorem erdos_350 (A : Finset ℕ) (hA : DecidableDistinctSubsetSums A) :
    ∑ n ∈ A, (1 / n : ℝ) < 2 := by
  -- We need to show that the sum of the reciprocals of the elements in $A$ is less than 2. This follows from the fact that the elements of $A$ are distinct and positive, and their subset sums are also distinct.
  have h_reciprocal_sum : (∑ n ∈ A, (1 : ℚ) / n) < 2 := by
    -- Apply the lemma that states the sum of the reciprocals of the elements in A is less than 2.
    apply reciprocal_sum_lt_two;
    · intro S T hS hT hsum;
      contrapose! hsum; aesop;
    · -- Assume for contradiction that there exists an element $a \in A$ such that $a \leq 0$.
      by_contra h_neg;
      -- If $A$ contains 0, then we can consider the non-zero elements of $A$.
      obtain ⟨a, ha₀, ha₁⟩ : ∃ a ∈ A, a = 0 := by
        grind;
      have := hA { a } ( by aesop ) { } ( by aesop ) ; aesop;
  -- Since the sum of reciprocals in the rationals is equal to the sum in the reals, we can directly use the inequality we have.
  have h_eq : (∑ n ∈ A, (1 : ℚ) / n) = (∑ n ∈ A, (1 : ℝ) / n) := by
    bound;
  exact h_eq ▸ mod_cast h_reciprocal_sum
