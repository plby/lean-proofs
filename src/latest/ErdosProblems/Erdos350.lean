/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 350.
https://www.erdosproblems.com/forum/thread/350

Informal authors:
- Charles Albert Ryavec
- ChatGPT

Formal authors:
- Aristotle
- Boris Alexeev

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos350.md
-/
import Mathlib

namespace Erdos350

set_option linter.style.setOption false
set_option linter.style.cdot false
set_option linter.style.docString false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.refine false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option aesop.warn.nonterminal false

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
  dsimp only
  intro hmem
  rw [diff_set, mem_image] at hmem
  rcases hmem with ⟨p, hp, hdiff⟩
  rw [Finset.product_eq_sprod, mem_product] at hp
  rcases hp with ⟨hp1, hp2⟩
  rw [mem_image] at hp1 hp2
  rcases hp1 with ⟨S, hSsub, hSsum⟩
  rcases hp2 with ⟨T, hTsub, hTsum⟩
  rw [mem_powerset] at hSsub hTsub
  rw [← hSsum, ← hTsum] at hdiff
  by_cases hle : ∑ j ∈ T, a j ≤ ∑ j ∈ S, a j
  · simp [hle] at hdiff
    have hsum : ∑ j ∈ S, a j = ∑ j ∈ T ∪ {k}, a j := by
      rw [sum_union]
      · simp
        omega
      · rw [disjoint_singleton_right]
        intro hkT
        have := hTsub hkT
        simp at this
    have heq := h_distinct S (T ∪ {k}) hsum
    have hk_mem : k ∈ T ∪ {k} := by simp
    rw [← heq] at hk_mem
    have := hSsub hk_mem
    simp at this
  · have hlt : ∑ j ∈ S, a j < ∑ j ∈ T, a j := Nat.lt_of_not_ge hle
    have hge : ∑ j ∈ S, a j ≤ ∑ j ∈ T, a j := le_of_lt hlt
    simp [hle] at hdiff
    have hsum : ∑ j ∈ T, a j = ∑ j ∈ S ∪ {k}, a j := by
      rw [sum_union]
      · simp
        omega
      · rw [disjoint_singleton_right]
        intro hkS
        have := hSsub hkS
        simp at this
    have heq := h_distinct T (S ∪ {k}) hsum
    have hk_mem : k ∈ S ∪ {k} := by simp
    rw [← heq] at hk_mem
    have := hTsub hk_mem
    simp at this

open Finset

lemma sum_inv_le_sum_inv_of_sum_ge {n : ℕ} {a b : Fin n → ℚ}
  (ha_pos : ∀ i, 0 < a i) (hb_pos : ∀ i, 0 < b i)
  (ha_mono : StrictMono a) (hb_mono : StrictMono b)
  (h_sum : ∀ k : Fin n, ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), a i ≥ ∑ i ∈ Finset.univ.filter (fun j => j ≤ k), b i) :
  ∑ i, 1 / a i ≤ ∑ i, 1 / b i := by
    -- By Abel's lemma, we can express the sum of (1/b_i - 1/a_i) as a telescoping series.
    have h_telescope : ∑ i, (1 / b i - 1 / a i) = ∑ i, ((a i - b i) / (a i * b i)) := by
      exact Finset.sum_congr rfl fun i _ => by rw [ div_sub_div ] <;> ring_nf <;> linarith [ ha_pos i, hb_pos i ] ;
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
          intro i
          rw [show (Finset.filter (fun x : Fin n => x ≤ i) Finset.univ : Finset (Fin n)) =
              Finset.filter (fun x : Fin n => x < i) Finset.univ ∪ {i} from ?_]
          rw [Finset.sum_union]
          · rw [Finset.sum_union]
            · simp
              field_simp [ne_of_gt (ha_pos i), ne_of_gt (hb_pos i)]
              ring
            · rw [disjoint_singleton_right]
              simp
          · rw [disjoint_singleton_right]
            simp
          · ext x
            simp only [mem_filter, mem_univ, true_and, mem_union, mem_singleton]
            exact le_iff_lt_or_eq
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
  let e : Fin A.card → ℕ := fun i => A.orderEmbOfFin rfl i
  have he_inj : Function.Injective e := (A.orderEmbOfFin rfl).injective
  have hseq : HasDistinctSubsetSumsSeq e := by
    intro S T hsum
    apply Finset.image_injective he_inj
    apply hA
    · intro x hx
      rw [mem_image] at hx
      rcases hx with ⟨i, _, rfl⟩
      exact Finset.orderEmbOfFin_mem A rfl i
    · intro x hx
      rw [mem_image] at hx
      rcases hx with ⟨i, _, rfl⟩
      exact Finset.orderEmbOfFin_mem A rfl i
    · rw [sum_image, sum_image]
      · exact hsum
      · intro x _ y _ hxy
        exact he_inj hxy
      · intro x _ y _ hxy
        exact he_inj hxy
  have h_sum_ge :
      ∀ k : Fin A.card,
        ∑ i ∈ Finset.univ.filter (fun j => j.val < k.val + 1), (e i : ℚ) ≥
          2^(k.val + 1) - 1 := by
    intro k
    have hnat := sum_ge_two_pow_sub_one hseq (k.val + 1) (Nat.succ_le_of_lt k.2)
    have hcast :
        ((2 ^ (k.val + 1) - 1 : ℕ) : ℚ) = (2 : ℚ) ^ (k.val + 1) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_pow (k.val + 1) 2 (by norm_num))]
      norm_num
    have hnat_cast :
        ((2 ^ (k.val + 1) - 1 : ℕ) : ℚ) ≤
          ∑ i ∈ Finset.univ.filter (fun j => j.val < k.val + 1), (e i : ℚ) := by
      exact_mod_cast hnat
    simpa [ge_iff_le, hcast] using hnat_cast
  have h_enum_inv_le :
      (∑ i : Fin A.card, (1 / (e i : ℚ))) ≤
        (∑ i ∈ Finset.range A.card, (1 / (2 ^ i : ℚ))) := by
    rw [Finset.sum_range]
    apply sum_inv_le_sum_inv_of_sum_ge
    · intro i
      exact Nat.cast_pos.mpr (hpos (e i) (Finset.orderEmbOfFin_mem A rfl i))
    · intro i
      positivity
    · intro i j hij
      exact Nat.cast_lt.mpr (by simpa [e] using hij)
    · have h_exp_mono : StrictMono (fun i : ℕ => (2 : ℚ) ^ i) := by
        apply pow_right_strictMono₀
        norm_num
      intro i j hij
      exact h_exp_mono (by simpa using hij)
    · intro k
      have hfilter :
          Finset.univ.filter (fun j : Fin A.card => j ≤ k) =
            Finset.univ.filter (fun j : Fin A.card => j.val < k.val + 1) := by
        ext i
        simp
      rw [hfilter]
      have hpow_sum :
          (∑ i ∈ Finset.univ.filter (fun j : Fin A.card => j.val < k.val + 1),
              ((2 : ℚ) ^ i.val)) =
            ∑ i ∈ Finset.range (k.val + 1), ((2 : ℚ) ^ i) := by
        rw [← hfilter]
        refine' Finset.sum_bij (fun i _ => i.val) _ _ _ _
        · intro i hi
          simp at hi ⊢
          exact hi
        · intro i _ j _ hij
          ext
          exact hij
        · intro b hb
          simp at hb
          refine ⟨⟨b, lt_of_le_of_lt hb k.2⟩, ?_, rfl⟩
          simp
          exact hb
        · intro i _
          rfl
      have hgeom :
          ∑ i ∈ Finset.range (k.val + 1), ((2 : ℚ) ^ i) = 2^(k.val + 1) - 1 := by
        rw [geom_sum_eq] <;> norm_num
      rw [hpow_sum, hgeom]
      exact h_sum_ge k
  have hA_eq : Finset.image e (Finset.univ : Finset (Fin A.card)) = A := by
    ext x
    rw [Finset.mem_image]
    simp only [Finset.mem_univ, true_and]
    change (∃ i : Fin A.card, e i = x) ↔ x ∈ A
    rw [← Set.mem_range]
    rw [Finset.range_orderEmbOfFin]
    simp [e]
  have h_sum_A : ∑ a ∈ A, (1 : ℚ) / a = ∑ i : Fin A.card, (1 / (e i : ℚ)) := by
    calc
      ∑ a ∈ A, (1 : ℚ) / a =
          ∑ a ∈ Finset.image e (Finset.univ : Finset (Fin A.card)), (1 : ℚ) / a := by
        rw [hA_eq]
      _ = ∑ i ∈ (Finset.univ : Finset (Fin A.card)), (1 : ℚ) / e i := by
        rw [Finset.sum_image]
        intro x _ y _ hxy
        exact he_inj hxy
      _ = ∑ i : Fin A.card, (1 / (e i : ℚ)) := by
        simp
  rw [h_sum_A]
  exact h_enum_inv_le.trans_lt (by ring_nf; rw [geom_sum_eq] <;> ring_nf <;> norm_num)

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

#print axioms erdos_350
-- 'Erdos350.erdos_350' depends on axioms: [propext, Classical.choice, Quot.sound]

end

end Erdos350
