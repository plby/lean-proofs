/-

This is a Lean formalization of a solution to Erdős Problem 845.
https://www.erdosproblems.com/forum/thread/845

The original proof was found by: Wouter van Doorn, Anneroos
R.F. Everts

[vDEv25] W. van Doorn and A. Everts, Smooth sums with small
spacings. arXiv:2511.04585 (2025).


This paper was auto-formalized by Aristotle (from Harmonic).  The
final theorem statement is from the Formal Conjectures project (from
Google DeepMind).

The nice "C=6" result was not successfully formalized, but the
solution to the Erdős Problem 845 still was.


This is a smaller file, trimmed from the raw output from Aristotle.


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/

/-
We have formally proven the main result of the paper: for every odd integer p > 1, there exists a constant C such that every positive integer n can be written as a sum of distinct elements of A_p (integers of the form 2^x * p^y) where the ratio between the largest and smallest summand is bounded by C. This confirms the conjecture by Erdős regarding the existence of such a constant for 3-smooth integers (and generally for p-smooth integers where p is odd). The proof constructs the sum explicitly using the algorithm described in the paper, involving the decomposition of coefficients into sums of elements from a specific set S_p and powers of 2.
-/

import Mathlib

namespace Erdos845

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000

noncomputable section

/-
Definition of the set A_p and the functions f_k and F.
-/
def A (p : ℕ) : Set ℕ := {n | ∃ x y : ℕ, n = 2^x * p^y}

def f (k : ℕ) (x : ℕ) : ℕ :=
  match k with
  | 0 => x
  | k+1 => max 1 (Nat.log2 (f k x))

/-
Definition of S_p as the set containing p and powers of 2 up to 2^(ceil(log2 p)).
-/
def S_p (p : ℕ) : Finset ℕ :=
  {p} ∪ (Finset.Ico 1 (Nat.clog 2 p + 1)).image (2 ^ ·)

/-
The cardinality of S_p is 1 + ceil(log_2 p).
-/
theorem S_p_card (p : ℕ) (hp_odd : Odd p) (hp_gt_1 : p > 1) : (S_p p).card = Nat.clog 2 p + 1 := by
  unfold S_p;
  rw [ Finset.card_union_of_disjoint ] <;> norm_num;
  · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
    grind;
  · intro x hx₁ hx₂; exact fun hx₃ => absurd ( hx₃.symm ▸ hp_odd ) ( by simp +decide [ Nat.even_pow ] ; linarith ) ;

/-
S_p contains all powers of 2 up to 2^k where 2^k <= |S_p|.
-/
theorem S_p_contains_powers (p : ℕ) (hp_odd : Odd p) (hp_gt_1 : p > 1) (k : ℕ) (hk : 1 ≤ k) (hk' : 2^k ≤ (S_p p).card) :
  2^k ∈ S_p p := by
    have h_log : k ≤ Nat.clog 2 p := by
      -- Since $2^k \leq \text{card}(S_p)$ and $\text{card}(S_p) = \text{clog}(2, p) + 1$, we have $2^k \leq \text{clog}(2, p) + 1$.
      have h_log : 2^k ≤ Nat.clog 2 p + 1 := by
        convert hk' using 1;
        exact S_p_card p hp_odd hp_gt_1 ▸ rfl;
      contrapose! h_log;
      exact Nat.lt_of_le_of_lt ( Nat.succ_le_of_lt h_log ) ( Nat.recOn k ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at * ; linarith );
    exact Finset.mem_union_right _ ( Finset.mem_image.mpr ⟨ k, Finset.mem_Ico.mpr ⟨ hk, by linarith ⟩, rfl ⟩ )

/-
Any natural number n < 2^k can be written as a sum of distinct powers of 2 with exponents in range k.
-/
theorem binary_sum_subset (n k : ℕ) (h : n < 2^k) :
  ∃ S : Finset ℕ, S ⊆ Finset.range k ∧ S.sum (2 ^ ·) = n := by
    induction' k with k ih generalizing n <;> simp_all +decide [ Finset.sum_range_succ', pow_succ' ];
    by_cases h₂ : n < 2 ^ k;
    · exact Exists.elim ( ih n h₂ ) fun S hS => ⟨ S, Finset.Subset.trans hS.1 ( Finset.range_mono ( Nat.le_succ _ ) ), hS.2 ⟩;
    · obtain ⟨ S, hS₁, hS₂ ⟩ := ih ( n - 2 ^ k ) ( by rw [ tsub_lt_iff_left ] <;> linarith );
      exact ⟨ Insert.insert k S, Finset.insert_subset_iff.mpr ⟨ Finset.mem_range.mpr ( Nat.lt_succ_self _ ), hS₁.trans ( Finset.range_mono ( Nat.le_succ _ ) ) ⟩, by rw [ Finset.sum_insert ( Finset.notMem_mono hS₁ ( by norm_num ) ), hS₂, add_tsub_cancel_of_le ( by linarith ) ] ⟩

/-
p + |S_p| < 2^(clog 2 p + 1).
-/
theorem p_plus_card_lt_two_pow (p : ℕ) (hp_odd : Odd p) (hp_gt_1 : p > 1) :
  p + (S_p p).card < 2 ^ (Nat.clog 2 p + 1) := by
    rw [ S_p_card p hp_odd hp_gt_1 ];
    -- By definition of Nat.clog, we know that 2^(Nat.clog 2 p) > p.
    have h_clog : 2 ^ (Nat.clog 2 p) > p := by
      -- By definition of Nat.clog, we know that 2^(Nat.clog 2 p) ≥ p.
      have h_clog_ge : 2 ^ (Nat.clog 2 p) ≥ p := by
        exact Nat.le_pow_clog ( by decide ) _;
      grind;
    rw [ pow_succ' ] ; linarith [ show Nat.clog 2 p < 2 ^ Nat.clog 2 p from Nat.recOn ( Nat.clog 2 p ) ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith ]

/-
Any even number n < 2^(k+1) can be written as a sum of distinct powers of 2 with exponents in {1, ..., k}.
-/
theorem even_sum_subset_pow2 (n k : ℕ) (h_lt : n < 2 ^ (k + 1)) (h_even : Even n) :
  ∃ S : Finset ℕ, S ⊆ Finset.Ico 1 (k + 1) ∧ S.sum (2 ^ ·) = n := by
    -- Since $n$ is even, we can write $n = 2 * m$.
    obtain ⟨m, hm⟩ : ∃ m, n = 2 * m := even_iff_two_dvd.mp h_even;
    -- Since $m < 2^k$, by binary_sum_subset, $m$ can be written as a sum of distinct powers of 2 with exponents in {0, ..., k-1}.
    obtain ⟨S', hS'_subset, hS'_sum⟩ : ∃ S' : Finset ℕ, S' ⊆ Finset.range k ∧ S'.sum (2 ^ ·) = m := by
      exact binary_sum_subset m k ( by rw [ pow_succ' ] at h_lt; linarith );
    refine' ⟨ Finset.image ( fun x => x + 1 ) S', _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
    simp +decide [ ← hS'_sum, pow_succ', Finset.mul_sum _ _ _ ]

/-
Definition of is_sum_of_distinct_elements.
-/
def is_sum_of_distinct_elements (S : Finset ℕ) (n : ℕ) : Prop :=
  ∃ s : Finset ℕ, s ⊆ S ∧ s.sum id = n

/-
The set S_p covers the range [p, p + |S_p|] with its subset sums.
-/
theorem S_p_covers_range (p : ℕ) (hp_odd : Odd p) (hp_gt_1 : p > 1) :
  ∀ x, p ≤ x → x ≤ p + (S_p p).card → is_sum_of_distinct_elements (S_p p) x := by
    -- Let k = clog 2 p. Then |S_p| = k + 1.
    set k := Nat.clog 2 p;
    -- The powers of 2 in S_p are {2^1, ..., 2^k}.
    have h_powers : Finset.image (fun x => 2 ^ x) (Finset.Ico 1 (k + 1)) ⊆ S_p p := by
      exact Finset.image_subset_iff.mpr fun x hx => Finset.mem_union_right _ <| Finset.mem_image_of_mem _ hx;
    -- Let x be in [p, p + k + 1].
    intro x hx_lower hx_upper
    by_cases hx_even : Even x;
    · -- By even_sum_subset_pow2, x is a sum of distinct powers of 2 with exponents in {1, ..., k}.
      obtain ⟨S', hS'_subset, hS'_sum⟩ : ∃ S' : Finset ℕ, S' ⊆ Finset.Ico 1 (k + 1) ∧ S'.sum (2 ^ ·) = x := by
        have h_even_sum : x < 2 ^ (k + 1) := by
          have h_even_sum : p + (S_p p).card < 2 ^ (k + 1) := by
            exact p_plus_card_lt_two_pow p hp_odd hp_gt_1;
          linarith;
        exact even_sum_subset_pow2 x k h_even_sum hx_even;
      exact ⟨ Finset.image ( fun x => 2 ^ x ) S', Finset.image_subset_iff.mpr fun x hx => h_powers <| Finset.mem_image_of_mem _ <| hS'_subset hx, by rw [ Finset.sum_image <| by aesop ] ; aesop ⟩;
    · -- Since x is odd, we can write x = p + m, where m = x - p is even.
      obtain ⟨m, hm⟩ : ∃ m, x = p + m ∧ Even m := by
        simp +zetaDelta at *;
        exact ⟨ x - p, by rw [ Nat.add_sub_cancel' hx_lower ], by simpa [ hx_lower, parity_simps ] using hx_even.add_odd hp_odd ⟩;
      -- Since $m < 2^{k+1}$, by even_sum_subset_pow2, $m$ is a sum of distinct powers of 2 with exponents in {1, ..., k}.
      obtain ⟨S', hS'_subset, hS'_sum⟩ : ∃ S' : Finset ℕ, S' ⊆ Finset.Ico 1 (k + 1) ∧ S'.sum (2 ^ ·) = m := by
        have h_m_lt_two_pow : m < 2 ^ (k + 1) := by
          have := p_plus_card_lt_two_pow p hp_odd hp_gt_1;
          grind;
        exact even_sum_subset_pow2 m k h_m_lt_two_pow hm.2;
      -- These powers are in S_p \ {p}.
      have h_powers_subset : (Finset.image (fun x => 2 ^ x) S') ⊆ S_p p \ {p} := by
        grind;
      refine' ⟨ { p } ∪ Finset.image ( fun x => 2 ^ x ) S', _, _ ⟩ <;> simp_all +decide [ Finset.subset_iff ];
      · exact Finset.mem_union_left _ ( Finset.mem_singleton_self _ );
      · rw [ Finset.sum_image ] <;> aesop

/-
Lemma ssize: Existence of a set S with the required properties.
-/
theorem lemma_ssize (p : ℕ) (hp_odd : Odd p) (hp_gt_1 : p > 1) :
  ∃ S : Finset ℕ,
    (∀ x ∈ S, x ∈ A p ∧ x ≠ 1) ∧
    (∀ k : ℕ, 1 ≤ k → 2^k ≤ S.card → 2^k ∈ S) ∧
    (∃ M₀ : ℕ, M₀ ≤ p ∧ M₀ > 0 ∧
      ∀ x, M₀ ≤ x → x ≤ M₀ + S.card → is_sum_of_distinct_elements S x) ∧
    S.card ≤ 1 + Nat.clog 2 p ∧
    (∃ m ∈ S, p ≤ m ∧ ∀ x ∈ S, x ≤ m ∧ m ≤ 2^(Nat.clog 2 p)) := by
      refine' ⟨ S_p p, _, _, _, _, _ ⟩;
      · unfold S_p A;
        norm_num +zetaDelta at *;
        exact ⟨ ⟨ ⟨ 0, 1, by norm_num ⟩, by linarith ⟩, fun a x hx₁ hx₂ hx₃ => ⟨ ⟨ x, 0, by aesop ⟩, by linarith [ Nat.pow_le_pow_right two_pos hx₁ ] ⟩ ⟩;
      · exact fun k a a_1 ↦ S_p_contains_powers p hp_odd hp_gt_1 k a a_1;
      · exact ⟨ p, le_rfl, hp_gt_1.le, S_p_covers_range p hp_odd hp_gt_1 ⟩;
      · rw [ S_p_card ] <;> norm_num;
        · linarith;
        · assumption;
        · bound;
      · unfold S_p;
        simp;
        refine' Or.inr ⟨ Nat.clog 2 p, _, _, _, _ ⟩;
        · norm_num;
          exact Nat.clog_pos ( by decide ) hp_gt_1;
        · exact Nat.le_pow_clog ( by decide ) _;
        · exact ⟨ Nat.le_pow_clog ( by decide ) _, le_rfl ⟩;
        · exact fun a x hx₁ hx₂ hx₃ => ⟨ hx₃ ▸ pow_le_pow_right₀ ( by decide ) ( by linarith ), le_rfl ⟩

/-
Lemma ssize: Existence of a set S with the required properties.
-/
theorem lemma_ssize_v2 (p : ℕ) (hp_odd : Odd p) (hp_gt_1 : p > 1) :
  ∃ S : Finset ℕ,
    (∀ x ∈ S, x ∈ A p ∧ x ≠ 1) ∧
    (∀ k : ℕ, 1 ≤ k → 2^k ≤ S.card → 2^k ∈ S) ∧
    (∃ M₀ : ℕ, M₀ ≤ p ∧ M₀ > 0 ∧
      ∀ x, M₀ ≤ x → x ≤ M₀ + S.card → is_sum_of_distinct_elements S x) ∧
    S.card ≤ 1 + Nat.clog 2 p ∧
    (∃ m ∈ S, p ≤ m ∧ ∀ x ∈ S, x ≤ m ∧ m ≤ 2^(Nat.clog 2 p)) := by
      -- Apply the lemma_ssize theorem to obtain the set S.
      obtain ⟨S, hS⟩ := lemma_ssize p hp_odd hp_gt_1;
      use S

/-
Definitions of S and M_0 with their properties extracted from lemma_ssize_v2.
-/
open Classical

def S_with_props (p : ℕ) (h : Odd p ∧ p > 1) :=
  lemma_ssize_v2 p h.1 h.2

def S (p : ℕ) : Finset ℕ :=
  if h : Odd p ∧ p > 1 then (S_with_props p h).choose else ∅

def M_0 (p : ℕ) : ℕ :=
  if h : Odd p ∧ p > 1 then (S_with_props p h).choose_spec.2.2.1.choose else 0

theorem S_properties (p : ℕ) (h : Odd p ∧ p > 1) :
  let s := S p
  (∀ x ∈ s, x ∈ A p ∧ x ≠ 1) ∧
  (∀ k : ℕ, 1 ≤ k → 2^k ≤ s.card → 2^k ∈ s) ∧
  (∃ M₀ : ℕ, M₀ ≤ p ∧ M₀ > 0 ∧
    ∀ x, M₀ ≤ x → x ≤ M₀ + s.card → is_sum_of_distinct_elements s x) ∧
  s.card ≤ 1 + Nat.clog 2 p ∧
  (∃ m ∈ s, p ≤ m ∧ ∀ x ∈ s, x ≤ m ∧ m ≤ 2^(Nat.clog 2 p)) := by
    unfold S;
    have := Exists.choose_spec ( lemma_ssize_v2 p h.1 h.2 );
    split_ifs ; tauto

theorem M_0_properties (p : ℕ) (h : Odd p ∧ p > 1) :
  let m0 := M_0 p
  m0 ≤ p ∧ m0 > 0 ∧
  ∀ x, m0 ≤ x → x ≤ m0 + (S p).card → is_sum_of_distinct_elements (S p) x := by
    simp +zetaDelta at *;
    revert p;
    unfold M_0 S;
    intro p hp;
    split_ifs;
    · have := Exists.choose_spec ( lemma_ssize_v2 p hp.1 hp.2 );
      exact ⟨ this.2.2.1.choose_spec.1, this.2.2.1.choose_spec.2.1, this.2.2.1.choose_spec.2.2 ⟩;
    · tauto

/-
Definition of iterated logarithm and proof that it eventually becomes <= 1.
-/
def iter_log (n : ℕ) : ℕ → ℕ
| 0 => n
| k+1 => Nat.log2 (iter_log n k)

theorem iter_log_eventually_le_one (n : ℕ) : ∃ k, iter_log n k ≤ 1 := by
  -- Since the iter_log function reduces n by taking logarithms repeatedly, and logarithms grow slower than linear functions, this process will eventually reduce n to 1 or less.
  by_contra h_contra;
  -- If for all $k$, $iter_log n k > 1$, then the sequence $iter_log n k$ is strictly decreasing and bounded below by 1.
  have h_decreasing : StrictAnti (fun k => iter_log n k) := by
    refine' strictAnti_nat_of_succ_lt fun k => _;
    -- By definition of $iter_log$, we have $iter_log n (k + 1) = Nat.log2 (iter_log n k)$.
    simp [iter_log];
    rw [ Nat.log2_lt ];
    · exact Nat.lt_two_pow_self;
    · exact fun h => h_contra ⟨ k, h.symm ▸ by norm_num ⟩;
  exact absurd ( Set.infinite_range_of_injective h_decreasing.injective ) ( Set.not_infinite.mpr <| Set.finite_iff_bddAbove.mpr ⟨ iter_log n 0, by rintro x ⟨ k, rfl ⟩ ; exact h_decreasing.antitone <| Nat.zero_le _ ⟩ )

/-
Definitions of M, K, u, C_p and proof that M eventually becomes <= 1.
-/
open Classical

def M (p : ℕ) : ℕ → ℕ
| 0 => 0
| 1 => M_0 p + (S p).card
| 2 => (S p).card
| (k + 1) => Nat.log2 (M p k)

theorem M_eq_iter_log (p : ℕ) (k : ℕ) : M p (k + 2) = iter_log (M p 2) k := by
  induction k with
  | zero => simp [iter_log]
  | succ k ih =>
    simp [M, iter_log, ih]

theorem M_eventually_le_one (p : ℕ) (h : Odd p ∧ p > 1) :
  ∃ k, k ≥ 2 ∧ M p k ≤ 1 := by
  obtain ⟨k, hk⟩ := iter_log_eventually_le_one (M p 2)
  use k + 2
  constructor
  · linarith
  · rw [M_eq_iter_log]
    exact hk

def K (p : ℕ) : ℕ :=
  if h : ∃ k, k ≥ 2 ∧ M p k ≤ 1 then Nat.find h else 2

def u (p : ℕ) : ℕ → ℕ
| 0 => 1
| 1 => 1
| 2 => if h : (S p).Nonempty then (S p).max' h else 1
| k => 2^(M p k)

def C_p (p : ℕ) : ℕ :=
  (List.range (K p + 1)).map (u p) |>.prod

end

/-
Definitions of P (partial products) and IsShortSum.
-/
noncomputable def P (p : ℕ) (k : ℕ) : ℕ := (List.range (k + 1)).map (u p) |>.prod

/-
The set A_p is infinite.
-/
theorem A_infinite (p : ℕ) (hp : p > 1) : (A p).Infinite := by
  exact Set.infinite_of_injective_forall_mem ( fun x y hxy => by simpa using hxy ) fun x => ⟨ x, 0, rfl ⟩

/-
a_seq is the sequence of elements of A_p in increasing order.
-/
noncomputable def a_seq (p : ℕ) (n : ℕ) : ℕ :=
  if h : (A p).Infinite then (@Nat.Subtype.orderIsoOfNat (A p) (Set.Infinite.to_subtype h) n).val else 0

/-
The n-th element of the sequence a_seq is in the set A_p.
-/
theorem a_seq_mem (p : ℕ) (hp : p > 1) (n : ℕ) : a_seq p n ∈ A p := by
  have := A_infinite p hp; unfold a_seq; aesop;

/-
The sequence a_seq is strictly increasing.
-/
theorem a_seq_strict_mono (p : ℕ) (hp : p > 1) : StrictMono (a_seq p) := by
  have := @a_seq_mem p hp;
  unfold a_seq;
  simp +zetaDelta at *;
  refine' strictMono_nat_of_lt_succ fun n => _;
  simp +decide [ Nat.Subtype.ofNat ];
  split_ifs <;> simp_all +decide [ Nat.Subtype.ofNat, Nat.Subtype.succ ];
  · linarith;
  · exact absurd ‹_› ( A_infinite p hp )

/-
The elements of the sequence a_seq are positive.
-/
theorem a_seq_pos (p : ℕ) (hp : p > 1) (n : ℕ) : a_seq p n > 0 := by
  have := a_seq_mem p hp n;
  obtain ⟨ x, y, hx ⟩ := this ; contrapose! hx ; aesop

/-
partial_sum is the sum of the first k elements of the sequence a_seq.
-/
noncomputable def partial_sum (p : ℕ) (k : ℕ) : ℕ := (List.range k).map (a_seq p) |>.sum

/-
The partial sums of the sequence a_seq are unbounded.
-/
theorem partial_sum_unbounded (p : ℕ) (hp : p > 1) (B : ℕ) : ∃ k, partial_sum p k > B := by
  -- Since $a_seq$ is strictly increasing and each term is greater than or equal to $1$, the partial sum $partial\_sum p k$ is at least $k$. Thus, if we choose $k = B + 1$, the partial sum will be greater than $B$.
  have h_partial_sum : ∀ k, partial_sum p k ≥ k := by
    exact fun k => le_trans ( by norm_num ) ( List.sum_le_sum fun _ _ => a_seq_pos p hp _ );
  exact ⟨ B + 1, by linarith [ h_partial_sum ( B + 1 ) ] ⟩

/-
m_index is the smallest index such that the partial sum exceeds n / M_0.
-/
noncomputable def m_index (p n : ℕ) (hp : Odd p ∧ p > 1) : ℕ :=
  Nat.find (partial_sum_unbounded p hp.2 (n / M_0 p))

theorem m_index_spec (p n : ℕ) (hp : Odd p ∧ p > 1) :
  partial_sum p (m_index p n hp) > n / M_0 p ∧
  ∀ k < m_index p n hp, partial_sum p k ≤ n / M_0 p := by
    exact ⟨ Nat.find_spec ( partial_sum_unbounded p hp.2 ( n / M_0 p ) ), fun k hk => not_lt.1 fun hk' => hk.not_ge ( Nat.find_min' _ hk' ) ⟩

/-
The set A_p is closed under multiplication.
-/
theorem A_mul_closed (p : ℕ) : ∀ x y, x ∈ A p → y ∈ A p → x * y ∈ A p := by
  rintro x y ⟨ a, b, rfl ⟩ ⟨ c, d, rfl ⟩ ; exact ⟨ a + c, b + d, by ring ⟩ ;

/-
The sequence a_seq maps onto A_p.
-/
theorem a_seq_surjective (p : ℕ) (hp : p > 1) : ∀ x, x ∈ A p ↔ ∃ n, a_seq p n = x := by
  -- Since $a_seq$ is the order isomorphism from $N$ to $A_p$, it covers all elements of $A_p$.
  have h_iso : ∀ x ∈ A p, ∃ n, a_seq p n = x := by
    unfold a_seq;
    have h_iso : Set.Infinite (A p) := by
      exact A_infinite p hp;
    have := h_iso.to_subtype;
    exact fun x hx => ⟨ ( Nat.Subtype.orderIsoOfNat ( A p ) ).symm ⟨ x, hx ⟩, by aesop ⟩;
  exact fun x => ⟨ h_iso x, fun ⟨ n, hn ⟩ => hn ▸ a_seq_mem p hp n ⟩

/-
index_in_A returns the index of an element in A_p.
-/
noncomputable def index_in_A (p : ℕ) (x : ℕ) : ℕ :=
  if h : x ∈ A p ∧ p > 1 then Nat.find ((a_seq_surjective p h.2 x).mp h.1) else 0

/-
Every power of 2 is in A_p.
-/
theorem pow2_mem_A (p : ℕ) (k : ℕ) : 2^k ∈ A p := by
  exact ⟨ k, 0, by ring ⟩

/-
pow2_index returns the index of 2^k in the sequence a_seq.
-/
noncomputable def pow2_index (p : ℕ) (hp : p > 1) (k : ℕ) : ℕ :=
  index_in_A p (2^k)

theorem pow2_index_spec (p : ℕ) (hp : p > 1) (k : ℕ) :
  a_seq p (pow2_index p hp k) = 2^k := by
    unfold pow2_index;
    unfold index_in_A;
    split_ifs <;> simp_all +decide [ pow2_mem_A ];
    exact Nat.find_spec ( a_seq_surjective p ( by tauto ) _ |>.mp ( by tauto ) )

/-
The index of 2^k in the sequence a_seq is strictly less than 2^k.
-/
theorem pow2_index_lt (p : ℕ) (hp : p > 1) (k : ℕ) :
  pow2_index p hp k < 2^k := by
    -- Since $a_seq$ is strictly increasing and its values are positive integers (>= 1), we have $a_seq n \geq n + 1$ for all $n$.
    have h_strict_mono : ∀ n, a_seq p n ≥ n + 1 := by
      intro n;
      induction' n with n ih;
      · exact Nat.one_le_iff_ne_zero.mpr ( ne_of_gt ( a_seq_pos p hp 0 ) );
      · exact Nat.succ_le_of_lt ( lt_of_le_of_lt ih ( a_seq_strict_mono p hp n.lt_succ_self ) );
    exact lt_of_not_ge fun h => by linarith [ h_strict_mono ( pow2_index p hp k ), pow2_index_spec p hp k ] ;

/-
If 2^k <= R, then the index of 2^k in a_seq is strictly less than R + 1.
-/
theorem pow2_index_le_R (p : ℕ) (hp : p > 1) (R k : ℕ) (h : 2^k ≤ R) :
  pow2_index p hp k < R + 1 := by
    linarith [ pow2_index_lt p hp k ]

/-
The function pow2_index is injective.
-/
theorem pow2_index_injective (p : ℕ) (hp : p > 1) : Function.Injective (pow2_index p hp) := by
  intro x y; have := pow2_index_spec p hp x; have := pow2_index_spec p hp y; aesop;

/-
coeff_from_binary is the coefficient of the i-th element of a_seq in the binary representation of R.
-/
noncomputable def coeff_from_binary (p : ℕ) (R : ℕ) (i : ℕ) : ℕ :=
  let x := a_seq p i
  if x = 2 ^ (Nat.log2 x) ∧ R.testBit (Nat.log2 x) then 1 else 0

/-
The coefficient is 1 if and only if the index corresponds to a power of 2 that is present in the binary expansion of R.
-/
theorem coeff_nonzero_iff (p : ℕ) (hp : p > 1) (R i : ℕ) :
  coeff_from_binary p R i = 1 ↔ ∃ k, i = pow2_index p hp k ∧ R.testBit k := by
    -- By definition of `coeff_from_binary`, it is 1 if and only if `a_seq p i` is a power of 2 and `R.testBit (Nat.log2 (a_seq p i))` is true.
    simp [coeff_from_binary];
    constructor;
    · intro h
      obtain ⟨k, hk⟩ : ∃ k, a_seq p i = 2^k := by
        exact ⟨ _, h.1 ⟩;
      use k;
      have h_pow2_index : pow2_index p hp k = i := by
        have := a_seq_strict_mono p hp;
        -- Since $a_seq p$ is strictly monotonic, the index of $2^k$ in $a_seq p$ is unique.
        have h_unique : ∀ j, a_seq p j = 2 ^ k → j = i := by
          exact fun j hj => this.injective <| hj.trans hk.symm;
        exact h_unique _ ( pow2_index_spec p hp k );
      grind +ring;
    · norm_num +zetaDelta at *;
      intro k hk hk'; rw [ hk ] ; have := pow2_index_spec p hp k; aesop;

/-
k is in the bitIndices of n if and only if the k-th bit of n is set.
-/
theorem mem_bitIndices_iff_testBit (n k : ℕ) :
  k ∈ n.bitIndices ↔ n.testBit k := by
    induction' n using Nat.strong_induction_on with n ih generalizing k;
    rcases k with ( _ | k ) <;> simp_all +decide [ Nat.testBit ];
    · cases Nat.mod_two_eq_zero_or_one n <;> simp +decide [ *, Nat.bitIndices ];
      · rw [ Nat.binaryRec ] ; aesop;
      · rw [ Nat.binaryRec ] ; aesop;
    · rcases Nat.even_or_odd' n with ⟨ c, rfl | rfl ⟩ <;> simp_all +decide [ Nat.shiftRight_eq_div_pow ];
      · rcases c with ( _ | c ) <;> simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
      · convert ih c ( by linarith ) k using 1 ; norm_num [ Nat.add_div, Nat.pow_succ', ← Nat.div_div_eq_div_mul ]

/-
The set of indices where the coefficient is 1 corresponds to the image of the set bits of R under the pow2_index map.
-/
theorem image_pow2_index_eq_filter (p : ℕ) (hp : p > 1) (R : ℕ) :
  Finset.image (pow2_index p hp) R.bitIndices.toFinset =
  (Finset.range (R + 1)).filter (fun i => coeff_from_binary p R i = 1) := by
    ext;
    simp +zetaDelta at *;
    constructor;
    · rintro ⟨ k, hk₁, rfl ⟩;
      -- Since $k \in R.bitIndices$, we have $R.testBit k$.
      have h_testBit : R.testBit k := by
        exact (mem_bitIndices_iff_testBit R k).mp hk₁;
      exact ⟨ pow2_index_le_R p hp R k <| Nat.le_of_not_lt fun h => by rw [ Nat.testBit_eq_false_of_lt h ] at h_testBit; contradiction, by rw [ coeff_nonzero_iff ] ; aesop ⟩;
    · intro h
      obtain ⟨i, hi⟩ := coeff_nonzero_iff p hp R ‹_› |>.1 h.right;
      use i;
      rw [ mem_bitIndices_iff_testBit ] ; aesop

/-
The sum of terms selected by coeff_from_binary is equal to R.
-/
theorem coeff_from_binary_sum (p : ℕ) (hp : p > 1) (R : ℕ) :
  ∑ i ∈ Finset.range (R + 1), (coeff_from_binary p R i) * a_seq p i = R := by
    -- The set of indices where the coefficient is 1 corresponds to the image of the set bits of R under the pow2_index map.
    have h_image : Finset.image (pow2_index p hp) R.bitIndices.toFinset = (Finset.range (R + 1)).filter (fun i => coeff_from_binary p R i = 1) := by
      convert image_pow2_index_eq_filter p hp R using 1;
    -- Using the image_pow2_index_eq_filter and the injectivity of pow2_index, we can transform the sum to a sum over k in R.bitIndices.toFinset of a_seq p (pow2_index p hp k).
    have h_sum_image : ∑ i ∈ Finset.range (R + 1), coeff_from_binary p R i * a_seq p i = ∑ k ∈ R.bitIndices.toFinset, a_seq p (pow2_index p hp k) := by
      have h_sum_image : ∑ i ∈ Finset.range (R + 1), coeff_from_binary p R i * a_seq p i = ∑ i ∈ (Finset.range (R + 1)).filter (fun i => coeff_from_binary p R i = 1), a_seq p i := by
        simp +decide [ Finset.sum_filter, coeff_from_binary ];
      rw [ h_sum_image, ← h_image, Finset.sum_image ];
      exact fun x hx y hy hxy => pow2_index_injective p hp hxy;
    rw [ h_sum_image, Finset.sum_congr rfl fun x hx => pow2_index_spec p hp x ];
    convert Finset.twoPowSum_toFinset_bitIndices R

/-
m is positive for positive n.
-/
noncomputable def m (p n : ℕ) (hp : Odd p ∧ p > 1) : ℕ := m_index p n hp

theorem m_pos (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) : m p n hp > 0 := by
  -- Since $n > 0$, we have $n / M_0 p \geq 0$. The partial sum $partial\_sum p 0 = 0$, so $k = 0$ does not satisfy the condition. Thus, the smallest $k$ must be $> 0$.
  have h_partial_sum_zero : partial_sum p 0 = 0 := by
    rfl;
  unfold m;
  exact Nat.pos_of_ne_zero ( by rintro h; have := m_index_spec p n hp; aesop )

/-
R is the remainder after subtracting the initial part of the sum. It is non-negative.
-/
noncomputable def R (p n : ℕ) (hp : Odd p ∧ p > 1) : ℕ :=
  n - M_0 p * partial_sum p (m p n hp - 1)

theorem R_nonneg (p n : ℕ) (hp : Odd p ∧ p > 1) :
  M_0 p * partial_sum p (m p n hp - 1) ≤ n := by
    -- By definition of $m$, we know that $partial_sum p (m - 1) \leq n / M_0 p$.
    have h_partial_sum : partial_sum p (m p n hp - 1) ≤ n / M_0 p := by
      by_cases h : m p n hp = 0;
      · simp_all +decide [ m ];
        unfold partial_sum; norm_num;
      · exact le_of_not_gt fun h' => Nat.find_min ( _ : ∃ k, partial_sum p k > n / M_0 p ) ( Nat.sub_lt ( Nat.pos_of_ne_zero h ) zero_lt_one ) h';
    exact le_trans ( Nat.mul_le_mul_left _ h_partial_sum ) ( Nat.mul_div_le _ _ )

/-
The weighted sum of c_init coefficients is equal to n.
-/
noncomputable def c_init (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) : ℕ :=
  let base := if i < m p n hp - 1 then M_0 p else 0
  let binary := coeff_from_binary p (R p n hp) i
  base + binary

theorem n_eq_sum_c_init (p n : ℕ) (hp : Odd p ∧ p > 1) :
  ∑ i ∈ Finset.range (R p n hp + m p n hp), (c_init p n hp i) * a_seq p i = n := by
    unfold m R c_init;
    by_cases h : m p n hp = 0 <;> simp_all +decide [ Finset.sum_add_distrib, add_mul ];
    · unfold m at h;
      unfold m_index at h;
      unfold partial_sum at h; aesop;
    · -- The sum of the coefficients times the sequence elements splits into two parts: the base part and the binary part.
      have h_split : (∑ i ∈ Finset.range (n - M_0 p * partial_sum p (m p n hp - 1) + m p n hp), if i < m p n hp - 1 then M_0 p * a_seq p i else 0) = M_0 p * partial_sum p (m p n hp - 1) ∧ (∑ i ∈ Finset.range (n - M_0 p * partial_sum p (m p n hp - 1) + m p n hp), coeff_from_binary p (R p n hp) i * a_seq p i) = R p n hp := by
        constructor <;> norm_num [ Finset.sum_ite ];
        · rw [ ← Finset.mul_sum _ _ _, show Finset.filter ( fun x => x < m p n hp - 1 ) ( Finset.range ( n - M_0 p * partial_sum p ( m p n hp - 1 ) + m p n hp ) ) = Finset.range ( m p n hp - 1 ) from ?_ ];
          · rfl;
          · grind;
        · convert coeff_from_binary_sum p hp.2 ( n - M_0 p * partial_sum p ( m p n hp - 1 ) ) using 1;
          -- Since the coefficients beyond $R p n hp + 1$ are zero, the sum up to $R p n hp + m p n hp$ is equal to the sum up to $R p n hp + 1$.
          have h_zero_coeff : ∀ i ≥ R p n hp + 1, coeff_from_binary p (R p n hp) i = 0 := by
            intro i hi;
            unfold coeff_from_binary;
            -- Since $i \geq R p n hp + 1$, we have $a_seq p i \geq i \geq R p n hp + 1$.
            have h_ai_ge_R : a_seq p i ≥ R p n hp + 1 := by
              have h_ai_ge_R : a_seq p i ≥ i := by
                have h_a_seq_ge_i : StrictMono (a_seq p) := by
                  exact a_seq_strict_mono p hp.2;
                exact h_a_seq_ge_i.id_le i;
              linarith;
            simp +zetaDelta at *;
            intro h_eq;
            rw [ Nat.testBit_eq_false_of_lt ];
            linarith;
          rw [ ← Finset.sum_subset ( Finset.range_mono ( Nat.succ_le_of_lt ( Nat.lt_add_of_pos_right ( Nat.pos_of_ne_zero h ) ) ) ) ] ; aesop;
          aesop;
      linarith! [ Nat.sub_add_cancel ( show M_0 p * partial_sum p ( m p n hp - 1 ) ≤ n from R_nonneg p n hp ) ]

/-
decompose_even_pow2 decomposes x or x-1 into a sum of distinct even powers of 2.
-/
noncomputable def decompose_even_pow2 (x : ℕ) : Finset ℕ :=
  if Even x then (x.bitIndices.map (2 ^ ·)).toFinset else ((x - 1).bitIndices.map (2 ^ ·)).toFinset

theorem decompose_even_pow2_spec (x : ℕ) (hx : x > 1) :
  let s := decompose_even_pow2 x
  (s.sum id = x ∨ s.sum id = x - 1) ∧
  (∀ y ∈ s, ∃ k ≥ 1, y = 2^k) := by
    refine' ⟨ _, _ ⟩;
    · unfold decompose_even_pow2;
      split_ifs <;> simp_all +decide [ Nat.even_iff ];
      · have h_binary_sum : ∑ k ∈ x.bitIndices.toFinset, 2^k = x := by
          induction' ( Nat.digits 2 x ) using List.reverseRecOn with d _ ih <;> simp_all +decide [ Nat.ofDigits ];
        convert Or.inl h_binary_sum using 2;
        refine' Finset.sum_bij ( fun k hk => Nat.log 2 k ) _ _ _ _ <;> aesop;
      · -- By definition of `bitIndices`, the sum of the elements in the list `List.map (fun x => 2 ^ x) (x - 1).bitIndices` is equal to `x - 1`.
        have h_sum_bitIndices : ∑ x ∈ (List.map (fun x => 2 ^ x) (x - 1).bitIndices).toFinset, x = (x - 1) := by
          have h_sum_bitIndices : ∑ x ∈ (Nat.bitIndices (x - 1)).toFinset, 2 ^ x = x - 1 := by
            aesop;
          convert h_sum_bitIndices using 1;
          refine' Finset.sum_bij ( fun y hy => Nat.log 2 y ) _ _ _ _ <;> aesop;
        exact Or.inr h_sum_bitIndices;
    · rcases Nat.even_or_odd' x with ⟨ c, rfl | rfl ⟩ <;> simp_all +decide [ decompose_even_pow2 ]

/-
1 is in A_p.
-/
theorem one_mem_A (p : ℕ) : 1 ∈ A p := by
  exact ⟨ 0, 0, by norm_num ⟩

/-
u_k is in A_p.
-/
theorem u_mem_A (p : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) : u p k ∈ A p := by
  rcases k with ( _ | _ | _ | k ) <;> simp_all +decide [ u ];
  · exact ⟨ 0, 0, rfl ⟩;
  · exact ⟨ 0, 0, rfl ⟩;
  · split_ifs with h;
    · exact S_properties p hp |>.1 _ ( Finset.max'_mem _ h ) |>.1;
    · exact one_mem_A p;
  · exact ⟨ M p ( k + 1 + 1 + 1 ), 0, by norm_num ⟩

/-
P_k is in A_p.
-/
theorem P_mem_A (p : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) : P p k ∈ A p := by
  induction' k with k ihk;
  · exact one_mem_A p;
  · -- By definition of $P$, we have $P p (k + 1) = P p k * u p (k + 1)$.
    have hP_succ : P p (k + 1) = P p k * u p (k + 1) := by
      exact Finset.prod_range_succ _ _;
    exact hP_succ.symm ▸ A_mul_closed p _ _ ihk ( u_mem_A p hp _ )

/-
a_seq at the index returned by index_in_A is the element itself.
-/
theorem a_seq_index_in_A (p : ℕ) (hp : p > 1) (x : ℕ) (hx : x ∈ A p) :
  a_seq p (index_in_A p x) = x := by
    unfold index_in_A;
    grind

/-
Definition of v_k and its property.
-/
noncomputable def v (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) : ℕ :=
  index_in_A p (P p k * a_seq p (m p n hp - 1))

theorem v_spec (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) :
  a_seq p (v p n hp k) = P p k * a_seq p (m p n hp - 1) := by
    -- By definition of `index_in_A`, we know that `a_seq p (index_in_A p x) = x`.
    apply a_seq_index_in_A;
    · exact hp.2;
    · exact A_mul_closed p _ _ ( P_mem_A p hp k ) ( a_seq_mem p hp.2 _ )

/-
Definition of decompose_S which decomposes a number into a sum of distinct elements of S.
-/
noncomputable def decompose_S (p : ℕ) (hp : Odd p ∧ p > 1) (x : ℕ) : Finset ℕ :=
  if h : M_0 p ≤ x ∧ x ≤ M_0 p + (S p).card then
    (M_0_properties p hp).2.2 x h.1 h.2 |>.choose
  else ∅

theorem decompose_S_spec (p : ℕ) (hp : Odd p ∧ p > 1) (x : ℕ) (h : M_0 p ≤ x ∧ x ≤ M_0 p + (S p).card) :
  (decompose_S p hp x) ⊆ S p ∧ (decompose_S p hp x).sum id = x := by
    unfold decompose_S;
    have := Classical.choose_spec ( M_0_properties p hp |>.2.2 x h.1 h.2 ) ; aesop;

/-
Definition of target_index and its property.
-/
noncomputable def target_index (p : ℕ) (i : ℕ) (s : ℕ) : ℕ :=
  index_in_A p (s * a_seq p i)

theorem target_index_spec (p : ℕ) (hp : p > 1) (i : ℕ) (s : ℕ) (hs : s ∈ A p) :
  a_seq p (target_index p i s) = s * a_seq p i := by
    exact a_seq_index_in_A p hp _ ( A_mul_closed p _ _ hs ( a_seq_mem p hp i ) )

/-
S is nonempty.
-/
theorem S_nonempty (p : ℕ) (hp : Odd p ∧ p > 1) : (S p).Nonempty := by
  have := S_properties p hp;
  exact ⟨ _, this.2.2.2.2.choose_spec.1 ⟩

/-
Elements of S are bounded by u_2.
-/
theorem s_in_S_le_u2 (p : ℕ) (hp : Odd p ∧ p > 1) (s : ℕ) (hs : s ∈ S p) : s ≤ u p 2 := by
  unfold u;
  split_ifs <;> [ exact Finset.le_max' _ _ hs; exact le_trans ( by aesop ) ( Nat.zero_le _ ) ]

/-
Elements of decompose_even_pow2 x are less than or equal to x.
-/
theorem decompose_even_pow2_le (x : ℕ) (hx : x > 1) :
  ∀ s ∈ decompose_even_pow2 x, s ≤ x := by
    intros s hs
    simp [decompose_even_pow2] at hs;
    split_ifs at hs <;> simp_all +decide [ Nat.even_iff ];
    · obtain ⟨ a, ha, rfl ⟩ := hs;
      exact Nat.two_pow_le_of_mem_bitIndices ha;
    · rcases hs with ⟨ a, ha, rfl ⟩;
      -- Since $a$ is in the bit indices of $x-1$, we have $2^a \leq x-1$.
      have h_le : 2 ^ a ≤ x - 1 := by
        exact Nat.two_pow_le_of_mem_bitIndices ha;
      exact le_trans h_le ( Nat.pred_le _ )

/-
index_in_A is the left inverse of a_seq.
-/
theorem index_a_seq_eq_self (p : ℕ) (hp : p > 1) (i : ℕ) :
  index_in_A p (a_seq p i) = i := by
    unfold index_in_A;
    split_ifs <;> simp_all +decide [ Nat.find_eq_iff ];
    · exact fun n hn => ne_of_lt <| a_seq_strict_mono p ( by linarith ) hn;
    · exact False.elim <| ‹a_seq p i ∉ A p› <| a_seq_mem p hp i

/-
P_1 is 1.
-/
theorem P_1_eq_1 (p : ℕ) : P p 1 = 1 := by
  exact rfl

/-
v_1 is m-1.
-/
theorem v_1_eq_m_sub_1 (p n : ℕ) (hp : Odd p ∧ p > 1) :
  v p n hp 1 = m p n hp - 1 := by
  rw [v, P_1_eq_1]
  simp
  apply index_a_seq_eq_self
  exact hp.2

/-
u_k is at least 1.
-/
theorem u_ge_one (p : ℕ) (k : ℕ) : 1 ≤ u p k := by
  rcases k with ( _ | _ | _ | k ) <;> simp +arith +decide [ u ];
  · split_ifs <;> norm_num;
    have := S_properties p ⟨ by
      unfold S at *; aesop, by
      unfold S at * ; aesop ⟩
    generalize_proofs at *;
    exact this.2.2.2.2.choose_spec.2.1.trans' ( Nat.one_le_iff_ne_zero.mpr <| by aesop ) |> le_trans <| Finset.le_max' _ _ this.2.2.2.2.choose_spec.1;
  · exact Nat.one_le_pow _ _ ( by decide )

/-
P_k is monotone.
-/
theorem P_mono (p : ℕ) : Monotone (P p) := by
  intro;
  unfold P;
  intro b hb; induction hb <;> simp_all +decide [ List.range_succ ];
  exact le_trans ‹_› ( Nat.mul_le_mul_left _ ( Nat.le_mul_of_pos_right _ ( u_ge_one _ _ ) ) )

/-
M_k is at least 1 for k <= K.
-/
theorem M_ge_one_of_le_K (p : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ K p) :
  M p k ≥ 1 := by
    induction' k using Nat.strong_induction_on with k ih;
    rcases k with ( _ | _ | _ | k ) <;> simp +arith +decide [ * ] at *;
    · -- Since $M_0 p$ is positive and $|S p|$ is positive, their sum $M p 1$ is also positive.
      have hM0_pos : 0 < M_0 p := by
        exact ( M_0_properties p hp ) |>.2.1;
      exact le_add_of_le_of_nonneg hM0_pos ( Nat.zero_le _ );
    · exact Finset.card_pos.mpr ⟨ _, Classical.choose_spec <| S_nonempty p hp ⟩;
    · -- Since $M p (k + 2) \geq 2$, we have $\log_2(M p (k + 2)) \geq 1$.
      have h_log_ge_one : 1 ≤ Nat.log2 (M p (k + 2)) := by
        rw [ Nat.le_log2 ];
        · unfold K at hk;
          aesop;
        · exact ne_of_gt ( ih _ le_rfl ( by linarith ) ( by linarith ) );
      exact h_log_ge_one

theorem v_strict_mono (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : 1 ≤ k ∧ k < K p) :
  v p n hp k < v p n hp (k + 1) := by
    -- Since $M (k+1) \geq 1$, we have $u (k+1) = 2^{M (k+1)} \geq 2$.
    have h_u_k1_ge_2 : 2 ≤ u p (k + 1) := by
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ u ];
      · split_ifs <;> simp_all +decide [ Finset.max' ];
        · have := S_properties p hp;
          exact ⟨ _, this.2.2.2.2.choose_spec.1, by linarith [ this.2.2.2.2.choose_spec.2.1, hp.2 ] ⟩;
        · exact absurd ‹_› ( Finset.Nonempty.ne_empty ( S_nonempty p hp ) );
      · refine' Nat.le_self_pow _ _ ; norm_num;
        -- Since $k + 1 + 1 < K p$, we have $M p (k + 1 + 1 + 1) \geq 1$.
        have h_M_ge_one : 1 ≤ M p (k + 1 + 1 + 1) := by
          apply M_ge_one_of_le_K p hp (k + 1 + 1 + 1) ⟨by linarith, by linarith⟩;
        linarith;
    -- Since $P (k+1) = P k * u (k+1)$ and $u (k+1) \geq 2$, we have $P (k+1) > P k$.
    have h_P_k1_gt_P_k : P p (k + 1) > P p k := by
      have h_P_k1_eq_P_k_mul_u_k1 : P p (k + 1) = P p k * u p (k + 1) := by
        exact List.prod_range_succ _ _;
      -- Since $P p k$ is positive and $u p (k + 1) \geq 2$, their product $P p (k + 1)$ is strictly greater than $P p k$.
      have h_P_k_pos : 0 < P p k := by
        have h_P_k_pos : ∀ k, 0 < P p k := by
          intro k; induction k <;> simp_all +decide [ P, List.range_succ ] ;
          · exact Nat.one_pos;
          · exact Nat.zero_lt_of_lt ( u_ge_one p _ );
        exact h_P_k_pos k;
      nlinarith;
    have h_v_k1_gt_v_k : a_seq p (v p n hp (k + 1)) > a_seq p (v p n hp k) := by
      rw [ v_spec, v_spec ];
      exact Nat.mul_lt_mul_of_pos_right h_P_k1_gt_P_k ( a_seq_pos p hp.2 _ );
    exact lt_of_not_ge fun h => h_v_k1_gt_v_k.not_ge <| by simpa using a_seq_strict_mono p hp.2 |>.monotone h;

/-
Definition of the final step index and the final coefficients.
-/
noncomputable def final_step_index (p n : ℕ) (hp : Odd p ∧ p > 1) : ℕ := v p n hp (K p) + 1

/-
M_K is at most 1.
-/
theorem M_K_le_one (p : ℕ) (hp : Odd p ∧ p > 1) :
  M p (K p) ≤ 1 := by
    -- By definition of $K$, we know that $K \geq 2$ and $M p K \leq 1$.
    have hK_def : ∃ k, 2 ≤ k ∧ M p k ≤ 1 := by
      exact M_eventually_le_one p hp;
    unfold K;
    split_ifs <;> [ exact Nat.find_spec hK_def |>.2; trivial ]

/-
p is less than or equal to u_2.
-/
theorem p_le_u2 (p : ℕ) (hp : Odd p ∧ p > 1) : p ≤ u p 2 := by
  rcases hp with ⟨ hp_odd, hp_gt_1 ⟩;
  obtain ⟨ m, hm₁, hm₂ ⟩ := S_properties p ⟨ hp_odd, hp_gt_1 ⟩ |>.2.2.2.2;
  unfold u;
  split_ifs <;> simp_all +decide [ Finset.max' ];
  exact ⟨ m, hm₁, hm₂.1 ⟩

/-
If a_i > R, then the coefficient from binary expansion is 0.
-/
theorem coeff_from_binary_eq_zero_of_gt (p : ℕ) (hp : p > 1) (R i : ℕ) (h : a_seq p i > R) :
  coeff_from_binary p R i = 0 := by
    unfold coeff_from_binary;
    norm_num +zetaDelta at *;
    intro h_eq;
    rw [ Nat.testBit_eq_false_of_lt ];
    linarith

/-
The remainder R is less than M_0 * a_{m-1}.
-/
theorem R_lt_M0_am_sub_1 (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) :
  R p n hp < M_0 p * a_seq p (m p n hp - 1) := by
    -- By definition of $R$, we have $R = n - M_0 \cdot \text{partial\_sum}(m-1)$.
    have hR : R p n hp = n - M_0 p * partial_sum p (m p n hp - 1) := by
      exact rfl;
    rw [ hR, tsub_lt_iff_left ];
    · -- By definition of $m$, we know that $M_0 \cdot \text{partial\_sum}(m) > n$.
      have h_m : M_0 p * partial_sum p (m p n hp) > n := by
        have := m_index_spec p n hp;
        nlinarith! [ Nat.div_add_mod n ( M_0 p ), Nat.mod_lt n ( show M_0 p > 0 from ( M_0_properties p hp ).2.1 ) ];
      rcases k : m p n hp <;> simp_all +decide [ partial_sum ];
      simpa [ List.range_succ, mul_add ] using h_m;
    · convert R_nonneg p n hp

/-
M_0 is less than or equal to P_2.
-/
theorem M_0_le_P2 (p : ℕ) (hp : Odd p ∧ p > 1) : M_0 p ≤ P p 2 := by
  have hM0_le_u2 : M_0 p ≤ u p 2 := by
    exact le_trans ( M_0_properties p hp |>.1 ) ( p_le_u2 p hp );
  unfold P;
  simp_all +decide [ List.range_succ ];
  unfold u; aesop;

/-
The remainder R is strictly less than P_2 * a_{m-1}.
-/
theorem R_lt_P2_am_sub_1 (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) :
  R p n hp < P p 2 * a_seq p (m p n hp - 1) := by
    exact lt_of_lt_of_le ( R_lt_M0_am_sub_1 p n hp hn ) ( Nat.mul_le_mul_right _ ( M_0_le_P2 p hp ) )

/-
v_{k-1} is greater than or equal to v_2 for k >= 3.
-/
theorem v_ge_v2_of_ge_3 (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : k ≥ 3) (hk_le : k ≤ K p) :
  v p n hp (k - 1) ≥ v p n hp 2 := by
    -- Since $k \geq 3$, we have $k - 1 \geq 2$.
    have h_k_minus_1_ge_2 : k - 1 ≥ 2 := by
      exact Nat.le_pred_of_lt hk;
    -- Since $v$ is strictly increasing (by `v_strict_mono`), we have $v_{k-1} \geq v_2$.
    have h_v_mono : ∀ (i j : ℕ), 1 ≤ i → i ≤ j → j ≤ K p → v p n hp i ≤ v p n hp j := by
      intros i j hi hj hjK
      induction' hj with j hj ih;
      · rfl;
      · exact le_trans ( ih ( Nat.le_of_succ_le hjK ) ) ( Nat.le_of_lt ( v_strict_mono p n hp _ ⟨ by linarith [ Nat.succ_le_succ hj ], hjK ⟩ ) );
    exact h_v_mono 2 ( k - 1 ) ( by decide ) ( by linarith ) ( by omega )

/-
K is at least 2.
-/
theorem K_ge_2 (p : ℕ) : K p ≥ 2 := by
  unfold K; aesop;

/-
If j > v K, then c_init j = 0.
-/
theorem c_init_eq_zero_of_gt_vK (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (hj : j > v p n hp (K p)) :
  c_init p n hp j = 0 := by
    have h_coeff_zero : a_seq p j > R p n hp := by
      have h_a_j_gt_R : a_seq p j > P p (K p) * a_seq p (m p n hp - 1) := by
        exact a_seq_strict_mono p hp.2 hj |> fun h => h.trans_le' <| by rw [ v_spec ] ;
      refine lt_of_le_of_lt ?_ h_a_j_gt_R;
      refine' le_trans _ ( Nat.mul_le_mul_right _ ( show P p ( K p ) ≥ P p 2 from _ ) );
      · by_cases hn : n > 0;
        · exact le_of_lt ( R_lt_P2_am_sub_1 p n hp hn );
        · unfold R; aesop;
      · exact P_mono p ( by linarith [ K_ge_2 p ] );
    have h_coeff_zero : coeff_from_binary p (R p n hp) j = 0 := by
      apply coeff_from_binary_eq_zero_of_gt;
      · exact hp.2;
      · exact h_coeff_zero;
    unfold c_init;
    have h_base_zero : m p n hp - 1 ≤ v p n hp (K p) := by
      have h_v_mono : ∀ k, 1 ≤ k → k ≤ K p → v p n hp k ≥ v p n hp 1 := by
        intros k hk1 hk2
        induction' hk1 with k hk ih;
        · norm_num;
        · exact le_trans ( ih ( Nat.le_of_succ_le hk2 ) ) ( Nat.le_of_lt ( v_strict_mono p n hp k ⟨ hk, Nat.lt_of_succ_le hk2 ⟩ ) );
      exact le_trans ( by rw [ v_1_eq_m_sub_1 ] ) ( h_v_mono _ ( by linarith [ K_ge_2 p ] ) ( by linarith [ K_ge_2 p ] ) );
    grind

/-
The set S contains at least one odd number.
-/
theorem exists_odd_in_S (p : ℕ) (hp : Odd p ∧ p > 1) :
  ∃ x ∈ S p, Odd x := by
    by_contra h_even_S
    have h_even_subset_sum : ∀ x ∈ (S p).powerset, Even (x.sum id) := by
      exact fun x hx => even_iff_two_dvd.mpr <| Finset.dvd_sum fun y hy => even_iff_two_dvd.mp <| by aesop;
    have h_odd_interval : ∃ x ∈ Finset.Icc (M_0 p) (M_0 p + (S p).card), Odd x := by
      by_cases h_even_interval : Even (M_0 p);
      · exact ⟨ M_0 p + 1, Finset.mem_Icc.mpr ⟨ by linarith, by linarith [ show 0 < Finset.card ( S p ) from Finset.card_pos.mpr ( S_nonempty p hp ) ] ⟩, by simpa [ parity_simps ] using h_even_interval ⟩;
      · exact ⟨ M_0 p, Finset.mem_Icc.mpr ⟨ le_rfl, Nat.le_add_right _ _ ⟩, by simpa using h_even_interval ⟩
    obtain ⟨x, hx_interval, hx_odd⟩ := h_odd_interval
    have hx_subset_sum : ∃ s ∈ (S p).powerset, s.sum id = x := by
      have := M_0_properties p hp; aesop;
    obtain ⟨s, hs_powerset, hs_sum⟩ := hx_subset_sum
    have hs_even : Even (s.sum id) := by
      exact h_even_subset_sum s hs_powerset
    rw [hs_sum] at hs_even
    exact absurd hs_even (by simp [hx_odd])

/-
There exists an element in S that is not a power of 2.
-/
theorem exists_non_pow2_in_S (p : ℕ) (hp : Odd p ∧ p > 1) :
  ∃ x ∈ S p, ∀ k, x ≠ 2^k := by
    obtain ⟨ x, hx₁, hx₂ ⟩ := exists_odd_in_S p hp;
    refine' ⟨ x, hx₁, fun k hk => _ ⟩;
    cases k <;> simp_all +decide [ Nat.even_pow ];
    · have := S_properties p hp;
      exact this.1 1 hx₁ |>.2 rfl;
    · exact absurd hx₂ ( by simp +decide [ Nat.even_pow ] )

/-
If c_init is greater than M_0, then a_i is a power of 2.
-/
theorem c_init_gt_M0_imp_pow2 (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ)
  (hi : i ≤ v p n hp 1) (h_gt : c_init p n hp i > M_0 p) :
  ∃ k, a_seq p i = 2^k := by
    unfold c_init at h_gt;
    split_ifs at h_gt <;> simp_all +decide [ coeff_from_binary ];
    · grind;
    · split_ifs at h_gt <;> norm_num at h_gt;
      exact ⟨ _, by tauto ⟩

/-
If s > 1, then the target index of s from k is strictly greater than k.
-/
theorem target_index_gt_self (p : ℕ) (hp : p > 1) (k : ℕ) (s : ℕ) (hs : s > 1) (hs_in_A : s ∈ A p) :
  target_index p k s > k := by
    -- By definition of $a_seq$, we have $a_seq p (target_index p k s) = s * a_seq p k$.
    have h_target_eq : a_seq p (target_index p k s) = s * a_seq p k := by
      exact target_index_spec p hp k s hs_in_A;
    contrapose! h_target_eq;
    refine' ne_of_lt ( lt_of_le_of_lt _ ( lt_mul_of_one_lt_left _ hs ) );
    · -- Since $a_seq$ is strictly monotone, we have $a_seq p (target_index p k s) \leq a_seq p k$ if and only if $target_index p k s \leq k$.
      have h_mono : StrictMono (a_seq p) := by
        exact a_seq_strict_mono p hp;
      exact h_mono.monotone h_target_eq;
    · exact a_seq_pos p hp k

/-
Recursive definition of P.
-/
theorem lemma_P_recursive (p : ℕ) (k : ℕ) (hk : k ≥ 1) : P p k = P p (k - 1) * u p k := by
  rcases k with ( _ | k ) <;> simp_all +decide [ pow_succ' ];
  unfold P;
  simp +decide [ List.range_succ ];
  ring

/-
For indices j < m-1, the initial coefficient c_init is between M_0 and M_0 + 1.
-/
theorem c_init_bounds_lt_m (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (hj : j < m p n hp - 1) :
  M_0 p ≤ c_init p n hp j ∧ c_init p n hp j ≤ M_0 p + 1 := by
    unfold c_init;
    unfold coeff_from_binary;
    grind +ring

/-
The decomposition of any number x using S is always a subset of S.
-/
theorem decompose_S_subset_S (p : ℕ) (hp : Odd p ∧ p > 1) (x : ℕ) :
  decompose_S p hp x ⊆ S p := by
    unfold decompose_S;
    split_ifs <;> [ exact Exists.choose_spec ( _ : ∃ s ⊆ S p, s.sum id = x ) |>.1; exact Finset.empty_subset _ ]

/-
Elements of the decomposition using S are in A_p and strictly greater than 1.
-/
theorem decompose_S_properties (p : ℕ) (hp : Odd p ∧ p > 1) (x : ℕ) :
  ∀ s ∈ decompose_S p hp x, s ∈ A p ∧ s > 1 := by
    have := S_properties p hp;
    -- Since `S p` is a subset of `A p` and all elements of `S p` are greater than 1, if `s` is in `S p`, then `s` is in `A p` and `s > 1`.
    intros s hs
    have h_in_A : s ∈ A p := by
      exact this.1 s ( Finset.mem_of_subset ( decompose_S_subset_S p hp x ) hs ) |>.1
    have h_gt_1 : s > 1 := by
      have h_gt_1 : s ∈ S p := by
        exact decompose_S_subset_S p hp x hs;
      exact lt_of_le_of_ne ( Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( by cases h_in_A; aesop ) ) ) ( Ne.symm ( this.1 s h_gt_1 |>.2 ) )
    exact ⟨h_in_A, h_gt_1⟩

/-
For indices i >= m-1, the initial coefficient is at most 1.
-/
theorem c_init_le_one_of_ge_m_sub_1 (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (hi : i ≥ m p n hp - 1) :
  c_init p n hp i ≤ 1 := by
    unfold c_init;
    unfold coeff_from_binary;
    grind

/-
If the initial coefficient is greater than M_0, then the corresponding sequence element is a power of 2.
-/
theorem ak_is_pow2_of_gt_M0 (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : k < m p n hp - 1)
  (h_gt : c_init p n hp k > M_0 p) :
  ∃ j, a_seq p k = 2^j := by
    exact c_init_gt_M0_imp_pow2 p n hp k ( by simpa [ v_1_eq_m_sub_1 ] using hk.le ) h_gt

/-
For k >= 2, u_{k+1} is 2 to the power of log2(M_k).
-/
theorem lemma_u_eq_pow2_log2_M (p : ℕ) (k : ℕ) (hk : k ≥ 2) :
  u p (k + 1) = 2 ^ (Nat.log2 (M p k)) := by
    rcases k with ( _ | _ | k ) <;> aesop

/-
If s is a positive element of A_p, then the target index is injective with respect to the source index j.
-/
theorem lemma_target_index_inj_j (p : ℕ) (hp : p > 1) (s : ℕ) (hs : s > 0) (hs_in_A : s ∈ A p) (j1 j2 : ℕ) :
  target_index p j1 s = target_index p j2 s → j1 = j2 := by
    -- By definition of `target_index`, we have `a_seq p (target_index p j s) = s * a_seq p j`.
    have h_target_def : ∀ j, a_seq p (target_index p j s) = s * a_seq p j := by
      intro j; exact (by
      exact target_index_spec p hp j s hs_in_A);
    have h_target_def : ∀ j, s * a_seq p j = a_seq p (target_index p j s) := by
      exact fun j => h_target_def j ▸ rfl;
    -- Since $s \neq 0$, we can divide both sides of the equation by $s$ to get $a_seq p j1 = a_seq p j2$.
    have h_div : ∀ j1 j2, s * a_seq p j1 = s * a_seq p j2 → a_seq p j1 = a_seq p j2 := by
      exact fun j1 j2 h => mul_left_cancel₀ hs.ne' h;
    exact fun h => StrictMono.injective ( a_seq_strict_mono p hp ) ( h_div _ _ <| by rw [ h_target_def, h_target_def, h ] )

/-
The product of an element s in A_p and an element of the sequence a_seq is in A_p.
-/
theorem s_mul_a_seq_mem_A (p : ℕ) (hp : p > 1) (s : ℕ) (hs : s ∈ A p) (j : ℕ) :
  s * a_seq p j ∈ A p := by
    -- By definition of $a_seq$, we know that $a_seq p j = 2^x * p^y$ for some $x$ and $y$.
    obtain ⟨x, y, hx⟩ : ∃ x y, a_seq p j = 2 ^ x * p ^ y := by
      unfold a_seq;
      split_ifs <;> norm_num;
      · unfold A at *;
        grind;
      · exact False.elim <| ‹¬ ( A p ).Infinite› <| Set.infinite_of_injective_forall_mem ( fun x y hxy => by simpa using hxy ) fun x => ⟨ x, 0, rfl ⟩;
    rcases hs with ⟨ x', y', rfl ⟩ ; exact ⟨ x' + x, y' + y, by rw [ hx ] ; ring ⟩ ;

/-
For a fixed source index j and target index i, the scalar s is unique.
-/
theorem lemma_scalar_unique_for_target_j (p : ℕ) (hp : p > 1) (j i : ℕ) (s1 s2 : ℕ)
  (hs1 : s1 > 0) (hs1_in_A : s1 ∈ A p)
  (hs2 : s2 > 0) (hs2_in_A : s2 ∈ A p) :
  target_index p j s1 = i → target_index p j s2 = i → s1 = s2 := by
    intros h1 h2;
    unfold target_index at h1 h2;
    -- Since $a_seq p j$ is positive, we can divide both sides of the equation $s1 * a_seq p j = s2 * a_seq p j$ by $a_seq p j$ to get $s1 = s2$.
    have h_div : s1 * a_seq p j = s2 * a_seq p j → s1 = s2 := by
      exact fun h => mul_right_cancel₀ ( ne_of_gt ( a_seq_pos p hp j ) ) h;
    apply h_div;
    rw [ ← a_seq_index_in_A p hp ( s1 * a_seq p j ) ( s_mul_a_seq_mem_A p hp s1 hs1_in_A j ), ← a_seq_index_in_A p hp ( s2 * a_seq p j ) ( s_mul_a_seq_mem_A p hp s2 hs2_in_A j ), h1, h2 ]

/-
Redefinition of intervals and invariants with corrected boundaries.
-/
def in_interval_v4 (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (i : ℕ) : Prop :=
  if k = 1 then i < v p n hp 1
  else v p n hp (k - 1) ≤ i ∧ i < v p n hp k

/-
The sequence v is non-decreasing (relative to v_1).
-/
theorem lemma_v_ge_v1 (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : 1 ≤ k) (hk_le : k ≤ K p) :
  v p n hp k ≥ v p n hp 1 := by
    have v_strict_mono : ∀ k, 1 ≤ k → k < K p → v p n hp k < v p n hp (k + 1) := by
      have := @v_strict_mono;
      exact fun k hk hk' => this p n hp k ⟨ hk, hk' ⟩;
    -- We can prove this by induction on $k$.
    induction' k with k ih;
    · contradiction;
    · grind

/-
For indices in intervals k >= 3, the sequence value is strictly greater than R.
-/
theorem a_i_gt_R_of_ge_3 (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (i : ℕ) (k : ℕ) (hk : k ≥ 3) (hk_le : k ≤ K p) (hi : in_interval_v4 p n hp k i) :
  a_seq p i > R p n hp := by
    -- Since $k \ge 3$, we have $i \ge v_{k-1} \ge v_2$ (by `v_ge_v2_of_ge_3` and definition of `in_interval_v4`).
    have hi_ge_v2 : i ≥ v p n hp 2 := by
      unfold in_interval_v4 at hi;
      have h_ai_bound : v p n hp (k - 1) ≥ v p n hp 2 := by
        apply_rules [ v_ge_v2_of_ge_3, Nat.le_sub_one_of_lt ];
      grind;
    -- Since `a_seq` is strictly monotone, $a_i \ge a_{v_2}$.
    have ha_i_ge_a_v2 : a_seq p i ≥ a_seq p (v p n hp 2) := by
      exact a_seq_strict_mono p hp.2 |> StrictMono.monotone <| hi_ge_v2;
    -- By `v_spec`, $a_{v_2} = P_2 a_{m-1}$.
    have ha_v2_eq_P2_am_sub_1 : a_seq p (v p n hp 2) = P p 2 * a_seq p (m p n hp - 1) := by
      exact v_spec p n hp 2;
    refine lt_of_lt_of_le ?_ ( ha_i_ge_a_v2.trans' ha_v2_eq_P2_am_sub_1.ge );
    exact R_lt_P2_am_sub_1 p n hp hn

/-
For indices in intervals k >= 3, the initial coefficient is 0.
-/
theorem c_init_eq_zero_of_ge_3_v3 (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (i : ℕ) (k : ℕ) (hk : k ≥ 3) (hk_le : k ≤ K p) (hi : in_interval_v4 p n hp k i) :
  c_init p n hp i = 0 := by
    -- Since $i \geq v_{k-1}$ and $v_{k-1} \geq v_2$, we have $i \geq v_2$.
    have h_i_ge_v2 : i ≥ v p n hp 2 := by
      have h_i_ge_v2 : i ≥ v p n hp (k - 1) := by
        unfold in_interval_v4 at hi; aesop;
      exact le_trans ( v_ge_v2_of_ge_3 p n hp k ( by omega ) ( by omega ) ) h_i_ge_v2;
    -- Since $i \geq v_2$, we have $i \geq m - 1$.
    have h_i_ge_m_sub_1 : i ≥ m p n hp - 1 := by
      have h_v2_ge_m_sub_1 : v p n hp 2 > v p n hp 1 := by
        apply_rules [ v_strict_mono ];
        exact ⟨ le_rfl, by linarith ⟩;
      linarith [ v_1_eq_m_sub_1 p n hp ];
    rw [ c_init ];
    rw [ if_neg h_i_ge_m_sub_1.not_gt, zero_add, coeff_from_binary_eq_zero_of_gt ];
    · exact hp.2;
    · exact a_i_gt_R_of_ge_3 p n hp hn i k hk hk_le hi

/-
The value of a target generated from interval k_idx is strictly less than the value at the boundary of the next interval.
-/
theorem lemma_target_val_lt_next_boundary (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (k_idx : ℕ) (s : ℕ)
  (hk_idx : 1 ≤ k_idx ∧ k_idx < K p)
  (hk_in : in_interval_v4 p n hp k_idx k)
  (hs : s ≤ u p (k_idx + 1))
  (hs_pos : s > 0) :
  s * a_seq p k < a_seq p (v p n hp (k_idx + 1)) := by
    have h_target_range : a_seq p k < P p k_idx * a_seq p (m p n hp - 1) := by
      have h_target_range : k < v p n hp k_idx := by
        unfold in_interval_v4 at hk_in; aesop;
      have h_target_range : a_seq p k < a_seq p (v p n hp k_idx) := by
        exact a_seq_strict_mono p hp.2 h_target_range;
      convert h_target_range using 1;
      exact Eq.symm (v_spec p n hp k_idx);
    have h_target_range : s * P p k_idx * a_seq p (m p n hp - 1) ≤ P p (k_idx + 1) * a_seq p (m p n hp - 1) := by
      have h_target_range : s * P p k_idx ≤ u p (k_idx + 1) * P p k_idx := by
        exact Nat.mul_le_mul_right _ hs;
      exact Nat.mul_le_mul_right _ ( h_target_range.trans ( by rw [ ← Nat.mul_comm ] ; exact lemma_P_recursive p ( k_idx + 1 ) ( Nat.succ_pos _ ) ▸ le_rfl ) );
    rw [ v_spec ] at * ; nlinarith

/-
If k is in interval k_idx, then any target generated by a valid scalar is strictly less than v_{k_idx+1}.
-/
theorem lemma_target_lt_v_next (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (k_idx : ℕ) (s : ℕ)
  (hk_idx : 1 ≤ k_idx ∧ k_idx < K p)
  (hk_in : in_interval_v4 p n hp k_idx k)
  (hs : s ≤ u p (k_idx + 1))
  (hs_pos : s > 0)
  (hs_in_A : s ∈ A p) :
  target_index p k s < v p n hp (k_idx + 1) := by
    have h_target_lt_v : s * a_seq p k < a_seq p (v p n hp (k_idx + 1)) := by
      exact lemma_target_val_lt_next_boundary p n hp k k_idx s hk_idx hk_in hs hs_pos;
    exact Nat.lt_of_not_ge fun h => h_target_lt_v.not_ge <| by rw [ ← target_index_spec p hp.2 k s hs_in_A ] ; exact a_seq_strict_mono p hp.2 |>.monotone h;

/-
The sequence v is non-decreasing on the range [1, K].
-/
theorem lemma_v_le_v_of_le (p n : ℕ) (hp : Odd p ∧ p > 1) (k1 k2 : ℕ) (hk1 : 1 ≤ k1) (hk2 : k2 ≤ K p) (h : k1 ≤ k2) :
  v p n hp k1 ≤ v p n hp k2 := by
    -- We prove this by induction on $k2 - k1$.
    induction' h with k h_ind;
    · rfl;
    · exact le_trans ( by solve_by_elim [ Nat.le_of_succ_le ] ) ( v_strict_mono p n hp k ⟨ Nat.pos_of_ne_zero ( by aesop ), by solve_by_elim [ Nat.le_of_succ_le ] ⟩ |> le_of_lt )

/-
Any index j less than v(K) falls into one of the intervals 1 to K.
-/
theorem lemma_interval_coverage (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (hj : j < v p n hp (K p)) :
  ∃ k, 1 ≤ k ∧ k ≤ K p ∧ in_interval_v4 p n hp k j := by
    -- We can use induction or the property of the sequence v being strictly increasing.
    have h_partition : ∃ k ∈ Finset.Icc 1 (K p), j < v p n hp k := by
      exact ⟨ K p, Finset.mem_Icc.mpr ⟨ by linarith [ K_ge_2 p ], by linarith [ K_ge_2 p ] ⟩, hj ⟩;
    obtain ⟨k, hk⟩ : ∃ k ∈ Finset.Icc 1 (K p), j < v p n hp k ∧ ∀ m ∈ Finset.Icc 1 (K p), m < k → v p n hp m ≤ j := by
      exact ⟨ Nat.find h_partition, Nat.find_spec h_partition |>.1, Nat.find_spec h_partition |>.2, by aesop ⟩;
    use k;
    rcases k with ( _ | _ | k ) <;> simp_all +decide [ in_interval_v4 ];
    grind

/-
If the index is greater than or equal to v(K), the initial coefficient is 0.
-/
theorem lemma_c_init_eq_zero_of_ge_vK (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (i : ℕ) (hi : i ≥ v p n hp (K p)) :
  c_init p n hp i = 0 := by
    -- If $i \geq v(K)$, then $a_i \geq a_{v(K)} = P(K) a_{m-1}$.
    have h_ai_ge_R : a_seq p i ≥ R p n hp + 1 := by
      refine' lt_of_lt_of_le _ ( a_seq_strict_mono p hp.2 |> StrictMono.monotone |> fun h => h hi );
      rw [ v_spec ];
      refine' lt_of_lt_of_le ( R_lt_P2_am_sub_1 p n hp hn ) _;
      exact Nat.mul_le_mul_right _ ( P_mono p ( by linarith [ K_ge_2 p ] ) );
    -- Since $a_i > R$, the coefficient from the binary representation is zero.
    have h_coeff_zero : coeff_from_binary p (R p n hp) i = 0 := by
      exact coeff_from_binary_eq_zero_of_gt p hp.2 ( R p n hp ) i h_ai_ge_R;
    -- Since $i \geq v(K)$ and $v(K)$ is the last interval, it follows that $i \geq m-1$.
    have h_i_ge_m_sub_1 : i ≥ m p n hp - 1 := by
      exact le_trans ( Nat.le_of_not_lt fun h => by have := v_1_eq_m_sub_1 p n hp; have := lemma_v_ge_v1 p n hp ( K p ) ( by linarith [ K_ge_2 p ] ) ( by linarith [ K_ge_2 p ] ) ; omega ) hi;
    unfold c_init; aesop;

/-
The sequence M is non-increasing for k >= 1.
-/
theorem lemma_M_antitone (p : ℕ) (hp : Odd p ∧ p > 1) :
  ∀ k1 k2, 1 ≤ k1 → k1 ≤ k2 → M p k2 ≤ M p k1 := by
    intros k1 k2 hk1 hk2
    induction' hk2 with k hk ih;
    · rfl;
    · rcases k with ( _ | _ | k ) <;> simp_all +decide [ M ];
      · grind;
      · refine' le_trans _ ih;
        exact Nat.log2_le_self (M p (k + 2))

/-
If s is a power of 2, greater than 1, and less than or equal to |S|, then s is in S.
-/
theorem lemma_pow2_in_S_if_le_card (p : ℕ) (hp : Odd p ∧ p > 1) (s : ℕ)
  (hs_pow2 : ∃ k, s = 2^k)
  (hs_gt_1 : s > 1)
  (hs_le : s ≤ (S p).card) :
  s ∈ S p := by
    have := S_properties p hp;
    grind

/-
If s is a power of 2, greater than 1, and less than or equal to |S|, then s is in S.
-/
theorem lemma_pow2_in_S_if_le_card_v2 (p : ℕ) (hp : Odd p ∧ p > 1) (s : ℕ)
  (hs_pow2 : ∃ k, s = 2^k)
  (hs_gt_1 : s > 1)
  (hs_le : s ≤ (S p).card) :
  s ∈ S p := by
    exact lemma_pow2_in_S_if_le_card p hp s hs_pow2 hs_gt_1 hs_le

/-
If the initial coefficient is 1 for an index i >= m-1, then a_i is a power of 2.
-/
theorem lemma_c_init_eq_one_imp_pow2_ge_m_sub_1 (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (hi : i ≥ m p n hp - 1) (h : c_init p n hp i = 1) :
  ∃ k, a_seq p i = 2^k := by
    unfold c_init at h;
    -- Since $i \geq m - 1$, the binary part must be 1.
    have h_binary : coeff_from_binary p (R p n hp) i = 1 := by
      grind;
    unfold coeff_from_binary at h_binary;
    grind

/-
Redefinition of the final algorithm steps using the correct split point `m-1`.
-/
noncomputable def step_transform_final_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) (c : ℕ → ℕ) (k : ℕ) : ℕ → ℕ :=
  if k < m p n hp - 1 then
    -- Use S
    let s_decomp := decompose_S p hp (c k)
    fun i =>
      if i = k then 0
      else c i + if ∃ s ∈ s_decomp, target_index p k s = i then 1 else 0
  else
    -- Use even powers of 2
    if c k > 1 then
      let s_decomp := decompose_even_pow2 (c k)
      fun i =>
        if i = k then c k - s_decomp.sum id
        else c i + if ∃ s ∈ s_decomp, target_index p k s = i then 1 else 0
    else
      c

noncomputable def c_step_final_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) : ℕ → ℕ → ℕ
| 0 => c_init p n hp
| k + 1 => step_transform_final_v2 p n hp (c_step_final_v2 p n hp k) k

noncomputable def used_s_final_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Finset ℕ :=
  let c := c_step_final_v2 p n hp j j
  if j < m p n hp - 1 then
    decompose_S p hp c
  else
    if c > 1 then decompose_even_pow2 c else ∅

/-
The set of scalars that have contributed to the coefficient at index i up to step `limit`.
-/
noncomputable def contributing_s_final_v2_up_to (p n : ℕ) (hp : Odd p ∧ p > 1) (limit : ℕ) (i : ℕ) : Finset ℕ :=
  (Finset.range limit).biUnion (fun j => (used_s_final_v2 p n hp j).filter (fun s => target_index p j s = i))

/-
If the coefficient at step k is within the valid range for `decompose_S`, then the used scalars are a subset of S.
-/
theorem lemma_used_s_final_v2_subset_S_of_bound (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : k < m p n hp - 1)
  (h_bound : c_step_final_v2 p n hp k k ≤ M_0 p + (S p).card) :
  used_s_final_v2 p n hp k ⊆ S p := by
    unfold used_s_final_v2;
    -- By definition of `decompose_S`, the scalars used in step k are a subset of S.
    have h_decomp_subset_S : ∀ c, c ≤ M_0 p + (S p).card → decompose_S p hp c ⊆ S p := by
      exact fun c a ↦ decompose_S_subset_S p hp c;
    aesop

/-
The scalars used in the final algorithm (v2) are always elements of A_p and strictly greater than 1.
-/
theorem lemma_used_s_final_v2_properties (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) :
  ∀ s ∈ used_s_final_v2 p n hp k, s ∈ A p ∧ s > 1 := by
    -- By definition of `used_s_final_v2`, we split into cases based on the value of `k`.
    by_cases hk : k < m p n hp - 1;
    · intro s hs;
      unfold used_s_final_v2 at hs;
      have := decompose_S_properties p hp ( c_step_final_v2 p n hp k k ) ; aesop;
    · -- If $k \geq m - 1$, then $used_s_final_v2$ uses $decompose_even_pow2$ (if $c > 1$).
      by_cases hc : c_step_final_v2 p n hp k k > 1;
      · -- By definition of `decompose_even_pow2`, each element in the decomposition is a power of 2 with exponent at least 1.
        have h_pow2 : ∀ s ∈ decompose_even_pow2 (c_step_final_v2 p n hp k k), ∃ r ≥ 1, s = 2^r := by
          intro s hs;
          -- By definition of `decompose_even_pow2`, each element in the decomposition is a power of 2 with exponent at least 1.
          have h_pow2 : ∀ x ∈ decompose_even_pow2 (c_step_final_v2 p n hp k k), ∃ r ≥ 1, x = 2^r := by
            intro x hx
            have h := decompose_even_pow2_spec (c_step_final_v2 p n hp k k) (by linarith)
            exact h.2 x hx;
          exact h_pow2 s hs;
        -- By definition of `used_s_final_v2`, if $k \geq m - 1$ and $c > 1$, then `used_s_final_v2` uses `decompose_even_pow2`.
        simp [used_s_final_v2, hc];
        split_ifs ; simp_all +decide [ A ];
        exact fun s hs => by obtain ⟨ r, hr, rfl ⟩ := h_pow2 s hs; exact ⟨ ⟨ r, 0, by norm_num ⟩, one_lt_pow₀ ( by norm_num ) ( by linarith ) ⟩ ;
      · -- If $c \leq 1$, then $used_s_final_v2$ is empty.
        simp [used_s_final_v2, hc];
        split_ifs ; aesop

/-
The target index function is injective with respect to the scalar s, for s in A_p.
-/
theorem lemma_target_index_inj_s (p : ℕ) (hp : p > 1) (k : ℕ) (s1 s2 : ℕ)
  (hs1 : s1 ∈ A p) (hs2 : s2 ∈ A p) :
  target_index p k s1 = target_index p k s2 → s1 = s2 := by
    have := @lemma_scalar_unique_for_target_j;
    contrapose! this;
    use p;
    use hp;
    exact ⟨ k, target_index p k s1, s1, s2, Nat.pos_of_ne_zero ( by cases hs1; aesop ), hs1, Nat.pos_of_ne_zero ( by cases hs2; aesop ), hs2, rfl, this.1.symm, this.2 ⟩

/-
The sum of the scalars used in step k (v2) is less than or equal to the coefficient at index k.
-/
theorem lemma_used_s_final_v2_sum_le (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) :
  (used_s_final_v2 p n hp k).sum id ≤ c_step_final_v2 p n hp k k := by
    -- Consider the two cases: k < m p n hp - 1 and k ≥ m p n hp - 1.
    by_cases hk : k < m p n hp - 1;
    · -- By definition of `used_s_final_v2`, if `k < m p n hp - 1`, then `used_s_final_v2 p n hp k = decompose_S p hp (c_step_final_v2 p n hp k k)`.
      have h_decomp : used_s_final_v2 p n hp k = decompose_S p hp (c_step_final_v2 p n hp k k) := by
        exact if_pos hk;
      rw [ h_decomp, decompose_S ];
      split_ifs <;> simp_all +decide [ decompose_S ];
      exact Exists.choose_spec ( show ∃ s : Finset ℕ, s ⊆ S p ∧ ∑ x ∈ s, x = c_step_final_v2 p n hp k k from by
                                  grind ) |>.2.le;
    · by_cases hk' : c_step_final_v2 p n hp k k > 1 <;> simp_all +decide [ used_s_final_v2 ];
      · rw [ if_neg ( by omega ) ];
        rw [ decompose_even_pow2 ];
        have h_sum_le : ∀ n : ℕ, n > 1 → (List.map (fun x => 2 ^ x) (n).bitIndices).toFinset.sum id ≤ n := by
          intro n hn;
          induction' n using Nat.strong_induction_on with n ih;
          rcases Nat.even_or_odd' n with ⟨ c, rfl | rfl ⟩ <;> simp_all +decide [ Nat.pow_succ', Nat.mul_mod ];
          · rcases c with ( _ | _ | c ) <;> simp_all +arith +decide;
            rw [ show ( List.map ( ( fun x => 2 ^ x ) ∘ fun x => x + 1 ) ( c + 2 ).bitIndices ).toFinset = Finset.image ( fun x => 2 ^ ( x + 1 ) ) ( List.toFinset ( List.map ( fun x => x ) ( c + 2 ).bitIndices ) ) from ?_ ];
            · rw [ Finset.sum_image ] <;> norm_num [ pow_succ' ];
              rw [ ← Finset.mul_sum _ _ _ ] ; aesop;
            · ext; simp [Function.comp];
          · have h_ind : ∑ x ∈ (List.map ((fun x => 2 ^ x) ∘ fun x => x + 1) c.bitIndices).toFinset, x = 2 * ∑ x ∈ (List.map (fun x => 2 ^ x) c.bitIndices).toFinset, x := by
              rw [ Finset.mul_sum _ _ _ ];
              refine' Finset.sum_bij ( fun x hx => x / 2 ) _ _ _ _ <;> simp_all +decide [ Function.comp, pow_succ' ];
            by_cases hc : 1 < c;
            · grind;
            · interval_cases c ; simp_all +decide;
        split_ifs <;> simp_all +decide [ Nat.even_iff ];
        exact le_trans ( h_sum_le _ ( by omega ) ) ( Nat.sub_le _ _ );
      · grind

def in_interval_final (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (i : ℕ) : Prop :=
  if k = 1 then i < v p n hp 1
  else v p n hp (k - 1) ≤ i ∧ i < v p n hp k

def CoeffBound_final (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ K p →
    ∀ i, in_interval_final p n hp k i →
      c_step_final_v2 p n hp j i ≤ M p k

def IsTarget_final (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ) : Prop :=
  ∃ s ∈ used_s_final_v2 p n hp j, target_index p j s = i

def UpdateConditionUpTo_final (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Prop :=
  ∀ i' < j, ∀ i, IsTarget_final p n hp i' i →
    ∀ k, 1 ≤ k → k ≤ K p →
      in_interval_final p n hp k i →
      (k ≥ 3 → i' ≥ v p n hp (k - 2))

def Lemma3_invariant_final (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Prop :=
  CoeffBound_final p n hp j ∧ UpdateConditionUpTo_final p n hp j

/-
If j is in interval k, and s <= u_{k+1}, then the target index of s from j is strictly less than v_{k+1}.
-/
theorem lemma_target_lt_v_next_final (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (k : ℕ) (s : ℕ)
  (hk : 1 ≤ k ∧ k < K p)
  (hj : in_interval_final p n hp k j)
  (hs : s ≤ u p (k + 1))
  (hs_pos : s > 0)
  (hs_in_A : s ∈ A p) :
  target_index p j s < v p n hp (k + 1) := by
    apply_rules [ lemma_target_lt_v_next ]

/-
Scalars used in the first interval of the final algorithm are bounded by u_2.
-/
theorem lemma_scalar_bound_final_k1 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (hj : in_interval_final p n hp 1 j) :
  ∀ s ∈ used_s_final_v2 p n hp j, s ≤ u p 2 := by
    -- Since j is in interval 1, j < m-1.
    have h_j_lt_m_minus_1 : j < m p n hp - 1 := by
      unfold in_interval_final at hj;
      unfold v at hj;
      unfold P at hj;
      unfold index_in_A at hj;
      unfold u at hj; norm_num [ List.range_succ ] at hj;
      split_ifs at hj <;> simp_all +decide [ a_seq ];
      · exact lt_of_not_ge fun h => hj _ h rfl;
      · grind;
    -- Since j is in interval 1, used_s_final_v2 uses decompose_S.
    have h_used_s_decomp_S : used_s_final_v2 p n hp j = decompose_S p hp (c_step_final_v2 p n hp j j) := by
      exact if_pos h_j_lt_m_minus_1;
    -- By definition of `decompose_S`, the scalars used are in `S`.
    have h_used_S_subset_S : used_s_final_v2 p n hp j ⊆ S p := by
      -- By definition of `decompose_S`, the scalars used are in `S`. Therefore, `used_s_final_v2 p n hp j` is a subset of `S p`.
      rw [h_used_s_decomp_S];
      -- By definition of decompose_S, it returns a subset of S.
      apply decompose_S_subset_S;
    exact fun s a ↦ s_in_S_le_u2 p hp s (h_used_S_subset_S a)

/-
For steps j >= m-1, the scalars used are powers of 2 and bounded by the coefficient.
-/
theorem lemma_used_s_final_v2_ge_m_properties (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (hj : j ≥ m p n hp - 1) :
  ∀ s ∈ used_s_final_v2 p n hp j, s ≤ c_step_final_v2 p n hp j j ∧ ∃ r, s = 2^r := by
    -- By definition of `used_s_final_v2`, if `j ≥ m - 1`, then `used_s_final_v2 p n hp j` is either empty or a subset of the even powers of 2 up to the coefficient.
    by_cases h_even : j ≥ m p n hp - 1;
    · unfold used_s_final_v2;
      split_ifs <;> simp_all +decide [ decompose_even_pow2_spec ];
      · omega;
      · split_ifs <;> simp_all +decide [ decompose_even_pow2_le ];
        unfold decompose_even_pow2; aesop;
    · grind

/-
If an index j is in interval k >= 2, then j >= m-1.
-/
theorem lemma_j_ge_m_sub_1_of_in_interval_final_ge_2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (k : ℕ) (hk : k ≥ 2) (hk_le : k ≤ K p) (hj : in_interval_final p n hp k j) :
  j ≥ m p n hp - 1 := by
    unfold in_interval_final at hj;
    -- Since $k \geq 2$, we have $k - 1 \geq 1$. By the properties of the interval bounds, $v(k-1) \geq v(1)$.
    have h_v_ge_v1 : v p n hp (k - 1) ≥ v p n hp 1 := by
      apply_rules [ lemma_v_le_v_of_le ];
      · norm_num;
      · omega;
      · exact Nat.le_sub_one_of_lt hk;
    split_ifs at hj <;> linarith [ v_1_eq_m_sub_1 p n hp ]

/-
For intervals k >= 2, the scalars used in the final algorithm are bounded by u_{k+1}.
-/
theorem lemma_scalar_bound_final_ge2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (k : ℕ) (hk : 2 ≤ k ∧ k < K p) (hj : in_interval_final p n hp k j)
  (hc_upper : CoeffBound_final p n hp j) :
  ∀ s ∈ used_s_final_v2 p n hp j, s ≤ u p (k + 1) := by
    -- Apply the lemma used_s_final_v2_ge_m_properties to get that s is a power of 2 and s ≤ c_step_final_v2 p n hp j j.
    have h_s_pow2 : ∀ s ∈ used_s_final_v2 p n hp j, ∃ r, s = 2^r ∧ s ≤ c_step_final_v2 p n hp j j := by
      have h_j_ge_m_sub_1 : j ≥ m p n hp - 1 := by
        apply lemma_j_ge_m_sub_1_of_in_interval_final_ge_2;
        exacts [ hk.1, hk.2.le, hj ];
      have := lemma_used_s_final_v2_ge_m_properties p n hp j h_j_ge_m_sub_1; aesop;
    -- Apply the lemma hc_upper to get that c_step_final_v2 p n hp j j ≤ M p k.
    have h_c_step_le_M : c_step_final_v2 p n hp j j ≤ M p k := by
      apply hc_upper k (by linarith) (by linarith) j hj;
    intro s hs
    obtain ⟨r, hr⟩ := h_s_pow2 s hs
    have h_s_le_M : s ≤ M p k := by
      linarith
    have h_s_le_u : s ≤ u p (k + 1) := by
      rw [ lemma_u_eq_pow2_log2_M ];
      · rw [ hr.1 ];
        refine' pow_le_pow_right₀ ( by decide ) _;
        rw [ Nat.le_log2 ] <;> linarith [ Nat.one_le_pow r 2 zero_lt_two ];
      · grind
    exact h_s_le_u

/-
For any interval k < K, the scalars used in the final algorithm are bounded by u_{k+1}.
-/
theorem lemma_scalar_bound_final (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (k : ℕ) (hk : 1 ≤ k ∧ k < K p) (hj : in_interval_final p n hp k j)
  (hc_upper : CoeffBound_final p n hp j) :
  ∀ s ∈ used_s_final_v2 p n hp j, s ≤ u p (k + 1) := by
    -- Split into cases based on the value of k.
    by_cases hk1 : k = 1;
    · simp_all +decide [ in_interval_final ];
      exact fun s a ↦ lemma_scalar_bound_final_k1 p n hp j hj s a;
    · exact lemma_scalar_bound_final_ge2 p n hp j k ⟨ Nat.lt_of_le_of_ne hk.1 ( Ne.symm hk1 ), hk.2 ⟩ hj hc_upper

/-
If a step j in interval k_j targets an index i in interval k (where k >= 3), then k_j must be at least k - 1.
-/
theorem lemma_interval_relation_final (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ)
  (h_coeff : CoeffBound_final p n hp j)
  (k : ℕ) (hk : 3 ≤ k ∧ k ≤ K p) (hi : in_interval_final p n hp k i)
  (k_j : ℕ) (hk_j : 1 ≤ k_j ∧ k_j < K p) (hj : in_interval_final p n hp k_j j)
  (s : ℕ) (hs : s ∈ used_s_final_v2 p n hp j) (ht : target_index p j s = i) :
  k_j ≥ k - 1 := by
    have h_scalar_bound : s ≤ u p (k_j + 1) := by
      apply lemma_scalar_bound_final p n hp j k_j hk_j hj h_coeff s hs
    have h_target_lt_v_next : i < v p n hp (k_j + 1) := by
      have h_target_lt_v_next : target_index p j s < v p n hp (k_j + 1) := by
        have h_target_lt_v_next : ∀ {s : ℕ}, s ∈ A p → s > 0 → s ≤ u p (k_j + 1) → target_index p j s < v p n hp (k_j + 1) := by
          intros s hs hs_pos hs_le
          apply lemma_target_lt_v_next_final p n hp j k_j s hk_j hj hs_le hs_pos hs;
        exact h_target_lt_v_next ( lemma_used_s_final_v2_properties p n hp j s hs |>.1 ) ( Nat.pos_of_ne_zero ( by intro t; have := lemma_used_s_final_v2_properties p n hp j s hs; aesop ) ) h_scalar_bound;
      aesop;
    -- Since `k >= 3`, `in_interval_final` implies `v p n hp (k - 1) <= i`.
    have h_v_k_minus_1_le_i : v p n hp (k - 1) ≤ i := by
      unfold in_interval_final at hi; aesop;
    contrapose! h_target_lt_v_next;
    exact le_trans ( lemma_v_le_v_of_le p n hp _ _ ( by linarith ) ( by omega ) ( by omega ) ) h_v_k_minus_1_le_i

/-
The sequence v is non-decreasing on the range [1, K].
-/
theorem lemma_v_mono_final (p n : ℕ) (hp : Odd p ∧ p > 1) (k1 k2 : ℕ) (hk1 : 1 ≤ k1) (hk2 : k2 ≤ K p) (h : k1 ≤ k2) :
  v p n hp k1 ≤ v p n hp k2 := by
    exact lemma_v_le_v_of_le p n hp k1 k2 hk1 hk2 h

/-
If the coefficient bound holds for all previous steps, then the update condition holds for the current step.
-/
theorem lemma_update_condition_final_step (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (h_prev : ∀ j' < j, CoeffBound_final p n hp j') :
  UpdateConditionUpTo_final p n hp j := by
    -- By definition of `IsTarget_final`, we need to show that if `i' < j` and `i'` targets `i` in interval `k >= 3`, then `i' >= v(k-2)`.
    intros i' hi' i hi k hk hki hi_k
    by_contra h_contra;
    -- By definition of `IsTarget_final`, we know that there exists some `s` in `used_s_final_v2 p n hp i'` such that `target_index p i' s = i`.
    obtain ⟨s, hs⟩ := hi;
    -- By Lemma_interval_relation_final, since $i' < j$ and $i'$ targets $i$, we have $k' \geq k - 1$.
    obtain ⟨k', hk', hk'_interval⟩ : ∃ k', 1 ≤ k' ∧ k' < K p ∧ in_interval_final p n hp k' i' ∧ k' ≥ k - 1 := by
      have := @lemma_interval_relation_final p n hp i' i ( h_prev i' hi' ) k ⟨ by linarith [ show 3 ≤ k from by omega ], hki ⟩ hi_k;
      by_cases hi'_lt_vK : i' < v p n hp (K p);
      · obtain ⟨k', hk'⟩ : ∃ k', 1 ≤ k' ∧ k' ≤ K p ∧ in_interval_final p n hp k' i' := by
          have := lemma_interval_coverage p n hp i' hi'_lt_vK; aesop;
        by_cases hk'_eq_K : k' = K p;
        · use K p - 1;
          rcases k with ( _ | _ | k ) <;> simp_all +arith +decide;
          rcases k with ( _ | k ) <;> simp_all +arith +decide [ in_interval_final ];
          split_ifs at hk' <;> simp_all +arith +decide [ Nat.sub_sub ];
          exact absurd hk'.2 ( not_le_of_gt ( lt_of_lt_of_le h_contra ( lemma_v_mono_final p n hp ( k + 1 ) ( K p - 1 ) ( by linarith ) ( Nat.sub_le_of_le_add <| by linarith ) <| by omega ) ) );
        · exact ⟨ k', hk'.1, lt_of_le_of_ne hk'.2.1 hk'_eq_K, hk'.2.2, this k' ⟨ hk'.1, lt_of_le_of_ne hk'.2.1 hk'_eq_K ⟩ hk'.2.2 s hs.1 hs.2 ⟩;
      · have := h_prev i' hi';
        have := this ( K p ) ( by linarith ) ( by linarith ) i' ; simp_all +decide [ in_interval_final ] ;
        exact absurd hi'_lt_vK ( not_le_of_gt ( lt_of_lt_of_le h_contra.2 ( lemma_v_mono_final p n hp _ _ ( by omega ) ( by omega ) ( by omega ) ) ) );
    rcases k with ( _ | _ | k ) <;> simp_all +decide;
    rcases k' with ( _ | _ | k' ) <;> simp_all +decide [ in_interval_final ];
    linarith [ show v p n hp ( k' + 1 ) ≥ v p n hp k from lemma_v_mono_final p n hp k ( k' + 1 ) ( by linarith ) ( by linarith ) ( by linarith ) ]

/-
If i is in the first interval, then any scalar contributing to i from previous steps must be in S.
-/
theorem lemma_contributing_subset_S_final (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (i : ℕ)
  (hi : in_interval_final p n hp 1 i)
  (h_ge : i ≥ j)
  (h_prev : ∀ j' < j, CoeffBound_final p n hp j') :
  contributing_s_final_v2_up_to p n hp j i ⊆ S p := by
    -- Since `j'` is in interval 1, `j' < m-1`.
    have hj'_lt_m_sub_1 : ∀ j' < j, in_interval_final p n hp 1 j' → j' < m p n hp - 1 := by
      intro j' hj' hj'_interval
      have hj'_lt_m_sub_1 : j' < v p n hp 1 := by
        unfold in_interval_final at hj'_interval; aesop;
      refine lt_tsub_iff_right.mpr ?_;
      unfold v at hj'_lt_m_sub_1;
      unfold index_in_A at hj'_lt_m_sub_1;
      split_ifs at hj'_lt_m_sub_1 <;> simp_all +decide [ Nat.find_eq_iff ];
      contrapose! hj'_lt_m_sub_1;
      refine' ⟨ m p n hp - 1, _, _ ⟩ <;> norm_num [ Nat.sub_add_cancel ( show 1 ≤ m p n hp from _ ) ];
      · linarith;
      · -- By definition of $P$, we know that $P p 1 = 1$.
        simp [P];
        norm_num [ List.range_succ, u ];
    -- Since `j'` is in interval 1, `used_s_final_v2` uses `decompose_S`.
    have h_decomp_S : ∀ j' < j, in_interval_final p n hp 1 j' → used_s_final_v2 p n hp j' ⊆ S p := by
      intros j' hj' hj'_interval
      have hj'_lt_m_sub_1 : j' < m p n hp - 1 := hj'_lt_m_sub_1 j' hj' hj'_interval
      simp [used_s_final_v2, hj'_lt_m_sub_1];
      exact decompose_S_subset_S p hp (c_step_final_v2 p n hp j' j');
    -- Since `i` is in interval 1, any `j'` that targets `i` must be in interval 1.
    have h_j'_in_interval_1 : ∀ j' < j, IsTarget_final p n hp j' i → in_interval_final p n hp 1 j' := by
      intros j' hj'_lt_j hj'_target
      obtain ⟨s, hs_used, hs_target⟩ := hj'_target
      have hj'_lt_i : j' < i := by
        grind;
      exact lt_of_lt_of_le hj'_lt_i hi.le;
    intro s hs;
    obtain ⟨ j', hj', hs' ⟩ := Finset.mem_biUnion.mp hs;
    simp +zetaDelta at *;
    exact h_decomp_S j' hj' ( h_j'_in_interval_1 j' hj' ⟨ s, hs'.1, hs'.2 ⟩ ) hs'.1

/-
The number of scalars in step j targeting i is 0 or 1.
-/
theorem lemma_card_filter_target_eq_final (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ) :
  ((used_s_final_v2 p n hp j).filter (fun s => target_index p j s = i)).card =
  if ∃ s ∈ used_s_final_v2 p n hp j, target_index p j s = i then 1 else 0 := by
    -- If there exists an element s in the set, then the set has exactly one element.
    by_cases h_exists : ∃ s ∈ used_s_final_v2 p n hp j, target_index p j s = i;
    · -- If there exists an element s in the set, then the set has exactly one element because target_index is injective.
      obtain ⟨s, hs⟩ := h_exists
      have h_card : ∀ s' ∈ used_s_final_v2 p n hp j, target_index p j s' = i → s' = s := by
        intros s' hs' hs'_target
        have h_eq : target_index p j s' = target_index p j s := by
          rw [hs'_target, hs.2];
        apply lemma_target_index_inj_s p (by linarith) j s' s (by
        exact lemma_used_s_final_v2_properties p n hp j s' hs' |>.1) (by
        exact lemma_used_s_final_v2_properties p n hp j s hs.1 |>.1) h_eq;
      rw [ if_pos ⟨ s, hs.1, hs.2 ⟩, Finset.card_eq_one ] ; use s ; ext ; aesop;
    · rw [ if_neg h_exists, Finset.card_eq_zero.mpr ] ; aesop

/-
For a fixed target i and scalar s, there is at most one step j where s is used to target i.
-/
theorem lemma_unique_source_for_s_final (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (s : ℕ) :
  Set.Subsingleton { j | s ∈ used_s_final_v2 p n hp j ∧ target_index p j s = i } := by
    intro j hj j' hj';
    -- Since $s$ is in $A_p$ and $s > 1$, we can apply the injectivity of the target index function.
    have h_inj : s ∈ A p ∧ s > 1 := by
      exact lemma_used_s_final_v2_properties p n hp j s hj.1;
    have h_inj : target_index p j s = target_index p j' s → j = j' := by
      apply lemma_target_index_inj_j;
      · exact hp.2;
      · linarith;
      · exact h_inj.1;
    aesop

/-
The sets of scalars contributing to index i from different steps j1 and j2 are disjoint.
-/
theorem lemma_contributing_scalars_disjoint_final (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (j1 j2 : ℕ) (h_neq : j1 ≠ j2) :
  Disjoint ((used_s_final_v2 p n hp j1).filter (fun s => target_index p j1 s = i))
           ((used_s_final_v2 p n hp j2).filter (fun s => target_index p j2 s = i)) := by
             -- Assume there exists a scalar s in both sets.
             by_contra h_inter
             obtain ⟨s, hs1, hs2⟩ : ∃ s, s ∈ used_s_final_v2 p n hp j1 ∧ target_index p j1 s = i ∧ s ∈ used_s_final_v2 p n hp j2 ∧ target_index p j2 s = i := by
               rw [ Finset.not_disjoint_iff ] at h_inter; aesop;
             apply h_neq;
             have := @lemma_unique_source_for_s_final p n hp i s;
             exact this ⟨ hs1, hs2.1 ⟩ ⟨ hs2.2.1, hs2.2.2 ⟩

/-
The number of contributing scalars up to step j+1 is the number up to step j plus the number from step j.
-/
theorem lemma_contributing_card_recurrence_final (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ) :
  (contributing_s_final_v2_up_to p n hp (j + 1) i).card =
  (contributing_s_final_v2_up_to p n hp j i).card +
  ((used_s_final_v2 p n hp j).filter (fun s => target_index p j s = i)).card := by
    unfold contributing_s_final_v2_up_to;
    rw [ Finset.range_add_one, Finset.biUnion_insert, Finset.card_union_of_disjoint ];
    · ring;
    · simp +contextual [ Finset.disjoint_left ];
      intro a ha₁ ha₂ x hx₁ hx₂ hx₃; have := lemma_unique_source_for_s_final p n hp i a; simp_all +decide [ Set.Subsingleton ] ;
      linarith [ this ha₁ ha₂ hx₂ hx₃ ]

/-
The coefficient at step j is the initial coefficient plus the number of contributing scalars up to step j.
-/
theorem lemma_c_step_final_eq_init_plus_card (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ) (h_ge : i ≥ j) :
  c_step_final_v2 p n hp j i = c_init p n hp i + (contributing_s_final_v2_up_to p n hp j i).card := by
    revert i j h_ge;
    -- Let's prove the main theorem by induction on j.
    intro j
    induction' j with j ih;
    · unfold contributing_s_final_v2_up_to; aesop;
    · intro i hi;
      -- By definition of `c_step_final_v2`, we have:
      have h_step : c_step_final_v2 p n hp (j + 1) i = c_step_final_v2 p n hp j i + (if ∃ s ∈ used_s_final_v2 p n hp j, target_index p j s = i then 1 else 0) := by
        rw [ show c_step_final_v2 p n hp ( j + 1 ) = step_transform_final_v2 p n hp ( c_step_final_v2 p n hp j ) j from rfl ];
        unfold step_transform_final_v2;
        unfold used_s_final_v2; aesop;
      rw [ h_step, ih i ( by linarith ), lemma_contributing_card_recurrence_final ];
      rw [ add_assoc, lemma_card_filter_target_eq_final ]

/-
The coefficient at index i (where i != j) after step j is updated by adding 1 if i is a target of step j, and 0 otherwise.
-/
theorem lemma_c_step_final_succ_eq (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ) (h_neq : i ≠ j) :
  c_step_final_v2 p n hp (j + 1) i = c_step_final_v2 p n hp j i + if ∃ s ∈ used_s_final_v2 p n hp j, target_index p j s = i then 1 else 0 := by
    -- By definition of `step_transform_final_v2`, we know that if `j < m - 1`, then the transformation uses `S`, otherwise it uses even powers of 2.
    have h_transform : step_transform_final_v2 p n hp (c_step_final_v2 p n hp j) j i = if j < m p n hp - 1 then
      if i = j then 0
      else c_step_final_v2 p n hp j i + if ∃ s ∈ decompose_S p hp (c_step_final_v2 p n hp j j), target_index p j s = i then 1 else 0
    else
      if c_step_final_v2 p n hp j j > 1 then
        if i = j then c_step_final_v2 p n hp j j - (decompose_even_pow2 (c_step_final_v2 p n hp j j)).sum id
        else c_step_final_v2 p n hp j i + if ∃ s ∈ (decompose_even_pow2 (c_step_final_v2 p n hp j j)), target_index p j s = i then 1 else 0
      else
        c_step_final_v2 p n hp j i := by
          unfold step_transform_final_v2; aesop;
    unfold used_s_final_v2 at *; aesop;

/-
If the target of a scalar s is a power of 2, then s itself must be a power of 2.
-/
theorem lemma_s_is_pow2_of_target_pow2 (p : ℕ) (hp : p > 1) (j : ℕ) (s : ℕ) (hs : s ∈ A p) (i : ℕ) (ht : target_index p j s = i) (h_pow2 : ∃ k, a_seq p i = 2^k) : ∃ k, s = 2^k := by
  have h_s_pow2 : s * a_seq p j = 2 ^ h_pow2.choose := by
    rw [ ← h_pow2.choose_spec, ← ht, target_index_spec ];
    · exact hp;
    · assumption;
  have : s ∣ 2 ^ h_pow2.choose := h_s_pow2 ▸ dvd_mul_right _ _; rw [ Nat.dvd_prime_pow ( by decide ) ] at this; tauto;

/-
The number of contributing scalars for an index in the first interval is at most |S|.
-/
theorem lemma_card_contributing_le_S_card_final (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ)
  (hi : in_interval_final p n hp 1 i)
  (h_ge : i ≥ j)
  (h_prev : ∀ j' < j, CoeffBound_final p n hp j') :
  (contributing_s_final_v2_up_to p n hp j i).card ≤ (S p).card := by
    apply_rules [ Finset.card_le_card ];
    exact lemma_contributing_subset_S_final p n hp j i hi h_ge h_prev

/-
If the target index corresponds to a power of 2, the number of contributing scalars is at most |S| - 1.
-/
theorem lemma_card_contributing_le_S_sub_one_final_if_pow2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ)
  (hi : in_interval_final p n hp 1 i)
  (h_ge : i ≥ j)
  (h_prev : ∀ j' < j, CoeffBound_final p n hp j')
  (h_pow2 : ∃ r, a_seq p i = 2^r) :
  (contributing_s_final_v2_up_to p n hp j i).card ≤ (S p).card - 1 := by
    cases' exists_non_pow2_in_S p hp with x hx;
    -- Since `s` is a power of 2 and `x` is not, `s` cannot be equal to `x`.
    have h_s_ne_x : ∀ s ∈ contributing_s_final_v2_up_to p n hp j i, s ≠ x := by
      intro s hs
      obtain ⟨j', hj', hs', ht⟩ : ∃ j' < j, ∃ s' ∈ used_s_final_v2 p n hp j', target_index p j' s' = i ∧ s = s' := by
        unfold contributing_s_final_v2_up_to at hs; aesop;
      have := lemma_s_is_pow2_of_target_pow2 p ( by linarith ) j' hs' ( by
        have := lemma_used_s_final_v2_properties p n hp j' hs'; aesop; ) i ht.2.1 h_pow2; aesop;
    have h_subset : contributing_s_final_v2_up_to p n hp j i ⊆ (S p).erase x := by
      intro s hs; exact Finset.mem_erase_of_ne_of_mem ( h_s_ne_x s hs ) ( lemma_contributing_subset_S_final p n hp j i hi h_ge h_prev hs ) ;
    exact le_trans ( Finset.card_le_card h_subset ) ( by rw [ Finset.card_erase_of_mem hx.1 ] )

/-
The set S contains at least one odd integer.
-/
theorem lemma_S_contains_odd (p : ℕ) (hp : Odd p ∧ p > 1) : ∃ x ∈ S p, Odd x := by
  -- By contradiction, assume that all elements in S p are even.
  by_contra h_even;
  -- If all elements in `S p` are even, then any sum of distinct elements of `S p` is even.
  have h_even_sum : ∀ Y ⊆ S p, Y.sum id % 2 = 0 := by
    norm_num +zetaDelta at *;
    exact fun Y hy => Nat.mod_eq_zero_of_dvd <| Finset.dvd_sum fun x hx => even_iff_two_dvd.mp <| h_even x <| hy hx;
  -- Since `M_0 p` and `M_0 p + 1` are consecutive integers, one of them is odd.
  obtain ⟨k, hk⟩ : ∃ k, k ∈ Finset.Icc (M_0 p) (M_0 p + (S p).card) ∧ Odd k := by
    by_cases h_even_M0 : Even (M_0 p);
    · use M_0 p + 1;
      simp_all +decide [ parity_simps ];
      exact S_nonempty p hp;
    · exact ⟨ M_0 p, Finset.mem_Icc.mpr ⟨ le_rfl, Nat.le_add_right _ _ ⟩, by simpa using h_even_M0 ⟩;
  -- Since `k` is in the range `[M_0 p, M_0 p + |S p|]`, there exists a subset `Y` of `S p` such that `Y.sum id = k`.
  obtain ⟨Y, hY⟩ : ∃ Y ⊆ S p, Y.sum id = k := by
    have := M_0_properties p hp;
    exact this.2.2 k ( Finset.mem_Icc.mp hk.1 |>.1 ) ( Finset.mem_Icc.mp hk.1 |>.2 );
  exact absurd ( h_even_sum Y hY.1 ) ( by rw [ hY.2, Nat.odd_iff.mp hk.2 ] ; norm_num )

/-
For indices in the first interval, the coefficient is bounded by M_1.
-/
theorem lemma_bound_final_k1 (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (j : ℕ)
  (i : ℕ) (hi : in_interval_final p n hp 1 i)
  (h_ge : i ≥ j)
  (h_prev : ∀ j' < j, CoeffBound_final p n hp j') :
  c_step_final_v2 p n hp j i ≤ M p 1 := by
    -- By definition of `in_interval_final`, we know that `i < v p n hp 1` and thus `i < m p n hp - 1`.
    have h_lt_m : i < m p n hp - 1 := by
      unfold in_interval_final at hi;
      unfold v at hi;
      unfold P at hi;
      unfold u at hi; norm_num [ List.range_succ ] at hi;
      refine lt_of_lt_of_le hi ?_;
      unfold index_in_A; aesop;
    by_cases h : c_init p n hp i > M_0 p <;> simp_all +decide [ Nat.lt_succ_iff ];
    · have h_ak_pow2 : ∃ r, a_seq p i = 2^r := by
        apply_rules [ ak_is_pow2_of_gt_M0 ];
      have h_card_le_S_sub_one : (contributing_s_final_v2_up_to p n hp j i).card ≤ (S p).card - 1 := by
        apply_rules [ lemma_card_contributing_le_S_sub_one_final_if_pow2 ];
      have h_c_step_le_M1 : c_step_final_v2 p n hp j i ≤ c_init p n hp i + (S p).card - 1 := by
        rw [ lemma_c_step_final_eq_init_plus_card ];
        · rw [ Nat.add_sub_assoc ] <;> norm_num at * ; omega;
          exact S_nonempty p hp;
        · linarith;
      have h_c_init_le_M0_plus_1 : c_init p n hp i ≤ M_0 p + 1 := by
        apply c_init_bounds_lt_m p n hp i h_lt_m |>.2;
      exact h_c_step_le_M1.trans ( Nat.sub_le_of_le_add <| by linarith! [ show M p 1 = M_0 p + ( S p |> Finset.card ) from rfl ] );
    · -- By Lemma 3.1, the number of contributing scalars is at most |S|.
      have h_card_contributing : (contributing_s_final_v2_up_to p n hp j i).card ≤ (S p).card := by
        exact lemma_card_contributing_le_S_card_final p n hp j i hi h_ge h_prev;
      rw [ show M p 1 = M_0 p + ( S p |> Finset.card ) by rfl ] ; linarith [ lemma_c_step_final_eq_init_plus_card p n hp j i h_ge ] ;

/-
Definition of the final coefficient at index i and the list of final summands.
-/
noncomputable def c_final_val_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) : ℕ :=
  c_step_final_v2 p n hp (final_step_index p n hp) i

noncomputable def final_summands_list_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) : List ℕ :=
  ((List.range (final_step_index p n hp)).filter (fun i => c_final_val_v2 p n hp i = 1)).map (a_seq p)

/-
For any scalar s used in step j of the final algorithm, the target index is strictly greater than j.
-/
theorem lemma_target_gt_source_final (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) :
  ∀ s ∈ used_s_final_v2 p n hp j, target_index p j s > j := by
    intros s hs;
    apply target_index_gt_self;
    · exact hp.2;
    · exact lemma_used_s_final_v2_properties p n hp j s hs |>.2;
    · exact lemma_used_s_final_v2_properties p n hp j s hs |>.1

/-
If j' targets i in interval k >= 3, then the scalar s is a power of 2 and bounded by M_{k-1}.
-/
theorem lemma_target_scalar_properties (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (h_update : UpdateConditionUpTo_final p n hp j)
  (h_prev_coeff : ∀ j' < j, CoeffBound_final p n hp j')
  (k : ℕ) (hk : 3 ≤ k ∧ k ≤ K p)
  (i : ℕ) (hi : in_interval_final p n hp k i)
  (j' : ℕ) (hj' : j' < j)
  (s : ℕ) (hs : s ∈ used_s_final_v2 p n hp j') (ht : target_index p j' s = i) :
  (∃ r, s = 2^r) ∧ s ≤ M p (k - 1) := by
    -- By `lemma_used_s_final_v2_ge_m_properties`, $s$ is a power of 2 and $s \le c_{j'}$.
    have h_s_pow2 : ∃ r, s = 2 ^ r := by
      -- Since $s \in \text{used\_s\_final\_v2 } p n hp j'$, we have $j' \ge m-1$.
      have h_j'_ge_m_sub_1 : j' ≥ m p n hp - 1 := by
        have h_j'_ge_m_sub_1 : j' ≥ v p n hp (k - 2) := by
          apply h_update j' hj' i ⟨ s, hs, ht ⟩ k ( by linarith ) ( by linarith ) hi ( by linarith )
        generalize_proofs at *;
        refine le_trans ?_ h_j'_ge_m_sub_1;
        have h_v_mono : ∀ k, 1 ≤ k → k ≤ K p → v p n hp k ≥ m p n hp - 1 := by
          intros k hk1 hk2
          have h_v_mono : v p n hp k ≥ v p n hp 1 := by
            exact lemma_v_ge_v1 p n hp k hk1 hk2
          generalize_proofs at *;
          convert h_v_mono using 1;
          exact Eq.symm (v_1_eq_m_sub_1 p n hp);
        exact h_v_mono _ ( Nat.sub_pos_of_lt ( by linarith ) ) ( Nat.sub_le_of_le_add ( by linarith ) );
      have := lemma_used_s_final_v2_ge_m_properties p n hp j' h_j'_ge_m_sub_1 s hs; aesop;
    have h_s_le_c_j' : s ≤ c_step_final_v2 p n hp j' j' := by
      exact lemma_used_s_final_v2_sum_le p n hp j' |> fun h => Finset.single_le_sum ( fun x _ => Nat.zero_le x ) hs |> le_trans ( by simp +decide [ hs ] ) |> le_trans <| h;
    -- Since $j'$ is in some interval $k'$, we have $k' \ge k-1$.
    obtain ⟨k', hk'⟩ : ∃ k', 1 ≤ k' ∧ k' ≤ K p ∧ in_interval_final p n hp k' j' := by
      have h_interval : j' < v p n hp (K p) := by
        have h_j'_lt_vK : j' < i := by
          exact ht ▸ lemma_target_gt_source_final p n hp j' s hs;
        have h_i_le_vK : i < v p n hp k := by
          unfold in_interval_final at hi; aesop;
        exact lt_of_lt_of_le h_j'_lt_vK ( le_trans h_i_le_vK.le ( lemma_v_mono_final p n hp k ( K p ) ( by linarith ) ( by linarith ) ( by linarith ) ) );
      have h_interval : ∃ k', 1 ≤ k' ∧ k' ≤ K p ∧ j' < v p n hp k' ∧ (k' = 1 ∨ j' ≥ v p n hp (k' - 1)) := by
        contrapose! h_interval;
        have h_interval : ∀ x, 1 ≤ x → x ≤ K p → j' ≥ v p n hp x := by
          intros x hx1 hx2
          induction' x with x ih;
          · contradiction;
          · grind +ring;
        exact h_interval _ ( by linarith ) ( by linarith );
      obtain ⟨ k', hk₁, hk₂, hk₃, hk₄ ⟩ := h_interval; use k'; unfold in_interval_final; aesop;
    -- Since $j'$ is in some interval $k'$, we have $k' \ge k-1$ and $k' \le k$.
    have hk'_ge_k_minus_1 : k' ≥ k - 1 := by
      have := h_update j' hj' i ⟨ s, hs, ht ⟩;
      specialize this k ( by linarith ) ( by linarith ) hi ( by linarith );
      contrapose! this;
      rcases k' with ( _ | _ | k' ) <;> simp_all +arith +decide [ in_interval_final ];
      · refine' lt_of_lt_of_le hk'.2 _;
        exact lemma_v_mono_final p n hp 1 ( k - 2 ) ( by norm_num ) ( by omega ) ( by omega );
      · exact lt_of_lt_of_le hk'.2.2 ( lemma_v_mono_final p n hp _ _ ( by omega ) ( by omega ) ( by omega ) )
    have hk'_le_k : k' ≤ k := by
      rcases k' with ( _ | _ | k' ) <;> rcases k with ( _ | _ | k ) <;> simp_all +arith +decide [ in_interval_final ];
      contrapose! hi;
      exact fun _ => le_trans ( lemma_v_mono_final p n hp _ _ ( by linarith ) ( by linarith ) ( by linarith ) ) ( le_trans hk'.2.1 ( by linarith [ target_index p j' s, show target_index p j' s > j' from lemma_target_gt_source_final p n hp j' s hs ] ) );
    -- Since $k' \ge k-1$ and $k' \le k$, we have $c_{j'} \le M_{k'}$.
    have h_c_j'_le_M_k' : c_step_final_v2 p n hp j' j' ≤ M p k' := by
      bound;
    have h_M_k'_le_M_k_minus_1 : M p k' ≤ M p (k - 1) := by
      apply_rules [ lemma_M_antitone ];
      omega;
    exact ⟨ h_s_pow2, le_trans h_s_le_c_j' ( le_trans h_c_j'_le_M_k' h_M_k'_le_M_k_minus_1 ) ⟩

/-
The number of steps targeting i is equal to the number of contributing scalars.
-/
theorem lemma_card_targets_eq_card_scalars (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ) :
  (Finset.filter (fun j' => IsTarget_final p n hp j' i) (Finset.range j)).card = (contributing_s_final_v2_up_to p n hp j i).card := by
    -- The contributing scalars are the union of the scalars used in each step j' that target i.
    have h_union : contributing_s_final_v2_up_to p n hp j i = Finset.biUnion (Finset.filter (fun j' => IsTarget_final p n hp j' i) (Finset.range j)) (fun j' => used_s_final_v2 p n hp j' |>.filter (fun s => target_index p j' s = i)) := by
      unfold contributing_s_final_v2_up_to IsTarget_final; aesop;
    -- Since the subsets are disjoint, the cardinality of the union is the sum of the cardinalities of each subset.
    have h_card_union : (contributing_s_final_v2_up_to p n hp j i).card = Finset.sum (Finset.filter (fun j' => IsTarget_final p n hp j' i) (Finset.range j)) (fun j' => ((used_s_final_v2 p n hp j').filter (fun s => target_index p j' s = i)).card) := by
      rw [ h_union, Finset.card_biUnion ];
      intros j' hj' j'' hj'' hij''; exact lemma_contributing_scalars_disjoint_final p n hp i j' j'' hij'';
    rw [ h_card_union, Finset.card_eq_sum_ones ];
    refine' Finset.sum_congr rfl _;
    intros j' hj'
    have h_target : ∃ s ∈ used_s_final_v2 p n hp j', target_index p j' s = i := by
      aesop;
    have := lemma_card_filter_target_eq_final p n hp j' i; aesop;

/-
For indices in intervals k >= 3, the number of previous steps targeting i is at most M_k.
-/
theorem lemma_target_count_bound_final (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (h_update : UpdateConditionUpTo_final p n hp j)
  (h_prev_coeff : ∀ j' < j, CoeffBound_final p n hp j')
  (k : ℕ) (hk : 3 ≤ k ∧ k ≤ K p)
  (i : ℕ) (hi : in_interval_final p n hp k i) :
  (Finset.filter (fun j' => IsTarget_final p n hp j' i) (Finset.range j)).card ≤ M p k := by
    rcases k with ( _ | _ | k ) <;> simp +arith +decide at *;
    -- By Lemma 2, the set of scalars $\{s \mid \exists j' < j, \text{used\_s\_final\_v2 } j' \ni s \land \text{target\_index } j' s = i\}$ is a subset of $\{s \le M_{k+1} \mid \exists r \ge 1, s = 2^r\}$.
    have h_scalars_subset : (contributing_s_final_v2_up_to p n hp j i) ⊆ Finset.image (fun r => 2^r) (Finset.Icc 1 (Nat.log2 (M p (k + 1)))) := by
      -- By Lemma 2, the set of scalars $\{s \mid \exists j' < j, \text{used\_s\_final\_v2 } j' \ni s \land \text{target\_index } j' s = i\}$ is a subset of $\{s \le M_{k+1} \mid \exists r \ge 1, s = 2^r\}$. Thus, we can apply `lemma_scalars_subset_S`.
      intros s hs
      obtain ⟨j', hj'_lt_j, hj'_target⟩ : ∃ j' < j, s ∈ used_s_final_v2 p n hp j' ∧ target_index p j' s = i := by
        unfold contributing_s_final_v2_up_to at hs; aesop;
      have := lemma_target_scalar_properties p n hp j h_update h_prev_coeff ( k + 2 ) ⟨ by linarith, by linarith ⟩ i hi j' hj'_lt_j s hj'_target.1 hj'_target.2;
      rcases this.1 with ⟨ r, rfl ⟩ ; rcases r with ( _ | r ) <;> simp_all +decide [ Nat.log2 ] ;
      · have := lemma_used_s_final_v2_properties p n hp j' 1 hj'_target.1; aesop;
      · -- Since $2^{r+1} \leq M p (k + 1)$, we have $r + 1 \leq \log_2(M p (k + 1))$.
        have h_log : r + 1 ≤ Nat.log2 (M p (k + 1)) := by
          rw [ Nat.le_log2 ] <;> linarith [ Nat.pow_le_pow_right two_pos ( show r + 1 ≥ 1 by linarith ) ];
        convert h_log using 1;
    -- The cardinality of the set $\{s \le M_{k+1} \mid \exists r \ge 1, s = 2^r\}$ is at most $\log_2 M_{k+1}$.
    have h_card_scalars : (contributing_s_final_v2_up_to p n hp j i).card ≤ Nat.log2 (M p (k + 1)) := by
      exact le_trans ( Finset.card_le_card h_scalars_subset ) ( Finset.card_image_le.trans ( by simp ) );
    -- By Lemma 1, the number of steps targeting i is equal to the number of scalars contributing to i.
    have h_card_steps : (Finset.filter (fun j' => IsTarget_final p n hp j' i) (Finset.range j)).card = (contributing_s_final_v2_up_to p n hp j i).card := by
      exact lemma_card_targets_eq_card_scalars p n hp j i;
    exact h_card_steps.symm ▸ h_card_scalars.trans ( by rcases k with ( _ | k ) <;> tauto )

/-
For indices in intervals k >= 3, the initial coefficient is 0.
-/
theorem lemma_c_init_eq_zero_of_ge_3_final (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (i : ℕ) (k : ℕ) (hk : k ≥ 3) (hk_le : k ≤ K p) (hi : in_interval_final p n hp k i) :
  c_init p n hp i = 0 := by
    exact c_init_eq_zero_of_ge_3_v3 p n hp hn i k hk hk_le hi

/-
For indices in intervals k >= 3, the coefficient at step j is bounded by M_k.
-/
theorem lemma_bound_final_ge3 (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (j : ℕ)
  (h_update : UpdateConditionUpTo_final p n hp j)
  (h_prev_coeff : ∀ j' < j, CoeffBound_final p n hp j')
  (k : ℕ) (hk : 3 ≤ k ∧ k ≤ K p)
  (i : ℕ) (hi : in_interval_final p n hp k i)
  (h_ge : i ≥ j) :
  c_step_final_v2 p n hp j i ≤ M p k := by
    rw [ lemma_c_step_final_eq_init_plus_card ];
    · have := lemma_c_init_eq_zero_of_ge_3_final p n hp hn i k hk.left hk.right hi;
      have := lemma_target_count_bound_final p n hp j h_update h_prev_coeff k hk i hi;
      rw [ lemma_card_targets_eq_card_scalars ] at this ; linarith;
    · assumption

/-
If j is in the second interval and the coefficient is bounded by M_2, then the used scalars are in S.
-/
theorem lemma_used_s_subset_S_final_v2_I2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (hj : in_interval_final p n hp 2 j)
  (hc : c_step_final_v2 p n hp j j ≤ M p 2) :
  used_s_final_v2 p n hp j ⊆ S p := by
    have h_scalar_bound : ∀ s ∈ used_s_final_v2 p n hp j, s ≤ M p 2 := by
      intros s hs;
      exact le_trans ( lemma_used_s_final_v2_sum_le p n hp j |> le_trans ( Finset.single_le_sum ( fun x _ => Nat.zero_le x ) hs ) ) hc;
    intros s hs
    have hs_pow2 : ∃ r, s = 2^r := by
      have h_scalar_pow2 : ∀ s ∈ used_s_final_v2 p n hp j, ∃ r, s = 2^r := by
        intro s hs
        have h_scalar_bounds : s ≤ c_step_final_v2 p n hp j j := by
          have := @lemma_used_s_final_v2_sum_le p n hp j;
          exact le_trans ( Finset.single_le_sum ( fun x _ => Nat.zero_le x ) hs ) this
        have h_scalar_pow2 : ∀ s ∈ used_s_final_v2 p n hp j, s ≤ c_step_final_v2 p n hp j j ∧ ∃ r, s = 2^r := by
          apply lemma_used_s_final_v2_ge_m_properties;
          exact lemma_j_ge_m_sub_1_of_in_interval_final_ge_2 p n hp j 2 ( by norm_num ) ( by
            unfold K; aesop; ) hj
        exact h_scalar_pow2 s hs |>.2;
      exact h_scalar_pow2 s hs
    have hs_gt_1 : s > 1 := by
      have := lemma_used_s_final_v2_properties p n hp j s hs; aesop;
    have hs_le_card : s ≤ (S p).card := by
      exact le_trans ( h_scalar_bound s hs ) ( by unfold M; norm_num )
    exact lemma_pow2_in_S_if_le_card_v2 p hp s hs_pow2 hs_gt_1 hs_le_card

/-
If j is in the first interval and the coefficient is bounded by M_1, then the used scalars are in S.
-/
theorem lemma_used_s_subset_S_of_I1 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (hj : in_interval_final p n hp 1 j)
  (hc : c_step_final_v2 p n hp j j ≤ M p 1) :
  used_s_final_v2 p n hp j ⊆ S p := by
    -- Since $j < m-1$, we have $c_step_final_v2 j j \leq M_0 + |S|$.
    have h_bound : c_step_final_v2 p n hp j j ≤ M_0 p + (S p).card := by
      unfold in_interval_final at hj; aesop;
    -- Apply the lemma that states if the coefficient is within the valid range for decompose_S, then the used scalars are a subset of S.
    apply lemma_used_s_final_v2_subset_S_of_bound p n hp j (by
    -- Since $j$ is in the first interval, we have $j < v p n hp 1$.
    have h_j_lt_v1 : j < v p n hp 1 := by
      unfold in_interval_final at hj; aesop;
    -- Since $v p n hp 1 = m p n hp - 1$, we can substitute this into the inequality $j < v p n hp 1$.
    have h_v1_eq_m_minus_1 : v p n hp 1 = m p n hp - 1 := by
      exact v_1_eq_m_sub_1 p n hp;
    exact h_v1_eq_m_minus_1 ▸ h_j_lt_v1) h_bound

/-
For indices in the second interval, the contributing scalars are a subset of S.
-/
theorem lemma_contributing_subset_S_final_interval_2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (i : ℕ)
  (hi : in_interval_final p n hp 2 i)
  (h_ge : i ≥ j)
  (h_prev : ∀ j' < j, CoeffBound_final p n hp j') :
  contributing_s_final_v2_up_to p n hp j i ⊆ S p := by
    unfold contributing_s_final_v2_up_to;
    intro s hs
    obtain ⟨j', hj', hs'⟩ : ∃ j', j' < j ∧ s ∈ used_s_final_v2 p n hp j' ∧ target_index p j' s = i := by
      aesop;
    -- Since $j' < j$ and $j < v_p^{(2)}$, we have $j' < v_p^{(2)}$. Therefore, $j'$ is in the first interval or the second interval.
    by_cases hj'_interval : j' < v p n hp 1;
    · -- Since $j' < v_p^{(1)}$, we have $c_{j'} \le M_1$.
      have h_coeff_j'_le_M1 : c_step_final_v2 p n hp j' j' ≤ M p 1 := by
        have := h_prev j' hj';
        exact this 1 ( by norm_num ) ( by linarith [ show K p ≥ 1 from Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( by unfold K; aesop ) ) ] ) j' ( by unfold in_interval_final; aesop );
      exact lemma_used_s_subset_S_of_I1 p n hp j' ( by unfold in_interval_final; aesop ) h_coeff_j'_le_M1 hs'.1;
    · -- Since $j' \geq v_p^{(2)}$, we have $j'$ is in the second interval.
      have hj'_interval_2 : v p n hp 1 ≤ j' ∧ j' < v p n hp 2 := by
        exact ⟨ le_of_not_gt hj'_interval, by linarith [ hi.2 ] ⟩;
      -- Since $j'$ is in the second interval, we have $c_step_final_v2 p n hp j' j' \leq M_2$.
      have h_coeff_bound : c_step_final_v2 p n hp j' j' ≤ M p 2 := by
        apply_rules [ lemma_bound_final_ge3 ];
        · norm_num;
        · unfold K; aesop;
      have := lemma_used_s_subset_S_final_v2_I2 p n hp j' hj'_interval_2 h_coeff_bound; aesop;

/-
If the initial coefficient is 0 for an index in the second interval, the coefficient bound holds.
-/
theorem lemma_bound_final_k2_case_0 (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (j : ℕ) (i : ℕ)
  (hi : in_interval_final p n hp 2 i)
  (h_ge : i ≥ j)
  (h_prev : ∀ j' < j, CoeffBound_final p n hp j')
  (h_init : c_init p n hp i = 0) :
  c_step_final_v2 p n hp j i ≤ M p 2 := by
    -- Since $c_{init}(i) = 0$, we have $c_{step}(i) = \text{card}(contributing\_scalars)$.
    have h_card : c_step_final_v2 p n hp j i = (contributing_s_final_v2_up_to p n hp j i).card := by
      rw [ lemma_c_step_final_eq_init_plus_card p n hp j i h_ge, h_init, zero_add ];
    -- The contributing scalars are a subset of S, so their cardinality is at most the cardinality of S.
    have h_card_le_S : (contributing_s_final_v2_up_to p n hp j i).card ≤ (S p).card := by
      exact le_trans ( Finset.card_le_card <| lemma_contributing_subset_S_final_interval_2 p n hp j i hi h_ge h_prev ) ( by norm_num );
    unfold M; aesop;

/-
If the target is a power of 2, the number of contributing scalars is at most |S| - 1.
-/
theorem lemma_card_contributing_le_S_sub_one_final_if_pow2_I2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (i : ℕ)
  (hi : in_interval_final p n hp 2 i)
  (h_ge : i ≥ j)
  (h_prev : ∀ j' < j, CoeffBound_final p n hp j')
  (h_pow2 : ∃ r, a_seq p i = 2^r) :
  (contributing_s_final_v2_up_to p n hp j i).card ≤ (S p).card - 1 := by
    -- By `lemma_contributing_subset_S_final_interval_2`, `contributing_s_final_v2_up_to p n hp j i ⊆ S p`.
    have h_subset : contributing_s_final_v2_up_to p n hp j i ⊆ S p := by
      exact lemma_contributing_subset_S_final_interval_2 p n hp j i hi h_ge h_prev;
    -- By `exists_non_pow2_in_S`, there exists `x ∈ S p` such that `x` is not a power of 2.
    obtain ⟨x, hx_S, hx_not_pow2⟩ : ∃ x ∈ S p, ¬∃ r, x = 2^r := by
      have := exists_non_pow2_in_S p hp;
      aesop;
    -- Let `s ∈ contributing_s_final_v2_up_to p n hp j i`. Then `s ∈ S p` and `s` is a power of 2.
    have h_pow2_s : ∀ s ∈ contributing_s_final_v2_up_to p n hp j i, ∃ r, s = 2^r := by
      intros s hs
      obtain ⟨j', hj', hs_j'⟩ : ∃ j' < j, s ∈ used_s_final_v2 p n hp j' ∧ target_index p j' s = i := by
        unfold contributing_s_final_v2_up_to at hs; aesop;
      have := lemma_s_is_pow2_of_target_pow2 p hp.2 j' s (lemma_used_s_final_v2_properties p n hp j' s hs_j'.1 |>.1) i hs_j'.2 h_pow2; aesop;
    refine' Nat.le_sub_one_of_lt ( Finset.card_lt_card _ );
    exact ⟨ h_subset, fun h => hx_not_pow2 <| h_pow2_s x <| h hx_S ⟩

/-
If the initial coefficient is 1 for an index in the second interval, the coefficient bound holds.
-/
theorem lemma_bound_final_k2_case_1 (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (j : ℕ) (i : ℕ)
  (hi : in_interval_final p n hp 2 i)
  (h_ge : i ≥ j)
  (h_prev : ∀ j' < j, CoeffBound_final p n hp j')
  (h_init : c_init p n hp i = 1) :
  c_step_final_v2 p n hp j i ≤ M p 2 := by
    -- Apply the lemma that states if the target is a power of 2, the number of contributing scalars is at most |S| - 1.
    have h_cardContributing : (contributing_s_final_v2_up_to p n hp j i).card ≤ (S p).card - 1 := by
      apply lemma_card_contributing_le_S_sub_one_final_if_pow2_I2 p n hp j i hi h_ge h_prev;
      apply lemma_c_init_eq_one_imp_pow2_ge_m_sub_1;
      apply lemma_j_ge_m_sub_1_of_in_interval_final_ge_2;
      any_goals assumption;
      · norm_num;
      · unfold K; aesop;
    rw [ lemma_c_step_final_eq_init_plus_card ];
    · refine' le_trans ( add_le_add_left h_cardContributing _ ) _;
      unfold M; norm_num [ h_init ] ;
      rw [ add_tsub_cancel_of_le ];
      exact Finset.card_pos.mpr ( by obtain ⟨ x, hx ⟩ := lemma_S_contains_odd p hp; exact ⟨ x, hx.1 ⟩ );
    · assumption

/-
For indices in the second interval, the coefficient at step j is bounded by M_2.
-/
theorem lemma_bound_final_k2 (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (j : ℕ) (i : ℕ)
  (hi : in_interval_final p n hp 2 i)
  (h_ge : i ≥ j)
  (h_prev : ∀ j' < j, CoeffBound_final p n hp j') :
  c_step_final_v2 p n hp j i ≤ M p 2 := by
    -- Since $i \in I_2$, $i \ge m-1$.
    have h_ge_m_sub_1 : i ≥ m p n hp - 1 := by
      unfold in_interval_final at hi;
      -- Since $i \ge v p n hp 1$ and $v p n hp 1 = m p n hp - 1$, we have $i \ge m p n hp - 1$.
      have h_i_ge_m_sub_1 : i ≥ m p n hp - 1 := by
        have h_v1 : v p n hp 1 = m p n hp - 1 := by
          exact v_1_eq_m_sub_1 p n hp
        grind;
      exact h_i_ge_m_sub_1;
    -- Since $c_{init}(i) \le 1$, we have two cases: $c_{init}(i) = 0$ or $c_{init}(i) = 1$.
    by_cases h_init : c_init p n hp i = 0 ∨ c_init p n hp i = 1;
    · cases h_init <;> [ exact lemma_bound_final_k2_case_0 p n hp hn j i hi h_ge h_prev ‹_› ; exact lemma_bound_final_k2_case_1 p n hp hn j i hi h_ge h_prev ‹_› ];
    · -- Since $c_{init}(i)$ is a natural number, it must be either 0 or 1. Therefore, the assumption h_init is impossible.
      have h_contra : c_init p n hp i ≤ 1 := by
        exact c_init_le_one_of_ge_m_sub_1 p n hp i h_ge_m_sub_1;
      interval_cases c_init p n hp i <;> trivial

/-
For indices in the first interval, the coefficient at step j is bounded by M_1.
-/
theorem lemma_bound_final_k1_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (j : ℕ) (i : ℕ)
  (hi : in_interval_final p n hp 1 i)
  (h_ge : i ≥ j)
  (h_prev : ∀ j' < j, CoeffBound_final p n hp j') :
  c_step_final_v2 p n hp j i ≤ M p 1 := by
    exact lemma_bound_final_k1 p n hp hn j i hi h_ge h_prev

/-
For indices in intervals k >= 2, the coefficient at step j is bounded by M_k.
-/
theorem lemma_bound_final_ge2 (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (j : ℕ)
  (h_update : UpdateConditionUpTo_final p n hp j)
  (h_prev_coeff : ∀ j' < j, CoeffBound_final p n hp j')
  (k : ℕ) (hk : 2 ≤ k ∧ k ≤ K p)
  (i : ℕ) (hi : in_interval_final p n hp k i)
  (h_ge : i ≥ j) :
  c_step_final_v2 p n hp j i ≤ M p k := by
    rcases hk with ⟨ hk_ge_2, hk_le_K ⟩;
    by_cases hk_eq_2 : k = 2;
    · subst hk_eq_2;
      apply lemma_bound_final_k2 p n hp hn j i hi h_ge h_prev_coeff;
    · have hk_ge_3 : k ≥ 3 := by omega;
      apply lemma_bound_final_ge3 p n hp hn j h_update h_prev_coeff k ⟨ hk_ge_3, hk_le_K ⟩ i hi h_ge;

/-
After step k, the coefficient at index k is at most 1.
-/
theorem lemma_coeff_bound_final_step (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (j : ℕ)
  (h_inv_prev : ∀ j' < j, Lemma3_invariant_final p n hp j') :
  CoeffBound_final p n hp j := by
    have h_coeff_bound : ∀ k, 1 ≤ k → k ≤ K p → ∀ i, in_interval_final p n hp k i → i ≥ j → c_step_final_v2 p n hp j i ≤ M p k := by
      intro k hk hk_le i hi h_ge
      by_cases hk_ge2 : k ≥ 2;
      · apply_rules [ lemma_bound_final_ge2 ];
        · exact lemma_update_condition_final_step p n hp j fun j' hj' => h_inv_prev j' hj' |>.1;
        · exact fun j' hj' => h_inv_prev j' hj' |>.1;
        · exact ⟨ hk_ge2, hk_le ⟩;
      · interval_cases k ; exact lemma_bound_final_k1_v2 p n hp hn j i hi h_ge ( fun j' hj' => h_inv_prev j' hj' |>.1 );
    exact fun k hk₁ hk₂ i hi => if h : i ≥ j then h_coeff_bound k hk₁ hk₂ i hi h else by
      have h_coeff_bound_lt_j : ∀ j' < j, c_step_final_v2 p n hp j' i ≤ M p k := by
        exact fun j' hj' => h_inv_prev j' hj' |>.1 k hk₁ hk₂ i hi;
      have h_coeff_bound_lt_j : c_step_final_v2 p n hp i i ≤ M p k := by
        exact h_coeff_bound_lt_j i ( lt_of_not_ge h );
      have h_coeff_bound_lt_j : c_step_final_v2 p n hp j i = c_step_final_v2 p n hp (i + 1) i := by
        have h_coeff_bound_lt_j : ∀ j' ≥ i + 1, c_step_final_v2 p n hp j' i = c_step_final_v2 p n hp (i + 1) i := by
          intro j' hj'
          induction' hj' with j' hj' ih;
          · rfl;
          · rw [ ← ih, show c_step_final_v2 p n hp ( j' + 1 ) i = c_step_final_v2 p n hp j' i from ?_ ];
            have h_coeff_bound_lt_j : c_step_final_v2 p n hp (j' + 1) i = c_step_final_v2 p n hp j' i + if ∃ s ∈ used_s_final_v2 p n hp j', target_index p j' s = i then 1 else 0 := by
              exact lemma_c_step_final_succ_eq p n hp j' i ( by aesop );
            rw [ h_coeff_bound_lt_j, if_neg ];
            · norm_num;
            · exact fun ⟨ s, hs₁, hs₂ ⟩ => by linarith [ lemma_target_gt_source_final p n hp j' s hs₁, Nat.succ_le_iff.mp hj' ] ;
        exact h_coeff_bound_lt_j j ( by linarith );
      have h_coeff_bound_lt_j : c_step_final_v2 p n hp (i + 1) i ≤ c_step_final_v2 p n hp i i := by
        rw [ show c_step_final_v2 p n hp ( i + 1 ) = step_transform_final_v2 p n hp ( c_step_final_v2 p n hp i ) i from rfl ] ; unfold step_transform_final_v2 ; aesop;
      linarith

/-
The invariant holds for all steps j.
-/
theorem lemma_invariant_final_holds (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (j : ℕ) :
  Lemma3_invariant_final p n hp j := by
    -- We proceed by strong induction on $j$.
    induction' j using Nat.strong_induction_on with j ih;
    -- Apply the lemma that states the coefficient bound holds for j if it holds for all previous steps.
    have h_coeff_bound : CoeffBound_final p n hp j := by
      apply lemma_coeff_bound_final_step p n hp hn j;
      exact ih;
    exact ⟨ h_coeff_bound, lemma_update_condition_final_step p n hp j fun j' hj' => ( ih j' hj' ) |>.1 ⟩

/-
After step k, the coefficient at index k is at most 1.
-/
theorem lemma_c_step_final_v2_at_k_le_one (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) :
  c_step_final_v2 p n hp (k + 1) k ≤ 1 := by
    -- By definition of `c_step_final_v2`, the value at index `k` is determined by the `if i = k` branch.
    have h_step : c_step_final_v2 p n hp (k + 1) k = if k < m p n hp - 1 then 0 else if c_step_final_v2 p n hp k k > 1 then c_step_final_v2 p n hp k k - (decompose_even_pow2 (c_step_final_v2 p n hp k k)).sum id else c_step_final_v2 p n hp k k := by
      -- By definition of `step_transform_final_v2`, the value at index `k` is determined by the `if i = k` branch.
      have h_step : c_step_final_v2 p n hp (k + 1) k = (step_transform_final_v2 p n hp (c_step_final_v2 p n hp k) k) k := by
        exact rfl;
      exact h_step.trans ( by unfold step_transform_final_v2; aesop );
    split_ifs at h_step <;> simp_all +decide [ Nat.sub_eq_zero_of_le ];
    have := decompose_even_pow2_spec ( c_step_final_v2 p n hp k k );
    cases this ‹_› |>.1 <;> simp_all +decide [ add_comm ];
    omega

/-
The coefficient at index i does not change during step j if i < j.
-/
theorem lemma_c_step_final_v2_stable (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ) (h : i < j) :
  c_step_final_v2 p n hp (j + 1) i = c_step_final_v2 p n hp j i := by
    -- Since $i < j$, by the lemma_c_step_final_succ_eq, the coefficient at $i$ in step $j+1$ is equal to the coefficient at $i$ in step $j$ plus the number of scalars used in step $j$ that target $i$. However, since $i < j$, by the lemma_target_gt_source_final, the target index of any scalar used in step $j$ is greater than $j$, which cannot be $i$. Hence, the number of such scalars is zero.
    have h_no_targets : ¬∃ s ∈ used_s_final_v2 p n hp j, target_index p j s = i := by
      exact fun ⟨ s, hs₁, hs₂ ⟩ => by linarith [ lemma_target_gt_source_final p n hp j s hs₁ ] ;
    rw [ lemma_c_step_final_succ_eq ] ; aesop;
    linarith

/-
The final coefficient at index i is at most 1.
-/
theorem lemma_c_final_v2_le_one (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (i : ℕ) (hi : i < final_step_index p n hp) :
  c_final_val_v2 p n hp i ≤ 1 := by
    -- Apply the lemma that states the coefficient at step j+1 for index j is at most 1.
    have h_step : c_step_final_v2 p n hp (i + 1) i ≤ 1 := by
      exact lemma_c_step_final_v2_at_k_le_one p n hp i;
    convert h_step using 1;
    have h_stable : ∀ j ≥ i + 1, c_step_final_v2 p n hp j i = c_step_final_v2 p n hp (i + 1) i := by
      intro j hj
      induction' hj with j hj ih;
      · exact rfl;
      · rw [ ← ih, lemma_c_step_final_v2_stable ] ; aesop;
    exact h_stable _ ( Nat.succ_le_of_lt hi )

/-
Every index j < v(K) belongs to some interval k.
-/
theorem lemma_interval_coverage_final (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (hj : j < v p n hp (K p)) :
  ∃ k, 1 ≤ k ∧ k ≤ K p ∧ in_interval_final p n hp k j := by
    -- Let $k$ be the smallest integer such that $j < v(k)$.
    obtain ⟨k, hk⟩ : ∃ k, 1 ≤ k ∧ k ≤ K p ∧ j < v p n hp k ∧ ∀ k', 1 ≤ k' → k' < k → j ≥ v p n hp k' := by
      have h_exists_k : ∃ k, 1 ≤ k ∧ k ≤ K p ∧ j < v p n hp k := by
        exact ⟨ K p, by linarith [ show K p ≥ 1 from Nat.succ_le_of_lt ( show K p > 0 from by { unfold K; aesop } ) ], by linarith, hj ⟩
      generalize_proofs at *;
      exact ⟨ Nat.find h_exists_k, Nat.find_spec h_exists_k |>.1, Nat.find_spec h_exists_k |>.2.1, Nat.find_spec h_exists_k |>.2.2, fun k' hk₁ hk₂ => not_lt.1 fun hk₃ => Nat.find_min h_exists_k hk₂ ⟨ hk₁, by linarith [ Nat.find_spec h_exists_k |>.2.1 ], hk₃ ⟩ ⟩
    generalize_proofs at *;
    rcases k with ( _ | _ | k ) <;> unfold in_interval_final <;> aesop

/-
The coefficient at index i becomes 0 after step i, if i < m - 1.
-/
theorem lemma_c_step_final_v2_eq_zero_at_step (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (hi : i < m p n hp - 1) :
  c_step_final_v2 p n hp (i + 1) i = 0 := by
    -- By definition of `step_transform_final_v2`, we know that if `k < m p n hp - 1`, then the coefficient at index `k` is zero.
    have h_step_transform : ∀ (c : ℕ → ℕ) (k : ℕ), k < m p n hp - 1 → (step_transform_final_v2 p n hp c k k) = 0 := by
      unfold step_transform_final_v2; aesop;
    exact h_step_transform _ _ hi

/-
The final coefficient at index i is 0 if i < m - 1.
-/
theorem lemma_c_final_v2_eq_zero_of_lt_m_sub_1 (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (hi : i < m p n hp - 1) :
  c_final_val_v2 p n hp i = 0 := by
    -- By definition of `final_step_index`, we know that `final_step_index > i`.
    have h_final_step_gt_i : final_step_index p n hp > i := by
      unfold final_step_index;
      -- By definition of $v$, we know that $v_{K p} \geq v_1$.
      have hv_ge_v1 : v p n hp (K p) ≥ v p n hp 1 := by
        apply lemma_v_mono_final;
        · norm_num;
        · norm_num;
        · exact Nat.one_le_iff_ne_zero.mpr ( by unfold K; aesop );
      -- By definition of $v$, we know that $v_1 = m - 1$.
      have hv1_eq_m_sub_1 : v p n hp 1 = m p n hp - 1 := by
        exact v_1_eq_m_sub_1 p n hp;
      linarith;
    -- By definition of `final_step_index`, we know that `final_step_index > i`, so `c_step_final_v2` is stable for `j > i`.
    have h_stable : ∀ j ≥ i + 1, c_step_final_v2 p n hp j i = c_step_final_v2 p n hp (i + 1) i := by
      intro j hj
      induction' hj with j hj ih;
      · rfl;
      · rw [ ← ih, lemma_c_step_final_v2_stable ] ; aesop;
    -- Apply the stability result to conclude that the final coefficient at index i is zero.
    have h_final_zero : c_step_final_v2 p n hp (final_step_index p n hp) i = c_step_final_v2 p n hp (i + 1) i := by
      exact h_stable _ h_final_step_gt_i;
    exact h_final_zero.trans ( lemma_c_step_final_v2_eq_zero_at_step p n hp i hi )

/-
If j is in the last interval K, then no scalars are used in step j.
-/
theorem lemma_used_s_empty_of_in_interval_K_final (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (j : ℕ) (hj : in_interval_final p n hp (K p) j) :
  used_s_final_v2 p n hp j = ∅ := by
    -- By Lemma3_invariant_final, we know that CoeffBound_final holds.
    have h_coeff_bound : CoeffBound_final p n hp j := by
      exact lemma_invariant_final_holds p n hp hn j |>.1;
    have h_coeff_le_one : c_step_final_v2 p n hp j j ≤ 1 := by
      -- Since $j$ is in the $K$-th interval, we can apply the coefficient bound for $k=K$.
      have h_coeff_bound_K : c_step_final_v2 p n hp j j ≤ M p (K p) := by
        exact h_coeff_bound _ ( by linarith [ K_ge_2 p ] ) ( by linarith [ K_ge_2 p ] ) _ ( by aesop );
      exact le_trans h_coeff_bound_K ( M_K_le_one p hp );
    -- If used_s_final_v2 p n hp j is non-empty, then there exists some scalar s in it.
    by_contra h_nonempty
    obtain ⟨s, hs⟩ : ∃ s, s ∈ used_s_final_v2 p n hp j := by
      exact Finset.nonempty_of_ne_empty h_nonempty;
    -- Since $s \in used_s_final_v2 p n hp j$, we have $s \leq c_step_final_v2 p n hp j j$.
    have h_s_le_coeff : s ≤ c_step_final_v2 p n hp j j := by
      have := lemma_used_s_final_v2_ge_m_properties p n hp j ( lemma_j_ge_m_sub_1_of_in_interval_final_ge_2 p n hp j ( K p ) ( by linarith [ K_ge_2 p ] ) ( by linarith [ K_ge_2 p ] ) hj ) s hs; aesop;
    exact absurd ( lemma_used_s_final_v2_properties p n hp j s hs ) ( by rintro ⟨ _, hs ⟩ ; linarith )

/-
If j < v_K, then any target generated by j is < v_K.
-/
theorem lemma_target_lt_vK_of_lt_vK_final (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (j : ℕ) (hj : j < v p n hp (K p))
  (h_coeff : CoeffBound_final p n hp j) :
  ∀ s ∈ used_s_final_v2 p n hp j, target_index p j s < v p n hp (K p) := by
    -- By lemma_interval_coverage_final, there exists k such that j is in interval k.
    obtain ⟨k, hk⟩ : ∃ k, 1 ≤ k ∧ k ≤ K p ∧ in_interval_final p n hp k j := by
      exact lemma_interval_coverage p n hp j hj;
    by_cases hkK : k = K p;
    · -- If k = K p, then used_s_final_v2 p n hp j is empty by lemma_used_s_empty_of_in_interval_K_final.
      have h_empty : used_s_final_v2 p n hp j = ∅ := by
        apply lemma_used_s_empty_of_in_interval_K_final;
        · grind;
        · grind;
      aesop;
    · -- Since $k < K$, we have $s \leq u_{k+1}$ by lemma_scalar_bound_final.
      intros s hs
      have hs_le : s ≤ u p (k + 1) := by
        exact lemma_scalar_bound_final p n hp j k ⟨ hk.1, lt_of_le_of_ne hk.2.1 hkK ⟩ hk.2.2 h_coeff s hs;
      have hs_lt : target_index p j s < v p n hp (k + 1) := by
        apply lemma_target_lt_v_next_final p n hp j k s ⟨ by linarith, by omega ⟩ hk.2.2 hs_le;
        · exact Nat.pos_of_ne_zero ( by have := lemma_used_s_final_v2_properties p n hp j s hs; aesop );
        · exact lemma_used_s_final_v2_properties p n hp j s hs |>.1;
      exact lt_of_lt_of_le hs_lt ( lemma_v_mono_final p n hp ( k + 1 ) ( K p ) ( by linarith ) ( by linarith ) ( by omega ) )

/-
The coefficient at index v_K before step v_K is 0.
-/
theorem lemma_c_step_at_vK_eq_zero (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) :
  c_step_final_v2 p n hp (v p n hp (K p)) (v p n hp (K p)) = 0 := by
    -- By Lemma 3, we know that the coefficient at index $v_K$ after step $v_K$ is zero.
    have h_coeff_zero : (contributing_s_final_v2_up_to p n hp (v p n hp (K p)) (v p n hp (K p))).card = 0 := by
      -- Since $j < v_K$, any target generated by $j$ is less than $v_K$, hence $target \neq v_K$.
      have h_target_lt_vK : ∀ j < v p n hp (K p), ∀ s ∈ used_s_final_v2 p n hp j, target_index p j s < v p n hp (K p) := by
        intros j hj s hs
        apply lemma_target_lt_vK_of_lt_vK_final p n hp hn j hj (lemma_invariant_final_holds p n hp hn j).left s hs;
      rw [ Finset.card_eq_zero ];
      ext s; simp [contributing_s_final_v2_up_to]; (
      exact fun j hj hs => ne_of_lt ( h_target_lt_vK j hj s hs ));
    rw [ lemma_c_step_final_eq_init_plus_card ];
    · rw [ lemma_c_init_eq_zero_of_ge_vK p n hp hn ] ; aesop;
      rfl;
    · norm_num

/-
The final coefficient at index i is 0 if i > v_K.
-/
theorem lemma_c_final_v2_eq_zero_of_gt_vK (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (i : ℕ) (hi : i > v p n hp (K p)) :
  c_final_val_v2 p n hp i = 0 := by
    -- Since $i > v_K$, the initial coefficient $c_{\text{init}} i$ is 0.
    have h_init_zero : c_init p n hp i = 0 := by
      apply lemma_c_init_eq_zero_of_ge_vK;
      · assumption;
      · linarith;
    -- Since $i > v_K$, the set of contributing scalars is empty.
    have h_contrib_empty : contributing_s_final_v2_up_to p n hp (final_step_index p n hp) i = ∅ := by
      -- For any step $j < v(K)$, the target index of any scalar $s$ in $used_s_final_v2$ is less than $v(K)$.
      have h_target_lt_vK : ∀ j < v p n hp (K p), ∀ s ∈ used_s_final_v2 p n hp j, target_index p j s < v p n hp (K p) := by
        intros j hj s hs
        apply lemma_target_lt_vK_of_lt_vK_final p n hp hn j hj;
        · exact lemma_invariant_final_holds p n hp hn j |>.1;
        · assumption;
      -- For any step $j = v(K)$, the target index of any scalar $s$ in $used_s_final_v2$ is less than $v(K)$.
      have h_target_lt_vK_vK : ∀ s ∈ used_s_final_v2 p n hp (v p n hp (K p)), target_index p (v p n hp (K p)) s < v p n hp (K p) := by
        -- Since $c_step_final_v2 p n hp (v p n hp (K p)) (v p n hp (K p)) = 0$, any $s$ in $used_s_final_v2 p n hp (v p n hp (K p))$ must satisfy $s \leq 0$, which contradicts $s > 1$.
        have h_contra : ∀ s ∈ used_s_final_v2 p n hp (v p n hp (K p)), s ≤ 0 := by
          intros s hs
          have h_contra : s ≤ c_step_final_v2 p n hp (v p n hp (K p)) (v p n hp (K p)) := by
            apply lemma_used_s_final_v2_ge_m_properties p n hp (v p n hp (K p)) (by
            apply lemma_v_ge_v1 p n hp (K p) (by linarith [K_ge_2 p]) (by linarith [K_ge_2 p]) |> le_trans (by
            rw [ v_1_eq_m_sub_1 ])) s hs |>.1;
          exact h_contra.trans ( by rw [ lemma_c_step_at_vK_eq_zero p n hp hn ] );
        exact fun s hs => by linarith [ h_contra s hs, show s > 0 from Nat.pos_of_ne_zero fun h => by have := lemma_used_s_final_v2_properties p n hp ( v p n hp ( K p ) ) s hs; aesop ] ;
      -- Since $i > v(K)$, there are no steps $j$ where the target index is $i$.
      have h_no_target : ∀ j < final_step_index p n hp, ∀ s ∈ used_s_final_v2 p n hp j, target_index p j s ≠ i := by
        exact fun j hj s hs => ne_of_lt <| lt_of_lt_of_le ( if hj' : j = v p n hp ( K p ) then by aesop else h_target_lt_vK j ( lt_of_le_of_ne ( Nat.le_of_lt_succ hj ) hj' ) s hs ) hi.le;
      exact Finset.eq_empty_of_forall_notMem fun x hx => by obtain ⟨ j, hj₁, hj₂ ⟩ := Finset.mem_biUnion.mp hx; specialize h_no_target j ( by aesop ) x ( by aesop ) ; aesop;
    convert lemma_c_step_final_eq_init_plus_card p n hp ( final_step_index p n hp ) i _;
    · aesop;
    · unfold final_step_index; aesop;

/-
For any step j up to v_K, the targets generated are strictly less than final_step_index.
-/
theorem lemma_targets_in_range_final (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (j : ℕ) (hj : j < final_step_index p n hp) :
  ∀ s ∈ used_s_final_v2 p n hp j, target_index p j s < final_step_index p n hp := by
    have h_target_lt_vK : ∀ s ∈ used_s_final_v2 p n hp j, target_index p j s < v p n hp (K p) := by
      by_cases hj_lt_vK : j < v p n hp (K p);
      · apply lemma_target_lt_vK_of_lt_vK_final p n hp hn j hj_lt_vK;
        apply lemma_invariant_final_holds p n hp hn j |>.1;
      · have h_used_s_empty : c_step_final_v2 p n hp (v p n hp (K p)) (v p n hp (K p)) = 0 := by
          exact lemma_c_step_at_vK_eq_zero p n hp hn;
        have h_used_s_empty : ∀ s ∈ used_s_final_v2 p n hp (v p n hp (K p)), s ≤ 0 := by
          intros s hs
          have h_s_le_c_step : s ≤ c_step_final_v2 p n hp (v p n hp (K p)) (v p n hp (K p)) := by
            apply le_of_not_gt; intro hs_gt;
            have := lemma_used_s_final_v2_sum_le p n hp ( v p n hp ( K p ) );
            exact this.not_gt ( lt_of_lt_of_le hs_gt ( Finset.single_le_sum ( fun x _ => Nat.zero_le x ) hs ) );
          linarith;
        have h_used_s_empty : used_s_final_v2 p n hp (v p n hp (K p)) = ∅ := by
          exact Finset.eq_empty_of_forall_notMem fun s hs => by have := h_used_s_empty s hs; exact absurd this ( not_le_of_gt ( Nat.pos_of_ne_zero ( by have := lemma_used_s_final_v2_properties p n hp ( v p n hp ( K p ) ) s hs; aesop ) ) ) ;
        cases lt_or_eq_of_le ( Nat.le_of_lt_succ hj ) <;> aesop;
    exact fun s hs => lt_of_lt_of_le ( h_target_lt_vK s hs ) ( Nat.le_succ _ )

/-
All elements in the final summands list are in A_p.
-/
theorem final_summands_in_A_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) :
  ∀ b ∈ final_summands_list_v2 p n hp, b ∈ A p := by
    intros b hb;
    -- By definition of `final_summands_list_v2`, there exists an index `i` such that `b = a_seq p i`.
    obtain ⟨i, hi⟩ : ∃ i, b = a_seq p i := by
      unfold final_summands_list_v2 at hb; aesop;
    exact hi ▸ a_seq_mem p hp.2 i

/-
The final summands list is sorted.
-/
theorem final_summands_sorted_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) :
  (final_summands_list_v2 p n hp).Sorted (· < ·) := by
    unfold final_summands_list_v2;
    have h_sorted : List.Sorted (· < ·) (List.range (final_step_index p n hp)) := by
      exact List.pairwise_iff_get.mpr ( by aesop );
    rw [ List.Sorted ] at *;
    rw [ List.pairwise_map ];
    exact List.Pairwise.imp_of_mem ( fun x y hxy => a_seq_strict_mono p hp.2 hxy ) ( List.Pairwise.filter _ h_sorted )

/-
The sum of sequence values at target indices is equal to the sum of scalars times the sequence value at the source index.
-/
theorem lemma_sum_targets_eq_sum_scalars_mul_ak (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ)
  (h_range : ∀ s ∈ used_s_final_v2 p n hp k, target_index p k s < final_step_index p n hp) :
  ∑ i ∈ Finset.range (final_step_index p n hp), (if ∃ s ∈ used_s_final_v2 p n hp k, target_index p k s = i then 1 else 0) * a_seq p i =
  (used_s_final_v2 p n hp k).sum id * a_seq p k := by
    have h_distinct : Finset.image (fun s => target_index p k s) (used_s_final_v2 p n hp k) = Finset.filter (fun i => ∃ s ∈ used_s_final_v2 p n hp k, target_index p k s = i) (Finset.range (final_step_index p n hp)) := by
      ext; aesop;
    have h_sum : ∑ i ∈ Finset.filter (fun i => ∃ s ∈ used_s_final_v2 p n hp k, target_index p k s = i) (Finset.range (final_step_index p n hp)), a_seq p i = (used_s_final_v2 p n hp k).sum (fun s => s * a_seq p k) := by
      rw [ ← h_distinct, Finset.sum_image ];
      · exact Finset.sum_congr rfl fun x hx => target_index_spec p hp.2 k x ( lemma_used_s_final_v2_properties p n hp k x hx |>.1 );
      · intro s hs t ht; apply_rules [ lemma_target_index_inj_s ] ; aesop;
        · exact lemma_used_s_final_v2_properties p n hp k s hs |>.1;
        · exact lemma_used_s_final_v2_properties p n hp k t ht |>.1;
    simp_all +decide [ Finset.sum_filter, Finset.sum_mul _ _ _ ]

/-
Algebraic lemma: The step transformation preserves the weighted sum, provided targets are distinct from the source.
-/
theorem lemma_step_transform_algebra (p n : ℕ) (hp : Odd p ∧ p > 1) (c c' : ℕ → ℕ) (k : ℕ) (U : Finset ℕ)
  (h_range : ∀ s ∈ U, target_index p k s < final_step_index p n hp)
  (h_k_lt : k < final_step_index p n hp)
  (h_ck : c' k = c k - U.sum id)
  (h_ci : ∀ i, i ≠ k → i < final_step_index p n hp → c' i = c i + (if ∃ s ∈ U, target_index p k s = i then 1 else 0))
  (h_sum_le : U.sum id ≤ c k)
  (h_sum_targets : ∑ i ∈ Finset.range (final_step_index p n hp), (if ∃ s ∈ U, target_index p k s = i then 1 else 0) * a_seq p i = U.sum id * a_seq p k)
  (h_target_neq : ∀ s ∈ U, target_index p k s ≠ k) :
  ∑ i ∈ Finset.range (final_step_index p n hp), c' i * a_seq p i = ∑ i ∈ Finset.range (final_step_index p n hp), c i * a_seq p i := by
    -- Expand the sum using the definitions of c' and the if statement.
    have h_expand : ∑ i ∈ Finset.range (final_step_index p n hp), c' i * a_seq p i = (c k - U.sum id) * a_seq p k + ∑ i ∈ Finset.range (final_step_index p n hp) \ {k}, (c i + if ∃ s ∈ U, target_index p k s = i then 1 else 0) * a_seq p i := by
      rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_range.mpr h_k_lt ) ];
      exact congrArg₂ ( · + · ) ( by rw [ h_ck ] ) ( Finset.sum_congr rfl fun x hx => by rw [ h_ci x ( by aesop ) ( by aesop ) ] );
    simp_all +decide [ Finset.sum_add_distrib, add_mul ];
    simp_all +decide [ ← Finset.sum_filter, Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_range.mpr h_k_lt ) ];
    rw [ if_neg ( by aesop ) ] at h_sum_targets ; nlinarith [ Nat.sub_add_cancel h_sum_le ]

/-
Algebraic lemma: The step transformation preserves the weighted sum, provided targets are distinct from the source.
-/
theorem lemma_step_transform_algebra_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) (c c' : ℕ → ℕ) (k : ℕ) (U : Finset ℕ)
  (h_range : ∀ s ∈ U, target_index p k s < final_step_index p n hp)
  (h_k_lt : k < final_step_index p n hp)
  (h_ck : c' k = c k - U.sum id)
  (h_ci : ∀ i, i ≠ k → i < final_step_index p n hp → c' i = c i + (if ∃ s ∈ U, target_index p k s = i then 1 else 0))
  (h_sum_le : U.sum id ≤ c k)
  (h_sum_targets : ∑ i ∈ Finset.range (final_step_index p n hp), (if ∃ s ∈ U, target_index p k s = i then 1 else 0) * a_seq p i = U.sum id * a_seq p k)
  (h_target_neq : ∀ s ∈ U, target_index p k s ≠ k) :
  ∑ i ∈ Finset.range (final_step_index p n hp), c' i * a_seq p i = ∑ i ∈ Finset.range (final_step_index p n hp), c i * a_seq p i := by
    apply_rules [ lemma_step_transform_algebra ]

/-
Definition of BoundAndSubsetAt.
-/
def BoundAndSubsetAt (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) : Prop :=
  c_step_final_v2 p n hp k k ≤ M_0 p + (S p).card ∧
  used_s_final_v2 p n hp k ⊆ S p

/-
If the bound and subset property holds for all previous steps, then the contributing scalars for the current step are a subset of S.
-/
theorem lemma_contributing_subset_S_of_prev_bound (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ)
  (h_prev : ∀ j < k, BoundAndSubsetAt p n hp j) :
  contributing_s_final_v2_up_to p n hp k k ⊆ S p := by
    intro s hs;
    -- By definition of `contributing_s_final_v2_up_to`, there exists some `j' < k` and `s ∈ used_s_final_v2 p n hp j'` such that `target_index p j' s = k`.
    obtain ⟨j', hj', hs'⟩ : ∃ j' < k, s ∈ used_s_final_v2 p n hp j' ∧ target_index p j' s = k := by
      unfold contributing_s_final_v2_up_to at hs; aesop;
    exact h_prev j' hj' |>.2 hs'.1

/-
The final coefficient at index v_K is 0.
-/
theorem c_final_v2_at_vK_eq_zero (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) :
  c_final_val_v2 p n hp (v p n hp (K p)) = 0 := by
    have := lemma_c_step_at_vK_eq_zero p n hp hn;
    -- By definition of `c_final_val_v2`, we have `c_final_val_v2 p n hp (v p n hp (K p)) = c_step_final_v2 p n hp (final_step_index p n hp) (v p n hp (K p))`.
    rw [c_final_val_v2];
    rw [ show final_step_index p n hp = v p n hp ( K p ) + 1 from rfl ];
    rw [ show c_step_final_v2 p n hp ( v p n hp ( K p ) + 1 ) = step_transform_final_v2 p n hp ( c_step_final_v2 p n hp ( v p n hp ( K p ) ) ) ( v p n hp ( K p ) ) from rfl ];
    unfold step_transform_final_v2; aesop;

/-
Every final summand is at least a_{m-1}.
-/
theorem lemma_final_summands_min (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) :
  ∀ b ∈ final_summands_list_v2 p n hp, b ≥ a_seq p (m p n hp - 1) := by
    intro b hb;
    -- Since `b` is in the final summands list, there exists an index `i` such that `c_final_val_v2 i = 1` and `b = a_seq p i`.
    obtain ⟨i, hi_coeff, rfl⟩ : ∃ i, c_final_val_v2 p n hp i = 1 ∧ b = a_seq p i := by
      unfold final_summands_list_v2 at hb; aesop;
    refine' a_seq_strict_mono p hp.2 |> ( fun h => h.monotone _ );
    contrapose! hi_coeff;
    exact ne_of_lt ( lt_of_eq_of_lt ( lemma_c_final_v2_eq_zero_of_lt_m_sub_1 p n hp i hi_coeff ) ( by norm_num ) )

/-
Every final summand is strictly less than a_{v_K}.
-/
theorem lemma_final_summands_max (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) :
  ∀ b ∈ final_summands_list_v2 p n hp, b < a_seq p (v p n hp (K p)) := by
    intros b hb
    obtain ⟨i, hi⟩ : ∃ i, i ∈ List.filter (fun i => c_final_val_v2 p n hp i = 1) (List.range (final_step_index p n hp)) ∧ b = a_seq p i := by
      unfold final_summands_list_v2 at hb; aesop;
    -- Since `c_final_val_v2 p n hp i = 1`, we must have `i < v_K`.
    have hi_lt_vK : i < v p n hp (K p) := by
      have hi_lt_vK : c_final_val_v2 p n hp i = 1 → i < v p n hp (K p) := by
        intro hi_eq_one
        by_contra hi_ge_vK;
        cases lt_or_eq_of_le ( le_of_not_gt hi_ge_vK ) <;> simp_all +decide;
        · exact absurd hi_eq_one ( by rw [ lemma_c_final_v2_eq_zero_of_gt_vK p n hp hn i ( by linarith ) ] ; norm_num );
        · have := c_final_v2_at_vK_eq_zero p n hp hn; aesop;
      aesop;
    exact hi.2.symm ▸ a_seq_strict_mono p hp.2 hi_lt_vK

/-
C_p is equal to P_K.
-/
theorem lemma_Cp_eq_PK (p : ℕ) : C_p p = P p (K p) := by
  exact rfl

/-
a_{v_K} is equal to C_p * a_{m-1}.
-/
theorem lemma_a_vK_eq (p n : ℕ) (hp : Odd p ∧ p > 1) :
  a_seq p (v p n hp (K p)) = C_p p * a_seq p (m p n hp - 1) := by
    -- By definition of $v$, we know that $a_{v K} = P_K \cdot a_{m-1}$.
    have hv_K : a_seq p (v p n hp (K p)) = P p (K p) * a_seq p (m p n hp - 1) := by
      exact v_spec p n hp (K p);
    rw [ hv_K, lemma_Cp_eq_PK ]

/-
The coefficient at index i (i != k) after step k is updated by adding 1 if i is a target.
-/
theorem lemma_c_step_final_v2_other_eq (p n : ℕ) (hp : Odd p ∧ p > 1) (k i : ℕ) (h_neq : i ≠ k) :
  c_step_final_v2 p n hp (k + 1) i = c_step_final_v2 p n hp k i + if ∃ s ∈ used_s_final_v2 p n hp k, target_index p k s = i then 1 else 0 := by
    exact lemma_c_step_final_succ_eq p n hp k i h_neq

/-
The target index is never equal to the source index.
-/
theorem lemma_target_neq_source_final (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) :
  ∀ s ∈ used_s_final_v2 p n hp k, target_index p k s ≠ k := by
    exact fun s hs => ne_of_gt ( lemma_target_gt_source_final p n hp k s hs )

/-
Any summand in the final list is strictly less than C_p times the smallest summand.
-/
theorem final_summands_max_lt_Cp_min_retry (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0)
  (h_nonempty : final_summands_list_v2 p n hp ≠ []) :
  let L := final_summands_list_v2 p n hp
  ∀ b ∈ L, b < C_p p * L.head! := by
    have := @lemma_final_summands_max p n hp hn;
    have := @lemma_a_vK_eq p n hp;
    have h_min : a_seq p (m p n hp - 1) ≤ (final_summands_list_v2 p n hp).head! := by
      have := @lemma_final_summands_min p n hp hn;
      cases h : final_summands_list_v2 p n hp <;> aesop;
    exact fun b hb => lt_of_lt_of_le ( ‹∀ b ∈ final_summands_list_v2 p n hp, b < a_seq p ( v p n hp ( K p ) ) › b hb ) ( by nlinarith [ show 0 < C_p p from Nat.pos_of_ne_zero ( by aesop ) ] )

/-
If a_k is a power of 2 and contributing scalars are in S, then the number of contributing scalars is at most |S| - 1.
-/
theorem lemma_card_contributing_le_S_sub_one_if_pow2_final_v2_lt_m (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : k < m p n hp - 1)
  (h_pow2 : ∃ r, a_seq p k = 2^r)
  (h_subset : contributing_s_final_v2_up_to p n hp k k ⊆ S p) :
  (contributing_s_final_v2_up_to p n hp k k).card ≤ (S p).card - 1 := by
    have h_card : (contributing_s_final_v2_up_to p n hp k k).card ≤ (S p).card - 1 := by
      have h_exists_odd : ∃ x ∈ S p, Odd x := lemma_S_contains_odd p hp
      obtain ⟨ x, hx₁, hx₂ ⟩ := h_exists_odd
      have h_not_in_subset : x ∉ contributing_s_final_v2_up_to p n hp k k := by
        have h_x_not_in_contributing : ∀ s ∈ contributing_s_final_v2_up_to p n hp k k, ¬Odd s := by
          intros s hs
          obtain ⟨ r, hr ⟩ := h_pow2
          have h_s_pow2 : ∃ r, s = 2^r := by
            -- By definition of contributing_s_final_v2_up_to, there exists some step j < k where s is used to target k.
            obtain ⟨j, hj₁, hj₂⟩ : ∃ j < k, s ∈ used_s_final_v2 p n hp j ∧ target_index p j s = k := by
              unfold contributing_s_final_v2_up_to at hs; aesop;
            have := lemma_s_is_pow2_of_target_pow2 p ( by linarith ) j s ( by
              exact lemma_used_s_final_v2_properties p n hp j s hj₂.1 |>.1 ) k hj₂.2 ⟨ r, hr ⟩ ; aesop;
          rcases h_s_pow2 with ⟨ r, rfl ⟩ ; simp +decide [ Nat.even_pow ];
          intro h; simp_all +decide [ contributing_s_final_v2_up_to ] ;
          obtain ⟨ a, ha₁, ha₂, ha₃ ⟩ := hs; have := lemma_used_s_final_v2_properties p n hp a; simp_all +decide [ used_s_final_v2 ] ;
          exact absurd ( this _ ha₂ ) ( by norm_num );
        exact fun h => h_x_not_in_contributing x h hx₂;
      exact Nat.le_sub_one_of_lt ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ h_subset, fun h => h_not_in_subset <| h.symm ▸ hx₁ ⟩ ) );
    exact h_card

/-
If the bound and subset property holds for all previous steps, then the coefficient at step k is bounded by M_0 + |S|.
-/
theorem lemma_c_step_final_v2_bound_lt_m_step (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : k < m p n hp - 1)
  (h_prev : ∀ j < k, BoundAndSubsetAt p n hp j) :
  c_step_final_v2 p n hp k k ≤ M_0 p + (S p).card := by
    have h_card : (contributing_s_final_v2_up_to p n hp k k).card ≤ (S p).card := by
      exact Finset.card_le_card ( lemma_contributing_subset_S_of_prev_bound p n hp k h_prev );
    have h_case : c_init p n hp k ≤ M_0 p + 1 := by
      unfold c_init;
      field_simp;
      split_ifs ; norm_num [ coeff_from_binary ];
      split_ifs <;> norm_num;
    by_cases h_pow : ∃ r, a_seq p k = 2 ^ r;
    · have h_card_le : (contributing_s_final_v2_up_to p n hp k k).card ≤ (S p).card - 1 := by
        apply lemma_card_contributing_le_S_sub_one_if_pow2_final_v2_lt_m p n hp k hk h_pow (lemma_contributing_subset_S_of_prev_bound p n hp k h_prev);
      rw [ lemma_c_step_final_eq_init_plus_card ] <;> try linarith;
      linarith [ Nat.sub_add_cancel ( show 1 ≤ ( S p ).card from Finset.card_pos.mpr ⟨ _, Finset.mem_coe.mpr ( lemma_S_contains_odd p hp |> Classical.choose_spec |> And.left ) ⟩ ) ];
    · by_cases h_gt : c_init p n hp k > M_0 p;
      · exact False.elim <| h_pow <| ak_is_pow2_of_gt_M0 p n hp k hk h_gt;
      · linarith [ lemma_c_step_final_eq_init_plus_card p n hp k k ( by linarith ) ]

/-
For k < m - 1, the coefficient at step k is bounded and the used scalars are in S.
-/
theorem lemma_c_step_final_v2_bound_lt_m (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : k < m p n hp - 1) :
  BoundAndSubsetAt p n hp k := by
    induction' k using Nat.strong_induction_on with k ih;
    have h_coeff_bound : c_step_final_v2 p n hp k k ≤ M_0 p + (S p).card := by
      apply lemma_c_step_final_v2_bound_lt_m_step p n hp k hk;
      exact fun j hj => ih j hj ( lt_trans hj hk );
    exact ⟨ h_coeff_bound, lemma_used_s_final_v2_subset_S_of_bound p n hp k hk h_coeff_bound ⟩

/-
The sequence a_seq grows at least linearly.
-/
theorem lemma_a_seq_ge_succ (p : ℕ) (hp : p > 1) (n : ℕ) : a_seq p n >= n + 1 := by
  -- We proceed by induction on $n$.
  induction' n with n ih;
  · exact Nat.one_le_iff_ne_zero.mpr ( by exact ne_of_gt ( a_seq_pos p hp 0 ) );
  · exact Nat.succ_le_of_lt ( lt_of_le_of_lt ih ( a_seq_strict_mono p hp ( Nat.lt_succ_self n ) ) )

/-
The initial coefficient is zero for indices greater than or equal to R + m.
-/
theorem lemma_c_init_eq_zero_of_ge_R_plus_m (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (hi : i >= R p n hp + m p n hp) :
  c_init p n hp i = 0 := by
    -- By Lemma~\ref{lem:coeff_from_binary_eq_zero_of_gt}, the binary part is 0 since $a_i > R$.
    have h_binary_zero : coeff_from_binary p (R p n hp) i = 0 := by
      exact coeff_from_binary_eq_zero_of_gt p hp.2 _ _ ( by linarith [ lemma_a_seq_ge_succ p hp.2 i, m_pos p n hp ] );
    unfold c_init;
    grind

/-
Definition of the sum of coefficients weighted by the sequence values at a given step.
-/
noncomputable def sum_at_step (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (final_step_index p n hp), c_step_final_v2 p n hp k i * a_seq p i

/-
The sum of initial coefficients weighted by the sequence is n.
-/
theorem lemma_sum_at_step_zero (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) :
  sum_at_step p n hp 0 = n := by
    -- Let's choose any $c$ such that $sum_at_step p n hp 0 = c$.
    set final_step := final_step_index p n hp;
    set c : ℕ → ℕ := fun i => c_init p n hp i;
    -- By definition of $sum_at_step$, we have $sum_at_step 0 = \sum_{i=0}^{final_step-1} c(i) * a_seq(i)$.
    have h_sum_at_step_zero : sum_at_step p n hp 0 = ∑ i ∈ Finset.range final_step, (c i) * a_seq p i := by
      exact rfl;
    -- By definition of $c$, we know that $\sum_{i=0}^{R_p(n) + m(p,n)} c(i) * a_seq(i) = n$.
    have h_sum_c : ∑ i ∈ Finset.range (R p n hp + m p n hp), (c i) * a_seq p i = n := by
      convert n_eq_sum_c_init p n hp;
    -- Since $c(i) = 0$ for $i \geq final_step$, the sum $\sum_{i=final_step}^{R_p(n) + m(p,n)} c(i) * a_seq(i)$ is zero.
    have h_sum_c_zero : ∑ i ∈ Finset.Ico final_step (R p n hp + m p n hp), (c i) * a_seq p i = 0 := by
      simp +zetaDelta at *;
      intros i hi₁ hi₂; exact Or.inl (by
      exact c_init_eq_zero_of_gt_vK p n hp i hi₁);
    cases le_total final_step ( R p n hp + m p n hp ) <;> simp_all +decide [ Finset.sum_range_add_sum_Ico ];
    · rw [ ← h_sum_c, Finset.sum_subset ( Finset.range_mono ‹_› ) ] ; aesop;
    · rw [ ← h_sum_c, ← Finset.sum_range_add_sum_Ico _ ‹_› ];
      simp +zetaDelta at *;
      exact fun i hi₁ hi₂ => Or.inl <| lemma_c_init_eq_zero_of_ge_R_plus_m p n hp i hi₁

/-
The coefficient at index k is updated by subtracting the sum of the used scalars.
-/
theorem lemma_c_step_final_v2_k_eq (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) :
  c_step_final_v2 p n hp (k + 1) k = c_step_final_v2 p n hp k k - (used_s_final_v2 p n hp k).sum id := by
    -- By definition of `c_step_final_v2`, we have:
    have h_c_step_def : c_step_final_v2 p n hp (k + 1) k = step_transform_final_v2 p n hp (c_step_final_v2 p n hp k) k k := by
      exact rfl;
    rw [ h_c_step_def, step_transform_final_v2 ];
    split_ifs <;> simp +decide [ *, used_s_final_v2 ];
    have := decompose_S_spec p hp ( c_step_final_v2 p n hp k k ) ?_;
    · aesop;
    · apply And.intro;
      · have h_c_step_ge_M0 : M_0 p ≤ c_init p n hp k := by
          unfold c_init; aesop;
        exact le_trans h_c_step_ge_M0 ( by rw [ lemma_c_step_final_eq_init_plus_card p n hp k k ( by linarith ) ] ; exact Nat.le_add_right _ _ );
      · apply (lemma_c_step_final_v2_bound_lt_m p n hp k ‹_›).left

/-
The sum of coefficients weighted by the sequence values is preserved at each step.
-/
theorem lemma_sum_at_step_succ (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (k : ℕ) (hk : k < final_step_index p n hp) :
  sum_at_step p n hp (k + 1) = sum_at_step p n hp k := by
    apply_rules [ lemma_step_transform_algebra_v2 ];
    -- Apply the lemma that states the targets of the used scalars are within the range.
    apply lemma_targets_in_range_final p n hp hn k hk;
    · exact lemma_c_step_final_v2_k_eq p n hp k;
    · exact fun i a a_1 ↦ lemma_c_step_final_v2_other_eq p n hp k i a;
    · exact lemma_used_s_final_v2_sum_le p n hp k;
    · apply lemma_sum_targets_eq_sum_scalars_mul_ak;
      exact fun s a ↦ lemma_targets_in_range_final p n hp hn k hk s a;
    · exact fun s a ↦ lemma_target_neq_source_final p n hp k s a

/-
The sum of coefficients weighted by the sequence values at the final step is n.
-/
theorem lemma_sum_at_step_final (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) :
  sum_at_step p n hp (final_step_index p n hp) = n := by
    -- We prove by induction on `k` that `sum_at_step p n hp k = n` for all `k <= final_step_index p n hp`.
    have h_ind : ∀ k ≤ final_step_index p n hp, sum_at_step p n hp k = n := by
      -- We proceed by induction on $k$.
      intro k hk
      induction' k with k ih;
      · exact lemma_sum_at_step_zero p n hp hn;
      · exact Eq.trans ( lemma_sum_at_step_succ p n hp hn k ( Nat.lt_of_succ_le hk ) ) ( ih ( Nat.le_of_succ_le hk ) );
    exact h_ind _ le_rfl

/-
The sum of the final summands is n.
-/
theorem lemma_final_sum_eq_n (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) :
  (final_summands_list_v2 p n hp).sum = n := by
    -- The sum of the final summands is equal to the sum of the coefficients at the final step multiplied by the sequence values.
    have h_sum_eq : (final_summands_list_v2 p n hp).sum = ∑ i ∈ Finset.range (final_step_index p n hp), (c_final_val_v2 p n hp i) * (a_seq p i) := by
      have h_sum_eq : (final_summands_list_v2 p n hp).sum = ∑ i ∈ Finset.filter (fun i => c_final_val_v2 p n hp i = 1) (Finset.range (final_step_index p n hp)), a_seq p i := by
        unfold final_summands_list_v2; aesop;
      rw [ h_sum_eq, Finset.sum_filter ];
      refine' Finset.sum_congr rfl fun i hi => _;
      have := lemma_c_final_v2_le_one p n hp hn i ( Finset.mem_range.mp hi ) ; interval_cases c_final_val_v2 p n hp i <;> simp +decide ;
    convert lemma_sum_at_step_final p n hp hn using 1

/-
The list of final summands is non-empty.
-/
theorem lemma_final_summands_nonempty (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) :
  final_summands_list_v2 p n hp ≠ [] := by
    by_contra h_empty;
    -- Since the list is empty, the sum of its elements is zero.
    have h_sum_zero : (final_summands_list_v2 p n hp).sum = 0 := by
      rw [h_empty]
      simp;
    exact absurd h_sum_zero ( by rw [ lemma_final_sum_eq_n p n hp hn ] ; positivity )

/-
Every summand in the final list is strictly less than C_p times the smallest summand.
-/
theorem final_summands_max_lt_Cp_min (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0)
  (h_nonempty : final_summands_list_v2 p n hp ≠ []) :
  let L := final_summands_list_v2 p n hp
  ∀ b ∈ L, b < C_p p * L.head! := by
    -- Apply the lemma `final_summands_max_lt_Cp_min_retry` with the given hypotheses.
    apply final_summands_max_lt_Cp_min_retry p n hp hn h_nonempty

/-
For every odd p > 1, there exists a constant C such that every positive integer n can be written as a sum of distinct elements of A_p with small spacing.
-/
theorem main_theorem (p : ℕ) (hp : Odd p ∧ p > 1) :
  ∃ C, ∀ n > 0, ∃ (L : List ℕ),
    L.Sorted (· < ·) ∧
    (∀ b ∈ L, b ∈ A p) ∧
    L.sum = n ∧
    L ≠ [] ∧
    (∀ b ∈ L, b < C * L.head!) := by
      use C_p p;
      intro n hn_pos
      use final_summands_list_v2 p n hp;
      apply And.intro;
      · exact final_summands_sorted_v2 p n hp;
      · exact ⟨ final_summands_in_A_v2 p n hp, lemma_final_sum_eq_n p n hp hn_pos, lemma_final_summands_nonempty p n hp hn_pos, final_summands_max_lt_Cp_min p n hp hn_pos ( lemma_final_summands_nonempty p n hp hn_pos ) ⟩

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

open scoped BigOperators

open Filter

theorem density_of_pos_integers : HasDensity {n : ℕ | n > 0} 1 := by
  -- Let's simplify the expression for the partial density.
  have h_density : Filter.Tendsto (fun x : ℕ => ((Finset.Ico 1 x).card : ℝ) / (x : ℝ)) Filter.atTop (nhds 1) := by
    -- We can simplify the expression inside the limit.
    suffices h_simp : Filter.Tendsto (fun x : ℕ => (x - 1 : ℝ) / x) Filter.atTop (nhds 1) by
      refine h_simp.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx; cases x <;> aesop );
    ring_nf;
    simpa using Filter.Tendsto.sub ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with x hx; aesop ) ) ( tendsto_inverse_atTop_nhds_zero_nat );
  unfold HasDensity partialDensity Set.interIio;
  -- Since the two sets are equal, their cardinalities are equal, and the limit is preserved.
  convert h_density using 1;
  congr! 2;
  · rw [ ← Set.ncard_coe_finset ] ; congr ; ext ; aesop;
  · norm_num [ Set.ncard_eq_toFinset_card' ]

open Filter

theorem main_theorem_consequence :
  ∃ C : ℝ, C > 0 ∧
  let f : ℕ × ℕ → ℕ := fun (k, l) ↦ 2 ^ k * 3 ^ l
  {n : ℕ | n > 0} ⊆ { ∑ x ∈ B, f x | (B : Finset (ℕ × ℕ)) (h : B.Nonempty) (hB : ((B.sup f : ℕ) : ℝ) ≤ C * ((B.inf' h f : ℕ) : ℝ)) } := by
    -- Apply `main_theorem` with `p=3`.
    obtain ⟨C_nat, hC_nat⟩ := main_theorem 3 ⟨by decide, by decide⟩;
    refine' ⟨ C_nat + 1, by positivity, fun n hn => _ ⟩;
    obtain ⟨ L, hL₁, hL₂, hL₃, hL₄, hL₅ ⟩ := hC_nat n hn;
    -- Let $B$ be the set of pairs $(k, l)$ such that $2^k * 3^l \in L$.
    obtain ⟨B, hB⟩ : ∃ B : Finset (ℕ × ℕ), (∀ x ∈ B, 2 ^ x.1 * 3 ^ x.2 ∈ L) ∧ (∀ x ∈ L, ∃ y ∈ B, 2 ^ y.1 * 3 ^ y.2 = x) ∧ L.sum = ∑ x ∈ B, 2 ^ x.1 * 3 ^ x.2 := by
      have hB : ∀ x ∈ L, ∃ y : ℕ × ℕ, 2 ^ y.1 * 3 ^ y.2 = x := by
        exact fun x hx => by obtain ⟨ k, l, rfl ⟩ := hL₂ x hx; exact ⟨ ⟨ k, l ⟩, rfl ⟩ ;
      choose! f hf using hB;
      refine' ⟨ L.toFinset.image f, _, _, _ ⟩ <;> simp_all +decide [ Finset.sum_image ];
      · exact fun x hx => ⟨ x, hx, hf x hx ⟩;
      · rw [ Finset.sum_image ];
        · rw [ ← hL₃, List.sum_toFinset ];
          · rw [ List.map_congr_left hf ] ; aesop;
          · exact hL₁.nodup;
        · intro x hx y hy; have := hf x; have := hf y; aesop;
    refine' ⟨ B, _, _, _ ⟩ <;> simp_all +decide [ Finset.sup'_le_iff, Finset.le_inf'_iff ];
    exact Exists.elim ( hB.2.1 _ ( Classical.choose_spec ( List.length_pos_iff_exists_mem.mp ( List.length_pos_iff.mpr hL₄ ) ) ) ) fun x hx => Exists.elim hx fun y hy => ⟨ ( x, y ), hy.1 ⟩;
    refine' mod_cast le_trans _ ( Nat.mul_le_mul_left _ <| Finset.le_inf' _ _ _ );
    rotate_left;
    exact L.head!;
    · intro x hx; specialize hB; have := hB.1 x hx; rcases L with ( _ | ⟨ y, _ | ⟨ z, L ⟩ ⟩ ) <;> simp_all +decide ;
      grind;
    · exact Finset.sup_le fun x hx => by nlinarith [ hL₅ _ ( hB.1 x hx ), Nat.zero_le ( L.head! ) ] ;

/-
Let $C > 0$. Is it true that the set of integers of the form $n = b_1 + \cdots + b_t$,
with $b_1 < \cdots < b_t$, where $b_i = 2^{k_i}3^{l_i}$ for $1 \leq i\leq t$ and
$b_t \leq Cb_1$ has density $0$?
-/
theorem erdos_845 : (false) ↔ ∀ᵉ (C : ℝ) (hC : 0 < C),
    let f : ℕ × ℕ → ℕ := fun (k, l) ↦ 2 ^ k * 3 ^ l
    HasDensity { ∑ x ∈ B, f x | (B : Finset (ℕ × ℕ)) (h : B.Nonempty)
      (hB : B.sup f ≤ C * B.inf' h f) } 0 := by
  norm_num;
  obtain ⟨C₀, hC₀_pos, hC₀⟩ : ∃ C₀ : ℝ, C₀ > 0 ∧ {n : ℕ | n > 0} ⊆ {∑ x ∈ B, 2 ^ x.1 * 3 ^ x.2 | (B : Finset (ℕ × ℕ)) (h : B.Nonempty) (hC₀ : (B.sup (fun (x : ℕ × ℕ) => 2 ^ x.1 * 3 ^ x.2) : ℕ) ≤ C₀ * (B.inf' h (fun (x : ℕ × ℕ) => 2 ^ x.1 * 3 ^ x.2) : ℕ))} := by
    convert main_theorem_consequence using 1;
  refine' ⟨ C₀, hC₀_pos, _ ⟩;
  intro h;
  -- Since $S_{C₀}$ contains all positive integers, its density is 1.
  have h_density_one : HasDensity {n : ℕ | n > 0} 1 := by
    convert density_of_pos_integers;
  have h_density_one : HasDensity {∑ x ∈ B, 2 ^ x.1 * 3 ^ x.2 | (B : Finset (ℕ × ℕ)) (h : B.Nonempty) (hC₀ : (B.sup (fun (x : ℕ × ℕ) => 2 ^ x.1 * 3 ^ x.2) : ℕ) ≤ C₀ * (B.inf' h (fun (x : ℕ × ℕ) => 2 ^ x.1 * 3 ^ x.2) : ℕ))} 1 := by
    refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' h_density_one tendsto_const_nhds _ _;
    · simp +zetaDelta at *;
      use 1;
      intro b hb; rw [ partialDensity, partialDensity ] ;
      gcongr;
      · exact Set.finite_iff_bddAbove.mpr ⟨ b, fun x hx => le_of_lt hx.2 ⟩;
      · grind;
    · refine' Filter.Eventually.of_forall fun b => div_le_one_of_le₀ _ _ <;> norm_num [ Set.ncard_eq_toFinset_card' ];
      exact le_trans ( Finset.card_filter_le _ _ ) ( by simp );
  have := h_density_one.sub h; aesop;

theorem van_doorn_everts_asymptotic_inexact :
    let f : ℕ × ℕ → ℕ := fun (k, l) ↦ 2 ^ k * 3 ^ l
    ∃ C, ∀ n, ∃ (B : Finset (ℕ × ℕ)), ¬ (∃ b ∈ B, ∃ b' ∈ B,
      f b' > C * f b) ∧ n = (∑ x ∈ B, f x) := by
  -- Apply the main theorem to obtain the constant C.
  obtain ⟨C, hC⟩ := main_theorem 3 (by decide);
  -- Apply the main theorem to obtain the constant C and the list L.
  use C + 1;
  intro n;
  by_cases hn : n > 0;
  · obtain ⟨ L, hL₁, hL₂, hL₃, hL₄, hL₅ ⟩ := hC n hn;
    -- For each element $b \in L$, there exist $k$ and $l$ such that $b = 2^k * 3^l$.
    obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ × ℕ, ∀ b ∈ L, b = 2^(f b).1 * 3^(f b).2 := by
      have h_factor : ∀ b ∈ L, ∃ k l : ℕ, b = 2^k * 3^l := by
        intro b hb; specialize hL₂ b hb; unfold A at hL₂; aesop;
      choose! k l hkl using h_factor;
      exact ⟨ fun b => ( k b, l b ), hkl ⟩;
    refine' ⟨ L.toFinset.image f, _, _ ⟩ <;> norm_num;
    · intro x hx y hy; rw [ ← hf x hx, ← hf y hy ] ; specialize hL₅ y hy; rcases L with ( _ | ⟨ z, _ | ⟨ w, L ⟩ ⟩ ) <;> norm_num at *;
      · nlinarith;
      · rcases hx with ( rfl | rfl | hx ) <;> rcases hy with ( rfl | rfl | hy ) <;> try nlinarith;
        · nlinarith [ hL₁.1.2 x hx ];
        · grind;
        · nlinarith [ hL₁.1.2 x hx, hL₁.1.2 y hy, hL₁.2.1 x hx, hL₁.2.1 y hy ];
    · rw [ ← hL₃, Finset.sum_image ];
      · rw [ ← Finset.sum_congr rfl fun x hx => hf x ( List.mem_toFinset.mp hx ), List.sum_toFinset ];
        · norm_num;
        · exact hL₁.nodup;
      · intro x hx y hy; have := hf x ( List.mem_toFinset.mp hx ) ; have := hf y ( List.mem_toFinset.mp hy ) ; norm_num at *;
        grind;
  · exact ⟨ ∅, by aesop ⟩

#print axioms erdos_845
-- 'erdos_845' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms van_doorn_everts_asymptotic_inexact
-- 'van_doorn_everts_asymptotic_inexact' depends on axioms: [propext, Classical.choice, Quot.sound]
