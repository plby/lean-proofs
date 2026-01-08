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


This is a bigger file, close to the raw output from Aristotle.


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/

/-
We have formally proven the main result of the paper: for every odd integer p > 1, there exists a constant C such that every positive integer n can be written as a sum of distinct elements of A_p (integers of the form 2^x * p^y) where the ratio between the largest and smallest summand is bounded by C. This confirms the conjecture by Erdős regarding the existence of such a constant for 3-smooth integers (and generally for p-smooth integers where p is odd). The proof constructs the sum explicitly using the algorithm described in the paper, involving the decomposition of coefficients into sums of elements from a specific set S_p and powers of 2.
-/

import Mathlib

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

def F (x : ℕ) : ℕ := (List.range (x + 1)).map (f · x) |>.prod

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
S_p is a subset of A_p.
-/
theorem S_p_subset_A (p : ℕ) : ∀ x ∈ S_p p, x ∈ A p := by
  -- By definition of $S_p$, every element in $S_p$ is either $p$ or a power of $2$ up to $2^{\lceil \log_2 p \rceil}$.
  intro x hx
  simp [S_p] at hx;
  rcases hx with ( rfl | ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ) <;> [ exact ⟨ 0, 1, by norm_num ⟩ ; exact ⟨ a, 0, by norm_num ⟩ ]

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
For p >= 3, clog 2 p + 1 < 2^(clog 2 p).
-/
theorem clog_bound (p : ℕ) (hp : 3 ≤ p) : Nat.clog 2 p + 1 < 2 ^ Nat.clog 2 p := by
  exact Nat.le_induction ( by native_decide ) ( fun m hm ih => by { rw [ pow_succ' ] ; linarith } ) _ ( show Nat.clog 2 p ≥ 2 by exact Nat.le_trans ( by native_decide ) ( Nat.clog_mono_right 2 hp ) )

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
Lemma ssize: Existence of a set S with the required properties.
-/
theorem lemma_ssize_v3 (p : ℕ) (hp_odd : Odd p) (hp_gt_1 : p > 1) :
  ∃ S : Finset ℕ,
    (∀ x ∈ S, x ∈ A p ∧ x ≠ 1) ∧
    (∀ k : ℕ, 1 ≤ k → 2^k ≤ S.card → 2^k ∈ S) ∧
    (∃ M₀ : ℕ, M₀ ≤ p ∧ M₀ > 0 ∧
      ∀ x, M₀ ≤ x → x ≤ M₀ + S.card → is_sum_of_distinct_elements S x) ∧
    S.card ≤ 1 + Nat.clog 2 p ∧
    (∃ m ∈ S, p ≤ m ∧ ∀ x ∈ S, x ≤ m ∧ m ≤ 2^(Nat.clog 2 p)) := by
      exact lemma_ssize_v2 p hp_odd hp_gt_1

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

def IsShortSum (p C : ℕ) (L : List ℕ) : Prop :=
  L.Sorted (· < ·) ∧
  (∀ b ∈ L, b ∈ A p) ∧
  L ≠ [] ∧
  (∀ b ∈ L, b < C * L.head!)

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
a_seq p i is a power of 2 if and only if i is the index of a power of 2.
-/
theorem is_pow2_iff_index (p : ℕ) (hp : p > 1) (i : ℕ) :
  (∃ k, a_seq p i = 2^k) ↔ ∃ k, i = pow2_index p hp k := by
    -- By definition of `pow2_index`, if `a_seq p i = 2^k`, then `i = pow2_index p hp k`.
    have h_pow2_index : ∀ k, a_seq p i = 2^k → i = pow2_index p hp k := by
      intro k hk;
      have h_index : a_seq p i = 2^k → i = pow2_index p hp k := by
        have h_unique : ∀ i j, a_seq p i = a_seq p j → i = j := by
          exact StrictMono.injective ( a_seq_strict_mono p hp );
        exact fun h => h_unique _ _ <| by rw [ h, pow2_index_spec p hp k ] ;
      exact h_index hk;
    exact ⟨ fun ⟨ k, hk ⟩ => ⟨ k, h_pow2_index k hk ⟩, fun ⟨ k, hk ⟩ => ⟨ k, hk ▸ pow2_index_spec p hp k ⟩ ⟩

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
The sum of terms selected by coeff_from_binary is equal to the sum of powers of 2 corresponding to the set bits of R.
-/
theorem coeff_from_binary_sum_eq_bitIndices_sum (p : ℕ) (hp : p > 1) (R : ℕ) :
  ∑ i ∈ Finset.range (R + 1), (coeff_from_binary p R i) * a_seq p i = ∑ k ∈ R.bitIndices.toFinset, 2^k := by
    convert coeff_from_binary_sum p hp R using 1;
    exact Finset.twoPowSum_toFinset_bitIndices R

/-
The sum of terms selected by coeff_from_binary is equal to R.
-/
theorem coeff_from_binary_sum_eq_R (p : ℕ) (hp : p > 1) (R : ℕ) :
  ∑ i ∈ Finset.range (R + 1), (coeff_from_binary p R i) * a_seq p i = R := by
    exact coeff_from_binary_sum p hp R

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
P_k * a_m is in A_p.
-/
theorem P_mul_am_mem_A (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) :
  P p k * a_seq p (m p n hp) ∈ A p := by
    -- By definition of $P$, we know that $P p k ∈ A p$.
    have hP : P p k ∈ A p := by
      exact P_mem_A p hp k;
    exact A_mul_closed p _ _ hP ( a_seq_mem p hp.2 _ )

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
Definition of the step transformation and the sequence of coefficients c_step.
-/
noncomputable def step_transform (p n : ℕ) (hp : Odd p ∧ p > 1) (c : ℕ → ℕ) (k : ℕ) : ℕ → ℕ :=
  if k < m p n hp then
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

noncomputable def c_step (p n : ℕ) (hp : Odd p ∧ p > 1) : ℕ → ℕ → ℕ
| 0 => c_init p n hp
| k + 1 => step_transform p n hp (c_step p n hp k) k

theorem c_step_eq_init (p n : ℕ) (hp : Odd p ∧ p > 1) :
  c_step p n hp 0 = c_init p n hp := rfl

theorem c_step_succ (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) :
  c_step p n hp (k + 1) = step_transform p n hp (c_step p n hp k) k := rfl

/-
After step k, the coefficient at index k is at most 1.
-/
theorem c_step_at_k_le_one (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) :
  c_step p n hp (k + 1) k ≤ 1 := by
    rw [ c_step_succ ];
    unfold step_transform;
    split_ifs <;> norm_num;
    · have := decompose_even_pow2_spec ( c_step p n hp k k );
      rcases this ‹_› with ⟨ h | h, h' ⟩ <;> norm_num at * <;> omega;
    · linarith

/-
Definition of in_interval.
-/
def in_interval (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (i : ℕ) : Prop :=
  if k = 1 then i ≤ v p n hp 1
  else v p n hp (k - 1) < i ∧ i ≤ v p n hp k

/-
Definition of used_s.
-/
noncomputable def used_s (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Finset ℕ :=
  let c := c_step p n hp j j
  if j < m p n hp then
    decompose_S p hp c
  else
    if c > 1 then decompose_even_pow2 c else ∅

/-
S is nonempty.
-/
theorem S_nonempty (p : ℕ) (hp : Odd p ∧ p > 1) : (S p).Nonempty := by
  have := S_properties p hp;
  exact ⟨ _, this.2.2.2.2.choose_spec.1 ⟩

/-
If x is a power of 2 and x <= y, then x <= 2^(log2 y).
-/
theorem pow2_le_imp_le_pow2_log2 (x y : ℕ) (hx : ∃ k, x = 2^k) (hxy : x ≤ y) (hy : y > 0) :
  x ≤ 2^(Nat.log2 y) := by
    -- Since x is a power of 2, let x = 2^k. If k were greater than log2(y), then 2^k would be greater than y, contradicting hxy.
    obtain ⟨k, rfl⟩ := hx
    have hk_le_log2y : k ≤ Nat.log2 y := by
      rw [ Nat.le_log2 ] <;> linarith;
    exact pow_le_pow_right₀ ( by decide ) hk_le_log2y

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
If k >= 2 and c <= M_k, then any scalar s from the decomposition of c is bounded by u_{k+1}.
-/
theorem s_le_u_k_ge_2 (p : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : k ≥ 2) (c : ℕ) (hc : c ≤ M p k) (s : ℕ) (hs : s ∈ decompose_even_pow2 c) :
  s ≤ u p (k + 1) := by
    -- By definition of `decompose_even_pow2`, if `s ∈ decompose_even_pow2 c`, then `s` is a power of 2.
    have hs_pow2 : ∃ m, s = 2 ^ m := by
      unfold decompose_even_pow2 at hs; aesop;
    -- By definition of `decompose_even_pow2`, if `s ∈ decompose_even_pow2 c`, then `s` is a power of 2 and `s ≤ c`.
    obtain ⟨m, hm⟩ := hs_pow2
    have hs_le_c : s ≤ c := by
      by_cases hc : c > 1;
      · exact decompose_even_pow2_le c hc s hs;
      · interval_cases c <;> simp_all +decide [ decompose_even_pow2 ];
    -- Since $m \leq \log_2 c$ and $c \leq M p k$, we have $m \leq \log_2 (M p k)$.
    have hm_le_log2_M : m ≤ Nat.log2 (M p k) := by
      rw [ Nat.le_log2 ] <;> linarith [ Nat.one_le_pow m 2 zero_lt_two ];
    rcases k with ( _ | _ | k ) <;> simp_all +decide [ u ];
    exact pow_le_pow_right₀ ( by decide ) hm_le_log2_M

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
index_in_A is monotone.
-/
theorem index_in_A_mono (p : ℕ) (hp : p > 1) (x y : ℕ) (hx : x ∈ A p) (hy : y ∈ A p) (hxy : x ≤ y) :
  index_in_A p x ≤ index_in_A p y := by
    -- By definition of index_in_A, we know that if x ≤ y, then a_seq p (index_in_A p x) ≤ a_seq p (index_in_A p y).
    have h_le : a_seq p (index_in_A p x) ≤ a_seq p (index_in_A p y) := by
      rw [ a_seq_index_in_A p hp x hx, a_seq_index_in_A p hp y hy ] ; assumption;
    exact le_of_not_gt fun h => h_le.not_gt <| a_seq_strict_mono p hp h

/-
If j is in the first interval, then j < m.
-/
theorem j_lt_m_of_in_interval_1 (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (j : ℕ) (hj : in_interval p n hp 1 j) :
  j < m p n hp := by
    unfold in_interval at hj;
    -- Since $m$ is positive, $m - 1 < m$, thus $j < m$.
    have h_m_pos : 0 < m p n hp := by
      exact m_pos p n hp hn;
    have h_v1_eq_m_sub_1 : v p n hp 1 = m p n hp - 1 := by
      exact v_1_eq_m_sub_1 p n hp;
    grind

/-
Helper lemma: Bound for scalars in interval 1.
-/
theorem s_le_u_with_bound_k1 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (hj : in_interval p n hp 1 j)
  (hc_lower : M_0 p ≤ c_step p n hp j j)
  (hc_upper : c_step p n hp j j ≤ M p 1) :
  ∀ s ∈ used_s p n hp j, s ≤ u p 2 := by
    unfold in_interval at hj;
    -- Since $j$ is in the first interval, $j < m$, so we use decompose_S.
    have h_decomp_S : used_s p n hp j = decompose_S p hp (c_step p n hp j j) := by
      unfold used_s;
      -- Since $j = 1$, we have $j < m p n hp$ by $j_lt_m_of_in_interval_1$.
      have hj_lt_m : j < m p n hp := by
        have h_j_lt_m : v p n hp 1 = m p n hp - 1 := by
          exact v_1_eq_m_sub_1 p n hp;
        rcases k : m p n hp with ( _ | k ) <;> simp_all +decide;
        · unfold m at k;
          unfold m_index at k;
          unfold partial_sum at k; aesop;
        · linarith;
      aesop;
    intro s hs; rw [h_decomp_S] at hs; exact s_in_S_le_u2 p hp s (decompose_S_spec p hp _ ⟨hc_lower, by
      exact hc_upper⟩ |>.1 hs)

/-
If j is in interval k >= 2, then j >= m.
-/
theorem j_ge_m_of_in_interval_ge_2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (k : ℕ) (hk : k ≥ 2) (hj : in_interval p n hp k j) :
  j ≥ m p n hp := by
    -- Since $k \geq 2$, we have $v_{k-1} \geq v_1$.
    have hv_k_minus_1_ge_v_1 : v p n hp (k - 1) ≥ v p n hp 1 := by
      unfold v;
      apply index_in_A_mono p hp.2;
      · -- Since $P p 1 = 1$ and $a_seq p (m p n hp - 1) \in A p$, their product is also in $A p$.
        have h_prod : 1 * a_seq p (m p n hp - 1) ∈ A p := by
          simpa using a_seq_mem p hp.2 ( m p n hp - 1 );
        convert h_prod using 1;
      · apply_rules [ A_mul_closed ];
        · exact P_mem_A p hp (k - 1);
        · exact a_seq_mem p hp.2 _;
      · exact Nat.mul_le_mul_right _ ( P_mono _ <| Nat.le_sub_one_of_lt hk );
    rcases k with ( _ | _ | k ) <;> simp_all +decide [ in_interval ];
    -- Since $v_1 = m - 1$, we have $m - 1 \leq v_{k+1}$.
    have hv_1_eq_m_sub_1 : v p n hp 1 = m p n hp - 1 := by
      exact v_1_eq_m_sub_1 p n hp;
    omega

/-
Helper lemma: Bound for scalars used in step j.
-/
theorem s_le_u_with_bound (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (k : ℕ) (hk : 1 ≤ k ∧ k < K p) (hj : in_interval p n hp k j)
  (hc_lower : k = 1 → M_0 p ≤ c_step p n hp j j)
  (hc_upper : c_step p n hp j j ≤ M p k) :
  ∀ s ∈ used_s p n hp j, s ≤ u p (k + 1) := by
    by_cases hk1 : k = 1;
    · -- If k=1, apply s_le_u_with_bound_k1 with hc_lower and hc_upper.
      have h_s_le_u_2 : ∀ s ∈ used_s p n hp j, s ≤ u p 2 := by
        apply s_le_u_with_bound_k1;
        · aesop;
        · exact hc_lower hk1;
        · aesop;
      aesop;
    · -- Since $k \geq 2$, we have $j \geq m$.
      have hj_ge_m : j ≥ m p n hp := by
        apply j_ge_m_of_in_interval_ge_2 p n hp j k (Nat.lt_of_le_of_ne hk.left (Ne.symm hk1)) hj;
      -- Since $k \geq 2$, we have $c_step p n hp j j \leq M_p k$.
      have hc_step_le_M_k : c_step p n hp j j ≤ M p k := by
        assumption;
      unfold used_s;
      field_simp;
      split_ifs <;> simp_all +decide [ Nat.lt_succ_iff ];
      · linarith;
      · apply s_le_u_k_ge_2 p hp k (by
        exact Nat.lt_of_le_of_ne hk.1 ( Ne.symm hk1 )) (c_step p n hp j j) (by
        linarith)

/-
Helper lemma: Bound for scalars used in step j (v2).
-/
theorem s_le_u_with_bound_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (k : ℕ) (hk : 1 ≤ k ∧ k < K p) (hj : in_interval p n hp k j)
  (hc_lower : k = 1 → M_0 p ≤ c_step p n hp j j)
  (hc_upper : c_step p n hp j j ≤ M p k) :
  ∀ s ∈ used_s p n hp j, s ≤ u p (k + 1) := by
  by_cases hk_eq_1 : k = 1
  · subst hk_eq_1
    apply s_le_u_with_bound_k1 p n hp j hj
    · apply hc_lower; rfl
    · exact hc_upper
  · have hk_ge_2 : k ≥ 2 := by
      have hk_ne_1 : k ≠ 1 := hk_eq_1
      have hk_ge_1 : k ≥ 1 := hk.1
      omega
    have hj_ge_m : j ≥ m p n hp := j_ge_m_of_in_interval_ge_2 p n hp j k hk_ge_2 hj
    intro s hs
    unfold used_s at hs
    rw [if_neg (not_lt_of_ge hj_ge_m)] at hs
    split_ifs at hs with hc_gt_1
    · apply s_le_u_k_ge_2 p hp k hk_ge_2 (c_step p n hp j j) hc_upper s hs
    · simp at hs

/-
For a fixed target i and scalar s, the source j is unique.
-/
theorem target_unique (p : ℕ) (hp : p > 1) (i : ℕ) (s : ℕ) (hs : s > 0) :
  Set.Subsingleton { j | s * a_seq p j = a_seq p i } := by
    intro j hj k hk;
    have := a_seq_strict_mono p hp;
    exact this.injective ( by nlinarith [ hj.symm, hk.symm ] )

/-
Scalars in used_s are in A_p.
-/
theorem s_in_used_s_mem_A (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (s : ℕ) (hs : s ∈ used_s p n hp j) :
  s ∈ A p := by
    revert s;
    unfold used_s;
    split_ifs <;> simp_all +decide;
    · intro s hs;
      -- By definition of `decompose_S`, if `s ∈ decompose_S p hp (c_step p n hp j j)`, then `s ∈ S p`.
      have h_s_in_S : s ∈ S p := by
        unfold decompose_S at hs;
        split_ifs at hs <;> simp_all +decide [ Finset.subset_iff ];
        have := Exists.choose_spec ( M_0_properties p hp |>.2.2 ( c_step p n hp j j ) ( by linarith ) ( by linarith ) );
        exact this.1 hs;
      exact S_properties p hp |>.1 s h_s_in_S |>.1;
    · split_ifs <;> simp_all +decide [ decompose_even_pow2 ];
      split_ifs <;> simp_all +decide [ pow2_mem_A ]

/-
Helper lemma: Bound for scalars used in step j (v3).
-/
theorem s_le_u_with_bound_v3 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (k : ℕ) (hk : 1 ≤ k ∧ k < K p) (hj : in_interval p n hp k j)
  (hc_lower : k = 1 → M_0 p ≤ c_step p n hp j j)
  (hc_upper : c_step p n hp j j ≤ M p k) :
  ∀ s ∈ used_s p n hp j, s ≤ u p (k + 1) := by
  by_cases hk_eq_1 : k = 1
  · subst hk_eq_1
    apply s_le_u_with_bound_k1 p n hp j hj
    · apply hc_lower; rfl
    · exact hc_upper
  · have hk_ge_2 : k ≥ 2 := by
      have hk_ne_1 : k ≠ 1 := hk_eq_1
      have hk_ge_1 : k ≥ 1 := hk.1
      omega
    have hj_ge_m : j ≥ m p n hp := j_ge_m_of_in_interval_ge_2 p n hp j k hk_ge_2 hj
    intro s hs
    unfold used_s at hs
    rw [if_neg (not_lt_of_ge hj_ge_m)] at hs
    split_ifs at hs with hc_gt_1
    · apply s_le_u_k_ge_2 p hp k hk_ge_2 (c_step p n hp j j) hc_upper s hs
    · simp at hs

/-
Updates from interval k land in interval k+1 (or earlier).
-/
theorem target_in_next_interval (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (k : ℕ) (hk : 1 ≤ k ∧ k < K p) (hj : in_interval p n hp k j)
  (hc_lower : k = 1 → M_0 p ≤ c_step p n hp j j)
  (hc_upper : c_step p n hp j j ≤ M p k) :
  ∀ s ∈ used_s p n hp j, target_index p j s ≤ v p n hp (k + 1) := by
    intro s hs;
    -- By definition of `target_index`, we know that `a_seq p (target_index p j s) = s * a_seq p j`.
    have h_target : a_seq p (target_index p j s) ≤ P p (k + 1) * a_seq p (m p n hp - 1) := by
      have h_div : s ≤ u p (k + 1) := by
        exact s_le_u_with_bound_v3 p n hp j k hk hj hc_lower hc_upper s hs;
      have h_div : a_seq p j ≤ P p k * a_seq p (m p n hp - 1) := by
        have h_div : j ≤ v p n hp k := by
          unfold in_interval at hj; aesop;
        refine' le_trans ( a_seq_strict_mono p hp.2 |>.monotone h_div ) _;
        rw [ v_spec ];
      have h_mul : s * a_seq p j ≤ u p (k + 1) * (P p k * a_seq p (m p n hp - 1)) := by
        gcongr;
      convert h_mul using 1;
      · exact target_index_spec p hp.2 j s ( s_in_used_s_mem_A p n hp j s hs );
      · unfold P; simp +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
        simp +decide [ List.range_succ, mul_assoc, mul_comm, mul_left_comm ];
    have h_target_le_v : a_seq p (target_index p j s) ≤ a_seq p (v p n hp (k + 1)) := by
      convert h_target using 1;
      exact v_spec p n hp ( k + 1 );
    exact le_of_not_gt fun h => h_target_le_v.not_gt <| a_seq_strict_mono p hp.2 h

/-
Helper lemma: Bound for scalars used in step j (v4).
-/
theorem s_le_u_with_bound_v4 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (k : ℕ) (hk : 1 ≤ k ∧ k < K p) (hj : in_interval p n hp k j)
  (hc_lower : k = 1 → M_0 p ≤ c_step p n hp j j)
  (hc_upper : c_step p n hp j j ≤ M p k) :
  ∀ s ∈ used_s p n hp j, s ≤ u p (k + 1) := by
  by_cases hk_eq_1 : k = 1
  · subst hk_eq_1
    apply s_le_u_with_bound_k1 p n hp j hj
    · apply hc_lower; rfl
    · exact hc_upper
  · have hk_ge_2 : k ≥ 2 := by
      have hk_ne_1 : k ≠ 1 := hk_eq_1
      have hk_ge_1 : k ≥ 1 := hk.1
      omega
    have hj_ge_m : j ≥ m p n hp := j_ge_m_of_in_interval_ge_2 p n hp j k hk_ge_2 hj
    intro s hs
    unfold used_s at hs
    rw [if_neg (not_lt_of_ge hj_ge_m)] at hs
    split_ifs at hs with hc_gt_1
    · apply s_le_u_k_ge_2 p hp k hk_ge_2 (c_step p n hp j j) hc_upper s hs
    · simp at hs

/-
Definition of contributing_s.
-/
noncomputable def contributing_s (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) : Finset ℕ :=
  (Finset.range i).biUnion (fun j => (used_s p n hp j).filter (fun s => target_index p j s = i))

/-
For a fixed target i and scalar s, the source j is unique.
-/
theorem unique_source_for_s (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (s : ℕ) :
  Set.Subsingleton { j | s ∈ used_s p n hp j ∧ target_index p j s = i } := by
    intros j hj k hk;
    -- Since $s \in A_p$ and $s \neq 0$, we have $s > 0$.
    have hs_pos : 0 < s := by
      have hs_pos : s ∈ A p := by
        exact s_in_used_s_mem_A p n hp j s hj.1;
      rcases hs_pos with ⟨ x, y, rfl ⟩ ; exact Nat.mul_pos ( pow_pos ( by decide ) _ ) ( pow_pos ( by linarith ) _ );
    have := target_unique p hp.2 i s hs_pos;
    exact this ( show s * a_seq p j = a_seq p i from by have := hj.2; have := target_index_spec p hp.2 j s ( s_in_used_s_mem_A p n hp j s hj.1 ) ; aesop ) ( show s * a_seq p k = a_seq p i from by have := hk.2; have := target_index_spec p hp.2 k s ( s_in_used_s_mem_A p n hp k s hk.1 ) ; aesop )

/-
Helper lemma: Bound for scalars used in step j (k >= 2).
-/
theorem s_le_u_with_bound_ge_2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (k : ℕ) (hk : 2 ≤ k ∧ k < K p) (hj : in_interval p n hp k j)
  (hc_upper : c_step p n hp j j ≤ M p k) :
  ∀ s ∈ used_s p n hp j, s ≤ u p (k + 1) := by
  have hj_ge_m : j ≥ m p n hp := j_ge_m_of_in_interval_ge_2 p n hp j k hk.1 hj
  intro s hs
  unfold used_s at hs
  rw [if_neg (not_lt_of_ge hj_ge_m)] at hs
  split_ifs at hs with hc_gt_1
  · apply s_le_u_k_ge_2 p hp k hk.1 (c_step p n hp j j) hc_upper s hs
  · simp at hs

/-
The coefficient c_i is the initial value plus the number of contributing scalars.
-/
theorem c_step_eq_init_plus_card (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) :
  c_step p n hp i i = c_init p n hp i + (contributing_s p n hp i).card := by
    -- By definition of $c_step$, we can express it recursively.
    have h_rec : ∀ j ≤ i, c_step p n hp j i = c_init p n hp i + ∑ k ∈ Finset.range j, (if ∃ s ∈ used_s p n hp k, target_index p k s = i then 1 else 0) := by
      intro j hj
      induction' j with j ih;
      · exact rfl;
      · rw [ Finset.sum_range_succ, ← add_assoc, ← ih ( Nat.le_of_succ_le hj ), c_step_succ ];
        unfold step_transform;
        unfold used_s; aesop;
    -- The cardinality of `contributing_s p n hp i` is equal to the sum over `j` in `Finset.range i` of the indicator function.
    have h_card : (contributing_s p n hp i).card = ∑ j ∈ Finset.range i, (if ∃ s ∈ used_s p n hp j, target_index p j s = i then 1 else 0) := by
      have h_biUnion : contributing_s p n hp i = Finset.biUnion (Finset.range i) (fun j => (used_s p n hp j).filter (fun s => target_index p j s = i)) := by
        exact rfl
      rw [ h_biUnion, Finset.card_biUnion ];
      · apply Finset.sum_congr rfl;
        intro j hj
        have h_unique : ∀ s₁ s₂, s₁ ∈ used_s p n hp j → s₂ ∈ used_s p n hp j → target_index p j s₁ = i → target_index p j s₂ = i → s₁ = s₂ := by
          intros s₁ s₂ hs₁ hs₂ hs₁_eq hs₂_eq;
          have h_unique : ∀ s₁ s₂, s₁ ∈ A p → s₂ ∈ A p → target_index p j s₁ = target_index p j s₂ → s₁ = s₂ := by
            intros s₁ s₂ hs₁ hs₂ h_eq;
            have h_unique : a_seq p (target_index p j s₁) = a_seq p (target_index p j s₂) := by
              rw [h_eq];
            have h_unique : a_seq p (target_index p j s₁) = s₁ * a_seq p j ∧ a_seq p (target_index p j s₂) = s₂ * a_seq p j := by
              exact ⟨ target_index_spec p hp.2 j s₁ hs₁, target_index_spec p hp.2 j s₂ hs₂ ⟩;
            nlinarith [ a_seq_pos p hp.2 j ];
          exact h_unique s₁ s₂ ( s_in_used_s_mem_A p n hp j s₁ hs₁ ) ( s_in_used_s_mem_A p n hp j s₂ hs₂ ) ( hs₁_eq.trans hs₂_eq.symm );
        split_ifs <;> simp_all +decide [ Finset.card_eq_one ];
        obtain ⟨ s, hs₁, hs₂ ⟩ := ‹_›; exact ⟨ s, Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_filter.mpr ⟨ hs₁, hs₂ ⟩, fun x hx => h_unique x s ( Finset.mem_filter.mp hx |>.1 ) hs₁ ( Finset.mem_filter.mp hx |>.2 ) hs₂ ⟩ ⟩ ;
      · intros j hj k hk hjk; simp_all +decide [ Finset.disjoint_left ] ;
        intro s hs₁ hs₂ hs₃ hs₄; have := unique_source_for_s p n hp i s; simp_all +decide [ Set.Subsingleton ] ;
        exact hjk ( this hs₁ hs₂ hs₃ hs₄ );
    rw [ h_rec i le_rfl, h_card ]

/-
c_init is at most 1 for i > v_1.
-/
theorem c_init_le_one_of_gt_v1 (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (hi : i > v p n hp 1) :
  c_init p n hp i ≤ 1 := by
    unfold c_init;
    split_ifs <;> simp_all +decide [ v_1_eq_m_sub_1 ];
    · linarith;
    · unfold coeff_from_binary;
      grind

/-
coeff_from_binary is at most 1.
-/
theorem coeff_from_binary_le_one (p : ℕ) (R i : ℕ) :
  coeff_from_binary p R i ≤ 1 := by
    -- By definition of coeff_from_binary, it returns either 0 or 1.
    simp [coeff_from_binary];
    split_ifs <;> norm_num

/-
c_init is bounded by M_1 for i <= v_1.
-/
theorem c_init_le_M1_of_le_v1 (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (hi : i ≤ v p n hp 1) :
  c_init p n hp i ≤ M p 1 := by
    unfold c_init at *;
    split_ifs <;> simp_all +decide [ M ];
    · exact le_trans ( coeff_from_binary_le_one _ _ _ ) ( Nat.one_le_iff_ne_zero.mpr <| Finset.card_ne_zero_of_mem <| Finset.mem_coe.mpr <| Classical.choose_spec <| S_nonempty p hp );
    · exact le_trans ( coeff_from_binary_le_one _ _ _ ) ( Nat.one_le_iff_ne_zero.mpr <| by linarith [ show 0 < M_0 p from M_0_properties p hp |>.2.1, show 0 < ( S p ).card from Finset.card_pos.mpr <| S_nonempty p hp ] )

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

/-
c_init is at most 1 for i > v_1.
-/
theorem c_init_le_one_of_gt_v1_new (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (hi : i > v p n hp 1) :
  c_init p n hp i ≤ 1 := by
  unfold c_init
  have h_base : (if i < m p n hp - 1 then M_0 p else 0) = 0 := by
    have h_v1 : v p n hp 1 = m p n hp - 1 := v_1_eq_m_sub_1 p n hp
    rw [h_v1] at hi
    have : ¬(i < m p n hp - 1) := not_lt_of_ge (le_of_lt hi)
    simp [this]
  rw [h_base, zero_add]
  apply coeff_from_binary_le_one

/-
Definition of interval_of.
-/
noncomputable def interval_of (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : ℕ :=
  if h : ∃ k, 1 ≤ k ∧ k ≤ K p ∧ in_interval p n hp k j then
    Nat.find h
  else
    K p + 1

theorem interval_of_spec (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (h : ∃ k, 1 ≤ k ∧ k ≤ K p ∧ in_interval p n hp k j) :
  let k := interval_of p n hp j
  1 ≤ k ∧ k ≤ K p ∧ in_interval p n hp k j := by
    norm_num [ interval_of ];
    split_ifs ; simp_all +decide [ Nat.find_spec h ]

/-
Definition of Bound.
-/
noncomputable def Bound (p : ℕ) (k : ℕ) : ℕ :=
  if k < 3 then M p k else M p k + 1

/-
Base case of Lemma 3: Initial coefficients satisfy the bounds.
-/
theorem lemma_maximums_base (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ K p) (i : ℕ) (hi : in_interval p n hp k i) :
  c_step p n hp 0 i ≤ M p k := by
    rcases k with ( _ | _ | k ) <;> simp_all +arith +decide [ in_interval ];
    · exact c_init_le_M1_of_le_v1 p n hp i hi;
    · -- Since $i > v p n hp (k + 1)$, we have $i > v p n hp 1$ (because $v p n hp 1 = m p n hp - 1$ and $v p n hp (k + 1) \geq v p n hp 1$).
      have hi_gt_v1 : i > v p n hp 1 := by
        refine' lt_of_le_of_lt _ hi.1;
        refine' monotone_nat_of_le_succ ( fun i => _ ) ( by linarith );
        apply_rules [ index_in_A_mono ];
        · linarith;
        · apply_rules [ A_mul_closed ];
          · exact P_mem_A p hp i;
          · exact a_seq_mem p hp.2 _;
        · apply_rules [ A_mul_closed, P_mem_A, a_seq_mem ];
          linarith;
        · exact Nat.mul_le_mul_right _ ( P_mono _ ( Nat.le_succ _ ) );
      exact le_trans ( c_init_le_one_of_gt_v1_new p n hp i hi_gt_v1 ) ( M_ge_one_of_le_K p hp ( k + 2 ) ⟨ by linarith, by linarith ⟩ )

/-
If a product is a power of 2, then the factors are powers of 2.
-/
theorem power_of_two_factor (x y : ℕ) (h : ∃ k, x * y = 2^k) : ∃ k, x = 2^k := by
  obtain ⟨ k, hk ⟩ := h; have := hk ▸ dvd_mul_right x y; ( have := hk ▸ dvd_mul_left y x; ( erw [ Nat.dvd_prime_pow ( by decide ) ] at *; aesop; ) )

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

theorem target_ge_j (p : ℕ) (hp : p > 1) (j : ℕ) (s : ℕ) (hs : s ≥ 1) (hs_in_A : s ∈ A p) :
  target_index p j s ≥ j := by
    -- Since `a_seq p j ∈ A p` and `s * a_seq p j ∈ A p` (by closure of A), we have `s * a_seq p j ≥ a_seq p j`.
    have h_ge : s * a_seq p j ≥ a_seq p j := by
      nlinarith [ a_seq_pos p hp j ];
    have h_monotone : ∀ x y : ℕ, x ∈ A p → y ∈ A p → x ≤ y → index_in_A p x ≤ index_in_A p y := by
      exact fun x y a a_1 a_2 ↦ index_in_A_mono p hp x y a a_1 a_2;
    exact h_monotone _ _ ( a_seq_mem p hp j ) ( A_mul_closed p s ( a_seq p j ) hs_in_A ( a_seq_mem p hp j ) ) h_ge |> le_trans ( by erw [ index_a_seq_eq_self p hp j ] )

theorem j_lt_i_of_target (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ) (s : ℕ) (hs : s ∈ used_s p n hp j) (ht : target_index p j s = i) :
  j < i := by
    rw [ ← ht ];
    apply lt_of_le_of_ne;
    · apply target_ge_j;
      · exact hp.2;
      · -- Since $s$ is in $used_s$, which is either $decompose_S$ or $decompose_even_pow2$, and both of these decompositions consist of elements in $A_p$, which are positive, $s$ must be positive.
        have h_s_pos : s ∈ A p := by
          exact s_in_used_s_mem_A p n hp j s hs;
        exact Nat.pos_of_ne_zero ( by rintro rfl; exact absurd h_s_pos ( by rintro ⟨ x, y, hxy ⟩ ; linarith [ show 2 ^ x * p ^ y > 0 by exact mul_pos ( pow_pos ( by decide ) _ ) ( pow_pos ( by linarith ) _ ) ] ) );
      · exact s_in_used_s_mem_A p n hp j s hs;
    · by_contra h_eq;
      -- If $j = \text{target\_index } j s$, then $a_seq p j = s * a_seq p j$, which implies $s = 1$.
      have h_s_one : s = 1 := by
        have h_s_one : s * a_seq p j = a_seq p j := by
          rw [ ← target_index_spec p hp.2 j s ];
          · rw [ ← h_eq ];
          · exact s_in_used_s_mem_A p n hp j s hs;
        nlinarith [ a_seq_pos p hp.2 j ];
      unfold used_s at hs; simp +decide [ h_s_one ] at hs;
      split_ifs at hs <;> norm_num [ decompose_even_pow2 ] at hs;
      · unfold decompose_S at hs; simp +decide [ h_s_one ] at hs;
        split_ifs at hs <;> norm_num at hs;
        have := Exists.choose_spec ( M_0_properties p hp |>.2.2 ( c_step p n hp j j ) ( by linarith ) ( by linarith ) );
        have := this.1 hs; simp +decide [ h_s_one ] at this;
        exact absurd ( S_properties p hp |>.1 1 this ) ( by norm_num [ one_mem_A ] );
      · rcases Nat.even_or_odd' ( c_step p n hp j j ) with ⟨ k, hk | hk ⟩ <;> simp +decide [ hk ] at *

theorem lemma_scalar_bound (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (k : ℕ) (hk : 1 ≤ k ∧ k < K p) (hj : in_interval p n hp k j)
  (hc_upper : k ≥ 2 → c_step p n hp j j ≤ M p k) :
  ∀ s ∈ used_s p n hp j, s ≤ u p (k + 1) := by
    rcases k with ( _ | _ | k ) <;> simp_all +decide [ in_interval ];
    · simp [used_s];
      split_ifs <;> simp_all +decide [ decompose_S ];
      · split_ifs <;> simp_all +decide [ Finset.subset_iff ];
        have := Exists.choose_spec ( M_0_properties p hp |>.2.2 ( c_step p n hp j j ) ( by linarith ) ( by linarith ) );
        exact fun s hs => s_in_S_le_u2 p hp s ( this.1 hs );
      · contrapose! hj;
        rw [ v_1_eq_m_sub_1 ];
        rw [ tsub_lt_iff_left ];
        · grind;
        · unfold m;
          unfold m_index;
          simp +zetaDelta at *;
          exact Nat.zero_le _;
    · apply s_le_u_with_bound_ge_2 p n hp j (k + 2) ⟨by linarith, by linarith⟩ hj hc_upper

theorem lemma_target_bound (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (k : ℕ) (hk : 1 ≤ k ∧ k < K p) (hj : in_interval p n hp k j)
  (hc_upper : k ≥ 2 → c_step p n hp j j ≤ M p k) :
  ∀ s ∈ used_s p n hp j, target_index p j s ≤ v p n hp (k + 1) := by
    -- By definition of `used_s`, we know that `s * a_seq p j` is bounded by `P p (k + 1) * a_seq p (m p n hp - 1)`.
    have h_bound : ∀ s ∈ used_s p n hp j, s * a_seq p j ≤ P p (k + 1) * a_seq p (m p n hp - 1) := by
      have h_bound : ∀ s ∈ used_s p n hp j, s * a_seq p j ≤ u p (k + 1) * P p k * a_seq p (m p n hp - 1) := by
        -- By definition of `used_s`, we know that `s` is bounded by `u p (k + 1)` and `a_seq p j` is bounded by `P p k * a_seq p (m p n hp - 1)`.
        have h_bound : ∀ s ∈ used_s p n hp j, s ≤ u p (k + 1) ∧ a_seq p j ≤ P p k * a_seq p (m p n hp - 1) := by
          have h_bound : ∀ s ∈ used_s p n hp j, s ≤ u p (k + 1) := by
            exact fun s a ↦ lemma_scalar_bound p n hp j k hk hj hc_upper s a;
          have h_bound : a_seq p j ≤ P p k * a_seq p (m p n hp - 1) := by
            have h_bound : a_seq p j ≤ a_seq p (v p n hp k) := by
              -- Since $j$ is in the interval $[v p n hp (k-1), v p n hp k]$, we have $j \leq v p n hp k$.
              have h_j_le_v : j ≤ v p n hp k := by
                unfold in_interval at hj; aesop;
              exact monotone_nat_of_le_succ ( fun n => by exact le_of_lt ( a_seq_strict_mono p hp.2 n.lt_succ_self ) ) h_j_le_v;
            exact h_bound.trans ( v_spec p n hp k ▸ le_rfl );
          aesop;
        exact fun s hs => by nlinarith only [ h_bound s hs, Nat.zero_le ( a_seq p j ) ] ;
      convert h_bound using 3 ; ring_nf;
      unfold P; ring_nf;
      rw [ show 2 + k = 1 + k + 1 by ring, List.range_succ ] ; norm_num ; ring;
    -- By definition of `target_index`, we know that `target_index p j s = index_in_A p (s * a_seq p j)`.
    intros s hs
    rw [target_index];
    apply_rules [ index_in_A_mono ];
    · linarith;
    · exact A_mul_closed p _ _ ( s_in_used_s_mem_A p n hp j s hs ) ( a_seq_mem p hp.2 j );
    · exact A_mul_closed p _ _ ( P_mem_A p hp ( k + 1 ) ) ( a_seq_mem p hp.2 _ )

/-
Definition of the final step index and the final coefficients.
-/
noncomputable def final_step_index (p n : ℕ) (hp : Odd p ∧ p > 1) : ℕ := v p n hp (K p) + 1

noncomputable def c_final (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) : ℕ :=
  c_step p n hp (final_step_index p n hp) i

/-
The coefficient at index i does not change during step j if i < j.
-/
theorem c_step_stable (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ) (h : i < j) :
  c_step p n hp (j + 1) i = c_step p n hp j i := by
    -- By definition of $c_step$, we know that $c_step p n hp (j + 1) i = step_transform p n hp (c_step p n hp j) j i$.
    rw [c_step_succ];
    unfold step_transform;
    split_ifs <;> norm_num [ h.ne ];
    · intro x hx;
      have := j_lt_i_of_target p n hp j ( target_index p j x ) x ( by
        unfold used_s; aesop; ) ( by
        rfl );
      linarith;
    · -- Since $x \in \text{decompose\_even\_pow2}(c\_step p n hp j j)$, we have $x \geq 1$.
      intro x hx
      have hx_ge_one : 1 ≤ x := by
        have hx_ge_one : ∀ x ∈ decompose_even_pow2 (c_step p n hp j j), 1 ≤ x := by
          intros x hx
          have hx_ge_one : ∃ k ≥ 1, x = 2^k := by
            exact decompose_even_pow2_spec ( c_step p n hp j j ) ( by linarith ) |>.2 x hx;
          exact hx_ge_one.choose_spec.2.symm ▸ Nat.one_le_pow _ _ ( by decide );
        exact hx_ge_one x hx;
      have h_target_ge_j : j ≤ target_index p j x := by
        apply_rules [ target_ge_j ];
        · linarith;
        · -- Since $x$ is a power of 2, it is in $A p$ by definition.
          have hx_pow2 : ∃ k, x = 2^k := by
            unfold decompose_even_pow2 at hx; aesop;
          exact hx_pow2.elim fun k hk => hk.symm ▸ pow2_mem_A p k;
      grind

/-
The final coefficient at index i is equal to the coefficient at index i after step i.
-/
theorem c_final_eq_c_step (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (hi : i < final_step_index p n hp) :
  c_final p n hp i = c_step p n hp (i + 1) i := by
    have h_ind : ∀ k, i < k → k ≤ final_step_index p n hp → c_step p n hp k i = c_step p n hp (i + 1) i := by
      intro k hk₁ hk₂
      induction' hk₁ with k hk ih;
      · rfl;
      · rw [ ← ih ( Nat.le_of_succ_le hk₂ ), c_step_stable ] ; aesop;
    exact h_ind _ hi le_rfl

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
If the initial coefficient at index i (>= m) is 1, then a_i is a power of 2.
-/
theorem c_init_eq_one_imp_pow2 (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (hi : i ≥ m p n hp) (h : c_init p n hp i = 1) :
  ∃ k, a_seq p i = 2^k := by
    unfold c_init at h;
    unfold coeff_from_binary at h;
    grind

/-
The remainder R is less than M_0 * a_m.
-/
theorem R_lt_M0_am (p n : ℕ) (hp : Odd p ∧ p > 1) :
  R p n hp < M_0 p * a_seq p (m p n hp) := by
    unfold R;
    rw [ tsub_lt_iff_left ];
    · -- Since `M_0` is positive, we can divide both sides of the inequality by `M_0`.
      have h_div : n / M_0 p < ∑ x ∈ Finset.range (m p n hp), a_seq p x := by
        apply Nat.find_spec (partial_sum_unbounded p hp.2 (n / M_0 p));
      have h_div : n / M_0 p < ∑ x ∈ Finset.range (m p n hp - 1), a_seq p x + a_seq p (m p n hp) := by
        rcases k : m p n hp with ( _ | k ) <;> simp_all +decide [ Finset.sum_range_succ ];
        exact h_div.trans_le ( add_le_add_left ( a_seq_strict_mono p hp.2 |> StrictMono.monotone <| Nat.le_succ _ ) _ );
      rw [ Nat.div_lt_iff_lt_mul ] at h_div;
      · convert h_div using 1 ; ring!;
      · exact Nat.pos_of_ne_zero ( by have := M_0_properties p hp; aesop );
    · exact R_nonneg p n hp

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
The remainder R is strictly less than P_2 * a_m.
-/
theorem R_lt_P2_am (p n : ℕ) (hp : Odd p ∧ p > 1) :
  R p n hp < P p 2 * a_seq p (m p n hp) := by
    -- By definition of $P$, we know that $P_2 = u_1 * u_2 = 1 * u_2 = u_2$.
    have hP2 : P p 2 = u p 2 := by
      unfold P;
      unfold u; simp +decide [ List.range_succ ] ;
    have hR_lt_M0_am : R p n hp < M_0 p * a_seq p (m p n hp) := by
      exact R_lt_M0_am p n hp;
    have hM0_le_u2 : M_0 p ≤ u p 2 := by
      exact le_trans ( M_0_properties p hp |>.1 ) ( p_le_u2 p hp );
    exact hR_lt_M0_am.trans_le ( Nat.mul_le_mul_right _ hM0_le_u2 |> le_trans <| by rw [ hP2 ] )

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
If i is in interval k >= 3, then a_i > P_2 * a_{m-1}.
-/
theorem a_i_gt_P2_am_sub_1 (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (k : ℕ) (hk : k ≥ 3) (hi : in_interval p n hp k i) :
  a_seq p i > P p 2 * a_seq p (m p n hp - 1) := by
    rcases k with ( _ | _ | _ | k ) <;> simp_all +decide [ in_interval ];
    -- Since $i > v_{k+2}$, we have $a_i > a_{v_{k+2}}$.
    have h_ai_gt_avk2 : a_seq p i > a_seq p (v p n hp (k + 2)) := by
      exact a_seq_strict_mono p hp.2 hi.1;
    refine' lt_of_le_of_lt _ h_ai_gt_avk2;
    rw [ v_spec ];
    exact Nat.mul_le_mul_right _ ( P_mono p ( by linarith ) )

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
For intervals k >= 3, the initial coefficient is 0.
-/
theorem c_init_eq_zero_of_ge_3 (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (i : ℕ) (k : ℕ) (hk : k ≥ 3) (hk_le : k ≤ K p) (hi : in_interval p n hp k i) :
  c_init p n hp i = 0 := by
    by_contra h_contra;
    -- Since $i > v_2$, we have $i \geq m$.
    have h_i_ge_m : i ≥ m p n hp := by
      have h_i_ge_m : v p n hp 2 ≥ m p n hp := by
        have h_v2_ge_m : v p n hp 2 ≥ v p n hp 1 + 1 := by
          apply v_strict_mono;
          exact ⟨ le_rfl, K_ge_2 p ⟩;
        -- Since $v_1 = m - 1$, we have $v_2 \geq (m - 1) + 1 = m$.
        have h_v2_ge_m : v p n hp 2 ≥ (m p n hp - 1) + 1 := by
          exact h_v2_ge_m.trans' ( by rw [ v_1_eq_m_sub_1 ] );
        rwa [ Nat.sub_add_cancel ( m_pos p n hp hn ) ] at h_v2_ge_m;
      -- Since $i$ is in the interval $k$ which is at least 3, we have $i > v p n hp (k-1)$.
      have h_i_gt_v : i > v p n hp (k - 1) := by
        unfold in_interval at hi; aesop;
      exact le_trans h_i_ge_m ( le_trans ( v_ge_v2_of_ge_3 p n hp k hk hk_le ) h_i_gt_v.le );
    -- Since $i \geq m$, we have $c_init p n hp i = coeff_from_binary p (R p n hp) i$.
    have h_c_init_eq_coeff : c_init p n hp i = coeff_from_binary p (R p n hp) i := by
      unfold c_init;
      grind;
    -- Since $i > v_2$, we have $a_i > P_2 * a_{m-1}$.
    have h_ai_gt_P2_am_sub_1 : a_seq p i > P p 2 * a_seq p (m p n hp - 1) := by
      apply a_i_gt_P2_am_sub_1 p n hp i k hk hi;
    exact h_contra <| h_c_init_eq_coeff.trans <| coeff_from_binary_eq_zero_of_gt p hp.2 _ _ <| by linarith [ R_lt_P2_am_sub_1 p n hp hn ] ;

/-
For intervals k >= 3, the initial coefficient is 0.
-/
theorem c_init_eq_zero_of_ge_3_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (i : ℕ) (k : ℕ) (hk : k ≥ 3) (hk_le : k ≤ K p) (hi : in_interval p n hp k i) :
  c_init p n hp i = 0 := by
    exact c_init_eq_zero_of_ge_3 p n hp hn i k hk hk_le hi

/-
Elements from the first interval cannot contribute to intervals k >= 3.
-/
theorem j_lt_m_cannot_contribute_to_ge_3 (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ) (k : ℕ) (hk : k ≥ 3) (hi : in_interval p n hp k i) (hj : j < m p n hp) :
  ∀ s ∈ used_s p n hp j, target_index p j s ≠ i := by
    intros s hs;
    -- Since $s \in used_s j$, we know $s \le u_2$.
    have hs_le_u2 : s ≤ u p 2 := by
      have h_s_le_u2 : ∀ s ∈ used_s p n hp j, s ≤ u p 2 := by
        apply lemma_scalar_bound;
        · exact ⟨ le_rfl, K_ge_2 p ⟩;
        · unfold in_interval;
          rw [ v_1_eq_m_sub_1 ];
          exact Nat.le_sub_one_of_lt hj;
        · norm_num;
      exact h_s_le_u2 s hs;
    -- Since $i \in I_k$ ($k \ge 3$), we know $a_i > P_2 a_{m-1}$.
    have h_ai_gt_P2_am_sub_1 : a_seq p i > P p 2 * a_seq p (m p n hp - 1) := by
      apply a_i_gt_P2_am_sub_1 p n hp i k hk hi;
    -- Since $s \le u_2$ and $a_i > P_2 a_{m-1}$, we have $s * a_j < a_i$.
    have h_sj_lt_ai : s * a_seq p j < a_seq p i := by
      refine' lt_of_le_of_lt _ h_ai_gt_P2_am_sub_1;
      gcongr;
      · convert hs_le_u2 using 1;
        unfold P; norm_num;
        norm_num [ List.range_succ ];
        unfold u; aesop;
      · exact monotone_nat_of_le_succ ( fun n => a_seq_strict_mono p hp.2 |> StrictMono.monotone |> fun h => h n.le_succ ) ( Nat.le_pred_of_lt hj );
    contrapose! h_sj_lt_ai;
    rw [ ← h_sj_lt_ai, target_index_spec p hp.2 j s ( s_in_used_s_mem_A p n hp j s hs ) ]

/-
Definitions for Lemma 3: IsTarget, CoeffBound, and UpdateConditionUpTo. Note that UpdateConditionUpTo uses k >= 3 as discussed.
-/
def IsTarget (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ) : Prop :=
  ∃ s ∈ used_s p n hp j, target_index p j s = i

def CoeffBound (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ K p →
    ∀ i, in_interval p n hp k i →
      c_step p n hp j i ≤ M p k

def UpdateConditionUpTo (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Prop :=
  ∀ i' < j, ∀ i, IsTarget p n hp i' i →
    ∀ k, 1 ≤ k → k ≤ K p →
      in_interval p n hp k i →
      (k ≥ 3 → i' > v p n hp (k - 2))

/-
If j >= m and c_j <= 1, then used_s is empty.
-/
theorem used_s_empty_of_le_one (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (hj : j ≥ m p n hp) (hc : c_step p n hp j j ≤ 1) :
  used_s p n hp j = ∅ := by
    unfold used_s;
    grind

/-
If j is in the last interval K, and coefficients satisfy the bound, then used_s is empty.
-/
theorem used_s_empty_of_in_interval_K (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (h_coeff : CoeffBound p n hp j) (hj : in_interval p n hp (K p) j) :
  used_s p n hp j = ∅ := by
    apply used_s_empty_of_le_one;
    · exact j_ge_m_of_in_interval_ge_2 p n hp j ( K p ) ( by linarith [ K_ge_2 p ] ) hj;
    · exact h_coeff ( K p ) ( by linarith [ K_ge_2 p ] ) le_rfl j hj |> le_trans <| M_K_le_one p hp

/-
If j targets i and is in some interval k <= K, then k < K.
-/
theorem target_implies_interval_lt_K (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ)
  (h_target : IsTarget p n hp j i)
  (h_coeff : CoeffBound p n hp j)
  (h_in_interval : ∃ k, 1 ≤ k ∧ k ≤ K p ∧ in_interval p n hp k j) :
  ∃ k_j, 1 ≤ k_j ∧ k_j < K p ∧ in_interval p n hp k_j j := by
    -- By definition of K p, if k = K p, then used_s p n hp j would be empty, contradicting h_target.
    obtain ⟨k, hk₁, hk₂, hk₃⟩ := h_in_interval
    by_cases hk : k = K p;
    · have := used_s_empty_of_in_interval_K p n hp j h_coeff ( by aesop ) ; unfold IsTarget at h_target; aesop;
    · exact ⟨ k, hk₁, lt_of_le_of_ne hk₂ hk, hk₃ ⟩

/-
If i < v_1, then c_init i >= M_0.
-/
theorem c_init_ge_M0 (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (hi : i < v p n hp 1) :
  c_init p n hp i ≥ M_0 p := by
    unfold c_init;
    unfold v at hi;
    rw [ show P p 1 = 1 from ?_ ] at hi;
    · rw [ one_mul, index_a_seq_eq_self ] at hi ; aesop;
      linarith;
    · exact rfl

/-
Corrected definitions of step_transform and c_step, splitting at m-1 instead of m.
-/
noncomputable def step_transform_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) (c : ℕ → ℕ) (k : ℕ) : ℕ → ℕ :=
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

noncomputable def c_step_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) : ℕ → ℕ → ℕ
| 0 => c_init p n hp
| k + 1 => step_transform_v2 p n hp (c_step_v2 p n hp k) k

/-
If j < v_1, then c_step j j >= M_0.
-/
theorem c_step_ge_M0_of_lt_v1 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (hj : j < v p n hp 1) :
  c_step p n hp j j ≥ M_0 p := by
    -- By definition of $c_step$, we have $c_step j j = c_init j + (contributing_s j).card$.
    have h_c_step : c_step p n hp j j = c_init p n hp j + Finset.card (contributing_s p n hp j) := by
      apply c_step_eq_init_plus_card;
    linarith [ c_init_ge_M0 p n hp j hj ]

/-
If j is in the first interval, then used_s j is a subset of S.
-/
theorem used_s_subset_S_of_interval_1 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (hj : in_interval p n hp 1 j) :
  used_s p n hp j ⊆ S p := by
    -- Since j is in the first interval, we have j < m p n hp.
    have hj_lt_m : j < m p n hp := by
      -- Since $v_1 = m - 1$, if $j \leq m - 1$, then $j < m$.
      have h_v1_eq_m_sub_1 : v p n hp 1 = m p n hp - 1 := by
        -- By definition of $v$, we know that $v p n hp 1 = m p n hp - 1$.
        apply v_1_eq_m_sub_1;
      -- Since $j \leq v_1$ and $v_1 = m - 1$, we have $j \leq m - 1$.
      have h_j_le_m_sub_1 : j ≤ m p n hp - 1 := by
        unfold in_interval at hj; aesop;
      -- Since $m$ is positive, we have $m - 1 < m$.
      have h_m_pos : 0 < m p n hp := by
        by_cases hn : n > 0;
        · -- Since $n > 0$, we have $m p n hp > 0$ by definition.
          apply m_pos p n hp hn;
        · simp_all +decide [ m ];
          unfold m_index; aesop;
      exact lt_of_le_of_lt h_j_le_m_sub_1 ( Nat.pred_lt h_m_pos.ne' );
    -- Since j is in the first interval, we have j < m p n hp. Therefore, used_s j is defined as decompose_S (c_step j j).
    have h_used_s_def : used_s p n hp j = decompose_S p hp (c_step p n hp j j) := by
      unfold used_s; aesop;
    rw [h_used_s_def];
    unfold decompose_S;
    split_ifs <;> [ exact Exists.choose_spec ( M_0_properties p hp |>.2.2 _ _ _ ) |>.1; exact Finset.empty_subset _ ];
    exact Exists.choose_spec ( M_0_properties p hp |>.2.2 _ ( by linarith ) ( by linarith ) ) |>.1

/-
If i <= v_1, then contributing_s i is a subset of S.
-/
theorem contributing_s_subset_S_of_le_v1 (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (hi : i ≤ v p n hp 1) :
  contributing_s p n hp i ⊆ S p := by
    -- Let `s ∈ contributing_s i`.
    intro s hs
    obtain ⟨j, hj₁, hj₂⟩ := Finset.mem_biUnion.mp hs;
    have hj_le_v1 : j ≤ v p n hp 1 := by
      linarith [ Finset.mem_range.mp hj₁ ];
    have hj_interval_1 : in_interval p n hp 1 j := by
      unfold in_interval; aesop;
    have := used_s_subset_S_of_interval_1 p n hp j hj_interval_1; aesop;

/-
If j targets i, and j is in interval k_j and i is in interval k, then k_j >= k - 1.
-/
theorem interval_bound_lemma (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ)
  (h_target : IsTarget p n hp j i)
  (h_coeff : CoeffBound p n hp j)
  (k : ℕ) (hk : 1 ≤ k ∧ k ≤ K p) (hi : in_interval p n hp k i)
  (k_j : ℕ) (hk_j : 1 ≤ k_j ∧ k_j < K p) (hj : in_interval p n hp k_j j) :
  k_j ≥ k - 1 := by
    -- By definition of $target_index$, we know that $i \leq v (k_j + 1)$.
    have h_i_le_v_succ : i ≤ v p n hp (k_j + 1) := by
      obtain ⟨ s, hs₁, hs₂ ⟩ := h_target;
      have := lemma_target_bound p n hp j k_j hk_j hj (fun hk => by
        exact h_coeff k_j ( by linarith ) ( by linarith ) j hj) s hs₁; aesop;
    -- By definition of $in_interval$, we know that $v (k-1) < i$ (if $k > 1$).
    by_cases hk_gt_1 : k > 1;
    · -- Since $v$ is strictly increasing, we have $v (k - 1) < v (k_j + 1)$.
      have h_v_lt_v_succ : v p n hp (k - 1) < v p n hp (k_j + 1) := by
        have h_v_lt_v_succ : v p n hp (k - 1) < i := by
          unfold in_interval at hi; aesop;
        linarith;
      have h_v_lt_v_succ : ∀ k1 k2, 1 ≤ k1 → k1 < k2 → k2 ≤ K p → v p n hp k1 < v p n hp k2 := by
        intros k1 k2 hk1 hk2 hk2_le_Kp
        induction' hk2 with k2 hk2 ih;
        · exact v_strict_mono p n hp k1 ⟨ hk1, by linarith ⟩;
        · exact lt_trans ( ih ( Nat.le_of_succ_le hk2_le_Kp ) ) ( v_strict_mono p n hp k2 ⟨ by linarith [ Nat.succ_le_iff.mp hk2 ], by linarith ⟩ );
      contrapose! h_v_lt_v_succ;
      use k_j + 1, k - 1;
      grind;
    · omega

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
If j targets i and j >= m, then c_step j j > 1.
-/
theorem c_step_gt_one_of_target (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ) (h : IsTarget p n hp j i) (hj : j ≥ m p n hp) :
  c_step p n hp j j > 1 := by
    exact not_le.mp fun contra => by obtain ⟨ s, hs₁, hs₂ ⟩ := h; exact absurd hs₁ ( by rw [ used_s_empty_of_le_one p n hp j hj contra ] ; aesop ) ;

/-
If j > v K and j targets i, then there exists j' < j targeting j.
-/
theorem exists_source_of_target_if_gt_vK (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ)
  (hj : j > v p n hp (K p))
  (h_target : IsTarget p n hp j i) :
  ∃ j', j' < j ∧ IsTarget p n hp j' j := by
    -- By definition of `contributing_s`, there exists some `j'` such that `s ∈ used_s p n hp j'` and `target_index p j' s = j`.
    obtain ⟨s, hs⟩ : ∃ s ∈ contributing_s p n hp j, True := by
      have h_card_gt_one : (contributing_s p n hp j).card > 1 := by
        have h_card : 1 < c_step p n hp j j := by
          apply c_step_gt_one_of_target p n hp j i h_target (by
          have h_j_ge_m : j > v p n hp (K p) → j ≥ m p n hp := by
            have h_j_ge_m : v p n hp (K p) ≥ v p n hp 1 := by
              have h_v_mono : ∀ k l, 1 ≤ k → k ≤ l → l ≤ K p → v p n hp k ≤ v p n hp l := by
                intros k l hk hkl hl
                induction' hkl with l hl ih;
                · rfl;
                · exact le_trans ( ih ( Nat.le_of_succ_le hl ) ) ( le_of_lt ( v_strict_mono p n hp _ ⟨ by linarith [ Nat.succ_le_succ ‹k.le l› ], by linarith ⟩ ) );
              exact h_v_mono 1 ( K p ) ( by norm_num ) ( by linarith [ K_ge_2 p ] ) ( by linarith [ K_ge_2 p ] );
            rw [v_1_eq_m_sub_1] at h_j_ge_m; omega;
          exact h_j_ge_m hj);
        have h_card_eq : c_step p n hp j j = c_init p n hp j + (contributing_s p n hp j).card := by
          apply c_step_eq_init_plus_card;
        linarith [ show c_init p n hp j = 0 from c_init_eq_zero_of_gt_vK p n hp j hj ];
      exact Exists.elim ( Finset.card_pos.mp ( pos_of_gt h_card_gt_one ) ) fun x hx => ⟨ x, hx, trivial ⟩;
    obtain ⟨j', hj', hs'⟩ : ∃ j', j' < j ∧ s ∈ used_s p n hp j' ∧ target_index p j' s = j := by
      unfold contributing_s at hs; aesop;
    exact ⟨ j', hj', s, hs'.1, hs'.2 ⟩

/-
If j' targets j and j' is in a valid interval (with bounded coefficients), then j is bounded by v(K).
-/
theorem target_bound_from_source (p n : ℕ) (hp : Odd p ∧ p > 1) (j' j : ℕ)
  (h_target : IsTarget p n hp j' j)
  (h_coeff : CoeffBound p n hp j')
  (h_valid : ∃ k', 1 ≤ k' ∧ k' ≤ K p ∧ in_interval p n hp k' j') :
  j ≤ v p n hp (K p) := by
    -- By `target_implies_interval_lt_K`, there exists `k'` such that `1 ≤ k' < K p` and `in_interval k' j'`.
    obtain ⟨k', hk'_le, hk'_lt⟩ : ∃ k', 1 ≤ k' ∧ k' < K p ∧ in_interval p n hp k' j' := by
      apply target_implies_interval_lt_K;
      exacts [ h_target, h_coeff, h_valid ];
    have h_j_le_v_k'_plus_1 : j ≤ v p n hp (k' + 1) := by
      have h_j_le_v_k'_plus_1 : ∀ s ∈ used_s p n hp j', target_index p j' s ≤ v p n hp (k' + 1) := by
        apply lemma_target_bound p n hp j' k' ⟨hk'_le, hk'_lt.left⟩ hk'_lt.right
        generalize_proofs at *; (
        exact fun hk'_ge_2 => h_coeff k' hk'_le ( by linarith ) j' hk'_lt.2 |> le_trans <| by linarith;);
      cases h_target ; aesop;
    -- Since `k' + 1 ≤ K p`, and `v` is monotone, `v (k' + 1) ≤ v (K p)`.
    have h_v_k'_plus_1_le_v_Kp : v p n hp (k' + 1) ≤ v p n hp (K p) := by
      have h_v_mono : ∀ k₁ k₂, 1 ≤ k₁ → k₁ ≤ k₂ → k₂ ≤ K p → v p n hp k₁ ≤ v p n hp k₂ := by
        intros k₁ k₂ hk₁ hk₂ hk₂_le_Kp
        induction' hk₂ with k₂ hk₂ ih;
        · rfl;
        · exact le_trans ( ih ( Nat.le_of_succ_le hk₂_le_Kp ) ) ( le_of_lt ( v_strict_mono p n hp k₂ ⟨ Nat.one_le_iff_ne_zero.mpr ( by aesop ), Nat.lt_of_succ_le hk₂_le_Kp ⟩ ) );
      grind;
    linarith

/-
If j targets i, and previous coefficients satisfy the bound, then j is in a valid interval. Proof by strong induction.
-/
theorem target_implies_in_valid_interval_strong (p n : ℕ) (hp : Odd p ∧ p > 1) :
  ∀ j, (∀ j' < j, CoeffBound p n hp j') →
  ∀ i, IsTarget p n hp j i →
  ∃ k, 1 ≤ k ∧ k ≤ K p ∧ in_interval p n hp k j := by
    intro j hj;
    -- We prove this by strong induction on `j`.
    induction' j using Nat.strong_induction_on with j ih generalizing hp;
    -- Suppose `j` is not in any valid interval.
    intro i hi
    by_contra h_contra;
    -- Then `j > v (K p)`.
    have h_j_gt_vK : j > v p n hp (K p) := by
      contrapose! h_contra;
      -- Since $j \leq v p n hp (K p)$, we can find $k$ such that $1 \leq k \leq K p$ and $j \in [v p n hp (k-1), v p n hp k]$.
      obtain ⟨k, hk⟩ : ∃ k, 1 ≤ k ∧ k ≤ K p ∧ j ≤ v p n hp k ∧ (k = 1 ∨ v p n hp (k - 1) < j) := by
        have h_exists_k : ∃ k, 1 ≤ k ∧ k ≤ K p ∧ j ≤ v p n hp k := by
          exact ⟨ K p, Nat.one_le_iff_ne_zero.mpr ( by linarith [ K_ge_2 p ] ), le_rfl, h_contra ⟩;
        obtain ⟨k, hk⟩ : ∃ k, 1 ≤ k ∧ k ≤ K p ∧ j ≤ v p n hp k ∧ ∀ k', 1 ≤ k' → k' < k → ¬(j ≤ v p n hp k') := by
          exact ⟨ Nat.find h_exists_k, Nat.find_spec h_exists_k |>.1, Nat.find_spec h_exists_k |>.2.1, Nat.find_spec h_exists_k |>.2.2, fun k' hk'₁ hk'₂ hk'₃ => Nat.find_min h_exists_k hk'₂ ⟨ hk'₁, by linarith [ Nat.find_spec h_exists_k |>.2.1 ], hk'₃ ⟩ ⟩;
        exact ⟨ k, hk.1, hk.2.1, hk.2.2.1, Classical.or_iff_not_imp_left.2 fun hk' => lt_of_not_ge fun hk'' => hk.2.2.2 ( k - 1 ) ( Nat.le_sub_one_of_lt ( lt_of_le_of_ne hk.1 ( Ne.symm hk' ) ) ) ( Nat.sub_lt hk.1 zero_lt_one ) hk'' ⟩;
      use k;
      unfold in_interval; aesop;
    -- By `exists_source_of_target_if_gt_vK` (using `j > v (K p)` and `IsTarget j i`), there exists `j' < j` such that `IsTarget j' j`.
    obtain ⟨j', hj'_lt_j, hj'_target⟩ : ∃ j', j' < j ∧ IsTarget p n hp j' j := by
      apply exists_source_of_target_if_gt_vK p n hp j i h_j_gt_vK hi;
    -- By the inductive hypothesis applied to `j'` (which is `< j`), and using `IsTarget j' j`, we conclude that `j'` is in a valid interval.
    obtain ⟨k', hk'_valid, hk'_interval⟩ : ∃ k', 1 ≤ k' ∧ k' ≤ K p ∧ in_interval p n hp k' j' := by
      exact ih j' hj'_lt_j hp ( fun j'' hj'' => hj j'' ( lt_trans hj'' hj'_lt_j ) ) _ hj'_target;
    -- By `target_bound_from_source` (using `IsTarget j' j`, `CoeffBound j'`, and `j'` in valid interval), we have `j ≤ v (K p)`.
    have h_j_le_vK : j ≤ v p n hp (K p) := by
      apply target_bound_from_source p n hp j' j hj'_target (hj j' hj'_lt_j) ⟨k', hk'_valid, hk'_interval.left, hk'_interval.right⟩;
    linarith

/-
M is decreasing (or zero).
-/
theorem M_decreasing (p : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : k ≥ 1) :
  M p (k + 1) < M p k ∨ (M p k = 0 ∧ M p (k + 1) = 0) := by
    by_cases h : M p k = 0;
    · rcases k with ( _ | _ | k ) <;> simp_all +arith +decide [ M ];
    · refine' Or.inl ( _ );
      -- Since $M p k$ is a positive integer, we have $Nat.log2 (M p k) < M p k$.
      have h_log2_lt : ∀ x : ℕ, 0 < x → Nat.log2 x < x := by
        intro x hx_pos;
        rw [ Nat.log2_lt ] <;> try linarith;
        exact Nat.lt_two_pow_self;
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ M ];
      · exact Nat.pos_of_ne_zero fun con => by have := M_0_properties p hp; aesop;
      · exact h_log2_lt _ ( Nat.pos_of_ne_zero h )

/-
Inductive step for proving that targeting indices are in valid intervals.
-/
def ValidInterval (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Prop :=
  ∃ k, 1 ≤ k ∧ k ≤ K p ∧ in_interval p n hp k j

theorem lemma_valid_interval_step (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (h_coeff : ∀ j' < j, CoeffBound p n hp j')
  (h_ih : ∀ j' < j, (∃ i, IsTarget p n hp j' i) → ValidInterval p n hp j')
  (h_target : ∃ i, IsTarget p n hp j i) :
  ValidInterval p n hp j := by
    have := @target_implies_in_valid_interval_strong p n hp;
    exact this j h_coeff _ h_target.choose_spec

/-
If j targets i in interval k >= 3, then j > v_{k-2}. Uses inductive hypotheses.
-/
theorem update_condition_step (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (h_prev_coeff : ∀ j' < j, CoeffBound p n hp j')
  (h_prev_valid : ∀ j' < j, (∃ i, IsTarget p n hp j' i) → ValidInterval p n hp j')
  (h_coeff_j : CoeffBound p n hp j) :
  ∀ i, IsTarget p n hp j i →
    ∀ k, 1 ≤ k → k ≤ K p →
      in_interval p n hp k i →
      (k ≥ 3 → j > v p n hp (k - 2)) := by
        -- By `lemma_valid_interval_step` (using `h_prev_coeff`, `h_prev_valid`, and `exists i, IsTarget j i`), `j` is in a valid interval `k_j`.
        intros i hi k hk1 hk2 hk_interval hk_ge_3
        obtain ⟨k_j, hk_j1, hk_j2, hk_j_interval⟩ : ∃ k_j, 1 ≤ k_j ∧ k_j ≤ K p ∧ in_interval p n hp k_j j := by
          exact target_implies_in_valid_interval_strong p n hp j h_prev_coeff i hi;
        -- By `interval_bound_lemma` (using `IsTarget j i`, `CoeffBound j`, `in_interval k i`, `in_interval k_j j`), `k_j >= k - 1`.
        have hk_j_ge_k_minus_1 : k_j ≥ k - 1 := by
          apply interval_bound_lemma;
          any_goals tauto;
          refine ⟨ hk_j1, lt_of_le_of_ne hk_j2 ?_ ⟩ ; rintro rfl ; simp_all +decide [ in_interval ];
          -- Since $j$ is in the last interval, $used_s p n hp j$ must be empty.
          have h_used_s_empty : used_s p n hp j = ∅ := by
            apply used_s_empty_of_in_interval_K; assumption; assumption;
          cases hi ; aesop;
        -- Since `k_j ≥ k - 1`, we have `k_j - 1 ≥ k - 2`. Monotonicity of `v` gives `v (k_j - 1) ≥ v (k - 2)`.
        have hv_k_j_minus_1_ge_v_k_minus_2 : v p n hp (k_j - 1) ≥ v p n hp (k - 2) := by
          have hv_monotone : ∀ k1 k2, 1 ≤ k1 → k1 ≤ k2 → k2 ≤ K p → v p n hp k1 ≤ v p n hp k2 := by
            intros k1 k2 hk1 hk2 hk2_le_Kp
            induction' hk2 with k2 hk2 ih;
            · rfl;
            · exact le_trans ( ih ( Nat.le_of_succ_le hk2_le_Kp ) ) ( le_of_lt ( v_strict_mono p n hp _ ⟨ by linarith [ Nat.succ_le_succ hk2 ], by linarith ⟩ ) );
          exact hv_monotone _ _ ( Nat.sub_pos_of_lt ( by linarith ) ) ( Nat.sub_le_sub_right hk_j_ge_k_minus_1 1 ) ( Nat.sub_le_of_le_add <| by omega );
        rcases k_j with ( _ | _ | k_j ) <;> simp_all +decide [ in_interval ];
        · linarith;
        · linarith

/-
For i >= j, c_step j i is the initial coefficient plus the number of targets from steps < j.
-/
theorem c_step_eq_card_targets_of_ge (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ) (h_ge : i ≥ j) :
  c_step p n hp j i = c_init p n hp i + (Finset.filter (fun j' => IsTarget p n hp j' i) (Finset.range j)).card := by
    -- We prove this by induction on $j$.
    induction' j with j ih generalizing i;
    · aesop;
    · -- By definition of `step_transform`, we have:
      have h_step_transform : c_step p n hp (j + 1) i = if i = j then 0 else c_step p n hp j i + if ∃ s ∈ used_s p n hp j, target_index p j s = i then 1 else 0 := by
        rw [ show c_step p n hp ( j + 1 ) = step_transform p n hp ( c_step p n hp j ) j from rfl ];
        unfold step_transform;
        unfold used_s; split_ifs <;> simp_all ( config := { decide := Bool.true } ) ;
        grind;
      simp_all ( config := { decide := Bool.true } ) [ Finset.filter ];
      split_ifs <;> simp_all ( config := { decide := Bool.true } ) [ Multiset.filter_cons, add_comm ];
      · split_ifs <;> simp_all ( config := { decide := Bool.true } ) [ IsTarget ];
        linarith [ ih i ( by linarith ) ];
      · rw [ ih i ( by linarith ), if_neg ] ; aesop;
        exact fun ⟨ s, hs₁, hs₂ ⟩ => ‹∀ x ∈ used_s p n hp j, ¬target_index p j x = i› s hs₁ hs₂

/-
Invariant for Lemma 3: Coefficients satisfy bounds and update condition holds for all previous steps.
-/
def Lemma3_invariant (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Prop :=
  CoeffBound p n hp j ∧ UpdateConditionUpTo p n hp j

/-
If a_i is a power of 2, then contributing scalars must be in S \ {p}.
-/
theorem contributing_s_subset_S_diff_p_of_pow2 (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ)
  (hi : i ≤ v p n hp 1) (h_pow2 : ∃ k, a_seq p i = 2^k) :
  contributing_s p n hp i ⊆ (S p).erase p := by
    -- If s is in contributing_s i, then there exists j such that s * a_j = a_i.
    have h_exists_j : ∀ s ∈ contributing_s p n hp i, ∃ j, s * a_seq p j = a_seq p i := by
      intro s hs
      obtain ⟨j, hj⟩ : ∃ j, s ∈ used_s p n hp j ∧ target_index p j s = i := by
        unfold contributing_s at hs; aesop;
      exact ⟨ j, by rw [ ← hj.2, target_index_spec p hp.2 j s ( by
        exact s_in_used_s_mem_A p n hp j s hj.1 ) ] ⟩;
    -- Since a_i is a power of 2, s must be a power of 2 (by power_of_two_factor).
    have h_s_pow2 : ∀ s ∈ contributing_s p n hp i, ∃ k, s = 2^k := by
      intro s hs
      obtain ⟨j, hj⟩ := h_exists_j s hs
      have h_s_pow2 : ∃ k, s = 2^k := by
        have hs_pow2 : s ∣ a_seq p i := by
          exact hj ▸ dvd_mul_right _ _;
        rw [ h_pow2.choose_spec ] at hs_pow2; rw [ Nat.dvd_prime_pow ] at hs_pow2 <;> aesop ( simp_config := { decide := true } ) ;
      exact h_s_pow2;
    -- Since s is in S (by contributing_s_subset_S_of_le_v1), and p is in S, and p is odd and p > 1, p is not a power of 2. Therefore s != p.
    have h_s_ne_p : ∀ s ∈ contributing_s p n hp i, s ≠ p := by
      grind;
    exact fun x hx => Finset.mem_erase_of_ne_of_mem ( by aesop ) ( contributing_s_subset_S_of_le_v1 p n hp i hi hx )

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
c_init is at most M_0 + 1 for i <= v_1.
-/
theorem c_init_le_M0_plus_one (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (hi : i ≤ v p n hp 1) :
  c_init p n hp i ≤ M_0 p + 1 := by
    unfold c_init;
    split_ifs <;> linarith [ coeff_from_binary_le_one p ( R p n hp ) i ]

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
If a_i is a power of 2, then contributing scalars are disjoint from the non-power-of-2 element in S.
-/
theorem contributing_s_subset_S_diff_non_pow2 (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ)
  (hi : i ≤ v p n hp 1) (h_pow2 : ∃ k, a_seq p i = 2^k) :
  ∃ x ∈ S p, (∀ k, x ≠ 2^k) ∧ contributing_s p n hp i ⊆ (S p).erase x := by
    -- Use `exists_non_pow2_in_S` to get `x \in S` such that `x` is not a power of 2.
    obtain ⟨x, hxS, hxnot_pow2⟩ : ∃ x ∈ S p, ∀ k, x ≠ 2 ^ k := exists_non_pow2_in_S p hp;
    refine' ⟨ x, hxS, hxnot_pow2, _ ⟩;
    intro s hs;
    -- If `s \in contributing_s i`, then `s` must be a power of 2 (since `a_i` is a power of 2).
    have hs_pow2 : ∃ k, s = 2 ^ k := by
      obtain ⟨ j, hj₁, hj₂ ⟩ := Finset.mem_biUnion.mp hs;
      -- Since $s \in used_s p n hp j$, we have $s \in A_p$.
      have hs_A : s ∈ A p := by
        exact s_in_used_s_mem_A p n hp j s ( Finset.mem_filter.mp hj₂ |>.1 );
      -- Since $s \in A_p$, we have $s \cdot a_j = a_i$.
      have hs_eq : s * a_seq p j = a_seq p i := by
        have := target_index_spec p hp.2 j s hs_A; aesop;
      -- Since $a_i$ is a power of 2, we have $s \cdot a_j = 2^k$ for some $k$.
      obtain ⟨k, hk⟩ : ∃ k, s * a_seq p j = 2 ^ k := by
        aesop;
      have : s ∣ 2 ^ k := hk ▸ dvd_mul_right _ _; ( erw [ Nat.dvd_prime_pow ( by decide ) ] at this; aesop; );
    have := contributing_s_subset_S_of_le_v1 p n hp i hi; aesop;

/-
If a_i is a power of 2, the number of contributing scalars is at most |S| - 1.
-/
theorem card_contributing_le_S_sub_one (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ)
  (hi : i ≤ v p n hp 1) (h_pow2 : ∃ k, a_seq p i = 2^k) :
  (contributing_s p n hp i).card ≤ (S p).card - 1 := by
    obtain ⟨ x, hx₁, hx₂ ⟩ := contributing_s_subset_S_diff_non_pow2 p n hp i hi h_pow2;
    exact le_trans ( Finset.card_le_card hx₂.2 ) ( by rw [ Finset.card_erase_of_mem hx₁ ] )

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
Lemma 3 Case k=1: Coefficients in the first interval satisfy the bound M_1.
-/
theorem lemma_3_case_k1 (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ)
  (hi : in_interval p n hp 1 i) :
  c_step p n hp i i ≤ M p 1 := by
    -- We can use the fact that $c_step p n hp i i = c_init p n hp i + (contributing_s p n hp i).card$.
    have h_eq : c_step p n hp i i = c_init p n hp i + (contributing_s p n hp i).card := by
      apply c_step_eq_init_plus_card;
    -- By definition of $c_init$, we know that $c_init i i \leq M_0 + 1$.
    have h_c_init : c_init p n hp i ≤ M_0 p + 1 := by
      apply c_init_le_M0_plus_one;
      unfold in_interval at hi; aesop;
    have h_card : (contributing_s p n hp i).card ≤ if c_init p n hp i > M_0 p then (S p).card - 1 else (S p).card := by
      split_ifs with h_gt;
      · apply card_contributing_le_S_sub_one p n hp i;
        · unfold in_interval at hi; aesop;
        · apply c_init_gt_M0_imp_pow2 p n hp i (by
          unfold in_interval at hi; aesop;) h_gt;
      · exact Finset.card_le_card ( by simpa using contributing_s_subset_S_of_le_v1 p n hp i ( by unfold in_interval at hi; aesop ) );
    unfold M;
    split_ifs at h_card <;> linarith [ Nat.sub_add_cancel ( show 1 ≤ ( S p ).card from Finset.card_pos.mpr ( S_nonempty p hp ) ) ]

/-
If x is small enough, its decomposition into even powers of 2 is a subset of S.
-/
theorem decompose_even_pow2_subset_S (p : ℕ) (hp : Odd p ∧ p > 1) (x : ℕ) (hx : x > 1) (h_le : x ≤ (S p).card) :
  decompose_even_pow2 x ⊆ S p := by
    intro s hs;
    have := decompose_even_pow2_spec x hx;
    simp +zetaDelta at *;
    obtain ⟨ k, hk₁, rfl ⟩ := this.2 s hs;
    have h_two_pow_k_in_S : 2^k ≤ (S p).card := by
      exact le_trans ( Finset.single_le_sum ( fun x _ => Nat.zero_le x ) hs ) ( this.1.elim ( fun h => by linarith ) fun h => by linarith [ Nat.sub_add_cancel hx.le ] ) |> le_trans <| h_le;
    have := S_properties p hp;
    exact this.2.1 k hk₁ h_two_pow_k_in_S

/-
If j is in the second interval and its coefficient is bounded by M_2, then the scalars used are in S.
-/
theorem used_s_subset_S_of_interval_2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (hj : in_interval p n hp 2 j)
  (hc : c_step p n hp j j ≤ M p 2) :
  used_s p n hp j ⊆ S p := by
    -- Since $j$ is in the second interval, $j > v_1 = m-1$, so $j \geq m$.
    have hj_ge_m : j ≥ m p n hp := by
      unfold in_interval at hj;
      norm_num at hj;
      -- By definition of $v$, we know that $v_1 = m - 1$.
      have hv1 : v p n hp 1 = m p n hp - 1 := by
        exact v_1_eq_m_sub_1 p n hp;
      omega;
    by_cases hc : c_step p n hp j j > 1 <;> simp_all +decide [ used_s ];
    · rw [ if_neg hj_ge_m.not_gt ];
      (expose_names; exact decompose_even_pow2_subset_S p hp (c_step p n hp j j) hc hc_1);
    · grind

/-
If i is in the second interval and previous coefficients are bounded, then contributing scalars are in S.
-/
theorem contributing_s_subset_S_of_interval_2 (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ)
  (hi : in_interval p n hp 2 i)
  (h_prev : ∀ j < i, CoeffBound p n hp j) :
  contributing_s p n hp i ⊆ S p := by
    intro s hs;
    obtain ⟨j, hj₁, hj₂⟩ : ∃ j < i, s ∈ used_s p n hp j ∧ target_index p j s = i := by
      unfold contributing_s at hs; aesop;
    by_cases hj_interval : in_interval p n hp 1 j;
    · have := used_s_subset_S_of_interval_1 p n hp j hj_interval; aesop;
    · -- Since j is not in the first interval, it must be in the second interval.
      have hj_interval_2 : in_interval p n hp 2 j := by
        unfold in_interval at *;
        grind;
      have := used_s_subset_S_of_interval_2 p n hp j hj_interval_2 ( h_prev j hj₁ 2 ( by decide ) ( by linarith [ show K p ≥ 2 from K_ge_2 p ] ) j hj_interval_2 ) ; aesop;

/-
If contributing scalars are in S and a_i is a power of 2, then the number of contributing scalars is at most |S| - 1.
-/
theorem card_contributing_le_S_sub_one_of_subset_S (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ)
  (h_subset : contributing_s p n hp i ⊆ S p)
  (h_pow2 : ∃ k, a_seq p i = 2^k) :
  (contributing_s p n hp i).card ≤ (S p).card - 1 := by
    -- Since $x$ is not a power of 2, it is not in the set of contributing scalars.
    have h_not_inContributing : ∃ x ∈ S p, (∀ k, x ≠ 2^k) ∧ x ∉ contributing_s p n hp i := by
      obtain ⟨ x, hx ⟩ := exists_non_pow2_in_S p hp;
      have h_not_inContributing : ∀ s ∈ contributing_s p n hp i, ∃ k, s = 2^k := by
        intro s hs
        obtain ⟨ j, hj, hs_target ⟩ := Finset.mem_biUnion.mp hs
        have h_power_of_two : ∃ k, s * a_seq p j = 2^k := by
          have h_power_of_two : a_seq p (target_index p j s) = s * a_seq p j := by
            exact target_index_spec p hp.2 j s ( s_in_used_s_mem_A p n hp j s ( Finset.filter_subset _ _ hs_target ) );
          aesop;
        exact power_of_two_factor s (a_seq p j) h_power_of_two;
      exact ⟨ x, hx.1, hx.2, fun h => hx.2 _ <| h_not_inContributing x h |> Classical.choose_spec ⟩;
    exact Nat.le_sub_one_of_lt ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ h_subset, fun h => by obtain ⟨ x, hx₁, hx₂, hx₃ ⟩ := h_not_inContributing; aesop ⟩ ) )

/-
Lemma 3 Case k=2: Coefficients in the second interval satisfy the bound M_2.
-/
theorem lemma_3_case_k2 (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ)
  (hi : in_interval p n hp 2 i)
  (h_prev : ∀ j < i, CoeffBound p n hp j) :
  c_step p n hp i i ≤ M p 2 := by
    have h_subset : contributing_s p n hp i ⊆ S p := by
      apply contributing_s_subset_S_of_interval_2;
      · assumption;
      · assumption;
    -- By Lemma 21, `c_init i` is at most 1.
    have h_c_init : c_init p n hp i ≤ 1 := by
      apply c_init_le_one_of_gt_v1;
      unfold in_interval at hi; aesop;
    by_cases h_c_init_eq : c_init p n hp i = 1;
    · have h_a_i_pow2 : ∃ k, a_seq p i = 2^k := by
        apply c_init_eq_one_imp_pow2 p n hp i (by
        have h_i_ge_m : i > v p n hp 1 := by
          unfold in_interval at hi; aesop;
        have h_i_ge_m : i > m p n hp - 1 := by
          exact h_i_ge_m.trans_le' ( by rw [ v_1_eq_m_sub_1 ] );
        exact Nat.le_of_pred_lt h_i_ge_m) h_c_init_eq;
      have h_card_le : (contributing_s p n hp i).card ≤ (S p).card - 1 := by
        apply card_contributing_le_S_sub_one_of_subset_S p n hp i h_subset h_a_i_pow2;
      rw [ c_step_eq_init_plus_card ];
      rw [ h_c_init_eq, M ];
      linarith [ Nat.sub_add_cancel ( show 1 ≤ ( S p ).card from Finset.card_pos.mpr ( S_nonempty p hp ) ) ];
    · -- By Lemma 22, `c_step i i = c_init i + (contributing_s i).card`.
      have h_c_step : c_step p n hp i i = c_init p n hp i + (contributing_s p n hp i).card := by
        apply c_step_eq_init_plus_card;
      exact h_c_step.symm ▸ by linarith [ show ( contributing_s p n hp i |> Finset.card ) ≤ ( S p |> Finset.card ) from Finset.card_le_card h_subset, show M p 2 = ( S p |> Finset.card ) from rfl, show c_init p n hp i = 0 from Nat.eq_zero_of_not_pos fun h => h_c_init_eq <| by linarith ] ;

/-
The number of even powers of 2 less than or equal to N is floor(log2 N).
-/
theorem card_pow2_le_log2 (N : ℕ) :
  (Finset.filter (fun s => ∃ k ≥ 1, s = 2^k) (Finset.range (N + 1))).card = Nat.log2 N := by
    -- We show that the set of even powers of 2 less than or equal to $N$ is equal to $\{2^1, 2^2, \dots, 2^{\lfloor \log_2 N \rfloor}\}$.
    have h_set_eq : (Finset.filter (fun s => ∃ k ≥ 1, s = 2 ^ k) (Finset.range (N + 1))) = Finset.image (fun k => 2 ^ k) (Finset.Icc 1 (Nat.log2 N)) := by
      ext;
      norm_num +zetaDelta at *;
      constructor;
      · rintro ⟨ h₁, k, hk₁, rfl ⟩;
        refine' ⟨ k, ⟨ hk₁, _ ⟩, rfl ⟩;
        rw [ Nat.le_log2 ] <;> linarith [ Nat.pow_le_pow_right two_pos hk₁ ];
      · norm_num +zetaDelta at *;
        rintro x hx₁ hx₂ rfl;
        rw [ Nat.le_log2 ] at hx₂ <;> norm_num at *;
        · exact ⟨ Nat.lt_succ_of_le hx₂, hx₁ ⟩;
        · aesop;
    rw [ h_set_eq, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ]

/-
The update condition holds for step j, given that the invariant holds for all previous steps.
-/
theorem lemma_update_condition_step_induction (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (h_inv_prev : ∀ j' < j, Lemma3_invariant p n hp j') :
  UpdateConditionUpTo p n hp j := by
    intro i' hi' i h_target k hk hk_le hk_i;
    -- We split into cases based on whether $j$ is zero or positive.
    by_cases hj : j = 0;
    · grind;
    · -- Since $j > 0$, we can split the condition into $i' < j-1$ and $i' = j-1$.
      by_cases hi'' : i' < j - 1;
      · have := h_inv_prev ( j - 1 ) ( Nat.sub_lt ( Nat.pos_of_ne_zero hj ) zero_lt_one );
        rcases this with ⟨ h₁, h₂ ⟩ ; specialize h₂ i' hi'' i h_target k hk hk_le hk_i ; aesop;
      · -- Since $i' = j - 1$ and $j < j$, we can apply the update_condition_step lemma.
        have h_update : IsTarget p n hp (j - 1) i → (k ≥ 3 → j - 1 > v p n hp (k - 2)) := by
          intros h_target h_k_ge_3
          apply update_condition_step p n hp (j - 1) (fun j' hj' => (h_inv_prev j' (by
          exact lt_of_lt_of_le hj' ( Nat.pred_le _ ))).left) (fun j' hj' => by
            apply lemma_valid_interval_step p n hp j' (fun j'' hj'' => (h_inv_prev j'' (by
            omega)).left) (fun j'' hj'' => by
              exact fun h => target_implies_in_valid_interval_strong p n hp j'' ( fun j''' hj''' => ( h_inv_prev j''' ( by linarith [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero hj ) ] ) |>.1 ) ) _ h.choose_spec)) (by
          exact h_inv_prev _ ( Nat.sub_lt ( Nat.pos_of_ne_zero hj ) zero_lt_one ) |>.1) i h_target k hk hk_le hk_i h_k_ge_3;
        grind

/-
If j' targets i in interval k >= 3, then j' is in an interval k' >= k-1.
-/
theorem lemma_source_interval_ge (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (h_update_j : UpdateConditionUpTo p n hp j)
  (k : ℕ) (hk : k ≥ 3) (hk_le : k ≤ K p)
  (i : ℕ) (hi : in_interval p n hp k i)
  (j' : ℕ) (hj' : j' < j)
  (h_target : ∃ s ∈ used_s p n hp j', target_index p j' s = i)
  (k' : ℕ) (hk' : 1 ≤ k' ∧ k' ≤ K p) (hj'_in : in_interval p n hp k' j') :
  k' ≥ k - 1 := by
    -- From `h_update_j`, we have `j' > v p n hp (k - 2)`.
    have h_j'_gt_v_k_minus_2 : j' > v p n hp (k - 2) := by
      have := h_update_j j' hj' i h_target k ( by linarith ) ( by linarith ) hi; aesop;
    -- Since $j'$ is in interval $k'$, we have $j' \leq v p n hp k'$.
    have h_j'_le_v_k' : j' ≤ v p n hp k' := by
      unfold in_interval at hj'_in; aesop;
    -- Since $v$ is strictly monotone, this implies $k' > k - 2$.
    have h_k'_gt_k_minus_2 : k' > k - 2 := by
      contrapose! h_j'_gt_v_k_minus_2;
      refine le_trans h_j'_le_v_k' ?_;
      -- Since $v$ is strictly monotone, we have $v p n hp k' \leq v p n hp (k - 2)$.
      have h_v_mono : ∀ k₁ k₂, 1 ≤ k₁ → k₁ ≤ k₂ → k₂ ≤ K p → v p n hp k₁ ≤ v p n hp k₂ := by
        intros k₁ k₂ hk₁ hk₂ hk₂_le_Kp
        induction' hk₂ with k₂ hk₂ ih;
        · rfl;
        · exact le_trans ( ih ( Nat.le_of_succ_le hk₂_le_Kp ) ) ( Nat.le_of_lt ( v_strict_mono p n hp k₂ ⟨ by linarith [ Nat.succ_le_succ hk₂ ], by linarith ⟩ ) );
      exact h_v_mono _ _ hk'.1 h_j'_gt_v_k_minus_2 ( Nat.sub_le_of_le_add <| by linarith );
    omega

/-
If j' targets i in interval k >= 3, then the scalar s used is bounded by M_{k-1}.
-/
theorem lemma_scalar_bound_for_target (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (h_inv_prev : ∀ j' < j, Lemma3_invariant p n hp j')
  (h_update_j : UpdateConditionUpTo p n hp j)
  (k : ℕ) (hk : k ≥ 3) (hk_le : k ≤ K p)
  (i : ℕ) (hi : in_interval p n hp k i)
  (j' : ℕ) (hj' : j' < j)
  (s : ℕ) (hs : s ∈ used_s p n hp j') (ht : target_index p j' s = i) :
  s ≤ M p (k - 1) := by
    have h_bounds : s ≤ c_step p n hp j' j' ∧ c_step p n hp j' j' ≤ M p (k - 1) := by
      have h_bounds : c_step p n hp j' j' ≤ M p (k - 1) := by
        have h_c_j'_le_M_k_minus_1 : ∃ k', 1 ≤ k' ∧ k' ≤ K p ∧ in_interval p n hp k' j' ∧ k' ≥ k - 1 := by
          have h_c_j'_le_M_k_minus_1 : ∃ k', 1 ≤ k' ∧ k' ≤ K p ∧ in_interval p n hp k' j' := by
            have := target_implies_in_valid_interval_strong p n hp j';
            exact this ( fun j'' hj'' => h_inv_prev j'' ( by linarith ) |>.1 ) i ⟨ s, hs, ht ⟩;
          have h_c_j'_le_M_k_minus_1 : ∀ k', 1 ≤ k' → k' ≤ K p → in_interval p n hp k' j' → k' ≥ k - 1 := by
            intros k' hk'_ge_1 hk'_le_K hk'_in_interval;
            apply lemma_source_interval_ge;
            all_goals tauto;
          aesop;
        have h_c_j'_le_M_k_minus_1 : ∀ k', 1 ≤ k' → k' ≤ K p → in_interval p n hp k' j' → c_step p n hp j' j' ≤ M p k' := by
          exact fun k' hk'_pos hk'_le hk'_in => h_inv_prev j' hj' |>.1 k' hk'_pos hk'_le j' hk'_in;
        obtain ⟨ k', hk'_range, hk'_le_K, hk'_interval, hk'_ge_k_minus_1 ⟩ := ‹∃ k', 1 ≤ k' ∧ k' ≤ K p ∧ in_interval p n hp k' j' ∧ k' ≥ k - 1›; exact le_trans ( h_c_j'_le_M_k_minus_1 k' hk'_range hk'_le_K hk'_interval ) ( by
          have h_M_decreasing : ∀ k, 1 ≤ k → k < K p → M p (k + 1) ≤ M p k := by
            exact fun k hk hk' => by have := M_decreasing p hp k hk; cases this <;> linarith;
          have h_M_le : ∀ k, 1 ≤ k → k ≤ K p → ∀ k', k ≤ k' → k' ≤ K p → M p k' ≤ M p k := by
            intros k hk hk_le_K k' hk'_ge_k hk'_le_K
            induction' hk'_ge_k with k' hk'_ge_k ih;
            · rfl;
            · grind;
          exact h_M_le _ ( Nat.le_sub_one_of_lt ( by linarith ) ) ( Nat.sub_le_of_le_add ( by linarith ) ) _ hk'_ge_k_minus_1 hk'_le_K ) ;
      cases le_or_gt j' ( m p n hp - 1 ) <;> simp_all +decide [ used_s ];
      · split_ifs at hs <;> simp_all +decide [ decompose_S ];
        · split_ifs at hs <;> simp_all +decide [ Finset.subset_iff ];
          have := Exists.choose_spec ( M_0_properties p hp |>.2.2 ( c_step p n hp j' j' ) ( by linarith ) ( by linarith ) );
          exact this.2 ▸ Finset.single_le_sum ( fun x _ => Nat.zero_le x ) hs;
        · exact decompose_even_pow2_le _ ( by linarith ) _ hs;
      · split_ifs at hs <;> norm_num at hs;
        · omega;
        · apply decompose_even_pow2_le;
          · linarith;
          · assumption;
    grind

/-
If j' targets i in interval k >= 3, then j' >= m.
-/
theorem lemma_source_ge_m (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (h_update_j : UpdateConditionUpTo p n hp j)
  (k : ℕ) (hk : k ≥ 3) (hk_le : k ≤ K p)
  (i : ℕ) (hi : in_interval p n hp k i)
  (j' : ℕ) (hj' : j' < j)
  (h_target : ∃ s ∈ used_s p n hp j', target_index p j' s = i)
  (h_valid_j' : ValidInterval p n hp j') :
  j' ≥ m p n hp := by
    obtain ⟨k', hk'_range, hk'_interval⟩ := h_valid_j';
    -- Since $k' \geq 2$, we have $j' > v p n hp (k' - 1)$.
    have h_j'_gt_v : j' > v p n hp (k' - 1) := by
      have h_k'_ge_2 : k' ≥ 2 := by
        have h_k'_ge_k_minus_1 : k' ≥ k - 1 := by
          have := lemma_source_interval_ge p n hp j h_update_j k hk hk_le i hi j' hj' h_target k' ⟨ hk'_range, hk'_interval.1 ⟩ hk'_interval.2; aesop;
        omega
      unfold in_interval at hk'_interval; aesop;
    -- Since $k' \geq 2$, we have $v p n hp (k' - 1) \geq v p n hp 1$.
    have h_v_ge_v1 : v p n hp (k' - 1) ≥ v p n hp 1 := by
      have h_v_ge_v1 : ∀ k, 1 ≤ k → k ≤ K p → v p n hp k ≥ v p n hp 1 := by
        intros k hk hk_le
        induction' k with k ih;
        · contradiction;
        · rcases k with ( _ | k ) <;> simp_all +decide [ Nat.succ_le_iff ];
          exact le_trans ( ih ( Nat.lt_of_succ_lt hk_le ) ) ( Nat.le_of_lt ( v_strict_mono p n hp ( k + 1 ) ⟨ by linarith, by linarith ⟩ ) );
      exact h_v_ge_v1 _ ( Nat.le_sub_one_of_lt ( lt_of_le_of_ne hk'_range ( Ne.symm ( by rintro rfl; exact absurd h_j'_gt_v ( by unfold v; aesop ) ) ) ) ) ( Nat.sub_le_of_le_add <| by linarith );
    -- Since $v p n hp 1 = m p n hp - 1$, we have $j' > m p n hp - 1$.
    have h_j'_gt_m_sub_1 : j' > m p n hp - 1 := by
      exact lt_of_le_of_lt ( by rw [ v_1_eq_m_sub_1 p n hp ] ) ( lt_of_le_of_lt h_v_ge_v1 h_j'_gt_v );
    exact Nat.le_of_pred_lt h_j'_gt_m_sub_1

/-
The source index and the scalar are in one-to-one correspondence for a fixed target.
-/
theorem lemma_target_map_injective (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (j₁ j₂ : ℕ) (s₁ s₂ : ℕ)
  (h₁ : s₁ ∈ used_s p n hp j₁) (ht₁ : target_index p j₁ s₁ = i)
  (h₂ : s₂ ∈ used_s p n hp j₂) (ht₂ : target_index p j₂ s₂ = i) :
  j₁ = j₂ ↔ s₁ = s₂ := by
    -- By definition of `target_index`, we have `a_seq p i = s₁ * a_seq p j₁` and `a_seq p i = s₂ * a_seq p j₂`.
    have h_eq : a_seq p i = s₁ * a_seq p j₁ ∧ a_seq p i = s₂ * a_seq p j₂ := by
      exact ⟨ by rw [ ← ht₁, target_index_spec p hp.2 j₁ s₁ ( s_in_used_s_mem_A p n hp j₁ s₁ h₁ ) ], by rw [ ← ht₂, target_index_spec p hp.2 j₂ s₂ ( s_in_used_s_mem_A p n hp j₂ s₂ h₂ ) ] ⟩;
    constructor <;> intro h <;> simp_all +decide [ ne_of_gt ( Nat.pos_of_ne_zero _ ), mul_comm ];
    · nlinarith [ show 0 < a_seq p j₂ from a_seq_pos p hp.2 j₂ ];
    · have h_inj : Function.Injective (a_seq p) := by
        exact a_seq_strict_mono p hp.2 |> StrictMono.injective;
      exact h_inj ( mul_left_cancel₀ ( show s₂ ≠ 0 from by rintro rfl; exact absurd h_eq.1 ( by have := a_seq_pos p hp.2 i; aesop ) ) <| by linarith )

/-
If the update condition holds, any source targeting an index in interval k >= 3 must be at least m.
-/
theorem lemma_source_ge_m_of_update_condition (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (h_update : UpdateConditionUpTo p n hp j)
  (k : ℕ) (hk : k ≥ 3) (hk_le : k ≤ K p)
  (i : ℕ) (hi : in_interval p n hp k i)
  (j' : ℕ) (hj' : j' < j)
  (h_target : ∃ s ∈ used_s p n hp j', target_index p j' s = i) :
  j' ≥ m p n hp := by
    have := @lemma_source_interval_ge p n hp;
    contrapose! this;
    refine' ⟨ j, h_update, k, hk, hk_le, i, hi, j', hj', h_target, 1, ⟨ by norm_num, by linarith [ K_ge_2 p ] ⟩, _, _ ⟩ <;> norm_num [ in_interval ] at *;
    · rw [ v_1_eq_m_sub_1 ] ; omega;
    · omega

/-
The scalars used to target i from steps < j are even powers of 2 bounded by M_{k-1}.
-/
theorem lemma_scalars_subset_pow2_Mk (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (h_inv : ∀ j' < j, Lemma3_invariant p n hp j')
  (k : ℕ) (hk : k ≥ 3) (hk_le : k ≤ K p)
  (i : ℕ) (hi : in_interval p n hp k i) :
  let S_targets := (Finset.range j).biUnion (fun j' => (used_s p n hp j').filter (fun s => target_index p j' s = i))
  S_targets ⊆ (Finset.range (M p (k - 1) + 1)).filter (fun s => ∃ m ≥ 1, s = 2^m) := by
    norm_num +zetaDelta at *;
    -- By definition of `used_s`, if `s ∈ used_s p n hp x`, then `s` is in the decomposition of `c_step p n hp x x`.
    intros x hx s hs
    have h_decomp : s ∈ decompose_even_pow2 (c_step p n hp x x) := by
      have h_source_ge_m : x ≥ m p n hp := by
        have h_source_ge_m : ∀ j' < j, IsTarget p n hp j' i → j' ≥ m p n hp := by
          intros j' hj' h_target
          apply lemma_source_ge_m_of_update_condition p n hp j (lemma_update_condition_step_induction p n hp j h_inv) k hk hk_le i hi j' hj' h_target;
        exact h_source_ge_m x hx ⟨ s, by aesop ⟩;
      have h_decomp : used_s p n hp x = decompose_even_pow2 (c_step p n hp x x) := by
        rw [used_s];
        rw [ if_neg h_source_ge_m.not_gt, if_pos ];
        apply c_step_gt_one_of_target;
        exact ⟨ s, Finset.mem_filter.mp hs |>.1, Finset.mem_filter.mp hs |>.2 ⟩;
        assumption;
      grind;
    -- By definition of `decompose_even_pow2`, if `s ∈ decompose_even_pow2 (c_step p n hp x x)`, then `s` is an even power of 2.
    have h_even_pow2 : ∃ m ≥ 1, s = 2 ^ m := by
      have h_decomp_def : s ∈ decompose_even_pow2 (c_step p n hp x x) := h_decomp
      have h_even_pow2 : ∀ x, x > 1 → ∀ s ∈ decompose_even_pow2 x, ∃ m ≥ 1, s = 2 ^ m := by
        intros x hx s hs;
        have := decompose_even_pow2_spec x hx; aesop;
      by_cases h_case : c_step p n hp x x > 1;
      · exact h_even_pow2 _ h_case _ h_decomp_def;
      · interval_cases _ : c_step p n hp x x <;> simp_all +decide [ decompose_even_pow2 ];
    have h_scalar_bound : s ≤ M p (k - 1) := by
      have h_scalar_bound : s ≤ M p (k - 1) := by
        have h_scalar_bound : ∀ s ∈ used_s p n hp x, target_index p x s = i → s ≤ M p (k - 1) := by
          intros s hs ht;
          apply lemma_scalar_bound_for_target p n hp j (fun j' hj' => h_inv j' hj') (lemma_update_condition_step_induction p n hp j (fun j' hj' => h_inv j' hj')) k hk hk_le i hi x hx s hs ht
        exact h_scalar_bound s (by
        aesop) (by
        aesop)
      exact h_scalar_bound;
    exact Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( Nat.lt_succ_of_le h_scalar_bound ), h_even_pow2 ⟩

/-
For i in interval k >= 3, the number of previous steps targeting i is at most M_k.
-/
theorem lemma_target_count_bound (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (h_inv : ∀ j' < j, Lemma3_invariant p n hp j')
  (k : ℕ) (hk : k ≥ 3) (hk_le : k ≤ K p)
  (i : ℕ) (hi : in_interval p n hp k i) :
  (Finset.filter (fun j' => IsTarget p n hp j' i) (Finset.range j)).card ≤ M p k := by
    -- By lemma_scalars_subset_pow2_Mk, the number of targets from steps < j is at most |STargets|.
    have h_card_STargets_le_log2 : (Finset.filter (fun j' => IsTarget p n hp j' i) (Finset.range j)).card ≤ (Finset.filter (fun s => ∃ m ≥ 1, s = 2^m) (Finset.range (M p (k - 1) + 1))).card := by
      -- Apply the lemma_target_map_injective to show that the map from T to STargets is a bijection.
      have h_bijection : Finset.filter (fun j' => IsTarget p n hp j' i) (Finset.range j) ⊆ Finset.biUnion (Finset.filter (fun s => ∃ m ≥ 1, s = 2^m) (Finset.range (M p (k - 1) + 1))) (fun s => Finset.filter (fun j' => IsTarget p n hp j' i ∧ s ∈ used_s p n hp j' ∧ target_index p j' s = i) (Finset.range j)) := by
        intro j' hj'; simp_all +decide [ Finset.subset_iff ] ;
        obtain ⟨ s, hs₁, hs₂ ⟩ := hj'.2;
        have := lemma_scalars_subset_pow2_Mk p n hp j h_inv k hk hk_le i hi;
        exact ⟨ s, by have := this ( Finset.mem_biUnion.mpr ⟨ j', Finset.mem_range.mpr hj'.1, Finset.mem_filter.mpr ⟨ hs₁, hs₂ ⟩ ⟩ ) ; aesop ⟩;
      have h_card_STargets_le_log2 : ∀ s ∈ Finset.filter (fun s => ∃ m ≥ 1, s = 2^m) (Finset.range (M p (k - 1) + 1)), (Finset.filter (fun j' => IsTarget p n hp j' i ∧ s ∈ used_s p n hp j' ∧ target_index p j' s = i) (Finset.range j)).card ≤ 1 := by
        intros s hs
        have h_unique : ∀ j' j'' : ℕ, j' < j → j'' < j → IsTarget p n hp j' i → IsTarget p n hp j'' i → s ∈ used_s p n hp j' → s ∈ used_s p n hp j'' → target_index p j' s = i → target_index p j'' s = i → j' = j'' := by
          intros j' j'' hj'_lt_j hj''_lt_j hj'_target hj''_target hs_j' hs_j'' ht'_eq_i ht''_eq_i;
          have := lemma_target_map_injective p n hp i j' j'' s s hs_j' ht'_eq_i hs_j'' ht''_eq_i; aesop;
        exact Finset.card_le_one.mpr fun x hx y hy => h_unique x y ( Finset.mem_range.mp ( Finset.mem_filter.mp hx |>.1 ) ) ( Finset.mem_range.mp ( Finset.mem_filter.mp hy |>.1 ) ) ( Finset.mem_filter.mp hx |>.2.1 ) ( Finset.mem_filter.mp hy |>.2.1 ) ( Finset.mem_filter.mp hx |>.2.2.1 ) ( Finset.mem_filter.mp hy |>.2.2.1 ) ( Finset.mem_filter.mp hx |>.2.2.2 ) ( Finset.mem_filter.mp hy |>.2.2.2 );
      exact le_trans ( Finset.card_le_card h_bijection ) ( Finset.card_biUnion_le.trans ( Finset.sum_le_card_nsmul _ _ _ fun x hx => h_card_STargets_le_log2 x hx ) ) |> le_trans <| by norm_num;
    have h_card_pow2_le_log2 : (Finset.filter (fun s => ∃ m ≥ 1, s = 2^m) (Finset.range (M p (k - 1) + 1))).card = Nat.log2 (M p (k - 1)) := by
      convert card_pow2_le_log2 ( M p ( k - 1 ) ) using 1;
    rcases k with ( _ | _ | _ | k ) <;> simp_all +decide [ M ]

/-
For i in the first interval, the coefficient is bounded by M_1.
-/
theorem lemma_bound_k1 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (i : ℕ)
  (hi : in_interval p n hp 1 i)
  (h_ge : i ≥ j) :
  c_step p n hp j i ≤ M p 1 := by
    -- Since $i$ is in the first interval, we have $c_step p n hp i i \leq M p 1$ by the lemma_3_case_k1.
    apply lemma_3_case_k1 p n hp i hi |> le_trans (by
    -- Since $j \leq i$, the set of targets for $j$ is a subset of the set of targets for $i$.
    have h_subset : Finset.filter (fun j' => IsTarget p n hp j' i) (Finset.range j) ⊆ Finset.filter (fun j' => IsTarget p n hp j' i) (Finset.range i) := by
      exact fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( lt_of_lt_of_le ( Finset.mem_range.mp ( Finset.mem_filter.mp hx |>.1 ) ) h_ge ), Finset.mem_filter.mp hx |>.2 ⟩;
    rw [ c_step_eq_card_targets_of_ge, c_step_eq_card_targets_of_ge ];
    · exact add_le_add_left ( Finset.card_mono h_subset ) _;
    · linarith;
    · assumption)

/-
If i is in the second interval, all scalars used to target i from previous steps are in S.
-/
theorem lemma_targets_subset_S_interval_2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (i : ℕ)
  (hi : in_interval p n hp 2 i)
  (h_ge : i ≥ j)
  (h_prev : ∀ j' < j, CoeffBound p n hp j') :
  ∀ j' < j, ∀ s ∈ used_s p n hp j', target_index p j' s = i → s ∈ S p := by
    intros j' hj' s hs ht;
    -- Since j' is in the first interval or the second interval, we can apply the respective subset relationship.
    by_cases h_j'_interval : in_interval p n hp 1 j' ∨ in_interval p n hp 2 j';
    · cases h_j'_interval <;> [ exact used_s_subset_S_of_interval_1 _ _ _ _ ‹_› hs; exact used_s_subset_S_of_interval_2 _ _ _ _ ‹_› ( h_prev _ hj' _ le_rfl ( by linarith ) _ ‹_› ) hs ];
      apply (used_s_subset_S_of_interval_2 p n hp j' ‹_› (by
      exact h_prev j' hj' 2 ( by norm_num ) ( by linarith [ show K p ≥ 2 from K_ge_2 p ] ) _ ‹_›)) hs;
    · have := h_prev j' hj' 1 ; simp_all +decide [ in_interval ];
      grind

/-
If a_i is a power of 2, then the scalar s used to target it cannot be p.
-/
theorem lemma_scalar_neq_p_of_pow2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (i : ℕ) (s : ℕ)
  (h_pow2 : ∃ k, a_seq p i = 2^k)
  (hs : s = p)
  (ht : target_index p j s = i) : False := by
    -- If p divides 2^k, then p must be a power of 2. But p is odd and greater than 1, so this is impossible.
    have h_pow2 : p ∣ 2 ^ h_pow2.choose := by
      have h_div : a_seq p i = p * a_seq p j := by
        have h_target : target_index p j p = i → a_seq p i = p * a_seq p j := by
          intros h;
          rw [ ← h, target_index_spec ];
          · grind;
          · exact ⟨ 0, 1, by norm_num ⟩;
        aesop;
      exact h_pow2.choose_spec ▸ h_div ▸ dvd_mul_right _ _;
    have := hp.1; ( have := Nat.Prime.dvd_of_dvd_pow ( Nat.minFac_prime ( by linarith ) ) ( dvd_trans ( Nat.minFac_dvd p ) h_pow2 ) ; simp_all +decide [ Nat.dvd_prime ] ; );
    grind

/-
The list of summands in the final representation.
-/
noncomputable def final_summands (p n : ℕ) (hp : Odd p ∧ p > 1) : List ℕ :=
  ((List.range (final_step_index p n hp)).filter (fun i => c_final p n hp i = 1)).map (a_seq p)

/-
The final summands are distinct.
-/
theorem final_summands_distinct (p n : ℕ) (hp : Odd p ∧ p > 1) :
  (final_summands p n hp).Nodup := by
    -- The list `final_summands p n hp` is nodup because it is constructed from a list of distinct indices.
    have h_distinct_indices : List.Nodup (List.filter (fun i => c_final p n hp i = 1) (List.range (final_step_index p n hp))) := by
      exact List.Nodup.filter _ ( List.nodup_range );
    exact List.Nodup.map ( fun i j hij => by simpa [ a_seq ] using StrictMono.injective ( a_seq_strict_mono p hp.2 ) hij ) h_distinct_indices

/-
All final summands are in A_p.
-/
theorem final_summands_in_A (p n : ℕ) (hp : Odd p ∧ p > 1) :
  ∀ b ∈ final_summands p n hp, b ∈ A p := by
    unfold final_summands;
    -- By definition of $a_seq$, we know that $a_seq p x \in A p$ for all $x$.
    have h_a_seq_in_A : ∀ x, a_seq p x ∈ A p := by
      unfold a_seq;
      split_ifs <;> simp_all +decide [ Set.Infinite ];
      exact absurd ‹_› ( A_infinite p hp.2 );
    aesop

/-
The final summands are sorted.
-/
theorem final_summands_sorted (p n : ℕ) (hp : Odd p ∧ p > 1) :
  (final_summands p n hp).Sorted (· < ·) := by
    -- The indices in the list are strictly increasing, hence their corresponding a_seq values are also strictly increasing.
    have h_sorted : List.Sorted (· < ·) (List.map (fun i => a_seq p i) (List.filter (fun i => c_final p n hp i = 1) (List.range (final_step_index p n hp)))) := by
      have h_sorted : List.Sorted (· < ·) (List.range (final_step_index p n hp)) := by
        exact List.pairwise_iff_get.mpr ( by aesop );
      have h_monotone : StrictMono (a_seq p) := by
        exact a_seq_strict_mono p hp.2;
      have h_monotone : List.Sorted (· < ·) (List.filter (fun i => c_final p n hp i = 1) (List.range (final_step_index p n hp))) := by
        exact h_sorted.filter _;
      (expose_names; exact (StrictMono.sorted_lt_listMap h_monotone_1).mpr h_monotone);
    exact h_sorted

/-
The final coefficient is 0 for indices less than m.
-/
theorem c_final_eq_zero_of_lt_m (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (hi : i < m p n hp) :
  c_final p n hp i = 0 := by
    -- Since $i < m$, we have $i < v_K < \text{final\_step\_index}$.
    have h_final_step : i < final_step_index p n hp := by
      refine lt_of_lt_of_le hi ?_;
      -- Since $v p n hp (K p)$ is the index in $A p$ of $P p (K p) * a_seq p (m p n hp - 1)$, and $a_seq p$ is strictly increasing, we have $v p n hp (K p) \geq m p n hp - 1$.
      have hv_ge_m_minus_1 : v p n hp (K p) ≥ m p n hp - 1 := by
        have h_vi_lt_final_step : ∀ k, 1 ≤ k → k ≤ K p → v p n hp k ≥ m p n hp - 1 := by
          intros k hk1 hk2
          have h_vi_lt_final_step : ∀ k, 1 ≤ k → k ≤ K p → v p n hp k ≥ v p n hp 1 := by
            intros k hk1 hk2
            induction' hk1 with k hk ih;
            · rfl;
            · exact le_trans ( ih ( Nat.le_of_succ_le hk2 ) ) ( Nat.le_of_lt ( v_strict_mono p n hp k ⟨ hk, Nat.lt_of_succ_le hk2 ⟩ ) );
          exact le_trans ( by rw [ v_1_eq_m_sub_1 ] ) ( h_vi_lt_final_step k hk1 hk2 );
        exact h_vi_lt_final_step _ ( Nat.one_le_iff_ne_zero.mpr <| by linarith [ K_ge_2 p ] ) le_rfl;
      unfold final_step_index; omega;
    rw [ c_final_eq_c_step p n hp i h_final_step ];
    rw [ c_step_succ, step_transform ] ; aesop

/-
All final summands are at least a_m.
-/
theorem final_summands_min_ge_m (p n : ℕ) (hp : Odd p ∧ p > 1) :
  ∀ b ∈ final_summands p n hp, b ≥ a_seq p (m p n hp) := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ : ∃ i, c_final p n hp i = 1 ∧ b = a_seq p i := by
      unfold final_summands at hb; aesop;
    by_cases hi_lt_m : i < m p n hp;
    · have := c_final_eq_zero_of_lt_m p n hp i hi_lt_m; aesop;
    · exact a_seq_strict_mono p hp.2 |> StrictMono.monotone <| le_of_not_gt hi_lt_m

/-
All final summands are at most a_{v_K}.
-/
theorem final_summands_max_le_vK (p n : ℕ) (hp : Odd p ∧ p > 1) :
  ∀ b ∈ final_summands p n hp, b ≤ a_seq p (v p n hp (K p)) := by
    intro b hb;
    -- By definition of `final_summands`, we know that every element in `final_summands p n hp` is of the form `a_seq p i` for some `i`.
    obtain ⟨i, hi⟩ : ∃ i, b = a_seq p i ∧ i < final_step_index p n hp := by
      unfold final_summands at hb; aesop;
    -- Since $a_seq p$ is strictly increasing, if $i < v p n hp (K p) + 1$, then $a_seq p i \leq a_seq p (v p n hp (K p))$.
    have h_le : a_seq p i ≤ a_seq p (v p n hp (K p)) := by
      have h_mono : StrictMono (a_seq p) := by
        exact a_seq_strict_mono p hp.2
      exact h_mono.monotone (by
      exact Nat.le_of_lt_succ hi.2);
    linarith

/-
If the coefficient bound holds at step j, then targets satisfy the update condition.
-/
theorem lemma_targets_condition (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (h_coeff : CoeffBound p n hp j)
  (h_valid : ∃ k_j, 1 ≤ k_j ∧ k_j ≤ K p ∧ in_interval p n hp k_j j) :
  ∀ i, IsTarget p n hp j i →
    ∀ k, 1 ≤ k → k ≤ K p →
      in_interval p n hp k i →
      (k ≥ 3 → j > v p n hp (k - 2)) := by
        -- By definition of IsTarget, there exists some s in used_s j and target_index j s = i.
        intro i hi k hk hk_le hk_ge_3;
        rcases hi with ⟨ s, hs₁, hs₂ ⟩;
        -- By Lemma 3, we know that $k_j \geq k - 1$.
        have h_kj_ge_k_1 : ∃ k_j, 1 ≤ k_j ∧ k_j < K p ∧ in_interval p n hp k_j j ∧ k_j ≥ k - 1 := by
          have := target_implies_interval_lt_K p n hp j i ⟨ s, hs₁, hs₂ ⟩ h_coeff h_valid;
          exact ⟨ this.choose, this.choose_spec.1, this.choose_spec.2.1, this.choose_spec.2.2, by have := interval_bound_lemma p n hp j i ⟨ s, hs₁, hs₂ ⟩ h_coeff k ⟨ hk, hk_le ⟩ hk_ge_3 this.choose ⟨ this.choose_spec.1, this.choose_spec.2.1 ⟩ this.choose_spec.2.2; linarith ⟩;
        rcases h_kj_ge_k_1 with ⟨ k_j, hk_j₁, hk_j₂, hk_j₃, hk_j₄ ⟩ ; rcases k with ( _ | _ | k ) <;> simp_all +arith +decide;
        rcases k with ( _ | k ) <;> simp_all +arith +decide [ in_interval ];
        split_ifs at hk_j₃ <;> try linarith;
        -- Since $k_j \geq k + 2$, we have $v p n hp (k_j - 1) \geq v p n hp (k + 1)$.
        have h_v_ge : v p n hp (k_j - 1) ≥ v p n hp (k + 1) := by
          have h_v_ge : ∀ k₁ k₂, 1 ≤ k₁ → k₁ ≤ k₂ → k₂ ≤ K p → v p n hp k₁ ≤ v p n hp k₂ := by
            intros k₁ k₂ hk₁ hk₂ hk₂_le_Kp
            induction' hk₂ with k₂ hk₂ ih;
            · rfl;
            · exact le_trans ( ih ( Nat.le_of_succ_le hk₂_le_Kp ) ) ( Nat.le_of_lt ( v_strict_mono p n hp k₂ ⟨ by linarith [ Nat.succ_le_succ hk₂ ], by linarith [ Nat.succ_le_succ hk₂ ] ⟩ ) );
          exact h_v_ge _ _ ( by linarith ) ( by omega ) ( by omega );
        linarith

/-
Inductive step for UpdateConditionUpTo.
-/
theorem lemma_update_condition_step_induction_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (h_inv_prev : ∀ j' < j, Lemma3_invariant p n hp j') :
  UpdateConditionUpTo p n hp j := by
    -- By definition of UpdateConditionUpTo, we need to show that for all i' < j, the update condition holds.
    intros i' hi' i h_target k hk hk' hi_interval hk_ge_3;
    -- Apply the lemma that states if i' targets i and k ≥ 3, then i' > v p n hp (k - 2).
    apply lemma_update_condition_step_induction p n hp j h_inv_prev i' hi' i h_target k hk hk' hi_interval;
    linarith

/-
The sum of sequence elements at target indices (indicated by the existence of a source scalar) is equal to the sum of the scalars times the sequence element at the source index.
-/
theorem lemma_sum_decomposition_contribution_exists (p : ℕ) (hp : p > 1) (k : ℕ) (U : Finset ℕ) (decomp : Finset ℕ)
  (h_in_A : ∀ s ∈ decomp, s ∈ A p)
  (h_targets : ∀ s ∈ decomp, target_index p k s ∈ U) :
  ∑ i ∈ U, (if ∃ s ∈ decomp, target_index p k s = i then 1 else 0) * a_seq p i = (decomp.sum id) * a_seq p k := by
    -- By definition of $target_index$, we know that $target_index p k s = i$ if and only if $a_seq p i = s * a_seq p k$.
    have h_target_index : ∀ s ∈ decomp, a_seq p (target_index p k s) = s * a_seq p k := by
      exact fun s a ↦ target_index_spec p hp k s (h_in_A s a);
    have h_sum : ∑ i ∈ U, (if ∃ s ∈ decomp, target_index p k s = i then 1 else 0) * a_seq p i = ∑ s ∈ decomp, a_seq p (target_index p k s) := by
      have : Finset.image (fun s => target_index p k s) decomp ⊆ U := by
        exact Finset.image_subset_iff.mpr h_targets
      -- Since $target_index$ is injective on $A_p$, and $s \in A_p$, the map $s \mapsto target_index p k s$ is injective on $decomp$.
      have h_inj : ∀ s t, s ∈ decomp → t ∈ decomp → target_index p k s = target_index p k t → s = t := by
        intros s t hs ht h_eq
        have h_eq' : a_seq p (target_index p k s) = a_seq p (target_index p k t) := by
          rw [h_eq];
        have h_eq'' : s * a_seq p k = t * a_seq p k := by
          rw [ ← h_target_index s hs, ← h_target_index t ht, h_eq' ];
        exact mul_right_cancel₀ ( show a_seq p k ≠ 0 from ne_of_gt ( a_seq_pos p hp k ) ) h_eq'';
      have h_sum_eq : ∑ i ∈ U, (if ∃ s ∈ decomp, target_index p k s = i then 1 else 0) * a_seq p i = ∑ i ∈ Finset.image (fun s => target_index p k s) decomp, a_seq p i := by
        rw [ ← Finset.sum_subset this ];
        · rw [ Finset.sum_congr rfl ] ; aesop;
        · aesop;
      rw [ h_sum_eq, Finset.sum_image <| by intros s hs t ht hst; exact h_inj s t hs ht hst ];
    rw [ h_sum, Finset.sum_congr rfl h_target_index, Finset.sum_mul _ _ _ ] ; aesop

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
Abstract lemma: If coefficients are updated by subtracting a decomposition sum from index k and adding 1 to target indices, the weighted sum is preserved.
-/
theorem lemma_step_preserves_sum_abstract (p : ℕ) (hp : p > 1) (c : ℕ → ℕ) (k : ℕ) (U : Finset ℕ)
  (decomp : Finset ℕ)
  (h_in_A : ∀ s ∈ decomp, s ∈ A p)
  (h_gt_1 : ∀ s ∈ decomp, s > 1)
  (h_decomp_sum_le : decomp.sum id ≤ c k)
  (c' : ℕ → ℕ)
  (h_c'_k : c' k = c k - decomp.sum id)
  (h_c'_other : ∀ i ∈ U, i ≠ k → c' i = c i + (if ∃ s ∈ decomp, target_index p k s = i then 1 else 0))
  (hk : k ∈ U)
  (h_targets : ∀ s ∈ decomp, target_index p k s ∈ U) :
  ∑ i ∈ U, c' i * a_seq p i = ∑ i ∈ U, c i * a_seq p i := by
    have h_total_contribution : ∑ i ∈ U \ {k}, (if ∃ s ∈ decomp, target_index p k s = i then 1 else 0) * a_seq p i = (decomp.sum id) * a_seq p k := by
      have h_total_contribution : ∑ i ∈ U, (if ∃ s ∈ decomp, target_index p k s = i then 1 else 0) * a_seq p i = (decomp.sum id) * a_seq p k := by
        convert lemma_sum_decomposition_contribution_exists p hp k U decomp h_in_A h_targets using 1;
      rw [ ← h_total_contribution, Finset.sum_eq_sum_diff_singleton_add hk ];
      split_ifs <;> simp_all +decide [ ne_of_gt ];
      obtain ⟨ s, hs₁, hs₂ ⟩ := ‹_›; have := target_index_gt_self p hp k s ( h_gt_1 s hs₁ ) ( h_in_A s hs₁ ) ; aesop;
    rw [ Finset.sum_eq_add_sum_diff_singleton hk ];
    rw [ Finset.sum_congr rfl fun i hi => by rw [ h_c'_other i ( Finset.mem_sdiff.mp hi |>.1 ) ( by aesop ) ] ];
    rw [ Finset.sum_eq_add_sum_diff_singleton hk ] ; simp +decide [ *, add_mul ] ; ring_nf;
    simp_all +decide [ Finset.sum_add_distrib, mul_comm, sub_mul ];
    nlinarith [ Nat.sub_add_cancel h_decomp_sum_le ]

/-
Properties of used_s for k < m.
-/
theorem used_s_properties_lt_m (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : k < m p n hp) :
  (∀ s ∈ used_s p n hp k, s ∈ A p ∧ s > 1) ∧
  (used_s p n hp k).sum id ≤ c_step p n hp k k := by
    -- By definition of `used_s`, we know that `used_s p n hp k` is a subset of `S`.
    have h_used_s_subset_S : used_s p n hp k ⊆ S p := by
      unfold used_s;
      have := decompose_S_spec p hp ( c_step p n hp k k );
      unfold decompose_S at * ; aesop;
    -- Since S is a subset of A, we know that all elements in S are greater than 1.
    have h_S_gt_one : ∀ s ∈ S p, s > 1 := by
      intros s hs;
      contrapose! hs; interval_cases s <;> simp_all +decide [ S ] ;
      · have := Exists.choose_spec ( show ∃ x : ℕ, x ∈ S p ∧ Odd x from by
                                      exact Exists.choose_spec ( exists_odd_in_S p hp ) |> fun h => ⟨ _, h.1, h.2 ⟩ )
        generalize_proofs at *;
        intro h; have := ‹∃ S : Finset ℕ, ( ∀ x ∈ S, x ∈ A p ∧ ¬x = 1 ) ∧ ( ∀ k : ℕ, 1 ≤ k → 2 ^ k ≤ S.card → 2 ^ k ∈ S ) ∧ ( ∃ M₀ ≤ p, 0 < M₀ ∧ ∀ x : ℕ, M₀ ≤ x → x ≤ M₀ + S.card → is_sum_of_distinct_elements S x ) ∧ S.card ≤ 1 + Nat.clog 2 p ∧ ∃ m ∈ S, p ≤ m ∧ ∀ x ∈ S, x ≤ m ∧ m ≤ 2 ^ Nat.clog 2 p›.choose_spec.1 0; simp_all +decide [ A ] ;
        linarith [ hp.2 ];
      · have := Exists.choose_spec ( show ∃ s : ℕ, s ∈ A p ∧ s > 1 from by
                                      grind )
        generalize_proofs at *;
        exact fun h => by have := ‹∃ S : Finset ℕ, ( ∀ x ∈ S, x ∈ A p ∧ ¬x = 1 ) ∧ ( ∀ k : ℕ, 1 ≤ k → 2 ^ k ≤ S.card → 2 ^ k ∈ S ) ∧ ( ∃ M₀ ≤ p, 0 < M₀ ∧ ∀ x : ℕ, M₀ ≤ x → x ≤ M₀ + S.card → is_sum_of_distinct_elements S x ) ∧ S.card ≤ 1 + Nat.clog 2 p ∧ ∃ m ∈ S, p ≤ m ∧ ∀ x ∈ S, x ≤ m ∧ m ≤ 2 ^ Nat.clog 2 p›.choose_spec.1 1 h; aesop;
    -- Since used_s is a subset of S and S elements are greater than 1, the sum of used_s elements is less than or equal to c_step k k.
    have h_sum_le_c_step : (used_s p n hp k).sum id ≤ c_step p n hp k k := by
      have h_decomp_S : used_s p n hp k = decompose_S p hp (c_step p n hp k k) := by
        unfold used_s; aesop;
      rw [ h_decomp_S, decompose_S ];
      split_ifs <;> norm_num;
      have := Exists.choose_spec ( show ∃ x : Finset ℕ, x ⊆ S p ∧ x.sum id = c_step p n hp k k from ⟨ _, decompose_S_spec p hp ( c_step p n hp k k ) ( by tauto ) |>.1, decompose_S_spec p hp ( c_step p n hp k k ) ( by tauto ) |>.2 ⟩ ) ; aesop;
    exact ⟨ fun s hs => ⟨ h_used_s_subset_S hs |> fun hs' => by have := S_properties p hp; aesop, h_S_gt_one s ( h_used_s_subset_S hs ) ⟩, h_sum_le_c_step ⟩

/-
Properties of used_s for k >= m.
-/
theorem used_s_properties_ge_m (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : k ≥ m p n hp) :
  (∀ s ∈ used_s p n hp k, s ∈ A p ∧ s > 1) ∧
  (used_s p n hp k).sum id ≤ c_step p n hp k k := by
    by_cases h : c_step p n hp k k > 1;
    · -- In this case, `used_s` is `decompose_even_pow2 (c_step k k)`.
      have h_used_s : used_s p n hp k = decompose_even_pow2 (c_step p n hp k k) := by
        unfold used_s; aesop;
      have := decompose_even_pow2_spec ( c_step p n hp k k ) h;
      simp_all +decide [ A ];
      exact ⟨ fun s hs => ⟨ by obtain ⟨ k, hk₁, rfl ⟩ := this.2 s hs; exact ⟨ k, 0, by ring ⟩, by obtain ⟨ k, hk₁, rfl ⟩ := this.2 s hs; exact one_lt_pow₀ one_lt_two ( by linarith ) ⟩, by cases this.1 <;> omega ⟩;
    · -- Since $c_step k k \leq 1$, by definition of $used_s$, we have $used_s k = ∅$.
      have h_used_empty : used_s p n hp k = ∅ := by
        have h_nonpos : c_step p n hp k k ≤ 1 := by linarith
        exact used_s_empty_of_le_one p n hp k hk h_nonpos;
      aesop

/-
The coefficient at index i is non-decreasing when moving from step k to k+1, provided k < i.
-/
theorem c_step_mono_up_to (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (k : ℕ) (hk : k < i) :
  c_step p n hp k i ≤ c_step p n hp (k + 1) i := by
    rw [ c_step_succ ];
    unfold step_transform; aesop;

/-
The sets of scalars used by different steps to target the same index are disjoint.
-/
theorem scalars_disjoint (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (j₁ j₂ : ℕ) (hj : j₁ ≠ j₂) :
  Disjoint ((used_s p n hp j₁).filter (fun s => target_index p j₁ s = i))
           ((used_s p n hp j₂).filter (fun s => target_index p j₂ s = i)) := by
             exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => hj <| by have := lemma_target_map_injective p n hp i j₁ j₂ x x; aesop;

/-
For any scalar s used in step k, the target index is strictly greater than k.
-/
theorem target_index_gt_source (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) :
  ∀ s ∈ used_s p n hp k, target_index p k s > k := by
    intro s hs;
    by_cases hk : k < m p n hp;
    · have := used_s_properties_lt_m p n hp k hk;
      exact target_index_gt_self p hp.2 k s ( this.1 s hs |>.2 ) ( this.1 s hs |>.1 );
    · -- Since $k \geq m$, we have $s > 1$.
      have hs_gt_1 : s > 1 := by
        have := used_s_properties_ge_m p n hp k ( le_of_not_gt hk );
        exact this.1 s hs |>.2;
      exact target_index_gt_self p hp.2 k s hs_gt_1 ( s_in_used_s_mem_A p n hp k s hs )

/-
The coefficient at index i is non-decreasing with respect to the step index k, as long as k <= i.
-/
theorem c_step_le_of_le (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (j k : ℕ) (hjk : j ≤ k) (hki : k ≤ i) :
  c_step p n hp j i ≤ c_step p n hp k i := by
    -- We proceed by induction on $k$.
    induction' hjk with k hk ih;
    · rfl;
    · exact le_trans ( ih ( Nat.le_of_succ_le hki ) ) ( c_step_mono_up_to _ _ _ _ _ ( Nat.lt_of_succ_le hki ) )

/-
In the second interval, the coefficient is bounded by M_2.
-/
theorem lemma_3_case_k2_new (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ)
  (hi : in_interval p n hp 2 i)
  (h_prev : ∀ j < i, CoeffBound p n hp j) :
  c_step p n hp i i ≤ M p 2 := by
    exact lemma_3_case_k2 p n hp i hi h_prev

/-
The set of contributing scalars up to step j is a subset of S, for i in the second interval.
-/
noncomputable def contributing_s_up_to (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ) : Finset ℕ :=
  (Finset.range j).biUnion (fun j' => (used_s p n hp j').filter (fun s => target_index p j' s = i))

theorem contributing_s_up_to_subset_S (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ)
  (hi : in_interval p n hp 2 i)
  (h_ge : i ≥ j)
  (h_prev : ∀ j' < j, CoeffBound p n hp j') :
  contributing_s_up_to p n hp j i ⊆ S p := by
    intro s hs
    obtain ⟨j', hj', hs_s, h_target⟩ : ∃ j', j' < j ∧ s ∈ used_s p n hp j' ∧ target_index p j' s = i := by
      unfold contributing_s_up_to at hs; aesop;
    have := lemma_targets_subset_S_interval_2 p n hp j i hi ( by linarith ) h_prev j' hj' s hs_s h_target; aesop;

/-
The coefficient at step j is the initial coefficient plus the number of contributing scalars up to step j.
-/
theorem c_step_eq_init_plus_scalars_card (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ) (h_ge : i ≥ j) :
  c_step p n hp j i = c_init p n hp i + (contributing_s_up_to p n hp j i).card := by
    have h_card : ∀ j' < j, Finset.card ((used_s p n hp j').filter (fun s => target_index p j' s = i)) = if ∃ s ∈ used_s p n hp j', target_index p j' s = i then 1 else 0 := by
      intro j' hj'
      have h_unique_scalar : ∀ s₁ s₂, s₁ ∈ used_s p n hp j' → s₂ ∈ used_s p n hp j' → target_index p j' s₁ = i → target_index p j' s₂ = i → s₁ = s₂ := by
        intros s₁ s₂ hs₁ hs₂ h₁ h₂;
        have := lemma_target_map_injective p n hp i j' j' s₁ s₂ hs₁ h₁ hs₂ h₂; aesop;
      split_ifs <;> simp_all +decide [ Finset.card_le_one ];
      exact Finset.card_eq_one.mpr ⟨ Classical.choose ‹∃ s ∈ used_s p n hp j', target_index p j' s = i›, Finset.eq_singleton_iff_unique_mem.mpr ⟨ Finset.mem_filter.mpr ⟨ Classical.choose_spec ‹∃ s ∈ used_s p n hp j', target_index p j' s = i› |>.1, Classical.choose_spec ‹∃ s ∈ used_s p n hp j', target_index p j' s = i› |>.2 ⟩, fun s hs => h_unique_scalar _ _ ( Finset.mem_filter.mp hs |>.1 ) ( Classical.choose_spec ‹∃ s ∈ used_s p n hp j', target_index p j' s = i› |>.1 ) ( Finset.mem_filter.mp hs |>.2 ) ( Classical.choose_spec ‹∃ s ∈ used_s p n hp j', target_index p j' s = i› |>.2 ) ⟩ ⟩;
    rw [ show contributing_s_up_to p n hp j i = Finset.biUnion ( Finset.range j ) fun j' => Finset.filter ( fun s => target_index p j' s = i ) ( used_s p n hp j' ) by rfl, Finset.card_biUnion ];
    · rw [ Finset.sum_congr rfl fun x hx => h_card x <| Finset.mem_range.mp hx ];
      convert c_step_eq_card_targets_of_ge p n hp j i h_ge using 1;
      simp +decide [ IsTarget ];
      congr! 2;
    · intros j' hj' j'' hj'' hij; have := scalars_disjoint p n hp i j' j'' hij; aesop;

/-
If the target a_i is a power of 2, then any contributing scalar s must be a power of 2.
-/
theorem lemma_scalars_pow2_if_target_pow2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ)
  (h_pow2 : ∃ k, a_seq p i = 2^k) :
  ∀ s ∈ contributing_s_up_to p n hp j i, ∃ k, s = 2^k := by
    intros s hs;
    -- By definition of contributing_s_up_to, there exists some j' < j such that s ∈ used_s p n hp j' and target_index p j' s = i.
    obtain ⟨j', hj', hs'⟩ : ∃ j', j' < j ∧ s ∈ used_s p n hp j' ∧ target_index p j' s = i := by
      unfold contributing_s_up_to at hs; aesop;
    -- By Lemma 2, $a_i = s * a_{j'}$.
    have h_ai : a_seq p i = s * a_seq p j' := by
      rw [ ← hs'.2, target_index_spec ];
      · grind;
      · exact s_in_used_s_mem_A p n hp j' s hs'.1;
    -- Since $a_i$ is a power of 2, $s * a_{j'}$ is also a power of 2.
    obtain ⟨k, hk⟩ : ∃ k, s * a_seq p j' = 2 ^ k := by
      aesop;
    have : s ∣ 2 ^ k := hk ▸ dvd_mul_right _ _; ( erw [ Nat.dvd_prime_pow ( by decide ) ] at this; tauto; )

/-
If the target is a power of 2, the number of contributing scalars is at most |S| - 1.
-/
theorem card_contributing_le_S_sub_one_if_pow2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ)
  (hi : in_interval p n hp 2 i)
  (h_ge : i ≥ j)
  (h_prev : ∀ j' < j, CoeffBound p n hp j')
  (h_pow2 : ∃ k, a_seq p i = 2^k) :
  (contributing_s_up_to p n hp j i).card ≤ (S p).card - 1 := by
    -- By `exists_non_pow2_in_S`, there exists `x ∈ S` such that `x` is not a power of 2.
    obtain ⟨x, hxS, hx_pow2⟩ : ∃ x ∈ S p, ∀ k : ℕ, x ≠ 2^k := by
      exact exists_non_pow2_in_S p hp;
    -- Thus `x \notin contributing_s_up_to`.
    have hx_not_in : x ∉ contributing_s_up_to p n hp j i := by
      contrapose! hx_pow2;
      exact lemma_scalars_pow2_if_target_pow2 p n hp j i h_pow2 x hx_pow2;
    have h_subset : contributing_s_up_to p n hp j i ⊆ (S p).erase x := by
      exact fun y hy => Finset.mem_erase_of_ne_of_mem ( by aesop ) ( contributing_s_up_to_subset_S p n hp j i hi h_ge h_prev hy );
    exact le_trans ( Finset.card_le_card h_subset ) ( by rw [ Finset.card_erase_of_mem hxS ] )

/-
Case 0 of Lemma 3 for k=2: If c_init is 0, the bound holds.
-/
theorem lemma_bound_k2_case_0 (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ)
  (hi : in_interval p n hp 2 i)
  (h_ge : i ≥ j)
  (h_prev : ∀ j' < j, CoeffBound p n hp j')
  (h_init : c_init p n hp i = 0) :
  c_step p n hp j i ≤ M p 2 := by
    have h_card : (contributing_s_up_to p n hp j i).card ≤ (S p).card := by
      exact Finset.card_le_card fun x hx => by have := contributing_s_up_to_subset_S p n hp j i hi h_ge h_prev; aesop;
    have := c_step_eq_init_plus_scalars_card p n hp j i h_ge; aesop;

/-
For indices in intervals k >= 3, the coefficient at step j is bounded by M_k.
-/
theorem lemma_bound_ge3 (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (j : ℕ)
  (h_inv_prev : ∀ j' < j, Lemma3_invariant p n hp j')
  (k : ℕ) (hk : k ≥ 3) (hk_le : k ≤ K p)
  (i : ℕ) (hi : in_interval p n hp k i)
  (h_ge : i ≥ j) :
  c_step p n hp j i ≤ M p k := by
    -- By definition of $c\_step$, we can write $c\_step j i$ as $c\_init i + (Finset.filter (fun j' => IsTarget p n hp j' i) (Finset.range j)).card$.
    have h_decomp : c_step p n hp j i = c_init p n hp i + (Finset.filter (fun j' => IsTarget p n hp j' i) (Finset.range j)).card := by
      apply c_step_eq_card_targets_of_ge; assumption;
    have h_card_targets : (Finset.filter (fun j' => IsTarget p n hp j' i) (Finset.range j)).card ≤ M p k := by
      exact lemma_target_count_bound p n hp j h_inv_prev k hk hk_le i hi;
    rw [ h_decomp ];
    rw [ c_init_eq_zero_of_ge_3 p n hp hn i k hk hk_le hi ] ; linarith

/-
If the initial coefficient is 1 for an index in the second interval, the coefficient bound holds.
-/
theorem lemma_bound_k2_case_1 (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (j : ℕ) (i : ℕ)
  (hi : in_interval p n hp 2 i)
  (h_ge : i ≥ j)
  (h_prev : ∀ j' < j, CoeffBound p n hp j')
  (h_init : c_init p n hp i = 1) :
  c_step p n hp j i ≤ M p 2 := by
    -- Applying `card_contributing_le_S_sub_one_if_pow2` and `c_step_eq_init_plus_scalars_card`, we can deduce the upper bound.
    have h_card : (contributing_s_up_to p n hp j i).card ≤ M p 2 - 1 := by
      convert card_contributing_le_S_sub_one_if_pow2 p n hp j i hi h_ge h_prev _;
      apply c_init_eq_one_imp_pow2 p n hp i (by
      exact j_ge_m_of_in_interval_ge_2 p n hp i 2 ( by norm_num ) hi) h_init;
    rw [ c_step_eq_init_plus_scalars_card ] ; linarith [ Nat.sub_add_cancel ( show 1 ≤ M p 2 from M_ge_one_of_le_K p hp 2 ⟨ by decide, by linarith [ K_ge_2 p ] ⟩ ) ] ;
    assumption

/-
For indices in the second interval, the coefficient at step j is bounded by M_2.
-/
theorem lemma_bound_k2 (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (j : ℕ) (i : ℕ)
  (hi : in_interval p n hp 2 i)
  (h_ge : i ≥ j)
  (h_prev : ∀ j' < j, CoeffBound p n hp j') :
  c_step p n hp j i ≤ M p 2 := by
    by_cases h_c_init : c_init p n hp i = 1;
    · exact lemma_bound_k2_case_1 p n hp hn j i hi h_ge h_prev h_c_init;
    · by_cases h_c_init : c_init p n hp i = 0;
      · exact lemma_bound_k2_case_0 p n hp j i hi h_ge h_prev h_c_init;
      · have := c_init_le_one_of_gt_v1 p n hp i ( by cases hi; aesop ) ; interval_cases _ : c_init p n hp i <;> simp_all +decide ;

/-
For indices in the second interval, the coefficient at step j is bounded by M_2.
-/
theorem lemma_bound_k2_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (j : ℕ) (i : ℕ)
  (hi : in_interval p n hp 2 i)
  (h_ge : i ≥ j)
  (h_prev : ∀ j' < j, CoeffBound p n hp j') :
  c_step p n hp j i ≤ M p 2 := by
    exact lemma_bound_k2 p n hp hn j i hi h_ge h_prev

/-
If the invariant holds for all steps before j, then the coefficient bounds hold at step j.
-/
theorem lemma_coeff_bound_step (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (j : ℕ)
  (h_inv_prev : ∀ j' < j, Lemma3_invariant p n hp j') :
  CoeffBound p n hp j := by
  intro k hk hk_le i hi
  by_cases h_lt : i < j
  · have h_stable : c_step p n hp j i = c_step p n hp (i + 1) i := by
      refine Nat.le_induction rfl (fun k hk_le ih => ?_) j h_lt
      rw [c_step_stable p n hp k i (by linarith), ih]
    rw [h_stable]
    apply le_trans (c_step_at_k_le_one p n hp i)
    apply M_ge_one_of_le_K p hp k ⟨hk, hk_le⟩
  · have h_ge : i ≥ j := le_of_not_gt h_lt
    by_cases hk_ge_3 : k ≥ 3
    · apply lemma_bound_ge3 p n hp hn j h_inv_prev k hk_ge_3 hk_le i hi h_ge
    · interval_cases k
      · apply lemma_bound_k1 p n hp j i hi h_ge
      · apply lemma_bound_k2_v2 p n hp hn j i hi h_ge (fun j' hj' => (h_inv_prev j' hj').1)

/-
Recursive definition of P.
-/
theorem lemma_P_recursive (p : ℕ) (k : ℕ) (hk : k ≥ 1) : P p k = P p (k - 1) * u p k := by
  rcases k with ( _ | k ) <;> simp_all +decide [ pow_succ' ];
  unfold P;
  simp +decide [ List.range_succ ];
  ring

/-
Upper bound for elements in interval k.
-/
theorem lemma_interval_upper_bound (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ K p) (i : ℕ) (hi : in_interval p n hp k i) :
  a_seq p i ≤ P p k * a_seq p (m p n hp - 1) := by
    -- By definition of in_interval, we know that i ≤ v p n hp k.
    have h_i_le_vk : i ≤ v p n hp k := by
      unfold in_interval at hi; aesop;
    have h_a_seq_le : a_seq p i ≤ a_seq p (v p n hp k) := by
      -- Since $a_seq$ is strictly increasing, we have $a_seq p i \leq a_seq p (v p n hp k)$.
      have h_a_inc : StrictMono (a_seq p) := by
        exact a_seq_strict_mono p hp.2;
      exact h_a_inc.monotone h_i_le_vk;
    convert h_a_seq_le using 1;
    exact Eq.symm (v_spec p n hp k)

/-
If j targets i from a much earlier interval, the scalar s must be large.
-/
theorem lemma_s_gt_u (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (i : ℕ) (s : ℕ)
  (k : ℕ) (hk : k ≥ 3) (hk_le : k ≤ K p) (hi : in_interval p n hp k i)
  (k_j : ℕ) (hk_j : 1 ≤ k_j ∧ k_j ≤ k - 2) (hj : in_interval p n hp k_j j)
  (ht : target_index p j s = i)
  (hs : s ∈ used_s p n hp j) :
  s > u p (k - 1) := by
    -- By the properties of the target index and the definition of $u$, we have $a_i = s * a_j$.
    obtain ⟨h_ai, h_aj⟩ : a_seq p i = s * a_seq p j ∧ a_seq p (v p n hp (k - 1)) = P p (k - 1) * a_seq p (m p n hp - 1) ∧ a_seq p j ≤ P p k_j * a_seq p (m p n hp - 1) := by
      have h_ai : a_seq p i = s * a_seq p j := by
        rw [ ← ht, target_index_spec ];
        · exact hp.2;
        · exact s_in_used_s_mem_A p n hp j s hs
      have h_aj : a_seq p (v p n hp (k - 1)) = P p (k - 1) * a_seq p (m p n hp - 1) := by
        exact v_spec p n hp (k - 1)
      have h_aj_le : a_seq p j ≤ P p k_j * a_seq p (m p n hp - 1) := by
        apply lemma_interval_upper_bound p n hp k_j ⟨by linarith, by
          omega⟩ j hj
      exact ⟨h_ai, h_aj, h_aj_le⟩;
    -- Since $a_seq$ is strictly increasing, $a_i > a_{v (k-1)} = P (k-1) * a_{m-1}$.
    have h_ai_gt : a_seq p i > P p (k - 1) * a_seq p (m p n hp - 1) := by
      have h_ai_gt : a_seq p i > a_seq p (v p n hp (k - 1)) := by
        apply_rules [ a_seq_strict_mono ];
        · linarith;
        · rcases k with ( _ | _ | k ) <;> simp_all +decide [ in_interval ];
      grind +ring;
    -- Since $k_j \leq k - 2$, we have $P k_j \leq P (k - 2)$.
    have h_P_kj_le_P_k_minus_2 : P p k_j ≤ P p (k - 2) := by
      apply_rules [ P_mono ] ; omega;
    -- Since $P (k - 1) = P (k - 2) * u (k - 1)$, we have $P (k - 1) / P k_j \geq u (k - 1)$.
    have h_P_k_minus_1_div_P_kj_ge_u_k_minus_1 : P p (k - 1) ≥ P p k_j * u p (k - 1) := by
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.succ_eq_add_one, mul_assoc, mul_comm, mul_left_comm, P ];
      simp_all +decide [ List.range_succ ];
      nlinarith [ Nat.zero_le ( ( List.map ( u p ) ( List.range k_j ) ).prod * u p k_j ), Nat.zero_le ( ( List.map ( u p ) ( List.range k ) ).prod * u p k ), Nat.zero_le ( u p ( k + 1 ) ) ];
    nlinarith [ show 0 < a_seq p ( m p n hp - 1 ) from Nat.pos_of_ne_zero ( by aesop ) ]

/-
Elements in interval k are strictly greater than P_{k-1} * a_{m-1}.
-/
theorem lemma_ai_gt_P_prev (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : k ≥ 2) (hk_le : k ≤ K p) (i : ℕ) (hi : in_interval p n hp k i) :
  a_seq p i > P p (k - 1) * a_seq p (m p n hp - 1) := by
    have h_i_gt_vk_minus_1 : i > v p n hp (k - 1) := by
      rw [ in_interval ] at hi ; aesop;
    have h_ai_gt_avk_minus_1 : a_seq p i > a_seq p (v p n hp (k - 1)) := by
      apply a_seq_strict_mono;
      · exact hp.2;
      · linarith;
    have := v_spec p n hp ( k - 1 );
    linarith

/-
P_{k-1} is at least u_{k-1} * P_{k_j}.
-/
theorem lemma_P_ratio_ge_u (p : ℕ) (k : ℕ) (hk : k ≥ 3) (k_j : ℕ) (hk_j : k_j ≤ k - 2) :
  P p (k - 1) ≥ u p (k - 1) * P p k_j := by
    -- By definition of $P$, we have $P p (k - 1) = P p (k - 2) * u p (k - 1)$.
    have hP_k_minus_1 : P p (k - 1) = P p (k - 2) * u p (k - 1) := by
      apply lemma_P_recursive;
      omega;
    rw [ hP_k_minus_1, Nat.mul_comm ];
    -- Since $k_j \leq k - 2$, we have $P p k_j \leq P p (k - 2)$ by the monotonicity of $P$.
    apply Nat.mul_le_mul_left
    apply P_mono
    exact hk_j

/-
The invariant Lemma3_invariant holds for all steps j.
-/
theorem lemma_invariant_holds (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (j : ℕ) :
  Lemma3_invariant p n hp j := by
    induction' j using Nat.strongRecOn with j ih;
    exact ⟨ lemma_coeff_bound_step p n hp hn j ih, lemma_update_condition_step_induction_v2 p n hp j ih ⟩

/-
For any step k within the range, all target indices generated are also within the range.
-/
theorem lemma_targets_in_range (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (k : ℕ) (hk : k < final_step_index p n hp) :
  ∀ s ∈ used_s p n hp k, target_index p k s < final_step_index p n hp := by
    -- Apply the lemma that states if k is in the interval k' and k' is less than K, then the target index is less than v_K.
    intros s hs
    have h_target_le_vK : target_index p k s ≤ v p n hp (K p) := by
      apply target_bound_from_source;
      exact ⟨ s, hs, rfl ⟩;
      · apply (lemma_invariant_holds p n hp hn k).left;
      · apply target_implies_in_valid_interval_strong;
        exacts [ fun j' hj' => lemma_invariant_holds p n hp hn j' |>.1, ⟨ s, hs, rfl ⟩ ];
    exact lt_of_le_of_lt h_target_le_vK ( Nat.lt_succ_self _ )

/-
Definitions for the v2 version of the algorithm, which splits at m-1 instead of m.
-/
noncomputable def used_s_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Finset ℕ :=
  let c := c_step_v2 p n hp j j
  if j < m p n hp - 1 then
    decompose_S p hp c
  else
    if c > 1 then decompose_even_pow2 c else ∅

def CoeffBound_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ K p →
    ∀ i, in_interval p n hp k i →
      c_step_v2 p n hp j i ≤ M p k

def IsTarget_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ) : Prop :=
  ∃ s ∈ used_s_v2 p n hp j, target_index p j s = i

def UpdateConditionUpTo_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Prop :=
  ∀ i' < j, ∀ i, IsTarget_v2 p n hp i' i →
    ∀ k, 1 ≤ k → k ≤ K p →
      in_interval p n hp k i →
      (k ≥ 3 → i' > v p n hp (k - 2))

def Lemma3_invariant_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Prop :=
  CoeffBound_v2 p n hp j ∧ UpdateConditionUpTo_v2 p n hp j

/-
For indices j < m-1, the initial coefficient c_init is between M_0 and M_0 + 1.
-/
theorem c_init_bounds_lt_m (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (hj : j < m p n hp - 1) :
  M_0 p ≤ c_init p n hp j ∧ c_init p n hp j ≤ M_0 p + 1 := by
    unfold c_init;
    unfold coeff_from_binary;
    grind +ring

/-
For indices in the first interval, the contributing scalars are a subset of S.
-/
noncomputable def contributing_scalars_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) : Finset ℕ :=
  (Finset.range i).biUnion (fun j => (used_s_v2 p n hp j).filter (fun s => target_index p j s = i))

theorem contributing_scalars_v2_subset_S (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (hi : i < m p n hp - 1) :
  contributing_scalars_v2 p n hp i ⊆ S p := by
    -- For j' < i, used_s_v2 j' is a subset of S by definition.
    have h_used_s_subset_S : ∀ j' < i, used_s_v2 p n hp j' ⊆ S p := by
      intro j' hj'
      simp [used_s_v2];
      split_ifs <;> simp_all +decide [ decompose_S ];
      · split_ifs <;> norm_num;
        all_goals generalize_proofs at *;
        exact Exists.choose_spec ‹∃ s ⊆ S p, ∑ x ∈ s, x = c_step_v2 p n hp j' j'› |>.1;
      · omega;
    exact Finset.biUnion_subset.mpr fun j' hj' => Finset.Subset.trans ( Finset.filter_subset _ _ ) ( h_used_s_subset_S j' ( by aesop ) )

/-
Definition of contributing scalars up to a certain step limit.
-/
noncomputable def contributing_scalars_v2_up_to (p n : ℕ) (hp : Odd p ∧ p > 1) (limit : ℕ) (i : ℕ) : Finset ℕ :=
  (Finset.range limit).biUnion (fun j => (used_s_v2 p n hp j).filter (fun s => target_index p j s = i))

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
Elements of used_s_v2 are in A_p and strictly greater than 1.
-/
theorem used_s_v2_properties (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) :
  ∀ s ∈ used_s_v2 p n hp j, s ∈ A p ∧ s > 1 := by
    -- By definition of `used_s_v2`, we split into cases based on `j < m - 1`.
    by_cases hj : j < m p n hp - 1;
    · -- By definition of `used_s_v2`, when `j < m - 1`, it is equal to `decompose_S`.
      have h_decomp_S : used_s_v2 p n hp j = decompose_S p hp (c_step_v2 p n hp j j) := by
        exact if_pos hj;
      exact h_decomp_S ▸ fun s hs => decompose_S_properties p hp _ s hs;
    · -- Since $j \geq m - 1$, used_s_v2 is either decompose_even_pow2 (if c > 1) or empty.
      simp [used_s_v2, hj];
      intro s hs; split_ifs at hs <;> simp_all +decide [ A ] ;
      have := decompose_even_pow2_spec ( c_step_v2 p n hp j j ) ‹_›;
      rcases this.2 s hs with ⟨ k, hk₁, rfl ⟩ ; exact ⟨ ⟨ k, 0, by norm_num ⟩, one_lt_pow₀ ( by norm_num ) ( by linarith ) ⟩ ;

/-
For indices i >= m-1, the initial coefficient is at most 1.
-/
theorem c_init_le_one_of_ge_m_sub_1 (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (hi : i ≥ m p n hp - 1) :
  c_init p n hp i ≤ 1 := by
    unfold c_init;
    unfold coeff_from_binary;
    grind

/-
The function index_in_A is injective on the set A_p.
-/
theorem index_in_A_injective_on_A (p : ℕ) (hp : p > 1) :
  ∀ x y, x ∈ A p → y ∈ A p → index_in_A p x = index_in_A p y → x = y := by
    -- By definition of `index_in_A`, if `index_in_A p x = index_in_A p y`, then `a_seq p (index_in_A p x) = a_seq p (index_in_A p y)`.
    intros x y hx hy hxy
    have h_eq : a_seq p (index_in_A p x) = a_seq p (index_in_A p y) := by
      rw [hxy];
    rw [ a_seq_index_in_A, a_seq_index_in_A ] at h_eq <;> tauto

/-
If the initial coefficient is greater than M_0, then the corresponding sequence element is a power of 2.
-/
theorem ak_is_pow2_of_gt_M0 (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : k < m p n hp - 1)
  (h_gt : c_init p n hp k > M_0 p) :
  ∃ j, a_seq p k = 2^j := by
    exact c_init_gt_M0_imp_pow2 p n hp k ( by simpa [ v_1_eq_m_sub_1 ] using hk.le ) h_gt

/-
The sum of the scalars used in step j is at most the coefficient at index j.
-/
theorem used_s_v2_sum_le (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) :
  (used_s_v2 p n hp j).sum id ≤ c_step_v2 p n hp j j := by
    unfold used_s_v2;
    split_ifs <;> simp_all +decide [ Nat.sub_eq_iff_eq_add ];
    · unfold decompose_S;
      split_ifs <;> simp_all +decide [ Finset.sum_ite ];
      have := Exists.choose_spec ( show ∃ s ∈ Finset.powerset ( S p ), s.sum id ≤ c_step_v2 p n hp j j ∧ ∀ t ∈ Finset.powerset ( S p ), t.sum id ≤ c_step_v2 p n hp j j → t.card ≤ s.card from by
                                    have h_max_card : ∃ s ∈ Finset.filter (fun t => t.sum id ≤ c_step_v2 p n hp j j) (Finset.powerset (S p)), ∀ t ∈ Finset.filter (fun t => t.sum id ≤ c_step_v2 p n hp j j) (Finset.powerset (S p)), t.card ≤ s.card := by
                                      apply_rules [ Finset.exists_max_image ];
                                      exact ⟨ ∅, by aesop ⟩;
                                    exact ⟨ h_max_card.choose, Finset.mem_filter.mp h_max_card.choose_spec.1 |>.1, Finset.mem_filter.mp h_max_card.choose_spec.1 |>.2, fun t ht ht' => h_max_card.choose_spec.2 t ( Finset.mem_filter.mpr ⟨ ht, ht' ⟩ ) ⟩ );
      all_goals generalize_proofs at *;
      exact ‹∃ s ⊆ S p, ∑ x ∈ s, x = c_step_v2 p n hp j j›.choose_spec.2.le;
    · split_ifs <;> simp_all +decide [ decompose_even_pow2 ];
      -- The sum of the even powers of 2 in the decomposition of x is at most x.
      have h_sum_even_powers : ∀ x, (List.map (fun x => 2 ^ x) (x).bitIndices).toFinset.sum id ≤ x := by
        intro x;
        induction' x using Nat.strong_induction_on with x ih;
        rcases Nat.even_or_odd' x with ⟨ k, rfl | rfl ⟩ <;> simp_all +decide [ Nat.pow_succ', Nat.mul_mod ];
        · by_cases hk : k = 0;
          · aesop;
          · convert Nat.mul_le_mul_left 2 ( ih k ( by linarith [ Nat.pos_of_ne_zero hk ] ) ) using 1;
            rw [ Finset.mul_sum _ _ _ ];
            refine' Finset.sum_bij ( fun x hx => x / 2 ) _ _ _ _ <;> simp_all +decide [ Function.comp, Nat.pow_succ' ];
        · have := ih k ( by linarith ) ; simp_all +decide [ Function.comp, Finset.sum_add_distrib ] ;
          rw [ show ( List.map ( ( fun x => 2 ^ x ) ∘ fun x => x + 1 ) k.bitIndices ).toFinset = Finset.image ( fun x => 2 ^ ( x + 1 ) ) ( List.toFinset k.bitIndices ) by ext; aesop ] ; rw [ Finset.sum_image ] <;> simp_all +decide [ pow_succ', mul_assoc, mul_comm, mul_left_comm ];
          rw [ ← Finset.mul_sum _ _ _ ] ; linarith! [ show ∑ x ∈ k.bitIndices.toFinset, 2 ^ x ≤ k from by simp [ List.map ] ] ;
      split_ifs <;> [ exact h_sum_even_powers _ |> le_trans <| by linarith; ; exact le_trans ( h_sum_even_powers _ ) <| by omega ]

/-
After step k, the coefficient at index k is at most 1.
-/
theorem c_step_v2_at_k_le_one (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) :
  c_step_v2 p n hp (k + 1) k ≤ 1 := by
    by_cases hk : k < m p n hp - 1;
    · -- By definition of step_transform_v2, if k < m - 1, then c_step_v2 p n hp (k + 1) k is the result of applying step_transform_v2 to c_step_v2 p n hp k.
      have h_step : c_step_v2 p n hp (k + 1) k = step_transform_v2 p n hp (c_step_v2 p n hp k) k k := by
        exact rfl;
      unfold step_transform_v2 at h_step; aesop;
    · -- By definition of step_transform_v2, if k ≥ m - 1 and c_step_v2 p n hp k k > 1, then c_step_v2 p n hp (k + 1) k = c_step_v2 p n hp k k - (decompose_even_pow2 (c_step_v2 p n hp k k)).sum id.
      have h_step_k_ge_m : c_step_v2 p n hp (k + 1) k = if c_step_v2 p n hp k k > 1 then c_step_v2 p n hp k k - (decompose_even_pow2 (c_step_v2 p n hp k k)).sum id else c_step_v2 p n hp k k := by
        simp +zetaDelta at *;
        rw [ show c_step_v2 p n hp ( k + 1 ) = step_transform_v2 p n hp ( c_step_v2 p n hp k ) k from rfl ];
        unfold step_transform_v2;
        split_ifs <;> simp_all +decide [ Nat.sub_sub ];
        · omega;
        · omega;
      split_ifs at h_step_k_ge_m <;> simp_all +decide;
      have h_decomp_sum : ∀ x, x > 1 → ∑ s ∈ decompose_even_pow2 x, s = x ∨ ∑ s ∈ decompose_even_pow2 x, s = x - 1 := by
        unfold decompose_even_pow2;
        intro x hx; split_ifs <;> simp_all +decide [ Nat.even_iff, Nat.odd_iff ] ;
        · have h_bitIndices_sum : ∀ x, ∑ s ∈ (List.map (fun x => 2 ^ x) x.bitIndices).toFinset, s = x := by
            intro x; induction' x using Nat.strong_induction_on with x ih; rcases Nat.even_or_odd' x with ⟨ c, rfl | rfl ⟩ <;> simp_all +decide [ Nat.pow_succ', Nat.mul_mod, Nat.add_mod ] ;
            · have h_bitIndices_sum : ∑ s ∈ (List.map (fun x => 2 ^ (x + 1)) c.bitIndices).toFinset, s = 2 * ∑ s ∈ (List.map (fun x => 2 ^ x) c.bitIndices).toFinset, s := by
                rw [ Finset.mul_sum _ _ _ ];
                refine' Finset.sum_bij ( fun x hx => x / 2 ) _ _ _ _ <;> simp_all +decide [ Nat.pow_succ', Nat.mul_mod, Nat.add_mod ];
              rcases c with ( _ | _ | c ) <;> simp_all +arith +decide;
              exact h_bitIndices_sum;
            · have := ih c ( by linarith ) ; simp_all +decide [ Function.comp, Finset.sum_add_distrib, pow_succ', mul_assoc, mul_comm, mul_left_comm ] ;
              rw [ show ( List.map ( ( fun x => 2 ^ x ) ∘ fun x => x + 1 ) c.bitIndices ).toFinset = Finset.image ( fun x => 2 ^ ( x + 1 ) ) ( List.toFinset c.bitIndices ) by ext; aesop ] ; rw [ Finset.sum_image ] <;> simp_all +decide [ pow_succ', mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ; ring_nf;
              rw [ ← Finset.sum_mul _ _ _, show ( List.map ( fun x => 2 ^ x ) c.bitIndices ).toFinset = c.bitIndices.toFinset.image ( fun x => 2 ^ x ) by ext; aesop ] at * ; aesop;
          exact Or.inl <| h_bitIndices_sum x;
        · have h_decomp_sum : ∑ s ∈ (Nat.bitIndices (x - 1)).toFinset.image (fun i => 2 ^ i), s = x - 1 := by
            have h_decomp_sum : ∀ n, ∑ s ∈ (Nat.bitIndices n).toFinset.image (fun i => 2 ^ i), s = n := by
              intro n; rw [ Finset.sum_image ] <;> norm_num;
            apply h_decomp_sum;
          convert Or.inr h_decomp_sum using 2;
          congr! 1;
          ext; simp [Finset.mem_image];
      cases h_decomp_sum _ ‹_› <;> omega

/-
For any scalar s used in step k (v2), the target index is strictly greater than k.
-/
theorem target_index_gt_source_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) :
  ∀ s ∈ used_s_v2 p n hp k, target_index p k s > k := by
    exact fun s hs => target_index_gt_self p hp.2 k s ( used_s_v2_properties p n hp k s hs |>.2 ) ( used_s_v2_properties p n hp k s hs |>.1 )

/-
The coefficients at step k+1 (v3) are obtained from step k by subtracting the sum of used scalars from index k and adding 1 to target indices.
-/
noncomputable def step_transform_v3 (p n : ℕ) (hp : Odd p ∧ p > 1) (c : ℕ → ℕ) (k : ℕ) : ℕ → ℕ :=
  if k < m p n hp - 1 then
    -- Use S
    let s_decomp := decompose_S p hp (c k)
    fun i =>
      if i = k then c k - s_decomp.sum id
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

noncomputable def c_step_v3 (p n : ℕ) (hp : Odd p ∧ p > 1) : ℕ → ℕ → ℕ
| 0 => c_init p n hp
| k + 1 => step_transform_v3 p n hp (c_step_v3 p n hp k) k

noncomputable def used_s_v3 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Finset ℕ :=
  let c := c_step_v3 p n hp j j
  if j < m p n hp - 1 then
    decompose_S p hp c
  else
    if c > 1 then decompose_even_pow2 c else ∅

theorem c_step_v3_succ_eq (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) :
  let c := c_step_v3 p n hp k
  let s_decomp := used_s_v3 p n hp k
  (c_step_v3 p n hp (k + 1) k = c k - s_decomp.sum id) ∧
  (∀ i, i ≠ k → c_step_v3 p n hp (k + 1) i = c i + if ∃ s ∈ s_decomp, target_index p k s = i then 1 else 0) := by
    -- We unfold c_step_v3 (k+1) and used_s_v3 k to match the goal.
    simp [c_step_v3, used_s_v3] at *;
    unfold step_transform_v3; split_ifs <;> simp_all +decide [ Finset.sum_range_succ' ] ;

/-
The scalars used in step j (v3) are in A_p and strictly greater than 1.
-/
theorem used_s_v3_properties (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) :
  ∀ s ∈ used_s_v3 p n hp j, s ∈ A p ∧ s > 1 := by
    unfold used_s_v3;
    split_ifs <;> simp +decide [ * ];
    · exact fun s a ↦ decompose_S_properties p hp (c_step_v3 p n hp j j) s a;
    · split_ifs <;> simp_all +decide [ decompose_even_pow2 ];
      split_ifs <;> simp_all +decide [ A ];
      · intro a ha
        have h_bit : a ∈ Nat.bitIndices (c_step_v3 p n hp j j) := by
          assumption;
        rcases a with ( _ | a ) <;> simp_all +decide [ Nat.pow_succ', Nat.mul_assoc ];
        · rw [ Nat.even_iff ] at *; rw [ ← Nat.mod_add_div ( c_step_v3 p n hp j j ) 2 ] at *; simp_all +decide [ Nat.add_mod, Nat.mul_mod ] ;
        · exact ⟨ a + 1, 0, by ring ⟩;
      · intro a ha; refine' ⟨ ⟨ a, 0, by ring ⟩, _ ⟩ ; intro ha'; simp_all +decide [ Nat.even_sub ( show 1 ≤ c_step_v3 p n hp j j from by linarith ) ] ;
        cases ‹Odd ( c_step_v3 p n hp j j ) › ; aesop

/-
Definitions of the invariant properties for the v3 algorithm.
-/
def CoeffBound_v3 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ K p →
    ∀ i, in_interval p n hp k i →
      c_step_v3 p n hp j i ≤ M p k

def IsTarget_v3 (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ) : Prop :=
  ∃ s ∈ used_s_v3 p n hp j, target_index p j s = i

def UpdateConditionUpTo_v3 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Prop :=
  ∀ i' < j, ∀ i, IsTarget_v3 p n hp i' i →
    ∀ k, 1 ≤ k → k ≤ K p →
      in_interval p n hp k i →
      (k ≥ 3 → i' > v p n hp (k - 2))

def Lemma3_invariant_v3 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Prop :=
  CoeffBound_v3 p n hp j ∧ UpdateConditionUpTo_v3 p n hp j

/-
The invariant holds at the start (step 0).
-/
theorem lemma_invariant_v3_base (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) :
  Lemma3_invariant_v3 p n hp 0 := by
    have := @lemma_invariant_holds;
    unfold Lemma3_invariant_v3;
    unfold CoeffBound_v3 UpdateConditionUpTo_v3; specialize this p n hp hn 0; unfold Lemma3_invariant at this; aesop;

/-
For k >= 2, u_{k+1} is 2 to the power of log2(M_k).
-/
theorem lemma_u_eq_pow2_log2_M (p : ℕ) (k : ℕ) (hk : k ≥ 2) :
  u p (k + 1) = 2 ^ (Nat.log2 (M p k)) := by
    rcases k with ( _ | _ | k ) <;> aesop

/-
For 1 <= k < K, M_k is strictly greater than 1.
-/
theorem M_gt_one_of_lt_K (p : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk_lower : 1 ≤ k) (hk_upper : k < K p) :
  M p k > 1 := by
    -- Since $k < K$, by definition of $K$, we have $M p k > 1$. Use this fact.
    have h_Mp_k_gt_1 : ∀ k < K p, k ≥ 1 → M p k > 1 := by
      intros k hk_lt_K hk_ge_1
      by_cases hk : k < 2;
      · interval_cases k ; simp_all +decide;
        unfold M; simp_all +decide [ M_0 ] ;
        refine' lt_add_of_pos_of_le _ _;
        · have := Exists.choose_spec ( show ∃ x : ℕ, Odd x ∧ 1 < x ∧ x ≤ 1000 ∧ x ≠ p from by
                                        exact ⟨ if p = 3 then 5 else 3, by split_ifs <;> norm_num, by split_ifs <;> norm_num, by split_ifs <;> linarith, by split_ifs <;> aesop_cat ⟩ )
          generalize_proofs at *;
          exact ‹∃ M₀ ≤ p, 0 < M₀ ∧ ∀ x a, x ≤ M₀ + _ → is_sum_of_distinct_elements _ x›.choose_spec.2.1;
        · refine' Finset.card_pos.mpr _;
          exact Exists.imp ( by aesop ) ( exists_odd_in_S p hp );
      · -- Since $k \geq 2$ and $k < K$, by definition of $K$, we have $M p k > 1$.
        have h_Mp_k_gt_1 : ∀ k, 2 ≤ k → k < K p → M p k > 1 := by
          intros k hk_ge_2 hk_lt_K;
          unfold K at hk_lt_K; aesop;
        exact h_Mp_k_gt_1 k ( le_of_not_gt hk ) hk_lt_K;
    exact h_Mp_k_gt_1 k hk_upper hk_lower

/-
If a power of 2 is less than or equal to N, it is less than or equal to 2^(log2 N).
-/
theorem lemma_pow2_le_log2_bound (s N : ℕ) (hs : ∃ r, s = 2^r) (h_le : s <= N) (hN : N > 0) :
  s <= 2 ^ (Nat.log2 N) := by
    rcases hs with ⟨ r, rfl ⟩;
    rw [ pow_le_pow_iff_right₀ ( by norm_num ) ];
    rw [ Nat.le_log2 ] <;> linarith

/-
If a power of 2 is bounded by M_k (for k >= 2), it is bounded by u_{k+1}.
-/
theorem lemma_pow2_le_M_imp_le_u_next (p : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : k ≥ 2) (s : ℕ) (hs_pow2 : ∃ r, s = 2^r) (hs_le : s ≤ M p k) :
  s ≤ u p (k + 1) := by
    -- Apply lemma_pow2_le_log2_bound to conclude that s ≤ 2^(Nat.log2 (M p k)).
    have h_log2 : s ≤ 2 ^ (Nat.log2 (M p k)) := by
      obtain ⟨r, hr⟩ : ∃ r, s = 2^r := hs_pow2;
      rw [ hr, Nat.le_iff_lt_or_eq ];
      refine' lt_or_eq_of_le ( Nat.pow_le_pow_right ( by decide ) _ );
      rw [ Nat.le_log2 ] <;> aesop;
    exact h_log2.trans ( by simp [ lemma_u_eq_pow2_log2_M p k hk ] )

/-
For indices j >= m-1, the scalars used in step j (v3) are powers of 2 and bounded by the coefficient.
-/
theorem lemma_used_s_v3_bound_and_pow2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (hj : j ≥ m p n hp - 1) :
  ∀ s ∈ used_s_v3 p n hp j, s ≤ c_step_v3 p n hp j j ∧ ∃ r, s = 2^r := by
    -- By definition of used_s_v3, if j ≥ m-1, then used_s_v3 p n hp j is either empty or a decomposition of c_step_v3 p n hp j j into even powers of 2.
    by_cases h : c_step_v3 p n hp j j > 1;
    · unfold used_s_v3;
      field_simp;
      split_ifs <;> simp_all +decide [ decompose_even_pow2 ];
      · omega;
      · split_ifs <;> simp_all +decide [ Nat.le_log_iff_pow_le ];
        · intro a ha;
          exact Nat.two_pow_le_of_mem_bitIndices ha;
        · intro a ha;
          have h_bit : 2 ^ a ≤ c_step_v3 p n hp j j - 1 := by
            exact Nat.two_pow_le_of_mem_bitIndices ha;
          exact le_trans h_bit ( Nat.pred_le _ );
    · unfold used_s_v3;
      grind

/-
For intervals k >= 2, the scalars used are bounded by u_{k+1}.
-/
theorem lemma_scalar_bound_v3_ge2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (k : ℕ) (hk : 2 ≤ k ∧ k < K p) (hj : in_interval p n hp k j)
  (hc_upper : CoeffBound_v3 p n hp j) :
  ∀ s ∈ used_s_v3 p n hp j, s ≤ u p (k + 1) := by
    -- Since k ≥ 2, we have j ≥ m (by j_ge_m_of_in_interval_ge_2).
    have hj_ge_m : j ≥ m p n hp := by
      exact j_ge_m_of_in_interval_ge_2 p n hp j k hk.1 hj;
    -- By lemma_used_s_v3_bound_and_pow2, for any s in used_s_v3 j, s <= c_step_v3 j j and s is a power of 2.
    have hs_le_c_step_v3 : ∀ s ∈ used_s_v3 p n hp j, s ≤ c_step_v3 p n hp j j ∧ ∃ r, s = 2^r := by
      intros s hs
      apply lemma_used_s_v3_bound_and_pow2 p n hp j (by
      exact Nat.sub_le_of_le_add <| by linarith;) s hs;
    -- By CoeffBound_v3, c_step_v3 j j <= M p k.
    have hc_step_v3_le_M : c_step_v3 p n hp j j ≤ M p k := by
      exact hc_upper k ( by linarith ) ( by linarith ) j hj;
    intros s hs; obtain ⟨ hs₁, ⟨ r, rfl ⟩ ⟩ := hs_le_c_step_v3 s hs; exact lemma_pow2_le_M_imp_le_u_next p hp k hk.1 _ ⟨ r, rfl ⟩ ( by linarith ) ;

/-
For intervals k >= 2, the scalars used are powers of 2 and bounded by M_k.
-/
theorem lemma_s_le_M_of_in_interval_ge2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (k : ℕ) (hk : 2 ≤ k ∧ k < K p) (hj : in_interval p n hp k j)
  (hc_upper : CoeffBound_v3 p n hp j) :
  ∀ s ∈ used_s_v3 p n hp j, s ≤ M p k ∧ ∃ r, s = 2^r := by
    -- By definition of used_s_v3, we know that s is either in decompose_S p hp (c_step_v3 p n hp j j) if j < m p n hp - 1, or in decompose_even_pow2 (c_step_v3 p n hp j j) if c_step_v3 p n hp j j > 1.
    intros s hs
    by_cases h_case : j < m p n hp - 1;
    · by_contra hk_gt_1;
      exact h_case.not_ge ( Nat.le_of_not_gt fun h => by have := j_ge_m_of_in_interval_ge_2 p n hp j k ( by linarith ) hj; omega );
    · have h_bound : s ≤ c_step_v3 p n hp j j ∧ ∃ r, s = 2^r := by
        apply_rules [ lemma_used_s_v3_bound_and_pow2 ];
        exact le_of_not_gt h_case;
      exact ⟨ h_bound.1.trans ( hc_upper k ( by linarith ) ( by linarith ) j hj ), h_bound.2 ⟩

/-
The sum of the scalars used in step j (v3) is at most the coefficient at index j.
-/
theorem used_s_v3_sum_le (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) :
  (used_s_v3 p n hp j).sum id ≤ c_step_v3 p n hp j j := by
    -- By definition of used_s_v3, we have two cases: j < m-1 and j ≥ m-1.
    by_cases hj : j < m p n hp - 1;
    · -- In this case, the sum of the scalars used is equal to the coefficient because the decomposition using S covers all possible scalars up to the coefficient.
      have h_sum_eq_coeff : ∀ x, (decompose_S p hp x).sum id ≤ x := by
        intro x;
        have := decompose_S_spec p hp x;
        contrapose! this;
        unfold decompose_S at *; aesop;
      unfold used_s_v3; aesop;
    · by_cases h : c_step_v3 p n hp j j > 1 <;> simp_all +decide [ used_s_v3 ];
      · rw [ if_neg ( by omega ) ];
        have := decompose_even_pow2_spec ( c_step_v3 p n hp j j ) h; aesop;
      · grind

/-
For any scalar s used in step k (v3), the target index is strictly greater than k.
-/
theorem target_index_gt_source_v3 (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) :
  ∀ s ∈ used_s_v3 p n hp k, target_index p k s > k := by
    intros s h; exact ( target_index_gt_self p hp.2 k s (used_s_v3_properties p n hp k s h).right (used_s_v3_properties p n hp k s h).left ) ;

/-
If the sequence value at k is bounded by the P-bound of interval k_idx, and the scalar s is bounded by u_{k_idx+1}, then the target index is bounded by v_{k_idx+1}.
-/
theorem target_index_bound_by_v (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (k_idx : ℕ) (s : ℕ)
  (hk_idx : 1 ≤ k_idx ∧ k_idx < K p)
  (h_val : a_seq p k ≤ P p k_idx * a_seq p (m p n hp - 1))
  (hs : s ≤ u p (k_idx + 1))
  (hs_in_A : s ∈ A p) :
  target_index p k s ≤ v p n hp (k_idx + 1) := by
    have h_mul : s * a_seq p k ≤ u p (k_idx + 1) * (P p k_idx * a_seq p (m p n hp - 1)) := by
      gcongr;
    apply index_in_A_mono p hp.2;
    · exact A_mul_closed p s ( a_seq p k ) hs_in_A ( a_seq_mem p hp.2 k );
    · exact A_mul_closed p _ _ ( P_mem_A p hp k_idx.succ ) ( a_seq_mem p hp.2 _ );
    · convert h_mul using 1 ; rw [ show P p ( k_idx + 1 ) = P p k_idx * u p ( k_idx + 1 ) from ?_ ] ; ring;
      exact Finset.prod_range_succ _ _

/-
If j is in the last interval K, then j is at least m - 1.
-/
theorem j_ge_m_sub_1_of_in_interval_K (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (hj : in_interval p n hp (K p) j) :
  j ≥ m p n hp - 1 := by
    unfold in_interval at hj;
    split_ifs at hj;
    · exact absurd ‹K p = 1› ( by linarith [ K_ge_2 p ] );
    · -- By definition of $v$, we know that $v_{K-1} \geq v_1$.
      have hv_ge_v1 : v p n hp (K p - 1) ≥ v p n hp 1 := by
        have hv_ge_v1 : ∀ k, 1 ≤ k → k < K p → v p n hp k ≥ v p n hp 1 := by
          intros k hk1 hk2
          induction' hk1 with k hk ih;
          · rfl;
          · exact le_trans ( ih ( Nat.lt_of_succ_lt hk2 ) ) ( Nat.le_of_lt ( v_strict_mono p n hp k ⟨ hk, Nat.lt_of_succ_lt hk2 ⟩ ) );
        grind;
      exact le_trans ( by linarith [ v_1_eq_m_sub_1 p n hp ] ) ( le_of_lt hj.1 )

/-
If j is in the last interval K, and coefficients satisfy the bound, then used_s is empty.
-/
theorem used_s_empty_of_in_interval_K_v3 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (hc_upper : c_step_v3 p n hp j j ≤ M p (K p)) (hj : in_interval p n hp (K p) j) :
  used_s_v3 p n hp j = ∅ := by
    unfold used_s_v3;
    have h_M_K_le_one : M p (K p) ≤ 1 := by
      exact M_K_le_one p hp;
    have h_j_ge_m_sub_1 : j ≥ m p n hp - 1 := by
      exact j_ge_m_sub_1_of_in_interval_K p n hp j hj;
    grind

/-
The coefficient at index i does not change during step j if i < j.
-/
theorem c_step_stable_v3 (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ) (h : i < j) :
  c_step_v3 p n hp (j + 1) i = c_step_v3 p n hp j i := by
    -- By definition of `c_step_v3`, we have:
    have h_step_def : c_step_v3 p n hp (j + 1) i = c_step_v3 p n hp j i + (if ∃ s ∈ used_s_v3 p n hp j, target_index p j s = i then 1 else 0) := by
      -- By definition of `c_step_v3`, we have `c_step_v3 (j + 1) i = c_step_v3 j i + if ∃ s ∈ used_s_v3 j, target_index p j s = i then 1 else 0`.
      apply (c_step_v3_succ_eq p n hp j).right;
      grind;
    -- Since $i < j$, there cannot be any $s \in \text{used\_s\_v3 } p n hp j$ such that $\text{target\_index } p j s = i$.
    have h_no_target : ¬∃ s ∈ used_s_v3 p n hp j, target_index p j s = i := by
      exact fun ⟨ s, hs₁, hs₂ ⟩ => h.not_ge <| hs₂ ▸ target_index_gt_source_v3 p n hp j s hs₁ |> le_of_lt;
    aesop

/-
Definition of the final coefficient at index i for the v3 algorithm.
-/
noncomputable def c_final_v3 (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) : ℕ :=
  c_step_v3 p n hp (final_step_index p n hp) i

/-
Definition of the final summands for the v3 algorithm.
-/
noncomputable def final_summands_v3 (p n : ℕ) (hp : Odd p ∧ p > 1) : List ℕ :=
  ((List.range (final_step_index p n hp)).filter (fun i => c_final_v3 p n hp i = 1)).map (a_seq p)

/-
The contributing scalars for an index i < m-1 are a subset of S.
-/
noncomputable def contributing_s_v3 (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) : Finset ℕ :=
  (Finset.range i).biUnion (fun j => (used_s_v3 p n hp j).filter (fun s => target_index p j s = i))

theorem contributing_s_v3_subset_S (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (hi : i < m p n hp - 1) :
  contributing_s_v3 p n hp i ⊆ S p := by
    -- By definition of contributing_s_v3, we know that for any j < i, used_s_v3 p n hp j is a subset of S p.
    have h_used_s_subset_S : ∀ j < i, used_s_v3 p n hp j ⊆ S p := by
      intros j hj;
      -- Since $j < i < m p n hp - 1$, we have $j < m p n hp - 1$. Therefore, $used_s_v3 p n hp j$ is defined as $decompose_S p hp (c_step_v3 p n hp j j)$.
      have h_used_s_v3_def : used_s_v3 p n hp j = decompose_S p hp (c_step_v3 p n hp j j) := by
        exact if_pos ( by linarith );
      exact h_used_s_v3_def ▸ decompose_S_subset_S p hp _;
    unfold contributing_s_v3; aesop_cat;

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
If the target a_k is a power of 2, then p cannot be a contributing scalar.
-/
theorem lemma_contributing_s_v3_not_p_if_pow2 (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : k < m p n hp - 1)
  (h_pow2 : ∃ r, a_seq p k = 2^r) :
  ∀ s ∈ contributing_s_v3 p n hp k, s ≠ p := by
    intro s hs hsp
    obtain ⟨j, hj_lt_k, hj_used⟩ : ∃ j < k, s ∈ used_s_v3 p n hp j ∧ target_index p j s = k := by
      unfold contributing_s_v3 at hs; aesop;
    exact absurd ( lemma_scalar_neq_p_of_pow2 p n hp j k s h_pow2 hsp hj_used.2 ) ( by aesop )

/-
For a fixed target i and scalar s, there is at most one step j where s is used to target i.
-/
theorem unique_source_for_s_v3 (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (s : ℕ) :
  Set.Subsingleton { j | s ∈ used_s_v3 p n hp j ∧ target_index p j s = i } := by
    intro j₁ hj₁ j₂ hj₂;
    have := lemma_target_index_inj_j p hp.2 s ( by
      exact Nat.pos_of_ne_zero ( by have := hj₁.1; have := used_s_v3_properties p n hp j₁ s this; aesop ) ) ( by
      exact used_s_v3_properties p n hp j₁ s hj₁.1 |>.1 ) j₁ j₂; aesop;

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
The sets of contributing scalars from different steps j1 and j2 targeting the same index k are disjoint.
-/
theorem contributing_scalars_disjoint (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (j1 j2 : ℕ) (h_neq : j1 ≠ j2) :
  Disjoint ((used_s_v3 p n hp j1).filter (fun s => target_index p j1 s = k))
           ((used_s_v3 p n hp j2).filter (fun s => target_index p j2 s = k)) := by
             -- If there were a common element s, then s would satisfy the target index condition for both j1 and j2.
             by_contra h_contra;
             obtain ⟨ s, hs1, hs2 ⟩ := Finset.not_disjoint_iff.mp h_contra;
             have := unique_source_for_s_v3 p n hp k s; simp_all +decide [ Set.Subsingleton ] ;
             exact h_neq ( this hs1.1 hs1.2 hs2.1 hs2.2 )

/-
The number of scalars in step j targeting k is 1 if such a scalar exists, and 0 otherwise.
-/
theorem card_filter_target_eq (p n : ℕ) (hp : Odd p ∧ p > 1) (j k : ℕ) :
  ((used_s_v3 p n hp j).filter (fun s => target_index p j s = k)).card =
  if ∃ s ∈ used_s_v3 p n hp j, target_index p j s = k then 1 else 0 := by
    split_ifs with h;
    · obtain ⟨ s, hs₁, hs₂ ⟩ := h;
      have h_unique : ∀ s' ∈ used_s_v3 p n hp j, target_index p j s' = k → s' = s := by
        intros s' hs' hs'_eq;
        apply_rules [ lemma_scalar_unique_for_target_j ];
        · linarith;
        · exact Nat.pos_of_ne_zero ( by rintro rfl; exact absurd ( used_s_v3_properties p n hp j 0 hs' ) ( by aesop ) );
        · exact used_s_v3_properties p n hp j s' hs' |>.1;
        · exact Nat.pos_of_ne_zero fun h => by have := used_s_v3_properties p n hp j s hs₁; aesop;
        · exact used_s_v3_properties p n hp j s hs₁ |>.1;
      exact Finset.card_eq_one.mpr ⟨ s, by ext; aesop ⟩;
    · aesop

/-
The coefficient at step k is the initial coefficient plus the number of contributing scalars.
-/
theorem c_step_v3_eq_init_plus_card (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) :
  c_step_v3 p n hp k k = c_init p n hp k + (contributing_s_v3 p n hp k).card := by
    -- By definition of `contributing_s_v3`, the cardinality of the contribution is the sum of the targets.
    have h_card_contribution : (contributing_s_v3 p n hp k).card = ∑ j ∈ Finset.range k, (if ∃ s ∈ used_s_v3 p n hp j, target_index p j s = k then 1 else 0) := by
      have h_card_contribution : (contributing_s_v3 p n hp k).card = Finset.sum (Finset.range k) (fun j => ((used_s_v3 p n hp j).filter (fun s => target_index p j s = k)).card) := by
        rw [ ← Finset.card_biUnion ];
        · rfl;
        · intros j hj j' hj' hij; exact (by
          apply_rules [ contributing_scalars_disjoint ]);
      rw [ h_card_contribution ];
      apply Finset.sum_congr rfl;
      intros j hj
      apply card_filter_target_eq;
    -- By definition of `c_step_v3`, the coefficient at step k is given by `c_step_v3 p n hp k k`.
    have h_coeff : ∀ j ≤ k, c_step_v3 p n hp j k = c_init p n hp k + ∑ j' ∈ Finset.range j, (if ∃ s ∈ used_s_v3 p n hp j', target_index p j' s = k then 1 else 0) := by
      intro j hj
      induction' j with j ih;
      · rfl;
      · rw [ Finset.sum_range_succ ];
        rw [ ← add_assoc, ← ih ( Nat.le_of_succ_le hj ), c_step_v3_succ_eq p n hp j |>.2 ];
        linarith;
    rw [ h_coeff k le_rfl, h_card_contribution ]

/-
If a_k is a power of 2, the number of contributing scalars is at most |S| - 1.
-/
theorem lemma_card_contributing_le_S_sub_one_if_pow2_v3 (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : k < m p n hp - 1)
  (h_pow2 : ∃ r, a_seq p k = 2^r) :
  (contributing_s_v3 p n hp k).card ≤ (S p).card - 1 := by
    have h_subset : contributing_s_v3 p n hp k ⊆ S p := by
      exact contributing_s_v3_subset_S p n hp k hk;
    -- Since there exists an element x in S that is not a power of 2, x cannot be in contributing_s_v3 k.
    obtain ⟨x, hx⟩ : ∃ x ∈ S p, ¬∃ r, x = 2 ^ r := by
      have h_exists_non_pow2 : ∃ x ∈ S p, ¬∃ r, x = 2^r := by
        have := exists_non_pow2_in_S p hp
        aesop;
      exact h_exists_non_pow2;
    refine' Nat.le_sub_one_of_lt ( Finset.card_lt_card _ );
    refine' ⟨ h_subset, _ ⟩;
    intro h; have := h hx.1; simp_all +decide [ contributing_s_v3 ] ;
    obtain ⟨ j, hj₁, hj₂, hj₃ ⟩ := this; have := used_s_v3_properties p n hp j x hj₂; simp_all +decide [ target_index ] ;
    have h_contra : a_seq p k = x * a_seq p j := by
      have h_eq : a_seq p (index_in_A p (x * a_seq p j)) = x * a_seq p j := by
        exact a_seq_index_in_A p hp.2 ( x * a_seq p j ) ( s_mul_a_seq_mem_A p hp.2 x this.1 j )
      aesop;
    obtain ⟨ r, hr ⟩ := h_pow2; simp_all +decide [ Nat.pow_succ', Nat.mul_assoc ] ;
    have : x ∣ 2 ^ r := h_contra.symm ▸ dvd_mul_right _ _; ( erw [ Nat.dvd_prime_pow ( by decide ) ] at this; aesop; )

/-
For k < m-1, the coefficient at step k is bounded by M_0 + |S|.
-/
theorem c_step_v3_bound_lt_m (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : k < m p n hp - 1) :
  c_step_v3 p n hp k k ≤ M_0 p + (S p).card := by
    -- Use `c_step_v3_eq_init_plus_card` to write `c_step_v3 k k = c_init k + (contributing_s_v3 k).card`.
    have h_eq : c_step_v3 p n hp k k = c_init p n hp k + (contributing_s_v3 p n hp k).card := by
      exact c_step_v3_eq_init_plus_card p n hp k
    rw [h_eq] at *; (
    -- By `c_init_bounds_lt_m`, `c_init k ≤ M_0 p + 1`.
    have h_c_init_bound : c_init p n hp k ≤ M_0 p + 1 := by
      exact c_init_bounds_lt_m p n hp k hk |>.2
    generalize_proofs at *; (
    by_cases h_case : c_init p n hp k > M_0 p;
    · -- By `ak_is_pow2_of_gt_M0`, `a_seq p k` is a power of 2.
      have h_ak_pow2 : ∃ r, a_seq p k = 2^r := by
        apply ak_is_pow2_of_gt_M0 p n hp k hk h_case
      generalize_proofs at *; (
      -- By `lemma_card_contributing_le_S_sub_one_if_pow2_v3`, `(contributing_s_v3 k).card ≤ (S p).card - 1`.
      have h_card_bound : (contributing_s_v3 p n hp k).card ≤ (S p).card - 1 := by
        apply lemma_card_contributing_le_S_sub_one_if_pow2_v3 p n hp k hk h_ak_pow2
      generalize_proofs at *; (exact by linarith [Nat.sub_add_cancel (show 1 ≤ (S p).card from by
                                                                        refine' Finset.card_pos.mpr _;
                                                                        exact S_nonempty p hp)]));
    · exact add_le_add ( le_of_not_gt h_case ) ( Finset.card_le_card ( contributing_s_v3_subset_S p n hp k hk ) )))

/-
After step k, the coefficient at index k is at most 1.
-/
theorem c_step_v3_at_k_le_one (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) :
  c_step_v3 p n hp (k + 1) k ≤ 1 := by
    -- By definition of step_transform_v3, if k < m - 1, then the sum of the used scalars is equal to c_step_v3 k k, making the new coefficient zero. If k ≥ m - 1, then the sum is either c_step_v3 k k or c_step_v3 k k - 1, making the new coefficient 0 or 1.
    have h_step_transform : c_step_v3 p n hp (k + 1) k = c_step_v3 p n hp k k - (used_s_v3 p n hp k).sum id := by
      exact c_step_v3_succ_eq p n hp k |>.1;
    by_cases hk : k < m p n hp - 1;
    · have h_sum_eq : (used_s_v3 p n hp k).sum id = c_step_v3 p n hp k k := by
        rw [ used_s_v3 ];
        rw [ if_pos hk, decompose_S ];
        have h_decomp_S : c_step_v3 p n hp k k ≥ M_0 p := by
          have h_decomp_S : c_step_v3 p n hp k k = c_init p n hp k + (contributing_s_v3 p n hp k).card := by
            exact c_step_v3_eq_init_plus_card p n hp k;
          exact h_decomp_S.symm ▸ le_add_of_le_of_nonneg ( c_init_bounds_lt_m p n hp k hk |>.1 ) ( Nat.zero_le _ )
        have h_decomp_S_le : c_step_v3 p n hp k k ≤ M_0 p + (S p).card := by
          apply c_step_v3_bound_lt_m; assumption
        generalize_proofs at *;
        split_ifs ; simp_all +decide [ Finset.subset_iff ];
        · exact ‹M_0 p ≤ c_step_v3 p n hp k k ∧ c_step_v3 p n hp k k ≤ M_0 p + ( S p ).card → ∃ s ⊆ S p, s.sum id = c_step_v3 p n hp k k› ‹_› |> Exists.choose_spec |> And.right;
        · aesop;
      aesop;
    · by_cases hk : c_step_v3 p n hp k k > 1;
      · have h_sum : (used_s_v3 p n hp k).sum id = if ∑ x ∈ decompose_even_pow2 (c_step_v3 p n hp k k), x = c_step_v3 p n hp k k then c_step_v3 p n hp k k else c_step_v3 p n hp k k - 1 := by
          rw [ used_s_v3 ];
          rw [ decompose_even_pow2 ];
          split_ifs <;> simp_all +decide [ Nat.even_iff ];
          · have h_sum : ∑ x ∈ (List.map (fun x => 2 ^ x) (c_step_v3 p n hp k k).bitIndices).toFinset, x = c_step_v3 p n hp k k := by
              have h_sum : ∀ n : ℕ, ∑ x ∈ (List.map (fun x => 2 ^ x) (Nat.bitIndices n)).toFinset, x = n := by
                intro n; induction' n using Nat.strong_induction_on with n ih; rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.bitIndices ] ;
                rw [ Nat.binaryRec ] ; simp +arith +decide [ * ];
                cases Nat.mod_two_eq_zero_or_one n <;> simp_all +decide [ Nat.shiftRight_eq_div_pow ];
                · convert congr_arg ( · * 2 ) ( ih ( n / 2 + 1 ) ( by linarith [ Nat.mod_add_div n 2 ] ) ) using 1;
                  · rw [ Finset.sum_mul _ _ _ ];
                    refine' Finset.sum_bij ( fun x hx => x / 2 ) _ _ _ _ <;> simp_all +decide [ Nat.pow_succ', Nat.mul_div_assoc ];
                    exact fun _ _ => mul_comm _ _;
                  · linarith [ Nat.mod_add_div n 2 ];
                · have := ih ( n / 2 + 1 ) ( by linarith [ Nat.mod_add_div n 2 ] ) ; simp_all +arith +decide [ Function.comp, Finset.sum_add_distrib, pow_succ' ] ;
                  convert congr_arg ( fun x => 1 + x * 2 ) this using 1;
                  · rw [ Finset.sum_mul _ _ _ ] ; simp +decide [ Function.comp, pow_succ' ];
                    refine' Finset.sum_bij ( fun x hx => x / 2 ) _ _ _ _ <;> simp_all +decide [ Function.comp, pow_succ' ];
                    exact fun _ _ => mul_comm _ _;
                  · linarith [ Nat.mod_add_div n 2 ];
              apply h_sum;
            contradiction;
          · have h_sum : ∀ x, ∑ i ∈ (Nat.bitIndices x).toFinset, 2 ^ i = x := by
              intro x; rw [ ← Nat.ofDigits_digits 2 x ] ; simp +decide [ Nat.ofDigits_eq_foldr ] ;
            rw [ List.sum_toFinset ];
            · norm_num;
              convert h_sum ( c_step_v3 p n hp k k - 1 ) using 1;
              rw [ List.sum_toFinset ];
              · rfl;
              · -- The bit indices of a number are unique, so the list is nodup.
                have h_bit_indices_unique : ∀ x : ℕ, List.Nodup (Nat.bitIndices x) := by
                  intro x; exact (by
                  induction' x using Nat.binaryRec with b x ih;
                  · native_decide +revert;
                  · cases b <;> simp_all +decide [ Nat.bit ];
                    · exact List.Nodup.map ( fun x y hxy => by simpa using hxy ) ih;
                    · exact List.Nodup.map ( fun x y hxy => by simpa using hxy ) ih);
                exact h_bit_indices_unique _;
            · rw [ List.nodup_map_iff_inj_on ];
              · aesop;
              · -- The bit indices of a number are unique, so the list is nodup.
                have h_bit_indices_unique : ∀ x : ℕ, List.Nodup (Nat.bitIndices x) := by
                  intro x; exact (by
                  induction' x using Nat.binaryRec with b x ih;
                  · native_decide +revert;
                  · cases b <;> simp_all +decide [ Nat.bit ];
                    · exact List.Nodup.map ( fun x y hxy => by simpa using hxy ) ih;
                    · exact List.Nodup.map ( fun x y hxy => by simpa using hxy ) ih);
                exact h_bit_indices_unique _;
        split_ifs at h_sum <;> omega;
      · grind +ring

/-
If a power of 2 is a sum of distinct elements from a set containing one odd number and even powers of 2, it must be in the set.
-/
theorem lemma_pow2_in_S_of_covered (p : ℕ) (hp : Odd p) (S : Finset ℕ)
  (h_subset : S ⊆ {p} ∪ (Finset.range (p + (S.card + 1))).filter (fun x => ∃ k > 0, x = 2^k))
  (h_p_in_S : p ∈ S)
  (h_no_one : 1 ∉ S)
  (s : ℕ) (hs_pow2 : ∃ k, s = 2^k) (hs_gt_1 : s > 1)
  (h_covered : is_sum_of_distinct_elements S s) :
  s ∈ S := by
    -- Let $A$ be the subset of $S$ whose elements sum to $s$.
    obtain ⟨A, hA_sub, hA_sum⟩ := h_covered;
    -- Since p is odd and all other elements in S are even, p cannot be in A. Therefore, A must consist of even powers of 2.
    have hA_even : ∀ x ∈ A, x ≠ p := by
      intro x hx hx'; have := h_subset ( hA_sub hx ) ; simp_all +decide [ parity_simps ] ;
      have hA_even : (∑ x ∈ A.erase p, x) % 2 = 0 := by
        have hA_even : ∀ x ∈ A.erase p, x % 2 = 0 := by
          intro x hx; specialize h_subset ( hA_sub ( Finset.mem_of_mem_erase hx ) ) ; aesop;
        exact Nat.mod_eq_zero_of_dvd <| Finset.dvd_sum fun x hx => Nat.dvd_of_mod_eq_zero <| hA_even x hx;
      simp_all +decide [ ← Finset.sum_erase_add _ _ hx ];
      have := congr_arg ( · % 2 ) hA_sum; norm_num [ Nat.add_mod, Nat.pow_mod, hA_even ] at this; obtain ⟨ k, rfl ⟩ := hp; norm_num at this;
      rcases hs_pow2 with ⟨ _ | k, rfl ⟩ <;> norm_num [ Nat.pow_mod ] at *;
    -- Since A consists of even powers of 2, we can write A as {2^{k_1}, 2^{k_2}, ..., 2^{k_m}} for some distinct k_i.
    obtain ⟨ks, hks⟩ : ∃ ks : Finset ℕ, A = Finset.image (fun k => 2 ^ k) ks := by
      have hA_powers_of_two : ∀ x ∈ A, ∃ k, x = 2 ^ k := by
        intro x hx; specialize h_subset ( hA_sub hx ) ; aesop;
      choose! k hk using hA_powers_of_two;
      use Finset.image k A;
      grind;
    -- Since $ks$ is nonempty, let $k$ be the maximum element in $ks$.
    obtain ⟨k, hk_max⟩ : ∃ k, k ∈ ks ∧ ∀ m ∈ ks, m ≤ k := by
      exact ⟨ Finset.max' ks ( Finset.nonempty_of_ne_empty ( by aesop_cat ) ), Finset.max'_mem _ _, fun m hm => Finset.le_max' _ _ hm ⟩;
    -- Since $ks$ is nonempty and $k$ is the maximum element, we have $s = 2^k$.
    have hs_eq_2k : s = 2 ^ k := by
      have hs_eq_2k : s ≤ 2 ^ (k + 1) - 1 := by
        have hs_le_2k : s ≤ Finset.sum (Finset.Ico 0 (k + 1)) (fun m => 2 ^ m) := by
          have hs_le_2k : s ≤ Finset.sum (Finset.image (fun m => 2 ^ m) (Finset.Ico 0 (k + 1))) id := by
            exact hA_sum ▸ Finset.sum_le_sum_of_subset ( hks ▸ Finset.image_subset_image ( fun m hm => Finset.mem_Ico.mpr ⟨ Nat.zero_le m, Nat.lt_succ_of_le ( hk_max.2 m hm ) ⟩ ) );
          rwa [ Finset.sum_image <| by aesop ] at hs_le_2k;
        simpa [ Nat.geomSum_eq ] using hs_le_2k;
      have hs_eq_2k : s ≥ 2 ^ k := by
        exact hA_sum ▸ Finset.single_le_sum ( fun x _ => Nat.zero_le x ) ( hks.symm ▸ Finset.mem_image_of_mem _ hk_max.1 ) |> le_trans ( by aesop );
      obtain ⟨ m, rfl ⟩ := hs_pow2;
      exact le_antisymm ( Nat.le_of_not_lt fun h => by have := Nat.pow_le_pow_right two_pos ( show m ≥ k + 1 from Nat.succ_le_of_lt ( Nat.lt_of_not_ge fun h' => by linarith [ pow_le_pow_right₀ ( show 1 ≤ 2 by decide ) h' ] ) ) ; omega ) hs_eq_2k;
    aesop

/-
Redefinition of intervals and invariants with corrected boundaries.
-/
def in_interval_v4 (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (i : ℕ) : Prop :=
  if k = 1 then i < v p n hp 1
  else v p n hp (k - 1) ≤ i ∧ i < v p n hp k

def CoeffBound_v4 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ K p →
    ∀ i, in_interval_v4 p n hp k i →
      c_step_v3 p n hp j i ≤ M p k

def IsTarget_v4 (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ) : Prop :=
  ∃ s ∈ used_s_v3 p n hp j, target_index p j s = i

def UpdateConditionUpTo_v4 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Prop :=
  ∀ i' < j, ∀ i, IsTarget_v4 p n hp i' i →
    ∀ k, 1 ≤ k → k ≤ K p →
      in_interval_v4 p n hp k i →
      (k ≥ 3 → i' ≥ v p n hp (k - 2))

def Lemma3_invariant_v4 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Prop :=
  CoeffBound_v4 p n hp j ∧ UpdateConditionUpTo_v4 p n hp j

/-
The initial coefficients in the first interval satisfy the bound M_1.
-/
theorem lemma_coeff_bound_v4_k1 (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) :
  ∀ i, in_interval_v4 p n hp 1 i → c_init p n hp i ≤ M p 1 := by
    intro i hi;
    -- By definition of in_interval_v4, we know that i < m - 1.
    have h_lt_m_minus_1 : i < m p n hp - 1 := by
      unfold in_interval_v4 at hi;
      unfold v at hi;
      simp_all +decide [ P ];
      unfold u at hi; simp_all +decide [ List.range_succ ] ;
      exact hi.trans_le ( by unfold index_in_A; aesop );
    have h_coeff_le : c_init p n hp i ≤ M_0 p + 1 := by
      exact c_init_bounds_lt_m p n hp i h_lt_m_minus_1 |>.2;
    refine le_trans h_coeff_le ?_;
    unfold M M_0;
    split_ifs ; simp_all +decide [ S ];
    have := Exists.choose_spec ( show ∃ S : Finset ℕ, S.card = Nat.log2 p + 1 ∧ p ∈ S ∧ ∀ x ∈ S, x = p ∨ ∃ k : ℕ, 0 < k ∧ x = 2 ^ k from ⟨ Finset.image ( fun k => 2 ^ k ) ( Finset.Icc 1 ( Nat.log2 p ) ) ∪ { p }, by
                                  rw [ Finset.card_union_of_disjoint ] <;> norm_num;
                                  · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
                                  · intro x hx₁ hx₂ hx₃; have := hp.1; simp_all +decide [ Nat.even_pow ] ;
                                    exact absurd ( hp.1 ) ( by rw [ ← hx₃ ] ; simp +decide [ Nat.even_pow ] ; linarith ), by
                                  aesop, by
                                  aesop ⟩ );
    all_goals generalize_proofs at *;
    exact ⟨ _, ‹∃ S, ( ∀ x ∈ S, x ∈ A p ∧ ¬x = 1 ) ∧ ( ∀ k : ℕ, 1 ≤ k → 2 ^ k ≤ S.card → 2 ^ k ∈ S ) ∧ ( ∃ M₀ ≤ p, 0 < M₀ ∧ ∀ x : ℕ, M₀ ≤ x → x ≤ M₀ + S.card → is_sum_of_distinct_elements S x ) ∧ S.card ≤ 1 + Nat.clog 2 p ∧ ∃ m ∈ S, p ≤ m ∧ ∀ x ∈ S, x ≤ m ∧ m ≤ 2 ^ Nat.clog 2 p›.choose_spec.2.2.2.2.choose_spec.1 ⟩

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
The sum of coefficients weighted by the sequence values is preserved after one step of the transformation.
-/
theorem c_step_v3_preserves_sum (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ)
  (h_sum : ∑ i ∈ Finset.range (final_step_index p n hp), c_step_v3 p n hp k i * a_seq p i = n)
  (h_range : ∀ s ∈ used_s_v3 p n hp k, target_index p k s < final_step_index p n hp)
  (h_k_lt : k < final_step_index p n hp) :
  ∑ i ∈ Finset.range (final_step_index p n hp), c_step_v3 p n hp (k + 1) i * a_seq p i = n := by
    apply Eq.symm; exact (by
    convert h_sum.symm using 1;
    apply lemma_step_preserves_sum_abstract;
    all_goals try tauto;
    any_goals exact Finset.filter ( fun s => target_index p k s ∈ Finset.range ( final_step_index p n hp ) ) ( used_s_v3 p n hp k );
    all_goals simp_all +decide [ Finset.mem_filter ];
    · exact fun s hs => used_s_v3_properties p n hp k s hs |>.1;
    · exact fun s hs => used_s_v3_properties p n hp k s hs |>.2;
    · exact le_trans ( Finset.sum_le_sum_of_subset ( fun x hx => by aesop ) ) ( used_s_v3_sum_le p n hp k );
    · rw [ Finset.sum_filter ];
      rw [ Finset.sum_congr rfl fun x hx => if_pos ( h_range x hx ) ];
      exact c_step_v3_succ_eq p n hp k |>.1;
    · intro i hi hi'; rw [ show c_step_v3 p n hp ( k + 1 ) i = c_step_v3 p n hp k i + ( if ∃ s ∈ used_s_v3 p n hp k, target_index p k s = i then 1 else 0 ) from ?_ ] ; aesop;
      exact c_step_v3_succ_eq p n hp k |>.2 i ( by tauto ))

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
Scalars used in the first interval are bounded by u_2.
-/
theorem lemma_scalar_bound_v3_k1 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (hj : in_interval_v4 p n hp 1 j) :
  ∀ s ∈ used_s_v3 p n hp j, s ≤ u p 2 := by
    unfold in_interval_v4 at hj;
    unfold used_s_v3;
    split_ifs <;> simp_all +decide [ v_1_eq_m_sub_1 ];
    exact fun s hs => s_in_S_le_u2 p hp s <| decompose_S_subset_S p hp _ hs

/-
For any interval k < K, the scalars used in that interval are bounded by u_{k+1}.
-/
theorem lemma_scalar_bound_v3_all (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (k : ℕ) (hk : 1 ≤ k ∧ k < K p) (hj : in_interval_v4 p n hp k j)
  (hc_upper : CoeffBound_v4 p n hp j) :
  ∀ s ∈ used_s_v3 p n hp j, s ≤ u p (k + 1) := by
    -- Consider two cases: $k = 1$ or $k \geq 2$.
    by_cases hk1 : k = 1;
    · intro s hs;
      -- Since $k = 1$, we have $j < v_1$. By lemma_scalar_bound_v3_k1, any scalar $s$ used in step $j$ satisfies $s \leq u_2$.
      have h_scalar_bound : ∀ s ∈ used_s_v3 p n hp j, s ≤ u p 2 := by
        apply_rules [ lemma_scalar_bound_v3_k1 ];
        aesop;
      aesop;
    · -- Since $k \geq 2$, we have $j \geq m - 1$.
      have hj_ge_m_sub_1 : j ≥ m p n hp - 1 := by
        -- Since $k \geq 2$, we have $v p n hp (k - 1) \geq m p n hp - 1$.
        have hv_ge_m_sub_1 : ∀ k, 2 ≤ k → k ≤ K p → v p n hp (k - 1) ≥ m p n hp - 1 := by
          intros k hk2 hkK;
          have hv_ge_m_sub_1 : ∀ k, 2 ≤ k → k ≤ K p → v p n hp (k - 1) ≥ v p n hp 1 := by
            intros k hk2 hkK;
            apply_rules [ lemma_v_ge_v1 ];
            · exact Nat.le_sub_one_of_lt hk2;
            · omega;
          exact le_trans ( by rw [ v_1_eq_m_sub_1 ] ) ( hv_ge_m_sub_1 k hk2 hkK );
        rcases k with ( _ | _ | k ) <;> simp_all +arith +decide;
        exact le_trans ( hv_ge_m_sub_1 _ ( by linarith ) ( by linarith ) ) ( Nat.succ_le_succ hj.1 );
      have h_s_pow2 : ∀ s ∈ used_s_v3 p n hp j, ∃ r, s = 2^r := by
        have := lemma_used_s_v3_bound_and_pow2 p n hp j hj_ge_m_sub_1; aesop;
      intros s hs
      obtain ⟨r, hr⟩ := h_s_pow2 s hs
      have h_s_le_M : s ≤ M p k := by
        have h_s_le_M : s ≤ c_step_v3 p n hp j j := by
          have := used_s_v3_sum_le p n hp j;
          exact le_trans ( Finset.single_le_sum ( fun x _ => Nat.zero_le x ) hs ) this;
        exact le_trans h_s_le_M ( hc_upper k hk.1 ( Nat.le_of_lt hk.2 ) j hj );
      exact lemma_pow2_le_M_imp_le_u_next p hp k ( Nat.lt_of_le_of_ne hk.1 ( Ne.symm hk1 ) ) s ⟨ r, hr ⟩ h_s_le_M

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
If a step is in an interval strictly less than K, its targets are strictly less than v(K).
-/
theorem lemma_target_lt_vK_of_interval_lt_K (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (k_idx : ℕ)
  (hk_idx : 1 ≤ k_idx ∧ k_idx < K p)
  (hj_in : in_interval_v4 p n hp k_idx j)
  (h_coeff : CoeffBound_v4 p n hp j) :
  ∀ s ∈ used_s_v3 p n hp j, target_index p j s < v p n hp (K p) := by
    -- By lemma_scalar_bound_v3_all, s ≤ u(k_idx+1).
    have h_scalar_bound : ∀ s ∈ used_s_v3 p n hp j, s ≤ u p (k_idx + 1) := by
      exact fun s a ↦ lemma_scalar_bound_v3_all p n hp j k_idx hk_idx hj_in h_coeff s a;
    -- By lemma_target_lt_v_next, target < v(k_idx+1).
    have h_target_lt_v_next : ∀ s ∈ used_s_v3 p n hp j, target_index p j s < v p n hp (k_idx + 1) := by
      intros s hs
      apply lemma_target_lt_v_next p n hp j k_idx s hk_idx hj_in (h_scalar_bound s hs) (by
      exact Nat.pos_of_ne_zero ( by have := used_s_v3_properties p n hp j s hs; aesop )) (by
      exact used_s_v3_properties p n hp j s hs |>.1);
    exact fun s hs => lt_of_lt_of_le ( h_target_lt_v_next s hs ) ( lemma_v_le_v_of_le p n hp ( k_idx + 1 ) ( K p ) ( by linarith ) ( by linarith ) ( by linarith ) )

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
If the coefficient is bounded by M_K (which is <= 1), then no scalars are used in the last interval.
-/
theorem used_s_empty_of_in_interval_K_v4 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (hc_upper : c_step_v3 p n hp j j ≤ M p (K p)) (hj : in_interval_v4 p n hp (K p) j) :
  used_s_v3 p n hp j = ∅ := by
    refine' Finset.eq_empty_of_forall_notMem fun s hs => _;
    -- Since $s \in used_s_v3 p n hp j$, we have $s \leq c_step_v3 p n hp j j$.
    have hs_le_coeff : s ≤ c_step_v3 p n hp j j := by
      have := used_s_v3_sum_le p n hp j;
      exact le_trans ( Finset.single_le_sum ( fun x _ => Nat.zero_le x ) hs ) this;
    -- Since $s \in A p$, we have $s > 1$.
    have hs_gt_one : 1 < s := by
      exact used_s_v3_properties p n hp j s hs |>.2;
    linarith [ M_K_le_one p hp ]

/-
If a step index is strictly less than v(K), then any target generated is strictly less than v(K).
-/
theorem lemma_target_lt_vK_of_lt_vK (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (hj : j < v p n hp (K p))
  (h_coeff : CoeffBound_v4 p n hp j) :
  ∀ s ∈ used_s_v3 p n hp j, target_index p j s < v p n hp (K p) := by
    -- Apply the lemma_interval_coverage to find k such that j is in interval k.
    obtain ⟨k, hk1, hk2, hk3⟩ : ∃ k, 1 ≤ k ∧ k ≤ K p ∧ in_interval_v4 p n hp k j := by
      exact lemma_interval_coverage p n hp j hj;
    by_cases hk : k < K p;
    · -- Apply the lemma_target_lt_vK_of_interval_lt_K with the given conditions.
      apply lemma_target_lt_vK_of_interval_lt_K p n hp j k ⟨hk1, hk⟩ hk3 h_coeff;
    · -- Since $k \geq K p$, we have $k = K p$.
      have hk_eq : k = K p := by
        linarith;
      -- Since $k = K p$, we have $c_step_v3 p n hp j j \leq M p (K p)$.
      have h_coeff_bound : c_step_v3 p n hp j j ≤ M p (K p) := by
        aesop;
      have := used_s_empty_of_in_interval_K_v4 p n hp j h_coeff_bound ( by aesop ) ; aesop;

/-
For any step k within the range, all target indices generated are also within the range, assuming coefficients are bounded up to k.
-/
theorem lemma_targets_in_range_v3_strong (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (k : ℕ) (hk : k < final_step_index p n hp)
  (h_coeff_all : ∀ j ≤ k, CoeffBound_v4 p n hp j) :
  ∀ s ∈ used_s_v3 p n hp k, target_index p k s < final_step_index p n hp := by
    simp +zetaDelta at *;
    by_cases hk_ge_vK : k ≥ v p n hp (K p);
    · -- Since $k \geq v(K)$, we have $c_step_v3 p n hp k k = 0$ by `c_step_v3_at_k_le_one`.
      have h_c_step_zero : c_step_v3 p n hp k k = 0 := by
        have h_c_init_zero : c_init p n hp k = 0 := by
          exact lemma_c_init_eq_zero_of_ge_vK p n hp hn k hk_ge_vK;
        have h_contributing_s_empty : contributing_s_v3 p n hp k = ∅ := by
          ext s
          simp [contributing_s_v3, h_c_init_zero];
          intro x hx hs htarget
          have htarget_lt_vK : target_index p x s < v p n hp (K p) := by
            apply lemma_target_lt_vK_of_lt_vK p n hp x (by
            unfold final_step_index at hk; linarith;) (h_coeff_all x (by
            linarith)) s hs;
          linarith;
        rw [ c_step_v3_eq_init_plus_card, h_c_init_zero, h_contributing_s_empty, Finset.card_empty, add_zero ];
      -- Since $c_step_v3 p n hp k k = 0$, the used_s_v3 p n hp k must be empty.
      have h_used_s_empty : used_s_v3 p n hp k = ∅ := by
        have h_used_s_empty : ∀ s ∈ used_s_v3 p n hp k, s ≤ c_step_v3 p n hp k k := by
          have := used_s_v3_sum_le p n hp k;
          exact fun s hs => le_trans ( Finset.single_le_sum ( fun x _ => Nat.zero_le x ) hs ) this;
        exact Finset.eq_empty_of_forall_notMem fun s hs => by have := h_used_s_empty s hs; linarith [ used_s_v3_properties p n hp k s hs ] ;
      grind;
    · intro s hs;
      -- Apply `lemma_target_lt_vK_of_lt_vK` using `h_coeff_all k le_rfl`.
      have h_target_lt_vK : target_index p k s < v p n hp (K p) := by
        exact lemma_target_lt_vK_of_lt_vK p n hp k ( by linarith ) ( h_coeff_all k le_rfl ) s hs;
      exact lt_of_lt_of_le h_target_lt_vK ( Nat.le_succ _ )

/-
If k is the boundary index v(K), then no scalars contribute to k from previous steps.
-/
theorem lemma_contributing_empty_at_vK (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : k = v p n hp (K p))
  (h_coeff_prev : ∀ j < k, CoeffBound_v4 p n hp j) :
  contributing_s_v3 p n hp k = ∅ := by
    by_contra h_nonempty;
    obtain ⟨ s, hs ⟩ := Finset.nonempty_of_ne_empty h_nonempty;
    obtain ⟨j, hj₁, hj₂⟩ : ∃ j < k, s ∈ used_s_v3 p n hp j ∧ target_index p j s = k := by
      unfold contributing_s_v3 at hs; aesop;
    have := lemma_target_lt_vK_of_lt_vK p n hp j ( by linarith ) ( h_coeff_prev j hj₁ ) s hj₂.1; aesop;

/-
The initial coefficients are zero for indices beyond the final step index.
-/
theorem lemma_c_init_support_bounded (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) :
  ∀ i, c_init p n hp i > 0 → i < final_step_index p n hp := by
    intro i hi
    by_cases hi_m : i < m p n hp - 1;
    · exact lt_of_lt_of_le hi_m ( Nat.le_succ_of_le <| by linarith [ show v p n hp 1 = m p n hp - 1 from v_1_eq_m_sub_1 p n hp, show v p n hp ( K p ) ≥ v p n hp 1 from lemma_v_ge_v1 p n hp ( K p ) ( by linarith [ show K p ≥ 2 from K_ge_2 p ] ) ( by linarith ) ] );
    · have hi_R : a_seq p i ≤ R p n hp := by
        have h_coeff : c_init p n hp i = coeff_from_binary p (R p n hp) i := by
          unfold c_init; aesop;
        exact not_lt.1 fun contra => hi.ne' <| h_coeff.trans <| coeff_from_binary_eq_zero_of_gt p hp.2 _ _ contra;
      -- Since $a_seq p i \leq R p n hp$ and $R p n hp < P p (K p) * a_seq p (m p n hp - 1)$, we have $a_seq p i < P p (K p) * a_seq p (m p n hp - 1)$.
      have hi_lt : a_seq p i < P p (K p) * a_seq p (m p n hp - 1) := by
        exact lt_of_le_of_lt hi_R ( R_lt_P2_am_sub_1 p n hp hn |> lt_of_lt_of_le <| Nat.mul_le_mul_right _ <| show P p ( K p ) ≥ P p 2 from by exact P_mono _ <| by linarith [ K_ge_2 p ] );
      exact Nat.lt_succ_of_le ( Nat.le_of_not_lt fun hi' => hi_lt.not_ge <| by rw [ ← v_spec p n hp ( K p ) ] ; exact a_seq_strict_mono p hp.2 |> StrictMono.monotone <| Nat.le_of_not_lt fun hi'' => by linarith )

/-
The initial coefficients satisfy the bounds for all intervals.
-/
theorem lemma_coeff_bound_v4_base (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) :
  CoeffBound_v4 p n hp 0 := by
    -- For k = 1, we have c_init i ≤ M_0 + 1 ≤ M_0 + |S| = M_1.
    have h_k1 : ∀ i, in_interval_v4 p n hp 1 i → c_init p n hp i ≤ M p 1 := by
      have := lemma_coeff_bound_v4_k1 p n hp hn; aesop;
    -- For k = 2, we have c_init i ≤ 1 ≤ |S| = M_2.
    have h_k2 : ∀ i, in_interval_v4 p n hp 2 i → c_init p n hp i ≤ M p 2 := by
      -- For indices i ≥ v p n hp 1, the initial coefficient is at most 1.
      have h_ge_v1 : ∀ i, i ≥ v p n hp 1 → c_init p n hp i ≤ 1 := by
        intros i hi
        apply c_init_le_one_of_ge_m_sub_1 p n hp i (by
        exact le_trans ( v_1_eq_m_sub_1 p n hp ▸ le_rfl ) hi);
      -- Since $i$ is in the second interval, we have $i \geq v p n hp 1$.
      intro i hi
      have h_i_ge_v1 : v p n hp 1 ≤ i := by
        unfold in_interval_v4 at hi; aesop;
      exact le_trans ( h_ge_v1 i h_i_ge_v1 ) ( by linarith [ show M p 2 ≥ 1 from M_ge_one_of_le_K p hp 2 ⟨ by norm_num, by linarith [ show K p ≥ 2 from by
                                                                                                                                        unfold K; aesop; ] ⟩ ] );
    -- For k ≥ 3, we have c_init i = 0 ≤ M_k by definition.
    have h_k_ge_3 : ∀ k, 3 ≤ k → k ≤ K p → ∀ i, in_interval_v4 p n hp k i → c_init p n hp i ≤ M p k := by
      intros k hk hk_le i hi
      have h_c_init_zero : c_init p n hp i = 0 := by
        apply c_init_eq_zero_of_ge_3_v3 p n hp hn i k hk hk_le hi;
      exact h_c_init_zero.symm ▸ Nat.zero_le _;
    intro k hk₁ hk₂ i hi; rcases k with ( _ | _ | _ | k ) <;> simp_all +arith +decide;
    · exact h_k1 i hi;
    · exact h_k2 i hi;
    · exact h_k_ge_3 _ le_add_self hk₂ _ hi

/-
If j targets i, and j is in interval k_j and i is in interval k, then k_j >= k - 1.
-/
theorem lemma_interval_relation_v4 (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ)
  (h_coeff : CoeffBound_v4 p n hp j)
  (k : ℕ) (hk : 3 ≤ k ∧ k ≤ K p) (hi : in_interval_v4 p n hp k i)
  (k_j : ℕ) (hk_j : 1 ≤ k_j ∧ k_j < K p) (hj : in_interval_v4 p n hp k_j j)
  (s : ℕ) (hs : s ∈ used_s_v3 p n hp j) (ht : target_index p j s = i) :
  k_j ≥ k - 1 := by
    by_contra h_contra;
    have h_P : a_seq p i < a_seq p (v p n hp (k_j + 1)) := by
      have h_P : s * a_seq p j < a_seq p (v p n hp (k_j + 1)) := by
        have h_P : s ≤ u p (k_j + 1) := by
          exact lemma_scalar_bound_v3_all p n hp j k_j hk_j hj h_coeff s hs;
        apply_rules [ lemma_target_val_lt_next_boundary ];
        exact Nat.pos_of_ne_zero fun h => by have := used_s_v3_properties p n hp j s hs; aesop;
      convert h_P using 1;
      rw [ ← ht, target_index ];
      exact a_seq_index_in_A p hp.2 ( s * a_seq p j ) ( s_mul_a_seq_mem_A p hp.2 s ( used_s_v3_properties p n hp j s hs |>.1 ) j );
    have h_P : a_seq p (v p n hp (k - 1)) ≤ a_seq p i := by
      apply_rules [ monotone_nat_of_le_succ ];
      · unfold a_seq;
        unfold A; aesop;
      · unfold in_interval_v4 at hi; aesop;
    have h_P : v p n hp (k - 1) ≥ v p n hp (k_j + 1) := by
      exact lemma_v_le_v_of_le p n hp ( k_j + 1 ) ( k - 1 ) ( by linarith ) ( by omega ) ( by omega );
    -- Since $a_seq$ is strictly increasing, we have $a_seq p (v p n hp (k - 1)) \geq a_seq p (v p n hp (k_j + 1))$.
    have h_a_seq_inc : StrictMono (a_seq p) := by
      exact strictMono_nat_of_lt_succ fun n => by
        exact Nat.lt_of_not_ge fun h => by have := a_seq_strict_mono p hp.2; linarith [ this n.lt_succ_self ] ;;
    linarith [ h_a_seq_inc.monotone h_P ]

/-
If the coefficient bound holds at step j, then any target i in an interval k >= 3 must come from a source j >= v(k-2).
-/
theorem lemma_update_condition_v4_step (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (h_coeff : CoeffBound_v4 p n hp j) :
  ∀ i, IsTarget_v4 p n hp j i →
    ∀ k, 3 ≤ k → k ≤ K p →
      in_interval_v4 p n hp k i →
      j ≥ v p n hp (k - 2) := by
        -- By lemma_interval_relation_v4, we have j ≥ v(k_j - 1) with k_j = k_index(j).
        intro i hi k hk_ge_3 hk_le_K hi_interval
        obtain ⟨k_j, hk_j, hk_j_range⟩ : ∃ k_j, 1 ≤ k_j ∧ k_j < K p ∧ in_interval_v4 p n hp k_j j := by
          have hj_lt_vK : j < v p n hp (K p) := by
            obtain ⟨ s, hs₁, hs₂ ⟩ := hi;
            have h_j_lt_vK : j < i := by
              have := target_index_gt_source_v3 p n hp j s hs₁; aesop;
            have h_i_lt_vK : i < v p n hp k := by
              unfold in_interval_v4 at hi_interval; aesop;
            exact lt_of_lt_of_le h_j_lt_vK ( le_trans h_i_lt_vK.le ( lemma_v_le_v_of_le p n hp k ( K p ) ( by linarith ) ( by linarith ) ( by linarith ) ) );
          obtain ⟨ k_j, hk_j, hk_j' ⟩ := lemma_interval_coverage p n hp j hj_lt_vK;
          by_cases hk_j_eq_K : k_j = K p;
          · have h_no_scalar_from_K : used_s_v3 p n hp j = ∅ := by
              apply used_s_empty_of_in_interval_K_v4;
              · exact h_coeff _ ( by linarith ) ( by linarith ) _ ( by aesop );
              · aesop;
            unfold IsTarget_v4 at hi; aesop;
          · exact ⟨ k_j, hk_j, lt_of_le_of_ne hk_j'.1 hk_j_eq_K, hk_j'.2 ⟩;
        have h_k_j_ge_k_minus_1 : k_j ≥ k - 1 := by
          obtain ⟨s, hs⟩ := hi;
          apply lemma_interval_relation_v4 p n hp j i h_coeff k ⟨hk_ge_3, hk_le_K⟩ hi_interval k_j ⟨hk_j, hk_j_range.1⟩ hk_j_range.2 s hs.1 hs.2;
        rcases k with ( _ | _ | k ) <;> simp_all +arith +decide [ in_interval_v4 ];
        exact le_trans ( lemma_v_le_v_of_le p n hp k ( k_j - 1 ) ( by linarith ) ( Nat.sub_le_of_le_add <| by linarith ) <| Nat.le_sub_one_of_lt h_k_j_ge_k_minus_1 ) <| by aesop;

/-
If the coefficient bound holds for all previous steps, then the update condition holds up to the current step.
-/
theorem lemma_update_condition_v4_induction (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (h_prev : ∀ j' < j, CoeffBound_v4 p n hp j') :
  UpdateConditionUpTo_v4 p n hp j := by
    intro i' hi' i hi k hk hk' hi'';
    exact fun hk'' => lemma_update_condition_v4_step p n hp i' ( h_prev i' hi' ) i hi k hk'' hk' hi''

/-
If the update condition holds, then any source targeting an index in interval k >= 3 must be at least m-1.
-/
theorem lemma_targets_ge_m_sub_1 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (h_update : UpdateConditionUpTo_v4 p n hp j)
  (k : ℕ) (hk : 3 ≤ k ∧ k ≤ K p)
  (i : ℕ) (hi : in_interval_v4 p n hp k i)
  (j' : ℕ) (hj' : j' < j)
  (h_target : IsTarget_v4 p n hp j' i) :
  j' ≥ m p n hp - 1 := by
    -- By the properties of the intervals, since $k \geq 3$, we have $v(k-2) \geq v(1)$.
    have h_v_ge_v1 : v p n hp (k - 2) ≥ v p n hp 1 := by
      apply_rules [ lemma_v_ge_v1 ];
      · omega;
      · omega;
    -- By the properties of the intervals, since $k \geq 3$, we have $v(1) = m - 1$.
    have h_v1_eq_m_minus_1 : v p n hp 1 = m p n hp - 1 := by
      exact v_1_eq_m_sub_1 p n hp;
    exact h_v1_eq_m_minus_1 ▸ h_v_ge_v1.trans ( h_update _ hj' _ h_target _ ( by linarith ) ( by linarith ) hi ( by linarith ) )

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
If the update condition holds, then any scalar targeting an index in interval k >= 3 is a power of 2 and bounded by M_{k-1}.
-/
theorem lemma_targets_properties_ge_3 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (h_update : UpdateConditionUpTo_v4 p n hp j)
  (h_prev_coeff : ∀ j' < j, CoeffBound_v4 p n hp j')
  (k : ℕ) (hk : 3 ≤ k ∧ k ≤ K p)
  (i : ℕ) (hi : in_interval_v4 p n hp k i)
  (j' : ℕ) (hj' : j' < j)
  (s : ℕ) (hs : s ∈ used_s_v3 p n hp j') (ht : target_index p j' s = i) :
  (∃ r, s = 2^r) ∧ s ≤ M p (k - 1) := by
    -- By `lemma_targets_ge_m_sub_1`, `j' >= m - 1`.
    have h_j'_ge_m_sub_1 : j' ≥ m p n hp - 1 := by
      apply lemma_targets_ge_m_sub_1 p n hp j h_update k hk i hi j' hj' ⟨s, hs, ht⟩;
    -- By `lemma_used_s_v3_bound_and_pow2`, `s` is a power of 2 and `s <= c_{j'}`.
    have h_s_pow2_and_le_c : ∃ r, s = 2^r ∧ s ≤ c_step_v3 p n hp j' j' := by
      have := lemma_used_s_v3_bound_and_pow2 p n hp j' h_j'_ge_m_sub_1 s hs; aesop;
    -- By `lemma_interval_coverage`, `j'` is in some interval `k_j`.
    obtain ⟨k_j, hk_j⟩ : ∃ k_j, 1 ≤ k_j ∧ k_j ≤ K p ∧ in_interval_v4 p n hp k_j j' := by
      apply lemma_interval_coverage p n hp j';
      have h_j'_lt_vK : j' < i := by
        have := target_index_gt_source_v3 p n hp j' s hs; aesop;
      -- Since $i$ is in interval $k$, we have $i < v p n hp k$.
      have h_i_lt_vk : i < v p n hp k := by
        unfold in_interval_v4 at hi; aesop;
      exact lt_trans h_j'_lt_vK ( lt_of_lt_of_le h_i_lt_vk ( lemma_v_le_v_of_le p n hp k ( K p ) ( by linarith ) ( by linarith ) ( by linarith ) ) );
    -- If `k_j = K`, then `used_s_v3` is empty by `used_s_empty_of_in_interval_K_v4`, contradiction. So `k_j < K`.
    by_cases hk_j_eq_K : k_j = K p;
    · have := used_s_empty_of_in_interval_K_v4 p n hp j' ?_ ?_ <;> aesop ( simp_config := { singlePass := true } ) ;
    · -- By `lemma_M_antitone`, `M_{k_j} <= M_{k-1}` (since `k_j >= k-1 >= 1`).
      have h_M_kj_le_M_k_minus_1 : M p k_j ≤ M p (k - 1) := by
        apply lemma_M_antitone p hp (k - 1) k_j (by
        omega) (by
        have := lemma_interval_relation_v4 p n hp j' i ( h_prev_coeff j' hj' ) k hk hi k_j ⟨ hk_j.1, lt_of_le_of_ne hk_j.2.1 hk_j_eq_K ⟩ hk_j.2.2 s hs ht; omega;);
      exact ⟨ ⟨ h_s_pow2_and_le_c.choose, h_s_pow2_and_le_c.choose_spec.1 ⟩, le_trans h_s_pow2_and_le_c.choose_spec.2 ( le_trans ( h_prev_coeff _ hj' _ ( by omega ) ( by omega ) _ hk_j.2.2 ) h_M_kj_le_M_k_minus_1 ) ⟩

/-
The number of contributing scalars up to a limit is equal to the number of steps that target the index.
-/
noncomputable def contributing_scalars_step_v4 (p n : ℕ) (hp : Odd p ∧ p > 1) (limit : ℕ) (i : ℕ) : Finset ℕ :=
  (Finset.range limit).biUnion (fun j => (used_s_v3 p n hp j).filter (fun s => target_index p j s = i))

theorem card_contributing_scalars_step_v4_eq_targets (p n : ℕ) (hp : Odd p ∧ p > 1) (limit : ℕ) (i : ℕ) :
  (contributing_scalars_step_v4 p n hp limit i).card = (Finset.filter (fun j => IsTarget_v4 p n hp j i) (Finset.range limit)).card := by
    -- Since the sets are disjoint, the cardinality of the union is the sum of the cardinalities.
    have h_card_union : (contributing_scalars_step_v4 p n hp limit i).card = ∑ j ∈ Finset.range limit, (Finset.filter (fun s => target_index p j s = i) (used_s_v3 p n hp j)).card := by
      rw [ ← Finset.card_biUnion ];
      · exact rfl;
      · intros j hj j' hj' hij; exact (by
        exact contributing_scalars_disjoint p n hp i j j' hij);
    -- Since the sets are disjoint, the cardinality of the union is the sum of the cardinalities of each set.
    simp [h_card_union, IsTarget_v4];
    rw [ Finset.card_filter ];
    exact Finset.sum_congr rfl fun x hx => by rw [ card_filter_target_eq ] ; aesop;

/-
For i in interval k >= 3, the number of previous steps targeting i is at most M_k.
-/
theorem lemma_target_count_bound_v4 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (h_update : UpdateConditionUpTo_v4 p n hp j)
  (h_prev_coeff : ∀ j' < j, CoeffBound_v4 p n hp j')
  (k : ℕ) (hk : 3 ≤ k ∧ k ≤ K p)
  (i : ℕ) (hi : in_interval_v4 p n hp k i) :
  (Finset.filter (fun j' => IsTarget_v4 p n hp j' i) (Finset.range j)).card ≤ M p k := by
    -- By `lemma_targets_properties_ge_3`, every `s \in S` satisfies `s <= M_{k-1}` and `s` is a power of 2.
    have h_S_subset_superset : ∀ s ∈ contributing_scalars_step_v4 p n hp j i, s ∈ Finset.image (fun r => 2^r) (Finset.Icc 1 (Nat.log2 (M p (k - 1)))) := by
      intros s hs
      obtain ⟨j', hj', hs_j', ht⟩ : ∃ j' < j, s ∈ used_s_v3 p n hp j' ∧ target_index p j' s = i := by
        unfold contributing_scalars_step_v4 at hs; aesop;
      have h_s_prop : ∃ r, s = 2^r ∧ s ≤ M p (k - 1) := by
        have := lemma_targets_properties_ge_3 p n hp j h_update h_prev_coeff k hk i hi j' hj' s hs_j' ht; aesop;
      obtain ⟨ r, rfl, hr ⟩ := h_s_prop;
      rcases r with ( _ | r ) <;> simp_all +decide [ Nat.le_log_iff_pow_le ];
      · exact absurd ( used_s_v3_properties p n hp j' 1 hs_j' ) ( by norm_num [ A ] );
      · rw [ Nat.le_log2 ] <;> linarith [ Nat.pow_le_pow_right two_pos ( show r + 1 ≥ 1 from Nat.succ_pos _ ) ];
    -- The cardinality of this superset is `log2(M_{k-1})`.
    have h_card_superset : (Finset.image (fun r => 2^r) (Finset.Icc 1 (Nat.log2 (M p (k - 1))))).card ≤ Nat.log2 (M p (k - 1)) := by
      exact Finset.card_image_le.trans ( by simp );
    -- Thus `|J| = |S| ≤ M_k`.
    have h_card_J_le_card_S : (Finset.filter (fun j' => IsTarget_v4 p n hp j' i) (Finset.range j)).card ≤ (contributing_scalars_step_v4 p n hp j i).card := by
      rw [ card_contributing_scalars_step_v4_eq_targets ];
    refine le_trans h_card_J_le_card_S <| le_trans ( Finset.card_le_card fun x hx => h_S_subset_superset x hx ) ?_;
    rcases k with ( _ | _ | _ | k ) <;> simp_all +arith +decide [ M ]

/-
The coefficient at step j is the initial coefficient plus the number of previous steps that target the index.
-/
theorem lemma_c_step_v3_eq_init_plus_targets (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ) (h_ge : i ≥ j) :
  c_step_v3 p n hp j i = c_init p n hp i + (Finset.filter (fun j' => IsTarget_v4 p n hp j' i) (Finset.range j)).card := by
    induction' j with j ih generalizing i;
    · aesop;
    · -- By definition of $c_step_v3$, we have:
      have h_c_step_succ : c_step_v3 p n hp (j + 1) i = c_step_v3 p n hp j i + if IsTarget_v4 p n hp j i then 1 else 0 := by
        -- By definition of $c_step_v3$, we have $c_step_v3 p n hp (j + 1) i = c_step_v3 p n hp j i + if IsTarget_v4 p n hp j i then 1 else 0$.
        have h_c_step_succ : c_step_v3 p n hp (j + 1) i = c_step_v3 p n hp j i + if ∃ s ∈ used_s_v3 p n hp j, target_index p j s = i then 1 else 0 := by
          exact ( c_step_v3_succ_eq p n hp j ) |>.2 i ( by linarith );
        unfold IsTarget_v4; aesop;
      rw [ h_c_step_succ, ih i ( by linarith ), Finset.range_add_one, Finset.filter_insert ] ; aesop

/-
For indices in intervals k >= 3, the coefficient at step j is bounded by M_k.
-/
theorem lemma_bound_ge3_v4 (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (j : ℕ)
  (h_update : UpdateConditionUpTo_v4 p n hp j)
  (h_prev_coeff : ∀ j' < j, CoeffBound_v4 p n hp j')
  (k : ℕ) (hk : 3 ≤ k ∧ k ≤ K p)
  (i : ℕ) (hi : in_interval_v4 p n hp k i)
  (h_ge : i ≥ j) :
  c_step_v3 p n hp j i ≤ M p k := by
    rw [ lemma_c_step_v3_eq_init_plus_targets ];
    · -- By Lemma 3, we know that $c_init i = 0$ for $i \geq 3$.
      have h_c_init_zero : c_init p n hp i = 0 := by
        apply c_init_eq_zero_of_ge_3_v3 p n hp hn i k hk.left hk.right hi;
      have := lemma_target_count_bound_v4 p n hp j h_update h_prev_coeff k hk i hi; aesop;
    · assumption

/-
For indices in the first interval, the coefficient at step j is bounded by M_1.
-/
theorem lemma_bound_k1_v4 (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (j : ℕ)
  (i : ℕ) (hi : in_interval_v4 p n hp 1 i)
  (h_ge : i ≥ j) :
  c_step_v3 p n hp j i ≤ M p 1 := by
    unfold in_interval_v4 at hi;
    -- Since $i < m - 1$, we have $c_step_v3 p n hp j i \leq M_0 p + |S|$ by the lemma.
    have h_bound : c_step_v3 p n hp j i ≤ M_0 p + (S p).card := by
      have h_bound : c_step_v3 p n hp j i ≤ c_step_v3 p n hp i i := by
        have h_bound : ∀ k, j ≤ k ∧ k ≤ i → c_step_v3 p n hp j i ≤ c_step_v3 p n hp k i := by
          intros k hk
          induction' hk.left with k hk ih;
          · rfl;
          · have h_bound : c_step_v3 p n hp (k + 1) i = c_step_v3 p n hp k i + if ∃ s ∈ used_s_v3 p n hp k, target_index p k s = i then 1 else 0 := by
              have := c_step_v3_succ_eq p n hp k;
              exact this.2 i ( by linarith );
            grind +ring;
        exact h_bound i ⟨ h_ge, le_rfl ⟩;
      convert h_bound.trans ( c_step_v3_bound_lt_m p n hp i _ );
      unfold v at hi;
      refine' lt_of_lt_of_le hi _;
      unfold P;
      unfold u; simp +arith +decide [ List.range_succ ] ;
      unfold index_in_A; aesop;
    exact h_bound.trans ( by unfold M; norm_num )

/-
If the coefficient at step j is bounded by |S| (when j >= m-1), then the scalars used in step j are a subset of S.
-/
theorem lemma_used_s_v3_subset_S (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (h_cond : j ≥ m p n hp - 1 → c_step_v3 p n hp j j ≤ (S p).card) :
  used_s_v3 p n hp j ⊆ S p := by
    -- Let's unfold the definition of `used_s_v3`.
    unfold used_s_v3;
    field_simp;
    split_ifs;
    · exact decompose_S_subset_S p hp (c_step_v3 p n hp j j);
    · apply decompose_even_pow2_subset_S;
      · tauto;
      · assumption;
      · exact h_cond ( le_of_not_gt ‹_› );
    · exact Finset.empty_subset _

/-
If j is less than v(2) and the coefficient bound holds, then the scalars used in step j are a subset of S.
-/
theorem lemma_used_s_subset_S_of_lt_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (hj : j < v p n hp 2)
  (h_coeff : CoeffBound_v4 p n hp j) :
  used_s_v3 p n hp j ⊆ S p := by
    by_cases hj' : j < m p n hp - 1;
    · -- By definition of `used_s_v3`, we know that it is a subset of `S p` when `j < m p n hp - 1`.
      have h_used_s_subset_S : used_s_v3 p n hp j = decompose_S p hp (c_step_v3 p n hp j j) := by
        exact if_pos hj';
      exact h_used_s_subset_S ▸ decompose_S_subset_S p hp _;
    · have := h_coeff 2 ( by decide ) ( by
        unfold K; aesop; ) j ( by
        -- Since $j \geq m - 1$ and $j < v(2)$, we can conclude that $j$ is in the interval $2$.
        simp [in_interval_v4, hj', hj];
        -- Since $v p n hp 1 = m p n hp - 1$, we can directly use $hj'$ to conclude $v p n hp 1 ≤ j$.
        have hv1_eq_m_minus_1 : v p n hp 1 = m p n hp - 1 := by
          norm_num +zetaDelta at *;
          exact v_1_eq_m_sub_1 p n hp;
        linarith );
      exact lemma_used_s_v3_subset_S p n hp j fun a ↦ this

/-
For indices in the second interval, the contributing scalars are a subset of S.
-/
theorem lemma_contributing_scalars_subset_S_v4 (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ)
  (hi : in_interval_v4 p n hp 2 i)
  (h_prev_coeff : ∀ j < i, CoeffBound_v4 p n hp j) :
  contributing_scalars_step_v4 p n hp i i ⊆ S p := by
    -- Since `i` is in interval 2, we have `i < v(2)`.
    have h_i_lt_v2 : i < v p n hp 2 := by
      unfold in_interval_v4 at hi; aesop;
    intro s hs
    obtain ⟨j, hj₁, hj₂⟩ : ∃ j < i, s ∈ used_s_v3 p n hp j ∧ target_index p j s = i := by
      unfold contributing_scalars_step_v4 at hs; aesop;
    exact lemma_used_s_subset_S_of_lt_v2 p n hp j ( by linarith ) ( h_prev_coeff j hj₁ ) |> Finset.mem_of_subset <| by aesop;

/-
If i is in the second interval and j < i, then the scalars used in step j are a subset of S.
-/
theorem lemma_used_s_subset_S_of_lt_i_in_interval_2 (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ)
  (hi : in_interval_v4 p n hp 2 i)
  (j : ℕ) (hj : j < i)
  (h_coeff : CoeffBound_v4 p n hp j) :
  used_s_v3 p n hp j ⊆ S p := by
    have := @lemma_used_s_subset_S_of_lt_v2;
    exact this p n hp j ( by rcases hi with ⟨ _, _ ⟩ ; linarith ) h_coeff

/-
If the target is a power of 2, then p cannot be a contributing scalar.
-/
theorem lemma_contributing_scalars_not_p_if_pow2 (p n : ℕ) (hp : Odd p ∧ p > 1) (limit : ℕ) (i : ℕ)
  (h_pow2 : ∃ r, a_seq p i = 2^r)
  (s : ℕ) (hs : s ∈ contributing_scalars_step_v4 p n hp limit i) :
  s ≠ p := by
    obtain ⟨j, hj, hs_j⟩ : ∃ j, j < limit ∧ s ∈ used_s_v3 p n hp j ∧ target_index p j s = i := by
      unfold contributing_scalars_step_v4 at hs; aesop;
    have h_div : s ∣ a_seq p i := by
      rw [ ← hs_j.2, target_index ];
      rw [ show a_seq p ( index_in_A p ( s * a_seq p j ) ) = s * a_seq p j from ?_ ];
      · exact dvd_mul_right _ _;
      · -- By definition of `a_seq`, we know that `a_seq p (index_in_A p (s * a_seq p j)) = s * a_seq p j`.
        apply a_seq_index_in_A;
        · exact hp.2;
        · exact s_mul_a_seq_mem_A p hp.2 s ( by
            exact used_s_v3_properties p n hp j s hs_j.1 |>.1 ) j;
    intro h_eq_p
    have h_div_pow2 : p ∣ 2 ^ h_pow2.choose := by
      aesop;
    have := hp.1; ( have := hp.2; ( have := Nat.Prime.dvd_of_dvd_pow ( Nat.minFac_prime ( by linarith ) ) ( dvd_trans ( Nat.minFac_dvd p ) h_div_pow2 ) ; simp_all +decide [ Nat.dvd_prime ] ; ) );
    exact absurd ( this.resolve_left hp.2.ne' ) ( by simpa [ ← even_iff_two_dvd ] using hp.1 )

/-
Corrected interval definitions and invariants.
-/
def in_interval_v5 (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (i : ℕ) : Prop :=
  if k = 1 then i ≤ v p n hp 1
  else v p n hp (k - 1) < i ∧ i ≤ v p n hp k

def CoeffBound_v5 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k ≤ K p →
    ∀ i, in_interval_v5 p n hp k i →
      c_step_v3 p n hp j i ≤ M p k

def IsTarget_v5 (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ) : Prop :=
  ∃ s ∈ used_s_v3 p n hp j, target_index p j s = i

def UpdateConditionUpTo_v5 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Prop :=
  ∀ i' < j, ∀ i, IsTarget_v5 p n hp i' i →
    ∀ k, 1 ≤ k → k ≤ K p →
      in_interval_v5 p n hp k i →
      (k ≥ 3 → i' > v p n hp (k - 2))

def Lemma3_invariant_v5 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Prop :=
  CoeffBound_v5 p n hp j ∧ UpdateConditionUpTo_v5 p n hp j

/-
The initial coefficients satisfy the bounds for the v5 intervals.
-/
theorem lemma_coeff_bound_v5_base (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) :
  CoeffBound_v5 p n hp 0 := by
    have := @lemma_invariant_v3_base p n hp hn;
    cases this ; aesop

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
The number of targets for an index in the second interval is at most |S|.
-/
theorem lemma_card_targets_le_S_card (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (i : ℕ)
  (hi : in_interval_v4 p n hp 2 i)
  (h_prev_coeff : ∀ j' < i, CoeffBound_v4 p n hp j') :
  (Finset.filter (fun j' => IsTarget_v4 p n hp j' i) (Finset.range j)).card ≤ (S p).card := by
    have h_subset_S : contributing_scalars_step_v4 p n hp j i ⊆ S p := by
      intro s hs
      obtain ⟨j', hj', hs_j', hs_target⟩ : ∃ j' < j, s ∈ used_s_v3 p n hp j' ∧ target_index p j' s = i := by
        unfold contributing_scalars_step_v4 at hs; aesop;
      have h_subset_S : s ∈ S p := by
        have h_interval : in_interval_v4 p n hp 2 i := hi
        have h_j'_lt_i : j' < i := by
          have h_j'_lt_i : target_index p j' s > j' := by
            exact target_index_gt_source_v3 p n hp j' s hs_j';
          linarith
        have h_j'_in_S : used_s_v3 p n hp j' ⊆ S p := by
          apply lemma_used_s_subset_S_of_lt_i_in_interval_2 p n hp i h_interval j' h_j'_lt_i (h_prev_coeff j' h_j'_lt_i)
        exact h_j'_in_S hs_j';
      exact h_subset_S;
    rw [ ← card_contributing_scalars_step_v4_eq_targets ];
    exact Finset.card_le_card h_subset_S

/-
The initial coefficient at index v_1 is at most 1.
-/
theorem lemma_c_init_at_v1 (p n : ℕ) (hp : Odd p ∧ p > 1) :
  c_init p n hp (v p n hp 1) ≤ 1 := by
    -- Since $v_1 = m - 1$, we can use the definition of $c_init$ for $i \geq m - 1$.
    have h_v1 : v p n hp 1 = m p n hp - 1 := by
      exact v_1_eq_m_sub_1 p n hp;
    exact h_v1.symm ▸ c_init_le_one_of_ge_m_sub_1 p n hp _ ( by omega )

/-
The contributing scalars for the index v_1 are a subset of S.
-/
theorem lemma_contributing_at_v1_subset_S (p n : ℕ) (hp : Odd p ∧ p > 1) :
  contributing_s_v3 p n hp (v p n hp 1) ⊆ S p := by
    have h_union_subset : ∀ j < v p n hp 1, used_s_v3 p n hp j ⊆ S p := by
      intros j hj_lt_m_sub_1;
      have h_union_subset : used_s_v3 p n hp j = decompose_S p hp (c_step_v3 p n hp j j) := by
        have h_j_lt_m : j < m p n hp - 1 := by
          unfold v at hj_lt_m_sub_1;
          refine lt_of_lt_of_le hj_lt_m_sub_1 ?_;
          unfold P;
          unfold u; norm_num [ List.range_succ ] ;
          unfold index_in_A a_seq; aesop;
        unfold used_s_v3; aesop;
      exact h_union_subset ▸ decompose_S_subset_S p hp _;
    exact Finset.biUnion_subset.mpr fun j hj => Finset.filter_subset _ _ |> Finset.Subset.trans <| h_union_subset j <| Finset.mem_range.mp hj

/-
If a_{v_1} is a power of 2, then p is not a contributing scalar for v_1.
-/
theorem lemma_contributing_at_v1_not_p_if_pow2 (p n : ℕ) (hp : Odd p ∧ p > 1)
  (h_pow2 : ∃ k, a_seq p (v p n hp 1) = 2^k) :
  ∀ s ∈ contributing_s_v3 p n hp (v p n hp 1), s ≠ p := by
    exact fun s a ↦
      lemma_contributing_scalars_not_p_if_pow2 p n hp (v p n hp 1) (v p n hp 1) h_pow2 s a

/-
The coefficient at index v_1 is bounded by M_1.
-/
theorem lemma_bound_at_v1 (p n : ℕ) (hp : Odd p ∧ p > 1) :
  c_step_v3 p n hp (v p n hp 1) (v p n hp 1) ≤ M p 1 := by
    -- By definition of $c_step_v3$, we know that $c_step_v3 p n hp (v p n hp 1) (v p n hp 1) = c_init p n hp (v p n hp 1) + contributing_s_v3 p n hp (v p n hp 1).card$.
    have h_c_step_v3_v1 : c_step_v3 p n hp (v p n hp 1) (v p n hp 1) = c_init p n hp (v p n hp 1) + (contributing_s_v3 p n hp (v p n hp 1)).card := by
      exact c_step_v3_eq_init_plus_card p n hp (v p n hp 1);
    have h_c_init_v1 : c_init p n hp (v p n hp 1) ≤ 1 := by
      exact lemma_c_init_at_v1 p n hp
    have h_contributing_v1 : (contributing_s_v3 p n hp (v p n hp 1)).card ≤ (S p).card := by
      apply Finset.card_le_card;
      exact lemma_contributing_at_v1_subset_S p n hp;
    unfold M M_0; norm_num;
    split_ifs ; norm_num at *;
    · all_goals generalize_proofs at *;
      linarith [ ‹∃ M₀ ≤ p, 0 < M₀ ∧ ∀ x ( a : M₀ ≤ x ), x ≤ M₀ + _ → is_sum_of_distinct_elements _ x›.choose_spec.2.1 ];
    · (expose_names; exact False.elim (h hp))

/-
The coefficient at index i is non-decreasing with respect to the step index, as long as the step index is less than or equal to i.
-/
theorem lemma_c_step_v3_mono (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) (j k : ℕ) (hjk : j ≤ k) (hki : k ≤ i) :
  c_step_v3 p n hp j i ≤ c_step_v3 p n hp k i := by
    -- By definition of $c$, we know that if $j \leq k \leq i$, then $c_j(a_i) \leq c_k(a_i)$.
    have h_chain_step : ∀ j k i, j < k → k ≤ i → c_step_v3 p n hp j i ≤ c_step_v3 p n hp k i := by
      intros j k i hjk hki
      induction' hjk with k hk ih;
      · by_cases h : i = j <;> simp_all +decide [ c_step_v3_succ_eq ];
      · have := c_step_v3_succ_eq p n hp k;
        grind;
    cases lt_or_eq_of_le hjk <;> aesop

/-
For indices in the first interval, the coefficient at step j is bounded by M_1.
-/
theorem lemma_bound_k1_v5 (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (j : ℕ)
  (i : ℕ) (hi : in_interval_v5 p n hp 1 i)
  (h_ge : i ≥ j) :
  c_step_v3 p n hp j i ≤ M p 1 := by
    by_cases hi'' : i = v p n hp 1;
    · rw [ hi'' ];
      exact le_trans ( lemma_c_step_v3_mono p n hp ( v p n hp 1 ) j ( v p n hp 1 ) ( by linarith ) ( by linarith ) ) ( lemma_bound_at_v1 p n hp );
    · -- Since $i \neq v_1$, we have $i < v_1$.
      have hi_lt_v1 : i < v p n hp 1 := by
        exact lt_of_le_of_ne ( by simpa using hi ) hi'';
      exact lemma_bound_k1_v4 p n hp hn j i hi_lt_v1 h_ge

/-
If the coefficient at step j is bounded by M_2, then the scalars used in step j are a subset of S.
-/
theorem lemma_used_s_subset_S_of_bound_M2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ)
  (h_bound : c_step_v3 p n hp j j ≤ M p 2) :
  used_s_v3 p n hp j ⊆ S p := by
    apply lemma_used_s_v3_subset_S;
    unfold M at h_bound; aesop;

/-
For indices in the first interval (v5), the coefficient at step j is bounded by M_1.
-/
theorem lemma_bound_k1_v5_new (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) (j : ℕ)
  (i : ℕ) (hi : in_interval_v5 p n hp 1 i)
  (h_ge : i ≥ j) :
  c_step_v3 p n hp j i ≤ M p 1 := by
    -- Unfold in_interval_v5 to see i <= v_1
    unfold in_interval_v5 at hi
    simp only [if_pos rfl] at hi
    -- Split cases i < v_1 or i = v_1
    by_cases h_lt : i < v p n hp 1
    · -- Case i < v_1
      have h_in_v4 : in_interval_v4 p n hp 1 i := by
        unfold in_interval_v4
        simp only [if_pos rfl]
        exact h_lt
      apply lemma_bound_k1_v4 p n hp hn j i h_in_v4 h_ge
    · -- Case i = v_1
      have h_eq : i = v p n hp 1 := by
        push_neg at h_lt
        exact le_antisymm hi h_lt
      subst h_eq
      -- Use monotonicity and bound at v_1
      have h_mono : c_step_v3 p n hp j (v p n hp 1) ≤ c_step_v3 p n hp (v p n hp 1) (v p n hp 1) := by
        apply lemma_c_step_v3_mono p n hp (v p n hp 1) j (v p n hp 1)
        · exact h_ge
        · exact le_refl _
      have h_bound : c_step_v3 p n hp (v p n hp 1) (v p n hp 1) ≤ M p 1 := by
        apply lemma_bound_at_v1 p n hp
      exact le_trans h_mono h_bound

/-
p is not a power of 2.
-/
theorem lemma_p_not_pow2 (p : ℕ) (hp : Odd p ∧ p > 1) : ∀ k, p ≠ 2^k := by
  grind

/-
The invariant holds at step 0.
-/
theorem lemma_invariant_v5_base (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) :
  Lemma3_invariant_v5 p n hp 0 := by
    have := @lemma_coeff_bound_v5_base;
    exact ⟨ this p n hp hn, by unfold UpdateConditionUpTo_v5; aesop ⟩

/-
If j is in interval k_j and s is bounded by u_{k_j+1}, then the target index is bounded by v_{k_j+1}.
-/
theorem lemma_target_le_v_next_v5 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (k_j : ℕ) (s : ℕ)
  (hk_j : 1 ≤ k_j ∧ k_j < K p)
  (hj : in_interval_v5 p n hp k_j j)
  (hs : s ≤ u p (k_j + 1))
  (hs_pos : s > 0)
  (hs_in_A : s ∈ A p) :
  target_index p j s ≤ v p n hp (k_j + 1) := by
    apply target_index_bound_by_v
    aesop;
    · -- By definition of $a_seq$, we know that $a_seq p j \leq a_seq p (v p n hp k_j)$.
      have h_a_seq_le : a_seq p j ≤ a_seq p (v p n hp k_j) := by
        unfold in_interval_v5 at hj;
        unfold a_seq;
        unfold A at *; aesop;
      convert h_a_seq_le using 1;
      exact Eq.symm (v_spec p n hp k_j);
    · exact hs;
    · assumption

/-
Scalars used in interval k >= 2 are bounded by u_{k+1}.
-/
theorem lemma_scalar_bound_v5_ge2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (k : ℕ) (hk : 2 ≤ k ∧ k < K p) (hj : in_interval_v5 p n hp k j)
  (hc_upper : CoeffBound_v5 p n hp j) :
  ∀ s ∈ used_s_v3 p n hp j, s ≤ u p (k + 1) := by
    -- Apply the lemma that states if the coefficient bound holds for a step in an interval k >= 2, then the scalars used in that step are bounded by u_{k+1}.
    apply lemma_scalar_bound_v3_ge2;
    · exact hk;
    · unfold in_interval_v5 at hj; aesop;
    · unfold CoeffBound_v5 at hc_upper; unfold CoeffBound_v3; aesop;

/-
M_k is at least 1 for 1 <= k <= K.
-/
theorem lemma_M_ge_one_upto_K (p : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ K p) :
  M p k ≥ 1 := by
    exact M_ge_one_of_le_K p hp k hk

/-
u_2 is at least p.
-/
theorem lemma_u2_ge_p (p : ℕ) (hp : Odd p ∧ p > 1) : u p 2 ≥ p := by
  exact p_le_u2 p hp

/-
clog 2 p + 1 < p for p >= 5.
-/
theorem lemma_clog_lt_p_of_ge_5 (p : ℕ) (hp : p ≥ 5) : Nat.clog 2 p + 1 < p := by
  induction' p using Nat.strong_induction_on with p ih;
  rcases hp with ( _ | _ | _ | _ | _ | p ) <;> simp +arith +decide [ Nat.clog_of_two_le ] at *;
  have := ih ( ( ‹_› + 6 ) / 2 ) ( by omega ) ( by omega );
  omega

/-
u_k > 1 for 2 <= k <= K.
-/
theorem lemma_u_gt_one_upto_K (p : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : 2 ≤ k ∧ k ≤ K p) :
  u p k > 1 := by
    rcases k with ( _ | _ | _ | k ) <;> simp_all +arith +decide [ Nat.le_log_iff_pow_le ];
    · exact le_trans ( by linarith ) ( lemma_u2_ge_p p hp );
    · rw [ u ];
      · exact le_self_pow ( by norm_num ) ( by linarith [ lemma_M_ge_one_upto_K p hp ( k + 3 ) ⟨ by linarith, by linarith ⟩ ] );
      · grind;
      · grind;
      · grind

/-
Definition of the transformation step for the final algorithm. It combines the logic for k < m (using S) and k >= m (using even powers of 2).
-/
noncomputable def step_transform_final (p n : ℕ) (hp : Odd p ∧ p > 1) (c : ℕ → ℕ) (k : ℕ) : ℕ → ℕ :=
  if k < m p n hp then
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

/-
Recursive definition of the coefficients after each step of the final algorithm.
-/
noncomputable def c_step_final (p n : ℕ) (hp : Odd p ∧ p > 1) : ℕ → ℕ → ℕ
| 0 => c_init p n hp
| k + 1 => step_transform_final p n hp (c_step_final p n hp k) k

/-
Definition of the set of scalars used in step j of the final algorithm.
-/
noncomputable def used_s_final (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) : Finset ℕ :=
  let c := c_step_final p n hp j j
  if j < m p n hp then
    decompose_S p hp c
  else
    if c > 1 then decompose_even_pow2 c else ∅

/-
Definition of the final coefficient at index i after the transformation process is complete.
-/
noncomputable def c_final_val (p n : ℕ) (hp : Odd p ∧ p > 1) (i : ℕ) : ℕ :=
  c_step_final p n hp (final_step_index p n hp) i

/-
Definition of the list of final summands. It filters the indices where the final coefficient is 1 and maps them to the corresponding sequence elements.
-/
noncomputable def final_summands_list (p n : ℕ) (hp : Odd p ∧ p > 1) : List ℕ :=
  ((List.range (final_step_index p n hp)).filter (fun i => c_final_val p n hp i = 1)).map (a_seq p)

/-
Properties of the scalars used in the final algorithm: they are in A_p and strictly greater than 1.
-/
theorem lemma_used_s_final_properties (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) :
  ∀ s ∈ used_s_final p n hp k, s ∈ A p ∧ s > 1 := by
    simp [used_s_final];
    split_ifs <;> simp_all +decide [ decompose_S, decompose_even_pow2 ];
    · exact fun s a ↦ decompose_S_properties p hp (c_step_final p n hp k k) s a;
    · split_ifs <;> simp_all +decide [ Nat.even_iff, Nat.odd_iff, A ];
      · intro a ha; induction a <;> simp_all +decide [ Nat.bitIndices ] ;
        · rw [ Nat.binaryRec ] at ha ; aesop;
        · exact ⟨ ‹_› + 1, 0, by norm_num ⟩;
      · intro a ha; rw [ ← Nat.mod_add_div ( c_step_final p n hp k k ) 2 ] at *; simp_all +decide [ Nat.even_iff, Nat.odd_iff, Nat.add_mod, Nat.mul_mod, Nat.pow_mod ] ;
        exact ⟨ ⟨ a, 0, by norm_num ⟩, by linarith [ ha.choose_spec ] ⟩

/-
The sum of the scalars used in step k is less than or equal to the coefficient at index k.
-/
theorem lemma_used_s_final_sum_le (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) :
  (used_s_final p n hp k).sum id ≤ c_step_final p n hp k k := by
    unfold used_s_final;
    split_ifs <;> simp_all +decide [ decompose_S, decompose_even_pow2 ];
    · split_ifs <;> norm_num;
      all_goals generalize_proofs at *;
      exact ‹∃ s ⊆ S p, ∑ x ∈ s, x = c_step_final p n hp k k›.choose_spec.2.le;
    · split_ifs <;> norm_num;
      · -- The sum of the powers of 2 in the binary representation of a number is exactly that number.
        have h_sum_powers_of_two : ∀ n : ℕ, (∑ x ∈ (List.map (fun x => 2 ^ x) (Nat.bitIndices n)).toFinset, x) = n := by
          intro n;
          have h_sum_powers_of_two : ∀ n : ℕ, (∑ x ∈ (List.map (fun x => 2 ^ x) (Nat.bitIndices n)).toFinset, x) = n := by
            intro n
            have h_binary : n = ∑ x ∈ (Nat.bitIndices n).toFinset, 2 ^ x := by
              exact Eq.symm (Finset.twoPowSum_toFinset_bitIndices n)
            convert h_binary.symm using 1;
            refine' Finset.sum_bij ( fun x hx => Nat.log 2 x ) _ _ _ _ <;> norm_num;
          exact h_sum_powers_of_two n;
        rw [ h_sum_powers_of_two ];
      · -- The sum of the elements in the list of powers of 2 is equal to the binary representation of the number.
        have h_sum_eq_binary : ∑ x ∈ (List.map (fun x => 2 ^ x) (Nat.bitIndices (c_step_final p n hp k k - 1))).toFinset, x = Nat.ofDigits 2 (Nat.digits 2 (c_step_final p n hp k k - 1)) := by
          have h_sum_eq_binary : ∀ (n : ℕ), ∑ x ∈ (List.map (fun x => 2 ^ x) (Nat.bitIndices n)).toFinset, x = Nat.ofDigits 2 (Nat.digits 2 n) := by
            intro n;
            induction' n using Nat.strong_induction_on with n ih;
            rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> simp_all +decide [ Nat.ofDigits ];
            · by_cases hk : k = 0 <;> simp_all +decide [ Nat.ofDigits_eq_foldr ];
              convert congr_arg ( fun x => 2 * x ) ( ih k ( by linarith [ Nat.pos_of_ne_zero hk ] ) ) using 1;
              · rw [ Finset.mul_sum _ _ _ ];
                refine' Finset.sum_bij ( fun x hx => x / 2 ) _ _ _ _ <;> simp_all +decide [ Function.comp ];
                · exact fun a ha => ⟨ a, ha, by norm_num [ Nat.pow_succ' ] ⟩;
                · exact fun x hx => ⟨ x, hx, Nat.div_eq_of_eq_mul_left zero_lt_two <| by ring ⟩;
                · exact fun a ha => by rw [ Nat.mul_div_cancel' ( dvd_pow_self _ ( Nat.succ_ne_zero _ ) ) ] ;
              · cases k <;> norm_num [ Nat.mul_mod, Nat.mul_div_assoc ] at *;
            · convert congr_arg ( fun x => 2 * x ) ( ih k ( by linarith ) ) using 1;
              · rw [ Finset.mul_sum _ _ _ ];
                refine' Finset.sum_bij ( fun x hx => x / 2 ) _ _ _ _ <;> simp_all +decide [ Function.comp ];
                · exact fun x hx => ⟨ x, hx, by rw [ Nat.pow_succ', Nat.mul_div_cancel_left _ ( by decide ) ] ⟩;
                · exact fun x hx => ⟨ x, hx, by norm_num [ Nat.pow_succ' ] ⟩;
                · exact fun a ha => by rw [ Nat.mul_div_cancel' ( dvd_pow_self _ ( Nat.succ_ne_zero _ ) ) ] ;
              · norm_num [ Nat.add_div ];
          apply h_sum_eq_binary;
        rw [ h_sum_eq_binary, Nat.ofDigits_digits ] ; omega

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
The invariant holds at the start of the final algorithm (step 0).
-/
theorem lemma_invariant_final_base (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) :
  Lemma3_invariant_final p n hp 0 := by
    constructor;
    · have := @lemma_coeff_bound_v4_base p n hp hn;
      unfold in_interval_v4 at this; aesop;
    · unfold UpdateConditionUpTo_final; aesop;

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
The sequence v is strictly increasing for k >= 1.
-/
theorem lemma_v_strict_mono_final (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : 1 ≤ k ∧ k < K p) :
  v p n hp k < v p n hp (k + 1) := by
    exact v_strict_mono p n hp k hk

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
If the target index corresponds to a power of 2, then p cannot be a contributing scalar.
-/
theorem lemma_contributing_scalars_not_p_if_pow2_final (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ)
  (h_pow2 : ∃ r, a_seq p i = 2^r)
  (s : ℕ) (hs : s ∈ contributing_s_final_v2_up_to p n hp j i) :
  s ≠ p := by
    obtain ⟨j', hj', hs'⟩ : ∃ j', j' < j ∧ s ∈ used_s_final_v2 p n hp j' ∧ target_index p j' s = i := by
      unfold contributing_s_final_v2_up_to at hs; aesop;
    have h_s_pow2 : ∃ r, s = 2 ^ r := by
      have := lemma_s_is_pow2_of_target_pow2 p ( by linarith ) j' s ( by
        exact lemma_used_s_final_v2_properties p n hp j' s hs'.1 |>.1 ) i ( by
        exact hs'.2 ) h_pow2; aesop;
    grind

/-
If the target index corresponds to a power of 2, then p cannot be a contributing scalar.
-/
theorem lemma_contributing_scalars_not_p_if_pow2_final_v2 (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ)
  (h_pow2 : ∃ r, a_seq p i = 2^r)
  (s : ℕ) (hs : s ∈ contributing_s_final_v2_up_to p n hp j i) :
  s ≠ p := by
    apply_mod_cast lemma_contributing_scalars_not_p_if_pow2_final p n hp j i h_pow2 s hs

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
If the target is a power of 2, the contributing scalars are a subset of S \ {p}.
-/
theorem lemma_contributing_subset_S_erase_p (p n : ℕ) (hp : Odd p ∧ p > 1) (j i : ℕ)
  (hi : in_interval_final p n hp 1 i)
  (h_ge : i ≥ j)
  (h_prev : ∀ j' < j, CoeffBound_final p n hp j')
  (h_pow2 : ∃ r, a_seq p i = 2^r) :
  contributing_s_final_v2_up_to p n hp j i ⊆ (S p).erase p := by
    -- By definition of contributing_s_final_v2_up_to, if s is in this set, then s is in S p and s is not equal to p.
    intros s hs
    have hs_S : s ∈ S p := by
      have := lemma_contributing_subset_S_final p n hp j i hi h_ge h_prev; aesop;
    have hs_ne_p : s ≠ p := by
      apply lemma_contributing_scalars_not_p_if_pow2_final_v2 p n hp j i h_pow2 s hs;
    exact Finset.mem_erase_of_ne_of_mem hs_ne_p hs_S

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
An odd number greater than 1 is not a power of 2.
-/
theorem odd_gt_one_not_pow2 (x : ℕ) (h_odd : Odd x) (h_gt_1 : x > 1) : ∀ k, x ≠ 2^k := by
  intro k hk; rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.pow_succ' ] ;
  exact absurd h_odd ( by simp +decide [ parity_simps ] )

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
Characterization of in_interval_final.
-/
theorem lemma_in_interval_range (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ K p) (j : ℕ) :
  in_interval_final p n hp k j ↔ (if k = 1 then j < v p n hp 1 else v p n hp (k - 1) ≤ j ∧ j < v p n hp k) := by
    exact Eq.to_iff rfl

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
For indices in the first interval, the contributing scalars are a subset of S.
-/
theorem lemma_contributing_subset_S_final_interval_1 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (i : ℕ)
  (hi : in_interval_final p n hp 1 i)
  (h_ge : i ≥ j)
  (h_prev : ∀ j' < j, CoeffBound_final p n hp j') :
  contributing_s_final_v2_up_to p n hp j i ⊆ S p := by
    exact lemma_contributing_subset_S_final p n hp j i hi h_ge h_prev

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
If the target is a power of 2, the number of contributing scalars in interval 1 is at most |S| - 1.
-/
theorem lemma_card_contributing_le_S_sub_one_final_if_pow2_I1 (p n : ℕ) (hp : Odd p ∧ p > 1) (j : ℕ) (i : ℕ)
  (hi : in_interval_final p n hp 1 i)
  (h_ge : i ≥ j)
  (h_prev : ∀ j' < j, CoeffBound_final p n hp j')
  (h_pow2 : ∃ r, a_seq p i = 2^r) :
  (contributing_s_final_v2_up_to p n hp j i).card ≤ (S p).card - 1 := by
    exact lemma_card_contributing_le_S_sub_one_final_if_pow2 p n hp j i hi h_ge h_prev h_pow2

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
The set of scalars contributing to index v_K from steps j < v_K is empty.
-/
theorem lemma_contributing_empty_at_vK_final (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) :
  contributing_s_final_v2_up_to p n hp (v p n hp (K p)) (v p n hp (K p)) = ∅ := by
    rw [ Finset.eq_empty_iff_forall_notMem ];
    intro x hx;
    -- Since $x$ is in the union, there exists some $j < v_K$ such that $x$ is in the used scalars of $j$ and targets $v_K$.
    obtain ⟨j, hj₁, hj₂⟩ : ∃ j < v p n hp (K p), x ∈ used_s_final_v2 p n hp j ∧ target_index p j x = v p n hp (K p) := by
      unfold contributing_s_final_v2_up_to at hx; aesop;
    have := lemma_target_lt_vK_of_lt_vK_final p n hp hn j hj₁ ( lemma_invariant_final_holds p n hp hn j |> And.left ) x hj₂.left; aesop;

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
The set of scalars used in step v_K is empty.
-/
theorem lemma_used_s_empty_at_vK (p n : ℕ) (hp : Odd p ∧ p > 1) (hn : n > 0) :
  used_s_final_v2 p n hp (v p n hp (K p)) = ∅ := by
    rw [used_s_final_v2];
    rw [ if_neg, if_neg ];
    · -- By definition of `c_step_final_v2`, we know that `c_step_final_v2 p n hp (v p n hp (K p)) (v p n hp (K p))` is the coefficient at index `v p n hp (K p)` after `v p n hp (K p)` steps.
      have h_coeff : c_step_final_v2 p n hp (v p n hp (K p)) (v p n hp (K p)) = 0 := by
        exact lemma_c_step_at_vK_eq_zero p n hp hn;
      linarith;
    · have := @lemma_v_ge_v1 p n hp ( K p ) ( by linarith [ K_ge_2 p ] ) ( by linarith [ K_ge_2 p ] );
      rw [ v_1_eq_m_sub_1 ] at this ; omega

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
The target contribution at the source index k is zero.
-/
theorem lemma_sum_targets_term_k_is_zero (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) :
  (if ∃ s ∈ used_s_final_v2 p n hp k, target_index p k s = k then 1 else 0) = 0 := by
    have := @lemma_target_gt_source_final;
    grind

/-
If the term at k is zero, the sum excluding k is equal to the total sum.
-/
theorem lemma_sum_delta_without_k (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (S : ℕ) (delta : ℕ → ℕ)
  (h_k_lt : k < final_step_index p n hp)
  (h_sum_all : ∑ i ∈ Finset.range (final_step_index p n hp), delta i * a_seq p i = S)
  (h_delta_k : delta k = 0) :
  ∑ i ∈ (Finset.range (final_step_index p n hp)).erase k, delta i * a_seq p i = S := by
    simp +decide [ ← h_sum_all, h_delta_k, Finset.sum_erase ]

/-
The sum of target contributions excluding index k is equal to the total scalar sum.
-/
theorem lemma_sum_diff_k_eq_sum_scalars (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (U : Finset ℕ)
  (h_sum_targets : ∑ i ∈ Finset.range (final_step_index p n hp), (if ∃ s ∈ U, target_index p k s = i then 1 else 0) * a_seq p i = U.sum id * a_seq p k)
  (h_delta_k_zero : (if ∃ s ∈ U, target_index p k s = k then 1 else 0) = 0)
  (h_k_lt : k < final_step_index p n hp) :
  ∑ i ∈ (Finset.range (final_step_index p n hp)).erase k, (if ∃ s ∈ U, target_index p k s = i then 1 else 0) * a_seq p i = U.sum id * a_seq p k := by
    rw [ ← h_sum_targets, Finset.sum_erase ] ; aesop

/-
The sum of a term that is non-zero only at k is equal to the value at k.
-/
theorem lemma_sum_correction_term (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (S : ℕ)
  (h_k_lt : k < final_step_index p n hp) :
  ∑ i ∈ Finset.range (final_step_index p n hp), (if i = k then S else 0) * a_seq p i = S * a_seq p k := by
    rw [ Finset.sum_eq_single k ] <;> aesop

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
The coefficient at step k (for k < m-1) is at least M_0.
-/
theorem lemma_c_step_v3_ge_M0 (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : k < m p n hp - 1) :
  c_step_v3 p n hp k k >= M_0 p := by
    -- Since $c_step_v3 0 k = c_init k$, we can use the fact that $c_init k \geq M_0 p$ to conclude $c_step_v3 k k \geq M_0 p$.
    have h_c_init_k_ge_M0 : c_init p n hp k ≥ M_0 p := by
      apply c_init_ge_M0 p n hp k;
      convert hk using 1;
      exact v_1_eq_m_sub_1 p n hp;
    refine le_trans h_c_init_k_ge_M0 ?_;
    convert lemma_c_step_v3_mono p n hp k 0 k _ _ <;> norm_num

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
If the target is a power of 2, then the contributing scalars are disjoint from the odd elements of S.
-/
theorem lemma_contributing_s_disjoint_odd_if_target_pow2 (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ)
  (h_pow2 : ∃ r, a_seq p k = 2^r) :
  Disjoint (contributing_s_final_v2_up_to p n hp k k) (Finset.filter Odd (S p)) := by
    -- If a scalar is in the contributing set, it must be a power of 2, hence even. Therefore, it cannot be in the odd part of S_p.
    have h_even : ∀ s ∈ contributing_s_final_v2_up_to p n hp k k, Even s := by
      intro s hs
      obtain ⟨j, hj, hs⟩ := Finset.mem_biUnion.mp hs;
      have h_pow2_s : ∃ r, s = 2^r := by
        have := lemma_s_is_pow2_of_target_pow2 p ( by linarith ) j s ( by
          exact lemma_used_s_final_v2_properties p n hp j s ( by aesop ) |>.1 ) k ( by
          aesop ) h_pow2; aesop;
      rcases h_pow2_s with ⟨ r, rfl ⟩ ; rcases r with ( _ | r ) <;> simp_all +decide [ Nat.pow_succ' ] ;
      have := lemma_used_s_final_v2_properties p n hp j 1 hs.1; aesop;
    simp_all +decide [ Finset.disjoint_left, Nat.even_iff ]

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
For k < m - 1, the coefficient at step k is at least M_0.
-/
theorem lemma_c_step_final_v2_ge_M0_lt_m (p n : ℕ) (hp : Odd p ∧ p > 1) (k : ℕ) (hk : k < m p n hp - 1) :
  c_step_final_v2 p n hp k k ≥ M_0 p := by
    have h_c_step_ge_init : c_step_final_v2 p n hp k k ≥ c_init p n hp k := by
      have h_nonneg : 0 ≤ (contributing_s_final_v2_up_to p n hp k k).card := by
        exact Nat.zero_le _
      rw [ lemma_c_step_final_eq_init_plus_card ] <;> aesop;
    refine le_trans ?_ h_c_step_ge_init;
    unfold c_init; aesop;

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

theorem A_3_eq : A 3 = {n | ∃ k l : ℕ, n = 2^k * 3^l} := by
  exact rfl

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

theorem density_unique {S : Set ℕ} {a b : ℝ} (ha : HasDensity S a) (hb : HasDensity S b) : a = b := by
  exact tendsto_nhds_unique ha hb

theorem f_injective : Function.Injective (fun (x : ℕ × ℕ) => 2^x.1 * 3^x.2) := by
  exact fun x y h => by have := congr_arg ( fun n : ℕ => ( n.factorization 2, n.factorization 3 ) ) h; norm_num at this; aesop;

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
