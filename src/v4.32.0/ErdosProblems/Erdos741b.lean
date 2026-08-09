/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 741.
https://www.erdosproblems.com/forum/thread/741

Informal authors:
- GPT-5.4 Pro
- Przemek Chojecki

Formal authors:
- Aristotle
- Przemek Chojecki

URLs:
- https://www.erdosproblems.com/forum/thread/741#post-5771
- https://www.ulam.ai/research/erdos741.pdf
- https://www.ulam.ai/research/erdos741.lean
-/
/-
# Erdős Problem 741

We formalize three results about Erdős problem #741:

1. **Upper density version is true**: If A ⊆ ℕ has ūd(A+A) > 0, then there is a partition
   A = A₁ ⊔ A₂ such that ūd(A₁+A₁) > 0 and ūd(A₂+A₂) > 0.

2. **Strict natural-density version is false**: There exists A ⊆ ℕ with d(A+A) = 1, but
   for every partition A = A₁ ⊔ A₂, it is not the case that both d(A₁+A₁) and d(A₂+A₂)
   exist and are positive.

3. **Syndetic question is affirmative**: There exists a basis A of order 2 such that for
   every partition A = A₁ ⊔ A₂, at least one of A₁+A₁ and A₂+A₂ is not syndetic.
-/
import Mathlib

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Erdos741b

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
-- Several generated density and sumset arguments time out at the default heartbeat limit.
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false
open Classical in
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 800000
-- The generated early construction lemmas need extra heartbeats.

noncomputable section

/-! ## Definitions -/

/-- Count of elements of S in {0, 1, ..., N-1}. -/
def countIn (S : Set ℕ) (N : ℕ) : ℕ :=
  (Finset.range N).filter (· ∈ S) |>.card

/-- Upper density of a set of natural numbers. -/
def upperDensity (S : Set ℕ) : ℝ :=
  Filter.limsup (fun N => (countIn S N : ℝ) / N) Filter.atTop

/-- A set S ⊆ ℕ has natural density d. -/
def HasNatDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun N => (countIn S (N + 1) : ℝ) / (N + 1)) Filter.atTop (nhds d)

/-- A set S ⊆ ℕ is syndetic (has bounded gaps). -/
def IsSyndetic' (S : Set ℕ) : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, ∃ m ∈ S, n ≤ m ∧ m ≤ n + C

/-- A is an asymptotic additive basis of order 2. -/
def IsAsympBasisOrder2 (A : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, n ∈ A + A

/-- A bipartition of a set A into two disjoint parts covering A. -/
structure BiPartition (A : Set ℕ) where
  left : Set ℕ
  right : Set ℕ
  disj : Disjoint left right
  cover : left ∪ right = A

/-- Swap the two sides of a bipartition. -/
def BiPartition.swap {A : Set ℕ} (P : BiPartition A) : BiPartition A where
  left := P.right
  right := P.left
  disj := P.disj.symm
  cover := by rw [Set.union_comm]; exact P.cover

/-! ## Part 3: A basis of order 2 with no syndetic split

The construction is from Alexeev–Putterman–Sawhney–Sellke–Valiant (arXiv:2603.29961, 2026).
For k ≥ 1, define:
  c_k = 4 · 5^(k-1)
  B_k = [5 · 5^(k-1), 6 · 5^(k-1) - 1]
  F_k = [10 · 5^(k-1) - 1, 15 · 5^(k-1)]
  A = [2,3] ∪ ⋃_{k≥1} ({c_k} ∪ B_k ∪ F_k)
-/

/-- The distinguished point at stage k (for k ≥ 1): c_k = 4 · 5^(k-1). -/
def ck (k : ℕ) : ℕ := 4 * 5 ^ (k - 1)

/-- The block Bk = [5 · 5^(k-1), 6 · 5^(k-1) - 1] for k ≥ 1. -/
def Bk (k : ℕ) : Set ℕ := Set.Icc (5 * 5 ^ (k - 1)) (6 * 5 ^ (k - 1) - 1)

/-- The fill block Fk = [10 · 5^(k-1) - 1, 15 · 5^(k-1)] for k ≥ 1. -/
def Fk (k : ℕ) : Set ℕ := Set.Icc (10 * 5 ^ (k - 1) - 1) (15 * 5 ^ (k - 1))

/-- The full basis set A = [2,3] ∪ ⋃_{k≥1} ({c_k} ∪ B_k ∪ F_k). -/
def syndeticA : Set ℕ :=
  Set.Icc 2 3 ∪ ⋃ k ∈ Set.Ici 1, ({ck k} ∪ Bk k ∪ Fk k)

/-- The finite approximation A_k = [2,3] ∪ ⋃_{i=1}^{k} ({c_i} ∪ B_i ∪ F_i). -/
def syndeticA_prefix (k : ℕ) : Set ℕ :=
  Set.Icc 2 3 ∪ ⋃ i ∈ Finset.Icc 1 k, ({ck i} ∪ Bk i ∪ Fk i)

/-- The rigid interval Jk = [9 · 5^(k-1), 10 · 5^(k-1) - 1] for k ≥ 1. -/
def Jk (k : ℕ) : Set ℕ := Set.Icc (9 * 5 ^ (k - 1)) (10 * 5 ^ (k - 1) - 1)

/-- Each syndeticA_prefix k is contained in syndeticA. -/
theorem syndeticA_prefix_sub (k : ℕ) :
    syndeticA_prefix k ⊆ syndeticA := by
  unfold syndeticA_prefix syndeticA
  intro x hx; aesop

/-
syndeticA_prefix k ⊆ syndeticA_prefix (k + 1).
-/
theorem syndeticA_prefix_mono {j k : ℕ} (hjk : j ≤ k) :
    syndeticA_prefix j ⊆ syndeticA_prefix k := by
  simp +decide [ syndeticA_prefix, Set.subset_def ];
  exact fun x hx => hx.imp id fun ⟨ i, hi, hx ⟩ => ⟨ i, ⟨ hi.1, hi.2.trans hjk ⟩, hx ⟩

/-
Base case: [4,6] ⊆ syndeticA_prefix 0 + syndeticA_prefix 0.
-/
theorem basis_stage_zero :
    Set.Icc 4 6 ⊆ syndeticA_prefix 0 + syndeticA_prefix 0 := by
  intro x hx; rcases hx with ⟨ hx₁, hx₂ ⟩ ; interval_cases x <;> simp +decide [ syndeticA_prefix ] ;
  · exact ⟨ 2, by norm_num, 2, by norm_num, by norm_num ⟩;
  · exact ⟨ 2, by norm_num, 3, by norm_num, by norm_num ⟩;
  · exact ⟨ 3, by norm_num, 3, by norm_num, by norm_num ⟩

/-
The interval [2·5^k, 3·5^k] ⊆ syndeticA_prefix (k+1).
-/
theorem interval_in_prefix (k : ℕ) :
    Set.Icc (2 * 5 ^ k) (3 * 5 ^ k) ⊆ syndeticA_prefix (k + 1) := by
  by_cases hk : k = 0;
  · simp +decide [ hk, syndeticA_prefix ];
  · intro x hx
    have hxFk : x ∈ Fk k := by
      unfold Fk; rcases k with ( _ | k ) <;> simp_all +decide [ pow_succ' ] ; omega;
    exact Set.mem_union_right _ <|
      Set.mem_iUnion₂.mpr
        ⟨ k, Finset.mem_Icc.mpr ⟨ Nat.pos_of_ne_zero hk, Nat.le_succ _ ⟩,
          Set.mem_union_right _ hxFk ⟩

/-
The Icc sumset property: Set.Icc a b + Set.Icc c d = Set.Icc (a+c) (b+d) for ℕ,
    when the intervals are nonempty.
-/
theorem Icc_add_Icc_eq (a b c d : ℕ) (hab : a ≤ b) (hcd : c ≤ d) :
    (Set.Icc a b : Set ℕ) + Set.Icc c d = Set.Icc (a + c) (b + d) := by
  rw [ Set.ext_iff ];
  intro x; erw [ Set.mem_add ] ; constructor;
  · grind;
  · simp +zetaDelta at *;
    exact fun hx₁ hx₂ =>
      ⟨ Min.min b ( x - c ), ⟨ by omega, by omega ⟩,
        x - Min.min b ( x - c ), ⟨ by omega, by omega ⟩, by omega ⟩

/-
The basis property: [4, 6·5^k] ⊆ A_k + A_k.

    Proof by induction. Base case k=0: [4,6] = [2,3]+[2,3].
    Inductive step: with Q = 5^k, verify that sums of pairs from the interval
    [2Q,3Q], {4Q}, [5Q,6Q-1], [10Q-1,15Q] cover [4Q,30Q].
    Together with the IH covering [4,6Q], we get [4,30Q] = [4,6·5^(k+1)].
-/
theorem basis_stage (k : ℕ) :
    Set.Icc 4 (6 * 5 ^ k) ⊆ syndeticA_prefix k + syndeticA_prefix k := by
  intro n hn
  induction k generalizing n with
  | zero =>
    exact basis_stage_zero hn;
  | succ k ih =>
    -- By the induction hypothesis, [4, 6Q] is covered at stage k+1.
    have h_ind : Set.Icc 4 (6 * 5 ^ k) ⊆ syndeticA_prefix (k + 1) + syndeticA_prefix (k + 1) := by
      exact fun x hx => by
        rcases ih hx with ⟨ a, ha, b, hb, hab ⟩
        exact
          ⟨ a, syndeticA_prefix_mono ( Nat.le_succ _ ) ha, b,
            syndeticA_prefix_mono ( Nat.le_succ _ ) hb, hab ⟩
    -- For the remaining [6Q+1, 30Q], we use that syndeticA_prefix (k+1) contains:
    -- - I := [2Q, 3Q] (by interval_in_prefix k)
    -- - {ck(k+1)} = {4Q} (stage k+1)
    -- - Bk(k+1) = [5Q, 6Q-1] (stage k+1)
    -- - Fk(k+1) = [10Q-1, 15Q] (stage k+1)
    have h_intervals :
        Set.Icc (2 * 5 ^ k) (3 * 5 ^ k) ⊆ syndeticA_prefix (k + 1) ∧
          {4 * 5 ^ k} ⊆ syndeticA_prefix (k + 1) ∧
            Set.Icc (5 * 5 ^ k) (6 * 5 ^ k - 1) ⊆
              syndeticA_prefix (k + 1) ∧
                Set.Icc (10 * 5 ^ k - 1) (15 * 5 ^ k) ⊆
                  syndeticA_prefix (k + 1) := by
      refine ⟨ interval_in_prefix k, ?_, ?_, ?_ ⟩ <;> simp_all +decide [ syndeticA_prefix ];
      · exact Or.inr
          ⟨ k + 1, ⟨ by linarith, by linarith ⟩,
            Or.inl <| Or.inl <| by unfold ck; simp +decide [ pow_succ' ] ⟩;
      · intro x hx; simp_all +decide [ Set.subset_def ] ;
        refine Or.inr ⟨ k + 1, ⟨ by linarith, by linarith ⟩, ?_ ⟩ ; simp_all +decide [ Bk, Fk ];
      · intro x hx; simp_all +decide [ Set.subset_def ] ;
        exact Or.inr
          ⟨ k + 1, ⟨ by linarith, by linarith ⟩,
            Or.inr <| by unfold Fk; norm_num; omega ⟩;
    -- The pairwise sums are:
    have h_sums :
        Set.Icc (6 * 5 ^ k) (7 * 5 ^ k) ⊆
          syndeticA_prefix (k + 1) + syndeticA_prefix (k + 1) ∧
            Set.Icc (7 * 5 ^ k) (9 * 5 ^ k - 1) ⊆
              syndeticA_prefix (k + 1) + syndeticA_prefix (k + 1) ∧
                Set.Icc (9 * 5 ^ k) (10 * 5 ^ k - 1) ⊆
                  syndeticA_prefix (k + 1) + syndeticA_prefix (k + 1) ∧
                    Set.Icc (10 * 5 ^ k) (12 * 5 ^ k - 2) ⊆
                      syndeticA_prefix (k + 1) + syndeticA_prefix (k + 1) ∧
                        Set.Icc (12 * 5 ^ k - 1) (18 * 5 ^ k) ⊆
                          syndeticA_prefix (k + 1) + syndeticA_prefix (k + 1) ∧
                            Set.Icc (15 * 5 ^ k - 1) (21 * 5 ^ k - 1) ⊆
                              syndeticA_prefix (k + 1) + syndeticA_prefix (k + 1) ∧
                                Set.Icc (20 * 5 ^ k - 2) (30 * 5 ^ k) ⊆
                                  syndeticA_prefix (k + 1) +
                                    syndeticA_prefix (k + 1) := by
      have h_sums :
          ∀ (a b c d : ℕ), a ≤ b → c ≤ d →
            Set.Icc a b + Set.Icc c d = Set.Icc (a + c) (b + d) := by
        exact fun a b c d hab hcd => Icc_add_Icc_eq a b c d hab hcd;
      refine ⟨ ?_, ?_, ?_, ?_, ?_ ⟩;
      · refine Set.Subset.trans ?_ ( Set.add_subset_add h_intervals.1 h_intervals.2.1 );
        norm_num [ Set.subset_def, h_sums ];
        exact fun x hx₁ hx₂ => ⟨ by linarith, by linarith ⟩;
      · refine Set.Subset.trans ?_ ( Set.add_subset_add h_intervals.1 h_intervals.2.2.1 );
        rw [ h_sums ] <;> norm_num;
        · exact Set.Icc_subset_Icc ( by ring_nf; norm_num ) ( by omega );
        · exact Nat.le_sub_one_of_lt ( by linarith [ pow_pos ( by decide : 0 < 5 ) k ] );
      · refine Set.Subset.trans ?_ ( Set.add_subset_add h_intervals.2.1 h_intervals.2.2.1 );
        norm_num [ Set.subset_def, Set.mem_add ];
        exact fun x hx₁ hx₂ => ⟨ by linarith, by omega ⟩;
      · refine Set.Subset.trans ?_ ( Set.add_subset_add h_intervals.2.2.1 h_intervals.2.2.1 );
        rw [ h_sums ];
        · exact Set.Icc_subset_Icc ( by ring_nf; norm_num ) ( by omega );
        · exact Nat.le_sub_one_of_lt ( by linarith [ pow_pos ( by decide : 0 < 5 ) k ] );
        · exact Nat.le_sub_one_of_lt ( by linarith [ pow_pos ( by decide : 0 < 5 ) k ] );
      · refine ⟨ ?_, ?_, ?_ ⟩;
        · refine Set.Subset.trans ?_ ( Set.add_subset_add h_intervals.1 h_intervals.2.2.2 );
          rw [ h_sums ] <;> norm_num;
          · exact Set.Icc_subset_Icc ( by omega ) ( by omega );
          · linarith [ pow_pos ( by decide : 0 < 5 ) k ];
        · refine Set.Subset.trans ?_ ( Set.add_subset_add h_intervals.2.2.1 h_intervals.2.2.2 );
          rw [ h_sums ] <;> norm_num;
          · exact Set.Icc_subset_Icc ( by omega ) ( by omega );
          · exact Nat.le_sub_one_of_lt ( by linarith [ pow_pos ( by decide : 0 < 5 ) k ] );
          · linarith [ pow_pos ( by decide : 0 < 5 ) k ];
        · refine Set.Subset.trans ?_ ( Set.add_subset_add h_intervals.2.2.2 h_intervals.2.2.2 );
          rw [ h_sums ] <;> norm_num;
          · exact Set.Icc_subset_Icc ( by omega ) ( by omega );
          · linarith [ pow_pos ( by decide : 0 < 5 ) k ];
          · linarith [ pow_pos ( by decide : 0 < 5 ) k ];
    grind +splitIndPred

/-- syndeticA is an asymptotic basis of order 2. -/
theorem syndeticA_is_basis : IsAsympBasisOrder2 syndeticA := by
  refine ⟨4, fun n hn => ?_⟩
  have h1 : n ≤ 6 * 5 ^ n := by
    have : n < 5 ^ n := Nat.lt_pow_self (by omega : 1 < 5)
    omega
  have h2 : n ∈ Set.Icc 4 (6 * 5 ^ n) := ⟨hn, h1⟩
  exact Set.add_subset_add (syndeticA_prefix_sub n) (syndeticA_prefix_sub n) (basis_stage n h2)

/-
Rigidity: if n ∈ Jk k (k ≥ 1) and n = a + b with a,b ∈ syndeticA, then
one of a,b is ck k and the other lies in Bk k.
Elements from stages > k are ≥ c_{k+1} = 20·5^(k-1), too large.
Elements from stages < k are ≤ 15·5^(k-2) = 3·5^(k-1), too small in pairs.
The only sums landing in [9·5^(k-1), 10·5^(k-1)-1] use exactly ck k and an
element of Bk k.

Elements of stage j are ≤ 15 · 5^(j-1).
-/
theorem stage_le (j : ℕ) (hj : 1 ≤ j) (x : ℕ)
    (hx : x ∈ ({ck j} : Set ℕ) ∪ Bk j ∪ Fk j) : x ≤ 15 * 5 ^ (j - 1) := by
  rcases hx with ( ( rfl | ⟨ hx₁, hx₂ ⟩ ) | ⟨ hx₃, hx₄ ⟩ )
  all_goals norm_num [ Bk, Fk, ck ] at * <;> omega

/-
Elements of stage j are ≥ ck j = 4 · 5^(j-1).
-/
theorem stage_ge (j : ℕ) (hj : 1 ≤ j) (x : ℕ)
    (hx : x ∈ ({ck j} : Set ℕ) ∪ Bk j ∪ Fk j) : 4 * 5 ^ (j - 1) ≤ x := by
  rcases j with ( _ | _ | j ) <;> simp_all +decide [ Bk, Fk, ck ];
  · omega;
  · omega

/-
All elements of syndeticA are ≥ 2.
-/
theorem syndeticA_ge_two (x : ℕ) (hx : x ∈ syndeticA) : 2 ≤ x := by
  unfold syndeticA at hx
  rcases hx with hx | hx
  · exact hx.1
  · rcases Set.mem_iUnion₂.mp hx with ⟨j, hj, hxj⟩
    exact le_trans (by nlinarith [pow_pos (by decide : 0 < 5) (j - 1)])
      (stage_ge j hj x hxj)

/-
If a ∈ syndeticA and a ≤ M, then a is in [2,3] or in some stage j ≤ k
    provided M < 4 · 5^k (i.e., smaller than the min element of stage k+1).
-/
theorem syndeticA_bounded_stage (x : ℕ) (hx : x ∈ syndeticA) (k : ℕ)
    (hbound : x < 4 * 5 ^ k) :
    x ∈ Set.Icc 2 3 ∨ ∃ j, 1 ≤ j ∧ j ≤ k ∧ x ∈ ({ck j} : Set ℕ) ∪ Bk j ∪ Fk j := by
  -- By definition of syndeticA, x is either in [2,3] or in some stage j ≥ 1.
  obtain ⟨j, hj⟩ : ∃ j, 1 ≤ j ∧ x ∈ ({ck j} : Set ℕ) ∪ Bk j ∪ Fk j ∨ x ∈ Set.Icc 2 3 := by
    unfold syndeticA at hx; aesop;
  exact hj.elim
    (fun h =>
      Or.inr
        ⟨ j, h.1,
          le_of_not_gt fun h' => by
            have := stage_ge j h.1 x h.2
            linarith [
              pow_le_pow_right₀ ( by decide : 1 ≤ 5 ) ( Nat.le_sub_one_of_lt h' ) ],
          h.2 ⟩)
    fun h => Or.inl h

theorem rigid (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : n ∈ Jk k)
    (a b : ℕ) (ha : a ∈ syndeticA) (hb : b ∈ syndeticA) (hab : n = a + b) :
    (a = ck k ∧ b ∈ Bk k) ∨ (b = ck k ∧ a ∈ Bk k) := by
  -- By the properties of syndeticA, we know that a and b must be in [2,3] or in some stage j ≤ k.
  obtain ⟨ja, hja⟩ :
      ∃ ja, 1 ≤ ja ∧ ja ≤ k ∧
        a ∈ ({ck ja} : Set ℕ) ∪ Bk ja ∪ Fk ja ∨ a ∈ Set.Icc 2 3 := by
    have := syndeticA_bounded_stage a ha k ?_;
    · aesop;
    · linarith [
        Set.mem_Icc.mp hn,
        Nat.sub_add_cancel
          ( show 1 ≤ 10 * 5 ^ ( k - 1 ) from Nat.one_le_iff_ne_zero.mpr <| by
            positivity ),
        show 5 ^ k = 5 * 5 ^ ( k - 1 ) by
          rw [ ← pow_succ', Nat.sub_add_cancel hk ] ];
  -- If $ja < k$ or $a \in [2,3]$, then $a \leq 3 \cdot 5^{k-1}$, which is less than $3 \cdot
  -- 5^{k-1}$.
  have ha_bound : a ≤ 3 * 5 ^ (k - 1) ∨ ja = k ∧ a ∈ ({ck k} : Set ℕ) ∪ Bk k ∪ Fk k := by
    by_cases hja_lt_k : ja < k;
    · rcases hja with ( ⟨ hja₁, hja₂, hja₃ ⟩ | ⟨ hja₁, hja₂ ⟩ );
      · have := stage_le ja hja₁ a hja₃;
        exact Or.inl <| le_trans this <| by
          rw [
            show 5 ^ ( k - 1 ) = 5 ^ ( ja - 1 ) * 5 ^ ( k - ja ) by
              rw [ ← pow_add, show k - 1 = ja - 1 + ( k - ja ) by omega ] ]
          nlinarith [
            pow_pos ( show 0 < 5 by decide ) ( ja - 1 ),
            pow_le_pow_right₀ ( show 1 ≤ 5 by decide )
              ( show k - ja ≥ 1 by omega ) ]
      · exact Or.inl ( le_trans hja₂ ( by linarith [ pow_pos ( by decide : 0 < 5 ) ( k - 1 ) ] ) );
    · grind +splitImp;
  -- Similarly, if $jb < k$ or $b \in [2,3]$, then $b \leq 3 \cdot 5^{k-1}$, which is less than $3
  -- \cdot 5^{k-1}$.
  obtain ⟨jb, hjb⟩ :
      ∃ jb, 1 ≤ jb ∧ jb ≤ k ∧
        b ∈ ({ck jb} : Set ℕ) ∪ Bk jb ∪ Fk jb ∨ b ∈ Set.Icc 2 3 := by
    have := syndeticA_bounded_stage b hb k ?_;
    · grind +locals;
    · rcases k with ( _ | k ) <;> simp_all +decide [ pow_succ' ];
      unfold Jk at hn
      norm_num at hn
      linarith [
        Nat.sub_add_cancel
          ( show 1 ≤ 10 * 5 ^ k from Nat.one_le_iff_ne_zero.mpr <| by
            positivity ) ]
  have hb_bound : b ≤ 3 * 5 ^ (k - 1) ∨ jb = k ∧ b ∈ ({ck k} : Set ℕ) ∪ Bk k ∪ Fk k := by
    by_cases h : jb < k;
    · rcases hjb with ( ⟨ hjb₁, hjb₂, hjb₃ ⟩ | hjb₃ );
      · have := stage_le jb hjb₁ b hjb₃;
        exact Or.inl <| this.trans <| by
          rw [
            show 5 ^ ( k - 1 ) = 5 ^ ( jb - 1 ) * 5 ^ ( k - jb ) by
              rw [ ← pow_add, show k - 1 = jb - 1 + ( k - jb ) by omega ] ]
          nlinarith [
            pow_pos ( show 0 < 5 by decide ) ( jb - 1 ),
            pow_le_pow_right₀ ( show 1 ≤ 5 by decide )
              ( show k - jb ≥ 1 by omega ) ]
      · exact Or.inl ( by linarith [ hjb₃.2, pow_pos ( by decide : 0 < 5 ) ( k - 1 ) ] );
    · grind +qlia;
  cases ha_bound <;> cases hb_bound <;> simp_all +decide [ Jk ];
  · grind +suggestions;
  · rcases ‹jb = k ∧ _› with ⟨ rfl, hb | hb ⟩ <;> simp_all +decide [ ck, Bk, Fk ];
    · omega;
    · grind;
  · rcases ‹ja = k ∧ _› with ⟨ rfl, ha | ha ⟩ <;> simp_all +decide [ ck, Bk, Fk ];
    · omega;
    · grind;
  · unfold ck Bk Fk at * ; simp_all +decide [ Set.mem_Icc ];
    omega

/-- If ck k ∉ P.left, then Jk k ∩ (P.left + P.left) = ∅. -/
theorem rigid_gap (k : ℕ) (hk : 1 ≤ k) (P : BiPartition syndeticA)
    (hck : ck k ∉ P.left) :
    ∀ n ∈ Jk k, n ∉ P.left + P.left := by
  intro n hn hsum
  rw [Set.mem_add] at hsum
  obtain ⟨a, ha, b, hb, hab⟩ := hsum
  have ha' : a ∈ syndeticA := P.cover ▸ Set.mem_union_left _ ha
  have hb' : b ∈ syndeticA := P.cover ▸ Set.mem_union_left _ hb
  rcases rigid k hk n hn a b ha' hb' hab.symm with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact hck ‹_›

/-
The Jk interval is nonempty for k ≥ 1.
-/
theorem Jk_nonempty (k : ℕ) (hk : 1 ≤ k) :
    (Jk k).Nonempty := by
  exact Set.nonempty_Icc.2 <|
    Nat.le_sub_one_of_lt <| by
      linarith [ pow_pos ( by decide : 0 < 5 ) ( k - 1 ) ]

/-
If S is syndetic with constant C, and C < 5^(k-1), then S meets Jk k.
-/
theorem syndetic_meets_Jk (k : ℕ) (hk : 1 ≤ k) (S : Set ℕ) (C : ℕ)
    (hS : ∀ n : ℕ, ∃ m ∈ S, n ≤ m ∧ m ≤ n + C) (hC : C < 5 ^ (k - 1)) :
    ∃ m ∈ S, m ∈ Jk k := by
  obtain ⟨ m, hm₁, hm₂, hm₃ ⟩ := hS ( 9 * 5 ^ ( k - 1 ) );
  exact ⟨ m, hm₁, hm₂, Nat.le_sub_one_of_lt <| by linarith ⟩

/-- The length of Jk grows without bound. -/
theorem Jk_length_unbounded : ∀ C : ℕ, ∃ k : ℕ, 1 ≤ k ∧ C < 5 ^ (k - 1) := by
  exact fun C => ⟨C + 2, by linarith,
    Nat.recOn C (by norm_num) fun n ihn => by
      norm_num [Nat.pow_succ'] at *; linarith⟩

/-
ck k ∈ syndeticA for k ≥ 1.
-/
theorem ck_mem_syndeticA (k : ℕ) (hk : 1 ≤ k) : ck k ∈ syndeticA := by
  exact Or.inr <|
    Set.mem_iUnion₂.mpr
      ⟨ k, hk,
        Set.mem_union_left _ <| Set.mem_union_left _ <| Set.mem_singleton _ ⟩

/-- Main Theorem 3: There exists a basis of order 2 such that every bipartition
    leaves at least one monochromatic self-sumset non-syndetic. -/
theorem erdos741_syndetic :
    ∃ A : Set ℕ, IsAsympBasisOrder2 A ∧
      ∀ P : BiPartition A,
        ¬IsSyndetic' (P.left + P.left) ∨ ¬IsSyndetic' (P.right + P.right) := by
  refine ⟨syndeticA, syndeticA_is_basis, fun P => ?_⟩
  by_contra h
  push Not at h
  obtain ⟨⟨CL, hCL⟩, ⟨CR, hCR⟩⟩ := h
  -- Pick k large enough
  obtain ⟨k, hk1, hkC⟩ := Jk_length_unbounded (max CL CR)
  have hCL' : CL < 5 ^ (k - 1) := lt_of_le_of_lt (le_max_left _ _) hkC
  have hCR' : CR < 5 ^ (k - 1) := lt_of_le_of_lt (le_max_right _ _) hkC
  -- ck k is in P.left or P.right
  have hck_mem := ck_mem_syndeticA k hk1
  rw [← P.cover] at hck_mem
  rcases hck_mem with hL | hR
  · -- ck k ∈ P.left ⟹ ck k ∉ P.right ⟹ Jk k misses P.right + P.right
    have hck_not_right : ck k ∉ P.right :=
      fun h => P.disj.ne_of_mem hL h rfl
    -- By rigid_gap on the swapped partition:
    have hgap := rigid_gap k hk1 P.swap hck_not_right
    -- But syndeticity of P.right + P.right means Jk k meets it
    obtain ⟨m, hm_S, hm_J⟩ := syndetic_meets_Jk k hk1 (P.right + P.right) CR hCR hCR'
    exact hgap m hm_J hm_S
  · -- ck k ∈ P.right ⟹ ck k ∉ P.left ⟹ Jk k misses P.left + P.left
    have hck_not_left : ck k ∉ P.left :=
      fun h => P.disj.ne_of_mem h hR rfl
    have hgap := rigid_gap k hk1 P hck_not_left
    obtain ⟨m, hm_S, hm_J⟩ := syndetic_meets_Jk k hk1 (P.left + P.left) CL hCL hCL'
    exact hgap m hm_J hm_S

/-! ## Part 1: The upper-density version is true

Proof sketch: Case 1: If ūd(A) > 0, construct alternating blocks so both parts
have positive upper density, then apply sumset-large lemma.
Case 2: If ūd(A) = 0 but ūd(A+A) > 0, construct alternating blocks so that
at each odd scale the "noise" from A₂ is small.
-/

/-
If a set of naturals is infinite, we can find arbitrarily large elements.
-/
theorem Set.Infinite.exists_gt' {S : Set ℕ} (hS : S.Infinite) (n : ℕ) :
    ∃ m ∈ S, n < m := by
  exact Exists.elim ( hS.exists_gt n ) fun m hm => ⟨ m, hm.1, hm.2 ⟩

/-
For counting-based upper density, limsup along a strict-mono subsequence
    is ≤ the full limsup.
-/
theorem countIn_upperDensity_le_of_subseq (S : Set ℕ) (f : ℕ → ℕ) (hf : StrictMono f)
    (hf_pos : ∀ k, 0 < f k) :
    Filter.limsup (fun k => (countIn S (f k) : ℝ) / (f k)) Filter.atTop ≤ upperDensity S := by
  refine le_csInf ?_ ?_ <;> norm_num;
  · use 1;
    use 1; intro b hb; rw [ div_le_iff₀ ] <;> norm_cast ;
    grind +locals;
  · intro b x hx; refine csInf_le ?_ ?_ <;> norm_num;
    · exact ⟨ 0, by rintro _ ⟨ k, hk ⟩ ; exact le_trans ( by positivity ) ( hk _ le_rfl ) ⟩;
    · exact ⟨ x, fun n hn => hx _ <| hn.trans <| hf.id_le _ ⟩

/-
countIn is monotone in the set argument.
-/
theorem countIn_mono {S T : Set ℕ} (h : S ⊆ T) (N : ℕ) : countIn S N ≤ countIn T N := by
  exact Finset.card_mono <| fun x hx => by aesop;

/-
countIn is monotone in N.
-/
theorem countIn_mono_N (S : Set ℕ) {M N : ℕ} (h : M ≤ N) : countIn S M ≤ countIn S N := by
  unfold countIn
  exact Finset.card_le_card fun x hx => by
    simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
    exact ⟨lt_of_lt_of_le hx.1 h, hx.2⟩

theorem countIn_eq_ncard (S : Set ℕ) (N : ℕ) :
    countIn S N = (S ∩ Set.Iio N).ncard := by
  rw [countIn, ← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [Set.mem_Iio, and_comm]

theorem countIn_add_le_mul (S T : Set ℕ) (N : ℕ) :
    countIn (S + T) N ≤ countIn S N * countIn T N := by
  rw [countIn_eq_ncard (S + T) N, countIn_eq_ncard S N, countIn_eq_ncard T N]
  have hS_fin : (S ∩ Set.Iio N).Finite :=
    (Set.finite_Iio N).subset fun x hx => hx.2
  have hT_fin : (T ∩ Set.Iio N).Finite :=
    (Set.finite_Iio N).subset fun x hx => hx.2
  have hprod_fin : ((S ∩ Set.Iio N) ×ˢ (T ∩ Set.Iio N)).Finite :=
    Set.Finite.prod hS_fin hT_fin
  have hsubset :
      (S + T) ∩ Set.Iio N ⊆
        (fun p : ℕ × ℕ => p.1 + p.2) '' ((S ∩ Set.Iio N) ×ˢ (T ∩ Set.Iio N)) := by
    rintro x ⟨hxsum, hxN⟩
    rw [Set.mem_add] at hxsum
    rcases hxsum with ⟨a, ha, b, hb, rfl⟩
    have haN : a < N := Nat.lt_of_le_of_lt (Nat.le_add_right a b) hxN
    have hbN : b < N := Nat.lt_of_le_of_lt (by omega : b ≤ a + b) hxN
    exact ⟨(a, b), ⟨⟨ha, haN⟩, ⟨hb, hbN⟩⟩, rfl⟩
  calc
    ((S + T) ∩ Set.Iio N).ncard
        ≤ ((fun p : ℕ × ℕ => p.1 + p.2) '' ((S ∩ Set.Iio N) ×ˢ (T ∩ Set.Iio N))).ncard :=
      Set.ncard_le_ncard hsubset (Set.Finite.image _ hprod_fin)
    _ ≤ ((S ∩ Set.Iio N) ×ˢ (T ∩ Set.Iio N)).ncard :=
      Set.ncard_image_le hprod_fin
    _ = (S ∩ Set.Iio N).ncard * (T ∩ Set.Iio N).ncard := by
      rw [Set.ncard_prod]

/-
Key counting lemma: if A₁ = A ∩ ⋃_j (M(2j), M(2j+1)] and N = M(2k+1),
    then countIn A₁ N ≥ countIn A N - countIn A (M(2k) + 1).
    Elements of A not in A₁ that are < M(2k+1) must be ≤ M(2k).
-/
theorem alternating_block_count (A : Set ℕ) (M : ℕ → ℕ) (hM : StrictMono M) (k : ℕ) :
    let A₁ := A ∩ ⋃ j, Set.Ioc (M (2 * j)) (M (2 * j + 1))
    countIn A₁ (M (2 * k + 1)) ≥ countIn A (M (2 * k + 1)) - countIn A (M (2 * k) + 1) := by
  norm_num [ countIn ];
  refine le_trans ?_
    (Finset.card_union_le
      {x ∈ Finset.range (M (2 * k + 1)) |
        x ∈ A ∧ ∃ i, M (2 * i) < x ∧ x ≤ M (2 * i + 1)}
      {x ∈ Finset.range (M (2 * k) + 1) | x ∈ A});
  refine Finset.card_mono ?_;
  intro x hx; by_cases hx' : x ≤ M ( 2 * k ) <;> simp_all +decide [ Finset.subset_iff ] ;
  exact Or.inl ⟨ k, hx', hx.1.le ⟩

/-
Any set with positive upper density can be partitioned into two parts,
    each with positive upper density.
-/
theorem split_positive_upper_density (A : Set ℕ) (hA : upperDensity A > 0) :
    ∃ P : BiPartition A, upperDensity P.left > 0 ∧ upperDensity P.right > 0 := by
  have h_inf : {N : ℕ | (countIn A N : ℝ) / N > upperDensity A / 2}.Infinite := by
    contrapose! hA;
    have h_limsup_le : ∀ᶠ N in Filter.atTop, (countIn A N : ℝ) / N ≤ upperDensity A / 2 := by
      exact Filter.eventually_atTop.mpr
        ⟨ hA.bddAbove.some + 1, fun N hN =>
          not_lt.1 fun contra => not_lt_of_ge ( hA.bddAbove.choose_spec contra ) hN ⟩;
    have h_limsup_le :
        Filter.limsup (fun N => (countIn A N : ℝ) / N) Filter.atTop ≤
          upperDensity A / 2 := by
      refine csInf_le ?_ ?_ <;> norm_num;
      · exact ⟨ 0, by rintro x ⟨ N, hN ⟩ ; exact le_trans ( by positivity ) ( hN _ le_rfl ) ⟩;
      · exact Filter.eventually_atTop.mp h_limsup_le;
    linarith!;
  obtain ⟨M, hM⟩ :
      ∃ M : ℕ → ℕ, StrictMono M ∧
        (∀ k, (countIn A (M k) : ℝ) / (M k) > upperDensity A / 2) ∧
          (∀ k, M (k + 1) > 2 * countIn A (M k + 1) / (upperDensity A / 2)) ∧
            M 0 > 0 := by
    have hM_exists :
        ∀ N : ℕ, ∃ M > N, (countIn A M : ℝ) / M > upperDensity A / 2 ∧
          M > 2 * countIn A (N + 1) / (upperDensity A / 2) := by
      intro N;
      obtain ⟨ M, hM₁, hM₂ ⟩ :=
        h_inf.exists_gt
          ( N + ⌈ ( 2 * countIn A ( N + 1 ) : ℝ ) /
            ( upperDensity A / 2 ) ⌉₊ );
      exact ⟨ M, by linarith, hM₁, Nat.lt_of_ceil_lt ( by linarith ) ⟩;
    choose f hf using hM_exists;
    use fun k => Nat.recOn k ( f 1 ) fun k ih => f ih;
    exact
      ⟨ strictMono_nat_of_lt_succ fun k => hf _ |>.1,
        fun k => Nat.recOn k ( hf _ |>.2.1 ) fun k ih => hf _ |>.2.1,
        fun k => hf _ |>.2.2, hf _ |>.1.trans_le' <| Nat.zero_le _ ⟩;
  -- Define A₁ and A₂ as described.
  set A₁ := A ∩ ⋃ j, Set.Ioc (M (2 * j)) (M (2 * j + 1))
  set A₂ := A \ A₁;
  have hA₁ :
      Filter.limsup
          (fun k => (countIn A₁ (M (2 * k + 1)) : ℝ) / (M (2 * k + 1)))
          Filter.atTop ≥
        upperDensity A / 4 := by
    have hA₁_count :
        ∀ k, (countIn A₁ (M (2 * k + 1)) : ℝ) ≥
          (countIn A (M (2 * k + 1)) : ℝ) -
            (countIn A (M (2 * k) + 1) : ℝ) := by
      intro k;
      have := alternating_block_count A M hM.1 k;
      norm_cast;
      grind +revert;
    have hA₁_lower :
        ∀ k, (countIn A₁ (M (2 * k + 1)) : ℝ) / (M (2 * k + 1)) ≥
          (upperDensity A / 2) -
            (countIn A (M (2 * k) + 1) : ℝ) / (M (2 * k + 1)) := by
      intro k
      specialize hA₁_count k
      specialize hM
      have := hM.2.1 ( 2 * k + 1 )
      simp_all +decide [ div_eq_mul_inv ]
      have := hM.2.1 ( 2 * k + 1 )
      rw [ ← add_mul ]
      exact le_trans this.le ( mul_le_mul_of_nonneg_right ( by linarith ) ( by positivity ) )
    have hA₁_small :
        ∀ k, (countIn A (M (2 * k) + 1) : ℝ) / (M (2 * k + 1)) ≤
          upperDensity A / 4 := by
      intro k
      specialize hM
      have := hM.2.2.1 ( 2 * k )
      rw [ gt_iff_lt, div_lt_iff₀ ] at this <;> try linarith
      rw [ div_le_iff₀ ] <;>
        nlinarith [
          show ( M ( 2 * k + 1 ) : ℝ ) > 0 from Nat.cast_pos.mpr <| by
            linarith [ hM.1 ( show 2 * k < 2 * k + 1 from Nat.lt_succ_self _ ) ] ]
    refine le_csInf ?_ ?_ <;> norm_num;
    · use 1;
      use 1;
      intro k hk
      exact
        div_le_one_of_le₀
          ( mod_cast le_trans
            ( countIn_mono ( show A₁ ⊆ Set.univ from Set.subset_univ _ ) _ )
            ( by simp +decide [ countIn ] ) )
          ( Nat.cast_nonneg _ )
    · intro b x hx
      specialize hx x le_rfl
      linarith [ hA₁_small x, hA₁_lower x ]
  have hA₂ :
      Filter.limsup
          (fun k => (countIn A₂ (M (2 * k + 2)) : ℝ) / (M (2 * k + 2)))
          Filter.atTop ≥
        upperDensity A / 4 := by
    have hA₂_count :
        ∀ k, countIn A₂ (M (2 * k + 2)) ≥
          countIn A (M (2 * k + 2)) - countIn A (M (2 * k + 1) + 1) := by
      intro k
      simp [A₂, countIn];
      refine le_trans ?_
        (Finset.card_union_le
          {x ∈ Finset.range (M (2 * k + 2)) | x ∈ A ∧ x ∉ A₁}
          {x ∈ Finset.range (M (2 * k + 1) + 1) | x ∈ A});
      refine Finset.card_mono ?_;
      intro x hx; by_cases hx' : x ∈ A₁ <;> simp_all +decide [ Finset.subset_iff ] ;
      simp +zetaDelta at *;
      obtain ⟨ i, hi₁, hi₂ ⟩ := hx'.2;
      have hi_succ_le : 2 * i + 1 ≤ 2 * k + 1 :=
        Nat.succ_le_succ <|
          Nat.mul_le_mul_left 2 <|
            Nat.le_of_not_lt fun hi₃ => by
              linarith [
                hM.1.monotone ( show 2 * i ≥ 2 * k + 2 by linarith ) ]
      exact le_trans hi₂ ( hM.1.monotone hi_succ_le )
    have hA₂_lower :
        ∀ k, (countIn A₂ (M (2 * k + 2)) : ℝ) / (M (2 * k + 2)) ≥
          (upperDensity A / 2) -
            (countIn A (M (2 * k + 1) + 1) : ℝ) / (M (2 * k + 2)) := by
      intro k
      have hA₂_bound_step :
          (countIn A₂ (M (2 * k + 2)) : ℝ) ≥
            (countIn A (M (2 * k + 2)) : ℝ) -
              (countIn A (M (2 * k + 1) + 1) : ℝ) := by
        norm_cast;
        rw [ Int.subNatNat_eq_coe ] ; specialize hA₂_count k ; omega;
      have := hM.2.1 ( 2 * k + 2 );
      rw [ ge_iff_le, le_div_iff₀ ] <;>
        nlinarith [
          show ( M ( 2 * k + 2 ) : ℝ ) > 0 from Nat.cast_pos.mpr <| by
            linarith [ hM.1 ( show 2 * k + 2 > 0 from Nat.succ_pos _ ) ],
          div_mul_cancel₀ ( countIn A ( M ( 2 * k + 2 ) ) : ℝ )
            ( show ( M ( 2 * k + 2 ) : ℝ ) ≠ 0 from Nat.cast_ne_zero.mpr <| by
              linarith [ hM.1 ( show 2 * k + 2 > 0 from Nat.succ_pos _ ) ] ),
          div_mul_cancel₀ ( countIn A ( M ( 2 * k + 1 ) + 1 ) : ℝ )
            ( show ( M ( 2 * k + 2 ) : ℝ ) ≠ 0 from Nat.cast_ne_zero.mpr <| by
              linarith [ hM.1 ( show 2 * k + 2 > 0 from Nat.succ_pos _ ) ] ) ]
    have hA₂_small :
        ∀ k, (countIn A (M (2 * k + 1) + 1) : ℝ) / (M (2 * k + 2)) ≤
          upperDensity A / 4 := by
      intros k
      have := hM.right.right.left (2 * k + 1);
      rw [ div_le_iff₀ ] <;>
        nlinarith [
          show ( M ( 2 * k + 2 ) : ℝ ) > 0 from Nat.cast_pos.mpr <| by
            linarith [ hM.1 ( show 0 < 2 * k + 2 from Nat.succ_pos _ ) ],
          mul_div_cancel₀ ( 2 * ( countIn A ( M ( 2 * k + 1 ) + 1 ) : ℝ ) )
            ( ne_of_gt ( half_pos hA ) ) ]
    refine le_csInf ?_ ?_ <;> norm_num;
    · exact
        ⟨ 1, ⟨ 0, fun n hn =>
          div_le_one_of_le₀
            ( mod_cast le_trans
              ( countIn_mono ( show A₂ ⊆ Set.univ from Set.subset_univ _ ) _ )
              ( by simp +decide [ countIn ] ) )
            ( Nat.cast_nonneg _ ) ⟩ ⟩;
    · intro b x hx
      specialize hx x le_rfl
      linarith [ hA₂_small x, hA₂_lower x ]
  have hA₁_pos : upperDensity A₁ ≥ upperDensity A / 4 := by
    refine le_trans hA₁ ?_;
    apply countIn_upperDensity_le_of_subseq;
    · exact hM.1.comp ( strictMono_nat_of_lt_succ fun k => by linarith );
    · exact fun k => by linarith [ hM.1 ( show 0 < 2 * k + 1 from Nat.succ_pos _ ) ] ;
  have hA₂_pos : upperDensity A₂ ≥ upperDensity A / 4 := by
    refine le_trans hA₂ ?_;
    apply countIn_upperDensity_le_of_subseq;
    · exact hM.1.comp ( strictMono_nat_of_lt_succ fun k => by linarith );
    · exact fun k => by linarith [ hM.1 ( show 2 * k + 2 > 0 by linarith ) ] ;
  refine ⟨ ⟨ A₁, A₂, ?_, ?_ ⟩, ?_, ?_ ⟩;
  all_goals norm_num [ Set.disjoint_left ];
  · aesop;
  · exact Set.union_sdiff_cancel ( Set.inter_subset_left );
  · linarith;
  · linarith

/-
The sumset-large lemma: |X_N + X_N| ≥ 2|X_N| - 1 implies ūd(X+X) ≥ ūd(X).
    Uses the Cauchy–Davenport-type bound for finite sets of integers.
-/
theorem upperDensity_sumset_ge (X : Set ℕ) :
    upperDensity (X + X) ≥ upperDensity X := by
  -- Since $X_N + X_N \subseteq (X + X)_{2N}$, we have
  -- $countIn (X + X) (2N) \geq 2 * countIn X N -
  -- 1$.
  have h_count : ∀ N, countIn (X + X) (2 * N) ≥ 2 * countIn X N - 1 := by
    intro N
    have h_cauchy_davenport :
        ∀ (Y : Finset ℕ), Y.Nonempty → (Y + Y).card ≥ 2 * Y.card - 1 := by
      intro Y hY_nonempty
      obtain ⟨y_min, hy_min⟩ : ∃ y_min ∈ Y, ∀ y ∈ Y, y_min ≤ y := by
        exact
          ⟨ Nat.find hY_nonempty, Nat.find_spec hY_nonempty,
            fun y hy => Nat.find_min' hY_nonempty hy ⟩
      obtain ⟨y_max, hy_max⟩ : ∃ y_max ∈ Y, ∀ y ∈ Y, y ≤ y_max := by
        exact
          ⟨ Finset.max' Y hY_nonempty, Finset.max'_mem _ _,
            fun y hy => Finset.le_max' _ _ hy ⟩
      -- Consider the set $\{y_min + y \mid y \in Y\} \cup \{y + y_max \mid y \in Y\}$.
      have h_set :
          (Finset.image (fun y => y_min + y) Y ∪
              Finset.image (fun y => y + y_max) Y).card ≥
            2 * Y.card - 1 := by
        have h_set :
            (Finset.image (fun y => y_min + y) Y ∩
                Finset.image (fun y => y + y_max) Y).card ≤ 1 := by
          exact Finset.card_le_one.mpr fun x hx y hy => by
            obtain ⟨a, ha, ha'⟩ :=
              Finset.mem_image.mp (Finset.mem_inter.mp hx |>.1)
            obtain ⟨b, hb, hb'⟩ :=
              Finset.mem_image.mp (Finset.mem_inter.mp hx |>.2)
            obtain ⟨c, hc, hc'⟩ :=
              Finset.mem_image.mp (Finset.mem_inter.mp hy |>.1)
            obtain ⟨d, hd, hd'⟩ :=
              Finset.mem_image.mp (Finset.mem_inter.mp hy |>.2)
            linarith [
              hy_min.2 a ha, hy_max.2 a ha, hy_min.2 b hb, hy_max.2 b hb,
              hy_min.2 c hc, hy_max.2 c hc, hy_min.2 d hd, hy_max.2 d hd]
        have :=
          Finset.card_union_add_card_inter
            (Finset.image (fun y => y_min + y) Y)
            (Finset.image (fun y => y + y_max) Y)
        simp_all +decide [Finset.card_image_of_injective, Function.Injective]
        omega
      exact h_set.trans <|
        Finset.card_mono <|
          Finset.union_subset
            (Finset.image_subset_iff.mpr fun x hx =>
              Finset.add_mem_add hy_min.1 hx)
            (Finset.image_subset_iff.mpr fun x hx =>
              Finset.add_mem_add hx hy_max.1)
    by_cases hX : (Finset.filter (· ∈ X) (Finset.range N)).Nonempty
    · refine le_trans
        (h_cauchy_davenport {x ∈ Finset.range N | x ∈ X} hX) ?_
      refine Finset.card_mono ?_
      simp +decide [ Finset.subset_iff, Finset.mem_add ];
      exact fun x a ha ha' b hb hb' hx =>
        ⟨ by linarith, hx ▸ Set.add_mem_add ha' hb' ⟩
    · simp_all +decide [ Finset.ext_iff, countIn ];
      rw [ Finset.card_eq_zero.mpr ] <;> aesop;
  -- Taking the limsup of both sides of the inequality, we get $\limsup_{N \to \infty} \frac{countIn
  -- (X + X) (2N)}{2N} \geq \limsup_{N \to \infty} \frac{countIn X N}{N}$.
  have h_limsup :
      Filter.limsup (fun N => (countIn X N : ℝ) / N) Filter.atTop ≤
        Filter.limsup
          (fun N => (countIn (X + X) (2 * N) : ℝ) / (2 * N))
          Filter.atTop := by
    have h_limsup :
        ∀ N ≥ 1,
          (countIn (X + X) (2 * N) : ℝ) / (2 * N) ≥
            (countIn X N : ℝ) / N - 1 / (2 * N) := by
      intro N hN
      rw [ div_sub_div, ge_iff_le, div_le_div_iff₀ ] <;> try positivity
      have := h_count N;
      rcases k : countIn X N with ( _ | k ) <;> simp_all +decide [ Nat.mul_succ ];
      · exact le_trans ( neg_nonpos_of_nonneg ( by positivity ) ) ( by positivity );
      · have h_cast :
            (2 : ℝ) * ↑‹ℕ› + 1 ≤ countIn (X + X) (2 * N) := by
          norm_cast
        nlinarith [h_cast, pow_pos (by positivity : 0 < (N : ℝ)) 2]
    refine le_of_forall_pos_le_add fun ε ε_pos => ?_;
    refine csInf_le ?_ ?_ <;> norm_num;
    · exact ⟨ 0, by rintro x ⟨ N, hN ⟩ ; exact le_trans ( by positivity ) ( hN _ le_rfl ) ⟩;
    · obtain ⟨ N, hN ⟩ := Filter.eventually_atTop.mp (show
          ∀ᶠ N : ℕ in Filter.atTop,
            (countIn (X + X) (2 * N) : ℝ) / (2 * N) ≤
              Filter.limsup
                (fun N : ℕ => (countIn (X + X) (2 * N) : ℝ) / (2 * N))
                Filter.atTop + ε / 2 from
          Filter.eventually_atTop.mpr <| by
            have :=
              exists_lt_of_csInf_lt
                (show
                  { a : ℝ |
                      ∀ᶠ n : ℕ in Filter.atTop,
                        (countIn (X + X) (2 * n) : ℝ) / (2 * n) ≤ a
                    }.Nonempty from ?_)
                (show
                  InfSet.sInf
                      { a : ℝ |
                          ∀ᶠ n : ℕ in Filter.atTop,
                            (countIn (X + X) (2 * n) : ℝ) / (2 * n) ≤ a } <
                    InfSet.sInf
                        { a : ℝ |
                            ∀ᶠ n : ℕ in Filter.atTop,
                              (countIn (X + X) (2 * n) : ℝ) / (2 * n) ≤ a } +
                      ε / 2 from
                  lt_add_of_pos_right _ <| half_pos ε_pos)
            · exact Filter.eventually_atTop.mp this.choose_spec.1 |>
                fun ⟨N, hN⟩ =>
                  ⟨N, fun n hn => le_trans (hN n hn) this.choose_spec.2.le⟩
            · refine ⟨1, Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩⟩
              rw [ div_le_iff₀ ] <;> norm_cast <;> norm_num [ countIn ];
              · grind
              · linarith)
      exact ⟨ N + ⌈ε⁻¹ * 2⌉₊ + 1, fun n hn => by
        have := hN n (by linarith)
        have := h_limsup n (by linarith)
        nlinarith [
          Nat.le_ceil (ε⁻¹ * 2),
          mul_inv_cancel₀ (ne_of_gt ε_pos),
          show (n : ℝ) ≥ N + ⌈ε⁻¹ * 2⌉₊ + 1 by exact_mod_cast hn,
          one_div_mul_cancel
            (by
              norm_cast
              linarith : (2 * n : ℝ) ≠ 0)] ⟩
  refine le_trans h_limsup ?_;
  unfold upperDensity;
  rw [ Filter.limsup_eq, Filter.limsup_eq ];
  refine le_csInf ?_ ?_;
  · refine ⟨ 2, Filter.eventually_atTop.mpr ⟨ 1, fun n hn => ?_ ⟩ ⟩;
    rw [ div_le_iff₀ ] <;> norm_cast;
    grind +locals;
  · intro b hb;
    refine csInf_le ?_ ?_;
    · exact ⟨ 0, fun a ha => by
        rcases Filter.eventually_atTop.mp ha with ⟨N, hN⟩
        exact le_trans (by positivity) (hN _ le_rfl) ⟩
    · filter_upwards [
        hb.filter_mono (Filter.tendsto_id.nsmul_atTop two_pos)] with n hn using by
        simpa [mul_div_mul_left] using hn

/-
Small-summand lemma: if A = A₁ ∪ A₂ and A₂ ∩ [0,N) ⊆ [0,K),
    then |(A+A) ∩ [0,N)| ≤ |(A₁+A₁) ∩ [0,N)| + K·|A ∩ [0,N)|.
    This bounds the contribution of the "small" part.
-/
theorem small_summand_bound (A A₁ A₂ : Set ℕ) (hcover : A₁ ∪ A₂ = A)
    (N K : ℕ) (hA₂ : ∀ x ∈ A₂, x < N → x < K) :
    countIn (A + A) N ≤ countIn (A₁ + A₁) N + K * countIn A N := by
  have h_count_def : countIn (A + A) N ≤ countIn (A₁ + A₁) N + countIn (A + A₂) N := by
    refine le_trans ?_
      (Finset.card_union_le
        {x ∈ Finset.range N | x ∈ A₁ + A₁}
        {x ∈ Finset.range N | x ∈ A + A₂});
    unfold countIn
    refine Finset.card_le_card ?_
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    rw [Finset.mem_union]
    simp only [Finset.mem_filter, Finset.mem_range]
    rcases hx with ⟨hxN, hxsum⟩
    rw [Set.mem_add] at hxsum
    rcases hxsum with ⟨a, haA, b, hbA, rfl⟩
    have haU : a ∈ A₁ ∪ A₂ := by simpa [hcover] using haA
    rcases haU with ha₁ | ha₂
    · have hbU : b ∈ A₁ ∪ A₂ := by simpa [hcover] using hbA
      rcases hbU with hb₁ | hb₂
      · exact Or.inl ⟨hxN, by rw [Set.mem_add]; exact ⟨a, ha₁, b, hb₁, rfl⟩⟩
      · exact Or.inr ⟨hxN, by rw [Set.mem_add]; exact ⟨a, haA, b, hb₂, rfl⟩⟩
    · exact Or.inr ⟨hxN, by
        rw [Set.mem_add]
        exact ⟨b, hbA, a, ha₂, Nat.add_comm b a⟩⟩
  have h_count_def2 : countIn (A + A₂) N ≤ K * countIn A N := by
    have h_decomp :
        ∀ x ∈ (A + A₂) ∩ Set.Iio N,
          ∃ a ∈ A ∩ Set.Iio N, ∃ b ∈ A₂ ∩ Set.Iio K, x = a + b := by
      rintro x ⟨hxsum, hxN⟩
      rw [Set.mem_add] at hxsum
      rcases hxsum with ⟨a, ha, b, hb, rfl⟩
      have haN : a < N := Nat.lt_of_le_of_lt (Nat.le_add_right a b) hxN
      have hbN : b < N := Nat.lt_of_le_of_lt (by omega : b ≤ a + b) hxN
      exact
        ⟨a, ⟨ha, haN⟩, b, ⟨hb, hA₂ b hb hbN⟩, rfl⟩
    have h_card_pairs :
        ((A + A₂) ∩ Set.Iio N).ncard ≤
          (A ∩ Set.Iio N).ncard * (A₂ ∩ Set.Iio K).ncard := by
      have hA_fin : (A ∩ Set.Iio N).Finite :=
        (Set.finite_Iio N).subset fun x hx => hx.2
      have hA₂_fin : (A₂ ∩ Set.Iio K).Finite :=
        (Set.finite_Iio K).subset fun x hx => hx.2
      have hprod_fin : ((A ∩ Set.Iio N) ×ˢ (A₂ ∩ Set.Iio K)).Finite :=
        Set.Finite.prod hA_fin hA₂_fin
      have h_card_pairs :
          ((A + A₂) ∩ Set.Iio N).ncard ≤
            (Set.image (fun p : ℕ × ℕ => p.1 + p.2)
              ((A ∩ Set.Iio N) ×ˢ (A₂ ∩ Set.Iio K))).ncard := by
        refine Set.ncard_le_ncard ?_ (Set.Finite.image _ hprod_fin)
        · exact fun x hx => by
            obtain ⟨a, ha, b, hb, rfl⟩ := h_decomp x hx
            exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
      refine le_trans h_card_pairs ?_
      calc
        (Set.image (fun p : ℕ × ℕ => p.1 + p.2)
            ((A ∩ Set.Iio N) ×ˢ (A₂ ∩ Set.Iio K))).ncard
            ≤ ((A ∩ Set.Iio N) ×ˢ (A₂ ∩ Set.Iio K)).ncard :=
          Set.ncard_image_le hprod_fin
        _ = (A ∩ Set.Iio N).ncard * (A₂ ∩ Set.Iio K).ncard := by
          rw [Set.ncard_prod]
    have h_card_A2 : (A₂ ∩ Set.Iio K).ncard ≤ K := by
      have hIio : (Set.Iio K : Set ℕ).ncard = K := by
        calc
          (Set.Iio K : Set ℕ).ncard = ((Finset.range K : Finset ℕ) : Set ℕ).ncard := by
            congr 1
            ext x
            simp [Set.mem_Iio]
          _ = (Finset.range K).card := Set.ncard_coe_finset _
          _ = K := Finset.card_range K
      exact (Set.ncard_le_ncard (fun x hx => hx.2) (Set.finite_Iio K)).trans
        (le_of_eq hIio)
    rw [countIn_eq_ncard (A + A₂) N, countIn_eq_ncard A N]
    calc
      ((A + A₂) ∩ Set.Iio N).ncard
          ≤ (A ∩ Set.Iio N).ncard * (A₂ ∩ Set.Iio K).ncard := h_card_pairs
      _ ≤ (A ∩ Set.Iio N).ncard * K := Nat.mul_le_mul_left _ h_card_A2
      _ = K * (A ∩ Set.Iio N).ncard := Nat.mul_comm _ K
  exact h_count_def.trans (Nat.add_le_add_left h_count_def2 _)

/-
Upper density is nonneg.
-/
lemma upperDensity_nonneg (S : Set ℕ) : upperDensity S ≥ 0 := by
  apply_rules [ Real.sInf_nonneg ];
  exact fun x hx => le_trans ( by positivity ) ( hx.exists.choose_spec )

/-
If ūd(S) ≤ 0 then countIn S N / N → 0.
-/
lemma upperDensity_le_zero_tendsto (S : Set ℕ) (h : ¬ upperDensity S > 0) :
    ∀ ε > (0 : ℝ), ∃ N₀ : ℕ, ∀ N ≥ N₀, (countIn S N : ℝ) < ε * N := by
      intro ε hε_pos
      have h_limsup : Filter.limsup (fun N => (countIn S N : ℝ) / N) Filter.atTop = 0 := by
        exact le_antisymm ( le_of_not_gt h ) ( upperDensity_nonneg S );
      rw [ Filter.limsup_eq ] at h_limsup;
      have :=
        exists_lt_of_csInf_lt
          (show
            { a : ℝ | ∀ᶠ n in Filter.atTop, (countIn S n : ℝ) / n ≤ a
              }.Nonempty from ?_)
          (show
            sInf { a : ℝ | ∀ᶠ n in Filter.atTop, (countIn S n : ℝ) / n ≤ a } < ε
              by linarith)
      · obtain ⟨a, ha₁, ha₂⟩ := this
        rcases Filter.eventually_atTop.mp ha₁ with ⟨N₀, hN₀⟩
        exact ⟨N₀ + 1, fun N hN => by
          have := hN₀ N (by linarith)
          rw [ div_le_iff₀ ] at this
          · nlinarith [show (N : ℝ) ≥ N₀ + 1 by exact_mod_cast hN]
          · exact_mod_cast lt_of_lt_of_le (Nat.succ_pos N₀) hN ⟩
      · refine
          ⟨ 1, Filter.eventually_atTop.mpr
            ⟨ 1, fun n hn => div_le_one_of_le₀ ?_ <| Nat.cast_nonneg _ ⟩ ⟩
        norm_cast;
        grind +locals

/-
If ūd(S) > 0 then countIn S N / N ≥ ūd(S)/2 for arbitrarily large N.
-/
lemma upperDensity_pos_frequently (S : Set ℕ) (h : upperDensity S > 0) :
    ∀ N₀ : ℕ, ∃ N > N₀, (countIn S N : ℝ) / N ≥ upperDensity S / 2 := by
      have h_inf : Set.Infinite { N : ℕ | (countIn S N : ℝ) / N ≥ upperDensity S / 2 } := by
        by_cases h₂ : ∃ N₀, ∀ N ≥ N₀, (countIn S N : ℝ) / N < upperDensity S / 2;
        · obtain ⟨ N₀, hN₀ ⟩ := h₂;
          have h_limsup :
              Filter.limsup (fun N => (countIn S N : ℝ) / N) Filter.atTop ≤
                upperDensity S / 2 := by
            refine csInf_le ?_ ?_;
            · exact ⟨ 0, fun x hx => by
                rcases Filter.eventually_atTop.mp hx with ⟨N, hN⟩
                exact le_trans (by positivity) (hN _ le_rfl) ⟩
            · exact Filter.eventually_atTop.mpr ⟨ N₀, fun N hN => le_of_lt ( hN₀ N hN ) ⟩;
          linarith!;
        · exact Set.infinite_of_not_bddAbove fun ⟨N₀, hN₀⟩ =>
            h₂ ⟨N₀ + 1, fun N hN =>
              lt_of_not_ge fun hN' => not_lt_of_ge (hN₀ hN') hN⟩
      exact fun N₀ => by
        obtain ⟨ N, hN ⟩ := h_inf.exists_gt N₀
        exact ⟨ N, hN.2, hN.1 ⟩

/-
Case 2 of Theorem 1: ūd(A) ≤ 0 but ūd(A+A) > 0 implies a good partition exists.
-/
theorem erdos741_upper_density_case2 (A : Set ℕ) (hA : ¬ upperDensity A > 0)
    (hAA : upperDensity (A + A) > 0) :
    ∃ P : BiPartition A,
      upperDensity (P.left + P.left) > 0 ∧ upperDensity (P.right + P.right) > 0 := by
        -- Set δ = upperDensity(A+A)/2 > 0. Since ¬(upperDensity A > 0), by
        -- upperDensity_le_zero_tendsto, for any ε > 0, eventually countIn(A, N) < ε*N.
        set δ := upperDensity (A + A) / 2 with hδ;
        -- Choose a sequence M : ℕ → ℕ such that M(0) = 1 and for each k, M(k+1) is large enough so
        -- that
        -- (a) countIn(A+A, M(k+1))/M(k+1) ≥ δ (using upperDensity_pos_frequently)
        -- (b) countIn(A, M(k+1)) < δ/(2*M(k)) * M(k+1) (using upperDensity_le_zero_tendsto with ε =
        -- δ/(2*M(k)))
        obtain ⟨M, hM⟩ :
            ∃ M : ℕ → ℕ,
              StrictMono M ∧
                ∀ k,
                  M 0 = 1 ∧
                    (countIn (A + A) (M (k + 1)) : ℝ) / (M (k + 1)) ≥ δ ∧
                      (countIn A (M (k + 1)) : ℝ) <
                        δ / (2 * M k) * (M (k + 1)) := by
          have h_seq :
              ∀ k : ℕ,
                ∃ N > k,
                  (countIn (A + A) N : ℝ) / N ≥ δ ∧
                    (countIn A N : ℝ) < δ / (2 * (k + 1)) * N := by
            intro k;
            -- By the properties of upper density, we can find such an N.
            obtain ⟨N₁, hN₁⟩ : ∃ N₁ > k, (countIn (A + A) N₁ : ℝ) / N₁ ≥ δ := by
              have := upperDensity_pos_frequently ( A + A ) hAA k; aesop;
            obtain ⟨N₂, hN₂⟩ :
                ∃ N₂ > k,
                  ∀ N ≥ N₂, (countIn A N : ℝ) < δ / (2 * (k + 1)) * N := by
              have := upperDensity_le_zero_tendsto A hA;
              exact
                Exists.elim
                  (this (δ / (2 * (k + 1))) (div_pos (half_pos hAA) (by positivity)))
                  fun N₀ hN₀ =>
                    ⟨N₀ + k + 1, by linarith,
                      fun N hN => hN₀ N (by linarith)⟩
            have h_seq : ∀ N₀ : ℕ, ∃ N > N₀, (countIn (A + A) N : ℝ) / N ≥ δ := by
              apply upperDensity_pos_frequently; exact hAA;
            exact
              Exists.elim (h_seq (Max.max N₁ N₂)) fun N hN =>
                ⟨N, by linarith [le_max_left N₁ N₂, le_max_right N₁ N₂],
                  hN.2, hN₂.2 N
                    (by linarith [le_max_left N₁ N₂, le_max_right N₁ N₂])⟩
          choose f hf using h_seq;
          refine
            ⟨ fun k => Nat.recOn k 1 fun k ih => f ih,
              strictMono_nat_of_lt_succ fun k => ?_, fun k => ?_ ⟩ <;>
            norm_num [ hf ]
          refine lt_of_lt_of_le
            (hf (Nat.recOn k 1 fun k ih => f ih) |>.2.2) ?_;
          gcongr;
          · exact mul_pos zero_lt_two <|
              Nat.cast_pos.mpr <|
                Nat.recOn k (by norm_num) fun k ih => by
                  linarith [hf (Nat.rec 1 (fun k ih => f ih) k)]
          · norm_num;
        -- Define A₁ = A ∩ ⋃_j Set.Ico (M(2*j)) (M(2*j+1)), A₂ = A \ A₁.
        set A₁ := A ∩ ⋃ j, Set.Ico (M (2 * j)) (M (2 * j + 1)) with hA₁
        set A₂ := A \ A₁ with hA₂;
        -- At scale N = M(2k+1): every element x ∈ A₂ with x < M(2k+1) satisfies x < M(2k) (since if
        -- x ≥ M(2k), then x ∈ [M(2j), M(2j+1)) for some j ≤ k, making x ∈ A₁, contradiction). By
        -- small_summand_bound with K = M(2k):
        have hA₁_bound :
            ∀ k,
              countIn (A₁ + A₁) (M (2 * k + 1)) ≥
                δ / 2 * (M (2 * k + 1)) := by
          -- By small_summand_bound with K = M(2k):
          intros k
          have h_small_summand :
              countIn (A + A) (M (2 * k + 1)) ≤
                countIn (A₁ + A₁) (M (2 * k + 1)) +
                  M (2 * k) * countIn A (M (2 * k + 1)) := by
            apply small_summand_bound;
            focus
              exact Set.union_sdiff_cancel ( Set.inter_subset_left )
            intro x hx hx'; contrapose! hx; aesop;
          -- Using the bounds from hM, we can derive the inequality.
          have h_bound :
              (countIn (A + A) (M (2 * k + 1)) : ℝ) ≥
                δ * (M (2 * k + 1)) := by
            have := hM.2 ( 2 * k );
            rw [ ge_iff_le, le_div_iff₀ ] at this <;> norm_num at * <;>
              linarith [hM.1.monotone (show 0 ≤ 2 * k + 1 from Nat.zero_le _)]
          have := hM.2 ( 2 * k );
          rw [ div_mul_eq_mul_div, lt_div_iff₀ ] at this <;> norm_num at *;
          · have h_small_cast :
                (countIn (A + A) (M (2 * k + 1)) : ℝ) ≤
                  countIn (A₁ + A₁) (M (2 * k + 1)) +
                    M (2 * k) * countIn A (M (2 * k + 1)) := by
              norm_cast
            nlinarith [h_small_cast]
          · linarith [ hM.1.monotone ( show 0 ≤ 2 * k by norm_num ) ];
        -- Similarly at scale M(2k+2): elements of A₁ below M(2k+2) are below M(2k+1). By
        -- small_summand_bound (with A₁ and A₂ roles swapped, using hcover: A₂ ∪ A₁ = A):
        have hA₂_bound :
            ∀ k,
              countIn (A₂ + A₂) (M (2 * k + 2)) ≥
                δ / 2 * (M (2 * k + 2)) := by
          intro k
          have hA₂_bound_step :
              countIn (A + A) (M (2 * k + 2)) ≤
                countIn (A₂ + A₂) (M (2 * k + 2)) +
                  M (2 * k + 1) * countIn A (M (2 * k + 2)) := by
            apply small_summand_bound;
            focus
              exact Set.sdiff_union_of_subset ( Set.inter_subset_left )
            simp +zetaDelta at *;
            intro x hx j hj₁ hj₂ hj₃; contrapose! hj₃;
            have hj_ge : j ≥ k + 1 := by
              exact Nat.succ_le_of_lt <| Nat.lt_of_not_ge fun h => by
                have hj_index : 2 * j + 1 ≤ 2 * k + 1 := by linarith
                linarith [hM.1.monotone hj_index]
            exact le_trans (hM.1.monotone (by linarith [hj_ge])) hj₁
          have := hM.2 ( 2 * k + 1 );
          rw [ div_mul_eq_mul_div, lt_div_iff₀ ] at this <;> norm_num at *;
          · rw [ le_div_iff₀ ] at this <;> norm_num at *;
            · have h_step_cast :
                  (countIn (A + A) (M (2 * k + 2)) : ℝ) ≤
                    countIn (A₂ + A₂) (M (2 * k + 2)) +
                      M (2 * k + 1) * countIn A (M (2 * k + 2)) := by
                exact_mod_cast hA₂_bound_step
              nlinarith! [h_step_cast]
            · linarith [ hM.1 ( show 0 < 2 * k + 1 + 1 by linarith ) ];
          · linarith [ hM.1 ( show 0 < 2 * k + 1 from Nat.succ_pos _ ) ];
        -- Using countIn_upperDensity_le_of_subseq, limsup along M(2k+1) ≤ ūd(A₁+A₁). Since limsup ≥
        -- δ/2 (all terms ≥ δ/2), ūd(A₁+A₁) ≥ δ/2 > 0.
        have hA₁_upperDensity : upperDensity (A₁ + A₁) ≥ δ / 2 := by
          refine le_trans ?_ <|
            countIn_upperDensity_le_of_subseq _
              (fun k => M (2 * k + 1))
              (hM.1.comp (strictMono_nat_of_lt_succ fun k => by linarith))
              fun k =>
                lt_of_le_of_lt (Nat.zero_le _) <|
                  hM.1 (show 0 < 2 * k + 1 by linarith)
          · refine le_csInf ?_ ?_ <;> norm_num;
            · refine ⟨ 1, ⟨ 0, fun n hn => ?_ ⟩ ⟩;
              refine div_le_one_of_le₀ ?_ ?_ <;> norm_cast;
              · grind +locals;
              · exact Nat.zero_le _;
            · intro b x hx
              specialize hx x le_rfl
              rw [ div_le_iff₀ ] at hx
              · have hx_pos :
                    (M (2 * x + 1) : ℝ) > 0 := by
                  exact Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by
                    linarith [hM.1 (show 0 < 2 * x + 1 from Nat.succ_pos _)]
                nlinarith [hA₁_bound x, hx_pos]
              · exact Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by
                  linarith [hM.1 (show 0 < 2 * x + 1 from Nat.succ_pos _)]
        -- Similarly, using countIn_upperDensity_le_of_subseq, limsup along M(2k+2) ≤ ūd(A₂+A₂).
        -- Since limsup ≥ δ/2 (all terms ≥ δ/2), ūd(A₂+A₂) ≥ δ/2 > 0.
        have hA₂_upperDensity : upperDensity (A₂ + A₂) ≥ δ / 2 := by
          refine le_trans ?_ <|
            countIn_upperDensity_le_of_subseq _
              (fun k => M (2 * k + 2))
              (hM.1.comp (strictMono_nat_of_lt_succ fun k => by linarith))
              fun k => by
                linarith [hM.1 <| show 2 * k + 2 > 0 from Nat.succ_pos _]
          refine le_csInf ?_ ?_ <;> norm_num;
          · use 1;
            use 1;
            intro k hk; rw [ div_le_iff₀ ] <;> norm_cast <;> norm_num [ countIn ];
            · grind +splitImp;
            · linarith [ hM.1 ( show 0 < 2 * k + 2 by linarith ) ];
          · intro b x hx
            specialize hx x le_rfl
            rw [ div_le_iff₀ ] at hx
            · have hx_pos :
                  (M (2 * x + 2) : ℝ) > 0 := by
                exact Nat.cast_pos.mpr <| by
                  linarith [hM.1 <| show 2 * x + 2 > 0 from Nat.succ_pos _]
              nlinarith [hA₂_bound x, hx_pos]
            · exact Nat.cast_pos.mpr <| by
                linarith [hM.1 <| show 2 * x + 2 > 0 from Nat.succ_pos _]
        use ⟨A₁, A₂, by
          exact disjoint_sdiff_self_right, by
          exact Set.union_sdiff_cancel <| Set.inter_subset_left⟩
        generalize_proofs at *;
        exact
          ⟨ lt_of_lt_of_le (half_pos (half_pos hAA)) hA₁_upperDensity,
            lt_of_lt_of_le (half_pos (half_pos hAA)) hA₂_upperDensity ⟩

theorem erdos741_upper_density (A : Set ℕ) (hA : upperDensity (A + A) > 0) :
    ∃ P : BiPartition A,
      upperDensity (P.left + P.left) > 0 ∧ upperDensity (P.right + P.right) > 0 := by
  by_cases h : upperDensity A > 0
  · -- Case 1: ūd(A) > 0. Split A with both parts positive ūd, then sumset-large.
    obtain ⟨P, hP₁, hP₂⟩ := split_positive_upper_density A h
    exact ⟨P, lt_of_lt_of_le hP₁ (upperDensity_sumset_ge P.left),
           lt_of_lt_of_le hP₂ (upperDensity_sumset_ge P.right)⟩
  · exact erdos741_upper_density_case2 A h hA

/-! ## Part 2: The strict natural-density version is false -/

/-- The base-4 set B₁ = {n : all base-4 digits ∈ {0,1}}. -/
def digitSetB1 : Set ℕ := {n | ∀ r : ℕ, n / 4 ^ r % 4 ∈ ({0, 1} : Set ℕ)}

/-- The base-4 set B₂ = {n : all base-4 digits ∈ {0,2}}. -/
def digitSetB2 : Set ℕ := {n | ∀ r : ℕ, n / 4 ^ r % 4 ∈ ({0, 2} : Set ℕ)}

/-
B₁ + B₂ covers all natural numbers.
-/
theorem digitSetB1_add_digitSetB2 : digitSetB1 + digitSetB2 = Set.univ := by
  apply Set.eq_univ_of_forall; intro n;
  induction n using Nat.strong_induction_on with
  | h n ih =>
    -- Let's consider the four cases for $n$: $n = 4k$, $n = 4k + 1$, $n = 4k + 2$, or $n = 4k + 3$
    -- for some $k$.
    obtain ⟨k, rfl | rfl | rfl | rfl⟩ :
        ∃ k, n = 4 * k ∨ n = 4 * k + 1 ∨
          n = 4 * k + 2 ∨ n = 4 * k + 3 := by
      exact ⟨ n / 4, by omega ⟩;
    · by_cases hk : k = 0;
      · exact ⟨ 0, by unfold digitSetB1; aesop, 0, by unfold digitSetB2; aesop, by aesop ⟩;
      · obtain ⟨ a, ha, b, hb, hab ⟩ := ih k ( by linarith [ Nat.pos_of_ne_zero hk ] );
        refine ⟨ 4 * a, ?_, 4 * b, ?_, ?_ ⟩ <;> simp_all +decide [ digitSetB1, digitSetB2 ];
        · rintro ( _ | r ) <;> simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
        · intro r
          rcases r with ( _ | r ) <;>
            norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ] at *
          all_goals aesop
        · linarith;
    · obtain ⟨ a, ha, b, hb, hab ⟩ := ih k ( by linarith );
      refine ⟨ 4 * a + 1, ?_, 4 * b, ?_, ?_ ⟩ <;> simp_all +decide [ digitSetB1, digitSetB2 ];
      · rintro ( _ | r ) <;> norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
        norm_num [ Nat.add_div ] ; aesop;
      · rintro ( _ | r ) <;> norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
        exact hb r;
      · linarith;
    · obtain ⟨ a, ha, b, hb, hab ⟩ := ih k ( by linarith );
      refine ⟨ 4 * a, ?_, 4 * b + 2, ?_, ?_ ⟩ <;> simp_all +decide [ digitSetB1, digitSetB2 ];
      · rintro ( _ | r ) <;> norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ] at * ; aesop;
      · intro r; rcases r with ( _ | r ) <;> norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ] ;
        norm_num [ Nat.add_div ] ; aesop;
      · bv_omega;
    · obtain ⟨ a, ha, b, hb, hab ⟩ := ih k ( by linarith );
      refine ⟨ 4 * a + 1, ?_, 4 * b + 2, ?_, ?_ ⟩ <;> simp_all +decide [ digitSetB1, digitSetB2 ];
      · rintro ( _ | r ) <;> norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
        norm_num [ Nat.add_div ] ; aesop;
      · intro r; rcases r with ( _ | r ) <;> norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ] ;
        norm_num [ Nat.add_div ] ; aesop;
      · linarith

/-- The counterexample set for Theorem 2: A = B₁ ∪ B₂ ∪ ⋃_{k≥1} I_k
    where N_k = 4^(3^k) and I_k = [N_k, (k+1)·N_k). -/
def counterexN (k : ℕ) : ℕ := 4 ^ 3 ^ k
def counterexI (k : ℕ) : Set ℕ := Set.Ico (counterexN k) ((k + 1) * counterexN k)
def counterexA : Set ℕ :=
  digitSetB1 ∪ digitSetB2 ∪ ⋃ k ∈ Set.Ici 1, counterexI k

/-- counterexA contains B₁ ∪ B₂ -/
lemma counterexA_contains_digit_sets : digitSetB1 ∪ digitSetB2 ⊆ counterexA := by
  intro x hx; left; exact hx

/-- counterexA + counterexA = ℕ -/
lemma counterexA_sumset_univ : counterexA + counterexA = Set.univ := by
  rw [Set.eq_univ_iff_forall]; intro n
  have h := digitSetB1_add_digitSetB2 ▸ (Set.mem_univ n)
  rw [Set.mem_add] at h ⊢
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact ⟨a, counterexA_contains_digit_sets (Or.inl ha), b,
         counterexA_contains_digit_sets (Or.inr hb), hab⟩

/-
Natural density of Set.univ is 1
-/
lemma hasNatDensity_univ : HasNatDensity Set.univ 1 := by
  refine tendsto_const_nhds.congr' ?_;
  filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN using by
    rw [ show countIn Set.univ (N + 1) = N + 1 by
      unfold countIn
      simp +decide [ Finset.filter_true_of_mem ] ]
    rw [ eq_div_iff ] <;> norm_cast
    linarith

/-
The digit decomposition bijection: every n < 4^m can be uniquely written as
    b₁ + b₂ where b₁ ∈ digitSetB1 ∩ [0, 4^m) and b₂ ∈ digitSetB2 ∩ [0, 4^m).
-/
lemma digit_decomp_unique (m : ℕ) (n : ℕ) (hn : n < 4 ^ m) :
    ∃! p : ℕ × ℕ, p.1 ∈ digitSetB1 ∧ p.1 < 4 ^ m ∧
      p.2 ∈ digitSetB2 ∧ p.2 < 4 ^ m ∧ p.1 + p.2 = n := by
        -- Define b₁ and b₂ as the sums of the digits of n in base-4, where b₁ takes the digits in
        -- {0,1} and b₂ takes the digits in {0,2}.
        obtain ⟨b₁, b₂, hb₁, hb₂, hsum⟩ :
            ∃ b₁ b₂ : ℕ,
              b₁ ∈ digitSetB1 ∧ b₁ < 4 ^ m ∧
                b₂ ∈ digitSetB2 ∧ b₂ < 4 ^ m ∧ b₁ + b₂ = n := by
          induction m generalizing n with
          | zero =>
            simp_all +decide [ pow_succ' ];
            exact ⟨ fun _ => by norm_num, fun _ => by norm_num ⟩;
          | succ m ih =>
            simp_all +decide [ pow_succ' ];
            -- Let's consider the base-4 representation of $n$. We can write $n$ as $4q + r$ where
            -- $q < 4^m$ and $r \in \{0, 1, 2, 3\}$.
            obtain ⟨q, r, hr⟩ : ∃ q r, n = 4 * q + r ∧ q < 4 ^ m ∧ r < 4 := by
              exact
                ⟨ n / 4, n % 4, by rw [ Nat.div_add_mod ],
                  Nat.div_lt_of_lt_mul <| by linarith, Nat.mod_lt _ <| by decide ⟩
            obtain ⟨b₁, hb₁, hb₁', b₂, hb₂, hb₂', h⟩ := ih q hr.2.1
            refine ⟨
              4 * b₁ +
                (if r = 0 then 0 else if r = 1 then 1 else if r = 2 then 0 else 1),
              ?_, ?_,
              4 * b₂ +
                (if r = 0 then 0 else if r = 1 then 0 else if r = 2 then 2 else 2),
              ?_, ?_, ?_⟩ <;>
              simp_all +decide [ Nat.add_mod, Nat.mul_mod ]
            · intro k
              rcases k with ( _ | k ) <;>
                simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ]
              · have := hr.2.2; interval_cases r <;> trivial;
              · split_ifs <;> norm_num [ Nat.add_div ]
                all_goals
                  have := hb₁ k
                  aesop ( simp_config := { decide := true } )
            · split_ifs <;> linarith;
            · intro r; split_ifs <;> simp_all +decide [ digitSetB2 ] ;
              · rcases r with ( _ | r ) <;>
                  simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ]
              · rcases r with ( _ | r ) <;>
                  simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ]
              · rcases r with ( _ | _ | r ) <;>
                  norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ] at *
                · norm_num [ Nat.add_div ] ; specialize hb₂ 0 ; aesop;
                · norm_num [ Nat.add_div ];
                  convert hb₂ ( r + 1 ) using 1
                  focus
                    norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ]
                  norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
            · split_ifs <;> linarith;
            · split_ifs <;> omega;
        refine ⟨ ⟨ b₁, b₂ ⟩, ?_, ?_ ⟩ <;> simp_all +decide [ ExistsUnique ];
        intro a b ha ha' hb hb' hab;
        -- By induction on $m$, we can show that $a = b₁$ and $b = b₂$.
        have h_ind :
            ∀ m : ℕ, ∀ a b b₁ b₂ : ℕ,
              a ∈ digitSetB1 → a < 4 ^ m →
              b ∈ digitSetB2 → b < 4 ^ m →
              b₁ ∈ digitSetB1 → b₁ < 4 ^ m →
              b₂ ∈ digitSetB2 → b₂ < 4 ^ m →
              a + b = b₁ + b₂ → a = b₁ ∧ b = b₂ := by
          intros m a b b₁ b₂ ha ha' hb hb' hb₁ hb₁' hb₂ hb₂' hab
          induction m generalizing a b b₁ b₂ with
          | zero =>
            aesop;
          | succ m ih =>
            -- By the properties of the digit sets, we know that $a \mod 4$ and $b \mod 4$ are in
            -- $\{0, 1\}$ and $\{0, 2\}$ respectively.
            have h_mod :
                a % 4 ∈ ({0, 1} : Set ℕ) ∧
                  b % 4 ∈ ({0, 2} : Set ℕ) ∧
                  b₁ % 4 ∈ ({0, 1} : Set ℕ) ∧
                  b₂ % 4 ∈ ({0, 2} : Set ℕ) := by
              exact
                ⟨ by simpa using ha 0, by simpa using hb 0,
                  by simpa using hb₁ 0, by simpa using hb₂ 0 ⟩
            -- By the properties of the digit sets, we know that $a / 4$ and $b / 4$ are in $\{0,
            -- 1\}$ and $\{0, 2\}$ respectively.
            have h_div :
                a / 4 ∈ digitSetB1 ∧ a / 4 < 4 ^ m ∧
                  b / 4 ∈ digitSetB2 ∧ b / 4 < 4 ^ m ∧
                  b₁ / 4 ∈ digitSetB1 ∧ b₁ / 4 < 4 ^ m ∧
                  b₂ / 4 ∈ digitSetB2 ∧ b₂ / 4 < 4 ^ m := by
              have h_div : ∀ n : ℕ, n ∈ digitSetB1 → n / 4 ∈ digitSetB1 := by
                intro n hn r
                specialize hn ( r + 1 )
                simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ]
              have h_div' : ∀ n : ℕ, n ∈ digitSetB2 → n / 4 ∈ digitSetB2 := by
                intro n hn r
                specialize hn ( r + 1 )
                simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ]
              exact
                ⟨ h_div a ha,
                  Nat.div_lt_of_lt_mul <| by rw [ pow_succ' ] at ha'; linarith,
                  h_div' b hb,
                  Nat.div_lt_of_lt_mul <| by rw [ pow_succ' ] at hb'; linarith,
                  h_div b₁ hb₁,
                  Nat.div_lt_of_lt_mul <| by rw [ pow_succ' ] at hb₁'; linarith,
                  h_div' b₂ hb₂,
                  Nat.div_lt_of_lt_mul <| by rw [ pow_succ' ] at hb₂'; linarith ⟩
            specialize ih ( a / 4 ) ( b / 4 ) ( b₁ / 4 ) ( b₂ / 4 )
            simp_all +decide [ Nat.pow_succ' ]
            lia;
        exact h_ind m a b b₁ b₂ ha ha' hb hb' hb₁ hb₂ hsum.1 hsum.2.1 ( by linarith )

/-- The digit decomposition as a function: given n < 4^m, returns the unique (b₁, b₂) with
    b₁ ∈ B₁, b₂ ∈ B₂, b₁ + b₂ = n. -/
noncomputable def digitDecomp (m : ℕ) (n : ℕ) : ℕ × ℕ :=
  if h : n < 4 ^ m then (digit_decomp_unique m n h).exists.choose
  else (0, 0)

lemma digitDecomp_spec (m n : ℕ) (hn : n < 4 ^ m) :
    let p := digitDecomp m n
    p.1 ∈ digitSetB1 ∧ p.1 < 4 ^ m ∧ p.2 ∈ digitSetB2 ∧ p.2 < 4 ^ m ∧ p.1 + p.2 = n := by
  simp only [digitDecomp, dif_pos hn]
  exact (digit_decomp_unique m n hn).exists.choose_spec

lemma digitDecomp_unique' (m n : ℕ) (hn : n < 4 ^ m) (q : ℕ × ℕ)
    (hq : q.1 ∈ digitSetB1 ∧ q.1 < 4 ^ m ∧ q.2 ∈ digitSetB2 ∧ q.2 < 4 ^ m ∧ q.1 + q.2 = n) :
    q = digitDecomp m n := by
  have h := digitDecomp_spec m n hn
  exact (digit_decomp_unique m n hn).unique hq h

/-
The add map is injective on B₁ × B₂ restricted to [0,4^m).
-/
lemma digit_add_injective (m : ℕ) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2)
      ((digitSetB1 ∩ Set.Iio (4^m)) ×ˢ (digitSetB2 ∩ Set.Iio (4^m))) := by
        intro p hp q hq h_eq
        have h_sum_lt : p.1 + p.2 < 4 ^ m ∧ q.1 + q.2 < 4 ^ m := by
          have h_sum_lt :
              ∀ (a b : ℕ),
                a ∈ digitSetB1 → b ∈ digitSetB2 →
                  a < 4 ^ m → b < 4 ^ m → a + b < 4 ^ m := by
            intros a b ha hb ha_lt hb_lt
            have h_sum_lt : ∀ r < m, (a / 4 ^ r % 4) + (b / 4 ^ r % 4) < 4 := by
              intro r hr; have := ha r; have := hb r; norm_num at *; aesop;
            have h_sum_lt : ∀ r ≤ m, (a / 4 ^ r) + (b / 4 ^ r) < 4 ^ (m - r) := by
              intro r hr;
              induction hr : m - r generalizing r with
              | zero =>
                simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
                rw [ Nat.sub_eq_iff_eq_add ] at hr <;> aesop;
              | succ k hk =>
                simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ];
                have := hk ( r + 1 ) ( by omega ) ( by omega );
                rw [
                  show
                      a / 4 ^ r =
                        (a / 4 ^ (r + 1)) * 4 + (a / 4 ^ r % 4) by
                    rw [ ← Nat.div_add_mod (a / 4 ^ r) 4 ]
                    norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ]
                    ring_nf
                    norm_num [ Nat.div_div_eq_div_mul, mul_comm ],
                  show
                      b / 4 ^ r =
                        (b / 4 ^ (r + 1)) * 4 + (b / 4 ^ r % 4) by
                    rw [ ← Nat.div_add_mod (b / 4 ^ r) 4 ]
                    norm_num [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ]
                    ring_nf
                    norm_num [ Nat.div_div_eq_div_mul, mul_comm ] ];
                linarith [ h_sum_lt r ( by omega ) ];
            simpa using h_sum_lt 0 bot_le;
          aesop;
        have := digit_decomp_unique m ( p.1 + p.2 ) h_sum_lt.1;
        exact this.unique
          ⟨ hp.1.1, hp.1.2, hp.2.1, hp.2.2, rfl ⟩
          ⟨ hq.1.1, hq.1.2, hq.2.1, hq.2.2, h_eq.symm ⟩

/-
The add map is surjective from B₁ × B₂ to [0,4^m).
-/
lemma digit_add_surjective (m : ℕ) :
    Set.SurjOn (fun p : ℕ × ℕ => p.1 + p.2)
      ((digitSetB1 ∩ Set.Iio (4^m)) ×ˢ (digitSetB2 ∩ Set.Iio (4^m)))
      (Set.Iio (4^m)) := by
        intro n hn
        obtain ⟨b₁, b₂, hb₁, hb₂, hsum⟩ :
            ∃ b₁ b₂, b₁ ∈ digitSetB1 ∧ b₁ < 4^m ∧
              b₂ ∈ digitSetB2 ∧ b₂ < 4^m ∧ b₁ + b₂ = n := by
          exact ExistsUnique.exists ( digit_decomp_unique m n hn ) |>
            fun ⟨p, hp⟩ => ⟨p.1, p.2, hp⟩
        exact ⟨ ⟨ b₁, b₂ ⟩, ⟨ ⟨ hb₁, hb₂ ⟩, ⟨ hsum.1, hsum.2.1 ⟩ ⟩, hsum.2.2 ⟩

/-
The count of (S₁ ∩ B₁) + (S₂ ∩ B₂) in [0, 4^m) equals
    |S₁ ∩ B₁ ∩ [0, 4^m)| * |S₂ ∩ B₂ ∩ [0, 4^m)|.
-/
lemma cross_digit_count (S₁ S₂ : Set ℕ) (m : ℕ) :
    countIn ((S₁ ∩ digitSetB1) + (S₂ ∩ digitSetB2)) (4 ^ m) =
    countIn (S₁ ∩ digitSetB1) (4 ^ m) * countIn (S₂ ∩ digitSetB2) (4 ^ m) := by
      refine Eq.symm ?_;
      unfold countIn;
      rw [ ← Finset.card_product ];
      refine Finset.card_bij ?_ ?_ ?_ ?_;
      focus
        use fun p hp => p.1 + p.2
      · simp +contextual [ Set.mem_add ];
        intro a b ha ha₁ ha₂ hb hb₁ hb₂; refine ⟨ ?_, a, ⟨ ha₁, ha₂ ⟩, b, ⟨ hb₁, hb₂ ⟩, rfl ⟩ ;
        have h_no_carry :
            ∀ m : ℕ, ∀ a ∈ digitSetB1, ∀ b ∈ digitSetB2,
              a < 4 ^ m → b < 4 ^ m → a + b < 4 ^ m := by
          intros m a ha b hb ha_lt hb_lt;
          induction m generalizing a b with
          | zero =>
            aesop;
          | succ m ih =>
            have h_no_carry : a / 4 ∈ digitSetB1 ∧ b / 4 ∈ digitSetB2 := by
              exact
                ⟨ fun r => by
                    simpa [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ] using ha ( r + 1 ),
                  fun r => by
                    simpa [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ] using hb ( r + 1 ) ⟩
            have h_no_carry : a / 4 + b / 4 < 4 ^ m := by
              exact ih _ h_no_carry.1 _ h_no_carry.2
                (Nat.div_lt_of_lt_mul <| by rw [ pow_succ' ] at ha_lt; linarith)
                (Nat.div_lt_of_lt_mul <| by rw [ pow_succ' ] at hb_lt; linarith)
            have := ha 0; have := hb 0; norm_num at *; omega;
        exact h_no_carry m a ha₂ b hb₂ ha hb;
      · simp +zetaDelta at *;
        intro a b ha ha₁ ha₂ hb hb₁ hb₂ a' b' ha' ha₁' ha₂' hb' hb₁' hb₂' hab;
        have := digit_add_injective m;
        have := @this (a, b)
          ⟨ ⟨ ha₂, ha ⟩, ⟨ hb₂, hb ⟩ ⟩
          (a', b') ⟨ ⟨ ha₂', ha' ⟩, ⟨ hb₂', hb' ⟩ ⟩
        aesop
      · simp +zetaDelta at *;
        rintro b hb ⟨ a, ha, c, hc, rfl ⟩;
        exact ⟨ a, c, ⟨ ⟨ by linarith, ha.1, ha.2 ⟩, ⟨ by linarith, hc.1, hc.2 ⟩ ⟩, rfl ⟩

/-
The B₁+B₁ self-sumset (digits in {0,1,2}) has at most 3^m elements in [0, 4^m).
-/
lemma digitSetB1_self_sum_count (m : ℕ) :
    countIn (digitSetB1 + digitSetB1) (4 ^ m) ≤ 3 ^ m := by
      refine le_trans
        (Finset.card_le_card
          (t := Finset.image
            (fun s : Fin m → Fin 3 =>
              ∑ i : Fin m, (if s i = 0 then 0 else if s i = 1 then 1 else 2) *
                4 ^ (i : ℕ))
            (Finset.univ : Finset (Fin m → Fin 3)))
          ?_)
        ?_;
      · intro x hx; simp_all +decide [ Finset.mem_image, Set.mem_add ] ;
        rcases hx with ⟨ hx₁, a, ha, b, hb, rfl ⟩;
        -- By definition of $digitSetB1$, we know that $a$ and $b$ have base-4 digits in $\{0,1\}$.
        have h_digits :
            ∀ i : Fin m,
              (a / 4 ^ (i : ℕ)) % 4 ∈ ({0, 1} : Set ℕ) ∧
                (b / 4 ^ (i : ℕ)) % 4 ∈ ({0, 1} : Set ℕ) := by
          exact fun i => ⟨ ha _, hb _ ⟩;
        -- Let's express the sum $a + b$ in terms of its base-4 digits.
        have h_sum_digits :
            a + b =
              ∑ i : Fin m,
                ((a / 4 ^ (i : ℕ)) % 4 + (b / 4 ^ (i : ℕ)) % 4) *
                  4 ^ (i : ℕ) := by
          have h_sum_digits :
              a = ∑ i : Fin m, (a / 4 ^ (i : ℕ)) % 4 * 4 ^ (i : ℕ) ∧
                b = ∑ i : Fin m, (b / 4 ^ (i : ℕ)) % 4 * 4 ^ (i : ℕ) := by
            have h_sum_digits :
                ∀ n : ℕ,
                  n < 4 ^ m →
                    n = ∑ i : Fin m, (n / 4 ^ (i : ℕ)) % 4 * 4 ^ (i : ℕ) := by
              intro n hn;
              have h_sum_digits :
                  ∀ (n : ℕ) (m : ℕ),
                    n < 4 ^ m →
                      n = ∑ i ∈ Finset.range m, (n / 4 ^ i) % 4 * 4 ^ i := by
                intro n m hn
                induction m generalizing n with
                | zero =>
                  norm_num [ Finset.sum_range_succ', pow_succ' ] at *
                  exact hn;
                | succ m ih =>
                  norm_num [ Finset.sum_range_succ', pow_succ' ] at *
                  have := ih ( n / 4 ) ( Nat.div_lt_of_lt_mul <| by linarith );
                  norm_num [ Nat.div_div_eq_div_mul, Nat.mul_mod_mul_left ] at *;
                  norm_num [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] at *;
                  rw [ ← Finset.mul_sum _ _ _, ← this ] ; linarith [ Nat.mod_add_div n 4 ];
              simpa only [ Finset.sum_range ] using h_sum_digits n m hn;
            exact ⟨ h_sum_digits a ( by linarith ), h_sum_digits b ( by linarith ) ⟩;
          simp +decide only [add_mul, Finset.sum_add_distrib];
          rw [ ← h_sum_digits.1, ← h_sum_digits.2 ];
        use fun i =>
          if (a / 4 ^ (i : ℕ)) % 4 + (b / 4 ^ (i : ℕ)) % 4 = 0 then 0
          else if (a / 4 ^ (i : ℕ)) % 4 + (b / 4 ^ (i : ℕ)) % 4 = 1 then 1
          else 2
        rw [ h_sum_digits ];
        refine Finset.sum_congr rfl fun i hi => ?_
        specialize h_digits i
        norm_num at h_digits ⊢
        rcases h_digits with ⟨ ha | ha, hb | hb ⟩ <;> norm_num [ ha, hb ];
        rfl;
      · exact Finset.card_image_le.trans ( by norm_num [ Finset.card_univ ] )

/-
The B₂+B₂ self-sumset (digits in {0,2,4 mod 4}) has at most 3^m elements in [0, 4^m).
-/
lemma digitSetB2_self_sum_count (m : ℕ) :
    countIn (digitSetB2 + digitSetB2) (4 ^ m) ≤ 3 ^ m := by
      refine le_trans
        (Finset.card_le_card
          (t := Finset.image
            (fun s : Fin m → Fin 3 =>
              ∑ i : Fin m, (if s i = 0 then 0 else if s i = 1 then 2 else 4) *
                4 ^ (i : ℕ))
            (Finset.univ : Finset (Fin m → Fin 3)))
          ?_)
        ?_;
      · intro x hx; simp_all +decide [ Finset.mem_image, Set.mem_add ] ;
        obtain ⟨ hx₁, a, ha, b, hb, rfl ⟩ := hx
        use fun i =>
          if a / 4 ^ (i : ℕ) % 4 = 0 then
            if b / 4 ^ (i : ℕ) % 4 = 0 then 0 else 1
          else if b / 4 ^ (i : ℕ) % 4 = 0 then 1 else 2
        simp +decide [ Finset.sum_ite ]
        have h_sum : a + b = ∑ i ∈ Finset.range m, (a / 4 ^ i % 4 + b / 4 ^ i % 4) * 4 ^ i := by
          have h_sum :
              ∀ n,
                a + b =
                  ∑ i ∈ Finset.range n, (a / 4 ^ i % 4 + b / 4 ^ i % 4) *
                      4 ^ i +
                    (a / 4 ^ n) * 4 ^ n + (b / 4 ^ n) * 4 ^ n := by
            intro n
            induction n with
            | zero =>
              simp +decide [ Finset.sum_range_succ, pow_succ,
                ← Nat.div_div_eq_div_mul ] at *
            | succ n ih =>
              simp +decide [ Finset.sum_range_succ, pow_succ,
                ← Nat.div_div_eq_div_mul ] at *
              nlinarith [
                Nat.mod_add_div (a / 4 ^ n) 4,
                Nat.mod_add_div (b / 4 ^ n) 4,
                pow_pos (show 0 < 4 by decide) n]
          specialize h_sum m;
          nlinarith [
            Nat.div_eq_of_lt
              (show a < 4 ^ m from lt_of_le_of_lt (Nat.le_add_right _ _) hx₁),
            Nat.div_eq_of_lt
              (show b < 4 ^ m from lt_of_le_of_lt (Nat.le_add_left _ _) hx₁)]
        rw [ h_sum, Finset.sum_range ];
        rw [ Finset.sum_filter, Finset.sum_filter ];
        rw [ Finset.sum_filter, Finset.sum_filter ]
        rw [ ← Finset.sum_add_distrib ]
        refine Finset.sum_congr rfl fun i hi => ?_
        have := ha i
        have := hb i
        simp_all +decide [ Nat.div_eq_of_lt ]
        rcases ‹a / 4 ^ (i : ℕ) % 4 = 0 ∨ a / 4 ^ (i : ℕ) % 4 = 2› with ha | ha <;>
          rcases ‹b / 4 ^ (i : ℕ) % 4 = 0 ∨ b / 4 ^ (i : ℕ) % 4 = 2› with hb | hb <;>
          simp +decide [ ha, hb ];
      · exact Finset.card_image_le.trans ( by norm_num [ Finset.card_univ ] )

/-
The size of I_k is k * N_k
-/
lemma counterexI_card (k : ℕ) (hk : k ≥ 1) :
    countIn (counterexI k) ((k + 1) * counterexN k) = k * counterexN k := by
      simp +decide [ countIn, counterexI ];
      rw [ show
          (Finset.filter
              (fun x => counterexN k ≤ x ∧ x < (k + 1) * counterexN k)
              (Finset.range ((k + 1) * counterexN k))) =
            Finset.Ico (counterexN k) ((k + 1) * counterexN k) by
        ext
        aesop ]
      simp +decide [ Nat.succ_mul ]

/-
Interval self-sum Cauchy-Davenport: if S ⊆ I_k with |S| = s, then |S+S| ≥ 2s-1
-/
lemma interval_self_sum_bound (k : ℕ) (S : Finset ℕ)
    (hS : ∀ x ∈ S, x ∈ counterexI k) (hne : S.Nonempty) :
    (S + S).card ≥ 2 * S.card - 1 := by
      -- By the properties of finite sets, we know that $|S + S| \geq 2|S| - 1$.
      have h_cauchy_davenport : ∀ (S : Finset ℤ), S.Nonempty → (S + S).card ≥ 2 * S.card - 1 := by
        intros S hS_nonempty
        have h_cauchy_davenport : (S + S).card ≥ S.card + S.card - 1 := by
          exact cauchy_davenport_of_isAddTorsionFree hS_nonempty hS_nonempty;
        simpa only [ two_mul ] using h_cauchy_davenport;
      convert h_cauchy_davenport ( S.image ( fun x : ℕ => x : ℕ → ℤ ) ) ( by simpa ) using 1;
      · convert rfl;
        convert Finset.card_image_of_injective _ Nat.cast_injective;
        all_goals try { infer_instance };
        ext; simp [Finset.mem_add, Finset.mem_image];
      · rw [ Finset.card_image_of_injective _ Nat.cast_injective ]

/-
Key impossibility: p*q ≥ 1 / 2 and (1-p)*(1-q) ≥ 1 / 2 is impossible for p,q ∈ [0,1].
-/
lemma pq_impossibility (p q : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (h1 : p * q ≥ 1 / 2) (h2 : (1 - p) * (1 - q) ≥ 1 / 2) : False := by
      nlinarith [ sq_nonneg ( p - q ) ]

/-
Lower bound on A₁+A₁ at gap scale from digit cross-sums.
-/
lemma gap_scale_lower (P : BiPartition counterexA) (k : ℕ) :
  countIn (P.left + P.left) (counterexN k) ≥
    countIn (P.left ∩ digitSetB1) (counterexN k) *
      countIn (P.left ∩ digitSetB2) (counterexN k) := by
      -- By cross_digit_count, countIn((P.left ∩ B₁) + (P.left ∩ B₂), 4^(3^k)) = countIn(P.left ∩
      -- B₁, 4^(3^k)) * countIn(P.left ∩ B₂, 4^(3^k)).
      have h_cross_digit_count :
          countIn ((P.left ∩ digitSetB1) + (P.left ∩ digitSetB2)) (counterexN k) =
            countIn (P.left ∩ digitSetB1) (counterexN k) *
              countIn (P.left ∩ digitSetB2) (counterexN k) := by
            simpa [counterexN] using cross_digit_count ( P.left ) ( P.left ) ( 3 ^ k )
      exact h_cross_digit_count ▸
        countIn_mono
          (Set.add_subset_add Set.inter_subset_left Set.inter_subset_left)
          (counterexN k)

/-
The algebraic bound: x*y + (1-x)*(1-y) ≤ 1 - x*y*(1-x)*(1-y).
-/
lemma density_algebraic_bound (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1) (hy : 0 ≤ y) (hy' : y ≤ 1) :
    x * y + (1 - x) * (1 - y) ≤ 1 - x * y * ((1 - x) * (1 - y)) := by
      nlinarith [
        mul_nonneg hx hy,
        mul_le_mul_of_nonneg_left hx' hy,
        mul_le_mul_of_nonneg_right hy' hx]

/-- B₁ has exactly 2^m elements below 4^m -/
lemma digitSetB1_countIn (m : ℕ) : countIn digitSetB1 (4 ^ m) = 2 ^ m := by
  induction m with
  | zero =>
    unfold digitSetB1; unfold countIn; simp +decide;
    rw [Finset.filter_singleton]; norm_num
  | succ m ih =>
    have h_split :
        ∀ N : ℕ,
          countIn digitSetB1 (4 * N) =
            countIn (fun n => n ∈ digitSetB1 ∧ n % 4 = 0) (4 * N) +
              countIn (fun n => n ∈ digitSetB1 ∧ n % 4 = 1) (4 * N) := by
      intro N
      simp +decide only [countIn, Finset.card_filter]
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl]
      intro x hx; split_ifs <;> simp_all +decide [Nat.mod_eq_of_lt]
      · cases ‹x ∈ digitSetB1 ∧ x % 4 = 0›.2.symm.trans ‹x ∈ digitSetB1 ∧ x % 4 = 1›.2
      · rename_i h₁ h₂ h₃
        have := h₁ 0; simp_all +decide [Nat.mod_eq_of_lt]
        exact h₂ ⟨h₁, this.resolve_right fun h => h₃ ⟨h₁, h⟩⟩
      · cases ‹x ∈ digitSetB1 ∧ x % 4 = 0›; cases ‹x ∈ digitSetB1 ∧ x % 4 = 1›; aesop
      · exact ‹x ∉ digitSetB1› (And.left ‹_›)
      · cases ‹_›; tauto
    have h_last_digit_zero :
        countIn (fun n => n ∈ digitSetB1 ∧ n % 4 = 0) (4 * 4 ^ m) =
          countIn digitSetB1 (4 ^ m) := by
      refine Finset.card_bij (fun x hx => x / 4) ?_ ?_ ?_ <;> simp_all +decide [Nat.div_eq_of_lt]
      · intro a ha h
        have := h.2
        rw [← Nat.mod_add_div a 4] at *
        simp_all +decide [Nat.add_mod, Nat.mul_mod]
        intro r; have := h.1 (r + 1); simp_all +decide [Nat.pow_succ', ← Nat.div_div_eq_div_mul]
      · intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h
        linarith [Nat.mod_add_div a₁ 4, Nat.mod_add_div a₂ 4, ha₂.2, ha₄.2]
      · intro b hb hb'; use 4 * b; simp_all +decide [Nat.mul_mod]
        exact
          ⟨fun r => by
            cases r <;> simpa [Nat.pow_succ', ← Nat.div_div_eq_div_mul] using hb' _,
            Nat.mul_mod_right _ _⟩
    have h_last_digit_one :
        countIn (fun n => n ∈ digitSetB1 ∧ n % 4 = 1) (4 * 4 ^ m) =
          countIn digitSetB1 (4 ^ m) := by
      have h_last_digit_one :
          ∀ n, n ∈ digitSetB1 ∧ n % 4 = 1 →
            ∃ k, n = 4 * k + 1 ∧ k ∈ digitSetB1 := by
        intro n hn; use n / 4; simp_all +decide [Nat.div_add_mod]
        exact
          ⟨by linarith [Nat.mod_add_div n 4], fun r => by
            have := hn.1 (r + 1)
            simp_all +decide [Nat.pow_succ', ← Nat.div_div_eq_div_mul]⟩
      refine Finset.card_bij (fun n hn => n / 4) ?_ ?_ ?_ <;> simp_all +decide [Nat.div_add_mod]
      · exact fun n hn hn' =>
          ⟨Nat.div_lt_of_lt_mul <| by linarith, by
            obtain ⟨k, rfl, hk⟩ := h_last_digit_one n hn'.1 hn'.2
            simpa [Nat.add_div] using hk⟩
      · intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h
        obtain ⟨k₁, rfl, hk₁⟩ := h_last_digit_one a₁ ha₂.1 ha₂.2
        obtain ⟨k₂, rfl, hk₂⟩ := h_last_digit_one a₂ ha₄.1 ha₄.2
        simp_all +decide [Nat.add_div]
      · intro b hb hb'; use 4 * b + 1; simp_all +decide [Nat.add_div]
        refine ⟨by linarith, ?_, ?_⟩ <;> norm_num [Nat.add_mod, Nat.mul_mod]
        intro r
        rcases r with (_ | r) <;> simp_all +decide [Nat.pow_succ', ← Nat.div_div_eq_div_mul]
        norm_num [Nat.add_div]
        exact hb' r
    grind +splitImp

/-
B₂ has exactly 2^m elements below 4^m
-/
lemma digitSetB2_countIn (m : ℕ) : countIn digitSetB2 (4 ^ m) = 2 ^ m := by
  induction m with
  | zero =>
    unfold digitSetB2; unfold countIn; simp +decide ;
    rw [ Finset.filter_singleton ] ; norm_num;
  | succ m ih =>
    -- We'll use the fact that numbers in `digitSetB2` can be split into those with last digit 0 and
    -- those with last digit 2.
    have h_split :
        ∀ N : ℕ,
          countIn digitSetB2 (4 * N) =
            countIn (fun n => n ∈ digitSetB2 ∧ n % 4 = 0) (4 * N) +
              countIn (fun n => n ∈ digitSetB2 ∧ n % 4 = 2) (4 * N) := by
      intro N;
      simp +decide only [countIn, Finset.card_filter];
      rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl ];
      intro x hx; split_ifs <;> simp_all +decide [ Nat.mod_eq_of_lt ] ;
      · cases ‹x ∈ digitSetB2 ∧ x % 4 = 0›.2.symm.trans ‹x ∈ digitSetB2 ∧ x % 4 = 2›.2;
      · rename_i h₁ h₂ h₃;
        have := h₁ 0; simp_all +decide [ Nat.mod_eq_of_lt ] ;
        exact h₂ ⟨ h₁, this.resolve_right fun h => h₃ ⟨ h₁, h ⟩ ⟩;
      · cases ‹x ∈ digitSetB2 ∧ x % 4 = 0› ; cases ‹x ∈ digitSetB2 ∧ x % 4 = 2› ; aesop;
      · exact ‹x ∉ digitSetB2› ( And.left ‹_› );
      · cases ‹_› ; tauto;
    -- For numbers with last digit 0, we can remove the last digit and get a number in `digitSetB2`
    -- with `m` digits.
    have h_last_digit_zero :
        countIn (fun n => n ∈ digitSetB2 ∧ n % 4 = 0) (4 * 4 ^ m) =
          countIn digitSetB2 (4 ^ m) := by
      refine Finset.card_bij (fun x hx => x / 4) ?_ ?_ ?_ <;>
        simp_all +decide [Nat.div_eq_of_lt];
      · intro a ha h
        have := h.2
        rw [ ← Nat.mod_add_div a 4 ] at *
        simp_all +decide [ Nat.add_mod, Nat.mul_mod ]
        intro r
        have := h.1 ( r + 1 )
        simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ]
      · intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h
        linarith [ Nat.mod_add_div a₁ 4, Nat.mod_add_div a₂ 4, ha₂.2, ha₄.2 ]
      · intro b hb hb'; use 4 * b; simp_all +decide [ Nat.mul_mod ] ;
        exact
          ⟨ fun r => by
              cases r <;> simpa [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ] using hb' _,
            Nat.mul_mod_right _ _ ⟩
    -- For numbers with last digit 2, we can remove the last digit and get a number in `digitSetB2`
    -- with `m` digits.
    have h_last_digit_two :
        countIn (fun n => n ∈ digitSetB2 ∧ n % 4 = 2) (4 * 4 ^ m) =
          countIn digitSetB2 (4 ^ m) := by
      -- For numbers with last digit 2, we can remove the last digit and get a number in
      -- `digitSetB2` with `m` digits. This is because if `n` is in `digitSetB2` and `n % 4 = 2`,
      -- then `n = 4k + 2` for some `k` in `digitSetB2`.
      have h_last_digit_two :
          ∀ n, n ∈ digitSetB2 ∧ n % 4 = 2 →
            ∃ k, n = 4 * k + 2 ∧ k ∈ digitSetB2 := by
        intro n hn; use n / 4; simp_all +decide [ Nat.div_add_mod ] ;
        exact
          ⟨ by linarith [ Nat.mod_add_div n 4 ], fun r => by
              have := hn.1 ( r + 1 )
              simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ] ⟩
      refine Finset.card_bij ( fun n hn => n / 4 ) ?_ ?_ ?_ <;>
        simp_all +decide [ Nat.div_add_mod ];
      · exact fun n hn hn' =>
          ⟨ Nat.div_lt_of_lt_mul <| by linarith, by
            obtain ⟨ k, rfl, hk ⟩ := h_last_digit_two n hn'.1 hn'.2
            simpa [ Nat.add_div ] using hk ⟩
      · intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h
        obtain ⟨ k₁, rfl, hk₁ ⟩ := h_last_digit_two a₁ ha₂.1 ha₂.2
        obtain ⟨ k₂, rfl, hk₂ ⟩ := h_last_digit_two a₂ ha₄.1 ha₄.2
        simp_all +decide [ Nat.add_div ]
      · intro b hb hb'
        use 4 * b + 2
        simp_all +decide [ Nat.add_div ]
        refine ⟨ by linarith, ?_, ?_ ⟩ <;> norm_num [ Nat.add_mod, Nat.mul_mod]
        intro r
        rcases r with ( _ | r ) <;>
          simp_all +decide [ Nat.pow_succ', ← Nat.div_div_eq_div_mul ]
        norm_num [ Nat.add_div ];
        exact hb' r;
    grind +splitImp

/-
P.left and P.right partition B₁
-/
lemma bipartition_B1_count (P : BiPartition counterexA) (m : ℕ) :
    countIn (P.left ∩ digitSetB1) (4 ^ m) + countIn (P.right ∩ digitSetB1) (4 ^ m) = 2 ^ m := by
  convert Set.ext_iff.mp (show
      (P.left ∩ digitSetB1) ∪ (P.right ∩ digitSetB1) = digitSetB1 from ?_) using 1;
  · constructor <;> intro h;
    · intro x; exact ⟨by aesop, by intro hx; exact (by
      exact P.cover.symm.subset
        (counterexA_contains_digit_sets (Set.mem_union_left _ hx)) |>
          Or.imp (fun h => ⟨h, hx⟩) fun h => ⟨h, hx⟩)⟩;
    · rw [ ← digitSetB1_countIn m, countIn, countIn, countIn ];
      rw [ ← Finset.card_union_of_disjoint ];
      · congr with x ; specialize h x ; aesop;
      · simp +contextual [ Finset.disjoint_left, P.disj ];
        exact fun x hx₁ hx₂ hx₃ hx₄ => P.disj.le_bot ⟨ hx₂, hx₄ ⟩;
  · ext x;
    by_cases hx : x ∈ P.left <;> simp_all +decide [ Set.ext_iff ];
    exact fun hx' =>
      Or.resolve_left
        (P.cover.symm.subset <| counterexA_contains_digit_sets <|
          Set.mem_union_left _ hx') hx

/-
P.left and P.right partition B₂
-/
lemma bipartition_B2_count (P : BiPartition counterexA) (m : ℕ) :
    countIn (P.left ∩ digitSetB2) (4 ^ m) + countIn (P.right ∩ digitSetB2) (4 ^ m) = 2 ^ m := by
  rw [ ← digitSetB2_countIn m, countIn, countIn, countIn ];
  rw [ ← Finset.card_union_of_disjoint ];
  · congr;
    have := P.cover; simp_all +decide [ Finset.ext_iff, Set.ext_iff ] ;
    intro a
    specialize this a
    by_cases ha : a ∈ P.left <;> by_cases hb : a ∈ P.right <;>
      simp_all +decide
    exact fun _ => fun h => this <| counterexA_contains_digit_sets <| Or.inr h;
  · simp +contextual [ Finset.disjoint_left, P.disj ];
    exact fun x hx₁ hx₂ hx₃ hx₄ => P.disj.le_bot ⟨ hx₂, hx₄ ⟩

/-
Elements of counterexA below N_k are in B₁ ∪ B₂ or in intervals I_j for some j
-/
lemma counterexA_below_Nk (x : ℕ) (hx : x ∈ counterexA) :
    x ∈ digitSetB1 ∪ digitSetB2 ∨ ∃ j ≥ 1, x ∈ counterexI j := by
  unfold counterexA at hx; aesop;

/-
For j ≥ k, counterexI j ∩ [0, N_k) = ∅ (since N_j ≥ N_k)
-/
lemma counterexI_disjoint_below (j k : ℕ) (hjk : j ≥ k) (x : ℕ) (hx : x ∈ counterexI j)
    (hx' : x < counterexN k) : False := by
  contrapose! hx';
  exact le_trans ( pow_le_pow_right₀ ( by decide ) ( pow_le_pow_right₀ ( by decide ) hjk ) ) hx.1

/-
Total interval elements of counterexA below N_k
-/
lemma interval_count_below_Nk (k : ℕ) (hk : k ≥ 2) :
    countIn (counterexA \ (digitSetB1 ∪ digitSetB2)) (counterexN k) ≤
    k ^ 2 * counterexN (k - 1) := by
  -- Elements of counterexA below N_k are in B₁ ∪ B₂ or in intervals I_j for some j.
  have h_elements :
      ∀ x ∈ Finset.range (counterexN k),
        x ∈ counterexA \ (digitSetB1 ∪ digitSetB2) →
          ∃ j ∈ Finset.Icc 1 (k - 1), x ∈ counterexI j := by
    intro x hx hx'
    specialize hx'
    have := counterexA_below_Nk x
    simp_all +decide [ Set.ext_iff ]
    obtain ⟨j, hj₁, hj₂⟩ := this
    exact
      ⟨j, ⟨hj₁, Nat.le_sub_one_of_lt <| Nat.lt_of_not_ge fun hj₃ => by
        have := counterexI_disjoint_below j k hj₃ x hj₂ hx
        contradiction⟩, hj₂⟩
  -- By the union bound, the count of elements in the union of intervals is at most the sum of the
  -- counts of elements in each interval.
  have h_union_bound :
      countIn (counterexA \ (digitSetB1 ∪ digitSetB2)) (counterexN k) ≤
        Finset.sum (Finset.Icc 1 (k - 1))
          (fun j => countIn (counterexI j) (counterexN k)) := by
    exact le_trans ( Finset.card_le_card fun x hx => by aesop ) ( Finset.card_biUnion_le );
  -- Each interval I_j has j*N_j elements (by counterexI_card).
  have h_interval_card :
      ∀ j ∈ Finset.Icc 1 (k - 1),
        countIn (counterexI j) (counterexN k) ≤ j * counterexN j := by
    intros j hj;
    refine le_trans
      (Finset.card_le_card
        (t := Finset.Ico (counterexN j) ((j + 1) * counterexN j))
        ?_)
      ?_;
    · intro x hx; aesop;
    · simp +arith +decide [ Nat.succ_mul ];
  refine le_trans h_union_bound <| le_trans ( Finset.sum_le_sum h_interval_card ) ?_;
  refine le_trans (Finset.sum_le_sum fun i hi =>
    Nat.mul_le_mul
      (Finset.mem_Icc.mp hi |>.2)
      (show counterexN i ≤ counterexN (k - 1) from ?_)) ?_;
  · exact Nat.pow_le_pow_right (by decide) <|
      Nat.pow_le_pow_right (by decide) (Finset.mem_Icc.mp hi |>.2)
  · norm_num [ ← Finset.mul_sum _ _ _ ];
    nlinarith only [
      Nat.sub_le k 1,
      Nat.zero_le ( counterexN ( k - 1 ) ),
      mul_le_mul_right (Nat.sub_le k 1) (counterexN (k - 1))]

/-
N_k grows super-exponentially: k^2 * N_{k-1}^2 / N_k → 0
-/
lemma counterexN_growth (k : ℕ) (hk : k ≥ 2) :
    (k : ℝ) ^ 2 * (counterexN (k - 1) : ℝ) ^ 2 ≤ counterexN k := by
  -- Since $4^{3^{k-1}} \geq k^2$ for all $k \geq 2$, we have $k^2 \leq 4^{3^{k-1}}$.
  have h_exp_growth : (k : ℝ) ^ 2 ≤ 4 ^ (3 ^ (k - 1)) := by
    induction hk <;> norm_num [ Nat.pow_succ', Nat.pow_mul, pow_succ' ] at *;
    rcases ‹2 ≤ _› with ( _ | _ | k ) <;> norm_num [ pow_succ, pow_mul ] at *;
    nlinarith [ sq ( ( 4 : ℝ ) ^ 3 ^ ‹_› * 4 ^ 3 ^ ‹_› * 4 ^ 3 ^ ‹_› - 1 ) ];
  rcases k with ( _ | _ | k ) <;> norm_num [ pow_succ', pow_mul ] at *;
  norm_num [ counterexN, pow_succ, pow_mul ] at *;
  norm_num [ ← mul_pow ] at *;
  exact le_trans (mul_le_mul_of_nonneg_right h_exp_growth <| by positivity) <| by
    rw [ ← mul_pow ]
    gcongr
    norm_num

/-
Upper bound on sumset at base-4 scale: cross-digit + error
-/
lemma sumset_upper_bound (P : BiPartition counterexA) (k : ℕ) (hk : k ≥ 2) :
    countIn (P.left + P.left) (counterexN k) ≤
      countIn (P.left ∩ digitSetB1) (counterexN k) *
        countIn (P.left ∩ digitSetB2) (counterexN k) +
      2 * 3 ^ (3 ^ k) +
      2 * (k ^ 2 * counterexN (k - 1)) *
        (2 ^ (3 ^ k + 1) + k ^ 2 * counterexN (k - 1)) := by
  set N := counterexN k;
  set L := P.left ∩ (digitSetB1 ∪ digitSetB2) ∩ Set.Iio N
  set L_I := P.left ∩ (counterexA \ (digitSetB1 ∪ digitSetB2)) ∩ Set.Iio N;
  have h_sumset_bound :
      countIn (P.left + P.left) N ≤
        countIn (L + L) N + 2 * countIn L_I N * (countIn L N + countIn L_I N) := by
    have h_sumset_bound :
        (P.left + P.left) ∩ Set.Iio N ⊆
          (L + L) ∪ (L + L_I) ∪ (L_I + L) ∪ (L_I + L_I) := by
      intro x hx
      obtain ⟨a, b, ha, hb, hab⟩ :
          ∃ a b, a ∈ P.left ∧ b ∈ P.left ∧ a + b = x ∧ a < N ∧ b < N := by
        rcases hx with ⟨⟨a, ha, b, hb, rfl⟩, hx⟩
        exact
          ⟨a, b, ha, hb, rfl,
            by linarith [ Set.mem_Iio.mp hx ],
            by linarith [ Set.mem_Iio.mp hx ]⟩
      by_cases ha' : a ∈ digitSetB1 ∪ digitSetB2 <;>
        by_cases hb' : b ∈ digitSetB1 ∪ digitSetB2 <;>
        simp_all +decide [ Set.mem_add ];
      · exact Or.inl <| Or.inl <| Or.inl
          ⟨a, ⟨⟨ha, ha'⟩, hab.2.1⟩, b, ⟨⟨hb, hb'⟩, hab.2.2⟩, hab.1⟩
      · exact Or.inl <| Or.inl <| Or.inr ⟨ a, ⟨ ⟨ ha, ha' ⟩, hab.2.1 ⟩, b, ⟨ ⟨ hb, by
          exact ⟨ P.cover.subset ( Or.inl hb ), by aesop ⟩ ⟩, hab.2.2 ⟩, hab.1 ⟩;
      · exact Or.inl <| Or.inr ⟨ a, ⟨ ⟨ ha, by
          exact ⟨ P.cover.subset ( Or.inl ha ), by aesop ⟩ ⟩, hab.2.1 ⟩, b, ⟨ ⟨ hb, by
          exact (Set.mem_union b digitSetB1 digitSetB2).mpr hb' ⟩, hab.2.2 ⟩, by linarith ⟩;
      · exact Or.inr ⟨ a, ⟨ ⟨ ha, by
          exact ⟨ P.cover.subset ( Or.inl ha ), by aesop ⟩ ⟩, hab.2.1 ⟩, b, ⟨ ⟨ hb, by
          exact ⟨ P.cover.subset ( Or.inl hb ), by aesop ⟩ ⟩, hab.2.2 ⟩, hab.1 ⟩;
    have h_sumset_bound :
        countIn (P.left + P.left) N ≤
          countIn (L + L) N + countIn (L + L_I) N +
            countIn (L_I + L) N + countIn (L_I + L_I) N := by
      have h_sumset_bound :
          countIn ((P.left + P.left) ∩ Set.Iio N) N ≤
            countIn (L + L) N + countIn (L + L_I) N +
              countIn (L_I + L) N + countIn (L_I + L_I) N := by
        have h_sumset_bound :
            countIn ((P.left + P.left) ∩ Set.Iio N) N ≤
              countIn ((L + L) ∪ (L + L_I) ∪ (L_I + L) ∪ (L_I + L_I)) N := by
          exact countIn_mono h_sumset_bound N;
        refine le_trans h_sumset_bound ?_;
        unfold countIn;
        simp +decide only [Finset.card_filter];
        simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_le_sum fun x hx => by aesop;
      convert h_sumset_bound using 1;
      exact congr_arg Finset.card ( by ext; aesop );
    have h_sumset_bound :
        countIn (L + L_I) N ≤ countIn L N * countIn L_I N ∧
          countIn (L_I + L) N ≤ countIn L_I N * countIn L N ∧
            countIn (L_I + L_I) N ≤ countIn L_I N * countIn L_I N := by
      exact ⟨countIn_add_le_mul L L_I N,
        countIn_add_le_mul L_I L N,
        countIn_add_le_mul L_I L_I N⟩
    lia;
  -- The countIn of L + L is bounded by the sum of the counts of B₁+B₁, B₂+B₂, and the cross-digit
  -- count.
  have h_L_L_bound :
      countIn (L + L) N ≤
        3 ^ (3 ^ k) + 3 ^ (3 ^ k) +
          countIn (P.left ∩ digitSetB1) N * countIn (P.left ∩ digitSetB2) N := by
    have h_L_L_bound :
        countIn (L + L) N ≤
          countIn (digitSetB1 + digitSetB1) N +
            countIn (digitSetB2 + digitSetB2) N +
              countIn ((P.left ∩ digitSetB1) + (P.left ∩ digitSetB2)) N := by
      have h_L_L_bound :
          L + L ⊆
            (digitSetB1 + digitSetB1) ∪ (digitSetB2 + digitSetB2) ∪
              ((P.left ∩ digitSetB1) + (P.left ∩ digitSetB2)) := by
        simp +decide [ Set.subset_def, Set.mem_add ];
        grind;
      refine le_trans ( countIn_mono h_L_L_bound N ) ?_;
      simp +decide [ countIn ];
      simp +decide only [Finset.card_filter];
      simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_le_sum fun x hx => by
        split_ifs <;> simp_all +decide [ Set.union_assoc ]
    refine le_trans h_L_L_bound ?_;
    gcongr;
    · simpa [N, counterexN] using digitSetB1_self_sum_count ( 3 ^ k )
    · simpa [N, counterexN] using digitSetB2_self_sum_count ( 3 ^ k )
    · exact le_of_eq
        (by simpa [N, counterexN] using cross_digit_count ( P.left ) ( P.left ) ( 3 ^ k ))
  -- The countIn of L is bounded by the sum of the counts of B₁ and B₂.
  have h_L_bound : countIn L N ≤ 2 ^ (3 ^ k + 1) := by
    have h_L_bound : countIn L N ≤ countIn (digitSetB1) N + countIn (digitSetB2) N := by
      refine le_trans ?_
        (Finset.card_union_le
          {x ∈ Finset.range N | x ∈ digitSetB1}
          {x ∈ Finset.range N | x ∈ digitSetB2});
      refine Finset.card_mono ?_;
      intro x hx; aesop;
    have h_digitSetB1_count : countIn digitSetB1 N = 2 ^ (3 ^ k) := by
      simpa [N, counterexN] using digitSetB1_countIn ( 3 ^ k )
    have h_digitSetB2_count : countIn digitSetB2 N = 2 ^ (3 ^ k) := by
      simpa [N, counterexN] using digitSetB2_countIn ( 3 ^ k )
    rw [h_digitSetB1_count, h_digitSetB2_count] at h_L_bound
    exact h_L_bound.trans (by ring_nf; norm_num);
  -- The countIn of L_I is bounded by the count of interval elements.
  have h_L_I_bound : countIn L_I N ≤ k ^ 2 * counterexN (k - 1) := by
    refine le_trans ?_ ( interval_count_below_Nk k hk );
    refine Finset.card_mono ?_;
    intro x hx; aesop;
  nlinarith [ Nat.zero_le ( countIn L_I N ) ]

/-
The cross-digit density converges to d along the base-4 scales
-/
lemma cross_digit_density_limit (P : BiPartition counterexA) (d : ℝ) (hd : d > 0)
    (hD : HasNatDensity (P.left + P.left) d) :
    Filter.Tendsto (fun k : ℕ =>
      (countIn (P.left ∩ digitSetB1) (counterexN k) *
       countIn (P.left ∩ digitSetB2) (counterexN k) : ℝ) / counterexN k)
    Filter.atTop (nhds d) := by
  contrapose! hD;
  intro h
  have h_main :
      Filter.Tendsto
        (fun k => (countIn (P.left + P.left) (counterexN k) : ℝ) / (counterexN k))
        Filter.atTop (nhds d) := by
    have h_main :
        Filter.Tendsto
          (fun N => (countIn (P.left + P.left) N : ℝ) / N)
          Filter.atTop (nhds d) := by
      rw [ ← Filter.tendsto_add_atTop_iff_nat 1 ] ; aesop;
    exact h_main.comp <| tendsto_pow_atTop_atTop_of_one_lt (by norm_num) |>
      Filter.Tendsto.comp <| tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have h_bound_zero :
      Filter.Tendsto
        (fun k =>
          (2 * 3 ^ (3 ^ k) +
            2 * (k ^ 2 * counterexN (k - 1)) *
              (2 ^ (3 ^ k + 1) + k ^ 2 * counterexN (k - 1)) : ℝ) /
            (counterexN k))
        Filter.atTop (nhds 0) := by
    -- We'll use the fact that $3^{3^k} / 4^{3^k} = (3/4)^{3^k}$ and $k^2 * 4^{3^{k-1}} * 2^{3^k} /
    -- 4^{3^k} = k^2 / 2^{3^{k-1}}$.
    suffices h_suff :
        Filter.Tendsto
          (fun k =>
            (2 * (3 / 4 : ℝ) ^ (3 ^ k) +
              2 * (k ^ 2 / 2 ^ (3 ^ (k - 1))) *
                (2 + k ^ 2 / 2 ^ (3 ^ (k - 1)))) : ℕ → ℝ)
          Filter.atTop (nhds 0) by
      refine h_suff.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 0 ] with k hk;
      unfold counterexN; norm_num [ pow_succ, pow_mul ] ; ring_nf;
      norm_num [ pow_mul', ← mul_pow ];
      rcases k with ( _ | k ) <;> norm_num [ pow_succ, pow_mul ] at *;
      norm_num [ pow_three, mul_assoc, ← mul_pow ];
    -- We'll use the fact that $k^2 / 2^{3^{k-1}}$ tends to $0$ as $k$ tends to infinity.
    have h_zero :
        Filter.Tendsto
          (fun k : ℕ => (k ^ 2 : ℝ) / 2 ^ (3 ^ (k - 1)))
          Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm' ?_ tendsto_inv_atTop_nhds_zero_nat;
      filter_upwards [ Filter.eventually_gt_atTop 3 ] with n hn;
      rw [ Real.norm_of_nonneg ( by positivity ), inv_eq_one_div, div_le_div_iff₀ ] <;>
        norm_cast <;>
        induction hn <;>
        norm_num [ Nat.pow_succ, Nat.pow_mul ] at *;
      rcases ‹4 ≤ _› with ( _ | _ | k ) <;> simp_all +decide [ Nat.pow_succ, Nat.pow_mul ];
      nlinarith [
        Nat.zero_le ( 2 ^ 3 ^ ‹_› * 2 ^ 3 ^ ‹_› * 2 ^ 3 ^ ‹_› ),
        pow_pos (by positivity : 0 < (‹_› : ℕ) + 1 + 1) 3]
    simpa using
      Filter.Tendsto.add
        (tendsto_const_nhds.mul
          (tendsto_pow_atTop_nhds_zero_of_lt_one
              (by norm_num) (by norm_num : (3 : ℝ) / 4 < 1) |>
            Filter.Tendsto.comp <|
              tendsto_pow_atTop_atTop_of_one_lt (by norm_num)))
        (Filter.Tendsto.mul
          (tendsto_const_nhds.mul h_zero)
          (tendsto_const_nhds.add h_zero))
  have h_error :
      Filter.Tendsto
        (fun k =>
          ((countIn (P.left + P.left) (counterexN k) : ℝ) -
              (countIn (P.left ∩ digitSetB1) (counterexN k) *
                countIn (P.left ∩ digitSetB2) (counterexN k) : ℝ)) /
            (counterexN k))
        Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ h_bound_zero;
    filter_upwards [ Filter.eventually_ge_atTop 2 ] with k hk;
    rw [ Real.norm_of_nonneg
      (div_nonneg
        (sub_nonneg_of_le <| mod_cast gap_scale_lower P k)
        (Nat.cast_nonneg _)) ];
    gcongr;
    have := sumset_upper_bound P k hk;
    exact sub_le_iff_le_add'.mpr ( mod_cast by linarith );
  have := h_error.sub h_main
  simp_all +decide [ sub_div ]

/-
Proposition (base-4 scale): if both densities exist and are positive, then α₁ + α₂ < 1.
    Proof: At scale N_k = 4^(3^k), cross_digit_density_limit gives
    d₁ = lim x_k·y_k/N_k and d₂ = lim (2^n-x_k)(2^n-y_k)/N_k.
    Since x_k·y_k/N_k + (2^n-x_k)(2^n-y_k)/N_k = p_k·q_k + (1-p_k)(1-q_k)
    ≤ 1 - p_k·q_k·(1-p_k)·(1-q_k) by density_algebraic_bound,
    taking limits gives d₁+d₂ ≤ 1-d₁·d₂ < 1.
-/
lemma prop_base4_scale (P : BiPartition counterexA)
    (d₁ d₂ : ℝ) (hd₁ : d₁ > 0) (hd₂ : d₂ > 0)
    (hD₁ : HasNatDensity (P.left + P.left) d₁)
    (hD₂ : HasNatDensity (P.right + P.right) d₂) :
    d₁ + d₂ < 1 := by
      -- By cross_digit_density_limit, we have that the limits of the densities exist and are
      -- positive.
      have h_lim_pos₁ :
          Filter.Tendsto (fun k : ℕ =>
            (countIn (P.left ∩ digitSetB1) (counterexN k) *
              countIn (P.left ∩ digitSetB2) (counterexN k) : ℝ) / counterexN k)
            Filter.atTop (nhds d₁) := by
          convert cross_digit_density_limit P d₁ hd₁ hD₁ using 1
      have h_lim_pos₂ :
          Filter.Tendsto (fun k : ℕ =>
            (countIn (P.right ∩ digitSetB1) (counterexN k) *
              countIn (P.right ∩ digitSetB2) (counterexN k) : ℝ) / counterexN k)
            Filter.atTop (nhds d₂) := by
          simpa [BiPartition.swap] using cross_digit_density_limit ( P.swap ) d₂ hd₂ hD₂
      -- By bipartition_B1_count and bipartition_B2_count, we have:
      have h_bipartition :
          ∀ k : ℕ,
            countIn (P.right ∩ digitSetB1) (counterexN k) =
              2 ^ (3 ^ k) - countIn (P.left ∩ digitSetB1) (counterexN k) ∧
            countIn (P.right ∩ digitSetB2) (counterexN k) =
              2 ^ (3 ^ k) - countIn (P.left ∩ digitSetB2) (counterexN k) := by
        intro k
        have h_bipartition_B1 :
            countIn (P.left ∩ digitSetB1) (counterexN k) +
              countIn (P.right ∩ digitSetB1) (counterexN k) = 2 ^ (3 ^ k) := by
          simpa [counterexN] using bipartition_B1_count P ( 3 ^ k )
        have h_bipartition_B2 :
            countIn (P.left ∩ digitSetB2) (counterexN k) +
              countIn (P.right ∩ digitSetB2) (counterexN k) = 2 ^ (3 ^ k) := by
          simpa [counterexN] using bipartition_B2_count P ( 3 ^ k )
        exact ⟨ eq_tsub_of_add_eq <| by linarith, eq_tsub_of_add_eq <| by linarith ⟩;
      -- By definition of $p_k$ and $q_k$, we have $p_k = \frac{x_k}{2^{3^k}}$ and $q_k =
      -- \frac{y_k}{2^{3^k}}$.
      set p := fun k : ℕ => (countIn (P.left ∩ digitSetB1) (counterexN k) : ℝ) / 2 ^ (3 ^ k)
      set q := fun k : ℕ => (countIn (P.left ∩ digitSetB2) (counterexN k) : ℝ) / 2 ^ (3 ^ k);
      -- By definition of $p_k$ and $q_k$, we have $p_k q_k = \frac{x_k y_k}{4^{3^k}}$ and $(1 -
      -- p_k)(1 - q_k) = \frac{(2^{3^k} - x_k)(2^{3^k} - y_k)}{4^{3^k}}$.
      have h_pq :
          Filter.Tendsto (fun k : ℕ => p k * q k) Filter.atTop (nhds d₁) ∧
            Filter.Tendsto (fun k : ℕ => (1 - p k) * (1 - q k))
              Filter.atTop (nhds d₂) := by
        refine ⟨ h_lim_pos₁.congr fun k => ?_, h_lim_pos₂.congr fun k => ?_ ⟩;
        · rw [ div_mul_div_comm, show
              (counterexN k : ℝ) = 2 ^ 3 ^ k * 2 ^ 3 ^ k by
            norm_cast
            rw [ ← pow_add, show counterexN k = 4 ^ 3 ^ k by rfl ]
            rw [ show (4 : ℕ) = 2 ^ 2 by norm_num, pow_right_comm ]
            ring_nf ];
        · rw [ h_bipartition k |>.1, h_bipartition k |>.2 ];
          rw [ Nat.cast_sub, Nat.cast_sub ] <;> norm_num [ p, q, counterexN ];
          · field_simp;
            rw [ show (4 : ℝ) ^ 3 ^ k = (2 ^ 3 ^ k) ^ 2 by
              norm_num [ sq, ← mul_pow ] ]
            ring_nf;
          · have := bipartition_B2_count P ( 3 ^ k );
            linarith;
          · have := bipartition_B1_count P ( 3 ^ k );
            linarith;
      -- By definition of $p_k$ and $q_k$, we have $0 \leq p_k \leq 1$ and $0 \leq q_k \leq 1$.
      have h_bounds : ∀ k : ℕ, 0 ≤ p k ∧ p k ≤ 1 ∧ 0 ≤ q k ∧ q k ≤ 1 := by
        intro k
        refine
          ⟨ div_nonneg (Nat.cast_nonneg _) (by positivity),
            div_le_one_of_le₀ ?_ (by positivity),
            div_nonneg (Nat.cast_nonneg _) (by positivity),
            div_le_one_of_le₀ ?_ (by positivity) ⟩ <;>
          norm_cast
        · have := bipartition_B1_count P ( 3 ^ k ) ; norm_num [ counterexN ] at * ; omega;
        · exact le_trans
            (countIn_mono
              (show P.left ∩ digitSetB2 ⊆ digitSetB2 from fun x hx => hx.2) _)
            (by simpa [counterexN] using digitSetB2_countIn ( 3 ^ k ) |> le_of_eq)
      have h_impossible :
          ∀ k : ℕ,
            p k * q k + (1 - p k) * (1 - q k) ≤
              1 - p k * q k * ((1 - p k) * (1 - q k)) := by
        exact fun k =>
          density_algebraic_bound _ _
            (h_bounds k |>.1) (h_bounds k |>.2.1)
            (h_bounds k |>.2.2.1) (h_bounds k |>.2.2.2)
      have h_impossible : d₁ + d₂ ≤ 1 - d₁ * d₂ := by
        exact le_of_tendsto_of_tendsto'
          (h_pq.1.add h_pq.2)
          (tendsto_const_nhds.sub (h_pq.1.mul h_pq.2))
          fun k => h_impossible k
      nlinarith

/-
Proposition (interval scale): if both densities exist and are positive, then α₁ + α₂ ≥ 1.
    This uses Cauchy-Davenport on the intervals I_k.
-/
lemma prop_interval_scale (P : BiPartition counterexA)
    (d₁ d₂ : ℝ) (hd₁ : d₁ > 0) (hd₂ : d₂ > 0)
    (hD₁ : HasNatDensity (P.left + P.left) d₁)
    (hD₂ : HasNatDensity (P.right + P.right) d₂) :
    d₁ + d₂ ≥ 1 := by
      unfold HasNatDensity at *;
      -- For each k ≥ 1, let U_k = P.left ∩ counterexI k and V_k = P.right ∩ counterexI k. Since P
      -- partitions counterexA ⊇ I_k:
      have h_partition :
          ∀ k ≥ 1,
            countIn (P.left ∩ counterexI k) ((k + 1) * counterexN k) +
              countIn (P.right ∩ counterexI k) ((k + 1) * counterexN k) =
                k * counterexN k := by
        intros k hk
        have h_card :
            countIn (counterexI k) ((k + 1) * counterexN k) =
              countIn (P.left ∩ counterexI k) ((k + 1) * counterexN k) +
                countIn (P.right ∩ counterexI k) ((k + 1) * counterexN k) := by
          unfold countIn;
          rw [ ← Finset.card_union_of_disjoint ];
          · congr with x ; simp +decide [ P.disj, P.cover ];
            have := P.cover;
            replace this := Set.ext_iff.mp this x; simp_all +decide [ counterexA ] ;
            grind +extAll;
          · simp +contextual [ Finset.disjoint_left, Set.disjoint_left ];
            intro a ha₁ ha₂ ha₃ ha₄; have := P.disj; simp_all +decide [ Set.disjoint_left ] ;
        rw [ ← h_card, counterexI_card k hk ];
      -- By Cauchy-Davenport: |U_k+U_k| ≥ 2|U_k|-1 and |V_k+V_k| ≥ 2|V_k|-1.
      have h_cauchy_davenport :
          ∀ k ≥ 1,
            countIn (P.left + P.left) (2 * (k + 1) * counterexN k) ≥
                2 * countIn (P.left ∩ counterexI k) ((k + 1) * counterexN k) - 1 ∧
              countIn (P.right + P.right) (2 * (k + 1) * counterexN k) ≥
                2 * countIn (P.right ∩ counterexI k) ((k + 1) * counterexN k) - 1 := by
        intro k hk
        have h_cauchy_davenport_step :
            ∀ S : Finset ℕ,
              (∀ x ∈ S, x ∈ counterexI k) → (S + S).card ≥ 2 * S.card - 1 := by
          intros S hS
          by_cases hS_empty : S.Nonempty;
          · exact interval_self_sum_bound k S hS hS_empty;
          · aesop;
        constructor <;> simp_all +decide [ countIn ];
        · refine le_trans
            (h_cauchy_davenport_step
              {x ∈ Finset.range ((k + 1) * counterexN k) |
                x ∈ P.left ∧ x ∈ counterexI k}
              fun x hx => by
                simp +decide at hx
                exact hx.2.2)
            ?_;
          refine Nat.succ_le_succ ( Finset.card_mono ?_ );
          simp +decide [ Finset.subset_iff, Finset.mem_add ];
          rintro x a ha₁ ha₂ ha₃ b hb₁ hb₂ hb₃ rfl; exact ⟨ by linarith, Set.add_mem_add ha₂ hb₂ ⟩ ;
        · refine le_trans
            (h_cauchy_davenport_step
              {x ∈ Finset.range ((k + 1) * counterexN k) |
                x ∈ P.right ∧ x ∈ counterexI k}
              fun x hx => by
                simp +decide at hx
                exact hx.2.2)
            ?_;
          refine Nat.succ_le_succ ( Finset.card_mono ?_ );
          simp +decide [ Finset.subset_iff, Finset.mem_add ];
          rintro x y hy₁ hy₂ hy₃ z hz₁ hz₂ hz₃ rfl; exact ⟨ by linarith, Set.add_mem_add hy₂ hz₂ ⟩ ;
      -- Adding these inequalities and dividing by $2(k+1)N_k$, we get:
      have h_divide :
          ∀ k ≥ 1,
            ((countIn (P.left + P.left) (2 * (k + 1) * counterexN k)) : ℝ) /
                (2 * (k + 1) * counterexN k) +
              ((countIn (P.right + P.right) (2 * (k + 1) * counterexN k)) : ℝ) /
                (2 * (k + 1) * counterexN k) ≥
              (k * counterexN k - 1) / ((k + 1) * counterexN k) := by
        intro k hk
        have h_sum :
            (countIn (P.left + P.left) (2 * (k + 1) * counterexN k)) +
              (countIn (P.right + P.right) (2 * (k + 1) * counterexN k)) ≥
                2 * (k * counterexN k) - 2 := by
          grind;
        rw [ ← add_div, ge_iff_le, div_le_div_iff₀ ] <;> norm_cast;
        · rw [ Int.subNatNat_eq_coe ]
          push_cast
          nlinarith [
            Nat.sub_add_cancel (show 2 ≤ 2 * (k * counterexN k) from by
              nlinarith [show 0 < counterexN k from pow_pos (by decide) _]),
            show 0 < (k + 1) * counterexN k from
              mul_pos (Nat.succ_pos _) (pow_pos (by decide) _)]
        · exact Nat.mul_pos ( Nat.succ_pos _ ) ( pow_pos ( by decide ) _ );
        · exact mul_pos ( by positivity ) ( pow_pos ( by decide ) _ );
      -- Taking the limit as $k \to \infty$, we get:
      have h_limit :
          Filter.Tendsto (fun k : ℕ =>
            ((countIn (P.left + P.left) (2 * (k + 1) * counterexN k)) : ℝ) /
                (2 * (k + 1) * counterexN k) +
              ((countIn (P.right + P.right) (2 * (k + 1) * counterexN k)) : ℝ) /
                (2 * (k + 1) * counterexN k))
            Filter.atTop (nhds (d₁ + d₂)) := by
        have h_limit :
            Filter.Tendsto (fun k : ℕ =>
              ((countIn (P.left + P.left) (2 * (k + 1) * counterexN k)) : ℝ) /
                (2 * (k + 1) * counterexN k)) Filter.atTop (nhds d₁) ∧
              Filter.Tendsto (fun k : ℕ =>
                ((countIn (P.right + P.right) (2 * (k + 1) * counterexN k)) : ℝ) /
                  (2 * (k + 1) * counterexN k)) Filter.atTop (nhds d₂) := by
          have h_limit :
              Filter.Tendsto (fun N : ℕ => ((countIn (P.left + P.left) N) : ℝ) / N)
                  Filter.atTop (nhds d₁) ∧
                Filter.Tendsto (fun N : ℕ => ((countIn (P.right + P.right) N) : ℝ) / N)
                  Filter.atTop (nhds d₂) := by
            exact
              ⟨ by rw [ ← Filter.tendsto_add_atTop_iff_nat 1 ]; simpa using hD₁,
                by rw [ ← Filter.tendsto_add_atTop_iff_nat 1 ]; simpa using hD₂ ⟩
          convert And.intro
              (h_limit.1.comp <| show
                Filter.Tendsto (fun k : ℕ => 2 * (k + 1) * counterexN k)
                  Filter.atTop Filter.atTop from ?_)
              (h_limit.2.comp <| show
                Filter.Tendsto (fun k : ℕ => 2 * (k + 1) * counterexN k)
                  Filter.atTop Filter.atTop from ?_) using 2 <;>
            norm_cast
          · exact Filter.tendsto_atTop_mono
              (fun k => by
                nlinarith [show counterexN k ≥ 1 from Nat.one_le_pow _ _ (by decide)])
              tendsto_natCast_atTop_atTop
          · exact Filter.tendsto_atTop_mono
              (fun k => by
                nlinarith [show counterexN k ≥ 1 from Nat.one_le_pow _ _ (by decide)])
              tendsto_natCast_atTop_atTop
        exact h_limit.1.add h_limit.2;
      -- Taking the limit of the right-hand side as $k \to \infty$, we get:
      have h_rhs_limit :
          Filter.Tendsto
            (fun k : ℕ => ((k * counterexN k - 1) : ℝ) / ((k + 1) * counterexN k))
            Filter.atTop (nhds 1) := by
        -- We can simplify the expression inside the limit.
        suffices h_simplify :
            Filter.Tendsto
              (fun k : ℕ => (1 - 1 / (k * counterexN k : ℝ)) / (1 + 1 / (k : ℝ)))
              Filter.atTop (nhds 1) by
          refine h_simplify.congr' ?_;
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with k hk;
          field_simp [hk];
          rw [ sub_div, mul_div_cancel_right₀ _ (by
            norm_cast
            exact ne_of_gt (pow_pos (by decide) _)) ];
        norm_num [ counterexN ];
        exact le_trans
          (Filter.Tendsto.div
            (tendsto_const_nhds.sub <|
              Filter.Tendsto.mul
                (tendsto_inv_atTop_zero.comp <|
                  tendsto_pow_atTop_atTop_of_one_lt (by norm_num) |>
                    Filter.Tendsto.comp <|
                      tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
                tendsto_inv_atTop_nhds_zero_nat)
            (tendsto_const_nhds.add <| tendsto_inv_atTop_nhds_zero_nat)
            (by norm_num))
          (by norm_num)
      exact le_of_tendsto_of_tendsto h_rhs_limit h_limit
        (Filter.eventually_atTop.mpr ⟨1, fun k hk => h_divide k hk⟩)

/-- Theorem 2: There exists A with d(A+A) = 1 such that no bipartition gives
    both self-sumsets positive natural density. -/
theorem erdos741_strict_density_counterexample :
    ∃ A : Set ℕ, HasNatDensity (A + A) 1 ∧
      ∀ P : BiPartition A, ¬(∃ d₁ > 0, ∃ d₂ > 0,
        HasNatDensity (P.left + P.left) d₁ ∧ HasNatDensity (P.right + P.right) d₂) := by
  refine ⟨counterexA, ?_, ?_⟩
  · rw [counterexA_sumset_univ]; exact hasNatDensity_univ
  · intro P h
    obtain ⟨d₁, hd₁, d₂, hd₂, hD₁, hD₂⟩ := h
    linarith [prop_base4_scale P d₁ d₂ hd₁ hd₂ hD₁ hD₂,
             prop_interval_scale P d₁ d₂ hd₁ hd₂ hD₁ hD₂]

end

#print axioms erdos741_upper_density
-- 'Erdos741b.erdos741_upper_density' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms erdos741_strict_density_counterexample
-- 'Erdos741b.erdos741_strict_density_counterexample' depends on axioms: [propext, Classical.choice,
-- Quot.sound]

end Erdos741b
