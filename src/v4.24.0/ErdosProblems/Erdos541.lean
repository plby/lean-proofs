/-

This is a Lean formalization of a solution to Erdős Problem 541.
https://www.erdosproblems.com/forum/thread/541

The result was proven for sufficiently large primes by Erdős and
Szemerédi and by Gao, Hamidoune, and Wang for all moduli (not
necessarily prime).

[ErSz76] Erdős, E. and Szemerédi, E., On a problem of
Graham. Publ. Math. Debrecen (1976), 123--127.

[GHW10] Gao, Weidong and Hamidoune, Yahya Ould and Wang, Guoqing,
Distinct length modular zero-sum subsequences: a proof of Graham's
conjecture. J. Number Theory (2010), 1425--1431.


Apparently ChatGPT chose to explain a proof closer to one by David
J. Grynkiewicz.

David J. Grynkiewicz, Note on a Conjecture of Graham, arXiv:0903.3200
(2009), later published in European Journal of Combinatorics (2011).


The proof was auto-formalized by Aristotle (from Harmonic), except one
lemma which was proven by ChatGPT.  The final theorem statement was
available from the Formal Conjectures project.


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We have formalized and proved the main theorem `thm_main` stating that if a sequence of length `p` in `Z/pZ` has a unique zero-sum length `r`, then it takes at most 2 distinct values. The proof follows the provided outline, utilizing lemmas such as `lem_max_multiplicity`, `lem_find_h`, and auxiliary claims about the structure of the sequence.
-/

import Mathlib

namespace Erdos541


set_option linter.mathlibStandardSet false

open scoped Classical
open scoped Pointwise
open Multiset
open Filter

set_option maxHeartbeats 0

noncomputable section

/-
Definitions of Σ_k(S), Σ_≤k(S), Σ_≥k(S), and h(S).
-/
variable {G : Type*} [AddCommMonoid G] [DecidableEq G]

/-- The set of sums of subsequences of `S` of length `k`. -/
def seq_sigma (S : Multiset G) (k : ℕ) : Finset G :=
  ((S.powersetCard k).map sum).toFinset

/-- The set of sums of subsequences of `S` of length `1` to `k`. -/
def seq_sigma_le (S : Multiset G) (k : ℕ) : Finset G :=
  ((Finset.range k).image (fun i => seq_sigma S (i + 1))).biUnion id

/-- The set of sums of subsequences of `S` of length `k` to `|S|`. -/
def seq_sigma_ge (S : Multiset G) (k : ℕ) : Finset G :=
  ((Finset.range (card S + 1)).filter (fun i => k ≤ i)).image (fun i => seq_sigma S i) |>.biUnion id

/-- The maximal multiplicity of an element in `S`. -/
def max_multiplicity (S : Multiset G) : ℕ :=
  (S.toFinset.image (S.count ·)).max.getD 0

/-
If $h(S) \le k$, then $S$ can be partitioned into $k$ sets (possibly empty).
-/
lemma exists_partition_into_sets {G : Type*} [DecidableEq G] (S : Multiset G) (k : ℕ)
    (h_mul : max_multiplicity S ≤ k) :
    ∃ A : Fin k → Finset G, ∑ i, (A i).val = S := by
  -- Let's denote the support of $S$ as $T$. Since $S$ is a finite multiset, $T$ is also finite.
  let T := Multiset.toFinset S;
  -- We define the sets $A_i$ by distributing the elements of $T$ among them such that each $A_i$ contains at most one copy of each element.
  obtain ⟨A, hA⟩ : ∃ A : Fin k → Finset G, (∀ x ∈ T, (Finset.univ.filter (fun i => x ∈ A i)).card = S.count x) ∧ (∀ i, ∀ x ∈ A i, x ∈ T) := by
    have h_dist : ∀ x ∈ T, ∃ A_x : Finset (Fin k), A_x.card = Multiset.count x S := by
      intro x hx
      have h_card : Multiset.count x S ≤ k := by
        have h_count_le_k : ∀ x ∈ T, S.count x ≤ max_multiplicity S := by
          unfold max_multiplicity;
          intro x hx;
          have := Finset.le_max ( Finset.mem_image_of_mem ( fun x => Multiset.count x S ) hx );
          cases h : Finset.max ( Finset.image ( fun x => Multiset.count x S ) T ) <;> aesop;
        exact le_trans ( h_count_le_k x hx ) h_mul;
      have h_dist : ∃ A_x : Finset (Fin k), A_x.card = Multiset.count x S := by
        have h_card : Multiset.count x S ≤ k := h_card
        have h_finset : ∃ A_x : Finset (Fin k), A_x.card = Multiset.count x S := by
          have h_finset : Finset.card (Finset.univ : Finset (Fin k)) ≥ Multiset.count x S := by
            aesop
          exact Exists.imp ( by aesop ) ( Finset.exists_subset_card_eq h_finset )
        exact h_finset;
      exact h_dist;
    choose! A hA using h_dist;
    refine' ⟨ fun i => Finset.filter ( fun x => i ∈ A x ) T, _, _ ⟩ <;> aesop;
  use A;
  ext x;
  by_cases hx : x ∈ T;
  · have h_count_x : ∀ x ∈ T, Multiset.count x (∑ i, (A i).val) = ∑ i, (if x ∈ A i then 1 else 0) := by
      intro x hx
      have h_count_x : Multiset.count x (∑ i, (A i).val) = ∑ i, Multiset.count x ((A i).val) := by
        induction' ( Finset.univ : Finset ( Fin k ) ) using Finset.induction <;> aesop;
      convert h_count_x using 2;
      split_ifs <;> simp_all +decide [ Multiset.count_eq_zero ];
      rw [ Multiset.count_eq_one_of_mem ];
      · exact Finset.nodup _;
      · aesop;
    aesop;
  · rw [ Multiset.count_eq_zero_of_notMem ];
    · rw [ Multiset.count_eq_zero_of_notMem ] ; aesop;
    · simp_all +decide [ Multiset.mem_sum ];
      exact fun i hi => hx ( hA.2 i x hi )

/-
If $h(S) \le k \le |S|$, then $S$ can be partitioned into $k$ nonempty sets.
-/
lemma exists_nonempty_partition_into_sets {G : Type*} [DecidableEq G] (S : Multiset G) (k : ℕ)
    (hk_card : k ≤ card S) (h_mul : max_multiplicity S ≤ k) :
    ∃ A : Fin k → Finset G, (∀ i, (A i).Nonempty) ∧ ∑ i, (A i).val = S := by
  -- Let's apply the lemma h_partition and obtain the corresponding partition.
  obtain ⟨A, hA⟩ := exists_partition_into_sets S k h_mul;
  induction' k with k ih;
  · aesop;
  · induction' i : Finset.card ( Finset.filter ( fun i => A i = ∅ ) Finset.univ ) using Nat.strong_induction_on with n ih generalizing A;
    by_cases hn : n = 0;
    · simp_all +decide [ Finset.ext_iff ];
      exact Filter.frequently_principal.mp fun a ↦ a i hA;
    · -- If there is an empty set $A_i$, since $\sum |A_j| = |S| \ge k + 1 > m$ (if $m < k + 1$), there must be some $A_j$ with $|A_j| \ge 2$.
      obtain ⟨i, hi⟩ : ∃ i, A i = ∅ := by
        exact Exists.elim ( Finset.card_pos.mp ( by linarith [ Nat.pos_of_ne_zero hn ] ) ) fun x hx => ⟨ x, by simpa using hx ⟩
      obtain ⟨j, hj⟩ : ∃ j, 2 ≤ (A j).card := by
        have h_sum_card : ∑ i, (A i).card = S.card := by
          replace hA := congr_arg Multiset.card hA ; aesop;
        contrapose! hk_card;
        rw [ ← h_sum_card, Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ i ) ];
        exact lt_of_le_of_lt ( add_le_add_left ( Finset.sum_le_sum fun _ _ => Nat.le_of_lt_succ ( hk_card _ ) ) _ ) ( by simp +decide [ Finset.card_sdiff, * ] );
      -- Pick $x \in A_j$. Move $x$ to $A_i$.
      obtain ⟨x, hx⟩ : ∃ x, x ∈ A j := by
        exact Finset.card_pos.mp ( pos_of_gt hj )
      set A' : Fin (k + 1) → Finset G := fun l => if l = i then {x} else if l = j then A j \ {x} else A l;
      refine' ih ( Finset.card ( Finset.filter ( fun l => A' l = ∅ ) Finset.univ ) ) _ A' _ _;
      · refine' lt_of_le_of_lt ( Finset.card_le_card _ ) _;
        exact Finset.filter ( fun l => A l = ∅ ) Finset.univ \ { i };
        · intro l hl; contrapose! hl; aesop;
        · grind;
      · rw [ ← hA ];
        rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ i ) ];
        rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_sdiff.mpr ⟨ Finset.mem_univ j, by aesop ⟩ : j ∈ Finset.univ \ { i } ) ];
        rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ j ) ];
        rw [ show ( Finset.univ \ { j } : Finset ( Fin ( k + 1 ) ) ) = ( Finset.univ \ { i } ) \ { j } ∪ { i } from ?_, Finset.sum_union ] <;> norm_num;
        · rw [ show A' i = { x } from if_pos rfl, show A' j = A j \ { x } from if_neg ( by aesop ) |> fun h => h.trans ( if_pos rfl ) ];
          simp +decide [ ← add_assoc, ← Multiset.cons_coe, hx, hi ];
          exact Finset.sum_congr rfl fun x hx => by aesop;
        · grind;
      · rfl

/-
Generalized Cauchy-Davenport for k sets.
-/
lemma cauchy_davenport_finset_sum {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : k ≠ 0)
    (A : Fin k → Finset (ZMod p)) (hA : ∀ i, (A i).Nonempty) :
    min p (∑ i, (A i).card - k + 1) ≤ (∑ i, A i).card := by
  have h_cauchy : ∀ (A₁ A₂ : Finset (ZMod p)), A₁.Nonempty → A₂.Nonempty → Finset.card (A₁ + A₂) ≥ min p (Finset.card A₁ + Finset.card A₂ - 1) := by
    intro A₁ A₂ hA₁ hA₂; have := @ZMod.cauchy_davenport;
    exact this Fact.out hA₁ hA₂;
  induction' k with k ih;
  · contradiction;
  · rcases eq_or_ne k 0 <;> simp_all +decide [ Fin.sum_univ_succ ];
    · aesop;
    · cases' ih ( fun i => A i.succ ) ( fun i => hA i.succ ) with h h;
      · have h_card_ge_p : Finset.card (A 0 + ∑ i : Fin k, A (Fin.succ i)) ≥ Finset.card (∑ i : Fin k, A (Fin.succ i)) := by
          exact?;
        exact Or.inl ( le_trans h h_card_ge_p );
      · specialize h_cauchy ( A 0 ) ( ∑ i : Fin k, A ( Fin.succ i ) ) ( hA 0 ) ( by
          contrapose! h; aesop );
        grind

/-
Lemma [Setpartition lower bound for $\Sigma_k$]
Let $p$ be prime, let $S$ be a sequence over $\G$, and let $k$ be an integer with $1\le k\le |S|$.
Assume $h(S)\le k$.
Then there exist nonempty sets $A_1,\dots,A_k\subseteq \G$ such that
1. $S=\prod_{i=1}^k \prod_{a\in A_i} a$ (each $A_i$ contains no repeated element, and the multiset union of the $A_i$ equals $S$);
2. $A_1+\cdots +A_k\subseteq \Sigma_k(S)$.
In particular, if $|S|\ge p+k-1$, then $\Sigma_k(S)=\G$.
-/
lemma lem_setpartition {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (k : ℕ)
    (hk_pos : 1 ≤ k) (hk_card : k ≤ card S) (h_mul : max_multiplicity S ≤ k) :
    ∃ A : Fin k → Finset (ZMod p),
      (∀ i, (A i).Nonempty) ∧
      (∑ i : Fin k, (A i).val) = S ∧
      (∑ i : Fin k, A i) ⊆ seq_sigma S k ∧
      (card S ≥ p + k - 1 → seq_sigma S k = Finset.univ) := by
  obtain ⟨ A, hA₁, hA₂ ⟩ := exists_nonempty_partition_into_sets S k hk_card h_mul;
  use A;
  have h_sum_subset : ∀ x ∈ ∑ i, A i, x ∈ seq_sigma S k := by
    intro x hx
    obtain ⟨a, ha⟩ : ∃ a : Fin k → ZMod p, (∀ i, a i ∈ A i) ∧ x = ∑ i, a i := by
      have h_exists_a : ∀ (k : ℕ) (A : Fin k → Finset (ZMod p)), (∀ i, (A i).Nonempty) → ∀ x ∈ ∑ i, A i, ∃ a : Fin k → ZMod p, (∀ i, a i ∈ A i) ∧ x = ∑ i, a i := by
        intro k A hA₁ x hx; induction' k with k ih generalizing x <;> simp_all +decide [ Fin.sum_univ_succ ] ;
        rw [ Finset.mem_add ] at hx; obtain ⟨ a, ha, b, hb, rfl ⟩ := hx; obtain ⟨ a', ha', rfl ⟩ := ih _ ( fun i => hA₁ i.succ ) _ hb; exact ⟨ Fin.cons a a', fun i => by cases i using Fin.inductionOn <;> aesop, by simp +decide [ Fin.sum_univ_succ ] ⟩ ;
      exact h_exists_a k A hA₁ x hx;
    -- Since $a_i \in A_i$ for all $i$, the multiset $\{a_1, \dots, a_k\}$ is a sub-multiset of $S$.
    have h_sub_multiset : Multiset.ofList (List.ofFn a) ≤ S := by
      rw [ ← hA₂ ];
      simp +decide [ List.ofFn_eq_map, Finset.sum ];
      induction' ( List.finRange k ) with i hi <;> simp_all +decide [ List.map ];
      exact add_le_add ( Multiset.singleton_le.mpr ( ha.1 i ) ) ‹_›;
    unfold seq_sigma; aesop;
  refine ⟨ hA₁, hA₂, h_sum_subset, ?_ ⟩;
  intro h_card
  have h_cauchy_davenport : (∑ i, A i).card ≥ p := by
    have h_cauchy_davenport : (∑ i, (A i).card) ≥ p + k - 1 := by
      replace hA₂ := congr_arg Multiset.card hA₂ ; aesop;
    have := cauchy_davenport_finset_sum ( show k ≠ 0 by linarith ) A hA₁;
    exact le_trans ( by omega ) this;
  exact Finset.eq_of_subset_of_card_le ( fun x hx => Finset.mem_univ x ) ( by rw [ Finset.card_univ ] ; simpa [ Finset.card_univ ] using h_cauchy_davenport.trans ( Finset.card_le_card <| show ∑ i : Fin k, A i ⊆ seq_sigma S k from fun x hx => h_sum_subset x hx ) )

/-
Proposition [Uniform representation from size]
Let $p$ be prime and let $A,B\subseteq \G$.
For $x\in \G$ let
\[
r_{A,B}(x)=|\{(a,b)\in A\times B: a+b=x\}|.
\]
Then $r_{A,B}(x)\ge |A|+|B|-p$ for every $x\in \G$.
In particular, if $|A|+|B|\ge p+k$, then $r_{A,B}(x)\ge k$ for every $x$.
-/
def representation_count {G : Type*} [AddCommMonoid G] [DecidableEq G] (A B : Finset G) (x : G) : ℕ :=
  ((A ×ˢ B).filter (fun p => p.1 + p.2 = x)).card

lemma prop_rep {p : ℕ} [Fact p.Prime] (A B : Finset (ZMod p)) (x : ZMod p) :
    representation_count A B x ≥ A.card + B.card - p := by
  -- Let $r_{A,B}(x)=|\{(a,b)\in A\times B: a+b=x\}|$.
  set r := fun x => Finset.card (Finset.filter (fun (ab : ZMod p × ZMod p) => ab.1 + ab.2 = x) (A ×ˢ B)) with hr_def
  have hr_eq : r x = Finset.card (Finset.filter (fun a => x - a ∈ B) A) := by
    refine' Finset.card_bij ( fun y hy => y.1 ) _ _ _ <;> aesop;
  have hr_bound : Finset.card (Finset.filter (fun a => x - a ∈ B) A) ≥ Finset.card A + Finset.card B - p := by
    have hr_bound : Finset.card (A ∩ (Finset.image (fun b => x - b) B)) ≥ Finset.card A + Finset.card (Finset.image (fun b => x - b) B) - p := by
      have hr_bound : Finset.card (A ∪ Finset.image (fun b => x - b) B) ≤ p := by
        exact le_trans ( Finset.card_le_univ _ ) ( by norm_num );
      exact Nat.sub_le_of_le_add <| by linarith [ Finset.card_union_add_card_inter A ( Finset.image ( fun b => x - b ) B ) ] ;
    convert hr_bound using 1;
    · exact congr_arg Finset.card ( by ext; aesop );
    · rw [ Finset.card_image_of_injective _ ( sub_right_injective ) ];
  convert hr_bound using 1

/-
If $S$ is zero-sum free, then the number of subsums is at least the length of $S$.
-/
lemma subsums_card_ge_card {G : Type*} [AddCommGroup G] [DecidableEq G] (S : Multiset G)
    (h_zs : 0 ∉ seq_sigma_ge S 1) :
    (seq_sigma_ge S 1).card ≥ S.card := by
  contrapose! h_zs;
  -- Consider the subsequence $\{x, -x\}$ of $S$. This subsequence sums to $0$.
  have h_subseq : ∃ T : Multiset G, T ≤ S ∧ T.card ≥ 1 ∧ T.sum = 0 := by
    -- By the pigeonhole principle, since $S$ is non-empty, there must exist a subsequence of $S$ that sums to zero.
    have h_pigeonhole : ∃ T : Multiset G, T ≤ S ∧ T.card ≥ 1 ∧ T.sum = 0 := by
      have h_count : ∃ i j : Fin (S.card + 1), i < j ∧ (Multiset.sum (Multiset.ofList (List.take i S.toList))) = (Multiset.sum (Multiset.ofList (List.take j S.toList))) := by
        have h_pigeonhole : Finset.card (Finset.image (fun i : Fin (S.card + 1) => Multiset.sum (Multiset.ofList (List.take i S.toList))) (Finset.univ : Finset (Fin (S.card + 1)))) ≤ (seq_sigma_ge S 1).card + 1 := by
          refine' le_trans ( Finset.card_le_card _ ) _;
          exact insert 0 ( seq_sigma_ge S 1 );
          · intro y hy;
            simp +zetaDelta at *;
            rcases hy with ⟨ a, rfl ⟩ ; rcases a with ⟨ _ | a, ha ⟩ <;> simp_all +decide [ seq_sigma_ge ] ;
            refine' Or.inr ⟨ a + 1, ⟨ by linarith, by linarith ⟩, _ ⟩;
            refine' Finset.mem_coe.2 ( Multiset.mem_toFinset.2 _ );
            refine' Multiset.mem_map.2 ⟨ Multiset.ofList ( List.take ( a + 1 ) S.toList ), _, _ ⟩ <;> simp +decide [ List.take_append ];
            exact ⟨ by simpa using Multiset.le_iff_exists_add.mpr ⟨ Multiset.ofList ( List.drop ( a + 1 ) S.toList ), by simp +decide [ List.take_append_drop ] ⟩, by linarith ⟩;
          · exact Finset.card_insert_le _ _;
        by_cases h_eq : ∀ i j : Fin (S.card + 1), i ≠ j → (Multiset.sum (Multiset.ofList (List.take i S.toList))) ≠ (Multiset.sum (Multiset.ofList (List.take j S.toList)));
        · exact absurd h_pigeonhole ( by rw [ Finset.card_image_of_injective _ fun i j hij => not_imp_not.mp ( h_eq i j ) hij ] ; simp +decide ; linarith );
        · push_neg at h_eq;
          obtain ⟨ i, j, hij, h ⟩ := h_eq; exact hij.lt_or_gt.elim ( fun hi => ⟨ i, j, hi, h ⟩ ) fun hj => ⟨ j, i, hj, h.symm ⟩ ;
      obtain ⟨ i, j, hij, h ⟩ := h_count;
      refine' ⟨ Multiset.ofList ( List.drop ( i : ℕ ) ( List.take ( j : ℕ ) S.toList ) ), _, _, _ ⟩ <;> simp_all +decide [ List.take_append_drop ];
      · rw [ Multiset.le_iff_count ];
        intro a;
        have h_count_le : List.count a (List.drop (i : ℕ) (List.take (j : ℕ) S.toList)) ≤ List.count a S.toList := by
          have h_count_le : List.count a (List.drop (i : ℕ) (List.take (j : ℕ) S.toList)) ≤ List.count a (List.take (j : ℕ) S.toList) := by
            rw [ ← List.take_append_drop ( i : ℕ ) ( List.take ( j : ℕ ) S.toList ), List.count_append ] ; aesop;
          have h_count_le : List.count a (List.take (j : ℕ) S.toList) ≤ List.count a S.toList := by
            rw [ ← List.take_append_drop ( j : ℕ ) S.toList, List.count_append ] ; simp +decide;
          linarith;
        convert h_count_le using 1;
        · exact coe_count a (List.drop (↑i) (List.take (↑j) S.toList));
        · rw [ ← Multiset.coe_count ] ; aesop;
      · grind;
      · have := List.sum_take_add_sum_drop ( List.take ( j : ℕ ) S.toList ) i; simp_all +decide [ add_comm ] ;
        grind;
    exact h_pigeonhole;
  obtain ⟨ T, hT₁, hT₂, hT₃ ⟩ := h_subseq;
  unfold seq_sigma_ge;
  simp +decide [ seq_sigma ];
  exact ⟨ T.card, ⟨ Nat.lt_succ_of_le ( Multiset.card_le_card hT₁ ), hT₂ ⟩, T, ⟨ hT₁, rfl ⟩, hT₃ ⟩

/-
Let $p$ be prime and let $S$ be a sequence over $\G$ of length $p-1$ with $0\notin \Sigma_{\ge 1}(S)$.
Then $|\supp(S)|=1$.
-/
lemma lem_zsfree_p_1 {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p))
    (h_len : S.card = p - 1) (h_zs : 0 ∉ seq_sigma_ge S 1) :
    S.toFinset.card = 1 := by
      have h_support : ∀ x ∈ S.toFinset, ∀ y ∈ S.toFinset, x ≠ y → False := by
        intro x hx y hy hxy
        obtain ⟨Sxy, hSxy⟩ : ∃ Sxy : Multiset (ZMod p), S = Sxy + {x, y} ∧ 0 ∉ seq_sigma_ge Sxy 1 := by
          obtain ⟨Sxy, hSxy⟩ : ∃ Sxy : Multiset (ZMod p), S = Sxy + {x, y} := by
            have h_partition : Multiset.count x S ≥ 1 ∧ Multiset.count y S ≥ 1 := by
              exact ⟨ Multiset.count_pos.mpr ( Multiset.mem_toFinset.mp hx ), Multiset.count_pos.mpr ( Multiset.mem_toFinset.mp hy ) ⟩;
            use S - {x, y};
            ext z; by_cases hz : z = x <;> by_cases hz' : z = y <;> aesop;
          refine' ⟨ Sxy, hSxy, _ ⟩;
          simp_all +decide [ seq_sigma_ge ];
          intro k hk₁ hk₂ hk₃; specialize h_zs k ( by linarith ) hk₂; simp_all +decide [ seq_sigma ] ;
          obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ := hk₃; specialize h_zs a; simp_all +decide [ Multiset.le_iff_count ] ;
          simp_all +decide [ Multiset.count_cons, Multiset.count_add ];
          grind;
        -- Since $Sxy$ is a subsequence of $S$, we have $|\Sigma_{\ge 0}(Sxy)| \ge p-2$.
        have h_sigma_ge_0_Sxy : (seq_sigma_ge Sxy 0).card ≥ p - 2 := by
          have h_sigma_ge_0_Sxy : (seq_sigma_ge Sxy 0).card ≥ Sxy.card + 1 := by
            have h_sigma_ge_0_Sxy : (seq_sigma_ge Sxy 0).card ≥ (seq_sigma_ge Sxy 1).card + 1 := by
              refine' Finset.card_lt_card _;
              constructor;
              · intro z hz; unfold seq_sigma_ge at *; aesop;
              · simp_all +decide [ seq_sigma_ge ];
                use 0; simp_all +decide [ Finset.subset_iff ] ;
                use 0; simp_all +decide [ seq_sigma ] ;
                exact hSxy.2;
            have h_sigma_ge_0_Sxy : (seq_sigma_ge Sxy 1).card ≥ Sxy.card := by
              apply subsums_card_ge_card; exact hSxy.right;
            linarith;
          rcases p with ( _ | _ | p ) <;> simp_all +decide;
        -- Since $x \neq y$, we have $-x \notin \Sigma_{\ge 0}(Sxy)$ and $-x \notin \Sigma_{\ge 0}(Sxy) + y \implies -x - y \notin \Sigma_{\ge 0}(Sxy)$.
        have h_neg_x_not_in_Sxy : -x ∉ seq_sigma_ge Sxy 0 := by
          contrapose! h_zs;
          -- Since $-x \in \Sigma_{\ge 0}(Sxy)$, we have $0 \in \Sigma_{\ge 1}(S)$.
          have h_zero_in_S : 0 ∈ seq_sigma_ge (Sxy + {x}) 1 := by
            unfold seq_sigma_ge at *;
            simp_all +decide [ Finset.mem_biUnion, Finset.mem_image ];
            obtain ⟨ a, ha₁, ha₂ ⟩ := h_zs; use a + 1; simp_all +decide [ seq_sigma ] ;
            obtain ⟨ T, ⟨ hT₁, hT₂ ⟩, hT₃ ⟩ := ha₂; use by linarith; ; use T + { x } ; aesop;
          simp_all +decide [ seq_sigma_ge ];
          obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ := h_zero_in_S; use a; simp_all +decide [ add_comm, add_left_comm, add_assoc ] ;
          refine' ⟨ by linarith, _ ⟩;
          refine' Finset.mem_of_subset _ ha₃;
          intro z hz; simp_all +decide [ seq_sigma ] ;
          obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ := hz; use a; simp_all +decide [ Multiset.le_iff_count ] ;
          intro z; specialize ha₁ z; by_cases hz : z = x <;> by_cases hz' : z = y <;> simp_all +decide [ Multiset.count_cons ] ;
          linarith
        have h_neg_x_not_in_Sxy_y : -x - y ∉ seq_sigma_ge Sxy 0 := by
          contrapose! h_zs;
          unfold seq_sigma_ge at *; simp_all +decide [ Finset.mem_biUnion ] ;
          obtain ⟨ a, ha₁, ha₂ ⟩ := h_zs; use a + 2; simp_all +decide [ seq_sigma ] ;
          exact ⟨ by omega, Or.inr ⟨ ha₂.choose + { y }, ⟨ by exact add_le_add_right ha₂.choose_spec.1.1 _, by simp +decide [ ha₂.choose_spec.1.2 ] ⟩, by simp +decide [ ha₂.choose_spec.2 ] ⟩ ⟩
        have h_neg_y_not_in_Sxy : -y ∉ seq_sigma_ge Sxy 0 := by
          simp_all +decide [ seq_sigma_ge ];
          intro k hk; specialize h_zs ( k + 1 ) ( by linarith ) ( by linarith ) ; contrapose! h_zs; simp_all +decide [ seq_sigma ] ;
          obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ := h_zs; exact Or.inl ⟨ a + { y }, ⟨ by exact add_le_add ha₁ ( by norm_num ), by simp +decide [ ha₂ ] ⟩, by simp +decide [ ha₃ ] ⟩ ;
        -- Since $x \neq y$, we have $-x$, $-y$, and $-x - y$ are distinct elements in $\mathbb{Z}/p\mathbb{Z}$.
        have h_distinct : -x ≠ -y ∧ -x ≠ -x - y ∧ -y ≠ -x - y := by
          simp_all +decide [ sub_eq_add_neg ];
          constructor <;> intro h <;> simp_all +decide [ seq_sigma_ge ];
          · specialize h_neg_y_not_in_Sxy 0 ; simp_all +decide [ seq_sigma ];
          · specialize h_neg_x_not_in_Sxy 0 ; simp_all +decide [ seq_sigma ];
        have h_card_Sxy : (seq_sigma_ge Sxy 0 ∪ {-x, -y, -x - y}).card ≤ p := by
          exact le_trans ( Finset.card_le_univ _ ) ( by norm_num );
        grind;
      exact Finset.card_eq_one.mpr ⟨ Classical.choose ( Multiset.card_pos_iff_exists_mem.mp ( by linarith [ Nat.sub_pos_of_lt ( Fact.out : p > 1 ) ] ) ), Finset.eq_singleton_iff_unique_mem.mpr ⟨ Multiset.mem_toFinset.mpr ( Classical.choose_spec ( Multiset.card_pos_iff_exists_mem.mp ( by linarith [ Nat.sub_pos_of_lt ( Fact.out : p > 1 ) ] ) ) ), fun y hy => Classical.not_not.mp fun h => h_support _ hy _ ( Multiset.mem_toFinset.mpr ( Classical.choose_spec ( Multiset.card_pos_iff_exists_mem.mp ( by linarith [ Nat.sub_pos_of_lt ( Fact.out : p > 1 ) ] ) ) ) ) h ⟩ ⟩

/-
The size of the union of $\{1, \dots, m-1\}$ and $\{1-h, \dots, m-h\}$ is at least $\min(p, m+h-1)$.
-/
lemma card_union_bound {p : ℕ} [Fact p.Prime] (m h_nat : ℕ)
    (hm : m ≤ p - 1) (hh : 2 ≤ h_nat) (hhm : h_nat ≤ m) :
    ((Finset.Ico 1 m).image (Nat.cast : ℕ → ZMod p) ∪
     ((Finset.Ico 1 (m + 1)).image (Nat.cast : ℕ → ZMod p)).image (fun x => x - (h_nat : ZMod p))).card ≥ min p (m + h_nat - 1) := by
       rw [ min_def ];
       split_ifs;
       · have h_union_size : Finset.image Nat.cast (Finset.Ico 1 m) ∪ Finset.image (fun x => x - h_nat : ZMod p → ZMod p) (Finset.image Nat.cast (Finset.Ico 1 (m + 1))) ⊇ Finset.image (fun x : ℕ => x : ℕ → ZMod p) (Finset.Ico 0 p) := by
           simp +decide [ Finset.subset_iff ];
           intro a ha
           by_cases h_case : a < m;
           · by_cases ha_zero : a = 0;
             · exact Or.inr ⟨ h_nat, ⟨ by linarith, by linarith ⟩, by simp +decide [ ha_zero ] ⟩;
             · exact Or.inl ⟨ a, ⟨ Nat.pos_of_ne_zero ha_zero, h_case ⟩, rfl ⟩;
           · exact Or.inr ⟨ a + h_nat - p, ⟨ by omega, by omega ⟩, by rw [ Nat.cast_sub ( by omega ) ] ; simp +decide [ Nat.cast_add, Nat.cast_sub ( by omega : p ≤ a + h_nat ) ] ⟩;
         refine le_trans ?_ ( Finset.card_mono h_union_size );
         rw [ Finset.card_image_of_injOn ] <;> norm_num [ Function.Injective ];
         exact fun x hx y hy hxy => Nat.mod_eq_of_lt hx.out ▸ Nat.mod_eq_of_lt hy.out ▸ by simpa [ ZMod.natCast_eq_natCast_iff ] using hxy;
       · -- The union of the sets $\{1, \dots, m-1\}$ and $\{1-h, \dots, m-h\}$ is the set $\{1-h, \dots, m-1\}$.
         have h_union : (Finset.image (Nat.cast : ℕ → ZMod p) (Finset.Ico 1 m) ∪ Finset.image (fun x : ZMod p => x - h_nat) (Finset.image (Nat.cast : ℕ → ZMod p) (Finset.Ico 1 (m + 1)))) = Finset.image (fun x : ℤ => x : ℤ → ZMod p) (Finset.Ico (1 - h_nat : ℤ) m) := by
           ext x
           simp [Finset.mem_union, Finset.mem_image];
           constructor;
           · rintro ( ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ | ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ );
             · use a;
               norm_cast;
               exact ⟨ ⟨ by linarith, ha₂ ⟩, rfl ⟩;
             · refine' ⟨ a - h_nat, _, _ ⟩ <;> norm_num [ Nat.cast_sub ( show h_nat ≤ a from _ ) ];
               exact ⟨ ha₁, by rw [ sub_lt_iff_lt_add ] ; norm_cast; linarith ⟩;
           · rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩;
             by_cases ha₃ : a < 0;
             · refine Or.inr ⟨ Int.toNat ( a + h_nat ), ⟨ ?_, ?_ ⟩, ?_ ⟩ <;> norm_num [ Int.toNat_of_nonneg ( by linarith : 0 ≤ a + h_nat ) ];
               · linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ a + h_nat ) ];
               · linarith;
               · norm_cast;
                 rw [ Int.subNatNat_eq_coe ] ; norm_num [ Int.toNat_of_nonneg ( by linarith : 0 ≤ a + h_nat ) ];
             · by_cases ha₄ : a = 0;
               · exact Or.inr ⟨ h_nat, ⟨ by linarith, by linarith ⟩, by simp +decide [ ha₄ ] ⟩;
               · exact Or.inl ⟨ a.natAbs, ⟨ by omega, by omega ⟩, by simp +decide [ abs_of_nonneg ( le_of_not_gt ha₃ ) ] ⟩;
         rw [ h_union, Finset.card_image_of_injOn ] <;> norm_num [ Function.Injective ];
         · omega;
         · intros x hx y hy hxy;
           rw [ ZMod.intCast_eq_intCast_iff ] at hxy;
           rw [ Int.modEq_iff_dvd ] at hxy;
           obtain ⟨ k, hk ⟩ := hxy; nlinarith [ show k = 0 by nlinarith [ hx.1, hx.2, hy.1, hy.2, Nat.sub_add_cancel ( show 1 ≤ p from Nat.Prime.pos Fact.out ), Nat.sub_add_cancel ( show 1 ≤ m + h_nat from by linarith ) ] ] ;

/-
If $h \in \{1, \dots, m\} \subseteq \mathbb{Z}/p\mathbb{Z}$ and $h \ne 1$, then $|\{1, \dots, m-1\} \cap (\{1, \dots, m\} - h)| \le m-2$.
-/
lemma card_intersection_bound {p : ℕ} [Fact p.Prime] (m : ℕ) (h : ZMod p)
    (hm : m ≤ p - 1)
    (h_in : h ∈ (Finset.Ico 1 (m + 1)).image (Nat.cast : ℕ → ZMod p))
    (h_ne_one : h ≠ 1) :
    ((Finset.Ico 1 m).image (Nat.cast : ℕ → ZMod p) ∩
     ((Finset.Ico 1 (m + 1)).image (Nat.cast : ℕ → ZMod p)).image (fun x => x - h)).card ≤ m - 2 := by
       -- Let $A = \{1, \dots, m-1\}$ and $B = \{1, \dots, m\} - h$.
       set A : Finset (ZMod p) := Finset.image (Nat.cast : ℕ → ZMod p) (Finset.Ico 1 m)
       set B : Finset (ZMod p) := Finset.image (fun x : ZMod p => x - h) (Finset.image (Nat.cast : ℕ → ZMod p) (Finset.Ico 1 (m + 1)));
       -- Since $h \in \{1, \dots, m\}$ and $h \ne 1$, let $h_{nat}$ be the integer representative in $[1, m]$. Then $h_{nat} \ge 2$.
       obtain ⟨h_nat, hh_nat⟩ : ∃ h_nat : ℕ, 2 ≤ h_nat ∧ h_nat ≤ m ∧ h = (h_nat : ZMod p) := by
         norm_num +zetaDelta at *;
         obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ := h_in; exact ⟨ a, Nat.lt_of_le_of_ne ha₁ ( Ne.symm <| by aesop ), Nat.le_of_lt_succ ha₂, rfl ⟩ ;
       -- By `card_union_bound`, $|A \cup B| \ge \min(p, m+h_{nat}-1)$.
       have h_union_bound : (A ∪ B).card ≥ min p (m + h_nat - 1) := by
         convert card_union_bound _ _ _ _ _ <;> aesop;
       -- Using the formula $|A \cap B| = |A| + |B| - |A \cup B|$, we get $|A \cap B| \le |A| + |B| - \min(p, m + h_{nat} - 1)$.
       have h_inter_bound : (A ∩ B).card ≤ A.card + B.card - min p (m + h_nat - 1) := by
         grind;
       -- Since $|A| = m-1$ and $|B| = m$, we have $|A \cap B| \le (m-1) + m - \min(p, m + h_{nat} - 1)$.
       have h_inter_bound_simplified : (A ∩ B).card ≤ (m - 1) + m - min p (m + h_nat - 1) := by
         refine le_trans h_inter_bound ?_;
         gcongr;
         · exact Finset.card_image_le.trans ( by simpa );
         · exact Finset.card_image_le.trans ( Finset.card_image_le.trans ( by simp +arith +decide ) );
       grind

/-
The set of all subsums of a multiset $S$ (including the empty sum) is equal to the sumset sum of $\{0, x\}$ for all $x \in S$.
-/
lemma subsums_eq_sum_pair_sets {G : Type*} [AddCommMonoid G] [DecidableEq G] (S : Multiset G) :
    seq_sigma_ge S 0 = (S.map (fun x => ({0, x} : Finset G))).sum := by
      ext x;
      induction' S using Multiset.induction with a S ih generalizing x <;> simp_all +decide [ Finset.sum_insert, Finset.sum_singleton ];
      · unfold seq_sigma_ge;
        unfold seq_sigma; aesop;
      · unfold seq_sigma_ge at *; simp_all +decide [ Finset.mem_add, Finset.mem_union ] ;
        constructor;
        · rintro ⟨ k, hk, hx ⟩ ; rcases k with ( _ | k ) <;> simp_all +decide [ seq_sigma ] ;
          · exact Or.inl ( by simpa using ih 0 |>.1 ⟨ 0, Nat.zero_lt_succ _, ∅, by simp +decide ⟩ );
          · rcases hx with ( ⟨ t, ⟨ ht₁, ht₂ ⟩, rfl ⟩ | ⟨ t, ⟨ ht₁, ht₂ ⟩, rfl ⟩ );
            · exact Or.inl ( ih _ |>.1 ⟨ _, Nat.lt_succ_of_le ( by linarith [ Multiset.card_le_card ht₁ ] ), _, ⟨ ht₁, ht₂ ⟩, rfl ⟩ );
            · exact Or.inr ⟨ _, ih _ |>.1 ⟨ k, hk, t, ⟨ ht₁, ht₂ ⟩, rfl ⟩, rfl ⟩;
        · rintro ( hx | ⟨ z, hz, rfl ⟩ );
          · obtain ⟨ k, hk, hk' ⟩ := ih x |>.2 hx;
            refine' ⟨ k, _, _ ⟩ <;> simp_all +decide [ seq_sigma ];
            · linarith;
            · exact ⟨ hk'.choose, ⟨ Multiset.le_cons_self _ _ |> le_trans hk'.choose_spec.1.1, hk'.choose_spec.1.2 ⟩, hk'.choose_spec.2 ⟩;
          · obtain ⟨ k, hk ⟩ := ih z |>.2 hz;
            use k + 1;
            unfold seq_sigma at *; aesop;

/-
Cauchy-Davenport inequality for a multiset of sets.
-/
lemma cauchy_davenport_multiset_sum {p : ℕ} [Fact p.Prime] (S : Multiset (Finset (ZMod p)))
    (hS : S ≠ 0) (h_nonempty : ∀ s ∈ S, s.Nonempty) :
    min p ((S.map Finset.card).sum - S.card + 1) ≤ S.sum.card := by
      -- By the induction hypothesis, the theorem holds for S'.
      have ih : ∀ (S' : Multiset (Finset (ZMod p))) (hS' : S' ≠ 0) (h_nonempty' : ∀ s ∈ S', s.Nonempty), min p ((Multiset.map Finset.card S').sum - S'.card + 1) ≤ (S').sum.card := by
        intro S' hS' h_nonempty'; induction' S' using Multiset.induction with s S' ih ; aesop;
        by_cases hS'' : S' = 0 <;> simp_all +decide;
        have h_cauchy_davenport : (s + S'.sum).card ≥ min p (s.card + S'.sum.card - 1) := by
          have := @cauchy_davenport_finset_sum p;
          specialize this ( show 2 ≠ 0 by decide ) ( fun i => if i = 0 then s else S'.sum ) ; simp_all +decide [ Fin.forall_fin_two ];
          contrapose! this;
          exact ⟨ Finset.nonempty_of_ne_empty ( by aesop_cat ), this.1, by omega ⟩;
        grind;
      exact ih S hS h_nonempty

/-
If $S$ is a nonempty multiset of non-zero elements in $\mathbb{Z}/p\mathbb{Z}$, then the number of subsums is at least $\min(p, |S| + 1)$.
-/
lemma subsums_card_lower_bound {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p))
    (hS_nonempty : S ≠ 0)
    (h_zero_not_in : 0 ∉ S) :
    (seq_sigma_ge S 0).card ≥ min p (S.card + 1) := by
      -- Apply the Cauchy-Davenport theorem to the sumset of the pairs.
      have h_cauchy_davenport : (Multiset.sum (Multiset.map (fun x => ({0, x} : Finset (ZMod p))) S)).card ≥ min p ((Multiset.map (fun _ => 2) S).sum - S.card + 1) := by
        have h_cauchy_davenport : ∀ T : Multiset (Finset (ZMod p)), T ≠ 0 → (∀ s ∈ T, s.Nonempty) → (Multiset.sum T).card ≥ min p ((Multiset.map Finset.card T).sum - T.card + 1) := by
          exact fun T a a_1 ↦ cauchy_davenport_multiset_sum T a a_1;
        convert h_cauchy_davenport _ _ _ using 3;
        · norm_num [ Finset.card_insert_of_notMem, h_zero_not_in ];
          rw [ Multiset.map_congr rfl fun x hx => Finset.card_pair <| by aesop ] ; norm_num [ mul_two ];
        · aesop;
        · aesop;
      convert h_cauchy_davenport using 2 ; simp +arith +decide [ subsums_eq_sum_pair_sets ];
      norm_num [ mul_two ]

/-
If $R$ has sum $m$ and subsums in $\{1, \dots, m\}$, and $R = h :: R'$ with $h \ne 1$, then the number of subsums of $R'$ is at most $m-2$.
-/
lemma subsums_card_upper_bound_of_interval {p : ℕ} [Fact p.Prime] (R : Multiset (ZMod p))
    (m : ℕ) (h_len : R.card = m) (h_m_le : m ≤ p - 1)
    (h_sum : R.sum = m)
    (h_subsums : seq_sigma_ge R 1 ⊆ (Finset.Ico 1 (m + 1)).image (Nat.cast : ℕ → ZMod p))
    (h : ZMod p) (h_ne_one : h ≠ 1)
    (R' : Multiset (ZMod p)) (h_R_eq : R = h ::ₘ R') :
    (seq_sigma_ge R' 1).card ≤ m - 2 := by
      -- Since $m \in \Sigma_{\ge 1}(R')$, there exists $U \subseteq R'$ with $\sigma(U)=m$.
      by_cases h_m_in_R'_subsums : (m : ZMod p) ∈ seq_sigma_ge R' 1;
      · have h_contradiction : (0 : ZMod p) ∈ seq_sigma_ge R 1 := by
          -- Since $m \in \Sigma_{\ge 1}(R')$, there exists $U \subseteq R'$ with $\sigma(U)=m$. Then $R \setminus U$ is a subsequence of $R$ with sum $\sigma(R) - \sigma(U) = m - m = 0$.
          obtain ⟨U, hU_sub, hU_sum⟩ : ∃ U : Multiset (ZMod p), U ≤ R' ∧ U.sum = (m : ZMod p) := by
            unfold seq_sigma_ge at h_m_in_R'_subsums;
            unfold seq_sigma at h_m_in_R'_subsums; aesop;
          have h_contradiction : ∃ V : Multiset (ZMod p), V ≤ R ∧ V.sum = 0 ∧ V ≠ 0 := by
            refine' ⟨ R - U, _, _, _ ⟩ <;> simp_all +decide [ Multiset.le_iff_count ];
            · intro a; by_cases ha : a = h <;> simp_all +decide [ Multiset.count_cons ] ;
            · have h_contradiction : (h ::ₘ R' - U).sum = (h ::ₘ R').sum - U.sum := by
                have h_contradiction : ∀ (A B : Multiset (ZMod p)), B ≤ A → (A - B).sum = A.sum - B.sum := by
                  intros A B hB_le_A; exact (by
                  have := Multiset.le_iff_exists_add.mp hB_le_A; aesop;);
                apply h_contradiction;
                exact le_trans ( Multiset.le_iff_count.mpr fun x => by aesop ) ( Multiset.le_cons_self _ _ );
              aesop;
            · simp_all +decide [ Multiset.cons_sub_of_le, Multiset.le_iff_count ];
          obtain ⟨ V, hV_sub, hV_sum, hV_ne ⟩ := h_contradiction; simp_all +decide [ seq_sigma_ge ] ;
          refine' ⟨ V.card, ⟨ _, _ ⟩, _ ⟩;
          · exact lt_of_le_of_lt ( Multiset.card_le_card hV_sub ) ( by simp +decide [ h_len ] );
          · exact Multiset.card_pos_iff_exists_mem.mpr ( Multiset.exists_mem_of_ne_zero hV_ne );
          · unfold seq_sigma; aesop;
        have := h_subsums h_contradiction; simp_all +decide ;
        obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ := this; rw [ ZMod.natCast_eq_zero_iff ] at ha₃; exact absurd ha₃ ( Nat.not_dvd_of_pos_of_lt ha₁ ( by linarith [ Nat.sub_add_cancel ( show 1 ≤ p from Nat.Prime.pos Fact.out ) ] ) ) ;
      · -- Also for $s \in \Sigma_{\ge 1}(R')$, $s+h \in \Sigma_{\ge 1}(R) \subseteq \{1, \dots, m\}$.
        have h_subsum_add_h_in_R : ∀ s ∈ seq_sigma_ge R' 1, s + h ∈ (Finset.Ico 1 (m + 1)).image (Nat.cast : ℕ → ZMod p) := by
          intro s hs;
          -- Since $s \in \Sigma_{\ge 1}(R')$, there exists a submultiset $U \subseteq R'$ such that $s = \sum U$.
          obtain ⟨U, hU⟩ : ∃ U : Multiset (ZMod p), U ≤ R' ∧ U ≠ 0 ∧ s = Multiset.sum U := by
            unfold seq_sigma_ge at hs;
            unfold seq_sigma at hs; aesop;
          -- Since $U \subseteq R'$, we have $U + \{h\} \subseteq R$.
          have h_subsum_add_h_subset_R : Multiset.sum (U + {h}) ∈ seq_sigma_ge R 1 := by
            simp_all +decide [ seq_sigma_ge ];
            refine' ⟨ U.card + 1, _, _ ⟩ <;> simp_all +decide [ seq_sigma ];
            · exact lt_of_le_of_lt ( Multiset.card_le_card hU.1 ) ( by linarith );
            · exact Or.inr ⟨ U, ⟨ hU.1, rfl ⟩, add_comm _ _ ⟩;
          simpa [ hU.2.2 ] using h_subsums h_subsum_add_h_subset_R;
        -- Thus $\Sigma_{\ge 1}(R') \subseteq \{1, \dots, m-1\} \cap (\{1, \dots, m\} - h)$.
        have h_subsums_subset : seq_sigma_ge R' 1 ⊆ ((Finset.Ico 1 m).image (Nat.cast : ℕ → ZMod p) ∩ ((Finset.Ico 1 (m + 1)).image (Nat.cast : ℕ → ZMod p)).image (fun x => x - h)) := by
          intro s hs;
          have h_s_in_Ico : s ∈ (Finset.Ico 1 (m + 1)).image (Nat.cast : ℕ → ZMod p) := by
            refine' h_subsums _;
            simp_all +decide [ seq_sigma_ge ];
            obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ := hs;
            refine' ⟨ a, ⟨ by linarith, ha₂ ⟩, _ ⟩;
            simp_all +decide [ seq_sigma ];
            exact ⟨ ha₃.choose, ⟨ le_trans ha₃.choose_spec.1.1 ( Multiset.le_cons_self _ _ ), ha₃.choose_spec.1.2 ⟩, ha₃.choose_spec.2 ⟩;
          simp_all +decide [ Finset.mem_image ];
          grind;
        refine le_trans ( Finset.card_le_card h_subsums_subset ) ?_;
        convert card_intersection_bound m h h_m_le _ h_ne_one using 1;
        replace h_subsums := @h_subsums ( h : ZMod p ) ; simp_all +decide [ seq_sigma_ge ] ;
        exact h_subsums 1 ( by linarith ) ( by linarith ) ( by unfold seq_sigma; aesop )

/-
Let $p$ be prime and let $R$ be a nonempty sequence over $\G$ with $|R|=m\le p-1$.
Assume
\[
\sigma(R)=m
\qquad\text{and}\qquad
\Sigma_{\ge 1}(R)\subseteq \{1,2,\dots,m\}\subseteq \G.
\]
Then $R=1^m$.
-/
lemma lem_interval_subsums {p : ℕ} [Fact p.Prime] (R : Multiset (ZMod p))
    (h_nonempty : R ≠ 0)
    (m : ℕ) (h_len : R.card = m) (h_m_le : m ≤ p - 1)
    (h_sum : R.sum = m)
    (h_subsums : seq_sigma_ge R 1 ⊆ (Finset.Ico 1 (m + 1)).image (Nat.cast : ℕ → ZMod p)) :
    R = Multiset.replicate m 1 := by
      by_contra h_contra;
      -- Assume $m \ge 2$. Assume for contradiction $R$ has a term $h \ne 1$.
      obtain ⟨h, h_ne_one, h_mem⟩ : ∃ h ∈ R, h ≠ 1 := by
        by_cases h_one : ∀ x ∈ R, x = 1;
        · exact False.elim <| h_contra <| Multiset.eq_replicate.mpr ⟨ h_len, h_one ⟩;
        · exact by push_neg at h_one; exact h_one;
      obtain ⟨R', h_R_eq⟩ : ∃ R' : Multiset (ZMod p), R = h ::ₘ R' := by
        exact Multiset.exists_cons_of_mem h_ne_one;
      -- First, show $0 \notin R$. If $0 \in R$, then $0 \in \Sigma_{\ge 1}(R) \subseteq \{1, \dots, m\}$. But $m \le p-1$, so $0 \notin \{1, \dots, m\}$. Contradiction.
      have h_zero_not_in_R : 0 ∉ R := by
        intro h_zero_in_R; have := h_subsums ( show 0 ∈ seq_sigma_ge R 1 from ?_ ) ; simp_all +decide [ seq_sigma_ge ] ;
        · obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ := this; rw [ ZMod.natCast_eq_zero_iff ] at ha₃; exact Nat.not_dvd_of_pos_of_lt ha₁ ( by linarith [ Nat.sub_add_cancel ( show 1 ≤ p from Nat.Prime.pos Fact.out ) ] ) ha₃;
        · simp_all +decide [ seq_sigma_ge ];
          use 1; simp_all +decide [ seq_sigma ] ;
          exact ⟨ by linarith, Or.imp id ( fun h => ⟨ { 0 }, ⟨ by aesop, by aesop ⟩, by aesop ⟩ ) h_zero_in_R ⟩;
      -- Since $\Sigma_{\ge 0}(R') = \Sigma_{\ge 1}(R') \cup \{0\}$, we have $|\Sigma_{\ge 0}(R')| \le |\Sigma_{\ge 1}(R')| + 1 \le m-1$.
      have h_card_sigma_ge_zero_R' : (seq_sigma_ge R' 0).card ≤ m - 1 := by
        have h_card_sigma_ge_zero_R' : (seq_sigma_ge R' 0).card ≤ (seq_sigma_ge R' 1).card + 1 := by
          have h_card_sigma_ge_zero_R' : seq_sigma_ge R' 0 = seq_sigma_ge R' 1 ∪ {0} := by
            ext x; simp [seq_sigma_ge];
            constructor <;> intro hx;
            · rcases hx with ⟨ a, ha, hx ⟩ ; rcases a with ( _ | a ) <;> simp_all +decide [ seq_sigma ] ;
              exact Or.inr ⟨ a + 1, ⟨ by linarith, by linarith ⟩, hx.choose, hx.choose_spec ⟩;
            · rcases hx with ( rfl | ⟨ a, ⟨ ha₁, ha₂ ⟩, hx ⟩ ) <;> [ exact ⟨ 0, Nat.zero_lt_succ _, by unfold seq_sigma; aesop ⟩ ; exact ⟨ a, ha₁, hx ⟩ ];
          exact h_card_sigma_ge_zero_R'.symm ▸ Finset.card_union_le _ _ |> le_trans <| by norm_num;
        have h_card_sigma_ge_one_R' : (seq_sigma_ge R' 1).card ≤ m - 2 := by
          apply subsums_card_upper_bound_of_interval R m h_len h_m_le h_sum h_subsums h h_mem R' h_R_eq;
        rcases m with ( _ | _ | m ) <;> simp_all +decide;
        linarith;
      have h_card_sigma_ge_zero_R' : (seq_sigma_ge R' 0).card ≥ min p (R'.card + 1) := by
        apply subsums_card_lower_bound;
        · aesop;
        · aesop;
      simp_all +decide [ Multiset.card_cons ];
      omega

/-
The set of sums of subsequences of length $k$ is the image of the set of sums of subsequences of length $|S|-k$ under the map $x \mapsto \sigma(S) - x$.
-/
lemma seq_sigma_complement {G : Type*} [AddCommGroup G] [DecidableEq G] (S : Multiset G) (k : ℕ)
    (hk : k ≤ S.card) :
    seq_sigma S k = (seq_sigma S (S.card - k)).image (fun x => S.sum - x) := by
      -- Let's choose any $x \in \Sigma_k(S)$.
      ext; simp [seq_sigma];
      constructor <;> rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩;
      · refine' ⟨ S - a, ⟨ _, _ ⟩, _ ⟩;
        · exact tsub_le_self;
        · rw [ ← ha₂, Multiset.card_sub ha₁ ];
        · rw [ sub_eq_of_eq_add ] ; rw [ ← Multiset.sum_add ] ; rw [ add_comm ] ; rw [ tsub_add_cancel_of_le ha₁ ];
      · refine' ⟨ S - a, ⟨ _, _ ⟩, _ ⟩;
        · exact Multiset.sub_le_self S a;
        · rw [ Multiset.card_sub ha₁, ha₂, tsub_tsub_cancel_of_le hk ];
        · have h_sum_diff : Multiset.sum (S - a) + Multiset.sum a = Multiset.sum S := by
            rw [ ← Multiset.sum_add, tsub_add_cancel_of_le ha₁ ];
          exact eq_sub_of_add_eq h_sum_diff

/-
The set of sums of subsequences of S of length at most k is equal to the set of sums of subsequences of S padded with k-1 zeros of length k.
-/
lemma sigma_le_eq_sigma_pad {G : Type*} [AddCommMonoid G] [DecidableEq G] (S : Multiset G) (k : ℕ)
    (hk : k ≥ 1) :
    seq_sigma_le S k = seq_sigma (Multiset.replicate (k - 1) 0 + S) k := by
      -- Let's prove the forward direction: if $x$ is a sum of a subsequence of $S$ of length at most $k$, then $x$ is also a sum of a subsequence of $S$ of length $k$ padded with zeros.
      apply Finset.ext
      intro x;
      unfold seq_sigma_le seq_sigma;
      induction hk <;> simp_all +decide [ seq_sigma, Finset.mem_biUnion, Finset.mem_image ];
      constructor;
      · rintro ⟨ a, ha, b, hb, hx ⟩;
        rename_i k hk ih;
        rcases ha with ( _ | ha );
        · exact ⟨ b, ⟨ by exact le_trans hb.1 ( Multiset.le_add_left _ _ ), hb.2 ⟩, hx ⟩;
        · refine' ⟨ b + Multiset.replicate ( k - a ) 0, _, _ ⟩ <;> simp_all +decide [ Multiset.le_iff_count ];
          refine' ⟨ fun g => _, by omega ⟩;
          by_cases hg : g = 0 <;> simp_all +decide [ Multiset.count_replicate ];
          · linarith [ hb.1 0, Nat.sub_add_cancel ( by linarith : a ≤ k ) ];
          · aesop;
      · rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, ha₃ ⟩;
        -- Since $a$ is a subsequence of $replicate m✝ 0 + S$, we can split $a$ into the part that comes from $replicate m✝ 0$ and the part that comes from $S$.
        obtain ⟨a_zero, a_S, ha⟩ : ∃ a_zero a_S, a = a_zero + a_S ∧ a_zero ≤ replicate ‹_› 0 ∧ a_S ≤ S := by
          have h_split : ∀ (m : Multiset G) (n : Multiset G), m ≤ n + S → ∃ m_zero m_S, m = m_zero + m_S ∧ m_zero ≤ n ∧ m_S ≤ S := by
            intro m n hmn; induction' n using Multiset.induction_on with n ih generalizing m; aesop;
            by_cases h : n ∈ m;
            · obtain ⟨ m', rfl ⟩ := Multiset.exists_cons_of_mem h;
              simp_all +decide [ Multiset.le_iff_count ];
              rename_i h; specialize h m'; simp_all +decide [ Multiset.count_cons ] ;
              obtain ⟨ m_zero, m_S, rfl, hm_zero, hm_S ⟩ := h; use n ::ₘ m_zero, m_S; aesop;
            · rename_i hmn';
              obtain ⟨ m_zero, m_S, rfl, hm_zero, hm_S ⟩ := hmn' m ( by simpa [ Multiset.le_iff_count ] using fun x => by by_cases hx : x = n <;> simpa [ hx, h ] using Multiset.le_iff_count.mp hmn x ) ; exact ⟨ m_zero, m_S, rfl, hm_zero.trans ( Multiset.le_cons_self _ _ ), hm_S ⟩ ;
          exact h_split a _ ha₁;
        -- Since $a_zero$ is a subsequence of $replicate m✝ 0$, we have $a_zero = replicate (a_zero.card) 0$.
        have ha_zero : a_zero = replicate (a_zero.card) 0 := by
          refine' Multiset.eq_replicate.mpr ⟨ _, _ ⟩;
          · rfl;
          · intro b hb; have := Multiset.mem_of_le ha.2.1 hb; rw [ Multiset.mem_replicate ] at this; aesop;
        refine' ⟨ a_S.card - 1, _, a_S, _, _ ⟩ <;> norm_num [ ha.1 ] at *;
        · omega;
        · rcases a_S with ⟨ ⟨ l ⟩ ⟩ <;> simp +decide [ ha.2 ];
          · rw [ ha_zero ] at ha₂ ; simp +decide at ha₂;
            exact absurd ( Multiset.card_le_card ha.1 ) ( by simp +decide [ ha₂ ] );
          · exact ha.2;
        · rw [ ← ha₃, ha_zero, Multiset.sum_replicate ] ; norm_num

/-
If $r > p/2$ and $0 \notin \Sigma_{\le r-1}(S)$, then $h(S) \ge r$.
-/
lemma lem_max_multiplicity_case1 {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (r : ℕ)
    (hp : S.card = p) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_r_large : p < 2 * r) :
    max_multiplicity S ≥ r := by
      -- Since $0 \notin \Sigma_{\le r-1}(S)$ and $r > 1$, we must have $0 \notin S$.
      have h_zero_not_in_S : 0 ∉ S := by
        contrapose! h_small; simp_all +decide [ seq_sigma_le ] ;
        refine' ⟨ 0, _, _ ⟩ <;> norm_num [ seq_sigma ] ; aesop;
        exact ⟨ { 0 }, by aesop ⟩;
      by_contra h_contra;
      -- Apply `lem_setpartition` with $k=r-1$.
      obtain ⟨A, hA_nonempty, hA_sum, hA_subset, hA_sum_eq⟩ := lem_setpartition (Multiset.replicate (r - 2) 0 + S) (r - 1) (by
      exact Nat.le_sub_one_of_lt hr.1) (by
      rcases r with ( _ | _ | r ) <;> simp_all +decide;
      linarith) (by
      unfold max_multiplicity at *;
      rcases r with ( _ | _ | r ) <;> simp_all +decide [ Finset.max ];
      split_ifs <;> simp_all +decide [ Finset.sup_union ];
      · exact Nat.le_of_lt_succ h_contra;
      · simp_all +decide [ max_def ];
        split_ifs <;> simp_all +decide [ Function.comp, Multiset.count_replicate ];
        · rw [ show ( S.toFinset.sup ( WithBot.some ∘ fun x => ( if 0 = x then r else 0 ) + count x S ) ) = ( S.toFinset.sup ( WithBot.some ∘ fun x => count x S ) ) from ?_ ];
          · exact Nat.le_of_lt_succ h_contra;
          · refine' Finset.sup_congr rfl fun x hx => _ ; aesop;
        · exact Nat.le_succ _);
      -- By `sigma_le_eq_sigma_pad`, $\Sigma_{\le r-1}(S) = \Sigma_{r-1}(U) = \mathbb{Z}/p\mathbb{Z}$.
      have h_sigma_le_eq_univ : seq_sigma_le S (r - 1) = seq_sigma (Multiset.replicate (r - 2) 0 + S) (r - 1) := by
        exact sigma_le_eq_sigma_pad _ _ ( Nat.sub_pos_of_lt hr.1 );
      rcases r with ( _ | _ | r ) <;> simp_all +decide;
      exact h_small <| hA_sum_eq ( by linarith ) ▸ Finset.mem_univ _

/-
The maximal multiplicity of $S$ is at most $k$ if and only if the count of every element in $S$ is at most $k$.
-/
lemma max_multiplicity_le {G : Type*} [DecidableEq G] (S : Multiset G) (k : ℕ) :
    max_multiplicity S ≤ k ↔ ∀ x, S.count x ≤ k := by
      unfold max_multiplicity;
      by_cases h : Finset.image ( fun x => count x S ) ( Multiset.toFinset S ) = ∅ <;> simp_all +decide [ Finset.ext_iff ];
      · rw [ Multiset.eq_zero_of_forall_notMem h ] ; simp +decide;
        exact Nat.zero_le _;
      · constructor <;> intro hk;
        · -- For any element x in G, if x is in S, then count x S is in the image of the count function, so it's ≤ k. If x is not in S, then count x S is 0, which is also ≤ k. Therefore, in all cases, count x S ≤ k.
          intros x
          by_cases hx : x ∈ S;
          · refine' le_trans _ hk;
            have := Finset.le_max ( Finset.mem_image_of_mem ( fun x => count x S ) ( Multiset.mem_toFinset.mpr hx ) );
            cases h : Finset.max ( Finset.image ( fun x => count x S ) S.toFinset ) <;> aesop;
          · simp +decide [ hx ];
        · have := Finset.max_of_nonempty ( Finset.nonempty_of_ne_empty ( by aesop : Finset.image ( fun x => count x S ) S.toFinset ≠ ∅ ) );
          rcases this with ⟨ a, ha ⟩ ; rw [ ha ] ; exact Nat.cast_le.mpr <| by obtain ⟨ x, hx ⟩ := Finset.mem_image.mp ( Finset.mem_of_max ha ) ; aesop;

/-
If the maximal multiplicity of $S$ is at most $k+1$, and $2(k+1) > |S|$, and $x$ has maximal multiplicity, then the maximal multiplicity of $S \setminus \{x\}$ is at most $k$.
-/
lemma max_multiplicity_erase_bound {G : Type*} [DecidableEq G] (S : Multiset G) (k : ℕ)
    (h_mul : max_multiplicity S ≤ k + 1)
    (h_card : 2 * (k + 1) > S.card)
    (x : G) (hx : S.count x = max_multiplicity S) :
    max_multiplicity (S.erase x) ≤ k := by
      have h_erase : ∀ y, Multiset.count y (Multiset.erase S x) ≤ k := by
        intro y; by_cases hy : y = x <;> simp_all +decide [ Multiset.count_erase_of_ne ] ;
        have h_count_y : Multiset.count y S ≤ max_multiplicity S := by
          unfold max_multiplicity;
          by_cases hy_mem : y ∈ S.toFinset;
          · have h_count_y : count y S ∈ Finset.image (fun x => count x S) S.toFinset := by
              exact Finset.mem_image_of_mem _ hy_mem;
            have := Finset.le_max h_count_y;
            cases h : Finset.max ( Finset.image ( fun x => count x S ) S.toFinset ) <;> aesop;
          · simp_all +decide [ Multiset.count_eq_zero.mpr ];
        have h_count_x : Multiset.count x S + Multiset.count y S ≤ S.card := by
          have h_count_x : Multiset.count x S + Multiset.count y S ≤ Multiset.card (Multiset.filter (fun z => z = x) S + Multiset.filter (fun z => z = y) S) := by
            rw [ Multiset.filter_eq', Multiset.filter_eq' ] ; aesop;
          exact h_count_x.trans ( Multiset.card_le_card <| Multiset.le_iff_count.mpr fun z => by by_cases hz : z = x <;> by_cases hz' : z = y <;> aesop );
        grind;
      convert max_multiplicity_le _ _ |>.2 h_erase using 1

/-
The set of sums of subsequences of length $k$ of $S$ padded with $k$ zeros is contained in the set of sums of subsequences of $S$ of length at most $k$ union $\{0\}$.
-/
lemma sigma_k_subset_sigma_le_union_zero {G : Type*} [AddCommMonoid G] [DecidableEq G] (S : Multiset G) (k : ℕ) :
    seq_sigma (Multiset.replicate k 0 + S) k ⊆ seq_sigma_le S k ∪ {0} := by
      intro x;
      unfold seq_sigma seq_sigma_le;
      simp;
      rintro T hT hk rfl;
      -- Since $T$ is a subsequence of $0^k + S$, we can write $T$ as $0^j + T'$ where $T'$ is a subsequence of $S$.
      obtain ⟨j, T', hT_eq⟩ : ∃ j T', T = Multiset.replicate j 0 + T' ∧ T' ≤ S := by
        use Multiset.count 0 T;
        refine' ⟨ T - Multiset.replicate ( Multiset.count 0 T ) 0, _, _ ⟩;
        · ext x;
          by_cases hx : x = 0 <;> simp_all +decide [ Multiset.count_replicate ];
          rw [ if_neg ( Ne.symm hx ), zero_add, Nat.sub_zero ];
        · rw [ Multiset.le_iff_count ] at *;
          intro a; specialize hT a; by_cases ha : a = 0 <;> simp_all ( config := { decide := Bool.true } ) [ Multiset.count_replicate ] ;
          aesop;
      by_cases hj : j = k <;> simp_all ( config := { decide := Bool.true } );
      refine' Or.inr ⟨ T'.card - 1, _, _ ⟩;
      · omega;
      · rcases T' with ⟨ ⟨ _ | _ | T' ⟩ ⟩ <;> simp_all +decide [ Nat.succ_eq_add_one ];
        unfold seq_sigma; aesop;

/-
If the set of sums of subsequences of length at most $|S|-r-1$ union $\{0\}$ is the whole group, then $0$ is a sum of a subsequence of length at least $r+1$.
-/
lemma zero_in_sigma_ge_of_sigma_le_univ {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] (S : Multiset G) (r : ℕ)
    (hr : r + 1 ≤ S.card)
    (h_univ : seq_sigma_le S (S.card - r - 1) ∪ {0} = Finset.univ) :
    0 ∈ seq_sigma_ge S (r + 1) := by
      rw [ Finset.eq_univ_iff_forall ] at h_univ;
      contrapose! h_univ;
      use S.sum;
      simp_all +decide [ seq_sigma_ge, seq_sigma_le ];
      refine' ⟨ _, _ ⟩;
      · exact fun h => h_univ _ ( Nat.lt_succ_self _ ) ( by linarith ) ( by unfold seq_sigma; aesop );
      · intro x hx;
        specialize h_univ ( S.card - ( x + 1 ) );
        rw [ seq_sigma_complement ];
        · simp_all +decide [ Finset.mem_image ];
          exact h_univ ( Nat.lt_succ_of_le ( Nat.sub_le _ _ ) ) ( by omega );
        · omega

/-
If $r \le (p-1)/2$ and $0 \notin \Sigma_{\le r-1}(S)$ and $0 \notin \Sigma_{\ge r+1}(S)$, then $h(S) \ge p-r+1$.
-/
lemma lem_max_multiplicity_case2 {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (r : ℕ)
    (hp : S.card = p) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (h_r_small : 2 * r ≤ p - 1) :
    max_multiplicity S ≥ p - r + 1 := by
      by_contra h_contra;
      -- Since $0 \notin \Sigma_{\le r-1}(S)$ and $r > 1$, we have $0 \notin S$.
      have h_not_zero : 0 ∉ S := by
        intro h; simp_all +decide [ seq_sigma_le ] ;
        exact h_small 0 ( Nat.sub_pos_of_lt hr.1 ) ( by exact Multiset.mem_toFinset.mpr <| Multiset.mem_map.mpr ⟨ { 0 }, Multiset.mem_powersetCard.mpr ⟨ Multiset.singleton_le.mpr h, by norm_num ⟩, by norm_num ⟩ );
      -- Let $x$ be an element with maximal multiplicity in $S$.
      obtain ⟨x, hx⟩ : ∃ x ∈ S, S.count x = max_multiplicity S := by
        -- By definition of `max_multiplicity`, there exists an element `x` in `S` such that `count x S` is maximal.
        obtain ⟨x, hx⟩ : ∃ x ∈ S.toFinset, ∀ y ∈ S.toFinset, S.count y ≤ S.count x := by
          apply_rules [ Finset.exists_max_image ];
          exact ⟨ Classical.choose ( Multiset.card_pos_iff_exists_mem.mp ( by linarith ) ), Multiset.mem_toFinset.mpr ( Classical.choose_spec ( Multiset.card_pos_iff_exists_mem.mp ( by linarith ) ) ) ⟩;
        unfold max_multiplicity;
        rw [ Finset.max_eq_sup_coe ];
        rw [ Finset.sup_image ];
        rw [ show S.toFinset.sup ( WithBot.some ∘ fun x => count x S ) = WithBot.some ( count x S ) from ?_ ] ; aesop;
        exact le_antisymm ( Finset.sup_le fun y hy => WithBot.coe_le_coe.mpr ( hx.2 y hy ) ) ( Finset.le_sup ( f := WithBot.some ∘ fun x => count x S ) hx.1 );
      -- Let $S' = S \setminus \{x\}$.
      set S' : Multiset (ZMod p) := S.erase x;
      -- Let $k = p-r-1$.
      set k : ℕ := p - r - 1;
      -- By `lem_setpartition` applied to $U$ and $k$, since $|U| \ge p+k-1$, we have $\Sigma_k(U) = \mathbb{Z}/p\mathbb{Z}$.
      have h_sigma_k_U : seq_sigma (Multiset.replicate k 0 + S') k = Finset.univ := by
        have h_sigma_k_U : k ≤ (Multiset.replicate k 0 + S').card ∧ max_multiplicity (Multiset.replicate k 0 + S') ≤ k ∧ (Multiset.replicate k 0 + S').card ≥ p + k - 1 := by
          have h_max_mul_S' : max_multiplicity S' ≤ k := by
            apply max_multiplicity_erase_bound;
            · omega;
            · omega;
            · exact hx.2;
          have h_max_mul_U : max_multiplicity (Multiset.replicate k 0 + S') ≤ k := by
            unfold max_multiplicity at *;
            simp_all +decide [ Finset.max ];
            split_ifs <;> simp_all +decide [ Finset.sup_union ];
            erw [ max_eq_left ] <;> norm_cast;
            · simp +decide [ show count 0 S' = 0 from Multiset.count_eq_zero_of_notMem fun h => h_not_zero <| Multiset.mem_of_mem_erase h ];
              rfl;
            · simp_all +decide [ Finset.sup_le_iff ];
              intro b hb; by_cases hb' : b = 0 <;> simp_all +decide [ Multiset.count_replicate ] ;
              refine' le_add_of_le_of_nonneg _ _;
              · refine' WithBot.coe_le_coe.mpr _;
                refine' le_trans _ h_max_mul_S';
                have h_max_mul_S' : ∀ y ∈ S'.toFinset, count y S' ≤ (S'.toFinset.sup (WithBot.some ∘ fun x => count x S')) := by
                  exact fun y hy => Finset.le_sup ( f := WithBot.some ∘ fun x => count x S' ) hy;
                convert h_max_mul_S' b ( Multiset.mem_toFinset.mpr hb ) using 1;
                erw [ WithBot.coe_le_iff ] ; aesop;
              · exact Nat.cast_nonneg _;
          simp +zetaDelta at *;
          exact ⟨ h_max_mul_U, by linarith [ Nat.sub_add_cancel ( show r ≤ p from by linarith ), Nat.sub_add_cancel ( show 1 ≤ p - r from Nat.sub_pos_of_lt ( by linarith ) ), Multiset.card_erase_add_one hx.1 ] ⟩;
        have := lem_setpartition ( Multiset.replicate k 0 + S' ) k ( Nat.pos_of_ne_zero ?_ ) h_sigma_k_U.1 h_sigma_k_U.2.1; aesop;
        omega;
      -- Since $U \subseteq 0^k + S$, we have $\Sigma_k(U) \subseteq \Sigma_k(0^k + S)$.
      have h_sigma_k_U_subset : seq_sigma (Multiset.replicate k 0 + S') k ⊆ seq_sigma (Multiset.replicate k 0 + S) k := by
        simp +decide [ seq_sigma ];
        intro y hy;
        simp +zetaDelta at *;
        obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ := hy; exact ⟨ a, ⟨ le_trans ha₁ ( add_le_add_left ( Multiset.erase_le _ _ ) _ ), ha₂ ⟩, ha₃ ⟩ ;
      -- By `sigma_k_subset_sigma_le_union_zero`, $\Sigma_k(0^k + S) \subseteq \Sigma_{\le k}(S) \cup \{0\}$.
      have h_sigma_k_S_subset : seq_sigma (Multiset.replicate k 0 + S) k ⊆ seq_sigma_le S k ∪ {0} := by
        apply sigma_k_subset_sigma_le_union_zero;
      -- Apply `zero_in_sigma_ge_of_sigma_le_univ` with parameter $r$.
      have h_zero_in_sigma_ge : 0 ∈ seq_sigma_ge S (r + 1) := by
        apply zero_in_sigma_ge_of_sigma_le_univ;
        · omega;
        · aesop;
      contradiction

/-
If $r \le (p-1)/2$ and $0 \notin \Sigma_{\le r-1}(S)$ and $0 \notin \Sigma_{\ge r+1}(S)$, then $h(S) \ge p-r+1$.
-/
lemma lem_max_multiplicity_case2_v2 {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (r : ℕ)
    (hp : S.card = p) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (h_r_small : 2 * r ≤ p - 1) :
    max_multiplicity S ≥ p - r + 1 := by
      apply lem_max_multiplicity_case2 S r hp hr h_small h_large h_r_small

/-
If $S$ is a sequence of length $p$ such that $0$ is not a sum of a subsequence of length $\le r-1$ and $0$ is not a sum of a subsequence of length $\ge r+1$, then the maximal multiplicity of $S$ is at least $\max(r, p-r+1)$.
-/
lemma lem_max_multiplicity {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (r : ℕ)
    (hp : S.card = p) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1)) :
    max_multiplicity S ≥ max r (p - r + 1) := by
      -- Split into two cases: $r > p/2$ and $r \le p/2$.
      by_cases h_case : r > p / 2;
      · have := @lem_max_multiplicity_case1;
        grind;
      · apply le_trans _ ( lem_max_multiplicity_case2_v2 S r hp hr h_small h_large _ );
        · exact max_le ( by omega ) le_rfl;
        · cases Nat.Prime.eq_two_or_odd ( Fact.out : Nat.Prime p ) <;> omega

/-
If $R$ is a nonempty sequence with sum equal to its length, no zero-sum subsequences, and no 1s, then there exists a nonempty subsequence with sum outside $\{0, 1, \dots, |R|\}$.
-/
lemma exists_subsum_outside_interval {p : ℕ} [Fact p.Prime] (R : Multiset (ZMod p))
    (h_nonempty : R ≠ 0)
    (h_sum : R.sum = R.card)
    (h_card_le : R.card ≤ p - 1)
    (h_zs : 0 ∉ seq_sigma_ge R 1)
    (h_not_ones : R.count 1 = 0) :
    ∃ R₀ ≤ R, R₀ ≠ 0 ∧ R₀.sum ∉ (Finset.Ico 0 (R.card + 1)).image (Nat.cast : ℕ → ZMod p) := by
      by_contra! h;
      -- By `lem_interval_subsums`, this implies $R = 1^{|R|}$.
      have h_R_eq_replicate : R = Multiset.replicate R.card 1 := by
        apply_rules [ lem_interval_subsums ];
        intro x hx;
        obtain ⟨ y, hy ⟩ := Finset.mem_image.mp ( show x ∈ Finset.image ( fun m : ℕ => ( m : ZMod p ) ) ( Finset.Ico 0 ( R.card + 1 ) ) from by
                                                    obtain ⟨ s, hs ⟩ := Finset.mem_biUnion.mp hx;
                                                    norm_num +zetaDelta at *;
                                                    rcases hs with ⟨ ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩, hx ⟩ ; unfold seq_sigma at hx; aesop; );
        rcases y with ( _ | y ) <;> simp_all +decide [ Finset.mem_Ico ];
        exact ⟨ y + 1, ⟨ by linarith, by linarith ⟩, by simpa using hy.2 ⟩;
      rw [ h_R_eq_replicate ] at h_not_ones; simp +decide at h_not_ones;
      contradiction

/-
If a subsequence $R_0$ of $T$ (where $S = 1^l T$) has sum $t$ close to $p$, we can add 1s to make a zero sum of length $\le r-1$.
-/
lemma lem_forbidden_upper {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (r s : ℕ)
    (R₀ : Multiset (ZMod p)) (hR₀ : R₀ ≤ S) (hs : R₀.card = s)
    (t : ℕ) (ht_val : (t : ZMod p) = R₀.sum)
    (ht_range : p - (r - s - 1) ≤ t ∧ t ≤ p - 1)
    (hs_small : s ≤ r - 2)
    (h_ones : S.count 1 ≥ r) :
    0 ∈ seq_sigma_le S (r - 1) := by
      -- Let $u = p - t$. From the range of $t$, we have $1 \le u \le r - s - 1$.
      set u := p - t with hu
      have hu_bounds : 1 ≤ u ∧ u ≤ r - s - 1 := by
        rcases p with ( _ | _ | p ) <;> simp_all +decide;
        · exact Nat.not_prime_zero Fact.out;
        · exact absurd ( Fact.out ( p := Nat.Prime 1 ) ) ( by decide );
        · omega;
      -- Since $S$ has at least $r$ ones, we can find $u$ ones in $S$, disjoint from $R₀$.
      obtain ⟨ones_subset, h_ones_subset⟩ : ∃ ones_subset : Multiset (ZMod p), ones_subset ≤ S ∧ ones_subset.card = u ∧ ones_subset.sum = u ∧ ones_subset.count 1 = u ∧ R₀ + ones_subset ≤ S := by
        -- Since $S$ has at least $r$ ones, we can find $u$ ones in $S$, disjoint from $R₀$. Let $ones_subset$ be this multiset of $u$ ones.
        obtain ⟨ones_subset, h_ones_subset⟩ : ∃ ones_subset : Multiset (ZMod p), ones_subset ≤ S ∧ ones_subset.card = u ∧ ones_subset.sum = u ∧ ones_subset.count 1 = u ∧ ones_subset + R₀ ≤ S := by
          have h_count_ones : (S - R₀).count 1 ≥ u := by
            have h_count_one : (S - R₀).count 1 = S.count 1 - R₀.count 1 := by
              rw [ Multiset.count_sub ];
            have h_count_one_R₀ : R₀.count 1 ≤ s := by
              exact hs ▸ Multiset.count_le_card _ _;
            omega
          have h_ones_subset : ∃ ones_subset : Multiset (ZMod p), ones_subset ≤ S - R₀ ∧ ones_subset.card = u ∧ ones_subset.sum = u ∧ ones_subset.count 1 = u := by
            use Multiset.replicate u 1;
            simp_all +decide [ Multiset.le_iff_count ];
            intro a; by_cases ha : a = 1 <;> simp_all +decide [ Multiset.count_replicate ] ;
            rw [ if_neg ( Ne.symm ha ) ] ; exact Nat.zero_le _;
          obtain ⟨ ones_subset, h₁, h₂, h₃, h₄ ⟩ := h_ones_subset; use ones_subset; simp_all +decide [ Multiset.le_iff_count ] ;
          exact ⟨ fun a => le_trans ( h₁ a ) ( Nat.sub_le _ _ ), fun a => by linarith [ h₁ a, Nat.sub_add_cancel ( show count a R₀ ≤ count a S from hR₀ a ) ] ⟩;
        exact ⟨ ones_subset, h_ones_subset.1, h_ones_subset.2.1, h_ones_subset.2.2.1, h_ones_subset.2.2.2.1, by simpa only [ add_comm ] using h_ones_subset.2.2.2.2 ⟩;
      -- Since $R₀ + ones_subset$ is a subsequence of $S$ with sum $0$ and length $s + u \le r - 1$, it follows that $0 \in \Sigma_{\le r-1}(S)$.
      have h_zero_in_sigma : (seq_sigma_le S (r - 1)) ⊇ {R₀.sum + ones_subset.sum} := by
        simp_all +decide [ seq_sigma_le ];
        use s + u - 1;
        exact ⟨ by omega, by rw [ Nat.sub_add_cancel ( by omega ) ] ; exact Multiset.mem_toFinset.mpr ( Multiset.mem_map.mpr ⟨ R₀ + ones_subset, Multiset.mem_powersetCard.mpr ⟨ h_ones_subset.2.2.2.2, by aesop ⟩, by aesop ⟩ ) ⟩;
      simp_all +decide [ ← ht_val ];
      rw [ Nat.cast_sub ( by omega ) ] at h_zero_in_sigma ; aesop

/-
Case 2 of finding h: t is in the middle range.
-/
lemma lem_find_h_case2 {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (R : Multiset (ZMod p)) (hR : R ≤ T)
    (R₀ : Multiset (ZMod p)) (hR₀ : R₀ ≤ R)
    (s : ℕ) (hs : R₀.card = s)
    (t : ℕ) (ht : (t : ZMod p) = R₀.sum)
    (hs_bounds : 1 ≤ s ∧ s ≤ r - 2)
    (hR_card : R.card ≤ r - 1)
    (ht_bounds : R.card + 1 ≤ t ∧ t ≤ p - r + s - 1)
    (ht_case2 : t > l + R.card - r + s) :
    ∃ h ∈ seq_sigma_ge (Multiset.replicate l 1 + R₀) (r + 1),
      h ∉ (Finset.Ico 1 (l + R.card + 1)).image (Nat.cast : ℕ → ZMod p) := by
        refine' ⟨ t + ( r + 1 - s ), _, _ ⟩ <;> norm_num;
        · -- Since $R₀$ is a subsequence of $R$ and $R$ is a subsequence of $T$, we can add $r + 1 - s$ ones to $R₀$ to get a subsequence of length $r + 1$.
          have h_subseq : ∃ U : Multiset (ZMod p), U ≤ replicate l 1 + R₀ ∧ U.card = r + 1 ∧ U.sum = t + (r + 1 - s) := by
            refine' ⟨ Multiset.replicate ( r + 1 - s ) 1 + R₀, _, _, _ ⟩ <;> simp_all +decide [ Multiset.le_iff_count ];
            · intro a; by_cases ha : a = 1 <;> simp_all +decide [ Multiset.count_replicate ] ; omega;
              aesop;
            · omega;
            · rw [ Nat.cast_sub ] <;> push_cast <;> ring_nf ; omega;
          obtain ⟨ U, hU₁, hU₂, hU₃ ⟩ := h_subseq; simp_all +decide [ seq_sigma_ge ] ;
          refine' ⟨ r + 1, ⟨ by omega, by omega ⟩, _ ⟩ ; unfold seq_sigma ; aesop;
        · intros x hx₁ hx₂ hx₃;
          -- Since $x \equiv t + r + 1 - s \pmod{p}$ and $x < l + R.card + 1$, we have $p \mid (t + r + 1 - s - x)$.
          have h_div : p ∣ Int.natAbs (t + r + 1 - s - x) := by
            rw [ ← Int.natCast_dvd_natCast ] ; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
            ring;
          -- Since $p \mid (t + r + 1 - s - x)$ and $0 < t + r + 1 - s - x < p$, we have a contradiction.
          have h_contradiction : 0 < Int.natAbs (t + r + 1 - s - x) ∧ Int.natAbs (t + r + 1 - s - x) < p := by
            omega;
          exact Nat.not_dvd_of_pos_of_lt h_contradiction.1 h_contradiction.2 h_div

/-
Case 1 of finding h: t is small enough.
-/
lemma lem_find_h_case1 {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (R : Multiset (ZMod p)) (hR : R ≤ T)
    (hR_sum : R.sum = R.card)
    (R₀ : Multiset (ZMod p)) (hR₀ : R₀ ≤ R)
    (s : ℕ) (hs : R₀.card = s)
    (t : ℕ) (ht : (t : ZMod p) = R₀.sum)
    (hs_bounds : 1 ≤ s ∧ s ≤ r - 2)
    (hR_card : R.card ≤ r - 1)
    (ht_bounds : R.card + 1 ≤ t)
    (ht_case1 : t ≤ l + R.card - r + s) :
    ∃ h ∈ seq_sigma_ge (Multiset.replicate l 1 + R₀) (r + 1),
      h ∉ (Finset.Ico 1 (l + R.card + 1)).image (Nat.cast : ℕ → ZMod p) := by
        -- Set $k = l + |R| + 1 - t$. Since $t \ge |R| + 1$, $k \le l$.
        set k := l + R.card + 1 - t with hk_def
        have hk_le_l : k ≤ l := by
          omega;
        -- Consider $U = R_0 + 1^k$. $U \le 1^l + R_0$.
        set U : Multiset (ZMod p) := R₀ + Multiset.replicate k 1 with hU_def
        have hU_le : U ≤ Multiset.replicate l 1 + R₀ := by
          rw [ add_comm ];
          exact add_le_add_left ( Multiset.le_iff_count.mpr fun x => by rw [ Multiset.count_replicate, Multiset.count_replicate ] ; aesop ) _;
        have hU_card : U.card = s + k := by
          aesop
        have hU_sum : U.sum = l + R.card + 1 := by
          norm_num +zetaDelta at *;
          rw [ Nat.cast_sub ] <;> push_cast <;> ring_nf;
          · rw [ ← ht ] ; ring;
          · omega;
        -- Since $s + k \ge r + 1$, we have $h \in \Sigma_{\ge r+1}(1^l + R_0)$.
        have hU_ge_r1 : U.sum ∈ seq_sigma_ge (Multiset.replicate l 1 + R₀) (r + 1) := by
          have hU_ge_r1 : U.card ≥ r + 1 := by
            omega;
          apply Finset.mem_biUnion.mpr;
          refine' ⟨ _, Finset.mem_image.mpr ⟨ U.card, _, rfl ⟩, _ ⟩ <;> simp_all +decide [ Finset.mem_filter, Finset.mem_range ];
          · omega;
          · convert Finset.mem_coe.mpr ( Multiset.mem_toFinset.mpr <| Multiset.mem_map.mpr ⟨ U, ?_, ?_ ⟩ ) <;> aesop;
        -- Since $l + |R| < p$, we have $l + |R| + 1 \le p$.
        have hU_lt_p : l + R.card + 1 ≤ p := by
          have h_l_R_lt_p : l + T.card = p := by
            aesop;
          have h_l_R_lt_p : R.card < T.card := by
            by_cases hR_eq_T : R = T;
            · simp_all ( config := { decide := Bool.true } ) [ seq_sigma_ge ];
              contrapose! h_large;
              refine' ⟨ p, _, _, _ ⟩ <;> norm_num [ h_l_R_lt_p ];
              · linarith;
              · simp_all ( config := { decide := Bool.true } ) [ seq_sigma ];
                refine' ⟨ replicate l 1 + T, _, _ ⟩ <;> norm_num [ h_l_R_lt_p ];
                rw [ hR_sum ] ; norm_cast ; aesop;
            · exact lt_of_le_of_ne ( Multiset.card_le_card hR ) fun h => hR_eq_T <| Multiset.eq_of_le_of_card_le hR <| by linarith;
          linarith;
        refine' ⟨ _, hU_ge_r1, _ ⟩;
        by_cases h : l + R.card + 1 = p <;> simp_all +decide [ Nat.mod_eq_of_lt ];
        · intro x hx₁ hx₂; norm_cast;
          rw [ ZMod.eq_iff_modEq_nat ] ; norm_num [ Nat.modEq_iff_dvd, h ];
          exact_mod_cast Nat.not_dvd_of_pos_of_lt hx₁ hx₂;
        · intro x hx₁ hx₂; norm_cast;
          rw [ ZMod.eq_iff_modEq_nat ];
          rw [ Nat.ModEq, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] <;> omega

/-
If $0 \notin \Sigma_{\le r-1}(S)$, then the sum $t$ of a subsequence $R_0$ cannot be too close to $p$.
-/
lemma lem_t_upper_bound {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (r s : ℕ)
    (R₀ : Multiset (ZMod p)) (hR₀ : R₀ ≤ S) (hs : R₀.card = s)
    (t : ℕ) (ht_val : (t : ZMod p) = R₀.sum)
    (ht_range : 1 ≤ t ∧ t ≤ p - 1)
    (hs_small : s ≤ r - 2)
    (h_ones : S.count 1 ≥ r)
    (h_small : 0 ∉ seq_sigma_le S (r - 1)) :
    t ≤ p - r + s := by
      contrapose! h_small;
      apply lem_forbidden_upper S r s R₀ hR₀ hs t ht_val ⟨by omega, by omega⟩ hs_small h_ones

/-
The sum of lengths $l + |R|$ is strictly less than $p$.
-/
lemma lem_l_plus_R_lt_p {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : r < p)
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (R : Multiset (ZMod p)) (hR : R ≤ T)
    (hR_sum : R.sum = R.card) :
    l + R.card < p := by
      contrapose! h_large;
      -- Since $l + R.card \geq p$, we have $|R| = |T|$.
      have hR_card_eq_T_card : R.card = T.card := by
        linarith [ Multiset.card_le_card hR, show Multiset.card S = l + Multiset.card T from by rw [ hS, Multiset.card_add, Multiset.card_replicate ] ];
      have hR_eq_T : R = T := by
        exact Multiset.eq_of_le_of_card_le hR hR_card_eq_T_card.ge;
      have h_sigma_S_zero : S.sum = 0 := by
        replace hp := congr_arg ( fun x : ℕ => ( x : ZMod p ) ) hp ; aesop;
      -- Since $S.sum = 0$, we have $0 \in \Sigma_{\ge r+1}(S)$.
      have h_zero_in_sigma_ge : S.sum ∈ seq_sigma S (S.card) := by
        unfold seq_sigma; aesop;
      unfold seq_sigma_ge; aesop;

/-
There exists a subsequence $R_0$ of $R$ with sum $t$ such that $t$ is in the allowed range.
-/
lemma lem_find_R0_and_t {p : ℕ} [Fact p.Prime] (h_odd : p ≠ 2)
    (l : ℕ) (T : Multiset (ZMod p))
    (S : Multiset (ZMod p)) (h_S_def : S = Multiset.replicate l 1 + T)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (hl : l ≥ r)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_one_not_in_T : 1 ∉ T)
    (R : Multiset (ZMod p)) (h_R_sub : R ≤ T)
    (h_R_sum : R.sum = R.card)
    (h_R_card : R.card ≤ r - 1)
    (h_R_nonempty : R ≠ 0) :
    ∃ R₀ ≤ R, ∃ s t : ℕ,
      R₀.card = s ∧ (t : ZMod p) = R₀.sum ∧
      1 ≤ s ∧ s ≤ r - 2 ∧
      R.card + 1 ≤ t ∧ t ≤ p - r + s := by
        obtain ⟨R₀, hR₀⟩ : ∃ R₀ ≤ R, R₀ ≠ 0 ∧ R₀.sum ∉ (Finset.Ico 0 (R.card + 1)).image (Nat.cast : ℕ → ZMod p) := by
          apply exists_subsum_outside_interval R h_R_nonempty h_R_sum;
          · omega;
          · intro h_zero_in_R
            obtain ⟨U, hU_sub, hU_sum⟩ : ∃ U : Multiset (ZMod p), U ≤ R ∧ U.sum = 0 ∧ U.card ≥ 1 := by
              unfold seq_sigma_ge at h_zero_in_R;
              unfold seq_sigma at h_zero_in_R; aesop;
            have hU_le_S : U ≤ S := by
              exact le_trans hU_sub ( h_R_sub.trans ( h_S_def.symm ▸ Multiset.le_add_left _ _ ) );
            have hU_in_S_le : U.sum ∈ seq_sigma_le S (r - 1) := by
              have hU_in_S_le : U.card ≥ 1 ∧ U.card ≤ r - 1 := by
                exact ⟨ hU_sum.2, le_trans ( Multiset.card_le_card hU_sub ) h_R_card ⟩;
              have hU_in_S_le : U.sum ∈ seq_sigma S U.card := by
                unfold seq_sigma; aesop;
              exact Finset.mem_biUnion.mpr ⟨ _, Finset.mem_image.mpr ⟨ U.card - 1, Finset.mem_range.mpr ( by omega ), rfl ⟩, by simpa [ Nat.sub_add_cancel hU_sum.2 ] using hU_in_S_le ⟩;
            aesop;
          · exact Multiset.count_eq_zero_of_notMem fun h => h_one_not_in_T <| Multiset.mem_of_le h_R_sub h;
        -- Since $R₀$ is a nonempty subsequence of $R$, we have $1 \leq R₀.card$.
        have h_card_R₀ : 1 ≤ R₀.card := by
          exact Nat.pos_of_ne_zero ( by aesop );
        have h_card_R₀_le : R₀.card ≤ R.card := by
          exact Multiset.card_le_card hR₀.1
        have h_card_R₀_le_r_minus_2 : R₀.card ≤ r - 2 := by
          by_contra h_contra;
          -- Since $R₀$ is a nonempty subsequence of $R$, we have $R₀ = R$.
          have h_R₀_eq_R : R₀ = R := by
            exact Multiset.eq_of_le_of_card_le hR₀.1 ( by omega );
          simp_all +decide [ Finset.mem_image ];
          exact hR₀ _ ( Nat.lt_succ_self _ ) rfl
        have h_sum_R₀_ge : R.card + 1 ≤ R₀.sum.val := by
          contrapose! hR₀; aesop;
        have h_sum_R₀_le : R₀.sum.val ≤ p - r + R₀.card := by
          apply lem_t_upper_bound S r R₀.card;
          exact le_trans hR₀.1 ( le_trans h_R_sub ( by simp +decide [ h_S_def ] ) );
          any_goals omega;
          · exact ZMod.natCast_zmod_val _;
          · exact ⟨ by linarith [ show R.card ≥ 0 from Nat.zero_le _ ], Nat.le_sub_one_of_lt <| ZMod.val_lt _ ⟩;
          · rw [ h_S_def, Multiset.count_add ] ; aesop
        aesop

/-
Lemma (find-h-good-case)
If there exists a subsequence $R_0 \subseteq R$ with sum $t$ such that $|R|+1 \le t \le p-r+|R_0|-1$, then there exists $h \in \Sigma_{\ge r+1}(1^l R)$ outside the interval $\{1, \dots, l+|R|\}$.
-/
lemma lem_find_h_good_case {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (R : Multiset (ZMod p)) (hR : R ≤ T)
    (hR_sum : R.sum = R.card)
    (R₀ : Multiset (ZMod p)) (hR₀ : R₀ ≤ R)
    (s : ℕ) (hs : R₀.card = s)
    (t : ℕ) (ht : (t : ZMod p) = R₀.sum)
    (hs_bounds : 1 ≤ s ∧ s ≤ r - 2)
    (hR_card : R.card ≤ r - 1)
    (ht_bounds : R.card + 1 ≤ t ∧ t ≤ p - r + s - 1) :
    ∃ h ∈ seq_sigma_ge (Multiset.replicate l 1 + R) (r + 1),
      h ∉ (Finset.Ico 1 (l + R.card + 1)).image (Nat.cast : ℕ → ZMod p) := by
        by_cases ht_case : t > l + R.card - r + s;
        · obtain ⟨h, hh₁, hh₂⟩ := lem_find_h_case2 S l T hS r hr h_large hl R hR R₀ hR₀ s hs t ht hs_bounds hR_card ht_bounds ht_case;
          refine' ⟨ h, _, _ ⟩;
          · unfold seq_sigma_ge at *;
            simp_all +decide [ seq_sigma ];
            obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, b, ⟨ hb₁, hb₂ ⟩, rfl ⟩ := hh₁;
            refine' ⟨ a, ⟨ by linarith [ show s ≤ R.card from hs ▸ Multiset.card_le_card hR₀ ], ha₂ ⟩, b, ⟨ hb₁.trans ( add_le_add_left hR₀ _ ), hb₂ ⟩, rfl ⟩;
          · exact hh₂;
        · have := @lem_find_h_case1 p _ S l T hS hp r hr h_large hl R hR hR_sum R₀ hR₀ s hs t ht hs_bounds hR_card ht_bounds.1 ( le_of_not_gt ht_case );
          obtain ⟨ h, hh₁, hh₂ ⟩ := this; use h; simp_all +decide [ seq_sigma_ge ] ;
          obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ := hh₁; use a; refine' ⟨ ⟨ _, _ ⟩, _ ⟩ <;> try linarith;
          · linarith [ show R.card ≥ s by simpa [ hs ] using Multiset.card_le_card hR₀ ];
          · rw [seq_sigma] at *;
            simp +zetaDelta at *;
            exact ⟨ ha₃.choose, ⟨ le_trans ha₃.choose_spec.1.1 ( add_le_add_left hR₀ _ ), ha₃.choose_spec.1.2 ⟩, ha₃.choose_spec.2 ⟩

/-
Lemma (find-h-bad-case-aux)
If $2r \le p-1$, then $R_1 = R \setminus R_0$ satisfies the conditions for the good case.
-/
lemma lem_find_h_bad_case_aux {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (hl : l ≥ r)
    (R : Multiset (ZMod p)) (hR : R ≤ T)
    (hR_sum : R.sum = R.card)
    (R₀ : Multiset (ZMod p)) (hR₀ : R₀ ≤ R)
    (s : ℕ) (hs : R₀.card = s)
    (t : ℕ) (ht : (t : ZMod p) = R₀.sum)
    (hs_bounds : 1 ≤ s ∧ s ≤ r - 2)
    (hR_card : R.card ≤ r - 1)
    (ht_val : t = p - r + s)
    (h2r : 2 * r ≤ p - 1) :
    let R₁ := R - R₀
    let s₁ := R₁.card
    let t₁ := s₁ + r
    1 ≤ s₁ ∧ s₁ ≤ r - 2 ∧
    (t₁ : ZMod p) = R₁.sum ∧
    R.card + 1 ≤ t₁ ∧ t₁ ≤ p - r + s₁ - 1 := by
      refine' ⟨ _, _, _, _, _ ⟩;
      · simp_all +decide [ Multiset.le_iff_exists_add ];
        rcases hR₀ with ⟨ u, rfl ⟩ ; simp +arith +decide [ hs ];
        rcases u with ⟨ ⟨ _ | _ | u ⟩ ⟩ <;> simp_all +decide;
        exact absurd ht ( by rw [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( Nat.sub_pos_of_lt hr.2 ) ( by omega ) );
      · have h_card_sub : Multiset.card (R - R₀) = Multiset.card R - Multiset.card R₀ := by
          rw [ Multiset.card_sub hR₀ ];
        omega;
      · rw [ Multiset.card_sub hR₀ ];
        have hR₁_sum : (R - R₀).sum = R.sum - R₀.sum := by
          exact eq_sub_of_add_eq <| by rw [ ← Multiset.sum_add, tsub_add_cancel_of_le hR₀ ] ;
        simp_all +decide [ Nat.cast_sub ( show s ≤ R.card from hs.symm ▸ le_trans ( by omega ) ( Multiset.card_le_card hR₀ ) ) ];
        rw [ ← ht ] ; rw [ Nat.cast_sub ( by linarith [ Nat.sub_add_cancel hr.2.le ] ) ] ; ring_nf;
        simp +decide [ sub_eq_add_neg ];
      · have := Multiset.card_le_card hR₀; simp_all +decide ; omega;
      · omega

/-
Property that every nonempty zero-sum subsequence of S has length r.
-/
def has_unique_zero_sum_len {G : Type*} [AddCommMonoid G] (S : Multiset G) (r : ℕ) : Prop :=
  ∀ T ≤ S, T ≠ 0 → T.sum = 0 → T.card = r

/-
Case r=1: If every nonempty zero-sum subsequence has length 1, then S has at most 2 distinct values.
-/
lemma thm_main_case_r_eq_1 {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p))
    (hp : S.card = p)
    (h_property : has_unique_zero_sum_len S 1) :
    S.toFinset.card ≤ 2 := by
      -- Since $r=1$, the only nonempty zero-sum subsequence of $S$ is $0$, which must occur exactly once in $S$.
      have h_zero_occurrence : S.count 0 = 1 := by
        -- Since $0$ is a nonempty zero-sum subsequence of $S$, by $h_property$, its length must be $1$.
        have h_zero_subseq : ∃ T ≤ S, T ≠ 0 ∧ T.sum = 0 ∧ T.card = 1 := by
          have h_zero_in_S : ∃ T ≤ S, T ≠ 0 ∧ T.sum = 0 := by
            by_contra h_no_zero_sum_subseq;
            -- By the pigeonhole principle, there exist indices $i < j$ such that the sums $s_i$ and $s_j$ are equal.
            obtain ⟨i, j, hij, hsum⟩ : ∃ i j : ℕ, i < j ∧ i ≤ p ∧ j ≤ p ∧ (Multiset.sum (Multiset.ofList (List.take i (Multiset.toList S)))) = (Multiset.sum (Multiset.ofList (List.take j (Multiset.toList S)))) := by
              have h_pigeonhole : Finset.card (Finset.image (fun i => (Multiset.sum (Multiset.ofList (List.take i (Multiset.toList S))))) (Finset.range (p + 1))) ≤ p := by
                exact le_trans ( Finset.card_le_univ _ ) ( by norm_num );
              by_cases h_eq : ∀ i j : ℕ, i < j → i ≤ p → j ≤ p → (Multiset.sum (Multiset.ofList (List.take i (Multiset.toList S)))) ≠ (Multiset.sum (Multiset.ofList (List.take j (Multiset.toList S))));
              · exact absurd h_pigeonhole ( by rw [ Finset.card_image_of_injOn fun i hi j hj hij => le_antisymm ( not_lt.mp fun hi' => h_eq _ _ hi' ( Finset.mem_range_succ_iff.mp hj ) ( Finset.mem_range_succ_iff.mp hi ) hij.symm ) ( not_lt.mp fun hj' => h_eq _ _ hj' ( Finset.mem_range_succ_iff.mp hi ) ( Finset.mem_range_succ_iff.mp hj ) hij ) ] ; simp +arith +decide );
              · aesop;
            refine' h_no_zero_sum_subseq ⟨ Multiset.ofList ( List.drop i ( List.take j ( Multiset.toList S ) ) ), _, _, _ ⟩ <;> simp_all +decide [ List.take_drop ];
            · have h_subseq : Multiset.ofList (List.drop i (List.take j S.toList)) ≤ Multiset.ofList (List.take j S.toList) := by
                exact List.drop_sublist _ _ |> List.Sublist.subperm;
              exact le_trans h_subseq ( by simpa [ hp ] using Multiset.le_iff_exists_add.mpr ⟨ Multiset.ofList ( List.drop j S.toList ), by simp +decide [ ← hp ] ⟩ );
            · have h_sum_eq : (List.take j S.toList).sum = (List.take i S.toList).sum + (List.drop i (List.take j S.toList)).sum := by
                rw [ ← List.sum_take_add_sum_drop _ i ];
                grind;
              aesop;
          obtain ⟨ T, hT₁, hT₂, hT₃ ⟩ := h_zero_in_S; specialize h_property T hT₁ hT₂ hT₃; aesop;
        -- Since every nonempty zero-sum subsequence of S has length 1, S can't have any other zero-sum subsequences longer than 1. Therefore, S can't have more than one 0.
        have h_no_other_zeros : ∀ x ∈ S, x = 0 → Multiset.count x S = 1 := by
          intro x hx hx'; specialize h_property ( Multiset.replicate 2 x ) ; simp_all +decide ;
          exact le_antisymm ( Nat.le_of_not_lt fun h => h_property <| Multiset.le_iff_count.mpr fun y => by by_cases hy : y = 0 <;> aesop ) ( Multiset.count_pos.mpr hx );
        obtain ⟨ T, hT₁, hT₂, hT₃, hT₄ ⟩ := h_zero_subseq; rw [ Multiset.card_eq_one ] at hT₄; aesop;
      -- The subsequence $S0^{-1}$ has length $p-1$ and has no nonempty zero-sum subsequence, so by Lemma~\ref{lem:zsfree-p-1} it is constant.
      have h_S0_inv_constant : (S - {0}).toFinset.card = 1 := by
        -- Apply Lemma `lem_zsfree_p_1` to the multiset $S - {0}$.
        have h_S0_inv_zsfree : 0 ∉ seq_sigma_ge (S - {0}) 1 := by
          intro h_zero_subseq
          obtain ⟨T, hT_subseq, hT_zero⟩ : ∃ T ≤ S - {0}, T ≠ 0 ∧ T.sum = 0 := by
            unfold seq_sigma_ge at h_zero_subseq;
            unfold seq_sigma at h_zero_subseq; aesop;
          have := h_property T ?_ hT_zero.1 hT_zero.2 <;> simp_all +decide [ Multiset.le_iff_count ];
          · obtain ⟨ x, hx ⟩ := Multiset.card_eq_one.mp this; specialize hT_subseq x; simp_all +decide ;
          · exact fun a => le_trans ( hT_subseq a ) ( Multiset.count_le_of_le _ ( Multiset.erase_le _ _ ) );
        apply lem_zsfree_p_1;
        · rw [ Multiset.card_sub ] ; aesop;
          exact Multiset.le_iff_count.mpr fun x => by by_cases hx : x = 0 <;> aesop;
        · assumption;
      -- Since $S$ is the union of $\{0\}$ and $S0^{-1}$, and $S0^{-1}$ has exactly one element, the total number of distinct elements in $S$ is at most $1 + 1 = 2$.
      have h_union : S.toFinset = {0} ∪ (S - {0}).toFinset := by
        ext x; by_cases hx : x = 0 <;> simp_all +decide [ Finset.ext_iff ] ;
        · exact Multiset.count_pos.mp ( by linarith );
        · rw [ Multiset.mem_erase_of_ne hx ];
      grind

/-
Case r=p: If every nonempty zero-sum subsequence has length p, then S has at most 2 distinct values.
-/
lemma thm_main_case_r_eq_p {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p))
    (hp : S.card = p)
    (h_property : has_unique_zero_sum_len S p) :
    S.toFinset.card ≤ 2 := by
      -- By contradiction, assume $S$ has more than two distinct values.
      by_contra h_contra;
      -- Then there exist distinct elements $a, b, c \in S$.
      obtain ⟨a, ha⟩ : ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
        obtain ⟨ a, ha, b, hb, hab ⟩ := Finset.two_lt_card.mp ( by linarith ) ; use a, by aesop, b, by aesop; ; aesop;
      -- Let $R = S \setminus \{a\}$. Then $|R| = p - 1$ and $R$ is zero-sum free.
      set R := S - {a} with hR
      have hR_card : R.card = p - 1 := by
        aesop
      have hR_zsfree : 0 ∉ seq_sigma_ge R 1 := by
        intro h_zero_sum
        obtain ⟨T, hT_sub, hT_zero⟩ : ∃ T ≤ R, T ≠ 0 ∧ T.sum = 0 := by
          simp_all ( config := { decide := Bool.true } ) [ seq_sigma_ge ];
          obtain ⟨ k, ⟨ hk₁, hk₂ ⟩, hk₃ ⟩ := h_zero_sum; unfold seq_sigma at hk₃; aesop;
        have := h_property T ?_ hT_zero.1 hT_zero.2 <;> simp_all ( config := { decide := Bool.true } );
        · have := Multiset.card_le_card hT_sub; simp_all ( config := { decide := Bool.true } ) ;
          exact Nat.not_le_of_gt ( Nat.pred_lt ( ne_bot_of_gt ( Fact.out ( p := p.Prime ) |> Nat.Prime.pos ) ) ) this;
        · exact le_trans hT_sub ( Multiset.erase_le _ _ );
      -- By Lemma lem_zsfree_p_1, $|\supp(R)|=1$.
      have hR_supp : R.toFinset.card = 1 := by
        apply_rules [ lem_zsfree_p_1 ];
      -- Since $R$ has only one distinct element, $S$ can have at most two distinct elements.
      have hS_supp : S.toFinset ⊆ {a} ∪ R.toFinset := by
        simp_all +decide [ Finset.subset_iff ];
        exact fun x hx => Classical.or_iff_not_imp_left.2 fun hx' => Multiset.mem_erase_of_ne hx' |>.2 hx;
      exact h_contra <| le_trans ( Finset.card_le_card hS_supp ) <| by rw [ Finset.card_union ] ; aesop;

/-
If $t = p - r + s$ and $t \ge |R| + 1$, then $\sigma(R_1) = |R_1| + r$ and $|R_1| + r < p$.
-/
lemma lem_R1_sum_properties {p : ℕ} [Fact p.Prime] (R R₀ : Multiset (ZMod p))
    (r : ℕ)
    (s : ℕ) (hs : R₀.card = s)
    (t : ℕ) (ht : (t : ZMod p) = R₀.sum)
    (hR₀ : R₀ ≤ R)
    (hR_sum : R.sum = R.card)
    (ht_val : t = p - r + s)
    (ht_lower : R.card + 1 ≤ t)
    (h_r_bound : r < p)
    (h_s_bound : s ≤ R.card) :
    let R₁ := R - R₀
    (R₁.sum : ZMod p) = (R₁.card + r : ℕ) ∧ R₁.card + r < p := by
      have h_sigma_R1 : let R₁ := R - R₀; R₁.sum = (R.card : ZMod p) - (t : ZMod p) := by
        have h_sigma_R1 : let R₁ := R - R₀; R₁.sum = R.sum - R₀.sum := by
          exact eq_sub_of_add_eq <| by rw [ ← Multiset.sum_add, tsub_add_cancel_of_le hR₀ ] ;
        aesop;
      simp_all +decide [ Nat.sub_add_comm h_r_bound.le ];
      rw [ Nat.cast_sub ] at * <;> try linarith;
      rw [ ← ht ] ; ring_nf;
      exact ⟨ by rw [ sub_add_eq_add_sub, eq_comm ] ; norm_num [ ← ZMod.natCast_eq_zero_iff ], by omega ⟩

/-
If $t = p - r + s$ and $2r > p$, then we derive a contradiction using `lem_R1_sum_properties`.
-/
lemma lem_bad_case_impossible_if_large_r {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (hl : l ≥ r)
    (R : Multiset (ZMod p)) (hR : R ≤ T)
    (hR_sum : R.sum = R.card)
    (R₀ : Multiset (ZMod p)) (hR₀ : R₀ ≤ R)
    (s : ℕ) (hs : R₀.card = s)
    (t : ℕ) (ht : (t : ZMod p) = R₀.sum)
    (hs_bounds : 1 ≤ s ∧ s ≤ r - 2)
    (hR_card : R.card ≤ r - 1)
    (ht_val : t = p - r + s)
    (ht_lower : R.card + 1 ≤ t)
    (h2r : 2 * r > p) :
    False := by
      -- Form the subsequence $W = R_1 \cup \{1\}^u$.
      obtain ⟨W, hW⟩ : ∃ W : Multiset (ZMod p), W ≤ S ∧ W ≠ 0 ∧ W.sum = 0 ∧ W.card ≤ r - 1 := by
        refine' ⟨ R - R₀ + Multiset.replicate ( p - r - ( R.card - R₀.card ) ) 1, _, _, _, _ ⟩ <;> simp_all +decide [ Nat.sub_sub ];
        · simp_all ( config := { decide := Bool.true } ) [ Multiset.le_iff_exists_add ];
          rcases hR with ⟨ u, rfl ⟩ ; rcases hR₀ with ⟨ v, rfl ⟩ ; simp_all ( config := { decide := Bool.true } ) [ add_assoc, add_comm, add_left_comm, add_assoc ] ;
          refine' ⟨ R₀ + replicate ( l - ( p - ( r + v.card ) ) ) 1 + u, _ ⟩ ; ext x ; simp ( config := { decide := Bool.true } ) [ add_comm, add_left_comm, add_assoc, Multiset.count_replicate ];
          split_ifs <;> omega;
        · intro h; simp_all +decide [ Multiset.eq_zero_iff_forall_not_mem ] ;
          exact ⟨ 1, Multiset.mem_replicate.mpr ⟨ by omega, by norm_num ⟩ ⟩;
        · have h_sum_R1 : (R - R₀).sum = (R.card - s + r : ℕ) := by
            have h_sum_R1 : (R - R₀).sum = (R.card - s + r : ℕ) := by
              have h_sum_R1_eq : (R - R₀).sum = (R.sum - R₀.sum : ZMod p) := by
                rw [ eq_sub_iff_add_eq', ← Multiset.sum_add ];
                rw [ add_tsub_cancel_of_le hR₀ ]
              simp_all +decide [ Nat.cast_sub ( show s ≤ R.card from by linarith [ Multiset.card_le_card hR₀ ] ) ];
              rw [ ← ht ] ; simp +decide [ Nat.cast_sub ( show r ≤ p from by linarith ) ] ; ring;
            exact h_sum_R1;
          rw [ h_sum_R1 ] ; norm_cast ; simp +decide [ Nat.cast_sub ( show r + ( R.card - s ) ≤ p from by omega ) ] ; ring;
        · omega;
      contrapose! h_small;
      refine' Finset.mem_biUnion.mpr ⟨ _, _, _ ⟩;
      exact seq_sigma S W.card;
      · rcases k : W.card with ( _ | k ) <;> aesop;
      · unfold seq_sigma; aesop;

/-
Reduction step for the bad case when $2r \le p - 1$.
-/
lemma lem_bad_case_reduction {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (hl : l ≥ r)
    (R : Multiset (ZMod p)) (hR : R ≤ T)
    (hR_sum : R.sum = R.card)
    (R₀ : Multiset (ZMod p)) (hR₀ : R₀ ≤ R)
    (s : ℕ) (hs : R₀.card = s)
    (t : ℕ) (ht : (t : ZMod p) = R₀.sum)
    (hs_bounds : 1 ≤ s ∧ s ≤ r - 2)
    (hR_card : R.card ≤ r - 1)
    (ht_val : t = p - r + s)
    (ht_lower : R.card + 1 ≤ t)
    (h2r : 2 * r ≤ p - 1) :
    let R₁ := R - R₀
    let s₁ := R₁.card
    let t₁ := s₁ + r
    1 ≤ s₁ ∧ s₁ ≤ r - 2 ∧
    (t₁ : ZMod p) = R₁.sum ∧
    R.card + 1 ≤ t₁ ∧ t₁ ≤ p - r + s₁ - 1 := by
      have := lem_find_h_bad_case_aux S l T hS r hr h_small hl R hR hR_sum R₀ hR₀ s hs t ht hs_bounds hR_card ht_val h2r; aesop;

/-
Bound on the size of T.
-/
lemma lem_T_card_bound {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (h_one_not_in_T : 1 ∉ T) :
    T.card ≤ r - 1 := by
      -- By Lemma \ref{lem:max_multiplicity}, $h(S) \ge \max(r, p-r+1)$.
      have h_multiplicity : max_multiplicity S ≥ Nat.max r (p - r + 1) := by
        apply lem_max_multiplicity S r hp hr h_small h_large;
      -- Since $S = 1^l T$ and $1 \notin T$, the multiplicity of $1$ is $l$. For any $x \in T$, its multiplicity in $S$ is its multiplicity in $T$, which is $\le |T| = p - l$.
      have h_multiplicity_le : max_multiplicity S ≤ max l (p - l) := by
        rw [ max_multiplicity_le ];
        intro x; by_cases hx : x = 1 <;> simp_all +decide [ Multiset.count_replicate ] ;
        split_ifs <;> simp_all +decide [ eq_comm ];
        exact Or.inr ( Multiset.count_le_card _ _ );
      have := hp; simp_all +decide [ add_comm, add_left_comm, add_assoc ] ; omega;

/-
Main lemma to find h.
-/
lemma lem_find_h {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (h_one_not_in_T : 1 ∉ T)
    (R : Multiset (ZMod p)) (hR : R ≤ T)
    (hR_sum : R.sum = R.card)
    (hR_nonempty : R ≠ 0) :
    ∃ h ∈ seq_sigma_ge (Multiset.replicate l 1 + R) (r + 1),
      h ∉ (Finset.Ico 1 (l + R.card + 1)).image (Nat.cast : ℕ → ZMod p) := by
        obtain ⟨ R₀, hR₀, s, t, hs, ht, hs_bounds, hR_card, ht_bounds ⟩ : ∃ R₀ ≤ R, ∃ s t : ℕ, R₀.card = s ∧ (t : ZMod p) = R₀.sum ∧ 1 ≤ s ∧ s ≤ r - 2 ∧ R.card + 1 ≤ t ∧ t ≤ p - r + s := by
          apply_rules [ lem_find_R0_and_t ];
          · linarith;
          · exact le_trans ( Multiset.card_le_card hR ) ( by linarith [ hS, hp, lem_T_card_bound S l T hS hp r hr h_small h_large hl h_one_not_in_T ] );
        by_cases ht_eq : t = p - r + s;
        · by_cases h2r : 2 * r ≤ p - 1;
          · -- Apply `lem_find_h_good_case` with $R_0 = R_1$.
            obtain ⟨R₁, hR₁⟩ : ∃ R₁ ≤ R, let s₁ := R₁.card; let t₁ := s₁ + r; 1 ≤ s₁ ∧ s₁ ≤ r - 2 ∧ (t₁ : ZMod p) = R₁.sum ∧ R.card + 1 ≤ t₁ ∧ t₁ ≤ p - r + s₁ - 1 := by
              have hR₁ : let R₁ := R - R₀; let s₁ := R₁.card; let t₁ := s₁ + r; 1 ≤ s₁ ∧ s₁ ≤ r - 2 ∧ (t₁ : ZMod p) = R₁.sum ∧ R.card + 1 ≤ t₁ ∧ t₁ ≤ p - r + s₁ - 1 := by
                apply_rules [ lem_bad_case_reduction ];
                · exact ⟨ hs_bounds, hR_card ⟩;
                · have hR_card_bound : T.card ≤ r - 1 := by
                    apply_rules [ lem_T_card_bound ];
                  exact le_trans ( Multiset.card_le_card hR ) hR_card_bound;
                · linarith;
              use R - R₀;
              aesop;
            have := lem_find_h_good_case S l T hS hp r hr h_large hl R hR hR_sum R₁ hR₁.1;
            apply this R₁.card rfl (R₁.card + r);
            · aesop;
            · exact ⟨ hR₁.2.1, hR₁.2.2.1 ⟩;
            · exact le_trans ( Multiset.card_le_card hR ) ( by linarith [ show T.card ≤ r - 1 from by
                                                                            apply lem_T_card_bound S l T hS hp r hr h_small h_large hl h_one_not_in_T ] );
            · grind +ring;
          · contrapose! h2r;
            have := @lem_bad_case_impossible_if_large_r p;
            norm_num +zetaDelta at *;
            specialize this S l T hS r hr.1 hr.2 h_small hl R hR hR_sum R₀ hR₀ t ht (by linarith) (by linarith) (by
            linarith [ show R.card ≤ T.card from Multiset.card_le_card hR, show T.card ≤ r - 1 from by
                                                                            apply lem_T_card_bound S l T hS hp r hr h_small h_large hl h_one_not_in_T ]) (by
            linarith) (by
            linarith);
            exact Nat.le_sub_one_of_lt ( lt_of_le_of_ne this ( by rintro h; have := Nat.Prime.eq_two_or_odd ( Fact.out : Nat.Prime p ) ; omega ) );
        · apply_rules [ lem_find_h_good_case ];
          · tauto;
          · have hT_card : T.card ≤ r - 1 := by
              apply_rules [ lem_T_card_bound ];
            exact le_trans ( Multiset.card_le_card hR ) hT_card;
          · exact ⟨ ht_bounds.1, Nat.le_sub_one_of_lt ( lt_of_le_of_ne ht_bounds.2 ht_eq ) ⟩

/-
If 0 is not a sum of a subsequence of length <= r-1 and not a sum of a subsequence of length >= r+1, then any zero-sum subsequence must have length r.
-/
lemma zero_sum_len_must_be_r {G : Type*} [AddCommMonoid G] [DecidableEq G] (S : Multiset G) (r : ℕ)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (T : Multiset G) (hT : T ≤ S) (hT_ne : T ≠ 0) (hT_sum : T.sum = 0) :
    T.card = r := by
      by_contra h_contra;
      cases' lt_or_gt_of_ne h_contra with h h;
      · cases r <;> simp_all +decide [ seq_sigma_le ];
        unfold seq_sigma at *;
        specialize h_small ( T.card - 1 ) ; rcases k : T.card with ( _ | k ) <;> simp_all +decide;
      · unfold seq_sigma_ge at h_large;
        simp_all +decide [ Finset.ext_iff ];
        specialize h_large ( seq_sigma S T.card ) T.card ( Nat.lt_succ_of_le ( Multiset.card_le_card hT ) ) h;
        unfold seq_sigma at h_large; aesop;

/-
The difference between the sum of the first t elements and the sum of the first s elements is the sum of the elements from index s to t-1.
-/
lemma sum_take_sub_sum_take {G : Type*} [AddCommGroup G] (L : List G) (s t : ℕ)
    (hst : s ≤ t) (ht : t ≤ L.length) :
    (L.take t).sum - (L.take s).sum = ((L.drop s).take (t - s)).sum := by
      rw [ ← add_tsub_cancel_of_le hst ];
      simp +decide [ List.take_add ]

/-
The set of prefix sums of a list, including 0.
-/
def prefix_sums_set {G : Type*} [AddMonoid G] [DecidableEq G] (L : List G) : Finset G :=
  (List.range (L.length + 1)).map (fun i => (L.take i).sum) |>.toFinset

/-
If a list is zero-sum free, then the set of its prefix sums (including 0) has size equal to length + 1.
-/
lemma prefix_sums_set_card_eq_length_succ {G : Type*} [AddCommGroup G] [DecidableEq G] (L : List G)
    (h_zs : 0 ∉ seq_sigma_ge (Multiset.ofList L) 1) :
    (prefix_sums_set L).card = L.length + 1 := by
      have h_distinct_prefix_sums : ∀ i j : ℕ, i < j → i ≤ L.length → j ≤ L.length → (L.take i).sum ≠ (L.take j).sum := by
        intro i j hij hi hj h_eq
        have h_subseq : ((L.drop i).take (j - i)).sum = 0 := by
          have h_subseq : ((L.take j).sum - (L.take i).sum) = ((L.drop i).take (j - i)).sum := by
            convert sum_take_sub_sum_take L i j hij.le hj using 1;
          aesop;
        -- The subsequence from i to j-1 in L is a subsequence of L, and its sum is zero.
        have h_subseq_in_L : ∃ T : Multiset G, T ≤ Multiset.ofList L ∧ T ≠ 0 ∧ T.sum = 0 := by
          refine' ⟨ Multiset.ofList ( List.take ( j - i ) ( List.drop i L ) ), _, _, _ ⟩ <;> simp_all +decide [ List.take_append, List.drop_append ];
          · exact List.Sublist.subperm ( List.take_sublist _ _ |> List.Sublist.trans <| List.drop_sublist _ _ );
          · exact ⟨ Nat.sub_ne_zero_of_lt hij, lt_of_lt_of_le hij hj ⟩;
        obtain ⟨ T, hT₁, hT₂, hT₃ ⟩ := h_subseq_in_L; simp_all +decide [ seq_sigma_ge ] ;
        exact h_zs T.card ( Nat.lt_succ_of_le ( by simpa using Multiset.card_le_card hT₁ ) ) ( Nat.pos_of_ne_zero ( by simpa using hT₂ ) ) ( by
          exact Finset.mem_coe.2 ( Multiset.mem_toFinset.2 <| Multiset.mem_map.2 ⟨ T, Multiset.mem_powersetCard.2 ⟨ hT₁, rfl ⟩, hT₃ ⟩ ) );
      erw [ Finset.card_eq_of_bijective ];
      use fun i hi => ( L.take i ).sum;
      · unfold prefix_sums_set; aesop;
      · intro i hi; exact Multiset.mem_toFinset.mpr ( List.mem_map.mpr ⟨ i, List.mem_range.mpr hi, rfl ⟩ ) ;
      · exact fun i j hi hj h => le_antisymm ( le_of_not_gt fun hi' => h_distinct_prefix_sums _ _ hi' ( by linarith ) ( by linarith ) h.symm ) ( le_of_not_gt fun hj' => h_distinct_prefix_sums _ _ hj' ( by linarith ) ( by linarith ) h )

/-
The size of the set of prefix sums of U is p - l - |R| + 1.
-/
lemma claim_1_B_card {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (h_one_not_in_T : 1 ∉ T)
    (R : Multiset (ZMod p)) (hR : R ≤ T)
    (U_list : List (ZMod p))
    (h_U_list : Multiset.ofList U_list = T - R) :
    (prefix_sums_set U_list).card = p - l - R.card + 1 := by
      -- By definition of $U_list$, we know that its length is $T.card - R.card$.
      have hU_length : U_list.length = T.card - R.card := by
        replace h_U_list := congr_arg Multiset.card h_U_list ; aesop;
      -- By definition of $U_list$, we know that $U_list$ is zero-sum free.
      have hU_zero_sum_free : 0 ∉ seq_sigma_ge (Multiset.ofList U_list) 1 := by
        have hU_zero_sum_free : ∀ T' ≤ Multiset.ofList U_list, T' ≠ 0 → T'.sum ≠ 0 := by
          intros T' hT' hT'_nonempty hT'_sum_zero
          have hT'_length : T'.card ≤ r - 1 := by
            have hT'_length : T'.card ≤ T.card := by
              exact le_trans ( Multiset.card_le_card hT' ) ( by simp [ hU_length ] );
            have hT_card_bound : T.card ≤ r - 1 := by
              apply lem_T_card_bound S l T hS hp r hr h_small h_large hl h_one_not_in_T;
            linarith
          have hT'_in_S : T' ≤ S := by
            simp_all +decide [ Multiset.le_iff_count ];
            grind
          have hT'_not_in_small : 0 ∉ seq_sigma_le S (r - 1) := by
            assumption
          have h_contradiction : 0 ∈ seq_sigma_le S (r - 1) := by
            unfold seq_sigma_le; simp +decide [ * ] ;
            use T'.card - 1;
            rw [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero ( by aesop ) ) ];
            exact ⟨ lt_of_lt_of_le ( Nat.pred_lt ( by aesop ) ) hT'_length, by unfold seq_sigma; aesop ⟩
          contradiction;
        simp_all +decide [ seq_sigma_ge ];
        intro x hx₁ hx₂; specialize hU_zero_sum_free; unfold seq_sigma; aesop;
      have hU_card : (prefix_sums_set U_list).card = U_list.length + 1 := by
        convert prefix_sums_set_card_eq_length_succ U_list hU_zero_sum_free;
      simp_all +decide [ Nat.sub_sub ];
      omega

/-
If l < k <= l + |R|, then k is a sum of a subsequence of length >= r+1.
-/
lemma claim_1_large_k_construction {p : ℕ} [Fact p.Prime] (l : ℕ) (R : Multiset (ZMod p))
    (r : ℕ) (hr : 1 < r)
    (hl : l ≥ r)
    (hR_sum : R.sum = R.card)
    (hR_card : R.card ≤ r - 1)
    (k : ℕ)
    (hk_lower : l < k)
    (hk_upper : k ≤ l + R.card) :
    (k : ZMod p) ∈ seq_sigma_ge (Multiset.replicate l 1 + R) (r + 1) := by
      unfold seq_sigma_ge;
      norm_num [ seq_sigma ];
      refine' ⟨ k, ⟨ by linarith, by linarith ⟩, _ ⟩;
      refine' ⟨ Multiset.replicate ( k - R.card ) 1 + R, ⟨ _, _ ⟩, _ ⟩ <;> norm_num;
      · exact Multiset.le_iff_exists_add.mpr ⟨ Multiset.replicate ( l - ( k - R.card ) ) 1, by rw [ ← Multiset.replicate_add, Nat.add_sub_of_le ( by omega ) ] ⟩;
      · omega;
      · rw [ hR_sum, Nat.cast_sub ( by linarith [ Nat.sub_add_cancel hr.le ] ) ] ; ring

/-
Any element of A not in {1, ..., r} is in Sigma_{>= r+1}(1^l R).
-/
lemma claim_1_A_large_elements_in_sigma {p : ℕ} [Fact p.Prime] (l : ℕ) (R : Multiset (ZMod p)) (h : ZMod p)
    (r : ℕ) (hr : 1 < r)
    (hl : l ≥ r)
    (hR_sum : R.sum = R.card)
    (hR_card : R.card ≤ r - 1)
    (hh_ge : h ∈ seq_sigma_ge (Multiset.replicate l 1 + R) (r + 1))
    (a : ZMod p)
    (ha : a ∈ (Finset.Ico 1 (l + R.card + 1)).image (Nat.cast : ℕ → ZMod p) ∪ {h})
    (ha_large : a ∉ (Finset.Ico 1 (r + 1)).image (Nat.cast : ℕ → ZMod p)) :
    a ∈ seq_sigma_ge (Multiset.replicate l 1 + R) (r + 1) := by
      simp +zetaDelta at *;
      rcases ha with ( rfl | ⟨ x, hx, rfl ⟩ );
      · exact hh_ge;
      · -- Since $x \ge r+1$, we can use `claim_1_large_k_construction`.
        by_cases hx_large : x > l;
        · convert claim_1_large_k_construction l R r hr hl hR_sum hR_card x ( by linarith ) ( by linarith ) using 1;
        · -- Since $x \leq l$, we can take the first $x$ ones, which forms a subsequence of length $x$.
          have h_subseq : ∃ T : Multiset (ZMod p), T ≤ replicate l 1 + R ∧ T.card = x ∧ T.sum = x := by
            refine' ⟨ Multiset.replicate x 1, _, _, _ ⟩ <;> norm_num;
            rw [ Multiset.le_iff_count ];
            intro a; by_cases ha : a = 1 <;> simp_all +decide [ Multiset.count_replicate ] ;
            · linarith;
            · aesop;
          obtain ⟨ T, hT₁, hT₂, hT₃ ⟩ := h_subseq; simp_all +decide [ seq_sigma_ge ] ;
          exact ⟨ x, ⟨ by linarith, by contrapose! ha_large; aesop ⟩, by unfold seq_sigma; aesop ⟩

/-
If a small number of 1s plus a prefix sum is 0, then the total length is r.
-/
lemma small_representation_implies_extension {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (U_list : List (ZMod p)) (hU : Multiset.ofList U_list ≤ T)
    (a : ℕ) (ha : 1 ≤ a ∧ a ≤ r)
    (s : ℕ) (hs : s ≤ U_list.length)
    (h_sum : (a : ZMod p) + (U_list.take s).sum = 0) :
    a + s = r := by
      -- By Lemma `zero_sum_len_must_be_r`, since the sum is 0, the length must be r.
      have h_len : ∀ T ≤ S, T ≠ 0 → T.sum = 0 → T.card = r := by
        intro T hT hT_nonzero hT_sum
        apply zero_sum_len_must_be_r S r h_small h_large T hT hT_nonzero hT_sum;
      convert h_len ( Multiset.replicate a 1 + Multiset.ofList ( U_list.take s ) ) _ _ _ using 1 <;> simp_all ( config := { decide := Bool.true } ) [ add_comm ];
      · refine' add_le_add _ _;
        · refine' le_trans _ hU;
          exact Multiset.le_iff_exists_add.mpr ⟨ Multiset.ofList ( List.drop s U_list ), by simp ( config := { decide := Bool.true } ) ⟩;
        · exact Multiset.le_iff_exists_add.mpr ⟨ Multiset.replicate ( l - a ) 1, by rw [ ← Multiset.replicate_add, Nat.add_sub_of_le ( by linarith ) ] ⟩;
      · cases a <;> aesop_cat

/-
If a + b_s = 0, then a must be small (<= r).
-/
lemma claim_1_A_elements_small {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (R : Multiset (ZMod p)) (hR : R ≤ T)
    (hR_sum : R.sum = R.card)
    (hR_card : R.card ≤ r - 1)
    (h : ZMod p)
    (hh_ge : h ∈ seq_sigma_ge (Multiset.replicate l 1 + R) (r + 1))
    (U_list : List (ZMod p)) (hU : Multiset.ofList U_list ≤ T - R)
    (a : ZMod p)
    (ha : a ∈ (Finset.Ico 1 (l + R.card + 1)).image (Nat.cast : ℕ → ZMod p) ∪ {h})
    (s : ℕ) (hs : s ≤ U_list.length)
    (h_sum : a + (U_list.take s).sum = 0) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ r ∧ (k : ZMod p) = a := by
      -- By `small_representation_implies_extension`, if $a \notin \{1, \dots, r\}$, then $a \in \Sigma_{\ge r+1}(1^l R)$.
      by_cases ha_in : a ∈ seq_sigma_ge (Multiset.replicate l 1 + R) (r + 1);
      · -- If $a \in \Sigma_{\ge r+1}(1^l R)$, then $a$ is the sum of a subsequence $V$ of $1^l R$ with $|V| \ge r+1$.
        obtain ⟨V, hV⟩ : ∃ V : Multiset (ZMod p), V ≤ Multiset.replicate l 1 + R ∧ V.card ≥ r + 1 ∧ V.sum = a := by
          unfold seq_sigma_ge at ha_in;
          unfold seq_sigma at ha_in; aesop;
        -- Since $U \le T - R$, $1^l R$ and $U$ are disjoint parts of $S$.
        have h_disjoint : V + (Multiset.ofList (List.take s U_list)) ≤ S := by
          have h_disjoint : V + Multiset.ofList (List.take s U_list) ≤ Multiset.replicate l 1 + R + (Multiset.ofList U_list) := by
            refine' add_le_add hV.1 _;
            exact List.take_sublist _ _ |> List.Sublist.subperm;
          have h_disjoint : Multiset.replicate l 1 + R + Multiset.ofList U_list ≤ Multiset.replicate l 1 + T := by
            rw [ add_assoc ];
            exact add_le_add_left ( by simpa using Multiset.le_iff_exists_add.mp hR |> fun ⟨ Q, hQ ⟩ => by simpa [ hQ ] using add_le_add_left hU Q ) _;
          exact hS.symm ▸ le_trans ‹_› h_disjoint;
        contrapose! h_large; simp_all +decide [ seq_sigma_ge ] ;
        refine' ⟨ V.card + s, _, _ ⟩ <;> simp_all +decide [ seq_sigma ];
        · have := Multiset.card_le_card h_disjoint; simp_all +decide ;
          exact ⟨ Nat.lt_succ_of_le this, by linarith ⟩;
        · refine' ⟨ V + Multiset.ofList ( List.take s U_list ), _, _ ⟩ <;> simp_all +decide [ Multiset.le_iff_count ];
      · by_cases ha_in : a ∈ (Finset.Ico 1 (r + 1)).image (Nat.cast : ℕ → ZMod p);
        · rw [ Finset.mem_image ] at ha_in; obtain ⟨ k, hk₁, rfl ⟩ := ha_in; exact ⟨ k, Finset.mem_Ico.mp hk₁ |>.1, by linarith [ Finset.mem_Ico.mp hk₁ |>.2 ], rfl ⟩ ;
        · exact absurd ( claim_1_A_large_elements_in_sigma l R h r hr.1 hl hR_sum hR_card hh_ge a ha ( by aesop ) ) ‹_›

/-
If a subsegment of U has sum equal to its length, it contradicts the maximality of R.
-/
lemma claim_1_contradiction_step {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (R : Multiset (ZMod p)) (hR : R ≤ T)
    (hR_sum : R.sum = R.card)
    (h_maximal : ∀ W ≤ T, W.sum = W.card → W.card ≤ R.card)
    (U_list : List (ZMod p)) (hU : Multiset.ofList U_list ≤ T - R)
    (s1 s2 : ℕ) (h_lt : s1 < s2) (h_s2 : s2 ≤ U_list.length)
    (h_eq : (U_list.take s2).sum - (U_list.take s1).sum = (s2 - s1 : ZMod p)) :
    False := by
      -- Let $V$ be the subsegment of $U_{list}$ from $s1$ to $s2$.
      set V : List (ZMod p) := (List.take s2 U_list).drop s1
      have hV : V.sum = V.length := by
        have hV_sum : V.sum = (List.take s2 U_list).sum - (List.take s1 U_list).sum := by
          rw [ eq_sub_iff_add_eq' ];
          rw [ ← List.sum_take_add_sum_drop ( List.take s2 U_list ) s1 ];
          grind;
        norm_num +zetaDelta at *;
        rw [ hV_sum, h_eq, min_eq_left h_s2, Nat.cast_sub h_lt.le ];
      -- By the maximality condition, $|W| \le |R|$.
      have hW_card : (Multiset.ofList V + R).card ≤ R.card := by
        apply h_maximal;
        · have hW_subset : Multiset.ofList V ≤ T - R := by
            refine' le_trans _ hU;
            -- Since $V$ is a sublist of $U_list$, we can apply the lemma that states a sublist is a subset.
            apply List.Sublist.subperm;
            exact List.Sublist.trans ( List.drop_sublist _ _ ) ( List.take_sublist _ _ );
          exact le_trans ( add_le_add_right hW_subset _ ) ( by rw [ tsub_add_cancel_of_le hR ] );
        · aesop;
      norm_num +zetaDelta at *;
      omega

/-
There exist two distinct indices s1 < s2 and elements a1, a2 in A such that a1 + prefix_sum(s1) = 0 and a2 + prefix_sum(s2) = 0.
-/
lemma claim_1_pairs_exist_aux {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (h_one_not_in_T : 1 ∉ T)
    (R : Multiset (ZMod p)) (hR : R ≤ T)
    (hR_sum : R.sum = R.card)
    (h : ZMod p)
    (hh_ge : h ∈ seq_sigma_ge (Multiset.replicate l 1 + R) (r + 1))
    (hh_not_in : h ∉ (Finset.Ico 1 (l + R.card + 1)).image (Nat.cast : ℕ → ZMod p))
    (U_list : List (ZMod p)) (hU : Multiset.ofList U_list = T - R)
    (h_l_R_lt_p : l + R.card < p) :
    ∃ s1 s2 : ℕ, s1 < s2 ∧ s2 ≤ U_list.length ∧
    ∃ a1 a2 : ZMod p,
      a1 ∈ (Finset.Ico 1 (l + R.card + 1)).image (Nat.cast : ℕ → ZMod p) ∪ {h} ∧
      a2 ∈ (Finset.Ico 1 (l + R.card + 1)).image (Nat.cast : ℕ → ZMod p) ∪ {h} ∧
      a1 + (U_list.take s1).sum = 0 ∧
      a2 + (U_list.take s2).sum = 0 := by
        have h_card : ((Finset.Ico 1 (l + R.card + 1)).image (Nat.cast : ℕ → ZMod p) ∪ {h}).card = l + R.card + 1 := by
          rw [ Finset.card_union_of_disjoint ] <;> norm_num [ hh_not_in ];
          rw [ Finset.card_image_of_injOn ] <;> norm_num [ Function.Injective ];
          exact fun x hx y hy hxy => Nat.mod_eq_of_lt ( show x < p from by linarith [ hx.2 ] ) ▸ Nat.mod_eq_of_lt ( show y < p from by linarith [ hy.2 ] ) ▸ by simpa [ ZMod.natCast_eq_natCast_iff ] using hxy;
        have h_card_B : (prefix_sums_set U_list).card = p - l - R.card + 1 := by
          convert claim_1_B_card S l T hS hp r hr h_small h_large hl h_one_not_in_T R hR U_list hU using 1;
        have h_rep : representation_count ((Finset.Ico 1 (l + R.card + 1)).image (Nat.cast : ℕ → ZMod p) ∪ {h}) (prefix_sums_set U_list) 0 ≥ 2 := by
          refine' Nat.le_trans _ ( prop_rep _ _ _ );
          omega;
        -- Since the representation count is at least 2, there exist two distinct pairs (a1, b1) and (a2, b2) in A × B that sum to zero.
        obtain ⟨a1, b1, a2, b2, h_distinct, h_sum1, h_sum2⟩ : ∃ a1 b1 a2 b2 : ZMod p, a1 ≠ a2 ∧ b1 ≠ b2 ∧ a1 ∈ (Finset.Ico 1 (l + R.card + 1)).image (Nat.cast : ℕ → ZMod p) ∪ {h} ∧ b1 ∈ prefix_sums_set U_list ∧ a2 ∈ (Finset.Ico 1 (l + R.card + 1)).image (Nat.cast : ℕ → ZMod p) ∪ {h} ∧ b2 ∈ prefix_sums_set U_list ∧ a1 + b1 = 0 ∧ a2 + b2 = 0 := by
          obtain ⟨ a1, ha1 ⟩ := Finset.one_lt_card.mp h_rep;
          grind;
        obtain ⟨s1, hs1⟩ : ∃ s1 : ℕ, s1 ≤ U_list.length ∧ b1 = (U_list.take s1).sum := by
          unfold prefix_sums_set at h_sum2;
          norm_num +zetaDelta at *;
          exact ⟨ h_sum2.2.1.choose, Nat.le_of_lt_succ h_sum2.2.1.choose_spec.1, h_sum2.2.1.choose_spec.2.symm ⟩
        obtain ⟨s2, hs2⟩ : ∃ s2 : ℕ, s2 ≤ U_list.length ∧ b2 = (U_list.take s2).sum := by
          simp_all +decide [ prefix_sums_set ];
          rcases h_sum2.2.2.2.1 with ⟨ s2, hs2, hs2' ⟩ ; exact ⟨ s2, Nat.le_of_lt_succ hs2, hs2'.symm ⟩ ;
        grind

/-
Claim 1: R is empty.
-/
lemma claim_1_R_empty {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (h_one_not_in_T : 1 ∉ T)
    (R : Multiset (ZMod p)) (hR : R ≤ T)
    (hR_sum : R.sum = R.card)
    (h_maximal : ∀ W ≤ T, W.sum = W.card → W.card ≤ R.card) :
    R = 0 := by
      -- By Lemma h existence of h is assumed.
      by_contra hR_nonempty
      obtain ⟨h, hh_ge, hh_not_in⟩ : ∃ h ∈ seq_sigma_ge (Multiset.replicate l 1 + R) (r + 1), h ∉ (Finset.Ico 1 (l + R.card + 1)).image (Nat.cast : ℕ → ZMod p) := by
        apply_rules [ lem_find_h ];
      -- Let $U = T - R$. Let $U_{list}$ be a list corresponding to $U$.
      set U := T - R
      obtain ⟨U_list, hU_list⟩ : ∃ U_list : List (ZMod p), Multiset.ofList U_list = U := by
        exact ⟨ U.toList, by simpa ⟩;
      -- Applying Claim 1 pairs exist auxiliary to find s1 and s2.
      obtain ⟨s1, s2, hs1s2, hs2, a1, a2, ha1, ha2, h_sum1, h_sum2⟩ : ∃ s1 s2 : ℕ, s1 < s2 ∧ s2 ≤ U_list.length ∧ ∃ a1 a2 : ZMod p, a1 ∈ (Finset.Ico 1 (l + R.card + 1)).image (Nat.cast : ℕ → ZMod p) ∪ {h} ∧ a2 ∈ (Finset.Ico 1 (l + R.card + 1)).image (Nat.cast : ℕ → ZMod p) ∪ {h} ∧ a1 + (U_list.take s1).sum = 0 ∧ a2 + (U_list.take s2).sum = 0 := by
        apply_rules [ claim_1_pairs_exist_aux ];
        have := lem_l_plus_R_lt_p S l T hS hp r hr.2 h_large R hR hR_sum; aesop;
      -- By `claim_1_A_elements_small`, $a_1$ and $a_2$ correspond to integers $k_1, k_2 \in \{1, \dots, r\}$.
      obtain ⟨k1, hk1⟩ : ∃ k1 : ℕ, 1 ≤ k1 ∧ k1 ≤ r ∧ (k1 : ZMod p) = a1 := by
        apply claim_1_A_elements_small S l T hS r hr h_small h_large hl R hR hR_sum (by
        have := lem_T_card_bound S l T hS hp r hr h_small h_large hl h_one_not_in_T;
        exact le_trans ( Multiset.card_le_card hR ) this) h hh_ge U_list (by
        aesop) a1 ha1 s1 (by
        linarith) h_sum1
      obtain ⟨k2, hk2⟩ : ∃ k2 : ℕ, 1 ≤ k2 ∧ k2 ≤ r ∧ (k2 : ZMod p) = a2 := by
        apply claim_1_A_elements_small S l T hS r hr h_small h_large hl R hR hR_sum (by
        apply lem_T_card_bound S l T hS hp r hr h_small h_large hl h_one_not_in_T |> le_trans (by
        exact Multiset.card_le_card hR)) h hh_ge U_list (by
        aesop) a2 ha2 s2 hs2 h_sum2;
      -- By `small_representation_implies_extension`, $k_1 + s1 = r$ and $k_2 + s2 = r$.
      have h_k1_s1 : k1 + s1 = r := by
        apply small_representation_implies_extension S l T hS r hr h_small h_large hl U_list (by
        aesop) k1 ⟨hk1.left, hk1.right.left⟩ s1 (by
        linarith) (by
        aesop)
      have h_k2_s2 : k2 + s2 = r := by
        apply small_representation_implies_extension S l T hS r hr h_small h_large hl U_list (by
        aesop) k2 (by
        tauto) s2 (by
        linarith) (by
        aesop);
      -- By `sum_take_sub_sum_take`, $b_{s2} - b_{s1} = -a_2 - (-a_1) = a_1 - a_2 = k_1 - k_2 = (r - s1) - (r - s2) = s2 - s1$.
      have h_diff : ((U_list.take s2).sum - (U_list.take s1).sum : ZMod p) = (s2 - s1 : ZMod p) := by
        have h_diff : ((U_list.take s2).sum - (U_list.take s1).sum : ZMod p) = (k1 - k2 : ZMod p) := by
          grind;
        exact h_diff.trans ( by rw [ show k1 = r - s1 by rw [ ← h_k1_s1, add_tsub_cancel_right ], show k2 = r - s2 by rw [ ← h_k2_s2, add_tsub_cancel_right ] ] ; rw [ Nat.cast_sub ( by linarith ), Nat.cast_sub ( by linarith ) ] ; ring );
      exact claim_1_contradiction_step S l T hS R hR hR_sum h_maximal U_list ( by aesop ) s1 s2 hs1s2 hs2 h_diff

/-
Claim 1: R is empty.
-/
lemma claim_1_R_empty_v2 {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (h_one_not_in_T : 1 ∉ T)
    (R : Multiset (ZMod p)) (hR : R ≤ T)
    (hR_sum : R.sum = R.card)
    (h_maximal : ∀ W ≤ T, W.sum = W.card → W.card ≤ R.card) :
    R = 0 := by
      -- Apply the lemma that states if R is nonempty, then there exists h in the sumset of 1^l R that's not in A.
      apply claim_1_R_empty S l T hS hp r hr h_small h_large hl h_one_not_in_T R hR hR_sum h_maximal

/-
Algebraic step: if k1+s1=r, k2+s2=r, k1+b1=0, k2+b2=0, then b2-b1 = s2-s1.
-/
lemma claim_1_algebra_step {p : ℕ} [Fact p.Prime] (r s1 s2 k1 k2 : ℕ)
    (hk1 : k1 + s1 = r)
    (hk2 : k2 + s2 = r)
    (b1 b2 : ZMod p)
    (hb1 : (k1 : ZMod p) + b1 = 0)
    (hb2 : (k2 : ZMod p) + b2 = 0) :
    b2 - b1 = (s2 - s1 : ZMod p) := by
      norm_num [ show k2 = r - s2 by rw [ ← hk2, Nat.add_sub_cancel ] ] at *;
      rw [ Nat.cast_sub ( by omega ) ] at hb2;
      norm_num [ ← hk1 ] at * ; linear_combination hb2 - hb1

/-
Claim 1: R is empty.
-/
lemma claim_1_R_empty_final {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (h_one_not_in_T : 1 ∉ T)
    (R : Multiset (ZMod p)) (hR : R ≤ T)
    (hR_sum : R.sum = R.card)
    (h_maximal : ∀ W ≤ T, W.sum = W.card → W.card ≤ R.card) :
    R = 0 := by
      apply claim_1_R_empty;
      all_goals assumption

/-
Claim 1: R is empty.
-/
lemma claim_1_R_empty_proven {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (h_one_not_in_T : 1 ∉ T)
    (R : Multiset (ZMod p)) (hR : R ≤ T)
    (hR_sum : R.sum = R.card)
    (h_maximal : ∀ W ≤ T, W.sum = W.card → W.card ≤ R.card) :
    R = 0 := by
      -- Apply the lemma that states if R is nonempty and satisfies the conditions, then we derive a contradiction.
      apply claim_1_R_empty_final S l T hS hp r hr h_small h_large hl h_one_not_in_T R hR hR_sum h_maximal

/-
There exists at least one representation of 0 in A + B.
-/
lemma claim_2_existence {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (h_one_not_in_T : 1 ∉ T)
    (T_list : List (ZMod p)) (hT_list : Multiset.ofList T_list = T) :
    let A := (Finset.Ico 1 (l + 1)).image (Nat.cast : ℕ → ZMod p)
    let B := prefix_sums_set T_list
    representation_count A B 0 ≥ 1 := by
      -- Using `lem_T_card_bound`, we get $|T| \le r - 1$.
      have h_T_card_bound : T.card ≤ r - 1 := by
        apply lem_T_card_bound S l T hS hp r hr h_small h_large hl h_one_not_in_T;
      -- Using `prefix_sums_set_card_eq_length_succ`, we get $|B| = |T| + 1$.
      have h_B_card : (prefix_sums_set T_list).card = T.card + 1 := by
        -- Since $T$ is zero-sum free, the prefix sums set of $T_list$ has cardinality $T.card + 1$.
        have h_T_zero_sum_free : ∀ T' ≤ Multiset.ofList T_list, T' ≠ 0 → T'.sum ≠ 0 := by
          intros T' hT'_le hT'_ne_zero hT'_sum_zero
          have hT'_in_S : T' ≤ S := by
            exact le_trans hT'_le ( by rw [ hS, hT_list ] ; exact Multiset.le_add_left _ _ );
          -- Since $T'$ is a subsequence of $S$ and $T'$ sums to zero, $T'$ must have length $r$.
          have hT'_length : T'.card = r := by
            apply zero_sum_len_must_be_r S r h_small h_large T' hT'_in_S hT'_ne_zero hT'_sum_zero;
          have hT'_card_le_T_card : T'.card ≤ T.card := by
            exact le_trans ( Multiset.card_le_card hT'_le ) ( by aesop );
          omega;
        convert prefix_sums_set_card_eq_length_succ T_list _ using 1;
        · aesop;
        · simp_all +decide [ seq_sigma_ge ];
          intro x hx₁ hx₂; specialize h_T_zero_sum_free; unfold seq_sigma; aesop;
      -- Using `prop_rep`, we get `representation_count A B 0 ≥ A.card + B.card - p`.
      have h_rep_count : representation_count (Finset.image (fun x : ℕ => x : ℕ → ZMod p) (Finset.Ico 1 (l + 1))) (prefix_sums_set T_list) 0 ≥ (Finset.image (fun x : ℕ => x : ℕ → ZMod p) (Finset.Ico 1 (l + 1))).card + (prefix_sums_set T_list).card - p := by
        convert prop_rep _ _ _;
        exact ⟨ Fact.out ⟩;
      -- Since $A$ is the image of $\{1, \ldots, l\}$ under the cast function, and since $1, \ldots, l$ are distinct elements in $\mathbb{Z}/p\mathbb{Z}$ (because $l \leq p-1$), the cardinality of $A$ is indeed $l$.
      have h_A_card : (Finset.image (fun x : ℕ => x : ℕ → ZMod p) (Finset.Ico 1 (l + 1))).card = l := by
        have h_distinct : ∀ x y : ℕ, 1 ≤ x → x ≤ l → 1 ≤ y → y ≤ l → x ≠ y → (x : ZMod p) ≠ (y : ZMod p) := by
          intros x y hx hy hx' hy' hxy; exact (by
          contrapose! hxy; erw [ ZMod.natCast_eq_natCast_iff ] at *; simp_all +decide [ Nat.modEq_iff_dvd ] ;
          obtain ⟨ k, hk ⟩ := hxy; nlinarith [ show k = 0 by nlinarith ] ;)
        rw [ Finset.card_image_of_injOn fun x hx y hy hxy => by contrapose! hxy; exact h_distinct x y ( Finset.mem_Ico.mp hx |>.1 ) ( Finset.mem_Ico.mp hx |>.2 |> Nat.lt_succ_iff.mp ) ( Finset.mem_Ico.mp hy |>.1 ) ( Finset.mem_Ico.mp hy |>.2 |> Nat.lt_succ_iff.mp ) hxy ] ; simp +arith +decide;
      norm_num +zetaDelta at *;
      linarith! [ show l + T.card = p by rw [ hS ] at hp; norm_num at hp; linarith [ show Multiset.card ( replicate l 1 ) = l by rw [ Multiset.card_replicate ] ] ]

/-
If a + prefix_sum = 0, then a corresponds to a small integer k <= r.
-/
lemma claim_2_a_le_r {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (T_list : List (ZMod p)) (hT_list : Multiset.ofList T_list = T)
    (a : ZMod p)
    (ha : a ∈ (Finset.Ico 1 (l + 1)).image (Nat.cast : ℕ → ZMod p))
    (s : ℕ) (hs : s ≤ T_list.length)
    (h_sum : a + (T_list.take s).sum = 0) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ r ∧ (k : ZMod p) = a := by
      unfold seq_sigma_ge at h_large; simp_all ( config := { decide := Bool.true } ) [ List.take_append_eq_append_take ] ;
      contrapose! h_large;
      obtain ⟨ k, ⟨ hk₁, hk₂ ⟩, rfl ⟩ := ha;
      refine' ⟨ k + s, _, _, _ ⟩;
      · linarith [ show T.card = T_list.length from by simpa [ ← hT_list ] ];
      · exact le_of_not_lt fun h => h_large k hk₁ ( by linarith ) rfl;
      · -- Let's choose the subsequence of $S$ consisting of $k$ copies of $1$ and the first $s$ elements of $T_list$.
        obtain ⟨T_sub, hT_sub⟩ : ∃ T_sub : Multiset (ZMod p), T_sub ≤ Multiset.ofList T_list ∧ Multiset.card T_sub = s ∧ (T_sub.sum : ZMod p) = (List.take s T_list).sum := by
          refine' ⟨ Multiset.ofList ( List.take s T_list ), _, _, _ ⟩;
          · simp ( config := { decide := Bool.true } ) [ Multiset.le_iff_count ];
            intro a; rw [ ← List.take_append_drop s T_list, List.count_append ] ; aesop;
          · aesop;
          · rfl;
        -- Let's choose the subsequence of $S$ consisting of $k$ copies of $1$ and the first $s$ elements of $T_list$, which sums to $0$.
        have h_subseq : ∃ T_sub' ≤ Multiset.replicate l 1 + T, Multiset.card T_sub' = k + s ∧ (T_sub'.sum : ZMod p) = 0 := by
          refine' ⟨ Multiset.replicate k 1 + T_sub, _, _, _ ⟩ <;> simp_all ( config := { decide := Bool.true } ) [ Multiset.le_iff_count ];
          intro a; by_cases ha : a = 1 <;> simp_all ( config := { decide := Bool.true } ) [ Multiset.count_replicate ] ;
          · linarith [ hT_sub.1 1 ];
          · grind +ring;
        unfold seq_sigma; aesop;

/-
If there are two representations, the indices must be equal.
-/
lemma claim_2_uniqueness {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (h_one_not_in_T : 1 ∉ T)
    (h_no_sum_eq_len : ∀ W ≤ T, W ≠ 0 → W.sum ≠ W.card)
    (T_list : List (ZMod p)) (hT_list : Multiset.ofList T_list = T)
    (a1 a2 : ZMod p)
    (ha1 : a1 ∈ (Finset.Ico 1 (l + 1)).image (Nat.cast : ℕ → ZMod p))
    (ha2 : a2 ∈ (Finset.Ico 1 (l + 1)).image (Nat.cast : ℕ → ZMod p))
    (s1 s2 : ℕ) (hs1 : s1 ≤ T_list.length) (hs2 : s2 ≤ T_list.length)
    (h_sum1 : a1 + (T_list.take s1).sum = 0)
    (h_sum2 : a2 + (T_list.take s2).sum = 0) :
    s1 = s2 := by
      by_contra h_contra;
      -- Assume $s1 \ne s2$. WLOG $s1 < s2$.
      wlog h_lt : s1 < s2 generalizing s1 s2 a1 a2;
      · exact this a2 a1 ha2 ha1 s2 s1 hs2 hs1 h_sum2 h_sum1 ( Ne.symm h_contra ) ( lt_of_le_of_ne ( le_of_not_gt h_lt ) ( Ne.symm h_contra ) );
      · -- By `claim_2_a_le_r`, $a1$ corresponds to $k1 \le r$ and $a2$ corresponds to $k2 \le r$.
        obtain ⟨k1, hk1⟩ : ∃ k1 : ℕ, 1 ≤ k1 ∧ k1 ≤ r ∧ (k1 : ZMod p) = a1 := by
          apply_rules [ claim_2_a_le_r ]
        obtain ⟨k2, hk2⟩ : ∃ k2 : ℕ, 1 ≤ k2 ∧ k2 ≤ r ∧ (k2 : ZMod p) = a2 := by
          apply claim_2_a_le_r S l T hS r hr h_large hl T_list hT_list a2 ha2 s2 hs2 h_sum2;
        -- By `small_representation_implies_extension`, $k1 + s1 = r$ and $k2 + s2 = r$.
        have h_eq1 : k1 + s1 = r := by
          have := @small_representation_implies_extension;
          specialize this S l T hS r hr h_small h_large hl T_list ; aesop
        have h_eq2 : k2 + s2 = r := by
          have := small_representation_implies_extension S l T ( by aesop ) r hr h_small h_large hl T_list ( by aesop ) k2 ⟨ by linarith, by linarith ⟩ s2 hs2; aesop;
        -- By `claim_1_algebra_step`, $(T_{take\ s2}).sum - (T_{take\ s1}).sum = s2 - s1$.
        have h_diff : (T_list.take s2).sum - (T_list.take s1).sum = (s2 - s1 : ZMod p) := by
          have h_diff : (T_list.take s2).sum - (T_list.take s1).sum = (s2 - s1 : ZMod p) := by
            have := claim_1_algebra_step r s1 s2 k1 k2 h_eq1 h_eq2 (T_list.take s1).sum (T_list.take s2).sum
            aesop;
          convert h_diff using 1;
        -- By `sum_take_sub_sum_take`, this difference is $\sigma(T_{s1:s2})$.
        have h_subseq_sum : (T_list.drop s1 |>.take (s2 - s1)).sum = (s2 - s1 : ZMod p) := by
          rw [ ← h_diff, ← sum_take_sub_sum_take ];
          · linarith;
          · linarith;
        -- Let $W = T_{s1:s2}$. $W$ is a sublist of $T_{list}$, so $W \le T$.
        set W : Multiset (ZMod p) := Multiset.ofList (T_list.drop s1 |>.take (s2 - s1)) with hW_def
        have hW_le_T : W ≤ T := by
          rw [ ← hT_list ];
          exact List.take_sublist _ _ |> List.Sublist.subperm |> List.Subperm.trans <| List.drop_sublist _ _ |> List.Sublist.subperm;
        -- $W$ is nonempty since $s1 < s2$.
        have hW_nonempty : W ≠ 0 := by
          simp +zetaDelta at *;
          exact ⟨ Nat.sub_ne_zero_of_lt h_lt, lt_of_lt_of_le h_lt hs2 ⟩;
        specialize h_no_sum_eq_len W hW_le_T hW_nonempty ; simp_all +decide [ add_comm ];
        exact h_no_sum_eq_len ( by rw [ Nat.cast_sub h_lt.le ] )

/-
The number of representations of 0 in A + B is exactly 1.
-/
lemma claim_2_rep_count_eq_one {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (h_one_not_in_T : 1 ∉ T)
    (h_no_sum_eq_len : ∀ W ≤ T, W ≠ 0 → W.sum ≠ W.card)
    (T_list : List (ZMod p)) (hT_list : Multiset.ofList T_list = T) :
    let A := (Finset.Ico 1 (l + 1)).image (Nat.cast : ℕ → ZMod p)
    let B := prefix_sums_set T_list
    representation_count A B 0 = 1 := by
      -- From `claim_2_existence`, count $\ge 1$.
      have h_count_ge_one : 1 ≤ representation_count (Finset.image (fun k : ℕ => (k : ZMod p)) (Finset.Ico 1 (l + 1))) (prefix_sums_set T_list) 0 := by
        apply claim_2_existence S l T hS hp r hr h_small h_large hl h_one_not_in_T T_list hT_list;
      refine le_antisymm ?_ h_count_ge_one;
      -- By `claim_2_uniqueness`, if there are two pairs summing to 0, they must be the same.
      have h_unique : ∀ (a1 a2 : ZMod p) (ha1 : a1 ∈ Finset.image (fun k : ℕ => (k : ZMod p)) (Finset.Ico 1 (l + 1))) (ha2 : a2 ∈ Finset.image (fun k : ℕ => (k : ZMod p)) (Finset.Ico 1 (l + 1))) (s1 s2 : ℕ) (hs1 : s1 ≤ T_list.length) (hs2 : s2 ≤ T_list.length) (h_sum1 : a1 + (T_list.take s1).sum = 0) (h_sum2 : a2 + (T_list.take s2).sum = 0), (a1, (T_list.take s1).sum) = (a2, (T_list.take s2).sum) := by
        intros a1 a2 ha1 ha2 s1 s2 hs1 hs2 h_sum1 h_sum2
        have h_eq_s : s1 = s2 := by
          apply claim_2_uniqueness S l T hS hp r hr h_small h_large hl h_one_not_in_T h_no_sum_eq_len T_list hT_list a1 a2 ha1 ha2 s1 s2 hs1 hs2 h_sum1 h_sum2;
        grind;
      unfold representation_count;
      rw [ Finset.card_le_one_iff ];
      simp +zetaDelta at *;
      intro a b a_1 b_1 x hx hx' hx'' hx''' hx'''' y hy hy' hy'' hy''' hy''''; unfold prefix_sums_set at *; simp_all +decide [ Finset.mem_image ] ;
      grind

/-
The set of prefix sums B has the structure {0, ..., m-1} union {b_star} where b_star is in -A.
-/
lemma claim_2_B_structure {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (h_one_not_in_T : 1 ∉ T)
    (h_no_sum_eq_len : ∀ W ≤ T, W ≠ 0 → W.sum ≠ W.card)
    (T_list : List (ZMod p)) (hT_list : Multiset.ofList T_list = T)
    (h_rep_count : representation_count ((Finset.Ico 1 (l + 1)).image (Nat.cast : ℕ → ZMod p)) (prefix_sums_set T_list) 0 = 1) :
    let B := prefix_sums_set T_list
    let m := T.card
    ∃ b_star, B = (Finset.Ico 0 m).image (Nat.cast : ℕ → ZMod p) ∪ {b_star} ∧
              b_star ∈ (Finset.Ico (p - l) p).image (Nat.cast : ℕ → ZMod p) := by
                have h_card_B : (prefix_sums_set T_list).card = T.card + 1 := by
                  have hZS_T_list : 0 ∉ seq_sigma_ge (Multiset.ofList T_list) 1 := by
                    intro h;
                    obtain ⟨W, hW_le, hW_ne_zero, hW_sum⟩ : ∃ W ≤ T, W ≠ 0 ∧ W.sum = 0 := by
                      obtain ⟨W, hW_le, hW_sum⟩ : ∃ W : Multiset (ZMod p), W ≤ Multiset.ofList T_list ∧ W ≠ 0 ∧ W.sum = 0 := by
                        rw [seq_sigma_ge] at h;
                        rw [Finset.mem_biUnion] at h;
                        obtain ⟨ a, ha₁, ha₂ ⟩ := h; rw [ Finset.mem_image ] at ha₁; obtain ⟨ i, hi, rfl ⟩ := ha₁; simp_all +decide [ seq_sigma ] ;
                        exact ⟨ ha₂.choose, ha₂.choose_spec.1.1, by intro h; have := ha₂.choose_spec.1.2; aesop, ha₂.choose_spec.2 ⟩;
                      aesop;
                    have hW_card : W.card = r := by
                      apply zero_sum_len_must_be_r S r h_small h_large W (by
                      exact le_trans hW_le ( hS.symm ▸ Multiset.le_add_left _ _ )) hW_ne_zero hW_sum;
                    have := lem_T_card_bound S l T hS hp r hr h_small h_large hl h_one_not_in_T;
                    exact absurd ( Multiset.card_le_card hW_le ) ( by omega );
                  have := prefix_sums_set_card_eq_length_succ T_list hZS_T_list; aesop;
                have hB_inter_negA : (prefix_sums_set T_list ∩ Finset.image (Nat.cast : ℕ → ZMod p) (Finset.Ico (p - l) p)).card = 1 := by
                  convert h_rep_count using 1;
                  unfold representation_count;
                  refine' Finset.card_bij ( fun x hx => ( -x, x ) ) _ _ _ <;> simp_all +decide;
                  · rintro a ha x hx₁ hx₂ rfl;
                    use p - x;
                    exact ⟨ ⟨ Nat.sub_pos_of_lt hx₂, by omega ⟩, by simp +decide [ Nat.cast_sub hx₂.le ] ⟩;
                  · intros; subst_vars; simp_all +decide [ ← eq_sub_iff_add_eq' ] ;
                    refine' ⟨ p - ( ↑‹ℕ› : ℕ ), _, _ ⟩ <;> norm_num;
                    · omega;
                    · rw [ Nat.cast_sub ( by linarith ) ] ; simp +decide;
                have hB_minus_negA : (prefix_sums_set T_list \ Finset.image (Nat.cast : ℕ → ZMod p) (Finset.Ico (p - l) p)).card = T.card := by
                  have := Finset.card_sdiff_add_card_inter ( prefix_sums_set T_list ) ( Finset.image ( Nat.cast : ℕ → ZMod p ) ( Finset.Ico ( p - l ) p ) ) ; aesop;
                have hB_minus_negA_subset : prefix_sums_set T_list \ Finset.image (Nat.cast : ℕ → ZMod p) (Finset.Ico (p - l) p) ⊆ Finset.image (Nat.cast : ℕ → ZMod p) (Finset.Ico 0 T.card) := by
                  simp +decide [ Finset.subset_iff ];
                  intro x hx hx'; unfold prefix_sums_set at hx; simp_all +decide [ Finset.mem_map ] ;
                  contrapose! hx';
                  refine' ⟨ x.val, _, _, _ ⟩ <;> norm_num [ ← hp ];
                  · linarith [ show x.val ≥ T.card from Nat.le_of_not_lt fun h => hx' ( x.val ) h <| by simp +decide [ ZMod.natCast_zmod_val ] ];
                  · exact lt_of_lt_of_le ( ZMod.val_lt x ) ( by linarith );
                have hB_minus_negA_eq : prefix_sums_set T_list \ Finset.image (Nat.cast : ℕ → ZMod p) (Finset.Ico (p - l) p) = Finset.image (Nat.cast : ℕ → ZMod p) (Finset.Ico 0 T.card) := by
                  refine' Finset.eq_of_subset_of_card_le hB_minus_negA_subset _;
                  rw [ hB_minus_negA ];
                  exact Finset.card_image_le.trans ( by simpa );
                obtain ⟨ b_star, hb_star ⟩ := Finset.card_eq_one.mp hB_inter_negA;
                refine' ⟨ b_star, _, _ ⟩ <;> simp_all +decide [ Finset.ext_iff ];
                · grind;
                · specialize hb_star b_star; aesop;

/-
Swapping adjacent elements in a list preserves prefix sums at all indices except possibly the one between the swapped elements.
-/
lemma prefix_sums_swap_almost_same {G : Type*} [AddCommGroup G] [DecidableEq G]
    (L : List G) (i : ℕ) (h : i + 1 < L.length) :
    let L' := L.set i (L.get ⟨i + 1, h⟩) |>.set (i + 1) (L.get ⟨i, by omega⟩)
    ∀ j, j ≠ i + 1 → (L'.take j).sum = (L.take j).sum := by
      intro L' j hj
      generalize_proofs at *;
      induction' j with j ih generalizing i;
      · rfl;
      · rcases j with ( _ | j ) <;> simp_all +decide [ List.take_succ ];
        · cases i <;> aesop;
        · unfold L'; simp +decide [ List.getElem?_set ] ;
          rcases eq_or_ne i j with ( rfl | hne ) <;> simp_all +decide [ add_comm, add_left_comm ];
          · rw [ add_comm ];
            rw [ List.take_set_of_le, List.take_set_of_le ] <;> aesop;
          · grind

/-
If swapping adjacent elements preserves the set of prefix sums (and they were distinct), then the swapped elements are equal.
-/
lemma swap_prefix_sums_set_eq_implies_val_eq {G : Type*} [AddCommGroup G] [DecidableEq G]
    (L : List G) (i : ℕ) (h : i + 1 < L.length)
    (h_distinct : (prefix_sums_set L).card = L.length + 1)
    (L' : List G) (hL' : L' = (L.set i (L.get ⟨i + 1, h⟩)).set (i + 1) (L.get ⟨i, by omega⟩))
    (h_set_eq : prefix_sums_set L' = prefix_sums_set L) :
    L.get ⟨i, by omega⟩ = L.get ⟨i + 1, h⟩ := by
      -- By the properties of prefix sums, if swapping adjacent elements preserves the set of prefix sums, then the elements must be equal.
      have h_prefix_sum_eq : ∀ j, j ≠ i + 1 → (L'.take j).sum = (L.take j).sum := by
        convert prefix_sums_swap_almost_same L i h using 1;
        rw [ hL' ]
      generalize_proofs at *;
      have h_s_i_plus_1 : (L'.take (i + 1)).sum = (L.take (i + 1)).sum := by
        replace h_set_eq := Finset.ext_iff.mp h_set_eq; have := h_set_eq ( ( List.take ( i + 1 ) L' ).sum ) ; have := h_set_eq ( ( List.take ( i + 1 ) L ).sum ) ; simp_all +decide ;
        specialize h_set_eq ( ( List.take ( i + 1 ) L ).sum ) ; simp_all +decide [ prefix_sums_set ] ;
        contrapose! h_set_eq;
        refine' Or.inr ⟨ _, i + 1, _, _ ⟩;
        · intro x hx; by_cases hx' : x = i + 1 <;> simp_all +decide ;
          have := Finset.card_image_iff.mp ( show Finset.card ( Finset.image ( fun j => ( List.take j L ).sum ) ( Finset.range ( L.length + 1 ) ) ) = Finset.card ( Finset.range ( L.length + 1 ) ) from ?_ ) ; simp_all +decide [ Finset.card_image_of_injective, Function.Injective ] ;
          · have := @this x ( by aesop ) ( i + 1 ) ( by aesop ) ; aesop;
          · convert h_distinct using 1;
            simp +decide;
        · linarith;
        · aesop;
      rw [ List.take_succ ] at h_s_i_plus_1 ; aesop

/-
If we swap adjacent elements before the index k where the prefix sum is b_star, the elements must be equal.
-/
lemma claim_2_t_equal_next {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (h_one_not_in_T : 1 ∉ T)
    (h_no_sum_eq_len : ∀ W ≤ T, W ≠ 0 → W.sum ≠ W.card)
    (T_list : List (ZMod p)) (hT_list : Multiset.ofList T_list = T)
    (b_star : ZMod p)
    (hb_star : b_star ∈ (Finset.Ico (p - l) p).image (Nat.cast : ℕ → ZMod p))
    (B : Finset (ZMod p)) (hB : B = prefix_sums_set T_list)
    (hB_struct : B = (Finset.Ico 0 T.card).image (Nat.cast : ℕ → ZMod p) ∪ {b_star})
    (k : ℕ) (hk : k ≤ T_list.length)
    (hb_k : (T_list.take k).sum = b_star)
    (i : ℕ) (hi : i + 1 < k) :
    T_list.get ⟨i, by omega⟩ = T_list.get ⟨i + 1, by omega⟩ := by
      -- Let $T'$ be the list obtained by swapping $t_i$ and $t_{i+1}$.
      let T'_list := List.set (List.set T_list i (T_list.get ⟨i + 1, by
        linarith⟩)) (i + 1) (T_list.get ⟨i, by
        linarith⟩)
      generalize_proofs at *;
      -- Since $T'$ is a permutation of $T$, it satisfies the same conditions, so $B'$ has the structure $\{0, \dots, m-1\} \cup \{b_*'\}$ with $b_*' \in -A$.
      have hT'_struct : let A := (Finset.Ico 1 (l + 1)).image (Nat.cast : ℕ → ZMod p)
        let B := prefix_sums_set T'_list
        ∃ b_star' : ZMod p, B = (Finset.Ico 0 T.card).image (Nat.cast : ℕ → ZMod p) ∪ {b_star'} ∧
          b_star' ∈ (Finset.Ico (p - l) p).image (Nat.cast : ℕ → ZMod p) := by
            have hT'_struct : representation_count ((Finset.Ico 1 (l + 1)).image (Nat.cast : ℕ → ZMod p)) (prefix_sums_set T'_list) 0 = 1 := by
              convert claim_2_rep_count_eq_one S l T hS hp r hr h_small h_large hl h_one_not_in_T _ T'_list _;
              · assumption;
              · rw [ ← hT_list ];
                simp +decide [ List.count_set ];
                grind +ring
            generalize_proofs at *;
            have := @claim_2_B_structure p ( Fact.mk ( Fact.out : Nat.Prime p ) ) S l T hS hp r hr h_small h_large hl h_one_not_in_T ?_ T'_list ?_ hT'_struct
            generalize_proofs at *;
            · exact this;
            · exact h_no_sum_eq_len;
            · rw [ ← hT_list ];
              ext x; simp +decide [ List.getElem_set, List.getElem_set ] ;
              grind +ring
      generalize_proofs at *;
      -- Since $b_k = b_*$ and $b_k' = b_*$, we must have $b_*' = b_*$.
      obtain ⟨b_star', hb_star'_struct, hb_star'_in_A⟩ := hT'_struct
      have hb_star'_eq_b_star : b_star' = b_star := by
        have hb_star'_eq_b_star : b_star ∈ prefix_sums_set T'_list := by
          have h_sum_eq : ((T'_list.drop i).take (k - i)).sum = b_star - (T_list.take i).sum := by
            have h_sum_eq : (T'_list.take k).sum = b_star := by
              convert prefix_sums_swap_almost_same T_list i ‹_› k _ using 1
              generalize_proofs at *;
              · exact hb_k.symm;
              · linarith
            generalize_proofs at *;
            have h_sum_eq : (T'_list.take k).sum = (T'_list.take i).sum + ((T'_list.drop i).take (k - i)).sum := by
              rw [ ← List.sum_take_add_sum_drop ];
              rw [ List.take_take, List.drop_take ];
              rw [ min_eq_left ( by linarith ) ]
            generalize_proofs at *;
            have h_sum_eq : (T'_list.take i).sum = (T_list.take i).sum := by
              rw [ List.take_set_of_le, List.take_set_of_le ] <;> norm_num
            generalize_proofs at *;
            exact eq_sub_of_add_eq' ( by rw [ ← ‹ ( List.take k T'_list ).sum = b_star ›, ‹ ( List.take k T'_list ).sum = ( List.take i T'_list ).sum + ( List.take ( k - i ) ( List.drop i T'_list ) ).sum ›, h_sum_eq ] )
          generalize_proofs at *;
          have h_sum_eq : ((T'_list.take (i + (k - i))).sum) = b_star := by
            rw [ List.take_add ];
            rw [ List.sum_append, h_sum_eq ] ; ring_nf;
            rw [ List.take_set_of_le, List.take_set_of_le ] <;> norm_num
          generalize_proofs at *;
          simp_all +decide [ prefix_sums_set ];
          replace hb_star'_struct := Finset.ext_iff.mp hb_star'_struct b_star; simp_all +decide [ List.mem_map, List.mem_range ] ;
          grind
        generalize_proofs at *;
        rw [ hb_star'_struct ] at hb_star'_eq_b_star;
        simp_all +decide [ Finset.mem_union, Finset.mem_image ];
        rcases hb_star'_eq_b_star with ( rfl | ⟨ a, ha, rfl ⟩ ) <;> simp_all +decide [ Finset.ext_iff ];
        obtain ⟨ b, hb₁, hb₂ ⟩ := hb_star; obtain ⟨ c, hc₁, hc₂ ⟩ := hb_star'_in_A; simp_all +decide [ ZMod.natCast_eq_natCast_iff' ] ;
        rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] at hb₂ <;> linarith
      generalize_proofs at *;
      -- Since $B' = B$, by the previous lemma, $t_i = t_{i+1}$.
      have h_swap_eq : prefix_sums_set T'_list = prefix_sums_set T_list := by
        grind +ring
      generalize_proofs at *;
      have := swap_prefix_sums_set_eq_implies_val_eq T_list i ‹_› ?_ T'_list rfl h_swap_eq;
      · exact this;
      · rw [ ← hB, hB_struct ];
        rw [ Finset.card_union_of_disjoint ] <;> norm_num [ Finset.card_image_of_injective, Function.Injective, hT_list ];
        · rw [ Finset.card_image_of_injOn, Finset.card_range ] ; aesop_cat;
          simp +decide [ Set.InjOn ];
          exact fun x₁ hx₁ x₂ hx₂ h => Nat.mod_eq_of_lt ( show x₁ < p from lt_of_lt_of_le hx₁ ( by linarith [ show T.card ≤ p from by simpa [ ← hS, hp ] using Multiset.card_le_card ( show T ≤ S from by rw [ hS ] ; exact Multiset.le_add_left _ _ ) ] ) ) ▸ Nat.mod_eq_of_lt ( show x₂ < p from lt_of_lt_of_le hx₂ ( by linarith [ show T.card ≤ p from by simpa [ ← hS, hp ] using Multiset.card_le_card ( show T ≤ S from by rw [ hS ] ; exact Multiset.le_add_left _ _ ) ] ) ) ▸ by simpa [ ZMod.natCast_eq_natCast_iff ] using h;
        · intro x hx; contrapose! hb_star; simp_all +decide [ Finset.mem_image ] ;
          obtain ⟨ a, ⟨ ha₁, ha₂ ⟩, ha₃ ⟩ := hb_star'_in_A; norm_num [ ← hb_star, ← ha₃ ] at *;
          rw [ ZMod.natCast_eq_natCast_iff ] at ha₃ ; simp_all +decide [ Nat.mod_eq_of_lt ];
          rw [ Nat.ModEq, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] at ha₃ <;> linarith

/-
If T' is a permutation of T and contains the special element b*, then its prefix sums set is the same as T's.
-/
lemma claim_2_permutation_prefix_sums_structure {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (h_one_not_in_T : 1 ∉ T)
    (h_no_sum_eq_len : ∀ W ≤ T, W ≠ 0 → W.sum ≠ W.card)
    (T_list : List (ZMod p)) (hT_list : Multiset.ofList T_list = T)
    (b_star : ZMod p)
    (hb_star : b_star ∈ (Finset.Ico (p - l) p).image (Nat.cast : ℕ → ZMod p))
    (B : Finset (ZMod p)) (hB : B = prefix_sums_set T_list)
    (hB_struct : B = (Finset.Ico 0 T.card).image (Nat.cast : ℕ → ZMod p) ∪ {b_star})
    (T'_list : List (ZMod p))
    (h_perm : List.Perm T_list T'_list)
    (h_b_star_in : b_star ∈ prefix_sums_set T'_list) :
    prefix_sums_set T'_list = prefix_sums_set T_list := by
      have h_rep_count : (representation_count (Finset.image (Nat.cast : ℕ → ZMod p) (Finset.Ico 1 (l + 1))) (prefix_sums_set T'_list) 0) = 1 := by
        apply claim_2_rep_count_eq_one;
        any_goals tauto;
        exact hT_list ▸ by simpa using h_perm.symm;
      have hB'_struct : ∃ b'_star : ZMod p, prefix_sums_set T'_list = Finset.image (Nat.cast : ℕ → ZMod p) (Finset.Ico 0 (Multiset.card T)) ∪ {b'_star} ∧ b'_star ∈ Finset.image (Nat.cast : ℕ → ZMod p) (Finset.Ico (p - l) p) := by
        apply claim_2_B_structure;
        exact hS;
        all_goals try assumption;
        exact hT_list ▸ by simpa using h_perm.symm;
      -- Since $b_star \in B'$ and $b_star \ge p-l > m-1$, we must have $b'_star = b_star$.
      obtain ⟨b'_star, hb'_star⟩ := hB'_struct
      have hb'_star_eq : b'_star = b_star := by
        simp_all +decide [ Finset.ext_iff ];
        rcases h_b_star_in with ( rfl | ⟨ a, ha, rfl ⟩ ) <;> norm_num at *;
        obtain ⟨ b, hb₁, hb₂ ⟩ := hb_star; obtain ⟨ c, hc₁, hc₂ ⟩ := hb'_star.2; simp_all ( config := { decide := Bool.true } ) [ ZMod.natCast_eq_natCast_iff' ] ;
        rw [ Nat.mod_eq_of_lt, Nat.mod_eq_of_lt ] at hb₂ <;> try linarith;
      grind +ring

/-
If we swap adjacent elements after the index k where the prefix sum is b_star, the elements must be equal.
-/
lemma claim_2_t_equal_suffix {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (h_one_not_in_T : 1 ∉ T)
    (h_no_sum_eq_len : ∀ W ≤ T, W ≠ 0 → W.sum ≠ W.card)
    (T_list : List (ZMod p)) (hT_list : Multiset.ofList T_list = T)
    (b_star : ZMod p)
    (hb_star : b_star ∈ (Finset.Ico (p - l) p).image (Nat.cast : ℕ → ZMod p))
    (B : Finset (ZMod p)) (hB : B = prefix_sums_set T_list)
    (hB_struct : B = (Finset.Ico 0 T.card).image (Nat.cast : ℕ → ZMod p) ∪ {b_star})
    (k : ℕ) (hk : k ≤ T_list.length)
    (hb_k : (T_list.take k).sum = b_star)
    (i : ℕ) (hi : k ≤ i ∧ i + 1 < T_list.length) :
    T_list.get ⟨i, by omega⟩ = T_list.get ⟨i + 1, by omega⟩ := by
      -- By `claim_2_permutation_prefix_sums_structure`, we have `prefix_sums_set T'_list = prefix_sums_set T_list`.
      have h_perm_prefix_sums : prefix_sums_set ((T_list.set i (T_list.get ⟨i + 1, by linarith⟩)).set (i + 1) (T_list.get ⟨i, by linarith⟩)) = prefix_sums_set T_list := by
        convert claim_2_permutation_prefix_sums_structure S l T hS hp r hr h_small h_large hl h_one_not_in_T h_no_sum_eq_len T_list hT_list b_star hb_star B hB hB_struct _ _ _ using 1
        generalize_proofs at *;
        · grind;
        · have h_swap_prefix_sums : ∀ j, j ≤ k → ((T_list.set i (T_list.get ⟨i + 1, by linarith⟩)).set (i + 1) (T_list.get ⟨i, by linarith⟩)).take j = T_list.take j := by
            intro j hj; induction j <;> simp_all +decide [ List.take_succ ] ;
            grind
          generalize_proofs at *;
          simp_all +decide [ prefix_sums_set ];
          exact ⟨ k, Nat.lt_succ_of_le hk, by rw [ h_swap_prefix_sums k le_rfl, hb_k ] ⟩
      generalize_proofs at *;
      -- Since the set of prefix sums is preserved and has size $|T|+1$, the swapped elements must be equal.
      -- First show `prefix_sums_set T_list` has full cardinality, using the explicit structure `hB_struct`.
      have hadd : l + T.card = p := by
        have : (Multiset.replicate l (1 : ZMod p) + T).card = p := by
          simpa [hS] using hp
        simpa [Multiset.card_add, Multiset.card_replicate] using this
      have hTcard_le_p : T.card ≤ p := by
        exact le_trans (Nat.le_add_left _ _) (le_of_eq hadd)
      have hTcard : p - l = T.card := by
        simpa [hadd] using (Nat.add_sub_cancel_left l T.card)
      -- Nat.cast is injective on `Ico 0 T.card`, since `T.card ≤ p` and we can read values via `ZMod.val`.
      have hinj : Set.InjOn (fun n : ℕ => (n : ZMod p)) (Finset.Ico 0 T.card) := by
        intro a ha b hb hab
        have ha_lt : a < p := lt_of_lt_of_le (Finset.mem_Ico.mp ha).2 hTcard_le_p
        have hb_lt : b < p := lt_of_lt_of_le (Finset.mem_Ico.mp hb).2 hTcard_le_p
        have hval : (a : ZMod p).val = (b : ZMod p).val := by
          simpa using congrArg ZMod.val hab
        simpa [ZMod.val_cast_of_lt ha_lt, ZMod.val_cast_of_lt hb_lt] using hval
      have hcardImage :
          ((Finset.Ico 0 T.card).image (Nat.cast : ℕ → ZMod p)).card = T.card := by
        have h :
            ((Finset.Ico 0 T.card).image (Nat.cast : ℕ → ZMod p)).card = (Finset.Ico 0 T.card).card := by
          exact (Finset.card_image_iff.mpr hinj)
        subst hb_k hS hB_struct hT_list
        simp_all only [ge_iff_le, and_true, List.get_eq_getElem, coe_card, Finset.mem_image, Finset.mem_Ico, mem_coe,
          ne_eq, Nat.Ico_zero_eq_range, Finset.coe_range, Finset.card_range, card_add, card_replicate,
          Finset.union_singleton]
      -- `b_star` is not in the initial interval-image, because it's also in the disjoint upper interval-image.
      have hb_notmem :
          b_star ∉ (Finset.Ico 0 T.card).image (Nat.cast : ℕ → ZMod p) := by
        intro hbmem
        rcases Finset.mem_image.mp hbmem with ⟨n, hnI, hnEq⟩
        rcases Finset.mem_image.mp hb_star with ⟨m, hmI, hmEq⟩
        have hnm : (n : ZMod p) = (m : ZMod p) := hnEq.trans hmEq.symm
        have hn_lt_p : n < p := lt_of_lt_of_le (Finset.mem_Ico.mp hnI).2 hTcard_le_p
        have hm_lt_p : m < p := (Finset.mem_Ico.mp hmI).2
        have hval : (n : ZMod p).val = (m : ZMod p).val := by
          simpa using congrArg ZMod.val hnm
        have hnmNat : n = m := by
          simpa [ZMod.val_cast_of_lt hn_lt_p, ZMod.val_cast_of_lt hm_lt_p] using hval
        have hn_lt_T : n < T.card := (Finset.mem_Ico.mp hnI).2
        have hm_ge_T : T.card ≤ m := by
          have hm_ge : p - l ≤ m := (Finset.mem_Ico.mp hmI).1
          simpa [hTcard] using hm_ge
        have hn_lt_m : n < m := lt_of_lt_of_le hn_lt_T hm_ge_T
        have : n < n := by simp [hnmNat] at hn_lt_m
        exact (Nat.lt_irrefl _ this)
      have hcardB : B.card = T.card + 1 := by
        rw [hB_struct]
        have hcardUnion :
            (((Finset.Ico 0 T.card).image (Nat.cast : ℕ → ZMod p)) ∪ {b_star}).card
              = ((Finset.Ico 0 T.card).image (Nat.cast : ℕ → ZMod p)).card + 1 := by
          have :
              ((Finset.Ico 0 T.card).image (Nat.cast : ℕ → ZMod p)) ∪ {b_star}
                = insert b_star ((Finset.Ico 0 T.card).image (Nat.cast : ℕ → ZMod p)) := by
            ext x
            simp
          rw [this]
          exact Finset.card_insert_of_notMem hb_notmem
        have hcardImage_succ :
            (Finset.image Nat.cast (Finset.Ico 0 T.card)).card + 1 = T.card + 1 :=
          congrArg (fun n : ℕ => n + 1) hcardImage
        exact hcardUnion.trans hcardImage_succ
      have hlen : T.card = T_list.length := by
        have : T_list.length = T.card := by
          simpa using congrArg Multiset.card hT_list
        exact this.symm
      have h_distinct : (prefix_sums_set T_list).card = T_list.length + 1 := by
        have : (prefix_sums_set T_list).card = T.card + 1 := by
          simpa [hB] using hcardB
        simpa [hlen] using this
      -- Apply the swap lemma: we already have distinctness and equality of prefix-sum sets.
      have h_eq_omega :
          T_list.get ⟨i, by omega⟩ = T_list.get ⟨i + 1, by omega⟩ := by
        -- `h_perm_prefix_sums` is *definitionally* the equality needed by the swap lemma,
        -- because it uses the same swap construction (with `by omega` in the lemma statement).
        refine
          swap_prefix_sums_set_eq_implies_val_eq
            (L := T_list) (i := i) (h := by omega)
            (h_distinct := h_distinct)
            (L' :=
              (T_list.set i (T_list.get ⟨i + 1, by omega⟩)).set (i + 1) (T_list.get ⟨i, by omega⟩))
            (hL' := rfl)
            (h_set_eq := ?_)
        -- rewrite `h_perm_prefix_sums` so its swapped list matches the one above
        -- (they differ only by the proof term in the `Fin` index at `i`).
        -- This is handled by `simp` using the fact that `Fin` is extensional in its `val`.
        -- We do it explicitly:
        have hfin :
            (⟨i, by omega⟩ : Fin T_list.length) = ⟨i, by omega⟩ := by
          -- two `Fin`s with the same `val` are equal
          ext
          rfl
        have hget :
            T_list.get ⟨i, by omega⟩ = T_list.get ⟨i, by omega⟩ := by
          simp
        -- Now rewrite the swapped list in `h_perm_prefix_sums` using `hget`.
        simpa [hget] using h_perm_prefix_sums
      -- Convert from `⟨i, by omega⟩` to `⟨i, pf✝⟩` in the final goal.
      have hfin_back :
          (⟨i, by omega⟩ : Fin T_list.length) = ⟨i, by omega⟩ := by
        ext
        rfl
      have hget_back :
          T_list.get ⟨i, by omega⟩ = T_list.get ⟨i, by omega⟩ := by
        simp
      -- Finish.
      calc
        T_list.get ⟨i, by omega⟩ = T_list.get ⟨i, by omega⟩ := hget_back
        _ = T_list.get ⟨i + 1, by omega⟩ := h_eq_omega

/-
If adjacent elements in a prefix of length k are equal, then all elements in that prefix are equal.
-/
lemma constant_of_adjacent_eq_prefix {α : Type*} (L : List α) (k : ℕ) (hk : k ≤ L.length)
    (h_adj : ∀ i, (hi : i + 1 < k) → L.get ⟨i, by
      linarith⟩ = L.get ⟨i + 1, by
      linarith⟩) :
    ∀ i j, (hi : i < k) → (hj : j < k) → L.get ⟨i, by
      grind⟩ = L.get ⟨j, by
      linarith⟩ := by
      intro i j hi hj; induction' i with i ih generalizing j; induction' j with j ih'; aesop;
      · rw [ ih' ( Nat.lt_of_succ_lt hj ), h_adj _ hj ];
      · grind

/-
The list T is constant on the intervals [0, k) and [k, m).
-/
lemma claim_2_T_piecewise_constant {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (h_one_not_in_T : 1 ∉ T)
    (h_no_sum_eq_len : ∀ W ≤ T, W ≠ 0 → W.sum ≠ W.card)
    (T_list : List (ZMod p)) (hT_list : Multiset.ofList T_list = T)
    (b_star : ZMod p)
    (hb_star : b_star ∈ (Finset.Ico (p - l) p).image (Nat.cast : ℕ → ZMod p))
    (B : Finset (ZMod p)) (hB : B = prefix_sums_set T_list)
    (hB_struct : B = (Finset.Ico 0 T.card).image (Nat.cast : ℕ → ZMod p) ∪ {b_star})
    (k : ℕ) (hk : k ≤ T_list.length)
    (hb_k : (T_list.take k).sum = b_star) :
    (∀ i j, (hi : i < k) → (hj : j < k) → T_list.get ⟨i, by omega⟩ = T_list.get ⟨j, by omega⟩) ∧
    (∀ i j, (hi : k ≤ i) → (hi' : i < T_list.length) → (hj : k ≤ j) → (hj' : j < T_list.length) → T_list.get ⟨i, by omega⟩ = T_list.get ⟨j, by omega⟩) := by
      have h_const_prefix : ∀ i j : ℕ, (hi : i < k) → (hj : j < k) → T_list.get ⟨i, by
        linarith⟩ = T_list.get ⟨j, by
        linarith⟩ := by
        intro i j hi hj; exact constant_of_adjacent_eq_prefix T_list k hk ( fun i hi => claim_2_t_equal_next S l T hS hp r hr h_small h_large hl h_one_not_in_T h_no_sum_eq_len T_list hT_list b_star hb_star B hB hB_struct k hk hb_k i ( by linarith ) ) i j hi hj;
      generalize_proofs at *;
      have h_const_suffix : ∀ i : ℕ, (hi : k ≤ i ∧ i + 1 < T_list.length) → T_list.get ⟨i, by
        linarith⟩ = T_list.get ⟨i + 1, by
        linarith⟩ := by
        all_goals generalize_proofs at *;
        intros i hi
        generalize_proofs at *;
        exact claim_2_t_equal_suffix S l T hS hp r hr h_small h_large hl h_one_not_in_T h_no_sum_eq_len T_list hT_list b_star hb_star B hB hB_struct k hk hb_k i hi
      generalize_proofs at *;
      refine ⟨ h_const_prefix, ?_ ⟩;
      intro i j hi hi' hj hj';
      induction' hi with i hi ih generalizing j;
      · induction hj <;> aesop;
      · grind

/-
A list is piecewise constant if it can be split into two parts, each of which is constant.
-/
def IsPiecewiseConstant {α : Type*} (L : List α) : Prop :=
  ∃ k, k ≤ L.length ∧
    (∀ (i j : Fin L.length), (i : ℕ) < k → (j : ℕ) < k → L.get i = L.get j) ∧
    (∀ (i j : Fin L.length), k ≤ (i : ℕ) → k ≤ (j : ℕ) → L.get i = L.get j)

/-
If every permutation of a list of length at least 3 is piecewise constant, then the list is constant.
-/
lemma piecewise_constant_perm_implies_constant {α : Type*} [DecidableEq α] (L : List α)
  (h_len : L.length ≥ 3)
  (h_all_perm : ∀ L' : List α, List.Perm L' L → IsPiecewiseConstant L') :
  ∃ c, ∀ x ∈ L, x = c := by
    -- By contradiction, assume there exist distinct elements $u$ and $v$ in $L$.
    by_contra h_nonconst
    obtain ⟨u, v, hu, hv, huv⟩ : ∃ u v : α, u ≠ v ∧ u ∈ L ∧ v ∈ L := by
      norm_num +zetaDelta at *;
      obtain ⟨ u, hu ⟩ := h_nonconst ( L.get ⟨ 0, by linarith ⟩ ) ; obtain ⟨ v, hv ⟩ := h_nonconst u; use u, v; aesop;
    -- Since $|L| \ge 3$, one of the values in $L$ must appear at least twice.
    obtain ⟨c, hc⟩ : ∃ c : α, c ∈ L ∧ List.count c L ≥ 2 := by
      contrapose! h_len; simp_all +decide [ Finset.sum_add_distrib ] ;
      have h_count : ∑ c ∈ L.toFinset, List.count c L ≤ ∑ c ∈ L.toFinset, 1 := by
        exact Finset.sum_le_sum fun x hx => Nat.le_of_lt_succ ( h_len x ( List.mem_toFinset.mp hx ) );
      have h_card : L.toFinset.card ≤ 2 := by
        have := h_all_perm ( L.rotate 1 ) ( List.rotate_perm _ _ ) ; obtain ⟨ k, hk₁, hk₂, hk₃ ⟩ := this; simp_all +decide [ List.rotate ] ;
        rcases L with ( _ | ⟨ x, _ | ⟨ y, L ⟩ ⟩ ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
        rcases k with ( _ | _ | k ) <;> simp_all +decide [ Fin.forall_fin_succ ];
        · have := @hk₃ ⟨ 0, by simp +arith +decide ⟩ ⟨ 1, by simp +arith +decide ⟩ ; simp_all +decide ;
          grind;
        · rcases L with ( _ | ⟨ z, L ⟩ ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
          · exact Finset.card_insert_le _ _;
          · have := hk₃ ⟨ 1, by simp +arith +decide ⟩ ⟨ 2, by simp +arith +decide ⟩ ; simp_all +decide ;
            grind +ring;
        · specialize hk₂ ⟨ 0, by simp +decide ⟩ ⟨ 1, by simp +decide ⟩ ; simp_all +decide [ Nat.mod_eq_of_lt ] ;
          grind;
      have h_card : L.length ≤ L.toFinset.card := by
        rw [ ← Multiset.coe_card ] ; aesop;
      linarith;
    -- Without loss of generality, assume $c \neq u$.
    by_cases hcu : c = u;
    · obtain ⟨ L', hL' ⟩ := h_all_perm ( List.cons u ( List.cons v ( List.cons u ( L.erase u |>.erase v |>.erase u ) ) ) ) ( by
        rw [ List.perm_iff_count ];
        grind );
      rcases L' with ( _ | _ | _ | L' ) <;> simp_all +decide;
      · specialize hL' ⟨ 0, by simp +decide ⟩ ⟨ 1, by simp +decide ⟩ ; simp_all +decide;
      · specialize hL' ⟨ 1, by simp +arith +decide ⟩ ⟨ 2, by simp +arith +decide ⟩ ; simp_all +decide;
      · have := hL'.1 ⟨ 0, by simp +decide ⟩ ⟨ 1, by simp +decide ⟩ ; simp_all +decide ;
      · have := hL'.2.1 ⟨ 0, by simp +arith +decide ⟩ ⟨ 1, by simp +arith +decide ⟩ ; simp_all +decide ;
    · -- Construct a permutation $L'$ starting with $[c, u, c]$.
      obtain ⟨L', hL'⟩ : ∃ L' : List α, L'.Perm L ∧ L'.take 3 = [c, u, c] := by
        -- Let's remove two occurrences of $c$ and one occurrence of $u$ from $L$ to form $L''$.
        obtain ⟨L'', hL''⟩ : ∃ L'' : List α, L''.Perm (L.erase c |>.erase c |>.erase u) := by
          exact ⟨ _, List.Perm.refl _ ⟩;
        refine' ⟨ [ c, u, c ] ++ L'', _, _ ⟩ <;> simp_all +decide [ List.perm_iff_count ];
        grind;
      obtain ⟨ k, hk₁, hk₂, hk₃ ⟩ := h_all_perm L' hL'.1;
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ List.take_succ ];
      · rcases L' with ( _ | ⟨ x, _ | ⟨ y, _ | ⟨ z, _ | L' ⟩ ⟩ ⟩ ) <;> simp_all +decide;
        · exact hcu ( by simpa using hk₃ 0 1 );
        · have := hk₃ ⟨ 0, by simp +decide ⟩ ⟨ 1, by simp +decide ⟩ ; simp_all +decide ;
      · rcases L' with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | L' ⟩ ⟩ ⟩ ) <;> simp_all +decide;
        · have := hk₃ 1 2; simp_all +decide ;
        · have := hk₃ ⟨ 1, by simp +decide ⟩ ⟨ 2, by simp +decide ⟩ ; simp_all +decide ;
      · rcases L' with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | L' ⟩ ⟩ ⟩ ) <;> simp_all +decide [ Fin.forall_fin_succ ]

/-
Under the conditions of Claim 2, any ordering of T is piecewise constant.
-/
lemma claim_2_list_is_piecewise_constant {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (h_one_not_in_T : 1 ∉ T)
    (h_no_sum_eq_len : ∀ W ≤ T, W ≠ 0 → W.sum ≠ W.card)
    (T_list : List (ZMod p)) (hT_list : Multiset.ofList T_list = T) :
    IsPiecewiseConstant T_list := by
      -- Let $b^*$ be the special element in the prefix sums set of $T_list$.
      obtain ⟨b_star, hb_star⟩ : ∃ b_star, b_star ∈ (Finset.Ico (p - l) p).image (Nat.cast : ℕ → ZMod p) ∧ b_star ∈ prefix_sums_set T_list ∧
        prefix_sums_set T_list = (Finset.Ico 0 T.card).image (Nat.cast : ℕ → ZMod p) ∪ {b_star} := by
          have := claim_2_B_structure S l T hS hp r hr h_small h_large hl h_one_not_in_T h_no_sum_eq_len T_list hT_list;
          have := claim_2_rep_count_eq_one S l T hS hp r hr h_small h_large hl h_one_not_in_T h_no_sum_eq_len T_list hT_list; aesop;
      -- Let $k$ be the index where the prefix sum is $b^*$.
      obtain ⟨k, hk⟩ : ∃ k, k ≤ T_list.length ∧ (T_list.take k).sum = b_star := by
        simp_all +decide [ prefix_sums_set ];
        exact ⟨ hb_star.2.1.choose, Nat.le_of_lt_succ hb_star.2.1.choose_spec.1, hb_star.2.1.choose_spec.2 ⟩;
      exact ⟨ k, hk.1, fun i j hi hj => by
        have := claim_2_T_piecewise_constant S l T hS hp r hr h_small h_large hl h_one_not_in_T h_no_sum_eq_len T_list hT_list b_star hb_star.1 ( prefix_sums_set T_list ) rfl hb_star.2.2 k hk.1 hk.2; aesop;, fun i j hi hj => by
        have := claim_2_T_piecewise_constant S l T hS hp r hr h_small h_large hl h_one_not_in_T h_no_sum_eq_len T_list hT_list b_star hb_star.1 (prefix_sums_set T_list) rfl hb_star.2.2 k hk.1 hk.2; aesop; ⟩

/-
If |T| >= 3, then T is constant.
-/
lemma claim_2_T_constant_of_ge_3 {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (h_one_not_in_T : 1 ∉ T)
    (h_no_sum_eq_len : ∀ W ≤ T, W ≠ 0 → W.sum ≠ W.card)
    (h_len_ge_3 : T.card ≥ 3) :
    ∃ c, ∀ x ∈ T, x = c := by
      -- Let $L$ be a list corresponding to $T$.
      obtain ⟨L, hL⟩ : ∃ L : List (ZMod p), Multiset.ofList L = T := by
        exact ⟨ T.toList, by simpa ⟩;
      have hL_piecewise_constant : ∀ L' : List (ZMod p), List.Perm L' L → IsPiecewiseConstant L' := by
        intros L' hL'_perm
        apply claim_2_list_is_piecewise_constant S l T hS hp r hr h_small h_large hl h_one_not_in_T h_no_sum_eq_len L' (by
        rw [ ← hL, Multiset.coe_eq_coe ] ; aesop);
      have := piecewise_constant_perm_implies_constant L ?_ hL_piecewise_constant;
      · aesop;
      · aesop

/-
If |T| = 2, then T is constant.
-/
lemma claim_2_T_constant_of_eq_2 {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (h_one_not_in_T : 1 ∉ T)
    (h_property : has_unique_zero_sum_len S r)
    (h_len_eq_2 : T.card = 2) :
    ∃ c, ∀ x ∈ T, x = c := by
      -- Since $|T| = 2$, we can write $T = \{a, b\}$ for some $a, b \in \mathbb{Z}_p$.
      obtain ⟨a, b, hab⟩ : ∃ a b : ZMod p, T = {a, b} := by
        exact Multiset.card_eq_two.mp h_len_eq_2;
      have h_ab_ne_one : a ≠ 1 ∧ b ≠ 1 := by
        aesop_cat
      have h_ab_ne_zero : a ≠ 0 ∧ b ≠ 0 := by
        constructor <;> intro h <;> simp_all +decide [ seq_sigma_le, seq_sigma_ge ];
        · specialize h_small 0 ; simp_all +decide [ seq_sigma ];
        · specialize h_property { 0 } ; simp_all +decide [ has_unique_zero_sum_len ];
      have h_Sa_in_S : (Multiset.replicate 1 a + Multiset.replicate (p - a.val) 1) ≤ S := by
        have h_Sa_in_S : p - a.val ≤ l := by
          have h_Sa_in_S : a.val ≥ 2 := by
            contrapose! h_ab_ne_one; have := ZMod.val_lt a; interval_cases _ : a.val <;> simp_all +decide ;
            rw [ ← ZMod.natCast_zmod_val a ] ; aesop;
          have h_Sa_in_S : l = p - 2 := by
            aesop;
          omega;
        rw [ Multiset.le_iff_count ];
        intro x; by_cases hx : x = a <;> by_cases hx' : x = 1 <;> simp_all +decide [ Multiset.count_replicate ] ;
        split_ifs <;> simp_all +decide [ eq_comm ]
      have h_Sb_in_S : (Multiset.replicate 1 b + Multiset.replicate (p - b.val) 1) ≤ S := by
        have h_Sb_in_S : (Multiset.replicate 1 b + Multiset.replicate (p - b.val) 1) ≤ Multiset.replicate l 1 + {b} := by
          have h_Sb_in_S : p - b.val ≤ l := by
            have h_Sb_in_S : p - b.val ≤ p - 2 := by
              have h_b_ge_2 : 2 ≤ b.val := by
                contrapose! h_ab_ne_one; interval_cases _ : b.val <;> simp_all +decide ;
                rw [ ← ZMod.natCast_zmod_val b ] ; aesop;
              exact Nat.sub_le_sub_left h_b_ge_2 _;
            aesop;
          rw [ add_comm ];
          exact add_le_add ( Multiset.le_iff_count.mpr fun x => by rw [ Multiset.count_replicate, Multiset.count_replicate ] ; aesop ) ( Multiset.le_iff_count.mpr fun x => by rw [ Multiset.count_replicate, Multiset.count_singleton ] ; aesop );
        exact le_trans h_Sb_in_S ( by rw [ hS, hab ] ; exact add_le_add_left ( by simp +decide ) _ )
      have h_Sa_length : (Multiset.replicate 1 a + Multiset.replicate (p - a.val) 1).card = r := by
        have := h_property _ h_Sa_in_S;
        simp_all +decide [ Multiset.sum_replicate ];
        exact this ( by rw [ Nat.cast_sub ( show a.val ≤ p from a.val_lt.le ) ] ; simp +decide [ ZMod.natCast_zmod_val ] )
      have h_Sb_length : (Multiset.replicate 1 b + Multiset.replicate (p - b.val) 1).card = r := by
        -- Since $S_b$ is a subsequence of $S$ and $S_b$ sums to $0$, by the property $h_property$, the length of $S_b$ must be $r$.
        have h_Sb_zero_sum : (Multiset.replicate 1 b + Multiset.replicate (p - b.val) 1).sum = 0 := by
          simp +decide [ ZMod.natCast_eq_zero_iff, Nat.cast_sub ( show b.val ≤ p from b.val_lt.le ) ];
        exact h_property _ h_Sb_in_S ( by aesop ) h_Sb_zero_sum;
      have h_ab_eq : a.val = b.val := by
        norm_num +zetaDelta at *;
        omega;
      exact ⟨ a, by rw [ hab ] ; intro x hx; rw [ ZMod.val_injective p |>.eq_iff ] at h_ab_eq; aesop ⟩

/-
Under the conditions of Claim 2, T is constant.
-/
lemma claim_2_T_constant {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (h_one_not_in_T : 1 ∉ T)
    (h_property : has_unique_zero_sum_len S r)
    (h_no_sum_eq_len : ∀ W ≤ T, W ≠ 0 → W.sum ≠ W.card) :
    ∃ c, ∀ x ∈ T, x = c := by
      by_cases hT_card : T.card ≥ 2;
      · have := @claim_2_T_constant_of_eq_2 p;
        by_cases hT_card_eq_2 : T.card = 2;
        · exact this S l T hS hp r hr h_small h_large hl h_one_not_in_T h_property hT_card_eq_2;
        · exact claim_2_T_constant_of_ge_3 S l T hS hp r hr h_small h_large hl h_one_not_in_T h_no_sum_eq_len ( lt_of_le_of_ne hT_card ( Ne.symm hT_card_eq_2 ) );
      · interval_cases _ : T.card <;> simp_all +decide;
        rw [ Multiset.card_eq_one ] at * ; aesop

/-
Scaling by a non-zero element preserves the unique zero-sum length property.
-/
lemma has_unique_zero_sum_len_smul {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (r : ℕ)
    (a : ZMod p) (ha : a ≠ 0) :
    has_unique_zero_sum_len S r ↔ has_unique_zero_sum_len (S.map (fun x => a * x)) r := by
      constructor <;> intro h <;> unfold has_unique_zero_sum_len at *;
      · intro T hT hT_ne_zero hT_sum_zero
        have hT_preimage : ∃ T' ≤ S, Multiset.map (fun x => a * x) T' = T := by
          use Multiset.map (fun x => x / a) T;
          have hT_preimage : Multiset.map (fun x => x / a) T ≤ Multiset.map (fun x => x / a) (Multiset.map (fun x => a * x) S) := by
            exact map_le_map hT;
          simp_all +decide [ div_eq_inv_mul, mul_assoc, mul_left_comm ];
        obtain ⟨ T', hT'_sub, rfl ⟩ := hT_preimage; simp_all +decide [ ← mul_assoc, Multiset.sum_map_mul_left ] ;
        rw [ Multiset.sum_map_mul_left ] at hT_sum_zero ; aesop;
      · intro T hT hT' hT''; specialize h ( Multiset.map ( fun x => a * x ) T ) ; simp_all +decide [ Multiset.map_le_map_iff ] ;
        exact h ( by rw [ Multiset.sum_map_mul_left ] ; aesop )

/-
If every nonempty zero-sum subsequence has length r, then 0 is not a sum of a subsequence of length <= r-1 or >= r+1.
-/
lemma unique_zero_sum_len_implies_bounds {G : Type*} [AddCommMonoid G] [DecidableEq G] (S : Multiset G) (r : ℕ)
    (h_property : has_unique_zero_sum_len S r) :
    0 ∉ seq_sigma_le S (r - 1) ∧ 0 ∉ seq_sigma_ge S (r + 1) := by
      constructor;
      · unfold seq_sigma_le;
        simp +decide [ seq_sigma ];
        intro x hx y hy hxy hsum; specialize h_property y hy ( by aesop ) hsum; omega;
      · intro h;
        obtain ⟨T, hT, hT_ne, hT_sum⟩ : ∃ T ≤ S, T ≠ 0 ∧ T.sum = 0 ∧ r + 1 ≤ T.card := by
          unfold seq_sigma_ge at h;
          unfold seq_sigma at h; aesop;
        have := h_property T hT hT_ne hT_sum.1; linarith;

/-
Under the unique zero-sum length condition, the maximal multiplicity is at least r.
-/
lemma thm_main_l_ge_r {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p))
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_property : has_unique_zero_sum_len S r)
    (l : ℕ) (hl_def : l = max_multiplicity S) :
    l ≥ r := by
      have := unique_zero_sum_len_implies_bounds S r h_property;
      have := @lem_max_multiplicity p;
      exact hl_def ▸ le_trans ( le_max_left _ _ ) ( this S r hp hr ( by tauto ) ( by tauto ) )

/-
Under the conditions of Claim 1, T has no nonempty subsequence with sum equal to its length.
-/
lemma claim_1_consequence {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (l : ℕ) (T : Multiset (ZMod p))
    (hS : S = Multiset.replicate l 1 + T)
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_small : 0 ∉ seq_sigma_le S (r - 1))
    (h_large : 0 ∉ seq_sigma_ge S (r + 1))
    (hl : l ≥ r)
    (h_one_not_in_T : 1 ∉ T) :
    ∀ W ≤ T, W ≠ 0 → W.sum ≠ W.card := by
      -- Let $R$ be a subsequence of $T$ of maximal length such that $\sigma(R)=|R|$.
      obtain ⟨R, hR⟩ : ∃ R : Multiset (ZMod p), R ≤ T ∧ R.sum = R.card ∧ ∀ W : Multiset (ZMod p), W ≤ T → W.sum = W.card → W.card ≤ R.card := by
        have h_finite : Set.Finite {W : Multiset (ZMod p) | W ≤ T ∧ W.sum = W.card} := by
          exact Set.finite_iff_bddAbove.mpr ⟨ T, fun W hW => hW.1 ⟩;
        have := h_finite.toFinset.exists_max_image ( fun W => Multiset.card W ) ⟨ ∅, by aesop ⟩ ; aesop;
      -- By `claim_1_R_empty_proven`, $R=0$.
      have hR_empty : R = 0 := by
        apply claim_1_R_empty_v2 S l T hS hp r hr h_small h_large hl h_one_not_in_T R hR.left hR.right.left hR.right.right;
      intro W hW hW_ne_zero hW_sum_eq_card; specialize hR; have := hR.2.2 W hW hW_sum_eq_card; aesop;

/-
The main theorem holds in the case 1 < r < p when the most frequent element is 1.
-/
lemma thm_main_case_middle_normalized {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p))
    (hp : S.card = p)
    (r : ℕ) (hr : 1 < r ∧ r < p)
    (h_property : has_unique_zero_sum_len S r)
    (l : ℕ) (hl_def : l = max_multiplicity S)
    (h_most_freq_is_one : S.count 1 = l) :
    S.toFinset.card ≤ 2 := by
      -- Let T be the elements of S excluding the l occurrences of 1.
      set T := S.filter (· ≠ 1)
      have hS_T : S = Multiset.replicate l 1 + T := by
        ext x;
        by_cases hx : x = 1 <;> simp_all +decide [ count_replicate ];
        · aesop;
        · rw [ Multiset.count_filter ] ; aesop;
      -- By Lemma `claim_1_consequence`, T has no nonempty subsequence with sum equal to its length.
      have h_no_sum_eq_len : ∀ W ≤ T, W ≠ 0 → W.sum ≠ W.card := by
        apply claim_1_consequence S l T hS_T hp r hr (unique_zero_sum_len_implies_bounds S r h_property).left (unique_zero_sum_len_implies_bounds S r h_property).right (thm_main_l_ge_r S hp r hr h_property l hl_def) (by
        simp +zetaDelta at *);
      -- By Lemma `claim_2_T_constant`, T is constant.
      obtain ⟨c, hc⟩ : ∃ c, ∀ x ∈ T, x = c := by
        apply claim_2_T_constant S l T hS_T hp r hr (unique_zero_sum_len_implies_bounds S r h_property).left (unique_zero_sum_len_implies_bounds S r h_property).right (thm_main_l_ge_r S hp r hr h_property l hl_def) (by
        exact fun h => by simpa using Multiset.mem_filter.mp h |>.2;) h_property h_no_sum_eq_len;
      -- Since every element in S is either 1 or c, the support of S is a subset of {1, c}.
      have h_support_subset : S.toFinset ⊆ {1, c} := by
        intro x hx; by_cases hx' : x = 1 <;> simp +decide [ hx' ] at hx ⊢;
        exact hc x ( Multiset.mem_filter.mpr ⟨ hx, hx' ⟩ );
      exact le_trans ( Finset.card_le_card h_support_subset ) ( Finset.card_insert_le _ _ )

/-
Scaling by a non-zero element preserves the maximal multiplicity.
-/
lemma max_multiplicity_smul {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p)) (a : ZMod p) (ha : a ≠ 0) :
    max_multiplicity (S.map (fun x => a * x)) = max_multiplicity S := by
      unfold max_multiplicity;
      have h_max_mult_scaled : Finset.image (fun x => Multiset.count x (Multiset.map (fun x => a * x) S)) (Multiset.map (fun x => a * x) S).toFinset = Finset.image (fun x => Multiset.count x S) S.toFinset := by
        ext; simp [Finset.mem_image];
        simp +decide [ Multiset.count_map, ha ];
        simp +decide [ count, Multiset.filter_eq ];
      rw [h_max_mult_scaled]

/-
Any sequence in a finite abelian group with length at least the group order contains a nonempty zero-sum subsequence.
-/
lemma exists_zero_sum_subsequence_of_card_ge_order {G : Type*} [AddCommGroup G] [Fintype G] (S : Multiset G)
    (h_card : S.card ≥ Fintype.card G) :
    ∃ T ≤ S, T ≠ 0 ∧ T.sum = 0 := by
      -- Let's construct the list L of the elements in S and compute the prefix sums.
      obtain ⟨L, hL⟩ : ∃ L : List G, List.length L = S.card ∧ Multiset.ofList L = S := by
        exact ⟨ S.toList, by simp +decide, by simp +decide ⟩;
      -- By the pigeonhole principle, since the length of L is at least the cardinality of G, there must be two distinct indices i and j such that the prefix sums at those indices are equal.
      obtain ⟨i, j, hij, h_eq⟩ : ∃ i j : Fin (L.length + 1), i < j ∧ (L.take i).sum = (L.take j).sum := by
        by_contra h_contra;
        exact absurd ( Finset.card_le_univ ( Finset.image ( fun i : Fin ( L.length + 1 ) => ( List.take ( i : ℕ ) L ).sum ) Finset.univ ) ) ( by rw [ Finset.card_image_of_injective _ fun i j hij => le_antisymm ( not_lt.1 fun hi => h_contra ⟨ j, i, hi, hij.symm ⟩ ) ( not_lt.1 fun hj => h_contra ⟨ i, j, hj, hij ⟩ ) ] ; simp +decide ; linarith );
      refine' ⟨ Multiset.ofList ( List.take j L |> List.drop i ), _, _, _ ⟩;
      · rw [ ← hL.2 ];
        exact List.Sublist.subperm ( List.drop_sublist _ _ |> List.Sublist.trans <| List.take_sublist _ _ );
      · simp_all +decide [ ne_of_gt hij, List.drop_eq_nil_of_le ];
        exact lt_of_lt_of_le hij ( Nat.le_trans ( Nat.le_of_lt_succ ( Fin.is_lt _ ) ) ( by linarith ) );
      · have h_sum_eq : (List.take j L).sum = (List.take i L).sum + (List.drop i (List.take j L)).sum := by
          rw [ ← List.sum_take_add_sum_drop ( List.take ( j : ℕ ) L ) ( i : ℕ ) ];
          grind;
        aesop

/-
Main Theorem: If a sequence of length p in Z/pZ has a unique zero-sum length r, then it has at most 2 distinct values.
-/
theorem thm_main {p : ℕ} [Fact p.Prime] (S : Multiset (ZMod p))
    (hp : S.card = p)
    (h_exists_r : ∃ r, has_unique_zero_sum_len S r) :
    S.toFinset.card ≤ 2 := by
      -- Apply the main theorem to conclude the proof.
      obtain ⟨r, hr⟩ := h_exists_r;
      have := hr;
      exact (by
      by_cases hr : r = 1 ∨ r = p;
      · -- Apply the respective theorems for the cases where r is 1 or p.
        cases hr <;> simp_all +decide [ thm_main_case_r_eq_1, thm_main_case_r_eq_p ];
      · -- Let $x$ be a most frequent element in $S$.
        obtain ⟨x, hx⟩ : ∃ x, S.count x = max_multiplicity S ∧ x ≠ 0 := by
          -- Let $x$ be a most frequent element in $S$. Since $r \neq 1$, $x \neq 0$.
          obtain ⟨x, hx⟩ : ∃ x, S.count x = max_multiplicity S := by
            have h_max_multiplicity : ∃ x ∈ S.toFinset, ∀ y ∈ S.toFinset, Multiset.count y S ≤ Multiset.count x S := by
              apply_rules [ Finset.exists_max_image ];
              exact Exists.elim ( Multiset.card_pos_iff_exists_mem.mp ( by rw [ hp ] ; exact Nat.Prime.pos Fact.out ) ) fun x hx => ⟨ x, Multiset.mem_toFinset.mpr hx ⟩;
            obtain ⟨ x, hx₁, hx₂ ⟩ := h_max_multiplicity;
            rw [ max_multiplicity ];
            rw [ Finset.max_eq_sup_coe ];
            rw [ show ( Finset.image ( fun x => count x S ) S.toFinset ).sup WithBot.some = WithBot.some ( count x S ) from ?_ ];
            · exact exists_apply_eq_apply (fun a ↦ count a S) x;
            · exact le_antisymm ( Finset.sup_le fun y hy => by aesop ) ( Finset.le_sup ( f := WithBot.some ) ( Finset.mem_image_of_mem _ hx₁ ) );
          by_cases hx_zero : x = 0;
          · have h_zero_sum : ∃ T ≤ S, T ≠ 0 ∧ T.sum = 0 ∧ T.card = 1 := by
              use {0}
              simp [hx_zero];
              contrapose! hx; simp_all +decide [ max_multiplicity ] ;
              rw [ eq_comm ] ; intro H; simp_all +decide [ Finset.max ] ;
              -- Since $S$ is nonempty, there must be some element $x$ in $S$ with a positive count.
              obtain ⟨x, hx⟩ : ∃ x ∈ S, 0 < Multiset.count x S := by
                exact Exists.elim ( Multiset.card_pos_iff_exists_mem.mp ( by rw [ hp ] ; exact Nat.Prime.pos Fact.out ) ) fun x hx => ⟨ x, hx, Multiset.count_pos.mpr hx ⟩;
              have h_max_pos : (S.toFinset.sup (WithBot.some ∘ fun x => Multiset.count x S)) ≥ Multiset.count x S := by
                exact Finset.le_sup ( f := WithBot.some ∘ fun x => Multiset.count x S ) ( Multiset.mem_toFinset.mpr hx.1 );
              cases h : S.toFinset.sup ( WithBot.some ∘ fun x => count x S ) <;> aesop;
            obtain ⟨ T, hT₁, hT₂, hT₃, hT₄ ⟩ := h_zero_sum; specialize this; unfold has_unique_zero_sum_len at this; aesop;
          · use x;
        -- Let $S' = x^{-1} S$. Then $S'$ has most frequent element $1$ with count $l$.
        set S' : Multiset (ZMod p) := S.map (fun y => x⁻¹ * y) with hS'
        have hS'_card : S'.card = p := by
          aesop
        have hS'_unique_zero_sum_len : has_unique_zero_sum_len S' r := by
          have hS'_unique_zero_sum_len : has_unique_zero_sum_len S r ↔ has_unique_zero_sum_len S' r := by
            apply has_unique_zero_sum_len_smul;
            aesop;
          exact hS'_unique_zero_sum_len.mp this
        have hS'_most_freq_is_one : S'.count 1 = max_multiplicity S' := by
          have hS'_most_freq_is_one : S'.count 1 = S.count x := by
            rw [ Multiset.count_map ];
            rw [ Multiset.count_eq_card_filter_eq ];
            simp +decide [ eq_inv_mul_iff_mul_eq₀ hx.2, eq_comm ];
          have hS'_max_multiplicity : max_multiplicity S' = max_multiplicity S := by
            rw [ max_multiplicity_smul ] ; aesop;
          grind;
        have := thm_main_case_middle_normalized S' hS'_card r ( show 1 < r ∧ r < p from ?_ ) hS'_unique_zero_sum_len ( max_multiplicity S' ) ( by
                                                                  rfl ) hS'_most_freq_is_one
        generalize_proofs at *;
        · -- Since $S' = x^{-1} S$, we have $|\supp(S)| = |\supp(S')|$.
          have h_support_eq : S.toFinset = (S'.toFinset.image (fun y => x * y)) := by
            ext y; aesop;
          exact h_support_eq ▸ Finset.card_image_le.trans this;
        · rcases r with ( _ | _ | r ) <;> simp_all +decide [ has_unique_zero_sum_len ];
          · have := exists_zero_sum_subsequence_of_card_ge_order S ; simp_all +decide [ Finset.ext_iff ];
            tauto;
          · -- Since $S$ has a zero-sum subsequence of length $r+2$, and the cardinality of $S$ is $p$, it follows that $r+2 \leq p$.
            have h_le : r + 2 ≤ p := by
              have h_le : ∃ T ≤ S, T ≠ 0 ∧ T.sum = 0 := by
                have h_exists_zero_sum_subseq : ∃ T ≤ S, T ≠ 0 ∧ T.sum = 0 := by
                  have h_card_ge_p : S.card ≥ p := by
                    rw [hp]
                  have h_exists_zero_sum_subseq : ∃ T ≤ S, T ≠ 0 ∧ T.sum = 0 := by
                    have h_card_ge_p : S.card ≥ Fintype.card (ZMod p) := by
                      exact h_card_ge_p.trans' ( by simp +decide [ ZMod.card ] )
                    convert exists_zero_sum_subsequence_of_card_ge_order S h_card_ge_p using 1;
                  exact h_exists_zero_sum_subseq;
                exact h_exists_zero_sum_subseq;
              obtain ⟨ T, hT₁, hT₂, hT₃ ⟩ := h_le; linarith [ ‹∀ T ≤ S, ¬T = 0 → T.sum = 0 → T.card = r + 1 + 1› T hT₁ hT₂ hT₃, Multiset.card_le_card hT₁ ] ;
            exact lt_of_le_of_ne h_le hr)

/-
If T is a sub-multiset of the values of a, then T corresponds to a subset of indices.
-/
lemma subset_indices_of_submultiset {α : Type*} [DecidableEq α] {n : ℕ} (a : Fin n → α)
    (T : Multiset α) (hT : T ≤ Multiset.ofList (List.ofFn a)) :
    ∃ I : Finset (Fin n), T = Multiset.map a I.val := by
      revert T;
      induction' n with n ih <;> simp_all ( config := { decide := Bool.true } ) [ List.ofFn_succ ];
      · exact ⟨ ∅, rfl ⟩;
      · intro T hT
        by_cases h0 : a 0 ∈ T;
        · -- Let $T' = T - \{a 0\}$.
          obtain ⟨T', hT'⟩ : ∃ T', T = Multiset.cons (a 0) T' := by
            exact Multiset.exists_cons_of_mem h0;
          obtain ⟨I', hI'⟩ : ∃ I' : Finset (Fin n), T' = Multiset.map (fun i => a i.succ) I'.val := by
            apply ih (fun i => a i.succ) T';
            simp_all ( config := { decide := Bool.true } ) [ Multiset.le_iff_count ];
            intro x; specialize hT x; by_cases hx : x = a 0 <;> simp_all ( config := { decide := Bool.true } ) [ List.count_cons ] ;
            aesop;
          refine' ⟨ Finset.image ( Fin.succ ) I' ∪ { 0 }, _ ⟩ ; simp_all +decide [ Finset.sum_union, Finset.sum_singleton, Finset.mul_sum _ _ _ ] ;
          rw [ Multiset.dedup_eq_self.mpr ] ; aesop;
          exact Multiset.Nodup.map ( fun i j hij => by simpa [ Fin.ext_iff ] using hij ) ( Finset.nodup _ );
        · specialize ih ( fun i => a i.succ ) T ?_;
          · simp_all +decide [ Multiset.le_iff_count ];
            intro x; specialize hT x; by_cases hx : x = a 0 <;> simp_all +decide [ List.count_cons ] ;
            aesop;
          · obtain ⟨ I, rfl ⟩ := ih; use Finset.image ( Fin.succ ) I; simp ( config := { decide := Bool.true } ) [ Finset.sum_image, Finset.prod_image ] ;
            rw [ Multiset.dedup_eq_self.mpr ] ; aesop;
            exact Multiset.Nodup.map ( fun i j hij => by simpa [ Fin.ext_iff ] using hij ) ( Finset.nodup _ )

/-
Let $a_1, \dots, a_p$ be (not necessarily distinct) residues modulo a prime $p$, such that there
exists some $r$ so that if $S \subseteq [p]$ is non-empty and
$$\sum_{i \in S} a_i \equiv 0 \pmod{p}$$
then $|S| = r$.
Must there be at most two distinct residues amongst the $a_i$?
-/
theorem erdos_541 : ∀ p, Fact p.Prime → ∀ (a : Fin p → ZMod p),
    (∃ r, ∀ (S : Finset (Fin p)), S ≠ ∅ → ∑ i ∈ S, a i = 0 → S.card = r) →
      (Set.range a).ncard ≤ 2 := by
  intros p hp a ha
  obtain ⟨r, hr⟩ := ha
  have h_subset : ∀ T ≤ Multiset.ofList (List.ofFn a), T ≠ 0 → T.sum = 0 → T.card = r := by
    intro T hT hT_nonempty hT_zero_sum
    obtain ⟨I, hI⟩ := subset_indices_of_submultiset a T hT;
    specialize hr I ; aesop;
  have := @thm_main p hp ( Multiset.ofList ( List.ofFn a ) ) ?_ ⟨ r, h_subset ⟩ <;> simp_all +decide [ Set.ncard_eq_toFinset_card' ] ;
  convert this using 2 ; ext ; simp +decide [ List.ofFn_eq_map ]

#print axioms erdos_541
-- 'erdos_541' depends on axioms: [propext, Classical.choice, Quot.sound]
