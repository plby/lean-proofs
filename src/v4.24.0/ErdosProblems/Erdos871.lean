/-

This is a Lean formalization of a solution to Erdős Problem 871.
https://www.erdosproblems.com/forum/thread/871

A multiagent system built on Claude Opus 4.5 (from Anthropic) and
Gemini 3 Pro (from Google DeepMind) formalized Lemmas 3 and 4 from
[ErNa89].  Daniel Larsen wondered what the obstacle was in extending
that to a solution to the problem, and Claude Opus 4.5 was able to
solve the problem.

"Additive bases with many representations" Paul Erdős and Melvyn
B. Nathanson Acta Arithmetica LII (1989), pp. 399–406.


The theorems of that proof were given to Aristotle (from Harmonic) to
reprove, and the results were re-organized in an attempt to shorten
the proof.


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/

import Mathlib

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.induction false
set_option linter.style.cases false
set_option linter.style.refine false
set_option linter.style.multiGoal false

set_option maxHeartbeats 0

def shiftedPairs (x y k : ℕ) : Finset (ℕ × ℕ) :=
  Finset.image (fun i => (x - i, y + i)) (Finset.range k)

lemma shiftedPairs_card (x y k : ℕ) (hx : k ≤ x) :
    (shiftedPairs x y k).card = k := by
  have h_inj : Function.Injective (fun i => (x - i, y + i)) := by
    norm_num [ Function.Injective ];
  unfold shiftedPairs;
  rw [ Finset.card_image_of_injective _ h_inj, Finset.card_range ]

def countRepsGen (S : Finset ℕ) (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun p : ℕ × ℕ =>
    p.1 ≤ p.2 ∧ p.1 + p.2 = n ∧ p.1 ∈ S ∧ p.2 ∈ S)
    (Finset.product S S))

lemma countRepsGen_ge_of_shiftedPairs (S : Finset ℕ) (x y k : ℕ)
    (hk : k ≥ 1) (hx : k ≤ x) (hxy : x ≤ y)
    (hfst : ∀ p ∈ shiftedPairs x y k, p.1 ∈ S)
    (hsnd : ∀ p ∈ shiftedPairs x y k, p.2 ∈ S) :
    k ≤ countRepsGen S (x + y) := by
  have h_all_pairs : ∀ p ∈ shiftedPairs x y k, p.1 ≤ p.2 ∧ p.1 + p.2 = x + y ∧ p.1 ∈ S ∧ p.2 ∈ S := by
    simp_all +decide [ shiftedPairs ];
    exact fun a ha => ⟨ by linarith, by linarith [ Nat.sub_add_cancel ( by linarith : a ≤ x ) ] ⟩;
  have h_all_pairs_card : Finset.card (Finset.filter (fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ p.1 + p.2 = x + y ∧ p.1 ∈ S ∧ p.2 ∈ S) (Finset.product S S)) ≥ Finset.card (shiftedPairs x y k) := by
    exact Finset.card_le_card fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_product.mpr ⟨ hfst p hp, hsnd p hp ⟩, h_all_pairs p hp ⟩;
  exact h_all_pairs_card.trans' ( by rw [ shiftedPairs_card ] ; linarith )

structure NathansonSeq where
  n : ℕ → ℕ
  n_pos : ∀ k, 0 < n k
  n_mono : ∀ k, n k ≤ n (k + 1)
  growth_bound : ∀ k ≥ 1, n (k - 1) ≥ 3 * k^2 + 6 * k + 1
  exponential_growth : ∀ k ≥ 1, n k ≥ 8 * n (k - 1)

namespace NathansonSeq

variable (seq : NathansonSeq)

def N (k : ℕ) : ℕ := 2 * seq.n k + 1

def P (k : ℕ) : Finset ℕ :=
  if k = 0 then ∅
  else Finset.Icc (seq.N (k - 1) + 1) (seq.n k - seq.N (k - 1))

def Q (k : ℕ) : Finset ℕ :=
  if k = 0 then ∅
  else Finset.image (fun u => seq.n k - seq.n (k - 1) - 3 * k * u + 1)
                    (Finset.Icc 1 (k + 1))

def R (k : ℕ) : Finset ℕ :=
  if k = 0 then ∅
  else (Finset.Icc (seq.n k + 1) (seq.n k + seq.N (k - 1))) \
       Finset.image (fun u => seq.n k + seq.n (k - 1) + 3 * k * u)
                    (Finset.Icc 1 (k + 1))

def B_k (k : ℕ) : Finset ℕ := seq.P k ∪ seq.Q k ∪ seq.R k

def S (k : ℕ) : Finset ℕ :=
  if k = 0 then ∅
  else Finset.Icc (seq.n k + 1) (seq.n k + seq.n (k - 1) + k + 1)

def T (k : ℕ) : Finset ℕ :=
  if k = 0 then ∅
  else Finset.Icc (seq.n k + seq.n (k - 1) + 3 * k * (k + 1) + 1) (seq.n k + seq.N (k - 1))

def inB (x : ℕ) : Prop := ∃ k ≥ 1, x ∈ seq.B_k k

def countReps (S : Finset ℕ) (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun p : ℕ × ℕ =>
    p.1 ≤ p.2 ∧ p.1 + p.2 = n ∧ p.1 ∈ S ∧ p.2 ∈ S)
    (Finset.product S S))

lemma countReps_eq_countRepsGen (S : Finset ℕ) (n : ℕ) :
    countReps S n = countRepsGen S n := rfl

lemma countReps_mono {S T : Finset ℕ} (h : S ⊆ T) (n : ℕ) :
    countReps S n ≤ countReps T n := by
  apply Finset.card_mono;
  intro p hp; aesop;

lemma n_mono_from_zero (seq : NathansonSeq) (j : ℕ) : seq.n 0 ≤ seq.n j := by
  exact Nat.recOn j ( by norm_num ) fun n ihn => by linarith [ seq.n_mono n ] ;

lemma n_mono_le (seq : NathansonSeq) {i j : ℕ} (h : i ≤ j) : seq.n i ≤ seq.n j := by
  exact monotone_nat_of_le_succ ( fun k => seq.n_mono k ) h

lemma N_mono_from_zero (seq : NathansonSeq) (j : ℕ) : seq.N 0 ≤ seq.N j := by
  unfold NathansonSeq.N;
  linarith [ seq.n_mono_from_zero j ]

lemma n_strict_mono (seq : NathansonSeq) (k : ℕ) (hk : k ≥ 1) : seq.n (k - 1) < seq.n k := by
  have := seq.growth_bound k hk;
  have := seq.exponential_growth k hk;
  grind

lemma N_strict_mono (seq : NathansonSeq) (k : ℕ) : seq.N k < seq.N (k + 1) := by
  have hN_def : seq.N k = 2 * seq.n k + 1 ∧ seq.N (k + 1) = 2 * seq.n (k + 1) + 1 := by
    exact ⟨ rfl, rfl ⟩;
  have h_n_mono : seq.n k < seq.n (k + 1) := by
    exact seq.n_strict_mono _ ( Nat.succ_pos _ );
  linarith

lemma N_strict_mono_lt (seq : NathansonSeq) {i j : ℕ} (h : i < j) : seq.N i < seq.N j := by
  induction' h with j hj ih;
  · exact seq.N_strict_mono i;
  · exact lt_trans ih ( seq.N_strict_mono _ )

lemma N_mono_le (seq : NathansonSeq) {i j : ℕ} (h : i ≤ j) : seq.N i ≤ seq.N j := by
  exact Nat.le_induction ( by norm_num ) ( fun k hk ih => by linarith! [ Nat.le_of_lt ( seq.N_strict_mono k ) ] ) _ h

lemma n_exponential_bound (seq : NathansonSeq) (j : ℕ) : seq.n j ≥ 8^j * seq.n 0 := by
  induction' j with j ih;
  · norm_num;
  · simpa only [ pow_succ', mul_assoc ] using le_trans ( mul_le_mul_left' ih 8 ) ( seq.exponential_growth _ ( Nat.succ_pos _ ) )

lemma N_unbounded (seq : NathansonSeq) (M : ℕ) : ∃ k, M < seq.N k := by
  have hN_lower_bound : ∀ k, seq.N k ≥ 2 * 8^k * seq.n 0 + 1 := by
    exact fun k => by linarith [ seq.n_exponential_bound k, show seq.N k = 2 * seq.n k + 1 from rfl ] ;
  obtain ⟨k, hk⟩ : ∃ k, 8^k > M := by
    exact pow_unbounded_of_one_lt _ <| by norm_num;
  exact ⟨ k, by nlinarith [ hN_lower_bound k, seq.n_pos 0 ] ⟩

lemma N_eventually_large (seq : NathansonSeq) (N₀ : ℕ) :
    ∃ k₀, ∀ k ≥ k₀, seq.N k ≥ N₀ := by
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, seq.N k₀ > N₀ := by
    exact N_unbounded seq N₀;
  have h_mono : ∀ k ≥ k₀, seq.N k ≥ seq.N k₀ := by
    exact fun k hk => Nat.le_induction ( by linarith ) ( fun n hn ih => by linarith [ seq.N_strict_mono n ] ) k hk;
  exact ⟨ k₀, fun k hk => le_trans hk₀.le ( h_mono k hk ) ⟩

lemma P_subset (seq : NathansonSeq) (k : ℕ) (hk : 1 ≤ k) :
    ∀ x ∈ seq.P k, seq.N (k-1) + 1 ≤ x ∧ x ≤ seq.n k := by
  intros x hx
  simp [NathansonSeq.P] at hx;
  split_ifs at hx <;> norm_num at hx;
  exact ⟨ hx.1, hx.2.trans ( Nat.sub_le _ _ ) ⟩

lemma R_subset (seq : NathansonSeq) (k : ℕ) (hk : 1 ≤ k) :
    ∀ x ∈ seq.R k, seq.n k + 1 ≤ x ∧ x ≤ seq.n k + seq.N (k-1) := by
  unfold NathansonSeq.R; aesop

lemma S_subset_R (seq : NathansonSeq) (k : ℕ) (hk : 1 ≤ k) :
    seq.S k ⊆ seq.R k := by
  intro x hx
  simp [NathansonSeq.S, NathansonSeq.R] at hx ⊢;
  split_ifs at * ; aesop;
  simp_all +decide [ Finset.mem_Icc, Nat.add_assoc ];
  constructor;
  · unfold NathansonSeq.N;
    have := seq.growth_bound k hk;
    nlinarith only [ this, hx.2 ];
  · intro u hu₁ hu₂; nlinarith [ seq.growth_bound k hk ] ;

lemma S_subset_B (seq : NathansonSeq) (k : ℕ) (hk : 1 ≤ k) :
    seq.S k ⊆ seq.B_k k := by
  intro x hx;
  have hx_R : x ∈ seq.R k := by
    apply_rules [ S_subset_R ];
  exact Finset.mem_union_right _ hx_R

lemma Q_upper_bound (seq : NathansonSeq) (k : ℕ) (hk : 1 ≤ k) :
    ∀ x ∈ seq.Q k, x ≤ seq.n k - seq.n (k-1) - 3*k + 1 := by
  intro x hx
  obtain ⟨u, hu⟩ : ∃ u ∈ Finset.Icc 1 (k + 1), x = seq.n k - seq.n (k - 1) - 3 * k * u + 1 := by
    unfold NathansonSeq.Q at hx; aesop;
  exact hu.2.symm ▸ Nat.succ_le_succ ( Nat.sub_le_sub_left ( by nlinarith [ Finset.mem_Icc.mp hu.1 ] ) _ )

lemma Q_lt_n (seq : NathansonSeq) (k : ℕ) (hk : 1 ≤ k) :
    ∀ x ∈ seq.Q k, x < seq.n k := by
  intro x hx;
  have := seq.growth_bound k hk;
  have := seq.exponential_growth k hk;
  unfold NathansonSeq.Q at hx;
  grind

lemma B_k_upper_bound (seq : NathansonSeq) (k : ℕ) (hk : 1 ≤ k) :
    ∀ x ∈ seq.B_k k, x ≤ seq.n k + seq.N (k-1) := by
  intro x hx
  rw [B_k] at hx
  simp at hx;
  rcases hx with ( hx | hx | hx );
  · exact le_trans ( P_subset seq k hk x hx |>.2 ) ( Nat.le_add_right _ _ );
  · have h_Q_le : x ≤ seq.n k - seq.n (k - 1) - 3 * k + 1 := by
      exact Q_upper_bound seq k hk x hx;
    unfold NathansonSeq.N at *; omega;
  · exact ( seq.R_subset k hk ) x hx |>.2

lemma B_k_lower_bound (seq : NathansonSeq) (k : ℕ) (hk : 1 ≤ k) :
    ∀ x ∈ seq.B_k k, x ≥ seq.N (k-1) + 1 := by
  intro x hx
  simp [NathansonSeq.B_k] at hx;
  rcases hx with ( hx | hx | hx ) <;> simp_all +decide [ NathansonSeq.P, NathansonSeq.Q, NathansonSeq.R ];
  · aesop;
  · split_ifs at hx ; aesop;
    rw [ Finset.mem_image ] at hx; obtain ⟨ u, hu, rfl ⟩ := hx; unfold NathansonSeq.N; simp +arith +decide [ * ] ;
    have := seq.growth_bound k hk;
    have := seq.exponential_growth k hk;
    exact le_tsub_of_add_le_left <| le_tsub_of_add_le_left <| by nlinarith only [ this, ‹seq.n ( k - 1 ) ≥ 3 * k ^ 2 + 6 * k + 1›, Finset.mem_Icc.mp hu ] ;
  · split_ifs at hx <;> norm_num at hx;
    unfold NathansonSeq.N at *;
    have h_n_k_ge_8n_k_minus_1 : seq.n k ≥ 8 * seq.n (k - 1) := by
      exact seq.exponential_growth k hk;
    linarith [ seq.n_pos ( k - 1 ) ]

lemma B_j_gt_N_k (seq : NathansonSeq) (j k : ℕ) (hjk : j > k) (hj : 1 ≤ j) :
    ∀ x ∈ seq.B_k j, x > seq.N k := by
  have hx_bounds : ∀ x ∈ seq.B_k j, seq.N (j - 1) + 1 ≤ x ∧ x ≤ seq.n j + seq.N (j - 1) := by
    intro x hx;
    exact ⟨ B_k_lower_bound seq j hj x hx, B_k_upper_bound seq j hj x hx ⟩;
  intros x hx;
  exact lt_of_lt_of_le ( Nat.lt_succ_of_le ( seq.N_mono_le ( Nat.le_sub_one_of_lt hjk ) ) ) ( hx_bounds x hx |>.1 )

lemma B_j_le_bound (seq : NathansonSeq) (j k : ℕ) (hjk : j < k) (hj : 1 ≤ j) :
    ∀ x ∈ seq.B_k j, x ≤ seq.n (k-1) + seq.N (k-2) := by
  intro x hx
  have hx' : x ≤ seq.n j + seq.N (j - 1) := by
    exact B_k_upper_bound seq j hj x hx;
  exact le_trans hx' ( add_le_add ( seq.n_mono_le ( Nat.le_sub_one_of_lt hjk ) ) ( seq.N_mono_le ( Nat.pred_le_pred ( Nat.le_sub_one_of_lt hjk ) ) ) )

lemma lemma3_part1_mixed_impossible (seq : NathansonSeq) (k : ℕ) (hk : k ≥ 1) :
    ∀ a ∈ seq.P k ∪ seq.Q k, ∀ b ∈ seq.R k, a + b ≠ seq.N k := by
      intro a ha b hb;
      cases' Finset.mem_union.mp ha with ha' ha' <;> simp_all +decide [ R, S, Q, P ];
      · split_ifs at * <;> simp_all +decide;
        unfold NathansonSeq.N at *; omega;
      · split_ifs at * <;> simp_all +decide [ Nat.sub_sub ];
        rcases ha' with ⟨ a', ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; rw [ tsub_add_eq_add_tsub ];
        · rw [ tsub_add_eq_add_tsub ];
          · rw [ Nat.sub_eq_iff_eq_add ];
            · rw [ show seq.N k = 2 * seq.n k + 1 by rfl ];
              exact fun h => hb.2 a' ha₁ ha₂ <| by linarith;
            · nlinarith [ seq.growth_bound k hk, seq.exponential_growth k hk ];
          · have := seq.growth_bound k hk;
            nlinarith only [ this, ha₂, seq.exponential_growth k hk ];
        · have := seq.exponential_growth k hk;
          nlinarith [ seq.growth_bound k hk ]

lemma lemma3_part1_L_k_sum_lt_N (seq : NathansonSeq) (k : ℕ) (hk : k ≥ 1) :
    ∀ a ∈ seq.P k ∪ seq.Q k, ∀ b ∈ seq.P k ∪ seq.Q k, a + b < seq.N k := by
      have h_le_nk : ∀ a ∈ seq.P k ∪ seq.Q k, a ≤ seq.n k := by
        intros a ha
        by_cases haP : a ∈ seq.P k;
        · exact P_subset seq k hk a haP |>.2;
        · exact le_of_lt ( seq.Q_lt_n k hk a ( by aesop ) );
      exact fun a ha b hb => by linarith [ h_le_nk a ha, h_le_nk b hb, show seq.N k = 2 * seq.n k + 1 from rfl ] ;

lemma lemma3_part1_R_k_sum_gt_N (seq : NathansonSeq) (k : ℕ) (hk : k ≥ 1) :
    ∀ a ∈ seq.R k, ∀ b ∈ seq.R k, a + b > seq.N k := by
      have hR_bound : ∀ a ∈ seq.R k, seq.n k + 1 ≤ a := by
        exact fun a ha => R_subset seq k hk a ha |>.1;
      exact fun a ha b hb => by linarith [ hR_bound a ha, hR_bound b hb, show seq.N k = 2 * seq.n k + 1 from rfl ] ;

lemma lemma3_part1_case_eq_k (seq : NathansonSeq) (k : ℕ) (hk : k ≥ 1) :
    ∀ a ∈ seq.B_k k, ∀ b ∈ seq.B_k k, a + b ≠ seq.N k := by
      intro a ha b hb
      by_cases h : a ∈ seq.P k ∪ seq.Q k ∧ b ∈ seq.P k ∪ seq.Q k ∨ a ∈ seq.R k ∧ b ∈ seq.R k ∨ a ∈ seq.P k ∪ seq.Q k ∧ b ∈ seq.R k ∨ a ∈ seq.R k ∧ b ∈ seq.P k ∪ seq.Q k;
      · rcases h with ( ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩ | ⟨ ha, hb ⟩ );
        · exact ne_of_lt ( lemma3_part1_L_k_sum_lt_N seq k hk a ha b hb );
        · exact ne_of_gt ( by linarith [ lemma3_part1_R_k_sum_gt_N seq k hk a ha b hb ] );
        · exact lemma3_part1_mixed_impossible seq k hk a ha b hb;
        · exact fun h => lemma3_part1_mixed_impossible seq k hk b hb a ha ( by linarith );
      · unfold NathansonSeq.B_k at *; aesop;

lemma lemma3_part1_case_lt_k (seq : NathansonSeq) (k : ℕ) :
    ∀ a, (∃ j < k, j ≥ 1 ∧ a ∈ seq.B_k j) →
    ∀ b, (∃ l < k, l ≥ 1 ∧ b ∈ seq.B_k l) →
    a + b < seq.N k := by
      intros a ha b hb
      obtain ⟨j, hj₁, hj₂, hj₃⟩ := ha
      obtain ⟨l, hl₁, hl₂, hl₃⟩ := hb
      have h_bound_a : a ≤ seq.n (k-1) + seq.N (k-2) := by
        exact B_j_le_bound seq j k hj₁ hj₂ a hj₃
      have h_bound_b : b ≤ seq.n (k-1) + seq.N (k-2) := by
        exact B_j_le_bound seq l k hl₁ hl₂ b hl₃;
      suffices h_suff : 2 * (seq.n (k-1) + seq.N (k-2)) < 2 * seq.n k + 1 by
        linarith! [ show seq.N k = 2 * seq.n k + 1 from rfl ];
      have h_bounds : seq.n k ≥ 8 * seq.n (k-1) ∧ seq.N (k-2) ≤ 2 * seq.n (k-1) + 1 := by
        apply And.intro;
        · exact seq.exponential_growth k ( by linarith );
        · rcases k with ( _ | _ | k ) <;> simp_all +arith +decide;
          exact Nat.succ_le_succ ( Nat.mul_le_mul_left 2 ( seq.n_mono k ) );
      linarith [ seq.n_pos ( k - 1 ) ]

lemma lemma3_part1_case_mixed_lt (seq : NathansonSeq) (k : ℕ) :
    ∀ a ∈ seq.B_k k, ∀ b, (∃ j < k, j ≥ 1 ∧ b ∈ seq.B_k j) →
    a + b ≠ seq.N k := by
      intros a ha b hb;
      obtain ⟨j, hj₁, hj₂, hj₃⟩ := hb
      have hb_le : b ≤ 3 * seq.n (k - 1) + 1 := by
        have hb_le : b ≤ seq.n j + seq.N (j - 1) := by
          exact B_k_upper_bound seq j hj₂ b hj₃;
        have h_bounds : seq.n j ≤ seq.n (k - 1) ∧ seq.N (j - 1) ≤ 2 * seq.n (k - 2) + 1 := by
          exact ⟨ seq.n_mono_le ( by omega ), by exact add_le_add_right ( Nat.mul_le_mul_left _ ( seq.n_mono_le ( by omega ) ) ) _ ⟩;
        linarith [ seq.n_mono_le ( show k - 2 ≤ k - 1 from Nat.pred_le _ ) ];
      have ha_le : a ≤ seq.n k + 2 * seq.n (k - 1) + 1 := by
        have := B_k_upper_bound seq k ( by linarith ) a ha; aesop;
      have := seq.exponential_growth k;
      unfold NathansonSeq.N; linarith [ this ( by linarith ), seq.n_pos ( k - 1 ) ] ;

lemma lemma3_part1_case_gt_k (seq : NathansonSeq) (k : ℕ) :
    ∀ a, (∃ j > k, a ∈ seq.B_k j) →
    ∀ b, seq.inB b →
    a + b ≠ seq.N k := by
      rintro a ⟨ j, hj, ha ⟩ b ⟨ l, hl, hb ⟩ H; have := seq.B_j_gt_N_k j k hj ( by linarith ) a ha; linarith;

theorem lemma3_part1 (seq : NathansonSeq) (k : ℕ) :
    ¬∃ (a b : ℕ), seq.inB a ∧ seq.inB b ∧ a + b = seq.N k := by
  by_contra h_contra
  obtain ⟨a, b, ha, hb, hab⟩ := h_contra;
  rcases ha with ⟨ j, hj, ha ⟩;
  rcases hb with ⟨ l, hl, hb ⟩;
  by_cases h_cases : j > k ∨ l > k;
  · cases h_cases <;> [ exact lemma3_part1_case_gt_k seq k a ⟨ j, by linarith, ha ⟩ b ⟨ l, hl, hb ⟩ hab; exact lemma3_part1_case_gt_k seq k b ⟨ l, by linarith, hb ⟩ a ⟨ j, hj, ha ⟩ ( by linarith ) ];
  · push_neg at h_cases;
    cases lt_or_eq_of_le h_cases.1 <;> cases lt_or_eq_of_le h_cases.2 <;> simp_all +decide;
    · exact absurd hab ( ne_of_lt ( lemma3_part1_case_lt_k seq k a ⟨ j, by linarith, hj, ha ⟩ b ⟨ l, by linarith, hl, hb ⟩ ) );
    · exact lemma3_part1_case_mixed_lt seq k b hb a ⟨ j, by linarith, by linarith, ha ⟩ ( by linarith );
    · exact lemma3_part1_case_mixed_lt seq k a ha b ⟨ l, by linarith, by linarith, hb ⟩ hab;
    · exact lemma3_part1_case_eq_k seq k hj a ha b hb hab

theorem lemma3_case1 (seq : NathansonSeq) (k : ℕ) (hk : k ≥ 3) (n : ℕ)
    (hn_lo : 2 * seq.N (k - 1) + 2 * k ≤ n)
    (hn_hi : n ≤ seq.N k - 2 * seq.N (k - 1) - 2 * k + 1) :
    k ≤ countReps (seq.P k) n := by
      set x := n / 2
      set y := n - x;
      have h_bounds : x - (k - 1) ≥ seq.N (k - 1) + 1 ∧ y + (k - 1) ≤ seq.n k - seq.N (k - 1) := by
        norm_num +zetaDelta at *;
        unfold NathansonSeq.N at *;
        omega;
      have h_shifted_pairs : ∀ i ∈ Finset.range k, (x - i, y + i) ∈ seq.P k ×ˢ seq.P k := by
        simp +zetaDelta at *;
        intro i hi
        have h_x : seq.N (k - 1) + 1 ≤ n / 2 - i ∧ n / 2 - i ≤ seq.n k - seq.N (k - 1) := by
          grind
        have h_y : seq.N (k - 1) + 1 ≤ n - n / 2 + i ∧ n - n / 2 + i ≤ seq.n k - seq.N (k - 1) := by
          grind;
        unfold NathansonSeq.P; aesop;
      have h_distinct_pairs : Finset.image (fun i => (x - i, y + i)) (Finset.range k) ⊆ Finset.filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = n ∧ p.1 ∈ seq.P k ∧ p.2 ∈ seq.P k) (seq.P k ×ˢ seq.P k) := by
        grind;
      have := Finset.card_le_card h_distinct_pairs; rw [ Finset.card_image_of_injOn ] at this <;> aesop;

lemma lemma3_case2_ineq3 (seq : NathansonSeq) (k : ℕ) (hk : k ≥ 3) :
    seq.N (k - 1) + 1 + (seq.n k + seq.n (k - 1) + 3 * k * (k + 1) + 1) + k - 1
    ≤ seq.N k - 2 * seq.N (k - 1) - 2 * k + 2 := by
      have h_simp : 7 * seq.n (k - 1) + 3 * k^2 + 6 * k + 1 ≤ seq.n k := by
        have h_bound : 7 * seq.n (k - 1) + 3 * k^2 + 6 * k + 1 ≤ 8 * seq.n (k - 1) := by
          have := seq.growth_bound k ( by linarith ) ; ( rcases k with ( _ | _ | k ) <;> norm_num at * ; nlinarith; );
        exact le_trans h_bound ( by simpa using seq.exponential_growth k ( by linarith ) );
      unfold NathansonSeq.N;
      grind

lemma lemma3_case2_ineq1 (seq : NathansonSeq) (k : ℕ) (hk : k ≥ 3) :
    seq.N (k - 1) + 1 + k - 1 ≤ seq.n k - seq.N (k - 1) := by
      have h_sub : 2 * seq.n (k - 1) + 1 + k ≤ seq.n k - (2 * seq.n (k - 1) + 1) := by
        refine Nat.le_sub_of_add_le ?_;
        rcases k with ( _ | _ | k ) <;> simp +arith +decide at *;
        have := seq.exponential_growth ( k + 2 ) ( by linarith ) ; ( have := seq.growth_bound ( k + 2 ) ( by linarith ) ; norm_num at * ; nlinarith; );
      unfold NathansonSeq.N; aesop;

lemma lemma3_case2_ineq2 (seq : NathansonSeq) (k : ℕ) (hk : k ≥ 3) :
    seq.n k + seq.n (k - 1) + 3 * k * (k + 1) + 1 + k - 1 ≤ seq.n k + seq.N (k - 1) := by
      have h_growth_bound : seq.n (k - 1) ≥ 3 * k^2 + 6 * k + 1 := by
        exact seq.growth_bound k ( by linarith ) |> le_trans <| by rcases k with ( _ | _ | k ) <;> trivial;
      simp +arith +decide [ NathansonSeq.N ];
      nlinarith

lemma lemma3_case2_n_ge_max_T (seq : NathansonSeq) (k : ℕ) (hk : k ≥ 3) (n : ℕ)
    (hn_lo : seq.N k - 2 * seq.N (k - 1) - 2 * k + 2 ≤ n) :
    seq.n k + seq.N (k - 1) ≤ n := by
      have h_ineq : 6 * seq.n (k - 1) + 2 * k ≤ seq.n k := by
        rcases k with ( _ | _ | k ) <;> simp_all +arith +decide;
        have := seq.exponential_growth ( k + 2 ) ( by linarith );
        have := seq.growth_bound ( k + 2 ) ( by linarith ) ; norm_num at * ; nlinarith;
      unfold NathansonSeq.N at *; omega;

lemma lemma3_case2_existence (seq : NathansonSeq) (k : ℕ) (hk : k ≥ 3) (n : ℕ)
    (hn_lo : seq.N k - 2 * seq.N (k - 1) - 2 * k + 2 ≤ n)
    (hn_hi : n ≤ seq.N k - k) :
    ∃ x y, x + y = n ∧
           x ≥ seq.N (k - 1) + 1 + (k - 1) ∧
           x ≤ seq.n k - seq.N (k - 1) ∧
           y ≥ seq.n k + seq.n (k - 1) + 3 * k * (k + 1) + 1 ∧
           y + (k - 1) ≤ seq.n k + seq.N (k - 1) := by
             set min_P := seq.N (k - 1) + 1
             set max_P := seq.n k - seq.N (k - 1)
             set min_T := seq.n k + seq.n (k - 1) + 3 * k * (k + 1) + 1
             set max_T := seq.n k + seq.N (k - 1)
             set L1 := min_P + k - 1
             set R1 := max_P
             set L2 := n - max_T + k - 1
             set R2 := n - min_T;
             have h_intersect : L1 ≤ R1 ∧ L2 ≤ R2 ∧ L1 ≤ R2 ∧ L2 ≤ R1 := by
               have h_intersect : L1 ≤ R1 ∧ L2 ≤ R2 ∧ L1 ≤ R2 ∧ L2 ≤ R1 := by
                 have hL1R1 : L1 ≤ R1 := by
                   exact lemma3_case2_ineq1 seq k hk
                 have hL2R2 : L2 ≤ R2 := by
                   have hn_ge_max_T : n ≥ max_T := by
                     have := lemma3_case2_n_ge_max_T seq k hk n hn_lo; aesop;
                   have := lemma3_case2_ineq2 seq k hk;
                   omega
                 have hL1R2 : L1 ≤ R2 := by
                   have := lemma3_case2_ineq3 seq k hk;
                   omega
                 have hL2R1 : L2 ≤ R1 := by
                   unfold NathansonSeq.N at *;
                   omega
                 exact ⟨hL1R1, hL2R2, hL1R2, hL2R1⟩;
               exact h_intersect;
             use max L1 L2;
             refine' ⟨ n - Max.max L1 L2, _, _, _, _, _ ⟩ <;> omega

theorem lemma3_case2 (seq : NathansonSeq) (k : ℕ) (hk : k ≥ 3) (n : ℕ)
    (hn_lo : seq.N k - 2 * seq.N (k - 1) - 2 * k + 2 ≤ n)
    (hn_hi : n ≤ seq.N k - k) :
    k ≤ countReps (seq.P k ∪ seq.T k) n := by
      obtain ⟨ x, y, rfl, hx, hy, hxy, hxy' ⟩ := lemma3_case2_existence seq k hk n hn_lo hn_hi;
      have h_shifted_pairs : ∀ p ∈ shiftedPairs x y k, p.1 ∈ seq.P k ∧ p.2 ∈ seq.T k := by
        intros p hp
        obtain ⟨i, hi, rfl⟩ : ∃ i < k, p = (x - i, y + i) := by
          unfold shiftedPairs at hp; aesop;
        constructor;
        · unfold NathansonSeq.P;
          rw [ if_neg ( by linarith ) ] ; exact Finset.mem_Icc.mpr ⟨ Nat.le_sub_of_add_le ( by linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ k ) ] ), Nat.sub_le_of_le_add ( by linarith ) ⟩;
        · unfold NathansonSeq.T;
          exact if_neg ( by linarith ) |> fun h => h.symm ▸ Finset.mem_Icc.mpr ⟨ by linarith, by omega ⟩;
      convert countRepsGen_ge_of_shiftedPairs ( seq.P k ∪ seq.T k ) x y k ( by linarith ) ( by omega ) ( by omega ) _ _ using 1;
      · exact fun p hp => Finset.mem_union_left _ ( h_shifted_pairs p hp |>.1 );
      · exact fun p hp => Finset.mem_union_right _ ( h_shifted_pairs p hp |>.2 )

theorem lemma3_case3 (seq : NathansonSeq) (k : ℕ) (hk : k ≥ 3) (n : ℕ)
    (hn_lo : seq.N (k - 1) + 2 * k - 1 ≤ n)
    (hn_hi : n ≤ seq.N (k - 1) + seq.N (k - 2)) :
    k ≤ countReps (seq.S (k - 1)) n := by
      set x := n / 2
      set y := n - x with hy_def;
      have hx_ge_min : x - (k - 1) ≥ seq.n (k - 1) + 1 := by
        unfold NathansonSeq.N at * ; omega;
      have hy_le_max : y + (k - 1) ≤ seq.n (k - 1) + seq.n (k - 2) + k := by
        unfold NathansonSeq.N at *; omega;
      have h_shifted_pairs_subset : ∀ p ∈ shiftedPairs x y k, p.1 ∈ seq.S (k - 1) ∧ p.2 ∈ seq.S (k - 1) := by
        intro p hp
        obtain ⟨i, hi⟩ : ∃ i ∈ Finset.range k, p = (x - i, y + i) := by
          unfold shiftedPairs at hp; aesop;
        simp_all +decide [ NathansonSeq.S ];
        rcases k with ( _ | _ | k ) <;> simp_all +arith +decide;
        omega;
      have h_count_ge_k : k ≤ countRepsGen (seq.S (k - 1)) (x + y) := by
        apply countRepsGen_ge_of_shiftedPairs (seq.S (k - 1)) x y k (by linarith) (by
        omega) (by
        omega) (by
        exact fun p hp => h_shifted_pairs_subset p hp |>.1) (by
        exact fun p hp => h_shifted_pairs_subset p hp |>.2);
      convert h_count_ge_k using 1;
      rw [ countReps_eq_countRepsGen, show x + y = n by rw [ Nat.add_sub_of_le ( Nat.div_le_self _ _ ) ] ]

def lemma3_case5_x (seq : NathansonSeq) (k u : ℕ) : ℕ :=
  seq.n k - seq.n (k - 1) - 3 * k * u + 1

def lemma3_case5_y (seq : NathansonSeq) (k u j : ℕ) : ℕ :=
  seq.n k + seq.n (k - 1) + 3 * k * u - j

lemma lemma3_case5_valid (seq : NathansonSeq) (k : ℕ) (hk : k ≥ 3) (n : ℕ)
    (hn_lo : seq.N k - k + 1 ≤ n)
    (hn_hi : n ≤ seq.N k - 1)
    (u : ℕ) (hu : u ∈ Finset.Icc 1 k) :
    let j := seq.N k - n
    let x := lemma3_case5_x seq k u
    let y := lemma3_case5_y seq k u j
    x ∈ seq.Q k ∧ y ∈ seq.R k ∧ x + y = n ∧ x ≤ y := by
      constructor;
      · simp +zetaDelta at *;
        have hQ_image : seq.n k - seq.n (k - 1) - 3 * k * u + 1 ∈ Finset.image (fun u => seq.n k - seq.n (k - 1) - 3 * k * u + 1) (Finset.Icc 1 (k + 1)) := by
          exact Finset.mem_image.mpr ⟨ u, Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩, rfl ⟩;
        unfold NathansonSeq.Q; aesop;
      · constructor;
        · have hy_bounds : seq.n k + 1 ≤ seq.lemma3_case5_y k u (seq.N k - n) ∧ seq.lemma3_case5_y k u (seq.N k - n) ≤ seq.n k + seq.N (k - 1) := by
            unfold lemma3_case5_y;
            constructor;
            · refine' Nat.le_sub_of_add_le' _;
              rw [ tsub_add_eq_add_tsub ];
              · rw [ tsub_le_iff_left ];
                nlinarith [ Nat.sub_add_cancel ( show k ≤ seq.N k from by linarith [ show seq.N k ≥ k + 1 from by linarith [ show seq.N k ≥ 2 * seq.n k + 1 from by rfl, show seq.n k ≥ k from by
                                                                                                                                                                          have h_n_ge_k : ∀ k, seq.n k ≥ k := by
                                                                                                                                                                            intro k; induction' k with k ih <;> norm_num;
                                                                                                                                                                            exact Nat.succ_le_of_lt ( lt_of_le_of_lt ih ( seq.n_strict_mono _ ( Nat.succ_pos _ ) ) );
                                                                                                                                                                          exact h_n_ge_k k ] ] ), Finset.mem_Icc.mp hu ];
              · exact hn_hi.trans ( Nat.sub_le _ _ );
            · rw [ tsub_le_iff_right ];
              have h_ineq : 3 * k^2 ≤ seq.n (k - 1) := by
                rcases k with ( _ | _ | k ) <;> simp_all +arith +decide;
                have := seq.growth_bound ( k + 2 ) ( by linarith ) ; norm_num at * ; nlinarith;
              unfold NathansonSeq.N at *;
              nlinarith [ Finset.mem_Icc.mp hu, Nat.sub_add_cancel ( show n ≤ 2 * seq.n k + 1 from by omega ) ];
          have hy_not_in_set : ∀ v ∈ Finset.Icc 1 (k + 1), seq.lemma3_case5_y k u (seq.N k - n) ≠ seq.n k + seq.n (k - 1) + 3 * k * v := by
            intros v hv h_eq
            have h_j : seq.N k - n = 3 * k * (u - v) := by
              unfold lemma3_case5_y at h_eq;
              rw [ Nat.sub_eq_iff_eq_add ] at h_eq;
              · rw [ Nat.mul_sub_left_distrib, eq_tsub_iff_add_eq_of_le ] <;> linarith;
              · exact le_of_lt ( Nat.lt_of_sub_ne_zero ( by aesop ) );
            have h_j_bounds : 1 ≤ seq.N k - n ∧ seq.N k - n ≤ k - 1 := by
              omega;
            nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ k ), show u - v > 0 from Nat.pos_of_ne_zero fun h => by aesop ];
          unfold NathansonSeq.R; aesop;
        · unfold lemma3_case5_x lemma3_case5_y;
          constructor;
          · zify;
            repeat rw [ Nat.cast_sub ] <;> push_cast;
            · unfold NathansonSeq.N; ring_nf;
              norm_num;
            · exact hn_hi.trans ( Nat.sub_le _ _ );
            · have h_sub : seq.n k ≥ seq.n (k - 1) + 3 * k^2 + 6 * k + 1 := by
                have := seq.growth_bound k ( by linarith );
                linarith [ seq.exponential_growth k ( by linarith ) ];
              grind;
            · exact seq.n_mono_le ( Nat.pred_le _ );
            · have := seq.growth_bound k ( by linarith );
              exact le_tsub_of_add_le_left ( by nlinarith only [ this, seq.exponential_growth k ( by linarith ), Finset.mem_Icc.mp hu ] );
          · have h_n_k_minus_1 : seq.n (k - 1) ≥ 3 * k^2 + 6 * k + 1 := by
              exact seq.growth_bound ( k - 1 + 1 ) ( by omega ) |> fun h => by cases k <;> norm_num at * ; linarith;
            grind

theorem lemma3_case5 (seq : NathansonSeq) (k : ℕ) (hk : k ≥ 3) (n : ℕ)
    (hn_lo : seq.N k - k + 1 ≤ n)
    (hn_hi : n ≤ seq.N k - 1) :
    k ≤ countReps (seq.Q k ∪ seq.R k) n := by
      set j := seq.N k - n
      have hj_bounds : 1 ≤ j ∧ j ≤ k - 1 := by
        omega;
      set Xu : ℕ → ℕ := fun u => seq.n k - seq.n (k - 1) - 3 * k * u + 1
      set Yu : ℕ → ℕ := fun u => seq.n k + seq.n (k - 1) + 3 * k * u - j
      have hXu_yu : ∀ u ∈ Finset.Icc 1 k, Xu u ∈ seq.Q k ∧ Yu u ∈ seq.R k ∧ Xu u + Yu u = n ∧ Xu u ≤ Yu u := by
        apply lemma3_case5_valid;
        · linarith;
        · linarith;
        · assumption;
      have h_distinct : ∀ u v : ℕ, u ∈ Finset.Icc 1 k → v ∈ Finset.Icc 1 k → u ≠ v → (Xu u, Yu u) ≠ (Xu v, Yu v) := by
        simp +zetaDelta at *;
        intros; rw [ tsub_left_inj ] at *;
        · aesop;
        · grind;
        · grind;
      have h_card : Finset.card (Finset.image (fun u => (Xu u, Yu u)) (Finset.Icc 1 k)) ≤ Finset.card (Finset.filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = n ∧ p.1 ∈ seq.Q k ∪ seq.R k ∧ p.2 ∈ seq.Q k ∪ seq.R k) (Finset.product (seq.Q k ∪ seq.R k) (seq.Q k ∪ seq.R k))) := by
        exact Finset.card_le_card fun x hx => by obtain ⟨ u, hu, rfl ⟩ := Finset.mem_image.mp hx; exact Finset.mem_filter.mpr ⟨ Finset.mem_product.mpr ⟨ Finset.mem_union_left _ ( hXu_yu u hu |>.1 ), Finset.mem_union_right _ ( hXu_yu u hu |>.2.1 ) ⟩, hXu_yu u hu |>.2.2.2, hXu_yu u hu |>.2.2.1, Finset.mem_union_left _ ( hXu_yu u hu |>.1 ), Finset.mem_union_right _ ( hXu_yu u hu |>.2.1 ) ⟩ ;
      exact le_trans ( by rw [ Finset.card_image_of_injOn fun u hu v hv huv => by contrapose! huv; exact h_distinct u v hu hv huv ] ; norm_num ) h_card

lemma lemma3_case4_existence (seq : NathansonSeq) (k : ℕ) (hk : k ≥ 3) (n : ℕ)
    (hn_lo : seq.N (k - 1) + seq.N (k - 2) + 1 ≤ n)
    (hn_hi : n ≤ 2 * seq.N (k - 1) + 2 * k - 1) :
    ∃ x y, x + y = n ∧
           x ≥ seq.N (k - 3) + 1 + (k - 1) ∧
           x ≤ seq.n (k - 2) - seq.N (k - 3) ∧
           y ≥ seq.N (k - 1) + 1 ∧
           y + (k - 1) ≤ seq.n k - seq.N (k - 1) := by
             obtain ⟨x, hx_bounds⟩ : ∃ x, x ∈ Finset.Icc (seq.N (k - 3) + 1 + (k - 1)) (seq.n (k - 2) - seq.N (k - 3)) ∧ n - x ∈ Finset.Icc (seq.N (k - 1) + 1) (seq.n k - seq.N (k - 1) - (k - 1)) := by
               have h_interval : max (seq.N (k - 3) + 1 + (k - 1)) (n - (seq.n k - seq.N (k - 1) - (k - 1))) ≤ min (seq.n (k - 2) - seq.N (k - 3)) (n - (seq.N (k - 1) + 1)) := by
                 rcases k with ( _ | _ | _ | k ) <;> simp_all +arith +decide;
                 unfold NathansonSeq.N at *;
                 have := seq.growth_bound ( k + 1 ) ( by linarith ) ; have := seq.growth_bound ( k + 2 ) ( by linarith ) ; have := seq.growth_bound ( k + 3 ) ( by linarith ) ; have := seq.exponential_growth ( k + 1 ) ( by linarith ) ; have := seq.exponential_growth ( k + 2 ) ( by linarith ) ; have := seq.exponential_growth ( k + 3 ) ( by linarith ) ; norm_num at * ; omega;
               simp +zetaDelta at *;
               use max (seq.N (k - 3) + 1 + (k - 1)) (n - (seq.n k - seq.N (k - 1) - (k - 1)));
               omega;
             use x, n - x;
             simp +zetaDelta at *;
             omega

theorem lemma3_case4 (seq : NathansonSeq) (k : ℕ) (hk : k ≥ 3) (n : ℕ)
    (hn_lo : seq.N (k - 1) + seq.N (k - 2) + 1 ≤ n)
    (hn_hi : n ≤ 2 * seq.N (k - 1) + 2 * k - 1) :
    k ≤ countReps (seq.P k ∪ seq.P (k - 2)) n := by
      have := lemma3_case4_existence seq k hk n hn_lo hn_hi;
      obtain ⟨ x, y, hxy, hx, hx', hy, hy' ⟩ := this;
      have h_shifted_pairs : ∀ i ∈ Finset.range k, (x - i) ∈ seq.P (k - 2) ∧ (y + i) ∈ seq.P k := by
        unfold NathansonSeq.P;
        rcases k with ( _ | _ | k ) <;> simp_all +arith +decide;
        intro i hi; split_ifs <;> simp_all +arith +decide;
        omega;
      have h_countRepsGen : k ≤ countRepsGen (seq.P k ∪ seq.P (k - 2)) (x + y) := by
        apply countRepsGen_ge_of_shiftedPairs;
        · linarith;
        · grind;
        · rcases k with ( _ | _ | k ) <;> simp_all +arith +decide;
          unfold NathansonSeq.N at *;
          omega;
        · unfold shiftedPairs; aesop;
        · unfold shiftedPairs; aesop;
      aesop

def lemma3_case6_x (seq : NathansonSeq) (k u : ℕ) : ℕ :=
  seq.n (k - 1) - seq.n (k - 2) - 3 * (k - 1) * u + 1

def lemma3_case6_y (seq : NathansonSeq) (k u j : ℕ) : ℕ :=
  seq.n (k - 1) + seq.n (k - 2) + 3 * (k - 1) * u + j

lemma lemma3_case6_valid (seq : NathansonSeq) (k : ℕ) (hk : k ≥ 3) (n : ℕ)
    (hn_lo : seq.N (k - 1) + 1 ≤ n)
    (hn_hi : n ≤ seq.N (k - 1) + 2 * k - 2)
    (u : ℕ) (hu : u ∈ Finset.Icc 1 k) :
    let j := n - seq.N (k - 1)
    let x := lemma3_case6_x seq k u
    let y := lemma3_case6_y seq k u j
    x ∈ seq.Q (k - 1) ∧ y ∈ seq.R (k - 1) ∧ x + y = n ∧ x ≤ y := by
      unfold NathansonSeq.Q NathansonSeq.R;
      rcases k with ( _ | _ | k ) <;> simp_all +arith +decide;
      unfold lemma3_case6_x lemma3_case6_y;
      refine' ⟨ _, _, _, _ ⟩;
      · exact ⟨ u, hu, rfl ⟩;
      · simp +zetaDelta at *;
        refine' ⟨ ⟨ _, _ ⟩, _ ⟩;
        · grind;
        · unfold NathansonSeq.N at *;
          have := seq.growth_bound ( k + 1 ) ( by linarith );
          norm_num at * ; nlinarith only [ this, hn_hi, hu, Nat.sub_add_cancel ( by linarith : 2 * seq.n ( k + 1 ) + 1 ≤ n ) ];
        · intro x hx₁ hx₂ hx₃;
          have h_j_bounds : 1 ≤ n - seq.N (k + 1) ∧ n - seq.N (k + 1) ≤ 2 * k + 2 := by
            omega;
          nlinarith only [ hu, hx₁, hx₂, hx₃, h_j_bounds, show x = u by nlinarith only [ hu, hx₁, hx₂, hx₃, h_j_bounds ] ];
      · zify;
        rw [ Nat.sub_sub, Nat.cast_sub ] <;> push_cast;
        · rw [ Nat.cast_sub ] <;> linarith [ show seq.N ( k + 1 ) = 2 * seq.n ( k + 1 ) + 1 from rfl ];
        · have := seq.exponential_growth ( k + 1 ) ( by linarith );
          nlinarith! [ seq.growth_bound ( k + 1 ) ( by linarith ) ];
      · grind

theorem lemma3_case6 (seq : NathansonSeq) (k : ℕ) (hk : k ≥ 3) (n : ℕ)
    (hn_lo : seq.N (k - 1) + 1 ≤ n)
    (hn_hi : n ≤ seq.N (k - 1) + 2 * k - 2) :
    k ≤ countReps (seq.Q (k - 1) ∪ seq.R (k - 1)) n := by
      have h_lemma3_case6 : ∀ u ∈ Finset.Icc 1 k, let j := n - seq.N (k - 1); let x := lemma3_case6_x seq k u; let y := lemma3_case6_y seq k u j; x ∈ seq.Q (k - 1) ∧ y ∈ seq.R (k - 1) ∧ x + y = n ∧ x ≤ y := by
        exact fun u a ↦
          let j := n - seq.N (k - 1);
          let x := seq.lemma3_case6_x k u;
          let y := seq.lemma3_case6_y k u j;
          lemma3_case6_valid seq k hk n hn_lo hn_hi u a;
      have h_image : Finset.image (fun u => (lemma3_case6_x seq k u, lemma3_case6_y seq k u (n - seq.N (k - 1)))) (Finset.Icc 1 k) ⊆ Finset.filter (fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ p.1 + p.2 = n ∧ p.1 ∈ seq.Q (k - 1) ∪ seq.R (k - 1) ∧ p.2 ∈ seq.Q (k - 1) ∪ seq.R (k - 1)) (Finset.product (seq.Q (k - 1) ∪ seq.R (k - 1)) (seq.Q (k - 1) ∪ seq.R (k - 1))) := by
        intro p hp
        aesop;
      refine' le_trans _ ( Finset.card_mono h_image );
      rw [ Finset.card_image_of_injOn ];
      · norm_num;
      · intros u hu v hv huv;
        simp_all +decide [ lemma3_case6_x, lemma3_case6_y ];
        grind

theorem lemma3_intervals_cover (seq : NathansonSeq) (k : ℕ) (hk : k ≥ 3) (n : ℕ)
    (hn_lo : seq.N (k - 1) + 1 ≤ n) (hn_hi : n ≤ seq.N k - 1) :
    (seq.N (k - 1) + 1 ≤ n ∧ n ≤ seq.N (k - 1) + 2 * k - 2) ∨
    (seq.N (k - 1) + 2 * k - 1 ≤ n ∧ n ≤ seq.N (k - 1) + seq.N (k - 2)) ∨
    (seq.N (k - 1) + seq.N (k - 2) + 1 ≤ n ∧ n ≤ 2 * seq.N (k - 1) + 2 * k - 1) ∨
    (2 * seq.N (k - 1) + 2 * k ≤ n ∧ n ≤ seq.N k - 2 * seq.N (k - 1) - 2 * k + 1) ∨
    (seq.N k - 2 * seq.N (k - 1) - 2 * k + 2 ≤ n ∧ n ≤ seq.N k - k) ∨
    (seq.N k - k + 1 ≤ n ∧ n ≤ seq.N k - 1) := by
      grind

theorem lemma3_part2 (seq : NathansonSeq) (k : ℕ) (hk : k ≥ 3) (n : ℕ)
    (hn_lo : seq.N (k - 1) + 1 ≤ n) (hn_hi : n ≤ seq.N k - 1) :
    k ≤ countReps (seq.B_k k ∪ seq.B_k (k - 1) ∪ seq.B_k (k - 2)) n := by
  have h_cases : (seq.N (k - 1) + 1 ≤ n ∧ n ≤ seq.N (k - 1) + 2 * k - 2) ∨
              (seq.N (k - 1) + 2 * k - 1 ≤ n ∧ n ≤ seq.N (k - 1) + seq.N (k - 2)) ∨
              (seq.N (k - 1) + seq.N (k - 2) + 1 ≤ n ∧ n ≤ 2 * seq.N (k - 1) + 2 * k - 1) ∨
              (2 * seq.N (k - 1) + 2 * k ≤ n ∧ n ≤ seq.N k - 2 * seq.N (k - 1) - 2 * k + 1) ∨
              (seq.N k - 2 * seq.N (k - 1) - 2 * k + 2 ≤ n ∧ n ≤ seq.N k - k) ∨
              (seq.N k - k + 1 ≤ n ∧ n ≤ seq.N k - 1) := by
                exact lemma3_intervals_cover seq k hk n hn_lo hn_hi;
  revert h_cases;
  norm_num +zetaDelta at *;
  intro h_cases
  cases' h_cases with h_case1 h_case2;
  · refine le_trans ( lemma3_case6 seq k hk n h_case1.1 h_case1.2 ) ?_;
    apply_rules [ countReps_mono ];
    unfold NathansonSeq.B_k; aesop_cat;
  · rcases h_case2 with ( h_case2 | h_case2 | h_case2 | h_case2 | h_case2 );
    · refine' le_trans _ ( countReps_mono ( show seq.S ( k - 1 ) ⊆ seq.B_k k ∪ ( seq.B_k ( k - 1 ) ∪ seq.B_k ( k - 2 ) ) from _ ) _ );
      · convert lemma3_case3 seq k hk n _ _;
        · omega;
        · linarith;
      · exact fun x hx => Finset.mem_union_right _ <| Finset.mem_union_left _ <| S_subset_B _ _ ( Nat.sub_pos_of_lt <| by linarith ) hx;
    · refine' le_trans _ ( countReps_mono _ _ );
      convert lemma3_case4 seq k hk n h_case2.1 h_case2.2 using 1;
      intro x hx; unfold NathansonSeq.B_k; aesop;
    · refine' le_trans ( lemma3_case1 seq k hk n h_case2.1 h_case2.2 ) _;
      apply_rules [ countReps_mono ];
      exact fun x hx => Finset.mem_union_left _ <| Finset.mem_union_left _ <| Finset.mem_union_left _ hx;
    · refine' le_trans _ ( countReps_mono _ _ );
      convert lemma3_case2 seq k hk n h_case2.1 h_case2.2 using 1;
      simp +decide [ Finset.subset_iff, NathansonSeq.B_k ];
      intro x hx; rcases hx with ( hx | hx ) <;> simp_all +decide [ NathansonSeq.T, NathansonSeq.R ] ;
      split_ifs at hx <;> simp_all +decide [ Nat.sub_sub ];
      exact Or.inr <| Or.inr <| Or.inl ⟨ by nlinarith only [ hx.1, hx.2, seq.n_pos k, seq.n_pos ( k - 1 ) ], fun u hu₁ hu₂ => by nlinarith only [ hx.1, hx.2, hu₁, hu₂ ] ⟩;
    · refine le_trans ( lemma3_case5 seq k hk n h_case2.1 h_case2.2 ) ?_;
      apply_rules [ countReps_mono ];
      unfold NathansonSeq.B_k; aesop_cat;

theorem lemma4_part1 (seq : NathansonSeq) (k : ℕ) :
    ∀ a b, seq.inB a → seq.inB b → a + b ≠ seq.N k := by
  intros a b ha hb hab
  apply (lemma3_part1 seq k) ⟨a, b, ha, hb, hab⟩

theorem lemma4_part2 (seq : NathansonSeq) (t : ℕ) :
    ∃ M, ∀ n ≥ M, (∀ k, n ≠ seq.N k) →
      ∃ j ≥ 3, t ≤ countReps (seq.B_k j ∪ seq.B_k (j - 1) ∪ seq.B_k (j - 2)) n := by
  norm_num +zetaDelta at *;
  use seq.N t + seq.N ( t + 1 ) + seq.N ( t + 2 ) + 1;
  intros n hn hn_ne_N
  obtain ⟨k, hk⟩ : ∃ k, n ∈ Finset.Icc (seq.N (k - 1) + 1) (seq.N k - 1) := by
    obtain ⟨k, hk⟩ : ∃ k, seq.N k ≤ n ∧ n < seq.N (k + 1) := by
      have h_finite : Set.Finite {k | n ≥ seq.N k} := by
        have h_finite : ∃ k₀, ∀ k ≥ k₀, n < seq.N k := by
          exact N_eventually_large seq n.succ;
        exact Set.finite_iff_bddAbove.mpr ⟨ h_finite.choose, fun k hk => not_lt.1 fun contra => not_le_of_gt ( h_finite.choose_spec k contra.le ) hk ⟩;
      contrapose! h_finite;
      exact Set.infinite_univ.mono fun k _ => Nat.recOn k ( by norm_num; linarith [ seq.N_mono_from_zero t, seq.N_mono_from_zero ( t + 1 ), seq.N_mono_from_zero ( t + 2 ) ] ) h_finite;
    use k + 1;
    exact Finset.mem_Icc.mpr ⟨ Nat.succ_le_of_lt ( lt_of_le_of_ne hk.1 ( Ne.symm ( hn_ne_N _ ) ) ), Nat.le_sub_one_of_lt hk.2 ⟩;
  have hk_ge_t3 : k ≥ t + 3 := by
    contrapose! hn;
    have hNk_le_Nt2 : seq.N k ≤ seq.N (t + 2) := by
      exact seq.N_mono_le ( by linarith );
    linarith [ Finset.mem_Icc.mp hk, Nat.sub_le ( seq.N k ) 1 ];
  have := lemma3_part2 seq k ( by linarith ) n ( Finset.mem_Icc.mp hk |>.1 ) ( Finset.mem_Icc.mp hk |>.2 );
  exact ⟨ k, by linarith, by simpa only [ ← Finset.union_assoc ] using by linarith ⟩

end NathansonSeq

variable (seq : NathansonSeq)

def NathansonSeq.BSet : Set ℕ := {x | seq.inB x}

lemma NathansonSeq.B_unbounded : ∀ M, ∃ x > M, seq.inB x := by
  have h_infinite : Set.Infinite seq.BSet := by
    have hB_nonempty : ∀ k ≥ 1, (seq.B_k k).Nonempty := by
      unfold NathansonSeq.B_k;
      unfold NathansonSeq.P NathansonSeq.Q NathansonSeq.R; aesop;
    have hB_infinite : ∀ M : ℕ, ∃ x ∈ seq.BSet, x > M := by
      intro M
      obtain ⟨k, hk⟩ : ∃ k ≥ 1, seq.N (k - 1) > M := by
        have := seq.N_unbounded M;
        exact ⟨ this.choose + 1, Nat.succ_pos _, by simpa using this.choose_spec ⟩;
      obtain ⟨ x, hx ⟩ := hB_nonempty k hk.1;
      exact ⟨ x, ⟨ k, hk.1, hx ⟩, by linarith [ seq.B_k_lower_bound k hk.1 x hx ] ⟩;
    exact Set.infinite_of_forall_exists_gt hB_infinite;
  exact fun M => by cases' h_infinite.exists_gt M with x hx; exact ⟨ x, hx.2, hx.1 ⟩ ;

def cumulativeCount (H : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | m + 1 => cumulativeCount H m + Nat.choose (H m) m

structure GrowingConstruction where
  seq : NathansonSeq
  a : ℕ → ℕ
  H : ℕ → ℕ
  F : ℕ → Finset ℕ
  stage : ℕ → ℕ
  a_in_B : ∀ i ≥ 1, seq.inB (a i)
  a_mono : ∀ i, a i < a (i + 1)
  a_covers : ∀ x, seq.inB x → ∃ i ≥ 1, a i = x
  H_mono : ∀ m, H m ≤ H (m + 1)
  H_unbounded : ∀ M, ∃ m, H m > M
  F_card : ∀ k ≥ 1, (F k).card = stage k
  F_subset : ∀ k ≥ 1, ∀ x ∈ F k, ∃ i, 1 ≤ i ∧ i ≤ H (stage k) ∧ a i = x
  stage_pos : ∀ k ≥ 1, stage k ≥ 1
  stage_unbounded : ∀ M, ∃ k₀, ∀ k ≥ k₀, stage k > M
  exhaustive : ∀ m ≥ 1, ∀ S : Finset ℕ,
    (∀ x ∈ S, ∃ i, 1 ≤ i ∧ i ≤ H m ∧ a i = x) → S.card = m →
    ∃ k, stage k = m ∧ F k = S
  F_lt_N_prev : ∀ k ≥ 2, ∀ x ∈ F k, x < seq.N (k - 1)
  k_grows_with_stage : ∀ m ≥ 1, ∃ k₀, ∀ k, stage k = m → k ≥ k₀
  stage_le_k : ∀ k ≥ 1, stage k ≤ k
  stage_zero : stage 0 = 0
  H_linear : ∀ m ≥ 1, H m ≥ 2 * m

namespace GrowingConstruction

variable (gc : GrowingConstruction)

lemma a_strict_mono_ge (i j : ℕ) (hi : i ≥ 1) (hj : j ≥ 1) (hij : i < j) :
    gc.a i < gc.a j := by
  exact strictMono_nat_of_lt_succ gc.a_mono hij

lemma F_lt_N (k : ℕ) (hk : k ≥ 2) (x : ℕ) (hx : x ∈ gc.F k) : x < gc.seq.N k := by
  have h_x_lt_Nk_minus_1 : x < gc.seq.N (k - 1) := by
    exact gc.F_lt_N_prev k hk x hx;
  exact h_x_lt_Nk_minus_1.trans_le ( Nat.le_of_lt ( gc.seq.N_strict_mono_lt ( Nat.sub_lt ( by linarith ) zero_lt_one ) ) )

def G (k : ℕ) : Finset ℕ :=
  gc.F k |>.image (fun f => gc.seq.N k - f)

lemma G_mem (k : ℕ) (g : ℕ) : g ∈ gc.G k ↔ ∃ f ∈ gc.F k, g = gc.seq.N k - f := by
  exact ⟨ fun h => by obtain ⟨ f, hf, rfl ⟩ := Finset.mem_image.mp h; exact ⟨ f, hf, rfl ⟩, fun h => by obtain ⟨ f, hf, rfl ⟩ := h; exact Finset.mem_image.mpr ⟨ f, hf, rfl ⟩ ⟩

def inA (x : ℕ) : Prop :=
  gc.seq.inB x ∨ ∃ k ≥ 2, x ∈ gc.G k

lemma G_range (k : ℕ) (hk : k ≥ 2) (g : ℕ) (hg : g ∈ gc.G k) :
    gc.seq.N k - gc.seq.N (k - 1) < g ∧ g < gc.seq.N k := by
  obtain ⟨f, hfF, rfl⟩ : ∃ f ∈ gc.F k, g = gc.seq.N k - f := by
    exact (G_mem gc k g).mp hg;
  constructor;
  · rw [ tsub_lt_tsub_iff_left_of_le ];
    · exact gc.F_lt_N_prev k hk f hfF;
    · exact gc.seq.N_mono_le ( Nat.pred_le _ );
  · apply Nat.sub_lt;
    · exact Nat.succ_pos _;
    · have := gc.F_subset k ( by linarith ) f hfF;
      obtain ⟨ i, hi₁, hi₂, rfl ⟩ := this;
      linarith [ gc.a_mono i, show gc.a i ≥ i from Nat.recOn i ( by linarith [ gc.a_mono 0 ] ) fun n ihn => by linarith [ gc.a_mono n ] ]

lemma G_disjoint_B (k : ℕ) (hk : k ≥ 2) : ∀ x ∈ gc.G k, ¬gc.seq.inB x := by
  intro x hx
  obtain ⟨f, hfF, rfl⟩ := G_mem gc k x |>.1 hx;
  have := gc.F_lt_N k hk f hfF;
  have h_not_in_B : ¬∃ a b : ℕ, gc.seq.inB a ∧ gc.seq.inB b ∧ a + b = gc.seq.N k := by
    exact NathansonSeq.lemma3_part1 gc.seq k;
  contrapose! h_not_in_B;
  exact ⟨ _, _, h_not_in_B, by
    have := gc.F_subset k ( by linarith ) f hfF;
    exact this.elim fun i hi => by simpa [ hi.2.2 ] using gc.a_in_B i hi.1;, Nat.sub_add_cancel this.le ⟩

lemma NathansonSeq.N_strong_growth (seq : NathansonSeq) (k : ℕ) (hk : k ≥ 1) :
    seq.N k ≥ 8 * seq.N (k - 1) - 7 := by
      have hN_def : seq.N k = 2 * seq.n k + 1 ∧ seq.N (k - 1) = 2 * seq.n (k - 1) + 1 := by
        exact ⟨ rfl, rfl ⟩;
      exact Nat.sub_le_of_le_add <| by linarith [ seq.exponential_growth k hk ] ;

lemma G_plus_G_ne_Nk (gc : GrowingConstruction) (k : ℕ) (hk : k ≥ 2) :
    ∀ i j, i ≥ 2 → j ≥ 2 → ∀ a ∈ gc.G i, ∀ b ∈ gc.G j, a + b ≠ gc.seq.N k := by
      intros i j hi hj a ha b hb hab
      by_cases h_cases : i = k ∨ j = k;
      · rcases h_cases with ( rfl | rfl );
        · obtain ⟨f_a, hf_a⟩ : ∃ f_a ∈ gc.F i, a = gc.seq.N i - f_a := by
            unfold GrowingConstruction.G at ha; aesop;
          have hb_in_B : b ∈ {x | gc.seq.inB x} := by
            have hb_in_B : b = f_a := by
              linarith [ Nat.sub_add_cancel ( show f_a ≤ gc.seq.N i from by linarith [ Nat.sub_add_cancel ( show f_a ≤ gc.seq.N i from by linarith [ Nat.sub_add_cancel ( show f_a ≤ gc.seq.N i from by linarith [ Nat.sub_add_cancel ( show f_a ≤ gc.seq.N i from by linarith [ Nat.sub_add_cancel ( show f_a ≤ gc.seq.N i from by linarith [ Nat.sub_add_cancel ( show f_a ≤ gc.seq.N i from by linarith [ Nat.sub_add_cancel ( show f_a ≤ gc.seq.N i from by linarith [ Nat.sub_add_cancel ( show f_a ≤ gc.seq.N i from by linarith [ Nat.sub_add_cancel ( show f_a ≤ gc.seq.N i from by linarith [ gc.F_lt_N i hi f_a hf_a.1 ] ) ] ) ] ) ] ) ] ) ] ) ] ) ] ) ] ) ];
            obtain ⟨ i, hi, hi' ⟩ := gc.F_subset i ( by linarith ) f_a hf_a.1;
            exact hb_in_B.symm ▸ hi'.2 ▸ gc.a_in_B i hi;
          exact False.elim ( gc.G_disjoint_B _ hj _ hb hb_in_B );
        · obtain ⟨f_b, hf_b⟩ : ∃ f_b ∈ gc.F j, b = gc.seq.N j - f_b := by
            exact (G_mem gc j b).mp hb;
          have h_contradiction : f_b ∈ gc.G i := by
            have h_contradiction : a = f_b := by
              linarith [ Nat.sub_add_cancel ( show f_b ≤ gc.seq.N j from le_of_lt ( by { have := G_range gc j hj b hb; omega } ) ) ];
            aesop;
          have h_contradiction : ¬gc.seq.inB f_b := by
            exact fun h => gc.G_disjoint_B i hi f_b h_contradiction h;
          have h_contradiction : ∃ i ≥ 1, gc.a i = f_b := by
            have := gc.F_subset j ( by linarith ) f_b hf_b.1; aesop;
          exact ‹¬gc.seq.inB f_b› ( by obtain ⟨ i, hi, rfl ⟩ := h_contradiction; exact gc.a_in_B i hi );
      · by_cases h_cases : i > k ∨ j > k;
        · cases' h_cases with h_cases h_cases;
          · have h_a_gt_Ni_minus_Nip1 : a > gc.seq.N i - gc.seq.N (i - 1) := by
              exact G_range gc i hi a ha |>.1;
            have h_Ni_ge_8Nip1_minus_7 : gc.seq.N i ≥ 8 * gc.seq.N (i - 1) - 7 := by
              convert Nat.sub_le_of_le_add _;
              have := gc.seq.exponential_growth i ( by linarith );
              unfold NathansonSeq.N at * ; linarith;
            have h_Nip1_ge_Nk : gc.seq.N (i - 1) ≥ gc.seq.N k := by
              exact gc.seq.N_mono_le ( Nat.le_sub_one_of_lt h_cases );
            have h_7Nk_minus_7_gt_Nk : 7 * gc.seq.N k - 7 > gc.seq.N k := by
              exact lt_tsub_iff_left.mpr ( by linarith [ show gc.seq.N k ≥ 3 by exact Nat.succ_le_of_lt ( by linarith [ show gc.seq.N k ≥ 3 by exact Nat.succ_le_of_lt ( by linarith [ show gc.seq.N k ≥ 3 by exact Nat.succ_le_of_lt ( by linarith [ show gc.seq.n k ≥ 1 by exact gc.seq.n_pos k, show gc.seq.n ( k - 1 ) ≥ 1 by exact gc.seq.n_pos ( k - 1 ), show gc.seq.N k = 2 * gc.seq.n k + 1 by rfl ] ) ] ) ] ) ] );
            omega;
          · have hb_gt : b > gc.seq.N j - gc.seq.N (j - 1) := by
              have := gc.G_range j hj b hb; aesop;
            have hN_j_ge : gc.seq.N j ≥ 8 * gc.seq.N (j - 1) - 7 := by
              apply NathansonSeq.N_strong_growth;
              linarith;
            have hN_j_ge_N_k : gc.seq.N j ≥ gc.seq.N k + 1 := by
              exact Nat.succ_le_of_lt ( Nat.lt_of_le_of_lt ( Nat.le_refl _ ) ( Nat.succ_le_of_lt ( gc.seq.N_strict_mono_lt ( Nat.lt_of_le_of_lt ( Nat.le_refl _ ) h_cases ) ) ) );
            have hN_j_minus_1_ge_N_k : gc.seq.N (j - 1) ≥ gc.seq.N k := by
              exact gc.seq.N_mono_le ( Nat.le_sub_one_of_lt h_cases );
            omega;
        · have h_bounds : a < gc.seq.N (k - 1) ∧ b < gc.seq.N (k - 1) := by
            have h_bounds : a < gc.seq.N i ∧ b < gc.seq.N j := by
              exact ⟨ G_range gc i hi a ha |>.2, G_range gc j hj b hb |>.2 ⟩;
            exact ⟨ lt_of_lt_of_le h_bounds.1 ( gc.seq.N_mono_le ( Nat.le_sub_one_of_lt ( lt_of_le_of_ne ( le_of_not_gt fun hi' => h_cases <| Or.inl hi' ) ( by tauto ) ) ) ), lt_of_lt_of_le h_bounds.2 ( gc.seq.N_mono_le ( Nat.le_sub_one_of_lt ( lt_of_le_of_ne ( le_of_not_gt fun hj' => h_cases <| Or.inr hj' ) ( by tauto ) ) ) ) ⟩;
          have h_contradiction : gc.seq.N k ≥ 8 * gc.seq.N (k - 1) - 7 := by
            apply NathansonSeq.N_strong_growth;
            linarith;
          omega

lemma B_plus_G_ne_Nk (gc : GrowingConstruction) (k : ℕ) (hk : k ≥ 2) :
    ∀ a b, gc.seq.inB a → (∃ j ≥ 2, j ≠ k ∧ b ∈ gc.G j) → a + b ≠ gc.seq.N k := by
      intros a b ha hb
      obtain ⟨j, hj_ge_2, hj_ne_k, hb_g⟩ := hb;
      by_cases hj_gt_k : j > k;
      · have := gc.G_range j ( by linarith ) b hb_g;
        have h_N_j_ge : gc.seq.N j ≥ 8 * gc.seq.N (j - 1) - 7 := by
          apply NathansonSeq.N_strong_growth;
          grind;
        have h_N_j_minus_1_ge_N_k : gc.seq.N (j - 1) ≥ gc.seq.N k := by
          exact gc.seq.N_mono_le ( Nat.le_sub_one_of_lt hj_gt_k );
        omega;
      · have hb_lt_Nk_minus_1 : b < gc.seq.N (k - 1) := by
          have := gc.G_range j hj_ge_2 b hb_g;
          exact this.2.trans_le ( Nat.le_induction ( by aesop ) ( fun m hm ih => by exact le_trans ih <| by simpa using Nat.le_of_lt <| gc.seq.N_strict_mono m ) _ <| Nat.le_sub_one_of_lt <| lt_of_le_of_ne ( le_of_not_gt hj_gt_k ) hj_ne_k );
        obtain ⟨m, hm_ge_1, hm⟩ : ∃ m ≥ 1, a ∈ gc.seq.B_k m := by
          cases ha ; aesop;
        by_cases hm_gt_k : m > k;
        · have := gc.seq.B_j_gt_N_k m k hm_gt_k hm_ge_1 a hm;
          grind;
        · have ha_le_nk_plus_Nk_minus_1 : a ≤ gc.seq.n k + gc.seq.N (k - 1) := by
            have ha_le_nk_plus_Nk_minus_1 : a ≤ gc.seq.n m + gc.seq.N (m - 1) := by
              exact gc.seq.B_k_upper_bound m hm_ge_1 a hm;
            exact le_trans ha_le_nk_plus_Nk_minus_1 ( add_le_add ( gc.seq.n_mono_le ( by linarith ) ) ( gc.seq.N_mono_le ( by omega ) ) );
          have h_ineq : gc.seq.n k + 2 * gc.seq.N (k - 1) < gc.seq.N k := by
            unfold NathansonSeq.N at *;
            linarith [ gc.seq.exponential_growth k ( by linarith ), gc.seq.n_pos ( k - 1 ), gc.seq.n_pos k ];
          linarith

lemma N_representations (k : ℕ) (hk : k ≥ 2) :
    ∀ a b, gc.inA a → gc.inA b → a + b = gc.seq.N k →
      a ∈ gc.F k ∧ b ∈ gc.G k ∨ a ∈ gc.G k ∧ b ∈ gc.F k := by
  intro a b ha hb hab
  cases' ha with ha ha_cases
  cases' hb with hb hb_cases;
  · exact False.elim <| gc.seq.lemma4_part1 k a b ha hb hab;
  · obtain ⟨ j, hj, hb ⟩ := hb_cases;
    by_cases hjk : j = k;
    · obtain ⟨f, hfF, hf⟩ : ∃ f ∈ gc.F k, b = gc.seq.N k - f := by
        unfold GrowingConstruction.G at hb; aesop;
      simp_all +decide [ Nat.sub_sub_self ( show f ≤ gc.seq.N k from le_of_lt ( gc.F_lt_N k hk f hfF ) ) ];
      exact Or.inl ( by convert hfF using 1; linarith [ Nat.sub_add_cancel ( show f ≤ gc.seq.N k from le_of_lt ( gc.F_lt_N k hk f hfF ) ) ] );
    · exact False.elim ( GrowingConstruction.B_plus_G_ne_Nk gc k hk a b ha ⟨ j, hj, hjk, hb ⟩ hab );
  · cases' hb with hb hb_cases;
    · rcases ha_cases with ⟨ j, hj, hj' ⟩;
      by_cases hjk : j = k;
      · obtain ⟨ f, hfF, hf ⟩ : ∃ f ∈ gc.F k, a = gc.seq.N k - f := by
          unfold GrowingConstruction.G at hj'; aesop;
        exact Or.inr ⟨ by aesop, by convert hfF using 1; rw [ eq_tsub_iff_add_eq_of_le ] at hf <;> linarith [ Nat.sub_add_cancel ( show f ≤ gc.seq.N k from by linarith [ gc.F_lt_N k hk f hfF ] ) ] ⟩;
      · exact False.elim <| GrowingConstruction.B_plus_G_ne_Nk gc k hk b a hb ⟨ j, hj, hjk, hj' ⟩ <| by linarith;
    · obtain ⟨ i, hi, hi' ⟩ := ha_cases
      obtain ⟨ j, hj, hj' ⟩ := hb_cases
      by_cases h_cases : i = k ∧ j = k;
      · simp_all +decide [ GrowingConstruction.G ];
        obtain ⟨ x, hx, rfl ⟩ := hi'
        obtain ⟨ y, hy, rfl ⟩ := hj';
        have h_eq : x = gc.seq.N k - y ∧ y = gc.seq.N k - x := by
          have h_eq : x + y = gc.seq.N k := by
            linarith [ Nat.sub_add_cancel ( show x ≤ gc.seq.N k from le_of_lt ( gc.F_lt_N k hk x hx ) ), Nat.sub_add_cancel ( show y ≤ gc.seq.N k from le_of_lt ( gc.F_lt_N k hk y hy ) ) ];
          exact ⟨ by rw [ ← h_eq, Nat.add_sub_cancel ], by rw [ ← h_eq, Nat.add_sub_cancel_left ] ⟩;
        exact Or.inl ( h_eq.2 ▸ hy );
      · have h_contradiction : a ∈ gc.G i ∧ b ∈ gc.G j → a + b ≠ gc.seq.N k := by
          intro h_pair
          apply GrowingConstruction.G_plus_G_ne_Nk;
          exacts [ hk, hi, hj, h_pair.1, h_pair.2 ];
        aesop

theorem rep_count_Nk (k : ℕ) (hk : k ≥ 2) :
    ∃ pairs : Finset (ℕ × ℕ),
      pairs.card = gc.stage k ∧
      ∀ p ∈ pairs, gc.inA p.1 ∧ gc.inA p.2 ∧ p.1 + p.2 = gc.seq.N k ∧ p.1 ≤ p.2 := by
  have hF_card : (gc.F k).card = gc.stage k := by
    exact gc.F_card k ( by linarith );
  have h_pairs : ∀ f ∈ gc.F k, gc.inA f ∧ gc.inA (gc.seq.N k - f) ∧ f + (gc.seq.N k - f) = gc.seq.N k ∧ f ≤ gc.seq.N k - f := by
    intro f hf
    have h_f_in_A : gc.inA f := by
      apply Or.inl; exact (by
      have := gc.F_subset k ( by linarith ) f hf;
      exact this.elim fun i hi => hi.2.2 ▸ gc.a_in_B i hi.1)
    have h_Nk_minus_f_in_A : gc.inA (gc.seq.N k - f) := by
      exact Or.inr ⟨ k, hk, Finset.mem_image_of_mem _ hf ⟩
    have h_sum : f + (gc.seq.N k - f) = gc.seq.N k := by
      rw [ Nat.add_sub_of_le ];
      exact le_of_lt ( gc.F_lt_N k hk f hf )
    have h_le : f ≤ gc.seq.N k - f := by
      have h_f_lt_Nk_minus_f : f < gc.seq.N (k - 1) := by
        exact gc.F_lt_N_prev k hk f hf;
      have h_Nk_ge_2Nk_minus_1 : gc.seq.N k ≥ 2 * gc.seq.N (k - 1) + 1 := by
        unfold NathansonSeq.N;
        have := gc.seq.exponential_growth k ( by linarith );
        linarith [ gc.seq.n_pos ( k - 1 ) ];
      omega
    exact ⟨h_f_in_A, h_Nk_minus_f_in_A, h_sum, h_le⟩;
  use Finset.image (fun f => (f, gc.seq.N k - f)) (gc.F k);
  rw [ Finset.card_image_of_injective ] <;> aesop_cat

lemma stage_ensures_large_N (N₀ : ℕ) :
    ∃ m₀ ≥ 2, ∀ m ≥ m₀, ∀ k, gc.stage k = m → gc.seq.N k ≥ N₀ := by
  have h_stage_growth : ∀ m₀, ∃ m₁ ≥ m₀, ∀ k, k ≥ m₁ → gc.seq.N k ≥ N₀ := by
    have := gc.seq.N_unbounded N₀;
    exact fun m₀ => by obtain ⟨ k, hk ⟩ := this; exact ⟨ k + m₀, by linarith, fun n hn => le_trans ( le_of_lt hk ) ( by exact Nat.le_induction ( by linarith ) ( fun n hn ih => by linarith [ gc.seq.N_strict_mono n ] ) _ ( show n ≥ k by linarith ) ) ⟩ ;
  obtain ⟨ m₁, hm₁, hm₁' ⟩ := h_stage_growth 2;
  exact ⟨ m₁, hm₁, fun m hm k hk => hm₁' k <| by linarith [ hk ▸ gc.stage_le_k k ( show k ≥ 1 from Nat.pos_of_ne_zero fun h => by subst h; linarith [ gc.stage_zero ] ) ] ⟩

lemma Nk_rep_needs_Fk (k : ℕ) (hk : k ≥ 2) (B' : Set ℕ)
    (hB'_sub : ∀ x ∈ B', gc.inA x)
    (hrep : ∃ a ∈ B', ∃ b ∈ B', a + b = gc.seq.N k) :
    ∃ f ∈ gc.F k, f ∈ B' := by
  obtain ⟨ a, ha, b, hb, hab ⟩ := hrep;
  have := gc.N_representations k hk a b ?_ ?_ ?_ <;> aesop

lemma exists_disjoint_gadget (gc : GrowingConstruction) (S₀ : Finset ℕ) (hS₀ : ∀ x ∈ S₀, gc.seq.inB x) :
    ∃ m₀, ∀ m ≥ m₀, ∃ k, gc.stage k = m ∧ Disjoint (gc.F k) S₀ := by
      obtain ⟨L, hL⟩ : ∃ L, ∀ x ∈ S₀, ∃ i ∈ Finset.Icc 1 L, gc.a i = x := by
        choose! f hf using fun x hx => gc.a_covers x ( hS₀ x hx );
        exact ⟨ Finset.sup S₀ f, fun x hx => ⟨ f x, Finset.mem_Icc.mpr ⟨ hf x hx |>.1, Finset.le_sup ( f := f ) hx ⟩, hf x hx |>.2 ⟩ ⟩;
      use L + 1;
      intros m hm
      obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S ⊆ Finset.image gc.a (Finset.Icc 1 (gc.H m)) ∧ S.card = m ∧ Disjoint S S₀ := by
        have h_subset : (Finset.image gc.a (Finset.Icc 1 (gc.H m))).card ≥ m + S₀.card := by
          rw [ Finset.card_image_of_injOn ];
          · have h_card : S₀.card ≤ L := by
              have hL_card : S₀.card ≤ Finset.card (Finset.image (fun i => gc.a i) (Finset.Icc 1 L)) := by
                exact Finset.card_le_card fun x hx => by obtain ⟨ i, hi, rfl ⟩ := hL x hx; exact Finset.mem_image_of_mem _ hi;
              exact hL_card.trans ( Finset.card_image_le.trans ( by simp ) );
            have := gc.H_linear m ( by linarith ) ; norm_num at * ; linarith;
          · exact ( StrictMonoOn.injOn <| fun i hi j hj hij => by exact gc.a_strict_mono_ge i j ( Finset.mem_Icc.mp hi |>.1 ) ( Finset.mem_Icc.mp hj |>.1 ) hij );
        have h_subset : (Finset.image gc.a (Finset.Icc 1 (gc.H m)) \ S₀).card ≥ m := by
          rw [ Finset.card_sdiff ];
          exact le_tsub_of_add_le_left ( by linarith [ show Finset.card ( S₀ ∩ Finset.image gc.a ( Finset.Icc 1 ( gc.H m ) ) ) ≤ S₀.card from Finset.card_le_card fun x hx => by aesop ] );
        obtain ⟨ S, hS ⟩ := Finset.exists_subset_card_eq h_subset;
        exact ⟨ S, Finset.Subset.trans hS.1 ( Finset.sdiff_subset ), hS.2, Finset.disjoint_left.mpr fun x hxS hxS₀ => Finset.mem_sdiff.mp ( hS.1 hxS ) |>.2 hxS₀ ⟩;
      obtain ⟨k, hk⟩ : ∃ k, gc.stage k = m ∧ gc.F k = S := by
        have := gc.exhaustive m ( by linarith ) S;
        exact this ( fun x hx => by have := hS.1 hx; aesop ) hS.2.1;
      aesop

lemma F_intersects_basis (gc : GrowingConstruction) (B' C' : Set ℕ)
    (hpart : ∀ x, gc.inA x ↔ x ∈ B' ∨ x ∈ C')
    (hB'_basis : ∀ᶠ n in Filter.atTop, ∃ a ∈ B', ∃ b ∈ B', a + b = n) :
    ∃ k₀, ∀ k ≥ k₀, ∃ f ∈ gc.F k, f ∈ B' := by
      obtain ⟨M, hM⟩ : ∃ M, ∀ n ≥ M, ∃ a ∈ B', ∃ b ∈ B', a + b = n := by
        exact Filter.eventually_atTop.mp hB'_basis;
      obtain ⟨k₀, hk₀⟩ : ∃ k₀, ∀ k ≥ k₀, gc.seq.N k ≥ M := by
        exact NathansonSeq.N_eventually_large gc.seq M;
      exact ⟨ k₀ + 2, fun k hk => by obtain ⟨ a, ha, b, hb, hab ⟩ := hM _ ( hk₀ _ ( by linarith ) ) ; exact gc.Nk_rep_needs_Fk k ( by linarith ) B' ( fun x hx => by specialize hpart x; aesop ) ⟨ a, ha, b, hb, hab ⟩ ⟩

lemma intersection_infinite (B' C' : Set ℕ)
    (hpart : ∀ x, gc.inA x ↔ x ∈ B' ∨ x ∈ C')
    (hdisj : Disjoint B' C')
    (hB'_basis : ∀ᶠ n in Filter.atTop, ∃ a ∈ B', ∃ b ∈ B', a + b = n) :
    Set.Infinite (B' ∩ {x | gc.seq.inB x}) := by
  by_contra hS_finite
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, ∀ k ≥ k₀, ∃ f ∈ gc.F k, f ∈ B' := by
    have hF_intersects_basis : ∃ k₀, ∀ k ≥ k₀, ∃ f ∈ gc.F k, f ∈ B' := by
      have hB'_basis : ∀ᶠ n in Filter.atTop, ∃ a ∈ B', ∃ b ∈ B', a + b = n := hB'_basis
      (expose_names; exact GrowingConstruction.F_intersects_basis gc B' C' hpart hB'_basis_1);
    exact hF_intersects_basis;
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, ∀ m ≥ m₀, ∃ k, gc.stage k = m ∧ Disjoint (gc.F k) (Set.Finite.toFinset (Set.not_infinite.mp hS_finite)) := by
    apply GrowingConstruction.exists_disjoint_gadget;
    aesop;
  obtain ⟨ k, hk₁, hk₂ ⟩ := hm₀ ( m₀ + k₀ + 1 ) ( by linarith );
  obtain ⟨ f, hf₁, hf₂ ⟩ := hk₀ k ( by linarith [ gc.stage_le_k k ( show k ≥ 1 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ gc.stage_zero ] ) ) ] ) ; simp_all +decide [ Set.disjoint_left ] ;
  simp_all +decide [ Finset.disjoint_left, Set.disjoint_left ];
  have hf_in_B : gc.seq.inB f := by
    obtain ⟨ i, hi₁, hi₂, rfl ⟩ := gc.F_subset k ( show k ≥ 1 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ gc.stage_zero ] ) ) f hf₁; exact gc.a_in_B i hi₁;
  exact hk₂ hf₁ hf₂ hf_in_B

lemma impossible_rep (gc : GrowingConstruction) (k : ℕ) (hk : k ≥ 2) (B' C' : Set ℕ)
    (hdisj : Disjoint B' C') (hC_sub : C' ⊆ {x | gc.inA x}) (hF : ↑(gc.F k) ⊆ B') :
    ¬∃ x ∈ C', ∃ y ∈ C', x + y = gc.seq.N k := by
      rintro ⟨ x, hx, y, hy, hxy ⟩;
      have := gc.N_representations k hk x y; simp_all +decide [ Set.disjoint_left ] ;
      cases this ( hC_sub hx ) ( hC_sub hy ) <;> simp_all +decide [ Set.subset_def ]

lemma exists_bad_k (m : ℕ) (hm : m ≥ 1) (B' C' : Set ℕ)
    (hpart : ∀ x, gc.inA x ↔ x ∈ B' ∨ x ∈ C')
    (hdisj : Disjoint B' C') :
    ∃ k, gc.stage k = m ∧ ((↑(gc.F k) ⊆ B') ∨ (↑(gc.F k) ⊆ C')) := by
      have := gc.H_linear m hm;
      have h_case : Set.ncard {x | ∃ i, 1 ≤ i ∧ i ≤ gc.H m ∧ gc.a i = x ∧ gc.a i ∈ B'} ≥ m ∨ Set.ncard {x | ∃ i, 1 ≤ i ∧ i ≤ gc.H m ∧ gc.a i = x ∧ gc.a i ∈ C'} ≥ m := by
        have h_card_union : Set.ncard {x | ∃ i, 1 ≤ i ∧ i ≤ gc.H m ∧ gc.a i = x ∧ gc.a i ∈ B'} + Set.ncard {x | ∃ i, 1 ≤ i ∧ i ≤ gc.H m ∧ gc.a i = x ∧ gc.a i ∈ C'} ≥ Set.ncard {x | ∃ i, 1 ≤ i ∧ i ≤ gc.H m ∧ gc.a i = x} := by
          have h_card_union : Set.ncard {x | ∃ i, 1 ≤ i ∧ i ≤ gc.H m ∧ gc.a i = x} ≤ Set.ncard ({x | ∃ i, 1 ≤ i ∧ i ≤ gc.H m ∧ gc.a i = x ∧ gc.a i ∈ B'} ∪ {x | ∃ i, 1 ≤ i ∧ i ≤ gc.H m ∧ gc.a i = x ∧ gc.a i ∈ C'}) := by
            apply Set.ncard_le_ncard;
            · intro x hx
              obtain ⟨i, hi1, hi2, hi3⟩ := hx
              have h_in_B_or_C : gc.a i ∈ B' ∨ gc.a i ∈ C' := by
                exact hpart _ |>.1 ( by exact Or.inl <| gc.a_in_B i hi1 );
              grind;
            · exact Set.Finite.subset ( Set.toFinite ( Finset.image ( fun i => gc.a i ) ( Finset.Icc 1 ( gc.H m ) ) ) ) fun x hx => by aesop;
          exact h_card_union.trans ( Set.ncard_union_le _ _ );
        have h_card_union : Set.ncard {x | ∃ i, 1 ≤ i ∧ i ≤ gc.H m ∧ gc.a i = x} ≥ 2 * m := by
          have h_card_union : Set.ncard {x | ∃ i, 1 ≤ i ∧ i ≤ gc.H m ∧ gc.a i = x} = Set.ncard (Set.image gc.a (Set.Icc 1 (gc.H m))) := by
            exact congr_arg _ ( by ext; aesop );
          rw [ h_card_union, Set.ncard_image_of_injective ];
          · norm_num [ Set.ncard_eq_toFinset_card' ] ; linarith;
          · exact ( StrictMono.injective <| strictMono_nat_of_lt_succ fun i => gc.a_mono i );
        contrapose! h_card_union; linarith;
      cases' h_case with h_case h_case;
      · obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S.card = m ∧ ∀ x ∈ S, ∃ i, 1 ≤ i ∧ i ≤ gc.H m ∧ gc.a i = x ∧ gc.a i ∈ B' := by
          obtain ⟨ S, hS ⟩ := Set.exists_subset_card_eq h_case;
          cases' Set.Finite.exists_finset_coe ( show Set.Finite S from Set.finite_of_ncard_pos ( by linarith ) ) ; aesop;
        have := gc.exhaustive m hm S ( fun x hx => by obtain ⟨ i, hi₁, hi₂, rfl, hi₃ ⟩ := hS.2 x hx; exact ⟨ i, hi₁, hi₂, rfl ⟩ ) hS.1;
        grind;
      · obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S.card = m ∧ ∀ x ∈ S, ∃ i, 1 ≤ i ∧ i ≤ gc.H m ∧ gc.a i = x ∧ gc.a i ∈ C' := by
          obtain ⟨ S, hS ⟩ := Set.exists_subset_card_eq h_case;
          cases' Set.Finite.exists_finset_coe ( show Set.Finite S from Set.finite_of_ncard_pos ( by linarith ) ) ; aesop;
        obtain ⟨k, hk⟩ : ∃ k, gc.stage k = m ∧ gc.F k = S := by
          have := gc.exhaustive m hm S;
          exact this ( fun x hx => by obtain ⟨ i, hi₁, hi₂, hi₃, hi₄ ⟩ := hS.2 x hx; exact ⟨ i, hi₁, hi₂, hi₃ ⟩ ) hS.1;
        grind

theorem non_decomposable :
    ¬∃ (B' C' : Set ℕ),
      (∀ x, gc.inA x ↔ x ∈ B' ∨ x ∈ C') ∧
      Disjoint B' C' ∧
      (∀ᶠ n in Filter.atTop, ∃ a ∈ B', ∃ b ∈ B', a + b = n) ∧
      (∀ᶠ n in Filter.atTop, ∃ a ∈ C', ∃ b ∈ C', a + b = n) := by
  intro h
  obtain ⟨B', C', h_partition, h_disjoint, h_B', h_C'⟩ := h
  have h_inf_B' : Set.Infinite (B' ∩ {x | gc.seq.inB x}) := by
    exact intersection_infinite gc B' C' h_partition h_disjoint h_B';
  obtain ⟨N_max, hN_max⟩ : ∃ N_max, (∀ n ≥ N_max, ∃ a ∈ B', ∃ b ∈ B', a + b = n) ∧ (∀ n ≥ N_max, ∃ a ∈ C', ∃ b ∈ C', a + b = n) := by
    simp +zetaDelta at *;
    exact ⟨ Max.max h_B'.choose h_C'.choose, fun n hn => h_B'.choose_spec n ( le_trans ( le_max_left _ _ ) hn ), fun n hn => h_C'.choose_spec n ( le_trans ( le_max_right _ _ ) hn ) ⟩;
  obtain ⟨m₀, hm₀_ge_2, hm₀⟩ : ∃ m₀ ≥ 2, ∀ m ≥ m₀, ∀ k, gc.stage k = m → gc.seq.N k ≥ N_max := by
    exact stage_ensures_large_N gc N_max;
  obtain ⟨k, hk_stage, hk_subset⟩ : ∃ k, gc.stage k = m₀ ∧ ((↑(gc.F k) ⊆ B') ∨ (↑(gc.F k) ⊆ C')) := by
    exact Exists.imp ( by aesop ) ( exists_bad_k gc m₀ ( by linarith ) B' C' h_partition h_disjoint );
  cases' hk_subset with hk_subset hk_subset;
  · have h_impossible_rep : ¬∃ x ∈ C', ∃ y ∈ C', x + y = gc.seq.N k := by
      apply impossible_rep gc k (by
      linarith [ gc.stage_le_k k ( show k ≥ 1 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ gc.stage_zero ] ) ) ]) B' C' h_disjoint (by
      exact fun x hx => h_partition x |>.2 <| Or.inr hx) hk_subset;
    exact h_impossible_rep <| hN_max.2 _ <| hm₀ _ le_rfl _ hk_stage;
  · have h_impossible_rep : ¬∃ x ∈ B', ∃ y ∈ B', x + y = gc.seq.N k := by
      apply impossible_rep;
      any_goals tauto;
      · linarith [ gc.stage_le_k k ( by linarith [ show k ≥ 1 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ gc.stage_zero ] ) ] ) ];
      · exact fun x hx => h_partition x |>.2 ( Or.inl hx );
    exact h_impossible_rep <| hN_max.1 _ <| hm₀ _ ( by linarith ) _ hk_stage

end GrowingConstruction

open NathansonSeq GrowingConstruction

def concreteN (k : ℕ) : ℕ := 100 * 8^k

lemma concreteN_pos : ∀ k, 0 < concreteN k := by
  intro k
  apply mul_pos
  norm_num
  apply pow_pos
  norm_num

lemma concreteN_mono : ∀ k, concreteN k ≤ concreteN (k + 1) := by
  intro k
  simp [concreteN];
  norm_num [pow_succ']

lemma concreteN_growth_bound : ∀ k ≥ 1, concreteN (k - 1) ≥ 3 * k^2 + 6 * k + 1 := by
  intro k hk
  induction' hk with k ih;
  · decide;
  · simp [concreteN];
    exact Nat.recOn k ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at * ; nlinarith

lemma concreteN_exponential_growth : ∀ k ≥ 1, concreteN k ≥ 8 * concreteN (k - 1) := by
  simp [concreteN];
  intro k hk
  rw [show 8^k = 8 * 8^(k-1) by rw [← pow_succ', Nat.sub_add_cancel hk]]
  linarith

def concreteSeq : NathansonSeq where
  n := concreteN
  n_pos := concreteN_pos
  n_mono := concreteN_mono
  growth_bound := concreteN_growth_bound
  exponential_growth := concreteN_exponential_growth

def simpleH (m : ℕ) : ℕ := 2 * m

lemma simpleH_mono : ∀ m, simpleH m ≤ simpleH (m + 1) := by
  simp [simpleH]

lemma simpleH_unbounded : ∀ M, ∃ m, simpleH m > M := by
  intro M
  use M + 1
  simp [simpleH];
  linarith

lemma simpleH_linear : ∀ m ≥ 1, simpleH m ≥ 2 * m := fun _ _ => le_refl _

def inB_concrete (x : ℕ) : Prop := concreteSeq.inB x

lemma B_has_next (M : ℕ) : ∃ x, x > M ∧ inB_concrete x := by
  exact B_unbounded concreteSeq M

noncomputable instance (M x : ℕ) : Decidable (x > M ∧ inB_concrete x) := Classical.propDecidable _

noncomputable def nextInB (M : ℕ) : ℕ :=
  Nat.find (B_has_next M)

lemma nextInB_gt (M : ℕ) : nextInB M > M := (Nat.find_spec (B_has_next M)).1

lemma nextInB_in_B (M : ℕ) : inB_concrete (nextInB M) := (Nat.find_spec (B_has_next M)).2

noncomputable def enumerateB : ℕ → ℕ
  | 0 => 0  
  | n + 1 => nextInB (enumerateB n)

lemma enumerateB_zero : enumerateB 0 = 0 := rfl

lemma enumerateB_mono (n : ℕ) : enumerateB n < enumerateB (n + 1) := by
  apply nextInB_gt

lemma enumerateB_in_B (n : ℕ) (hn : n ≥ 1) : inB_concrete (enumerateB n) := by
  induction' n with n ih;
  · grind;
  · apply nextInB_in_B

lemma enumerateB_covers (x : ℕ) (hx : inB_concrete x) : ∃ n ≥ 1, enumerateB n = x := by
  obtain ⟨n, hn⟩ : ∃ n, x = enumerateB n := by
    contrapose! hx;
    intro H;
    obtain ⟨n, hn⟩ : ∃ n, enumerateB n > x := by
      exact ⟨ x + 1, Nat.recOn x ( by linarith! [ enumerateB_mono 0 ] ) fun n ihn => by linarith! [ enumerateB_mono ( n + 1 ) ] ⟩;
    induction' n with n ih;
    · exact hn.not_ge ( Nat.zero_le _ );
    · simp +zetaDelta at *;
      exact hn.not_ge ( Nat.find_min' ( B_has_next ( enumerateB n ) ) ⟨ ih.lt_of_ne ( Ne.symm <| hx _ ), H ⟩ );
  induction' n with n ih;
  · cases hx;
    rename_i k hk;
    unfold NathansonSeq.B_k at hk;
    unfold NathansonSeq.P NathansonSeq.Q NathansonSeq.R at hk;
    split_ifs at hk <;> simp_all +arith +decide;
    unfold enumerateB at hk; aesop;
  · exact ⟨ n + 1, Nat.succ_pos _, hn.symm ⟩

def K (m : ℕ) : ℕ := cumulativeCount simpleH m

lemma K_zero : K 0 = 0 := rfl

lemma K_one : K 1 = 0 := rfl

lemma K_succ (m : ℕ) (hm : m ≥ 1) : K (m + 1) = K m + Nat.choose (simpleH m) m := by
  cases m <;> trivial

lemma K_mono (m : ℕ) : K m ≤ K (m + 1) := by
  induction m <;> simp +arith +decide [ *, Nat.choose ];
  exact Nat.le_add_right _ _

lemma K_mono_le {a b : ℕ} (hab : a ≤ b) : K a ≤ K b := by
  exact monotone_nat_of_le_succ K_mono hab

noncomputable def stageAssign (k : ℕ) : ℕ :=
  if hk : k = 0 then 0
  else Nat.find (exists_stage k (Nat.one_le_iff_ne_zero.mpr hk))

where
  exists_stage (k : ℕ) (hk_pos : k ≥ 1) : ∃ m, K m < k ∧ k ≤ K (m + 1) := by
    have hK_grows : ∀ m, K m ≤ K (m + 1) := K_mono
    have hK_strict : ∀ m ≥ 1, K (m + 1) ≥ K m + 2 := by
      intro m hm
      rw [K_succ _ hm]
      simp only [simpleH]
      have hchoose : Nat.choose (2 * m) m ≥ 2 := by
        cases m with
        | zero => omega
        | succ m =>
          have h : Nat.choose (2 * (m + 1)) (m + 1) ≥ 2 := by
            calc Nat.choose (2 * (m + 1)) (m + 1)
              = Nat.choose (2 * m + 2) (m + 1) := by ring_nf
              _ ≥ 2 := by
                cases m with
                | zero => decide
                | succ m' =>
                  have h_central : Nat.choose (2 * (m' + 1) + 2) (m' + 1 + 1)
                      = Nat.choose (2 * (m' + 2)) (m' + 2) := by ring_nf
                  rw [h_central]
                  have hpos : m' + 2 > 0 := by omega
                  exact Nat.two_le_centralBinom (m' + 2) hpos
          exact h
      omega
    have hK_unbounded : ∀ M, ∃ m, K m > M := by
      intro M
      use M + 2
      have h : K (M + 2) ≥ 2 * (M + 1) := by
        induction M with
        | zero =>
          simp only [K, cumulativeCount, simpleH]
          decide
        | succ M ih =>
          have hstrict := hK_strict (M + 2) (by omega)
          calc K (M + 2 + 1) ≥ K (M + 2) + 2 := hstrict
            _ ≥ 2 * (M + 1) + 2 := by omega
            _ = 2 * (M + 2) := by ring
      omega
    have hexists : ∃ m, K (m + 1) ≥ k := by
      obtain ⟨m, hm⟩ := hK_unbounded k
      by_cases hm0 : m = 0
      · rw [hm0, K_zero] at hm; omega
      · have hm_ge : m ≥ 1 := Nat.one_le_iff_ne_zero.mpr hm0
        use m - 1
        calc K ((m - 1) + 1) = K m := by rw [Nat.sub_add_cancel hm_ge]
          _ ≥ k + 1 := hm
          _ ≥ k := by omega
    let m := Nat.find hexists
    have hm_spec : K (m + 1) ≥ k := Nat.find_spec hexists
    use m
    constructor
    · by_contra hle
      push_neg at hle
      by_cases hm0 : m = 0
      · have hK1_eq : K 1 = 0 := K_one
        rw [hm0] at hm_spec
        rw [hK1_eq] at hm_spec
        omega
      · have hm_ge_1 : m ≥ 1 := Nat.one_le_iff_ne_zero.mpr hm0
        have hprev : K ((m - 1) + 1) ≥ k := by
          simp only [Nat.sub_add_cancel hm_ge_1]
          exact hle
        have hmin := Nat.find_min hexists (Nat.sub_lt hm_ge_1 Nat.one_pos)
        exact hmin hprev
    · exact hm_spec

lemma stageAssign_zero : stageAssign 0 = 0 := by simp [stageAssign]

lemma stageAssign_pos (k : ℕ) (hk : k ≥ 1) : stageAssign k ≥ 1 := by
  unfold stageAssign; aesop;

lemma stageAssign_unbounded : ∀ M, ∃ k₀, ∀ k ≥ k₀, stageAssign k > M := by
  simp_all +decide [ stageAssign ];
  intro M; use K ( M + 1 ) + 1; intro k hk; split_ifs <;> norm_num at *;
  generalize_proofs at *;
  · linarith [ Nat.zero_le ( K ( M + 1 ) ) ];
  · intro m hm₁ hm₂; linarith [ K_mono m, K_mono_le ( by linarith : m + 1 ≤ M + 1 ) ] ;

noncomputable def nthSubsetOfIcc (n m i : ℕ) : Finset ℕ :=
  if hm0 : m = 0 then ∅
  else if hn0 : n = 0 then ∅
  else if hmn : m > n then ∅
  else
    let without_n := Nat.choose (n - 1) m
    if i < without_n then
      nthSubsetOfIcc (n - 1) m i
    else
      insert n (nthSubsetOfIcc (n - 1) (m - 1) (i - without_n))
termination_by (n, m)

lemma nthSubsetOfIcc_le (n m i : ℕ) : ∀ x ∈ nthSubsetOfIcc n m i, x ≤ n := by
  induction' n with n ih generalizing m i;
  · unfold nthSubsetOfIcc; aesop;
  · unfold nthSubsetOfIcc;
    grind

lemma nthSubsetOfIcc_ge_one (n m i : ℕ) (hn : n ≥ 1) : ∀ x ∈ nthSubsetOfIcc n m i, x ≥ 1 := by
  induction' n with n ih generalizing m i;
  · contradiction;
  · rcases m with ( _ | m ) <;> rcases n with ( _ | n ) <;> simp_all +arith +decide [ Nat.choose_eq_zero_of_lt ];
    · unfold nthSubsetOfIcc; aesop;
    · unfold nthSubsetOfIcc; aesop;
    · unfold nthSubsetOfIcc;
      unfold nthSubsetOfIcc; aesop;
    · unfold nthSubsetOfIcc; aesop;

lemma nthSubsetOfIcc_card (n m i : ℕ) (hi : i < Nat.choose n m) :
    (nthSubsetOfIcc n m i).card = m := by
  induction' n using Nat.strong_induction_on with n ih generalizing m i;
  rcases n with ( _ | _ | n ) <;> rcases m with ( _ | _ | m ) <;> simp_all +arith +decide;
  all_goals unfold nthSubsetOfIcc; simp +arith +decide [ Nat.choose_succ_succ ] at *;
  · unfold nthSubsetOfIcc; simp +decide ;
  · split_ifs <;> simp_all +arith +decide;
    unfold nthSubsetOfIcc; aesop;
  · split_ifs <;> simp_all +arith +decide [ Nat.choose_succ_succ ];
    · linarith [ Nat.choose_eq_zero_of_lt ‹_›, Nat.choose_eq_zero_of_lt ( by linarith : n < m + 1 ), Nat.choose_eq_zero_of_lt ( by linarith : n < m + 2 ) ];
    · rw [ Finset.card_insert_of_notMem ];
      · rw [ ih _ ( by linarith ) _ _ ];
        rw [ tsub_lt_iff_left ] <;> linarith [ Nat.choose_succ_succ n m, Nat.choose_succ_succ n ( m + 1 ) ];
      · exact fun h => by have := nthSubsetOfIcc_le ( n + 1 ) ( m + 1 ) ( i - ( n.choose ( m + 1 ) + n.choose ( m + 2 ) ) ) ( n + 2 ) h; linarith;

lemma nthSubsetOfIcc_subset (n m i : ℕ) (hi : i < Nat.choose n m) :
    ∀ x ∈ nthSubsetOfIcc n m i, 1 ≤ x ∧ x ≤ n := by
  intros x hx
  apply And.intro;
  · by_cases hn : n ≥ 1;
    · exact nthSubsetOfIcc_ge_one n m i hn x hx;
    · unfold nthSubsetOfIcc at hx; aesop;
  · exact nthSubsetOfIcc_le n m i x hx

lemma nthSubsetOfIcc_exhaustive (n m : ℕ) (S : Finset ℕ)
    (hS_card : S.card = m) (hS_subset : ∀ x ∈ S, 1 ≤ x ∧ x ≤ n) :
    ∃ i < Nat.choose n m, nthSubsetOfIcc n m i = S := by
  have h_subset_index : Finset.image (fun i => nthSubsetOfIcc n m i) (Finset.range (Nat.choose n m)) = Finset.powersetCard m (Finset.Icc 1 n) := by
    refine' Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr _ ) _;
    · simp +zetaDelta at *;
      intro x hx; exact ⟨ fun y hy => Finset.mem_Icc.mpr ( nthSubsetOfIcc_subset _ _ _ ( by linarith ) _ hy ), nthSubsetOfIcc_card _ _ _ ( by linarith ) ⟩ ;
    · rw [ Finset.card_image_of_injOn ];
      · simp +arith +decide;
      · have h_inj : ∀ i j, i < Nat.choose n m → j < Nat.choose n m → nthSubsetOfIcc n m i = nthSubsetOfIcc n m j → i = j := by
          intros i j hi hj h_eq;
          have h_inj : ∀ n m i j, i < Nat.choose n m → j < Nat.choose n m → nthSubsetOfIcc n m i = nthSubsetOfIcc n m j → i = j := by
            intros n m i j hi hj h_eq;
            induction' n with n ih generalizing m i j <;> induction' m with m ih' generalizing i j <;> simp_all +decide [ Nat.choose ];
            unfold nthSubsetOfIcc at h_eq; simp +decide at h_eq;
            split_ifs at h_eq;
            · simp_all +decide [ Nat.choose_eq_zero_of_lt ];
              rw [ Nat.choose_eq_zero_of_lt ] at hi hj <;> linarith;
            · (expose_names; exact ih (m + 1) i j h_1 h_2 h_eq);
            · replace h_eq := Finset.ext_iff.mp h_eq ( n + 1 ) ; simp +decide at h_eq;
              exact absurd h_eq ( by exact fun h => by have := nthSubsetOfIcc_le n ( m + 1 ) i ( n + 1 ) h; linarith );
            · replace h_eq := Finset.ext_iff.mp h_eq ( n + 1 ) ; simp +decide at h_eq;
              exact absurd h_eq ( by { exact fun h => by have := nthSubsetOfIcc_le n ( m + 1 ) j ( n + 1 ) h; linarith } );
            · specialize ih m ( i - n.choose ( m + 1 ) ) ( j - n.choose ( m + 1 ) ) ; simp_all +decide [ Nat.choose_succ_succ ];
              contrapose! ih;
              refine' ⟨ _, _, _, _ ⟩;
              · omega;
              · omega;
              · rw [ Finset.ext_iff ] at h_eq;
                ext x; specialize h_eq x; by_cases hx : x = n + 1 <;> simp_all +decide ;
                have h_not_in_range : ∀ i, n + 1 ∉ nthSubsetOfIcc n m i := by
                  intros i hi; exact (by
                  exact absurd ( nthSubsetOfIcc_le n m i ( n + 1 ) hi ) ( by norm_num ));
                exact iff_of_false ( h_not_in_range _ ) ( h_not_in_range _ );
              · grind;
          exact h_inj n m i j hi hj h_eq;
        exact fun i hi j hj hij => h_inj i j ( Finset.mem_range.mp hi ) ( Finset.mem_range.mp hj ) hij;
  rw [ Finset.ext_iff ] at h_subset_index;
  simpa using h_subset_index S |>.2 ( Finset.mem_powersetCard.mpr ⟨ fun x hx => Finset.mem_Icc.mpr ( hS_subset x hx ), hS_card ⟩ )

noncomputable def indexInStage (k : ℕ) : ℕ :=
  if k = 0 then 0
  else k - K (stageAssign k) - 1

noncomputable def F (k : ℕ) : Finset ℕ :=
  if hk : k = 0 then ∅
  else
    let m := stageAssign k
    let Hm := simpleH m
    let idx := indexInStage k
    let indices := nthSubsetOfIcc Hm m idx
    indices.image enumerateB

lemma B1_lower_bound : ∀ x, concreteSeq.inB x → x ≥ concreteSeq.N 0 + 1 := by
  intro x hx
  obtain ⟨k, hk⟩ := hx;
  have hx_ge_N_k_minus_1 : x ≥ concreteSeq.N (k - 1) + 1 := by
    have := B_k_lower_bound ( concreteSeq ) k hk.left x hk.right; aesop;
  have hN_mono : ∀ k ≥ 1, concreteSeq.N (k - 1) ≥ concreteSeq.N 0 := by
    exact fun k a ↦ N_mono_from_zero concreteSeq (k - 1);
  exact le_trans ( Nat.succ_le_succ ( hN_mono k hk.1 ) ) hx_ge_N_k_minus_1

lemma enumerateB_1_lower_bound : enumerateB 1 ≥ concreteSeq.N 0 + 1 := by
  apply B1_lower_bound;
  exact enumerateB_in_B _ le_rfl

lemma P_card_formula (k : ℕ) (hk : k ≥ 1) : (concreteSeq.P k).card = 400 * 8^(k-1) - 2 := by
  cases k with
  | zero => omega
  | succ k' =>
    simp only [NathansonSeq.P, if_neg (Nat.succ_ne_zero k')]
    simp only [NathansonSeq.N, concreteSeq, concreteN]
    simp only [Nat.add_sub_cancel]
    rw [Nat.card_Icc]
    have h1 : 100 * 8 ^ (k' + 1) = 800 * 8 ^ k' := by ring
    have h2 : 2 * (100 * 8 ^ k') + 1 = 200 * 8 ^ k' + 1 := by ring
    simp only [h1, h2]
    have h8k_pos : 8 ^ k' ≥ 1 := Nat.one_le_pow k' 8 (by omega)
    omega

lemma P_card_dominates_central (k : ℕ) (hk : k ≥ 1) :
    (concreteSeq.P k).card > Nat.choose (2 * k) k := by
  rw [ P_card_formula ];
  · have h_exp_growth : ∀ k ≥ 1, 4^k < 400 * 8^(k-1) - 2 := by
      intro k hk; rcases k with ( _ | _ | k ) <;> norm_num [ pow_succ' ] at *;
      exact lt_tsub_iff_left.mpr ( by linarith [ pow_pos ( by decide : 0 < 4 ) k, pow_le_pow_left' ( by decide : 4 ≤ 8 ) k ] );
    refine lt_of_le_of_lt ?_ ( h_exp_growth k hk );
    rw [ show 4 ^ k = ( 2 : ℕ ) ^ ( 2 * k ) by norm_num [ pow_mul ] ];
    rw [ ← Nat.sum_range_choose ] ; exact Finset.single_le_sum ( fun x _ => Nat.zero_le _ ) ( Finset.mem_range.mpr ( by linarith ) );
  · assumption

/-- P_1 for the concrete sequence: integers from 202 to 599 -/
lemma P1_concrete : concreteSeq.P 1 = Finset.Icc 202 599 := by
  simp only [NathansonSeq.P, if_neg (Nat.one_ne_zero)]
  simp only [NathansonSeq.N, concreteSeq, concreteN]
  rfl

lemma P1_card : (concreteSeq.P 1).card = 398 := by
  rw [P1_concrete]
  norm_num

/-- Sum of |P_1|...|P_m| exceeds K(m+1) for all m ≥ 1 -/
lemma P_sum_dominates_K (m : ℕ) (hm : m ≥ 1) :
    (Finset.range m).sum (fun k => (concreteSeq.P (k+1)).card) > K (m + 1) := by
  induction m with
  | zero => omega
  | succ m' ih =>
    by_cases hm' : m' = 0
    · -- Base case: m = 1
      subst hm'
      simp only [Finset.range_one, Finset.sum_singleton, Nat.zero_add]
      have hP1 : (concreteSeq.P 1).card = 398 := P1_card
      rw [hP1]
      decide
    · -- Inductive case: m' ≥ 1
      have hm'_pos : m' ≥ 1 := Nat.one_le_iff_ne_zero.mpr hm'
      have ih' := ih hm'_pos
      simp only [Finset.range_add_one, Finset.sum_insert (Finset.notMem_range_self)]
      have hK_succ : K (m' + 2) = K (m' + 1) + Nat.choose (2 * (m' + 1)) (m' + 1) := by
        rw [K_succ (m' + 1) (by omega)]
        simp only [simpleH]
      rw [hK_succ]
      have hdom := P_card_dominates_central (m' + 1) (by omega)
      omega

lemma B_count_le_enumerateB (i : ℕ) (hi : i ≥ 1) :
    ∀ x, inB_concrete x → x ≤ enumerateB i → ∃ k, 1 ≤ k ∧ k ≤ i ∧ enumerateB k = x := by
  intro x hx hx';
  have := enumerateB_covers x hx;
  obtain ⟨ n, hn, rfl ⟩ := this;
  exact ⟨ n, hn, le_of_not_gt fun h => hx'.not_gt <| by exact strictMono_nat_of_lt_succ ( fun k => enumerateB_mono k ) h, rfl ⟩

def UnionB (m : ℕ) : Finset ℕ :=
  (Finset.range m).biUnion (fun j => concreteSeq.B_k (j + 1))

lemma UnionB_card_lower (m : ℕ) (hm : m ≥ 1) :
    (UnionB m).card > K (m + 1) := by
      have h_card_lower : (Finset.biUnion (Finset.Ico 0 m) (fun j => concreteSeq.B_k (j + 1))).card ≥ (Finset.range m).sum (fun j => (concreteSeq.P (j + 1)).card) := by
        have h_card_lower : (Finset.biUnion (Finset.Ico 0 m) (fun j => concreteSeq.B_k (j + 1))).card ≥ (Finset.biUnion (Finset.Ico 0 m) (fun j => concreteSeq.P (j + 1))).card := by
          refine Finset.card_mono ?_;
          simp +decide [ Finset.subset_iff ];
          unfold NathansonSeq.B_k; aesop;
        refine le_trans ?_ h_card_lower;
        rw [ Finset.card_biUnion ] ; aesop;
        intros i hi j hj hij;
        cases lt_or_gt_of_ne hij <;> simp_all +decide [ Finset.disjoint_left ];
        · intro x hx₁ hx₂; have := P_subset concreteSeq ( i + 1 ) ( by linarith ) x hx₁; have := P_subset concreteSeq ( j + 1 ) ( by linarith ) x hx₂; simp_all +decide [ Finset.mem_Icc ] ;
          have h_N_j_ge_N_i_plus_1 : concreteSeq.N j ≥ concreteSeq.N (i + 1) := by
            exact Nat.le_induction ( by norm_num ) ( fun k hk ih => by linarith! [ Nat.pow_le_pow_right ( by norm_num : 1 ≤ 8 ) ( by linarith : k ≥ i + 1 ), Nat.pow_le_pow_right ( by norm_num : 1 ≤ 8 ) ( by linarith : k + 1 ≥ i + 1 ), concreteSeq.N_strict_mono k ] ) j ( by linarith : i + 1 ≤ j );
          unfold NathansonSeq.N at * ; linarith;
        · intro x hx₁ hx₂;
          have := concreteSeq.P_subset ( i + 1 ) ( by linarith ) x hx₁; have := concreteSeq.P_subset ( j + 1 ) ( by linarith ) x hx₂; simp_all +decide [ Nat.succ_eq_add_one ] ;
          unfold NathansonSeq.N at *;
          unfold concreteSeq at *; norm_num at *;
          unfold concreteN at * ; linarith [ pow_le_pow_right₀ ( show 1 ≤ 8 by norm_num ) ( show i ≥ j + 1 by linarith ) ];
      refine lt_of_lt_of_le ( P_sum_dominates_K m hm ) ?_;
      unfold UnionB; aesop;

lemma stages_contradict_positions (m : ℕ) (hm : m ≥ 1) (i : ℕ) (hi : i ≥ 2)
    (hi_le : i ≤ K (m + 1))
    (hbound : ∀ j', j' ≤ m → j' ≥ 1 → ∀ x ∈ concreteSeq.B_k j', x ≤ enumerateB (i - 1)) :
    False := by
  set S : Finset ℕ := (Finset.range m).biUnion (fun j => concreteSeq.B_k (j + 1));
  have hS_subset_B : S ⊆ Finset.image enumerateB (Finset.Icc 1 (i - 1)) := by
    intro x hx
    obtain ⟨j, hj⟩ : ∃ j, 1 ≤ j ∧ j ≤ m ∧ x ∈ concreteSeq.B_k j := by
      aesop;
    have := B_count_le_enumerateB ( i - 1 ) ( Nat.sub_pos_of_lt hi ) x ( by
      exact ⟨ j, hj.1, hj.2.2 ⟩ ) ( by
      exact hbound j hj.2.1 hj.1 x hj.2.2 ) ; aesop;
  have := Finset.card_le_card hS_subset_B; simp_all +decide [ Finset.card_image_of_injective, Function.Injective ] ;
  exact this.not_gt ( lt_of_le_of_lt ( Finset.card_image_le ) ( by simpa using by linarith! [ Nat.sub_add_cancel ( by linarith : 1 ≤ i ), UnionB_card_lower m hm ] ) )

lemma enumerateB_stage_upper_bound (m : ℕ) (hm : m ≥ 1) (i : ℕ) (hi : 1 ≤ i) (hi_le : i ≤ K (m + 1)) :
    enumerateB i ≤ concreteSeq.n m + concreteSeq.N (m - 1) := by
  apply Classical.byContradiction
  intro h_contra;
  have h_all_le : ∀ j', j' ≤ m → j' ≥ 1 → ∀ x ∈ concreteSeq.B_k j', x ≤ enumerateB (i - 1) := by
    intros j' hj' hj'_ge_1 x hx
    have hx_le_i_minus_1 : x < enumerateB i := by
      have hx_le_i_minus_1 : x ≤ concreteSeq.n m + concreteSeq.N (m - 1) := by
        have := B_k_upper_bound ( concreteSeq ) j' hj'_ge_1 x hx;
        exact le_trans this ( add_le_add ( n_mono_le ( concreteSeq ) ( by linarith ) ) ( N_mono_le ( concreteSeq ) ( by omega ) ) );
      linarith;
    have hx_le_i_minus_1 : ∀ k, x ∈ concreteSeq.B_k k → x < enumerateB i → x ≤ enumerateB (i - 1) := by
      intros k hk hx_lt_i
      have hx_le_i_minus_1 : ∀ j, x ∈ concreteSeq.B_k j → x < enumerateB i → x ≤ enumerateB (i - 1) := by
        intros j hj hx_lt_i
        have hx_le_i_minus_1 : ∀ j, x ∈ concreteSeq.B_k j → x < enumerateB i → x ≤ enumerateB (i - 1) := by
          intros j hj hx_lt_i
          exact (by
            have := B_count_le_enumerateB i hi
            obtain ⟨ k, hk₁, hk₂, rfl ⟩ := this x ( by
              exact ⟨ j', hj'_ge_1, hx ⟩ ) hx_lt_i.le;
            exact monotone_nat_of_le_succ ( fun n => Nat.le_of_lt ( enumerateB_mono n ) ) ( Nat.le_pred_of_lt ( show k < i from lt_of_le_of_ne hk₂ ( by aesop_cat ) ) ))
        exact hx_le_i_minus_1 j hj hx_lt_i;
      exact hx_le_i_minus_1 k hk hx_lt_i;
    exact hx_le_i_minus_1 j' hx ‹_›;
  apply stages_contradict_positions m hm i (by
  rcases i with ( _ | _ | i ) <;> norm_num at *;
  exact absurd ( h_all_le 1 ( by linarith ) ( by linarith ) _ ( show 202 ∈ concreteSeq.B_k 1 from by
                                                                  exact Finset.mem_union_left _ ( Finset.mem_union_left _ ( Finset.mem_Icc.mpr ⟨ by decide, by decide ⟩ ) ) ) ) ( by
                                                                  exact not_le_of_gt ( by linarith! [ enumerateB_zero, enumerateB_1_lower_bound ] ) )) hi_le h_all_le

lemma enumerateB_exp_bound (m : ℕ) (hm : m ≥ 1) (i : ℕ) (hi : 1 ≤ i) (hi_le : i ≤ K (m + 1)) :
    enumerateB i ≤ 200 * 8^m := by
  have h_subst : concreteSeq.n m + concreteSeq.N (m - 1) = 100 * 8^m + (2 * (100 * 8^(m - 1)) + 1) := by
    rfl;
  exact le_trans ( enumerateB_stage_upper_bound m hm i hi hi_le ) ( by rcases m with ( _ | m ) <;> norm_num [ pow_succ' ] at * ; linarith [ pow_pos ( by decide : 0 < 8 ) m ] )

lemma indexInStage_valid (k : ℕ) (hk : k ≥ 1) :
    indexInStage k < Nat.choose (simpleH (stageAssign k)) (stageAssign k) := by
  unfold indexInStage;
  split_ifs;
  · grind;
  · rw [ tsub_tsub, tsub_lt_iff_left ];
    · have h_stage : K (stageAssign k) < k ∧ k ≤ K (stageAssign k + 1) := by
        unfold stageAssign;
        grind;
      rw [ K_succ ] at h_stage;
      · linarith;
      · exact stageAssign_pos k hk;
    · unfold stageAssign;
      grind

lemma F_card_prop (k : ℕ) (hk : k ≥ 1) : (F k).card = stageAssign k := by
  unfold _root_.F;
  split_ifs;
  · grind;
  · rw [ Finset.card_image_of_injective ];
    · apply nthSubsetOfIcc_card;
      exact indexInStage_valid k hk;
    · exact strictMono_nat_of_lt_succ ( fun n => by exact enumerateB_mono n ) |> StrictMono.injective

lemma F_subset_prop (k : ℕ) (hk : k ≥ 1) (x : ℕ) (hx : x ∈ F k) :
    ∃ i, 1 ≤ i ∧ i ≤ simpleH (stageAssign k) ∧ enumerateB i = x := by
  have h_subset : x ∈ (nthSubsetOfIcc (simpleH (stageAssign k)) (stageAssign k) (indexInStage k)).image enumerateB := by
    unfold _root_.F at hx; aesop;
  obtain ⟨ i, hi, rfl ⟩ := Finset.mem_image.mp h_subset;
  have h_bounds : ∀ x ∈ nthSubsetOfIcc (simpleH (stageAssign k)) (stageAssign k) (indexInStage k), 1 ≤ x ∧ x ≤ simpleH (stageAssign k) := by
    apply nthSubsetOfIcc_subset;
    exact indexInStage_valid k hk;
  exact ⟨ i, h_bounds i hi |>.1, h_bounds i hi |>.2, rfl ⟩

lemma K_lower_bound (m : ℕ) (hm : m ≥ 1) : K (m + 1) ≥ 2 * m := by
  induction hm <;> simp_all +arith +decide [ Nat.mul_succ, K_succ ];
  unfold simpleH at * ; simp_all +arith +decide [ Nat.choose ];
  linarith [ Nat.choose_pos ( show ‹_› ≤ 2 * ‹_› by linarith ), Nat.choose_pos ( show ‹_› + 1 ≤ 2 * ‹_› + 1 by linarith ), Nat.choose_pos ( show ‹_› ≤ 2 * ‹_› + 1 by linarith ) ]

lemma K_ge_self (m : ℕ) (hm : m ≥ 2) : K m ≥ m := by
  induction' hm with m hm ih;
  · decide
  · rw [ show K ( m + 1 ) = K m + Nat.choose ( simpleH m ) m from K_succ m ( le_of_lt hm ) ];
    exact Nat.succ_le_of_lt ( lt_add_of_le_of_pos ih ( Nat.choose_pos ( by linarith [ Nat.succ_le_iff.mp hm, show simpleH m ≥ 2 * m from by rfl ] ) ) )

lemma stage_le_k_prop (k : ℕ) (hk : k ≥ 1) : stageAssign k ≤ k := by
  obtain ⟨hK_lt, hK_ge⟩ : K (stageAssign k) < k ∧ k ≤ K (stageAssign k + 1) := by
    unfold stageAssign;
    grind;
  contrapose! hK_lt;
  exact le_trans ( by linarith ) ( K_ge_self _ ( by linarith ) )

lemma k_grows_with_stage_prop (m : ℕ) (hm : m ≥ 1) : ∃ k₀, ∀ k, stageAssign k = m → k ≥ k₀ := by
  exact ⟨ 0, fun k hk => Nat.zero_le k ⟩

lemma exhaustive_prop (m : ℕ) (hm : m ≥ 1) (S : Finset ℕ)
    (hS_range : ∀ x ∈ S, ∃ i, 1 ≤ i ∧ i ≤ simpleH m ∧ enumerateB i = x)
    (hS_card : S.card = m) :
    ∃ k, stageAssign k = m ∧ F k = S := by
  apply Classical.byContradiction
  intro h_contra;
  obtain ⟨i, hi⟩ : ∃ i < Nat.choose (2 * m) m, S = (nthSubsetOfIcc (2 * m) m i).image enumerateB := by
    have h_exhaustive : ∃ i < Nat.choose (2 * m) m, S = (nthSubsetOfIcc (2 * m) m i).image enumerateB := by
      have h_subset : ∃ T : Finset ℕ, T ⊆ Finset.Icc 1 (2 * m) ∧ S = T.image enumerateB ∧ T.card = m := by
        choose! f hf using hS_range;
        refine' ⟨ Finset.image f S, _, _, _ ⟩;
        · exact Finset.image_subset_iff.mpr fun x hx => Finset.mem_Icc.mpr ⟨ hf x hx |>.1, hf x hx |>.2.1 ⟩;
        · ext x; aesop;
        · rw [ Finset.card_image_of_injOn fun x hx y hy hxy => by have := hf x hx; have := hf y hy; aesop, hS_card ]
      obtain ⟨ T, hT₁, rfl, hT₂ ⟩ := h_subset;
      have h_exhaustive : ∃ i < Nat.choose (2 * m) m, nthSubsetOfIcc (2 * m) m i = T := by
        apply nthSubsetOfIcc_exhaustive;
        · exact hT₂;
        · exact fun x hx => Finset.mem_Icc.mp ( hT₁ hx );
      grind;
    exact h_exhaustive;
  obtain ⟨k, hk⟩ : ∃ k, k = K m + i + 1 ∧ stageAssign k = m := by
    have h_stage : K m < K m + i + 1 ∧ K m + i + 1 ≤ K (m + 1) := by
      exact ⟨ by linarith, by linarith! [ K_succ m hm, Nat.choose_pos ( show m ≤ 2 * m by linarith ) ] ⟩;
    unfold stageAssign;
    norm_num +zetaDelta at *;
    rw [ Nat.find_eq_iff ];
    exact ⟨ h_stage, fun n hn => fun h => by linarith [ show K n ≤ K m from K_mono_le <| by linarith, show K ( n + 1 ) ≤ K m from K_mono_le <| by linarith ] ⟩;
  unfold _root_.F at h_contra;
  simp_all +decide [ indexInStage ];
  specialize h_contra k hk.2 ; simp_all +decide [ Nat.sub_sub ];
  exact h_contra rfl

lemma F_lt_N_prev_prop (k : ℕ) (hk : k ≥ 2) (x : ℕ) (hx : x ∈ F k) : x < concreteSeq.N (k - 1) := by
  by_contra h_contra;
  obtain ⟨i, hi⟩ : ∃ i, i ∈ nthSubsetOfIcc (simpleH (stageAssign k)) (stageAssign k) (indexInStage k) ∧ enumerateB i = x := by
    unfold _root_.F at hx; aesop;
  have h_enum_le : enumerateB i ≤ 200 * 8^(stageAssign k) := by
    apply enumerateB_exp_bound;
    · exact stageAssign_pos k ( by linarith );
    · have := nthSubsetOfIcc_subset ( simpleH ( stageAssign k ) ) ( stageAssign k ) ( indexInStage k ) ( Nat.lt_of_succ_le ( Nat.succ_le_of_lt ( indexInStage_valid k ( by linarith ) ) ) ) ; aesop;
    · have h_i_le_K : i ≤ simpleH (stageAssign k) := by
        exact nthSubsetOfIcc_le _ _ _ _ hi.1;
      have h_K_ge_i : K (stageAssign k + 1) ≥ simpleH (stageAssign k) := by
        apply K_lower_bound;
        exact stageAssign_pos k ( by linarith );
      linarith;
  have h_final_le : 200 * 8^(stageAssign k) ≤ 200 * 8^(k - 1) := by
    gcongr;
    · norm_num;
    · have h_stage_le : stageAssign k ≤ k := by
        apply stage_le_k_prop;
        linarith;
      cases h_stage_le.eq_or_lt <;> simp_all +decide [ Nat.sub_add_cancel ( by linarith : 1 ≤ k ) ];
      · have h_stage_k : K k < k ∧ k ≤ K (k + 1) := by
          have h_stage_k : K (stageAssign k) < k ∧ k ≤ K (stageAssign k + 1) := by
            have := Nat.find_spec (stageAssign.exists_stage k (by linarith))
            unfold stageAssign at *; aesop;
          aesop;
        have h_K_ge_k : K k ≥ k := by
          apply K_ge_self; linarith;
        grind;
      · exact Nat.le_pred_of_lt ‹_›;
  rcases k with ( _ | _ | k ) <;> simp_all +decide [ concreteSeq ];
  norm_num [ concreteSeq, NathansonSeq.N ] at *;
  exact h_contra.not_gt ( by rw [ show concreteN ( k + 1 ) = 100 * 8 ^ ( k + 1 ) by rfl ] at *; linarith )

noncomputable def concreteGC : GrowingConstruction where
  seq := concreteSeq
  a := enumerateB
  H := simpleH
  F := F
  stage := stageAssign
  a_in_B := fun i hi => enumerateB_in_B i hi
  a_mono := enumerateB_mono
  a_covers := fun x hx => enumerateB_covers x hx
  H_mono := simpleH_mono
  H_unbounded := simpleH_unbounded
  F_card := F_card_prop
  F_subset := F_subset_prop
  stage_pos := stageAssign_pos
  stage_unbounded := stageAssign_unbounded
  exhaustive := exhaustive_prop
  F_lt_N_prev := F_lt_N_prev_prop
  k_grows_with_stage := k_grows_with_stage_prop
  stage_le_k := stage_le_k_prop
  stage_zero := stageAssign_zero
  H_linear := simpleH_linear

open NathansonSeq GrowingConstruction Filter

theorem concreteGC_reps_ge_t (t : ℕ) :
    ∀ᶠ n in atTop, ∃ pairs : Finset (ℕ × ℕ),
      pairs.card ≥ t ∧ ∀ p ∈ pairs, concreteGC.inA p.1 ∧ concreteGC.inA p.2 ∧ p.1 + p.2 = n ∧ p.1 ≤ p.2 := by
        revert t;
        have h_lemma4_part2 : ∀ t, ∃ M, ∀ n ≥ M, (∀ k, n ≠ concreteSeq.N k) → ∃ j ≥ 3, t ≤ countReps (concreteSeq.B_k j ∪ concreteSeq.B_k (j - 1) ∪ concreteSeq.B_k (j - 2)) n := by
          exact fun t ↦ lemma4_part2 concreteSeq t;
        have h_reps_in_B : ∀ t, ∃ M, ∀ n ≥ M, (∀ k, n ≠ concreteSeq.N k) → ∃ pairs : Finset (ℕ × ℕ), pairs.card ≥ t ∧ ∀ p ∈ pairs, concreteGC.seq.inB p.1 ∧ concreteGC.seq.inB p.2 ∧ p.1 + p.2 = n ∧ p.1 ≤ p.2 := by
          intro t
          obtain ⟨M, hM⟩ := h_lemma4_part2 t
          use M
          intro n hn hn_ne_Nk
          obtain ⟨j, hj_ge_3, hj_count⟩ := hM n hn hn_ne_Nk
          have h_pairs_in_B : ∃ pairs : Finset (ℕ × ℕ), pairs.card ≥ t ∧ ∀ p ∈ pairs, concreteGC.seq.inB p.1 ∧ concreteGC.seq.inB p.2 ∧ p.1 + p.2 = n ∧ p.1 ≤ p.2 := by
            obtain ⟨pairs, hpairs_card, hpairs⟩ : ∃ pairs : Finset (ℕ × ℕ), pairs.card = countReps (concreteSeq.B_k j ∪ concreteSeq.B_k (j - 1) ∪ concreteSeq.B_k (j - 2)) n ∧ ∀ p ∈ pairs, p.1 ∈ concreteSeq.B_k j ∪ concreteSeq.B_k (j - 1) ∪ concreteSeq.B_k (j - 2) ∧ p.2 ∈ concreteSeq.B_k j ∪ concreteSeq.B_k (j - 1) ∪ concreteSeq.B_k (j - 2) ∧ p.1 + p.2 = n ∧ p.1 ≤ p.2 := by
              unfold NathansonSeq.countReps; aesop;
            use pairs;
            simp_all +decide [ NathansonSeq.inB ];
            intro a b hab; specialize hpairs a b hab; rcases hpairs.1 with ( ha | ha | ha ) <;> rcases hpairs.2.1 with ( hb | hb | hb ) <;> exact ⟨ ⟨ _, by omega, ha ⟩, ⟨ _, by omega, hb ⟩ ⟩ ;
          exact h_pairs_in_B;
        have h_reps_in_A : ∀ t, ∃ M, ∀ n ≥ M, (∃ k, n = concreteSeq.N k ∧ concreteGC.stage k ≥ t) → ∃ pairs : Finset (ℕ × ℕ), pairs.card ≥ t ∧ ∀ p ∈ pairs, concreteGC.inA p.1 ∧ concreteGC.inA p.2 ∧ p.1 + p.2 = n ∧ p.1 ≤ p.2 := by
          intro t;
          have := concreteGC.rep_count_Nk;
          use concreteSeq.N 2 + 1;
          rintro n hn ⟨ k, rfl, hk ⟩;
          exact Exists.elim ( this k ( by contrapose! hn; interval_cases k <;> trivial ) ) fun pairs hpairs => ⟨ pairs, hpairs.1.symm ▸ hk, hpairs.2 ⟩;
        have h_exists_k : ∀ t, ∃ M, ∀ n ≥ M, (∃ k, n = concreteSeq.N k) → ∃ k, n = concreteSeq.N k ∧ concreteGC.stage k ≥ t := by
          intro t
          obtain ⟨k₀, hk₀⟩ : ∃ k₀, ∀ k ≥ k₀, concreteGC.stage k ≥ t := by
            have := concreteGC.stage_unbounded t;
            exact ⟨ this.choose, fun k hk => le_of_lt ( this.choose_spec k hk ) ⟩;
          use concreteSeq.N k₀ + 1;
          rintro n hn ⟨ k, rfl ⟩;
          use k;
          field_simp;
          exact ⟨ trivial, hk₀ k ( le_of_not_gt fun hk => by linarith [ show concreteSeq.N k ≤ concreteSeq.N k₀ from by exact Nat.le_induction ( by norm_num ) ( fun n hn ih => by linarith [ concreteSeq.N_strict_mono n ] ) _ hk.le ] ) ⟩;
        intro t;
        obtain ⟨ M₁, hM₁ ⟩ := h_reps_in_B t
        obtain ⟨ M₂, hM₂ ⟩ := h_reps_in_A t
        obtain ⟨ M₃, hM₃ ⟩ := h_exists_k t
        use Filter.eventually_atTop.mpr ⟨ Max.max M₁ ( Max.max M₂ M₃ ), fun n hn => ?_ ⟩;
        by_cases h : ∃ k, n = concreteSeq.N k <;> simp_all +decide;
        · grind;
        · obtain ⟨ pairs, hpairs₁, hpairs₂ ⟩ := hM₁ n hn.1 h; exact ⟨ pairs, hpairs₁, fun a b hab => ⟨ by exact Or.inl <| hpairs₂ a b hab |>.1, by exact Or.inl <| hpairs₂ a b hab |>.2.1, hpairs₂ a b hab |>.2.2.1, hpairs₂ a b hab |>.2.2.2 ⟩ ⟩ ;

theorem not_erdos_871 :
    ∃ (A : Set ℕ),
      (∀ᶠ n in Filter.atTop, ∃ a ∈ A, ∃ b ∈ A, a + b = n) ∧
      (∀ t, ∀ᶠ n in Filter.atTop, ∃ pairs : Finset (ℕ × ℕ),
        pairs.card ≥ t ∧ ∀ p ∈ pairs, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n ∧ p.1 ≤ p.2) ∧
      ¬∃ (B C : Set ℕ),
        (∀ x, x ∈ A ↔ x ∈ B ∨ x ∈ C) ∧
        Disjoint B C ∧
        (∀ᶠ n in Filter.atTop, ∃ a ∈ B, ∃ b ∈ B, a + b = n) ∧
        (∀ᶠ n in Filter.atTop, ∃ a ∈ C, ∃ b ∈ C, a + b = n) := by
  use {x | concreteGC.inA x};
  constructor;
  · have := @concreteGC_reps_ge_t 1;
    filter_upwards [ this ] with n hn using by obtain ⟨ pairs, hpairs₁, hpairs₂ ⟩ := hn; obtain ⟨ p, hp ⟩ := Finset.card_pos.mp ( by linarith ) ; use p.1, hpairs₂ p hp |>.1, p.2, hpairs₂ p hp |>.2.1, hpairs₂ p hp |>.2.2.1;
  · constructor;
    · exact fun t ↦ concreteGC_reps_ge_t t;
    · convert GrowingConstruction.non_decomposable concreteGC using 1

#print axioms not_erdos_871
-- 'not_erdos_871' depends on axioms: [propext, Classical.choice, Quot.sound]
