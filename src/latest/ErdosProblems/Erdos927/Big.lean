/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 John Jennings. All rights reserved.
Released under Apache 2.0 license; see LICENSE.
Modified for this repository and Lean/Mathlib 4.33.0.
-/
/-
Erdős Problem 927.
Informal proof: Joel H. Spencer, "On cliques in graphs" (1971).
Formal authors: John Jennings and Aristotle (Harmonic).
Jake Mallen replaced native evaluation with kernel-checked proofs in the selected copy.
Source: https://www.erdosproblems.com/927#post-6850
https://gist.githubusercontent.com/JohnEdwardJennings/24c9debc9854cb118fbc1314c70941c3/raw/b4fc5ef91876a89018b10508c479c000258504fb/Erdos927.lean
https://github.com/Jayyhk/erdos-lean/tree/cc6c94bd3f9de7c4cf7703ed40d8fd06380780a3/problems/927
Original and selected toolchain: Lean 4.28.0.
Selected Mathlib commit: 8f9d9cff6bd728b17a24e163c9402775d9e6a365.
-/
import ErdosProblems.Erdos927.Medium

set_option linter.mathlibStandardSet false

namespace Erdos927

/-
# Big Clique Construction

For each d with 2^n + n < d ≤ spB n, we construct a maximal clique of size d
in Spencer's graph. The clique consists of generic y-vertices (from a selected
subset), ALL C* vertices, and C_i for i not in the selected subset.
-/

/-- The big clique for selector set S ⊆ {generic selectors}:
  {y_i : i ∈ S} ∪ {cStar j : all j} ∪ ⋃_{i ∉ S} C_i

  S should only contain generic selectors (i < n/2) for the clique property. -/
noncomputable def bigClique (n : ℕ) (S : Finset (Fin n)) : Finset (SpVtx n (spA n)) := by
  classical
  exact S.biUnion (fun i => {.y i}) ∪
  Finset.univ.image SpVtx.cStar ∪
  (Finset.univ \ S).biUnion (fun i => Finset.univ.image fun j => SpVtx.c i j)

/-- y_i is in the big clique iff i ∈ S. -/
lemma y_mem_bigClique_iff (n : ℕ) (S : Finset (Fin n)) (i : Fin n) :
    SpVtx.y i ∈ bigClique n S ↔ i ∈ S := by
  classical
  simp [bigClique, SpVtx.y.injEq]

/-- cStar_j is in the big clique. -/
lemma cStar_mem_bigClique (n : ℕ) (S : Finset (Fin n)) (j : Fin (spA n)) :
    SpVtx.cStar j ∈ bigClique n S := by
  classical
  simp [bigClique]

/-- c_i_j is in the big clique iff i ∉ S. -/
lemma c_mem_bigClique_iff (n : ℕ) (S : Finset (Fin n)) (i : Fin n) (j : Fin (cSize i)) :
    SpVtx.c i j ∈ bigClique n S ↔ i ∉ S := by
  classical
  simp [bigClique, SpVtx.c.injEq]

/-- yStar is NOT in the big clique. -/
lemma yStar_not_mem_bigClique (n : ℕ) (S : Finset (Fin n)) :
    SpVtx.yStar ∉ bigClique n S := by
  classical
  simp [bigClique]

/-- z is NOT in the big clique. -/
lemma z_not_mem_bigClique (n : ℕ) (S : Finset (Fin n)) :
    SpVtx.z ∉ bigClique n S := by
  classical
  simp [bigClique]

/-
The big clique is a clique when S only contains generic selectors.
-/
set_option maxHeartbeats 800000 in
lemma bigClique_isClique (n : ℕ) (S : Finset (Fin n))
    (hS : ∀ i ∈ S, isGeneric n i = true) :
    (spGraph n).IsClique (↑(bigClique n S) : Set _) := by
  classical
  push_cast [ SimpleGraph.isClique_iff, bigClique ];
  simp +decide [ Set.Pairwise, spGraph ];
  unfold spAdj; aesop;

/-
The big clique is maximal when n ≥ 2.
-/
set_option maxHeartbeats 800000 in
lemma bigClique_isMaximal (n : ℕ) (hn : n ≥ 2) (S : Finset (Fin n)) :
    ∀ t : Finset (SpVtx n (spA n)),
      (spGraph n).IsClique (↑t : Set _) → bigClique n S ⊆ t → t = bigClique n S := by
  classical
  intro t ht ht';
  refine' le_antisymm _ ht';
  intro v hv;
  rcases v with ( _ | _ | _ | _ | _ ) <;> simp_all +decide [ Finset.subset_iff ];
  · rename_i i;
    by_cases hi : i ∈ S <;> simp_all +decide [ bigClique ];
    have := ht hv ( ht' <| Or.inr <| Or.inr <| ⟨ i, hi, ⟨ 0, by
      exact Nat.succ_pos _ ⟩, rfl ⟩ ) ; simp_all +decide [ spGraph ];
    unfold spAdj at this; aesop;
  · have := ht hv ( ht' ( cStar_mem_bigClique n S ⟨ 0, spA_pos n ⟩ ) ) ; simp_all +decide [ spGraph ] ;
    cases this ; tauto;
  · contrapose! hv;
    intro h;
    have := ht h ( ht' <| show SpVtx.y ‹_› ∈ bigClique n S from ?_ ) ; simp_all +decide [ spGraph ];
    · unfold spAdj at this; aesop;
    · unfold bigClique at *; aesop;
  · exact Finset.mem_union_left _ ( Finset.mem_union_right _ ( Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) ) );
  · by_cases h : ⟨ 0, by linarith ⟩ ∈ S <;> simp_all +decide [ bigClique ];
    · have := ht hv ( ht' <| Or.inl ⟨ _, h, rfl ⟩ ) ; simp_all +decide [ spGraph ] ;
      unfold spAdj at this; simp_all +decide [ isGeneric ] ;
    · have := ht hv ( ht' <| Or.inr <| Or.inr <| ⟨ ⟨ 0, by linarith ⟩, h, ⟨ 0, by simp +decide [ cSize ] ⟩, rfl ⟩ ) ; simp_all +decide [ spGraph ] ;
      cases this ; contradiction

/-- The big clique is a maximal clique when S contains only generic selectors. -/
lemma bigClique_isMaximalClique (n : ℕ) (hn : n ≥ 2) (S : Finset (Fin n))
    (hS : ∀ i ∈ S, isGeneric n i = true) :
    IsMaximalClique (spGraph n) (bigClique n S) :=
  ⟨bigClique_isClique n S hS, bigClique_isMaximal n hn S⟩

/-
The card of the big clique.
-/
lemma bigClique_card (n : ℕ) (S : Finset (Fin n)) :
    (bigClique n S).card = spB n - ∑ i ∈ S, 2 ^ (i : ℕ) := by
  classical
  unfold bigClique;
  rw [ Finset.card_union_of_disjoint, Finset.card_union_of_disjoint ] <;>
    norm_num [ Finset.card_image_of_injective, Function.Injective ];
  · rw [ Finset.card_biUnion, Finset.card_biUnion ];
    · have hstar : ((Finset.univ : Finset (Fin (spA n))).image
          (SpVtx.cStar (n := n))).card = spA n := by
        rw [Finset.card_image_of_injective _ (by intro x y h; injection h)]
        simp
      have hc (i : Fin n) : ((Finset.univ : Finset (Fin (cSize i))).image
          (SpVtx.c (A := spA n) i)).card = cSize i := by
        rw [Finset.card_image_of_injective _ (by intro x y h; injection h)]
        simp
      simp only [hstar, hc, spB]
      have h_sum_cSize : ∑ i : Fin n, cSize i = 2 ^ n - 1 + n := by
        simpa only [cSize] using sum_cSize_Fin n
      rw [← Finset.sum_sdiff (Finset.subset_univ S)] at h_sum_cSize
      simp only [cSize, Finset.card_singleton, Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul, mul_one] at h_sum_cSize ⊢
      have hpow := Nat.one_le_pow n 2 zero_lt_two
      omega
    · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by aesop;
    · exact fun i hi j hj hij => Finset.disjoint_singleton.2 <| by simpa [ Fin.ext_iff ] using hij;
  · simp +decide [ Finset.disjoint_right ];
  · constructor <;> rw [ Finset.disjoint_left ] <;> aesop

/-
spA n ≤ 2^(n/2) for n ≥ 16.
-/
lemma spA_le_pow_half (n : ℕ) (hn : n ≥ 16) : spA n ≤ 2 ^ (n / 2) := by
  classical
  -- By induction on $n$, we can show that $spAux n \leq 4n$ for all $n \geq 16$.
  have h_spAux_le_4n (n : ℕ) (hn : n ≥ 16) : spAux n ≤ 4 * n := by
    induction' n using Nat.strong_induction_on with n ih;
    unfold spAux;
    rcases n with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n ) <;>
      simp +arith +decide [ * ] at *;
    by_cases h₂ : 16 ≤ Nat.log 2 (n + 15) + 1;
    · have := ih ( Nat.log 2 ( n + 15 ) + 1 ) ( by
        linarith [Nat.log_lt_of_lt_pow ( by linarith ) ( show n + 15 < 2 ^ ( n + 15 ) by
            exact Nat.recOn n ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at * ; linarith )
          ]
        ) ( by linarith );
      have := Nat.pow_log_le_self 2 ( by linarith : n + 15 ≠ 0 );
      rcases k : Nat.log 2 ( n + 15 ) with
        ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k ) <;>
          simp_all +arith +decide [ Nat.pow_succ' ];
      · linarith;
      · rename_i k' hk';
        linarith [ show 2 ^ k' ≥ k' + 1 from
          Nat.recOn k' ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith ];
    · split_ifs <;> simp_all +arith +decide;
      · interval_cases Nat.log 2 ( n + 15 ) <;> norm_num at *;
      · interval_cases _ : Nat.log 2 ( n + 15 ) <;> simp +arith +decide at *;
        all_goals rw [ Nat.log_eq_iff ] at * <;> norm_num at *;
        all_goals unfold spAux; simp +arith +decide at *;
        all_goals norm_num [ Nat.log_of_lt ] at *;
        all_goals unfold spAux; simp +arith +decide at *;
        all_goals norm_num [ Nat.log_of_lt ] at *;
        all_goals omega;
  refine le_trans ( h_spAux_le_4n n hn ) ?_;
  rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> norm_num [ Nat.pow_add, Nat.pow_mul ] at *;
  · exact Nat.le_induction ( by norm_num )
      ( fun n hn ih => by norm_num [ Nat.pow_succ ] at * ; linarith ) k ( show k ≥ 8 by linarith );
  · norm_num [ Nat.add_div ];
    exact Nat.le_induction ( by norm_num )
      ( fun n hn ih => by norm_num [ Nat.pow_succ' ] at * ; linarith ) _ ( show k ≥ 8 by linarith )

/-
For each d with 2^n + n < d ≤ spB n, there exists a maximal clique of size d.
-/
theorem big_clique_exists (n : ℕ) (hn : n ≥ 16) (d : ℕ)
    (hd1 : 2 ^ n + n < d) (hd2 : d ≤ spB n) :
    ∃ s : Finset (SpVtx n (spA n)),
      IsMaximalClique (spGraph n) s ∧ s.card = d := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin (n / 2)), ∑ i ∈ S, 2 ^ (i : ℕ) = spB n - d := by
    apply binary_expansion;
    rw [ tsub_lt_iff_left ] <;> try linarith;
    unfold spB at *;
    linarith [ Nat.sub_add_cancel ( show 1 ≤ 2 ^ n + n from by linarith [ Nat.one_le_pow n 2 zero_lt_two ] ), spA_le_pow_half n hn ];
  refine' ⟨ bigClique n ( Finset.image ( fun i ↦ ⟨ i.val, lt_of_lt_of_le i.2 ( Nat.div_le_self _ _ ) ⟩ ) S ), _, _ ⟩;
  · apply bigClique_isMaximalClique;
    · grind;
    · unfold isGeneric; aesop;
  · rw [ bigClique_card, Finset.sum_image ];
    · exact Nat.sub_eq_of_eq_add <| by linarith! [ Nat.sub_add_cancel hd2 ] ;
    · exact fun x hx y hy hxy => Fin.ext <| by simpa using congr_arg Fin.val hxy;

end Erdos927
