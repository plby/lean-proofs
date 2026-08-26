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
import ErdosProblems.Erdos927.Definitions

set_option linter.mathlibStandardSet false

namespace Erdos927

/-- Any specific graph on `Fin n` gives a lower bound on `g n`. -/
lemma le_g_of_graph {n : ℕ} (G : SimpleGraph (Fin n)) :
    (maximalCliqueSizes G).card ≤ g n :=
  Finset.le_sup (f := fun G => (maximalCliqueSizes G).card) (Finset.mem_univ G)

/-
A graph on any type with cardinality `n` gives a lower bound on `g n`.
  This lets us work with convenient vertex types rather than `Fin n`.
-/
lemma g_ge_of_card {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) {n : ℕ} (hn : Fintype.card α = n) :
    (maximalCliqueSizes G).card ≤ g n := by
  classical
  let e := Fintype.equivFinOfCardEq hn
  apply le_trans ?_ (le_g_of_graph (SimpleGraph.comap e.symm G))
  apply Finset.card_le_card
  intro k hk
  obtain ⟨s, hs, hsize⟩ := Finset.mem_image.mp hk
  have hmax : IsMaximalClique G s := (Finset.mem_filter.mp hs).2
  apply Finset.mem_image.mpr
  refine ⟨s.image e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
  · constructor
    · intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      change G.Adj (e.symm (e a)) (e.symm (e b))
      simpa only [Equiv.symm_apply_apply] using
        hmax.1 ha hb (fun hab => hxy (congrArg e hab))
    · intro t ht hsub
      have hpre : G.IsClique (↑(t.image e.symm) : Set α) := by
        intro x hx y hy hxy
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
        exact ht ha hb (fun hab => hxy (congrArg e.symm hab))
      have hsub' : s ⊆ t.image e.symm := by
        intro a ha
        exact Finset.mem_image.mpr
          ⟨e a, hsub (Finset.mem_image_of_mem e ha), e.symm_apply_apply a⟩
      have heq := hmax.2 (t.image e.symm) hpre hsub'
      rw [← heq, Finset.image_image]
      simp
  · rw [Finset.card_image_of_injective _ e.injective]
    exact hsize

/-- If for each `k ∈ sizes` there is a maximal clique of size `k`,
  then `sizes ⊆ maximalCliqueSizes G`. -/
lemma maximalCliqueSizes_card_ge {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) {sizes : Finset ℕ}
    (h : ∀ k ∈ sizes, ∃ s : Finset α, IsMaximalClique G s ∧ s.card = k) :
    sizes ⊆ maximalCliqueSizes G := by
  classical
  intro k hk
  obtain ⟨s, hs, rfl⟩ := h k hk
  exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩)

@[simp] lemma logStar_zero : logStar 0 = 0 := by unfold logStar; rfl
@[simp] lemma logStar_one : logStar 1 = 0 := by unfold logStar; rfl

lemma logStar_eq_succ {n : ℕ} (hn : n ≥ 2) :
    logStar n = logStar (Nat.log 2 n) + 1 := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp [logStar]

/-
`logStar` is monotone.
-/
lemma logStar_mono {m n : ℕ} (h : m ≤ n) : logStar m ≤ logStar n := by
  classical
  induction' n using Nat.strongRecOn with n ih generalizing m;
  rcases n with ( _ | _ | n ) <;> rcases m with ( _ | _ | m );
  all_goals norm_num [ logStar_eq_succ ] at *;
  convert ih _ _ _ using 1;
  · refine' Nat.le_of_lt_succ ( Nat.log_lt_of_lt_pow _ _ ) <;> norm_num;
    exact Nat.lt_two_pow_self;
  · exact Nat.log_mono_right ( by linarith )

/-
`logStar` is unbounded: for any `C`, there exists `n` with `logStar n > C`.
-/
lemma logStar_unbounded : ∀ C : ℕ, ∃ n : ℕ, C < logStar n := by
  classical
  intro C;
  induction' C with C ih;
  · exact ⟨ 2, by rw [logStar_eq_succ (by norm_num)]; simp ⟩;
  · obtain ⟨ n, hn ⟩ := ih;
    use 2^(n+1);
    rw [ logStar_eq_succ ] <;> norm_num [ Nat.log_pow ];
    · exact hn.trans_le ( logStar_mono ( Nat.le_succ _ ) );
    · exact le_self_pow ( by norm_num ) ( Nat.succ_ne_zero _ )

/-
# Binary Expansion Helper

For any α < 2^m, there exists a subset S of Fin m whose sum of 2^i equals α.
-/

/-
Every natural number less than 2^m can be expressed as a sum of distinct
powers of 2 with exponents in {0, ..., m-1}.
-/
lemma binary_expansion (m α : ℕ) (h : α < 2 ^ m) :
    ∃ S : Finset (Fin m), ∑ i ∈ S, 2 ^ (i : ℕ) = α := by
  classical
  induction' m with m ih generalizing α;
  · aesop;
  · by_cases h_case : α < 2 ^ m;
    · exact Exists.elim ( ih α h_case ) fun S hS => ⟨ S.image ( Fin.castSucc ),
        by simpa [ Finset.sum_image ] using hS ⟩;
    · -- Since α ≥ 2^m, we can write α as 2^m + β for some β < 2^m.
      obtain ⟨β, hβ⟩ : ∃ β, α = 2 ^ m + β ∧ β < 2 ^ m := by
        exact ⟨ α - 2 ^ m, by rw [ Nat.add_sub_cancel' ( le_of_not_gt h_case ) ],
          by rw [ tsub_lt_iff_left ( le_of_not_gt h_case ) ] ; rw [ pow_succ' ] at h; linarith ⟩;
      obtain ⟨ S, hS ⟩ := ih β hβ.2;
      use Finset.image ( fun i : Fin m => Fin.castSucc i ) S ∪ { Fin.last m } ;
      simp_all +decide [ Finset.sum_image ]

/-
The sum of all 2^i for i in Fin m equals 2^m - 1.
-/
lemma sum_pow_two_Fin (m : ℕ) :
    ∑ i : Fin m, 2 ^ (i : ℕ) = 2 ^ m - 1 := by
  classical
  induction' m with m ih;
  · rfl;
  · norm_num [ Fin.sum_univ_castSucc, pow_succ', ih ];
    grind +qlia

/-
The sum of (2^i + 1) for i in Fin m equals 2^m - 1 + m.
-/
lemma sum_cSize_Fin (m : ℕ) :
    ∑ i : Fin m, (2 ^ (i : ℕ) + 1) = 2 ^ m - 1 + m := by
  classical
  simp +arith +decide [ Finset.sum_add_distrib, sum_pow_two_Fin ]

end Erdos927
