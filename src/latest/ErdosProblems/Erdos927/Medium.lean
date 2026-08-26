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
import ErdosProblems.Erdos927.Lookup

set_option linter.mathlibStandardSet false

namespace Erdos927

/-
# Medium Clique Construction

For each d with n+1 ≤ d ≤ 2^n + n, we construct a maximal clique of size d
in Spencer's graph. The clique consists of yStar, a subset of y-vertices,
and all C_i for i not in the selected subset.
-/

/-- The medium clique for selector set S:
  {yStar} ∪ {y_i : i ∈ S} ∪ ⋃_{i ∉ S} C_i -/
noncomputable def medClique (n : ℕ) (S : Finset (Fin n)) : Finset (SpVtx n (spA n)) := by
  classical
  exact {.yStar} ∪
  S.biUnion (fun i => {.y i}) ∪
  (Finset.univ \ S).biUnion (fun i => Finset.univ.image fun j => SpVtx.c i j)

/-- yStar is in the medium clique. -/
lemma yStar_mem_medClique (n : ℕ) (S : Finset (Fin n)) :
    SpVtx.yStar ∈ medClique n S := by
  classical
  simp [medClique]

/-- y_i is in the medium clique iff i ∈ S. -/
lemma y_mem_medClique_iff (n : ℕ) (S : Finset (Fin n)) (i : Fin n) :
    SpVtx.y i ∈ medClique n S ↔ i ∈ S := by
  classical
  simp [medClique, SpVtx.y.injEq]

/-- c_i_j is in the medium clique iff i ∉ S. -/
lemma c_mem_medClique_iff (n : ℕ) (S : Finset (Fin n)) (i : Fin n) (j : Fin (cSize i)) :
    SpVtx.c i j ∈ medClique n S ↔ i ∉ S := by
  classical
  simp [medClique, SpVtx.c.injEq]

/-- cStar vertices are NOT in the medium clique. -/
lemma cStar_not_mem_medClique (n : ℕ) (S : Finset (Fin n)) (j : Fin (spA n)) :
    SpVtx.cStar j ∉ medClique n S := by
  classical
  simp [medClique]

/-- z is NOT in the medium clique. -/
lemma z_not_mem_medClique (n : ℕ) (S : Finset (Fin n)) :
    SpVtx.z ∉ medClique n S := by
  classical
  simp [medClique]

/-
The medium clique is a clique.
-/
lemma medClique_isClique (n : ℕ) (S : Finset (Fin n)) :
    (spGraph n).IsClique (↑(medClique n S) : Set _) := by
  classical
  intro x hx y hy hxy; unfold medClique at hx hy; simp_all +decide [ ] ;
  unfold spGraph; unfold spAdj; aesop;

/-
The medium clique is maximal.
-/
lemma medClique_isMaximal (n : ℕ) (S : Finset (Fin n)) :
    ∀ t : Finset (SpVtx n (spA n)),
      (spGraph n).IsClique (↑t : Set _) → medClique n S ⊆ t → t = medClique n S := by
  classical
  intro t ht ht_sub
  have ht_eq : ∀ v ∈ t, v ∈ medClique n S := by
    intro v hv;
    rcases v with ( _ | _ | _ | _ | _ );
    · rename_i i;
      by_cases hi : i ∈ S <;> simp_all +decide [ medClique ];
      have := ht hv ( ht_sub <| show SpVtx.c i ⟨ 0, by simp +decide [ cSize ] ⟩ ∈ _ from by aesop ) ;
      simp_all +decide [ spGraph ] ;
      unfold spAdj at this; aesop;
    · exact yStar_mem_medClique n S;
    · rename_i i j;
      by_cases hi : i ∈ S <;> simp_all +decide [ medClique ];
      have := ht ( ht_sub ( Finset.mem_insert_of_mem ( Finset.mem_union_left _
        ( Finset.mem_biUnion.mpr ⟨ i, hi, Finset.mem_singleton_self _ ⟩ ) ) ) ) hv;
      simp_all +decide [ spGraph ] ;
      unfold spAdj at this; aesop;
    · have := ht ( show SpVtx.yStar ∈ t from ht_sub <| by simp +decide [ medClique ] ) hv;
      simp_all +decide [ spGraph ] ;
      cases this ; tauto;
    · have := ht ( show SpVtx.yStar ∈ t from ht_sub ( by simp +decide [ medClique ] ) ) hv;
      simp +decide [ ] at this;
      cases this ; contradiction;
  exact subset_antisymm ht_eq ht_sub

/-- The medium clique is a maximal clique. -/
lemma medClique_isMaximalClique (n : ℕ) (S : Finset (Fin n)) :
    IsMaximalClique (spGraph n) (medClique n S) :=
  ⟨medClique_isClique n S, medClique_isMaximal n S⟩

/-
The card of the medium clique.
-/
lemma medClique_card (n : ℕ) (S : Finset (Fin n)) :
    (medClique n S).card = 2 ^ n + n - ∑ i ∈ S, 2 ^ (i : ℕ) := by
  classical
  unfold medClique;
  rw [ Finset.card_union_of_disjoint, Finset.card_union_of_disjoint ] <;> norm_num;
  · rw [ Finset.card_biUnion, Finset.card_biUnion ] <;> norm_num;
    · rw [ Finset.sum_congr rfl fun i hi => Finset.card_image_of_injective _ fun x y hxy => by injection hxy ];
      simp only [Finset.card_univ, Fintype.card_fin]
      simp +arith +decide [cSize]
      have h_sum : ∑ i : Fin n, (2 ^ (i : ℕ) + 1) = 2 ^ n - 1 + n := by
        exact sum_cSize_Fin n;
      rw [ ← Finset.sum_sdiff ( Finset.subset_univ S ) ] at *;
      exact eq_tsub_of_add_eq ( by
          norm_num [ Finset.sum_add_distrib ] at *;
          linarith [ Nat.sub_add_cancel ( Nat.one_le_pow n 2 zero_lt_two ) ]
        );
    · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by aesop;
  · aesop;
  · simp +contextual [ Finset.disjoint_left ]

/-
For each d with n+1 ≤ d ≤ 2^n + n, there exists a maximal clique of size d.
-/
theorem medium_clique_exists (n : ℕ) (hn : n ≥ 2) (d : ℕ)
    (hd1 : n + 1 ≤ d) (hd2 : d ≤ 2 ^ n + n) :
    ∃ s : Finset (SpVtx n (spA n)),
      IsMaximalClique (spGraph n) s ∧ s.card = d := by
  classical
  -- Let α = 2^n + n - d. Then 0 ≤ α ≤ 2^n - 1.
  set α := 2 ^ n + n - d
  have hα_nonneg : 0 ≤ α := by
    exact Nat.zero_le _
  have hα_lt : α < 2 ^ n := by
    omega;
  obtain ⟨ S, hS ⟩ := binary_expansion n α hα_lt;
  exact ⟨ medClique n S, medClique_isMaximalClique n S, by rw [ medClique_card ] ; omega ⟩

end Erdos927
