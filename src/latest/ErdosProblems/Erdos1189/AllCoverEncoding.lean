/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A finite universe containing every irreducible covering set of a fixed size.
Informal source: BBMST Sections 6 and 7.2.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.ArithmeticFrameStructure
import ErdosProblems.Erdos1189.SparseCoverCount
import ErdosProblems.Erdos1189.FrameUniverseBound

namespace Erdos1189

open Finset

lemma divisor_mem_fullProfile {N d : ℕ} (hN : N ≠ 0) (hd : d ∣ N) :
    d ∈ boundedProfileModuli N N.factorization := by
  exact mem_boundedProfileModuli hN hd (fun p =>
    (Nat.factorization_le_iff_dvd (ne_zero_of_dvd_ne_zero hN hd) hN).mpr hd p)

noncomputable def localCoverUniverse (N T k : ℕ) (η : ℝ) : Finset (Finset ℕ) :=
  if simpsonWeight N ≤ k then
    if k ≤ 4 * simpsonWeight N then frameUniverse N T k η
    else (boundedProfileModuli N N.factorization).powersetCard k
  else ∅

noncomputable def allCoverUniverse (T k : ℕ) (η : ℝ) : Finset (Finset ℕ) :=
  (range (2 ^ k + 1)).biUnion (fun N => localCoverUniverse N T k η)

theorem exists_allCoverUniverse {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ T : ℕ, ∀ k : ℕ, irreducibleSetsOfSize k ⊆ (allCoverUniverse T k η : Set (Finset ℕ)) := by
  obtain ⟨T, hframes⟩ := exists_uniform_frame_universe hη hη1
  refine ⟨T, ?_⟩
  intro k D hD
  obtain ⟨hD, hk⟩ := hD
  have hW : simpsonWeight (D.lcm id) ≤ k := by have := hD.simpson; omega
  have hN : D.lcm id ≤ 2 ^ k :=
    (le_two_pow_simpsonWeight hD.1.lcm_pos.ne').trans (Nat.pow_le_pow_right (by norm_num) hW)
  apply mem_biUnion.mpr
  refine ⟨D.lcm id, mem_range.mpr (by omega), ?_⟩
  unfold localCoverUniverse
  rw [if_pos hW]
  split_ifs with hefficient
  · have h := hframes D hD (by rw [hk]; exact_mod_cast hefficient)
    simpa only [hk] using h
  · exact mem_powersetCard.mpr ⟨fun d hd =>
      divisor_mem_fullProfile hD.1.lcm_pos.ne' (dvd_lcm hd), hk⟩

lemma allCoverUniverse_card_le_exp {T k : ℕ} {η B : ℝ}
    (hlocal : ∀ N, ((localCoverUniverse N T k η).card : ℝ) ≤ Real.exp B) :
    ((allCoverUniverse T k η).card : ℝ) ≤
      Real.exp (((k + 1 : ℕ) : ℝ) * Real.log 2 + B) := by
  have hsum : ((allCoverUniverse T k η).card : ℝ) ≤
      ∑ N ∈ range (2 ^ k + 1), ((localCoverUniverse N T k η).card : ℝ) := by
    exact_mod_cast card_biUnion_le
  have hpow : 2 ^ k + 1 ≤ 2 ^ (k + 1) := by
    have hpos : 0 < 2 ^ k := by positivity
    rw [pow_succ]
    omega
  calc
    _ ≤ _ := hsum
    _ ≤ ((2 ^ k + 1 : ℕ) : ℝ) * Real.exp B := by
      simpa only [sum_const, card_range, nsmul_eq_mul] using
        sum_le_sum (s := range (2 ^ k + 1)) (fun N _ => hlocal N)
    _ ≤ ((2 ^ (k + 1) : ℕ) : ℝ) * Real.exp B :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hpow) (Real.exp_pos B).le
    _ = _ := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num)]
      push_cast
      rfl

lemma irreducibleCount_le_allCoverUniverse {T k : ℕ} {η : ℝ}
    (hsub : irreducibleSetsOfSize k ⊆ (allCoverUniverse T k η : Set (Finset ℕ))) :
    irreducibleCount k ≤ (allCoverUniverse T k η).card := by
  simpa only [irreducibleCount, Set.ncard_coe_finset] using
    Set.ncard_le_ncard hsub (allCoverUniverse T k η).finite_toSet

end Erdos1189
