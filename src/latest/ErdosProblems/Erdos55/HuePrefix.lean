/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import ErdosProblems.Erdos55.HueBalance

/-!
# Finite prefixes of an infinite set, split by rank hue

This file identifies the first `Nat.count (· ∈ A) (N+1)` terms of the
canonical increasing enumeration with `A ∩ [0,N]`, and transports the
abstract hue-balance inequalities to actual finite sets of integers.
-/

namespace Erdos55

open scoped BigOperators

noncomputable def enumeration (A : Set ℕ) (k : ℕ) : ℕ :=
  Nat.nth (fun n ↦ n ∈ A) k

noncomputable def prefixLength (A : Set ℕ) (N : ℕ) : ℕ :=
  by
    classical
    exact Nat.count (fun n ↦ n ∈ A) (N + 1)

noncomputable def rankPrefix (A : Set ℕ) (N : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.range (prefixLength A N)).image (enumeration A)

noncomputable def rankHuePrefix (A : Set ℕ) (h s N : ℕ) : Finset ℕ :=
  by
    classical
    exact (residueIndices (prefixLength A N) h s).image (enumeration A)

theorem enumeration_injective {A : Set ℕ} (hA : A.Infinite) :
    Function.Injective (enumeration A) := by
  intro i j hij
  apply Nat.nth_injective (p := fun n ↦ n ∈ A) hA
  simpa only [enumeration] using hij

theorem enumeration_monotone {A : Set ℕ} (hA : A.Infinite) :
    Monotone (enumeration A) := by
  intro i j hij
  exact Nat.nth_monotone (p := fun n ↦ n ∈ A) hA hij

theorem mem_rankPrefix_iff {A : Set ℕ} (hA : A.Infinite) {N a : ℕ} :
    a ∈ rankPrefix A N ↔ a ∈ A ∧ a ≤ N := by
  classical
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨k, hk, rfl⟩
    have hklt : k < prefixLength A N := Finset.mem_range.mp hk
    have hnthlt : enumeration A k < N + 1 := by
      exact (Nat.lt_nth_iff_count_lt (p := fun n ↦ n ∈ A) hA).mp
        (by simpa [prefixLength] using hklt)
    exact ⟨Nat.nth_mem_of_infinite hA k, by omega⟩
  · rintro ⟨haA, haN⟩
    let k := rankIn A a
    have hklt : k < prefixLength A N := by
      exact (Nat.lt_nth_iff_count_lt (p := fun n ↦ n ∈ A) hA).mpr (by
        rw [show Nat.nth (fun n ↦ n ∈ A) k = a by
          simpa [k] using nth_rankIn haA]
        omega)
    apply Finset.mem_image.mpr
    exact ⟨k, Finset.mem_range.mpr hklt, by simpa [enumeration, k] using nth_rankIn haA⟩

theorem mem_rankHuePrefix_iff {A : Set ℕ} (hA : A.Infinite)
    {h s N a : ℕ} :
    a ∈ rankHuePrefix A h s N ↔
      a ∈ A ∧ a ≤ N ∧ hueIn A h a = s := by
  classical
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨k, hk, rfl⟩
    have hk' := Finset.mem_filter.mp hk
    have hklt : k < prefixLength A N := Finset.mem_range.mp hk'.1
    have hnthlt : enumeration A k < N + 1 := by
      exact (Nat.lt_nth_iff_count_lt (p := fun n ↦ n ∈ A) hA).mp
        (by simpa [prefixLength] using hklt)
    refine ⟨Nat.nth_mem_of_infinite hA k, by omega, ?_⟩
    change rankIn A (Nat.nth (fun n ↦ n ∈ A) k) % h = s
    rw [rankIn_nth hA]
    exact hk'.2
  · rintro ⟨haA, haN, hahue⟩
    let k := rankIn A a
    have hklt : k < prefixLength A N := by
      exact (Nat.lt_nth_iff_count_lt (p := fun n ↦ n ∈ A) hA).mpr (by
        rw [show Nat.nth (fun n ↦ n ∈ A) k = a by
          simpa [k] using nth_rankIn haA]
        omega)
    have hkres : k % h = s := by simpa [hueIn, k] using hahue
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hklt, hkres⟩, ?_⟩
    simpa [enumeration, k] using nth_rankIn haA

theorem sum_rankPrefix {A : Set ℕ} (hA : A.Infinite) (N : ℕ) :
    (∑ a ∈ rankPrefix A N, a) =
      ∑ k ∈ Finset.range (prefixLength A N), enumeration A k := by
  classical
  rw [rankPrefix, Finset.sum_image (enumeration_injective hA).injOn]

theorem sum_rankHuePrefix {A : Set ℕ} (hA : A.Infinite) (h s N : ℕ) :
    (∑ a ∈ rankHuePrefix A h s N, a) =
      ∑ k ∈ residueIndices (prefixLength A N) h s, enumeration A k := by
  classical
  rw [rankHuePrefix, Finset.sum_image (enumeration_injective hA).injOn]

theorem huePrefix_sum_balance {A : Set ℕ} (hA : A.Infinite)
    {h s N : ℕ} (hh : 0 < h) :
    h * (∑ a ∈ rankHuePrefix A h s N, a) ≤
      (∑ a ∈ rankPrefix A N, a) + 2 * h * N := by
  classical
  rw [sum_rankHuePrefix hA, sum_rankPrefix hA]
  apply mul_sum_residueIndices_le_of_monotone (enumeration A) hh
  · exact enumeration_monotone hA
  · intro k hk
    have hnthlt : enumeration A k < N + 1 := by
      exact (Nat.lt_nth_iff_count_lt (p := fun n ↦ n ∈ A) hA).mp
        (by simpa [prefixLength] using hk)
    omega

theorem sum_exp_rankPrefix {A : Set ℕ} (hA : A.Infinite) (N q : ℕ) :
    (∑ a ∈ rankPrefix A N, Real.exp (-(a : ℝ) / q)) =
      ∑ k ∈ Finset.range (prefixLength A N),
        Real.exp (-(enumeration A k : ℝ) / q) := by
  classical
  rw [rankPrefix, Finset.sum_image (enumeration_injective hA).injOn]

theorem sum_exp_rankHuePrefix {A : Set ℕ} (hA : A.Infinite)
    (h s N q : ℕ) :
    (∑ a ∈ rankHuePrefix A h s N, Real.exp (-(a : ℝ) / q)) =
      ∑ k ∈ residueIndices (prefixLength A N) h s,
        Real.exp (-(enumeration A k : ℝ) / q) := by
  classical
  rw [rankHuePrefix, Finset.sum_image (enumeration_injective hA).injOn]

theorem huePrefix_exp_balance {A : Set ℕ} (hA : A.Infinite)
    {h s N q : ℕ} (hh : 0 < h) (hq : 0 < q) :
    (h : ℝ) * (∑ a ∈ rankHuePrefix A h s N,
        Real.exp (-(a : ℝ) / q)) ≤
      (∑ a ∈ rankPrefix A N, Real.exp (-(a : ℝ) / q)) + h := by
  classical
  rw [sum_exp_rankHuePrefix hA, sum_exp_rankPrefix hA]
  let w : ℕ → ℝ := fun k ↦ Real.exp (-(enumeration A k : ℝ) / q)
  have hw : Antitone w := by
    intro i j hij
    apply Real.exp_le_exp.mpr
    have henum : enumeration A i ≤ enumeration A j := enumeration_monotone hA hij
    apply div_le_div_of_nonneg_right
    · exact neg_le_neg (by exact_mod_cast henum)
    · positivity
  have hbase := natCast_mul_sum_residueIndices_le_of_antitone
    (m := prefixLength A N) (s := s) w hh hw (fun k ↦ Real.exp_pos _ |>.le)
  have hwzero : w 0 ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  dsimp only [w] at hbase hwzero ⊢
  calc
    (h : ℝ) *
          (∑ k ∈ residueIndices (prefixLength A N) h s,
            Real.exp (-(enumeration A k : ℝ) / q)) ≤
        (∑ k ∈ Finset.range (prefixLength A N),
            Real.exp (-(enumeration A k : ℝ) / q)) +
          (h : ℝ) * Real.exp (-(enumeration A 0 : ℝ) / q) := hbase
    _ ≤ (∑ k ∈ Finset.range (prefixLength A N),
            Real.exp (-(enumeration A k : ℝ) / q)) + h := by
      apply add_le_add_right
      simpa using mul_le_mul_of_nonneg_left hwzero (Nat.cast_nonneg h)

end Erdos55
