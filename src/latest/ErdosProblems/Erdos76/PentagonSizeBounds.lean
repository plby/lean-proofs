/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos76.PentagonSizeTables

/-!
# The analytic bound on pentagon blob sizes

The finite tables in `PentagonSizeTables` only enumerate vectors whose five
entries lie in `{1, ..., 5}`.  This module proves the missing human step from
Section 7: if the five nonempty blobs have total size between 17 and 25 and
the standard pentagon packing does not exceed the stability threshold, then
every blob has size at most five.

The proof is the paper's Cauchy--Schwarz calculation.  If one blob has size
`a`, write `N` for the total and `Q` for the sum of the five squares.  The
packing inequality says `6Q <= N^2 + 5N`, while Cauchy--Schwarz on the other
four blobs says `(N-a)^2 <= 4(Q-a^2)`.  Consequently

`15a^2 - 6aN + N^2 - 10N <= 0`.

For `a >= 6` and `N <= 25` the left side is at least its value at `a=6`,
namely `(N-23)^2 + 11`, a contradiction.
-/

open Finset
open scoped BigOperators

namespace Erdos76

private lemma two_mul_fivePairSum_cast (x : Fin 5 → ℕ) :
    2 * (fivePairSum x : ℝ) =
      (∑ i, (x i : ℝ) ^ 2) - (fiveSizeSum x : ℝ) := by
  simp only [fivePairSum, fiveSizeSum, Nat.cast_sum, Nat.cast_choose_two]
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Cauchy--Schwarz and the pentagon packing inequality force every nonempty
blob in a graph of order at most 25 to have size at most five. -/
theorem pentagon_blobSize_le_five
    (x : Fin 5 → ℕ)
    (hpos : ∀ i, 1 ≤ x i)
    (hn17 : 17 ≤ fiveSizeSum x)
    (hn25 : fiveSizeSum x ≤ 25)
    (hineq : 12 * fivePairSum x ≤
      fiveSizeSum x * (fiveSizeSum x - 1)) :
    ∀ i, x i ≤ 5 := by
  intro i
  by_contra hi
  have hai : 6 ≤ x i := by omega
  let N : ℝ := fiveSizeSum x
  let a : ℝ := x i
  let Q : ℝ := ∑ j, (x j : ℝ) ^ 2
  have hNposNat : 0 < fiveSizeSum x := by omega
  have hcastIneq :
      12 * (fivePairSum x : ℝ) ≤
        (fiveSizeSum x : ℝ) * ((fiveSizeSum x : ℝ) - 1) := by
    calc
      12 * (fivePairSum x : ℝ) = ((12 * fivePairSum x : ℕ) : ℝ) := by
        norm_num
      _ ≤ ((fiveSizeSum x * (fiveSizeSum x - 1) : ℕ) : ℝ) := by
        exact_mod_cast hineq
      _ = (fiveSizeSum x : ℝ) * ((fiveSizeSum x : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ fiveSizeSum x)]
        norm_num
  have hupper : 6 * Q ≤ N ^ 2 + 5 * N := by
    have hpairs := two_mul_fivePairSum_cast x
    dsimp only [N, Q]
    nlinarith
  have hsumErase :
      (∑ j ∈ (Finset.univ : Finset (Fin 5)).erase i, (x j : ℝ)) = N - a := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Fin 5))
      (fun j ↦ (x j : ℝ)) (Finset.mem_univ i)
    dsimp only [N, a, fiveSizeSum]
    rw [Nat.cast_sum]
    exact eq_sub_of_add_eq h
  have hsqErase :
      (∑ j ∈ (Finset.univ : Finset (Fin 5)).erase i, (x j : ℝ) ^ 2) =
        Q - a ^ 2 := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Fin 5))
      (fun j ↦ (x j : ℝ) ^ 2) (Finset.mem_univ i)
    dsimp only [Q, a]
    exact eq_sub_of_add_eq h
  have hcardErase : ((Finset.univ : Finset (Fin 5)).erase i).card = 4 := by
    simp
  have hcauchy := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Fin 5)).erase i)
    (f := fun j ↦ (x j : ℝ))
  rw [hsumErase, hsqErase, hcardErase] at hcauchy
  norm_num at hcauchy
  have hpoly : 15 * a ^ 2 - 6 * a * N + N ^ 2 - 10 * N ≤ 0 := by
    nlinarith
  have ha6 : (6 : ℝ) ≤ a := by
    dsimp only [a]
    exact_mod_cast hai
  have hN25 : N ≤ 25 := by
    dsimp only [N]
    exact_mod_cast hn25
  have hfactor : 0 ≤ 15 * (a + 6) - 6 * N := by nlinarith
  have hmonotone :
      0 ≤ (a - 6) * (15 * (a + 6) - 6 * N) :=
    mul_nonneg (sub_nonneg.mpr ha6) hfactor
  have hsquare : 0 ≤ (N - 23) ^ 2 := sq_nonneg _
  nlinarith

/-- The analytic bound followed by the finite `B₁` table. -/
theorem pentagonB1Sizes_of_threshold
    (x : Fin 5 → ℕ)
    (hpos : ∀ i, 1 ≤ x i)
    (hn17 : 17 ≤ fiveSizeSum x)
    (hn25 : fiveSizeSum x ≤ 25)
    (hineq : 12 * fivePairSum x ≤
      fiveSizeSum x * (fiveSizeSum x - 1)) :
    PentagonB1Sizes x :=
  pentagonB1Sizes_of_bounded x hpos
    (pentagon_blobSize_le_five x hpos hn17 hn25 hineq) hn17 hineq

/-- The analytic bound also applies to the stronger one-flip inequality and
therefore feeds the finite `B₂` table. -/
theorem pentagonB2Sizes_of_threshold
    (x : Fin 5 → ℕ)
    (hpos : ∀ i, 1 ≤ x i)
    (hn17 : 17 ≤ fiveSizeSum x)
    (hn25 : fiveSizeSum x ≤ 25)
    (hineq : 12 * (fivePairSum x + 1) ≤
      fiveSizeSum x * (fiveSizeSum x - 1)) :
    PentagonB2Sizes x := by
  apply pentagonB2Sizes_of_bounded x hpos _ hn17 hineq
  apply pentagon_blobSize_le_five x hpos hn17 hn25
  omega

end Erdos76
