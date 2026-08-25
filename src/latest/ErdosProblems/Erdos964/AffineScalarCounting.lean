import ErdosProblems.Erdos964.AffineSquarefreeRoots

/-!
# The scalar divisor count for the affine product

Each root modulo `d` contributes `N/d` with error at most one on the
doubling interval. Together with CRT this gives the first arithmetic
counting formula for the scalar GGPY sieve.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

def affineProductMultipleCount (A B : Fin 3 → ℕ) (N d : ℕ) : ℕ :=
  ((Finset.Ico N (2 * N)).filter (fun n => d ∣ ∏ i, (A i * n + B i))).card

theorem mod_mem_affineProductRoots_iff (A B : Fin 3 → ℕ) (d n : ℕ) (hd : 0 < d) :
    n % d ∈ affineProductRoots A B d ↔ d ∣ ∏ i, (A i * n + B i) := by
  have hmod : n % d ≡ n [MOD d] := by simp [Nat.ModEq]
  have hpoly := affine_product_modEq A B hmod
  constructor
  · intro h
    exact Nat.modEq_zero_iff_dvd.mp
      (hpoly.symm.trans (Nat.modEq_zero_iff_dvd.mpr (Finset.mem_filter.mp h).2))
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt n hd),
      Nat.modEq_zero_iff_dvd.mp (hpoly.trans (Nat.modEq_zero_iff_dvd.mpr h))⟩

theorem affineProductMultipleCount_eq_sum_roots (A B : Fin 3 → ℕ) (N d : ℕ) (hd : 0 < d) :
    affineProductMultipleCount A B N d = ∑ a ∈ affineProductRoots A B d,
      ((Finset.Ico N (2 * N)).filter (fun n => n ≡ a [MOD d])).card := by
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.Ico N (2 * N)) (affineProductRoots A B d) (fun n => n % d)
  have hfilter : (Finset.Ico N (2 * N)).filter (fun n => n % d ∈ affineProductRoots A B d) =
      (Finset.Ico N (2 * N)).filter (fun n => d ∣ ∏ i, (A i * n + B i)) := by
    apply Finset.filter_congr
    intro n _
    exact mod_mem_affineProductRoots_iff A B d n hd
  rw [hfilter] at hfiber
  calc
    _ = ∑ a ∈ affineProductRoots A B d,
        ((Finset.Ico N (2 * N)).filter (fun n => n % d = a)).card := hfiber.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      have hal := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
      congr 1
      apply Finset.filter_congr
      intro n _
      simp only [Nat.ModEq, Nat.mod_eq_of_lt hal]

theorem affineProductMultipleCount_error_le_roots (A B : Fin 3 → ℕ) (N d : ℕ) (hd : 0 < d) :
    |(affineProductMultipleCount A B N d : ℝ) -
        (N : ℝ) / d * (affineProductRoots A B d).card| ≤
      (affineProductRoots A B d).card := by
  have hcount : (affineProductMultipleCount A B N d : ℝ) =
      ∑ a ∈ affineProductRoots A B d,
        (((Finset.Ico N (2 * N)).filter (fun n => n ≡ a [MOD d])).card : ℝ) := by
    exact_mod_cast affineProductMultipleCount_eq_sum_roots A B N d hd
  have herr (a : ℕ) :
      |(((Finset.Ico N (2 * N)).filter (fun n => n ≡ a [MOD d])).card : ℝ) -
          (N : ℝ) / d| ≤ 1 := by
    obtain ⟨e, he, hcard⟩ := doublingIntervalModEq_card_decomposition N d a hd
    rw [hcard, add_sub_cancel_left]
    exact he
  have hid : (affineProductMultipleCount A B N d : ℝ) -
      (N : ℝ) / d * (affineProductRoots A B d).card =
      ∑ a ∈ affineProductRoots A B d,
        ((((Finset.Ico N (2 * N)).filter (fun n => n ≡ a [MOD d])).card : ℝ) - (N : ℝ) / d) := by
    rw [hcount, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hid]
  calc
    _ ≤ ∑ a ∈ affineProductRoots A B d,
        |(((Finset.Ico N (2 * N)).filter (fun n => n ≡ a [MOD d])).card : ℝ) - (N : ℝ) / d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ affineProductRoots A B d, (1 : ℝ) := Finset.sum_le_sum (fun a _ => herr a)
    _ = _ := by simp

theorem normalized_affineProductMultipleCount_error (A B : Fin 3 → ℕ) (v N d : ℕ)
    (hd : Squarefree d) (hdM : d.Coprime (affineNormalizationModulus A B)) :
    |(affineProductMultipleCount (fun i => A i * affineNormalizationModulus A B)
        (fun i => A i * v + B i) N d : ℝ) -
      (N : ℝ) / d * (3 : ℝ) ^ d.primeFactors.card| ≤ (3 : ℝ) ^ d.primeFactors.card := by
  have h := affineProductMultipleCount_error_le_roots
    (fun i => A i * affineNormalizationModulus A B) (fun i => A i * v + B i) N d
    (Nat.pos_of_ne_zero hd.ne_zero)
  rw [normalized_affineProductRoots_card_squarefree A B v d hd hdM] at h
  exact_mod_cast h

end Erdos964
