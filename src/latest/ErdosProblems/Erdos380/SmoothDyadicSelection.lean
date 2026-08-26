import ErdosProblems.Erdos380.SmoothDyadicLower
import Mathlib.Data.Nat.Find

/-! # Choosing the dyadic prime rectangle for arbitrary dyadic endpoints -/

open scoped BigOperators

namespace Erdos380

def topDyadicSum (Y k : ℕ) : ℕ := ∑ i ∈ Finset.range k, (Y - i)

@[simp] lemma topDyadicSum_zero (Y : ℕ) : topDyadicSum Y 0 = 0 := by simp [topDyadicSum]

lemma topDyadicSum_succ (Y k : ℕ) :
    topDyadicSum Y (k + 1) = topDyadicSum Y k + (Y - k) := by
  exact Finset.sum_range_succ _ _

lemma two_mul_dyadicRectangleExponent (b k : ℕ) :
    2 * dyadicRectangleExponent b k = k * (2 * b + k + 1) := by
  induction k with
  | zero => simp [dyadicRectangleExponent]
  | succ k ih =>
    have hsum : dyadicRectangleExponent b (k + 1) = dyadicRectangleExponent b k + (b + k + 1) := by
      simp only [dyadicRectangleExponent, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    rw [hsum]
    nlinarith

lemma two_mul_topDyadicSum_add_square (Y k : ℕ) (hk : k ≤ Y) :
    2 * topDyadicSum Y k + k ^ 2 = k * (2 * Y + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkY : k ≤ Y := by omega
    have hsub : Y - k + k = Y := Nat.sub_add_cancel hkY
    have hprev := ih hkY
    rw [topDyadicSum_succ]
    nlinarith

lemma topDyadicSum_eq_rectangle (Y k : ℕ) (hk : k ≤ Y) :
    topDyadicSum Y k = dyadicRectangleExponent (Y - k) k := by
  have htop := two_mul_topDyadicSum_add_square Y k hk
  have hrect := two_mul_dyadicRectangleExponent (Y - k) k
  have hsub : Y - k + k = Y := Nat.sub_add_cancel hk
  nlinarith

lemma mul_sub_le_topDyadicSum (Y k : ℕ) : k * (Y - k) ≤ topDyadicSum Y k := by
  calc
    k * (Y - k) = ∑ _i ∈ Finset.range k, (Y - k) := by simp
    _ ≤ _ := Finset.sum_le_sum fun i hi => Nat.sub_le_sub_left (by
      have := Finset.mem_range.mp hi
      omega) Y

/-- The last complete block of descending dyadic exponents leaves a
cofactor exponent no larger than the smallest prime-pool exponent. -/
lemma exists_dyadic_rectangle_for_endpoint {X Y K : ℕ}
    (hKY : K ≤ Y) (hX : X ≤ topDyadicSum Y K) :
    ∃ a b k : ℕ, a ≤ b ∧ b + k = Y ∧ k ≤ K ∧
      X = a + dyadicRectangleExponent b k ∧ k * (Y - K) ≤ X := by
  let k := Nat.findGreatest (fun j => topDyadicSum Y j ≤ X) K
  have hkK : k ≤ K := Nat.findGreatest_le K
  have hkY : k ≤ Y := hkK.trans hKY
  have hSk : topDyadicSum Y k ≤ X :=
    Nat.findGreatest_spec (P := fun j => topDyadicSum Y j ≤ X) (m := 0)
      (show 0 ≤ K by omega) (by simp)
  let a := X - topDyadicSum Y k
  have hXeq : X = a + topDyadicSum Y k := (Nat.sub_add_cancel hSk).symm
  have ha : a ≤ Y - k := by
    by_cases hk : k = K
    · have ha0 : a = 0 := by dsimp [a]; rw [hk]; omega
      omega
    · have hklt : k < K := by omega
      have hnext : ¬ topDyadicSum Y (k + 1) ≤ X :=
        Nat.findGreatest_is_greatest (P := fun j => topDyadicSum Y j ≤ X)
          (n := K) (k := k + 1) (show k < k + 1 by omega) (by omega)
      rw [topDyadicSum_succ] at hnext
      omega
  refine ⟨a, Y - k, k, ha, Nat.sub_add_cancel hkY, hkK, ?_, ?_⟩
  · simpa only [topDyadicSum_eq_rectangle Y k hkY] using hXeq
  · calc
      k * (Y - K) ≤ k * (Y - k) := Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hkK Y)
      _ ≤ topDyadicSum Y k := mul_sub_le_topDyadicSum Y k
      _ ≤ X := hSk

/-- A lower bound for every pair of dyadic endpoints in the stated range.
The auxiliary `K` controls how far the selected prime pools descend. -/
theorem exists_smoothCount_all_dyadic_lower : ∃ b₀ : ℕ,
    ∀ X Y K : ℕ, K ≤ Y → b₀ ≤ Y - K → X ≤ K * (Y - K) →
      ∃ k : ℕ, k ≤ K ∧ k * (Y - K) ≤ X ∧
        (2 : ℝ) ^ X ≤ (20 * Y : ℝ) ^ k * (smoothCount (2 ^ X) (2 ^ Y) : ℝ) := by
  obtain ⟨b₀, hb₀⟩ := exists_smoothCount_dyadic_lower
  refine ⟨b₀, fun X Y K hKY hb hX => ?_⟩
  obtain ⟨a, b, k, hab, hbk, hkK, hXe, hkX⟩ :=
    exists_dyadic_rectangle_for_endpoint hKY (hX.trans (mul_sub_le_topDyadicSum Y K))
  have hbb : b₀ ≤ b := by omega
  have hbound := hb₀ b hbb a k hab
  refine ⟨k, hkK, hkX, ?_⟩
  simpa only [← hXe, ← Nat.cast_add, hbk] using hbound

end Erdos380
