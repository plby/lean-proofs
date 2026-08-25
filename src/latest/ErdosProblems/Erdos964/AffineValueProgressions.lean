import ErdosProblems.Erdos964.AffineCoprimeSquarefreeRoots

/-!
# Passing from an affine parameter to its value

An arithmetic progression for `n` becomes one for `A*n+B` modulo `A*q`.
Keeping the exact translated endpoints avoids an unproved boundary error.
-/

namespace Erdos964

open scoped BigOperators

theorem affine_modEq_scaled_iff (A B n c q : ℕ) (hA : 0 < A) :
    (A * n + B) ≡ (A * c + B) [MOD A * q] ↔ n ≡ c [MOD q] := by
  constructor
  · intro h
    exact Nat.ModEq.mul_left_cancel' hA.ne' (Nat.ModEq.add_right_cancel' B h)
  · intro h
    exact (h.mul_left' A).add_right B

theorem affine_interval_residue_image (A B N q c : ℕ) (hA : 0 < A) :
    (((Finset.Ico N (2 * N)).filter (fun n => n ≡ c [MOD q])).image
      (fun n => A * n + B)) =
      (Finset.Ico (A * N + B) (A * (2 * N) + B)).filter
        (fun m => m ≡ A * c + B [MOD A * q]) := by
  ext m
  constructor
  · intro hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    have hn' := Finset.mem_filter.mp hn
    have hnb := Finset.mem_Ico.mp hn'.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
      ⟨Nat.add_le_add_right (Nat.mul_le_mul_left A hnb.1) B,
        Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hnb.2 hA) B⟩,
      (affine_modEq_scaled_iff A B n c q hA).mpr hn'.2⟩
  · intro hm
    have hm' := Finset.mem_filter.mp hm
    have hmb := Finset.mem_Ico.mp hm'.1
    have hBm : B ≤ m := by omega
    have hmodA : m ≡ B [MOD A] := by
      have h := hm'.2.of_mul_right q
      have hbase : A * c + B ≡ B [MOD A] := by simp [Nat.ModEq]
      exact h.trans hbase
    have hsub : m - B ≡ 0 [MOD A] := by
      apply Nat.ModEq.add_right_cancel' B
      simpa only [Nat.sub_add_cancel hBm, zero_add] using hmodA
    obtain ⟨n, hn⟩ := Nat.modEq_zero_iff_dvd.mp hsub
    have heq : A * n + B = m := by rw [← hn, Nat.sub_add_cancel hBm]
    have hnlo : N ≤ n := by
      by_contra h
      have hlt := Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge h) hA
      rw [← heq] at hmb
      omega
    have hnhi : n < 2 * N := by
      by_contra h
      have hle := Nat.mul_le_mul_left A (Nat.le_of_not_gt h)
      rw [← heq] at hmb
      omega
    have hnmod : n ≡ c [MOD q] := by
      apply (affine_modEq_scaled_iff A B n c q hA).mp
      rw [heq]
      exact hm'.2
    exact Finset.mem_image.mpr ⟨n, Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨hnlo, hnhi⟩, hnmod⟩, heq⟩

theorem sum_affine_interval_residue (A B N q c : ℕ) (hA : 0 < A) (F : ℕ → ℝ) :
    (∑ n ∈ (Finset.Ico N (2 * N)).filter (fun n => n ≡ c [MOD q]), F (A * n + B)) =
      ∑ m ∈ (Finset.Ico (A * N + B) (A * (2 * N) + B)).filter
        (fun m => m ≡ A * c + B [MOD A * q]), F m := by
  rw [← affine_interval_residue_image A B N q c hA]
  symm
  apply Finset.sum_image
  intro n _ r _ hnr
  exact Nat.eq_of_mul_eq_mul_left hA (Nat.add_right_cancel hnr)

theorem affine_value_residue_coprime (A B q c : ℕ) (hBA : B.Coprime A)
    (hqc : q.Coprime (A * c + B)) : (A * c + B).Coprime (A * q) := by
  have hmod : A * c + B ≡ B [MOD A] := by simp [Nat.ModEq]
  have hcA : (A * c + B).Coprime A := by
    change Nat.gcd (A * c + B) A = 1
    rw [hmod.gcd_eq]
    exact hBA
  exact hcA.mul_right hqc.symm

theorem sum_affine_coprime_product_classes (A B : Fin 3 → ℕ) (j : Fin 3)
    (N q : ℕ) (hq : 0 < q) (F : ℕ → ℝ) :
    (∑ n ∈ (Finset.Ico N (2 * N)).filter
      (fun n => q ∣ ∏ i, (A i * n + B i) ∧ q.Coprime (A j * n + B j)), F n) =
      ∑ c ∈ affineCoprimeProductRoots A B j q,
        ∑ n ∈ (Finset.Ico N (2 * N)).filter (fun n => n ≡ c [MOD q]), F n := by
  have hfiber := Finset.sum_fiberwise_eq_sum_filter (Finset.Ico N (2 * N))
    (affineCoprimeProductRoots A B j q) (fun n => n % q) F
  have hfilter : (Finset.Ico N (2 * N)).filter
      (fun n => n % q ∈ affineCoprimeProductRoots A B j q) =
      (Finset.Ico N (2 * N)).filter
        (fun n => q ∣ ∏ i, (A i * n + B i) ∧ q.Coprime (A j * n + B j)) := by
    apply Finset.filter_congr
    intro n _
    exact mod_mem_affineCoprimeProductRoots_iff A B j q n hq
  rw [hfilter] at hfiber
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro c hc
  have hclt := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).1
  congr 1
  apply Finset.filter_congr
  intro n _
  simp only [Nat.ModEq, Nat.mod_eq_of_lt hclt]

end Erdos964
