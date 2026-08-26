import ErdosProblems.Erdos67.StationaryHarmonicAverage

/-!
# Truncating a harmonic average at a fixed fraction of its endpoint

The harmonic mass between `N/d` and `N` is bounded by `d`. This deliberately
coarse bound is sufficient for conditional dilation and requires no logarithmic
asymptotic formula.
-/

open scoped BigOperators Topology
open Finset Filter

namespace Erdos67.StationaryHarmonicAverage

/-- A harmonic prefix with the normalization belonging to a possibly larger endpoint. -/
noncomputable def truncatedAverage (N M : ℕ) (F : ℕ → ℝ) : ℝ :=
  (∑ j ∈ range M, ((j + 1 : ℕ) : ℝ)⁻¹ * F (j + 1)) / mass N

theorem truncatedAverage_self (N : ℕ) (F : ℕ → ℝ) :
    truncatedAverage N N F = average N F := rfl

theorem truncatedAverage_sub (N M : ℕ) (F G : ℕ → ℝ) :
    truncatedAverage N M (fun n ↦ F n - G n) =
      truncatedAverage N M F - truncatedAverage N M G := by
  simp only [truncatedAverage, mul_sub, Finset.sum_sub_distrib, sub_div]

theorem sum_mul_truncatedAverage {A : Type*} [Fintype A] (p : A → ℝ)
    (F : A → ℕ → ℝ) (N M : ℕ) :
    (∑ a, p a * truncatedAverage N M (F a)) =
      truncatedAverage N M (fun n ↦ ∑ a, p a * F a n) := by
  unfold truncatedAverage
  simp_rw [← mul_div_assoc, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem mass_add (m k : ℕ) :
    mass (m + k) = mass m + ∑ n ∈ range k, ((m + n + 1 : ℕ) : ℝ)⁻¹ := by
  exact Finset.sum_range_add (fun n ↦ ((n + 1 : ℕ) : ℝ)⁻¹) m k

theorem mass_mono : Monotone mass := by
  intro m n hmn
  unfold mass
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
    (fun _ _ _ ↦ by positivity)

theorem abs_truncatedAverage_le {N M : ℕ} (hN : 0 < N) (hMN : M ≤ N)
    (F : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ n, |F n| ≤ B) :
    |truncatedAverage N M F| ≤ B := by
  unfold truncatedAverage
  rw [abs_div, abs_of_pos (mass_pos hN)]
  apply (div_le_iff₀ (mass_pos hN)).mpr
  calc
    |∑ j ∈ range M, ((j + 1 : ℕ) : ℝ)⁻¹ * F (j + 1)| ≤
        ∑ j ∈ range M, ((j + 1 : ℕ) : ℝ)⁻¹ * B := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((j + 1 : ℕ) : ℝ)⁻¹)]
      exact mul_le_mul_of_nonneg_left (hF _) (by positivity)
    _ = mass M * B := by rw [← Finset.sum_mul]; rfl
    _ ≤ B * mass N := by
      rw [mul_comm B]
      exact mul_le_mul_of_nonneg_right (mass_mono hMN) hB

theorem mass_sub_mass_le {m n : ℕ} (hmn : m ≤ n) :
    mass n - mass m ≤ ((n - m : ℕ) : ℝ) / (m + 1 : ℕ) := by
  have hid := mass_add m (n - m)
  rw [Nat.add_sub_of_le hmn] at hid
  rw [hid, add_sub_cancel_left]
  calc
    (∑ j ∈ range (n - m), ((m + j + 1 : ℕ) : ℝ)⁻¹) ≤
        ∑ _ ∈ range (n - m), ((m + 1 : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro j _
      apply inv_anti₀ (by positivity)
      exact_mod_cast (by omega : m + 1 ≤ m + j + 1)
    _ = ((n - m : ℕ) : ℝ) / (m + 1 : ℕ) := by simp [div_eq_mul_inv]

theorem mass_sub_mass_div_le (n d : ℕ) (hd : 0 < d) :
    mass n - mass (n / d) ≤ d := by
  apply (mass_sub_mass_le (Nat.div_le_self n d)).trans
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n / d + 1 : ℕ))).mpr
  have hmod := Nat.mod_lt n hd
  have hsplit := Nat.mod_add_div n d
  have hn : n ≤ d * (n / d + 1) := by nlinarith
  have hsub : n - n / d ≤ d * (n / d + 1) := (Nat.sub_le n _).trans hn
  exact_mod_cast hsub

theorem harmonic_prefix_sub_identity (F : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    (∑ j ∈ range n, ((j + 1 : ℕ) : ℝ)⁻¹ * F (j + 1)) -
      (∑ j ∈ range m, ((j + 1 : ℕ) : ℝ)⁻¹ * F (j + 1)) =
        ∑ j ∈ range (n - m), ((m + j + 1 : ℕ) : ℝ)⁻¹ * F (m + j + 1) := by
  have h := Finset.sum_range_add (fun j ↦ ((j + 1 : ℕ) : ℝ)⁻¹ * F (j + 1)) m (n - m)
  rw [Nat.add_sub_of_le hmn] at h
  rw [h, add_sub_cancel_left]

theorem abs_harmonic_prefix_sub_le (F : ℕ → ℝ) (B : ℝ) (hF : ∀ n, |F n| ≤ B)
    {m n : ℕ} (hmn : m ≤ n) :
    |(∑ j ∈ range n, ((j + 1 : ℕ) : ℝ)⁻¹ * F (j + 1)) -
      (∑ j ∈ range m, ((j + 1 : ℕ) : ℝ)⁻¹ * F (j + 1))| ≤
        (mass n - mass m) * B := by
  rw [harmonic_prefix_sub_identity F hmn]
  have hid := mass_add m (n - m)
  rw [Nat.add_sub_of_le hmn] at hid
  rw [hid, add_sub_cancel_left, Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((m + j + 1 : ℕ) : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_left (hF _) (by positivity)

/-- The same normalizing mass is retained on both sides. -/
theorem abs_average_sub_truncated_le (F : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ n, |F n| ≤ B) {n : ℕ} (hn : 0 < n) (d : ℕ) (hd : 0 < d) :
    |average n F -
      (∑ j ∈ range (n / d), ((j + 1 : ℕ) : ℝ)⁻¹ * F (j + 1)) / mass n| ≤
        (d : ℝ) * B / mass n := by
  unfold average
  rw [← sub_div, abs_div, abs_of_pos (mass_pos hn)]
  apply div_le_div_of_nonneg_right _ (mass_pos hn).le
  exact (abs_harmonic_prefix_sub_le F B hF (Nat.div_le_self n d)).trans
    (mul_le_mul_of_nonneg_right (mass_sub_mass_div_le n d hd) hB)

end Erdos67.StationaryHarmonicAverage
