import ErdosProblems.Erdos421.DirichletGram

/-! # Subdividing the time interval in the large-value estimate -/

namespace Erdos421

noncomputable def timeSlice (S : Finset ℕ) (t : ℕ → ℝ) (A U : ℝ) (k : ℕ) : Finset ℕ :=
  S.filter (fun i ↦ ⌊(t i - A) / U⌋₊ = k)

theorem timeSlice_subset (S : Finset ℕ) (t : ℕ → ℝ) (A U : ℝ) (k : ℕ) :
    timeSlice S t A U k ⊆ S := Finset.filter_subset _ _

theorem timeSlice_bounds {S : Finset ℕ} {t : ℕ → ℝ} {A U : ℝ} {k i : ℕ}
    (hU : 0 < U) (hA : A ≤ t i) (hi : i ∈ timeSlice S t A U k) :
    A + k * U ≤ t i ∧ t i ≤ A + (k + 1) * U := by
  have hcode := (Finset.mem_filter.mp hi).2
  have hlo := Nat.floor_le (div_nonneg (sub_nonneg.mpr hA) hU.le)
  have hhi := Nat.lt_floor_add_one ((t i - A) / U)
  rw [hcode] at hlo hhi
  have hlow := (le_div_iff₀ hU).mp hlo
  have hhigh := (div_lt_iff₀ hU).mp hhi
  constructor <;> linarith

theorem sum_timeSlice_card (S : Finset ℕ) (t : ℕ → ℝ) {A B U : ℝ}
    (hU : 0 < U) (ht : ∀ i ∈ S, t i ≤ B) :
    (∑ k ∈ Finset.range (⌊(B - A) / U⌋₊ + 1), (timeSlice S t A U k).card) = S.card := by
  have hmap : ∀ i ∈ S, ⌊(t i - A) / U⌋₊ ∈ Finset.range (⌊(B - A) / U⌋₊ + 1) := by
    intro i hi
    have h := Nat.floor_mono (div_le_div_of_nonneg_right (sub_le_sub_right (ht i hi) A) hU.le)
    exact Finset.mem_range.mpr (by omega)
  exact (Finset.card_eq_sum_card_fiberwise hmap).symm

theorem dirichletBlock_large_values_subdivided {M N : ℕ} (hM : 0 < M) (hN : N ≤ M)
    (S : Finset ℕ) (c : ℕ → ℂ) (t : ℕ → ℝ) {A B V U : ℝ}
    (hAB : A ≤ B) (hU : 0 < U) (ht : ∀ i ∈ S, A ≤ t i ∧ t i ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|)
    (hV : 0 ≤ V) (hlarge : ∀ i ∈ S, V ≤ ‖dirichletBlock M N c (t i)‖)
    (hwindow : 1280 * Real.sqrt U * coefficientEnergy N c ≤ V ^ 2) :
    S.card * V ^ 2 ≤ ((B - A) / U + 1) *
      (5120 * M * Real.log (U + 2) * coefficientEnergy N c) := by
  let K := ⌊(B - A) / U⌋₊
  let C := 5120 * (M : ℝ) * Real.log (U + 2) * coefficientEnergy N c
  have hC : 0 ≤ C := by
    have hlog : 0 ≤ Real.log (U + 2) := Real.log_nonneg (by linarith)
    have henergy := coefficientEnergy_nonneg N c
    dsimp only [C]
    positivity
  have hslices : ∀ k, (timeSlice S t A U k).card * V ^ 2 ≤ C := by
    intro k
    have hsub := timeSlice_subset S t A U k
    have hlen : (A + (k + 1) * U) - (A + k * U) = U := by ring
    have h := dirichletBlock_large_values_short_window hM hN (timeSlice S t A U k) c t
      (A := A + k * U) (B := A + (k + 1) * U) (by nlinarith)
      (fun i hi ↦ timeSlice_bounds hU (ht i (hsub hi)).1 hi)
      (fun i hi j hj hij ↦ hsep i (hsub hi) j (hsub hj) hij) hV
      (fun i hi ↦ hlarge i (hsub hi)) (by rw [hlen]; exact hwindow)
    rwa [hlen] at h
  have hsum := Finset.sum_le_sum (s := Finset.range (K + 1)) (fun k _ ↦ hslices k)
  have hcard : (∑ k ∈ Finset.range (K + 1), ((timeSlice S t A U k).card : ℝ)) = S.card := by
    exact_mod_cast sum_timeSlice_card S t hU (fun i hi ↦ (ht i hi).2)
  rw [← Finset.sum_mul, hcard] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hsum
  have hK : (K : ℝ) ≤ (B - A) / U := Nat.floor_le (div_nonneg (sub_nonneg.mpr hAB) hU.le)
  exact hsum.trans (mul_le_mul_of_nonneg_right (add_le_add hK le_rfl) hC)

end Erdos421
