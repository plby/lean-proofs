import ErdosProblems.Erdos421.BandSums

/-! # Counting increments close to a multiple of a full period -/

namespace Erdos421

theorem strongly_antitone_band_card_bound (S : Finset ℕ) (d : ℕ → ℝ) {a b η : ℝ}
    (hab : a ≤ b) (hη : 0 < η)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≤ j → η * ((j : ℝ) - i) ≤ d i - d j)
    (hband : ∀ i ∈ S, a ≤ d i ∧ d i ≤ b) : (S.card : ℝ) ≤ (b - a) / η + 1 := by
  by_cases hS : S.Nonempty
  · have hmin := S.min'_mem hS
    have hmax := S.max'_mem hS
    have hsub : S ⊆ Finset.Icc (S.min' hS) (S.max' hS) :=
      fun i hi ↦ Finset.mem_Icc.mpr ⟨S.min'_le i hi, S.le_max' i hi⟩
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    have hnat : S.card + S.min' hS ≤ S.max' hS + 1 := by
      have horder := S.min'_le_max' hS
      omega
    have hreal : (S.card : ℝ) + (S.min' hS : ℝ) ≤ (S.max' hS : ℝ) + 1 := by
      exact_mod_cast hnat
    have hs := hsep _ hmin _ hmax (S.min'_le_max' hS)
    have hlo := (hband _ hmax).1
    have hhi := (hband _ hmin).2
    have hw : η * ((S.card : ℝ) - 1) ≤ b - a := by nlinarith
    have hdiv : (S.card : ℝ) - 1 ≤ (b - a) / η := by
      apply (le_div_iff₀ hη).mpr
      nlinarith
    linarith
  · have heq : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [heq, Finset.card_empty, Nat.cast_zero]
    have hnonneg : 0 ≤ (b - a) / η := div_nonneg (sub_nonneg.mpr hab) hη.le
    linarith

noncomputable def phaseNearPeriodIndices (f : ℕ → ℝ) (N : ℕ) (j : ℤ) (δ : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (fun n ↦
    2 * Real.pi * j - δ ≤ phaseIncrement f n ∧ phaseIncrement f n ≤ 2 * Real.pi * j + δ)

theorem phaseNearPeriodIndices_card_bound (f : ℕ → ℝ) (N : ℕ) (j : ℤ) {δ η : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 < η)
    (hsep : ∀ i < N, ∀ k < N, i ≤ k →
      η * ((k : ℝ) - i) ≤ phaseIncrement f i - phaseIncrement f k) :
    ((phaseNearPeriodIndices f N j δ).card : ℝ) ≤ 2 * δ / η + 1 := by
  classical
  have h := strongly_antitone_band_card_bound (phaseNearPeriodIndices f N j δ)
    (phaseIncrement f) (a := 2 * Real.pi * j - δ) (b := 2 * Real.pi * j + δ)
    (by linarith) hη (by
      intro i hi k hk hik
      exact hsep i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
        k (Finset.mem_range.mp (Finset.mem_filter.mp hk).1) hik)
    (fun _ hi ↦ (Finset.mem_filter.mp hi).2)
  have heq : 2 * Real.pi * j + δ - (2 * Real.pi * j - δ) = 2 * δ := by ring
  rwa [heq] at h

end Erdos421
