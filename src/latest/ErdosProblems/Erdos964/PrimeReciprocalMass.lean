import ErdosProblems.Erdos964.PrimeMertensCumulative

/-!
# Bounded reciprocal-prime mass above a positive power cutoff
-/

namespace Erdos964

open BoundedGaps.Maynard Filter

theorem exists_primeReciprocalMass_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℕ) (P : Finset ℕ) (η : ℝ), 2 ≤ T → 0 < η →
      (∀ p ∈ P, p.Prime ∧ p ≤ T ∧ η * Real.log T ≤ Real.log p) →
      (∑ p ∈ P, (1 : ℝ) / p) ≤ (Real.log T + C) / (η * Real.log T) := by
  obtain ⟨C, hC⟩ := exists_uniform_abs_primeLogHarmonicSum_sub_log
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine ⟨C, hC0, ?_⟩
  intro T P η hT hη hP
  have hlog : 0 < Real.log T := Real.log_pos (by exact_mod_cast (show 1 < T by omega))
  have hden : 0 < η * Real.log T := mul_pos hη hlog
  apply (le_div_iff₀ hden).mpr
  calc
    _ = ∑ p ∈ P, (η * Real.log T) / p := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ ∑ p ∈ P, Real.log p / (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact div_le_div_of_nonneg_right (hP p hp).2.2 (Nat.cast_nonneg _)
    _ ≤ primeLogHarmonicSum T := by
      unfold primeLogHarmonicSum
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact Nat.mem_primesLE.mpr ⟨(hP p hp).2.1, (hP p hp).1⟩
      · intro p hp hnot
        exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
    _ ≤ Real.log T + C := by linarith [(abs_le.mp (hC T)).2]

theorem exists_primeReciprocalMass_uniform_bound (η : ℝ) (hη : 0 < η) :
    ∃ T₀ : ℕ, 2 ≤ T₀ ∧ ∀ (T : ℕ) (P : Finset ℕ), T₀ ≤ T →
      (∀ p ∈ P, p.Prime ∧ p ≤ T ∧ η * Real.log T ≤ Real.log p) →
      (∑ p ∈ P, (1 : ℝ) / p) ≤ 2 / η := by
  obtain ⟨C, hC, hbound⟩ := exists_primeReciprocalMass_bound
  have hlog : Tendsto (fun T : ℕ => Real.log T) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (hlog.eventually (eventually_ge_atTop C))
  refine ⟨max T₁ 2, le_max_right _ _, ?_⟩
  intro T P hT hP
  have hT2 : 2 ≤ T := (le_max_right T₁ 2).trans hT
  have hLT : 0 < Real.log T := Real.log_pos (by exact_mod_cast (show 1 < T by omega))
  have hCT := hT₁ T ((le_max_left T₁ 2).trans hT)
  calc
    _ ≤ (Real.log T + C) / (η * Real.log T) := hbound T P η hT2 hη hP
    _ ≤ (2 * Real.log T) / (η * Real.log T) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by field_simp

end Erdos964
