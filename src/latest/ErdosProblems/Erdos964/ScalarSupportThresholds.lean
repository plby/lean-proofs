import ErdosProblems.Erdos964.ScalarPowerLogLimits

/-!
# The smaller primes in the concrete support eventually exceed any threshold
-/

namespace Erdos964

open BoundedGaps.Maynard Filter

theorem exists_scalarSmallPrimeSupport_ge (B : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ T₀ : ℕ, 4 ≤ T₀ ∧ ∀ t : ℕ, T₀ ≤ t → ∀ K : ℕ, 1 ≤ K →
      ∀ p ∈ scalarSmallPrimeSupport η K t, B ≤ p := by
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp
    ((tendsto_scalar_power_radius η hη).eventually (eventually_ge_atTop B))
  refine ⟨max T₁ 4, le_max_right _ _, ?_⟩
  intro t ht K hK p hp
  have hcut := hT₁ t ((le_max_left T₁ 4).trans ht)
  have hB : (B : ℝ) ≤ Real.rpow (t : ℝ) η :=
    (show (B : ℝ) ≤ modulusCutoff η t by exact_mod_cast hcut).trans
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) η))
  have hpower : Real.rpow (t : ℝ) η ≤ Real.rpow (K * t : ℕ) η :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.le_mul_of_pos_left t hK) hη.le
  have hBp : (B : ℝ) ≤ p :=
    hB.trans (hpower.trans (scalarSmallPrimeSupport_spec η K t p hp).2.2.le)
  exact_mod_cast hBp

end Erdos964
