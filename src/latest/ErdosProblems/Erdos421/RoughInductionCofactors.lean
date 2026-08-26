import ErdosProblems.Erdos421.RoughCountEstimate
import ErdosProblems.Erdos421.RoughCofactorErrors

/-! # Applying the preceding rough-count estimate to every actual cofactor -/

namespace Erdos421

theorem roughCountEstimate_cofactor_error {n : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hcount : RoughCountEstimate n C) {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ B > 1, ∀ b : ℝ, B ≤ b → ∀ a : ℝ, b / 2 ≤ a → a ≤ b → ∀ z : ℕ,
      2 ≤ z → b ≤ (z : ℝ) ^ (n + 3) →
      |(∑ p ∈ sievePrimes z (roughSquareCutoff b),
        ((roughInRealInterval (a / p) (b / p) p).card : ℝ)) -
        ∑ p ∈ sievePrimes z (roughSquareCutoff b), roughCountMain n (a / p) (b / p) p| ≤
          ε * b / (Real.log b) ^ A +
            (32 * C * ((n : ℝ) + 3)) * (b - a) ^ 2 / (b * (Real.log b) ^ 2) := by
  let R : ℝ := 8 * ((n : ℝ) + 3)
  have hR : 0 < R := by dsimp only [R]; positivity
  let η : ℝ := ε / ((2 : ℝ) ^ A * R)
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨B₀, hB₀, hchild⟩ := hcount A η hA hη
  refine ⟨max 16 (B₀ ^ 2), (by norm_num : (1 : ℝ) < 16).trans_le (le_max_left _ _), ?_⟩
  intro b hb a ha hab z hz hbz
  obtain ⟨hb16, hbB⟩ := max_le_iff.mp hb
  have hBs : B₀ ≤ Real.sqrt b := Real.le_sqrt_of_sq_le hbB
  have hb1 : 1 < b := by linarith
  let P := sievePrimes z (roughSquareCutoff b)
  have hpoint : ∀ p ∈ P,
      |((roughInRealInterval (a / p) (b / p) p).card : ℝ) -
        roughCountMain n (a / p) (b / p) p| ≤
        η * (b / p) / (Real.log (b / p)) ^ A +
          C * (b / p - a / p) ^ 2 / ((b / p) * (Real.log (b / p)) ^ 2) := by
    intro p hp
    obtain ⟨hp2, hpc, hpow, hlo, hhi, hsc, _, _⟩ :=
      rough_cofactor_scale hb16 ha hab hz hbz hp
    exact hchild (b / p) (hBs.trans hsc) (a / p) hlo hhi p hp2 hpc hpow
  have hP : ∀ p ∈ P, 0 < p ∧ Real.log b / 2 ≤ Real.log (b / p) := by
    intro p hp
    obtain ⟨hp2, _, _, _, _, _, hlog, _⟩ := rough_cofactor_scale hb16 ha hab hz hbz hp
    exact ⟨by omega, hlog⟩
  have hmass : (∑ p ∈ P, (p : ℝ)⁻¹) ≤ R := rough_cofactor_reciprocal_mass hb16 hz hbz
  have hsum := sum_cofactor_errors_le (a := a) P hb1 hA hη.le hC hP hmass
  have hηeq : η * (2 : ℝ) ^ A * R = ε := by
    have htwo : (2 : ℝ) ^ A ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) A).ne'
    dsimp only [η]
    field_simp
  rw [hηeq] at hsum
  change |(∑ p ∈ P, _) - ∑ p ∈ P, _| ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ P, |((roughInRealInterval (a / p) (b / p) p).card : ℝ) -
        roughCountMain n (a / p) (b / p) p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P, (η * (b / p) / (Real.log (b / p)) ^ A +
        C * (b / p - a / p) ^ 2 / ((b / p) * (Real.log (b / p)) ^ 2)) :=
      Finset.sum_le_sum hpoint
    _ ≤ _ := hsum
    _ = _ := by dsimp only [R]; ring

end Erdos421
