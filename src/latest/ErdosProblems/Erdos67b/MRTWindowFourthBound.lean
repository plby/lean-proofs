import ErdosProblems.Erdos67b.MRTWindowGeometric
import ErdosProblems.Erdos67b.MRTCompatibleWindows

/-! # The actual dual-window fourth moment is bounded by prime-quadruple mass -/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67b

noncomputable section

theorem mrtNorm_fourthMomentCoefficient_le_one {S : Finset ℕ} {a : ℕ → ℂ}
    (ha : ∀ n ∈ S, ‖a n‖ ≤ 1) {p : (ℕ × ℕ) × (ℕ × ℕ)}
    (hp : p ∈ primeQuadrupleSet S) : ‖fourthMomentCoefficient a p‖ ≤ 1 := by
  obtain ⟨⟨h₁₁, h₁₂⟩, h₂₁, h₂₂⟩ :=
    (show (p.1.1 ∈ S ∧ p.1.2 ∈ S) ∧ p.2.1 ∈ S ∧ p.2.2 ∈ S by
      simpa only [primeQuadrupleSet, Finset.mem_product] using hp)
  simp only [fourthMomentCoefficient, norm_mul, Complex.norm_conj]
  calc
    _ ≤ 1 * 1 * 1 * (1 : ℝ) := by
      gcongr
      · exact ha _ h₂₂
      · exact ha _ h₂₁
      · exact ha _ h₁₂
      · exact ha _ h₁₁
    _ = _ := by norm_num

theorem mrtCofactorPhaseSum_eq_zero {Z H M : ℕ} {p n : (ℕ × ℕ) × (ℕ × ℕ)}
    (he : ¬(mrtQuadCofactors Z H M p n).Nonempty) (α : ℝ) :
    mrtCofactorPhaseSum Z H M p n α = 0 := by
  simp [mrtCofactorPhaseSum, Finset.not_nonempty_iff_eq_empty.1 he]

theorem mrtSum_startQuadruples_eq_compatible (Z H M Y : ℕ)
    (p : (ℕ × ℕ) × (ℕ × ℕ)) (θ : ℕ → ℂ) (α : ℝ) :
    (∑ n ∈ primeQuadrupleSet (Finset.Ioc Y (2 * Y)),
      fourthMomentCoefficient θ n * mrtCofactorPhaseSum Z H M p n α) =
    ∑ n ∈ mrtCompatibleStarts Z H M Y p,
      fourthMomentCoefficient θ n * mrtCofactorPhaseSum Z H M p n α := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hne
  have he : ¬(mrtQuadCofactors Z H M p n).Nonempty := by
    intro hh
    exact hne (Finset.mem_filter.2 ⟨hn, hh⟩)
  simp [mrtCofactorPhaseSum_eq_zero he]

theorem mrtNorm_sum_compatible_le (Z H M Y : ℕ) (p : (ℕ × ℕ) × (ℕ × ℕ))
    (θ : ℕ → ℂ) (α : ℝ) (hθ : ∀ n ∈ Finset.Ioc Y (2 * Y), ‖θ n‖ ≤ 1)
    {P : ℕ} (hP : 0 < P) (hPH : P ≤ H)
    (h₁₁ : P ≤ p.1.1) (h₁₂ : 0 < p.1.2) (h₂₁ : 0 < p.2.1) (h₂₂ : 0 < p.2.2)
    (h₁₂' : p.1.2 ≤ 2 * p.1.1) (h₂₁' : p.2.1 ≤ 2 * p.1.1)
    (h₂₂' : p.2.2 ≤ 2 * p.1.1) :
    ‖∑ n ∈ mrtCompatibleStarts Z H M Y p,
      fourthMomentCoefficient θ n * mrtCofactorPhaseSum Z H M p n α‖ ≤
    128 * Y * H ^ 3 * vinogradovWeight H P (α * (primeQuadrupleDifference p : ℝ)) := by
  have hfirst : 0 < p.1.1 := hP.trans_le h₁₁
  have hweight := vinogradovWeight_nonneg H P (α * (primeQuadrupleDifference p : ℝ))
  have hcount := card_mrtCompatibleStarts_le_cube Z H M Y p (hP.trans_le hPH)
    hfirst h₁₂' h₂₁' h₂₂'
  have hcount' : ((mrtCompatibleStarts Z H M Y p).card : ℝ) ≤
      64 * Y * H ^ 3 := by exact_mod_cast hcount
  calc
    _ ≤ ∑ n ∈ mrtCompatibleStarts Z H M Y p,
        ‖fourthMomentCoefficient θ n * mrtCofactorPhaseSum Z H M p n α‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ mrtCompatibleStarts Z H M Y p,
        2 * vinogradovWeight H P (α * (primeQuadrupleDifference p : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      have hnorm := mrtNorm_fourthMomentCoefficient_le_one hθ (Finset.mem_filter.1 hn).1
      calc
        _ ≤ 1 * (2 * vinogradovWeight H P (α * (primeQuadrupleDifference p : ℝ))) :=
          mul_le_mul hnorm
            (mrtCofactorPhaseSum_le_weight Z H M p n α hfirst h₁₂ h₂₁ h₂₂ hP h₁₁ hPH)
            (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    _ = (mrtCompatibleStarts Z H M Y p).card *
        (2 * vinogradovWeight H P (α * (primeQuadrupleDifference p : ℝ))) := by simp
    _ ≤ (64 * Y * H ^ 3) *
        (2 * vinogradovWeight H P (α * (primeQuadrupleDifference p : ℝ))) :=
      mul_le_mul_of_nonneg_right hcount' (mul_nonneg (by norm_num) hweight)
    _ = _ := by ring

theorem mrtWindowPrimeRow_fourthMoment_le (S : Finset ℕ) (Z H M Y P : ℕ)
    (c θ : ℕ → ℂ) (α : ℝ) (hP : 0 < P) (hPH : P ≤ H)
    (hS : S ⊆ dyadicPrimeBlock P 0) (hc : ∀ p ∈ S, ‖c p‖ ≤ 1)
    (hθ : ∀ n ∈ Finset.Ioc Y (2 * Y), ‖θ n‖ ≤ 1) :
    (∑ m ∈ Finset.Icc 1 M, ‖mrtWindowPrimeRow S Z H Y c θ α m‖ ^ 4 : ℝ) ≤
      128 * Y * H ^ 3 * minorArcPrimeQuadrupleMass H P α := by
  classical
  let V : ℝ := ∑ m ∈ Finset.Icc 1 M, ‖mrtWindowPrimeRow S Z H Y c θ α m‖ ^ 4
  have hV : 0 ≤ V := Finset.sum_nonneg fun _ _ ↦ by positivity
  have hexact := mrtWindowPrimeRow_fourthMoment_eq S Z H M Y c θ α
  have hprimes {r : ℕ} (hr : r ∈ S) : P < r ∧ r ≤ 2 * P := by
    simpa using (mem_dyadicPrimeBlock.1 (hS hr)).2
  have hquad : primeQuadrupleSet S ⊆ primeQuadrupleSet (dyadicPrimeBlock P 0) :=
    Finset.product_subset_product (Finset.product_subset_product hS hS)
      (Finset.product_subset_product hS hS)
  change V ≤ _
  calc
    V = ‖(V : ℂ)‖ := by simp [Real.norm_eq_abs, abs_of_nonneg hV]
    _ = ‖∑ p ∈ primeQuadrupleSet S, fourthMomentCoefficient c p *
        ∑ n ∈ mrtCompatibleStarts Z H M Y p,
          fourthMomentCoefficient θ n * mrtCofactorPhaseSum Z H M p n α‖ := by
      rw [hexact]
      simp_rw [mrtSum_startQuadruples_eq_compatible]
    _ ≤ ∑ p ∈ primeQuadrupleSet S, ‖fourthMomentCoefficient c p *
        ∑ n ∈ mrtCompatibleStarts Z H M Y p,
          fourthMomentCoefficient θ n * mrtCofactorPhaseSum Z H M p n α‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ primeQuadrupleSet S,
        128 * Y * H ^ 3 * vinogradovWeight H P (α * (primeQuadrupleDifference p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨⟨hp₁₁, hp₁₂⟩, hp₂₁, hp₂₂⟩ :=
        (show (p.1.1 ∈ S ∧ p.1.2 ∈ S) ∧ p.2.1 ∈ S ∧ p.2.2 ∈ S by
          simpa only [primeQuadrupleSet, Finset.mem_product] using hp)
      have hb₁₁ := hprimes hp₁₁
      have hb₁₂ := hprimes hp₁₂
      have hb₂₁ := hprimes hp₂₁
      have hb₂₂ := hprimes hp₂₂
      rw [norm_mul]
      calc
        _ ≤ 1 * (128 * Y * H ^ 3 *
            vinogradovWeight H P (α * (primeQuadrupleDifference p : ℝ))) :=
          mul_le_mul (mrtNorm_fourthMomentCoefficient_le_one hc hp)
            (mrtNorm_sum_compatible_le Z H M Y p θ α hθ hP hPH hb₁₁.1.le
              (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
            (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    _ = 128 * Y * H ^ 3 *
        ∑ p ∈ primeQuadrupleSet S, vinogradovWeight H P ((primeQuadrupleDifference p : ℝ) * α) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [mul_comm α]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg hquad
        (fun p _ _ ↦ vinogradovWeight_nonneg H P _)

end

end Erdos67b
