import ErdosProblems.Erdos421.BuchstabWeightVariation
import ErdosProblems.Erdos421.WeightedPrimeLogSaving

/-! # Uniform prime summation for smooth branches of the Buchstab function -/

namespace Erdos421

open MeasureTheory

noncomputable def buchstabPrimeDiscrepancy (X : ℝ) (F : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (∑ p ∈ primesInRealInterval a b,
    F (logarithmicBuchstabArgument X p) / ((p : ℝ) * Real.log p)) -
    ∫ t in a..b, buchstabPrimeWeight X F t

theorem buchstab_weight_prime_log_saving {A ε K : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) (hK : 0 ≤ K) :
    ∃ X₀ > 1, ∀ X a b : ℝ, 1 < X → X₀ ≤ a → a ≤ b → 1 ≤ Real.log a →
      Real.log X ≤ K * Real.log a → ∀ F : ℝ → ℝ,
      (∀ t ∈ Set.Icc a b, DifferentiableAt ℝ F (logarithmicBuchstabArgument X t)) →
      ContinuousOn (fun t ↦ deriv F (logarithmicBuchstabArgument X t)) (Set.Icc a b) →
      (∀ t ∈ Set.Icc a b, |F (logarithmicBuchstabArgument X t)| ≤ 1) →
      (∀ t ∈ Set.Icc a b, |deriv F (logarithmicBuchstabArgument X t)| ≤ 2) →
      |buchstabPrimeDiscrepancy X F a b| ≤ ε / (Real.log a) ^ A := by
  have hC : 0 < 2 * K + 5 := by linarith
  obtain ⟨X₀, hX₀, hprime⟩ := prime_log_weighted_log_saving hA (div_pos hε hC)
  refine ⟨X₀, hX₀, ?_⟩
  intro X a b hX ha hab hlog hscale F hFd hFc hF hF'
  have ha1 := hX₀.trans_le ha
  have hlap := Real.log_pos ha1
  obtain ⟨hgd, hgc⟩ := buchstabPrimeWeight_regular ha1 hFd hFc
  have hp := hprime a b ha hab (buchstabPrimeWeight X F) hgd hgc
  have hn := buchstabPrimeWeight_variation_le hX ha1 hab hlog hK hscale hFd hFc hF hF'
  have hsum : (∑ p ∈ primesInRealInterval a b, buchstabPrimeWeight X F p * Real.log p) =
      ∑ p ∈ primesInRealInterval a b,
        F (logarithmicBuchstabArgument X p) / ((p : ℝ) * Real.log p) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    have hpr : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hpp.one_lt)
    dsimp only [buchstabPrimeWeight, reciprocalLogSquare]
    field_simp
  rw [hsum] at hp
  calc
    _ ≤ _ := hp
    _ ≤ (ε / (2 * K + 5) / (Real.log a) ^ A) * (2 * K + 5) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = _ := by field_simp

end Erdos421
