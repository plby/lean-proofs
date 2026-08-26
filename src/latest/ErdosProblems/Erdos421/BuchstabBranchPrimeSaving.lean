import ErdosProblems.Erdos421.BuchstabWeightPrimeSaving
import ErdosProblems.Erdos421.BuchstabWeightBranches

/-! # Prime summation for each actual finite Buchstab branch -/

namespace Erdos421

open MeasureTheory

theorem buchstabPrimeDiscrepancy_congr {X a b : ℝ} {F G : ℝ → ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hFG : ∀ t ∈ Set.Icc a b, F (logarithmicBuchstabArgument X t) =
      G (logarithmicBuchstabArgument X t)) :
    buchstabPrimeDiscrepancy X F a b = buchstabPrimeDiscrepancy X G a b := by
  unfold buchstabPrimeDiscrepancy
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨_, hpa, hpb⟩ := (mem_primesInRealInterval ha hab p).mp hp
    rw [hFG p ⟨hpa.le, hpb⟩]
  · apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    change F (logarithmicBuchstabArgument X t) * reciprocalLogSquare t =
      G (logarithmicBuchstabArgument X t) * reciprocalLogSquare t
    rw [hFG t ht]

theorem buchstab_low_branch_prime_saving {A ε K : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) (hK : 0 ≤ K) :
    ∃ X₀ > 1, ∀ X a b : ℝ, 1 < X → X₀ ≤ a → a ≤ b → 1 ≤ Real.log a →
      Real.log X ≤ K * Real.log a → ∀ n : ℕ,
      (∀ t ∈ Set.Icc a b, logarithmicBuchstabArgument X t ∈ Set.Icc (1 : ℝ) 2) →
      |buchstabPrimeDiscrepancy X (finiteBuchstab n) a b| ≤ ε / (Real.log a) ^ A := by
  obtain ⟨X₀, hX₀, hprime⟩ := buchstab_weight_prime_log_saving hA hε hK
  refine ⟨X₀, hX₀, ?_⟩
  intro X a b hX ha hab hlog hscale n harg
  have ha1 := hX₀.trans_le ha
  obtain ⟨hFd, hFc, hF, hF'⟩ := inverse_buchstab_branch_conditions ha1 (fun t ht ↦ (harg t ht).1)
  have heq := buchstabPrimeDiscrepancy_congr (by linarith : 0 ≤ a) hab
    (F := finiteBuchstab n) (G := fun u : ℝ ↦ u⁻¹) (by
      intro t ht
      simpa only [one_div] using finiteBuchstab_initial n (harg t ht))
  rw [heq]
  exact hprime X a b hX ha hab hlog hscale (fun u ↦ u⁻¹) hFd hFc hF hF'

theorem buchstab_zero_prime_saving {A ε K : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) (hK : 0 ≤ K) :
    ∃ X₀ > 1, ∀ X a b : ℝ, 1 < X → X₀ ≤ a → a ≤ b → 1 ≤ Real.log a →
      Real.log X ≤ K * Real.log a →
      (∀ t ∈ Set.Icc a b, 1 ≤ logarithmicBuchstabArgument X t) →
      |buchstabPrimeDiscrepancy X (finiteBuchstab 0) a b| ≤ ε / (Real.log a) ^ A := by
  obtain ⟨X₀, hX₀, hprime⟩ := buchstab_weight_prime_log_saving hA hε hK
  refine ⟨X₀, hX₀, ?_⟩
  intro X a b hX ha hab hlog hscale harg
  have ha1 := hX₀.trans_le ha
  obtain ⟨hFd, hFc, hF, hF'⟩ := inverse_buchstab_branch_conditions ha1 harg
  have heq := buchstabPrimeDiscrepancy_congr (by linarith : 0 ≤ a) hab
    (X := X) (F := finiteBuchstab 0) (G := fun u : ℝ ↦ u⁻¹) (by
      intro t ht
      simp only [finiteBuchstab, max_eq_right (harg t ht), one_div])
  rw [heq]
  exact hprime X a b hX ha hab hlog hscale (fun u ↦ u⁻¹) hFd hFc hF hF'

theorem buchstab_upper_branch_prime_saving {A ε K : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) (hK : 0 ≤ K) :
    ∃ X₀ > 1, ∀ X a b : ℝ, 1 < X → X₀ ≤ a → a ≤ b → 1 ≤ Real.log a →
      Real.log X ≤ K * Real.log a → ∀ n : ℕ,
      (∀ t ∈ Set.Icc a b, 2 ≤ logarithmicBuchstabArgument X t) →
      |buchstabPrimeDiscrepancy X (finiteBuchstab (n + 1)) a b| ≤ ε / (Real.log a) ^ A := by
  obtain ⟨X₀, hX₀, hprime⟩ := buchstab_weight_prime_log_saving hA hε hK
  refine ⟨X₀, hX₀, ?_⟩
  intro X a b hX ha hab hlog hscale n harg
  have ha1 := hX₀.trans_le ha
  obtain ⟨hFd, hFc, hF, hF'⟩ := upper_buchstab_branch_conditions n ha1 harg
  have heq := buchstabPrimeDiscrepancy_congr (by linarith : 0 ≤ a) hab
    (F := finiteBuchstab (n + 1)) (G := buchstabExtension n)
    (fun t ht ↦ (buchstabExtension_eq n (harg t ht)).symm)
  rw [heq]
  exact hprime X a b hX ha hab hlog hscale (buchstabExtension n) hFd hFc hF hF'

end Erdos421
