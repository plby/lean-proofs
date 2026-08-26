import ErdosProblems.Erdos4.OuterNoncoverage
import ErdosProblems.Erdos4.OuterCleanup

/-!
# Unconditional interval covers on the outer ray

All expected-uncovered costs fit the fresh-prime reserve. One fixed
Rankin loss parameter works for every fixed positive integer length
multiplier. No numerical covering hypothesis remains in the conclusion.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos4.OuterCover

open SmoothParameters ChebyshevIntervals OuterRay OuterAccuracy OuterPrimeSupply OuterCleanup
open ConditionalTupleMoments ConditionalCovering

theorem exists_arbitrary_length_covers :
    ∃ a : ℕ, ∀ D : ℕ, 1 ≤ D → ∀ᶠ r : ℕ in atTop,
      ∃ cover : Erdos4.ResidueCover (length a D r),
        cover.modulus ≤ primorial (frontier a r) := by
  classical
  obtain ⟨a, hsmooth⟩ := exists_negligible_smooth
  obtain ⟨c, hc, hsupply⟩ := exists_prime_supply
  obtain ⟨_c₀, C, _hc₀, hC, hdensity⟩ := OuterDensity.exists_survival_density_bounds
  let P : ℝ := 3 * Real.log 2
  have hP : 0 < P := by dsimp [P]; positivity
  refine ⟨a, ?_⟩
  intro D hD
  have hDR : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  let η := c / (8 * C * D)
  let β := c / (8 * C * D * P)
  have hη : 0 < η := by dsimp [η]; positivity
  have hβ : 0 < β := by dsimp [β]; positivity
  have hbalance : C * D * (η + β * P) = c / 4 := by
    dsimp [η, β]
    field_simp
    ring
  obtain ⟨k, K, hk, _hK, hmiss⟩ := OuterNoncoverage.exists_parameters D hD hβ hη
  have hH : 1 ≤ k * primorial K := Nat.mul_pos hk (primorial_pos K)
  have hc4 : 0 < c / 4 := by positivity
  filter_upwards [eventually_ge_atTop 1, hmiss a, hsupply a, hdensity a,
    eventually_target_count a hD, eventually_small_prime_cost a (k * primorial K) hH hC hc4,
    hsmooth D hD (c / 4) hc4, eventually_length_le_zeroCutoff a D,
    eventually_small_le_smooth a] with r hr hmiss hsrc hden hcount hsmall hsmooth hzero hwz
  obtain ⟨μ, hμ, bad, _hbsub, hbcard, hgood⟩ := hmiss
  let ell : randomPrimes a r → ℕ := fun l => l
  let σ := UnitFourier.unitDensity ell
  let s : ℝ := (r : ℝ) * core r
  have hσ : 0 < σ := UnitFourier.unitDensity_pos ell
  have hV : (0 : ℝ) < core r := by exact_mod_cast core_pos r
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hs : 0 < s := mul_pos hrR hV
  have hX : (0 : ℝ) < frontier a r := by exact_mod_cast frontier_pos a r
  have hlog : 0 < Real.log (primaryFrontier a r : ℝ) :=
    Real.log_pos (by exact_mod_cast primary_two_le a r)
  have hsum := CoverBudget.target_sum_le ell (AffineWeights.shift K : Fin k → ℕ)
    (sourcePrimes a r) (primeInterval (base a r) (length a D r)) bad (length a D r) μ hμ hβ.le hgood
  have hbad : (bad.card : ℝ) + β * (primeInterval (base a r) (length a D r)).card ≤
      (η + β * P) * length a D r / Real.log (primaryFrontier a r : ℝ) +
        Nat.primeCounting (k * primorial K * frontier a r) := by
    have hh := add_le_add hbcard (mul_le_mul_of_nonneg_left hcount hβ.le)
    exact hh.trans_eq (by dsimp [P]; ring)
  have hmain : (C / s) * ((η + β * P) * length a D r /
      Real.log (primaryFrontier a r : ℝ)) =
        (c / 4) * frontier a r / Real.log (primaryFrontier a r : ℝ) := by
    calc
      _ = (C * D * (η + β * P)) * frontier a r /
          Real.log (primaryFrontier a r : ℝ) := by
        rw [OuterRay.length]
        push_cast
        dsimp [s]
        field_simp
      _ = _ := by rw [hbalance]
  have hsmall' := hsmall σ hσ.le hden.2
  have hbudget : σ * (∑ q ∈ primeInterval (base a r) (length a D r),
      mean ell q (miss ell (AffineWeights.shift K : Fin k → ℕ) (sourcePrimes a r)
        (length a D r) μ q)) +
        (Nat.smoothNumbersUpTo (length a D r) (smoothFrontier r + 1)).card <
          (reservePrimes a r).card + 1 := by
    calc
      _ ≤ σ * (bad.card + β * (primeInterval (base a r) (length a D r)).card) +
          (Nat.smoothNumbersUpTo (length a D r) (smoothFrontier r + 1)).card :=
        add_le_add (mul_le_mul_of_nonneg_left hsum hσ.le) le_rfl
      _ ≤ σ * ((η + β * P) * length a D r / Real.log (primaryFrontier a r : ℝ) +
          Nat.primeCounting (k * primorial K * frontier a r)) +
          (Nat.smoothNumbersUpTo (length a D r) (smoothFrontier r + 1)).card :=
        add_le_add (mul_le_mul_of_nonneg_left hbad hσ.le) le_rfl
      _ = σ * ((η + β * P) * length a D r / Real.log (primaryFrontier a r : ℝ)) +
          σ * Nat.primeCounting (k * primorial K * frontier a r) +
          (Nat.smoothNumbersUpTo (length a D r) (smoothFrontier r + 1)).card := by ring
      _ ≤ (C / s) * ((η + β * P) * length a D r / Real.log (primaryFrontier a r : ℝ)) +
          (c / 4) * frontier a r / Real.log (primaryFrontier a r : ℝ) +
          (c / 4) * frontier a r / Real.log (primaryFrontier a r : ℝ) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_right hden.2 (by positivity)) hsmall') hsmooth
      _ = (3 * c / 4) * frontier a r / Real.log (primaryFrontier a r : ℝ) := by rw [hmain]; ring
      _ ≤ c * frontier a r / Real.log (primaryFrontier a r : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hX.le) hlog.le
      _ ≤ (reservePrimes a r).card := hsrc.2.2
      _ < _ := by linarith
  exact CompleteCover.exists_ray_cover_of_budget a D r hD hr hwz hzero
    (AffineWeights.shift K : Fin k → ℕ) μ hμ hbudget

end Erdos4.OuterCover
