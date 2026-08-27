import ErdosProblems.Erdos4.TiltedPrimeInitialization
import ErdosProblems.Erdos4.TiltedPrimeCoverFinite
import ErdosProblems.Erdos4.TiltedPrimeCoverBudget
import ErdosProblems.Erdos4.TiltedPrimePartitionBudget

/-! The prime covering has a small expected cost on the same tilted sieve space as the composites. -/

namespace Erdos4.Tilted

open Filter FGKMT

theorem eventually_prime_cover_for_data {c G C : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ∀ (D : PrimeExposureData c x G C) (hτ : 0 ≤ tiltExponent x)
      (W : Finset (primeTargets c x)), ∃ b : ∀ p : growingSourcePrimes x, ZMod p.val,
      ((sourceSurvivors (growingSourcePrimes x) (primeTargets c x) W b).card : ℝ) ≤
        primeCoverCost (primeSurvivorLaw c x hτ) D.law D.bad (growingCoverDensity x) W := by
  classical
  filter_upwards [eventually_prime_initialization (G := G) (C := C) hc,
    eventually_prime_partition_budget, eventually_gapTarget_bounds hc,
    eventually_growing_cover_sparsity, eventually_ge_atTop 1]
    with x hinit hpart hY hsparse hx
  intro D hτ W
  let ν := primeSurvivorLaw c x hτ
  let laws := fun p => cappedEdgeLaw ν (D.law p) W
  let bad := primeBadSet ν D.law D.bad W
  have hi := hinit D hτ
  have hxpos : (0 : ℝ) < x := Nat.cast_pos.mpr hx
  have hεδ := growing_marginal_le_sparsity hx
  have hpartition : (growingRounds x : ℝ) * (primeTargets c x).card *
      Real.exp (-((1 / 2 : ℝ) ^ growingRounds x) / (6 * (x : ℝ) ^ (-4 / 5 : ℝ))) < 1 := by
    simpa only [growingCoverDensity] using hpart (primeTargets c x).card
      ((primeTargets_card_le c x).trans hY.2.2.2.1)
  have hdegree : ∀ v ∈ W \ bad, 4 ≤ vertexDegree laws v := by
    intro v hv
    obtain ⟨hvW, hvbad⟩ := Finset.mem_sdiff.mp hv
    by_contra hpoor
    apply hvbad
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hvW, Or.inr (lt_of_not_ge hpoor)⟩
  obtain ⟨b, hb⟩ := source_cover_with_bad_vertices (growingSourcePrimes x) (primeTargets c x)
    laws W bad (primeBadSet_subset ν D.law D.bad W)
    (m := growingRounds x) (r := sieveDimension (growingIndex x)) Nat.one_le_two_pow
    (Real.rpow_pos_of_pos hxpos (-4 / 5 : ℝ)) (Real.rpow_nonneg hxpos.le (-1 / 5 : ℝ)) hεδ
    hdegree (hi.2.1 W)
    (source_count_square_budget hx (growingSourcePrimes_card_le x))
    (fun v w hvw => (hi.2.2.1 W v w hvw).trans hεδ) (hi.2.2.2 W) hpartition hsparse
  refine ⟨b, hb.trans_eq ?_⟩
  unfold primeCoverCost growingCoverDensity
  ring

theorem exists_prime_cover_cost {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℕ in atTop, ∀ hτ : 0 ≤ tiltExponent x,
      ∃ cost : SieveState x → ℝ, (∀ a, 0 ≤ cost a) ∧
        (actualSieveLaw x hτ).mean cost ≤ ε * (x : ℝ) / Real.log (x : ℝ) ∧
        ∀ a, ∃ b : ∀ p : growingSourcePrimes x, ZMod p.val,
          ((sourceSurvivors (growingSourcePrimes x) (primeTargets c x)
            (primeSurvivors c x a) b).card : ℝ) ≤ cost a := by
  classical
  let G := ε / (8 * (3 * Real.log 2))
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hG : 0 < G := by dsimp [G]; positivity
  obtain ⟨c, C, hc, hC, hdata⟩ := exists_primeExposureData hG
  refine ⟨c, hc, ?_⟩
  filter_upwards [hdata, eventually_prime_initialization (G := G) (C := C) hc,
    eventually_prime_cover_for_data (G := G) (C := C) hc,
    eventually_prime_cover_numeric_budget hc hG hC (by positivity : 0 < ε / 2)]
    with x hdata hinit hcover hbudget
  intro hτ
  obtain ⟨D⟩ := hdata
  let ν := primeSurvivorLaw c x hτ
  let κ := growingCoverDensity x
  let cost := fun a => primeCoverCost ν D.law D.bad κ (primeSurvivors c x a)
  have hκ : 0 ≤ κ := by dsimp [κ, growingCoverDensity]; positivity
  have hmean := mean_primeCoverCost_le ν D.law D.bad (primeDensity_pos x)
    (by positivity : 0 ≤ 1 / Real.log (x : ℝ) ^ (40 : ℕ)) hκ
    (primeSurvivorLaw_singleton c x hτ) (hinit D hτ).1
  have hcoef : ε / 2 + 4 * (3 * Real.log 2) * G = ε := by
    dsimp [G]
    field_simp
    ring
  refine ⟨cost, fun a => primeCoverCost_nonneg ν D.law D.bad hκ _, ?_, fun a => hcover D hτ _⟩
  calc
    _ = ν.mean (primeCoverCost ν D.law D.bad κ) :=
      (FiniteLaw.mean_map (actualSieveLaw x hτ) (primeSurvivors c x) (primeCoverCost ν D.law D.bad κ)).symm
    _ ≤ primeDensity x * ((D.bad.card : ℝ) +
        (1 / Real.log (x : ℝ) ^ (40 : ℕ)) * (primeTargets c x).card) +
        2 * κ * (primeDensity x * (primeTargets c x).card) := by
      simpa only [Fintype.card_coe] using hmean
    _ ≤ (ε / 2 + 4 * (3 * Real.log 2) * G) * (x : ℝ) / Real.log (x : ℝ) := hbudget D
    _ = _ := by rw [hcoef]

end Erdos4.Tilted
