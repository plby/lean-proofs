/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceCoveringResidues

/-! # Actual small- and large-prime residues with prime-count-scale survivors -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem RegularSourceConditions.removed_count_le_primeScale {a c e : ℝ} {x : ℕ}
    {D : SourceProbabilityData c e x} {b : ResidueAssignment (sourceSmallPrimes a x)}
    (H : RegularSourceConditions D a b) (hℓ : 1 ≤ Real.log (Real.log (x : ℝ))) :
    ((sourceSurvivorVertices a c x b \ H.edgeFamily.vertices).card : ℝ) ≤
      2 * (x : ℝ) / Real.log (x : ℝ) := by
  have hL : 0 < Real.log (x : ℝ) := by linarith [H.log_ge]
  have hℓsq : 1 ≤ Real.log (Real.log (x : ℝ)) ^ 2 := by nlinarith
  have hdiv : (x : ℝ) / (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ)) ^ 2) ≤
      (x : ℝ) / Real.log (x : ℝ) := by
    rw [div_mul_eq_div_div]
    exact div_le_self (div_nonneg (Nat.cast_nonneg _) hL.le) hℓsq
  exact H.removed_count.le.trans (by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 2))

theorem SourceGeometricPartition.CoveringWitness.exists_full_prime_residue_sieve
    {a c e : ℝ} {x : ℕ} {D : SourceProbabilityData c e x}
    {b : ResidueAssignment (sourceSmallPrimes a x)} {H : RegularSourceConditions D a b}
    (B : SourceGeometricPartition H) (W : B.CoveringWitness)
    (hℓ : 1 ≤ Real.log (Real.log (x : ℝ))) {K : ℝ}
    (hcount : ((coveringRemaining B.family H.edgeFamily.vertices
      (sourceBatchCount x) W.history).card : ℝ) ≤ K * x / Real.log (x : ℝ)) :
    ∃ r : ResidueAssignment (commonPinnedPrimeSet (x / 2) x),
      ((naturalResidueSurvivors (commonPinnedPrimeSet (x / 2) x)
        (sourceSurvivorVertices a c x b) r).card : ℝ) ≤ (K + 2) * x / Real.log (x : ℝ) := by
  obtain ⟨r, hr⟩ := W.exists_prime_residue_sieve B
  have hregR : ((naturalResidueSurvivors (commonPinnedPrimeSet (x / 2) x)
      H.edgeFamily.vertices r).card : ℝ) ≤
      (coveringRemaining B.family H.edgeFamily.vertices (sourceBatchCount x) W.history).card := by
    exact_mod_cast hr
  have hreg := hregR.trans hcount
  have hcard := naturalResidueSurvivors_card_le (commonPinnedPrimeSet (x / 2) x)
    (sourceSurvivorVertices a c x b) H.edgeFamily.vertices r
  have hcardR : ((naturalResidueSurvivors (commonPinnedPrimeSet (x / 2) x)
      (sourceSurvivorVertices a c x b) r).card : ℝ) ≤
      (naturalResidueSurvivors (commonPinnedPrimeSet (x / 2) x) H.edgeFamily.vertices r).card +
        (sourceSurvivorVertices a c x b \ H.edgeFamily.vertices).card := by exact_mod_cast hcard
  refine ⟨r, hcardR.trans ?_⟩
  have hremoved := H.removed_count_le_primeScale hℓ
  calc
    _ ≤ K * x / Real.log (x : ℝ) + 2 * (x : ℝ) / Real.log (x : ℝ) :=
      add_le_add hreg hremoved
    _ = _ := by ring

theorem exists_source_prime_sieve {a : ℝ} (ha : 0 < a) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ᶠ x : ℕ in atTop,
      ∃ (b : ResidueAssignment (sourceSmallPrimes a x))
        (r : ResidueAssignment (commonPinnedPrimeSet (x / 2) x)),
        ((naturalResidueSurvivors (commonPinnedPrimeSet (x / 2) x)
          (sourceSurvivorVertices a c x b) r).card : ℝ) ≤ K * x / Real.log (x : ℝ) := by
  obtain ⟨c, K, hc, hK, hdata⟩ := exists_sourceCoveringData (e := 1 / 120) ha
    (by norm_num) le_rfl
  refine ⟨c, K + 2, hc, by linarith, ?_⟩
  have hℓ := Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [hdata, hℓ.eventually_ge_atTop 1] with x hx hℓx
  obtain ⟨D, b, H, B, W, hcount⟩ := hx
  obtain ⟨r, hr⟩ := W.exists_full_prime_residue_sieve B hℓx hcount
  exact ⟨b, r, hr⟩

end

end Erdos4b.FGKMT
