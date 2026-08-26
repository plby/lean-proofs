import ErdosProblems.Erdos67b.MRGSTwistedEuler
import ErdosProblems.Erdos67b.MRTMajorArc

/-!
# Distance transfer to an untwisted coefficient at a cofactor scale

The Mertens loss is absolute when the lower logarithm is at least half
the ambient logarithm. The frequency shift is kept inside the original
nonpretentiousness window explicitly.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos67b

noncomputable section

def mrCofactorDistanceLoss : ℝ := 2 * Real.log 2 + 4 * PrimeEstimates.mertensBound

theorem mrCofactorDistanceLoss_nonneg : 0 ≤ mrCofactorDistanceLoss := by
  have hM := PrimeEstimates.mertensBound_nonneg
  unfold mrCofactorDistanceLoss
  positivity

theorem mrPretentiousDistSq_tail_le_cofactorLoss {f g : ℕ → ℂ} {Z X : ℕ}
    (hZ : 2 ≤ Z) (hZX : Z ≤ X)
    (hlog : Real.log (X : ℝ) ≤ 2 * Real.log (Z : ℝ))
    (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) :
    pretentiousDistSq f g X - pretentiousDistSq f g Z ≤ mrCofactorDistanceLoss := by
  have hLZ : 0 < Real.log (Z : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
  have hLX : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hloglog := Real.log_le_log hLX hlog
  rw [Real.log_mul (by norm_num) hLZ.ne'] at hloglog
  have hmass := PrimeEstimates.reciprocalPrimeInterval_le_log_log_sub_add hZ hZX
  calc
    _ ≤ ∑ p ∈ primesBetween Z X, 2 / (p : ℝ) := pretentiousDistSq_tail_le_primeHarmonic hZX hf hg
    _ = 2 * PrimeEstimates.reciprocalPrimeInterval Z X := by
      unfold PrimeEstimates.reciprocalPrimeInterval PrimeEstimates.primesInInterval primesBetween
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ 2 * (Real.log (Real.log (X : ℝ)) - Real.log (Real.log (Z : ℝ)) +
        2 * PrimeEstimates.mertensBound) := mul_le_mul_of_nonneg_left hmass (by norm_num)
    _ ≤ mrCofactorDistanceLoss := by unfold mrCofactorDistanceLoss; linarith

theorem mrArchimedeanTwist_add_of_pos {n : ℕ} (hn : 0 < n) (t u : ℝ) :
    archimedeanTwist (t + u) n = archimedeanTwist t n * archimedeanTwist u n := by
  unfold archimedeanTwist
  rw [Complex.ofReal_add, mul_add, Complex.cpow_add _ _ (by exact_mod_cast hn.ne')]

theorem mrNorm_archimedeanUntwist_of_pos (f : ℕ → ℂ) (t : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖archimedeanUntwist f t n‖ = ‖f n‖ := by
  rw [archimedeanUntwist, if_neg hn.ne', norm_mul, Complex.norm_conj,
    norm_archimedeanTwist hn, mul_one]

theorem mrPretentiousDistSq_archimedeanUntwist (f : ℕ → ℂ) (t u : ℝ) (X : ℕ) :
    pretentiousDistSq (archimedeanUntwist f t) (archimedeanTwist u) X =
      pretentiousDistSq f (archimedeanTwist (t + u)) X := by
  unfold pretentiousDistSq
  apply Finset.sum_congr rfl
  intro p hp
  have hpPrime := (mem_primesUpTo.1 hp).1
  unfold pretentiousTerm archimedeanUntwist
  rw [if_neg hpPrime.ne_zero, mrArchimedeanTwist_add_of_pos hpPrime.pos, map_mul, mul_assoc]

theorem mrArchimedeanNonpretentious_untwist_lower_scale
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {N M Z X : ℕ}
    (hNM : (N : ℝ) + mrCofactorDistanceLoss ≤ M)
    (hZ : 2 ≤ Z) (hZX : Z ≤ X) (hlog : Real.log (X : ℝ) ≤ 2 * Real.log (Z : ℝ))
    {t : ℝ} (hwindow : |t| + (Z : ℝ) ≤ X)
    (hnonpret : MRArchimedeanNonpretentious f M X) :
    MRArchimedeanNonpretentious (archimedeanUntwist f t) N Z := by
  intro u hu
  rw [mrPretentiousDistSq_archimedeanUntwist]
  have hfreq : |t + u| ≤ (X : ℝ) := (abs_add_le t u).trans (by linarith)
  have hupper := hnonpret (t + u) hfreq
  have htail := mrPretentiousDistSq_tail_le_cofactorLoss hZ hZX hlog
    (fun p hp ↦ hbound p hp.pos) (fun p hp ↦ (norm_archimedeanTwist hp.pos (t + u)).le)
  linarith

end

end Erdos67b
