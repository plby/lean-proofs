import ErdosProblems.Erdos67.MRCofactorPerron

/-!
# Uniform selected-prime loss for a Ramaré block

The beta-average representation of the common Ramaré denominator scales
the coefficient at every selected prime.  Its pretentious-distance loss
is the reciprocal mass of those primes.  This file proves that the loss is
an absolute constant when the block lies between `L` and `(L-1)^2`,
independently of the ambient cutoff.
-/

open scoped BigOperators
open Finset

namespace Erdos67

noncomputable section

theorem mrSelectedPrimeReciprocalMass_primesInBlock_le
    (I : ℕ × ℕ) (X : ℕ) (hlo : 0 < I.1) :
    mrSelectedPrimeReciprocalMass (primesInBlock I) X ≤
      PrimeEstimates.reciprocalPrimeInterval (I.1 - 1) I.2 := by
  unfold mrSelectedPrimeReciprocalMass
  rw [← Finset.sum_filter]
  unfold PrimeEstimates.reciprocalPrimeInterval
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_filter] at hp
    rw [PrimeEstimates.mem_primesInInterval]
    have hpblock := mem_primesInBlock.mp hp.2
    exact ⟨by omega, hpblock.2.2, hpblock.1⟩
  · intro p hp hnot
    positivity

theorem reciprocalPrimeInterval_pred_le_log_two_add
    {L U : ℕ} (hL : 3 ≤ L) (hLU : L ≤ U)
    (hUsq : U ≤ (L - 1) ^ 2) :
    PrimeEstimates.reciprocalPrimeInterval (L - 1) U ≤
      Real.log 2 + 2 * PrimeEstimates.mertensBound := by
  have hLm : 2 ≤ L - 1 := by omega
  have hLmU : L - 1 ≤ U := by omega
  have hmass := PrimeEstimates.reciprocalPrimeInterval_le_log_log_sub_add
    hLm hLmU
  have hlogLm : 0 < Real.log ((L - 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < L - 1 by omega))
  have hUpos : (0 : ℝ) < U := by
    exact_mod_cast (show 0 < U by omega)
  have hsqpos : (0 : ℝ) < ((L - 1) ^ 2 : ℕ) := by positivity
  have hlogUle : Real.log (U : ℝ) ≤
      Real.log (((L - 1) ^ 2 : ℕ) : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using hUpos)
      (by simpa only [Set.mem_Ioi] using hsqpos)
      (by exact_mod_cast hUsq)
  have hlogUpos : 0 < Real.log (U : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < U by omega))
  have hlogSqPos : 0 < Real.log (((L - 1) ^ 2 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < (L - 1) ^ 2 by omega))
  have hloglogUle : Real.log (Real.log (U : ℝ)) ≤
      Real.log (Real.log (((L - 1) ^ 2 : ℕ) : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using hlogUpos)
      (by simpa only [Set.mem_Ioi] using hlogSqPos)
      hlogUle
  have hsquare :
      Real.log (Real.log (((L - 1) ^ 2 : ℕ) : ℝ)) -
        Real.log (Real.log ((L - 1 : ℕ) : ℝ)) = Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
    rw [Real.log_mul (by norm_num) hlogLm.ne']
    ring
  calc
    PrimeEstimates.reciprocalPrimeInterval (L - 1) U ≤
        Real.log (Real.log (U : ℝ)) -
          Real.log (Real.log ((L - 1 : ℕ) : ℝ)) +
            2 * PrimeEstimates.mertensBound := hmass
    _ ≤ Real.log (Real.log (((L - 1) ^ 2 : ℕ) : ℝ)) -
          Real.log (Real.log ((L - 1 : ℕ) : ℝ)) +
            2 * PrimeEstimates.mertensBound := by linarith
    _ = Real.log 2 + 2 * PrimeEstimates.mertensBound := by rw [hsquare]

/-- Power-sized version of the reciprocal-prime interval estimate.  The
loss grows only like `log K` when the upper endpoint is at most the
`K`-th power of the lower endpoint. -/
theorem reciprocalPrimeInterval_pred_le_log_nat_add
    {L U K : ℕ} (hL : 3 ≤ L) (hLU : L ≤ U) (hK : 0 < K)
    (hUpow : U ≤ (L - 1) ^ K) :
    PrimeEstimates.reciprocalPrimeInterval (L - 1) U ≤
      Real.log (K : ℝ) + 2 * PrimeEstimates.mertensBound := by
  have hLm : 2 ≤ L - 1 := by omega
  have hLmU : L - 1 ≤ U := by omega
  have hmass := PrimeEstimates.reciprocalPrimeInterval_le_log_log_sub_add
    hLm hLmU
  have hlogLm : 0 < Real.log ((L - 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < L - 1 by omega))
  have hUpos : (0 : ℝ) < U := by
    exact_mod_cast (show 0 < U by omega)
  have hpowpos : (0 : ℝ) < ((L - 1) ^ K : ℕ) := by positivity
  have hlogUle : Real.log (U : ℝ) ≤
      Real.log (((L - 1) ^ K : ℕ) : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using hUpos)
      (by simpa only [Set.mem_Ioi] using hpowpos)
      (by exact_mod_cast hUpow)
  have hlogUpos : 0 < Real.log (U : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < U by omega))
  have hlogPowPos : 0 < Real.log (((L - 1) ^ K : ℕ) : ℝ) :=
    Real.log_pos (by
      exact_mod_cast (show 1 < (L - 1) ^ K by
        exact one_lt_pow₀ (by omega) hK.ne'))
  have hloglogUle : Real.log (Real.log (U : ℝ)) ≤
      Real.log (Real.log (((L - 1) ^ K : ℕ) : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using hlogUpos)
      (by simpa only [Set.mem_Ioi] using hlogPowPos)
      hlogUle
  have hKreal : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hpower :
      Real.log (Real.log (((L - 1) ^ K : ℕ) : ℝ)) -
        Real.log (Real.log ((L - 1 : ℕ) : ℝ)) =
          Real.log (K : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    rw [Real.log_mul hKreal.ne' hlogLm.ne']
    ring
  calc
    PrimeEstimates.reciprocalPrimeInterval (L - 1) U ≤
        Real.log (Real.log (U : ℝ)) -
          Real.log (Real.log ((L - 1 : ℕ) : ℝ)) +
            2 * PrimeEstimates.mertensBound := hmass
    _ ≤ Real.log (Real.log (((L - 1) ^ K : ℕ) : ℝ)) -
          Real.log (Real.log ((L - 1 : ℕ) : ℝ)) +
            2 * PrimeEstimates.mertensBound := by linarith
    _ = Real.log (K : ℝ) + 2 * PrimeEstimates.mertensBound := by rw [hpower]

theorem mrSelectedPrimeReciprocalMass_block_le_log_two_add
    {I : ℕ × ℕ} (hlo : 3 ≤ I.1) (hI : I.1 ≤ I.2)
    (hsq : I.2 ≤ (I.1 - 1) ^ 2) (X : ℕ) :
    mrSelectedPrimeReciprocalMass (primesInBlock I) X ≤
      Real.log 2 + 2 * PrimeEstimates.mertensBound := by
  exact (mrSelectedPrimeReciprocalMass_primesInBlock_le I X (by omega)).trans
    (reciprocalPrimeInterval_pred_le_log_two_add hlo hI hsq)

theorem mrSelectedPrimeReciprocalMass_powerBlock_le_log_nat_add
    {I : ℕ × ℕ} {K : ℕ} (hlo : 3 ≤ I.1) (hI : I.1 ≤ I.2)
    (hK : 0 < K) (hpow : I.2 ≤ (I.1 - 1) ^ K) (X : ℕ) :
    mrSelectedPrimeReciprocalMass (primesInBlock I) X ≤
      Real.log (K : ℝ) + 2 * PrimeEstimates.mertensBound := by
  exact (mrSelectedPrimeReciprocalMass_primesInBlock_le I X (by omega)).trans
    (reciprocalPrimeInterval_pred_le_log_nat_add hlo hI hK hpow)

/-- Euler suppression for the actual denominator-weighted cofactor series,
with an absolute selected-prime loss for a square-sized Ramaré block. -/
theorem exists_uniform_norm_mrCofactorLSeries_squareBlock_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {I : ℕ × ℕ}, 3 ≤ I.1 → I.1 ≤ I.2 → I.2 ≤ (I.1 - 1) ^ 2 →
      ∀ {f : ℕ → ℂ} {A X Y : ℕ},
        IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        2 ≤ Y → Y < X →
        MRArchimedeanNonpretentious f A X →
        ∀ t : ℝ, |t| ≤ X →
          ‖mrCofactorLSeries (primesInBlock I) f
              (MRHalaszEuler.halaszPoint Y t)‖ ≤
            Real.exp
              (Real.log (riemannZeta (EulerResidue.taoExponent Y : ℂ)).re -
                Real.exp (-1) *
                  ((A : ℝ) -
                    2 * (Real.log ((X : ℝ) / (Y + 1 : ℝ)) + C) /
                      Real.log (Y + 1 : ℝ) -
                    (Real.log 2 + 2 * PrimeEstimates.mertensBound)) +
                3 * EulerQuantitative.primeQuadraticConstant) := by
  obtain ⟨C, hC, hbase⟩ :=
    exists_uniform_norm_mrCofactorLSeries_lower_halaszPoint_le
  refine ⟨C, hC, ?_⟩
  intro I hlo hI hsq f A X Y hmul hbound hY hYX hnonpret t ht
  have h := hbase (P := primesInBlock I)
    (fun p hp ↦ (mem_primesInBlock.mp hp).1)
    hmul hbound hY hYX hnonpret t ht
  refine h.trans (Real.exp_le_exp.mpr ?_)
  have hmass := mrSelectedPrimeReciprocalMass_block_le_log_two_add
    hlo hI hsq Y
  have hexp : 0 < Real.exp (-1) := Real.exp_pos _
  nlinarith

/-- Power-block form used in the source parameter hierarchy.  Increasing
the power makes the sifted exceptional density small, while its effect on
the cofactor Euler estimate is only the displayed `log K` loss. -/
theorem exists_uniform_norm_mrCofactorLSeries_powerBlock_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {I : ℕ × ℕ} {K : ℕ},
        3 ≤ I.1 → I.1 ≤ I.2 → 0 < K → I.2 ≤ (I.1 - 1) ^ K →
      ∀ {f : ℕ → ℂ} {A X Y : ℕ},
        IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        2 ≤ Y → Y < X →
        MRArchimedeanNonpretentious f A X →
        ∀ t : ℝ, |t| ≤ X →
          ‖mrCofactorLSeries (primesInBlock I) f
              (MRHalaszEuler.halaszPoint Y t)‖ ≤
            Real.exp
              (Real.log (riemannZeta (EulerResidue.taoExponent Y : ℂ)).re -
                Real.exp (-1) *
                  ((A : ℝ) -
                    2 * (Real.log ((X : ℝ) / (Y + 1 : ℝ)) + C) /
                      Real.log (Y + 1 : ℝ) -
                    (Real.log (K : ℝ) +
                      2 * PrimeEstimates.mertensBound)) +
                3 * EulerQuantitative.primeQuadraticConstant) := by
  obtain ⟨C, hC, hbase⟩ :=
    exists_uniform_norm_mrCofactorLSeries_lower_halaszPoint_le
  refine ⟨C, hC, ?_⟩
  intro I K hlo hI hK hpow f A X Y hmul hbound hY hYX hnonpret t ht
  have h := hbase (P := primesInBlock I)
    (fun p hp ↦ (mem_primesInBlock.mp hp).1)
    hmul hbound hY hYX hnonpret t ht
  refine h.trans (Real.exp_le_exp.mpr ?_)
  have hmass := mrSelectedPrimeReciprocalMass_powerBlock_le_log_nat_add
    hlo hI hK hpow Y
  have hexp : 0 < Real.exp (-1) := Real.exp_pos _
  nlinarith

end

end Erdos67
