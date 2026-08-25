import ErdosProblems.Erdos1197.BMPrimeCoefficients

namespace Erdos1197

open Chebyshev
open MeasureTheory Set
open scoped Asymptotics BigOperators Chebyshev ENNReal

noncomputable section

lemma bm_flat_intrel_of_prime_window
    {k ν : ℕ} (hν : 3 ≤ ν) (p : PrimeIdx k → ℕ)
    (hpPairwise : Pairwise (fun i j => p i ≠ p j))
    (hpPrime : ∀ i, Nat.Prime (p i))
    (hp_window :
      ∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
            (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν) :
    ∀ r : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ,
      (∃ z : ℤ, ∑ j, bmFlatAlpha p j * (r j : ℝ) = z) →
      ∃ z : ℤ, ∑ j, bmFlatBeta k ν j * (r j : ℝ) = z := by
  intro r hrel
  let rBM : BMIdx k ν → ℤ := fun x => r (bmFlatEquiv k ν x)
  rcases hrel with ⟨z, hz⟩
  have hzBM :
      ∑ x : BMIdx k ν, bmAlpha p x * (rBM x : ℝ) = z := by
    have hsum' :
        ∑ x : BMIdx k ν, bmAlpha p x * (rBM x : ℝ) =
          ∑ j : Fin (2 ^ k + (2 ^ (ν - 2) + 1)), bmFlatAlpha p j * (r j : ℝ) := by
      exact Fintype.sum_equiv (bmFlatEquiv k ν)
        (fun x : BMIdx k ν => bmAlpha p x * (rBM x : ℝ))
        (fun j : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) => bmFlatAlpha p j * (r j : ℝ))
        (fun x => by
          cases x with
          | inl i => simp [rBM, bmFlatAlpha, bmAlpha, bmFlatEquiv]
          | inr j => simp [rBM, bmFlatAlpha, bmAlpha, bmFlatEquiv])
    have hsum :
        ∑ x : BMIdx k ν, bmAlpha p x * (rBM x : ℝ) =
          ∑ j : Fin (2 ^ k + (2 ^ (ν - 2) + 1)), bmFlatAlpha p j * (r j : ℝ) := by
      simpa [rBM, bmFlatAlpha, bmAlpha, bmFlatEquiv] using hsum'
    exact hsum.trans hz
  have hzSplit :
      (∑ i : PrimeIdx k, Real.logb 2 (p i : ℝ) * (rBM (Sum.inl i) : ℝ)) +
          ∑ j : IntIdx ν, Real.logb 2 (bmIntVal ν j : ℝ) * (rBM (Sum.inr j) : ℝ) = z := by
    simpa [bmAlpha, rBM, Fintype.sum_sum_type, mul_comm, mul_left_comm, mul_assoc] using hzBM
  have hAB : bmA p rBM z = bmB p rBM z :=
    bm_product_eq_of_log_relation hν p hpPrime rBM z hzSplit
  have hprimeCoeffZero : ∀ i : PrimeIdx k, rBM (Sum.inl i) = 0 :=
    bm_prime_coeff_zero_of_product_eq hν p hpPairwise hpPrime hp_window rBM z hAB
  refine ⟨0, ?_⟩
  have hbetaBM :
      ∑ x : BMIdx k ν, bmBeta k ν x * (rBM x : ℝ) = 0 := by
    rw [Fintype.sum_sum_type]
    simp [bmBeta, hprimeCoeffZero, rBM]
  have hbetaFlat :
      ∑ j : Fin (2 ^ k + (2 ^ (ν - 2) + 1)), bmFlatBeta k ν j * (r j : ℝ) = 0 := by
    have hbetaFlat' :
        ∑ x : BMIdx k ν, bmBeta k ν x * (rBM x : ℝ) =
          ∑ j : Fin (2 ^ k + (2 ^ (ν - 2) + 1)), bmFlatBeta k ν j * (r j : ℝ) := by
      exact Fintype.sum_equiv (bmFlatEquiv k ν)
        (fun x : BMIdx k ν => bmBeta k ν x * (rBM x : ℝ))
        (fun j : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) => bmFlatBeta k ν j * (r j : ℝ))
        (fun x => by
          cases x with
          | inl i => simp [rBM, bmFlatBeta, bmBeta, bmFlatEquiv]
          | inr j => simp [rBM, bmFlatBeta, bmBeta, bmFlatEquiv])
    exact hbetaFlat'.symm.trans hbetaBM
  simpa using hbetaFlat

end

end Erdos1197
