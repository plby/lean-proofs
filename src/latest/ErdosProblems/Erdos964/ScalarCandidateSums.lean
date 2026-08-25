import ErdosProblems.Erdos964.ScalarAffineModel
import ErdosProblems.Erdos964.ScalarAffineS2

/-!
# The common actual square weight and its first and second sums
-/

namespace Erdos964

noncomputable def normalizedScalarCandidateWeight (A B : Fin 3 → ℕ)
    (hA : ∀ i, 0 < A i) (hne : ∀ i j, i ≠ j → A i * B j ≠ A j * B i)
    (hadm : ∀ p, p.Prime → ∃ n : ℕ, ∀ i, ¬ p ∣ A i * n + B i)
    (v N R n : ℕ) : ℝ :=
  let s := normalizedScalarTripleSieve A B hA hne hadm v N R
  scalarAffineWeight (fun i => A i * affineNormalizationModulus A B)
    (fun i => A i * v + B i) s.prodPrimes (scalarSelbergCoefficient s (scalarLinearY R)) n

theorem normalizedScalarCandidateWeight_nonneg (A B : Fin 3 → ℕ)
    (hA : ∀ i, 0 < A i) (hne : ∀ i j, i ≠ j → A i * B j ≠ A j * B i)
    (hadm : ∀ p, p.Prime → ∃ n : ℕ, ∀ i, ¬ p ∣ A i * n + B i)
    (v N R n : ℕ) : 0 ≤ normalizedScalarCandidateWeight A B hA hne hadm v N R n :=
  scalarAffineWeight_nonneg _ _ _ _ _

noncomputable def normalizedScalarCandidateFirstSum (A B : Fin 3 → ℕ)
    (hA : ∀ i, 0 < A i) (hne : ∀ i j, i ≠ j → A i * B j ≠ A j * B i)
    (hadm : ∀ p, p.Prime → ∃ n : ℕ, ∀ i, ¬ p ∣ A i * n + B i)
    (v N R : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico N (2 * N), normalizedScalarCandidateWeight A B hA hne hadm v N R n

noncomputable def normalizedScalarCandidateSecondSum (A B : Fin 3 → ℕ)
    (hA : ∀ i, 0 < A i) (hne : ∀ i j, i ≠ j → A i * B j ≠ A j * B i)
    (hadm : ∀ p, p.Prime → ∃ n : ℕ, ∀ i, ¬ p ∣ A i * n + B i)
    (j : Fin 3) (v N R : ℕ) (S : Finset ℕ) : ℝ :=
  let s := normalizedScalarTripleSieve A B hA hne hadm v N R
  scalarAffineSecondSum (fun i => A i * affineNormalizationModulus A B)
    (fun i => A i * v + B i) j N s.prodPrimes
      (scalarSelbergCoefficient s (scalarLinearY R)) S

theorem normalizedScalarCandidateSecondSum_eq_filter (A B : Fin 3 → ℕ)
    (hA : ∀ i, 0 < A i) (hne : ∀ i j, i ≠ j → A i * B j ≠ A j * B i)
    (hadm : ∀ p, p.Prime → ∃ n : ℕ, ∀ i, ¬ p ∣ A i * n + B i)
    (j : Fin 3) (v N R : ℕ) (S : Finset ℕ) :
    normalizedScalarCandidateSecondSum A B hA hne hadm j v N R S =
      ∑ n ∈ (Finset.Ico N (2 * N)).filter
        (fun n => A j * affineNormalizationModulus A B * n + (A j * v + B j) ∈ S),
          normalizedScalarCandidateWeight A B hA hne hadm v N R n := rfl

end Erdos964
