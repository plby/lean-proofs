/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform entropy bounds for frame profiles and unrestricted remaining moduli.
Informal source: BBMST Lemmas 7.1--7.3.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.BoundedProfiles
import ErdosProblems.Erdos1189.LargeCoordinateWeights
import ErdosProblems.Erdos1189.RootLogCutoff

namespace Erdos1189

noncomputable def frameEntropyError (C : ℝ) (N T : ℕ) : ℝ :=
  C + T * Real.log ((simpsonWeight N : ℝ) + 1) + Real.log 2 +
    T * Real.log ((T : ℝ) + 1)

lemma frameEntropyError_nonneg {C : ℝ} (hC : 0 ≤ C) (N T : ℕ) :
    0 ≤ frameEntropyError C N T := by
  have hW : 0 ≤ Real.log ((simpsonWeight N : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (simpsonWeight N) (α := ℝ); linarith)
  have hT : 0 ≤ Real.log ((T : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg T (α := ℝ); linarith)
  have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  exact add_nonneg (add_nonneg (add_nonneg hC (mul_nonneg (Nat.cast_nonneg _) hW)) h2)
    (mul_nonneg (Nat.cast_nonneg _) hT)

theorem exists_uniform_frame_entropy_bounds {b : ℝ} (hb : 2 * Real.sqrt tau < b) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (N : ℕ) (rank : PrimeCoordinate N → ℕ) (i : PrimeCoordinate N) (T : ℕ),
        Real.log (frameAllowedModuli rank i T).card ≤
          b * rootLog (prefixWeight (largeCoordinates N T) rank
            (fun c => coordinateSize c - 1) i) + frameEntropyError C N T) ∧
      (∀ N T : ℕ, Real.log (boundedProfileModuli N N.factorization).card ≤
        b * rootLog (largeCoordinateWeight N T) + frameEntropyError C N T) := by
  obtain ⟨C, hC, hbound⟩ := exists_profileEntropy_large_prime_bound hb
  refine ⟨C, hC, ?_, ?_⟩
  · intro N rank i T
    have hprofile := hbound N.primeFactors (fibreExponent (rankPrefix rank i)) T
      (fun p hp => Nat.prime_of_mem_primeFactors hp)
    rw [profileWeight_prefix_large] at hprofile
    change profileEntropy N.primeFactors (fibreExponent (rankPrefix rank i)) ≤
      b * rootLog (prefixWeight (largeCoordinates N T) rank (fun c => coordinateSize c - 1) i) +
        C + T * Real.log
          ((profileWeight N.primeFactors (fibreExponent (rankPrefix rank i)) : ℝ) + 1)
      at hprofile
    have hlog : Real.log
        ((profileWeight N.primeFactors (fibreExponent (rankPrefix rank i)) : ℝ) + 1) ≤
          Real.log ((simpsonWeight N : ℝ) + 1) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast Nat.add_le_add_right (profileWeight_fibreExponent_le (rankPrefix rank i)) 1
    have hlogT := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg T (α := ℝ))
    have hallowed := log_frameAllowedModuli_card rank i T
    unfold frameEntropyError
    linarith
  · intro N T
    rw [log_boundedProfileModuli_card]
    have hprofile := hbound N.primeFactors N.factorization T
      (fun p hp => Nat.prime_of_mem_primeFactors hp)
    rw [profileWeight_large_factorization] at hprofile
    change profileEntropy N.primeFactors N.factorization ≤
      b * rootLog (largeCoordinateWeight N T) + C + T * Real.log ((simpsonWeight N : ℝ) + 1)
      at hprofile
    have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hT : 0 ≤ (T : ℝ) * Real.log ((T : ℝ) + 1) := mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (by have := Nat.cast_nonneg T (α := ℝ); linarith))
    unfold frameEntropyError
    linarith

end Erdos1189
