/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Large-prime weights and their prefixes under arbitrary coordinate orders.
Informal source: BBMST Section 7.1.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.FrameDivisorProfiles
import ErdosProblems.Erdos1189.SqrtPrefixSums

namespace Erdos1189

open Finset

def largeCoordinates (N T : ℕ) : Finset (PrimeCoordinate N) :=
  univ.filter (fun c => T < coordinateSize c)

def largeCoordinateWeight (N T : ℕ) : ℕ :=
  ∑ c ∈ largeCoordinates N T, (coordinateSize c - 1)

lemma profileWeight_prefix_large {N : ℕ} (rank : PrimeCoordinate N → ℕ)
    (i : PrimeCoordinate N) (T : ℕ) :
    profileWeight (N.primeFactors.filter (fun p => T < p)) (fibreExponent (rankPrefix rank i)) =
      prefixWeight (largeCoordinates N T) rank (fun c => coordinateSize c - 1) i := by
  rw [profileWeight_fibreExponent_on]
  unfold prefixWeight rankPrefix largeCoordinates
  congr 1
  ext c
  simp only [mem_filter, mem_univ, true_and, c.1.property, coordinateSize]
  constructor
  · intro h
    exact ⟨mem_filter.mpr ⟨mem_univ _, h.2⟩, h.1⟩
  · intro h
    exact ⟨h.2, (mem_filter.mp h.1).2⟩

lemma profileWeight_large_factorization (N T : ℕ) :
    profileWeight (N.primeFactors.filter (fun p => T < p)) N.factorization =
      largeCoordinateWeight N T := by
  have heq : profileWeight (N.primeFactors.filter (fun p => T < p)) N.factorization =
      profileWeight (N.primeFactors.filter (fun p => T < p))
        (fibreExponent (N := N) univ) := by
    apply sum_congr rfl
    intro p hp
    rw [fibreExponent_univ (N := N) ⟨p, (mem_filter.mp hp).1⟩]
  rw [heq, profileWeight_fibreExponent_on]
  unfold largeCoordinateWeight
  congr 1
  ext c
  simp only [largeCoordinates, mem_filter, mem_univ, true_and, c.1.property, coordinateSize]
  exact ⟨fun h => mem_filter.mpr ⟨mem_univ _, h⟩, fun h => (mem_filter.mp h).2⟩

lemma profileWeight_fibreExponent_le {N : ℕ} (S : Finset (PrimeCoordinate N)) :
    profileWeight N.primeFactors (fibreExponent S) ≤ simpsonWeight N := by
  rw [profileWeight_fibreExponent, ← sum_coordinateSize]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)

lemma largeCoordinateWeight_le (N T : ℕ) : largeCoordinateWeight N T ≤ simpsonWeight N := by
  rw [largeCoordinateWeight, ← sum_coordinateSize]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)

end Erdos1189
