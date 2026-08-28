import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessGlobal
import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessEulerAlgebra

/-!
# Rationalization of the genuine global star sequence

Flatness of the rationals preserves the proved exactness of the original
integral Mayer--Vietoris maps.  Rank-nullity and finite telescoping then
give Euler additivity for the actual threefold.  The top boundary term
vanishes by the proved bound on the original overlaps.
-/

noncomputable section

open scoped BigOperators TensorProduct

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.Finiteness

open ThreefoldHomologyFinitenessAlgebra
open ThreefoldHomologyFinitenessEulerAlgebra

abbrev RationalStarOverlap (n : ℕ) := ℚ ⊗[ℤ] StarOverlapHomology n

abbrev RationalStarPair (n : ℕ) := ℚ ⊗[ℤ] StarPairHomology n

/-- Rationalization of the original signed overlap map. -/
def rationalStarLeft (n : ℕ) : RationalStarOverlap n →ₗ[ℚ] RationalStarPair n :=
  (starLeftHomologyMap n).baseChange ℚ

/-- Rationalization of the original four inclusions into the threefold. -/
def rationalStarRight (n : ℕ) : RationalStarPair n →ₗ[ℚ] RationalHomology n :=
  (starRightHomologyMap n).baseChange ℚ

/-- Rationalization of the genuine singular connecting homomorphism. -/
def rationalStarConnecting (n : ℕ) :
    RationalHomology (n + 1) →ₗ[ℚ] RationalStarOverlap n :=
  (starConnectingHomomorphism n).baseChange ℚ

theorem rationalStar_exact_at_pair (n : ℕ) :
    Function.Exact (rationalStarLeft n) (rationalStarRight n) :=
  rationalization_exact _ _ (star_exact_at_pair n)

theorem rationalStar_exact_at_ambient (n : ℕ) :
    Function.Exact (rationalStarRight (n + 1)) (rationalStarConnecting n) :=
  rationalization_exact _ _ (star_exact_at_ambient n)

theorem rationalStar_exact_at_intersection (n : ℕ) :
    Function.Exact (rationalStarConnecting n) (rationalStarLeft n) :=
  rationalization_exact _ _ (star_exact_at_intersection n)

theorem rationalStarRight_zero_surjective : Function.Surjective (rationalStarRight 0) :=
  rationalization_surjective _ starRightHomologyMap_zero_surjective

theorem rationalStarOverlap_finite (n : ℕ) : Module.Finite ℚ (RationalStarOverlap n) := by
  have := starOverlapHomology_finite n
  exact rationalization_finite (StarOverlapHomology n)

theorem rationalStarPair_finite (n : ℕ) : Module.Finite ℚ (RationalStarPair n) := by
  have := starPairHomology_finite n
  exact rationalization_finite (StarPairHomology n)

theorem rationalStarOverlap_subsingleton_of_lt {n : ℕ} (hn : 5 < n) :
    Subsingleton (RationalStarOverlap n) := by
  have := starOverlapHomology_subsingleton hn
  infer_instance

/-- Euler additivity follows from the actual maps.  No coordinate matrix,
splitting of the sequence, or unknown Betti number is a hypothesis. -/
theorem rational_star_euler_of_le {N : ℕ} (hN : 6 ≤ N) :
    (∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (rationalBetti n : ℤ)) =
      (∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n *
        (Module.finrank ℚ (RationalStarPair n) : ℤ)) -
      (∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n *
        (Module.finrank ℚ (RationalStarOverlap n) : ℤ)) := by
  have : ∀ n, Module.Finite ℚ (RationalStarOverlap n) := rationalStarOverlap_finite
  have : ∀ n, Module.Finite ℚ (RationalStarPair n) := rationalStarPair_finite
  have : ∀ n, Module.Finite ℚ (RationalHomology n) := rational_homology_finite
  exact rational_finrank_euler_of_exact_sequence
    rationalStarLeft rationalStarRight rationalStarConnecting
    rationalStar_exact_at_pair rationalStar_exact_at_ambient
    rationalStar_exact_at_intersection rationalStarRight_zero_surjective N
    (rationalStarOverlap_subsingleton_of_lt (by omega))

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.Finiteness
