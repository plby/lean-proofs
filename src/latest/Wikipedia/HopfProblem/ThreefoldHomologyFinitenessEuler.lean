import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessEulerPieces
import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessEulerSequence

/-!
# Euler characteristic two for the actual constructed threefold

The genuine global star sequence gives Euler additivity.  Its original
regular family and three overlaps contribute zero, the two elliptic
pieces contribute zero, and the full original cusp piece contributes
two.  The rational Betti numbers vanish above six, so this finite sum
is the Euler characteristic of the actual threefold.
-/

noncomputable section

open scoped BigOperators

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.Finiteness

/-- The actual alternating Betti sum is two for every cutoff beyond
the proved homology bound. -/
theorem euler_sum_eq_two (N : ℕ) (hN : 7 ≤ N) :
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (rationalBetti n : ℤ)) = 2 := by
  cases N with
  | zero => omega
  | succ N =>
    rw [rational_star_euler_of_le (by omega : 6 ≤ N)]
    rw [starPairRationalHomology_euler_of_le (by omega : 6 ≤ N + 1),
      starOverlapRationalHomology_euler_of_le (by omega : 6 ≤ N + 1)]
    norm_num

/-- Euler characteristic computed from the genuine rationalized integral
singular homology, with the proved degree-six bound. -/
def eulerCharacteristic : ℤ :=
  ∑ n ∈ Finset.range 7, (-1 : ℤ) ^ n * (rationalBetti n : ℤ)

theorem eulerCharacteristic_eq_two : eulerCharacteristic = 2 :=
  euler_sum_eq_two 7 (by decide)

/-- The same Euler characteristic is obtained with any larger finite cutoff. -/
theorem eulerCharacteristic_eq_sum (N : ℕ) (hN : 7 ≤ N) :
    eulerCharacteristic =
      ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (rationalBetti n : ℤ) :=
  eulerCharacteristic_eq_two.trans (euler_sum_eq_two N hN).symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.Finiteness
