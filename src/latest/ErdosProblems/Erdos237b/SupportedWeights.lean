import ErdosProblems.Erdos237b.SieveCollisionLimits

/-!
# Restricting bounded weights to Maynard's divisor support

The restriction introduces exactly the shared-prime collisions already
controlled in `SieveCollisionLimits`. Thus an independent tuple asymptotic
for bounded weights transfers to the actual Y-diagonal.
-/

namespace Erdos237b

open Finset Filter BoundedGaps.Maynard
open scoped BigOperators

noncomputable def restrictToMaynardSupport (H : Finset ℕ) (R W : ℕ)
    (f : (H → ℕ) → ℝ) (r : H → ℕ) : ℝ := by
  classical
  exact if r ∈ maynardDivisorTupleSupport H R W then f r else 0

theorem restrictToMaynardSupport_supported (H : Finset ℕ) (R W : ℕ)
    (f : (H → ℕ) → ℝ) :
    IsSupportedMaynardY H R W (restrictToMaynardSupport H R W f) := by
  classical
  intro r hr
  by_cases hmem : r ∈ maynardDivisorTupleSupport H R W
  · exact isMaynardDivisorTuple_of_mem_support hmem
  · exact False.elim (hr (by simp [restrictToMaynardSupport, hmem]))

theorem abs_restrictToMaynardSupport_le {H : Finset ℕ} (R W : ℕ)
    {f : (H → ℕ) → ℝ} {B : ℝ} (hB : 0 ≤ B) (hf : ∀ r, |f r| ≤ B) (r : H → ℕ) :
    |restrictToMaynardSupport H R W f r| ≤ B := by
  classical
  unfold restrictToMaynardSupport
  split_ifs
  · exact hf r
  · simpa using hB

theorem yDiagonal_restrictToMaynardSupport (H : Finset ℕ) (R W : ℕ)
    (f : (H → ℕ) → ℝ) :
    maynardYDiagonalSum H R W (restrictToMaynardSupport H R W f) =
      ∑ u ∈ maynardDivisorTupleSupport H R W,
        f u ^ 2 * reciprocalTotientTupleWeight H u := by
  classical
  unfold maynardYDiagonalSum
  apply sum_congr rfl
  intro u hu
  simp only [restrictToMaynardSupport, if_pos hu, reciprocalTotientTupleWeight,
    div_eq_mul_inv, one_mul, prod_inv_distrib]

theorem independent_eq_restricted_diagonal_add_collision
    (H : Finset ℕ) (R W : ℕ) (f : (H → ℕ) → ℝ) :
    (∑ u ∈ preSievedSimplexTupleSupport H R W,
      f u ^ 2 * reciprocalTotientTupleWeight H u) =
      maynardYDiagonalSum H R W (restrictToMaynardSupport H R W f) +
        ∑ u ∈ preSievedSimplexCollisionSupport H R W,
          f u ^ 2 * reciprocalTotientTupleWeight H u := by
  rw [yDiagonal_restrictToMaynardSupport]
  exact sum_preSievedSimplex_eq_maynard_add_collision H R W _

theorem tendsto_restricted_diagonal_of_independent
    {H : Finset ℕ} {alpha B I : ℝ} (halpha : 0 < alpha) (hB : 0 ≤ B)
    (f : ℕ → (H → ℕ) → ℝ) (hf : ∀ N r, |f N r| ≤ B)
    (hind : Tendsto (fun N : ℕ =>
      (∑ u ∈ preSievedSimplexTupleSupport H
        (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N),
        f N u ^ 2 * reciprocalTotientTupleWeight H u) /
          sieveCoordinateScale alpha N ^ Fintype.card H) atTop (nhds I)) :
    Tendsto (fun N : ℕ =>
      maynardYDiagonalSum H (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
        (restrictToMaynardSupport H (engelsmaMaynardRadius alpha N)
          (engelsmaMaynardModulus N) (f N)) /
          sieveCoordinateScale alpha N ^ Fintype.card H) atTop (nhds I) := by
  have hcollision := tendsto_normalized_weighted_collision halpha hB f hf
  have hdiff := hind.sub hcollision
  simp only [sub_zero] at hdiff
  apply hdiff.congr'
  filter_upwards [] with N
  rw [independent_eq_restricted_diagonal_add_collision]
  ring

end Erdos237b
