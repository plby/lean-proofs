import ErdosProblems.Erdos237.DyadicSupport

/-!
# The actual dyadic Y-diagonal asymptotic

The independent rectangular limit survives both the strict product cutoff
and the exclusion of shared-prime collisions. The half-exponent choice
contributes the factor `2^(-k)` to the limiting denominator.
-/

namespace Erdos237

open Finset Filter BoundedGaps.Maynard
open scoped BigOperators

theorem tendsto_sieveCoordinateScale_ratio {alpha beta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) :
    Tendsto (fun N : ℕ => sieveCoordinateScale alpha N / sieveCoordinateScale beta N)
      atTop (nhds (alpha / beta)) := by
  apply (tendsto_log_engelsmaMaynardRadius_ratio halpha hbeta).congr'
  filter_upwards [] with N
  unfold sieveCoordinateScale
  rw [mul_div_mul_left _ _ (preSieveSingularSeries_pos _).ne']

theorem eventually_dyadic_independent_sum_eq {H : Finset ℕ} {L k : ℕ}
    (e : H ≃ Fin k) {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop,
      (∑ u ∈ preSievedSimplexTupleSupport H (engelsmaMaynardRadius alpha N)
        (engelsmaMaynardModulus N),
        dyadicRawWeight (L := L) e alpha N u ^ 2 * reciprocalTotientTupleWeight H u) =
      ∑ x ∈ dyadicGoodBoxes L k, (∏ i, dyadicHeight L (x i) ^ 2) *
        engelsmaFractionalTupleShellMass H (alpha / 2)
          (fun h => dyadicLength L k (x (e h)))
          (fun h => dyadicUpper L k (x (e h))) N := by
  have hsubs : ∀ᶠ N : ℕ in atTop, ∀ x ∈ dyadicGoodBoxes L k,
      dyadicTupleShell e alpha N x ⊆
        preSievedSimplexTupleSupport H (engelsmaMaynardRadius alpha N)
          (engelsmaMaynardModulus N) :=
    (dyadicGoodBoxes L k).eventually_all.mpr
      (fun _ hx => eventually_dyadicTupleShell_subset e halpha hx)
  filter_upwards [hsubs, eventually_ge_atTop 2] with N hsub hN
  have hdisj : (dyadicGoodBoxes L k : Set (Fin k → Fin L)).Pairwise
      (fun x y => Disjoint (dyadicTupleShell e alpha N x) (dyadicTupleShell e alpha N y)) :=
    fun _ _ _ _ hxy => dyadicTupleShell_disjoint e halpha hN hxy
  have heq := sum_finiteBoxWeight_sq_mul (dyadicGoodBoxes L k)
    (preSievedSimplexTupleSupport H (engelsmaMaynardRadius alpha N)
      (engelsmaMaynardModulus N)) (dyadicTupleShell e alpha N)
    (fun x => ∏ i, dyadicHeight L (x i)) (reciprocalTotientTupleWeight H) hdisj hsub
  simpa only [dyadicRawWeight, dyadicTupleShell, engelsmaFractionalTupleShellMass, prod_pow]
    using heq

theorem tendsto_dyadic_independent_diagonal {H : Finset ℕ} {L k : ℕ}
    (hL : 0 < L) (hk : 2 ^ L ≤ k) (e : H ≃ Fin k)
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      (∑ u ∈ preSievedSimplexTupleSupport H (engelsmaMaynardRadius alpha N)
        (engelsmaMaynardModulus N),
        dyadicRawWeight (L := L) e alpha N u ^ 2 * reciprocalTotientTupleWeight H u) /
          sieveCoordinateScale alpha N ^ Fintype.card H)
      atTop (nhds (boxDenominator (dyadicSquareMass L k) (dyadicUpper L k) k *
        (1 / 2 : ℝ) ^ k)) := by
  have hhalf : 0 < alpha / 2 := by positivity
  have hmass := tendsto_dyadic_independent_box_mass hL hk e hhalf
  have hcard : Fintype.card H = k := (Fintype.card_congr e).trans (Fintype.card_fin k)
  have hratio : Tendsto (fun N : ℕ =>
      (sieveCoordinateScale (alpha / 2) N / sieveCoordinateScale alpha N) ^ k)
      atTop (nhds ((1 / 2 : ℝ) ^ k)) := by
    have h := (tendsto_sieveCoordinateScale_ratio hhalf halpha).pow k
    have heq : (alpha / 2) / alpha = 1 / 2 := by field_simp
    simpa only [heq] using h
  apply (hmass.mul hratio).congr'
  filter_upwards [eventually_dyadic_independent_sum_eq (L := L) e halpha,
    eventually_sieveCoordinateScale_pos hhalf,
    eventually_sieveCoordinateScale_pos halpha] with N heq hsmall hlarge
  rw [heq]
  simp only [normalizedEngelsmaFractionalTupleShellMass, ← mul_div_assoc]
  rw [← sum_div, div_pow, hcard]
  change (_ / sieveCoordinateScale (alpha / 2) N ^ k) *
    (sieveCoordinateScale (alpha / 2) N ^ k / sieveCoordinateScale alpha N ^ k) = _
  field_simp

theorem tendsto_dyadicY_diagonal {H : Finset ℕ} {L k : ℕ}
    (hL : 0 < L) (hk : 2 ^ L ≤ k) (e : H ≃ Fin k)
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      maynardYDiagonalSum H (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
        (dyadicY (L := L) e alpha N) / sieveCoordinateScale alpha N ^ Fintype.card H)
      atTop (nhds (boxDenominator (dyadicSquareMass L k) (dyadicUpper L k) k *
        (1 / 2 : ℝ) ^ k)) :=
  tendsto_restricted_diagonal_of_independent halpha (dyadicWeightBound_nonneg L k)
    (dyadicRawWeight e alpha) (abs_dyadicRawWeight_le e alpha)
    (tendsto_dyadic_independent_diagonal hL hk e halpha)

end Erdos237
