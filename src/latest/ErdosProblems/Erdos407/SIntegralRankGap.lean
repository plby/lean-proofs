/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.RankDrop

/-!
# The determinant gap for `Z[1/6]` approximation boxes

Exterior coordinates in the rational Subspace-Theorem argument are
`S`-integral rather than integral.  The determinant argument still applies:
the determinant of an `S`-integral matrix is an `S`-integer, and the product
of its norms at infinity, `2`, and `3` is at least one when it is nonzero.
-/

namespace Erdos407.RankDrop

open scoped BigOperators Matrix

open Erdos407.PadicSubspace

/-- Exact determinant change of coordinates for a rational row family. -/
theorem det_rationalLocalEvaluationRowMatrix {n : ℕ}
    (L : LocalForms n) (v : Place23) (x : Fin n → RatVector n) :
    (rationalLocalEvaluationRowMatrix L v x).det =
      (rationalRowMatrix x).det * (formMatrix L v).det := by
  rw [rationalLocalEvaluationRowMatrix_eq_mul, Matrix.det_mul,
    Matrix.det_transpose]

/-- Product formula after changing to each of the three local form bases. -/
theorem prod_realPlaceNorm_det_rationalLocalEvaluationRowMatrix {n : ℕ}
    (L : LocalForms n) (x : Fin n → RatVector n) :
    (∏ v, HeightBoxes.realPlaceNorm v
      (rationalLocalEvaluationRowMatrix L v x).det) =
      PadicProduct.normProduct23 (rationalRowMatrix x).det *
        realFormDetProduct L := by
  simp_rw [det_rationalLocalEvaluationRowMatrix,
    HeightBoxes.realPlaceNorm, placeNorm_mul, Rat.cast_mul,
    Finset.prod_mul_distrib]
  have hpoints :
      (∏ v, (placeNorm v (rationalRowMatrix x).det : ℝ)) =
        PadicProduct.normProduct23 (rationalRowMatrix x).det := by
    have h := congrArg ((↑) : ℚ → ℝ)
      (PadicSubspace.prod_placeNorm_eq_threePlaceProduct
        (rationalRowMatrix x).det)
    simpa using h
  rw [hpoints]
  have hforms :
      (∏ v, (placeNorm v (formMatrix L v).det : ℝ)) =
        realFormDetProduct L := by
    simp [realFormDetProduct, formDetProduct]
  rw [hforms]

/-- Product-form determinant bound for rational points in one real box. -/
theorem prod_realPlaceNorm_det_rationalLocalEvaluationRowMatrix_le {n : ℕ}
    (L : LocalForms n) (x : Fin n → RatVector n)
    (c : Place23 → Fin n → ℝ)
    (hc : ∀ v i, 0 ≤ c v i)
    (hx : ∀ j v i,
      HeightBoxes.realPlaceNorm v (L v i (x j)) ≤ c v i) :
    (∏ v, HeightBoxes.realPlaceNorm v
      (rationalLocalEvaluationRowMatrix L v x).det) ≤
      (Nat.factorial n : ℝ) ^ 3 *
        PadicSubspace.realLocalRadiiProduct c := by
  calc
    (∏ v, HeightBoxes.realPlaceNorm v
      (rationalLocalEvaluationRowMatrix L v x).det) ≤
        ∏ v, ((Nat.factorial n : ℝ) * ∏ i, c v i) := by
      apply Finset.prod_le_prod
      · intro v _
        exact HeightBoxes.realPlaceNorm_nonneg v _
      · intro v _
        have hv := PadicSubspace.real_placeNorm_det_le_rowProduct v
          (rationalLocalEvaluationRowMatrix L v x)ᵀ (c v) (hc v)
          (fun i j ↦ by
            change (placeNorm v (L v i (x j)) : ℝ) ≤ c v i
            exact hx j v i)
        simpa [HeightBoxes.realPlaceNorm] using hv
    _ = (Nat.factorial n : ℝ) ^ 3 *
        PadicSubspace.realLocalRadiiProduct c := by
      simp [PadicSubspace.realLocalRadiiProduct, Finset.prod_mul_distrib]

/-- A sufficiently small three-place box cannot contain a rational basis
whose coordinates all lie in `Z[1/6]`. -/
theorem not_linearIndependent_of_real_sIntegral_local_bounds {n : ℕ}
    (L : LocalForms n) (x : Fin n → RatVector n)
    (hxS : ∀ j, AdelicMinkowski.InZOneSix (x j))
    (c : Place23 → Fin n → ℝ)
    (hc : ∀ v i, 0 ≤ c v i)
    (hx : ∀ j v i,
      HeightBoxes.realPlaceNorm v (L v i (x j)) ≤ c v i)
    (hsmall : (Nat.factorial n : ℝ) ^ 3 *
        PadicSubspace.realLocalRadiiProduct c < realFormDetProduct L) :
    ¬ LinearIndependent ℚ x := by
  intro hlin
  have hrows : LinearIndependent ℚ (rationalRowMatrix x).row := by
    change LinearIndependent ℚ x
    exact hlin
  have hunit : IsUnit (rationalRowMatrix x) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  have hdet0 : (rationalRowMatrix x).det ≠ 0 :=
    ((rationalRowMatrix x).isUnit_iff_isUnit_det.mp hunit).ne_zero
  have hdetS : SIntegerSix.IsSInteger (rationalRowMatrix x).det := by
    apply SIntegerSix.det
    intro i j
    exact SIntegerSix.of_inZOneSix_coordinate (hxS i) j
  have hnorm : (1 : ℝ) ≤
      PadicProduct.normProduct23 (rationalRowMatrix x).det := by
    exact_mod_cast SIntegerSix.one_le_normProduct23 hdetS hdet0
  have hleft : realFormDetProduct L ≤
      PadicProduct.normProduct23 (rationalRowMatrix x).det *
        realFormDetProduct L := by
    simpa [mul_comm] using
      (le_mul_of_one_le_right (realFormDetProduct_nonneg L) hnorm)
  rw [← prod_realPlaceNorm_det_rationalLocalEvaluationRowMatrix] at hleft
  have hupper :=
    prod_realPlaceNorm_det_rationalLocalEvaluationRowMatrix_le L x c hc hx
  exact (not_lt_of_ge (hleft.trans hupper)) hsmall

/-- Full rank is impossible in a small `S`-integral approximation box. -/
theorem not_hasRankAtLeast_realSIntegralApproximationDomain {n : ℕ}
    (L : LocalForms n) (Q : ℕ) (c : HeightBoxes.LocalConstants n)
    (hsmall : (Nat.factorial n : ℝ) ^ 3 *
        HeightBoxes.exponentRadiiProduct (Q : ℝ) c <
      realFormDetProduct L) :
    ¬ AdelicMinkowski.HasRankAtLeast
      (realSIntegralApproximationDomain L Q c) n := by
  rintro ⟨x, hlin, hx⟩
  apply not_linearIndependent_of_real_sIntegral_local_bounds L x
    (fun j ↦ (hx j).1)
    (HeightBoxes.exponentRadius (Q : ℝ) c)
    (fun v i ↦ Real.rpow_nonneg (Nat.cast_nonneg Q) (c v i))
    (fun j v i ↦ (hx j).2 v i)
  · simpa [PadicSubspace.realLocalRadiiProduct,
      HeightBoxes.exponentRadiiProduct] using hsmall
  · exact hlin

/-- Rank form of the preceding determinant gap. -/
theorem realSApproximationRank_lt_of_radiiProduct {n : ℕ}
    (L : LocalForms n) (Q : ℕ) (c : HeightBoxes.LocalConstants n)
    (hsmall : (Nat.factorial n : ℝ) ^ 3 *
        HeightBoxes.exponentRadiiProduct (Q : ℝ) c <
      realFormDetProduct L) :
    realSApproximationRank L Q c < n := by
  apply lt_of_not_ge
  intro hfull
  apply not_hasRankAtLeast_realSIntegralApproximationDomain L Q c hsmall
  exact (hasRankAtLeast_iff_le_finrank
    (realSIntegralApproximationDomain L Q c)).mpr hfull

/-- A negative total exponent makes all sufficiently large `S`-integral
real-exponent boxes rank deficient. -/
theorem eventually_realSApproximationRank_lt {n : ℕ}
    (L : LocalForms n) (hL : PadicSubspace.IsNonsingularFamily L)
    (c : HeightBoxes.LocalConstants n) {delta : ℝ} (hdelta : 0 < delta)
    (hc : (∑ v, ∑ i, c v i) ≤ -delta) :
    ∀ᶠ Q : ℕ in Filter.atTop, realSApproximationRank L Q c < n := by
  have hdet : 0 < PadicSubspace.realFormDetProduct L :=
    PadicSubspace.realFormDetProduct_pos hL
  have htendsto : Filter.Tendsto
      (fun Q : ℕ ↦ (Nat.factorial n : ℝ) ^ 3 * (Q : ℝ) ^ (-delta))
      Filter.atTop (nhds 0) := by
    simpa [Function.comp_def] using
      ((tendsto_rpow_neg_atTop hdelta).comp
        tendsto_natCast_atTop_atTop).const_mul ((Nat.factorial n : ℝ) ^ 3)
  have hsmallEventually : ∀ᶠ Q : ℕ in Filter.atTop,
      (Nat.factorial n : ℝ) ^ 3 * (Q : ℝ) ^ (-delta) <
        PadicSubspace.realFormDetProduct L :=
    htendsto.eventually (Iio_mem_nhds hdet)
  filter_upwards [hsmallEventually, Filter.eventually_ge_atTop 1] with
      Q hsmall hQ
  apply realSApproximationRank_lt_of_radiiProduct L Q c
  calc
    (Nat.factorial n : ℝ) ^ 3 *
        HeightBoxes.exponentRadiiProduct (Q : ℝ) c ≤
      (Nat.factorial n : ℝ) ^ 3 * (Q : ℝ) ^ (-delta) := by
        gcongr
        exact HeightBoxes.exponentRadiiProduct_le (by exact_mod_cast hQ) hc
    _ < PadicSubspace.realFormDetProduct L := hsmall

/-- A concrete cutoff form of `eventually_realSApproximationRank_lt`. -/
theorem exists_sRankDeficient_cutoff {n : ℕ}
    (L : LocalForms n) (hL : PadicSubspace.IsNonsingularFamily L)
    (c : HeightBoxes.LocalConstants n) {delta : ℝ} (hdelta : 0 < delta)
    (hc : (∑ v, ∑ i, c v i) ≤ -delta) :
    ∃ Q₀ : ℕ, ∀ Q, Q₀ ≤ Q → realSApproximationRank L Q c < n := by
  simpa only [Filter.eventually_atTop] using
    eventually_realSApproximationRank_lt L hL c hdelta hc

end Erdos407.RankDrop
