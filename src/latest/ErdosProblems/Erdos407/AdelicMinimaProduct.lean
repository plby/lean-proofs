/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.AdelicSuccessiveMinima
import ErdosProblems.Erdos407.SIntegralRankGap

/-!
# The lower product estimate for the three-place successive minima

This file proves the determinant half of the adelic second theorem needed in
the rational Subspace-Theorem argument.  If an `S`-integral rational basis is
contained in the local box dilated at infinity by factors `lambda_j`, the
product formula for its determinant gives a lower bound for the product of
the dilation factors.  The proof keeps the individual row factors throughout
the Leibniz expansion; replacing them by their maximum would lose exactly the
product estimate needed at the exterior-power endpoint.

The resulting bound is also rearranged into the usual
`C * Q ^ (-sum c) <= product lambda` form.  For ordered dilation factors this
forces the last successive minimum to grow, and a final eventual estimate
absorbs the fixed determinant constant into half of the exponent.
-/

namespace Erdos407.PadicSubspace

open scoped BigOperators Matrix

namespace AdelicMinima

open Erdos407 HeightBoxes

/-- A two-sided row/column version of the Leibniz determinant bound.  This
form is what retains the product of the successive-minimum factors: `a`
contains the row dilations and `b` the undilated local radii. -/
theorem real_placeNorm_det_le_row_mul_col_product {n : ℕ} (v : Place23)
    (M : Matrix (Fin n) (Fin n) ℚ) (a b : Fin n → ℝ)
    (_ha : ∀ i, 0 ≤ a i) (_hb : ∀ i, 0 ≤ b i)
    (hM : ∀ i j, (placeNorm v (M i j) : ℝ) ≤ a i * b j) :
    (placeNorm v M.det : ℝ) ≤
      (Nat.factorial n : ℝ) * (∏ i, a i) * ∏ j, b j := by
  classical
  let abv : AbsoluteValue ℚ ℚ :=
    IsAbsoluteValue.toAbsoluteValue (placeNorm v)
  rw [← Matrix.det_transpose, Matrix.det_apply]
  calc
    (placeNorm v (∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
        ∏ i, Mᵀ (σ i) i) : ℚ) ≤
        ((∑ σ : Equiv.Perm (Fin n),
          placeNorm v (Equiv.Perm.sign σ • ∏ i, Mᵀ (σ i) i) : ℚ) : ℝ) := by
      exact_mod_cast (abv.sum_le Finset.univ
        (fun σ : Equiv.Perm (Fin n) =>
          Equiv.Perm.sign σ • ∏ i, Mᵀ (σ i) i))
    _ = ∑ σ : Equiv.Perm (Fin n),
          ∏ i, (placeNorm v (M i (σ i)) : ℝ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro σ _
      have hq : placeNorm v (Equiv.Perm.sign σ • ∏ i, Mᵀ (σ i) i) =
          ∏ i, placeNorm v (M i (σ i)) := by
        change abv (Equiv.Perm.sign σ • ∏ i, Mᵀ (σ i) i) = _
        rw [abv.map_units_int_smul, abv.map_prod]
        rfl
      exact_mod_cast hq
    _ ≤ ∑ _σ : Equiv.Perm (Fin n),
          ((∏ i, a i) * ∏ j, b j) := by
      apply Finset.sum_le_sum
      intro σ _
      calc
        (∏ i, (placeNorm v (M i (σ i)) : ℝ)) ≤
            ∏ i, (a i * b (σ i)) := by
          apply Finset.prod_le_prod
          · intro i _
            exact_mod_cast placeNorm_nonneg v (M i (σ i))
          · intro i _
            exact hM i (σ i)
        _ = (∏ i, a i) * ∏ i, b (σ i) :=
          Finset.prod_mul_distrib
        _ = (∏ i, a i) * ∏ j, b j := by
          congr 1
          exact Equiv.prod_comp σ b
    _ = (Nat.factorial n : ℝ) * (∏ i, a i) * ∏ j, b j := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp [Fintype.card_perm]
      ring

theorem placeScale_nonneg (v : Place23) {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    0 ≤ placeScale v lambda := by
  simp only [placeScale]
  split_ifs
  · exact hlambda
  · exact zero_le_one

/-- Across the three retained rational places, a row dilation contributes
exactly its Archimedean factor. -/
theorem prod_placeScale (lambda : ℝ) :
    (∏ v : Place23, placeScale v lambda) = lambda := by
  simp [Fin.prod_univ_succ, placeScale, Place23.infinite]

/-- The product of all row dilations at all three places is the product of
the Archimedean successive-minimum factors. -/
theorem prod_prod_placeScale {n : ℕ} (lambda : Fin n → ℝ) :
    (∏ v : Place23, ∏ j : Fin n, placeScale v (lambda j)) =
      ∏ j, lambda j := by
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  exact prod_placeScale (lambda j)

/-- Product-form upper bound for the three local evaluation determinants,
retaining the individual Archimedean row dilations. -/
theorem prod_realPlaceNorm_det_le_with_row_scales {n : ℕ}
    (L : LocalForms n) (x : Fin n → RatVector n) (lambda : Fin n → ℝ)
    (hlambda : ∀ j, 0 ≤ lambda j) {Q : ℕ} (c : LocalConstants n)
    (hbound : ∀ j v i,
      realPlaceNorm v (L v i (x j)) ≤
        placeScale v (lambda j) * exponentRadius (Q : ℝ) c v i) :
    (∏ v, realPlaceNorm v
      (Erdos407.RankDrop.rationalLocalEvaluationRowMatrix L v x).det) ≤
      (Nat.factorial n : ℝ) ^ 3 * (∏ j, lambda j) *
        exponentRadiiProduct (Q : ℝ) c := by
  calc
    (∏ v, realPlaceNorm v
      (Erdos407.RankDrop.rationalLocalEvaluationRowMatrix L v x).det) ≤
        ∏ v, ((Nat.factorial n : ℝ) *
          (∏ j, placeScale v (lambda j)) *
          ∏ i, exponentRadius (Q : ℝ) c v i) := by
      apply Finset.prod_le_prod
      · intro v _
        exact realPlaceNorm_nonneg v _
      · intro v _
        simpa [realPlaceNorm] using
          real_placeNorm_det_le_row_mul_col_product v
            (Erdos407.RankDrop.rationalLocalEvaluationRowMatrix L v x)
            (fun j => placeScale v (lambda j))
            (fun i => exponentRadius (Q : ℝ) c v i)
            (fun j => placeScale_nonneg v (hlambda j))
            (fun i => Real.rpow_nonneg (Nat.cast_nonneg Q) (c v i))
            (fun j i => hbound j v i)
    _ = (Nat.factorial n : ℝ) ^ 3 * (∏ j, lambda j) *
        exponentRadiiProduct (Q : ℝ) c := by
      simp only [Finset.prod_mul_distrib]
      rw [prod_prod_placeScale]
      simp [exponentRadiiProduct]

/-- Determinant/product-formula lower estimate for an `S`-integral rational
basis in an adelically dilated approximation box. -/
theorem product_lower_of_local_bounds {n : ℕ} [NeZero n]
    (L : LocalForms n) (x : Fin n → RatVector n) (lambda : Fin n → ℝ)
    (hx : LinearIndependent ℚ x)
    (hxS : ∀ j, AdelicMinkowski.InZOneSix (x j))
    (hlambda : ∀ j, 0 ≤ lambda j) {Q : ℕ} (_hQ : 1 ≤ Q)
    (c : LocalConstants n)
    (hbound : ∀ j v i,
      realPlaceNorm v (L v i (x j)) ≤
        placeScale v (lambda j) * exponentRadius (Q : ℝ) c v i) :
    realFormDetProduct L ≤
      (Nat.factorial n : ℝ) ^ 3 * (∏ j, lambda j) *
        exponentRadiiProduct (Q : ℝ) c := by
  have hrows : LinearIndependent ℚ
      (Erdos407.RankDrop.rationalRowMatrix x).row := by
    change LinearIndependent ℚ x
    exact hx
  have hunit : IsUnit (Erdos407.RankDrop.rationalRowMatrix x) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  have hdet0 : (Erdos407.RankDrop.rationalRowMatrix x).det ≠ 0 :=
    ((Erdos407.RankDrop.rationalRowMatrix x).isUnit_iff_isUnit_det.mp hunit).ne_zero
  have hdetS : Erdos407.RankDrop.SIntegerSix.IsSInteger
      (Erdos407.RankDrop.rationalRowMatrix x).det := by
    apply Erdos407.RankDrop.SIntegerSix.det
    intro i j
    exact Erdos407.RankDrop.SIntegerSix.of_inZOneSix_coordinate (hxS i) j
  have hnorm : (1 : ℝ) ≤ PadicProduct.normProduct23
      (Erdos407.RankDrop.rationalRowMatrix x).det := by
    exact_mod_cast Erdos407.RankDrop.SIntegerSix.one_le_normProduct23 hdetS hdet0
  have hleft : realFormDetProduct L ≤
      PadicProduct.normProduct23
          (Erdos407.RankDrop.rationalRowMatrix x).det *
        realFormDetProduct L := by
    simpa [mul_comm] using
      (le_mul_of_one_le_right (realFormDetProduct_nonneg L) hnorm)
  rw [← Erdos407.RankDrop.prod_realPlaceNorm_det_rationalLocalEvaluationRowMatrix]
    at hleft
  exact hleft.trans
    (prod_realPlaceNorm_det_le_with_row_scales L x lambda hlambda c hbound)

/-- The determinant estimate in the customary volume-reciprocal form.  The
constant depends only on the fixed local forms and the dimension. -/
theorem normalized_product_lower_of_local_bounds {n : ℕ} [NeZero n]
    (L : LocalForms n) (x : Fin n → RatVector n) (lambda : Fin n → ℝ)
    (hx : LinearIndependent ℚ x)
    (hxS : ∀ j, AdelicMinkowski.InZOneSix (x j))
    (hlambda : ∀ j, 0 ≤ lambda j) {Q : ℕ} (hQ : 1 ≤ Q)
    (c : LocalConstants n)
    (hbound : ∀ j v i,
      realPlaceNorm v (L v i (x j)) ≤
        placeScale v (lambda j) * exponentRadius (Q : ℝ) c v i) :
    (realFormDetProduct L / (Nat.factorial n : ℝ) ^ 3) *
        (Q : ℝ) ^ (-(∑ v, ∑ i, c v i)) ≤ ∏ j, lambda j := by
  have hQreal : (0 : ℝ) < Q := by
    exact_mod_cast Nat.zero_lt_of_lt hQ
  have hcore :=
    product_lower_of_local_bounds L x lambda hx hxS hlambda hQ c hbound
  rw [exponentRadiiProduct_eq_rpow_sum hQreal] at hcore
  let A : ℝ := (Nat.factorial n : ℝ) ^ 3
  let R : ℝ := (Q : ℝ) ^ (∑ v, ∑ i, c v i)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hR : 0 < R := by
    exact Real.rpow_pos_of_pos hQreal _
  have hdiv : realFormDetProduct L / (A * R) ≤ ∏ j, lambda j := by
    apply (div_le_iff₀ (mul_pos hA hR)).2
    change realFormDetProduct L ≤ (∏ j, lambda j) * (A * R)
    calc
      realFormDetProduct L ≤
          (Nat.factorial n : ℝ) ^ 3 * (∏ j, lambda j) *
            (Q : ℝ) ^ (∑ v, ∑ i, c v i) := hcore
      _ = (∏ j, lambda j) * (A * R) := by
        simp only [A, R]
        ring
  calc
    (realFormDetProduct L / (Nat.factorial n : ℝ) ^ 3) *
        (Q : ℝ) ^ (-(∑ v, ∑ i, c v i)) =
        realFormDetProduct L / (A * R) := by
      rw [Real.rpow_neg hQreal.le]
      simp only [A, R, div_eq_mul_inv, mul_inv]
      ring
    _ ≤ ∏ j, lambda j := hdiv

/-- An ordered nonnegative family is bounded above by the constant family at
its final member. -/
def lastIndex (n : ℕ) [NeZero n] : Fin n :=
  ⟨n - 1, Nat.sub_lt (NeZero.pos n) zero_lt_one⟩

theorem le_lastIndex {n : ℕ} [NeZero n] (j : Fin n) :
    j ≤ lastIndex n := by
  apply Fin.le_iff_val_le_val.mpr
  change j.val ≤ n - 1
  have hj := j.isLt
  have hn := NeZero.pos n
  omega

theorem prod_le_last_pow {n : ℕ} [NeZero n] {lambda : Fin n → ℝ}
    (hlambda : ∀ j, 0 ≤ lambda j) (hmono : Monotone lambda) :
    (∏ j, lambda j) ≤ lambda (lastIndex n) ^ n := by
  calc
    (∏ j, lambda j) ≤ ∏ _j : Fin n, lambda (lastIndex n) := by
      apply Finset.prod_le_prod
      · intro j _
        exact hlambda j
      · intro j _
        exact hmono (le_lastIndex j)
    _ = lambda (lastIndex n) ^ n := by simp

/-- Largest-minimum form of the determinant estimate. -/
theorem product_lower_le_last_pow_of_local_bounds {n : ℕ} [NeZero n]
    (L : LocalForms n) (x : Fin n → RatVector n) (lambda : Fin n → ℝ)
    (hx : LinearIndependent ℚ x)
    (hxS : ∀ j, AdelicMinkowski.InZOneSix (x j))
    (hlambda : ∀ j, 0 ≤ lambda j) (hmono : Monotone lambda)
    {Q : ℕ} (hQ : 1 ≤ Q) (c : LocalConstants n)
    (hbound : ∀ j v i,
      realPlaceNorm v (L v i (x j)) ≤
        placeScale v (lambda j) * exponentRadius (Q : ℝ) c v i) :
    realFormDetProduct L ≤
      (Nat.factorial n : ℝ) ^ 3 *
        lambda (lastIndex n) ^ n *
        exponentRadiiProduct (Q : ℝ) c := by
  calc
    realFormDetProduct L ≤
        (Nat.factorial n : ℝ) ^ 3 * (∏ j, lambda j) *
          exponentRadiiProduct (Q : ℝ) c :=
      product_lower_of_local_bounds L x lambda hx hxS hlambda hQ c hbound
    _ ≤ (Nat.factorial n : ℝ) ^ 3 *
        lambda (lastIndex n) ^ n *
          exponentRadiiProduct (Q : ℝ) c := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (prod_le_last_pow hlambda hmono) (by positivity))
        (by
          apply Finset.prod_nonneg
          intro v _
          apply Finset.prod_nonneg
          intro i _
          exact Real.rpow_nonneg (Nat.cast_nonneg Q) (c v i))

/-- A negative total local exponent forces a power lower bound for the last
member of any ordered admissible basis. -/
theorem normalized_lower_le_last_pow_of_sum_le {n : ℕ} [NeZero n]
    (L : LocalForms n) (x : Fin n → RatVector n) (lambda : Fin n → ℝ)
    (hx : LinearIndependent ℚ x)
    (hxS : ∀ j, AdelicMinkowski.InZOneSix (x j))
    (hlambda : ∀ j, 0 ≤ lambda j) (hmono : Monotone lambda)
    {Q : ℕ} (hQ : 1 ≤ Q) (c : LocalConstants n) {delta : ℝ}
    (hc : (∑ v, ∑ i, c v i) ≤ -delta)
    (hbound : ∀ j v i,
      realPlaceNorm v (L v i (x j)) ≤
        placeScale v (lambda j) * exponentRadius (Q : ℝ) c v i) :
    (realFormDetProduct L / (Nat.factorial n : ℝ) ^ 3) *
        (Q : ℝ) ^ delta ≤ lambda (lastIndex n) ^ n := by
  calc
    (realFormDetProduct L / (Nat.factorial n : ℝ) ^ 3) *
        (Q : ℝ) ^ delta ≤
        (realFormDetProduct L / (Nat.factorial n : ℝ) ^ 3) *
          (Q : ℝ) ^ (-(∑ v, ∑ i, c v i)) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast hQ) (by linarith)
      · exact div_nonneg (realFormDetProduct_nonneg L) (by positivity)
    _ ≤ ∏ j, lambda j :=
      normalized_product_lower_of_local_bounds
        L x lambda hx hxS hlambda hQ c hbound
    _ ≤ lambda (lastIndex n) ^ n := prod_le_last_pow hlambda hmono

/-- Once the fixed determinant constant is absorbed, the last successive
minimum dominates `Q^(delta/(2n))`.  The statement is uniform over every
ordered admissible basis at the given height. -/
theorem eventually_half_power_le_last_of_sum_le {n : ℕ} [NeZero n]
    (L : LocalForms n) (hL : IsNonsingularFamily L)
    (c : LocalConstants n) {delta : ℝ} (hdelta : 0 < delta)
    (hc : (∑ v, ∑ i, c v i) ≤ -delta) :
    ∀ᶠ Q : ℕ in Filter.atTop,
      ∀ (x : Fin n → RatVector n) (lambda : Fin n → ℝ),
        LinearIndependent ℚ x →
        (∀ j, AdelicMinkowski.InZOneSix (x j)) →
        (∀ j, 0 ≤ lambda j) → Monotone lambda →
        (∀ j v i,
          realPlaceNorm v (L v i (x j)) ≤
            placeScale v (lambda j) * exponentRadius (Q : ℝ) c v i) →
        (Q : ℝ) ^ (delta / (2 * n)) ≤ lambda (lastIndex n) := by
  let C : ℝ := realFormDetProduct L / (Nat.factorial n : ℝ) ^ 3
  have hC : 0 < C := by
    exact div_pos (realFormDetProduct_pos hL) (by positivity)
  have hhalf : 0 < delta / 2 := by linarith
  have htendsto : Filter.Tendsto
      (fun Q : ℕ => C * (Q : ℝ) ^ (delta / 2))
      Filter.atTop Filter.atTop :=
    ((tendsto_rpow_atTop hhalf).comp tendsto_natCast_atTop_atTop).const_mul_atTop hC
  have habsorb : ∀ᶠ Q : ℕ in Filter.atTop,
      1 ≤ C * (Q : ℝ) ^ (delta / 2) :=
    htendsto.eventually (Filter.eventually_ge_atTop 1)
  filter_upwards [habsorb, Filter.eventually_ge_atTop 1] with Q habs hQ
  intro x lambda hx hxS hlambda hmono hbound
  have hQreal : (0 : ℝ) < Q := by
    exact_mod_cast Nat.zero_lt_of_lt hQ
  have hgrowth : C * (Q : ℝ) ^ delta ≤ lambda (lastIndex n) ^ n := by
    simpa only [C] using normalized_lower_le_last_pow_of_sum_le
      L x lambda hx hxS hlambda hmono hQ c hc hbound
  have ht_nonneg : 0 ≤ (Q : ℝ) ^ (delta / 2) :=
    Real.rpow_nonneg (Nat.cast_nonneg Q) _
  have hsq : (Q : ℝ) ^ delta =
      (Q : ℝ) ^ (delta / 2) * (Q : ℝ) ^ (delta / 2) := by
    rw [← Real.rpow_add hQreal]
    congr 1
    ring
  have hhalfGrowth : (Q : ℝ) ^ (delta / 2) ≤
      lambda (lastIndex n) ^ n := by
    calc
      (Q : ℝ) ^ (delta / 2) ≤
          (C * (Q : ℝ) ^ (delta / 2)) *
            (Q : ℝ) ^ (delta / 2) := by
        simpa using mul_le_mul_of_nonneg_right habs ht_nonneg
      _ = C * (Q : ℝ) ^ delta := by rw [hsq]; ring
      _ ≤ lambda (lastIndex n) ^ n := hgrowth
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hexp : delta / (2 * (n : ℝ)) * (n : ℝ) = delta / 2 := by
    field_simp
  apply (pow_le_pow_iff_left₀
    (Real.rpow_nonneg (Nat.cast_nonneg Q) _)
    (hlambda (lastIndex n)) (NeZero.ne n)).mp
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg Q)
    (delta / (2 * (n : ℝ))) n, hexp]
  exact hhalfGrowth

/-- Cutoff form of `eventually_half_power_le_last_of_sum_le`. -/
theorem exists_half_power_last_cutoff {n : ℕ} [NeZero n]
    (L : LocalForms n) (hL : IsNonsingularFamily L)
    (c : LocalConstants n) {delta : ℝ} (hdelta : 0 < delta)
    (hc : (∑ v, ∑ i, c v i) ≤ -delta) :
    ∃ Q0 : ℕ, ∀ Q, Q0 ≤ Q →
      ∀ (x : Fin n → RatVector n) (lambda : Fin n → ℝ),
        LinearIndependent ℚ x →
        (∀ j, AdelicMinkowski.InZOneSix (x j)) →
        (∀ j, 0 ≤ lambda j) → Monotone lambda →
        (∀ j v i,
          realPlaceNorm v (L v i (x j)) ≤
            placeScale v (lambda j) * exponentRadius (Q : ℝ) c v i) →
        (Q : ℝ) ^ (delta / (2 * n)) ≤ lambda (lastIndex n) := by
  simpa only [Filter.eventually_atTop] using
    eventually_half_power_le_last_of_sum_le L hL c hdelta hc

end AdelicMinima

end Erdos407.PadicSubspace
