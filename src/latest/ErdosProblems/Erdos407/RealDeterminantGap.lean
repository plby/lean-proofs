/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos407.DeterminantGap

/-!
# The three-place determinant gap with real radii

The logarithmic approximation boxes used in the Subspace-Theorem argument
have radii `H ^ c` in `ℝ`.  The underlying local norms are rational-valued,
but rounding each exponent to an integral power of `H` loses too much in the
product.  This file therefore records the determinant gap after coercing the
local norms to `ℝ`; it connects the fine boxes in `HeightBoxes` directly to
the integral determinant argument.
-/

namespace Erdos407.PadicSubspace

open scoped BigOperators Matrix

/-- Product of a real radius in every form coordinate at every retained
place. -/
noncomputable def realLocalRadiiProduct {n : ℕ}
    (c : Place23 → Fin n → ℝ) : ℝ :=
  ∏ v, ∏ i, c v i

/-- Product of the three local change-of-basis determinants, coerced to
`ℝ`. -/
noncomputable def realFormDetProduct {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) : ℝ :=
  formDetProduct L

theorem realFormDetProduct_nonneg {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) :
    0 ≤ realFormDetProduct L := by
  change (0 : ℝ) ≤ (formDetProduct L : ℝ)
  exact_mod_cast formDetProduct_nonneg L

theorem realFormDetProduct_pos {n : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    (hL : IsNonsingularFamily L) : 0 < realFormDetProduct L := by
  change (0 : ℝ) < (formDetProduct L : ℝ)
  exact_mod_cast formDetProduct_pos hL

/-- The Leibniz row bound with real row radii. -/
theorem real_placeNorm_det_le_rowProduct {n : ℕ} (v : Place23)
    (M : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℝ)
    (_hc : ∀ i, 0 ≤ c i)
    (hM : ∀ i j, (placeNorm v (M i j) : ℝ) ≤ c i) :
    (placeNorm v M.det : ℝ) ≤ (Nat.factorial n : ℝ) * ∏ i, c i := by
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
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), ∏ i, c i := by
      apply Finset.sum_le_sum
      intro σ _
      apply Finset.prod_le_prod
      · intro i _
        exact_mod_cast placeNorm_nonneg v (M i (σ i))
      · intro i _
        exact hM i (σ i)
    _ = (Nat.factorial n : ℝ) * ∏ i, c i := by
      simp [Fintype.card_perm]

/-- Product-form bound for evaluated determinants of integral points in one
real local box. -/
theorem real_prod_placeNorm_det_evaluationMatrix_le {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (x : Fin n → Fin n → ℤ) (c : Place23 → Fin n → ℝ)
    (hc : ∀ v i, 0 ≤ c v i)
    (hx : ∀ j v i,
      (placeNorm v (L v i (intCastVec (x j))) : ℝ) ≤ c v i) :
    (∏ v, (placeNorm v (evaluationMatrix L v x).det : ℝ)) ≤
      (Nat.factorial n : ℝ) ^ 3 * realLocalRadiiProduct c := by
  calc
    (∏ v, (placeNorm v (evaluationMatrix L v x).det : ℝ)) ≤
        ∏ v, ((Nat.factorial n : ℝ) * ∏ i, c v i) := by
      apply Finset.prod_le_prod
      · intro v _
        exact_mod_cast placeNorm_nonneg v (evaluationMatrix L v x).det
      · intro v _
        exact real_placeNorm_det_le_rowProduct v (evaluationMatrix L v x)
          (c v) (hc v) (fun i j => hx j v i)
    _ = (Nat.factorial n : ℝ) ^ 3 * realLocalRadiiProduct c := by
      simp [realLocalRadiiProduct, Finset.prod_mul_distrib]

/-- A sufficiently small real local box cannot contain a full integral
basis.  This is the exact real-radii counterpart of
`det_integralPointMatrix_eq_zero_of_local_bounds`. -/
theorem det_integralPointMatrix_eq_zero_of_real_local_bounds {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (x : Fin n → Fin n → ℤ) (c : Place23 → Fin n → ℝ)
    (hc : ∀ v i, 0 ≤ c v i)
    (hx : ∀ j v i,
      (placeNorm v (L v i (intCastVec (x j))) : ℝ) ≤ c v i)
    (hsmall : (Nat.factorial n : ℝ) ^ 3 * realLocalRadiiProduct c <
      realFormDetProduct L) :
    (integralPointMatrix x).det = 0 := by
  by_contra hdet
  have hchangeQ := prod_placeNorm_det_evaluationMatrix L x
  have hchange :
      (∏ v, (placeNorm v (evaluationMatrix L v x).det : ℝ)) =
        realFormDetProduct L *
          PadicProduct.normProduct23 ((integralPointMatrix x).det : ℚ) := by
    have hcast := congrArg ((↑) : ℚ → ℝ) hchangeQ
    simpa [realFormDetProduct] using hcast
  have hnorm : (1 : ℝ) ≤
      PadicProduct.normProduct23 ((integralPointMatrix x).det : ℚ) := by
    exact_mod_cast one_le_threePlaceProduct_int hdet
  have hleft : realFormDetProduct L ≤
      realFormDetProduct L *
        PadicProduct.normProduct23 ((integralPointMatrix x).det : ℚ) :=
    le_mul_of_one_le_right (realFormDetProduct_nonneg L) hnorm
  rw [← hchange] at hleft
  have hbound := real_prod_placeNorm_det_evaluationMatrix_le L x c hc hx
  exact (not_lt_of_ge (hleft.trans hbound)) hsmall

/-- Real local-box rank drop, stated as rational linear dependence. -/
theorem not_linearIndependent_of_real_local_bounds {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (x : Fin n → Fin n → ℤ) (c : Place23 → Fin n → ℝ)
    (hc : ∀ v i, 0 ≤ c v i)
    (hx : ∀ j v i,
      (placeNorm v (L v i (intCastVec (x j))) : ℝ) ≤ c v i)
    (hsmall : (Nat.factorial n : ℝ) ^ 3 * realLocalRadiiProduct c <
      realFormDetProduct L) :
    ¬ LinearIndependent ℚ (fun j ↦ intCastVec (x j)) := by
  intro hlin
  have hcols : LinearIndependent ℚ (pointMatrix x).col := by
    change LinearIndependent ℚ (fun j i ↦ (x j i : ℚ)) at hlin ⊢
    exact hlin
  have hunit : IsUnit (pointMatrix x) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hcols
  have hdetQ : (pointMatrix x).det ≠ 0 :=
    ((pointMatrix x).isUnit_iff_isUnit_det.mp hunit).ne_zero
  rw [det_pointMatrix,
    det_integralPointMatrix_eq_zero_of_real_local_bounds L x c hc hx hsmall,
    Int.cast_zero] at hdetQ
  exact hdetQ rfl

end Erdos407.PadicSubspace
