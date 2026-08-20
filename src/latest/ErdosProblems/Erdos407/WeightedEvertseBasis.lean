/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.EvertseBasis
import ErdosProblems.Erdos407.HeightBoxes

/-!
# Row-weighted Evertse basis lemma

This file normalizes a positive radius attached to every local row by a
nonzero rational scalar.  At the real place density of the rationals gives a
factor two approximation.  At the finite places successive integral powers
of `2` and `3` give factors two and three.  Applying the unweighted Evertse
basis lemma to the normalized rows and then undoing the row scalings gives
the weighted pairwise-minimum estimates while retaining the actual unit
lower-triangular change-of-basis matrix.
-/

namespace Erdos407.PadicSubspace

open scoped BigOperators Matrix

namespace WeightedEvertseBasis

open Erdos407 HeightBoxes

theorem realPlaceNorm_two_two_neg_zpow (z : ℤ) :
    realPlaceNorm Place23.two ((2 : ℚ) ^ (-z)) = (2 : ℝ) ^ z := by
  have hp : padicNorm 2 (2 : ℚ) = (2 : ℚ)⁻¹ :=
    padicNorm.padicNorm_p_of_prime
  unfold realPlaceNorm
  rw [placeNorm_two, PadicProduct.padicNorm_zpow, hp]
  rw [Rat.cast_zpow]
  norm_num only [Rat.cast_inv, Rat.cast_ofNat]
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
    inv_zpow, zpow_neg, inv_inv]

theorem realPlaceNorm_three_three_neg_zpow (z : ℤ) :
    realPlaceNorm Place23.three ((3 : ℚ) ^ (-z)) = (3 : ℝ) ^ z := by
  have hp : padicNorm 3 (3 : ℚ) = (3 : ℚ)⁻¹ :=
    padicNorm.padicNorm_p_of_prime
  unfold realPlaceNorm
  rw [placeNorm_three, PadicProduct.padicNorm_zpow, hp]
  rw [Rat.cast_zpow]
  norm_num only [Rat.cast_inv, Rat.cast_ofNat]
  rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num,
    inv_zpow, zpow_neg, inv_inv]

/-- Loss incurred by discretizing an arbitrary positive local row radius by
a rational scalar at the indicated place. -/
def rowApproxFactor : Place23 → ℝ
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 3

@[simp] theorem rowApproxFactor_infinite :
    rowApproxFactor Place23.infinite = 2 := rfl

@[simp] theorem rowApproxFactor_two :
    rowApproxFactor Place23.two = 2 := rfl

@[simp] theorem rowApproxFactor_three :
    rowApproxFactor Place23.three = 3 := rfl

theorem one_le_rowApproxFactor (v : Place23) : 1 ≤ rowApproxFactor v := by
  fin_cases v <;> norm_num [rowApproxFactor, Place23.infinite, Place23.two, Place23.three]

/-- A rational local scalar whose norm approximates `rho⁻¹` from below.
The approximation loss is `2` at `∞` and `2`, and `3` at `3`.  The two
multiplicative inequalities are the form needed to normalize and later
unscale a row of linear forms without division. -/
theorem exists_rowNormalizer (v : Place23) {rho : ℝ} (hrho : 0 < rho) :
    ∃ s : ℚ, s ≠ 0 ∧
      realPlaceNorm v s * rho ≤ 1 ∧
      1 ≤ rowApproxFactor v * rho * realPlaceNorm v s := by
  fin_cases v
  · have hinterval : 1 / (2 * rho) < 1 / rho := by
      apply one_div_lt_one_div_of_lt hrho
      nlinarith
    obtain ⟨s, hslo, hshi⟩ := exists_rat_btwn hinterval
    have hspos : (0 : ℝ) < (s : ℝ) :=
      (one_div_pos.mpr (mul_pos (by norm_num) hrho)).trans hslo
    have hs0 : s ≠ 0 := by
      intro hs
      subst s
      norm_num at hspos
    refine ⟨s, hs0, ?_, ?_⟩
    · change realPlaceNorm Place23.infinite s * rho ≤ 1
      rw [HeightBoxes.realPlaceNorm, placeNorm_infinite,
        Rat.cast_abs, abs_of_pos hspos]
      exact (lt_div_iff₀ hrho).mp hshi |>.le
    · change 1 ≤ rowApproxFactor Place23.infinite * rho *
        realPlaceNorm Place23.infinite s
      rw [rowApproxFactor_infinite, HeightBoxes.realPlaceNorm,
        placeNorm_infinite, Rat.cast_abs, abs_of_pos hspos]
      have h := (div_lt_iff₀ (mul_pos (by norm_num) hrho)).mp hslo
      nlinarith
  · obtain ⟨z, hzlo, hzhi⟩ :=
      exists_mem_Ico_zpow (x := 1 / rho) (y := (2 : ℝ))
        (one_div_pos.mpr hrho) (by norm_num)
    let s : ℚ := (2 : ℚ) ^ (-z)
    have hs0 : s ≠ 0 := zpow_ne_zero _ (by norm_num)
    refine ⟨s, hs0, ?_, ?_⟩
    · change realPlaceNorm Place23.two ((2 : ℚ) ^ (-z)) * rho ≤ 1
      rw [realPlaceNorm_two_two_neg_zpow]
      exact (le_div_iff₀ hrho).mp hzlo
    · change 1 ≤ rowApproxFactor Place23.two * rho *
        realPlaceNorm Place23.two ((2 : ℚ) ^ (-z))
      rw [rowApproxFactor_two, realPlaceNorm_two_two_neg_zpow]
      rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)] at hzhi
      have h := (div_lt_iff₀ hrho).mp hzhi
      nlinarith
  · obtain ⟨z, hzlo, hzhi⟩ :=
      exists_mem_Ico_zpow (x := 1 / rho) (y := (3 : ℝ))
        (one_div_pos.mpr hrho) (by norm_num)
    let s : ℚ := (3 : ℚ) ^ (-z)
    have hs0 : s ≠ 0 := zpow_ne_zero _ (by norm_num)
    refine ⟨s, hs0, ?_, ?_⟩
    · change realPlaceNorm Place23.three ((3 : ℚ) ^ (-z)) * rho ≤ 1
      rw [realPlaceNorm_three_three_neg_zpow]
      exact (le_div_iff₀ hrho).mp hzlo
    · change 1 ≤ rowApproxFactor Place23.three * rho *
        realPlaceNorm Place23.three ((3 : ℚ) ^ (-z))
      rw [rowApproxFactor_three, realPlaceNorm_three_three_neg_zpow]
      rw [zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)] at hzhi
      have h := (div_lt_iff₀ hrho).mp hzhi
      nlinarith

/-- Rowwise rational normalization of a local family of forms. -/
def normalizedForms {n : ℕ} (s : Place23 → Fin n → ℚ)
    (L : Place23 → Fin n → RatLinearForm n) :
    Place23 → Fin n → RatLinearForm n :=
  fun v i ↦ s v i • L v i

@[simp] theorem normalizedForms_apply {n : ℕ}
    (s : Place23 → Fin n → ℚ) (L : Place23 → Fin n → RatLinearForm n)
    (v : Place23) (i : Fin n) (x : Fin n → ℚ) :
    normalizedForms s L v i x = s v i * L v i x := by
  simp [normalizedForms]

theorem normalizedForms_nonsingular {n : ℕ}
    (s : Place23 → Fin n → ℚ) (hs : ∀ v i, s v i ≠ 0)
    (L : Place23 → Fin n → RatLinearForm n) (hL : IsNonsingularFamily L) :
    IsNonsingularFamily (normalizedForms s L) := by
  intro v
  have h := (hL v).units_smul (fun i ↦ Units.mk0 (s v i) (hs v i))
  convert h using 1
  funext i
  ext x
  simp [normalizedForms]

/-- A unit-lower-triangular change preserves linear independence of the
ordered basis. -/
theorem transformBasis_linearIndependent {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℚ} {x : Fin n → Fin n → ℚ}
    (hA : EvertseBasis.IsUnitLowerTriangular A)
    (hx : LinearIndependent ℚ x) :
    LinearIndependent ℚ (EvertseBasis.transformBasis A x) := by
  let X : Matrix (Fin n) (Fin n) ℚ := fun i j ↦ x i j
  have hX : IsUnit X := by
    apply Matrix.linearIndependent_rows_iff_isUnit.mp
    exact hx
  have hAdet : A.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular A hA.1]
    simp [hA.2]
  have hAu : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det, hAdet]
    exact isUnit_one
  have hmul : IsUnit (A * X) := hAu.mul hX
  let Y : Matrix (Fin n) (Fin n) ℚ :=
    fun i j ↦ EvertseBasis.transformBasis A x i j
  change LinearIndependent ℚ Y.row
  rw [Matrix.linearIndependent_rows_iff_isUnit]
  have heq : Y = A * X := by
    ext i j
    simp only [Y, X, EvertseBasis.transformBasis,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  rw [heq]
  exact hmul

/-- A change with entries in `ℤ[1/6]` preserves `S`-integrality of the
ordered basis. -/
theorem transformBasis_inZOneSix {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℚ} {x : Fin n → Fin n → ℚ}
    (hA : ∀ i j,
      AdelicMinkowski.InZOneSix (fun _ : Fin 1 ↦ A i j))
    (hx : ∀ i, AdelicMinkowski.InZOneSix (x i)) :
    ∀ i, AdelicMinkowski.InZOneSix (EvertseBasis.transformBasis A x i) := by
  intro i
  let term : Fin n → (Fin n → ℚ) := fun j ↦ A i j • x j
  have hterm : ∀ j, AdelicMinkowski.InZOneSix (term j) := by
    intro j
    apply SIntegerApproximation.InZOneSixScalar.smul
    · exact hA i j
    · exact hx j
  change AdelicMinkowski.InZOneSix (∑ j, A i j • x j)
  change AdelicMinkowski.InZOneSix (∑ j, term j)
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty =>
      exact ⟨0, AdelicMinkowski.inDenominatorLattice_zero⟩
  | @insert j t hj ih =>
      rw [Finset.sum_insert hj]
      exact (hterm j).add ih

theorem realPlaceNorm_mul (v : Place23) (q r : ℚ) :
    realPlaceNorm v (q * r) = realPlaceNorm v q * realPlaceNorm v r := by
  unfold realPlaceNorm
  rw [placeNorm_mul, Rat.cast_mul]

/-- Weighted form of Evertse's basis lemma.  The returned basis is displayed
as the transform by the actual unit-lower-triangular matrix, so in particular
all of its initial spans agree with those of the input basis.  The local loss
is `2*C` at `∞`, `2` at the `2`-adic place, and `3` at the `3`-adic place;
these constants are independent of the row radii. -/
theorem exists_weightedEvertseBasis {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (hL : IsNonsingularFamily L) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (x : Fin n → Fin n → ℚ)
        (rho mu : Place23 → Fin n → ℝ),
        LinearIndependent ℚ x →
        (∀ i, AdelicMinkowski.InZOneSix (x i)) →
        (∀ v i, 0 < rho v i) →
        (∀ v i, 0 < mu v i) →
        (∀ v, Monotone (mu v)) →
        (∀ v k j, realPlaceNorm v (L v k (x j)) ≤ rho v k * mu v j) →
        ∃ A : Matrix (Fin n) (Fin n) ℚ,
          EvertseBasis.IsUnitLowerTriangular A ∧
          (∀ i j, AdelicMinkowski.InZOneSix (fun _ : Fin 1 ↦ A i j)) ∧
          LinearIndependent ℚ (EvertseBasis.transformBasis A x) ∧
          (∀ i, AdelicMinkowski.InZOneSix
            (EvertseBasis.transformBasis A x i)) ∧
          ∃ pi : Place23 → Equiv.Perm (Fin n), ∀ v i j,
            realPlaceNorm v
                (L v (pi v i) (EvertseBasis.transformBasis A x j)) ≤
              (rowApproxFactor v *
                  (if v = Place23.infinite then C else 1)) *
                rho v (pi v i) * min (mu v i) (mu v j) := by
  refine ⟨EvertseBasis.basisConstant n,
    EvertseBasis.one_le_basisConstant n, ?_⟩
  intro x rho mu hx hxS hrho hmu hmono hbound
  choose s hs0 hsUpper hsLower using fun v i ↦
    exists_rowNormalizer v (hrho v i)
  let L' := normalizedForms s L
  have hL' : IsNonsingularFamily L' :=
    normalizedForms_nonsingular s hs0 L hL
  obtain ⟨A, hAtri, hAS, pi, hpi⟩ :=
      EvertseBasis.evertseBasis_induction n L' hL' x mu hx hmu hmono (by
    intro v k j
    change realPlaceNorm v (normalizedForms s L v k (x j)) ≤ mu v j
    rw [normalizedForms_apply, realPlaceNorm_mul]
    calc
      realPlaceNorm v (s v k) * realPlaceNorm v (L v k (x j)) ≤
          realPlaceNorm v (s v k) * (rho v k * mu v j) :=
        mul_le_mul_of_nonneg_left (hbound v k j)
          (realPlaceNorm_nonneg v (s v k))
      _ = (realPlaceNorm v (s v k) * rho v k) * mu v j := by ring
      _ ≤ 1 * mu v j :=
        mul_le_mul_of_nonneg_right (hsUpper v k) (hmu v j).le
      _ = mu v j := one_mul _)
  refine ⟨A, hAtri, hAS, transformBasis_linearIndependent hAtri hx,
    transformBasis_inZOneSix hAS hxS, pi, ?_⟩
  intro v i j
  have hpi' := hpi v i j
  change realPlaceNorm v (normalizedForms s L v (pi v i)
      (EvertseBasis.transformBasis A x j)) ≤
    (if v = Place23.infinite then EvertseBasis.basisConstant n else 1) *
      min (mu v i) (mu v j) at hpi'
  rw [normalizedForms_apply, realPlaceNorm_mul] at hpi'
  have hnorm : 0 ≤ realPlaceNorm v
      (L v (pi v i) (EvertseBasis.transformBasis A x j)) :=
    realPlaceNorm_nonneg _ _
  calc
    realPlaceNorm v
          (L v (pi v i) (EvertseBasis.transformBasis A x j)) =
        1 * realPlaceNorm v
          (L v (pi v i) (EvertseBasis.transformBasis A x j)) := by ring
    _ ≤ (rowApproxFactor v * rho v (pi v i) *
          realPlaceNorm v (s v (pi v i))) *
        realPlaceNorm v
          (L v (pi v i) (EvertseBasis.transformBasis A x j)) :=
      mul_le_mul_of_nonneg_right (hsLower v (pi v i)) hnorm
    _ = rowApproxFactor v * rho v (pi v i) *
        (realPlaceNorm v (s v (pi v i)) *
          realPlaceNorm v
            (L v (pi v i) (EvertseBasis.transformBasis A x j))) := by ring
    _ ≤ rowApproxFactor v * rho v (pi v i) *
        ((if v = Place23.infinite then EvertseBasis.basisConstant n else 1) *
          min (mu v i) (mu v j)) :=
      mul_le_mul_of_nonneg_left hpi'
        (mul_nonneg (one_le_rowApproxFactor v |>.trans' zero_le_one)
          (hrho v (pi v i)).le)
    _ = (rowApproxFactor v *
          (if v = Place23.infinite then EvertseBasis.basisConstant n else 1)) *
        rho v (pi v i) * min (mu v i) (mu v j) := by ring

end WeightedEvertseBasis

end Erdos407.PadicSubspace
