import ErdosProblems.Erdos88.GaussianInfluentialNormalized

/-!
# Selecting an influential Gaussian coordinate

This module completes the influential-coordinate branch of the lower half of
KSSS Theorem 5.2(2).  Under the source's ordered-eigenvalue hypothesis, either
the maximal nonnegative eigenvalue coordinate is influential, or any
influential coordinate has a linearly dominated quadratic part.
-/

open MeasureTheory ProbabilityTheory Set

namespace Erdos88.GaussianQuadratic

/-- Symmetric branch radius used by the linearly dominated alternative. -/
noncomputable def influentialLinearT (M rho : ℝ) : ℝ :=
  4 * (((M + 2 * Real.sqrt 15) / rho) + 1) + 1

/-- Smaller influence threshold reserved for the maximal nonnegative
eigenvalue coordinate. -/
noncomputable def influentialPositiveThreshold (M rho : ℝ) : ℝ :=
  rho / (16 * influentialLinearT M rho)

noncomputable def influentialPositiveConstant (M rho : ℝ) : ℝ :=
  let rho0 := influentialPositiveThreshold M rho
  let A0 := (M + 2 * Real.sqrt 15) / rho0
  rho0 / (2 * A0 + 7) * gaussianPDFReal 0 1 (A0 + 3) * (1 / 75)

noncomputable def influentialLinearConstant (M rho : ℝ) : ℝ :=
  rho / 2 * gaussianPDFReal 0 1 (influentialLinearT M rho) * (1 / 75)

/-- A coefficient-uniform lower constant for the influential-coordinate
case. -/
noncomputable def influentialLowerConstant (M rho : ℝ) : ℝ :=
  min (influentialPositiveConstant M rho) (influentialLinearConstant M rho)

lemma influentialLowerConstant_pos {M rho : ℝ} (hM : 0 ≤ M) (hrho : 0 < rho) :
    0 < influentialLowerConstant M rho := by
  let T := influentialLinearT M rho
  let rho0 := influentialPositiveThreshold M rho
  let A0 := (M + 2 * Real.sqrt 15) / rho0
  have hT : 0 < T := by
    dsimp only [T, influentialLinearT]
    have : 0 ≤ (M + 2 * Real.sqrt 15) / rho := by positivity
    linarith
  have hrho0 : 0 < rho0 := by
    dsimp only [rho0, influentialPositiveThreshold]
    positivity
  have hA0 : 0 ≤ A0 := by dsimp only [A0]; positivity
  unfold influentialLowerConstant influentialPositiveConstant
    influentialLinearConstant
  dsimp only
  exact lt_min
    (mul_pos
      (mul_pos (div_pos hrho0 (by positivity))
        (gaussianPDFReal_pos 0 1 (A0 + 3) one_ne_zero))
      (by norm_num))
    (mul_pos
      (mul_pos (div_pos hrho (by norm_num))
        (gaussianPDFReal_pos 0 1 T one_ne_zero))
      (by norm_num))

/-- The influential-coordinate alternative in the lower half of KSSS
Theorem 5.2(2), normalized to total variance one.  The constant is uniform in
the center and interval length. -/
theorem uniform_diagonal_lower_of_ordered_eigenvalues_influential
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (k : ι) {rho M : ℝ}
    (hsum : totalVariance a lam = 1)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hM : 0 ≤ M)
    (hlamk : 0 ≤ lam k)
    (hmax : ∀ i, |lam i| ≤ lam k)
    (hinfluential : ∃ i, rho ≤ coordinateSigma (a i) (lam i)) :
    ∀ {x eps : ℝ},
      0 ≤ x → x ≤ M → 0 ≤ eps → eps ≤ 1 →
      influentialLowerConstant M rho * eps ≤
        (Measure.pi fun _ : ι ↦ standardGaussian).real
          ((diagonalPartialSum a lam Finset.univ) ⁻¹' Set.Icc x (x + eps)) := by
  let T := 4 * (((M + 2 * Real.sqrt 15) / rho) + 1) + 1
  let rho0 := rho / (16 * T)
  let A0 := (M + 2 * Real.sqrt 15) / rho0
  let c1 := rho0 / (2 * A0 + 7) * gaussianPDFReal 0 1 (A0 + 3) * (1 / 75)
  let c2 := rho / 2 * gaussianPDFReal 0 1 T * (1 / 75)
  have hT : 1 ≤ T := by
    dsimp only [T]
    have : 0 ≤ (M + 2 * Real.sqrt 15) / rho := by positivity
    linarith
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hrho0 : 0 < rho0 := by
    dsimp only [rho0]
    positivity
  have hrho0Rho : rho0 ≤ rho := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hTpos)).2
    have hden : 1 ≤ 16 * T := by nlinarith
    have := mul_le_mul_of_nonneg_left hden hrho.le
    nlinarith
  have hrho0One : rho0 ≤ 1 := hrho0Rho.trans hrhoOne
  have hA0 : 0 ≤ A0 := by
    dsimp only [A0]
    positivity
  have hc1 : 0 < c1 := by
    dsimp only [c1]
    exact mul_pos
      (mul_pos
        (div_pos hrho0 (by positivity))
        (gaussianPDFReal_pos 0 1 (A0 + 3) one_ne_zero))
      (by norm_num)
  have hc2 : 0 < c2 := by
    dsimp only [c2]
    exact mul_pos
      (mul_pos (div_pos hrho (by norm_num))
        (gaussianPDFReal_pos 0 1 T one_ne_zero))
      (by norm_num)
  change ∀ {x eps : ℝ},
    0 ≤ x → x ≤ M → 0 ≤ eps → eps ≤ 1 →
      min c1 c2 * eps ≤
        (Measure.pi fun _ : ι ↦ standardGaussian).real
          ((diagonalPartialSum a lam Finset.univ) ⁻¹' Set.Icc x (x + eps))
  intro x eps hx hxM heps hepsOne
  by_cases hk : rho0 ≤ coordinateSigma (a k) (lam k)
  · have hbase :=
      measureReal_diagonalPartialSum_univ_Icc_ge_of_normalized_influential_nonneg_all
        a lam k hsum hlamk hrho0 hrho0One hk hM hx hxM heps hepsOne
    have hc1bound : c1 * eps ≤
        (Measure.pi fun _ : ι ↦ standardGaussian).real
          ((diagonalPartialSum a lam Finset.univ) ⁻¹' Set.Icc x (x + eps)) := by
      calc
        c1 * eps =
            ((rho0 * eps) / (2 * A0 + 7) *
              gaussianPDFReal 0 1 (A0 + 3)) * (1 / 75) := by
          dsimp only [c1]
          ring
        _ ≤ _ := by
          simpa only [rho0, A0] using hbase
    exact (mul_le_mul_of_nonneg_right (min_le_left c1 c2) heps).trans hc1bound
  · obtain ⟨i, hi⟩ := hinfluential
    have hkSmall : coordinateSigma (a k) (lam k) < rho0 := lt_of_not_ge hk
    have hlamkSigma : lam k ≤ coordinateSigma (a k) (lam k) := by
      have hquad := sqrt_two_mul_abs_quadratic_le_coordinateSigma (a k) (lam k)
      have hsqrt : 1 ≤ Real.sqrt 2 := (Real.one_le_sqrt).2 (by norm_num)
      have habs : |lam k| = lam k := abs_of_nonneg hlamk
      rw [habs] at hquad
      have hmul := mul_le_mul_of_nonneg_right hsqrt hlamk
      linarith
    have hlamSmall : |lam i| < rho0 :=
      (hmax i).trans_lt (hlamkSigma.trans_lt hkSmall)
    have hscale : 8 * T * |lam i| ≤ rho / 2 := by
      have h8T : 0 < (8 : ℝ) * T := mul_pos (by norm_num) hTpos
      have hmul := mul_lt_mul_of_pos_left hlamSmall h8T
      have heq : 8 * T * rho0 = rho / 2 := by
        dsimp only [rho0]
        field_simp [hTpos.ne']
        ring
      exact le_of_lt (hmul.trans_eq heq)
    have hlamQuarter : |lam i| ≤ rho / 4 := by
      have hrho0Quarter : rho0 ≤ rho / 4 := by
        dsimp only [rho0]
        apply (div_le_iff₀ (mul_pos (by norm_num) hTpos)).2
        have hden : 4 ≤ 16 * T := by nlinarith
        have hmul := mul_le_mul_of_nonneg_left hden hrho.le
        calc
          rho = (rho * 4) / 4 := by ring
          _ ≤ (rho * (16 * T)) / 4 :=
            div_le_div_of_nonneg_right hmul (by norm_num)
          _ = (rho / 4) * (16 * T) := by ring
      exact hlamSmall.le.trans hrho0Quarter
    have hrhoSq : rho ^ 2 ≤ coordinateSigma (a i) (lam i) ^ 2 :=
      (sq_le_sq₀ hrho.le (coordinateSigma_nonneg _ _)).mpr hi
    have hlamSq : lam i ^ 2 ≤ (rho / 4) ^ 2 := by
      have := (sq_le_sq₀ (abs_nonneg (lam i)) (by positivity)).mpr hlamQuarter
      simpa only [sq_abs] using this
    have haHalf : rho / 2 ≤ |a i| := by
      apply (sq_le_sq₀ (by positivity) (abs_nonneg (a i))).mp
      rw [sq_abs]
      rw [coordinateSigma_sq, coordinateVariance] at hrhoSq
      nlinarith
    have hdom : 8 * T * |lam i| ≤ |a i| := hscale.trans haHalf
    have hbase :=
      measureReal_diagonalPartialSum_univ_Icc_ge_of_normalized_influential_linear_dominates_all
        a lam i hsum hrho hrhoOne hi
        (by simpa only [T] using hdom) hM hx hxM heps hepsOne
    have hc2bound : c2 * eps ≤
        (Measure.pi fun _ : ι ↦ standardGaussian).real
          ((diagonalPartialSum a lam Finset.univ) ⁻¹' Set.Icc x (x + eps)) := by
      calc
        c2 * eps =
            (((rho * eps) / 2) * gaussianPDFReal 0 1 T) * (1 / 75) := by
          dsimp only [c2]
          ring
        _ ≤ _ := by simpa only [T] using hbase
    exact (mul_le_mul_of_nonneg_right (min_le_right c1 c2) heps).trans hc2bound

/-- Existential packaging of the coefficient-uniform influential lower
constant. -/
theorem exists_uniform_diagonal_lower_of_ordered_eigenvalues_influential
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (k : ι) {rho M : ℝ}
    (hsum : totalVariance a lam = 1)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hM : 0 ≤ M)
    (hlamk : 0 ≤ lam k)
    (hmax : ∀ i, |lam i| ≤ lam k)
    (hinfluential : ∃ i, rho ≤ coordinateSigma (a i) (lam i)) :
    ∃ c : ℝ, 0 < c ∧ ∀ {x eps : ℝ},
      0 ≤ x → x ≤ M → 0 ≤ eps → eps ≤ 1 →
      c * eps ≤
        (Measure.pi fun _ : ι ↦ standardGaussian).real
          ((diagonalPartialSum a lam Finset.univ) ⁻¹' Set.Icc x (x + eps)) := by
  exact ⟨influentialLowerConstant M rho,
    influentialLowerConstant_pos hM hrho,
    uniform_diagonal_lower_of_ordered_eigenvalues_influential
      a lam k hsum hrho hrhoOne hM hlamk hmax hinfluential⟩

end Erdos88.GaussianQuadratic
