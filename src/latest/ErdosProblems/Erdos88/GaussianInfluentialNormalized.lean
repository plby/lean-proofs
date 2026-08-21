import ErdosProblems.Erdos88.GaussianInfluentialConvolution

/-!
# Normalized influential-coordinate Gaussian lower bound

This module packages the influential-coordinate convolution at total variance
one and makes its interval lower bound explicitly linear in the requested
window length.
-/

open MeasureTheory ProbabilityTheory Set

namespace Erdos88.GaussianQuadratic

lemma partialVariance_erase_add_coordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (i : ι) :
    partialVariance a lam (Finset.univ.erase i) +
        coordinateVariance (a i) (lam i) = totalVariance a lam := by
  unfold partialVariance totalVariance
  exact Finset.sum_erase_add Finset.univ
    (fun j ↦ coordinateVariance (a j) (lam j)) (Finset.mem_univ i)

/-- A diagonal block with zero variance is pointwise zero.  This is the
degenerate complementary-block case omitted by the one-sided fourth-moment
argument. -/
lemma diagonalPartialSum_eq_zero_of_partialVariance_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (S : Finset ι)
    (hzero : partialVariance a lam S = 0) :
    diagonalPartialSum a lam S = 0 := by
  have hcoord : ∀ j ∈ S, coordinateVariance (a j) (lam j) = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦
      coordinateVariance_nonneg (a j) (lam j)).mp
    simpa only [partialVariance] using hzero
  funext z
  unfold diagonalPartialSum
  apply Finset.sum_eq_zero
  intro j hj
  obtain ⟨ha, hlam⟩ := (coordinateVariance_eq_zero_iff (a j) (lam j)).mp
    (hcoord j hj)
  simp only [centeredCoordinatePolynomial, ha, hlam, zero_mul, zero_add]

/-- Unit-variance, scale-free form of the nonnegative influential-coordinate
branch.  The lower bound is linear in the requested interval length. -/
theorem measureReal_diagonalPartialSum_univ_Icc_ge_of_normalized_influential_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (i : ι) {rho M x eps : ℝ}
    (hsum : totalVariance a lam = 1)
    (hlam : 0 ≤ lam i) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hinfluential : rho ≤ coordinateSigma (a i) (lam i))
    (hrem : 0 < partialVariance a lam (Finset.univ.erase i))
    (hM : 0 ≤ M) (hx : 0 ≤ x) (hxM : x ≤ M)
    (heps : 0 ≤ eps) (hepsOne : eps ≤ 1) :
    ((rho * eps) /
        (2 * ((M + 2 * Real.sqrt 15) / rho) + 7) *
        gaussianPDFReal 0 1 ((M + 2 * Real.sqrt 15) / rho + 3)) *
          (1 / 75) ≤
      (Measure.pi fun _ : ι ↦ standardGaussian).real
        ((diagonalPartialSum a lam Finset.univ) ⁻¹' Set.Icc x (x + eps)) := by
  let sigma := coordinateSigma (a i) (lam i)
  let V := partialVariance a lam (Finset.univ.erase i)
  let A := (M + 2 * Real.sqrt 15) / rho
  let eps0 := min eps sigma
  have hsigmaPos : 0 < sigma := hrho.trans_le hinfluential
  have hdecomp : V + coordinateVariance (a i) (lam i) = 1 := by
    rw [partialVariance_erase_add_coordinate, hsum]
  have hVnonneg : 0 ≤ V := partialVariance_nonneg a lam _
  have hcoordNonneg : 0 ≤ coordinateVariance (a i) (lam i) :=
    coordinateVariance_nonneg _ _
  have hVle : V ≤ 1 := by linarith
  have hsqrtV : Real.sqrt V ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hVle
  have hsigmaSq : sigma ^ 2 = coordinateVariance (a i) (lam i) := by
    dsimp only [sigma, coordinateSigma]
    exact Real.sq_sqrt hcoordNonneg
  have hsigmaLe : sigma ≤ 1 := by
    apply (sq_le_sq₀ (coordinateSigma_nonneg _ _) (by norm_num)).mp
    rw [hsigmaSq]
    linarith
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have heps0 : 0 ≤ eps0 := by
    exact le_min heps (coordinateSigma_nonneg _ _)
  have heps0Sigma : eps0 ≤ sigma := min_le_right _ _
  have heps0Eps : eps0 ≤ eps := min_le_left _ _
  have hepsLower : rho * eps ≤ eps0 := by
    by_cases hle : eps ≤ sigma
    · dsimp only [eps0]
      rw [min_eq_left hle]
      exact mul_le_of_le_one_left heps hrhoOne
    · dsimp only [eps0]
      rw [min_eq_right (le_of_not_ge hle)]
      have hs : rho * 1 ≤ sigma := by simpa only [mul_one, sigma] using hinfluential
      exact (mul_le_mul_of_nonneg_left hepsOne hrho.le).trans hs
  have hxA : x + 2 * Real.sqrt 15 * Real.sqrt V ≤ A * sigma := by
    have hsqrt15 : 0 ≤ Real.sqrt 15 := Real.sqrt_nonneg _
    have hmulSqrt : 2 * Real.sqrt 15 * Real.sqrt V ≤
        2 * Real.sqrt 15 * 1 :=
      mul_le_mul_of_nonneg_left hsqrtV (mul_nonneg (by norm_num) hsqrt15)
    have hleft : x + 2 * Real.sqrt 15 * Real.sqrt V ≤ M + 2 * Real.sqrt 15 := by
      nlinarith
    have hright : M + 2 * Real.sqrt 15 ≤ A * sigma := by
      have hnum : 0 ≤ M + 2 * Real.sqrt 15 := by positivity
      have := mul_le_mul_of_nonneg_left hinfluential hnum
      dsimp only [A, sigma] at this ⊢
      field_simp [hrho.ne'] at this ⊢
      nlinarith
    exact hleft.trans hright
  have hbase := measureReal_diagonalPartialSum_univ_Icc_ge_of_influential_nonneg
    a lam i (A := A) (x := x) (eps := eps0) hlam hA hsigmaPos hrem
      heps0 heps0Sigma hx hxA
  let target0 := (diagonalPartialSum a lam Finset.univ) ⁻¹'
    Set.Icc x (x + eps0)
  let target := (diagonalPartialSum a lam Finset.univ) ⁻¹'
    Set.Icc x (x + eps)
  have htarget : target0 ⊆ target := by
    intro z hz
    change diagonalPartialSum a lam Finset.univ z ∈ Set.Icc x (x + eps0) at hz
    change diagonalPartialSum a lam Finset.univ z ∈ Set.Icc x (x + eps)
    exact ⟨hz.1, hz.2.trans (by simpa only [add_comm] using add_le_add_left heps0Eps x)⟩
  have hcoef :
      (rho * eps) / (2 * A + 7) * gaussianPDFReal 0 1 (A + 3) * (1 / 75) ≤
        (eps0 / ((2 * A + 7) * sigma) *
          gaussianPDFReal 0 1 (A + 3)) * (1 / 75) := by
    have hdenPos : 0 < 2 * A + 7 := by positivity
    have hfrac : (rho * eps) / (2 * A + 7) ≤
        eps0 / ((2 * A + 7) * sigma) := by
      apply (div_le_div_iff₀ hdenPos (mul_pos hdenPos hsigmaPos)).2
      have hnonneg : 0 ≤ rho * eps := mul_nonneg hrho.le heps
      have hmul := mul_le_mul_of_nonneg_right hsigmaLe hnonneg
      nlinarith [hepsLower]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hfrac (gaussianPDFReal_nonneg 0 1 (A + 3)))
      (by norm_num)
  calc
    ((rho * eps) / (2 * A + 7) * gaussianPDFReal 0 1 (A + 3)) *
        (1 / 75) ≤
      (eps0 / ((2 * A + 7) * sigma) * gaussianPDFReal 0 1 (A + 3)) *
        (1 / 75) := hcoef
    _ ≤ (Measure.pi fun _ : ι ↦ standardGaussian).real target0 := by
      simpa only [sigma, V, A, eps0, target0] using hbase
    _ ≤ (Measure.pi fun _ : ι ↦ standardGaussian).real target :=
      measureReal_mono htarget
    _ = _ := by rfl

/-- The normalized nonnegative-eigenvalue influential-coordinate bound,
including the degenerate case where the complementary block has variance
zero. -/
theorem measureReal_diagonalPartialSum_univ_Icc_ge_of_normalized_influential_nonneg_all
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (i : ι) {rho M x eps : ℝ}
    (hsum : totalVariance a lam = 1)
    (hlam : 0 ≤ lam i) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hinfluential : rho ≤ coordinateSigma (a i) (lam i))
    (hM : 0 ≤ M) (hx : 0 ≤ x) (hxM : x ≤ M)
    (heps : 0 ≤ eps) (hepsOne : eps ≤ 1) :
    ((rho * eps) /
        (2 * ((M + 2 * Real.sqrt 15) / rho) + 7) *
        gaussianPDFReal 0 1 ((M + 2 * Real.sqrt 15) / rho + 3)) *
          (1 / 75) ≤
      (Measure.pi fun _ : ι ↦ standardGaussian).real
        ((diagonalPartialSum a lam Finset.univ) ⁻¹' Set.Icc x (x + eps)) := by
  let V := partialVariance a lam (Finset.univ.erase i)
  have hVnonneg : 0 ≤ V := partialVariance_nonneg a lam _
  rcases hVnonneg.eq_or_lt with hVzero | hVpos
  · let P : Measure (ι → ℝ) := Measure.pi fun _ : ι ↦ standardGaussian
    let sigma := coordinateSigma (a i) (lam i)
    let A := (M + 2 * Real.sqrt 15) / rho
    let eps0 := min eps sigma
    let p := centeredCoordinatePolynomial (a i) (lam i)
    let X : (ι → ℝ) → ℝ := fun z ↦ p (z i)
    have hsigmaPos : 0 < sigma := hrho.trans_le hinfluential
    have hdecomp : V + coordinateVariance (a i) (lam i) = 1 := by
      rw [partialVariance_erase_add_coordinate, hsum]
    have hsigmaSq : sigma ^ 2 = coordinateVariance (a i) (lam i) := by
      dsimp only [sigma, coordinateSigma]
      exact Real.sq_sqrt (coordinateVariance_nonneg _ _)
    have hsigmaLe : sigma ≤ 1 := by
      apply (sq_le_sq₀ (coordinateSigma_nonneg _ _) (by norm_num)).mp
      rw [hsigmaSq]
      linarith
    have hA : 0 ≤ A := by
      dsimp only [A]
      positivity
    have heps0 : 0 ≤ eps0 := le_min heps (coordinateSigma_nonneg _ _)
    have heps0Sigma : eps0 ≤ sigma := min_le_right _ _
    have heps0Eps : eps0 ≤ eps := min_le_left _ _
    have hepsLower : rho * eps ≤ eps0 := by
      by_cases hle : eps ≤ sigma
      · dsimp only [eps0]
        rw [min_eq_left hle]
        exact mul_le_of_le_one_left heps hrhoOne
      · dsimp only [eps0]
        rw [min_eq_right (le_of_not_ge hle)]
        have hs : rho * 1 ≤ sigma := by
          simpa only [mul_one, sigma] using hinfluential
        exact (mul_le_mul_of_nonneg_left hepsOne hrho.le).trans hs
    have hremFun : diagonalPartialSum a lam (Finset.univ.erase i) = 0 :=
      diagonalPartialSum_eq_zero_of_partialVariance_eq_zero a lam _
        (by simpa only [V] using hVzero.symm)
    have hfull : diagonalPartialSum a lam Finset.univ = X := by
      funext z
      have hsumErase := Finset.sum_erase_add Finset.univ
        (fun j ↦ centeredCoordinatePolynomial (a j) (lam j) (z j))
        (Finset.mem_univ i)
      change (∑ j, centeredCoordinatePolynomial (a j) (lam j) (z j)) = X z
      rw [← hsumErase]
      change diagonalPartialSum a lam (Finset.univ.erase i) z +
        centeredCoordinatePolynomial (a i) (lam i) (z i) = X z
      rw [congrFun hremFun z]
      simp only [Pi.zero_apply, zero_add]
      rfl
    have hXmeas : Measurable X := by
      dsimp only [X, p]
      exact (continuous_centeredCoordinatePolynomial (a i) (lam i)).measurable.comp
        (measurable_pi_apply i)
    have hmapX : P.map X = standardGaussian.map p := by
      let eval : (ι → ℝ) → ℝ := fun z ↦ z i
      have hEval : P.map eval = standardGaussian := by
        dsimp only [P, eval]
        exact (measurePreserving_eval
          (μ := fun _ : ι ↦ standardGaussian) i).map_eq
      have hfun : X = p ∘ eval := rfl
      rw [hfun, ← Measure.map_map
        (continuous_centeredCoordinatePolynomial (a i) (lam i)).measurable
        (measurable_pi_apply i), hEval]
    have hbase :=
      map_centeredCoordinatePolynomial_measureReal_Icc_ge_of_quadratic_nonneg
        (a := a i) (lam := lam i) (A := A) (u := x) (eps := eps0)
        hlam hA hsigmaPos heps0 heps0Sigma hx (by
          have hnum : 0 ≤ M + 2 * Real.sqrt 15 := by positivity
          have hright : M + 2 * Real.sqrt 15 ≤ A * sigma := by
            have hmul := mul_le_mul_of_nonneg_left hinfluential hnum
            dsimp only [A, sigma] at hmul ⊢
            field_simp [hrho.ne'] at hmul ⊢
            nlinarith
          exact hxM.trans (by
            calc
              M ≤ M + 2 * Real.sqrt 15 := by
                linarith [Real.sqrt_nonneg 15]
              _ ≤ A * sigma := hright))
    let target0 := Set.Icc x (x + eps0)
    let target := Set.Icc x (x + eps)
    have htarget : target0 ⊆ target := by
      intro y hy
      exact ⟨hy.1, hy.2.trans (by linarith)⟩
    have hpull : (standardGaussian.map p).real target0 =
        P.real ((diagonalPartialSum a lam Finset.univ) ⁻¹' target0) := by
      rw [← hmapX, map_measureReal_apply hXmeas measurableSet_Icc, hfull]
    have hfrac : (rho * eps) / (2 * A + 7) ≤
        eps0 / ((2 * A + 7) * sigma) := by
      have hdenPos : 0 < 2 * A + 7 := by positivity
      apply (div_le_div_iff₀ hdenPos (mul_pos hdenPos hsigmaPos)).2
      have hnonneg : 0 ≤ rho * eps := mul_nonneg hrho.le heps
      have hmul := mul_le_mul_of_nonneg_right hsigmaLe hnonneg
      nlinarith [hepsLower]
    have hcoeff :
        (rho * eps) / (2 * A + 7) * gaussianPDFReal 0 1 (A + 3) * (1 / 75) ≤
          eps0 / ((2 * A + 7) * sigma) * gaussianPDFReal 0 1 (A + 3) := by
      have hpdf : 0 ≤ gaussianPDFReal 0 1 (A + 3) :=
        gaussianPDFReal_nonneg 0 1 _
      calc
        (rho * eps) / (2 * A + 7) * gaussianPDFReal 0 1 (A + 3) * (1 / 75) ≤
            (rho * eps) / (2 * A + 7) * gaussianPDFReal 0 1 (A + 3) := by
          have hleft : 0 ≤ (rho * eps) / (2 * A + 7) *
              gaussianPDFReal 0 1 (A + 3) := by positivity
          nlinarith
        _ ≤ eps0 / ((2 * A + 7) * sigma) *
              gaussianPDFReal 0 1 (A + 3) :=
          mul_le_mul_of_nonneg_right hfrac hpdf
    calc
      ((rho * eps) / (2 * A + 7) * gaussianPDFReal 0 1 (A + 3)) * (1 / 75) ≤
          eps0 / ((2 * A + 7) * sigma) * gaussianPDFReal 0 1 (A + 3) := hcoeff
      _ ≤ (standardGaussian.map p).real target0 := by
        simpa only [sigma, A, eps0, p, target0] using hbase
      _ = P.real ((diagonalPartialSum a lam Finset.univ) ⁻¹' target0) := hpull
      _ ≤ P.real ((diagonalPartialSum a lam Finset.univ) ⁻¹' target) :=
        measureReal_mono (Set.preimage_mono htarget)
      _ = _ := by rfl
  · exact measureReal_diagonalPartialSum_univ_Icc_ge_of_normalized_influential_nonneg
      a lam i hsum hlam hrho hrhoOne hinfluential
        (by simpa only [V] using hVpos) hM hx hxM heps hepsOne

/-- Unit-variance form of the linearly dominated influential-coordinate
branch, including a zero-variance complementary block. -/
theorem measureReal_diagonalPartialSum_univ_Icc_ge_of_normalized_influential_linear_dominates_all
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (i : ι) {rho M x eps : ℝ}
    (hsum : totalVariance a lam = 1)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hinfluential : rho ≤ coordinateSigma (a i) (lam i))
    (hdom : 8 *
        (4 * (((M + 2 * Real.sqrt 15) / rho) + 1) + 1) * |lam i| ≤ |a i|)
    (hM : 0 ≤ M) (hx : 0 ≤ x) (hxM : x ≤ M)
    (heps : 0 ≤ eps) (hepsOne : eps ≤ 1) :
    (((rho * eps) / 2) *
        gaussianPDFReal 0 1
          (4 * (((M + 2 * Real.sqrt 15) / rho) + 1) + 1)) *
          (1 / 75) ≤
      (Measure.pi fun _ : ι ↦ standardGaussian).real
        ((diagonalPartialSum a lam Finset.univ) ⁻¹' Set.Icc x (x + eps)) := by
  let P : Measure (ι → ℝ) := Measure.pi fun _ : ι ↦ standardGaussian
  let sigma := coordinateSigma (a i) (lam i)
  let V := partialVariance a lam (Finset.univ.erase i)
  let A := (M + 2 * Real.sqrt 15) / rho
  let T := 4 * (A + 1) + 1
  let eps0 := min eps sigma
  have hsigmaPos : 0 < sigma := hrho.trans_le hinfluential
  have hdecomp : V + coordinateVariance (a i) (lam i) = 1 := by
    rw [partialVariance_erase_add_coordinate, hsum]
  have hVnonneg : 0 ≤ V := partialVariance_nonneg a lam _
  have hsigmaSq : sigma ^ 2 = coordinateVariance (a i) (lam i) := by
    dsimp only [sigma, coordinateSigma]
    exact Real.sq_sqrt (coordinateVariance_nonneg _ _)
  have hsigmaLe : sigma ≤ 1 := by
    apply (sq_le_sq₀ (coordinateSigma_nonneg _ _) (by norm_num)).mp
    rw [hsigmaSq]
    linarith
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have heps0 : 0 ≤ eps0 := le_min heps (coordinateSigma_nonneg _ _)
  have heps0Sigma : eps0 ≤ sigma := min_le_right _ _
  have heps0Eps : eps0 ≤ eps := min_le_left _ _
  have hepsLower : rho * eps ≤ eps0 := by
    by_cases hle : eps ≤ sigma
    · dsimp only [eps0]
      rw [min_eq_left hle]
      exact mul_le_of_le_one_left heps hrhoOne
    · dsimp only [eps0]
      rw [min_eq_right (le_of_not_ge hle)]
      have hs : rho * 1 ≤ sigma := by
        simpa only [mul_one, sigma] using hinfluential
      exact (mul_le_mul_of_nonneg_left hepsOne hrho.le).trans hs
  have hxA : x + 2 * Real.sqrt 15 * Real.sqrt V ≤ A * sigma := by
    have hsqrtV : Real.sqrt V ≤ 1 := by
      rw [Real.sqrt_le_one]
      linarith [coordinateVariance_nonneg (a i) (lam i)]
    have hsqrt15 : 0 ≤ Real.sqrt 15 := Real.sqrt_nonneg _
    have hmulSqrt : 2 * Real.sqrt 15 * Real.sqrt V ≤
        2 * Real.sqrt 15 * 1 :=
      mul_le_mul_of_nonneg_left hsqrtV (mul_nonneg (by norm_num) hsqrt15)
    have hleft : x + 2 * Real.sqrt 15 * Real.sqrt V ≤
        M + 2 * Real.sqrt 15 := by nlinarith
    have hnum : 0 ≤ M + 2 * Real.sqrt 15 := by positivity
    have hright : M + 2 * Real.sqrt 15 ≤ A * sigma := by
      have hmul := mul_le_mul_of_nonneg_left hinfluential hnum
      dsimp only [A, sigma] at hmul ⊢
      field_simp [hrho.ne'] at hmul ⊢
      nlinarith
    exact hleft.trans hright
  let target0 := (diagonalPartialSum a lam Finset.univ) ⁻¹'
    Set.Icc x (x + eps0)
  let target := (diagonalPartialSum a lam Finset.univ) ⁻¹'
    Set.Icc x (x + eps)
  have htarget : target0 ⊆ target := by
    intro z hz
    exact ⟨hz.1, hz.2.trans (by linarith)⟩
  have hsource :
      (eps0 / (2 * sigma) * gaussianPDFReal 0 1 T) * (1 / 75) ≤
        P.real target0 := by
    rcases hVnonneg.eq_or_lt with hVzero | hVpos
    · let p := centeredCoordinatePolynomial (a i) (lam i)
      let X : (ι → ℝ) → ℝ := fun z ↦ p (z i)
      have hremFun : diagonalPartialSum a lam (Finset.univ.erase i) = 0 :=
        diagonalPartialSum_eq_zero_of_partialVariance_eq_zero a lam _
          (by simpa only [V] using hVzero.symm)
      have hfull : diagonalPartialSum a lam Finset.univ = X := by
        funext z
        have hsumErase := Finset.sum_erase_add Finset.univ
          (fun j ↦ centeredCoordinatePolynomial (a j) (lam j) (z j))
          (Finset.mem_univ i)
        change (∑ j, centeredCoordinatePolynomial (a j) (lam j) (z j)) = X z
        rw [← hsumErase]
        change diagonalPartialSum a lam (Finset.univ.erase i) z +
          centeredCoordinatePolynomial (a i) (lam i) (z i) = X z
        rw [congrFun hremFun z]
        simp only [Pi.zero_apply, zero_add]
        rfl
      have hXmeas : Measurable X := by
        dsimp only [X, p]
        exact (continuous_centeredCoordinatePolynomial (a i) (lam i)).measurable.comp
          (measurable_pi_apply i)
      have hmapX : P.map X = standardGaussian.map p := by
        let eval : (ι → ℝ) → ℝ := fun z ↦ z i
        have hEval : P.map eval = standardGaussian := by
          dsimp only [P, eval]
          exact (measurePreserving_eval
            (μ := fun _ : ι ↦ standardGaussian) i).map_eq
        have hfun : X = p ∘ eval := rfl
        rw [hfun, ← Measure.map_map
          (continuous_centeredCoordinatePolynomial (a i) (lam i)).measurable
          (measurable_pi_apply i), hEval]
      have hbase :=
        map_centeredCoordinatePolynomial_measureReal_Icc_ge_of_linear_dominates
          (a := a i) (lam := lam i) (A := A) (u := x) (eps := eps0)
          hA hsigmaPos (by simpa only [A] using hdom) heps0 heps0Sigma hx
          (by
            calc
              x ≤ M := hxM
              _ ≤ M + 2 * Real.sqrt 15 := by
                linarith [Real.sqrt_nonneg 15]
              _ ≤ A * sigma := by
                have hnum : 0 ≤ M + 2 * Real.sqrt 15 := by positivity
                have hmul := mul_le_mul_of_nonneg_left hinfluential hnum
                dsimp only [A, sigma] at hmul ⊢
                field_simp [hrho.ne'] at hmul ⊢
                nlinarith)
      have hpull : (standardGaussian.map p).real (Set.Icc x (x + eps0)) =
          P.real target0 := by
        dsimp only [target0]
        rw [← hmapX, map_measureReal_apply hXmeas measurableSet_Icc, hfull]
      have hcoefNonneg : 0 ≤ eps0 / (2 * sigma) *
          gaussianPDFReal 0 1 T :=
        mul_nonneg
          (div_nonneg heps0 (mul_nonneg (by norm_num) hsigmaPos.le))
          (gaussianPDFReal_nonneg 0 1 T)
      calc
        (eps0 / (2 * sigma) * gaussianPDFReal 0 1 T) * (1 / 75) ≤
            eps0 / (2 * sigma) * gaussianPDFReal 0 1 T := by nlinarith
        _ ≤ (standardGaussian.map p).real (Set.Icc x (x + eps0)) := by
          simpa only [sigma, A, T, eps0, p] using hbase
        _ = P.real target0 := hpull
    · have hbase :=
        measureReal_diagonalPartialSum_univ_Icc_ge_of_influential_linear_dominates
          a lam i (A := A) (x := x) (eps := eps0) hA hsigmaPos
          (by simpa only [A] using hdom) (by simpa only [V] using hVpos)
          heps0 heps0Sigma hx hxA
      simpa only [P, sigma, V, A, T, eps0, target0] using hbase
  have hfrac : (rho * eps) / 2 ≤ eps0 / (2 * sigma) := by
    apply (div_le_div_iff₀ (by norm_num) (mul_pos (by norm_num) hsigmaPos)).2
    have hnonneg : 0 ≤ rho * eps := mul_nonneg hrho.le heps
    have hmul := mul_le_mul_of_nonneg_right hsigmaLe hnonneg
    nlinarith [hepsLower]
  have hcoef :
      ((rho * eps) / 2 * gaussianPDFReal 0 1 T) * (1 / 75) ≤
        (eps0 / (2 * sigma) * gaussianPDFReal 0 1 T) * (1 / 75) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hfrac (gaussianPDFReal_nonneg 0 1 T))
      (by norm_num)
  calc
    ((rho * eps) / 2 * gaussianPDFReal 0 1 T) * (1 / 75) ≤
        (eps0 / (2 * sigma) * gaussianPDFReal 0 1 T) * (1 / 75) := hcoef
    _ ≤ P.real target0 := hsource
    _ ≤ P.real target := measureReal_mono htarget
    _ = _ := by rfl

end Erdos88.GaussianQuadratic
