import ErdosProblems.Erdos88.GaussianLower

/-!
# Lower intervals for general Gaussian quadratic forms

This module transports the ordered diagonal lower theorem through orthogonal
diagonalization.  The sign in KSSS Claim 12.1 is selected by taking an
eigenvalue of maximal absolute value and reflecting the whole centered
quadratic form when that eigenvalue is negative.
-/

open MeasureTheory ProbabilityTheory Set

namespace Erdos88.GaussianQuadratic

open BooleanSlices

/-- Multiplying every linear and quadratic diagonal coefficient by the same
scalar is the pushforward of the centered diagonal law by that scalar. -/
theorem diagonalCenteredLaw_smul {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (s : ℝ) :
    diagonalCenteredLaw (fun i ↦ s * a i) (fun i ↦ s * lam i) =
      (diagonalCenteredLaw a lam).map (fun x ↦ s * x) := by
  classical
  rw [diagonalCenteredLaw_eq_map_diagonalCenteredSum,
    diagonalCenteredLaw_eq_map_diagonalCenteredSum]
  rw [Measure.map_map (by fun_prop)
    (continuous_diagonalCenteredSum a lam).measurable]
  congr 1
  funext z
  dsimp only [Function.comp_apply]
  unfold diagonalCenteredSum centeredCoordinatePolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma smallBall_map_mul_sign
    (mu : Measure ℝ) {s eps x : ℝ} (hs : s = 1 ∨ s = -1) :
    Erdos88.Esseen.smallBall (mu.map (fun y ↦ s * y)) eps x =
      Erdos88.Esseen.smallBall mu eps (s * x) := by
  rcases hs with rfl | rfl
  · simp only [one_mul]
    change Erdos88.Esseen.smallBall (mu.map id) eps x = _
    rw [Measure.map_id]
  · unfold Erdos88.Esseen.smallBall
    rw [map_measureReal_apply (by fun_prop) measurableSet_Icc]
    congr 1
    ext y
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> intro hy <;> constructor <;> linarith [hy.1, hy.2]

/-- A unit-variance diagonal Gaussian quadratic always has a choice of sign
for which the lower interval estimate holds on the positive half-line.  The
sign depends only on the quadratic coefficients. -/
theorem exists_sign_uniform_diagonal_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a lam : ι → ℝ) {M x eps : ℝ}
    (hsum : totalVariance a lam = 1)
    (hM : 0 ≤ M) (hx : 0 ≤ x) (hxM : x ≤ M)
    (heps : 0 ≤ eps) (hepsOne : eps ≤ 1) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      orderedGaussianLowerConstant M * eps ≤
        ((diagonalCenteredLaw a lam).map (fun y ↦ s * y)).real
          (Set.Icc x (x + eps)) := by
  classical
  obtain ⟨k, _hkMem, hk⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) (fun i ↦ |lam i|)
      Finset.univ_nonempty
  let s : ℝ := if 0 ≤ lam k then 1 else -1
  have hsCases : s = 1 ∨ s = -1 := by
    dsimp only [s]
    split_ifs <;> simp
  have hsSq : s ^ 2 = 1 := by
    rcases hsCases with hs | hs <;> simp [hs]
  have hsAbs : |s| = 1 := by
    rcases hsCases with hs | hs <;> simp [hs]
  have hsk : s * lam k = |lam k| := by
    dsimp only [s]
    split_ifs with hkNonneg
    · simpa [abs_of_nonneg hkNonneg]
    · have hkNeg : lam k < 0 := lt_of_not_ge hkNonneg
      simpa [abs_of_neg hkNeg]
  have hsum' :
      totalVariance (fun i ↦ s * a i) (fun i ↦ s * lam i) = 1 := by
    calc
      totalVariance (fun i ↦ s * a i) (fun i ↦ s * lam i) =
          totalVariance a lam := by
        unfold totalVariance coordinateVariance
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_pow, mul_pow, hsSq]
        ring
      _ = 1 := hsum
  have hmax : ∀ i, |s * lam i| ≤ s * lam k := by
    intro i
    rw [abs_mul, hsAbs, one_mul, hsk]
    exact hk i (Finset.mem_univ i)
  have hlamk : 0 ≤ s * lam k := by rw [hsk]; exact abs_nonneg _
  have hbase := uniform_diagonal_lower_of_ordered_eigenvalues
    (fun i ↦ s * a i) (fun i ↦ s * lam i) k hsum' hM hlamk hmax
      hx hxM heps hepsOne
  have hscaled : orderedGaussianLowerConstant M * eps ≤
      (diagonalCenteredLaw (fun i ↦ s * a i) (fun i ↦ s * lam i)).real
        (Set.Icc x (x + eps)) := by
    rw [← map_diagonalPartialSum_univ_eq_diagonalCenteredLaw
      (fun i ↦ s * a i) (fun i ↦ s * lam i)]
    rw [map_measureReal_apply
      (continuous_diagonalPartialSum
        (fun i ↦ s * a i) (fun i ↦ s * lam i) Finset.univ).measurable
      measurableSet_Icc]
    exact hbase
  refine ⟨s, hsCases, ?_⟩
  rw [← diagonalCenteredLaw_smul a lam s]
  exact hscaled

/-- Coordinate-free normalized lower half of KSSS Theorem 5.2(2).  The
chosen reflection sign depends only on the Hermitian quadratic matrix. -/
theorem exists_sign_gaussianQuadraticCenteredLaw_normalized_lower
    {n : ℕ} [NeZero n] (f : Fin n → ℝ)
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    {sigma M x eps : ℝ} (hsigma : 0 < sigma)
    (hsigmaSq : sigma ^ 2 = 2 * frobeniusSq F + vectorSqNorm f)
    (hM : 0 ≤ M) (hx : 0 ≤ x) (hxM : x ≤ M)
    (heps : 0 ≤ eps) (hepsOne : eps ≤ 1) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      orderedGaussianLowerConstant M * eps ≤
        (((gaussianQuadraticCenteredLaw f F).map (fun y ↦ y / sigma)).map
          (fun y ↦ s * y)).real (Set.Icc x (x + eps)) := by
  let a : Fin n → ℝ := fun i ↦ eigenLinearCoefficient hF f i / sigma
  let lam : Fin n → ℝ := fun i ↦ hF.eigenvalues i / sigma
  have hsum : totalVariance a lam = 1 := by
    exact totalVariance_normalized_eigenbasis hF f hsigma hsigmaSq
  obtain ⟨s, hs, hlower⟩ := exists_sign_uniform_diagonal_lower
    a lam hsum hM hx hxM heps hepsOne
  refine ⟨s, hs, ?_⟩
  rw [gaussianQuadraticCenteredLaw_map_div_eq_diagonal f hF hsigma.ne']
  exact hlower

/-- Uniform-in-the-linear-part version of the coordinate-free Gaussian
lower theorem.  The reflection sign is selected before the linear
coefficients, normalization, center, and interval radius are introduced;
it therefore depends only on the Hermitian quadratic matrix. -/
theorem exists_sign_gaussianQuadraticCenteredLaw_normalized_lower_uniform
    {n : ℕ} [NeZero n]
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ∀ (f : Fin n → ℝ) {sigma M x eps : ℝ},
        0 < sigma →
        sigma ^ 2 = 2 * frobeniusSq F + vectorSqNorm f →
        0 ≤ M → 0 ≤ x → x ≤ M → 0 ≤ eps → eps ≤ 1 →
        orderedGaussianLowerConstant M * eps ≤
          (((gaussianQuadraticCenteredLaw f F).map
              (fun y ↦ y / sigma)).map (fun y ↦ s * y)).real
            (Set.Icc x (x + eps)) := by
  classical
  obtain ⟨k, _hkMem, hk⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin n))
      (fun i ↦ |hF.eigenvalues i|) Finset.univ_nonempty
  let s : ℝ := if 0 ≤ hF.eigenvalues k then 1 else -1
  have hsCases : s = 1 ∨ s = -1 := by
    dsimp only [s]
    split_ifs <;> simp
  have hsSq : s ^ 2 = 1 := by
    rcases hsCases with hs | hs <;> simp [hs]
  have hsAbs : |s| = 1 := by
    rcases hsCases with hs | hs <;> simp [hs]
  have hsk : s * hF.eigenvalues k = |hF.eigenvalues k| := by
    dsimp only [s]
    split_ifs with hkNonneg
    · simpa [abs_of_nonneg hkNonneg]
    · have hkNeg : hF.eigenvalues k < 0 := lt_of_not_ge hkNonneg
      simpa [abs_of_neg hkNeg]
  refine ⟨s, hsCases, ?_⟩
  intro f sigma M x eps hsigma hsigmaSq hM hx hxM heps hepsOne
  let a : Fin n → ℝ := fun i ↦ eigenLinearCoefficient hF f i / sigma
  let lam : Fin n → ℝ := fun i ↦ hF.eigenvalues i / sigma
  have hsum : totalVariance a lam = 1 := by
    simpa only [a, lam] using
      totalVariance_normalized_eigenbasis hF f hsigma hsigmaSq
  have hsum' :
      totalVariance (fun i ↦ s * a i) (fun i ↦ s * lam i) = 1 := by
    calc
      totalVariance (fun i ↦ s * a i) (fun i ↦ s * lam i) =
          totalVariance a lam := by
        unfold totalVariance coordinateVariance
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_pow, mul_pow, hsSq]
        ring
      _ = 1 := hsum
  have hskNorm : s * lam k = |hF.eigenvalues k| / sigma := by
    dsimp only [lam]
    rw [show s * (hF.eigenvalues k / sigma) =
        (s * hF.eigenvalues k) / sigma by ring, hsk]
  have hmax : ∀ i, |s * lam i| ≤ s * lam k := by
    intro i
    rw [hskNorm]
    calc
      |s * lam i| = |hF.eigenvalues i| / sigma := by
        dsimp only [lam]
        rw [abs_mul, hsAbs, one_mul, abs_div, abs_of_pos hsigma]
      _ ≤ |hF.eigenvalues k| / sigma :=
        (div_le_div_iff_of_pos_right hsigma).2 (hk i (Finset.mem_univ i))
  have hlamk : 0 ≤ s * lam k := by
    rw [hskNorm]
    positivity
  have hbase := uniform_diagonal_lower_of_ordered_eigenvalues
    (fun i ↦ s * a i) (fun i ↦ s * lam i) k hsum' hM hlamk hmax
      hx hxM heps hepsOne
  have hscaled : orderedGaussianLowerConstant M * eps ≤
      (diagonalCenteredLaw (fun i ↦ s * a i)
        (fun i ↦ s * lam i)).real (Set.Icc x (x + eps)) := by
    rw [← map_diagonalPartialSum_univ_eq_diagonalCenteredLaw
      (fun i ↦ s * a i) (fun i ↦ s * lam i)]
    rw [map_measureReal_apply
      (continuous_diagonalPartialSum
        (fun i ↦ s * a i) (fun i ↦ s * lam i) Finset.univ).measurable
      measurableSet_Icc]
    exact hbase
  rw [gaussianQuadraticCenteredLaw_map_div_eq_diagonal f hF hsigma.ne']
  change orderedGaussianLowerConstant M * eps ≤
    ((diagonalCenteredLaw a lam).map (fun y ↦ s * y)).real
      (Set.Icc x (x + eps))
  rw [← diagonalCenteredLaw_smul a lam s]
  exact hscaled

/-- The same matrix-only sign, in the symmetric-small-ball form used by
reverse Esseen. -/
theorem exists_sign_gaussianQuadraticCenteredLaw_smallBall_lower_uniform
    {n : ℕ} [NeZero n]
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ∀ (f : Fin n → ℝ) {sigma M x eps : ℝ},
        0 < sigma →
        sigma ^ 2 = 2 * frobeniusSq F + vectorSqNorm f →
        0 ≤ M → 0 ≤ x → x ≤ M → 0 ≤ eps → eps ≤ 1 →
        orderedGaussianLowerConstant M * eps ≤
          Erdos88.Esseen.smallBall
            ((gaussianQuadraticCenteredLaw f F).map (fun y ↦ y / sigma))
            eps (s * x) := by
  obtain ⟨s, hs, hlower⟩ :=
    exists_sign_gaussianQuadraticCenteredLaw_normalized_lower_uniform hF
  refine ⟨s, hs, ?_⟩
  intro f sigma M x eps hsigma hsigmaSq hM hx hxM heps hepsOne
  let nu := (gaussianQuadraticCenteredLaw f F).map (fun y ↦ y / sigma)
  let : IsProbabilityMeasure (gaussianQuadraticCenteredLaw f F) := by
    unfold gaussianQuadraticCenteredLaw
    exact Measure.isProbabilityMeasure_map
      ((continuous_quadraticPolynomial 0 f F).sub continuous_const).aemeasurable
  let : IsProbabilityMeasure nu := by
    dsimp only [nu]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hinterval := hlower f hsigma hsigmaSq hM hx hxM heps hepsOne
  change orderedGaussianLowerConstant M * eps ≤
    (nu.map (fun y ↦ s * y)).real (Set.Icc x (x + eps)) at hinterval
  have hsigned : orderedGaussianLowerConstant M * eps ≤
      Erdos88.Esseen.smallBall (nu.map (fun y ↦ s * y)) eps x := by
    apply hinterval.trans
    unfold Erdos88.Esseen.smallBall
    apply measureReal_mono (h₂ := measure_ne_top (nu.map (fun y ↦ s * y)) _)
    intro y hy
    exact ⟨by linarith [hy.1], hy.2⟩
  rw [smallBall_map_mul_sign nu hs] at hsigned
  exact hsigned

/-- The normalized Gaussian law satisfies precisely the interval-ratio
hypothesis used by the generalized reverse Esseen lemma at one of the two
signed centers whenever an upper bound linear in the radius is available. -/
theorem exists_sign_gaussianQuadraticCenteredLaw_smallBallRatioOn
    {n : ℕ} [NeZero n] (f : Fin n → ℝ)
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    {sigma M x eps C R : ℝ} (hsigma : 0 < sigma)
    (hsigmaSq : sigma ^ 2 = 2 * frobeniusSq F + vectorSqNorm f)
    (hM : 0 ≤ M) (hx : 0 ≤ x) (hxM : x ≤ M)
    (heps : 0 < eps) (hepsOne : eps ≤ 1) (hC : 0 ≤ C)
    (hupper : ∀ y : ℝ,
      Erdos88.Esseen.smallBall
          ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma))
          eps y ≤ C * eps) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      let nu := (gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma)
      orderedGaussianLowerConstant M * eps ≤
          Erdos88.Esseen.smallBall nu eps (s * x) ∧
        Erdos88.Esseen.SmallBallRatioOn nu (s * x) eps R
          (C / orderedGaussianLowerConstant M) := by
  obtain ⟨s, hs, hlower⟩ :=
    exists_sign_gaussianQuadraticCenteredLaw_normalized_lower
      f hF hsigma hsigmaSq hM hx hxM heps.le hepsOne
  refine ⟨s, hs, ?_⟩
  let nu := (gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma)
  let : IsProbabilityMeasure (gaussianQuadraticCenteredLaw f F) := by
    unfold gaussianQuadraticCenteredLaw
    exact Measure.isProbabilityMeasure_map
      ((continuous_quadraticPolynomial 0 f F).sub continuous_const).aemeasurable
  let : IsProbabilityMeasure
      ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  let : IsProbabilityMeasure nu := by
    dsimp only [nu]
    infer_instance
  have hc : 0 < orderedGaussianLowerConstant M :=
    orderedGaussianLowerConstant_pos hM
  change orderedGaussianLowerConstant M * eps ≤
    (nu.map (fun y ↦ s * y)).real (Set.Icc x (x + eps)) at hlower
  have hsignedBall : orderedGaussianLowerConstant M * eps ≤
      Erdos88.Esseen.smallBall (nu.map (fun y ↦ s * y)) eps x := by
    apply hlower.trans
    unfold Erdos88.Esseen.smallBall
    apply measureReal_mono (h₂ := measure_ne_top (nu.map (fun y ↦ s * y)) _)
    intro y hy
    exact ⟨by linarith [hy.1], hy.2⟩
  have hball : orderedGaussianLowerConstant M * eps ≤
      Erdos88.Esseen.smallBall nu eps (s * x) := by
    rw [← smallBall_map_mul_sign nu hs]
    exact hsignedBall
  refine ⟨hball, ?_⟩
  intro u _hu
  have hu : Erdos88.Esseen.smallBall nu eps u ≤ C * eps := by
    exact hupper u
  calc
    Erdos88.Esseen.smallBall nu eps u ≤ C * eps := hu
    _ = (C / orderedGaussianLowerConstant M) *
        (orderedGaussianLowerConstant M * eps) := by
      field_simp [hc.ne']
    _ ≤ (C / orderedGaussianLowerConstant M) *
        Erdos88.Esseen.smallBall nu eps (s * x) := by
      exact mul_le_mul_of_nonneg_left hball (div_nonneg hC hc.le)

end Erdos88.GaussianQuadratic
