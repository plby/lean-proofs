import ErdosProblems.Erdos525.Core

open scoped BigOperators Topology ComplexConjugate RealInnerProductSpace

namespace Erdos525

open Classical Filter Finset Set MeasureTheory
open Asymptotics

abbrev PositionCoordinate (m : ℕ) := Fin m → Fin 2 → ℝ
abbrev PositionEuclidean (m : ℕ) := EuclideanSpace ℝ (Fin m × Fin 2)

noncomputable def positionToEuclidean
    (u : PositionCoordinate m) : PositionEuclidean m :=
  WithLp.toLp 2 (fun i ↦ u i.1 i.2)

noncomputable def euclideanToPosition
    (x : PositionEuclidean m) : PositionCoordinate m :=
  fun r c ↦ x (r, c)

noncomputable def positionPhaseEmbedding
    (u : PositionCoordinate m) : PhaseCoordinate m :=
  fun r c ↦ if h : c.val < 2 then u r (Fin.castLT c h) else 0

@[simp] lemma positionPhaseEmbedding_castLE
    (u : PositionCoordinate m) (r : Fin m) (c : Fin 2) :
    positionPhaseEmbedding u r (Fin.castLE (by omega) c) = u r c := by
  change (if h : c.val < 2 then u r ⟨c.val, h⟩ else 0) = u r c
  rw [dif_pos c.isLt]

lemma phaseNormSq_positionPhaseEmbedding (u : PositionCoordinate m) :
    phaseNormSq (positionPhaseEmbedding u) = ‖positionToEuclidean u‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold phaseNormSq positionToEuclidean
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Fin.sum_univ_two, Fin.sum_univ_four]
  simp [positionPhaseEmbedding]

noncomputable def normalizedPositionEuclideanWalk
    (n : ℕ) (e : SignVector (2 * n)) (points : Fin m → ℝ) :
    PositionEuclidean m :=
  positionToEuclidean (fun r c ↦
    normalizedPhaseWalk n e points r (Fin.castLE (by omega) c))

/-- A covariance lower bound only on the position coordinates.  This is the
precise non-degeneracy needed for small-ball estimates for values of the
polynomial; derivative coordinates may degenerate near the real points
`0` and `π n`. -/
def HasPositionCovarianceLower
    (n : ℕ) (points : Fin m → ℝ) (gamma : ℝ) : Prop :=
  ∀ u : PositionCoordinate m,
    gamma * (2 * n + 1 : ℝ) * ‖positionToEuclidean u‖ ^ 2 ≤
      ∑ j : Fin (2 * n + 1),
        (phaseProjection n points (positionPhaseEmbedding u) j) ^ 2

lemma hasPositionCovarianceLower_of_phase
    (n : ℕ) (points : Fin m → ℝ) (gamma : ℝ)
    (hcov : HasPhaseCovarianceLower n points gamma) :
    HasPositionCovarianceLower n points gamma := by
  intro u
  simpa [phaseNormSq_positionPhaseEmbedding] using
    hcov (positionPhaseEmbedding u)

lemma phasePairing_positionPhaseEmbedding
    (u : PositionCoordinate m) (z : PhaseCoordinate m) :
    phasePairing (positionPhaseEmbedding u) z =
      ∑ r : Fin m, ∑ c : Fin 2,
        u r c * z r (Fin.castLE (by omega) c) := by
  unfold phasePairing positionPhaseEmbedding
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Fin.sum_univ_two, Fin.sum_univ_four]
  simp

lemma positionPairing_eq_inner
    (u : PositionCoordinate m) (z : PhaseCoordinate m) :
    (∑ r : Fin m, ∑ c : Fin 2,
        u r c * z r (Fin.castLE (by omega) c)) =
      ⟪positionToEuclidean u,
        positionToEuclidean (fun r c ↦
          z r (Fin.castLE (by omega) c))⟫ := by
  simp [positionToEuclidean, EuclideanSpace.inner_toLp_toLp,
    dotProduct, Fintype.sum_prod_type, mul_comm]

lemma positionCharFun_eq_phase
    (n : ℕ) (points : Fin m → ℝ) (u : PositionEuclidean m) :
    Erdos88.Fourier.finExpectation (SignVector (2 * n)) (fun e ↦
      Complex.exp (((⟪u, normalizedPositionEuclideanWalk n e points⟫ : ℝ) : ℂ) *
        Complex.I)) =
      normalizedPhaseCharFun n points
        (positionPhaseEmbedding (euclideanToPosition u)) := by
  unfold normalizedPhaseCharFun
  apply congrArg (Erdos88.Fourier.finExpectation (SignVector (2 * n)))
  funext e
  congr 2
  rw [phasePairing_positionPhaseEmbedding]
  rw [positionPairing_eq_inner]
  simp [normalizedPositionEuclideanWalk, euclideanToPosition,
    positionToEuclidean]

lemma norm_positionCharFun_le_gaussian_of_covariance
    (n : ℕ) (points : Fin m → ℝ) (gamma : ℝ)
    (hcov : HasPhaseCovarianceLower n points gamma)
    (u : PositionEuclidean m) (hu : ‖u‖ ≤ phaseNoWrapRadius n m) :
    ‖Erdos88.Fourier.finExpectation (SignVector (2 * n)) (fun e ↦
      Complex.exp (((⟪u, normalizedPositionEuclideanWalk n e points⟫ : ℝ) : ℂ) *
        Complex.I))‖ ≤
      Real.exp (-(gamma / Real.pi ^ 2 * ‖u‖ ^ 2)) := by
  rw [positionCharFun_eq_phase]
  have hnorm : ‖phaseToEuclidean
      (positionPhaseEmbedding (euclideanToPosition u))‖ = ‖u‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    rw [← phaseNormSq_eq_norm_sq,
      phaseNormSq_positionPhaseEmbedding]
    simp [positionToEuclidean, euclideanToPosition]
  have hsmall := normalizedPhase_no_wrap_of_norm_le
    n m (positionPhaseEmbedding (euclideanToPosition u)) (by
      rw [hnorm]
      exact hu)
  have h := norm_normalizedPhaseCharFun_le_gaussian_of_covariance
    n points gamma hcov
      (positionPhaseEmbedding (euclideanToPosition u)) hsmall
  rw [phaseNormSq_positionPhaseEmbedding] at h
  simpa [positionToEuclidean, euclideanToPosition] using h

lemma norm_positionCharFun_le_gaussian_of_positionCovariance
    (n : ℕ) (points : Fin m → ℝ) (gamma : ℝ)
    (hcov : HasPositionCovarianceLower n points gamma)
    (u : PositionEuclidean m) (hu : ‖u‖ ≤ phaseNoWrapRadius n m) :
    ‖Erdos88.Fourier.finExpectation (SignVector (2 * n)) (fun e ↦
      Complex.exp (((⟪u, normalizedPositionEuclideanWalk n e points⟫ : ℝ) : ℂ) *
        Complex.I))‖ ≤
      Real.exp (-(gamma / Real.pi ^ 2 * ‖u‖ ^ 2)) := by
  rw [positionCharFun_eq_phase]
  let v : PositionCoordinate m := euclideanToPosition u
  let z : PhaseCoordinate m := positionPhaseEmbedding v
  have hnorm : phaseNormSq z = ‖u‖ ^ 2 := by
    dsimp [z, v]
    rw [phaseNormSq_positionPhaseEmbedding]
    simp [positionToEuclidean, euclideanToPosition]
  have hsmall :
      |(Real.sqrt (2 * n + 1 : ℝ))⁻¹| *
          (∑ r : Fin m, ∑ c : Fin 4, |z r c|) / Real.pi < 1 / 2 := by
    apply normalizedPhase_no_wrap_of_norm_le n m z
    have hnorm' : ‖phaseToEuclidean z‖ = ‖u‖ := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
      rw [← phaseNormSq_eq_norm_sq, hnorm]
    exact hnorm'.trans_le hu
  have hraw :
      ‖normalizedPhaseCharFun n points z‖ ≤
        Real.exp (-(((Real.sqrt (2 * n + 1 : ℝ))⁻¹ / Real.pi) ^ 2 *
          (gamma * (2 * n + 1 : ℝ) * phaseNormSq z))) := by
    rw [normalizedPhaseCharFun_eq_projected]
    apply norm_projectedPhaseWalk_charFun_le_exp_neg
    rw [phaseProjection_distance_sum_eq n points z
      (Real.sqrt (2 * n + 1 : ℝ))⁻¹ hsmall]
    have hposition : gamma * (2 * n + 1 : ℝ) * phaseNormSq z ≤
        ∑ j : Fin (2 * n + 1), (phaseProjection n points z j) ^ 2 := by
      dsimp [z]
      rw [phaseNormSq_positionPhaseEmbedding]
      exact hcov v
    exact mul_le_mul_of_nonneg_left hposition (sq_nonneg _)
  convert hraw using 1
  have hcount : (0 : ℝ) < 2 * n + 1 := by positivity
  have hsqrt : Real.sqrt (2 * n + 1 : ℝ) ^ 2 = (2 * n + 1 : ℝ) :=
    Real.sq_sqrt hcount.le
  congr 2
  rw [hnorm, div_pow, inv_pow, hsqrt]
  field_simp [Real.pi_ne_zero]

noncomputable def positionCharFun (n : ℕ) (points : Fin m → ℝ)
    (u : PositionEuclidean m) : ℂ :=
  Erdos88.Fourier.finExpectation (SignVector (2 * n)) (fun e ↦
    Complex.exp (((⟪u, normalizedPositionEuclideanWalk n e points⟫ : ℝ) : ℂ) *
      Complex.I))

lemma positionCharFun_eq_normalizedPhaseCharFun
    (n : ℕ) (points : Fin m → ℝ) (u : PositionEuclidean m) :
    positionCharFun n points u = normalizedPhaseCharFun n points
      (positionPhaseEmbedding (euclideanToPosition u)) :=
  positionCharFun_eq_phase n points u

lemma norm_positionCharFun_le_one
    (n : ℕ) (points : Fin m → ℝ) (u : PositionEuclidean m) :
    ‖positionCharFun n points u‖ ≤ 1 := by
  rw [positionCharFun_eq_normalizedPhaseCharFun]
  exact norm_normalizedPhaseCharFun_le_one_test _ _ _

lemma finrank_positionEuclidean :
    Module.finrank ℝ (PositionEuclidean m) = 2 * m := by
  simp [PositionEuclidean, mul_comm]

lemma positionGaussian_integral
    (m : ℕ) (sigma : ℝ) (hsigma : 0 < sigma)
    (w : PositionEuclidean m) :
    (∫ u : PositionEuclidean m,
      Complex.exp (-((sigma ^ 2 / 2 : ℝ) : ℂ) * ‖u‖ ^ 2 +
        Complex.I * (⟪w, u⟫ : ℂ))) =
      ((Real.pi : ℂ) / ((sigma ^ 2 / 2 : ℝ) : ℂ)) ^
          ((Module.finrank ℝ (PositionEuclidean m) : ℂ) / 2) *
        Complex.exp (-((‖w‖ ^ 2 / (2 * sigma ^ 2) : ℝ) : ℂ)) := by
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (V := PositionEuclidean m) (b := ((sigma ^ 2 / 2 : ℝ) : ℂ))
    (by change 0 < sigma ^ 2 / 2; positivity) Complex.I w
  rw [h]
  congr 2
  rw [Complex.I_sq]
  push_cast
  field_simp [hsigma.ne']
  ring

noncomputable def positionGaussianSmoothedMass
    (n : ℕ) (points : Fin m → ℝ) (sigma : ℝ)
    (y : PositionEuclidean m) : ℂ :=
  Erdos88.Fourier.finExpectation (SignVector (2 * n)) (fun e ↦
    Complex.exp (-((‖normalizedPositionEuclideanWalk n e points - y‖ ^ 2 /
      (2 * sigma ^ 2) : ℝ) : ℂ)))

lemma positionSmoothing_term_eq
    (n : ℕ) (points : Fin m → ℝ) (sigma : ℝ)
    (y u : PositionEuclidean m) (e : SignVector (2 * n)) :
    Complex.exp (-((sigma ^ 2 / 2 : ℝ) : ℂ) * ‖u‖ ^ 2) *
        Complex.exp (-((⟪u, y⟫ : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((⟪u, normalizedPositionEuclideanWalk n e points⟫ : ℝ) : ℂ) *
          Complex.I) =
      Complex.exp (-((sigma ^ 2 / 2 : ℝ) : ℂ) * ‖u‖ ^ 2 +
        Complex.I *
          (⟪normalizedPositionEuclideanWalk n e points - y, u⟫ : ℂ)) := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  rw [inner_sub_left]
  simp only [real_inner_comm u]
  push_cast
  ring

lemma integrable_positionSmoothing_term
    (n : ℕ) (points : Fin m → ℝ) (sigma : ℝ) (hsigma : 0 < sigma)
    (y : PositionEuclidean m) (e : SignVector (2 * n)) :
    Integrable (fun u : PositionEuclidean m ↦
      Complex.exp (-((sigma ^ 2 / 2 : ℝ) : ℂ) * ‖u‖ ^ 2) *
        Complex.exp (-((⟪u, y⟫ : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((⟪u, normalizedPositionEuclideanWalk n e points⟫ : ℝ) : ℂ) *
          Complex.I)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := PositionEuclidean m) (b := ((sigma ^ 2 / 2 : ℝ) : ℂ))
    (by change 0 < sigma ^ 2 / 2; positivity) Complex.I
      (normalizedPositionEuclideanWalk n e points - y)
  exact h.congr (Eventually.of_forall fun u ↦
    (positionSmoothing_term_eq n points sigma y u e).symm)

lemma integral_positionSmoothing_term
    (n : ℕ) (points : Fin m → ℝ) (sigma : ℝ) (hsigma : 0 < sigma)
    (y : PositionEuclidean m) (e : SignVector (2 * n)) :
    (∫ u : PositionEuclidean m,
      Complex.exp (-((sigma ^ 2 / 2 : ℝ) : ℂ) * ‖u‖ ^ 2) *
        Complex.exp (-((⟪u, y⟫ : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((⟪u, normalizedPositionEuclideanWalk n e points⟫ : ℝ) : ℂ) *
          Complex.I)) =
      ((Real.pi : ℂ) / ((sigma ^ 2 / 2 : ℝ) : ℂ)) ^
          ((Module.finrank ℝ (PositionEuclidean m) : ℂ) / 2) *
        Complex.exp
          (-((‖normalizedPositionEuclideanWalk n e points - y‖ ^ 2 /
            (2 * sigma ^ 2) : ℝ) : ℂ)) := by
  apply Eq.trans (integral_congr_ae (Eventually.of_forall fun u ↦
    positionSmoothing_term_eq n points sigma y u e))
  exact positionGaussian_integral m sigma hsigma
    (normalizedPositionEuclideanWalk n e points - y)

theorem positionGaussianSmoothedMass_fourier
    (n : ℕ) (points : Fin m → ℝ) (sigma : ℝ) (hsigma : 0 < sigma)
    (y : PositionEuclidean m) :
    (∫ u : PositionEuclidean m,
      Complex.exp (-((sigma ^ 2 / 2 : ℝ) : ℂ) * ‖u‖ ^ 2) *
        Complex.exp (-((⟪u, y⟫ : ℝ) : ℂ) * Complex.I) *
        positionCharFun n points u) =
      ((Real.pi : ℂ) / ((sigma ^ 2 / 2 : ℝ) : ℂ)) ^
          ((Module.finrank ℝ (PositionEuclidean m) : ℂ) / 2) *
        positionGaussianSmoothedMass n points sigma y := by
  rw [show (fun u : PositionEuclidean m ↦
      Complex.exp (-((sigma ^ 2 / 2 : ℝ) : ℂ) * ‖u‖ ^ 2) *
        Complex.exp (-((⟪u, y⟫ : ℝ) : ℂ) * Complex.I) *
        positionCharFun n points u) =
      (fun u ↦ (∑ e : SignVector (2 * n),
        Complex.exp (-((sigma ^ 2 / 2 : ℝ) : ℂ) * ‖u‖ ^ 2) *
          Complex.exp (-((⟪u, y⟫ : ℝ) : ℂ) * Complex.I) *
          Complex.exp
            (((⟪u, normalizedPositionEuclideanWalk n e points⟫ : ℝ) : ℂ) *
              Complex.I)) /
        (Fintype.card (SignVector (2 * n)) : ℂ)) by
    funext u
    unfold positionCharFun Erdos88.Fourier.finExpectation
    have hsum :
        (∑ e : SignVector (2 * n),
          Complex.exp (-((sigma ^ 2 / 2 : ℝ) : ℂ) * ‖u‖ ^ 2) *
            Complex.exp (-((⟪u, y⟫ : ℝ) : ℂ) * Complex.I) *
            Complex.exp
              (((⟪u, normalizedPositionEuclideanWalk n e points⟫ : ℝ) : ℂ) *
                Complex.I)) =
          (Complex.exp (-((sigma ^ 2 / 2 : ℝ) : ℂ) * ‖u‖ ^ 2) *
            Complex.exp (-((⟪u, y⟫ : ℝ) : ℂ) * Complex.I)) *
              ∑ e : SignVector (2 * n),
                Complex.exp
                  (((⟪u, normalizedPositionEuclideanWalk n e points⟫ : ℝ) : ℂ) *
                    Complex.I) := by
      rw [Finset.mul_sum]
    rw [hsum]
    ring]
  rw [integral_div, integral_finsetSum]
  · simp_rw [integral_positionSmoothing_term n points sigma hsigma y]
    unfold positionGaussianSmoothedMass Erdos88.Fourier.finExpectation
    have hsum :
        (∑ e : SignVector (2 * n),
          ((Real.pi : ℂ) / ((sigma ^ 2 / 2 : ℝ) : ℂ)) ^
              ((Module.finrank ℝ (PositionEuclidean m) : ℂ) / 2) *
            Complex.exp
              (-((‖normalizedPositionEuclideanWalk n e points - y‖ ^ 2 /
                (2 * sigma ^ 2) : ℝ) : ℂ))) =
          ((Real.pi : ℂ) / ((sigma ^ 2 / 2 : ℝ) : ℂ)) ^
              ((Module.finrank ℝ (PositionEuclidean m) : ℂ) / 2) *
            ∑ e : SignVector (2 * n),
              Complex.exp
                (-((‖normalizedPositionEuclideanWalk n e points - y‖ ^ 2 /
                  (2 * sigma ^ 2) : ℝ) : ℂ)) := by
      rw [Finset.mul_sum]
    rw [hsum]
    ring
  · intro e _he
    exact integrable_positionSmoothing_term n points sigma hsigma y e

noncomputable def positionFourierMultiplier
    (sigma : ℝ) (y u : PositionEuclidean m) : ℂ :=
  Complex.exp (((-(sigma ^ 2 / 2) * ‖u‖ ^ 2 : ℝ) : ℂ)) *
    Complex.exp (-((⟪u, y⟫ : ℝ) : ℂ) * Complex.I)

lemma norm_positionFourierMultiplier
    (sigma : ℝ) (y u : PositionEuclidean m) :
    ‖positionFourierMultiplier sigma y u‖ =
      Real.exp (-(sigma ^ 2 / 2) * ‖u‖ ^ 2) := by
  unfold positionFourierMultiplier
  rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
  have hfirst :
      (((-(sigma ^ 2 / 2) * ‖u‖ ^ 2 : ℝ) : ℂ)).re =
        -(sigma ^ 2 / 2) * ‖u‖ ^ 2 := rfl
  have hsecond : (-((⟪u, y⟫ : ℝ) : ℂ) * Complex.I).re = 0 := by simp
  rw [hfirst, hsecond, Real.exp_zero, mul_one]

lemma positionFourierMultiplier_eq
    (sigma : ℝ) (y u : PositionEuclidean m) :
    positionFourierMultiplier sigma y u =
      Complex.exp (-((sigma ^ 2 / 2 : ℝ) : ℂ) * ‖u‖ ^ 2) *
        Complex.exp (-((⟪u, y⟫ : ℝ) : ℂ) * Complex.I) := by
  unfold positionFourierMultiplier
  congr 2
  push_cast
  ring

lemma integrable_positionFourier_charFun
    (n : ℕ) (points : Fin m → ℝ) (sigma : ℝ) (hsigma : 0 < sigma)
    (y : PositionEuclidean m) :
    Integrable (fun u ↦ positionFourierMultiplier sigma y u *
      positionCharFun n points u) := by
  rw [show (fun u : PositionEuclidean m ↦
      positionFourierMultiplier sigma y u * positionCharFun n points u) =
      (fun u ↦ (∑ e : SignVector (2 * n),
        Complex.exp (-((sigma ^ 2 / 2 : ℝ) : ℂ) * ‖u‖ ^ 2) *
          Complex.exp (-((⟪u, y⟫ : ℝ) : ℂ) * Complex.I) *
          Complex.exp
            (((⟪u, normalizedPositionEuclideanWalk n e points⟫ : ℝ) : ℂ) *
              Complex.I)) /
        (Fintype.card (SignVector (2 * n)) : ℂ)) by
    funext u
    rw [positionFourierMultiplier_eq]
    unfold positionCharFun Erdos88.Fourier.finExpectation
    have hsum :
        (∑ e : SignVector (2 * n),
          Complex.exp (-((sigma ^ 2 / 2 : ℝ) : ℂ) * ‖u‖ ^ 2) *
            Complex.exp (-((⟪u, y⟫ : ℝ) : ℂ) * Complex.I) *
            Complex.exp
              (((⟪u, normalizedPositionEuclideanWalk n e points⟫ : ℝ) : ℂ) *
                Complex.I)) =
          (Complex.exp (-((sigma ^ 2 / 2 : ℝ) : ℂ) * ‖u‖ ^ 2) *
            Complex.exp (-((⟪u, y⟫ : ℝ) : ℂ) * Complex.I)) *
              ∑ e : SignVector (2 * n),
                Complex.exp
                  (((⟪u, normalizedPositionEuclideanWalk n e points⟫ : ℝ) : ℂ) *
                    Complex.I) := by
      rw [Finset.mul_sum]
    rw [hsum]
    ring]
  exact (integrable_finsetSum (Finset.univ : Finset (SignVector (2 * n)))
    (fun e _he ↦ integrable_positionSmoothing_term n points sigma hsigma y e)).div_const _

lemma positionFourierExponent_eq (m : ℕ) :
    ((Module.finrank ℝ (PositionEuclidean m) : ℂ) / 2) = (m : ℕ) := by
  rw [finrank_positionEuclidean]
  push_cast
  ring

lemma positionFourierNormalization_eq_real
    (m : ℕ) (sigma : ℝ) (hsigma : 0 < sigma) :
    ((Real.pi : ℂ) / ((sigma ^ 2 / 2 : ℝ) : ℂ)) ^
          ((Module.finrank ℝ (PositionEuclidean m) : ℂ) / 2) =
      (((2 * Real.pi / sigma ^ 2) ^ m : ℝ) : ℂ) := by
  rw [positionFourierExponent_eq, Complex.cpow_natCast]
  push_cast
  congr 1
  field_simp [hsigma.ne']

noncomputable def positionGaussianSmoothedMassReal
    (n : ℕ) (points : Fin m → ℝ) (sigma : ℝ)
    (y : PositionEuclidean m) : ℝ :=
  uniformExpectation (fun e : SignVector (2 * n) ↦
    Real.exp (-(‖normalizedPositionEuclideanWalk n e points - y‖ ^ 2 /
      (2 * sigma ^ 2))))

lemma positionGaussianSmoothedMass_eq_real
    (n : ℕ) (points : Fin m → ℝ) (sigma : ℝ)
    (y : PositionEuclidean m) :
    positionGaussianSmoothedMass n points sigma y =
      (positionGaussianSmoothedMassReal n points sigma y : ℂ) := by
  unfold positionGaussianSmoothedMass positionGaussianSmoothedMassReal
    Erdos88.Fourier.finExpectation uniformExpectation
  push_cast
  congr 1

lemma uniformProbability_positionBall_mul_le_smoothedMassReal
    (n : ℕ) (points : Fin m → ℝ) (sigma delta : ℝ)
    (hsigma : 0 < sigma) (hdelta : 0 ≤ delta)
    (y : PositionEuclidean m) :
    uniformProbability (fun e : SignVector (2 * n) ↦
        ‖normalizedPositionEuclideanWalk n e points - y‖ ≤ delta) *
        Real.exp (-(delta ^ 2 / (2 * sigma ^ 2))) ≤
      positionGaussianSmoothedMassReal n points sigma y := by
  rw [← uniformExpectation_indicator]
  change _ ≤ uniformExpectation (fun e : SignVector (2 * n) ↦
    Real.exp (-(‖normalizedPositionEuclideanWalk n e points - y‖ ^ 2 /
      (2 * sigma ^ 2))))
  rw [mul_comm, ← uniformExpectation_const_mul]
  apply uniformExpectation_mono
  intro e
  by_cases he : ‖normalizedPositionEuclideanWalk n e points - y‖ ≤ delta
  · rw [if_pos he, mul_one]
    apply Real.exp_le_exp.mpr
    have hsquare :
        ‖normalizedPositionEuclideanWalk n e points - y‖ ^ 2 ≤ delta ^ 2 := by
      nlinarith [norm_nonneg (normalizedPositionEuclideanWalk n e points - y)]
    exact neg_le_neg (div_le_div_of_nonneg_right hsquare (by positivity))
  · rw [if_neg he, mul_zero]
    positivity

lemma integrable_rexp_neg_mul_position_norm_sq
    (m : ℕ) (c : ℝ) (hc : 0 < c) :
    Integrable (fun u : PositionEuclidean m ↦ Real.exp (-c * ‖u‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := PositionEuclidean m) (b := (c : ℂ))
    (by simpa using hc) 0 (0 : PositionEuclidean m)).norm
  apply h.congr
  filter_upwards [] with u
  rw [Complex.norm_exp]
  have hexp :
      (-(c : ℂ) * (‖u‖ : ℂ) ^ 2 +
        0 * (⟪(0 : PositionEuclidean m), u⟫ : ℂ)) =
        ((-c * ‖u‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hexp]
  rfl

lemma positionGaussianSmoothedMassReal_fourier_le
    (n m : ℕ) (points : Fin m → ℝ)
    (sigma : ℝ) (hsigma : 0 < sigma) (y : PositionEuclidean m) :
    (2 * Real.pi / sigma ^ 2) ^ m *
        positionGaussianSmoothedMassReal n points sigma y ≤
      ∫ u : PositionEuclidean m,
        Real.exp (-(sigma ^ 2 / 2) * ‖u‖ ^ 2) *
          ‖positionCharFun n points u‖ := by
  have h := norm_integral_le_integral_norm (μ := volume)
    (fun u : PositionEuclidean m ↦
      positionFourierMultiplier sigma y u * positionCharFun n points u)
  rw [show (∫ u : PositionEuclidean m,
      positionFourierMultiplier sigma y u * positionCharFun n points u) =
      ((Real.pi : ℂ) / ((sigma ^ 2 / 2 : ℝ) : ℂ)) ^
          ((Module.finrank ℝ (PositionEuclidean m) : ℂ) / 2) *
        positionGaussianSmoothedMass n points sigma y by
      apply Eq.trans (integral_congr_ae (Eventually.of_forall fun u ↦ by
        rw [positionFourierMultiplier_eq]))
      exact positionGaussianSmoothedMass_fourier n points sigma hsigma y,
    positionFourierNormalization_eq_real m sigma hsigma,
    positionGaussianSmoothedMass_eq_real] at h
  have hmassNonneg : 0 ≤
      positionGaussianSmoothedMassReal n points sigma y := by
    unfold positionGaussianSmoothedMassReal uniformExpectation
    positivity
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < (2 * Real.pi / sigma ^ 2) ^ m),
    abs_of_nonneg hmassNonneg, norm_positionFourierMultiplier] using h

lemma positionCharFun_smoothingTail_le
    (n m : ℕ) (points : Fin m → ℝ)
    (sigma B : ℝ) (hsigma : 0 < sigma) (hB : 0 ≤ B) :
    (∫ u : PositionEuclidean m in {u | B ≤ ‖u‖},
      Real.exp (-(sigma ^ 2 / 2) * ‖u‖ ^ 2) *
        ‖positionCharFun n points u‖) ≤
      Real.exp (-(sigma ^ 2 / 4) * B ^ 2) *
        (Real.pi / (sigma ^ 2 / 4)) ^ m := by
  let c : ℝ := sigma ^ 2 / 4
  let C : ℝ := Real.exp (-c * B ^ 2)
  let g : PositionEuclidean m → ℝ := fun u ↦ C * Real.exp (-c * ‖u‖ ^ 2)
  have hc : 0 < c := by dsimp [c]; positivity
  have hg : Integrable g :=
    (integrable_rexp_neg_mul_position_norm_sq m c hc).const_mul C
  calc
    (∫ u : PositionEuclidean m in {u | B ≤ ‖u‖},
      Real.exp (-(sigma ^ 2 / 2) * ‖u‖ ^ 2) *
        ‖positionCharFun n points u‖) ≤
        ∫ u : PositionEuclidean m in {u | B ≤ ‖u‖}, g u := by
      apply setIntegral_mono_of_nonneg
      · intro u _hu
        positivity
      · intro u hu
        have hchar := norm_positionCharFun_le_one n points u
        change B ≤ ‖u‖ at hu
        have hsquares : B ^ 2 ≤ ‖u‖ ^ 2 := by
          nlinarith [norm_nonneg u]
        have hexp : Real.exp (-c * ‖u‖ ^ 2) ≤
            Real.exp (-c * B ^ 2) := by
          apply Real.exp_le_exp.mpr
          nlinarith [mul_le_mul_of_nonneg_left hsquares hc.le]
        have hsplit : Real.exp (-(sigma ^ 2 / 2) * ‖u‖ ^ 2) =
            Real.exp (-c * ‖u‖ ^ 2) * Real.exp (-c * ‖u‖ ^ 2) := by
          rw [← Real.exp_add]
          congr 1
          dsimp [c]
          ring
        rw [hsplit]
        unfold g C
        calc
          _ ≤ (Real.exp (-c * B ^ 2) * Real.exp (-c * ‖u‖ ^ 2)) * 1 := by
            gcongr
          _ = _ := by ring
      · exact hg.integrableOn
    _ ≤ ∫ u : PositionEuclidean m, g u := by
      apply setIntegral_le_integral hg
      exact Eventually.of_forall fun u ↦ by unfold g C; positivity
    _ = C * (Real.pi / c) ^ m := by
      unfold g
      rw [integral_const_mul]
      rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hc]
      rw [finrank_positionEuclidean]
      rw [show ((2 * m : ℕ) : ℝ) / 2 = (m : ℕ) by push_cast; ring,
        Real.rpow_natCast]
    _ = _ := by rfl

lemma positionCharFun_integral_le_of_positionCovariance
    (n m : ℕ) (points : Fin m → ℝ) (gamma sigma : ℝ)
    (hgamma : 0 < gamma) (hsigma : 0 < sigma)
    (hcov : HasPositionCovarianceLower n points gamma) :
    (∫ u : PositionEuclidean m,
      Real.exp (-(sigma ^ 2 / 2) * ‖u‖ ^ 2) *
        ‖positionCharFun n points u‖) ≤
      (Real.pi / (gamma / Real.pi ^ 2)) ^ m +
        Real.exp (-(sigma ^ 2 / 4) * phaseNoWrapRadius n m ^ 2) *
          (Real.pi / (sigma ^ 2 / 4)) ^ m := by
  let f : PositionEuclidean m → ℝ := fun u ↦
    Real.exp (-(sigma ^ 2 / 2) * ‖u‖ ^ 2) * ‖positionCharFun n points u‖
  let B : Set (PositionEuclidean m) := Metric.ball 0 (phaseNoWrapRadius n m)
  let g : PositionEuclidean m → ℝ := fun u ↦
    Real.exp (-(gamma / Real.pi ^ 2) * ‖u‖ ^ 2)
  have hc : 0 < gamma / Real.pi ^ 2 := by positivity
  have hg : Integrable g := by
    simpa [g] using integrable_rexp_neg_mul_position_norm_sq m _ hc
  have hf : Integrable f := by
    have h := (integrable_positionFourier_charFun
      n points sigma hsigma (0 : PositionEuclidean m)).norm
    apply h.congr
    filter_upwards [] with u
    dsimp [f]
    rw [norm_mul, norm_positionFourierMultiplier]
  have hball : (∫ u in B, f u) ≤ ∫ u, g u := by
    calc
      (∫ u in B, f u) ≤ ∫ u in B, g u := by
        apply setIntegral_mono_on hf.integrableOn hg.integrableOn
          measurableSet_ball
        intro u hu
        have huR : ‖u‖ ≤ phaseNoWrapRadius n m :=
          (mem_ball_zero_iff.mp hu).le
        have hchar := norm_positionCharFun_le_gaussian_of_positionCovariance
          n points gamma hcov u huR
        have hweight : Real.exp (-(sigma ^ 2 / 2) * ‖u‖ ^ 2) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          exact mul_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr (by positivity)) (sq_nonneg _)
        dsimp [f, g]
        calc
          _ ≤ 1 * Real.exp (-(gamma / Real.pi ^ 2 * ‖u‖ ^ 2)) :=
            mul_le_mul hweight hchar (norm_nonneg _) zero_le_one
          _ = _ := by congr 1 <;> ring
      _ ≤ ∫ u, g u := setIntegral_le_integral hg
        (Eventually.of_forall fun u ↦ by dsimp [g]; positivity)
  have htail : (∫ u in Bᶜ, f u) ≤
      Real.exp (-(sigma ^ 2 / 4) * phaseNoWrapRadius n m ^ 2) *
        (Real.pi / (sigma ^ 2 / 4)) ^ m := by
    have h := positionCharFun_smoothingTail_le n m points sigma
      (phaseNoWrapRadius n m) hsigma (by unfold phaseNoWrapRadius; positivity)
    have hBc : Bᶜ = {u : PositionEuclidean m |
        phaseNoWrapRadius n m ≤ ‖u‖} := by
      ext u
      simp [B, mem_ball_zero_iff]
    rw [hBc]
    simpa [f] using h
  rw [← integral_add_compl (s := B) measurableSet_ball hf]
  calc
    (∫ u in B, f u) + ∫ u in Bᶜ, f u ≤
        (∫ u, g u) +
          Real.exp (-(sigma ^ 2 / 4) * phaseNoWrapRadius n m ^ 2) *
            (Real.pi / (sigma ^ 2 / 4)) ^ m := add_le_add hball htail
    _ = _ := by
      rw [show (∫ u : PositionEuclidean m, g u) =
          (Real.pi / (gamma / Real.pi ^ 2)) ^ m by
        dsimp [g]
        rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hc]
        rw [finrank_positionEuclidean]
        rw [show ((2 * m : ℕ) : ℝ) / 2 = (m : ℕ) by push_cast; ring,
          Real.rpow_natCast]]

lemma positionCharFun_integral_le_of_covariance
    (n m : ℕ) (points : Fin m → ℝ) (gamma sigma : ℝ)
    (hgamma : 0 < gamma) (hsigma : 0 < sigma)
    (hcov : HasPhaseCovarianceLower n points gamma) :
    (∫ u : PositionEuclidean m,
      Real.exp (-(sigma ^ 2 / 2) * ‖u‖ ^ 2) *
        ‖positionCharFun n points u‖) ≤
      (Real.pi / (gamma / Real.pi ^ 2)) ^ m +
        Real.exp (-(sigma ^ 2 / 4) * phaseNoWrapRadius n m ^ 2) *
          (Real.pi / (sigma ^ 2 / 4)) ^ m :=
  positionCharFun_integral_le_of_positionCovariance n m points gamma sigma
    hgamma hsigma (hasPositionCovarianceLower_of_phase n points gamma hcov)

lemma uniformProbability_positionBall_le_of_positionCovariance
    (n m : ℕ) (points : Fin m → ℝ) (gamma sigma delta : ℝ)
    (hgamma : 0 < gamma) (hsigma : 0 < sigma) (hdelta : 0 ≤ delta)
    (hcov : HasPositionCovarianceLower n points gamma)
    (y : PositionEuclidean m) :
    uniformProbability (fun e : SignVector (2 * n) ↦
        ‖normalizedPositionEuclideanWalk n e points - y‖ ≤ delta) ≤
      ((Real.pi / (gamma / Real.pi ^ 2)) ^ m +
          Real.exp (-(sigma ^ 2 / 4) * phaseNoWrapRadius n m ^ 2) *
            (Real.pi / (sigma ^ 2 / 4)) ^ m) /
        ((2 * Real.pi / sigma ^ 2) ^ m *
          Real.exp (-(delta ^ 2 / (2 * sigma ^ 2)))) := by
  have hmass := uniformProbability_positionBall_mul_le_smoothedMassReal
    n points sigma delta hsigma hdelta y
  have hscaled := mul_le_mul_of_nonneg_left hmass
    (show 0 ≤ (2 * Real.pi / sigma ^ 2) ^ m by positivity)
  have hfour := positionGaussianSmoothedMassReal_fourier_le
    n m points sigma hsigma y
  have hintegral := positionCharFun_integral_le_of_positionCovariance
    n m points gamma sigma hgamma hsigma hcov
  have hupper : (2 * Real.pi / sigma ^ 2) ^ m *
        positionGaussianSmoothedMassReal n points sigma y ≤
      (Real.pi / (gamma / Real.pi ^ 2)) ^ m +
        Real.exp (-(sigma ^ 2 / 4) * phaseNoWrapRadius n m ^ 2) *
          (Real.pi / (sigma ^ 2 / 4)) ^ m := hfour.trans hintegral
  have hden : 0 < (2 * Real.pi / sigma ^ 2) ^ m *
      Real.exp (-(delta ^ 2 / (2 * sigma ^ 2))) := by positivity
  apply (le_div_iff₀ hden).2
  calc
    _ = (2 * Real.pi / sigma ^ 2) ^ m *
        (uniformProbability (fun e : SignVector (2 * n) ↦
          ‖normalizedPositionEuclideanWalk n e points - y‖ ≤ delta) *
          Real.exp (-(delta ^ 2 / (2 * sigma ^ 2)))) := by ring
    _ ≤ (2 * Real.pi / sigma ^ 2) ^ m *
        positionGaussianSmoothedMassReal n points sigma y := hscaled
    _ ≤ _ := hupper

lemma uniformProbability_positionBall_le_of_covariance
    (n m : ℕ) (points : Fin m → ℝ) (gamma sigma delta : ℝ)
    (hgamma : 0 < gamma) (hsigma : 0 < sigma) (hdelta : 0 ≤ delta)
    (hcov : HasPhaseCovarianceLower n points gamma)
    (y : PositionEuclidean m) :
    uniformProbability (fun e : SignVector (2 * n) ↦
        ‖normalizedPositionEuclideanWalk n e points - y‖ ≤ delta) ≤
      ((Real.pi / (gamma / Real.pi ^ 2)) ^ m +
          Real.exp (-(sigma ^ 2 / 4) * phaseNoWrapRadius n m ^ 2) *
            (Real.pi / (sigma ^ 2 / 4)) ^ m) /
        ((2 * Real.pi / sigma ^ 2) ^ m *
          Real.exp (-(delta ^ 2 / (2 * sigma ^ 2)))) := by
  have hmass := uniformProbability_positionBall_mul_le_smoothedMassReal
    n points sigma delta hsigma hdelta y
  have hscaled := mul_le_mul_of_nonneg_left hmass
    (show 0 ≤ (2 * Real.pi / sigma ^ 2) ^ m by positivity)
  have hfour := positionGaussianSmoothedMassReal_fourier_le
    n m points sigma hsigma y
  have hintegral := positionCharFun_integral_le_of_covariance
    n m points gamma sigma hgamma hsigma hcov
  have hupper : (2 * Real.pi / sigma ^ 2) ^ m *
        positionGaussianSmoothedMassReal n points sigma y ≤
      (Real.pi / (gamma / Real.pi ^ 2)) ^ m +
        Real.exp (-(sigma ^ 2 / 4) * phaseNoWrapRadius n m ^ 2) *
          (Real.pi / (sigma ^ 2 / 4)) ^ m := hfour.trans hintegral
  have hden : 0 < (2 * Real.pi / sigma ^ 2) ^ m *
      Real.exp (-(delta ^ 2 / (2 * sigma ^ 2))) := by positivity
  apply (le_div_iff₀ hden).2
  calc
    _ = (2 * Real.pi / sigma ^ 2) ^ m *
        (uniformProbability (fun e : SignVector (2 * n) ↦
          ‖normalizedPositionEuclideanWalk n e points - y‖ ≤ delta) *
          Real.exp (-(delta ^ 2 / (2 * sigma ^ 2)))) := by ring
    _ ≤ (2 * Real.pi / sigma ^ 2) ^ m *
        positionGaussianSmoothedMassReal n points sigma y := hscaled
    _ ≤ _ := hupper

lemma phaseVelocityCoeff_positionPhaseEmbedding
    (u : PositionCoordinate m) (r : Fin m) :
    phaseVelocityCoeff (positionPhaseEmbedding u) r = 0 := by
  unfold phaseVelocityCoeff positionPhaseEmbedding
  norm_num

/-- In the position subspace the affine velocity correction vanishes
identically, so high-frequency rigidity remains valid at weak separation
without the scale condition needed for general phase directions. -/
theorem phaseLatticeEnergy_high_frequency_position_rigidity
    (n m Q R q k W H : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hQ : 0 < Q)
    (hR : 800 ≤ R) (hq : 800 ≤ q) (hW : 0 < W) (hH : 0 < H)
    (K lam eps a t E J : ℝ)
    (points : Fin m → ℝ) (u : PhaseCoordinate m)
    (hu : phaseNormSq u = 1)
    (hvelocityZero : ∀ r, phaseVelocityCoeff u r = 0)
    (hsmooth : ∀ r, IsSmooth n K (points r))
    (hspread : IsSpread n lam points)
    (hrho : 0 < min (K / n) (lam / n))
    (hQK : Q ^ (2 * m) ≤ Nat.floor K + 1)
    (heps0 : 0 ≤ eps) (hepsSmall : eps < 1 / 16)
    (hscale : 4000 * eps / R ≤ K / n)
    (ha : 0 < a) (ht : t ≠ 0)
    (hblock : (W : ℝ) * (E / a ^ 2 + 1) ≤ 2 * n + 1)
    (hfit : 2 * H + 2 * (phaseTwistCount m * q) +
        2 * k * (R * Q ^ (2 * m)) ≤ W)
    (hJ : 0 ≤ J) (hJsize : (n : ℝ) ≤ J * H)
    (hunwrap :
      (|t| / Real.pi) *
          ((4 * m : ℕ) *
            ((2 * Real.pi / Q) ^ (2 * k) +
              2 * (k : ℝ) * ((Q ^ (2 * m) : ℕ) : ℝ) / n *
                (2 * Real.pi / Q) ^ (2 * k - 1))) +
        (2 : ℝ) ^ (2 * k) * a < 1)
    (hdeltaOne :
      individualDilationGap q (min (K / n) (lam / n)) ≤ 1)
    (hposition :
      phaseHighPositionBudget t E J (phaseTwistCount m) k <
        phaseHighPositionDemand m H k (phaseTwistCount m) eps
          (individualDilationGap q (min (K / n) (lam / n)))) :
    E < phaseLatticeEnergy n points u t := by
  by_contra hnot
  have henergy : phaseLatticeEnergy n points u t ≤ E := le_of_not_gt hnot
  let rho : ℝ := min (K / n) (lam / n)
  let delta : ℝ := individualDilationGap q rho
  let eta : ℝ := 2 * Real.pi / Q
  let ellTwist : ℕ := phaseTwistCount m
  have hrho' : 0 < rho := by simpa [rho] using hrho
  have hdeltaPos : 0 < delta := by
    dsimp [delta, individualDilationGap]
    have hqreal : (0 : ℝ) < q := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hq)
    positivity
  have hdelta0 : 0 ≤ delta := hdeltaPos.le
  have heta0 : 0 ≤ eta := by dsimp [eta]; positivity
  rcases exists_scaledPhase_good_block_of_energy_le
      n W points u t a E hW ha henergy hblock with ⟨s, hs, hgood⟩
  have hsle : s ≤ 2 * n := by omega
  have hjbase : |((((s : ℕ) : ℤ) - (n : ℤ)) : ℝ)| ≤ (n : ℝ) := by
    have hsreal : (s : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hsle
    simp only [Int.cast_sub, Int.cast_natCast]
    rw [abs_le]
    constructor <;> linarith
  have hj : |((((s : ℕ) : ℤ) - (n : ℤ)) : ℝ)| ≤ J * H :=
    hjbase.trans hJsize
  rcases exists_large_phaseCoeff_general hm u with ⟨r, hlarge⟩
  have hpos : phaseNormSq u / (2 * (m : ℝ)) ≤
      Complex.normSq (phasePositionCoeff u r) := by
    rcases hlarge with hpos | hvel
    · exact hpos
    · rw [hvelocityZero r, Complex.normSq_zero] at hvel
      have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
      rw [hu] at hvel
      have : 0 < 1 / (2 * (m : ℝ)) := by positivity
      linarith
  let target : ReflectedMode m := (r, true)
  rcases exists_reflectedMode_dirichletStep n m Q hn hQ points with
    ⟨q₀, hq₀1, hq₀Q, hdirichletStrict⟩
  have hdirichlet : ∀ b : ReflectedMode m,
      ‖complexWave n (reflectedModeTime points b) (q₀ : ℤ) - 1‖ ≤ eta := by
    intro b
    exact (hdirichletStrict b).le
  have hq₀K : q₀ ≤ Nat.floor K + 1 := hq₀Q.trans hQK
  have hdist : ∀ b : ReflectedMode m, b ≠ target →
      rho ≤ distanceToInteger
        ((reflectedModeTime points target - reflectedModeTime points b) /
          (2 * Real.pi * n)) := by
    intro b hbt
    simpa [rho] using reflectedMode_distance_lower
      n hn K lam points hsmooth hspread target b hbt.symm
  rcases exists_variableReflectedSteps n hn points target q hq rho hrho' hdist with
    ⟨step, hstep, hsep⟩
  let twists := variableReflectedTwists n points step target
  have hlen : twists.length = ellTwist := by
    simpa [twists, ellTwist, phaseTwistCount] using
      variableReflectedTwists_length n points step target
  have hsum : variableStepSum twists ≤ ellTwist * q := by
    have hs' := variableReflectedTwists_stepSum_le n points step target q
      (fun b hbt ↦ (hstep b hbt).2.le)
    simpa [twists, ellTwist, phaseTwistCount] using hs'
  have hspan : variableTwistSpan twists ≤ 2 * (ellTwist * q) := by
    rw [variableTwistSpan_eq_two_mul_stepSum]
    omega
  have hsep' : ∀ b : ReflectedMode m, b ≠ target →
      delta ≤ ‖complexWave n (reflectedModeTime points target) (step b : ℤ) -
        complexWave n (reflectedModeTime points b) (step b : ℤ)‖ := by
    simpa [delta, rho] using hsep
  have hl1 := phaseL1_le_of_phaseNormSq_eq_one u hu
  have hq₀Real : (q₀ : ℝ) ≤ (Q ^ (2 * m) : ℕ) := by exact_mod_cast hq₀Q
  have hunwrapActual :
      (|t| / Real.pi) *
          ((∑ r : Fin m, ∑ c : Fin 4, |u r c|) *
            (eta ^ (2 * k) +
              2 * (k : ℝ) * (q₀ : ℝ) / n * eta ^ (2 * k - 1))) +
        (2 : ℝ) ^ (2 * k) * a < 1 := by
    apply lt_of_le_of_lt _ hunwrap
    have hsecond :
        2 * (k : ℝ) * (q₀ : ℝ) / n * eta ^ (2 * k - 1) ≤
          2 * (k : ℝ) * ((Q ^ (2 * m) : ℕ) : ℝ) / n *
            eta ^ (2 * k - 1) := by
      gcongr
    have hl1' : (∑ r : Fin m, ∑ c : Fin 4, |u r c|) ≤
        ((4 * m : ℕ) : ℝ) := by
      convert hl1 using 1 <;> push_cast <;> ring
    have hinside :
        (∑ r : Fin m, ∑ c : Fin 4, |u r c|) *
            (eta ^ (2 * k) +
              2 * (k : ℝ) * (q₀ : ℝ) / n * eta ^ (2 * k - 1)) ≤
          ((4 * m : ℕ) : ℝ) *
            ((2 * Real.pi / Q) ^ (2 * k) +
              2 * (k : ℝ) * ((Q ^ (2 * m) : ℕ) : ℝ) / n *
                (2 * Real.pi / Q) ^ (2 * k - 1)) := by
      dsimp [eta]
      exact mul_le_mul hl1' (add_le_add le_rfl hsecond)
        (by positivity) (by positivity)
    exact add_le_add
      (mul_le_mul_of_nonneg_left hinside (by positivity)) le_rfl
  have hmultiple : ∀ ell ∈ Finset.Ico 1 R,
      ‖complexWave n (reflectedModeTime points target)
          ((ell * q₀ : ℕ) : ℤ) - 1‖ ≤ eps := by
    intro ell hell
    have hellR : ell + 1 ≤ R := (Finset.mem_Ico.mp hell).2
    have hstepBound : (ell + 1) * q₀ ≤ R * Q ^ (2 * m) :=
      Nat.mul_le_mul hellR hq₀Q
    have hfitActual :
        2 * H + variableTwistSpan twists + 2 * k * (ell + 1) * q₀ ≤ W := by
      have hscaled : 2 * k * ((ell + 1) * q₀) ≤
          2 * k * (R * Q ^ (2 * m)) :=
        Nat.mul_le_mul_left (2 * k) hstepBound
      calc
        2 * H + variableTwistSpan twists + 2 * k * (ell + 1) * q₀ ≤
            2 * H + 2 * (ellTwist * q) +
              2 * k * ((ell + 1) * q₀) := by
                simpa [Nat.mul_assoc] using
                  Nat.add_le_add_right
                    (Nat.add_le_add_left hspan (2 * H))
                    (2 * k * ((ell + 1) * q₀))
        _ ≤ 2 * H + 2 * (ellTwist * q) +
              2 * k * (R * Q ^ (2 * m)) := by
                exact Nat.add_le_add_left
                  (by simpa [Nat.mul_assoc] using hscaled) _
        _ ≤ W := by simpa [ellTwist] using hfit
    by_contra hlargeChord
    have htarget : eps ≤
        ‖complexWave n (reflectedModeTime points (r, true))
            ((ell * q₀ : ℕ) : ℤ) - 1‖ := by
      simpa [target, not_le] using le_of_not_ge hlargeChord
    have hA := sqrt_one_div_eight_mul_le_reflectedPositionCoeff_true
      hm u hu r hpos
    have hvelReflected : reflectedVelocityCoeff u target = 0 := by
      simp [target, reflectedVelocityCoeff, hvelocityZero]
    have hcorrActual :
        2 * (4 : ℝ) ^ twists.length *
            (‖reflectedVelocityCoeff u target‖ *
              ‖complexWave n (reflectedModeTime points target)
                  ((ell * q₀ : ℕ) : ℤ) - 1‖ ^ (2 * k)) *
            (variableStepSum twists : ℝ) / n +
          ((k : ℝ) * (4 : ℝ) ^ k *
              ‖reflectedVelocityCoeff u target‖ *
                ((ell * q₀ : ℕ) : ℝ) / n) *
            delta ^ (2 * twists.length) ≤
        (Real.sqrt (1 / (8 * (m : ℝ))) * eps ^ (2 * k) *
          delta ^ (2 * twists.length)) / 2 := by
      rw [hvelReflected, norm_zero]
      simp only [zero_mul, mul_zero, zero_div, zero_add]
      positivity
    have hforce := goodBlock_largePosition_forces_latticeEnergy_multiple_pow_gap
      n hn points u t ht q₀ ell k eta heta0 hdirichlet
      s W hs a ha.le hgood step r delta hdelta0
      (by simpa [target] using hsep') H hH J hJ hj
      (by simpa [twists, target] using hfitActual) hunwrapActual
      (Real.sqrt (1 / (8 * (m : ℝ)))) eps (Real.sqrt_nonneg _) heps0
      (by simpa [target] using hA) (by simpa [target] using htarget)
      (by simpa [twists, target] using hcorrActual)
    have hbudget :
        (2 + 4 * (J + 1) ^ 2) * (36 : ℝ) ^
            (variableReflectedTwists n points step (r, true)).length *
          ((Real.pi / |t|) ^ 2 * (4 : ℝ) ^ (2 * k) *
            phaseLatticeEnergy n points u t) ≤
        (2 + 4 * (J + 1) ^ 2) * (36 : ℝ) ^
            (variableReflectedTwists n points step (r, true)).length *
          ((Real.pi / |t|) ^ 2 * (4 : ℝ) ^ (2 * k) * E) := by
      gcongr
    have hforce' := hforce.trans hbudget
    rw [show (variableReflectedTwists n points step (r, true)).length =
        ellTwist by simpa [twists, target] using hlen] at hforce'
    have hforced :
        phaseHighPositionDemand m H k ellTwist eps delta ≤
          phaseHighPositionBudget t E J ellTwist k := by
      simpa [phaseHighPositionDemand, phaseHighPositionBudget] using hforce'
    exact (not_le_of_gt (by simpa [ellTwist, delta, rho] using hposition)
      hforced).elim
  have hsmoothTarget : IsSmooth n K (reflectedModeTime points target) := by
    simpa [target, reflectedModeTime] using hsmooth r
  rcases hsmoothTarget.exists_large_multipleWave hn hq₀1 hq₀K
      R hR eps heps0 hepsSmall hscale with ⟨ell, hell, hlargeChord⟩
  exact (not_lt_of_ge (hmultiple ell hell)) hlargeChord

/-! ### Moment-dependent scales for weakly separated position events -/

noncomputable def positionRigidityBlockExponent (m : ℕ) : ℝ :=
  1 - weakSeparationExponent m

noncomputable def positionRigidityDilationLossExponent (m : ℕ) : ℝ :=
  2 * weakSeparationExponent m

noncomputable def positionRigidityDilationExponent (m : ℕ) : ℝ :=
  1 - positionRigidityDilationLossExponent m

noncomputable def positionRigidityEnergyExponent (m : ℕ) : ℝ :=
  weakSeparationExponent m / 10

noncomputable def positionRigidityGoodThresholdExponent (m : ℕ) : ℝ :=
  weakSeparationExponent m / 10

noncomputable def positionRigidityGapLossExponent (m : ℕ) : ℝ :=
  positionRigidityDilationLossExponent m + weakSeparationExponent m

lemma weakSeparationExponent_le_ten_thousandth (m : ℕ) :
    weakSeparationExponent m ≤ (1 / 10000 : ℝ) := by
  unfold weakSeparationExponent
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  have hsq : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith
  exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)

lemma positionRigidityDilationLossExponent_pos (m : ℕ) :
    0 < positionRigidityDilationLossExponent m := by
  unfold positionRigidityDilationLossExponent
  exact mul_pos (by norm_num) (weakSeparationExponent_pos m)

lemma positionRigidityDilationExponent_pos (m : ℕ) :
    0 < positionRigidityDilationExponent m := by
  have hs := weakSeparationExponent_le_ten_thousandth m
  unfold positionRigidityDilationExponent positionRigidityDilationLossExponent
  linarith

lemma positionRigidityBlockExponent_pos (m : ℕ) :
    0 < positionRigidityBlockExponent m := by
  have hs := weakSeparationExponent_le_ten_thousandth m
  unfold positionRigidityBlockExponent
  linarith

lemma positionRigidityEnergyExponent_pos (m : ℕ) :
    0 < positionRigidityEnergyExponent m := by
  unfold positionRigidityEnergyExponent
  exact div_pos (weakSeparationExponent_pos m) (by norm_num)

lemma positionRigidityGoodThresholdExponent_pos (m : ℕ) :
    0 < positionRigidityGoodThresholdExponent m := by
  unfold positionRigidityGoodThresholdExponent
  exact div_pos (weakSeparationExponent_pos m) (by norm_num)

lemma positionRigidity_dilation_lt_block (m : ℕ) :
    positionRigidityDilationExponent m < positionRigidityBlockExponent m := by
  have hs := weakSeparationExponent_pos m
  unfold positionRigidityDilationExponent positionRigidityDilationLossExponent
    positionRigidityBlockExponent
  linarith

lemma positionRigidity_propagation_lt_block
    {m : ℕ} (hm : 0 < m) :
    rigidityPropagationExponent m + 1 / 20 <
      positionRigidityBlockExponent m := by
  have h := rigidity_propagation_dirichlet_lt_block hm
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have heq : ((2 * m : ℕ) : ℝ) * rigidityDirichletExponent m =
      1 / 20 := by
    unfold rigidityDirichletExponent
    push_cast
    field_simp
    ring
  rw [heq] at h
  have hs := weakSeparationExponent_le_ten_thousandth m
  change rigidityPropagationExponent m + 1 / 20 < 99 / 100 at h
  unfold positionRigidityBlockExponent
  linarith

lemma positionRigidity_good_block_margin (m : ℕ) :
    positionRigidityBlockExponent m + positionRigidityEnergyExponent m +
        2 * positionRigidityGoodThresholdExponent m < 1 := by
  have hs := weakSeparationExponent_pos m
  unfold positionRigidityBlockExponent positionRigidityEnergyExponent
    positionRigidityGoodThresholdExponent
  linarith

lemma positionRigidity_position_demand_margin_from_eighth
    {m : ℕ} (hm : 0 < m) :
    2 * (1 - positionRigidityBlockExponent m) + 1 / 4 +
        positionRigidityEnergyExponent m <
      positionRigidityBlockExponent m -
        4 * (rigidityDifferenceOrder m : ℕ) *
          rigidityEpsilonExponent m -
        4 * (phaseTwistCount m : ℕ) *
          positionRigidityGapLossExponent m := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hell : ((phaseTwistCount m : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
    exact_mod_cast phaseTwistCount_le_two_mul m
  have hspos := weakSeparationExponent_pos m
  have hsbound := weakSeparationExponent_le_ten_thousandth m
  have heps :
      4 * (rigidityDifferenceOrder m : ℝ) * rigidityEpsilonExponent m =
        1 / 250 := by
    unfold rigidityDifferenceOrder rigidityEpsilonExponent
    push_cast
    field_simp
    ring
  have hgap :
      4 * (phaseTwistCount m : ℝ) * positionRigidityGapLossExponent m ≤
        24 * (m : ℝ) * weakSeparationExponent m := by
    unfold positionRigidityGapLossExponent
      positionRigidityDilationLossExponent
    nlinarith
  have hmsep :
      (m : ℝ) * weakSeparationExponent m ≤ 1 / 10000 := by
    unfold weakSeparationExponent
    have hden : (0 : ℝ) < 10000 * ((m : ℝ) + 1) ^ 2 := by positivity
    rw [show (m : ℝ) * (1 / (10000 * ((m : ℝ) + 1) ^ 2)) =
        (m : ℝ) / (10000 * ((m : ℝ) + 1) ^ 2) by ring]
    rw [div_le_iff₀ hden]
    field_simp
    nlinarith [sq_nonneg (m : ℝ)]
  rw [heps]
  unfold positionRigidityBlockExponent positionRigidityEnergyExponent
  have hgap' :
      4 * (phaseTwistCount m : ℝ) * positionRigidityGapLossExponent m ≤
        24 / 10000 := hgap.trans (by nlinarith)
  push_cast
  nlinarith

noncomputable def positionRigidityFourierExponent (m : ℕ) : ℝ :=
  rigidityFourierExponent m - 1

noncomputable def positionRigidityBlockScale (m n : ℕ) : ℕ :=
  ⌊rigidityPower n (positionRigidityBlockExponent m)⌋₊

noncomputable def positionRigidityCoreScale (m n : ℕ) : ℕ :=
  ⌊rigidityPower n (positionRigidityBlockExponent m) / 10⌋₊

noncomputable def positionRigidityEnergyScale (m n : ℕ) : ℝ :=
  rigidityPower n (positionRigidityEnergyExponent m)

noncomputable def positionRigidityGoodThresholdScale (m n : ℕ) : ℝ :=
  rigidityPower n (-positionRigidityGoodThresholdExponent m)

noncomputable def positionRigidityLocationScale (m n : ℕ) : ℝ :=
  20 * rigidityPower n (weakSeparationExponent m)

lemma positionRigidityBlockScale_cast_upper (m n : ℕ) :
    (positionRigidityBlockScale m n : ℝ) ≤
      rigidityPower n (positionRigidityBlockExponent m) :=
  natFloor_rigidityPower_upper n _

lemma positionRigidityCoreScale_cast_upper (m n : ℕ) :
    (positionRigidityCoreScale m n : ℝ) ≤
      rigidityPower n (positionRigidityBlockExponent m) / 10 := by
  unfold positionRigidityCoreScale
  exact Nat.floor_le
    (div_nonneg (rigidityPower_nonneg n _) (by norm_num))

lemma eventually_half_positionRigidityBlockScale (m : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      rigidityPower n (positionRigidityBlockExponent m) / 2 ≤
        (positionRigidityBlockScale m n : ℝ) :=
  eventually_half_rigidityPower_le_natFloor
    (positionRigidityBlockExponent_pos m)

lemma eventually_half_positionRigidityCoreScale (m : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      rigidityPower n (positionRigidityBlockExponent m) / 20 ≤
        (positionRigidityCoreScale m n : ℝ) := by
  have hlarge := (tendsto_rigidityPower_atTop
    (positionRigidityBlockExponent_pos m)).eventually
      (eventually_ge_atTop (20 : ℝ))
  filter_upwards [hlarge] with n hn
  have hfloor := Nat.lt_floor_add_one
    (rigidityPower n (positionRigidityBlockExponent m) / 10)
  change rigidityPower n (positionRigidityBlockExponent m) / 20 ≤
    ((⌊rigidityPower n (positionRigidityBlockExponent m) / 10⌋₊ : ℕ) : ℝ)
  push_cast at hfloor
  linarith

lemma tendsto_positionRigidityBlockScale_atTop (m : ℕ) :
    Tendsto (positionRigidityBlockScale m) atTop atTop := by
  unfold positionRigidityBlockScale
  exact tendsto_nat_floor_atTop.comp
    (tendsto_rigidityPower_atTop (positionRigidityBlockExponent_pos m))

lemma tendsto_positionRigidityCoreScale_atTop (m : ℕ) :
    Tendsto (positionRigidityCoreScale m) atTop atTop := by
  unfold positionRigidityCoreScale
  apply tendsto_nat_floor_atTop.comp
  have h := tendsto_rigidityPower_atTop (positionRigidityBlockExponent_pos m)
  have h' := Tendsto.atTop_mul_const (by norm_num : (0 : ℝ) < 1 / 10) h
  simpa [div_eq_mul_inv] using h'

lemma eventually_positionRigidity_scale_positivity
    {m : ℕ} (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop,
      0 < n ∧
      0 < rigidityDirichletScale m n ∧
      800 ≤ rigidityPropagationScale m n ∧
      800 ≤ weakDilationScale m n ∧
      0 < positionRigidityBlockScale m n ∧
      0 < positionRigidityCoreScale m n ∧
      0 < rigidityEpsilonScale m n ∧
      rigidityEpsilonScale m n < 1 / 16 ∧
      0 < positionRigidityGoodThresholdScale m n ∧
      0 < positionRigidityEnergyScale m n ∧
      0 ≤ positionRigidityLocationScale m n := by
  have hQ := (tendsto_rigidityDirichletScale_atTop hm).eventually
    (eventually_gt_atTop 0)
  have hR := (tendsto_rigidityPropagationScale_atTop hm).eventually
    (eventually_ge_atTop 800)
  have hq := (weakDilationScale_tendsto_atTop m).eventually
    (eventually_ge_atTop 800)
  have hW := (tendsto_positionRigidityBlockScale_atTop m).eventually
    (eventually_gt_atTop 0)
  have hH := (tendsto_positionRigidityCoreScale_atTop m).eventually
    (eventually_gt_atTop 0)
  have heps := (tendsto_rigidityEpsilonScale_zero hm).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))
  filter_upwards [Nat.eventually_pos, hQ, hR, hq, hW, hH, heps]
    with n hn hQ hR hq hW hH heps
  refine ⟨hn, hQ, hR, hq, hW, hH, ?_, heps, ?_, ?_, ?_⟩
  · exact rigidityPower_pos hn _
  · exact rigidityPower_pos hn _
  · exact rigidityPower_pos hn _
  · unfold positionRigidityLocationScale
    exact mul_nonneg (by norm_num) (rigidityPower_nonneg n _)

lemma weakDilationScale_cast_upper (m n : ℕ) :
    (weakDilationScale m n : ℝ) ≤
      rigidityPower n (1 - 2 * weakSeparationExponent m) :=
  natFloor_rigidityPower_upper n _

lemma eventually_half_weakDilationScale (m : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      rigidityPower n (1 - 2 * weakSeparationExponent m) / 2 ≤
        (weakDilationScale m n : ℝ) :=
  eventually_half_rigidityPower_le_natFloor (weakDilationExponent_pos m)

lemma eventually_positionRigidity_fit_condition
    {m : ℕ} (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop,
      2 * positionRigidityCoreScale m n +
          2 * (phaseTwistCount m * weakDilationScale m n) +
          2 * rigidityDifferenceOrder m *
            (rigidityPropagationScale m n *
              rigidityDirichletScale m n ^ (2 * m)) ≤
        positionRigidityBlockScale m n := by
  have hqsmall := eventually_const_mul_rigidityPower_le
    (40 * (phaseTwistCount m : ℝ))
    (1 - 2 * weakSeparationExponent m)
    (positionRigidityBlockExponent m)
    (by simpa [positionRigidityDilationExponent,
      positionRigidityDilationLossExponent] using
        positionRigidity_dilation_lt_block m)
  have hprodsmall := eventually_const_mul_rigidityPower_le
    (320000 * (rigidityDifferenceOrder m : ℝ))
    (rigidityPropagationExponent m + 1 / 20)
    (positionRigidityBlockExponent m)
    (positionRigidity_propagation_lt_block hm)
  filter_upwards [Nat.eventually_pos,
      eventually_half_positionRigidityBlockScale m,
      eventually_rigidityPropagationScale_cast_upper hm,
      hqsmall, hprodsmall]
    with n hn hWlower hRupper hqsmallN hprodsmallN
  let P : ℝ := rigidityPower n (positionRigidityBlockExponent m)
  have hP0 : 0 ≤ P := rigidityPower_nonneg n _
  have hH : (positionRigidityCoreScale m n : ℝ) ≤ P / 10 := by
    simpa [P] using positionRigidityCoreScale_cast_upper m n
  have hqUpper : (weakDilationScale m n : ℝ) ≤
      rigidityPower n (1 - 2 * weakSeparationExponent m) :=
    weakDilationScale_cast_upper m n
  have hqterm :
      (2 * (phaseTwistCount m * weakDilationScale m n) : ℕ) ≤
        P / 20 := by
    push_cast
    have hmul := mul_le_mul_of_nonneg_left hqUpper
      (by positivity : 0 ≤ 2 * (phaseTwistCount m : ℝ))
    have hscaled :
        2 * (phaseTwistCount m : ℝ) *
            rigidityPower n (1 - 2 * weakSeparationExponent m) ≤ P / 20 := by
      have := hqsmallN
      dsimp [P] at *
      nlinarith [rigidityPower_nonneg n
        (1 - 2 * weakSeparationExponent m)]
    simpa only [mul_assoc] using hmul.trans hscaled
  have hQpow := rigidityDirichletScale_pow_cast_upper hm hn
  have hQpow' :
      (rigidityDirichletScale m n : ℝ) ^ (2 * m) ≤
        rigidityPower n (1 / 20) := by
    simpa only [Nat.cast_pow] using hQpow
  have hRQ :
      ((rigidityPropagationScale m n *
          rigidityDirichletScale m n ^ (2 * m) : ℕ) : ℝ) ≤
        8000 * rigidityPower n
          (rigidityPropagationExponent m + 1 / 20) := by
    push_cast
    calc
      (rigidityPropagationScale m n : ℝ) *
          (rigidityDirichletScale m n : ℝ) ^ (2 * m) ≤
        (8000 * rigidityPower n (rigidityPropagationExponent m)) *
          rigidityPower n (1 / 20) :=
            mul_le_mul hRupper hQpow'
              (pow_nonneg (Nat.cast_nonneg _) _)
              (mul_nonneg (by norm_num)
                (rigidityPower_nonneg n (rigidityPropagationExponent m)))
      _ = 8000 * rigidityPower n
          (rigidityPropagationExponent m + 1 / 20) := by
            rw [rigidityPower_add hn]
            ring
  have hprodterm :
      ((2 * rigidityDifferenceOrder m *
          (rigidityPropagationScale m n *
            rigidityDirichletScale m n ^ (2 * m)) : ℕ) : ℝ) ≤
        P / 20 := by
    push_cast
    have hmul := mul_le_mul_of_nonneg_left hRQ
      (by positivity : 0 ≤ 2 * (rigidityDifferenceOrder m : ℝ))
    have hscaled :
        2 * (rigidityDifferenceOrder m : ℝ) *
            (8000 * rigidityPower n
              (rigidityPropagationExponent m + 1 / 20)) ≤ P / 20 := by
      have := hprodsmallN
      dsimp [P] at *
      nlinarith [rigidityPower_nonneg n
        (rigidityPropagationExponent m + 1 / 20)]
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, mul_assoc] using
      hmul.trans hscaled
  have hcast :
      ((2 * positionRigidityCoreScale m n +
          2 * (phaseTwistCount m * weakDilationScale m n) +
          2 * rigidityDifferenceOrder m *
            (rigidityPropagationScale m n *
              rigidityDirichletScale m n ^ (2 * m)) : ℕ) : ℝ) ≤
        (positionRigidityBlockScale m n : ℝ) := by
    push_cast
    have hW : P / 2 ≤ (positionRigidityBlockScale m n : ℝ) := by
      simpa [P] using hWlower
    calc
      2 * (positionRigidityCoreScale m n : ℝ) +
          2 * ((phaseTwistCount m : ℝ) *
            (weakDilationScale m n : ℝ)) +
          2 * (rigidityDifferenceOrder m : ℝ) *
            ((rigidityPropagationScale m n : ℝ) *
              (rigidityDirichletScale m n : ℝ) ^ (2 * m)) ≤
        2 * (P / 10) + P / 20 + P / 20 := by
          have hHterm : 2 * (positionRigidityCoreScale m n : ℝ) ≤
              2 * (P / 10) := by gcongr
          have hqterm' :
              2 * ((phaseTwistCount m : ℝ) *
                (weakDilationScale m n : ℝ)) ≤ P / 20 := by
            simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hqterm
          have hprodterm' :
              2 * (rigidityDifferenceOrder m : ℝ) *
                ((rigidityPropagationScale m n : ℝ) *
                  (rigidityDirichletScale m n : ℝ) ^ (2 * m)) ≤ P / 20 := by
            simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, mul_assoc] using
              hprodterm
          exact add_le_add (add_le_add hHterm hqterm') hprodterm'
      _ ≤ P / 2 := by linarith
      _ ≤ (positionRigidityBlockScale m n : ℝ) := hW
  exact_mod_cast hcast

lemma eventually_positionRigidity_location_condition (m : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ≤ positionRigidityLocationScale m n *
        positionRigidityCoreScale m n := by
  filter_upwards [Nat.eventually_pos,
      eventually_half_positionRigidityCoreScale m]
    with n hn hHlower
  have hloc0 : 0 ≤ positionRigidityLocationScale m n := by
    unfold positionRigidityLocationScale
    exact mul_nonneg (by norm_num) (rigidityPower_nonneg n _)
  calc
    (n : ℝ) = rigidityPower n 1 := by simp [rigidityPower]
    _ = (20 * rigidityPower n (weakSeparationExponent m)) *
          (rigidityPower n (positionRigidityBlockExponent m) / 20) := by
      symm
      calc
        (20 * rigidityPower n (weakSeparationExponent m)) *
            (rigidityPower n (positionRigidityBlockExponent m) / 20) =
          rigidityPower n (weakSeparationExponent m) *
            rigidityPower n (positionRigidityBlockExponent m) := by ring
        _ = rigidityPower n
            (weakSeparationExponent m + positionRigidityBlockExponent m) :=
          (rigidityPower_add hn _ _).symm
        _ = rigidityPower n 1 := by
          congr 1
          unfold positionRigidityBlockExponent
          ring
    _ ≤ positionRigidityLocationScale m n *
          (positionRigidityCoreScale m n : ℝ) := by
      unfold positionRigidityLocationScale
      exact mul_le_mul_of_nonneg_left hHlower hloc0

lemma positionRigidityEnergy_div_goodThreshold_sq
    {m n : ℕ} (hn : 0 < n) :
    positionRigidityEnergyScale m n /
        positionRigidityGoodThresholdScale m n ^ 2 =
      rigidityPower n
        (positionRigidityEnergyExponent m +
          2 * positionRigidityGoodThresholdExponent m) := by
  unfold positionRigidityEnergyScale positionRigidityGoodThresholdScale
  rw [rigidityPower_nat_pow hn]
  rw [show (-positionRigidityGoodThresholdExponent m) * (2 : ℕ) =
      -(2 * positionRigidityGoodThresholdExponent m) by push_cast; ring]
  calc
    rigidityPower n (positionRigidityEnergyExponent m) /
        rigidityPower n (-(2 * positionRigidityGoodThresholdExponent m)) =
      rigidityPower n
        (positionRigidityEnergyExponent m -
          (-(2 * positionRigidityGoodThresholdExponent m))) :=
      (Real.rpow_sub (by exact_mod_cast hn)
        (positionRigidityEnergyExponent m)
        (-(2 * positionRigidityGoodThresholdExponent m))).symm
    _ = rigidityPower n
        (positionRigidityEnergyExponent m +
          2 * positionRigidityGoodThresholdExponent m) := by
      congr 1
      ring

lemma eventually_positionRigidity_block_condition (m : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (positionRigidityBlockScale m n : ℝ) *
          (positionRigidityEnergyScale m n /
              positionRigidityGoodThresholdScale m n ^ 2 + 1) ≤
        2 * n + 1 := by
  let beta : ℝ := positionRigidityBlockExponent m +
    positionRigidityEnergyExponent m +
      2 * positionRigidityGoodThresholdExponent m
  have hbeta : beta < 1 := by
    simpa [beta] using positionRigidity_good_block_margin m
  have hbetaSmall := eventually_const_mul_rigidityPower_le 2 beta 1 hbeta
  have hb : positionRigidityBlockExponent m < (1 : ℝ) := by
    have hs := weakSeparationExponent_pos m
    unfold positionRigidityBlockExponent
    linarith
  have hbSmall := eventually_const_mul_rigidityPower_le
    2 (positionRigidityBlockExponent m) 1 hb
  filter_upwards [Nat.eventually_pos, hbetaSmall, hbSmall]
    with n hn hbetaN hbN
  have hW := positionRigidityBlockScale_cast_upper m n
  have hfactor0 : 0 ≤
      positionRigidityEnergyScale m n /
          positionRigidityGoodThresholdScale m n ^ 2 + 1 := by
    exact add_nonneg
      (div_nonneg (rigidityPower_nonneg n _) (sq_nonneg _)) (by norm_num)
  calc
    (positionRigidityBlockScale m n : ℝ) *
          (positionRigidityEnergyScale m n /
              positionRigidityGoodThresholdScale m n ^ 2 + 1) ≤
        rigidityPower n (positionRigidityBlockExponent m) *
          (positionRigidityEnergyScale m n /
              positionRigidityGoodThresholdScale m n ^ 2 + 1) :=
      mul_le_mul_of_nonneg_right hW hfactor0
    _ = rigidityPower n beta +
          rigidityPower n (positionRigidityBlockExponent m) := by
      rw [positionRigidityEnergy_div_goodThreshold_sq hn]
      dsimp [beta]
      have hp :
          rigidityPower n (positionRigidityBlockExponent m) *
              rigidityPower n
                (positionRigidityEnergyExponent m +
                  2 * positionRigidityGoodThresholdExponent m) =
            rigidityPower n
              (positionRigidityBlockExponent m +
                positionRigidityEnergyExponent m +
                  2 * positionRigidityGoodThresholdExponent m) := by
        calc
          _ = rigidityPower n
              (positionRigidityBlockExponent m +
                (positionRigidityEnergyExponent m +
                  2 * positionRigidityGoodThresholdExponent m)) :=
            (rigidityPower_add hn _ _).symm
          _ = _ := by congr 1 <;> ring
      rw [mul_add, mul_one, hp]
    _ ≤ rigidityPower n 1 / 2 + rigidityPower n 1 / 2 := by
      exact add_le_add (by nlinarith) (by nlinarith)
    _ = (n : ℝ) := by simp [rigidityPower]
    _ ≤ 2 * n + 1 := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith

lemma weakSpreadScale_div_eq_power
    {m n : ℕ} (hn : 0 < n) :
    weakSpreadScale m n / n =
      rigidityPower n (-weakSeparationExponent m - 1) := by
  unfold weakSpreadScale rigidityPower
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  simpa using (Real.rpow_sub hnreal (-weakSeparationExponent m) 1).symm

lemma weakSpread_div_le_smooth_div
    {m n : ℕ} (hn : 0 < n) :
    weakSpreadScale m n / n ≤ rigiditySmoothScale n / n := by
  rw [weakSpreadScale_div_eq_power hn, rigiditySmoothScale_div_eq_power hn]
  have hnbase : (1 : ℝ) ≤ n := by exact_mod_cast hn
  apply Real.rpow_le_rpow_of_exponent_le hnbase
  have hs := weakSeparationExponent_pos m
  norm_num [rigiditySmoothExponent]
  linarith

lemma positionRigidity_gap_exponent_identity (m : ℕ) :
    (1 - 2 * weakSeparationExponent m) +
        (-weakSeparationExponent m - 1) =
      -positionRigidityGapLossExponent m := by
  unfold positionRigidityGapLossExponent
    positionRigidityDilationLossExponent
  ring

lemma eventually_positionRigidity_individualDilationGap_lower (m : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      rigidityPower n (-positionRigidityGapLossExponent m) / 4000 ≤
        individualDilationGap (weakDilationScale m n)
          (min (rigiditySmoothScale n / n) (weakSpreadScale m n / n)) := by
  filter_upwards [Nat.eventually_pos, eventually_half_weakDilationScale m]
    with n hn hqLower
  let d : ℝ := positionRigidityGapLossExponent m
  let rho : ℝ := weakSpreadScale m n / n
  have hnbase : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmin : min (rigiditySmoothScale n / n)
      (weakSpreadScale m n / n) = rho := by
    rw [min_eq_right (weakSpread_div_le_smooth_div hn)]
  have hrho : rho = rigidityPower n (-weakSeparationExponent m - 1) := by
    simpa [rho] using weakSpreadScale_div_eq_power (m := m) hn
  have hrhoPos : 0 < rho := by rw [hrho]; exact rigidityPower_pos hn _
  have hproduct :
      rigidityPower n (-d) / 2 ≤
        (weakDilationScale m n : ℝ) * rho := by
    have hmul := mul_le_mul_of_nonneg_right hqLower hrhoPos.le
    have hid :
        rigidityPower n (1 - 2 * weakSeparationExponent m) / 2 * rho =
          rigidityPower n (-d) / 2 := by
      rw [hrho]
      rw [show rigidityPower n (1 - 2 * weakSeparationExponent m) / 2 *
          rigidityPower n (-weakSeparationExponent m - 1) =
          (rigidityPower n (1 - 2 * weakSeparationExponent m) *
            rigidityPower n (-weakSeparationExponent m - 1)) / 2 by ring]
      rw [← rigidityPower_add hn]
      rw [positionRigidity_gap_exponent_identity]
    rw [hid] at hmul
    exact hmul
  have hpowOne : rigidityPower n (-d) ≤ 1 := by
    unfold rigidityPower
    have hd : 0 < d := by
      dsimp [d]
      unfold positionRigidityGapLossExponent
      exact add_pos (positionRigidityDilationLossExponent_pos m)
        (weakSeparationExponent_pos m)
    simpa using Real.rpow_le_rpow_of_exponent_le hnbase
      (show -d ≤ 0 by linarith)
  have hleft : rigidityPower n (-d) / 16000 ≤ (1 / 64 : ℝ) := by
    nlinarith [rigidityPower_nonneg n (-d)]
  have hright : rigidityPower n (-d) / 16000 ≤
      (weakDilationScale m n : ℝ) * rho / 8000 := by
    nlinarith
  unfold individualDilationGap
  rw [hmin]
  change rigidityPower n (-d) / 4000 ≤
    4 * min (1 / 64) ((weakDilationScale m n : ℝ) * rho / 8000)
  have hminLower := le_min hleft hright
  nlinarith

lemma eventually_positionRigidity_unwrap_condition
    {m : ℕ} (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      |t| ≤ rigidityPower n (positionRigidityFourierExponent m) →
      (|t| / Real.pi) *
          ((4 * m : ℕ) *
            ((2 * Real.pi / rigidityDirichletScale m n) ^
                (2 * rigidityDifferenceOrder m) +
              2 * (rigidityDifferenceOrder m : ℝ) *
                ((rigidityDirichletScale m n ^ (2 * m) : ℕ) : ℝ) / n *
                (2 * Real.pi / rigidityDirichletScale m n) ^
                  (2 * rigidityDifferenceOrder m - 1))) +
        (2 : ℝ) ^ (2 * rigidityDifferenceOrder m) *
          positionRigidityGoodThresholdScale m n < 1 := by
  let C : ℝ := (2 : ℝ) ^ (2 * rigidityDifferenceOrder m)
  have hfour := eventually_const_mul_rigidityPower_le
    4 (positionRigidityFourierExponent m) (rigidityFourierExponent m) (by
      unfold positionRigidityFourierExponent
      linarith)
  have hnewSmall := eventually_const_mul_rigidityPower_le
    (2 * C) (-positionRigidityGoodThresholdExponent m) 0 (by
      have hg := positionRigidityGoodThresholdExponent_pos m
      linarith)
  filter_upwards [eventually_rigidity_unwrap_condition hm, hfour, hnewSmall]
    with n hold hfourN hnewSmallN
  intro t ht
  let A : ℝ :=
    ((4 * m : ℕ) : ℝ) *
      ((2 * Real.pi / rigidityDirichletScale m n) ^
          (2 * rigidityDifferenceOrder m) +
        2 * (rigidityDifferenceOrder m : ℝ) *
          ((rigidityDirichletScale m n ^ (2 * m) : ℕ) : ℝ) / n *
          (2 * Real.pi / rigidityDirichletScale m n) ^
            (2 * rigidityDifferenceOrder m - 1))
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hscaled : |4 * t| ≤ rigidityPower n (rigidityFourierExponent m) := by
    calc
      |4 * t| = 4 * |t| := by rw [abs_mul]; norm_num
      _ ≤ 4 * rigidityPower n (positionRigidityFourierExponent m) := by gcongr
      _ ≤ rigidityPower n (rigidityFourierExponent m) := hfourN
  have hold' := hold (4 * t) hscaled
  have holdThreshold0 :
      0 ≤ (2 : ℝ) ^ (2 * rigidityDifferenceOrder m) *
        rigidityGoodThresholdScale n := by
    unfold rigidityGoodThresholdScale
    exact mul_nonneg (pow_nonneg (by norm_num) _)
      (rigidityPower_nonneg n _)
  have hmain4 : (|4 * t| / Real.pi) * A < 1 := by
    apply lt_of_le_of_lt (le_add_of_nonneg_right holdThreshold0)
    simpa [A] using hold'
  have hmain : (|t| / Real.pi) * A < 1 / 4 := by
    have heq : (|4 * t| / Real.pi) * A =
        4 * ((|t| / Real.pi) * A) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      ring
    rw [heq] at hmain4
    nlinarith
  have hthreshold :
      C * positionRigidityGoodThresholdScale m n ≤ 1 / 2 := by
    have hpow0 := rigidityPower_nonneg n
      (-positionRigidityGoodThresholdExponent m)
    have hrewrite :
        positionRigidityGoodThresholdScale m n =
          rigidityPower n (-positionRigidityGoodThresholdExponent m) := rfl
    rw [hrewrite]
    simpa [rigidityPower] using (show
      C * rigidityPower n (-positionRigidityGoodThresholdExponent m) ≤ 1 / 2 by
        have : 2 * C *
            rigidityPower n (-positionRigidityGoodThresholdExponent m) ≤ 1 := by
          simpa [rigidityPower] using hnewSmallN
        nlinarith)
  change (|t| / Real.pi) * A +
      C * positionRigidityGoodThresholdScale m n < 1
  linarith

lemma eventually_positionRigidity_demand_condition
    {m : ℕ} (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      rigidityPower n (-1 / 8) ≤ |t| →
      phaseHighPositionBudget t (positionRigidityEnergyScale m n)
          (positionRigidityLocationScale m n) (phaseTwistCount m)
          (rigidityDifferenceOrder m) <
        phaseHighPositionDemand m (positionRigidityCoreScale m n)
          (rigidityDifferenceOrder m) (phaseTwistCount m)
          (rigidityEpsilonScale m n)
          (individualDilationGap (weakDilationScale m n)
            (min (rigiditySmoothScale n / n) (weakSpreadScale m n / n))) := by
  let k : ℕ := rigidityDifferenceOrder m
  let ell : ℕ := phaseTwistCount m
  let x : ℝ := rigidityEpsilonExponent m
  let d : ℝ := positionRigidityGapLossExponent m
  let b : ℝ := positionRigidityBlockExponent m
  let e : ℝ := positionRigidityEnergyExponent m
  let alphaBudget : ℝ := 2 * (1 - b) + 1 / 4 + e
  let alphaPosition : ℝ := b - 4 * (k : ℝ) * x - 4 * (ell : ℝ) * d
  let S : ℝ := Real.sqrt (1 / (8 * (m : ℝ)))
  let Cpos : ℝ := 18 * 20 ^ 2 * (36 : ℝ) ^ ell * Real.pi ^ 2 *
    (4 : ℝ) ^ (2 * k)
  let Dpos : ℝ := (1 / 20 : ℝ) *
    (S / (2 * (4000 : ℝ) ^ (2 * ell))) ^ 2
  have hS : 0 < S := by
    dsimp [S]
    have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have hDpos : 0 < Dpos := by dsimp [Dpos]; positivity
  have hposExp : alphaBudget < alphaPosition := by
    have h := positionRigidity_position_demand_margin_from_eighth hm
    simpa [alphaBudget, alphaPosition, b, e, k, ell, x, d] using h
  have hposPoly := eventually_const_mul_rigidityPower_le
    (2 * Cpos / Dpos) alphaBudget alphaPosition hposExp
  filter_upwards [Nat.eventually_pos,
      eventually_half_positionRigidityCoreScale m,
      eventually_positionRigidity_individualDilationGap_lower m,
      hposPoly]
    with n hn hHlower hdeltaLower hposPolyN
  intro t ht
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hnbase : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let delta : ℝ := individualDilationGap (weakDilationScale m n)
    (min (rigiditySmoothScale n / n) (weakSpreadScale m n / n))
  have hrho : 0 ≤ min (rigiditySmoothScale n / n)
      (weakSpreadScale m n / n) := by
    exact le_min
      (div_nonneg (rigidityPower_nonneg n _) (Nat.cast_nonneg n))
      (by
        unfold weakSpreadScale
        exact div_nonneg (rigidityPower_nonneg n _) (Nat.cast_nonneg n))
  have hdelta0 : 0 ≤ delta := individualDilationGap_nonneg _ hrho
  have hepsPow : rigidityEpsilonScale m n ^ (2 * k) =
      rigidityPower n (-(2 * (k : ℝ) * x)) := by
    rw [rigidityEpsilonScale_nat_pow hn]
    congr 1
    dsimp [x]
    push_cast
    ring
  have hdeltaPow :
      (rigidityPower n (-d) / 4000) ^ (2 * ell) ≤
        delta ^ (2 * ell) :=
    pow_le_pow_left₀
      (div_nonneg (rigidityPower_nonneg n _) (by norm_num))
      (by simpa [delta, d] using hdeltaLower) _
  have hdeltaPowEq :
      (rigidityPower n (-d) / 4000) ^ (2 * ell) =
        rigidityPower n (-(2 * (ell : ℝ) * d)) /
          (4000 : ℝ) ^ (2 * ell) := by
    rw [div_pow, rigidityPower_nat_pow hn]
    congr 2
    push_cast
    ring
  have hcore :
      (1 / (4000 : ℝ) ^ (2 * ell)) *
          rigidityPower n (-(2 * (k : ℝ) * x + 2 * (ell : ℝ) * d)) ≤
        rigidityEpsilonScale m n ^ (2 * k) * delta ^ (2 * ell) := by
    calc
      (1 / (4000 : ℝ) ^ (2 * ell)) *
          rigidityPower n (-(2 * (k : ℝ) * x + 2 * (ell : ℝ) * d)) =
        rigidityPower n (-(2 * (k : ℝ) * x)) *
          (rigidityPower n (-(2 * (ell : ℝ) * d)) /
            (4000 : ℝ) ^ (2 * ell)) := by
        have hp : rigidityPower n (-(2 * (k : ℝ) * x)) *
              rigidityPower n (-(2 * (ell : ℝ) * d)) =
            rigidityPower n (-(2 * (k : ℝ) * x + 2 * (ell : ℝ) * d)) := by
          calc
            _ = rigidityPower n
                (-(2 * (k : ℝ) * x) + -(2 * (ell : ℝ) * d)) :=
              (rigidityPower_add hn _ _).symm
            _ = _ := by ring_nf
        rw [← hp]
        ring
      _ = rigidityEpsilonScale m n ^ (2 * k) *
          (rigidityPower n (-d) / 4000) ^ (2 * ell) := by
        rw [hepsPow, hdeltaPowEq]
      _ ≤ rigidityEpsilonScale m n ^ (2 * k) * delta ^ (2 * ell) := by
        exact mul_le_mul_of_nonneg_left hdeltaPow
          (pow_nonneg (rigidityPower_nonneg n _) _)
  have hcoreSq :
      (1 / (4000 : ℝ) ^ (4 * ell)) *
          rigidityPower n (-(4 * (k : ℝ) * x + 4 * (ell : ℝ) * d)) ≤
        (rigidityEpsilonScale m n ^ (2 * k)) ^ 2 *
          (delta ^ (2 * ell)) ^ 2 := by
    have hsquare := pow_le_pow_left₀
      (mul_nonneg (by positivity) (rigidityPower_nonneg n _)) hcore 2
    calc
      (1 / (4000 : ℝ) ^ (4 * ell)) *
          rigidityPower n (-(4 * (k : ℝ) * x + 4 * (ell : ℝ) * d)) =
        ((1 / (4000 : ℝ) ^ (2 * ell)) *
          rigidityPower n
            (-(2 * (k : ℝ) * x + 2 * (ell : ℝ) * d))) ^ 2 := by
        rw [mul_pow]
        rw [rigidityPower_nat_pow hn]
        congr 2 <;> push_cast <;> ring
      _ ≤ (rigidityEpsilonScale m n ^ (2 * k) *
          delta ^ (2 * ell)) ^ 2 := hsquare
      _ = (rigidityEpsilonScale m n ^ (2 * k)) ^ 2 *
          (delta ^ (2 * ell)) ^ 2 := by ring
  have hpi : (Real.pi / |t|) ^ 2 ≤
      Real.pi ^ 2 * rigidityPower n (1 / 4) := by
    let p : ℝ := rigidityPower n (1 / 8)
    have hp : 0 < p := rigidityPower_pos hn _
    have hneg : rigidityPower n (-1 / 8) = 1 / p := by
      dsimp [p, rigidityPower]
      rw [show (-1 / 8 : ℝ) = -(1 / 8) by ring,
        Real.rpow_neg (by exact_mod_cast hn.le)]
      simp [one_div]
    have htpos : 0 < |t| :=
      (rigidityPower_pos hn (-1 / 8)).trans_le ht
    have hinv : 1 / |t| ≤ p := by
      have hone := one_div_le_one_div_of_le
        (rigidityPower_pos hn (-1 / 8)) ht
      rw [hneg] at hone
      simpa [one_div, hp.ne'] using hone
    have hdiv : Real.pi / |t| ≤ Real.pi * p := by
      simpa [div_eq_mul_inv, one_div] using
        (mul_le_mul_of_nonneg_left hinv Real.pi_pos.le)
    calc
      (Real.pi / |t|) ^ 2 ≤ (Real.pi * p) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hdiv 2
      _ = Real.pi ^ 2 * rigidityPower n (1 / 4) := by
        rw [mul_pow]
        dsimp [p]
        rw [rigidityPower_nat_pow hn]
        congr 2
        push_cast
        ring
  have hJone : 1 ≤ positionRigidityLocationScale m n := by
    unfold positionRigidityLocationScale
    have hp : 1 ≤ rigidityPower n (weakSeparationExponent m) :=
      Real.one_le_rpow hnbase (weakSeparationExponent_pos m).le
    nlinarith
  have hJfactor :
      2 + 4 * (positionRigidityLocationScale m n + 1) ^ 2 ≤
        18 * positionRigidityLocationScale m n ^ 2 := by
    nlinarith [sq_nonneg (positionRigidityLocationScale m n - 1)]
  have hJsq : positionRigidityLocationScale m n ^ 2 =
      20 ^ 2 * rigidityPower n (2 * (1 - b)) := by
    unfold positionRigidityLocationScale
    rw [mul_pow, rigidityPower_nat_pow hn]
    congr 2
    dsimp [b]
    unfold positionRigidityBlockExponent
    push_cast
    ring
  have hbudget :
      phaseHighPositionBudget t (positionRigidityEnergyScale m n)
          (positionRigidityLocationScale m n) ell k ≤
        Cpos * rigidityPower n alphaBudget := by
    unfold phaseHighPositionBudget
    calc
      (2 + 4 * (positionRigidityLocationScale m n + 1) ^ 2) *
          (36 : ℝ) ^ ell *
          ((Real.pi / |t|) ^ 2 * (4 : ℝ) ^ (2 * k) *
            positionRigidityEnergyScale m n) ≤
        (18 * positionRigidityLocationScale m n ^ 2) *
          (36 : ℝ) ^ ell *
          ((Real.pi ^ 2 * rigidityPower n (1 / 4)) *
            (4 : ℝ) ^ (2 * k) * positionRigidityEnergyScale m n) := by
        gcongr
        · unfold positionRigidityEnergyScale
          exact mul_nonneg
            (mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num) _))
            (rigidityPower_nonneg n _)
        · unfold positionRigidityEnergyScale
          exact rigidityPower_nonneg n _
      _ = Cpos * rigidityPower n alphaBudget := by
        rw [hJsq]
        unfold positionRigidityEnergyScale
        have hp : rigidityPower n (2 * (1 - b)) *
              rigidityPower n (1 / 4) * rigidityPower n e =
            rigidityPower n alphaBudget := by
          dsimp [alphaBudget]
          rw [← rigidityPower_add hn, ← rigidityPower_add hn]
        calc
          _ = Cpos * (rigidityPower n (2 * (1 - b)) *
              rigidityPower n (1 / 4) * rigidityPower n e) := by
            dsimp [Cpos, e]
            ring
          _ = Cpos * rigidityPower n alphaBudget := by rw [hp]
  have hdemand :
      Dpos * rigidityPower n alphaPosition ≤
        phaseHighPositionDemand m (positionRigidityCoreScale m n) k ell
          (rigidityEpsilonScale m n) delta := by
    unfold phaseHighPositionDemand
    calc
      Dpos * rigidityPower n alphaPosition =
        (rigidityPower n b / 20) *
          ((S / 2) ^ 2 *
            ((1 / (4000 : ℝ) ^ (4 * ell)) *
              rigidityPower n
                (-(4 * (k : ℝ) * x + 4 * (ell : ℝ) * d)))) := by
        have hp : rigidityPower n b *
              rigidityPower n
                (-(4 * (k : ℝ) * x + 4 * (ell : ℝ) * d)) =
            rigidityPower n alphaPosition := by
          calc
            _ = rigidityPower n
                (b + -(4 * (k : ℝ) * x + 4 * (ell : ℝ) * d)) :=
              (rigidityPower_add hn _ _).symm
            _ = _ := by
              congr 1
              dsimp [alphaPosition]
              ring
        rw [← hp]
        dsimp [Dpos]
        ring
      _ ≤ (positionRigidityCoreScale m n : ℝ) *
          ((S / 2) ^ 2 *
            ((rigidityEpsilonScale m n ^ (2 * k)) ^ 2 *
              (delta ^ (2 * ell)) ^ 2)) := by
        have hsecond := mul_le_mul_of_nonneg_left hcoreSq (sq_nonneg (S / 2))
        exact mul_le_mul hHlower hsecond
          (mul_nonneg (sq_nonneg (S / 2))
            (mul_nonneg (by positivity) (rigidityPower_nonneg n _)))
          (Nat.cast_nonneg _)
      _ = (positionRigidityCoreScale m n : ℝ) *
          ((S * rigidityEpsilonScale m n ^ (2 * k) *
            delta ^ (2 * ell)) / 2) ^ 2 := by ring
  have hpoly : Cpos * rigidityPower n alphaBudget <
      Dpos * rigidityPower n alphaPosition := by
    have hhalf : Cpos * rigidityPower n alphaBudget ≤
        (Dpos / 2) * rigidityPower n alphaPosition := by
      calc
        Cpos * rigidityPower n alphaBudget =
            (Dpos / 2) * ((2 * Cpos / Dpos) *
              rigidityPower n alphaBudget) := by field_simp
        _ ≤ (Dpos / 2) * rigidityPower n alphaPosition :=
          mul_le_mul_of_nonneg_left hposPolyN (by positivity)
    have hstrict : (Dpos / 2) * rigidityPower n alphaPosition <
        Dpos * rigidityPower n alphaPosition := by
      have hp := rigidityPower_pos hn alphaPosition
      exact mul_lt_mul_of_pos_right
        (by nlinarith only [hDpos] : Dpos / 2 < Dpos) hp
    exact hhalf.trans_lt hstrict
  exact (hbudget.trans_lt hpoly).trans_le hdemand

theorem eventually_phaseLatticeEnergy_high_frequency_position
    {m : ℕ} (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop, ∀ (points : Fin m → ℝ)
        (u : PositionCoordinate m) (t : ℝ),
      phaseNormSq (positionPhaseEmbedding u) = 1 →
      (∀ r, IsSmooth n (rigiditySmoothScale n) (points r)) →
      IsSpread n (weakSpreadScale m n) points →
      rigidityPower n (-1 / 8) ≤ |t| →
      |t| ≤ rigidityPower n (positionRigidityFourierExponent m) →
      positionRigidityEnergyScale m n <
        phaseLatticeEnergy n points (positionPhaseEmbedding u) t := by
  filter_upwards [eventually_positionRigidity_scale_positivity hm,
      eventually_positionRigidity_fit_condition hm,
      eventually_positionRigidity_location_condition m,
      eventually_positionRigidity_block_condition m,
      eventually_positionRigidity_unwrap_condition hm,
      eventually_positionRigidity_demand_condition hm]
    with n hscales hfit hJsize hblock hunwrap hdemand
  rcases hscales with
    ⟨hn, hQ, hR, hq, hW, hH, heps, hepsSmall, ha, hE, hJ⟩
  intro points u t hu hsmooth hspread htLower htUpper
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : 0 < rigiditySmoothScale n := by
    unfold rigiditySmoothScale
    exact rigidityPower_pos hn _
  have hlam : 0 < weakSpreadScale m n := by
    unfold weakSpreadScale
    exact rigidityPower_pos hn _
  have hrho : 0 < min (rigiditySmoothScale n / n)
      (weakSpreadScale m n / n) :=
    lt_min (div_pos hK hnreal) (div_pos hlam hnreal)
  have ht : t ≠ 0 := by
    intro ht0
    subst t
    simp only [abs_zero] at htLower
    exact (not_le_of_gt (rigidityPower_pos hn (-1 / 8))) htLower
  refine phaseLatticeEnergy_high_frequency_position_rigidity
    n m (rigidityDirichletScale m n) (rigidityPropagationScale m n)
    (weakDilationScale m n) (rigidityDifferenceOrder m)
    (positionRigidityBlockScale m n) (positionRigidityCoreScale m n)
    hn hm hQ hR hq hW hH
    (rigiditySmoothScale n) (weakSpreadScale m n)
    (rigidityEpsilonScale m n) (positionRigidityGoodThresholdScale m n) t
    (positionRigidityEnergyScale m n) (positionRigidityLocationScale m n)
    points (positionPhaseEmbedding u) hu
    (phaseVelocityCoeff_positionPhaseEmbedding u)
    hsmooth hspread hrho
    (rigidityDirichletScale_pow_le_smooth hm hn) heps.le hepsSmall
    (rigidity_propagation_scale_condition hm hn) ha ht hblock hfit hJ
    hJsize (hunwrap t htUpper)
    (individualDilationGap_le_one (weakDilationScale m n)
      (min (rigiditySmoothScale n / n) (weakSpreadScale m n / n)))
    (hdemand t htLower)

noncomputable def positionUnit (u : PositionCoordinate m) :
    PositionCoordinate m :=
  fun r c ↦ u r c / Real.sqrt (phaseNormSq (positionPhaseEmbedding u))

lemma positionPhaseEmbedding_positionUnit (u : PositionCoordinate m) :
    positionPhaseEmbedding (positionUnit u) =
      phaseUnit (positionPhaseEmbedding u) := by
  funext r c
  fin_cases c <;>
    simp [positionPhaseEmbedding, positionUnit, phaseUnit]

theorem eventually_norm_positionCharFun_high_frequency
    {m : ℕ} (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop, ∀ (points : Fin m → ℝ)
        (u : PositionEuclidean m),
      0 < ‖u‖ →
      (∀ r, IsSmooth n (rigiditySmoothScale n) (points r)) →
      IsSpread n (weakSpreadScale m n) points →
      rigidityPower n (-1 / 8) ≤
        |normalizedPhaseFrequency n
          (positionPhaseEmbedding (euclideanToPosition u))| →
      |normalizedPhaseFrequency n
          (positionPhaseEmbedding (euclideanToPosition u))| ≤
        rigidityPower n (positionRigidityFourierExponent m) →
      ‖positionCharFun n points u‖ ≤
        Real.exp (-positionRigidityEnergyScale m n) := by
  filter_upwards [eventually_phaseLatticeEnergy_high_frequency_position hm]
    with n henergy
  intro points u hu hsmooth hspread htLower htUpper
  have hphase : 0 < phaseNormSq
      (positionPhaseEmbedding (euclideanToPosition u)) := by
    rw [phaseNormSq_positionPhaseEmbedding]
    simp [positionToEuclidean, euclideanToPosition]
    positivity
  rw [positionCharFun_eq_normalizedPhaseCharFun]
  apply norm_normalizedPhaseCharFun_le_exp_neg_of_phaseLatticeEnergy
    n points (positionPhaseEmbedding (euclideanToPosition u)) hphase
      (positionRigidityEnergyScale m n)
  rw [← positionPhaseEmbedding_positionUnit]
  exact (henergy points (positionUnit (euclideanToPosition u))
    (normalizedPhaseFrequency n
      (positionPhaseEmbedding (euclideanToPosition u)))
    (by
      rw [positionPhaseEmbedding_positionUnit]
      exact phaseNormSq_phaseUnit _ hphase)
    hsmooth hspread htLower htUpper).le

lemma normalizedPhaseFrequency_position_eq
    (n : ℕ) (u : PositionEuclidean m) :
    normalizedPhaseFrequency n
        (positionPhaseEmbedding (euclideanToPosition u)) =
      ‖u‖ / Real.sqrt (2 * n + 1 : ℝ) := by
  unfold normalizedPhaseFrequency
  rw [phaseNormSq_positionPhaseEmbedding]
  simp [positionToEuclidean, euclideanToPosition]

noncomputable def positionHighFourierRadius (m n : ℕ) : ℝ :=
  Real.sqrt (2 * n + 1 : ℝ) *
    rigidityPower n (positionRigidityFourierExponent m)

theorem eventually_norm_positionCharFun_mid_frequency
    {m : ℕ} (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop, ∀ (points : Fin m → ℝ)
        (u : PositionEuclidean m),
      (∀ r, IsSmooth n (rigiditySmoothScale n) (points r)) →
      IsSpread n (weakSpreadScale m n) points →
      phaseNoWrapRadius n m ≤ ‖u‖ →
      ‖u‖ ≤ positionHighFourierRadius m n →
      ‖positionCharFun n points u‖ ≤
        Real.exp (-positionRigidityEnergyScale m n) := by
  let c : ℝ := Real.pi / (16 * (m + 1 : ℕ))
  have hc : 0 < c := by dsimp [c]; positivity
  have hlower := eventually_rigidityPower_le_const_mul c
    (-1 / 8) 0 hc (by norm_num)
  filter_upwards [Nat.eventually_pos,
      eventually_norm_positionCharFun_high_frequency hm, hlower]
    with n hn hhigh hlowerN
  intro points u hsmooth hspread huLower huUpper
  have hsqrt : 0 < Real.sqrt (2 * n + 1 : ℝ) := by positivity
  have hnormPos : 0 < ‖u‖ := by
    have hR : 0 < phaseNoWrapRadius n m := by
      unfold phaseNoWrapRadius
      positivity
    exact hR.trans_le huLower
  have hfreq : normalizedPhaseFrequency n
      (positionPhaseEmbedding (euclideanToPosition u)) =
      ‖u‖ / Real.sqrt (2 * n + 1 : ℝ) :=
    normalizedPhaseFrequency_position_eq n u
  have hfreqPos : 0 < normalizedPhaseFrequency n
      (positionPhaseEmbedding (euclideanToPosition u)) := by
    rw [hfreq]
    positivity
  apply hhigh points u hnormPos hsmooth hspread
  · rw [abs_of_pos hfreqPos, hfreq]
    have hconstant : c ≤ ‖u‖ / Real.sqrt (2 * n + 1 : ℝ) := by
      rw [le_div_iff₀ hsqrt]
      calc
        c * Real.sqrt (2 * n + 1 : ℝ) = phaseNoWrapRadius n m := by
          unfold c phaseNoWrapRadius
          ring
        _ ≤ ‖u‖ := huLower
    have hpow0 : rigidityPower n 0 = 1 := by simp [rigidityPower]
    rw [hpow0] at hlowerN
    exact hlowerN.trans (by simpa using hconstant)
  · rw [abs_of_pos hfreqPos, hfreq]
    rw [div_le_iff₀ hsqrt]
    simpa [positionHighFourierRadius, mul_comm] using huUpper

lemma positionRigidityFourierExponent_pos
    {m : ℕ} (hm : 0 < m) :
    0 < positionRigidityFourierExponent m := by
  unfold positionRigidityFourierExponent rigidityFourierExponent
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  push_cast
  linarith

lemma eventually_phaseNoWrapRadius_le_positionHighFourierRadius
    {m : ℕ} (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop,
      phaseNoWrapRadius n m ≤ positionHighFourierRadius m n := by
  let c : ℝ := Real.pi / (16 * (m + 1 : ℕ))
  have hc : 0 < c := by dsimp [c]; positivity
  have hlarge := (tendsto_rigidityPower_atTop
    (positionRigidityFourierExponent_pos hm)).eventually
      (eventually_ge_atTop c)
  filter_upwards [hlarge] with n hn
  have hsqrt0 : 0 ≤ Real.sqrt (2 * n + 1 : ℝ) := Real.sqrt_nonneg _
  calc
    phaseNoWrapRadius n m =
        Real.sqrt (2 * n + 1 : ℝ) * c := by
      unfold phaseNoWrapRadius c
      ring
    _ ≤ Real.sqrt (2 * n + 1 : ℝ) *
        rigidityPower n (positionRigidityFourierExponent m) :=
      mul_le_mul_of_nonneg_left hn hsqrt0
    _ = positionHighFourierRadius m n := by
      unfold positionHighFourierRadius
      rfl

theorem eventually_positionCharFun_integral_le_weakSpread
    {m : ℕ} (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop, ∀ (points : Fin m → ℝ) (gamma sigma : ℝ),
      0 < gamma →
      0 < sigma →
      HasPhaseCovarianceLower n points gamma →
      (∀ r, IsSmooth n (rigiditySmoothScale n) (points r)) →
      IsSpread n (weakSpreadScale m n) points →
      (∫ u : PositionEuclidean m,
        Real.exp (-(sigma ^ 2 / 2) * ‖u‖ ^ 2) *
          ‖positionCharFun n points u‖) ≤
        (Real.pi / (gamma / Real.pi ^ 2)) ^ m +
          Real.exp (-positionRigidityEnergyScale m n) *
            (2 * Real.pi / sigma ^ 2) ^ m +
          Real.exp (-(sigma ^ 2 / 4) *
              positionHighFourierRadius m n ^ 2) *
            (Real.pi / (sigma ^ 2 / 4)) ^ m := by
  filter_upwards [eventually_norm_positionCharFun_mid_frequency hm,
      eventually_phaseNoWrapRadius_le_positionHighFourierRadius hm]
    with n hhigh hRadii
  intro points gamma sigma hgamma hsigma hcov hsmooth hspread
  let f : PositionEuclidean m → ℝ := fun u ↦
    Real.exp (-(sigma ^ 2 / 2) * ‖u‖ ^ 2) *
      ‖positionCharFun n points u‖
  let g : PositionEuclidean m → ℝ := fun u ↦
    Real.exp (-positionRigidityEnergyScale m n) *
      Real.exp (-(sigma ^ 2 / 2) * ‖u‖ ^ 2)
  let B0 : Set (PositionEuclidean m) :=
    Metric.ball 0 (phaseNoWrapRadius n m)
  let B1 : Set (PositionEuclidean m) :=
    Metric.ball 0 (positionHighFourierRadius m n)
  have hf : Integrable f := by
    have h := (integrable_positionFourier_charFun
      n points sigma hsigma (0 : PositionEuclidean m)).norm
    apply h.congr
    filter_upwards [] with u
    dsimp [f]
    rw [norm_mul, norm_positionFourierMultiplier]
  have hc : 0 < sigma ^ 2 / 2 := by positivity
  have hgauss : Integrable (fun u : PositionEuclidean m ↦
      Real.exp (-(sigma ^ 2 / 2) * ‖u‖ ^ 2)) :=
    integrable_rexp_neg_mul_position_norm_sq m _ hc
  have hg : Integrable g := hgauss.const_mul _
  have hB0meas : MeasurableSet B0 := by
    dsimp [B0]
    exact Metric.isOpen_ball.measurableSet
  have hB1meas : MeasurableSet B1 := by
    dsimp [B1]
    exact Metric.isOpen_ball.measurableSet
  have hsubset : B0 ⊆ B1 := by
    intro u hu
    have hunorm : ‖u‖ < phaseNoWrapRadius n m := by
      simpa [B0, Metric.mem_ball, dist_zero_right] using hu
    have : ‖u‖ < positionHighFourierRadius m n := hunorm.trans_le hRadii
    simpa [B1, Metric.mem_ball, dist_zero_right] using this
  have hlow : (∫ u in B0, f u) ≤
      (Real.pi / (gamma / Real.pi ^ 2)) ^ m := by
    let h : PositionEuclidean m → ℝ := fun u ↦
      Real.exp (-(gamma / Real.pi ^ 2) * ‖u‖ ^ 2)
    have hcoef : 0 < gamma / Real.pi ^ 2 := by positivity
    have hh : Integrable h := by
      simpa [h] using integrable_rexp_neg_mul_position_norm_sq m _ hcoef
    calc
      (∫ u in B0, f u) ≤ ∫ u in B0, h u := by
        apply setIntegral_mono_on hf.integrableOn hh.integrableOn
          Metric.isOpen_ball.measurableSet
        intro u hu
        have huR : ‖u‖ ≤ phaseNoWrapRadius n m :=
          (mem_ball_zero_iff.mp hu).le
        have hchar := norm_positionCharFun_le_gaussian_of_covariance
          n points gamma hcov u huR
        have hweight : Real.exp (-(sigma ^ 2 / 2) * ‖u‖ ^ 2) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          exact mul_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr (by positivity)) (sq_nonneg _)
        dsimp [f, h]
        calc
          _ ≤ 1 * Real.exp (-(gamma / Real.pi ^ 2 * ‖u‖ ^ 2)) :=
            mul_le_mul hweight hchar (norm_nonneg _) zero_le_one
          _ = _ := by congr 1 <;> ring
      _ ≤ ∫ u, h u := setIntegral_le_integral hh
        (Eventually.of_forall fun u ↦ by dsimp [h]; positivity)
      _ = (Real.pi / (gamma / Real.pi ^ 2)) ^ m := by
        dsimp [h]
        rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hcoef]
        rw [finrank_positionEuclidean]
        rw [show ((2 * m : ℕ) : ℝ) / 2 = (m : ℕ) by push_cast; ring,
          Real.rpow_natCast]
  have hmid : (∫ u in B1 \ B0, f u) ≤
      Real.exp (-positionRigidityEnergyScale m n) *
        (2 * Real.pi / sigma ^ 2) ^ m := by
    calc
      (∫ u in B1 \ B0, f u) ≤ ∫ u in B1 \ B0, g u := by
        apply setIntegral_mono_on hf.integrableOn hg.integrableOn
          (hB1meas.diff hB0meas)
        intro u hu
        have huUpper : ‖u‖ ≤ positionHighFourierRadius m n := by
          have := (mem_ball_zero_iff.mp hu.1).le
          exact this
        have huLower : phaseNoWrapRadius n m ≤ ‖u‖ := by
          have : ¬ ‖u‖ < phaseNoWrapRadius n m := by
            simpa [B0, Metric.mem_ball, dist_zero_right] using hu.2
          exact le_of_not_gt this
        have hchar := hhigh points u hsmooth hspread huLower huUpper
        dsimp [f, g]
        calc
          _ ≤ Real.exp (-(sigma ^ 2 / 2) * ‖u‖ ^ 2) *
              Real.exp (-positionRigidityEnergyScale m n) :=
            mul_le_mul_of_nonneg_left hchar (Real.exp_pos _).le
          _ = _ := by ring
      _ ≤ ∫ u, g u := setIntegral_le_integral hg
        (Eventually.of_forall fun u ↦ by dsimp [g]; positivity)
      _ = Real.exp (-positionRigidityEnergyScale m n) *
          (2 * Real.pi / sigma ^ 2) ^ m := by
        dsimp [g]
        rw [integral_const_mul]
        rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hc]
        rw [finrank_positionEuclidean]
        rw [show ((2 * m : ℕ) : ℝ) / 2 = (m : ℕ) by push_cast; ring,
          Real.rpow_natCast]
        congr 2
        field_simp [hsigma.ne']
  have htail : (∫ u in B1ᶜ, f u) ≤
      Real.exp (-(sigma ^ 2 / 4) * positionHighFourierRadius m n ^ 2) *
        (Real.pi / (sigma ^ 2 / 4)) ^ m := by
    have h := positionCharFun_smoothingTail_le n m points sigma
      (positionHighFourierRadius m n) hsigma (by
        unfold positionHighFourierRadius
        exact mul_nonneg (Real.sqrt_nonneg _) (rigidityPower_nonneg n _))
    have hBc : B1ᶜ = {u : PositionEuclidean m |
        positionHighFourierRadius m n ≤ ‖u‖} := by
      ext u
      simp [B1, Metric.mem_ball]
    rw [hBc]
    simpa [f] using h
  have hsplitWhole := integral_add_compl
    (s := B1) hB1meas hf
  have hsplitB1 := setIntegral_union
    (f := f) (s := B0) (t := B1 \ B0) disjoint_sdiff_right
    (hB1meas.diff hB0meas)
    hf.integrableOn hf.integrableOn
  have hunion : B0 ∪ (B1 \ B0) = B1 := by
    ext u
    constructor
    · intro hu
      rcases hu with hu | hu
      · exact hsubset hu
      · exact hu.1
    · intro hu
      by_cases h0 : u ∈ B0
      · exact Or.inl h0
      · exact Or.inr ⟨hu, h0⟩
  rw [hunion] at hsplitB1
  calc
    (∫ u : PositionEuclidean m, f u) =
        (∫ u in B1, f u) + ∫ u in B1ᶜ, f u := hsplitWhole.symm
    _ = ((∫ u in B0, f u) + ∫ u in B1 \ B0, f u) +
        ∫ u in B1ᶜ, f u := by rw [hsplitB1]
    _ ≤ (Real.pi / (gamma / Real.pi ^ 2)) ^ m +
          (Real.exp (-positionRigidityEnergyScale m n) *
            (2 * Real.pi / sigma ^ 2) ^ m) +
          (Real.exp (-(sigma ^ 2 / 4) *
              positionHighFourierRadius m n ^ 2) *
            (Real.pi / (sigma ^ 2 / 4)) ^ m) := by
      exact add_le_add (add_le_add hlow hmid) htail
    _ = _ := by ring

noncomputable def positionWeakIntegralUpper
    (m n : ℕ) (gamma sigma : ℝ) : ℝ :=
  (Real.pi / (gamma / Real.pi ^ 2)) ^ m +
    Real.exp (-positionRigidityEnergyScale m n) *
      (2 * Real.pi / sigma ^ 2) ^ m +
    Real.exp (-(sigma ^ 2 / 4) * positionHighFourierRadius m n ^ 2) *
      (Real.pi / (sigma ^ 2 / 4)) ^ m

/-- Fourier inversion turns any integral majorant for the position
characteristic function into a Euclidean small-ball estimate. -/
lemma uniformProbability_positionBall_le_of_integral
    (n m : ℕ) (points : Fin m → ℝ) (sigma delta C : ℝ)
    (hsigma : 0 < sigma) (hdelta : 0 ≤ delta)
    (hintegral :
      (∫ u : PositionEuclidean m,
        Real.exp (-(sigma ^ 2 / 2) * ‖u‖ ^ 2) *
          ‖positionCharFun n points u‖) ≤ C) :
    uniformProbability (fun e : SignVector (2 * n) ↦
        ‖normalizedPositionEuclideanWalk n e points‖ ≤ delta) ≤
      C / ((2 * Real.pi / sigma ^ 2) ^ m *
        Real.exp (-(delta ^ 2 / (2 * sigma ^ 2)))) := by
  have hmass := uniformProbability_positionBall_mul_le_smoothedMassReal
    n points sigma delta hsigma hdelta (0 : PositionEuclidean m)
  have hscaled := mul_le_mul_of_nonneg_left hmass
    (show 0 ≤ (2 * Real.pi / sigma ^ 2) ^ m by positivity)
  have hfour := positionGaussianSmoothedMassReal_fourier_le
    n m points sigma hsigma (0 : PositionEuclidean m)
  have hupper : (2 * Real.pi / sigma ^ 2) ^ m *
        positionGaussianSmoothedMassReal n points sigma
          (0 : PositionEuclidean m) ≤ C := hfour.trans hintegral
  have hden : 0 < (2 * Real.pi / sigma ^ 2) ^ m *
      Real.exp (-(delta ^ 2 / (2 * sigma ^ 2))) := by positivity
  have hproduct :
      uniformProbability (fun e : SignVector (2 * n) ↦
          ‖normalizedPositionEuclideanWalk n e points‖ ≤ delta) *
          ((2 * Real.pi / sigma ^ 2) ^ m *
            Real.exp (-(delta ^ 2 / (2 * sigma ^ 2)))) ≤ C := by
    calc
      _ = (2 * Real.pi / sigma ^ 2) ^ m *
        (uniformProbability (fun e : SignVector (2 * n) ↦
          ‖normalizedPositionEuclideanWalk n e points‖ ≤ delta) *
          Real.exp (-(delta ^ 2 / (2 * sigma ^ 2)))) := by
        ring
      _ ≤ (2 * Real.pi / sigma ^ 2) ^ m *
        positionGaussianSmoothedMassReal n points sigma
          (0 : PositionEuclidean m) := by
        simpa only [sub_zero] using hscaled
      _ ≤ C := hupper
  exact (le_div_iff₀ hden).2 hproduct

lemma norm_normalizedPositionEuclideanWalk_sq
    (n : ℕ) (e : SignVector (2 * n)) (points : Fin m → ℝ) :
    ‖normalizedPositionEuclideanWalk n e points‖ ^ 2 =
      ∑ r : Fin m, ‖rescaledCenteredEval n e (points r)‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold normalizedPositionEuclideanWalk positionToEuclidean
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Fin.sum_univ_two]
  simp only [WithLp.ofLp_toLp]
  change (normalizedPhaseWalk n e points r 0) ^ 2 +
      (normalizedPhaseWalk n e points r 1) ^ 2 =
    ‖rescaledCenteredEval n e (points r)‖ ^ 2
  have hleft :
      (normalizedPhaseWalk n e points r 0) ^ 2 +
          (normalizedPhaseWalk n e points r 1) ^ 2 =
        Complex.normSq (phasePosition (normalizedPhaseWalk n e points) r) := by
    simp [phasePosition, Complex.normSq_apply, pow_two]
  rw [hleft]
  rw [← Complex.normSq_eq_norm_sq]
  rw [phasePosition_normalizedPhaseWalk]

/-- Joint truncated representatives force the entire normalized position
vector into the small Euclidean ball obtained by summing the one-site affine
position bounds. -/
lemma joint_truncatedLocalRepresentatives_positionBall
    (n : ℕ) (hn : 0 < n) (u velocityLower velocityUpper : ℝ)
    (hu : 0 ≤ u) (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper)
    (e : SignVector (2 * n))
    (s : Finset (Fin (localMeshSize n)))
    (hrep : ∀ a ∈ s,
      IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a) :
    ‖normalizedPositionEuclideanWalk n e (localSitesPoints s)‖ ≤
      Real.sqrt s.card *
        (localMeshHalfWidth n * velocityUpper + u / n) := by
  let R : ℝ := localMeshHalfWidth n * velocityUpper + u / n
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hR : 0 ≤ R := by
    dsimp [R]
    exact add_nonneg
      (mul_nonneg (by unfold localMeshHalfWidth; positivity) hvelocityUpper)
      (div_nonneg hu hnreal.le)
  have hregion := (joint_truncatedLocalRepresentatives_iff_region n hn u
    velocityLower velocityUpper hvelocityLower e s).1 hrep
  have hcoord : ∀ r : Fin s.card,
      ‖rescaledCenteredEval n e (localSitesPoints s r)‖ ≤ R := by
    intro r
    have hr := hregion r (Set.mem_univ r)
    change phaseToBlocks
        (normalizedPhaseEuclideanWalk n e (localSitesPoints s)) r ∈
      truncatedBlockRegion n u (localMeshHalfWidth n)
        velocityLower velocityUpper at hr
    have hcompact := truncatedBlockRegion_subset_compactProduct n hn u
      (localMeshHalfWidth n) velocityLower velocityUpper hu
      (by unfold localMeshHalfWidth; positivity) hvelocityLower hr
    have hfirst := hcompact.1
    rw [phaseToBlocks_normalizedPhaseEuclideanWalk] at hfirst
    simpa [Metric.mem_closedBall, dist_zero_right, R] using hfirst
  have hsquares : ∑ r : Fin s.card,
      ‖rescaledCenteredEval n e (localSitesPoints s r)‖ ^ 2 ≤
      s.card * R ^ 2 := by
    calc
      _ ≤ ∑ _r : Fin s.card, R ^ 2 := by
        apply Finset.sum_le_sum
        intro r _hr
        exact (sq_le_sq₀ (norm_nonneg _) hR).2 (hcoord r)
      _ = s.card * R ^ 2 := by simp
  have hnormsq :
      ‖normalizedPositionEuclideanWalk n e (localSitesPoints s)‖ ^ 2 ≤
        (Real.sqrt s.card * R) ^ 2 := by
    rw [norm_normalizedPositionEuclideanWalk_sq]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    push_cast
    simpa [R] using hsquares
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hR)).1
    hnormsq

noncomputable def weakPhaseCovarianceGamma (m n : ℕ) : ℝ :=
  phaseCovarianceGammaVariableL2 n m (weakCovarianceWindow n) 3
    (individualDilationGap (weakDilationScale m n)
      (min (rigiditySmoothScale n / n) (weakSpreadScale m n / n)))

noncomputable def positionCovarianceLossExponent (m : ℕ) : ℝ :=
  8 * (phaseTwistCount m : ℝ) * positionRigidityGapLossExponent m

noncomputable def positionCovarianceFloorExponent (m : ℕ) : ℝ :=
  1 / (50 * (m : ℝ))

lemma positionCovarianceFloorExponent_pos {m : ℕ} (hm : 0 < m) :
    0 < positionCovarianceFloorExponent m := by
  unfold positionCovarianceFloorExponent
  positivity

lemma positionCovarianceLoss_lt_floor {m : ℕ} (hm : 0 < m) :
    positionCovarianceLossExponent m < positionCovarianceFloorExponent m := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hell : ((phaseTwistCount m : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
    exact_mod_cast phaseTwistCount_le_two_mul m
  have hratio : (m : ℝ) ^ 2 < ((m : ℝ) + 1) ^ 2 := by nlinarith
  unfold positionCovarianceLossExponent positionRigidityGapLossExponent
    positionRigidityDilationLossExponent positionCovarianceFloorExponent
    weakSeparationExponent
  have hden : 0 < 10000 * ((m : ℝ) + 1) ^ 2 := by positivity
  have hmain : 48 * (m : ℝ) /
        (10000 * ((m : ℝ) + 1) ^ 2) < 1 / (50 * (m : ℝ)) := by
    rw [div_lt_div_iff₀ hden (mul_pos (by norm_num) hmreal)]
    nlinarith
  calc
    8 * (phaseTwistCount m : ℝ) *
          (2 * (1 / (10000 * ((m : ℝ) + 1) ^ 2)) +
            1 / (10000 * ((m : ℝ) + 1) ^ 2)) ≤
        48 * (m : ℝ) /
          (10000 * ((m : ℝ) + 1) ^ 2) := by
      rw [show 2 * (1 / (10000 * ((m : ℝ) + 1) ^ 2)) +
          1 / (10000 * ((m : ℝ) + 1) ^ 2) =
          3 / (10000 * ((m : ℝ) + 1) ^ 2) by ring]
      have hnonneg : 0 ≤ 3 / (10000 * ((m : ℝ) + 1) ^ 2) := by positivity
      calc
        _ ≤ 8 * (2 * (m : ℝ)) *
            (3 / (10000 * ((m : ℝ) + 1) ^ 2)) := by gcongr
        _ = _ := by ring
    _ < _ := hmain

lemma eventually_weakPhaseCovarianceGamma_lower
    {m : ℕ} (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop,
      rigidityPower n (-positionCovarianceFloorExponent m) ≤
        weakPhaseCovarianceGamma m n := by
  let L : ℕ := phaseTwistCount m
  let D : ℝ := phaseCovarianceL2Denominator m 3
  let C : ℝ := 9 * D * (4000 : ℝ) ^ (8 * L)
  have hD : 0 < D := by
    dsimp [D]
    exact phaseCovarianceL2Denominator_pos m hm 3
  have hC : 0 < C := by dsimp [C]; positivity
  have hexp := positionCovarianceLoss_lt_floor hm
  have habsorb := eventually_const_mul_rigidityPower_le C
    (-positionCovarianceFloorExponent m)
    (-positionCovarianceLossExponent m) (by linarith)
  filter_upwards [eventually_ge_atTop (2 : ℕ),
      eventually_positionRigidity_individualDilationGap_lower m,
      habsorb]
    with n hn hdelta habsorbN
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  let delta : ℝ := individualDilationGap (weakDilationScale m n)
    (min (rigiditySmoothScale n / n) (weakSpreadScale m n / n))
  have hdelta0 : 0 ≤ rigidityPower n
      (-positionRigidityGapLossExponent m) / 4000 :=
    div_nonneg (rigidityPower_nonneg n _) (by norm_num)
  have hdeltaPow := pow_le_pow_left₀ hdelta0 (by simpa [delta] using hdelta) (8 * L)
  have hpowEq :
      (rigidityPower n (-positionRigidityGapLossExponent m) / 4000) ^
          (8 * L) =
        rigidityPower n (-positionCovarianceLossExponent m) /
          (4000 : ℝ) ^ (8 * L) := by
    rw [div_pow, rigidityPower_nat_pow hnpos]
    congr 2
    unfold positionCovarianceLossExponent
    push_cast
    ring
  rw [hpowEq] at hdeltaPow
  have hwindow : (n : ℝ) / 3 ≤ weakCovarianceWindow n := by
    unfold weakCovarianceWindow
    push_cast
    have hfloor : n / 2 + 1 > n / 2 := Nat.lt_succ_self _
    have htwo : 2 * (n / 2) ≤ n := Nat.mul_div_le _ _
    have hlower : n ≤ 3 * (n / 2) := by omega
    have hlowerR : (n : ℝ) ≤ 3 * ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hlower
    linarith
  have hdenUpper : (2 * n + 1 : ℝ) ≤ 3 * n := by
    exact_mod_cast (show 2 * n + 1 ≤ 3 * n by omega)
  have hratio : (1 / 9 : ℝ) ≤
      (weakCovarianceWindow n : ℝ) / (2 * n + 1 : ℝ) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hgammaCore :
      rigidityPower n (-positionCovarianceLossExponent m) / C ≤
        weakPhaseCovarianceGamma m n := by
    unfold weakPhaseCovarianceGamma phaseCovarianceGammaVariableL2
    change rigidityPower n (-positionCovarianceLossExponent m) /
          (9 * D * (4000 : ℝ) ^ (8 * L)) ≤
      (weakCovarianceWindow n : ℝ) * delta ^ (8 * L) /
        (D * (2 * n + 1 : ℝ))
    have hdeltaScaled :
        rigidityPower n (-positionCovarianceLossExponent m) /
            (4000 : ℝ) ^ (8 * L) ≤ delta ^ (8 * L) := by
      simpa [delta] using hdeltaPow
    have hleft :
        rigidityPower n (-positionCovarianceLossExponent m) /
            (9 * D * (4000 : ℝ) ^ (8 * L)) =
          (1 / D) * ((1 / 9) *
            (rigidityPower n (-positionCovarianceLossExponent m) /
              (4000 : ℝ) ^ (8 * L))) := by ring
    have hright :
        (weakCovarianceWindow n : ℝ) * delta ^ (8 * L) /
            (D * (2 * n + 1 : ℝ)) =
          (1 / D) *
            (((weakCovarianceWindow n : ℝ) / (2 * n + 1 : ℝ)) *
              delta ^ (8 * L)) := by
      field_simp [hD.ne', (show (2 * n + 1 : ℝ) ≠ 0 by positivity)]
      <;> ring
    rw [hleft, hright]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul hratio hdeltaScaled
      (div_nonneg (rigidityPower_nonneg n _) (by positivity))
      (div_nonneg (Nat.cast_nonneg _) (by positivity))
  calc
    rigidityPower n (-positionCovarianceFloorExponent m) =
        (C * rigidityPower n (-positionCovarianceFloorExponent m)) / C := by
      field_simp
    _ ≤ rigidityPower n (-positionCovarianceLossExponent m) / C := by
      gcongr
    _ ≤ weakPhaseCovarianceGamma m n := hgammaCore

noncomputable def positionSmoothingScale (n : ℕ) : ℝ := (n : ℝ)⁻¹

noncomputable def positionRepresentativeRadius
    (m n : ℕ) (u velocityUpper : ℝ) : ℝ :=
  Real.sqrt m * (localMeshHalfWidth n * velocityUpper + u / n)

noncomputable def positionRepresentativeExponentBound
    (m : ℕ) (u velocityUpper : ℝ) : ℝ :=
  (m : ℝ) * (Real.pi * velocityUpper + u) ^ 2 / 2

lemma localMeshSize_cast_le_two_mul_sq (n : ℕ) (hn : 0 < n) :
    (localMeshSize n : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
  unfold localMeshSize
  push_cast
  nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]

lemma n_mul_localMeshHalfWidth_le_pi (n : ℕ) :
    (n : ℝ) * localMeshHalfWidth n ≤ Real.pi := by
  by_cases hn : n = 0
  · subst n
    simp [localMeshHalfWidth, Real.pi_pos.le]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hM : (n : ℝ) ^ 2 ≤ localMeshSize n := by
    unfold localMeshSize
    push_cast
    linarith
  unfold localMeshHalfWidth
  rw [show (n : ℝ) * (Real.pi * n / localMeshSize n) =
      Real.pi * ((n : ℝ) ^ 2 / localMeshSize n) by ring]
  have hratio : (n : ℝ) ^ 2 / localMeshSize n ≤ 1 := by
    rw [div_le_one (by exact_mod_cast localMeshSize_pos n :
      (0 : ℝ) < localMeshSize n)]
    exact hM
  nlinarith [Real.pi_pos]

lemma positionRepresentativeRadius_exponent_le
    (m n : ℕ) (hn : 0 < n) (u velocityUpper : ℝ)
    (hu : 0 ≤ u) (hvelocityUpper : 0 ≤ velocityUpper) :
    positionRepresentativeRadius m n u velocityUpper ^ 2 /
        (2 * positionSmoothingScale n ^ 2) ≤
      positionRepresentativeExponentBound m u velocityUpper := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hhalf : 0 ≤ localMeshHalfWidth n := by
    unfold localMeshHalfWidth
    positivity
  have hinside : 0 ≤ localMeshHalfWidth n * velocityUpper + u / n :=
    add_nonneg (mul_nonneg hhalf hvelocityUpper) (div_nonneg hu hnreal.le)
  have hscaled :
      (n : ℝ) * (localMeshHalfWidth n * velocityUpper + u / n) ≤
        Real.pi * velocityUpper + u := by
    calc
      (n : ℝ) * (localMeshHalfWidth n * velocityUpper + u / n) =
          ((n : ℝ) * localMeshHalfWidth n) * velocityUpper + u := by
        field_simp
      _ ≤ Real.pi * velocityUpper + u := by
        gcongr
        exact n_mul_localMeshHalfWidth_le_pi n
  have hright : 0 ≤ Real.pi * velocityUpper + u :=
    add_nonneg (mul_nonneg Real.pi_pos.le hvelocityUpper) hu
  have hsquare := (sq_le_sq₀ (mul_nonneg hnreal.le hinside) hright).2 hscaled
  unfold positionRepresentativeRadius positionSmoothingScale
    positionRepresentativeExponentBound
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  have heq :
      (m : ℝ) *
          (localMeshHalfWidth n * velocityUpper + u / n) ^ 2 /
            (2 * (n : ℝ)⁻¹ ^ 2) =
        (m : ℝ) *
          ((n : ℝ) *
            (localMeshHalfWidth n * velocityUpper + u / n)) ^ 2 / 2 := by
    field_simp [hnreal.ne']
  rw [heq]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsquare (Nat.cast_nonneg m)) (by norm_num)

lemma positionSmoothing_normalization_lower
    (m n : ℕ) (hn : 0 < n) :
    (localMeshSize n : ℝ) ^ m ≤
      (2 * Real.pi / positionSmoothingScale n ^ 2) ^ m := by
  apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ m
  have hsize := localMeshSize_cast_le_two_mul_sq n hn
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  unfold positionSmoothingScale
  rw [inv_pow, div_eq_mul_inv, inv_inv]
  have hpi : (2 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  calc
    (localMeshSize n : ℝ) ≤ 2 * (n : ℝ) ^ 2 := hsize
    _ ≤ (2 * Real.pi) * (n : ℝ) ^ 2 := by gcongr
    _ = 2 * Real.pi * (n : ℝ) ^ 2 := rfl

lemma positionCovarianceFloor_mul (m : ℕ) (hm : 0 < m) :
    positionCovarianceFloorExponent m * (m : ℝ) = 1 / 50 := by
  have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold positionCovarianceFloorExponent
  field_simp

lemma positionLowIntegralTerm_eq
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (Real.pi /
        (rigidityPower n (-positionCovarianceFloorExponent m) /
          Real.pi ^ 2)) ^ m =
      Real.pi ^ (3 * m) * rigidityPower n (1 / 50) := by
  have hgamma : 0 < rigidityPower n (-positionCovarianceFloorExponent m) :=
    rigidityPower_pos hn _
  rw [show Real.pi /
      (rigidityPower n (-positionCovarianceFloorExponent m) / Real.pi ^ 2) =
      Real.pi ^ 3 /
        rigidityPower n (-positionCovarianceFloorExponent m) by
    field_simp [hgamma.ne', Real.pi_ne_zero]
    ]
  rw [div_pow, pow_mul]
  have hinv :
      (rigidityPower n (-positionCovarianceFloorExponent m)) ^ m =
        rigidityPower n (-(positionCovarianceFloorExponent m * m)) := by
    rw [rigidityPower_nat_pow hn]
    congr 1
    push_cast
    ring
  rw [hinv, positionCovarianceFloor_mul m hm]
  unfold rigidityPower
  rw [Real.rpow_neg (by exact_mod_cast hn.le)]
  field_simp

lemma positionMidIntegralTerm_tendsto
    (m : ℕ) (u velocityUpper : ℝ) :
    Tendsto (fun n : ℕ ↦
      Real.exp (positionRepresentativeExponentBound m u velocityUpper) *
        (Real.exp (-positionRigidityEnergyScale m n) *
          (2 * Real.pi / positionSmoothingScale n ^ 2) ^ m))
      atTop (𝓝 0) := by
  let C : ℝ := Real.exp
      (positionRepresentativeExponentBound m u velocityUpper) *
    (2 * Real.pi) ^ m
  have hcore :=
    (tendsto_rigidityPower_mul_exp_neg_power_test
      (2 * (m : ℝ)) (positionRigidityEnergyExponent m) 1
      (positionRigidityEnergyExponent_pos m) (by norm_num)).const_mul C
  have hcore0 : Tendsto (fun n : ℕ ↦
      C * (rigidityPower n (2 * (m : ℝ)) *
        Real.exp (-1 * rigidityPower n
          (positionRigidityEnergyExponent m)))) atTop (𝓝 0) := by
    simpa using hcore
  apply hcore0.congr'
  filter_upwards [Nat.eventually_pos] with n hn
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hnorm :
      (2 * Real.pi / positionSmoothingScale n ^ 2) ^ m =
        (2 * Real.pi) ^ m * rigidityPower n (2 * (m : ℝ)) := by
    unfold positionSmoothingScale
    rw [inv_pow, div_eq_mul_inv, inv_inv, mul_pow]
    rw [← rigidityPower_nat_pow hn 2 m]
    congr 2
    simp [rigidityPower]
  rw [hnorm]
  unfold positionRigidityEnergyScale
  dsimp [C]
  ring

noncomputable def positionTailDecayExponent (m : ℕ) : ℝ :=
  2 * positionRigidityFourierExponent m - 1

lemma positionTailDecayExponent_pos (m : ℕ) :
    0 < positionTailDecayExponent m := by
  unfold positionTailDecayExponent positionRigidityFourierExponent
    rigidityFourierExponent
  push_cast
  linarith

lemma positionTailGaussianExponent_lower
    (m n : ℕ) (hn : 0 < n) :
    (positionSmoothingScale n ^ 2 / 4) *
        positionHighFourierRadius m n ^ 2 ≥
      (1 / 4 : ℝ) * rigidityPower n (positionTailDecayExponent m) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : Real.sqrt (2 * n + 1 : ℝ) ^ 2 = (2 * n + 1 : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hpow :
      rigidityPower n (positionRigidityFourierExponent m) ^ 2 =
        rigidityPower n (2 * positionRigidityFourierExponent m) := by
    rw [rigidityPower_nat_pow hn]
    congr 1
    ring
  have hfactor : (n : ℝ) ≤ 2 * n + 1 := by
    push_cast
    linarith
  have hnonneg :
      0 ≤ positionSmoothingScale n ^ 2 / 4 *
        rigidityPower n (positionRigidityFourierExponent m) ^ 2 := by
    positivity
  unfold positionHighFourierRadius
  rw [mul_pow, hsqrt, hpow]
  calc
    positionSmoothingScale n ^ 2 / 4 *
          ((2 * n + 1 : ℝ) *
            rigidityPower n (2 * positionRigidityFourierExponent m)) ≥
        positionSmoothingScale n ^ 2 / 4 *
          ((n : ℝ) *
            rigidityPower n (2 * positionRigidityFourierExponent m)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hfactor
          (rigidityPower_nonneg n _)) (by positivity)
    _ = (1 / 4 : ℝ) * rigidityPower n
          (2 * positionRigidityFourierExponent m - 1) := by
      unfold positionSmoothingScale
      rw [show ((n : ℝ)⁻¹) ^ 2 / 4 *
          ((n : ℝ) *
            rigidityPower n (2 * positionRigidityFourierExponent m)) =
          (1 / 4) *
            (rigidityPower n (-1) *
              rigidityPower n (2 * positionRigidityFourierExponent m)) by
        unfold rigidityPower
        rw [Real.rpow_neg_one]
        field_simp]
      rw [← rigidityPower_add hn]
      congr 2
      ring
    _ = _ := by rfl

lemma positionTailIntegralTerm_tendsto
    (m : ℕ) (u velocityUpper : ℝ) :
    Tendsto (fun n : ℕ ↦
      Real.exp (positionRepresentativeExponentBound m u velocityUpper) *
        (Real.exp (-(positionSmoothingScale n ^ 2 / 4) *
            positionHighFourierRadius m n ^ 2) *
          (Real.pi / (positionSmoothingScale n ^ 2 / 4)) ^ m))
      atTop (𝓝 0) := by
  let C : ℝ := Real.exp
      (positionRepresentativeExponentBound m u velocityUpper) *
    (4 * Real.pi) ^ m
  let core : ℕ → ℝ := fun n ↦
    C * (rigidityPower n (2 * (m : ℝ)) *
      Real.exp (-(1 / 4) *
        rigidityPower n (positionTailDecayExponent m)))
  have hcore : Tendsto core atTop (𝓝 0) := by
    simpa [core, C] using
      (tendsto_rigidityPower_mul_exp_neg_power_test
        (2 * (m : ℝ)) (positionTailDecayExponent m) (1 / 4)
        (positionTailDecayExponent_pos m) (by norm_num)).const_mul C
  apply squeeze_zero' (Eventually.of_forall fun n ↦ by positivity) _ hcore
  filter_upwards [Nat.eventually_pos] with n hn
  have hexp := positionTailGaussianExponent_lower m n hn
  have hexpBound :
      Real.exp (-(positionSmoothingScale n ^ 2 / 4) *
          positionHighFourierRadius m n ^ 2) ≤
        Real.exp (-(1 / 4) *
          rigidityPower n (positionTailDecayExponent m)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hnorm :
      (Real.pi / (positionSmoothingScale n ^ 2 / 4)) ^ m =
        (4 * Real.pi) ^ m * rigidityPower n (2 * (m : ℝ)) := by
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    unfold positionSmoothingScale
    rw [show Real.pi / (((n : ℝ)⁻¹) ^ 2 / 4) =
        (4 * Real.pi) * (n : ℝ) ^ 2 by
      field_simp [hnreal.ne']]
    rw [mul_pow, ← rigidityPower_nat_pow hn 2 m]
    congr 2
    simp [rigidityPower]
  rw [hnorm]
  dsimp [core, C]
  have hnonneg : 0 ≤ Real.exp
      (positionRepresentativeExponentBound m u velocityUpper) *
        ((4 * Real.pi) ^ m * rigidityPower n (2 * (m : ℝ))) := by
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) _)
        (rigidityPower_nonneg n _))
  calc
    _ = (Real.exp (positionRepresentativeExponentBound m u velocityUpper) *
          ((4 * Real.pi) ^ m * rigidityPower n (2 * (m : ℝ)))) *
        Real.exp (-(positionSmoothingScale n ^ 2 / 4) *
          positionHighFourierRadius m n ^ 2) := by ring
    _ ≤ (Real.exp (positionRepresentativeExponentBound m u velocityUpper) *
          ((4 * Real.pi) ^ m * rigidityPower n (2 * (m : ℝ)))) *
        Real.exp (-(1 / 4) *
          rigidityPower n (positionTailDecayExponent m)) :=
      mul_le_mul_of_nonneg_left hexpBound hnonneg
    _ = _ := by ring

lemma HasPhaseCovarianceLower.mono
    {n m : ℕ} {points : Fin m → ℝ} {gamma gamma' : ℝ}
    (hcov : HasPhaseCovarianceLower n points gamma)
    (hle : gamma' ≤ gamma) :
    HasPhaseCovarianceLower n points gamma' := by
  intro w
  have hnonneg : 0 ≤ (2 * n + 1 : ℝ) * phaseNormSq w :=
    mul_nonneg (by positivity) (phaseNormSq_nonneg w)
  have hcov' : gamma * ((2 * n + 1 : ℝ) * phaseNormSq w) ≤
      ∑ j : Fin (2 * n + 1), (phaseProjection n points w j) ^ 2 := by
    simpa only [mul_assoc] using hcov w
  have hmain := (mul_le_mul_of_nonneg_right hle hnonneg).trans hcov'
  simpa only [mul_assoc] using hmain

/-- A position-space representative event at a smooth, weakly separated
tuple has probability at most its Fourier majorant, with the mesh
normalization canceled explicitly. -/
theorem eventually_scaled_positionBall_probability_le_integralUpper
    {m : ℕ} (hm : 0 < m) (u velocityUpper : ℝ)
    (hu : 0 ≤ u) (hvelocityUpper : 0 ≤ velocityUpper) :
    ∀ᶠ n : ℕ in atTop, ∀ points : Fin m → ℝ,
      (∀ r, IsSmooth n (rigiditySmoothScale n) (points r)) →
      IsSpread n (weakSpreadScale m n) points →
      (localMeshSize n : ℝ) ^ m *
          uniformProbability (fun e : SignVector (2 * n) ↦
            ‖normalizedPositionEuclideanWalk n e points‖ ≤
              positionRepresentativeRadius m n u velocityUpper) ≤
        Real.exp (positionRepresentativeExponentBound m u velocityUpper) *
          positionWeakIntegralUpper m n
            (rigidityPower n (-positionCovarianceFloorExponent m))
            (positionSmoothingScale n) := by
  filter_upwards [Nat.eventually_pos,
      eventually_hasPhaseCovarianceLower_weak hm,
      eventually_weakPhaseCovarianceGamma_lower hm,
      eventually_positionCharFun_integral_le_weakSpread hm]
    with n hn hcovWeak hgammaFloor hfourier
  intro points hsmooth hspread
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hgamma : 0 < rigidityPower n
      (-positionCovarianceFloorExponent m) := rigidityPower_pos hn _
  have hsigma : 0 < positionSmoothingScale n := by
    unfold positionSmoothingScale
    positivity
  have hcov : HasPhaseCovarianceLower n points
      (rigidityPower n (-positionCovarianceFloorExponent m)) :=
    (hcovWeak points hsmooth hspread).mono hgammaFloor
  have hintegral := hfourier points
    (rigidityPower n (-positionCovarianceFloorExponent m))
    (positionSmoothingScale n) hgamma hsigma hcov hsmooth hspread
  have hdelta : 0 ≤ positionRepresentativeRadius m n u velocityUpper := by
    unfold positionRepresentativeRadius
    have hhalf : 0 ≤ localMeshHalfWidth n := by
      unfold localMeshHalfWidth
      positivity
    exact mul_nonneg (Real.sqrt_nonneg _)
      (add_nonneg (mul_nonneg hhalf hvelocityUpper)
        (div_nonneg hu hnreal.le))
  have hprob := uniformProbability_positionBall_le_of_integral
    n m points (positionSmoothingScale n)
      (positionRepresentativeRadius m n u velocityUpper)
      (positionWeakIntegralUpper m n
        (rigidityPower n (-positionCovarianceFloorExponent m))
        (positionSmoothingScale n))
      hsigma hdelta hintegral
  let probability : ℝ := uniformProbability (fun e : SignVector (2 * n) ↦
    ‖normalizedPositionEuclideanWalk n e points‖ ≤
      positionRepresentativeRadius m n u velocityUpper)
  let normalization : ℝ :=
    (2 * Real.pi / positionSmoothingScale n ^ 2) ^ m
  let exponent : ℝ :=
    positionRepresentativeRadius m n u velocityUpper ^ 2 /
      (2 * positionSmoothingScale n ^ 2)
  let upper : ℝ := positionWeakIntegralUpper m n
    (rigidityPower n (-positionCovarianceFloorExponent m))
    (positionSmoothingScale n)
  let B : ℝ := positionRepresentativeExponentBound m u velocityUpper
  have hnormalization : (localMeshSize n : ℝ) ^ m ≤ normalization := by
    simpa [normalization] using positionSmoothing_normalization_lower m n hn
  have hexponent : exponent ≤ B := by
    simpa [exponent, B] using positionRepresentativeRadius_exponent_le
      m n hn u velocityUpper hu hvelocityUpper
  have hdenExp : Real.exp (-B) ≤ Real.exp (-exponent) := by
    exact Real.exp_le_exp.mpr (neg_le_neg hexponent)
  have hden : 0 < normalization * Real.exp (-exponent) := by
    dsimp [normalization]
    positivity
  have hprob' : probability ≤ upper /
      (normalization * Real.exp (-exponent)) := by
    simpa [probability, normalization, exponent, upper] using hprob
  have hproduct : probability *
      (normalization * Real.exp (-exponent)) ≤ upper :=
    (le_div_iff₀ hden).mp hprob'
  have hsmallDen : (localMeshSize n : ℝ) ^ m * Real.exp (-B) ≤
      normalization * Real.exp (-exponent) := by
    exact mul_le_mul hnormalization hdenExp
      (Real.exp_pos _).le (by dsimp [normalization]; positivity)
  have hscaledProduct :
      ((localMeshSize n : ℝ) ^ m * probability) * Real.exp (-B) ≤ upper := by
    calc
      ((localMeshSize n : ℝ) ^ m * probability) * Real.exp (-B) =
          probability * ((localMeshSize n : ℝ) ^ m * Real.exp (-B)) := by ring
      _ ≤ probability * (normalization * Real.exp (-exponent)) :=
        mul_le_mul_of_nonneg_left hsmallDen
          (uniformProbability_nonneg _)
      _ ≤ upper := hproduct
  have hdivide : (localMeshSize n : ℝ) ^ m * probability ≤
      upper / Real.exp (-B) :=
    (le_div_iff₀ (Real.exp_pos _)).2 hscaledProduct
  calc
    _ = (localMeshSize n : ℝ) ^ m * probability := rfl
    _ ≤ upper / Real.exp (-B) := hdivide
    _ = Real.exp B * upper := by
      rw [Real.exp_neg, div_inv_eq_mul]
      ring
    _ = _ := by rfl

lemma eventually_positionWeakIntegralUpper_le_power
    {m : ℕ} (hm : 0 < m) (u velocityUpper : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (positionRepresentativeExponentBound m u velocityUpper) *
          positionWeakIntegralUpper m n
            (rigidityPower n (-positionCovarianceFloorExponent m))
            (positionSmoothingScale n) ≤
        rigidityPower n (1 / 20) := by
  let B : ℝ := positionRepresentativeExponentBound m u velocityUpper
  have hlow := eventually_const_mul_rigidityPower_le
    (Real.exp B * Real.pi ^ (3 * m)) (1 / 50) (1 / 25)
      (by norm_num)
  have hmid : ∀ᶠ n : ℕ in atTop,
      Real.exp B *
        (Real.exp (-positionRigidityEnergyScale m n) *
          (2 * Real.pi / positionSmoothingScale n ^ 2) ^ m) < 1 :=
    (positionMidIntegralTerm_tendsto m u velocityUpper).eventually
      (Iio_mem_nhds (by norm_num))
  have htail : ∀ᶠ n : ℕ in atTop,
      Real.exp B *
        (Real.exp (-(positionSmoothingScale n ^ 2 / 4) *
            positionHighFourierRadius m n ^ 2) *
          (Real.pi / (positionSmoothingScale n ^ 2 / 4)) ^ m) < 1 :=
    (positionTailIntegralTerm_tendsto m u velocityUpper).eventually
      (Iio_mem_nhds (by norm_num))
  have hsum := eventually_const_mul_rigidityPower_le
    3 (1 / 25) (1 / 20) (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlow, hmid, htail, hsum]
    with n hn hlowN hmidN htailN hsumN
  have hnpos : 0 < n := by omega
  have hpOne : 1 ≤ rigidityPower n (1 / 25) := by
    unfold rigidityPower
    exact Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hlowTerm :
      Real.exp B *
          (Real.pi /
            (rigidityPower n (-positionCovarianceFloorExponent m) /
              Real.pi ^ 2)) ^ m ≤
        rigidityPower n (1 / 25) := by
    rw [positionLowIntegralTerm_eq m n hm hnpos]
    simpa only [mul_assoc] using hlowN
  have hmidTerm :
      Real.exp B *
        (Real.exp (-positionRigidityEnergyScale m n) *
          (2 * Real.pi / positionSmoothingScale n ^ 2) ^ m) ≤
        rigidityPower n (1 / 25) := hmidN.le.trans hpOne
  have htailTerm :
      Real.exp B *
        (Real.exp (-(positionSmoothingScale n ^ 2 / 4) *
            positionHighFourierRadius m n ^ 2) *
          (Real.pi / (positionSmoothingScale n ^ 2 / 4)) ^ m) ≤
        rigidityPower n (1 / 25) := htailN.le.trans hpOne
  change Real.exp B *
      ((Real.pi /
          (rigidityPower n (-positionCovarianceFloorExponent m) /
            Real.pi ^ 2)) ^ m +
        Real.exp (-positionRigidityEnergyScale m n) *
          (2 * Real.pi / positionSmoothingScale n ^ 2) ^ m +
        Real.exp (-(positionSmoothingScale n ^ 2 / 4) *
            positionHighFourierRadius m n ^ 2) *
          (Real.pi / (positionSmoothingScale n ^ 2 / 4)) ^ m) ≤ _
  calc
    _ = Real.exp B *
          (Real.pi /
            (rigidityPower n (-positionCovarianceFloorExponent m) /
              Real.pi ^ 2)) ^ m +
        Real.exp B *
          (Real.exp (-positionRigidityEnergyScale m n) *
            (2 * Real.pi / positionSmoothingScale n ^ 2) ^ m) +
        Real.exp B *
          (Real.exp (-(positionSmoothingScale n ^ 2 / 4) *
              positionHighFourierRadius m n ^ 2) *
            (Real.pi / (positionSmoothingScale n ^ 2 / 4)) ^ m) := by ring
    _ ≤ rigidityPower n (1 / 25) + rigidityPower n (1 / 25) +
          rigidityPower n (1 / 25) := by gcongr
    _ = 3 * rigidityPower n (1 / 25) := by ring
    _ ≤ rigidityPower n (1 / 20) := hsumN

theorem eventually_scaled_positionBall_probability_le_power
    {m : ℕ} (hm : 0 < m) (u velocityUpper : ℝ)
    (hu : 0 ≤ u) (hvelocityUpper : 0 ≤ velocityUpper) :
    ∀ᶠ n : ℕ in atTop, ∀ points : Fin m → ℝ,
      (∀ r, IsSmooth n (rigiditySmoothScale n) (points r)) →
      IsSpread n (weakSpreadScale m n) points →
      (localMeshSize n : ℝ) ^ m *
          uniformProbability (fun e : SignVector (2 * n) ↦
            ‖normalizedPositionEuclideanWalk n e points‖ ≤
              positionRepresentativeRadius m n u velocityUpper) ≤
        rigidityPower n (1 / 20) := by
  filter_upwards [
      eventually_scaled_positionBall_probability_le_integralUpper
        hm u velocityUpper hu hvelocityUpper,
      eventually_positionWeakIntegralUpper_le_power hm u velocityUpper]
    with n hprob hupper
  intro points hsmooth hspread
  exact (hprob points hsmooth hspread).trans hupper

lemma eventually_smoothBadLocalSites_ratio_le_power :
    ∀ᶠ n : ℕ in atTop,
      ((smoothBadLocalSites n (rigiditySmoothScale n)).card : ℝ) /
          localMeshSize n ≤
        32 * rigidityPower n (-1 / 4) := by
  have hKtop : Tendsto rigiditySmoothScale atTop atTop := by
    unfold rigiditySmoothScale rigiditySmoothExponent
    exact tendsto_rigidityPower_atTop (by norm_num)
  have hKone : ∀ᶠ n : ℕ in atTop, 1 ≤ rigiditySmoothScale n :=
    hKtop.eventually (eventually_ge_atTop 1)
  filter_upwards [Nat.eventually_pos, hKone] with n hn hKn
  let K : ℝ := rigiditySmoothScale n
  let P : ℕ := Nat.floor K + 1
  let M : ℕ := localMeshSize n
  let X : ℝ := (K / n) * M
  let D : ℕ := Nat.floor X + 1
  have hK0 : 0 ≤ K := by dsimp [K]; exact rigidityPower_nonneg _ _
  have hraw := card_smoothBadLocalSites_le n hn K hK0
  have hraw' : (smoothBadLocalSites n K).card ≤
      P * ((2 * P) * (2 * D)) := by
    simpa [P, D, X, M] using hraw
  have hrawR : ((smoothBadLocalSites n K).card : ℝ) ≤
      (P : ℝ) * ((2 * P : ℕ) * (2 * D : ℕ)) := by
    exact_mod_cast hraw'
  have hP : (P : ℝ) ≤ 2 * K := by
    have hfloor := Nat.floor_le hK0
    push_cast
    dsimp [P]
    push_cast
    linarith
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hMreal : (0 : ℝ) < M := by exact_mod_cast localMeshSize_pos n
  have hMge : (n : ℝ) ≤ M := by
    dsimp [M, localMeshSize]
    push_cast
    nlinarith [sq_nonneg (n : ℝ), show (1 : ℝ) ≤ n by exact_mod_cast hn]
  have hMn : (1 : ℝ) ≤ (M : ℝ) / n :=
    (le_div_iff₀ hnreal).2 (by simpa using hMge)
  have hXeq : X = K * ((M : ℝ) / n) := by dsimp [X]; ring
  have hXone : 1 ≤ X := by
    rw [hXeq]
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ K * ((M : ℝ) / n) := mul_le_mul hKn hMn (by norm_num) hK0
  have hD : (D : ℝ) ≤ 2 * X := by
    have hfloor := Nat.floor_le (by positivity : 0 ≤ X)
    push_cast
    dsimp [D]
    push_cast
    linarith
  have h2P : ((2 * P : ℕ) : ℝ) ≤ 4 * K := by
    push_cast
    linarith
  have h2D : ((2 * D : ℕ) : ℝ) ≤ 4 * X := by
    push_cast
    linarith
  have hcard : ((smoothBadLocalSites n K).card : ℝ) ≤
      32 * K ^ 2 * X := by
    calc
      ((smoothBadLocalSites n K).card : ℝ) ≤
          (P : ℝ) * ((2 * P : ℕ) * (2 * D : ℕ)) := hrawR
      _ ≤ (2 * K) * ((4 * K) * (4 * X)) := by
        apply mul_le_mul hP
        · exact mul_le_mul h2P h2D (by positivity) (by positivity)
        · positivity
        · positivity
      _ = 32 * K ^ 2 * X := by ring
  change ((smoothBadLocalSites n K).card : ℝ) / M ≤ _
  calc
    ((smoothBadLocalSites n K).card : ℝ) / M ≤
        (32 * K ^ 2 * X) / M :=
      div_le_div_of_nonneg_right hcard hMreal.le
    _ = 32 * K ^ 3 / n := by
      rw [hXeq]
      field_simp [hMreal.ne', hnreal.ne']
    _ = 32 * rigidityPower n (-13 / 16) := by
      dsimp [K]
      rw [show 32 * rigiditySmoothScale n ^ 3 / (n : ℝ) =
        32 * (rigiditySmoothScale n ^ 3 / n) by ring]
      rw [rigiditySmoothScale_cube_div_eq hn]
    _ ≤ 32 * rigidityPower n (-1 / 4) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      unfold rigidityPower
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ n by omega)) (by norm_num)

lemma eventually_cyclicBoundarySites_ratio_le_power :
    ∀ᶠ n : ℕ in atTop,
      ((cyclicBoundarySites (localMeshSize n)
        (rigiditySmoothScale n / n)).card : ℝ) / localMeshSize n ≤
          4 * rigidityPower n (-3 / 4) := by
  have hKtop : Tendsto rigiditySmoothScale atTop atTop := by
    unfold rigiditySmoothScale rigiditySmoothExponent
    exact tendsto_rigidityPower_atTop (by norm_num)
  have hKone : ∀ᶠ n : ℕ in atTop, 1 ≤ rigiditySmoothScale n :=
    hKtop.eventually (eventually_ge_atTop 1)
  filter_upwards [Nat.eventually_pos, hKone] with n hn hKn
  let M : ℕ := localMeshSize n
  let delta : ℝ := rigiditySmoothScale n / n
  let X : ℝ := delta * M
  let D : ℕ := Nat.floor X + 1
  have hdelta : 0 ≤ delta := by dsimp [delta]; positivity
  have hraw := card_cyclicBoundarySites_le M (localMeshSize_pos n) delta hdelta
  have hrawR : ((cyclicBoundarySites M delta).card : ℝ) ≤ 2 * D := by
    exact_mod_cast hraw
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hMreal : (0 : ℝ) < M := by exact_mod_cast localMeshSize_pos n
  have hMge : (n : ℝ) ≤ M := by
    dsimp [M, localMeshSize]
    push_cast
    nlinarith [sq_nonneg (n : ℝ), show (1 : ℝ) ≤ n by exact_mod_cast hn]
  have hMn : (1 : ℝ) ≤ (M : ℝ) / n :=
    (le_div_iff₀ hnreal).2 (by simpa using hMge)
  have hXeq : X = rigiditySmoothScale n * ((M : ℝ) / n) := by
    dsimp [X, delta]
    ring
  have hXone : 1 ≤ X := by
    rw [hXeq]
    simpa only [one_mul] using
      (mul_le_mul hKn hMn (by norm_num) (by positivity))
  have hD : (D : ℝ) ≤ 2 * X := by
    have hfloor := Nat.floor_le (by positivity : 0 ≤ X)
    push_cast
    dsimp [D]
    push_cast
    linarith
  have hcard : ((cyclicBoundarySites M delta).card : ℝ) ≤ 4 * X := by
    calc
      _ ≤ 2 * (D : ℝ) := hrawR
      _ ≤ 2 * (2 * X) := by gcongr
      _ = 4 * X := by ring
  change ((cyclicBoundarySites M delta).card : ℝ) / M ≤ _
  calc
    _ ≤ (4 * X) / M := div_le_div_of_nonneg_right hcard hMreal.le
    _ = 4 * delta := by
      dsimp [X]
      field_simp [hMreal.ne']
    _ = 4 * rigidityPower n (-15 / 16) := by
      dsimp [delta]
      rw [rigiditySmoothScale_div_eq_power hn]
      congr 2
      unfold rigiditySmoothExponent
      ring
    _ ≤ 4 * rigidityPower n (-3 / 4) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      unfold rigidityPower
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ n by omega)) (by norm_num)

lemma eventually_singletonSpreadBadSites_ratio_le_power :
    ∀ᶠ n : ℕ in atTop,
      ((singletonSpreadBadSites n
        (rigiditySmoothScale n / n)).card : ℝ) / localMeshSize n ≤
          16 * rigidityPower n (-3 / 4) := by
  have hKtop : Tendsto rigiditySmoothScale atTop atTop := by
    unfold rigiditySmoothScale rigiditySmoothExponent
    exact tendsto_rigidityPower_atTop (by norm_num)
  have hKone : ∀ᶠ n : ℕ in atTop, 1 ≤ rigiditySmoothScale n :=
    hKtop.eventually (eventually_ge_atTop 1)
  filter_upwards [Nat.eventually_pos, hKone] with n hn hKn
  let M : ℕ := localMeshSize n
  let delta : ℝ := rigiditySmoothScale n / n
  let X : ℝ := (2 * delta) * M
  let D : ℕ := Nat.floor X + 1
  have hdelta : 0 ≤ delta := by dsimp [delta]; positivity
  have hraw := card_singletonSpreadBadSites_le' n hn delta hdelta
  have hraw' : (singletonSpreadBadSites n delta).card ≤ 4 * D := by
    dsimp [D, X, M]
    omega
  have hrawR : ((singletonSpreadBadSites n delta).card : ℝ) ≤ 4 * D := by
    exact_mod_cast hraw'
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hMreal : (0 : ℝ) < M := by exact_mod_cast localMeshSize_pos n
  have hMge : (n : ℝ) ≤ M := by
    dsimp [M, localMeshSize]
    push_cast
    nlinarith [sq_nonneg (n : ℝ), show (1 : ℝ) ≤ n by exact_mod_cast hn]
  have hMn : (1 : ℝ) ≤ (M : ℝ) / n :=
    (le_div_iff₀ hnreal).2 (by simpa using hMge)
  have hXeq : X = 2 * rigiditySmoothScale n * ((M : ℝ) / n) := by
    dsimp [X, delta]
    ring
  have hXone : 1 ≤ X := by
    rw [hXeq]
    have hprod : 1 ≤ rigiditySmoothScale n * ((M : ℝ) / n) := by
      simpa only [one_mul] using
        (mul_le_mul hKn hMn (by norm_num) (by positivity))
    nlinarith
  have hD : (D : ℝ) ≤ 2 * X := by
    have hfloor := Nat.floor_le (by positivity : 0 ≤ X)
    push_cast
    dsimp [D]
    push_cast
    linarith
  have hcard : ((singletonSpreadBadSites n delta).card : ℝ) ≤ 8 * X := by
    calc
      _ ≤ 4 * (D : ℝ) := hrawR
      _ ≤ 4 * (2 * X) := by gcongr
      _ = 8 * X := by ring
  change ((singletonSpreadBadSites n delta).card : ℝ) / M ≤ _
  calc
    _ ≤ (8 * X) / M := div_le_div_of_nonneg_right hcard hMreal.le
    _ = 16 * delta := by
      dsimp [X]
      field_simp [hMreal.ne']
      ring
    _ = 16 * rigidityPower n (-15 / 16) := by
      dsimp [delta]
      rw [rigiditySmoothScale_div_eq_power hn]
      congr 2
      unfold rigiditySmoothExponent
      ring
    _ ≤ 16 * rigidityPower n (-3 / 4) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      unfold rigidityPower
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ n by omega)) (by norm_num)

lemma eventually_badLocalTuples_ratio_le_power
    (k : ℕ) (hk : 0 < k) :
    ∀ᶠ n : ℕ in atTop,
      ((badLocalTuples n k).card : ℝ) /
          (localMeshSize n : ℝ) ^ k ≤
        ((32 : ℝ) * k + 16 * k + 8 * k ^ 2) *
          rigidityPower n (-1 / 4) := by
  let upper : ℕ → ℝ := fun n ↦
    k * (((smoothBadLocalSites n (rigiditySmoothScale n)).card : ℝ) /
      localMeshSize n) +
    k * (((singletonSpreadBadSites n
      (rigiditySmoothScale n / n)).card : ℝ) / localMeshSize n) +
    2 * k ^ 2 * (((cyclicBoundarySites (localMeshSize n)
      (rigiditySmoothScale n / n)).card : ℝ) / localMeshSize n)
  have hbound : ∀ᶠ n : ℕ in atTop,
      ((badLocalTuples n k).card : ℝ) /
          (localMeshSize n : ℝ) ^ k ≤ upper n := by
    filter_upwards [Nat.eventually_pos] with n hn
    have hraw := card_badLocalTuples_le n k hn
    have hrawR : ((badLocalTuples n k).card : ℝ) ≤
        k * ((localMeshSize n : ℝ) ^ (k - 1) *
          (smoothBadLocalSites n (rigiditySmoothScale n)).card) +
        k * ((localMeshSize n : ℝ) ^ (k - 1) *
          (singletonSpreadBadSites n
            (rigiditySmoothScale n / n)).card) +
        2 * (k ^ 2 * ((localMeshSize n : ℝ) ^ (k - 1) *
          (cyclicBoundarySites (localMeshSize n)
            (rigiditySmoothScale n / n)).card)) := by
      exact_mod_cast hraw
    have hden : 0 ≤ (localMeshSize n : ℝ) ^ k := by positivity
    have hdiv := div_le_div_of_nonneg_right hrawR hden
    rw [add_div, add_div] at hdiv
    simp only [mul_div_assoc] at hdiv
    rw [pow_pred_mul_div_pow_eq_div_assoc (localMeshSize n) k
      (localMeshSize_pos n) hk] at hdiv
    rw [pow_pred_mul_div_pow_eq_div_assoc (localMeshSize n) k
      (localMeshSize_pos n) hk] at hdiv
    rw [pow_pred_mul_div_pow_eq_div_assoc (localMeshSize n) k
      (localMeshSize_pos n) hk] at hdiv
    simpa only [upper, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_mul, mul_assoc]
      using hdiv
  filter_upwards [eventually_ge_atTop (1 : ℕ), hbound,
      eventually_smoothBadLocalSites_ratio_le_power,
      eventually_singletonSpreadBadSites_ratio_le_power,
      eventually_cyclicBoundarySites_ratio_le_power]
    with n hn hbad hsmooth hsingle hcyclic
  have hpower : rigidityPower n (-3 / 4) ≤ rigidityPower n (-1 / 4) := by
    unfold rigidityPower
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num)
  calc
    ((badLocalTuples n k).card : ℝ) /
          (localMeshSize n : ℝ) ^ k ≤ upper n := hbad
    _ ≤ (k : ℝ) * (32 * rigidityPower n (-1 / 4)) +
        k * (16 * rigidityPower n (-3 / 4)) +
        2 * k ^ 2 * (4 * rigidityPower n (-3 / 4)) := by
      dsimp [upper]
      gcongr
    _ ≤ (k : ℝ) * (32 * rigidityPower n (-1 / 4)) +
        k * (16 * rigidityPower n (-1 / 4)) +
        2 * k ^ 2 * (4 * rigidityPower n (-1 / 4)) := by
      gcongr
    _ = ((32 : ℝ) * k + 16 * k + 8 * k ^ 2) *
          rigidityPower n (-1 / 4) := by ring

theorem weighted_badLocalSiteSets_ratio_tendsto_zero
    (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ ↦
      rigidityPower n (1 / 20) *
        (((badLocalSiteSets n k).card : ℝ) /
          (localMeshSize n : ℝ) ^ k)) atTop (𝓝 0) := by
  let C : ℝ := (32 : ℝ) * k + 16 * k + 8 * k ^ 2
  have hupper : ∀ᶠ n : ℕ in atTop,
      rigidityPower n (1 / 20) *
          (((badLocalSiteSets n k).card : ℝ) /
            (localMeshSize n : ℝ) ^ k) ≤
        C * rigidityPower n (-1 / 5) := by
    filter_upwards [Nat.eventually_pos,
        eventually_badLocalTuples_ratio_le_power k hk]
      with n hn hbad
    have hsite : ((badLocalSiteSets n k).card : ℝ) /
          (localMeshSize n : ℝ) ^ k ≤
        ((badLocalTuples n k).card : ℝ) /
          (localMeshSize n : ℝ) ^ k := by
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast badLocalSiteSets_subset_badLocalTuples_card n k)
        (by positivity)
    calc
      _ ≤ rigidityPower n (1 / 20) *
          (((badLocalTuples n k).card : ℝ) /
            (localMeshSize n : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left hsite (rigidityPower_nonneg n _)
      _ ≤ rigidityPower n (1 / 20) *
          (C * rigidityPower n (-1 / 4)) := by
        exact mul_le_mul_of_nonneg_left (by simpa [C] using hbad)
          (rigidityPower_nonneg n _)
      _ = C * rigidityPower n (-1 / 5) := by
        rw [show rigidityPower n (1 / 20) *
            (C * rigidityPower n (-1 / 4)) =
          C * (rigidityPower n (1 / 20) *
            rigidityPower n (-1 / 4)) by ring]
        rw [← rigidityPower_add hn]
        congr 2
        norm_num
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply squeeze_zero'
    (Eventually.of_forall fun n ↦
      mul_nonneg (rigidityPower_nonneg n _)
        (div_nonneg (Nat.cast_nonneg _) (by positivity)))
    hupper
  convert
    (tendsto_rigidityPower_neg_zero
      (by norm_num : (0 : ℝ) < 1 / 5)).const_mul C using 1 <;> norm_num

noncomputable def halfWeakNonspreadLocalSiteSets (n k : ℕ) :
    Finset (Finset (Fin (localMeshSize n))) :=
  (halfNonspreadLocalSiteSets n k).filter fun s ↦
    IsSpread n (weakSpreadScale k n) (localSitesPoints s)

noncomputable def halfVeryCloseLocalSiteSets (n k : ℕ) :
    Finset (Finset (Fin (localMeshSize n))) :=
  (halfNonspreadLocalSiteSets n k).filter fun s ↦
    ¬IsSpread n (weakSpreadScale k n) (localSitesPoints s)

lemma halfNonspread_eq_weak_union_veryClose (n k : ℕ) :
    halfNonspreadLocalSiteSets n k =
      halfWeakNonspreadLocalSiteSets n k ∪
        halfVeryCloseLocalSiteSets n k := by
  classical
  ext s
  simp [halfWeakNonspreadLocalSiteSets, halfVeryCloseLocalSiteSets]
  tauto

lemma halfWeakNonspread_disjoint_veryClose (n k : ℕ) :
    Disjoint (halfWeakNonspreadLocalSiteSets n k)
      (halfVeryCloseLocalSiteSets n k) := by
  rw [Finset.disjoint_left]
  intro s hweak hclose
  have hweak' := Finset.mem_filter.mp hweak
  have hclose' := Finset.mem_filter.mp hclose
  exact hclose'.2 hweak'.2

lemma halfWeakNonspread_subset_badLocalSiteSets (n k : ℕ) :
    halfWeakNonspreadLocalSiteSets n k ⊆ badLocalSiteSets n k := by
  intro s hs
  have hweak := Finset.mem_filter.mp hs
  have hnonspread := Finset.mem_filter.mp hweak.1
  have hpowerset := Finset.mem_powersetCard.mp hnonspread.1
  rw [badLocalSiteSets, Finset.mem_filter]
  refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ s, hpowerset.2⟩, ?_⟩
  intro hgood
  exact hnonspread.2 hgood.2

noncomputable def halfWeakNonspreadTruncatedChooseContribution
    (n k : ℕ) (u velocityLower velocityUpper : ℝ) : ℝ :=
  ∑ s ∈ halfWeakNonspreadLocalSiteSets n k,
    uniformProbability (fun e : SignVector (2 * n) ↦
      ∀ a ∈ s,
        IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)

noncomputable def halfVeryCloseTruncatedChooseContribution
    (n k : ℕ) (u velocityLower velocityUpper : ℝ) : ℝ :=
  ∑ s ∈ halfVeryCloseLocalSiteSets n k,
    uniformProbability (fun e : SignVector (2 * n) ↦
      ∀ a ∈ s,
        IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)

lemma halfNonspreadTruncatedChooseContribution_eq_weak_add_veryClose
    (n k : ℕ) (u velocityLower velocityUpper : ℝ) :
    halfNonspreadTruncatedChooseContribution n k u velocityLower velocityUpper =
      halfWeakNonspreadTruncatedChooseContribution n k u
          velocityLower velocityUpper +
        halfVeryCloseTruncatedChooseContribution n k u
          velocityLower velocityUpper := by
  rw [halfNonspreadTruncatedChooseContribution,
    halfNonspread_eq_weak_union_veryClose,
    Finset.sum_union (halfWeakNonspread_disjoint_veryClose n k)]
  rfl

theorem eventually_scaled_halfWeakNonspread_site_probability_le_power
    (k : ℕ) (hk : 0 < k)
    (u velocityLower velocityUpper : ℝ)
    (hu : 0 ≤ u) (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper) :
    ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ halfWeakNonspreadLocalSiteSets n k,
        (localMeshSize n : ℝ) ^ k *
          uniformProbability (fun e : SignVector (2 * n) ↦
            ∀ a ∈ s,
              IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a) ≤
        rigidityPower n (1 / 20) := by
  filter_upwards [Nat.eventually_pos,
      eventually_scaled_positionBall_probability_le_power
        hk u velocityUpper hu hvelocityUpper]
    with n hn hball
  intro s hs
  have hweak := Finset.mem_filter.mp hs
  have hnonspread := Finset.mem_filter.mp hweak.1
  have hpowerset := Finset.mem_powersetCard.mp hnonspread.1
  have hcard : s.card = k := hpowerset.2
  have hsmooth : ∀ r : Fin s.card,
      IsSmooth n (rigiditySmoothScale n) (localSitesPoints s r) := by
    intro r
    exact (Finset.mem_filter.mp
      (hpowerset.1 (localSite_mem s r))).2
  have hprobMono :
      uniformProbability (fun e : SignVector (2 * n) ↦
          ∀ a ∈ s,
            IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a) ≤
        uniformProbability (fun e : SignVector (2 * n) ↦
          ‖normalizedPositionEuclideanWalk n e (localSitesPoints s)‖ ≤
            positionRepresentativeRadius s.card n u velocityUpper) := by
    apply uniformProbability_mono
    intro e he
    exact joint_truncatedLocalRepresentatives_positionBall n hn u
      velocityLower velocityUpper hu hvelocityLower hvelocityUpper e s he
  subst k
  calc
    (localMeshSize n : ℝ) ^ s.card *
        uniformProbability (fun e : SignVector (2 * n) ↦
          ∀ a ∈ s,
            IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a) ≤
      (localMeshSize n : ℝ) ^ s.card *
        uniformProbability (fun e : SignVector (2 * n) ↦
          ‖normalizedPositionEuclideanWalk n e (localSitesPoints s)‖ ≤
            positionRepresentativeRadius s.card n u velocityUpper) :=
      mul_le_mul_of_nonneg_left hprobMono (by positivity)
    _ ≤ rigidityPower n (1 / 20) := hball (localSitesPoints s) hsmooth hweak.2

theorem halfWeakNonspreadTruncatedChooseContribution_tendsto_zero
    (k : ℕ) (hk : 0 < k)
    (u velocityLower velocityUpper : ℝ)
    (hu : 0 ≤ u) (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper) :
    Tendsto (fun n : ℕ ↦
      halfWeakNonspreadTruncatedChooseContribution n k u
        velocityLower velocityUpper) atTop (𝓝 0) := by
  have hupper : ∀ᶠ n : ℕ in atTop,
      halfWeakNonspreadTruncatedChooseContribution n k u
          velocityLower velocityUpper ≤
        rigidityPower n (1 / 20) *
          (((badLocalSiteSets n k).card : ℝ) /
            (localMeshSize n : ℝ) ^ k) := by
    filter_upwards [eventually_scaled_halfWeakNonspread_site_probability_le_power
        k hk u velocityLower velocityUpper hu hvelocityLower hvelocityUpper]
      with n hsite
    let q : ℝ := (localMeshSize n : ℝ) ^ k
    have hq : 0 < q := by
      dsimp [q]
      exact pow_pos (by exact_mod_cast localMeshSize_pos n) k
    have hterm : ∀ s ∈ halfWeakNonspreadLocalSiteSets n k,
        uniformProbability (fun e : SignVector (2 * n) ↦
          ∀ a ∈ s,
            IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a) ≤
          rigidityPower n (1 / 20) / q := by
      intro s hs
      exact (le_div_iff₀ hq).2 (by simpa [q, mul_comm] using hsite s hs)
    calc
      halfWeakNonspreadTruncatedChooseContribution n k u
          velocityLower velocityUpper ≤
        ∑ _s ∈ halfWeakNonspreadLocalSiteSets n k,
          rigidityPower n (1 / 20) / q := by
        unfold halfWeakNonspreadTruncatedChooseContribution
        exact Finset.sum_le_sum fun s hs ↦ hterm s hs
      _ = ((halfWeakNonspreadLocalSiteSets n k).card : ℝ) *
          (rigidityPower n (1 / 20) / q) := by simp
      _ ≤ ((badLocalSiteSets n k).card : ℝ) *
          (rigidityPower n (1 / 20) / q) := by
        have hcard : ((halfWeakNonspreadLocalSiteSets n k).card : ℝ) ≤
            (badLocalSiteSets n k).card := by
          exact_mod_cast Finset.card_le_card
            (halfWeakNonspread_subset_badLocalSiteSets n k)
        exact mul_le_mul_of_nonneg_right
          hcard
          (div_nonneg (rigidityPower_nonneg n _) hq.le)
      _ = rigidityPower n (1 / 20) *
          (((badLocalSiteSets n k).card : ℝ) /
            (localMeshSize n : ℝ) ^ k) := by
        dsimp only [q]
        ring
  apply squeeze_zero'
    (Eventually.of_forall fun n ↦ by
      unfold halfWeakNonspreadTruncatedChooseContribution
      exact Finset.sum_nonneg fun s _ ↦ uniformProbability_nonneg _)
    hupper
  exact weighted_badLocalSiteSets_ratio_tendsto_zero k hk

/-- The location parameter built into the rigidity argument makes the
velocity-demand inequality a formal consequence of the harder position
demand inequality. -/
lemma phaseHighVelocity_demand_of_position_demand
    (n m H k ell : ℕ) (hn : 0 < n) (hm : 0 < m) (hH : 0 < H)
    (epsilon delta t E J : ℝ) (hE : 0 < E) (ht : t ≠ 0)
    (hJ : 0 ≤ J) (hJsize : (n : ℝ) ≤ J * H)
    (hposition :
      phaseHighPositionBudget t E J ell k <
        phaseHighPositionDemand m H k ell epsilon delta) :
    phaseHighVelocityBudget t E ell k <
      phaseHighVelocityDemand n m H k ell epsilon delta := by
  let A : ℝ := 2 + 4 * (J + 1) ^ 2
  let X : ℝ := (36 : ℝ) ^ ell *
    ((Real.pi / |t|) ^ 2 * (4 : ℝ) ^ (2 * k) * E)
  let D : ℝ :=
    (Real.sqrt (1 / (8 * (m : ℝ))) * epsilon ^ (2 * k) *
      delta ^ (2 * ell)) ^ 2
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  have hA : 0 < A := by dsimp [A]; positivity
  have hX : 0 < X := by
    dsimp [X]
    positivity
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hDformula : D = (1 / (8 * (m : ℝ))) *
      (epsilon ^ (2 * k)) ^ 2 * (delta ^ (2 * ell)) ^ 2 := by
    have hbase : 0 ≤ (1 / (8 * (m : ℝ))) := by positivity
    dsimp [D]
    rw [mul_pow, mul_pow, Real.sq_sqrt hbase]
  have hposition' : A * X < (H : ℝ) * D / 4 := by
    have hposition0 : A * X < (H : ℝ) *
        ((Real.sqrt (1 / (8 * (m : ℝ))) * epsilon ^ (2 * k) *
          delta ^ (2 * ell)) / 2) ^ 2 := by
      simpa only [phaseHighPositionBudget, phaseHighPositionDemand, A, X,
        mul_assoc] using hposition
    have hsquare :
        ((Real.sqrt (1 / (8 * (m : ℝ))) * epsilon ^ (2 * k) *
          delta ^ (2 * ell)) / 2) ^ 2 = D / 4 := by
      dsimp [D]
      ring
    rw [hsquare] at hposition0
    simpa only [mul_div_assoc] using hposition0
  have hXupper : 2 * X < (H : ℝ) * D / (2 * A) := by
    have hdiv : X < ((H : ℝ) * D / 4) / A := by
      rw [lt_div_iff₀ hA]
      simpa [mul_comm] using hposition'
    calc
      2 * X < 2 * ((H : ℝ) * D / 4 / A) :=
        mul_lt_mul_of_pos_left hdiv (by norm_num)
      _ = (H : ℝ) * D / (2 * A) := by ring
  have hnSq : (n : ℝ) ^ 2 ≤ J ^ 2 * (H : ℝ) ^ 2 := by
    have hsquare := (sq_le_sq₀ hnreal.le
      (mul_nonneg hJ hHreal.le)).2 hJsize
    nlinarith
  have hJbound : J ^ 2 ≤ 2 * A := by
    dsimp [A]
    nlinarith [sq_nonneg (J + 1)]
  have hnSq' : (n : ℝ) ^ 2 ≤ 2 * A * (H : ℝ) ^ 2 := by
    calc
      _ ≤ J ^ 2 * (H : ℝ) ^ 2 := hnSq
      _ ≤ (2 * A) * (H : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hJbound (sq_nonneg _)
  have hrecip : 1 / (2 * A) ≤ (H : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hA) (sq_pos_of_pos hnreal)]
    nlinarith
  have hfactor : (H : ℝ) * D / (2 * A) ≤
      (H : ℝ) * ((H : ℝ) / n) ^ 2 * D := by
    have hHD : 0 ≤ (H : ℝ) * D := mul_nonneg hHreal.le hD
    calc
      (H : ℝ) * D / (2 * A) =
          ((H : ℝ) * D) * (1 / (2 * A)) := by ring
      _ ≤ ((H : ℝ) * D) * ((H : ℝ) ^ 2 / (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hrecip hHD
      _ = (H : ℝ) * ((H : ℝ) / n) ^ 2 * D := by ring
  have hmain : 2 * X < (H : ℝ) * ((H : ℝ) / n) ^ 2 * D :=
    hXupper.trans_le hfactor
  unfold phaseHighVelocityBudget phaseHighVelocityDemand
  simpa only [X, hDformula, mul_assoc] using hmain

/-! ### A moment-dependent acceleration cutoff for microscopic clusters -/

/-- The acceleration cutoff used to resolve failures of weak separation is
smaller than the reciprocal weak-separation scale. -/
noncomputable def fineAccelerationExponent (k : ℕ) : ℝ :=
  weakSeparationExponent k / 4

noncomputable def fineAccelerationCutoff (k n : ℕ) : ℝ :=
  rigidityPower n (fineAccelerationExponent k)

def HasHighFineMeshAcceleration (k n : ℕ)
    (e : SignVector (2 * n)) : Prop :=
  ∃ a : Fin (localMeshSize n),
    fineAccelerationCutoff k n ≤
      ‖rescaledCenteredAcceleration n e (localMeshPoint n a)‖

noncomputable def fineGlobalAccelerationBound (k n : ℕ) : ℝ :=
  fineAccelerationCutoff k n +
    2 * Real.sqrt (2 * n + 1 : ℝ) * localMeshHalfWidth n

lemma fineAccelerationExponent_pos (k : ℕ) :
    0 < fineAccelerationExponent k := by
  unfold fineAccelerationExponent
  exact div_pos (weakSeparationExponent_pos k) (by norm_num)

lemma fineAccelerationCutoff_pos (k n : ℕ) (hn : 0 < n) :
    0 < fineAccelerationCutoff k n := by
  unfold fineAccelerationCutoff
  exact rigidityPower_pos hn _

lemma uniformProbability_highFineMeshAcceleration_le
    (k n : ℕ) (hn : 0 < n) :
    uniformProbability (HasHighFineMeshAcceleration k n) ≤
      (localMeshSize n : ℝ) *
        (4 * Real.exp (-(fineAccelerationCutoff k n / 2) ^ 2 / 2)) := by
  have hcut := fineAccelerationCutoff_pos k n hn
  calc
    uniformProbability (HasHighFineMeshAcceleration k n) ≤
        ∑ a : Fin (localMeshSize n),
          uniformProbability (fun e : SignVector (2 * n) ↦
            fineAccelerationCutoff k n ≤
              ‖rescaledCenteredAcceleration n e (localMeshPoint n a)‖) := by
      exact uniformProbability_exists_le_sum _
    _ ≤ ∑ _a : Fin (localMeshSize n),
        4 * Real.exp (-(fineAccelerationCutoff k n / 2) ^ 2 / 2) := by
      apply Finset.sum_le_sum
      intro a _ha
      exact uniformProbability_acceleration_norm_ge n hn
        (localMeshPoint n a) (fineAccelerationCutoff k n) hcut
    _ = (localMeshSize n : ℝ) *
        (4 * Real.exp (-(fineAccelerationCutoff k n / 2) ^ 2 / 2)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp only [nsmul_eq_mul]

theorem scaled_highFineMeshAcceleration_upper_tendsto_zero
    (k d : ℕ) :
    Tendsto (fun n : ℕ ↦
      (localMeshSize n : ℝ) ^ (d + 1) *
        (4 * Real.exp (-(fineAccelerationCutoff k n / 2) ^ 2 / 2)))
      atTop (𝓝 0) := by
  let C : ℝ := 4 * 2 ^ (d + 1)
  have hq : 0 < 2 * fineAccelerationExponent k := by
    exact mul_pos (by norm_num) (fineAccelerationExponent_pos k)
  have hcore :=
    (tendsto_rigidityPower_mul_exp_neg_power_test
      (2 * (d + 1)) (2 * fineAccelerationExponent k) (1 / 8)
      hq (by norm_num)).const_mul C
  refine squeeze_zero'
    (g := fun n : ℕ ↦ C *
      (rigidityPower n (2 * (d + 1)) *
        Real.exp (-(1 / 8) *
          rigidityPower n (2 * fineAccelerationExponent k))))
    (Eventually.of_forall fun n ↦ by positivity) ?_ ?_
  · filter_upwards [Nat.eventually_pos] with n hn
    have hsize : (localMeshSize n : ℝ) ≤ 2 * rigidityPower n 2 := by
      simp only [localMeshSize, rigidityPower]
      norm_num
      push_cast
      nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]
    have hsizePow : (localMeshSize n : ℝ) ^ (d + 1) ≤
        (2 * rigidityPower n 2) ^ (d + 1) := by
      exact pow_le_pow_left₀ (by positivity) hsize _
    have hrpow : rigidityPower n 2 ^ (d + 1) =
        rigidityPower n (2 * (d + 1)) := by
      convert rigidityPower_nat_pow hn 2 (d + 1) using 1 <;> norm_num
    have hsizePow' : (localMeshSize n : ℝ) ^ (d + 1) ≤
        2 ^ (d + 1) * rigidityPower n (2 * (d + 1)) := by
      calc
        _ ≤ (2 * rigidityPower n 2) ^ (d + 1) := hsizePow
        _ = 2 ^ (d + 1) * rigidityPower n (2 * (d + 1)) := by
          rw [mul_pow, hrpow]
    have hcutSq : fineAccelerationCutoff k n ^ 2 =
        rigidityPower n (2 * fineAccelerationExponent k) := by
      unfold fineAccelerationCutoff
      simpa [mul_comm] using
        rigidityPower_nat_pow hn (fineAccelerationExponent k) 2
    have hexp : -(fineAccelerationCutoff k n / 2) ^ 2 / 2 =
        -(1 / 8) * rigidityPower n (2 * fineAccelerationExponent k) := by
      rw [div_pow, hcutSq]
      ring
    rw [hexp]
    have hnonneg : 0 ≤ 4 * Real.exp
        (-(1 / 8) * rigidityPower n (2 * fineAccelerationExponent k)) := by
      positivity
    calc
      (localMeshSize n : ℝ) ^ (d + 1) *
          (4 * Real.exp
            (-(1 / 8) * rigidityPower n (2 * fineAccelerationExponent k))) ≤
        (2 ^ (d + 1) * rigidityPower n (2 * (d + 1))) *
          (4 * Real.exp
            (-(1 / 8) * rigidityPower n (2 * fineAccelerationExponent k))) :=
        mul_le_mul_of_nonneg_right hsizePow' hnonneg
      _ = C * (rigidityPower n (2 * (d + 1)) *
          Real.exp (-(1 / 8) *
            rigidityPower n (2 * fineAccelerationExponent k))) := by
        dsimp [C]
        ring
  · simpa [C] using hcore

theorem localMeshSize_pow_mul_highFineMeshAcceleration_tendsto_zero
    (k d : ℕ) :
    Tendsto (fun n : ℕ ↦ (localMeshSize n : ℝ) ^ d *
      uniformProbability (HasHighFineMeshAcceleration k n)) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n ↦
    mul_nonneg (by positivity) (uniformProbability_nonneg _))
  · filter_upwards [Nat.eventually_pos] with n hn
    have hprob := uniformProbability_highFineMeshAcceleration_le k n hn
    have hmesh : 0 ≤ (localMeshSize n : ℝ) ^ d := by positivity
    have := mul_le_mul_of_nonneg_left hprob hmesh
    convert this using 1 <;> ring
  · convert scaled_highFineMeshAcceleration_upper_tendsto_zero k d using 1
    funext n
    ring

lemma norm_rescaledCenteredAcceleration_le_of_not_highFine
    (k n : ℕ) (hn : 0 < n) (e : SignVector (2 * n))
    (hgood : ¬HasHighFineMeshAcceleration k n e)
    (t : ℝ) (ht : t ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n)) :
    ‖rescaledCenteredAcceleration n e t‖ ≤
      fineGlobalAccelerationBound k n := by
  by_cases htop : t = Real.pi * n
  · subst t
    let a : Fin (localMeshSize n) := ⟨0, localMeshSize_pos n⟩
    have ha : ‖rescaledCenteredAcceleration n e (localMeshPoint n a)‖ <
        fineAccelerationCutoff k n := by
      exact lt_of_not_ge fun hge ↦ hgood ⟨a, hge⟩
    have hpoint : localMeshPoint n a = -(Real.pi * n) := by
      simp [a, localMeshPoint]
    have hperiod := rescaledCenteredAcceleration_add_period n e (-(Real.pi * n))
    have harg : -(Real.pi * n) + 2 * Real.pi * n = Real.pi * n := by ring
    rw [harg] at hperiod
    rw [hpoint] at ha
    rw [hperiod]
    unfold fineGlobalAccelerationBound
    have hhalf : 0 ≤ localMeshHalfWidth n := by
      unfold localMeshHalfWidth
      positivity
    exact ha.le.trans (le_add_of_nonneg_right
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hhalf))
  · have htIco : t ∈ Set.Ico (-(Real.pi * n)) (Real.pi * n) :=
      ⟨ht.1, lt_of_le_of_ne ht.2 htop⟩
    rcases exists_localMeshPoint_within_step n hn t htIco with
      ⟨a, hdiff0, hdiff⟩
    have ha : ‖rescaledCenteredAcceleration n e (localMeshPoint n a)‖ <
        fineAccelerationCutoff k n := by
      exact lt_of_not_ge fun hge ↦ hgood ⟨a, hge⟩
    have hsub := norm_rescaledCenteredAcceleration_sub_le
      n e (localMeshPoint n a) t
    rw [abs_of_nonneg hdiff0] at hsub
    have htri : ‖rescaledCenteredAcceleration n e t‖ ≤
        ‖rescaledCenteredAcceleration n e t -
          rescaledCenteredAcceleration n e (localMeshPoint n a)‖ +
        ‖rescaledCenteredAcceleration n e (localMeshPoint n a)‖ := by
      have heq : rescaledCenteredAcceleration n e t =
          (rescaledCenteredAcceleration n e t -
            rescaledCenteredAcceleration n e (localMeshPoint n a)) +
          rescaledCenteredAcceleration n e (localMeshPoint n a) := by abel
      calc
        ‖rescaledCenteredAcceleration n e t‖ =
            ‖(rescaledCenteredAcceleration n e t -
              rescaledCenteredAcceleration n e (localMeshPoint n a)) +
              rescaledCenteredAcceleration n e (localMeshPoint n a)‖ :=
          congrArg norm heq
        _ ≤ _ := norm_add_le _ _
    unfold fineGlobalAccelerationBound
    have hsqrt : 0 ≤ Real.sqrt (2 * n + 1 : ℝ) := Real.sqrt_nonneg _
    calc
      ‖rescaledCenteredAcceleration n e t‖ ≤
          ‖rescaledCenteredAcceleration n e t -
            rescaledCenteredAcceleration n e (localMeshPoint n a)‖ +
          ‖rescaledCenteredAcceleration n e (localMeshPoint n a)‖ := htri
      _ ≤ Real.sqrt (2 * n + 1 : ℝ) *
            (t - localMeshPoint n a) +
          ‖rescaledCenteredAcceleration n e (localMeshPoint n a)‖ := by
        gcongr
      _ ≤ Real.sqrt (2 * n + 1 : ℝ) *
            (2 * localMeshHalfWidth n) + fineAccelerationCutoff k n := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hdiff.le hsqrt) ha.le
      _ = fineAccelerationCutoff k n +
          2 * Real.sqrt (2 * n + 1 : ℝ) * localMeshHalfWidth n := by ring

lemma norm_rescaledCenteredEval_sub_linear_le_of_not_highFine
    (k n : ℕ) (hn : 0 < n) (e : SignVector (2 * n))
    (hgood : ¬HasHighFineMeshAcceleration k n e)
    (x y : ℝ)
    (hx : x ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n))
    (hy : y ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n)) :
    ‖rescaledCenteredEval n e y -
        (rescaledCenteredEval n e x + ((y - x : ℝ) : ℂ) *
          rescaledCenteredVelocity n e x)‖ ≤
      fineGlobalAccelerationBound k n * (y - x) ^ 2 := by
  by_cases hxy : x ≤ y
  · apply norm_taylor_sub_le_of_le_on
      (rescaledCenteredEval n e)
      (rescaledCenteredVelocity n e)
      (rescaledCenteredAcceleration n e)
      (fineGlobalAccelerationBound k n) x y hxy
      (hasDerivAt_rescaledCenteredEval n e)
      (hasDerivAt_rescaledCenteredVelocity n e)
    · unfold fineGlobalAccelerationBound
      exact add_nonneg (rigidityPower_nonneg n _)
        (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
          (by unfold localMeshHalfWidth; positivity))
    · intro t htseg
      apply norm_rescaledCenteredAcceleration_le_of_not_highFine k n hn e hgood
      exact ⟨hx.1.trans htseg.1, htseg.2.trans hy.2⟩
  · have hyx : y ≤ x := le_of_not_ge hxy
    apply norm_taylor_sub_le_of_ge_on
      (rescaledCenteredEval n e)
      (rescaledCenteredVelocity n e)
      (rescaledCenteredAcceleration n e)
      (fineGlobalAccelerationBound k n) x y hyx
      (hasDerivAt_rescaledCenteredEval n e)
      (hasDerivAt_rescaledCenteredVelocity n e)
    · unfold fineGlobalAccelerationBound
      exact add_nonneg (rigidityPower_nonneg n _)
        (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
          (by unfold localMeshHalfWidth; positivity))
    · intro t htseg
      apply norm_rescaledCenteredAcceleration_le_of_not_highFine k n hn e hgood
      exact ⟨hy.1.trans htseg.1, htseg.2.trans hx.2⟩

lemma norm_rescaledCenteredVelocity_sub_le_of_not_highFine
    (k n : ℕ) (hn : 0 < n) (e : SignVector (2 * n))
    (hgood : ¬HasHighFineMeshAcceleration k n e)
    (x y : ℝ)
    (hx : x ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n))
    (hy : y ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n)) :
    ‖rescaledCenteredVelocity n e y -
        rescaledCenteredVelocity n e x‖ ≤
      fineGlobalAccelerationBound k n * |y - x| := by
  by_cases hxy : x ≤ y
  · have hbound := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := rescaledCenteredVelocity n e)
      (f' := rescaledCenteredAcceleration n e)
      (a := x) (b := y) (C := fineGlobalAccelerationBound k n)
      (fun t _ht ↦
        (hasDerivAt_rescaledCenteredVelocity n e t).hasDerivWithinAt)
      (fun t ht ↦ norm_rescaledCenteredAcceleration_le_of_not_highFine
        k n hn e hgood t ⟨hx.1.trans ht.1, ht.2.le.trans hy.2⟩)
      y (Set.right_mem_Icc.mpr hxy)
    simpa [abs_of_nonneg (sub_nonneg.mpr hxy)] using hbound
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hbound := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := rescaledCenteredVelocity n e)
      (f' := rescaledCenteredAcceleration n e)
      (a := y) (b := x) (C := fineGlobalAccelerationBound k n)
      (fun t _ht ↦
        (hasDerivAt_rescaledCenteredVelocity n e t).hasDerivWithinAt)
      (fun t ht ↦ norm_rescaledCenteredAcceleration_le_of_not_highFine
        k n hn e hgood t ⟨hy.1.trans ht.1, ht.2.le.trans hx.2⟩)
      x (Set.right_mem_Icc.mpr hyx)
    rw [← norm_neg, neg_sub]
    simpa [abs_of_nonpos (sub_nonpos.mpr hyx)] using hbound

lemma localRepresentative_pair_affine_displacement_bound_fine
    (k n : ℕ) (hn : 0 < n) (e : SignVector (2 * n))
    (hgood : ¬HasHighFineMeshAcceleration k n e)
    (u velocityLower velocityUpper : ℝ)
    (a b : Fin (localMeshSize n))
    (ha : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)
    (hb : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e b) :
    velocityLower *
        |(localMeshPoint n b + localAffineOffset n e b) -
          (localMeshPoint n a + localAffineOffset n e a)| ≤
      2 * (u / n) +
        fineGlobalAccelerationBound k n *
          (localMeshPoint n b - localMeshPoint n a) ^ 2 +
        localMeshHalfWidth n *
          (fineGlobalAccelerationBound k n *
            |localMeshPoint n b - localMeshPoint n a|) := by
  let x : ℝ := localMeshPoint n a
  let y : ℝ := localMeshPoint n b
  let sx : ℝ := localAffineOffset n e a
  let sy : ℝ := localAffineOffset n e b
  let X : ℂ := rescaledCenteredEval n e x
  let Y : ℂ := rescaledCenteredEval n e y
  let Bx : ℂ := rescaledCenteredVelocity n e x
  let By : ℂ := rescaledCenteredVelocity n e y
  let Ax : ℂ := X + (sx : ℂ) * Bx
  let Ay : ℂ := Y + (sy : ℂ) * By
  let R : ℂ := Y - (X + ((y - x : ℝ) : ℂ) * Bx)
  let dr : ℝ := (y + sy) - (x + sx)
  have hx : x ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n) :=
    ⟨(localMeshPoint_mem_Ico n hn a).1,
      (localMeshPoint_mem_Ico n hn a).2.le⟩
  have hy : y ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n) :=
    ⟨(localMeshPoint_mem_Ico n hn b).1,
      (localMeshPoint_mem_Ico n hn b).2.le⟩
  have hAx : ‖Ax‖ ≤ u / n := by
    simpa [Ax, X, Bx, sx, x] using ha.1.affine_norm_le hn
  have hAy : ‖Ay‖ ≤ u / n := by
    simpa [Ay, Y, By, sy, y] using hb.1.affine_norm_le hn
  have hR : ‖R‖ ≤ fineGlobalAccelerationBound k n * (y - x) ^ 2 := by
    simpa [R, X, Y, Bx] using
      norm_rescaledCenteredEval_sub_linear_le_of_not_highFine
        k n hn e hgood x y hx hy
  have hvel : ‖By - Bx‖ ≤
      fineGlobalAccelerationBound k n * |y - x| := by
    simpa [Bx, By] using
      norm_rescaledCenteredVelocity_sub_le_of_not_highFine
        k n hn e hgood x y hx hy
  have hsy : |sy| ≤ localMeshHalfWidth n := by
    simpa [sy] using hb.1.2.1
  have hBx : velocityLower ≤ ‖Bx‖ := by
    simpa [Bx, x] using ha.2.1
  have hid : Ay - Ax =
      (dr : ℂ) * Bx + R + (sy : ℂ) * (By - Bx) := by
    dsimp [Ay, Ax, dr, R]
    simp only [Complex.ofReal_add, Complex.ofReal_sub]
    ring
  have hdrnorm : |dr| * ‖Bx‖ ≤
      ‖Ay - Ax‖ + ‖R‖ + ‖(sy : ℂ) * (By - Bx)‖ := by
    have hrearrange : (dr : ℂ) * Bx =
        (Ay - Ax) - R - (sy : ℂ) * (By - Bx) := by
      rw [hid]
      abel
    calc
      |dr| * ‖Bx‖ = ‖(dr : ℂ) * Bx‖ := by simp
      _ = ‖(Ay - Ax) - R - (sy : ℂ) * (By - Bx)‖ := by rw [hrearrange]
      _ ≤ ‖(Ay - Ax) - R‖ + ‖(sy : ℂ) * (By - Bx)‖ := norm_sub_le _ _
      _ ≤ (‖Ay - Ax‖ + ‖R‖) + ‖(sy : ℂ) * (By - Bx)‖ := by
        exact add_le_add (norm_sub_le (Ay - Ax) R) le_rfl
  have hleft : velocityLower * |dr| ≤ |dr| * ‖Bx‖ := by
    rw [mul_comm velocityLower]
    exact mul_le_mul_of_nonneg_left hBx (abs_nonneg dr)
  calc
    velocityLower * |dr| ≤ |dr| * ‖Bx‖ := hleft
    _ ≤ ‖Ay - Ax‖ + ‖R‖ + ‖(sy : ℂ) * (By - Bx)‖ := hdrnorm
    _ ≤ (‖Ay‖ + ‖Ax‖) + ‖R‖ +
          (|sy| * ‖By - Bx‖) := by
      gcongr
      · exact norm_sub_le Ay Ax
      · simp
    _ ≤ (u / n + u / n) +
          fineGlobalAccelerationBound k n * (y - x) ^ 2 +
          (localMeshHalfWidth n *
            (fineGlobalAccelerationBound k n * |y - x|)) := by
      have hhalf : 0 ≤ localMeshHalfWidth n := by
        unfold localMeshHalfWidth
        positivity
      exact add_le_add
        (add_le_add (add_le_add hAy hAx) hR)
        (mul_le_mul hsy hvel (norm_nonneg _) hhalf)
    _ = 2 * (u / n) +
        fineGlobalAccelerationBound k n * (y - x) ^ 2 +
        localMeshHalfWidth n *
          (fineGlobalAccelerationBound k n * |y - x|) := by ring

lemma localMeshCenterDistance_le_of_two_representatives_fine
    (k n : ℕ) (hn : 0 < n) (e : SignVector (2 * n))
    (hgood : ¬HasHighFineMeshAcceleration k n e)
    (u velocityLower velocityUpper : ℝ)
    (hu : 0 ≤ u) (hvelocityLower : 0 < velocityLower)
    (a b : Fin (localMeshSize n))
    (ha : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)
    (hb : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e b)
    (hquadratic : fineGlobalAccelerationBound k n *
      |localMeshPoint n b - localMeshPoint n a| ≤ velocityLower / 4)
    (hcell : fineGlobalAccelerationBound k n * localMeshHalfWidth n ≤
      velocityLower / 4) :
    |localMeshPoint n b - localMeshPoint n a| ≤
      4 * localMeshHalfWidth n +
        4 * (u / n) / velocityLower := by
  let x : ℝ := localMeshPoint n a
  let y : ℝ := localMeshPoint n b
  let sx : ℝ := localAffineOffset n e a
  let sy : ℝ := localAffineOffset n e b
  let h : ℝ := localMeshHalfWidth n
  let C : ℝ := fineGlobalAccelerationBound k n
  let d : ℝ := |y - x|
  let q : ℝ := u / n
  have hd : 0 ≤ d := abs_nonneg _
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C, fineGlobalAccelerationBound]
    exact add_nonneg (rigidityPower_nonneg n _)
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (by unfold localMeshHalfWidth; positivity))
  have hh : 0 ≤ h := by
    dsimp [h, localMeshHalfWidth]
    positivity
  have hsx : |sx| ≤ h := by
    simpa [sx, h] using ha.1.2.1
  have hsy : |sy| ≤ h := by
    simpa [sy, h] using hb.1.2.1
  have hadjusted : d - 2 * h ≤ |(y + sy) - (x + sx)| := by
    exact centerDistance_sub_offsets_le_adjustedDistance x y sx sy h hsx hsy
  have hpair : velocityLower * |(y + sy) - (x + sx)| ≤
      2 * q + C * d ^ 2 + h * (C * d) := by
    simpa [x, y, sx, sy, h, C, d, q, sq_abs] using
      localRepresentative_pair_affine_displacement_bound_fine
        k n hn e hgood u velocityLower velocityUpper a b ha hb
  have hleft : velocityLower * (d - 2 * h) ≤
      velocityLower * |(y + sy) - (x + sx)| :=
    mul_le_mul_of_nonneg_left hadjusted hvelocityLower.le
  have hquad : C * d ≤ velocityLower / 4 := by
    simpa [C, d, x, y] using hquadratic
  have hcell' : C * h ≤ velocityLower / 4 := by
    simpa [C, h, mul_comm] using hcell
  have hquadTerm : C * d ^ 2 ≤ velocityLower / 4 * d := by
    calc
      C * d ^ 2 = (C * d) * d := by ring
      _ ≤ (velocityLower / 4) * d :=
        mul_le_mul_of_nonneg_right hquad hd
  have hcellTerm : h * (C * d) ≤ velocityLower / 4 * d := by
    calc
      h * (C * d) = (C * h) * d := by ring
      _ ≤ (velocityLower / 4) * d :=
        mul_le_mul_of_nonneg_right hcell' hd
  have hmul : velocityLower * d ≤
      4 * velocityLower * h + 4 * q := by
    nlinarith [hleft.trans hpair]
  calc
    d = (velocityLower * d) / velocityLower := by field_simp
    _ ≤ (4 * velocityLower * h + 4 * q) / velocityLower :=
      div_le_div_of_nonneg_right hmul hvelocityLower.le
    _ = 4 * h + 4 * q / velocityLower := by field_simp

lemma localRepresentative_pair_affine_location_bound_fine
    (k n : ℕ) (hn : 0 < n) (e : SignVector (2 * n))
    (hgood : ¬HasHighFineMeshAcceleration k n e)
    (u velocityLower velocityUpper : ℝ)
    (hu : 0 ≤ u) (hvelocityLower : 0 ≤ velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper)
    (a b : Fin (localMeshSize n))
    (ha : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)
    (hb : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e b) :
    velocityLower ^ 2 *
        |(localMeshPoint n b + localAffineOffset n e b) -
          (localMeshPoint n a + localAffineOffset n e a)| ≤
      (u / n) *
          (fineGlobalAccelerationBound k n *
            |localMeshPoint n b - localMeshPoint n a|) +
        (fineGlobalAccelerationBound k n *
            (localMeshPoint n b - localMeshPoint n a) ^ 2) *
          velocityUpper +
        localMeshHalfWidth n *
          (fineGlobalAccelerationBound k n *
            |localMeshPoint n b - localMeshPoint n a|) *
          velocityUpper := by
  let x : ℝ := localMeshPoint n a
  let y : ℝ := localMeshPoint n b
  let sx : ℝ := localAffineOffset n e a
  let sy : ℝ := localAffineOffset n e b
  let X : ℂ := rescaledCenteredEval n e x
  let Y : ℂ := rescaledCenteredEval n e y
  let Bx : ℂ := rescaledCenteredVelocity n e x
  let By : ℂ := rescaledCenteredVelocity n e y
  let Ax : ℂ := X + (sx : ℂ) * Bx
  let Ay : ℂ := Y + (sy : ℂ) * By
  let R : ℂ := Y - (X + ((y - x : ℝ) : ℂ) * Bx)
  let dr : ℝ := (y + sy) - (x + sx)
  have hx : x ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n) :=
    ⟨(localMeshPoint_mem_Ico n hn a).1,
      (localMeshPoint_mem_Ico n hn a).2.le⟩
  have hy : y ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n) :=
    ⟨(localMeshPoint_mem_Ico n hn b).1,
      (localMeshPoint_mem_Ico n hn b).2.le⟩
  have hAy : ‖Ay‖ ≤ u / n := by
    simpa [Ay, Y, By, sy, y] using hb.1.affine_norm_le hn
  have hR : ‖R‖ ≤ fineGlobalAccelerationBound k n * (y - x) ^ 2 := by
    simpa [R, X, Y, Bx] using
      norm_rescaledCenteredEval_sub_linear_le_of_not_highFine
        k n hn e hgood x y hx hy
  have hvel : ‖By - Bx‖ ≤
      fineGlobalAccelerationBound k n * |y - x| := by
    simpa [Bx, By] using
      norm_rescaledCenteredVelocity_sub_le_of_not_highFine
        k n hn e hgood x y hx hy
  have hsy : |sy| ≤ localMeshHalfWidth n := by
    simpa [sy] using hb.1.2.1
  have hBxLower : velocityLower ≤ ‖Bx‖ := by
    simpa [Bx, x] using ha.2.1
  have hBxUpper : ‖Bx‖ ≤ velocityUpper := by
    simpa [Bx, x] using ha.2.2
  have hBx : Bx ≠ 0 := by
    simpa [Bx, x] using ha.1.1
  have hBy : By ≠ 0 := by
    simpa [By, y] using hb.1.1
  have hAxOrth : (Ax * conj Bx).re = 0 := by
    simpa [Ax, X, Bx, sx, x, localAffineOffset] using
      affineClosestOffset_real_projection_zero X Bx hBx
  have hAyOrth : (Ay * conj By).re = 0 := by
    simpa [Ay, Y, By, sy, y, localAffineOffset] using
      affineClosestOffset_real_projection_zero Y By hBy
  have hid : Ay - Ax =
      (dr : ℂ) * Bx + R + (sy : ℂ) * (By - Bx) := by
    dsimp [Ay, Ax, dr, R]
    simp only [Complex.ofReal_add, Complex.ofReal_sub]
    ring
  have hprojection : dr * Complex.normSq Bx =
      (Ay * conj (Bx - By)).re - (R * conj Bx).re -
        (((sy : ℂ) * (By - Bx)) * conj Bx).re := by
    have hrearrange : (dr : ℂ) * Bx =
        (Ay - Ax) - R - (sy : ℂ) * (By - Bx) := by
      rw [hid]
      abel
    have hAyRewrite : (Ay * conj Bx).re =
        (Ay * conj (Bx - By)).re := by
      have hc : conj Bx = conj (Bx - By) + conj By := by
        rw [map_sub]
        ring
      rw [hc, mul_add, Complex.add_re, hAyOrth, add_zero]
    calc
      dr * Complex.normSq Bx = (((dr : ℂ) * Bx) * conj Bx).re := by
        simp [Complex.normSq_apply]
        ring
      _ = (((Ay - Ax) - R - (sy : ℂ) * (By - Bx)) * conj Bx).re := by
        rw [hrearrange]
      _ = (Ay * conj (Bx - By)).re - (R * conj Bx).re -
          (((sy : ℂ) * (By - Bx)) * conj Bx).re := by
        simp only [sub_mul, Complex.sub_re, map_sub]
        rw [hAyRewrite, hAxOrth]
        rw [map_sub, mul_sub, Complex.sub_re]
        ring
  have hprojectionAbs : |dr| * ‖Bx‖ ^ 2 ≤
      ‖Ay‖ * ‖By - Bx‖ + ‖R‖ * ‖Bx‖ +
        |sy| * ‖By - Bx‖ * ‖Bx‖ := by
    have habs := congrArg abs hprojection
    rw [abs_mul, abs_of_nonneg (Complex.normSq_nonneg Bx),
      Complex.normSq_eq_norm_sq] at habs
    rw [habs]
    calc
      |(Ay * conj (Bx - By)).re - (R * conj Bx).re -
          (((sy : ℂ) * (By - Bx)) * conj Bx).re| ≤
        |(Ay * conj (Bx - By)).re| + |(R * conj Bx).re| +
          |(((sy : ℂ) * (By - Bx)) * conj Bx).re| := by
        exact (abs_sub _ _).trans
          (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ ‖Ay * conj (Bx - By)‖ + ‖R * conj Bx‖ +
          ‖((sy : ℂ) * (By - Bx)) * conj Bx‖ := by
        gcongr <;> exact Complex.abs_re_le_norm _
      _ = ‖Ay‖ * ‖By - Bx‖ + ‖R‖ * ‖Bx‖ +
          |sy| * ‖By - Bx‖ * ‖Bx‖ := by
        simp only [norm_mul, Complex.norm_conj, Complex.norm_real,
          Real.norm_eq_abs]
        rw [norm_sub_rev Bx By]
  have hleft : velocityLower ^ 2 * |dr| ≤ |dr| * ‖Bx‖ ^ 2 := by
    have hsquare : velocityLower ^ 2 ≤ ‖Bx‖ ^ 2 := by
      exact (sq_le_sq₀ hvelocityLower (norm_nonneg Bx)).2 hBxLower
    nlinarith [abs_nonneg dr]
  calc
    velocityLower ^ 2 * |dr| ≤ |dr| * ‖Bx‖ ^ 2 := hleft
    _ ≤ ‖Ay‖ * ‖By - Bx‖ + ‖R‖ * ‖Bx‖ +
          |sy| * ‖By - Bx‖ * ‖Bx‖ := hprojectionAbs
    _ ≤ (u / n) * (fineGlobalAccelerationBound k n * |y - x|) +
          (fineGlobalAccelerationBound k n * (y - x) ^ 2) * velocityUpper +
          localMeshHalfWidth n *
            (fineGlobalAccelerationBound k n * |y - x|) * velocityUpper := by
      have hnR : (0 : ℝ) ≤ n := by positivity
      have hC : 0 ≤ fineGlobalAccelerationBound k n := by
        unfold fineGlobalAccelerationBound
        exact add_nonneg (rigidityPower_nonneg n _)
          (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
            (by unfold localMeshHalfWidth; positivity))
      have hhalf : 0 ≤ localMeshHalfWidth n := by
        unfold localMeshHalfWidth
        positivity
      exact add_le_add
        (add_le_add
          (mul_le_mul hAy hvel (norm_nonneg _) (div_nonneg hu hnR))
          (mul_le_mul hR hBxUpper (norm_nonneg _)
            (mul_nonneg hC (sq_nonneg _))))
        (mul_le_mul
          (mul_le_mul hsy hvel (norm_nonneg _) hhalf)
          hBxUpper (norm_nonneg _) (mul_nonneg hhalf
            (mul_nonneg hC (abs_nonneg _))))

lemma fineAccelerationExponent_lt_one (k : ℕ) :
    fineAccelerationExponent k < 1 := by
  have hweak := weakSeparationExponent_le_ten_thousandth k
  unfold fineAccelerationExponent
  linarith

lemma weakSpreadScale_tendsto_zero (k : ℕ) :
    Tendsto (weakSpreadScale k) atTop (𝓝 0) := by
  unfold weakSpreadScale
  exact tendsto_rigidityPower_neg_zero (weakSeparationExponent_pos k)

lemma fineAccelerationCutoff_mul_weakSpread_tendsto_zero (k : ℕ) :
    Tendsto (fun n : ℕ ↦
      fineAccelerationCutoff k n * weakSpreadScale k n) atTop (𝓝 0) := by
  have hneg : 0 < 3 * weakSeparationExponent k / 4 := by
    exact div_pos (mul_pos (by norm_num) (weakSeparationExponent_pos k))
      (by norm_num)
  have h := tendsto_rigidityPower_neg_zero hneg
  apply h.congr'
  filter_upwards [Nat.eventually_pos] with n hn
  unfold fineAccelerationCutoff fineAccelerationExponent weakSpreadScale
  rw [← rigidityPower_add hn]
  congr 2
  ring

lemma sqrt_centeredCount_mul_halfWidth_tendsto_zero :
    Tendsto (fun n : ℕ ↦
      Real.sqrt (2 * n + 1 : ℝ) * localMeshHalfWidth n) atTop (𝓝 0) := by
  have h := sqrt_centeredCount_div_tendsto_zero.mul
    scaled_localMeshHalfWidth_tendsto_pi
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [Nat.eventually_pos] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

lemma fineGlobalAccelerationBound_mul_weakSpread_tendsto_zero (k : ℕ) :
    Tendsto (fun n : ℕ ↦
      fineGlobalAccelerationBound k n * weakSpreadScale k n)
      atTop (𝓝 0) := by
  have hsecond :=
    (sqrt_centeredCount_mul_halfWidth_tendsto_zero.mul
      (weakSpreadScale_tendsto_zero k)).const_mul 2
  have hsum := (fineAccelerationCutoff_mul_weakSpread_tendsto_zero k).add hsecond
  convert hsum using 1
  · funext n
    unfold fineGlobalAccelerationBound
    ring
  · norm_num

lemma fineAccelerationCutoff_div_tendsto_zero (k : ℕ) :
    Tendsto (fun n : ℕ ↦ fineAccelerationCutoff k n / (n : ℝ))
      atTop (𝓝 0) := by
  have hneg : 0 < 1 - fineAccelerationExponent k := by
    linarith [fineAccelerationExponent_lt_one k]
  have h := tendsto_rigidityPower_neg_zero hneg
  apply h.congr'
  filter_upwards [Nat.eventually_pos] with n hn
  unfold fineAccelerationCutoff rigidityPower
  rw [show (-(1 - fineAccelerationExponent k) : ℝ) =
      fineAccelerationExponent k - 1 by ring,
    Real.rpow_sub (by exact_mod_cast hn), Real.rpow_one]

lemma fineGlobalAccelerationBound_div_tendsto_zero (k : ℕ) :
    Tendsto (fun n : ℕ ↦ fineGlobalAccelerationBound k n / (n : ℝ))
      atTop (𝓝 0) := by
  have hsecond :=
    (sqrt_centeredCount_div_tendsto_zero.mul localMeshHalfWidth_tendsto_zero).const_mul 2
  have hsum := (fineAccelerationCutoff_div_tendsto_zero k).add hsecond
  convert hsum using 1
  · funext n
    by_cases hn : n = 0
    · subst n
      simp [fineGlobalAccelerationBound]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    unfold fineGlobalAccelerationBound
    field_simp
  · norm_num

lemma fineGlobalAccelerationBound_mul_halfWidth_tendsto_zero (k : ℕ) :
    Tendsto (fun n : ℕ ↦
      fineGlobalAccelerationBound k n * localMeshHalfWidth n)
      atTop (𝓝 0) := by
  have hfirst := (fineAccelerationCutoff_div_tendsto_zero k).mul
    scaled_localMeshHalfWidth_tendsto_pi
  have hsecond := localMeshTaylorError_tendsto_zero.const_mul 2
  have hsum := hfirst.add hsecond
  convert hsum using 1
  · funext n
    by_cases hn : n = 0
    · subst n
      simp [fineGlobalAccelerationBound, localMeshTaylorError,
        localMeshHalfWidth, localMeshSize]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    unfold fineGlobalAccelerationBound localMeshTaylorError
    field_simp
  · norm_num

lemma localMeshHalfWidth_le_pi_div (n : ℕ) (hn : 0 < n) :
    localMeshHalfWidth n ≤ Real.pi / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold localMeshHalfWidth localMeshSize
  norm_num
  rw [div_le_div_iff₀ (by positivity) hnR]
  nlinarith [Real.pi_pos, sq_nonneg (n : ℝ)]

lemma pi_div_two_mul_le_localMeshHalfWidth (n : ℕ) (hn : 0 < n) :
    Real.pi / (2 * n) ≤ localMeshHalfWidth n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold localMeshHalfWidth localMeshSize
  norm_num
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [Real.pi_pos, sq_nonneg ((n : ℝ) - 1)]

lemma adjustedCenterDistance_ge_two_halfWidth_of_nonadjacent
    (n : ℕ) (a b : Fin (localMeshSize n)) (sx sy : ℝ)
    (hsx : |sx| ≤ localMeshHalfWidth n)
    (hsy : |sy| ≤ localMeshHalfWidth n)
    (hne : a ≠ b)
    (hnonadj : ¬(b.val = a.val + 1 ∨ a.val = b.val + 1)) :
    2 * localMeshHalfWidth n ≤
      |(localMeshPoint n b + sy) - (localMeshPoint n a + sx)| := by
  have hhalf : 0 ≤ localMeshHalfWidth n := by
    unfold localMeshHalfWidth
    positivity
  have hindex : (2 : ℝ) ≤ |(b.val : ℝ) - (a.val : ℝ)| := by
    by_cases hab : a.val < b.val
    · have hgap : a.val + 2 ≤ b.val := by omega
      have hgapR : (a.val : ℝ) + 2 ≤ b.val := by exact_mod_cast hgap
      have habR : (a.val : ℝ) < b.val := by exact_mod_cast hab
      rw [abs_of_pos (sub_pos.mpr habR)]
      linarith
    · have hba : b.val < a.val := by
        have hvne : a.val ≠ b.val := fun h ↦ hne (Fin.ext h)
        omega
      have hgap : b.val + 2 ≤ a.val := by omega
      have hgapR : (b.val : ℝ) + 2 ≤ a.val := by exact_mod_cast hgap
      have hbaR : (b.val : ℝ) < a.val := by exact_mod_cast hba
      rw [abs_of_neg (sub_neg.mpr hbaR)]
      linarith
  have hcenter : 4 * localMeshHalfWidth n ≤
      |localMeshPoint n b - localMeshPoint n a| := by
    rw [localMeshPoint_sub_eq]
    rw [abs_mul]
    have htwoAbs : |2 * localMeshHalfWidth n| = 2 * localMeshHalfWidth n := by
      rw [abs_of_nonneg]
      positivity
    rw [htwoAbs]
    change 4 * localMeshHalfWidth n ≤
      2 * localMeshHalfWidth n * |(b.val : ℝ) - (a.val : ℝ)|
    nlinarith
  have hadjusted := centerDistance_sub_offsets_le_adjustedDistance
    (localMeshPoint n a) (localMeshPoint n b) sx sy
      (localMeshHalfWidth n) hsx hsy
  linarith

lemma localRepresentatives_adjacent_of_fine_bounds
    (k n : ℕ) (hn : 0 < n) (e : SignVector (2 * n))
    (hgood : ¬HasHighFineMeshAcceleration k n e)
    (u velocityLower velocityUpper D : ℝ)
    (hu : 0 ≤ u) (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper) (hD : 0 ≤ D)
    (a b : Fin (localMeshSize n)) (hne : a ≠ b)
    (ha : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)
    (hb : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e b)
    (hcenter : |localMeshPoint n b - localMeshPoint n a| ≤ D / n)
    (herror :
      (u / n) * (fineGlobalAccelerationBound k n * (D / n)) +
          (fineGlobalAccelerationBound k n * (D / n) ^ 2) * velocityUpper +
          localMeshHalfWidth n *
            (fineGlobalAccelerationBound k n * (D / n)) * velocityUpper <
        velocityLower ^ 2 * (2 * localMeshHalfWidth n)) :
    b.val = a.val + 1 ∨ a.val = b.val + 1 := by
  by_contra hnonadj
  have hsx : |localAffineOffset n e a| ≤ localMeshHalfWidth n := ha.1.2.1
  have hsy : |localAffineOffset n e b| ≤ localMeshHalfWidth n := hb.1.2.1
  have hlower := adjustedCenterDistance_ge_two_halfWidth_of_nonadjacent
    n a b (localAffineOffset n e a) (localAffineOffset n e b)
      hsx hsy hne hnonadj
  have hloc := localRepresentative_pair_affine_location_bound_fine
    k n hn e hgood u velocityLower velocityUpper hu hvelocityLower.le
      hvelocityUpper a b ha hb
  have hnR : (0 : ℝ) ≤ n := by positivity
  have hC : 0 ≤ fineGlobalAccelerationBound k n := by
    unfold fineGlobalAccelerationBound
    exact add_nonneg (rigidityPower_nonneg n _)
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (by unfold localMeshHalfWidth; positivity))
  have hhalf : 0 ≤ localMeshHalfWidth n := by
    unfold localMeshHalfWidth
    positivity
  have hDn : 0 ≤ D / n := div_nonneg hD hnR
  have hfirst : fineGlobalAccelerationBound k n *
      |localMeshPoint n b - localMeshPoint n a| ≤
      fineGlobalAccelerationBound k n * (D / n) :=
    mul_le_mul_of_nonneg_left hcenter hC
  have hsq : (localMeshPoint n b - localMeshPoint n a) ^ 2 ≤
      (D / n) ^ 2 := by
    have := (sq_le_sq₀ (abs_nonneg _ ) hDn).2 hcenter
    simpa only [sq_abs] using this
  have hsecond : fineGlobalAccelerationBound k n *
      (localMeshPoint n b - localMeshPoint n a) ^ 2 ≤
      fineGlobalAccelerationBound k n * (D / n) ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hC
  have hupper :
      (u / n) *
          (fineGlobalAccelerationBound k n *
            |localMeshPoint n b - localMeshPoint n a|) +
        (fineGlobalAccelerationBound k n *
            (localMeshPoint n b - localMeshPoint n a) ^ 2) * velocityUpper +
        localMeshHalfWidth n *
          (fineGlobalAccelerationBound k n *
            |localMeshPoint n b - localMeshPoint n a|) * velocityUpper ≤
      (u / n) * (fineGlobalAccelerationBound k n * (D / n)) +
        (fineGlobalAccelerationBound k n * (D / n) ^ 2) * velocityUpper +
        localMeshHalfWidth n *
          (fineGlobalAccelerationBound k n * (D / n)) * velocityUpper := by
    gcongr
  have hleft : velocityLower ^ 2 * (2 * localMeshHalfWidth n) ≤
      velocityLower ^ 2 *
        |(localMeshPoint n b + localAffineOffset n e b) -
          (localMeshPoint n a + localAffineOffset n e a)| :=
    mul_le_mul_of_nonneg_left hlower (sq_nonneg velocityLower)
  exact (not_lt_of_ge (hleft.trans (hloc.trans hupper))) herror

theorem eventually_scaledWeakClose_representatives_adjacent
    (k : ℕ) (L u velocityLower velocityUpper : ℝ)
    (hL : 0 ≤ L)
    (hu : 0 ≤ u) (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper) :
    ∀ᶠ n : ℕ in atTop, ∀ (e : SignVector (2 * n)),
      ¬HasHighFineMeshAcceleration k n e →
      ∀ a b : Fin (localMeshSize n), a ≠ b →
        IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a →
        IsTruncatedLocalRepresentative n u velocityLower velocityUpper e b →
        |localMeshPoint n b - localMeshPoint n a| < L * weakSpreadScale k n →
        b.val = a.val + 1 ∨ a.val = b.val + 1 := by
  let D : ℝ := 4 * Real.pi + 4 * u / velocityLower
  let A : ℝ := u * D + D ^ 2 * velocityUpper +
    Real.pi * D * velocityUpper
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hweakLimit : Tendsto (fun n : ℕ ↦
      fineGlobalAccelerationBound k n * (L * weakSpreadScale k n))
      atTop (𝓝 0) := by
    have h :=
      (fineGlobalAccelerationBound_mul_weakSpread_tendsto_zero k).const_mul L
    convert h using 1
    · funext n
      ring
    · ring
  have hweak : ∀ᶠ n : ℕ in atTop,
      fineGlobalAccelerationBound k n * (L * weakSpreadScale k n) <
        velocityLower / 4 :=
    hweakLimit.eventually (Iio_mem_nhds (by positivity))
  have hcell : ∀ᶠ n : ℕ in atTop,
      fineGlobalAccelerationBound k n * localMeshHalfWidth n <
        velocityLower / 4 :=
    (fineGlobalAccelerationBound_mul_halfWidth_tendsto_zero k).eventually
      (Iio_mem_nhds (by positivity))
  have hnormalized : Tendsto (fun n : ℕ ↦
      A * (fineGlobalAccelerationBound k n / (n : ℝ))) atTop (𝓝 0) := by
    simpa using (fineGlobalAccelerationBound_div_tendsto_zero k).const_mul A
  have herrorScale : ∀ᶠ n : ℕ in atTop,
      A * (fineGlobalAccelerationBound k n / (n : ℝ)) <
        velocityLower ^ 2 * Real.pi :=
    hnormalized.eventually (Iio_mem_nhds (by positivity))
  filter_upwards [Nat.eventually_pos, hweak, hcell, herrorScale]
    with n hn hweakN hcellN herrorN
  intro e hgood a b hne ha hb hclose
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hC : 0 ≤ fineGlobalAccelerationBound k n := by
    unfold fineGlobalAccelerationBound
    exact add_nonneg (rigidityPower_nonneg n _)
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (by unfold localMeshHalfWidth; positivity))
  have hhalf : 0 ≤ localMeshHalfWidth n := by
    unfold localMeshHalfWidth
    positivity
  have hquadratic : fineGlobalAccelerationBound k n *
      |localMeshPoint n b - localMeshPoint n a| ≤ velocityLower / 4 := by
    exact (mul_le_mul_of_nonneg_left hclose.le hC).trans hweakN.le
  have hcenterRaw := localMeshCenterDistance_le_of_two_representatives_fine
    k n hn e hgood u velocityLower velocityUpper hu hvelocityLower a b ha hb
      hquadratic hcellN.le
  have hcenter : |localMeshPoint n b - localMeshPoint n a| ≤ D / n := by
    have hhUpper := localMeshHalfWidth_le_pi_div n hn
    dsimp [D]
    calc
      _ ≤ 4 * localMeshHalfWidth n + 4 * (u / n) / velocityLower := hcenterRaw
      _ ≤ 4 * (Real.pi / n) + 4 * (u / n) / velocityLower := by gcongr
      _ = (4 * Real.pi + 4 * u / velocityLower) / n := by
        field_simp
  have hhalfLower := pi_div_two_mul_le_localMeshHalfWidth n hn
  have hleftLower : velocityLower ^ 2 * (Real.pi / n) ≤
      velocityLower ^ 2 * (2 * localMeshHalfWidth n) := by
    have htwo : Real.pi / n ≤ 2 * localMeshHalfWidth n := by
      calc
        Real.pi / n = 2 * (Real.pi / (2 * n)) := by ring
        _ ≤ 2 * localMeshHalfWidth n :=
          mul_le_mul_of_nonneg_left hhalfLower (by norm_num)
    exact mul_le_mul_of_nonneg_left htwo (sq_nonneg velocityLower)
  let error : ℝ :=
      (u / n) * (fineGlobalAccelerationBound k n * (D / n)) +
        (fineGlobalAccelerationBound k n * (D / n) ^ 2) * velocityUpper +
        localMeshHalfWidth n *
          (fineGlobalAccelerationBound k n * (D / n)) * velocityUpper
  have herrorUpper : error ≤
      (A * (fineGlobalAccelerationBound k n / n)) / n := by
    have hhUpper := localMeshHalfWidth_le_pi_div n hn
    dsimp [error, A]
    have hDn : 0 ≤ D / n := div_nonneg hD hnR.le
    calc
      (u / n) * (fineGlobalAccelerationBound k n * (D / n)) +
          (fineGlobalAccelerationBound k n * (D / n) ^ 2) * velocityUpper +
          localMeshHalfWidth n *
            (fineGlobalAccelerationBound k n * (D / n)) * velocityUpper ≤
        (u / n) * (fineGlobalAccelerationBound k n * (D / n)) +
          (fineGlobalAccelerationBound k n * (D / n) ^ 2) * velocityUpper +
          (Real.pi / n) *
            (fineGlobalAccelerationBound k n * (D / n)) * velocityUpper := by
          gcongr
      _ = ((u * D + D ^ 2 * velocityUpper +
          Real.pi * D * velocityUpper) *
            (fineGlobalAccelerationBound k n / n)) / n := by
        field_simp
  have herrorFinal : error <
      velocityLower ^ 2 * (2 * localMeshHalfWidth n) := by
    have hdiv :
        (A * (fineGlobalAccelerationBound k n / n)) / n <
          (velocityLower ^ 2 * Real.pi) / n :=
      (div_lt_div_iff_of_pos_right hnR).2 herrorN
    have hid : (velocityLower ^ 2 * Real.pi) / n =
        velocityLower ^ 2 * (Real.pi / n) := by ring
    rw [hid] at hdiv
    exact herrorUpper.trans_lt (hdiv.trans_le hleftLower)
  exact localRepresentatives_adjacent_of_fine_bounds
    k n hn e hgood u velocityLower velocityUpper D hu hvelocityLower
      hvelocityUpper hD a b hne ha hb hcenter (by simpa [error] using herrorFinal)

lemma localMeshPoint_bounds_of_mem_half
    (n : ℕ) (hn : 0 < n) (a : Fin (localMeshSize n))
    (ha : a ∈ halfLocalMeshSites n) :
    0 ≤ localMeshPoint n a ∧ localMeshPoint n a < Real.pi * n := by
  rw [halfLocalMeshSites, Finset.mem_image] at ha
  rcases ha with ⟨b, _hb, rfl⟩
  exact ⟨halfLocalMeshPoint_nonneg n b,
    halfLocalMeshPoint_lt_pi_mul n hn b⟩

lemma half_sum_close_forces_endpoint_close
    (n : ℕ) (hn : 0 < n) (x y delta : ℝ)
    (hx : 0 ≤ x ∧ x < Real.pi * n)
    (hy : 0 ≤ y ∧ y < Real.pi * n)
    (hsum : distanceToInteger ((x + y) / (2 * Real.pi * n)) < delta) :
    distanceToInteger (x / (Real.pi * n)) < 2 * delta := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpiN : 0 < Real.pi * (n : ℝ) := mul_pos Real.pi_pos hnR
  let a : ℝ := x / (Real.pi * n)
  let b : ℝ := y / (Real.pi * n)
  let z : ℝ := (a + b) / 2
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg hx.1 hpiN.le
  have hb0 : 0 ≤ b := by
    dsimp [b]
    exact div_nonneg hy.1 hpiN.le
  have ha1 : a < 1 := by
    dsimp [a]
    exact (div_lt_one hpiN).2 hx.2
  have hb1 : b < 1 := by
    dsimp [b]
    exact (div_lt_one hpiN).2 hy.2
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hz1 : z < 1 := by dsimp [z]; linarith
  have hsum' : distanceToInteger z < delta := by
    have heq : (x + y) / (2 * Real.pi * n) = z := by
      dsimp [z, a, b]
      field_simp
    simpa [heq] using hsum
  by_cases hzhalf : z ≤ 1 / 2
  · have hdistz := distanceToInteger_eq_self_of_nonneg_le_half hz0 hzhalf
    have hzdelta : z < delta := by simpa [hdistz] using hsum'
    have hada : distanceToInteger a ≤ a := by
      have hmin := distanceToInteger_minimal a 0
      simpa [abs_of_nonneg ha0] using hmin
    have hadelta : a < 2 * delta := by
      dsimp [z] at hzdelta
      linarith [hb0]
    exact hada.trans_lt hadelta
  · have hzhalf' : 1 / 2 < z := lt_of_not_ge hzhalf
    have hdistz := distanceToInteger_eq_one_sub_of_half_lt_lt_one hzhalf' hz1
    have hzdelta : 1 - z < delta := by simpa [hdistz] using hsum'
    have hada : distanceToInteger a ≤ 1 - a := by
      have hmin := distanceToInteger_minimal a 1
      have habs : |a - (1 : ℝ)| = 1 - a := by
        rw [abs_of_nonpos (sub_nonpos.mpr ha1.le)]
        ring
      simpa [habs] using hmin
    have hadelta : 1 - a < 2 * delta := by
      dsimp [z] at hzdelta
      linarith [hb1]
    exact hada.trans_lt hadelta

lemma smooth_excludes_weak_singleton
    (n : ℕ) (hn : 0 < n) (K lam t : ℝ)
    (hscale : 2 * lam ≤ K)
    (hsmooth : IsSmooth n K t) :
    lam / n ≤ distanceToInteger (t / (2 * Real.pi * n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_contra hnot
  have hsmall : distanceToInteger (t / (2 * Real.pi * n)) < lam / n :=
    lt_of_not_ge hnot
  have hdouble := distanceToInteger_nsmul_le 2 (t / (2 * Real.pi * n))
  norm_num at hdouble
  have heq : 2 * (t / (2 * Real.pi * n)) = t / (Real.pi * n) := by
    field_simp
  rw [heq] at hdouble
  have hsmoothOne := hsmooth 1 (by omega) (by omega)
  norm_num at hsmoothOne
  have hupper : distanceToInteger (t / (Real.pi * n)) < K / n := by
    calc
      _ ≤ 2 * distanceToInteger (t / (2 * Real.pi * n)) := hdouble
      _ < 2 * (lam / n) := mul_lt_mul_of_pos_left hsmall (by norm_num)
      _ ≤ K / n := by
        rw [show 2 * (lam / n) = (2 * lam) / n by ring]
        exact div_le_div_of_nonneg_right hscale hnR.le
  exact (not_lt_of_ge hsmoothOne.le) hupper

lemma smooth_half_excludes_weak_sum
    (n : ℕ) (hn : 0 < n) (K lam x y : ℝ)
    (hscale : 2 * lam ≤ K)
    (hx : 0 ≤ x ∧ x < Real.pi * n)
    (hy : 0 ≤ y ∧ y < Real.pi * n)
    (hsmooth : IsSmooth n K x) :
    lam / n ≤ distanceToInteger ((x + y) / (2 * Real.pi * n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_contra hnot
  have hsum : distanceToInteger ((x + y) / (2 * Real.pi * n)) < lam / n :=
    lt_of_not_ge hnot
  have hend := half_sum_close_forces_endpoint_close n hn x y (lam / n) hx hy hsum
  have hsmoothOne := hsmooth 1 (by omega) (by omega)
  norm_num at hsmoothOne
  have hupper : distanceToInteger (x / (Real.pi * n)) < K / n := by
    calc
      _ < 2 * (lam / n) := hend
      _ ≤ K / n := by
        rw [show 2 * (lam / n) = (2 * lam) / n by ring]
        exact div_le_div_of_nonneg_right hscale hnR.le
  exact (not_lt_of_ge hsmoothOne.le) hupper

lemma halfSmooth_not_weakSpread_has_close_pair
    (n : ℕ) (hn : 0 < n) (k : ℕ)
    (hscale : 2 * weakSpreadScale k n ≤ rigiditySmoothScale n)
    (s : Finset (Fin (localMeshSize n)))
    (hsub : s ⊆ halfSmoothLocalMeshSites n)
    (hnot : ¬IsSpread n (weakSpreadScale k n) (localSitesPoints s)) :
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧
      |localMeshPoint n b - localMeshPoint n a| <
        2 * Real.pi * weakSpreadScale k n := by
  have hsmooth : ∀ r : Fin s.card,
      IsSmooth n (rigiditySmoothScale n) (localSitesPoints s r) := by
    intro r
    exact (Finset.mem_filter.mp (hsub (localSite_mem s r))).2
  have hhalf : ∀ r : Fin s.card,
      localSite s r ∈ halfLocalMeshSites n := by
    intro r
    exact (Finset.mem_filter.mp (hsub (localSite_mem s r))).1
  unfold IsSpread at hnot
  rw [not_and_or] at hnot
  rcases hnot with hsingle | hpairs
  · push Not at hsingle
    rcases hsingle with ⟨hcard, r, hr⟩
    exact False.elim (not_lt_of_ge
      (smooth_excludes_weak_singleton n hn
        (rigiditySmoothScale n) (weakSpreadScale k n)
        (localSitesPoints s r) hscale (hsmooth r)) hr)
  · push Not at hpairs
    rcases hpairs with ⟨r, q, hrq, hpairs⟩
    by_cases hdiff : weakSpreadScale k n / n ≤
        distanceToInteger
          ((localSitesPoints s r - localSitesPoints s q) /
            (2 * Real.pi * n))
    · have hsum := hpairs hdiff
      have hrBounds := localMeshPoint_bounds_of_mem_half n hn
        (localSite s r) (hhalf r)
      have hqBounds := localMeshPoint_bounds_of_mem_half n hn
        (localSite s q) (hhalf q)
      exact False.elim (not_lt_of_ge
        (smooth_half_excludes_weak_sum n hn
          (rigiditySmoothScale n) (weakSpreadScale k n)
          (localSitesPoints s r) (localSitesPoints s q) hscale
          (by simpa [localSitesPoints] using hrBounds)
          (by simpa [localSitesPoints] using hqBounds) (hsmooth r)) hsum)
    · have hdist : distanceToInteger
          ((localSitesPoints s r - localSitesPoints s q) /
            (2 * Real.pi * n)) < weakSpreadScale k n / n :=
        lt_of_not_ge hdiff
      let a := localSite s r
      let b := localSite s q
      have hab : a ≠ b := by
        intro hab
        apply hrq
        apply (s.equivFin.symm.injective)
        exact Subtype.ext hab
      refine ⟨a, localSite_mem s r, b, localSite_mem s q, hab, ?_⟩
      have harg :
          |(localSitesPoints s r - localSitesPoints s q) /
              (2 * Real.pi * n)| < 1 / 2 := by
        have hrBounds := localMeshPoint_bounds_of_mem_half n hn a (hhalf r)
        have hqBounds := localMeshPoint_bounds_of_mem_half n hn b (hhalf q)
        have habs : |localSitesPoints s r - localSitesPoints s q| <
            Real.pi * n := by
          dsimp [localSitesPoints, a, b]
          rw [abs_lt]
          constructor <;> linarith
        rw [abs_div]
        have hden : |2 * Real.pi * (n : ℝ)| = 2 * Real.pi * n := by
          rw [abs_of_pos]
          positivity
        rw [hden, div_lt_iff₀ (by positivity)]
        nlinarith
      rw [distanceToInteger_eq_abs_of_abs_lt_half harg] at hdist
      dsimp [localSitesPoints, a, b] at hdist ⊢
      rw [abs_div] at hdist
      have hden : |2 * Real.pi * (n : ℝ)| = 2 * Real.pi * n := by
        rw [abs_of_pos]
        positivity
      rw [hden] at hdist
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hdenPos : 0 < 2 * Real.pi * (n : ℝ) := by positivity
      have hmul := (div_lt_div_iff₀ hdenPos hnR).mp hdist
      have hprod :
          |localMeshPoint n (localSite s q) -
              localMeshPoint n (localSite s r)| * n <
            (2 * Real.pi * weakSpreadScale k n) * n := by
        calc
        |localMeshPoint n (localSite s q) -
            localMeshPoint n (localSite s r)| * n =
            |localMeshPoint n (localSite s r) -
              localMeshPoint n (localSite s q)| * n := by
              rw [abs_sub_comm]
        _ < weakSpreadScale k n * (2 * Real.pi * n) := hmul
        _ = (2 * Real.pi * weakSpreadScale k n) * n := by ring
      exact lt_of_mul_lt_mul_right hprod hnR.le

lemma eventually_two_weakSpreadScale_le_rigiditySmoothScale (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      2 * weakSpreadScale k n ≤ rigiditySmoothScale n := by
  have hexponent : -weakSeparationExponent k < rigiditySmoothExponent := by
    unfold rigiditySmoothExponent
    linarith [weakSeparationExponent_pos k]
  simpa [weakSpreadScale, rigiditySmoothScale] using
    (eventually_const_mul_rigidityPower_le
      2 (-weakSeparationExponent k) rigiditySmoothExponent hexponent)

theorem eventually_halfVeryClose_representatives_have_adjacent_pair
    (k : ℕ) (u velocityLower velocityUpper : ℝ)
    (hu : 0 ≤ u) (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper) :
    ∀ᶠ n : ℕ in atTop, ∀ (e : SignVector (2 * n)),
      ¬HasHighFineMeshAcceleration k n e →
      ∀ s ∈ halfVeryCloseLocalSiteSets n k,
        (∀ a ∈ s,
          IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a) →
        ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧
          (b.val = a.val + 1 ∨ a.val = b.val + 1) := by
  filter_upwards [Nat.eventually_pos,
      eventually_two_weakSpreadScale_le_rigiditySmoothScale k,
      eventually_scaledWeakClose_representatives_adjacent
        k (2 * Real.pi) u velocityLower velocityUpper
          (by positivity) hu hvelocityLower hvelocityUpper]
    with n hn hscale hadj
  intro e hfine s hs hreps
  have hclose := Finset.mem_filter.mp hs
  have hnonspread := Finset.mem_filter.mp hclose.1
  have hpowerset := Finset.mem_powersetCard.mp hnonspread.1
  rcases halfSmooth_not_weakSpread_has_close_pair n hn k hscale s
      hpowerset.1 hclose.2 with ⟨a, ha, b, hb, hab, hdist⟩
  exact ⟨a, ha, b, hb, hab,
    hadj e hfine a b hab (hreps a ha) (hreps b hb) hdist⟩

noncomputable def fineAdjacentAffineLocationError
    (k n : ℕ) (u velocityLower velocityUpper : ℝ) : ℝ :=
  ((u / n) *
      (fineGlobalAccelerationBound k n * (2 * localMeshHalfWidth n)) +
    (fineGlobalAccelerationBound k n * (2 * localMeshHalfWidth n) ^ 2) *
      velocityUpper +
    localMeshHalfWidth n *
      (fineGlobalAccelerationBound k n * (2 * localMeshHalfWidth n)) *
      velocityUpper) / velocityLower ^ 2

lemma adjacentRepresentatives_affine_locations_close_fine
    (k n : ℕ) (hn : 0 < n) (e : SignVector (2 * n))
    (hgood : ¬HasHighFineMeshAcceleration k n e)
    (u velocityLower velocityUpper : ℝ)
    (hu : 0 ≤ u) (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper)
    (a b : Fin (localMeshSize n)) (hab : b.val = a.val + 1)
    (ha : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)
    (hb : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e b) :
    |(localMeshPoint n b + localAffineOffset n e b) -
        (localMeshPoint n a + localAffineOffset n e a)| ≤
      fineAdjacentAffineLocationError k n u velocityLower velocityUpper := by
  have hbound := localRepresentative_pair_affine_location_bound_fine
    k n hn e hgood u velocityLower velocityUpper hu hvelocityLower.le
      hvelocityUpper a b ha hb
  rw [localMeshPoint_sub_eq_two_halfWidth_of_succ n a b hab] at hbound
  have hsq : velocityLower ^ 2 > 0 := sq_pos_of_pos hvelocityLower
  have htwo : 0 ≤ 2 * localMeshHalfWidth n := by
    unfold localMeshHalfWidth
    positivity
  rw [abs_of_nonneg htwo] at hbound
  unfold fineAdjacentAffineLocationError
  exact (le_div_iff₀ hsq).2 (by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hbound)

lemma adjacentRepresentatives_offsets_near_boundary_fine
    (k n : ℕ) (hn : 0 < n) (e : SignVector (2 * n))
    (hgood : ¬HasHighFineMeshAcceleration k n e)
    (u velocityLower velocityUpper : ℝ)
    (hu : 0 ≤ u) (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper)
    (a b : Fin (localMeshSize n)) (hab : b.val = a.val + 1)
    (ha : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)
    (hb : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e b) :
    localMeshHalfWidth n - localAffineOffset n e a ≤
        fineAdjacentAffineLocationError k n u velocityLower velocityUpper ∧
      localMeshHalfWidth n + localAffineOffset n e b ≤
        fineAdjacentAffineLocationError k n u velocityLower velocityUpper := by
  let h : ℝ := localMeshHalfWidth n
  let sx : ℝ := localAffineOffset n e a
  let sy : ℝ := localAffineOffset n e b
  have hsx : |sx| ≤ h := by simpa [sx, h] using ha.1.2.1
  have hsy : |sy| ≤ h := by simpa [sy, h] using hb.1.2.1
  have hloc := adjacentRepresentatives_affine_locations_close_fine
    k n hn e hgood u velocityLower velocityUpper hu hvelocityLower
      hvelocityUpper a b hab ha hb
  have hid :
      (localMeshPoint n b + localAffineOffset n e b) -
          (localMeshPoint n a + localAffineOffset n e a) =
        (h - sx) + (h + sy) := by
    dsimp [h, sx, sy]
    have hcenter := localMeshPoint_sub_eq_two_halfWidth_of_succ n a b hab
    linarith
  have hfirst : 0 ≤ h - sx := by
    rw [sub_nonneg]
    exact (le_abs_self sx).trans hsx
  have hsecond : 0 ≤ h + sy := by
    rw [← neg_le_iff_add_nonneg]
    exact (neg_le_abs sy).trans hsy
  rw [hid, abs_of_nonneg (add_nonneg hfirst hsecond)] at hloc
  exact ⟨(le_add_of_nonneg_right hsecond).trans hloc,
    (le_add_of_nonneg_left hfirst).trans hloc⟩

theorem fineAdjacentAffineLocationError_relative_tendsto_zero
    (k : ℕ) (u velocityLower velocityUpper : ℝ)
    (hvelocityLower : velocityLower ≠ 0) :
    Tendsto (fun n : ℕ ↦
      fineAdjacentAffineLocationError k n u velocityLower velocityUpper /
        localMeshHalfWidth n) atTop (𝓝 0) := by
  let reference : ℕ → ℝ := fun n ↦
    (2 * u * (fineGlobalAccelerationBound k n / (n : ℝ)) +
      6 * velocityUpper *
        (fineGlobalAccelerationBound k n * localMeshHalfWidth n)) /
      velocityLower ^ 2
  have href : Tendsto reference atTop (𝓝 0) := by
    have hnum :=
      (fineGlobalAccelerationBound_div_tendsto_zero k).const_mul (2 * u) |>.add
        ((fineGlobalAccelerationBound_mul_halfWidth_tendsto_zero k).const_mul
          (6 * velocityUpper))
    have hdiv := hnum.div_const (velocityLower ^ 2)
    simpa [reference] using hdiv
  apply href.congr'
  filter_upwards [Nat.eventually_pos] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hh : localMeshHalfWidth n ≠ 0 := by
    unfold localMeshHalfWidth
    exact div_ne_zero (mul_ne_zero Real.pi_ne_zero (by exact_mod_cast hn.ne'))
      (by exact_mod_cast (localMeshSize_pos n).ne')
  dsimp [reference]
  unfold fineAdjacentAffineLocationError
  field_simp
  ring

lemma adjacentRepresentatives_rightBoundary_of_not_highFine
    (k : ℕ) (eta u velocityLower velocityUpper : ℝ)
    (heta : 0 < eta)
    (n : ℕ) (hn : 0 < n)
    (herr : fineAdjacentAffineLocationError k n u velocityLower velocityUpper /
        localMeshHalfWidth n < eta)
    (e : SignVector (2 * n)) (hgood : ¬HasHighFineMeshAcceleration k n e)
    (a b : Fin (localMeshSize n)) (hab : b.val = a.val + 1)
    (ha : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)
    (hb : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e b)
    (hu : 0 ≤ u) (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper) :
    IsRightBoundaryTruncatedLocalRepresentative n eta u
      velocityLower velocityUpper e a := by
  refine ⟨ha, ?_⟩
  have hnear := (adjacentRepresentatives_offsets_near_boundary_fine
    k n hn e hgood u velocityLower velocityUpper hu hvelocityLower
      hvelocityUpper a b hab ha hb).1
  have hhalf : 0 < localMeshHalfWidth n := by
    unfold localMeshHalfWidth
    exact div_pos (mul_pos Real.pi_pos (by exact_mod_cast hn))
      (by exact_mod_cast localMeshSize_pos n)
  have herr' : fineAdjacentAffineLocationError k n u velocityLower velocityUpper <
      eta * localMeshHalfWidth n := (div_lt_iff₀ hhalf).mp herr
  nlinarith

theorem eventually_uniform_scaled_good_factoredTruncatedLocalProbability
    (m : ℕ) (hm : 0 < m)
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor : 0 < widthFactor) (hu : 0 < u)
    (hvelLower : 0 < velocityLower) (hvelUpper : 0 < velocityUpper)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ s : Finset (Fin (localMeshSize n)),
      s ∈ Finset.univ.powersetCard m →
      IsGoodLocalSiteSet n s →
      |(localMeshSize n : ℝ) ^ m *
          uniformProbability (fun e : SignVector (2 * n) ↦
            ∀ a ∈ s,
              IsFactoredTruncatedLocalRepresentative n widthFactor u
                velocityLower velocityUpper e a) -
        ((widthFactor * ((12 * u / Real.pi) *
          blockVelocityMass velocityLower velocityUpper)) ^ m)| < eps := by
  filter_upwards [Nat.eventually_pos,
      eventually_uniform_scaled_factoredTruncatedPhaseProbability
        m hm widthFactor u velocityLower velocityUpper hfactor hu hvelLower
          hvelUpper heps]
    with n hn hprob
  intro s hs hgood
  have hcard : s.card = m := (Finset.mem_powersetCard.mp hs).2
  subst m
  rw [joint_factoredTruncatedLocalProbability_eq_phase
    n hn widthFactor u velocityLower velocityUpper hvelLower s]
  exact hprob (localSitesPoints s) hgood.smooth_points hgood.2

noncomputable def halfGoodFactoredTruncatedChooseContribution
    (n m : ℕ) (widthFactor u velocityLower velocityUpper : ℝ) : ℝ :=
  ∑ s ∈ halfGoodLocalSiteSets n m,
    uniformProbability (fun e : SignVector (2 * n) ↦
      ∀ a ∈ s,
        IsFactoredTruncatedLocalRepresentative n widthFactor u
          velocityLower velocityUpper e a)

theorem eventually_halfGoodFactoredTruncatedChooseContribution_close
    (m : ℕ) (hm : 0 < m)
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor : 0 < widthFactor) (hu : 0 < u)
    (hvelLower : 0 < velocityLower) (hvelUpper : 0 < velocityUpper)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      |halfGoodFactoredTruncatedChooseContribution n m widthFactor u
          velocityLower velocityUpper -
        ((widthFactor * ((12 * u / Real.pi) *
          blockVelocityMass velocityLower velocityUpper)) ^ m) *
          ((halfGoodLocalSiteSets n m).card : ℝ) /
            (localMeshSize n : ℝ) ^ m| < eps := by
  have hlocal := eventually_uniform_scaled_good_factoredTruncatedLocalProbability
    m hm widthFactor u velocityLower velocityUpper hfactor hu hvelLower hvelUpper
      (half_pos heps)
  filter_upwards [hlocal] with n hn
  let A : ℝ := (widthFactor * ((12 * u / Real.pi) *
    blockVelocityMass velocityLower velocityUpper)) ^ m
  let q : ℝ := (localMeshSize n : ℝ) ^ m
  have hqpos : 0 < q := by
    dsimp [q]
    exact pow_pos (by exact_mod_cast localMeshSize_pos n) m
  have hcardNat : (halfGoodLocalSiteSets n m).card ≤ localMeshSize n ^ m := by
    calc
      (halfGoodLocalSiteSets n m).card ≤
          ((halfLocalMeshSites n).powersetCard m).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = (halfLocalMeshSize n).choose m := by
        rw [Finset.card_powersetCard, card_halfLocalMeshSites]
      _ ≤ (halfLocalMeshSize n) ^ m := Nat.choose_le_pow _ _
      _ ≤ (localMeshSize n) ^ m :=
        Nat.pow_le_pow_left (Nat.div_le_self _ _) m
  have hcardR : ((halfGoodLocalSiteSets n m).card : ℝ) ≤ q := by
    dsimp [q]
    exact_mod_cast hcardNat
  have hsum :
      |∑ s ∈ halfGoodLocalSiteSets n m,
          (q * uniformProbability (fun e : SignVector (2 * n) ↦
              ∀ a ∈ s,
                IsFactoredTruncatedLocalRepresentative n widthFactor u
                  velocityLower velocityUpper e a) - A)| ≤
        ((halfGoodLocalSiteSets n m).card : ℝ) * (eps / 2) := by
    calc
      _ ≤ ∑ s ∈ halfGoodLocalSiteSets n m,
          |q * uniformProbability (fun e : SignVector (2 * n) ↦
              ∀ a ∈ s,
                IsFactoredTruncatedLocalRepresentative n widthFactor u
                  velocityLower velocityUpper e a) - A| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s ∈ halfGoodLocalSiteSets n m, eps / 2 := by
        apply Finset.sum_le_sum
        intro s hs
        have hhalf := (Finset.mem_filter.mp hs).1
        have hall : s ∈ Finset.univ.powersetCard m := by
          rw [Finset.mem_powersetCard] at hhalf ⊢
          exact ⟨Finset.subset_univ s, hhalf.2⟩
        have hgood := (Finset.mem_filter.mp hs).2
        simpa [q, A] using (hn s hall hgood).le
      _ = ((halfGoodLocalSiteSets n m).card : ℝ) * (eps / 2) := by simp
  rw [halfGoodFactoredTruncatedChooseContribution,
    sum_sub_normalized_card _ _ q A hqpos.ne']
  rw [abs_div, abs_of_pos hqpos]
  calc
    _ ≤ (((halfGoodLocalSiteSets n m).card : ℝ) * (eps / 2)) / q :=
      div_le_div_of_nonneg_right hsum hqpos.le
    _ = (((halfGoodLocalSiteSets n m).card : ℝ) / q) * (eps / 2) := by ring
    _ ≤ 1 * (eps / 2) := by
      gcongr
      exact (div_le_one hqpos).2 hcardR
    _ < eps := by linarith

theorem halfGoodFactoredTruncatedChooseContribution_tendsto
    (m : ℕ) (hm : 0 < m)
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor : 0 < widthFactor) (hu : 0 < u)
    (hvelLower : 0 < velocityLower) (hvelUpper : 0 < velocityUpper) :
    Tendsto (fun n : ℕ ↦
      halfGoodFactoredTruncatedChooseContribution n m widthFactor u
        velocityLower velocityUpper) atTop
      (𝓝 (((widthFactor * ((6 * u / Real.pi) *
        blockVelocityMass velocityLower velocityUpper)) ^ m) /
          (m.factorial : ℝ))) := by
  let A : ℝ := (widthFactor * ((12 * u / Real.pi) *
    blockVelocityMass velocityLower velocityUpper)) ^ m
  let reference : ℕ → ℝ := fun n ↦
    A * ((halfGoodLocalSiteSets n m).card : ℝ) /
      (localMeshSize n : ℝ) ^ m
  have href : Tendsto reference atTop
      (𝓝 (A * (((1 / 2 : ℝ) ^ m) / (m.factorial : ℝ)))) := by
    dsimp [reference]
    convert tendsto_const_nhds.mul
      (halfGoodLocalSiteSets_ratio_tendsto_factorial m hm) using 1 <;> ring
  have hdiff : Tendsto (fun n : ℕ ↦
      halfGoodFactoredTruncatedChooseContribution n m widthFactor u
          velocityLower velocityUpper - reference n) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro eps heps
    have hclose := eventually_halfGoodFactoredTruncatedChooseContribution_close
      m hm widthFactor u velocityLower velocityUpper hfactor hu hvelLower
        hvelUpper heps
    apply eventually_atTop.1
    exact hclose.mono fun n hn ↦ by
      simpa only [Real.dist_eq, sub_zero, reference, A] using hn
  have hsum := hdiff.add href
  convert hsum using 1
  · funext n
    simp only [reference]
    ring
  · congr 1
    dsimp [A]
    rw [show widthFactor * (6 * u / Real.pi *
        blockVelocityMass velocityLower velocityUpper) =
      (widthFactor * (12 * u / Real.pi *
        blockVelocityMass velocityLower velocityUpper)) * (1 / 2 : ℝ) by ring,
      mul_pow]
    ring

lemma sum_uniformProbability_eq_uniformExpectation_card_filter
    {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq I]
    (s : Finset I) (P : I → Ω → Prop) :
    (∑ i ∈ s, uniformProbability (P i)) =
      uniformExpectation (fun e ↦ ((s.filter fun i ↦ P i e).card : ℝ)) := by
  classical
  calc
    (∑ i ∈ s, uniformProbability (P i)) =
        ∑ i ∈ s, uniformExpectation (fun e ↦ if P i e then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact (uniformExpectation_indicator (P i)).symm
    _ = uniformExpectation (fun e ↦
          ∑ i ∈ s, if P i e then (1 : ℝ) else 0) :=
      (uniformExpectation_finset_sum s
        (fun i e ↦ if P i e then (1 : ℝ) else 0)).symm
    _ = uniformExpectation (fun e ↦
          ((s.filter fun i ↦ P i e).card : ℝ)) := by
      congr 1
      funext e
      simp

noncomputable def halfGoodBoundaryDefectContribution
    (n m : ℕ) (widthFactor u velocityLower velocityUpper : ℝ) : ℝ :=
  ∑ s ∈ halfGoodLocalSiteSets n m,
    uniformProbability (fun e : SignVector (2 * n) ↦
      (∀ a ∈ s,
        IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a) ∧
      ¬(∀ a ∈ s,
        IsFactoredTruncatedLocalRepresentative n widthFactor u
          velocityLower velocityUpper e a))

lemma halfGoodBoundaryDefectContribution_eq_sub
    (n m : ℕ) (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor : widthFactor ≤ 1) :
    halfGoodBoundaryDefectContribution n m widthFactor u
        velocityLower velocityUpper =
      halfGoodTruncatedChooseContribution n m u velocityLower velocityUpper -
        halfGoodFactoredTruncatedChooseContribution n m widthFactor u
          velocityLower velocityUpper := by
  classical
  unfold halfGoodBoundaryDefectContribution
  unfold halfGoodTruncatedChooseContribution
  unfold halfGoodFactoredTruncatedChooseContribution
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _hs
  let P : SignVector (2 * n) → Prop := fun e ↦
    ∀ a ∈ s,
      IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a
  let Q : SignVector (2 * n) → Prop := fun e ↦
    ∀ a ∈ s,
      IsFactoredTruncatedLocalRepresentative n widthFactor u
        velocityLower velocityUpper e a
  have hQP : ∀ e, Q e → P e := by
    intro e he a ha
    exact (isFactoredTruncatedLocalRepresentative_one_iff
      n u velocityLower velocityUpper e a).1
        (isFactoredTruncatedLocalRepresentative_mono n widthFactor 1 u
          velocityLower velocityUpper hfactor e a (he a ha))
  exact uniformProbability_and_not_eq_sub P Q hQP

theorem halfGoodBoundaryDefectContribution_tendsto
    (m : ℕ) (hm : 0 < m)
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor : 0 < widthFactor) (hfactorOne : widthFactor ≤ 1)
    (hu : 0 < u) (hvelLower : 0 < velocityLower)
    (hvelUpper : 0 < velocityUpper) :
    Tendsto (fun n : ℕ ↦
      halfGoodBoundaryDefectContribution n m widthFactor u
        velocityLower velocityUpper) atTop
      (𝓝 (((((6 * u / Real.pi) *
          blockVelocityMass velocityLower velocityUpper) ^ m) -
        ((widthFactor * ((6 * u / Real.pi) *
          blockVelocityMass velocityLower velocityUpper)) ^ m)) /
          (m.factorial : ℝ))) := by
  have hfull := halfGoodTruncatedChooseContribution_tendsto
    m hm u velocityLower velocityUpper hu hvelLower hvelUpper
  have hnarrow := halfGoodFactoredTruncatedChooseContribution_tendsto
    m hm widthFactor u velocityLower velocityUpper hfactor hu hvelLower hvelUpper
  have hsub := (hfull.sub hnarrow).congr'
    (Eventually.of_forall fun n ↦
      (halfGoodBoundaryDefectContribution_eq_sub n m widthFactor u
        velocityLower velocityUpper hfactorOne).symm)
  convert hsub using 1 <;> ring

noncomputable def halfGoodBoundaryDefectSiteSets
    (n m : ℕ) (widthFactor u velocityLower velocityUpper : ℝ)
    (e : SignVector (2 * n)) : Finset (Finset (Fin (localMeshSize n))) :=
  (halfGoodLocalSiteSets n m).filter fun s ↦
    (∀ a ∈ s,
      IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a) ∧
    ¬(∀ a ∈ s,
      IsFactoredTruncatedLocalRepresentative n widthFactor u
        velocityLower velocityUpper e a)

noncomputable def halfNonspreadRepresentedLocalSiteSets
    (n m : ℕ) (u velocityLower velocityUpper : ℝ)
    (e : SignVector (2 * n)) : Finset (Finset (Fin (localMeshSize n))) :=
  (halfNonspreadLocalSiteSets n m).filter fun s ↦
    ∀ a ∈ s,
      IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a

noncomputable def halfRecursiveTargetSiteSets
    (n m : ℕ) (widthFactor u velocityLower velocityUpper : ℝ)
    (e : SignVector (2 * n)) : Finset (Finset (Fin (localMeshSize n))) :=
  halfGoodBoundaryDefectSiteSets n m widthFactor u velocityLower velocityUpper e ∪
    halfNonspreadRepresentedLocalSiteSets n m u velocityLower velocityUpper e

lemma halfGoodBoundaryDefectSiteSets_disjoint_halfNonspreadRepresented
    (n m : ℕ) (widthFactor u velocityLower velocityUpper : ℝ)
    (e : SignVector (2 * n)) :
    Disjoint
      (halfGoodBoundaryDefectSiteSets n m widthFactor u
        velocityLower velocityUpper e)
      (halfNonspreadRepresentedLocalSiteSets n m u
        velocityLower velocityUpper e) := by
  apply Finset.disjoint_filter_filter
  exact halfGoodLocalSiteSets_disjoint_halfNonspread n m

lemma uniformExpectation_halfGoodBoundaryDefectSiteSets_card
    (n m : ℕ) (widthFactor u velocityLower velocityUpper : ℝ) :
    uniformExpectation (fun e : SignVector (2 * n) ↦
      ((halfGoodBoundaryDefectSiteSets n m widthFactor u
        velocityLower velocityUpper e).card : ℝ)) =
      halfGoodBoundaryDefectContribution n m widthFactor u
        velocityLower velocityUpper := by
  classical
  unfold halfGoodBoundaryDefectSiteSets
  unfold halfGoodBoundaryDefectContribution
  simpa using (sum_uniformProbability_eq_uniformExpectation_card_filter
    (halfGoodLocalSiteSets n m)
    (fun s (e : SignVector (2 * n)) ↦
      (∀ a ∈ s,
        IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a) ∧
      ¬(∀ a ∈ s,
        IsFactoredTruncatedLocalRepresentative n widthFactor u
          velocityLower velocityUpper e a))).symm

lemma uniformExpectation_halfNonspreadRepresentedLocalSiteSets_card
    (n m : ℕ) (u velocityLower velocityUpper : ℝ) :
    uniformExpectation (fun e : SignVector (2 * n) ↦
      ((halfNonspreadRepresentedLocalSiteSets n m u
        velocityLower velocityUpper e).card : ℝ)) =
      halfNonspreadTruncatedChooseContribution n m u
        velocityLower velocityUpper := by
  classical
  unfold halfNonspreadRepresentedLocalSiteSets
  unfold halfNonspreadTruncatedChooseContribution
  convert (sum_uniformProbability_eq_uniformExpectation_card_filter
    (halfNonspreadLocalSiteSets n m)
    (fun s (e : SignVector (2 * n)) ↦
      ∀ a ∈ s,
        IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)).symm using 1
  apply congrArg uniformExpectation
  funext e
  apply congrArg (fun q : ℕ ↦ (q : ℝ))
  apply congrArg Finset.card
  ext s
  simp

lemma uniformExpectation_halfRecursiveTargetSiteSets_card
    (n m : ℕ) (widthFactor u velocityLower velocityUpper : ℝ) :
    uniformExpectation (fun e : SignVector (2 * n) ↦
      ((halfRecursiveTargetSiteSets n m widthFactor u
        velocityLower velocityUpper e).card : ℝ)) =
      halfGoodBoundaryDefectContribution n m widthFactor u
          velocityLower velocityUpper +
        halfNonspreadTruncatedChooseContribution n m u
          velocityLower velocityUpper := by
  have hpoint : ∀ e : SignVector (2 * n),
      ((halfRecursiveTargetSiteSets n m widthFactor u
        velocityLower velocityUpper e).card : ℝ) =
      ((halfGoodBoundaryDefectSiteSets n m widthFactor u
        velocityLower velocityUpper e).card : ℝ) +
      ((halfNonspreadRepresentedLocalSiteSets n m u
        velocityLower velocityUpper e).card : ℝ) := by
    intro e
    unfold halfRecursiveTargetSiteSets
    rw [(Finset.card_union_eq_card_add_card.mpr
      (halfGoodBoundaryDefectSiteSets_disjoint_halfNonspreadRepresented
        n m widthFactor u velocityLower velocityUpper e))]
    norm_num
  rw [show (fun e : SignVector (2 * n) ↦
      ((halfRecursiveTargetSiteSets n m widthFactor u
        velocityLower velocityUpper e).card : ℝ)) =
      (fun e ↦
        ((halfGoodBoundaryDefectSiteSets n m widthFactor u
          velocityLower velocityUpper e).card : ℝ) +
        ((halfNonspreadRepresentedLocalSiteSets n m u
          velocityLower velocityUpper e).card : ℝ)) by
        funext e; exact hpoint e]
  rw [show uniformExpectation (fun e : SignVector (2 * n) ↦
      ((halfGoodBoundaryDefectSiteSets n m widthFactor u
        velocityLower velocityUpper e).card : ℝ) +
      ((halfNonspreadRepresentedLocalSiteSets n m u
        velocityLower velocityUpper e).card : ℝ)) =
      uniformExpectation (fun e : SignVector (2 * n) ↦
        ((halfGoodBoundaryDefectSiteSets n m widthFactor u
          velocityLower velocityUpper e).card : ℝ)) +
      uniformExpectation (fun e : SignVector (2 * n) ↦
        ((halfNonspreadRepresentedLocalSiteSets n m u
          velocityLower velocityUpper e).card : ℝ)) by
        unfold uniformExpectation
        rw [Finset.sum_add_distrib]
        ring]
  rw [uniformExpectation_halfGoodBoundaryDefectSiteSets_card,
    uniformExpectation_halfNonspreadRepresentedLocalSiteSets_card]

noncomputable def halfVeryCloseLowRepresentedSiteSets
    (n k : ℕ) (u velocityLower velocityUpper : ℝ)
    (e : SignVector (2 * n)) : Finset (Finset (Fin (localMeshSize n))) :=
  (halfVeryCloseLocalSiteSets n k).filter fun s ↦
    ¬HasHighFineMeshAcceleration k n e ∧
      ∀ a ∈ s,
        IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a

noncomputable def halfVeryCloseLowTruncatedChooseContribution
    (n k : ℕ) (u velocityLower velocityUpper : ℝ) : ℝ :=
  ∑ s ∈ halfVeryCloseLocalSiteSets n k,
    uniformProbability (fun e : SignVector (2 * n) ↦
      ¬HasHighFineMeshAcceleration k n e ∧
        ∀ a ∈ s,
          IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)

lemma uniformExpectation_halfVeryCloseLowRepresentedSiteSets_card
    (n k : ℕ) (u velocityLower velocityUpper : ℝ) :
    uniformExpectation (fun e : SignVector (2 * n) ↦
      ((halfVeryCloseLowRepresentedSiteSets n k u
        velocityLower velocityUpper e).card : ℝ)) =
      halfVeryCloseLowTruncatedChooseContribution n k u
        velocityLower velocityUpper := by
  classical
  unfold halfVeryCloseLowRepresentedSiteSets
  unfold halfVeryCloseLowTruncatedChooseContribution
  convert (sum_uniformProbability_eq_uniformExpectation_card_filter
    (halfVeryCloseLocalSiteSets n k)
    (fun s (e : SignVector (2 * n)) ↦
      ¬HasHighFineMeshAcceleration k n e ∧
        ∀ a ∈ s,
          IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)).symm using 1
  apply congrArg uniformExpectation
  funext e
  apply congrArg (fun q : ℕ ↦ (q : ℝ))
  apply congrArg Finset.card
  ext s
  simp

lemma mem_halfRecursiveTargetSiteSets_card
    {n m : ℕ} {widthFactor u velocityLower velocityUpper : ℝ}
    {e : SignVector (2 * n)} {s : Finset (Fin (localMeshSize n))}
    (hs : s ∈ halfRecursiveTargetSiteSets n m widthFactor u
      velocityLower velocityUpper e) :
    s.card = m := by
  rw [halfRecursiveTargetSiteSets, Finset.mem_union] at hs
  rcases hs with hgood | hbad
  · exact (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp
        (Finset.mem_filter.mp hgood).1).1).2
  · exact (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp
        (Finset.mem_filter.mp hbad).1).1).2

lemma erase_adjacent_mem_halfRecursiveTargetSiteSets
    (k n : ℕ) (eta u velocityLower velocityUpper : ℝ)
    (heta : 0 < eta)
    (hn : 0 < n)
    (herr : fineAdjacentAffineLocationError k n u velocityLower velocityUpper /
      localMeshHalfWidth n < eta)
    (e : SignVector (2 * n)) (hacc : ¬HasHighFineMeshAcceleration k n e)
    (s : Finset (Fin (localMeshSize n)))
    (hs : s ∈ halfVeryCloseLocalSiteSets n k)
    (hreps : ∀ a ∈ s,
      IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)
    (a b : Fin (localMeshSize n)) (ha : a ∈ s) (hb : b ∈ s)
    (hab : b.val = a.val + 1)
    (hu : 0 ≤ u) (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper) :
    s.erase b ∈ halfRecursiveTargetSiteSets n (k - 1) (1 - eta) u
      velocityLower velocityUpper e := by
  classical
  have habne : a ≠ b := by
    intro heq
    subst b
    omega
  have haerase : a ∈ s.erase b := Finset.mem_erase.mpr ⟨habne, ha⟩
  have hclose := Finset.mem_filter.mp hs
  have hnonspread := Finset.mem_filter.mp hclose.1
  have hpowerset := Finset.mem_powersetCard.mp hnonspread.1
  have hcard : (s.erase b).card = k - 1 := by
    rw [Finset.card_erase_of_mem hb, hpowerset.2]
  have hsubSmooth : s.erase b ⊆ halfSmoothLocalMeshSites n :=
    fun x hx ↦ hpowerset.1 (Finset.mem_of_mem_erase hx)
  have hrepErase : ∀ x ∈ s.erase b,
      IsTruncatedLocalRepresentative n u velocityLower velocityUpper e x :=
    fun x hx ↦ hreps x (Finset.mem_of_mem_erase hx)
  have hboundary := adjacentRepresentatives_rightBoundary_of_not_highFine
    k eta u velocityLower velocityUpper heta n hn herr e hacc a b hab
      (hreps a ha) (hreps b hb) hu hvelocityLower hvelocityUpper
  rw [halfRecursiveTargetSiteSets, Finset.mem_union]
  by_cases hgood : IsGoodLocalSiteSet n (s.erase b)
  · apply Or.inl
    rw [halfGoodBoundaryDefectSiteSets, Finset.mem_filter]
    refine ⟨?_, hrepErase, ?_⟩
    · rw [halfGoodLocalSiteSets, Finset.mem_filter,
        Finset.mem_powersetCard]
      refine ⟨⟨?_, hcard⟩, hgood⟩
      intro x hx
      exact (Finset.mem_filter.mp (hsubSmooth hx)).1
    · intro hall
      have hnotNarrow := (rightBoundary_subset_full_not_factored
        n eta u velocityLower velocityUpper e a hboundary).2
      exact hnotNarrow (hall a haerase)
  · apply Or.inr
    rw [halfNonspreadRepresentedLocalSiteSets, Finset.mem_filter]
    refine ⟨?_, hrepErase⟩
    rw [halfNonspreadLocalSiteSets, Finset.mem_filter,
      Finset.mem_powersetCard]
    refine ⟨⟨hsubSmooth, hcard⟩, ?_⟩
    intro hspread
    apply hgood
    exact ⟨(fun x hx ↦ (Finset.mem_filter.mp (hsubSmooth hx)).2), hspread⟩

theorem eventually_halfVeryCloseLowRepresented_card_le_recursiveTarget
    (k : ℕ) (hk : 2 ≤ k)
    (eta u velocityLower velocityUpper : ℝ)
    (heta : 0 < eta)
    (hu : 0 ≤ u) (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper) :
    ∀ᶠ n : ℕ in atTop, ∀ e : SignVector (2 * n),
      (halfVeryCloseLowRepresentedSiteSets n k u
          velocityLower velocityUpper e).card ≤
        (k - 1) *
          (halfRecursiveTargetSiteSets n (k - 1) (1 - eta) u
            velocityLower velocityUpper e).card := by
  classical
  filter_upwards [Nat.eventually_pos,
      (fineAdjacentAffineLocationError_relative_tendsto_zero
        k u velocityLower velocityUpper hvelocityLower.ne').eventually
          (Iio_mem_nhds heta),
      eventually_halfVeryClose_representatives_have_adjacent_pair
        k u velocityLower velocityUpper hu hvelocityLower hvelocityUpper]
    with n hn herr hadj
  intro e
  let source := halfVeryCloseLowRepresentedSiteSets n k u
    velocityLower velocityUpper e
  let target := halfRecursiveTargetSiteSets n (k - 1) (1 - eta) u
    velocityLower velocityUpper e
  have horiented : ∀ s : {s // s ∈ source},
      ∃ p : Fin (localMeshSize n) × Fin (localMeshSize n),
        p.1 ∈ s.1 ∧ p.2 ∈ s.1 ∧ p.1 ≠ p.2 ∧
          p.2.val = p.1.val + 1 := by
    intro s
    have hsource := Finset.mem_filter.mp s.2
    have hs : s.1 ∈ halfVeryCloseLocalSiteSets n k := by
      simpa only [source, halfVeryCloseLowRepresentedSiteSets] using hsource.1
    have hacc : ¬HasHighFineMeshAcceleration k n e := hsource.2.1
    have hreps : ∀ a ∈ s.1,
        IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a :=
      hsource.2.2
    rcases hadj e hacc s.1 hs hreps with
      ⟨a, ha, b, hb, hab, hsucc | hsucc⟩
    · exact ⟨(a, b), ha, hb, hab, hsucc⟩
    · exact ⟨(b, a), hb, ha, Ne.symm hab, hsucc⟩
  let picked : {s // s ∈ source} →
      Fin (localMeshSize n) × Fin (localMeshSize n) :=
    fun s ↦ Classical.choose (horiented s)
  have hpicked : ∀ s : {s // s ∈ source},
      (picked s).1 ∈ s.1 ∧ (picked s).2 ∈ s.1 ∧
        (picked s).1 ≠ (picked s).2 ∧
        (picked s).2.val = (picked s).1.val + 1 := by
    intro s
    exact Classical.choose_spec (horiented s)
  let lower : {s // s ∈ source} → Fin (localMeshSize n) := fun s ↦ (picked s).1
  let upper : {s // s ∈ source} → Fin (localMeshSize n) := fun s ↦ (picked s).2
  let reduced : {s // s ∈ source} → Finset (Fin (localMeshSize n)) :=
    fun s ↦ s.1.erase (upper s)
  have hlower : ∀ s : {s // s ∈ source}, lower s ∈ s.1 := by
    intro s
    exact (hpicked s).1
  have hupper : ∀ s : {s // s ∈ source}, upper s ∈ s.1 := by
    intro s
    exact (hpicked s).2.1
  have hne : ∀ s : {s // s ∈ source}, lower s ≠ upper s := by
    intro s
    exact (hpicked s).2.2.1
  have hsucc : ∀ s : {s // s ∈ source},
      (upper s).val = (lower s).val + 1 := by
    intro s
    exact (hpicked s).2.2.2
  have hlowerReduced : ∀ s : {s // s ∈ source}, lower s ∈ reduced s := by
    intro s
    exact Finset.mem_erase.mpr ⟨hne s, hlower s⟩
  have hreducedTarget : ∀ s : {s // s ∈ source}, reduced s ∈ target := by
    intro s
    have hsource := Finset.mem_filter.mp s.2
    have hs : s.1 ∈ halfVeryCloseLocalSiteSets n k := by
      simpa only [source, halfVeryCloseLowRepresentedSiteSets] using hsource.1
    have hacc : ¬HasHighFineMeshAcceleration k n e := hsource.2.1
    have hreps : ∀ a ∈ s.1,
        IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a :=
      hsource.2.2
    simpa only [target, reduced] using
      (erase_adjacent_mem_halfRecursiveTargetSiteSets
        k n eta u velocityLower velocityUpper heta hn herr e hacc s.1 hs hreps
          (lower s) (upper s) (hlower s) (hupper s) (hsucc s) hu
            hvelocityLower hvelocityUpper)
  let C := Σ t : {t // t ∈ target}, {a // a ∈ t.1}
  let f : {s // s ∈ source} → C := fun s ↦
    ⟨⟨reduced s, hreducedTarget s⟩, ⟨lower s, hlowerReduced s⟩⟩
  have hf : Function.Injective f := by
    intro s₁ s₂ heq
    have ht : reduced s₁ = reduced s₂ :=
      congrArg (fun z : C ↦ z.1.1) heq
    have ha : lower s₁ = lower s₂ :=
      congrArg (fun z : C ↦ z.2.1) heq
    have hb : upper s₁ = upper s₂ := by
      apply Fin.ext
      have h₁ := hsucc s₁
      have h₂ := hsucc s₂
      have haval : (lower s₁).val = (lower s₂).val := congrArg Fin.val ha
      omega
    apply Subtype.ext
    calc
      s₁.1 = insert (upper s₁) (reduced s₁) :=
        (Finset.insert_erase (hupper s₁)).symm
      _ = insert (upper s₂) (reduced s₂) := by rw [hb, ht]
      _ = s₂.1 := Finset.insert_erase (hupper s₂)
  have hCcard : Fintype.card C = target.card * (k - 1) := by
    calc
      Fintype.card C = ∑ t : {t // t ∈ target}, t.1.card := by
        simp [C]
      _ = ∑ _t : {t // t ∈ target}, (k - 1) := by
        apply Finset.sum_congr rfl
        intro t _ht
        exact mem_halfRecursiveTargetSiteSets_card t.2
      _ = target.card * (k - 1) := by simp
  have hcard := Fintype.card_le_of_injective f hf
  have hsourceCard : Fintype.card {s // s ∈ source} = source.card := by simp
  rw [hsourceCard, hCcard] at hcard
  simpa only [source, target, mul_comm] using hcard

theorem eventually_halfVeryCloseLowTruncatedChooseContribution_le_recursiveTarget
    (k : ℕ) (hk : 2 ≤ k)
    (eta u velocityLower velocityUpper : ℝ)
    (heta : 0 < eta)
    (hu : 0 ≤ u) (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper) :
    ∀ᶠ n : ℕ in atTop,
      halfVeryCloseLowTruncatedChooseContribution n k u
          velocityLower velocityUpper ≤
        ((k - 1 : ℕ) : ℝ) *
          (halfGoodBoundaryDefectContribution n (k - 1) (1 - eta) u
              velocityLower velocityUpper +
            halfNonspreadTruncatedChooseContribution n (k - 1) u
              velocityLower velocityUpper) := by
  filter_upwards [eventually_halfVeryCloseLowRepresented_card_le_recursiveTarget
      k hk eta u velocityLower velocityUpper heta hu hvelocityLower
        hvelocityUpper]
    with n hcard
  have hexpect :
      uniformExpectation (fun e : SignVector (2 * n) ↦
        ((halfVeryCloseLowRepresentedSiteSets n k u
          velocityLower velocityUpper e).card : ℝ)) ≤
      uniformExpectation (fun e : SignVector (2 * n) ↦
        ((k - 1 : ℕ) : ℝ) *
          ((halfRecursiveTargetSiteSets n (k - 1) (1 - eta) u
            velocityLower velocityUpper e).card : ℝ)) := by
    apply uniformExpectation_mono
    intro e
    exact_mod_cast hcard e
  rw [uniformExpectation_halfVeryCloseLowRepresentedSiteSets_card] at hexpect
  rw [uniformExpectation_const_mul,
    uniformExpectation_halfRecursiveTargetSiteSets_card] at hexpect
  exact hexpect

lemma halfVeryCloseLocalSiteSets_card_le_pow (n k : ℕ) :
    (halfVeryCloseLocalSiteSets n k).card ≤ localMeshSize n ^ k := by
  calc
    (halfVeryCloseLocalSiteSets n k).card ≤
        ((halfSmoothLocalMeshSites n).powersetCard k).card := by
      apply Finset.card_le_card
      intro s hs
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1
    _ = (halfSmoothLocalMeshSites n).card.choose k := by
      rw [Finset.card_powersetCard]
    _ ≤ (halfSmoothLocalMeshSites n).card ^ k := Nat.choose_le_pow _ _
    _ ≤ localMeshSize n ^ k := by
      apply Nat.pow_le_pow_left
      calc
        (halfSmoothLocalMeshSites n).card ≤ (halfLocalMeshSites n).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ ≤ localMeshSize n := by
          rw [card_halfLocalMeshSites]
          exact Nat.div_le_self _ _

lemma halfVeryCloseTruncatedChooseContribution_le_high_add_low
    (n k : ℕ) (u velocityLower velocityUpper : ℝ) :
    halfVeryCloseTruncatedChooseContribution n k u velocityLower velocityUpper ≤
      (localMeshSize n : ℝ) ^ k *
          uniformProbability (HasHighFineMeshAcceleration k n) +
        halfVeryCloseLowTruncatedChooseContribution n k u
          velocityLower velocityUpper := by
  classical
  have hterm : ∀ s ∈ halfVeryCloseLocalSiteSets n k,
      uniformProbability (fun e : SignVector (2 * n) ↦
        ∀ a ∈ s,
          IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a) ≤
      uniformProbability (HasHighFineMeshAcceleration k n) +
        uniformProbability (fun e : SignVector (2 * n) ↦
          ¬HasHighFineMeshAcceleration k n e ∧
            ∀ a ∈ s,
              IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a) := by
    intro s _hs
    calc
      _ ≤ uniformProbability (fun e : SignVector (2 * n) ↦
          HasHighFineMeshAcceleration k n e ∨
            (¬HasHighFineMeshAcceleration k n e ∧
              ∀ a ∈ s,
                IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)) := by
        apply uniformProbability_mono
        intro e he
        by_cases hacc : HasHighFineMeshAcceleration k n e
        · exact Or.inl hacc
        · exact Or.inr ⟨hacc, he⟩
      _ ≤ _ := uniformProbability_or_le_add _ _
  unfold halfVeryCloseTruncatedChooseContribution
  calc
    (∑ s ∈ halfVeryCloseLocalSiteSets n k,
        uniformProbability (fun e : SignVector (2 * n) ↦
          ∀ a ∈ s,
            IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)) ≤
      ∑ s ∈ halfVeryCloseLocalSiteSets n k,
        (uniformProbability (HasHighFineMeshAcceleration k n) +
          uniformProbability (fun e : SignVector (2 * n) ↦
            ¬HasHighFineMeshAcceleration k n e ∧
              ∀ a ∈ s,
                IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)) := by
      apply Finset.sum_le_sum
      intro s hs
      exact hterm s hs
    _ = ((halfVeryCloseLocalSiteSets n k).card : ℝ) *
          uniformProbability (HasHighFineMeshAcceleration k n) +
        halfVeryCloseLowTruncatedChooseContribution n k u
          velocityLower velocityUpper := by
      rw [Finset.sum_add_distrib]
      simp [halfVeryCloseLowTruncatedChooseContribution]
    _ ≤ (localMeshSize n : ℝ) ^ k *
          uniformProbability (HasHighFineMeshAcceleration k n) +
        halfVeryCloseLowTruncatedChooseContribution n k u
          velocityLower velocityUpper := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right
          (by exact_mod_cast halfVeryCloseLocalSiteSets_card_le_pow n k)
          (uniformProbability_nonneg _)) le_rfl

lemma eventually_halfVeryCloseLocalSiteSets_one_eq_empty :
    ∀ᶠ n : ℕ in atTop, halfVeryCloseLocalSiteSets n 1 = ∅ := by
  filter_upwards [Nat.eventually_pos,
      eventually_two_weakSpreadScale_le_rigiditySmoothScale 1]
    with n hn hscale
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  have hclose := Finset.mem_filter.mp hs
  have hnonspread := Finset.mem_filter.mp hclose.1
  have hpowerset := Finset.mem_powersetCard.mp hnonspread.1
  rcases halfSmooth_not_weakSpread_has_close_pair n hn 1 hscale s
      hpowerset.1 hclose.2 with ⟨a, ha, b, hb, hab, _hdist⟩
  rcases Finset.card_eq_one.mp hpowerset.2 with ⟨x, rfl⟩
  simp at ha hb
  exact hab (ha.trans hb.symm)

theorem halfVeryCloseTruncatedChooseContribution_one_tendsto_zero
    (u velocityLower velocityUpper : ℝ) :
    Tendsto (fun n : ℕ ↦
      halfVeryCloseTruncatedChooseContribution n 1 u
        velocityLower velocityUpper) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_halfVeryCloseLocalSiteSets_one_eq_empty]
    with n hn
  rw [halfVeryCloseTruncatedChooseContribution, hn]
  simp

theorem halfNonspreadTruncatedChooseContribution_tendsto_zero
    (k : ℕ) (hk : 0 < k)
    (u velocityLower velocityUpper : ℝ)
    (hu : 0 < u) (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 < velocityUpper) :
    Tendsto (fun n : ℕ ↦
      halfNonspreadTruncatedChooseContribution n k u
        velocityLower velocityUpper) atTop (𝓝 0) := by
  have hcloseAll : ∀ q : ℕ, 0 < q →
      Tendsto (fun n : ℕ ↦
        halfVeryCloseTruncatedChooseContribution n q u
          velocityLower velocityUpper) atTop (𝓝 0) := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro hq
      by_cases hqOne : q = 1
      · subst q
        exact halfVeryCloseTruncatedChooseContribution_one_tendsto_zero
          u velocityLower velocityUpper
      · have hqTwo : 2 ≤ q := by omega
        let m : ℕ := q - 1
        have hm : 0 < m := by dsimp [m]; omega
        have hmq : m < q := by dsimp [m]; omega
        have hprevClose := ih m hmq hm
        have hprevWeak := halfWeakNonspreadTruncatedChooseContribution_tendsto_zero
          m hm u velocityLower velocityUpper hu.le hvelocityLower
            hvelocityUpper.le
        have hprevNonspread : Tendsto (fun n : ℕ ↦
            halfNonspreadTruncatedChooseContribution n m u
              velocityLower velocityUpper) atTop (𝓝 0) := by
          have hsum := hprevWeak.add hprevClose
          have hsum' : Tendsto (fun n : ℕ ↦
              halfWeakNonspreadTruncatedChooseContribution n m u
                  velocityLower velocityUpper +
                halfVeryCloseTruncatedChooseContribution n m u
                  velocityLower velocityUpper) atTop (𝓝 0) := by
            simpa using hsum
          apply hsum'.congr'
          exact Eventually.of_forall fun n ↦ by
            simpa only [m] using
              (halfNonspreadTruncatedChooseContribution_eq_weak_add_veryClose
                n (q - 1) u velocityLower velocityUpper).symm
        let A : ℝ := (6 * u / Real.pi) *
          blockVelocityMass velocityLower velocityUpper
        let D : ℝ → ℝ := fun eta ↦
          (A ^ m - (((1 - eta) * A) ^ m)) / (m.factorial : ℝ)
        have hDzero : Tendsto D (𝓝 0) (𝓝 0) := by
          have hcont : ContinuousAt D 0 := by
            dsimp [D]
            fun_prop
          simpa [D] using hcont.tendsto
        let etaSeq : ℕ → ℝ := fun j ↦ 1 / (j + 1 : ℝ)
        have hetaSeq : Tendsto etaSeq atTop (𝓝 0) := by
          simpa only [etaSeq] using tendsto_one_div_add_atTop_nhds_zero_nat
        have hscaledEta : Tendsto (fun j : ℕ ↦ (m : ℝ) * D (etaSeq j))
            atTop (𝓝 0) := by
          simpa using (hDzero.comp hetaSeq).const_mul (m : ℝ)
        rw [Metric.tendsto_atTop]
        intro eps heps
        have hsmallEta : ∀ᶠ j : ℕ in atTop,
            (m : ℝ) * D (etaSeq j) < eps / 4 :=
          hscaledEta.eventually (Iio_mem_nhds (by linarith))
        rcases (hsmallEta.and (eventually_ge_atTop (1 : ℕ))).exists with
          ⟨j, hsmallEtaJ, hj⟩
        let eta : ℝ := etaSeq j
        have heta : 0 < eta := by
          dsimp [eta, etaSeq]
          positivity
        have hetaOne : eta < 1 := by
          dsimp [eta, etaSeq]
          rw [div_lt_one]
          · exact_mod_cast (show 1 < j + 1 by omega)
          · positivity
        have hdefectRaw := halfGoodBoundaryDefectContribution_tendsto
          m hm (1 - eta) u velocityLower velocityUpper (sub_pos.mpr hetaOne)
            (by linarith) hu hvelocityLower hvelocityUpper
        have hdefect : Tendsto (fun n : ℕ ↦
            halfGoodBoundaryDefectContribution n m (1 - eta) u
              velocityLower velocityUpper) atTop (𝓝 (D eta)) := by
          simpa [D, A] using hdefectRaw
        have hhigh := localMeshSize_pow_mul_highFineMeshAcceleration_tendsto_zero
          q q
        let upper : ℕ → ℝ := fun n ↦
          (localMeshSize n : ℝ) ^ q *
              uniformProbability (HasHighFineMeshAcceleration q n) +
            (m : ℝ) *
              (halfGoodBoundaryDefectContribution n m (1 - eta) u
                  velocityLower velocityUpper +
                halfNonspreadTruncatedChooseContribution n m u
                  velocityLower velocityUpper)
        have hupperLimit : Tendsto upper atTop (𝓝 ((m : ℝ) * D eta)) := by
          have hsum := hhigh.add ((hdefect.add hprevNonspread).const_mul (m : ℝ))
          simpa [upper] using hsum
        have hbound : ∀ᶠ n : ℕ in atTop,
            halfVeryCloseTruncatedChooseContribution n q u
                velocityLower velocityUpper ≤ upper n := by
          filter_upwards [eventually_halfVeryCloseLowTruncatedChooseContribution_le_recursiveTarget
              q hqTwo eta u velocityLower velocityUpper heta hu.le
                hvelocityLower hvelocityUpper.le]
            with n hlow
          calc
            halfVeryCloseTruncatedChooseContribution n q u
                velocityLower velocityUpper ≤
              (localMeshSize n : ℝ) ^ q *
                  uniformProbability (HasHighFineMeshAcceleration q n) +
                halfVeryCloseLowTruncatedChooseContribution n q u
                  velocityLower velocityUpper :=
              halfVeryCloseTruncatedChooseContribution_le_high_add_low
                n q u velocityLower velocityUpper
            _ ≤ upper n := by
              dsimp [upper, m]
              exact add_le_add le_rfl hlow
        have hupperSmall : ∀ᶠ n : ℕ in atTop, upper n < eps := by
          exact hupperLimit.eventually (Iio_mem_nhds (by
            linarith))
        apply eventually_atTop.1
        filter_upwards [hbound, hupperSmall] with n hboundN hsmallN
        have hnonneg : 0 ≤ halfVeryCloseTruncatedChooseContribution n q u
            velocityLower velocityUpper := by
          unfold halfVeryCloseTruncatedChooseContribution
          exact Finset.sum_nonneg fun s _hs ↦ uniformProbability_nonneg _
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
        exact hboundN.trans_lt hsmallN
  have hweak := halfWeakNonspreadTruncatedChooseContribution_tendsto_zero
    k hk u velocityLower velocityUpper hu.le hvelocityLower hvelocityUpper.le
  have hclose := hcloseAll k hk
  have hsum := hweak.add hclose
  have hsum' : Tendsto (fun n : ℕ ↦
      halfWeakNonspreadTruncatedChooseContribution n k u
          velocityLower velocityUpper +
        halfVeryCloseTruncatedChooseContribution n k u
          velocityLower velocityUpper) atTop (𝓝 0) := by
    simpa using hsum
  apply hsum'.congr'
  exact Eventually.of_forall fun n ↦
    (halfNonspreadTruncatedChooseContribution_eq_weak_add_veryClose
      n k u velocityLower velocityUpper).symm

theorem uniformChooseMoment_halfTruncatedLocalMinimumCount_tendsto
    (k : ℕ) (u velocityLower velocityUpper : ℝ)
    (hu : 0 < u) (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 < velocityUpper) :
    Tendsto (fun n : ℕ ↦
      uniformChooseMoment
        (halfTruncatedLocalMinimumCount n u velocityLower velocityUpper) k)
      atTop
      (𝓝 ((((6 * u / Real.pi) *
        blockVelocityMass velocityLower velocityUpper) ^ k) /
          (k.factorial : ℝ))) := by
  by_cases hk : k = 0
  · subst k
    convert tendsto_const_nhds (x := (1 : ℝ)) using 1
    · funext n
      unfold uniformChooseMoment uniformExpectation
      simp
    · norm_num
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hgood := halfGoodTruncatedChooseContribution_tendsto
      k hkpos u velocityLower velocityUpper hu hvelocityLower hvelocityUpper
    have hbad := halfNonspreadTruncatedChooseContribution_tendsto_zero
      k hkpos u velocityLower velocityUpper hu hvelocityLower hvelocityUpper
    have hsum := hgood.add hbad
    have hsum' : Tendsto (fun n : ℕ ↦
        halfGoodTruncatedChooseContribution n k u velocityLower velocityUpper +
          halfNonspreadTruncatedChooseContribution n k u
            velocityLower velocityUpper) atTop
      (𝓝 ((((6 * u / Real.pi) *
        blockVelocityMass velocityLower velocityUpper) ^ k) /
          (k.factorial : ℝ))) := by
      simpa using hsum
    apply hsum'.congr'
    exact Eventually.of_forall fun n ↦
      (uniformChooseMoment_halfTruncated_eq_good_add_nonspread
        n k u velocityLower velocityUpper).symm

theorem uniformProbability_halfTruncatedLocalMinimumCount_eq_zero_tendsto
    (u velocityLower velocityUpper : ℝ)
    (hu : 0 < u) (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 < velocityUpper) :
    Tendsto (fun n : ℕ ↦
      uniformProbability (fun e : SignVector (2 * n) ↦
        halfTruncatedLocalMinimumCount n u velocityLower velocityUpper e = 0))
      atTop
      (𝓝 (Real.exp (-((6 * u / Real.pi) *
        blockVelocityMass velocityLower velocityUpper)))) := by
  exact uniformVoidProbability_tendsto_of_chooseMoments
    (fun n ↦ 2 * n)
    (fun n ↦ halfTruncatedLocalMinimumCount n u velocityLower velocityUpper)
    ((6 * u / Real.pi) * blockVelocityMass velocityLower velocityUpper)
    (fun k ↦ uniformChooseMoment_halfTruncatedLocalMinimumCount_tendsto
      k u velocityLower velocityUpper hu hvelocityLower hvelocityUpper)

end Erdos525
