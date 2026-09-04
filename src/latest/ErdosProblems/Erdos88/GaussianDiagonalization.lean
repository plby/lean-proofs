import ErdosProblems.Erdos88.GaussianDensity
import ErdosProblems.Erdos88.QuadraticNumerics
import ErdosProblems.Erdos88.SliceGaussianComparison
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open scoped BigOperators InnerProductSpace RealInnerProductSpace
  Matrix.Norms.Frobenius
open MeasureTheory ProbabilityTheory Real
open Matrix

namespace Erdos88.GaussianQuadratic

open BooleanSlices
open Erdos88.Invariance

/-- The linear coefficient of a quadratic polynomial in a normalized
eigenvector direction. -/
noncomputable def eigenLinearCoefficient {n : ℕ}
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    (f : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ i, f i * hF.eigenvectorBasis j i

/-- Synthesis of an ordinary coordinate vector in the orthonormal
eigenbasis of a real symmetric matrix. -/
noncomputable def eigenvectorSynthesis {n : ℕ}
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    (z : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, z j * hF.eigenvectorBasis j i

lemma continuous_eigenvectorSynthesis {n : ℕ}
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian) :
    Continuous (eigenvectorSynthesis hF) := by
  classical
  apply continuous_pi
  intro i
  apply continuous_finset_sum
  intro j _
  exact (continuous_apply j).mul continuous_const

lemma linearPart_eigenvectorSynthesis {n : ℕ}
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    (f z : Fin n → ℝ) :
    linearPart f (eigenvectorSynthesis hF z) =
      ∑ j, eigenLinearCoefficient hF f j * z j := by
  classical
  unfold linearPart eigenvectorSynthesis eigenLinearCoefficient
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma toLp_eigenvectorSynthesis {n : ℕ}
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    (z : Fin n → ℝ) :
    WithLp.toLp 2 (eigenvectorSynthesis hF z) =
      ∑ j, z j • hF.eigenvectorBasis j := by
  classical
  ext i
  simp [eigenvectorSynthesis]

lemma toEuclideanLin_eigenvectorSynthesis {n : ℕ}
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    (z : Fin n → ℝ) :
    F.toEuclideanLin (WithLp.toLp 2 (eigenvectorSynthesis hF z)) =
      ∑ j, (hF.eigenvalues j * z j) • hF.eigenvectorBasis j := by
  classical
  rw [toLp_eigenvectorSynthesis]
  simp_rw [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j _
  have heig := congrArg (WithLp.toLp 2) (hF.mulVec_eigenvectorBasis j)
  change F.toEuclideanLin (hF.eigenvectorBasis j) =
      (hF.eigenvalues j) • hF.eigenvectorBasis j at heig
  rw [heig]
  rw [smul_smul]
  ring_nf

lemma quadraticPart_eigenvectorSynthesis {n : ℕ}
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    (z : Fin n → ℝ) :
    quadraticPart F (eigenvectorSynthesis hF z) =
      ∑ j, hF.eigenvalues j * z j ^ 2 := by
  classical
  let b := hF.eigenvectorBasis
  calc
    quadraticPart F (eigenvectorSynthesis hF z) =
        ⟪WithLp.toLp 2 (eigenvectorSynthesis hF z),
          F.toEuclideanLin (WithLp.toLp 2 (eigenvectorSynthesis hF z))⟫_ℝ := by
      simp only [quadraticPart, PiLp.inner_apply,
        Matrix.toEuclideanLin_apply,
        Matrix.mulVec, dotProduct, Real.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ⟪WithLp.toLp 2 (eigenvectorSynthesis hF z),
        ∑ j, (hF.eigenvalues j * z j) • b j⟫_ℝ := by
      rw [toEuclideanLin_eigenvectorSynthesis]
    _ = ⟪∑ j, z j • b j, ∑ j, (hF.eigenvalues j * z j) • b j⟫_ℝ := by
      rw [toLp_eigenvectorSynthesis]
    _ = ∑ j, hF.eigenvalues j * z j ^ 2 := by
      rw [sum_inner]
      apply Finset.sum_congr rfl
      intro j _
      rw [real_inner_smul_left, b.orthonormal.inner_right_fintype]
      ring

theorem quadraticPolynomial_eigenvectorSynthesis {n : ℕ}
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    (f₀ : ℝ) (f z : Fin n → ℝ) :
    quadraticPolynomial f₀ f F (eigenvectorSynthesis hF z) =
      f₀ + ∑ j, (eigenLinearCoefficient hF f j * z j +
        hF.eigenvalues j * z j ^ 2) := by
  unfold quadraticPolynomial
  rw [linearPart_eigenvectorSynthesis,
    quadraticPart_eigenvectorSynthesis, Finset.sum_add_distrib]
  ring

/-- Standard product Gaussian measure is invariant under synthesis in the
orthonormal eigenbasis of a real symmetric matrix. -/
theorem gaussianProductMeasure_map_eigenvectorSynthesis {n : ℕ}
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian) :
    (gaussianProductMeasure n).map (eigenvectorSynthesis hF) =
      gaussianProductMeasure n := by
  classical
  let b := hF.eigenvectorBasis
  apply (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding.map_injective
  rw [Measure.map_map (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable
    (continuous_eigenvectorSynthesis hF).measurable]
  rw [MeasurableEquiv.coe_toLp]
  rw [show (WithLp.toLp 2 ∘ eigenvectorSynthesis hF) =
      fun z : Fin n → ℝ ↦ ∑ j, z j • b j by
    funext z
    exact toLp_eigenvectorSynthesis hF z]
  unfold gaussianProductMeasure
  rw [← stdGaussian_eq_map_pi_orthonormalBasis b]
  simpa only [Erdos88.Invariance.standardGaussian] using
    (map_pi_eq_stdGaussian (ι := Fin n)).symm

/-- Sum of independent centered diagonal quadratic coordinates, expressed
on the underlying product of standard Gaussian coordinates. -/
def diagonalCenteredSum {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (z : ι → ℝ) : ℝ :=
  ∑ i, centeredCoordinatePolynomial (a i) (lam i) (z i)

lemma continuous_diagonalCenteredSum {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) :
    Continuous (diagonalCenteredSum a lam) := by
  classical
  unfold diagonalCenteredSum centeredCoordinatePolynomial
  fun_prop

/-- The diagonal centered law is the direct pushforward of the product
standard Gaussian measure by the centered coordinate sum. -/
theorem diagonalCenteredLaw_eq_map_diagonalCenteredSum
    {ι : Type*} [Fintype ι] (a lam : ι → ℝ) :
    diagonalCenteredLaw a lam =
      (Measure.pi fun _ : ι ↦ gaussianReal 0 1).map
        (diagonalCenteredSum a lam) := by
  classical
  unfold diagonalCenteredLaw centeredCoordinateLaw
  rw [← Measure.pi_map_pi (fun i ↦
    (continuous_centeredCoordinatePolynomial (a i) (lam i)).aemeasurable)]
  have hcoord : Measurable (fun z : ι → ℝ ↦
      fun i ↦ centeredCoordinatePolynomial (a i) (lam i) (z i)) := by
    exact measurable_pi_lambda _ fun i ↦
      (continuous_centeredCoordinatePolynomial (a i) (lam i)).measurable.comp
        (measurable_pi_apply i)
  rw [Measure.map_map (by fun_prop) hcoord]
  congr 1

lemma integral_diagonalCenteredSum_cexp {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (t : ℝ) :
    ∫ z : ι → ℝ,
        Complex.exp ((((t * diagonalCenteredSum a lam z : ℝ) : ℂ) *
          Complex.I)) ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 1) =
      diagonalCenteredCharProduct a lam t := by
  rw [← charFun_diagonalCenteredLaw a lam]
  rw [charFun_apply_real, diagonalCenteredLaw_eq_map_diagonalCenteredSum]
  rw [integral_map
    (continuous_diagonalCenteredSum a lam).aemeasurable (by fun_prop)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z ↦ by
    congr 1
    push_cast
    ring

lemma continuous_quadraticPolynomial {n : ℕ}
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (quadraticPolynomial f₀ f F) := by
  classical
  unfold quadraticPolynomial linearPart quadraticPart
  fun_prop

/-- The real/imaginary definition used by the slice comparison is exactly
the complex exponential expectation of the full Gaussian quadratic. -/
theorem gaussianQuadraticCharacteristic_eq_integral_cexp {n : ℕ}
    (f₀ : ℝ) (f : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (t : ℝ) :
    gaussianQuadraticCharacteristic f₀ f F t =
      ∫ x : Fin n → ℝ,
        Complex.exp ((((t * quadraticPolynomial f₀ f F x : ℝ) : ℂ) *
          Complex.I)) ∂gaussianProductMeasure n := by
  let U : (Fin n → ℝ) → ℝ := fun x ↦
    t * quadraticPolynomial f₀ f F x
  have hU : Continuous U :=
    continuous_const.mul (continuous_quadraticPolynomial f₀ f F)
  have hcos : Integrable (fun x ↦ Real.cos (U x))
      (gaussianProductMeasure n) := by
    apply Integrable.of_bound
      (Real.continuous_cos.comp hU).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x ↦ by
      change |Real.cos (U x)| ≤ 1
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (U x)
  have hsin : Integrable (fun x ↦ Real.sin (U x))
      (gaussianProductMeasure n) := by
    apply Integrable.of_bound
      (Real.continuous_sin.comp hU).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x ↦ by
      change |Real.sin (U x)| ≤ 1
      simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (U x)
  unfold gaussianQuadraticCharacteristic gaussianExpectation
  change ((∫ x, Real.cos (U x) ∂gaussianProductMeasure n : ℝ) : ℂ) +
      ((∫ x, Real.sin (U x) ∂gaussianProductMeasure n : ℝ) : ℂ) *
        Complex.I = _
  rw [← integral_complex_ofReal, ← integral_complex_ofReal,
    ← integral_mul_const]
  calc
    (∫ x, (Real.cos (U x) : ℂ) ∂gaussianProductMeasure n) +
          ∫ x, (Real.sin (U x) : ℂ) * Complex.I
            ∂gaussianProductMeasure n =
        ∫ x, (Real.cos (U x) : ℂ) +
          (Real.sin (U x) : ℂ) * Complex.I
            ∂gaussianProductMeasure n :=
      (integral_add hcos.ofReal (hsin.ofReal.mul_const Complex.I)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        change (Real.cos (U x) : ℂ) +
            (Real.sin (U x) : ℂ) * Complex.I =
          Complex.exp ((U x : ℂ) * Complex.I)
        exact (Complex.exp_ofReal_mul_I (U x)).symm

/-- Spectral diagonalization of the Gaussian characteristic function.  The
only effect of the constant term and of centering the eigenvalue coordinates
is the displayed unit-modulus phase. -/
theorem gaussianQuadraticCharacteristic_eq_phase_mul_diagonal {n : ℕ}
    (f₀ : ℝ) (f : Fin n → ℝ) {F : Matrix (Fin n) (Fin n) ℝ}
    (hF : F.IsHermitian) (t : ℝ) :
    gaussianQuadraticCharacteristic f₀ f F t =
      Complex.exp ((((t * (f₀ + ∑ j, hF.eigenvalues j) : ℝ) : ℂ) *
        Complex.I)) *
      diagonalCenteredCharProduct (eigenLinearCoefficient hF f)
        hF.eigenvalues t := by
  classical
  let a : Fin n → ℝ := eigenLinearCoefficient hF f
  let lam : Fin n → ℝ := hF.eigenvalues
  let shift : ℝ := f₀ + ∑ j, lam j
  let mu : Measure (Fin n → ℝ) := gaussianProductMeasure n
  let g : (Fin n → ℝ) → ℂ := fun x ↦
    Complex.exp ((((t * quadraticPolynomial f₀ f F x : ℝ) : ℂ) *
      Complex.I))
  have hg : Continuous g := by
    dsimp only [g]
    apply Complex.continuous_exp.comp
    exact (Complex.continuous_ofReal.comp
      (continuous_const.mul (continuous_quadraticPolynomial f₀ f F))).mul
        continuous_const
  have hpoint (z : Fin n → ℝ) :
      quadraticPolynomial f₀ f F (eigenvectorSynthesis hF z) =
        shift + diagonalCenteredSum a lam z := by
    rw [quadraticPolynomial_eigenvectorSynthesis]
    dsimp only [shift, a, lam, diagonalCenteredSum]
    unfold centeredCoordinatePolynomial
    rw [show (fun j ↦
        eigenLinearCoefficient hF f j * z j +
          hF.eigenvalues j * (z j ^ 2 - 1)) =
        fun j ↦
          (eigenLinearCoefficient hF f j * z j +
            hF.eigenvalues j * z j ^ 2) - hF.eigenvalues j by
      funext j
      ring]
    rw [Finset.sum_sub_distrib]
    ring
  rw [gaussianQuadraticCharacteristic_eq_integral_cexp]
  change (∫ x, g x ∂mu) = _
  calc
    ∫ x, g x ∂mu = ∫ z, g (eigenvectorSynthesis hF z) ∂mu := by
      rw [← integral_map (continuous_eigenvectorSynthesis hF).aemeasurable
        hg.aestronglyMeasurable]
      rw [gaussianProductMeasure_map_eigenvectorSynthesis]
    _ = ∫ z, Complex.exp ((((t *
          (shift + diagonalCenteredSum a lam z) : ℝ) : ℂ) * Complex.I))
          ∂mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z ↦ by
        dsimp only [g]
        rw [hpoint]
    _ = Complex.exp ((((t * shift : ℝ) : ℂ) * Complex.I)) *
        ∫ z, Complex.exp ((((t * diagonalCenteredSum a lam z : ℝ) : ℂ) *
          Complex.I)) ∂mu := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z ↦ by
        change Complex.exp ((((t *
            (shift + diagonalCenteredSum a lam z) : ℝ) : ℂ) * Complex.I)) =
          Complex.exp ((((t * shift : ℝ) : ℂ) * Complex.I)) *
            Complex.exp ((((t * diagonalCenteredSum a lam z : ℝ) : ℂ) *
              Complex.I))
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
    _ = Complex.exp ((((t * (f₀ + ∑ j, hF.eigenvalues j) : ℝ) : ℂ) *
          Complex.I)) *
        diagonalCenteredCharProduct (eigenLinearCoefficient hF f)
          hF.eigenvalues t := by
      dsimp only [mu, shift, a, lam]
      unfold gaussianProductMeasure
      rw [integral_diagonalCenteredSum_cexp]

theorem norm_gaussianQuadraticCharacteristic_eq_diagonalCharModulus {n : ℕ}
    (f₀ : ℝ) (f : Fin n → ℝ) {F : Matrix (Fin n) (Fin n) ℝ}
    (hF : F.IsHermitian) (t : ℝ) :
    ‖gaussianQuadraticCharacteristic f₀ f F t‖ =
      diagonalCharModulus (eigenLinearCoefficient hF f) hF.eigenvalues t := by
  rw [gaussianQuadraticCharacteristic_eq_phase_mul_diagonal,
    norm_mul, Complex.norm_exp]
  have hre :
      ((((t * (f₀ + ∑ j, hF.eigenvalues j) : ℝ) : ℂ) *
        Complex.I)).re = 0 := by simp
  rw [hre, Real.exp_zero, one_mul, norm_diagonalCenteredCharProduct]

theorem gaussianQuadraticCharacteristic_integrable_of_four_le_spectralBlocks
    {n : ℕ} (f₀ : ℝ) (f : Fin n → ℝ)
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    {κ : Type*} [Fintype κ] (B : κ → Finset (Fin n))
    (hcard : 4 ≤ Fintype.card κ)
    (hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset κ) : Set κ) B)
    {s : ℝ} (hs : 0 < s)
    (hblock : ∀ j, s ≤ ∑ i ∈ B j, (hF.eigenvalues i) ^ 2) :
    Integrable (gaussianQuadraticCharacteristic f₀ f F) := by
  let phase : ℝ → ℂ := fun t ↦
    Complex.exp ((((t * (f₀ + ∑ j, hF.eigenvalues j) : ℝ) : ℂ) *
      Complex.I))
  have hphase : AEStronglyMeasurable phase := by
    apply Continuous.aestronglyMeasurable
    dsimp only [phase]
    fun_prop
  have hphaseBound : ∀ᵐ t : ℝ, ‖phase t‖ ≤ 1 :=
    Filter.Eventually.of_forall fun t ↦ by
      dsimp only [phase]
      rw [Complex.norm_exp]
      simp
  have hdiag : Integrable
      (diagonalCenteredCharProduct (eigenLinearCoefficient hF f)
        hF.eigenvalues) :=
    diagonalCenteredCharProduct_integrable_of_four_le_spectralBlocks
      (eigenLinearCoefficient hF f) hF.eigenvalues B hcard hdisj hs hblock
  have hprod : Integrable (fun t ↦ phase t *
      diagonalCenteredCharProduct (eigenLinearCoefficient hF f)
        hF.eigenvalues t) :=
    hdiag.bdd_mul hphase hphaseBound
  apply hprod.congr
  exact Filter.Eventually.of_forall fun t ↦ by
    exact (gaussianQuadraticCharacteristic_eq_phase_mul_diagonal
      f₀ f hF t).symm

lemma frobeniusSq_eq_trace_transpose_mul_self {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    frobeniusSq A = (Aᵀ * A).trace := by
  classical
  simp only [frobeniusSq, Matrix.trace, Matrix.mul_apply,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [Matrix.transpose_apply, pow_two]

lemma frobenius_norm_sq_eq_frobeniusSq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖A‖ ^ 2 = frobeniusSq A := by
  change ‖WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (fun j ↦ A i j))‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  simp_rw [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  rfl

lemma frobeniusSq_unitary_left {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    frobeniusSq ((U : Matrix (Fin n) (Fin n) ℝ) * A) =
      frobeniusSq A := by
  have hunit : (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * U = 1 := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact Unitary.coe_star_mul_self U
  rw [frobeniusSq_eq_trace_transpose_mul_self,
    frobeniusSq_eq_trace_transpose_mul_self, Matrix.transpose_mul]
  rw [show Aᵀ * (U : Matrix (Fin n) (Fin n) ℝ)ᵀ *
      ((U : Matrix (Fin n) (Fin n) ℝ) * A) =
      Aᵀ * ((U : Matrix (Fin n) (Fin n) ℝ)ᵀ * U) * A by noncomm_ring]
  rw [hunit]
  noncomm_ring

lemma frobeniusSq_unitary_right {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix.unitaryGroup (Fin n) ℝ) :
    frobeniusSq (A * (U : Matrix (Fin n) (Fin n) ℝ)) =
      frobeniusSq A := by
  have hunit : (U : Matrix (Fin n) (Fin n) ℝ) *
      (U : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1 := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact Unitary.coe_mul_star_self U
  rw [frobeniusSq_eq_trace_transpose_mul_self,
    frobeniusSq_eq_trace_transpose_mul_self, Matrix.transpose_mul]
  rw [show (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * Aᵀ *
      (A * (U : Matrix (Fin n) (Fin n) ℝ)) =
      ((U : Matrix (Fin n) (Fin n) ℝ)ᵀ * (Aᵀ * A)) * U by noncomm_ring]
  rw [Matrix.trace_mul_cycle, hunit, one_mul]

lemma rank_unitary_conj {n : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    ((U : Matrix (Fin n) (Fin n) ℝ) * B *
      star (U : Matrix (Fin n) (Fin n) ℝ)).rank = B.rank := by
  rw [Matrix.rank_mul_eq_left_of_isUnit_det
    (star (U : Matrix (Fin n) (Fin n) ℝ))
    ((U : Matrix (Fin n) (Fin n) ℝ) * B)
    (Matrix.UnitaryGroup.det_isUnit (star U))]
  rw [Matrix.rank_mul_eq_right_of_isUnit_det
    (U : Matrix (Fin n) (Fin n) ℝ) B
    (Matrix.UnitaryGroup.det_isUnit U)]

/-- Robust Frobenius rank is invariant under the orthogonal spectral
change of basis, so it may be applied directly to the eigenvalue diagonal. -/
theorem robustRankAt_diagonal_eigenvalues {n r : ℕ} {s : ℝ}
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    (hrob : RobustRankAt r s F) :
    RobustRankAt r s (Matrix.diagonal hF.eigenvalues) := by
  intro B hBrank
  let U : Matrix.unitaryGroup (Fin n) ℝ := hF.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal hF.eigenvalues
  let C : Matrix (Fin n) (Fin n) ℝ :=
    (U : Matrix (Fin n) (Fin n) ℝ) * B *
      star (U : Matrix (Fin n) (Fin n) ℝ)
  have hCrank : C.rank ≤ r := by
    rw [show C.rank = B.rank by exact rank_unitary_conj U B]
    exact hBrank
  have hspec : F = (U : Matrix (Fin n) (Fin n) ℝ) * D *
      star (U : Matrix (Fin n) (Fin n) ℝ) := by
    simpa [U, D, Unitary.conjStarAlgAut_apply, Function.comp_def] using
      hF.spectral_theorem
  have hdiff : F - C = (U : Matrix (Fin n) (Fin n) ℝ) * (D - B) *
      star (U : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hspec]
    dsimp only [C]
    noncomm_ring
  have h := hrob C hCrank
  rw [frobenius_norm_sq_eq_frobeniusSq, hdiff,
    show frobeniusSq
        ((U : Matrix (Fin n) (Fin n) ℝ) * (D - B) *
          star (U : Matrix (Fin n) (Fin n) ℝ)) =
        frobeniusSq ((U : Matrix (Fin n) (Fin n) ℝ) * (D - B)) by
      simpa using
        (frobeniusSq_unitary_right
          ((U : Matrix (Fin n) (Fin n) ℝ) * (D - B)) (star U)),
    frobeniusSq_unitary_left,
    ← frobenius_norm_sq_eq_frobeniusSq] at h
  exact h

/-- The robust-rank hypothesis on a Hermitian matrix gives the exact
eigenvalue-tail inequality needed by the spectral-block argument. -/
theorem robustRankAt_eigenvalue_tail {n r : ℕ} {s : ℝ}
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    (hrob : RobustRankAt r s F)
    (S : Finset (Fin n)) (hS : S.card ≤ r) :
    s ≤ ∑ i with i ∉ S, (hF.eigenvalues i) ^ 2 :=
  robustRankAt_diagonal_tail
    (robustRankAt_diagonal_eigenvalues hF hrob) S hS

lemma trace_sq_eq_sum_sq_eigenvalues {n : ℕ}
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian) :
    (F * F).trace = ∑ i, (hF.eigenvalues i) ^ 2 := by
  classical
  let U : Matrix (Fin n) (Fin n) ℝ := hF.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal hF.eigenvalues
  have hspec : F = U * D * star U := by
    simpa [U, D, Unitary.conjStarAlgAut_apply] using hF.spectral_theorem
  have hunit : star U * U = 1 := by
    simpa only [U] using Unitary.coe_star_mul_self hF.eigenvectorUnitary
  conv_lhs => rw [hspec]
  rw [show (U * D * star U) * (U * D * star U) =
      U * (D * D) * star U by
    calc
      (U * D * star U) * (U * D * star U) =
          U * D * (star U * U) * D * star U := by noncomm_ring
      _ = U * (D * D) * star U := by rw [hunit]; noncomm_ring]
  rw [Matrix.trace_mul_cycle, hunit, one_mul]
  simp [D, pow_two]

lemma sum_sq_eigenvalues_eq_frobeniusSq {n : ℕ}
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian) :
    (∑ i, (hF.eigenvalues i) ^ 2) = frobeniusSq F := by
  classical
  rw [← trace_sq_eq_sum_sq_eigenvalues hF]
  have hsymm : ∀ i j, F i j = F j i := by
    intro i j
    simpa using hF.apply j i
  simp [Matrix.trace, Matrix.mul_apply, frobeniusSq, hsymm, pow_two]

lemma sum_sq_eigenLinearCoefficient_eq_vectorSqNorm {n : ℕ}
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    (f : Fin n → ℝ) :
    (∑ j, (eigenLinearCoefficient hF f j) ^ 2) = vectorSqNorm f := by
  classical
  let b := hF.eigenvectorBasis
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 f
  have ha (j : Fin n) :
      eigenLinearCoefficient hF f j = ⟪b j, v⟫_ℝ := by
    unfold eigenLinearCoefficient
    dsimp only [b, v]
    simp only [PiLp.inner_apply, Real.inner_apply, WithLp.ofLp_toLp]
    apply Finset.sum_congr rfl
    intro i _
    ring
  calc
    (∑ j, (eigenLinearCoefficient hF f j) ^ 2) =
        ∑ j, ‖⟪b j, v⟫_ℝ‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [ha, Real.norm_eq_abs, sq_abs]
    _ = ‖v‖ ^ 2 := b.sum_sq_norm_inner_right v
    _ = vectorSqNorm f := by
      rw [EuclideanSpace.real_norm_sq_eq]
      rfl

theorem totalVariance_eigenbasis {n : ℕ}
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    (f : Fin n → ℝ) :
    totalVariance (eigenLinearCoefficient hF f) hF.eigenvalues =
      2 * frobeniusSq F + vectorSqNorm f := by
  unfold totalVariance coordinateVariance
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_sq_eigenLinearCoefficient_eq_vectorSqNorm,
    sum_sq_eigenvalues_eq_frobeniusSq]
  ring

lemma coordinateVariance_div (a lam sigma : ℝ) (hsigma : sigma ≠ 0) :
    coordinateVariance (a / sigma) (lam / sigma) =
      coordinateVariance a lam / sigma ^ 2 := by
  unfold coordinateVariance
  field_simp

lemma totalVariance_div {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) (sigma : ℝ) (hsigma : sigma ≠ 0) :
    totalVariance (fun i ↦ a i / sigma) (fun i ↦ lam i / sigma) =
      totalVariance a lam / sigma ^ 2 := by
  unfold totalVariance
  simp_rw [coordinateVariance_div _ _ _ hsigma]
  rw [Finset.sum_div]

/-- Normalizing the original quadratic by its standard deviation gives the
unit-variance diagonal coefficients required by the local central limit
theorem. -/
theorem totalVariance_normalized_eigenbasis {n : ℕ}
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    (f : Fin n → ℝ) {sigma : ℝ} (hsigma : 0 < sigma)
    (hsigmaSq : sigma ^ 2 = 2 * frobeniusSq F + vectorSqNorm f) :
    totalVariance
        (fun i ↦ eigenLinearCoefficient hF f i / sigma)
        (fun i ↦ hF.eigenvalues i / sigma) = 1 := by
  rw [totalVariance_div _ _ _ hsigma.ne', totalVariance_eigenbasis,
    ← hsigmaSq, div_self (pow_ne_zero 2 hsigma.ne')]

/-- The centered law of a general real Gaussian quadratic polynomial. -/
noncomputable def gaussianQuadraticCenteredLaw {n : ℕ}
    (f : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) : Measure ℝ :=
  (gaussianProductMeasure n).map fun x ↦
    quadraticPolynomial 0 f F x - BooleanSlices.trace F

/-- The characteristic function of the centered Gaussian quadratic law is
the full Gaussian characteristic function used by Lemma 11.1, with the
trace subtracted in its constant coefficient. -/
theorem charFun_gaussianQuadraticCenteredLaw {n : ℕ}
    (f : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    charFun (gaussianQuadraticCenteredLaw f F) t =
      gaussianQuadraticCharacteristic (-BooleanSlices.trace F) f F t := by
  let g : (Fin n → ℝ) → ℝ := fun x ↦
    quadraticPolynomial 0 f F x - BooleanSlices.trace F
  have hg : AEMeasurable g (gaussianProductMeasure n) := by
    exact ((continuous_quadraticPolynomial 0 f F).sub
      continuous_const).aemeasurable
  rw [charFun_apply_real]
  change (∫ x : ℝ, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)
      ∂(gaussianProductMeasure n).map g) = _
  rw [integral_map hg (by fun_prop)]
  rw [gaussianQuadraticCharacteristic_eq_integral_cexp]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    congr 1
    push_cast
    congr 1
    dsimp only [g]
    unfold quadraticPolynomial
    ring_nf

/-- After normalization, scalar division of the law corresponds exactly to
rescaling the Fourier variable in Lemma 11.1's Gaussian characteristic
function. -/
theorem charFun_gaussianQuadraticCenteredLaw_map_div {n : ℕ}
    (f : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (sigma t : ℝ) :
    charFun ((gaussianQuadraticCenteredLaw f F).map
      (fun x ↦ x / sigma)) t =
        gaussianQuadraticCharacteristic (-BooleanSlices.trace F) f F
          (t / sigma) := by
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
  rw [← charFun_gaussianQuadraticCenteredLaw f F (t / sigma)]
  rw [charFun_apply_real]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    congr 1
    push_cast
    field_simp

/-- Dividing a finite random variable rescales its Fourier parameter. -/
lemma finiteCharacteristic_div {Ω : Type*} [Fintype Ω]
    (X : Ω → ℝ) (sigma t : ℝ) :
    finiteCharacteristic (fun x ↦ X x / sigma) t =
      finiteCharacteristic X (t / sigma) := by
  unfold finiteCharacteristic
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  congr 1
  apply Finset.sum_congr rfl
  intro x _hx
  congr 1
  push_cast
  ring

/-- The finite characteristic function used by Lemma 11.1 is the
characteristic function of its finite uniform pushforward law. -/
lemma charFun_finiteUniformLaw_eq_finiteCharacteristic
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (t : ℝ) :
    charFun (Erdos88.Esseen.finiteUniformLaw Ω X) t =
      finiteCharacteristic X t := by
  rw [Erdos88.Esseen.charFun_finiteUniformLaw]
  unfold finiteCharacteristic Fourier.finCharFun Fourier.finExpectation
  rw [Fintype.expect_eq_sum_div_card]
  congr 1
  apply Finset.sum_congr rfl
  intro x _hx
  congr 1
  push_cast
  ring_nf

/-- The normalized characteristic-function bridge needed in Claim 12.1:
Lemma 11.1 compares the finite product-slice law directly with the actual
normalized continuous Gaussian quadratic law. -/
lemma norm_productSliceCharacteristic_div_sub_normalizedLaw_le
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (ell : Fin m → ℕ) [Nonempty (ProductSlicePoint P ell)]
    (f : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (delta q : ℝ) (hdelta : 0 ≤ delta) (hn : 1 ≤ n)
    (hf : ∀ i, |f i| ≤ scale n (1 / 2 + 3 * delta))
    (hF : ∀ i j, |F i j| ≤ 1)
    (C : FiniteWeightedCoupling (ProductSlicePoint P ell) (Finset (Fin n)))
    (hclose : C.IsClose
      (productSliceQuadratic P ell (-BooleanSlices.trace F) f F)
      (sliceQuadratic (-BooleanSlices.trace F) f F)
      (scale n (3 / 4 + 4 * delta)) q)
    (hexception : ksssQuadraticDifferenceBound n delta * q ≤
      scale n (3 / 4 + 4 * delta)) (sigma t : ℝ) :
    ‖finiteCharacteristic
          (fun x ↦ productSliceQuadratic P ell
            (-BooleanSlices.trace F) f F x / sigma) t -
        charFun ((gaussianQuadraticCenteredLaw f F).map
          (fun x ↦ x / sigma)) t‖ ≤
      (675 / 2 : ℝ) * |t / sigma| ^ 4 * scale n (3 + 12 * delta) +
        6 * |t / sigma| * scale n (3 / 4 + 4 * delta) := by
  rw [finiteCharacteristic_div]
  rw [charFun_gaussianQuadraticCenteredLaw_map_div]
  exact norm_productSliceCharacteristic_sub_gaussianQuadratic_le_ksss
    P ell (-BooleanSlices.trace F) f F delta q hdelta hn hf hF C hclose hexception
      (t / sigma)

/-- Measure-theoretic form of the normalized Lemma 11.1 comparison.  Both
sides are now genuine probability laws, so this statement can be integrated
directly by the relative Esseen lemmas. -/
lemma norm_productSliceLaw_div_sub_normalizedLaw_le
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (ell : Fin m → ℕ) [Nonempty (ProductSlicePoint P ell)]
    (f : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (delta q : ℝ) (hdelta : 0 ≤ delta) (hn : 1 ≤ n)
    (hf : ∀ i, |f i| ≤ scale n (1 / 2 + 3 * delta))
    (hF : ∀ i j, |F i j| ≤ 1)
    (C : FiniteWeightedCoupling (ProductSlicePoint P ell) (Finset (Fin n)))
    (hclose : C.IsClose
      (productSliceQuadratic P ell (-BooleanSlices.trace F) f F)
      (sliceQuadratic (-BooleanSlices.trace F) f F)
      (scale n (3 / 4 + 4 * delta)) q)
    (hexception : ksssQuadraticDifferenceBound n delta * q ≤
      scale n (3 / 4 + 4 * delta)) (sigma t : ℝ) :
    ‖charFun (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
          (fun x ↦ productSliceQuadratic P ell
            (-BooleanSlices.trace F) f F x / sigma)) t -
        charFun ((gaussianQuadraticCenteredLaw f F).map
          (fun x ↦ x / sigma)) t‖ ≤
      (675 / 2 : ℝ) * |t / sigma| ^ 4 * scale n (3 + 12 * delta) +
        6 * |t / sigma| * scale n (3 / 4 + 4 * delta) := by
  rw [charFun_finiteUniformLaw_eq_finiteCharacteristic]
  exact norm_productSliceCharacteristic_div_sub_normalizedLaw_le
    P ell f F delta q hdelta hn hf hF C hclose hexception sigma t

/-- A raw Lemma 11.1 characteristic-function estimate, independently of
how its coupling was constructed, transfers to the two actual normalized
probability laws.  This is the form consumed by the public eventual theorem
`ksssLemma111`. -/
lemma norm_productSliceLaw_div_sub_normalizedLaw_le_of_characteristic
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (ell : Fin m → ℕ) [Nonempty (ProductSlicePoint P ell)]
    (f : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (delta : ℝ)
    (hpoint : ∀ tau : ℝ,
      ‖finiteCharacteristic
          (productSliceQuadratic P ell (-BooleanSlices.trace F) f F) tau -
        gaussianQuadraticCharacteristic (-BooleanSlices.trace F) f F tau‖ ≤
          (675 / 2 : ℝ) * |tau| ^ 4 * scale n (3 + 12 * delta) +
            6 * |tau| * scale n (3 / 4 + 4 * delta))
    (sigma t : ℝ) :
    ‖charFun (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
          (fun x ↦ productSliceQuadratic P ell
            (-BooleanSlices.trace F) f F x / sigma)) t -
        charFun ((gaussianQuadraticCenteredLaw f F).map
          (fun x ↦ x / sigma)) t‖ ≤
      (675 / 2 : ℝ) * |t / sigma| ^ 4 * scale n (3 + 12 * delta) +
        6 * |t / sigma| * scale n (3 / 4 + 4 * delta) := by
  rw [charFun_finiteUniformLaw_eq_finiteCharacteristic]
  rw [finiteCharacteristic_div]
  rw [charFun_gaussianQuadraticCenteredLaw_map_div]
  exact hpoint (t / sigma)

/-- A pointwise quartic-plus-linear Fourier estimate integrated over the
exact compact window used by the relative Esseen inequalities. -/
lemma fourierError_le_of_pointwise_polynomial
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {eps sigma A B : ℝ} (heps : 0 < eps) (hsigma : 0 < sigma)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hpoint : ∀ t : ℝ,
      ‖charFun mu t - charFun nu t‖ ≤
        A * |t / sigma| ^ 4 + B * |t / sigma|) :
    Erdos88.Esseen.fourierError mu nu eps ≤
      (4 / eps) *
        (A * (2 / (eps * sigma)) ^ 4 + B * (2 / (eps * sigma))) := by
  let T : ℝ := 2 / eps
  let S : ℝ := 2 / (eps * sigma)
  have hT : 0 < T := by dsimp only [T]; positivity
  have hS : 0 < S := by dsimp only [S]; positivity
  rw [Erdos88.Esseen.fourierError]
  change (∫ t in -T..T, ‖charFun mu t - charFun nu t‖) ≤
    (4 / eps) * (A * S ^ 4 + B * S)
  calc
    (∫ t in -T..T, ‖charFun mu t - charFun nu t‖) ≤
        ∫ _t in -T..T, (A * S ^ 4 + B * S) := by
      apply intervalIntegral.integral_mono_on (by linarith)
        ((continuous_norm.comp
          (continuous_charFun.sub continuous_charFun)).intervalIntegrable _ _)
        intervalIntegrable_const
      intro t ht
      have htAbs : |t| ≤ T := by
        rw [abs_le]
        exact ⟨ht.1, ht.2⟩
      have hdiv : |t / sigma| ≤ S := by
        rw [abs_div, abs_of_pos hsigma]
        dsimp only [S, T] at htAbs ⊢
        calc
          |t| / sigma ≤ (2 / eps) / sigma :=
            div_le_div_of_nonneg_right htAbs hsigma.le
          _ = 2 / (eps * sigma) := by field_simp
      exact (hpoint t).trans (by
        have hpow : |t / sigma| ^ 4 ≤ S ^ 4 :=
          pow_le_pow_left₀ (abs_nonneg _) hdiv 4
        exact add_le_add
          (mul_le_mul_of_nonneg_left hpow hA)
          (mul_le_mul_of_nonneg_left hdiv hB))
    _ = (4 / eps) * (A * S ^ 4 + B * S) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      dsimp only [T]
      ring

/-- Integrated form of the normalized Lemma 11.1 comparison.  This is the
fully explicit finite-`n` precursor of the Fourier estimate (12.8). -/
lemma fourierError_productSliceLaw_div_normalizedLaw_le
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (ell : Fin m → ℕ) [Nonempty (ProductSlicePoint P ell)]
    (f : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (delta q : ℝ) (hdelta : 0 ≤ delta) (hn : 1 ≤ n)
    (hf : ∀ i, |f i| ≤ scale n (1 / 2 + 3 * delta))
    (hF : ∀ i j, |F i j| ≤ 1)
    (C : FiniteWeightedCoupling (ProductSlicePoint P ell) (Finset (Fin n)))
    (hclose : C.IsClose
      (productSliceQuadratic P ell (-BooleanSlices.trace F) f F)
      (sliceQuadratic (-BooleanSlices.trace F) f F)
      (scale n (3 / 4 + 4 * delta)) q)
    (hexception : ksssQuadraticDifferenceBound n delta * q ≤
      scale n (3 / 4 + 4 * delta))
    {eps sigma : ℝ} (heps : 0 < eps) (hsigma : 0 < sigma) :
    Erdos88.Esseen.fourierError
        (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
          (fun x ↦ productSliceQuadratic P ell
            (-BooleanSlices.trace F) f F x / sigma))
        ((gaussianQuadraticCenteredLaw f F).map (fun x ↦ x / sigma)) eps ≤
      (4 / eps) *
        (((675 / 2 : ℝ) * scale n (3 + 12 * delta)) *
            (2 / (eps * sigma)) ^ 4 +
          (6 * scale n (3 / 4 + 4 * delta)) *
            (2 / (eps * sigma))) := by
  let : IsProbabilityMeasure (gaussianQuadraticCenteredLaw f F) := by
    unfold gaussianQuadraticCenteredLaw
    exact Measure.isProbabilityMeasure_map
      ((continuous_quadraticPolynomial 0 f F).sub continuous_const).aemeasurable
  let : IsProbabilityMeasure
      ((gaussianQuadraticCenteredLaw f F).map (fun x ↦ x / sigma)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  apply fourierError_le_of_pointwise_polynomial _ _ heps hsigma
  · exact mul_nonneg (by norm_num) (scale_nonneg _ _)
  · exact mul_nonneg (by norm_num) (scale_nonneg _ _)
  · intro t
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      (norm_productSliceLaw_div_sub_normalizedLaw_le
        P ell f F delta q hdelta hn hf hF C hclose hexception sigma t)

/-- Integrated normalized-law consequence of a raw pointwise Lemma 11.1
estimate.  Unlike the coupling-level variant, this applies directly to the
output of `ksssLemma111`. -/
lemma fourierError_productSliceLaw_div_normalizedLaw_le_of_characteristic
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (ell : Fin m → ℕ) [Nonempty (ProductSlicePoint P ell)]
    (f : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (delta : ℝ)
    (hpoint : ∀ tau : ℝ,
      ‖finiteCharacteristic
          (productSliceQuadratic P ell (-BooleanSlices.trace F) f F) tau -
        gaussianQuadraticCharacteristic (-BooleanSlices.trace F) f F tau‖ ≤
          (675 / 2 : ℝ) * |tau| ^ 4 * scale n (3 + 12 * delta) +
            6 * |tau| * scale n (3 / 4 + 4 * delta))
    {eps sigma : ℝ} (heps : 0 < eps) (hsigma : 0 < sigma) :
    Erdos88.Esseen.fourierError
        (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
          (fun x ↦ productSliceQuadratic P ell
            (-BooleanSlices.trace F) f F x / sigma))
        ((gaussianQuadraticCenteredLaw f F).map (fun x ↦ x / sigma)) eps ≤
      (4 / eps) *
        (((675 / 2 : ℝ) * scale n (3 + 12 * delta)) *
            (2 / (eps * sigma)) ^ 4 +
          (6 * scale n (3 / 4 + 4 * delta)) *
            (2 / (eps * sigma))) := by
  let : IsProbabilityMeasure (gaussianQuadraticCenteredLaw f F) := by
    unfold gaussianQuadraticCenteredLaw
    exact Measure.isProbabilityMeasure_map
      ((continuous_quadraticPolynomial 0 f F).sub continuous_const).aemeasurable
  let : IsProbabilityMeasure
      ((gaussianQuadraticCenteredLaw f F).map (fun x ↦ x / sigma)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  apply fourierError_le_of_pointwise_polynomial _ _ heps hsigma
  · exact mul_nonneg (by norm_num) (scale_nonneg _ _)
  · exact mul_nonneg (by norm_num) (scale_nonneg _ _)
  · intro t
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      (norm_productSliceLaw_div_sub_normalizedLaw_le_of_characteristic
        P ell f F delta hpoint sigma t)

/-- The explicit right-hand side in the integrated form of Lemma 11.1 is
eventually at most `n⁻¹ᐟ⁵` whenever the standard deviation has its natural
linear lower bound.  The slightly more flexible hypothesis `δ < 1 / 80`
records the exact exponent gap: the slower term is
`n ^ (-1 / 4 + 4 * δ)`. -/
lemma eventually_fourierComparison_rhs_le_scale
    {delta eps a : ℝ} (hdelta : 0 ≤ delta)
    (hdeltaSmall : delta < 1 / 80) (heps : 0 < eps) (ha : 0 < a) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ {sigma : ℝ},
      a * (n : ℝ) ≤ sigma →
      (4 / eps) *
          (((675 / 2 : ℝ) * scale n (3 + 12 * delta)) *
              (2 / (eps * sigma)) ^ 4 +
            (6 * scale n (3 / 4 + 4 * delta)) *
              (2 / (eps * sigma))) ≤
        scale n (-1 / 5) := by
  let D : ℝ := 2 / (eps * a)
  let K : ℝ := (4 / eps) * ((675 / 2 : ℝ) * D ^ 4 + 6 * D)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hexp : -1 / 4 + 4 * delta < -1 / 5 := by linarith
  have hrate := QuadraticCancellation.eventually_const_mul_rpow_le_rpow
    K (-1 / 4 + 4 * delta) (-1 / 5) hK hexp
  filter_upwards [hrate, Filter.eventually_ge_atTop 1] with n hrateN hn
  intro sigma hsigmaLower
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hsigma : 0 < sigma := lt_of_lt_of_le (mul_pos ha hnR) hsigmaLower
  have hden : 0 < eps * (a * (n : ℝ)) := by positivity
  have hdenLe : eps * (a * (n : ℝ)) ≤ eps * sigma :=
    mul_le_mul_of_nonneg_left hsigmaLower heps.le
  have hscaleOne : scale n 1 = (n : ℝ) := by
    unfold scale
    exact Real.rpow_one _
  have hscaleZero : scale n 0 = 1 := by
    unfold scale
    exact Real.rpow_zero _
  have hscaleNegOne : scale n (-1) = (n : ℝ)⁻¹ := by
    have hmul := scale_mul hnpos 1 (-1)
    rw [hscaleOne, show (1 : ℝ) + (-1) = 0 by ring, hscaleZero] at hmul
    rw [inv_eq_one_div]
    apply (eq_div_iff hnR.ne').2
    simpa only [mul_comm] using hmul
  have hS : 2 / (eps * sigma) ≤ D * scale n (-1) := by
    calc
      2 / (eps * sigma) ≤ 2 / (eps * (a * (n : ℝ))) :=
        div_le_div_of_nonneg_left (by norm_num) hden hdenLe
      _ = D * scale n (-1) := by
        dsimp only [D]
        rw [hscaleNegOne]
        field_simp
  have hSnonneg : 0 ≤ 2 / (eps * sigma) := by positivity
  have hS4 : (2 / (eps * sigma)) ^ 4 ≤
      (D * scale n (-1)) ^ 4 := pow_le_pow_left₀ hSnonneg hS 4
  have hscale4 : scale n (-1) ^ 4 = scale n (-4) := by
    unfold scale
    convert (Real.rpow_mul_natCast (x := (n : ℝ)) hnR.le (-1) 4).symm using 1 <;>
      norm_num
  have hquartic :
      ((675 / 2 : ℝ) * scale n (3 + 12 * delta)) *
          (2 / (eps * sigma)) ^ 4 ≤
        ((675 / 2 : ℝ) * D ^ 4) * scale n (-1 + 12 * delta) := by
    calc
      ((675 / 2 : ℝ) * scale n (3 + 12 * delta)) *
          (2 / (eps * sigma)) ^ 4 ≤
          ((675 / 2 : ℝ) * scale n (3 + 12 * delta)) *
            (D * scale n (-1)) ^ 4 :=
        mul_le_mul_of_nonneg_left hS4
          (mul_nonneg (by norm_num) (scale_nonneg _ _))
      _ = ((675 / 2 : ℝ) * D ^ 4) * scale n (-1 + 12 * delta) := by
        rw [mul_pow, hscale4]
        calc
          (675 / 2 * scale n (3 + 12 * delta)) *
              (D ^ 4 * scale n (-4)) =
              (675 / 2 * D ^ 4) *
                (scale n (3 + 12 * delta) * scale n (-4)) := by ring
          _ = (675 / 2 * D ^ 4) * scale n (-1 + 12 * delta) := by
            rw [scale_mul hnpos]
            congr 2
            ring
  have hlinear :
      (6 * scale n (3 / 4 + 4 * delta)) *
          (2 / (eps * sigma)) ≤
        (6 * D) * scale n (-1 / 4 + 4 * delta) := by
    calc
      (6 * scale n (3 / 4 + 4 * delta)) *
          (2 / (eps * sigma)) ≤
          (6 * scale n (3 / 4 + 4 * delta)) *
            (D * scale n (-1)) :=
        mul_le_mul_of_nonneg_left hS
          (mul_nonneg (by norm_num) (scale_nonneg _ _))
      _ = (6 * D) * scale n (-1 / 4 + 4 * delta) := by
        calc
          (6 * scale n (3 / 4 + 4 * delta)) *
              (D * scale n (-1)) =
              (6 * D) *
                (scale n (3 / 4 + 4 * delta) * scale n (-1)) := by ring
          _ = (6 * D) * scale n (-1 / 4 + 4 * delta) := by
            rw [scale_mul hnpos]
            congr 2
            ring
  have hquarticScale : scale n (-1 + 12 * delta) ≤
      scale n (-1 / 4 + 4 * delta) := by
    apply scale_mono_exponent hn
    linarith [hdelta]
  calc
    (4 / eps) *
          (((675 / 2 : ℝ) * scale n (3 + 12 * delta)) *
              (2 / (eps * sigma)) ^ 4 +
            (6 * scale n (3 / 4 + 4 * delta)) *
              (2 / (eps * sigma))) ≤
        (4 / eps) *
          (((675 / 2 : ℝ) * D ^ 4) * scale n (-1 + 12 * delta) +
            (6 * D) * scale n (-1 / 4 + 4 * delta)) := by
      gcongr
    _ ≤ K * scale n (-1 / 4 + 4 * delta) := by
      dsimp only [K]
      have houter : 0 ≤ 4 / eps := by positivity
      calc
        (4 / eps) *
            (((675 / 2 : ℝ) * D ^ 4) * scale n (-1 + 12 * delta) +
              (6 * D) * scale n (-1 / 4 + 4 * delta)) ≤
            (4 / eps) *
              (((675 / 2 : ℝ) * D ^ 4) *
                  scale n (-1 / 4 + 4 * delta) +
                (6 * D) * scale n (-1 / 4 + 4 * delta)) := by
          gcongr
        _ = 4 / eps * (675 / 2 * D ^ 4 + 6 * D) *
            scale n (-1 / 4 + 4 * delta) := by ring
    _ ≤ scale n (-1 / 5) := by
      unfold scale
      exact hrateN

/-- Eventual integrated Fourier form of KSSS Lemma 11.1 for the actual
finite product-slice law and the actual centered Gaussian quadratic law.
For every fixed smoothing window and every linear standard-deviation lower
bound, the comparison error is at most `n⁻¹ᐟ⁵`. -/
theorem eventually_ksssLemma111_fourierError_le_scale
    {delta eps a : ℝ} (hdelta : 0 < delta)
    (hdeltaSmall : delta < 1 / 80) (heps : 0 < eps) (ha : 0 < a) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (m : ℕ) (P : BucketPartition (Fin n) (Fin m))
        (ell : Fin m → ℕ) (f : Fin n → ℝ)
        (F : Matrix (Fin n) (Fin n) ℝ),
        IsKSSSPartition delta P → IsNearBalanced delta P ell →
        HasKSSSBalancedCoefficients delta P f F →
        ∃ hleft : Nonempty (ProductSlicePoint P ell),
          letI := hleft
          ∀ {sigma : ℝ}, a * (n : ℝ) ≤ sigma →
            Erdos88.Esseen.fourierError
                (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
                  (fun x ↦ productSliceQuadratic P ell
                    (-BooleanSlices.trace F) f F x / sigma))
                ((gaussianQuadraticCenteredLaw f F).map
                  (fun x ↦ x / sigma)) eps ≤
              scale n (-1 / 5) := by
  have h111 := ksssLemma111 delta hdelta (by linarith)
  have hrate := eventually_fourierComparison_rhs_le_scale
    hdelta.le hdeltaSmall heps ha
  filter_upwards [h111, hrate, Filter.eventually_ge_atTop 1] with
    n h111N hrateN hn
  intro m P ell f F hpart hbalanced hcoeff
  obtain ⟨hleft, _hmean, _hvariance, hpoint⟩ :=
    h111N m P ell (-BooleanSlices.trace F) f F hpart hbalanced hcoeff
  refine ⟨hleft, ?_⟩
  let := hleft
  intro sigma hsigmaLower
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsigma : 0 < sigma :=
    lt_of_lt_of_le (mul_pos ha hnR) hsigmaLower
  exact (fourierError_productSliceLaw_div_normalizedLaw_le_of_characteristic
    P ell f F delta hpoint heps hsigma).trans (hrateN hsigmaLower)

/-- Orthogonal diagonalization identifies the centered law itself, not only
its characteristic function, with the independent diagonal-coordinate law. -/
theorem gaussianQuadraticCenteredLaw_eq_diagonal {n : ℕ}
    (f : Fin n → ℝ) {F : Matrix (Fin n) (Fin n) ℝ}
    (hF : F.IsHermitian) :
    gaussianQuadraticCenteredLaw f F =
      diagonalCenteredLaw (eigenLinearCoefficient hF f) hF.eigenvalues := by
  classical
  let g : (Fin n → ℝ) → ℝ := fun x ↦
    quadraticPolynomial 0 f F x - BooleanSlices.trace F
  have hg : Measurable g := by
    dsimp only [g]
    exact ((continuous_quadraticPolynomial 0 f F).sub continuous_const).measurable
  unfold gaussianQuadraticCenteredLaw
  change (gaussianProductMeasure n).map g = _
  rw [← gaussianProductMeasure_map_eigenvectorSynthesis hF]
  rw [Measure.map_map hg (continuous_eigenvectorSynthesis hF).measurable]
  rw [diagonalCenteredLaw_eq_map_diagonalCenteredSum]
  congr 1
  funext z
  dsimp only [Function.comp_apply, g]
  have htrace : BooleanSlices.trace F = ∑ j, hF.eigenvalues j := by
    change F.trace = ∑ j, hF.eigenvalues j
    simpa using hF.trace_eq_sum_eigenvalues
  rw [quadraticPolynomial_eigenvectorSynthesis, htrace]
  unfold diagonalCenteredSum centeredCoordinatePolynomial
  rw [show (fun j ↦
      eigenLinearCoefficient hF f j * z j +
        hF.eigenvalues j * z j ^ 2) =
      fun j ↦
        (eigenLinearCoefficient hF f j * z j +
          hF.eigenvalues j * (z j ^ 2 - 1)) + hF.eigenvalues j by
    funext j
    ring]
  rw [Finset.sum_add_distrib]
  ring

/-- Dividing all diagonal coefficients by the same nonzero scale is exactly
the pushforward of the original centered law by scalar division. -/
theorem diagonalCenteredLaw_div {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) {sigma : ℝ} (hsigma : sigma ≠ 0) :
    diagonalCenteredLaw (fun i ↦ a i / sigma)
        (fun i ↦ lam i / sigma) =
      (diagonalCenteredLaw a lam).map (fun x ↦ x / sigma) := by
  classical
  rw [diagonalCenteredLaw_eq_map_diagonalCenteredSum,
    diagonalCenteredLaw_eq_map_diagonalCenteredSum]
  rw [Measure.map_map (by fun_prop)
    (continuous_diagonalCenteredSum a lam).measurable]
  congr 1
  funext z
  dsimp only [Function.comp_apply]
  unfold diagonalCenteredSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  unfold centeredCoordinatePolynomial
  field_simp

/-- Scaled no-influential-coordinate branch of the Gaussian small-ball
theorem.  Before normalization, the bound is exactly `2 ε / σ`. -/
theorem smallBall_diagonalCenteredLaw_map_div_le_of_small_coordinates
    {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) {sigma eps : ℝ} (hsigma : 0 < sigma)
    (hsum : totalVariance a lam = sigma ^ 2)
    (hsmall : ∀ i,
      coordinateVariance (a i) (lam i) ≤ sigma ^ 2 / 4)
    (heps : 0 ≤ eps) (x : ℝ) :
    Esseen.smallBall
        ((diagonalCenteredLaw a lam).map (fun y ↦ y / sigma))
        (eps / sigma) (x / sigma) ≤ 2 * (eps / sigma) := by
  rw [← diagonalCenteredLaw_div a lam hsigma.ne']
  apply smallBall_diagonalCenteredLaw_le_two_mul_of_small_coordinates
  · rw [totalVariance_div _ _ _ hsigma.ne', hsum,
      div_self (pow_ne_zero 2 hsigma.ne')]
  · intro i
    rw [coordinateVariance_div _ _ _ hsigma.ne']
    exact (div_le_iff₀ (sq_pos_of_pos hsigma)).2 (by
      nlinarith [hsmall i])
  · exact div_nonneg heps hsigma.le

/-- Coordinate-free version of the scaled no-influential-coordinate
Gaussian small-ball bound, after orthogonal diagonalization. -/
theorem smallBall_gaussianQuadraticCenteredLaw_map_div_le_of_small_coordinates
    {n : ℕ} (f : Fin n → ℝ)
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    {sigma eps : ℝ} (hsigma : 0 < sigma)
    (hsigmaSq : sigma ^ 2 = 2 * frobeniusSq F + vectorSqNorm f)
    (hsmall : ∀ i,
      coordinateVariance (eigenLinearCoefficient hF f i)
          (hF.eigenvalues i) ≤ sigma ^ 2 / 4)
    (heps : 0 ≤ eps) (x : ℝ) :
    Esseen.smallBall
        ((gaussianQuadraticCenteredLaw f F).map (fun y ↦ y / sigma))
        (eps / sigma) (x / sigma) ≤ 2 * (eps / sigma) := by
  rw [gaussianQuadraticCenteredLaw_eq_diagonal f hF]
  exact smallBall_diagonalCenteredLaw_map_div_le_of_small_coordinates
    (eigenLinearCoefficient hF f) hF.eigenvalues hsigma
      (by rw [totalVariance_eigenbasis, ← hsigmaSq]) hsmall heps x

/-- Law-level normalized spectral representation of a centered Gaussian
quadratic form. -/
theorem gaussianQuadraticCenteredLaw_map_div_eq_diagonal {n : ℕ}
    (f : Fin n → ℝ) {F : Matrix (Fin n) (Fin n) ℝ}
    (hF : F.IsHermitian) {sigma : ℝ} (hsigma : sigma ≠ 0) :
    (gaussianQuadraticCenteredLaw f F).map (fun x ↦ x / sigma) =
      diagonalCenteredLaw
        (fun i ↦ eigenLinearCoefficient hF f i / sigma)
        (fun i ↦ hF.eigenvalues i / sigma) := by
  rw [gaussianQuadraticCenteredLaw_eq_diagonal f hF,
    ← diagonalCenteredLaw_div _ _ hsigma]

/-- Claim 12.1's continuous-density conclusion for the normalized original
Gaussian quadratic form, obtained by combining orthogonal diagonalization,
variance normalization, and the diagonal spectral-block theorem. -/
theorem exists_continuousDensity_gaussianQuadratic_normalized
    {n : ℕ} (f : Fin n → ℝ)
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    {sigma : ℝ} (hsigma : 0 < sigma)
    (hsigmaSq : sigma ^ 2 = 2 * frobeniusSq F + vectorSqNorm f)
    {κ : Type*} [Fintype κ] (B : κ → Finset (Fin n))
    (hcard : 4 ≤ Fintype.card κ)
    (hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset κ) : Set κ) B)
    {s : ℝ} (hs : 0 < s)
    (hblock : ∀ j, s ≤
      ∑ i ∈ B j, (hF.eigenvalues i / sigma) ^ 2) :
    ∃ p : ℝ → ℝ,
      Esseen.HasContinuousDensity
          ((gaussianQuadraticCenteredLaw f F).map (fun x ↦ x / sigma)) p ∧
        ∀ u : ℝ,
          |p u - standardNormalDensity u| ≤
            (2 * π)⁻¹ *
              (1280 /
                  lyapunovGamma
                    (fun i ↦ eigenLinearCoefficient hF f i / sigma)
                    (fun i ↦ hF.eigenvalues i / sigma) +
                16 /
                  (s * lyapunovGamma
                    (fun i ↦ eigenLinearCoefficient hF f i / sigma)
                    (fun i ↦ hF.eigenvalues i / sigma))) := by
  let a : Fin n → ℝ := fun i ↦ eigenLinearCoefficient hF f i / sigma
  let lam : Fin n → ℝ := fun i ↦ hF.eigenvalues i / sigma
  have hsum : totalVariance a lam = 1 := by
    exact totalVariance_normalized_eigenbasis hF f hsigma hsigmaSq
  obtain ⟨p, hp, hcompare⟩ :=
    exists_continuousDensity_diagonal_comparison_of_four_le_spectralBlocks
      a lam B hcard hdisj hsum hs hblock
  refine ⟨p, ?_, hcompare⟩
  rw [gaussianQuadraticCenteredLaw_map_div_eq_diagonal f hF hsigma.ne']
  exact hp

private lemma exists_subset_sum_between_one_two {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (S : Finset ι) {c : ℝ} (hc : 0 < c)
    (hsmall : ∀ i ∈ S, w i < c)
    (hsum : c ≤ ∑ i ∈ S, w i) :
    ∃ T ⊆ S, c ≤ ∑ i ∈ T, w i ∧ ∑ i ∈ T, w i < 2 * c := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty] at hsum
      linarith
  | @insert a S ha ih =>
      by_cases hSc : c ≤ ∑ i ∈ S, w i
      · obtain ⟨T, hTS, hTc, hTlt⟩ := ih
          (fun i hi ↦ hsmall i (Finset.mem_insert_of_mem hi)) hSc
        exact ⟨T, hTS.trans (Finset.subset_insert a S), hTc, hTlt⟩
      · have hSlt : ∑ i ∈ S, w i < c := lt_of_not_ge hSc
        have halt : w a < c := hsmall a (Finset.mem_insert_self a S)
        refine ⟨insert a S, Finset.Subset.rfl, hsum, ?_⟩
        rw [Finset.sum_insert ha]
        linarith

/-- A finite set whose weights are all below `c`, but whose total weight is
at least `2kc`, contains `k` pairwise-disjoint pieces of weight at least
`c`.  This is the greedy packing step behind the rank-`r` form of KSSS
Lemma 5.11. -/
private lemma exists_disjoint_blocks_of_sum {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (S : Finset ι) {c : ℝ} (hc : 0 < c)
    (hsmall : ∀ i ∈ S, w i < c) :
    ∀ k : ℕ, 2 * (k : ℝ) * c ≤ ∑ i ∈ S, w i →
      ∃ B : Fin k → Finset ι,
        Set.PairwiseDisjoint (Set.univ : Set (Fin k)) B ∧
          (∀ j, B j ⊆ S) ∧ ∀ j, c ≤ ∑ i ∈ B j, w i := by
  classical
  intro k
  induction k generalizing S with
  | zero =>
      intro hsum
      refine ⟨fun j ↦ Fin.elim0 j, ?_, ?_, ?_⟩
      · intro i hi
        exact Fin.elim0 i
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
  | succ k ih =>
      intro hsum
      have hcS : c ≤ ∑ i ∈ S, w i := by
        have hk0 : (0 : ℝ) ≤ k := by positivity
        rw [Nat.cast_add, Nat.cast_one] at hsum
        nlinarith
      obtain ⟨B0, hB0S, hB0c, hB0lt⟩ :=
        exists_subset_sum_between_one_two w S hc hsmall hcS
      let S1 := S \ B0
      have hsumS1 : ∑ i ∈ S1, w i =
          (∑ i ∈ S, w i) - ∑ i ∈ B0, w i :=
        Finset.sum_sdiff_eq_sub hB0S
      have hremaining : 2 * (k : ℝ) * c ≤ ∑ i ∈ S1, w i := by
        rw [hsumS1]
        push_cast at hsum
        nlinarith
      have hsmall1 : ∀ i ∈ S1, w i < c := fun i hi ↦
        hsmall i (Finset.sdiff_subset hi)
      obtain ⟨Bt, hBtDisj, hBtS1, hBtMass⟩ := ih S1 hsmall1 hremaining
      let B : Fin (k + 1) → Finset ι := Fin.cases B0 Bt
      refine ⟨B, ?_, ?_, ?_⟩
      · intro i hi j hj hij
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero => exact (hij rfl).elim
            | succ j =>
                change Disjoint B0 (Bt j)
                rw [Finset.disjoint_left]
                intro x hx0 hxj
                exact (Finset.mem_sdiff.mp (hBtS1 j hxj)).2 hx0
        | succ i =>
            cases j using Fin.cases with
            | zero =>
                change Disjoint (Bt i) B0
                rw [Finset.disjoint_left]
                intro x hxi hx0
                exact (Finset.mem_sdiff.mp (hBtS1 i hxi)).2 hx0
            | succ j =>
                exact hBtDisj (by simp) (by simp) (by
                  intro h
                  exact hij (congrArg Fin.succ h))
      · intro j
        cases j using Fin.cases with
        | zero => exact hB0S
        | succ j => exact (hBtS1 j).trans Finset.sdiff_subset
      · intro j
        cases j using Fin.cases with
        | zero => exact hB0c
        | succ j => exact hBtMass j

/-- A tail of mass `s` after deleting any `r` coordinates contains `k≤r`
disjoint blocks, each of mass at least `s/(2k)`.  Large coordinates are
used as singleton blocks; otherwise greedy packing applies to the remaining
small coordinates. -/
private lemma exists_disjoint_blocks_of_tail_mass
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) {r k : ℕ} {s : ℝ} (hk : 0 < k) (hkr : k ≤ r)
    (hs : 0 < s)
    (htail : ∀ S : Finset ι, S.card ≤ r →
      s ≤ ∑ i with i ∉ S, w i) :
    ∃ B : Fin k → Finset ι,
      Set.PairwiseDisjoint (Set.univ : Set (Fin k)) B ∧
        ∀ j, s / (2 * (k : ℝ)) ≤ ∑ i ∈ B j, w i := by
  classical
  let c : ℝ := s / (2 * (k : ℝ))
  let L : Finset ι := Finset.univ.filter fun i ↦ c ≤ w i
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  by_cases hlarge : k ≤ L.card
  · obtain ⟨T, hTL, hTcard⟩ := Finset.exists_subset_card_eq hlarge
    let e : Fin k ≃ T := (Finset.equivFinOfCardEq hTcard).symm
    let B : Fin k → Finset ι := fun j ↦ {(e j).1}
    refine ⟨B, ?_, ?_⟩
    · intro i hi j hj hij
      simp only [B, Finset.disjoint_singleton]
      intro heq
      exact hij (e.injective (Subtype.ext heq))
    · intro j
      simp only [B, Finset.sum_singleton]
      have hejL : (e j : ι) ∈ L := hTL (e j).property
      exact (Finset.mem_filter.mp hejL).2
  · have hLcard : L.card ≤ r := by
      have : L.card < k := lt_of_not_ge hlarge
      omega
    have htailL := htail L hLcard
    let S : Finset ι := Finset.univ \ L
    have hsumS : 2 * (k : ℝ) * c ≤ ∑ i ∈ S, w i := by
      have hcEq : 2 * (k : ℝ) * c = s := by
        dsimp only [c]
        field_simp
      rw [hcEq]
      have hset : Finset.univ.filter (fun i ↦ i ∉ L) = S := by
        ext i
        simp only [S, Finset.mem_filter, Finset.mem_univ,
          Finset.mem_sdiff, true_and]
      simpa only [hset] using htailL
    have hsmall : ∀ i ∈ S, w i < c := by
      intro i hi
      have hiL : i ∉ L := (Finset.mem_sdiff.mp hi).2
      simpa only [L, Finset.mem_filter, Finset.mem_univ, true_and,
        not_le] using hiL
    obtain ⟨B, hdisj, hsub, hmass⟩ :=
      exists_disjoint_blocks_of_sum w S hc hsmall k hsumS
    exact ⟨B, hdisj, by simpa only [c] using hmass⟩

private lemma exists_four_disjoint_blocks_of_sum {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (S : Finset ι) {c : ℝ} (hc : 0 < c)
    (hsmall : ∀ i ∈ S, w i < c)
    (hsum : 8 * c ≤ ∑ i ∈ S, w i) :
    ∃ B : Fin 4 → Finset ι,
      Set.PairwiseDisjoint (Set.univ : Set (Fin 4)) B ∧
        ∀ j, c ≤ ∑ i ∈ B j, w i := by
  classical
  have hcS : c ≤ ∑ i ∈ S, w i := by linarith
  obtain ⟨B0, hB0S, hB0c, hB0lt⟩ :=
    exists_subset_sum_between_one_two w S hc hsmall hcS
  let S1 := S \ B0
  have hsumS1 : ∑ i ∈ S1, w i =
      (∑ i ∈ S, w i) - ∑ i ∈ B0, w i := by
    exact Finset.sum_sdiff_eq_sub hB0S
  have h6 : 6 * c ≤ ∑ i ∈ S1, w i := by linarith
  have hsmall1 : ∀ i ∈ S1, w i < c := fun i hi ↦
    hsmall i (Finset.sdiff_subset hi)
  obtain ⟨B1, hB1S1, hB1c, hB1lt⟩ :=
    exists_subset_sum_between_one_two w S1 hc hsmall1 (by linarith)
  let S2 := S1 \ B1
  have hsumS2 : ∑ i ∈ S2, w i =
      (∑ i ∈ S1, w i) - ∑ i ∈ B1, w i := by
    exact Finset.sum_sdiff_eq_sub hB1S1
  have h4 : 4 * c ≤ ∑ i ∈ S2, w i := by linarith
  have hsmall2 : ∀ i ∈ S2, w i < c := fun i hi ↦
    hsmall1 i (Finset.sdiff_subset hi)
  obtain ⟨B2, hB2S2, hB2c, hB2lt⟩ :=
    exists_subset_sum_between_one_two w S2 hc hsmall2 (by linarith)
  let S3 := S2 \ B2
  have hsumS3 : ∑ i ∈ S3, w i =
      (∑ i ∈ S2, w i) - ∑ i ∈ B2, w i := by
    exact Finset.sum_sdiff_eq_sub hB2S2
  have h2 : 2 * c ≤ ∑ i ∈ S3, w i := by linarith
  have hsmall3 : ∀ i ∈ S3, w i < c := fun i hi ↦
    hsmall2 i (Finset.sdiff_subset hi)
  obtain ⟨B3, hB3S3, hB3c, hB3lt⟩ :=
    exists_subset_sum_between_one_two w S3 hc hsmall3 (by linarith)
  have hd01 : Disjoint B0 B1 := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    exact (Finset.mem_sdiff.mp (hB1S1 hx1)).2 hx0
  have hd02 : Disjoint B0 B2 := by
    rw [Finset.disjoint_left]
    intro x hx0 hx2
    have hxS1 := Finset.sdiff_subset (hB2S2 hx2)
    exact (Finset.mem_sdiff.mp hxS1).2 hx0
  have hd12 : Disjoint B1 B2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_sdiff.mp (hB2S2 hx2)).2 hx1
  have hd03 : Disjoint B0 B3 := by
    rw [Finset.disjoint_left]
    intro x hx0 hx3
    have hxS2 := Finset.sdiff_subset (hB3S3 hx3)
    have hxS1 := Finset.sdiff_subset hxS2
    exact (Finset.mem_sdiff.mp hxS1).2 hx0
  have hd13 : Disjoint B1 B3 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx3
    have hxS2 := Finset.sdiff_subset (hB3S3 hx3)
    exact (Finset.mem_sdiff.mp hxS2).2 hx1
  have hd23 : Disjoint B2 B3 := by
    rw [Finset.disjoint_left]
    intro x hx2 hx3
    exact (Finset.mem_sdiff.mp (hB3S3 hx3)).2 hx2
  have hd10 : Disjoint B1 B0 := hd01.symm
  have hd20 : Disjoint B2 B0 := hd02.symm
  have hd21 : Disjoint B2 B1 := hd12.symm
  have hd30 : Disjoint B3 B0 := hd03.symm
  have hd31 : Disjoint B3 B1 := hd13.symm
  have hd32 : Disjoint B3 B2 := hd23.symm
  let B : Fin 4 → Finset ι := fun j ↦
    if j = 0 then B0 else if j = 1 then B1 else if j = 2 then B2 else B3
  refine ⟨B, ?_, ?_⟩
  · intro i hi j hj hij
    change Disjoint (B i) (B j)
    fin_cases i <;> fin_cases j <;> simp_all [B]
  · intro j
    fin_cases j <;> simp only [B, Fin.zero_eta, ↓reduceIte, OfNat.ofNat]
    all_goals assumption

private lemma exists_four_disjoint_blocks_of_tail_mass
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) {r : ℕ} {s : ℝ} (hr : 3 ≤ r) (hs : 0 < s)
    (htail : ∀ S : Finset ι, S.card ≤ r →
      s ≤ ∑ i with i ∉ S, w i) :
    ∃ B : Fin 4 → Finset ι,
      Set.PairwiseDisjoint (Set.univ : Set (Fin 4)) B ∧
        ∀ j, s / 8 ≤ ∑ i ∈ B j, w i := by
  classical
  let c : ℝ := s / 8
  let L : Finset ι := Finset.univ.filter fun i ↦ c ≤ w i
  have hc : 0 < c := by dsimp only [c]; positivity
  by_cases hfour : 4 ≤ L.card
  · obtain ⟨T, hTL, hTcard⟩ := Finset.exists_subset_card_eq hfour
    let e : Fin 4 ≃ T := (Finset.equivFinOfCardEq hTcard).symm
    let B : Fin 4 → Finset ι := fun j ↦ {(e j).1}
    refine ⟨B, ?_, ?_⟩
    · intro i hi j hj hij
      simp only [B, Finset.disjoint_singleton]
      intro heq
      exact hij (e.injective (Subtype.ext heq))
    · intro j
      simp only [B, Finset.sum_singleton]
      have hejL : (e j : ι) ∈ L := hTL (e j).property
      exact (Finset.mem_filter.mp hejL).2
  · have hLcard : L.card ≤ 3 := by omega
    have htailL := htail L (hLcard.trans hr)
    let S : Finset ι := Finset.univ \ L
    have hsumS : 8 * c ≤ ∑ i ∈ S, w i := by
      dsimp only [c]
      have hcEq : 8 * (s / 8) = s := by ring
      rw [hcEq]
      have hset : Finset.univ.filter (fun i ↦ i ∉ L) = S := by
        ext i
        simp only [S, Finset.mem_filter, Finset.mem_univ,
          Finset.mem_sdiff, true_and]
      simpa only [hset] using htailL
    have hsmall : ∀ i ∈ S, w i < c := by
      intro i hi
      have hiL : i ∉ L := (Finset.mem_sdiff.mp hi).2
      simpa only [L, Finset.mem_filter, Finset.mem_univ, true_and,
        not_le] using hiL
    simpa only [c] using exists_four_disjoint_blocks_of_sum w S hc hsmall hsumS

/-- Rank-`r` spectral-block extraction from robust Frobenius rank.  This is
the source-shaped combinatorial input to KSSS Lemma 5.11: the eigenvalue
tail is split into `r` disjoint blocks, each retaining mass `s/(2r)`. -/
theorem exists_eigenvalue_blocks_of_robustRankAt
    {n r : ℕ} {s : ℝ} {F : Matrix (Fin n) (Fin n) ℝ}
    (hF : F.IsHermitian) (hrob : RobustRankAt r s F)
    (hr : 0 < r) (hs : 0 < s) :
    ∃ B : Fin r → Finset (Fin n),
      Set.PairwiseDisjoint (Set.univ : Set (Fin r)) B ∧
        ∀ j, s / (2 * (r : ℝ)) ≤
          ∑ i ∈ B j, (hF.eigenvalues i) ^ 2 := by
  classical
  apply exists_disjoint_blocks_of_tail_mass
    (fun i ↦ (hF.eigenvalues i) ^ 2) hr le_rfl hs
  intro S hS
  exact robustRankAt_eigenvalue_tail hF hrob S hS

/-- KSSS Lemma 5.11 in robust-rank form.  Robust rank `r` forces `r/4`
powers of Gaussian characteristic-function decay, with an explicit
`s/(2r)` spectral scale. -/
theorem norm_gaussianQuadraticCharacteristic_le_of_robustRankAt
    {n r : ℕ} (f₀ : ℝ) (f : Fin n → ℝ)
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    {s : ℝ} (hrob : RobustRankAt r s F) (hr : 0 < r) (hs : 0 < s)
    (t : ℝ) :
    ‖gaussianQuadraticCharacteristic f₀ f F t‖ ≤
      (1 + 4 * (s / (2 * (r : ℝ))) * t ^ 2) ^
        (-(r : ℝ) / 4 : ℝ) := by
  obtain ⟨B, hdisj, hmass⟩ :=
    exists_eigenvalue_blocks_of_robustRankAt hF hrob hr hs
  have hdisj' : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin r)) : Set (Fin r)) B := by
    simpa only [Finset.coe_univ] using hdisj
  rw [norm_gaussianQuadraticCharacteristic_eq_diagonalCharModulus f₀ f hF t]
  simpa only [Fintype.card_fin] using
    diagonalCharModulus_le_of_spectralBlocks
      (eigenLinearCoefficient hF f) hF.eigenvalues B hdisj'
        (by positivity) hmass t

/-- The rank-400 specialization used in (12.8).  At frequencies
`|t| ≥ n⁻⁰·⁹⁹`, robust spectral mass `c n²` gives the explicit decay
`(c/200)⁻¹⁰⁰ n⁻²`. -/
theorem norm_gaussianQuadraticCharacteristic_le_rank400
    {n : ℕ} (f₀ : ℝ) (f : Fin n → ℝ)
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    {c t : ℝ} (hc : 0 < c) (hn : 1 ≤ n)
    (hrob : RobustRankAt 400 (c * (n : ℝ) ^ 2) F)
    (ht : (n : ℝ) ^ (-99 / 100 : ℝ) ≤ |t|) :
    ‖gaussianQuadraticCharacteristic f₀ f F t‖ ≤
      (c / 200) ^ (-100 : ℝ) * (n : ℝ) ^ (-2 : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < c * (n : ℝ) ^ 2 := mul_pos hc (sq_pos_of_pos hnpos)
  have hraw := norm_gaussianQuadraticCharacteristic_le_of_robustRankAt
    f₀ f hF hrob (by norm_num) hs t
  have htSq : ((n : ℝ) ^ (-99 / 100 : ℝ)) ^ 2 ≤ t ^ 2 := by
    have h :=
      (sq_le_sq₀ (Real.rpow_nonneg hnpos.le _) (abs_nonneg t)).2 ht
    simpa only [sq_abs] using h
  have hpow2 : ((n : ℝ) ^ (-99 / 100 : ℝ)) ^ 2 =
      (n : ℝ) ^ (-99 / 50 : ℝ) := by
    calc
      ((n : ℝ) ^ (-99 / 100 : ℝ)) ^ 2 =
          (n : ℝ) ^ ((-99 / 100 : ℝ) * (2 : ℕ)) :=
        (Real.rpow_mul_natCast hnpos.le (-99 / 100 : ℝ) 2).symm
      _ = (n : ℝ) ^ (-99 / 50 : ℝ) := by norm_num
  have hnSq : (n : ℝ) ^ 2 = (n : ℝ) ^ (2 : ℝ) := by
    simpa using (Real.rpow_natCast (n : ℝ) 2).symm
  have hcombine : (n : ℝ) ^ 2 *
      (n : ℝ) ^ (-99 / 50 : ℝ) = (n : ℝ) ^ (1 / 50 : ℝ) := by
    rw [hnSq, ← Real.rpow_add hnpos]
    norm_num
  have hbase :
      (c / 200) * (n : ℝ) ^ (1 / 50 : ℝ) ≤
        1 + 4 * (c * (n : ℝ) ^ 2 / (2 * (400 : ℝ))) * t ^ 2 := by
    rw [show 4 * (c * (n : ℝ) ^ 2 / (2 * (400 : ℝ))) =
        (c / 200) * (n : ℝ) ^ 2 by ring]
    have hcoef : 0 ≤ (c / 200) * (n : ℝ) ^ 2 :=
      mul_nonneg (div_nonneg hc.le (by norm_num)) (sq_nonneg (n : ℝ))
    have hmul :
        ((c / 200) * (n : ℝ) ^ 2) *
            ((n : ℝ) ^ (-99 / 100 : ℝ)) ^ 2 ≤
          ((c / 200) * (n : ℝ) ^ 2) * t ^ 2 :=
      mul_le_mul_of_nonneg_left htSq hcoef
    calc
      (c / 200) * (n : ℝ) ^ (1 / 50 : ℝ) =
          ((c / 200) * (n : ℝ) ^ 2) *
            ((n : ℝ) ^ (-99 / 100 : ℝ)) ^ 2 := by
          rw [hpow2, ← hcombine]
          ring
      _ ≤ ((c / 200) * (n : ℝ) ^ 2) * t ^ 2 := hmul
      _ ≤ 1 + ((c / 200) * (n : ℝ) ^ 2) * t ^ 2 := by linarith
  have hbasePos : 0 < (c / 200) * (n : ℝ) ^ (1 / 50 : ℝ) := by positivity
  have hdecay :
      (1 + 4 * (c * (n : ℝ) ^ 2 / (2 * (400 : ℝ))) * t ^ 2) ^
          (-((400 : ℝ)) / 4 : ℝ) ≤
        ((c / 200) * (n : ℝ) ^ (1 / 50 : ℝ)) ^ (-100 : ℝ) := by
    convert Real.rpow_le_rpow_of_nonpos hbasePos hbase
      (by norm_num : (-100 : ℝ) ≤ 0) using 1 <;> norm_num
  have hnormalize :
      ((c / 200) * (n : ℝ) ^ (1 / 50 : ℝ)) ^ (-100 : ℝ) =
        (c / 200) ^ (-100 : ℝ) * (n : ℝ) ^ (-2 : ℝ) := by
    rw [Real.mul_rpow (div_nonneg hc.le (by norm_num))
      (Real.rpow_nonneg hnpos.le _)]
    rw [← Real.rpow_mul hnpos.le]
    congr 2
    norm_num
  exact hraw.trans (hdecay.trans_eq hnormalize)

/-- A positive robust-rank tail at rank at least three contains four disjoint
spectral blocks, each carrying at least one eighth of the tail mass. -/
theorem exists_four_eigenvalue_blocks_of_robustRankAt
    {n r : ℕ} {s : ℝ} {F : Matrix (Fin n) (Fin n) ℝ}
    (hF : F.IsHermitian) (hrob : RobustRankAt r s F)
    (hr : 3 ≤ r) (hs : 0 < s) :
    ∃ B : Fin 4 → Finset (Fin n),
      Set.PairwiseDisjoint (Set.univ : Set (Fin 4)) B ∧
        ∀ j, s / 8 ≤ ∑ i ∈ B j, (hF.eigenvalues i) ^ 2 := by
  classical
  apply exists_four_disjoint_blocks_of_tail_mass
    (fun i ↦ (hF.eigenvalues i) ^ 2) hr hs
  intro S hS
  exact robustRankAt_eigenvalue_tail hF hrob S hS

/-- The preceding four spectral blocks after division by the standard
deviation of the original Gaussian quadratic polynomial. -/
theorem exists_four_normalized_eigenvalue_blocks_of_robustRankAt
    {n r : ℕ} {s sigma : ℝ} {F : Matrix (Fin n) (Fin n) ℝ}
    (hF : F.IsHermitian) (hrob : RobustRankAt r s F)
    (hr : 3 ≤ r) (hs : 0 < s) (hsigma : 0 < sigma) :
    ∃ B : Fin 4 → Finset (Fin n),
      Set.PairwiseDisjoint (Set.univ : Set (Fin 4)) B ∧
        ∀ j, s / (8 * sigma ^ 2) ≤
          ∑ i ∈ B j, (hF.eigenvalues i / sigma) ^ 2 := by
  classical
  obtain ⟨B, hdisj, hmass⟩ :=
    exists_four_eigenvalue_blocks_of_robustRankAt hF hrob hr hs
  refine ⟨B, hdisj, ?_⟩
  intro j
  rw [show (∑ i ∈ B j, (hF.eigenvalues i / sigma) ^ 2) =
      (∑ i ∈ B j, (hF.eigenvalues i) ^ 2) / sigma ^ 2 by
    simp_rw [div_pow]
    rw [Finset.sum_div]]
  have hsigmaSq : 0 < sigma ^ 2 := sq_pos_of_pos hsigma
  calc
    s / (8 * sigma ^ 2) = (s / 8) / sigma ^ 2 := by field_simp
    _ ≤ (∑ i ∈ B j, (hF.eigenvalues i) ^ 2) / sigma ^ 2 :=
      (div_le_div_iff_of_pos_right hsigmaSq).2 (hmass j)

/-- Claim 12.1's continuous-density conclusion obtained directly from a
positive robust-rank hypothesis on the original Hermitian quadratic matrix. -/
theorem exists_continuousDensity_gaussianQuadratic_normalized_of_robustRankAt
    {n r : ℕ} (f : Fin n → ℝ)
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    {sigma s : ℝ} (hsigma : 0 < sigma)
    (hsigmaSq : sigma ^ 2 = 2 * frobeniusSq F + vectorSqNorm f)
    (hrob : RobustRankAt r s F) (hr : 3 ≤ r) (hs : 0 < s) :
    ∃ p : ℝ → ℝ,
      Esseen.HasContinuousDensity
          ((gaussianQuadraticCenteredLaw f F).map (fun x ↦ x / sigma)) p ∧
        ∀ u : ℝ,
          |p u - standardNormalDensity u| ≤
            (2 * π)⁻¹ *
              (1280 /
                  lyapunovGamma
                    (fun i ↦ eigenLinearCoefficient hF f i / sigma)
                    (fun i ↦ hF.eigenvalues i / sigma) +
                16 /
                  ((s / (8 * sigma ^ 2)) *
                    lyapunovGamma
                      (fun i ↦ eigenLinearCoefficient hF f i / sigma)
                      (fun i ↦ hF.eigenvalues i / sigma))) := by
  obtain ⟨B, hdisj, hblock⟩ :=
    exists_four_normalized_eigenvalue_blocks_of_robustRankAt
      hF hrob hr hs hsigma
  have hdisj' : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)) B := by
    simpa only [Finset.coe_univ] using hdisj
  exact exists_continuousDensity_gaussianQuadratic_normalized
    f hF hsigma hsigmaSq B (by norm_num) hdisj'
    (by positivity) hblock

theorem smallBall_gaussianQuadraticCenteredLaw_map_div_le_of_robustRankAt
    {n r : ℕ} (f : Fin n → ℝ)
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    {sigma s eps : ℝ} (hsigma : 0 < sigma)
    (hrob : RobustRankAt r s F) (hr : 3 ≤ r) (hs : 0 < s)
    (heps : 0 ≤ eps) (x : ℝ) :
    Erdos88.Esseen.smallBall
        ((gaussianQuadraticCenteredLaw f F).map (fun y ↦ y / sigma)) eps x ≤
      eps / (2 * Real.sqrt (s / (8 * sigma ^ 2))) := by
  obtain ⟨B, hdisj, hblock⟩ :=
    exists_four_normalized_eigenvalue_blocks_of_robustRankAt
      hF hrob hr hs hsigma
  rw [gaussianQuadraticCenteredLaw_map_div_eq_diagonal f hF hsigma.ne']
  exact smallBall_diagonalCenteredLaw_le_of_four_le_spectralBlocks
    (fun i ↦ eigenLinearCoefficient hF f i / sigma)
    (fun i ↦ hF.eigenvalues i / sigma) B (by norm_num)
    (by simpa only [Finset.coe_univ] using hdisj)
    (by positivity) hblock heps x

lemma smallBall_gaussianQuadraticCenteredLaw_map_div_le_two_mul
    {n r : ℕ} (f : Fin n → ℝ)
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    {sigma s eps : ℝ} (hsigma : 0 < sigma)
    (hrob : RobustRankAt r s F) (hr : 3 ≤ r) (hs : 0 < s)
    (heps : 0 ≤ eps) (x : ℝ) :
    Erdos88.Esseen.smallBall
        ((gaussianQuadraticCenteredLaw f F).map (fun y ↦ y / sigma)) eps x ≤
      2 * eps * sigma / Real.sqrt s := by
  have hraw :=
    smallBall_gaussianQuadraticCenteredLaw_map_div_le_of_robustRankAt
      f hF hsigma hrob hr hs heps x
  have hsqrtLower : Real.sqrt s / (4 * sigma) ≤
      Real.sqrt (s / (8 * sigma ^ 2)) := by
    have hfrac : s / (16 * sigma ^ 2) ≤ s / (8 * sigma ^ 2) := by
      apply div_le_div_of_nonneg_left hs.le (by positivity)
      nlinarith [sq_pos_of_pos hsigma]
    calc
      Real.sqrt s / (4 * sigma) = Real.sqrt (s / (16 * sigma ^ 2)) := by
        rw [Real.sqrt_div (by positivity : 0 ≤ s)]
        rw [show Real.sqrt (16 * sigma ^ 2) = 4 * sigma by
          rw [show (16 : ℝ) * sigma ^ 2 = (4 * sigma) ^ 2 by ring,
            Real.sqrt_sq (by positivity)]]
      _ ≤ Real.sqrt (s / (8 * sigma ^ 2)) := Real.sqrt_le_sqrt hfrac
  calc
    Erdos88.Esseen.smallBall
          ((gaussianQuadraticCenteredLaw f F).map (fun y ↦ y / sigma)) eps x ≤
        eps / (2 * Real.sqrt (s / (8 * sigma ^ 2))) := hraw
    _ ≤ eps / (2 * (Real.sqrt s / (4 * sigma))) := by
      apply div_le_div_of_nonneg_left heps (by positivity)
      exact mul_le_mul_of_nonneg_left hsqrtLower (by norm_num)
    _ = 2 * eps * sigma / Real.sqrt s := by
      field_simp [(Real.sqrt_pos.2 hs).ne', hsigma.ne']
      ring


end Erdos88.GaussianQuadratic
