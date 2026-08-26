import ErdosProblems.Erdos906.UniformDisk
import ErdosProblems.Erdos906.Saddle
import ErdosProblems.Erdos906.FockDerivatives
import ErdosProblems.Erdos906.InfinitePiSplit

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Real Set
open scoped ENNReal

namespace CofiniteDerivatives

noncomputable section

/-- The deterministic pointwise potential
`P_n(z) = log (sqrt (n!)) + |z| sqrt n`. -/
def pointwisePotential (n : ℕ) (z : ℂ) : ℝ :=
  Real.log (Real.sqrt (Nat.factorial n : ℝ)) + ‖z‖ * Real.sqrt n

/-- The `m`-th complex saddle monomial in the `n`-th derivative tail. -/
def saddleMonomial (n m : ℕ) (z : ℂ) : ℂ :=
  (Real.sqrt (Nat.factorial (n + m) : ℝ) / (Nat.factorial m : ℝ) : ℝ) * z ^ m

@[simp]
theorem norm_saddleMonomial (n m : ℕ) (z : ℂ) :
    ‖saddleMonomial n m z‖ = saddleCoeff n m ‖z‖ := by
  simp only [saddleMonomial, saddleCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_pow]
  rw [abs_of_nonneg]
  positivity

/-- The factorially weighted tail representing the `n`-th derivative after shifting the
coefficient sequence by `n`. -/
def pointwiseDerivativeSeries (ξ : ℕ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑' m : ℕ, ξ (n + m) * saddleMonomial n m z

/-- The pointwise saddle series is exactly the `n`-th derivative of the Fock function. -/
theorem pointwiseDerivativeSeries_eq_iteratedDeriv_fockFunction
    (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1) (n : ℕ) (z : ℂ) :
    pointwiseDerivativeSeries ξ n z = iteratedDeriv n (fockFunction ξ) z := by
  rw [pointwiseDerivativeSeries, iteratedDeriv_fockFunction_eq_tsum ξ hξ n z]
  apply tsum_congr
  intro m
  simp only [saddleMonomial]
  push_cast
  ring

/-- The saddle coordinate nearest to `|z| sqrt n`. -/
def pointwiseSaddleIndex (n : ℕ) (z : ℂ) : ℕ :=
  ⌊‖z‖ * Real.sqrt n⌋₊

/-- The logarithmic loss in the floor saddle-coefficient estimate. -/
def pointwiseSaddleLoss (n : ℕ) : ℝ :=
  2 + Real.log n / 2

/-- Explicit conditions saying that `n` is large enough for every point in the annulus
`δ ≤ |z| ≤ R` to lie in the floor saddle range. -/
def PointwiseSaddleReady (n : ℕ) (δ R : ℝ) : Prop :=
  1 ≤ δ * Real.sqrt n ∧ R ≤ Real.sqrt n

theorem summable_saddleCoeff (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    Summable (fun m : ℕ ↦ saddleCoeff n m r) := by
  refine (normalizedSaddleSeries_summable n hr).mul_left
    (Real.sqrt (Nat.factorial n : ℝ)) |>.congr ?_
  intro m
  exact (saddleCoeff_eq_sqrt_factorial_mul_normalized n m r).symm

theorem summable_pointwiseDerivativeSeries {ξ : ℕ → ℂ} (hξ : ∀ k, ‖ξ k‖ ≤ 1)
    (n : ℕ) (z : ℂ) :
    Summable (fun m : ℕ ↦ ξ (n + m) * saddleMonomial n m z) := by
  apply Summable.of_norm
  exact (summable_saddleCoeff n (norm_nonneg z)).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun m ↦ by
      rw [norm_mul, norm_saddleMonomial]
      exact mul_le_of_le_one_left (by
        rw [saddleCoeff]
        positivity) (hξ (n + m))

/-- Bounded coefficients make the derivative tail no larger than the deterministic saddle
series at the same radius. -/
theorem norm_pointwiseDerivativeSeries_le_saddleSeries {ξ : ℕ → ℂ}
    (hξ : ∀ k, ‖ξ k‖ ≤ 1) (n : ℕ) (z : ℂ) :
    ‖pointwiseDerivativeSeries ξ n z‖ ≤ saddleSeries n ‖z‖ := by
  calc
    ‖pointwiseDerivativeSeries ξ n z‖ ≤
        ∑' m : ℕ, ‖ξ (n + m) * saddleMonomial n m z‖ := by
      exact norm_tsum_le_tsum_norm
        ((summable_pointwiseDerivativeSeries hξ n z).norm)
    _ ≤ ∑' m : ℕ, saddleCoeff n m ‖z‖ := by
      exact (summable_pointwiseDerivativeSeries hξ n z).norm.tsum_le_tsum
        (fun m ↦ by
          rw [norm_mul, norm_saddleMonomial]
          exact mul_le_of_le_one_left (by
            rw [saddleCoeff]
            positivity) (hξ (n + m)))
        (summable_saddleCoeff n (norm_nonneg z))
    _ = saddleSeries n ‖z‖ := rfl

/-- Any function majorized by `saddleSeries` obeys the compact deterministic logarithmic
upper bound. This is the reusable deterministic half of the pointwise log estimate. -/
theorem log_norm_sub_pointwisePotential_le_of_norm_le_saddleSeries
    (F : ℕ → ℂ → ℂ) (n : ℕ) (z : ℂ) (R : ℝ) (hn : n ≠ 0)
    (hzR : ‖z‖ ≤ R) (hF : ‖F n z‖ ≤ saddleSeries n ‖z‖) :
    Real.log ‖F n z‖ - pointwisePotential n z ≤ (R + R ^ 2) / 2 := by
  have hR : 0 ≤ R := (norm_nonneg z).trans hzR
  by_cases hzero : F n z = 0
  · have hfactorial : (1 : ℝ) ≤ Real.sqrt (Nat.factorial n : ℝ) := by
      rw [← Real.sqrt_one]
      apply Real.sqrt_le_sqrt
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr n.factorial_ne_zero
    have hpotential : 0 ≤ pointwisePotential n z := by
      dsimp only [pointwisePotential]
      exact add_nonneg (Real.log_nonneg hfactorial)
        (mul_nonneg (norm_nonneg z) (Real.sqrt_nonneg _))
    simp only [hzero, norm_zero, Real.log_zero]
    nlinarith [sq_nonneg R]
  · have hlog : Real.log ‖F n z‖ ≤ Real.log (saddleSeries n ‖z‖) :=
      Real.log_le_log (norm_pos_iff.mpr hzero) hF
    have hsaddle := log_saddleSeries_le_on_compact n hn (norm_nonneg z) hzR
    dsimp only [pointwisePotential]
    rw [Real.log_sqrt (by positivity)]
    linarith

/-- Deterministic compact upper bound for the factorially weighted derivative tail. -/
theorem log_norm_pointwiseDerivativeSeries_sub_potential_le {ξ : ℕ → ℂ}
    (hξ : ∀ k, ‖ξ k‖ ≤ 1) (n : ℕ) (z : ℂ) (R : ℝ) (hn : n ≠ 0)
    (hzR : ‖z‖ ≤ R) :
    Real.log ‖pointwiseDerivativeSeries ξ n z‖ - pointwisePotential n z ≤
      (R + R ^ 2) / 2 := by
  exact log_norm_sub_pointwisePotential_le_of_norm_le_saddleSeries
    (fun n z ↦ pointwiseDerivativeSeries ξ n z) n z R hn hzR
    (norm_pointwiseDerivativeSeries_le_saddleSeries hξ n z)

/-- Deterministic compact upper bound for the actual `n`-th Fock derivative. -/
theorem log_norm_iteratedDeriv_fockFunction_sub_potential_le
    (ξ : ℕ → ℂ) (hξ : ∀ k, ‖ξ k‖ ≤ 1)
    (n : ℕ) (z : ℂ) (R : ℝ) (hn : n ≠ 0) (hzR : ‖z‖ ≤ R) :
    Real.log ‖iteratedDeriv n (fockFunction ξ) z‖ - pointwisePotential n z ≤
      (R + R ^ 2) / 2 := by
  rw [← pointwiseDerivativeSeries_eq_iteratedDeriv_fockFunction ξ hξ n z]
  exact log_norm_pointwiseDerivativeSeries_sub_potential_le hξ n z R hn hzR

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `F` has the quadratic small-ball bound supplied by an affine coordinate with coefficient
`a`. This is the interface expected from conditioning on all other random coordinates. -/
def HasQuadraticSmallBall (μ : Measure Ω) (F : Ω → ℂ) (a : ℂ) : Prop :=
  ∀ ε : ℝ, 0 ≤ ε →
    μ {ω | ‖F ω‖ < ε} ≤ ENNReal.ofReal ((ε / ‖a‖) ^ 2)

/-- An affine function of one uniform-disk coordinate has the required quadratic small-ball
bound. -/
theorem uniformDisk_affine_hasQuadraticSmallBall {a : ℂ} (ha : a ≠ 0) (w : ℂ) :
    HasQuadraticSmallBall uniformDisk (fun u ↦ a * u + w) a := by
  intro ε hε
  exact uniformDisk_affine_smallBall ha w hε

/-- Splitting an infinite product at a uniform-disk coordinate promotes the one-coordinate
affine estimate to a quadratic small-ball bound for the full random sum. -/
theorem infinitePi_uniformDisk_affine_hasQuadraticSmallBall
    {ι : Type*}
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    (j : ι) (hμj : μ j = uniformDisk) {a : ℂ} (ha : a ≠ 0)
    (H : ({i // i ≠ j} → ℂ) → ℂ) (hH : Measurable H) :
    HasQuadraticSmallBall (Measure.infinitePi μ)
      (fun ω ↦ a * ω j + H (fun i : {i // i ≠ j} ↦ ω i)) a := by
  intro ε hε
  apply infinitePi_affine_smallBall_of_law μ j uniformDisk hμj a H hH ε
    (ENNReal.ofReal ((ε / ‖a‖) ^ 2))
  intro w
  exact uniformDisk_affine_smallBall ha w hε

/-- A quadratic small-ball estimate at a coefficient whose logarithm reaches the potential up
to `loss` gives an `exp (-2s)` lower tail for the logarithm. The hypothesis is deliberately
abstract so a later infinite-product split can discharge it by conditioning. -/
theorem measure_pointwisePotential_sub_log_norm_gt_le_exp_of_smallBall
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℂ) (a : ℂ)
    (n : ℕ) (z : ℂ) (loss s : ℝ) (ha : a ≠ 0)
    (hscale : pointwisePotential n z - loss ≤ Real.log ‖a‖)
    (hsmall : HasQuadraticSmallBall μ F a) :
    μ {ω | pointwisePotential n z - Real.log ‖F ω‖ > s + loss} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  let ε : ℝ := Real.exp (pointwisePotential n z - (s + loss))
  have hε : 0 ≤ ε := Real.exp_nonneg _
  have hsubset :
      {ω | pointwisePotential n z - Real.log ‖F ω‖ > s + loss} ⊆
        {ω | ‖F ω‖ < ε} := by
    intro ω hω
    dsimp only [Set.mem_ofPred_eq, ε] at hω ⊢
    by_cases hzero : F ω = 0
    · simpa [hzero] using! Real.exp_pos (pointwisePotential n z - (s + loss))
    · rw [← Real.exp_log (norm_pos_iff.mpr hzero)]
      apply Real.exp_lt_exp.mpr
      linarith
  have ha_norm : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hscale_exp :
      Real.exp (pointwisePotential n z - loss) ≤ ‖a‖ := by
    calc
      Real.exp (pointwisePotential n z - loss) ≤ Real.exp (Real.log ‖a‖) :=
        Real.exp_le_exp.mpr hscale
      _ = ‖a‖ := Real.exp_log ha_norm
  have hratio : ε / ‖a‖ ≤ Real.exp (-s) := by
    rw [div_le_iff₀ ha_norm]
    calc
      ε = Real.exp (-s) * Real.exp (pointwisePotential n z - loss) := by
        dsimp only [ε]
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-s) * ‖a‖ := by
        exact mul_le_mul_of_nonneg_left hscale_exp (Real.exp_nonneg _)
  have hratio_nonneg : 0 ≤ ε / ‖a‖ := div_nonneg hε ha_norm.le
  have hsquare : (ε / ‖a‖) ^ 2 ≤ (Real.exp (-s)) ^ 2 := by
    nlinarith [Real.exp_nonneg (-s)]
  calc
    μ {ω | pointwisePotential n z - Real.log ‖F ω‖ > s + loss} ≤
        μ {ω | ‖F ω‖ < ε} := measure_mono hsubset
    _ ≤ ENNReal.ofReal ((ε / ‖a‖) ^ 2) := hsmall ε hε
    _ ≤ ENNReal.ofReal ((Real.exp (-s)) ^ 2) := ENNReal.ofReal_le_ofReal hsquare
    _ = ENNReal.ofReal (Real.exp (-2 * s)) := by
      congr 2
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring

/-- The floor saddle monomial reaches the deterministic potential up to
`2 + log n / 2` whenever `n` is in the eventual saddle range for `z`. -/
theorem pointwisePotential_sub_saddleLoss_le_log_norm_saddleMonomial
    (n : ℕ) (z : ℂ) (hx : 1 ≤ ‖z‖ * Real.sqrt n)
    (hzn : ‖z‖ ≤ Real.sqrt n) :
    pointwisePotential n z - pointwiseSaddleLoss n ≤
      Real.log ‖saddleMonomial n (pointwiseSaddleIndex n z) z‖ := by
  have hcoeff := log_saddleCoeff_floor_lower n (norm_nonneg z) hx hzn
  rw [norm_saddleMonomial]
  dsimp only [pointwisePotential, pointwiseSaddleLoss, pointwiseSaddleIndex]
  rw [Real.log_sqrt (by positivity)]
  linarith

theorem saddleMonomial_pointwiseSaddleIndex_ne_zero
    (n : ℕ) (z : ℂ) (hx : 1 ≤ ‖z‖ * Real.sqrt n) :
    saddleMonomial n (pointwiseSaddleIndex n z) z ≠ 0 := by
  have hz : z ≠ 0 := by
    intro hzero
    subst z
    norm_num at hx
  rw [saddleMonomial]
  exact mul_ne_zero (by
    norm_cast
    exact div_ne_zero (Real.sqrt_ne_zero'.mpr (by positivity)) (by positivity))
    (pow_ne_zero _ hz)

/-- Abstract conditional lower tail at the floor saddle coordinate. A product-coordinate split
only needs to prove `hsmall`, normally by `uniformDisk_affine_smallBall` after fixing the other
coordinates. -/
theorem measure_pointwise_floor_lowerTail_of_smallBall
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℂ)
    (n : ℕ) (z : ℂ) (s : ℝ)
    (hx : 1 ≤ ‖z‖ * Real.sqrt n) (hzn : ‖z‖ ≤ Real.sqrt n)
    (hsmall : HasQuadraticSmallBall μ F
      (saddleMonomial n (pointwiseSaddleIndex n z) z)) :
    μ {ω | pointwisePotential n z - Real.log ‖F ω‖ >
        s + pointwiseSaddleLoss n} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  exact measure_pointwisePotential_sub_log_norm_gt_le_exp_of_smallBall
    μ F (saddleMonomial n (pointwiseSaddleIndex n z) z) n z
    (pointwiseSaddleLoss n) s
    (saddleMonomial_pointwiseSaddleIndex_ne_zero n z hx)
    (pointwisePotential_sub_saddleLoss_le_log_norm_saddleMonomial n z hx hzn)
    hsmall

/-- Concrete one-coordinate version of the floor lower tail for a uniform-disk coordinate and
an arbitrary fixed remainder. -/
theorem uniformDisk_pointwise_floor_lowerTail
    (n : ℕ) (z w : ℂ) (s : ℝ)
    (hx : 1 ≤ ‖z‖ * Real.sqrt n) (hzn : ‖z‖ ≤ Real.sqrt n) :
    uniformDisk {u | pointwisePotential n z -
        Real.log ‖saddleMonomial n (pointwiseSaddleIndex n z) z * u + w‖ >
          s + pointwiseSaddleLoss n} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  apply measure_pointwise_floor_lowerTail_of_smallBall uniformDisk
    (fun u ↦ saddleMonomial n (pointwiseSaddleIndex n z) z * u + w)
    n z s hx hzn
  exact uniformDisk_affine_hasQuadraticSmallBall
    (saddleMonomial_pointwiseSaddleIndex_ne_zero n z hx) w

/-- Full infinite-product floor lower tail after splitting off one uniform-disk coordinate.
The measurable function `H` is the remainder of the random sum. -/
theorem infinitePi_pointwise_floor_lowerTail
    {ι : Type*}
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    (j : ι) (hμj : μ j = uniformDisk)
    (H : ({i // i ≠ j} → ℂ) → ℂ) (hH : Measurable H)
    (n : ℕ) (z : ℂ) (s : ℝ)
    (hx : 1 ≤ ‖z‖ * Real.sqrt n) (hzn : ‖z‖ ≤ Real.sqrt n) :
    Measure.infinitePi μ {ω | pointwisePotential n z -
        Real.log ‖saddleMonomial n (pointwiseSaddleIndex n z) z * ω j +
          H (fun i : {i // i ≠ j} ↦ ω i)‖ >
            s + pointwiseSaddleLoss n} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  apply measure_pointwise_floor_lowerTail_of_smallBall (Measure.infinitePi μ)
    (fun ω ↦ saddleMonomial n (pointwiseSaddleIndex n z) z * ω j +
      H (fun i : {i // i ≠ j} ↦ ω i)) n z s hx hzn
  exact infinitePi_uniformDisk_affine_hasQuadraticSmallBall μ j hμj
    (saddleMonomial_pointwiseSaddleIndex_ne_zero n z hx) H hH

/-- Full-product floor lower tail for a random function supplied together with its affine
saddle-coordinate decomposition. -/
theorem infinitePi_pointwise_floor_lowerTail_of_decomposition
    {ι : Type*}
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    (j : ι) (hμj : μ j = uniformDisk)
    (F : (ι → ℂ) → ℂ) (H : ({i // i ≠ j} → ℂ) → ℂ) (hH : Measurable H)
    (n : ℕ) (z : ℂ) (s : ℝ)
    (hF : ∀ ω, F ω = saddleMonomial n (pointwiseSaddleIndex n z) z * ω j +
      H (fun i : {i // i ≠ j} ↦ ω i))
    (hx : 1 ≤ ‖z‖ * Real.sqrt n) (hzn : ‖z‖ ≤ Real.sqrt n) :
    Measure.infinitePi μ {ω | pointwisePotential n z - Real.log ‖F ω‖ >
        s + pointwiseSaddleLoss n} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  simpa only [hF] using!
    infinitePi_pointwise_floor_lowerTail μ j hμj H hH n z s hx hzn

/-- Abstract floor-coordinate lower tail, uniformly applicable once `n` is ready for the
annulus `δ ≤ |z| ≤ R`. -/
theorem measure_pointwise_annulus_lowerTail_of_smallBall
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℂ)
    (n : ℕ) (z : ℂ) (δ R s : ℝ)
    (hn : PointwiseSaddleReady n δ R) (hzδ : δ ≤ ‖z‖) (hzR : ‖z‖ ≤ R)
    (hsmall : HasQuadraticSmallBall μ F
      (saddleMonomial n (pointwiseSaddleIndex n z) z)) :
    μ {ω | pointwisePotential n z - Real.log ‖F ω‖ >
        s + pointwiseSaddleLoss n} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  apply measure_pointwise_floor_lowerTail_of_smallBall μ F n z s
  · exact hn.1.trans <| mul_le_mul_of_nonneg_right hzδ (Real.sqrt_nonneg _)
  · exact hzR.trans hn.2
  · exact hsmall

/-- Concrete conditional slice bound for every point in a saddle-ready annulus. -/
theorem uniformDisk_pointwise_annulus_lowerTail
    (n : ℕ) (z w : ℂ) (δ R s : ℝ)
    (hn : PointwiseSaddleReady n δ R) (hzδ : δ ≤ ‖z‖) (hzR : ‖z‖ ≤ R) :
    uniformDisk {u | pointwisePotential n z -
        Real.log ‖saddleMonomial n (pointwiseSaddleIndex n z) z * u + w‖ >
          s + pointwiseSaddleLoss n} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  have hx : 1 ≤ ‖z‖ * Real.sqrt n :=
    hn.1.trans <| mul_le_mul_of_nonneg_right hzδ (Real.sqrt_nonneg _)
  exact uniformDisk_pointwise_floor_lowerTail n z w s hx (hzR.trans hn.2)

/-- Full infinite-product lower tail, uniformly applicable on a saddle-ready annulus. -/
theorem infinitePi_pointwise_annulus_lowerTail
    {ι : Type*}
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    (j : ι) (hμj : μ j = uniformDisk)
    (H : ({i // i ≠ j} → ℂ) → ℂ) (hH : Measurable H)
    (n : ℕ) (z : ℂ) (δ R s : ℝ)
    (hn : PointwiseSaddleReady n δ R) (hzδ : δ ≤ ‖z‖) (hzR : ‖z‖ ≤ R) :
    Measure.infinitePi μ {ω | pointwisePotential n z -
        Real.log ‖saddleMonomial n (pointwiseSaddleIndex n z) z * ω j +
          H (fun i : {i // i ≠ j} ↦ ω i)‖ >
            s + pointwiseSaddleLoss n} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  have hx : 1 ≤ ‖z‖ * Real.sqrt n :=
    hn.1.trans <| mul_le_mul_of_nonneg_right hzδ (Real.sqrt_nonneg _)
  exact infinitePi_pointwise_floor_lowerTail μ j hμj H hH n z s hx (hzR.trans hn.2)

@[simp]
theorem saddleMonomial_zero_zero (n : ℕ) :
    saddleMonomial n 0 0 = (Real.sqrt (Nat.factorial n : ℝ) : ℂ) := by
  simp [saddleMonomial]

theorem saddleMonomial_zero_zero_ne_zero (n : ℕ) : saddleMonomial n 0 0 ≠ 0 := by
  rw [saddleMonomial_zero_zero]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))

/-- At `z = 0`, coordinate `m = 0` reaches the potential exactly, so there is no logarithmic
loss. -/
theorem pointwisePotential_zero_eq_log_norm_saddleMonomial_zero (n : ℕ) :
    pointwisePotential n 0 = Real.log ‖saddleMonomial n 0 0‖ := by
  rw [saddleMonomial_zero_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  simp [pointwisePotential]

/-- Abstract lower tail at the origin, using the zeroth coordinate. -/
theorem measure_pointwise_zero_lowerTail_of_smallBall
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℂ)
    (n : ℕ) (s : ℝ)
    (hsmall : HasQuadraticSmallBall μ F (saddleMonomial n 0 0)) :
    μ {ω | pointwisePotential n 0 - Real.log ‖F ω‖ > s} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  simpa only [add_zero] using!
    measure_pointwisePotential_sub_log_norm_gt_le_exp_of_smallBall
      μ F (saddleMonomial n 0 0) n 0 0 s (saddleMonomial_zero_zero_ne_zero n)
      (by rw [sub_zero, pointwisePotential_zero_eq_log_norm_saddleMonomial_zero]) hsmall

/-- Concrete uniform-disk lower tail at `z = 0`, with the coordinate `m = 0`. -/
theorem uniformDisk_pointwise_zero_lowerTail (n : ℕ) (w : ℂ) (s : ℝ) :
    uniformDisk {u | pointwisePotential n 0 -
        Real.log ‖saddleMonomial n 0 0 * u + w‖ > s} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  apply measure_pointwise_zero_lowerTail_of_smallBall uniformDisk
    (fun u ↦ saddleMonomial n 0 0 * u + w) n s
  exact uniformDisk_affine_hasQuadraticSmallBall (saddleMonomial_zero_zero_ne_zero n) w

/-- Full infinite-product lower tail at the origin, using coordinate `m = 0`. -/
theorem infinitePi_pointwise_zero_lowerTail
    {ι : Type*}
    (μ : ι → Measure ℂ) [∀ i, IsProbabilityMeasure (μ i)]
    (j : ι) (hμj : μ j = uniformDisk)
    (H : ({i // i ≠ j} → ℂ) → ℂ) (hH : Measurable H)
    (n : ℕ) (s : ℝ) :
    Measure.infinitePi μ {ω | pointwisePotential n 0 -
        Real.log ‖saddleMonomial n 0 0 * ω j +
          H (fun i : {i // i ≠ j} ↦ ω i)‖ > s} ≤
      ENNReal.ofReal (Real.exp (-2 * s)) := by
  apply measure_pointwise_zero_lowerTail_of_smallBall (Measure.infinitePi μ)
    (fun ω ↦ saddleMonomial n 0 0 * ω j +
      H (fun i : {i // i ≠ j} ↦ ω i)) n s
  exact infinitePi_uniformDisk_affine_hasQuadraticSmallBall μ j hμj
    (saddleMonomial_zero_zero_ne_zero n) H hH

end

end CofiniteDerivatives
