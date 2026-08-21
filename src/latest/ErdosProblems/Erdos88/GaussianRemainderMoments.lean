import ErdosProblems.Erdos88.GaussianLowerInfluential
import ErdosProblems.Erdos88.GaussianHypercontractiveTail

/-!
# Fourth moments of centered diagonal Gaussian remainders

This module supplies the complementary-block input in the influential-coordinate
case of KSSS Theorem 5.2(2).  It proves a constant `15` fourth-moment bound for
arbitrary finite diagonal blocks and feeds it into the scale-covariant form of
KSSS Lemma 5.9.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos88.GaussianQuadratic

private lemma integral_add_pow_four_of_independent_centered
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hXY : IndepFun X Y P)
    (hX : AEStronglyMeasurable X P) (hY : AEStronglyMeasurable Y P)
    (hX4 : Integrable (fun ω ↦ X ω ^ 4) P)
    (hY4 : Integrable (fun ω ↦ Y ω ^ 4) P) {v w : ℝ}
    (hX1 : ∫ ω, X ω ∂P = 0) (hY1 : ∫ ω, Y ω ∂P = 0)
    (hY2 : ∫ ω, Y ω ^ 2 ∂P = v)
    (hY4m : ∫ ω, Y ω ^ 4 ∂P = w) :
    ∫ ω, (X ω + Y ω) ^ 4 ∂P =
      (∫ ω, X ω ^ 4 ∂P) + 6 * v * (∫ ω, X ω ^ 2 ∂P) + w := by
  have h31 : Integrable (fun ω ↦ X ω ^ 3 * Y ω) P := by
    refine Integrable.mono' (hX4.add hY4) (hX.pow 3 |>.mul hY) ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      simp only [Pi.add_apply]
      have hp : 0 ≤ (X ω - Y ω) ^ 2 *
          (2 * X ω ^ 2 + (X ω + Y ω) ^ 2) := by positivity
      have hm : 0 ≤ (X ω + Y ω) ^ 2 *
          (2 * X ω ^ 2 + (X ω - Y ω) ^ 2) := by positivity
      exact abs_le.mpr ⟨by
        nlinarith [hp, hm, sq_nonneg (X ω ^ 2), sq_nonneg (Y ω ^ 2)], by
        nlinarith [hp, hm, sq_nonneg (X ω ^ 2), sq_nonneg (Y ω ^ 2)]⟩
  have h22 : Integrable (fun ω ↦ X ω ^ 2 * Y ω ^ 2) P := by
    refine Integrable.mono' (hX4.add hY4) (hX.pow 2 |>.mul (hY.pow 2)) ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      simp only [Pi.add_apply]
      exact abs_le.mpr ⟨by
        nlinarith [sq_nonneg (X ω ^ 2), sq_nonneg (Y ω ^ 2),
          sq_nonneg (X ω * Y ω)], by
        nlinarith [sq_nonneg (X ω ^ 2 - Y ω ^ 2)]⟩
  have h13 : Integrable (fun ω ↦ X ω * Y ω ^ 3) P := by
    refine Integrable.mono' (hX4.add hY4) (hX.mul (hY.pow 3)) ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      simp only [Pi.add_apply]
      have hp : 0 ≤ (Y ω - X ω) ^ 2 *
          (2 * Y ω ^ 2 + (Y ω + X ω) ^ 2) := by positivity
      have hm : 0 ≤ (Y ω + X ω) ^ 2 *
          (2 * Y ω ^ 2 + (Y ω - X ω) ^ 2) := by positivity
      exact abs_le.mpr ⟨by
        nlinarith [hp, hm, sq_nonneg (X ω ^ 2), sq_nonneg (Y ω ^ 2)], by
        nlinarith [hp, hm, sq_nonneg (X ω ^ 2), sq_nonneg (Y ω ^ 2)]⟩
  have hexpand :
      ∫ ω, (X ω + Y ω) ^ 4 ∂P =
        (∫ ω, X ω ^ 4 ∂P) + 4 * (∫ ω, X ω ^ 3 * Y ω ∂P) +
          6 * (∫ ω, X ω ^ 2 * Y ω ^ 2 ∂P) +
          4 * (∫ ω, X ω * Y ω ^ 3 ∂P) + ∫ ω, Y ω ^ 4 ∂P := by
    have hi1 : (∫ ω, X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) ∂P) =
        (∫ ω, X ω ^ 4 ∂P) + ∫ ω, 4 * (X ω ^ 3 * Y ω) ∂P := by
      simpa only [Pi.add_apply] using integral_add hX4 (h31.const_mul 4)
    have hi2 :
        (∫ ω, (X ω ^ 4 + 4 * (X ω ^ 3 * Y ω)) +
          6 * (X ω ^ 2 * Y ω ^ 2) ∂P) =
        (∫ ω, X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) ∂P) +
          ∫ ω, 6 * (X ω ^ 2 * Y ω ^ 2) ∂P := by
      simpa only [Pi.add_apply] using
        integral_add (hX4.add (h31.const_mul 4)) (h22.const_mul 6)
    have hi3 :
        (∫ ω, ((X ω ^ 4 + 4 * (X ω ^ 3 * Y ω)) +
          6 * (X ω ^ 2 * Y ω ^ 2)) + 4 * (X ω * Y ω ^ 3) ∂P) =
        (∫ ω, (X ω ^ 4 + 4 * (X ω ^ 3 * Y ω)) +
          6 * (X ω ^ 2 * Y ω ^ 2) ∂P) +
          ∫ ω, 4 * (X ω * Y ω ^ 3) ∂P := by
      simpa only [Pi.add_apply] using
        integral_add ((hX4.add (h31.const_mul 4)).add (h22.const_mul 6))
          (h13.const_mul 4)
    have hi4 :
        (∫ ω, (((X ω ^ 4 + 4 * (X ω ^ 3 * Y ω)) +
          6 * (X ω ^ 2 * Y ω ^ 2)) + 4 * (X ω * Y ω ^ 3)) + Y ω ^ 4 ∂P) =
        (∫ ω, ((X ω ^ 4 + 4 * (X ω ^ 3 * Y ω)) +
          6 * (X ω ^ 2 * Y ω ^ 2)) + 4 * (X ω * Y ω ^ 3) ∂P) +
          ∫ ω, Y ω ^ 4 ∂P := by
      simpa only [Pi.add_apply] using
        integral_add (((hX4.add (h31.const_mul 4)).add (h22.const_mul 6)).add
          (h13.const_mul 4)) hY4
    calc
      (∫ ω, (X ω + Y ω) ^ 4 ∂P) =
          ∫ ω, (((X ω ^ 4 + 4 * (X ω ^ 3 * Y ω)) +
            6 * (X ω ^ 2 * Y ω ^ 2)) + 4 * (X ω * Y ω ^ 3)) +
            Y ω ^ 4 ∂P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω ↦ by ring
      _ = _ := by
        rw [hi4, hi3, hi2, hi1, integral_const_mul, integral_const_mul,
          integral_const_mul]
  rw [hexpand]
  have h31z := Erdos1028.expectation_pow_three_mul_eq_zero hXY hX hY hY1
  have h13z : ∫ ω, X ω * Y ω ^ 3 ∂P = 0 := by
    have hind : IndepFun X (fun ω ↦ Y ω ^ 3) P :=
      hXY.comp measurable_id (measurable_id.pow_const 3)
    have hfac := hind.integral_mul_eq_mul_integral hX (hY.pow 3)
    have hfac' : (∫ ω, X ω * Y ω ^ 3 ∂P) =
        (∫ ω, X ω ∂P) * ∫ ω, Y ω ^ 3 ∂P := by
      simpa only [Pi.mul_apply] using hfac
    rw [hfac', hX1, zero_mul]
  have h22f := Erdos1028.expectation_sq_mul_sq_eq_mul_expectation_sq hXY hX hY
  rw [h31z, h13z, h22f, hY2, hY4m]
  ring

/-- Full first, second, and fourth moment package for a centered diagonal
Gaussian remainder.  The fourth-moment constant `15` is stronger than the
constant `81` used in KSSS Lemma 5.9. -/
theorem diagonalPartialSum_moments
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (S : Finset ι) :
    Integrable (fun z : ι → ℝ ↦ diagonalPartialSum a lam S z ^ 4)
        (Measure.pi fun _ : ι ↦ standardGaussian) ∧
      (∫ z : ι → ℝ, diagonalPartialSum a lam S z
        ∂(Measure.pi fun _ : ι ↦ standardGaussian)) = 0 ∧
      (∫ z : ι → ℝ, diagonalPartialSum a lam S z ^ 2
        ∂(Measure.pi fun _ : ι ↦ standardGaussian)) = partialVariance a lam S ∧
      (∫ z : ι → ℝ, diagonalPartialSum a lam S z ^ 4
        ∂(Measure.pi fun _ : ι ↦ standardGaussian)) ≤
          15 * partialVariance a lam S ^ 2 := by
  let P : Measure (ι → ℝ) := Measure.pi fun _ : ι ↦ standardGaussian
  let X : ι → (ι → ℝ) → ℝ := fun i z ↦
    centeredCoordinatePolynomial (a i) (lam i) (z i)
  have hbase : iIndepFun (fun i (z : ι → ℝ) ↦ z i) P := by
    dsimp only [P]
    exact iIndepFun_pi fun _ ↦ aemeasurable_id
  have hindep : iIndepFun X P := by
    exact hbase.comp
      (fun i x ↦ centeredCoordinatePolynomial (a i) (lam i) x)
      (fun i ↦ (continuous_centeredCoordinatePolynomial (a i) (lam i)).measurable)
  have hmeas : ∀ i, Measurable (X i) := fun i ↦ by
    dsimp only [X]
    exact (continuous_centeredCoordinatePolynomial (a i) (lam i)).measurable.comp
      (measurable_pi_apply i)
  have hcoord4 : ∀ i, Integrable (fun z ↦ X i z ^ 4) P := fun i ↦ by
    have h := integrable_comp_eval
      (μ := fun _ : ι ↦ standardGaussian) (i := i)
      (centeredCoordinatePolynomial_fourth_integrable (a i) (lam i))
    simpa only [P, X] using h
  have hcoord1 : ∀ i, ∫ z, X i z ∂P = 0 := fun i ↦ by
    have h := integral_comp_eval
      (μ := fun _ : ι ↦ standardGaussian) (i := i)
      (continuous_centeredCoordinatePolynomial (a i) (lam i)).aestronglyMeasurable
    simpa only [P, X, coordinateFirstMoment_eq_zero] using h
  have hcoord2 : ∀ i, ∫ z, X i z ^ 2 ∂P =
      coordinateVariance (a i) (lam i) := fun i ↦ by
    have h := integral_comp_eval
      (μ := fun _ : ι ↦ standardGaussian) (i := i)
      (show AEStronglyMeasurable
        (fun x : ℝ ↦ centeredCoordinatePolynomial (a i) (lam i) x ^ 2)
          standardGaussian from
        ((continuous_centeredCoordinatePolynomial (a i) (lam i)).pow 2).aestronglyMeasurable)
    rw [show (∫ z, X i z ^ 2 ∂P) =
        ∫ x, centeredCoordinatePolynomial (a i) (lam i) x ^ 2
          ∂standardGaussian by simpa only [P, X] using h]
    exact coordinateSecondMoment_eq (a i) (lam i)
  have hcoord4le : ∀ i, ∫ z, X i z ^ 4 ∂P ≤
      15 * coordinateVariance (a i) (lam i) ^ 2 := fun i ↦ by
    have h := integral_comp_eval
      (μ := fun _ : ι ↦ standardGaussian) (i := i)
      (show AEStronglyMeasurable
        (fun x : ℝ ↦ centeredCoordinatePolynomial (a i) (lam i) x ^ 4)
          standardGaussian from
        ((continuous_centeredCoordinatePolynomial (a i) (lam i)).pow 4).aestronglyMeasurable)
    rw [show (∫ z, X i z ^ 4 ∂P) =
        ∫ x, centeredCoordinatePolynomial (a i) (lam i) x ^ 4
          ∂standardGaussian by simpa only [P, X] using h]
    exact coordinateFourthMoment_le (a i) (lam i)
  have hall : ∀ u : Finset ι,
      Integrable (fun z ↦ (∑ i ∈ u, X i z) ^ 4) P ∧
      (∫ z, ∑ i ∈ u, X i z ∂P) = 0 ∧
      (∫ z, (∑ i ∈ u, X i z) ^ 2 ∂P) =
        ∑ i ∈ u, coordinateVariance (a i) (lam i) ∧
      (∫ z, (∑ i ∈ u, X i z) ^ 4 ∂P) ≤
        15 * (∑ i ∈ u, coordinateVariance (a i) (lam i)) ^ 2 := by
    intro u
    induction u using Finset.induction_on with
    | empty =>
        constructor
        · simpa using (integrable_const (0 : ℝ) : Integrable (fun _ : ι → ℝ ↦ 0) P)
        simp
    | @insert i u hi ihu =>
        let U : (ι → ℝ) → ℝ := fun z ↦ ∑ j ∈ u, X j z
        let Y : (ι → ℝ) → ℝ := X i
        rcases ihu with ⟨hU4, hU1, hU2, hU4le⟩
        have hUmeas : AEStronglyMeasurable U P := by
          exact (Finset.measurable_sum u fun j _ ↦ hmeas j).aestronglyMeasurable
        have hYmeas : AEStronglyMeasurable Y P := (hmeas i).aestronglyMeasurable
        have hUY : IndepFun U Y P := by
          have h := hindep.indepFun_finsetSum_of_notMem hmeas hi
          convert h using 1 <;> funext z <;> simp only [U, Y, Finset.sum_apply]
        have hY4 : Integrable (fun z ↦ Y z ^ 4) P := hcoord4 i
        have hsum4 : Integrable (fun z ↦ (U z + Y z) ^ 4) P :=
          Invariance.integrable_add_pow_four hUmeas hYmeas hU4 hY4
        have hU : Integrable U P := by
          have h := Erdos1028.integrable_pow_of_integrable_pow_four
            hUmeas hU4 1 (by norm_num)
          simpa only [pow_one] using h
        have hY : Integrable Y P := by
          have h := Erdos1028.integrable_pow_of_integrable_pow_four
            hYmeas hY4 1 (by norm_num)
          simpa only [pow_one] using h
        have hsum1 : ∫ z, U z + Y z ∂P = 0 := by
          rw [integral_add hU hY, hU1, hcoord1 i, add_zero]
        have hsum2 : ∫ z, (U z + Y z) ^ 2 ∂P =
            (∑ j ∈ u, coordinateVariance (a j) (lam j)) +
              coordinateVariance (a i) (lam i) := by
          rw [Invariance.integral_add_sq_centered hUY hUmeas hYmeas hU4 hY4
            (hcoord1 i) (hcoord2 i), hU2]
        have hsum4eq : ∫ z, (U z + Y z) ^ 4 ∂P =
            (∫ z, U z ^ 4 ∂P) +
              6 * coordinateVariance (a i) (lam i) *
                (∫ z, U z ^ 2 ∂P) + ∫ z, Y z ^ 4 ∂P := by
          exact integral_add_pow_four_of_independent_centered hUY hUmeas hYmeas
            hU4 hY4 hU1 (hcoord1 i) (hcoord2 i) rfl
        have hsum4le : ∫ z, (U z + Y z) ^ 4 ∂P ≤
            15 * ((∑ j ∈ u, coordinateVariance (a j) (lam j)) +
              coordinateVariance (a i) (lam i)) ^ 2 := by
          rw [hsum4eq, hU2]
          calc
            (∫ z, U z ^ 4 ∂P) +
                6 * coordinateVariance (a i) (lam i) *
                  (∑ j ∈ u, coordinateVariance (a j) (lam j)) +
                ∫ z, Y z ^ 4 ∂P ≤
              15 * (∑ j ∈ u, coordinateVariance (a j) (lam j)) ^ 2 +
                6 * coordinateVariance (a i) (lam i) *
                  (∑ j ∈ u, coordinateVariance (a j) (lam j)) +
                15 * coordinateVariance (a i) (lam i) ^ 2 := by
              gcongr
              exact hcoord4le i
            _ ≤ 15 * ((∑ j ∈ u, coordinateVariance (a j) (lam j)) +
                coordinateVariance (a i) (lam i)) ^ 2 := by
              have hvi := coordinateVariance_nonneg (a i) (lam i)
              have hvu : 0 ≤ ∑ j ∈ u, coordinateVariance (a j) (lam j) :=
                Finset.sum_nonneg fun j _ ↦ coordinateVariance_nonneg (a j) (lam j)
              nlinarith
        constructor
        · simpa only [U, Y, Finset.sum_insert hi, add_comm] using hsum4
        constructor
        · simpa only [U, Y, Finset.sum_insert hi, add_comm] using hsum1
        constructor
        · simpa only [U, Y, Finset.sum_insert hi, add_comm] using hsum2
        · simpa only [U, Y, Finset.sum_insert hi, add_comm] using hsum4le
  simpa only [diagonalPartialSum, partialVariance, X] using hall S

theorem diagonalPartialSum_fourthMoment_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (S : Finset ι) :
    ∫ z : ι → ℝ, diagonalPartialSum a lam S z ^ 4
        ∂(Measure.pi fun _ : ι ↦ standardGaussian) ≤
      15 * partialVariance a lam S ^ 2 :=
  (diagonalPartialSum_moments a lam S).2.2.2

/-- KSSS Lemma 5.9 for any nondegenerate complementary block of a centered
diagonal Gaussian quadratic. -/
theorem measureReal_diagonalPartialSum_oneSided_ge
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (S : Finset ι)
    (hvariance : 0 < partialVariance a lam S) :
    1 / 75 ≤
      (Measure.pi fun _ : ι ↦ standardGaussian).real
        ((diagonalPartialSum a lam S) ⁻¹'
          Set.Icc (-2 * Real.sqrt 15 * Real.sqrt (partialVariance a lam S)) 0) := by
  let P : Measure (ι → ℝ) := Measure.pi fun _ : ι ↦ standardGaussian
  let X : (ι → ℝ) → ℝ := diagonalPartialSum a lam S
  let sigma := Real.sqrt (partialVariance a lam S)
  have hsigma : 0 < sigma := Real.sqrt_pos.2 hvariance
  have hsigmaSq : sigma ^ 2 = partialVariance a lam S := by
    exact Real.sq_sqrt hvariance.le
  rcases diagonalPartialSum_moments a lam S with ⟨hX4, hX1, hX2, hX4le⟩
  have hXmeas : Measurable X := continuous_diagonalPartialSum a lam S |>.measurable
  have hXaemeas : AEStronglyMeasurable X P := hXmeas.aestronglyMeasurable
  have hX : Integrable X P := by
    have h := Erdos1028.integrable_pow_of_integrable_pow_four
      hXaemeas hX4 1 (by norm_num)
    simpa only [pow_one] using h
  have hXsq : Integrable (fun z ↦ X z ^ 2) P :=
    Erdos1028.integrable_pow_of_integrable_pow_four hXaemeas hX4 2 (by norm_num)
  have hfourth : ∫ z, X z ^ 4 ∂P ≤ 15 * sigma ^ 4 := by
    rw [show sigma ^ 4 = partialVariance a lam S ^ 2 by
      rw [show sigma ^ 4 = (sigma ^ 2) ^ 2 by ring, hsigmaSq]]
    exact hX4le
  have hbase := measureReal_oneSided_interval_ge_of_fourthMoment_scaled
    P X (B := 15) (sigma := sigma) (by norm_num) hsigma
      hXmeas hX hXsq hX4 hX1 (by simpa only [hsigmaSq] using hX2) hfourth
  simpa only [P, X, sigma] using (show (1 / (5 * (15 : ℝ))) = 1 / 75 by norm_num) ▸ hbase

end Erdos88.GaussianQuadratic
