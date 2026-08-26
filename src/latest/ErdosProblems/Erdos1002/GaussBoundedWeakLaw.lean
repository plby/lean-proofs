import ErdosProblems.Erdos1002.GaussTransferCorrelation
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Weak law for bounded Lipschitz Gauss observables

The exponential transfer estimate is summed over all pairs of times.  The
finite geometric bookkeeping is proved explicitly, including the diagonal
and both time orderings.
-/

open Filter MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos1002

noncomputable section

/-- The explicit contraction coefficient of the normalized Gauss transfer. -/
def gaussTransferRate : ℝ := 527 / 540

/-- Symmetric natural-number distance, written without an integer coercion. -/
def natSymmetricLag (i j : ℕ) : ℕ := (i - j) + (j - i)

@[simp] theorem natSymmetricLag_self (i : ℕ) : natSymmetricLag i i = 0 := by
  simp [natSymmetricLag]

theorem natSymmetricLag_comm (i j : ℕ) :
    natSymmetricLag i j = natSymmetricLag j i := by
  simp only [natSymmetricLag]
  omega

theorem natSymmetricLag_eq_sub_of_le {i j : ℕ} (hij : i ≤ j) :
    natSymmetricLag i j = j - i := by
  simp [natSymmetricLag, Nat.sub_eq_zero_of_le hij]

/-- The geometric cross-term introduced when time `n` is added. -/
def gaussGeometricCross (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, gaussTransferRate ^ (n - i)

theorem gaussGeometricCross_succ (n : ℕ) :
    gaussGeometricCross (n + 1) =
      gaussTransferRate * gaussGeometricCross n + gaussTransferRate := by
  unfold gaussGeometricCross
  rw [Finset.sum_range_succ]
  have hsum :
      (∑ i ∈ Finset.range n, gaussTransferRate ^ (n + 1 - i)) =
        gaussTransferRate *
          ∑ i ∈ Finset.range n, gaussTransferRate ^ (n - i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    rw [show n + 1 - i = (n - i) + 1 by omega, pow_succ]
    ring
  rw [hsum]
  simp [gaussTransferRate]

theorem gaussGeometricCross_le (n : ℕ) :
    gaussGeometricCross n ≤ (540 / 13 : ℝ) := by
  induction n with
  | zero => norm_num [gaussGeometricCross]
  | succ n ih =>
      rw [gaussGeometricCross_succ]
      calc
        gaussTransferRate * gaussGeometricCross n + gaussTransferRate ≤
            gaussTransferRate * (540 / 13 : ℝ) + gaussTransferRate := by
          have hr0 : 0 ≤ gaussTransferRate := by norm_num [gaussTransferRate]
          gcongr
        _ ≤ (540 / 13 : ℝ) := by norm_num [gaussTransferRate]

/-- Total symmetric geometric weight of all ordered pairs below `n`. -/
def gaussGeometricDoubleSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
    gaussTransferRate ^ natSymmetricLag i j

theorem gaussGeometricDoubleSum_succ (n : ℕ) :
    gaussGeometricDoubleSum (n + 1) =
      gaussGeometricDoubleSum n + 2 * gaussGeometricCross n + 1 := by
  unfold gaussGeometricDoubleSum
  rw [Finset.sum_range_succ]
  simp_rw [Finset.sum_range_succ]
  have hright :
      (∑ i ∈ Finset.range n,
          gaussTransferRate ^ natSymmetricLag i n) =
        gaussGeometricCross n := by
    unfold gaussGeometricCross
    apply Finset.sum_congr rfl
    intro i hi
    rw [natSymmetricLag_eq_sub_of_le (Finset.mem_range.mp hi).le]
  have hleft :
      (∑ j ∈ Finset.range n,
          gaussTransferRate ^ natSymmetricLag n j) =
        gaussGeometricCross n := by
    rw [show (∑ j ∈ Finset.range n,
        gaussTransferRate ^ natSymmetricLag n j) =
        ∑ j ∈ Finset.range n,
          gaussTransferRate ^ natSymmetricLag j n by
      apply Finset.sum_congr rfl
      intro j hj
      rw [natSymmetricLag_comm]]
    exact hright
  rw [Finset.sum_add_distrib, hright, hleft]
  simp
  ring

theorem gaussGeometricDoubleSum_le (n : ℕ) :
    gaussGeometricDoubleSum n ≤ n * (1093 / 13 : ℝ) := by
  induction n with
  | zero => norm_num [gaussGeometricDoubleSum]
  | succ n ih =>
      rw [gaussGeometricDoubleSum_succ]
      have hcross := gaussGeometricCross_le n
      calc
        gaussGeometricDoubleSum n + 2 * gaussGeometricCross n + 1 ≤
            (n : ℝ) * (1093 / 13 : ℝ) +
              2 * (540 / 13 : ℝ) + 1 := by linarith
        _ = ((n + 1 : ℕ) : ℝ) * (1093 / 13 : ℝ) := by
          push_cast
          ring

/-! ## Covariance summation -/

theorem memLp_two_comp_gaussOrbit_of_unit_bounds
    {A : ℝ} {f : ℝ → ℝ} (hfM : Measurable f)
    (hf0 : GaussUnitNonnegative f) (hfA : GaussUnitUpperBound A f)
    (i : ℕ) :
    MemLp (fun x => f (gaussOrbit i x)) 2 gaussMeasure := by
  apply MemLp.of_bound
    (hfM.comp (measurable_gaussOrbit i)).aestronglyMeasurable A
  have horbit : ∀ᵐ x ∂gaussMeasure,
      gaussOrbit i x ∈ Icc (0 : ℝ) 1 := by
    cases i with
    | zero =>
        filter_upwards [gaussMeasure_unit_ae] with x hx
        simpa [gaussOrbit] using! And.intro hx.1.le hx.2
    | succ i =>
        filter_upwards with x
        have hx := gaussOrbit_succ_mem_Ico i x
        exact ⟨hx.1, hx.2.le⟩
  filter_upwards [horbit] with x hx
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (hf0 hx)]
  exact hfA hx

theorem abs_covariance_gaussOrbits_le
    {A K : ℝ} {f : ℝ → ℝ} (hK : 0 ≤ K)
    (hfM : Measurable f)
    (hf0 : GaussUnitNonnegative f) (hfA : GaussUnitUpperBound A f)
    (hfLip : GaussUnitLipschitzBound K f)
    (i j : ℕ) :
    |cov[(fun x => f (gaussOrbit i x)),
        (fun x => f (gaussOrbit j x)); gaussMeasure]| ≤
      gaussTransferRate ^ natSymmetricLag i j * K * A := by
  have hi := memLp_two_comp_gaussOrbit_of_unit_bounds hfM hf0 hfA i
  have hj := memLp_two_comp_gaussOrbit_of_unit_bounds hfM hf0 hfA j
  rw [covariance_eq_sub hi hj]
  simp only [Pi.mul_apply]
  rw [integral_comp_gaussOrbit f hfM i,
    integral_comp_gaussOrbit f hfM j]
  rcases le_total i j with hij | hji
  · simpa only [gaussTransferRate, pow_two,
      natSymmetricLag_eq_sub_of_le hij] using!
        abs_integral_mul_two_gaussOrbits_sub_sq_integral_le
          hK hfM hf0 hfA hfLip hij
  · have hbound :=
        abs_integral_mul_two_gaussOrbits_sub_sq_integral_le
          hK hfM hf0 hfA hfLip hji
      (i := j) (j := i)
    rw [show (∫ x, f (gaussOrbit i x) * f (gaussOrbit j x)
        ∂gaussMeasure) =
        ∫ x, f (gaussOrbit j x) * f (gaussOrbit i x)
          ∂gaussMeasure by
      apply integral_congr_ae
      filter_upwards with x
      ring]
    have hlag : natSymmetricLag i j = i - j := by
      rw [natSymmetricLag_comm]
      exact natSymmetricLag_eq_sub_of_le hji
    simpa only [gaussTransferRate, pow_two, hlag] using! hbound

/-- Variance of the first `n` iterates is `O(n)`, with every ordered pair
and both time directions included. -/
theorem variance_sum_gaussOrbits_le
    {A K : ℝ} {f : ℝ → ℝ} (hK : 0 ≤ K)
    (hfM : Measurable f)
    (hf0 : GaussUnitNonnegative f) (hfA : GaussUnitUpperBound A f)
    (hfLip : GaussUnitLipschitzBound K f)
    (n : ℕ) :
    Var[(fun x => ∑ i ∈ Finset.range n, f (gaussOrbit i x));
        gaussMeasure] ≤
      (n : ℝ) * (1093 / 13 : ℝ) * K * A := by
  have hA0 : 0 ≤ A := by
    have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    exact (hf0 hzero).trans (hfA hzero)
  have hmem : ∀ i ∈ Finset.range n,
      MemLp (fun x => f (gaussOrbit i x)) 2 gaussMeasure := by
    intro i hi
    exact memLp_two_comp_gaussOrbit_of_unit_bounds hfM hf0 hfA i
  rw [variance_fun_sum' hmem]
  calc
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        cov[(fun x => f (gaussOrbit i x)),
          (fun x => f (gaussOrbit j x)); gaussMeasure]) ≤
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          |cov[(fun x => f (gaussOrbit i x)),
            (fun x => f (gaussOrbit j x)); gaussMeasure]| := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact le_abs_self _
    _ ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        gaussTransferRate ^ natSymmetricLag i j * K * A := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact abs_covariance_gaussOrbits_le hK hfM hf0 hfA hfLip i j
    _ = gaussGeometricDoubleSum n * K * A := by
      unfold gaussGeometricDoubleSum
      simp_rw [Finset.sum_mul]
    _ ≤ ((n : ℝ) * (1093 / 13 : ℝ)) * K * A := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (gaussGeometricDoubleSum_le n) hK)
        hA0
    _ = (n : ℝ) * (1093 / 13 : ℝ) * K * A := by ring

/-! ## Averages and the bounded weak law -/

/-- Arithmetic average of the first `n` iterates of a Gauss observable. -/
def gaussBirkhoffAverage (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, f (gaussOrbit i x)) / (n : ℝ)

theorem memLp_two_gaussBirkhoffAverage
    {A : ℝ} {f : ℝ → ℝ} (hfM : Measurable f)
    (hf0 : GaussUnitNonnegative f) (hfA : GaussUnitUpperBound A f)
    (n : ℕ) :
    MemLp (gaussBirkhoffAverage f n) 2 gaussMeasure := by
  have hsum : MemLp
      (fun x => ∑ i ∈ Finset.range n, f (gaussOrbit i x))
      2 gaussMeasure := by
    have hraw := memLp_finset_sum' (Finset.range n) fun i hi =>
      memLp_two_comp_gaussOrbit_of_unit_bounds hfM hf0 hfA i
    convert! hraw using 1
    funext x
    rw [Finset.sum_apply]
  have hscaled := hsum.mul_const ((n : ℝ)⁻¹)
  simpa only [gaussBirkhoffAverage, div_eq_mul_inv] using! hscaled

theorem integral_gaussBirkhoffAverage
    {A : ℝ} {f : ℝ → ℝ} (hfM : Measurable f)
    (hf0 : GaussUnitNonnegative f) (hfA : GaussUnitUpperBound A f)
    {n : ℕ} (hn : 0 < n) :
    (∫ x, gaussBirkhoffAverage f n x ∂gaussMeasure) =
      ∫ x, f x ∂gaussMeasure := by
  have hint (i : ℕ) :
      Integrable (fun x => f (gaussOrbit i x)) gaussMeasure :=
    (memLp_two_comp_gaussOrbit_of_unit_bounds hfM hf0 hfA i).integrable
      (by norm_num)
  unfold gaussBirkhoffAverage
  rw [integral_div]
  rw [integral_finset_sum _ fun i hi => hint i]
  simp_rw [integral_comp_gaussOrbit f hfM]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp [hnR]

theorem variance_gaussBirkhoffAverage_le
    {A K : ℝ} {f : ℝ → ℝ} (hK : 0 ≤ K)
    (hfM : Measurable f)
    (hf0 : GaussUnitNonnegative f) (hfA : GaussUnitUpperBound A f)
    (hfLip : GaussUnitLipschitzBound K f)
    {n : ℕ} (hn : 0 < n) :
    Var[gaussBirkhoffAverage f n; gaussMeasure] ≤
      ((1093 / 13 : ℝ) * K * A) / (n : ℝ) := by
  let S : ℝ → ℝ := fun x =>
    ∑ i ∈ Finset.range n, f (gaussOrbit i x)
  have hvar := variance_sum_gaussOrbits_le
    hK hfM hf0 hfA hfLip n
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have havg : gaussBirkhoffAverage f n = fun x => (n : ℝ)⁻¹ * S x := by
    funext x
    simp only [gaussBirkhoffAverage, S, div_eq_inv_mul]
  rw [havg, variance_const_mul]
  calc
    (n : ℝ)⁻¹ ^ 2 * Var[S; gaussMeasure] ≤
        (n : ℝ)⁻¹ ^ 2 *
          ((n : ℝ) * (1093 / 13 : ℝ) * K * A) :=
      mul_le_mul_of_nonneg_left hvar (sq_nonneg _)
    _ = ((1093 / 13 : ℝ) * K * A) / (n : ℝ) := by
      field_simp [hnR]

/-- Weak law of large numbers for every bounded nonnegative Lipschitz
observable of the Gauss map. -/
theorem tendstoInMeasure_gaussBirkhoffAverage
    {A K : ℝ} {f : ℝ → ℝ} (hK : 0 ≤ K)
    (hfM : Measurable f)
    (hf0 : GaussUnitNonnegative f) (hfA : GaussUnitUpperBound A f)
    (hfLip : GaussUnitLipschitzBound K f) :
    TendstoInMeasure gaussMeasure
      (fun n => gaussBirkhoffAverage f n) atTop
      (fun _ => ∫ x, f x ∂gaussMeasure) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro epsilon hepsilon
  let E : ℕ → Set ℝ := fun n =>
    {x | epsilon ≤ dist (gaussBirkhoffAverage f n x)
      (∫ y, f y ∂gaussMeasure)}
  let upper : ℕ → ℝ := fun n =>
    (((1093 / 13 : ℝ) * K * A) / epsilon ^ 2) / (n : ℝ)
  have hupper : ∀ᶠ n : ℕ in atTop,
      gaussMeasure.real (E n) ≤ upper n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < n := by omega
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
    have hmem := memLp_two_gaussBirkhoffAverage hfM hf0 hfA n
    have hmean := integral_gaussBirkhoffAverage hfM hf0 hfA hnpos
    have hcheb := meas_ge_le_variance_div_sq hmem hepsilon
    have hset : E n =
        {x | epsilon ≤
          |gaussBirkhoffAverage f n x -
            ∫ y, gaussBirkhoffAverage f n y ∂gaussMeasure|} := by
      ext x
      simp only [E, mem_setOf_eq, Real.dist_eq, hmean]
    have hreal : gaussMeasure.real (E n) ≤
        Var[gaussBirkhoffAverage f n; gaussMeasure] / epsilon ^ 2 := by
      rw [hset, measureReal_def]
      calc
        (gaussMeasure
            {x | epsilon ≤
              |gaussBirkhoffAverage f n x -
                ∫ y, gaussBirkhoffAverage f n y ∂gaussMeasure|}).toReal ≤
            (ENNReal.ofReal
              (Var[gaussBirkhoffAverage f n; gaussMeasure] /
                epsilon ^ 2)).toReal := by
          exact ENNReal.toReal_mono (by finiteness) hcheb
        _ = Var[gaussBirkhoffAverage f n; gaussMeasure] /
              epsilon ^ 2 := by
          rw [ENNReal.toReal_ofReal]
          exact div_nonneg (variance_nonneg _ _) (sq_nonneg _)
    calc
      gaussMeasure.real (E n) ≤
          Var[gaussBirkhoffAverage f n; gaussMeasure] /
            epsilon ^ 2 := hreal
      _ ≤ (((1093 / 13 : ℝ) * K * A) / (n : ℝ)) /
            epsilon ^ 2 := by
        exact div_le_div_of_nonneg_right
          (variance_gaussBirkhoffAverage_le
            hK hfM hf0 hfA hfLip hnpos)
          (sq_nonneg epsilon)
      _ = upper n := by
        dsimp only [upper]
        field_simp [hnR, hepsilon.ne']
  have hupperZero : Tendsto upper atTop (𝓝 0) := by
    exact tendsto_const_div_atTop_nhds_zero_nat
      (((1093 / 13 : ℝ) * K * A) / epsilon ^ 2)
  exact squeeze_zero'
    (Eventually.of_forall fun n => measureReal_nonneg)
    hupper hupperZero

end

end Erdos1002
