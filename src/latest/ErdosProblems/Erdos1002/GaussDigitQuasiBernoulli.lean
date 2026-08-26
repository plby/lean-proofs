import ErdosProblems.Erdos1002.GaussFactorialTupleReplacement
import Mathlib.MeasureTheory.Function.JacobianOneDim

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Uniform distortion for one Gauss digit

This file begins the unconditional proof of the short-gap relative-mixing
input used by the factorial-moment argument.  The elementary kernel below is
the Radon--Nikodym derivative, with respect to Gauss measure, of one inverse
branch of the Gauss map.  Its oscillation on the complete tail interval is
bounded by an absolute constant, uniformly in the digit.

The statements in this file are deliberately quantitative.  They do not use
an abstract mixing hypothesis and they do not claim exponential decay; the
latter requires the separate Gauss--Kuzmin contraction theorem.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace Erdos1002

noncomputable section

/-- Conditional tail-density ratio attached to the first digit `q`.  The
Gauss density and the Jacobian of `y \mapsto 1/(q+y)` simplify to this
rational function. -/
def gaussBranchRatio (q : ℕ) (y : ℝ) : ℝ :=
  (1 + y) / (((q : ℝ) + y) * ((q : ℝ) + y + 1))

theorem measurable_gaussBranchRatio (q : ℕ) :
    Measurable (gaussBranchRatio q) := by
  unfold gaussBranchRatio
  fun_prop

theorem measurable_ofReal_gaussBranchRatio (q : ℕ) :
    Measurable fun y => ENNReal.ofReal (gaussBranchRatio q y) :=
  (measurable_gaussBranchRatio q).ennreal_ofReal

theorem gaussBranchRatio_pos {q : ℕ} (hq : 0 < q)
    {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    0 < gaussBranchRatio q y := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hnum : 0 < 1 + y := by linarith [hy.1]
  have hden₁ : 0 < (q : ℝ) + y := by linarith [hy.1]
  have hden₂ : 0 < (q : ℝ) + y + 1 := by linarith
  unfold gaussBranchRatio
  exact div_pos hnum (mul_pos hden₁ hden₂)

/-- Crude lower envelope, chosen to keep all constants completely explicit. -/
theorem one_div_digit_succ_mul_succ_le_gaussBranchRatio
    {q : ℕ} (hq : 0 < q) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    1 / (((q : ℝ) + 1) * ((q : ℝ) + 2)) ≤ gaussBranchRatio q y := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : 0 < (q : ℝ) + 1 := by positivity
  have hq2 : 0 < (q : ℝ) + 2 := by positivity
  have hqy : 0 < (q : ℝ) + y := by linarith [hy.1]
  have hqy1 : 0 < (q : ℝ) + y + 1 := by linarith
  have hqy_sq : 0 ≤ (q : ℝ) ^ 2 * y := mul_nonneg (sq_nonneg _) hy.1
  have hqy_mul : 0 ≤ (q : ℝ) * y := mul_nonneg hqR.le hy.1
  have hyone : 0 ≤ y * (1 - y) := mul_nonneg hy.1 (by linarith [hy.2])
  unfold gaussBranchRatio
  rw [div_le_div_iff₀ (mul_pos hq1 hq2) (mul_pos hqy hqy1)]
  nlinarith

/-- Matching upper envelope for the same branch kernel. -/
theorem gaussBranchRatio_le_two_div_digit_mul_succ
    {q : ℕ} (hq : 0 < q) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    gaussBranchRatio q y ≤ 2 / ((q : ℝ) * ((q : ℝ) + 1)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : 0 < (q : ℝ) + 1 := by positivity
  have hqy : 0 < (q : ℝ) + y := by linarith [hy.1]
  have hqy1 : 0 < (q : ℝ) + y + 1 := by linarith
  have hq_sq_one : 0 ≤ (q : ℝ) ^ 2 * (1 - y) :=
    mul_nonneg (sq_nonneg _) (by linarith [hy.2])
  have hqy_mul : 0 ≤ (q : ℝ) * y := mul_nonneg hqR.le hy.1
  have hy_sq : 0 ≤ y ^ 2 := sq_nonneg y
  unfold gaussBranchRatio
  rw [div_le_div_iff₀ (mul_pos hqy hqy1) (mul_pos hqR hq1)]
  nlinarith

theorem two_div_digit_mul_succ_le_six_div_succ_mul_succ
    {q : ℕ} (hq : 0 < q) :
    2 / ((q : ℝ) * ((q : ℝ) + 1)) ≤
      6 * (1 / (((q : ℝ) + 1) * ((q : ℝ) + 2))) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : 0 < (q : ℝ) + 1 := by positivity
  have hq2 : 0 < (q : ℝ) + 2 := by positivity
  have h : 2 / ((q : ℝ) * ((q : ℝ) + 1)) ≤
      6 / (((q : ℝ) + 1) * ((q : ℝ) + 2)) := by
    rw [div_le_div_iff₀ (mul_pos hqR hq1) (mul_pos hq1 hq2)]
    nlinarith [mul_nonneg (by linarith : 0 ≤ (q : ℝ) + 1)
      (by linarith : 0 ≤ 2 * (q : ℝ) - 2)]
  simpa only [div_eq_mul_inv, one_mul] using! h

/-- Uniform bounded distortion of a single inverse branch.  Six is not the
optimal constant, but it is elementary, uniform, and more than sufficient
for the short-gap factorial estimates. -/
theorem gaussBranchRatio_le_six_mul
    {q : ℕ} (hq : 0 < q) {y z : ℝ}
    (hy : y ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    gaussBranchRatio q y ≤ 6 * gaussBranchRatio q z := by
  calc
    gaussBranchRatio q y ≤
        2 / ((q : ℝ) * ((q : ℝ) + 1)) :=
      gaussBranchRatio_le_two_div_digit_mul_succ hq hy
    _ ≤ 6 * (1 / (((q : ℝ) + 1) * ((q : ℝ) + 2))) :=
      two_div_digit_mul_succ_le_six_div_succ_mul_succ hq
    _ ≤ 6 * gaussBranchRatio q z := by
      gcongr
      exact one_div_digit_succ_mul_succ_le_gaussBranchRatio hq hz

/-- Telescoping form of the branch probability kernel. -/
theorem gaussBranchRatio_succ_eq_telescoping
    (n : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    gaussBranchRatio (n + 1) y =
      (1 + y) *
        (1 / ((n : ℝ) + 1 + y) - 1 / ((n : ℝ) + 2 + y)) := by
  have h₁ : (n : ℝ) + 1 + y ≠ 0 := by positivity
  have h₂ : (n : ℝ) + 2 + y ≠ 0 := by positivity
  unfold gaussBranchRatio
  norm_num only [Nat.cast_add, Nat.cast_one]
  field_simp
  ring

/-- The inverse-branch ratios form a probability distribution for every
tail state in the closed unit interval.  This is the Markov normalization
underlying the transfer-operator route to true exponential mixing. -/
theorem hasSum_gaussBranchRatio (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ => gaussBranchRatio (n + 1) y) 1 := by
  have hbase : HasSum
      (fun n : ℕ =>
        1 / ((n : ℝ) + 1 + y) - 1 / ((n : ℝ) + 2 + y))
      (1 / (1 + y)) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg]
    · have htail : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1 + y))
          atTop (nhds 0) := by
        have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1 + y)
            atTop atTop := by
          simpa only [add_assoc] using!
            (tendsto_atTop_add_const_right _ (1 + y)
              tendsto_natCast_atTop_atTop)
        simpa only [one_div] using! tendsto_inv_atTop_zero.comp hden
      have htel :
          (fun N : ℕ => ∑ n ∈ Finset.range N,
            (1 / ((n : ℝ) + 1 + y) -
              1 / ((n : ℝ) + 2 + y))) =
            fun N : ℕ => 1 / (1 + y) - 1 / ((N : ℝ) + 1 + y) := by
        funext N
        calc
          (∑ n ∈ Finset.range N,
              (1 / ((n : ℝ) + 1 + y) -
                1 / ((n : ℝ) + 2 + y))) =
              ∑ n ∈ Finset.range N,
                (1 / ((n : ℝ) + 1 + y) -
                  1 / (((n + 1 : ℕ) : ℝ) + 1 + y)) := by
            apply Finset.sum_congr rfl
            intro n _hn
            congr 2
            norm_num [Nat.cast_add]
            ring
          _ = 1 / (((0 : ℕ) : ℝ) + 1 + y) -
              1 / ((N : ℝ) + 1 + y) :=
            Finset.sum_range_sub'
              (fun n : ℕ => 1 / ((n : ℝ) + 1 + y)) N
          _ = 1 / (1 + y) - 1 / ((N : ℝ) + 1 + y) := by norm_num
      rw [htel]
      simpa only [sub_zero] using!
        (tendsto_const_nhds.sub htail :
          Tendsto (fun N : ℕ =>
            1 / (1 + y) - 1 / ((N : ℝ) + 1 + y))
            atTop (nhds (1 / (1 + y) - 0)))
    · intro n
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h₁ : 0 < (n : ℝ) + 1 + y := by linarith [hy.1]
      have hle : (n : ℝ) + 1 + y ≤ (n : ℝ) + 2 + y := by linarith
      exact sub_nonneg.mpr (one_div_le_one_div_of_le h₁ hle)
  have hscaled := hbase.mul_left (1 + y)
  convert! hscaled using 1
  · funext n
    exact gaussBranchRatio_succ_eq_telescoping n hy.1
  · have hy1 : 1 + y ≠ 0 := by linarith [hy.1]
    field_simp

/-- Perron--Frobenius operator written with the normalized Gauss branch
kernel.  No convergence claim is made here for an arbitrary unbounded input;
the definition uses Lean's total `tsum`. -/
def gaussTransfer (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∑' n : ℕ,
    gaussBranchRatio (n + 1) y * f (gaussInverseBranch (n + 1) y)

/-- The explicit branch normalization says exactly that the transfer
operator preserves constants on the state interval. -/
theorem gaussTransfer_one {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    gaussTransfer (fun _ => 1) y = 1 := by
  unfold gaussTransfer
  simpa only [mul_one] using! (hasSum_gaussBranchRatio y hy).tsum_eq

/-! ## Exact one-branch change of variables -/

/-- The inverse-branch density with respect to Lebesgue measure. -/
def gaussBranchDensityReal (q : ℕ) (y : ℝ) : ℝ :=
  1 / (Real.log 2 * ((q : ℝ) + y) * ((q : ℝ) + y + 1))

theorem gaussBranchDensityReal_eq_ratio_mul_gaussDensityReal
    {q : ℕ} (hq : 0 < q) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    gaussBranchDensityReal q y =
      gaussBranchRatio q y * gaussDensityReal y := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hqy : (q : ℝ) + y ≠ 0 := by
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    linarith [hy.1]
  have hqy1 : (q : ℝ) + y + 1 ≠ 0 := by linarith [hy.1]
  have hy1 : 1 + y ≠ 0 := by linarith [hy.1]
  unfold gaussBranchDensityReal gaussBranchRatio gaussDensityReal
  field_simp

theorem gaussBranchDensityReal_pos
    {q : ℕ} (hq : 0 < q) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    0 < gaussBranchDensityReal q y := by
  rw [gaussBranchDensityReal_eq_ratio_mul_gaussDensityReal hq hy]
  exact mul_pos (gaussBranchRatio_pos hq hy)
    (by
      unfold gaussDensityReal
      have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
      exact one_div_pos.mpr (mul_pos hlog (by linarith [hy.1])))

theorem hasDerivAt_gaussInverseBranch
    {q : ℕ} {y : ℝ} (hden : (q : ℝ) + y ≠ 0) :
    HasDerivAt (gaussInverseBranch q)
      (-1 / (((q : ℝ) + y) ^ 2)) y := by
  unfold gaussInverseBranch
  convert! (hasDerivAt_const y (1 : ℝ)).div
    ((hasDerivAt_const y (q : ℝ)).add (hasDerivAt_id y)) hden using 1
  all_goals
    simp only [Pi.add_apply, id_eq]
    field_simp [hden]
    ring

theorem antitoneOn_gaussInverseBranch_of_subset_unit
    {q : ℕ} (hq : 0 < q) {s : Set ℝ} (hs : s ⊆ Icc (0 : ℝ) 1) :
    AntitoneOn (gaussInverseBranch q) s :=
  (strictAntiOn_gaussInverseBranch q hq).antitoneOn.mono hs

theorem inverseBranchJacobian_mul_gaussDensityReal
    {q : ℕ} (hq : 0 < q) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    1 / (((q : ℝ) + y) ^ 2) *
        gaussDensityReal (gaussInverseBranch q y) =
      gaussBranchDensityReal q y := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqy : (q : ℝ) + y ≠ 0 := by linarith [hy.1]
  have hqy1 : (q : ℝ) + y + 1 ≠ 0 := by linarith [hy.1]
  unfold gaussDensityReal gaussInverseBranch gaussBranchDensityReal
  field_simp

theorem gaussInverseBranch_image_subset_unit
    {q : ℕ} (hq : 0 < q) {s : Set ℝ} (hs : s ⊆ Icc (0 : ℝ) 1) :
    gaussInverseBranch q '' s ⊆ Ioc (0 : ℝ) 1 := by
  rintro _ ⟨y, hy, rfl⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hden : 0 < (q : ℝ) + y := by linarith [(hs hy).1]
  unfold gaussInverseBranch
  constructor
  · exact one_div_pos.mpr hden
  · exact (div_le_one hden).2 (by linarith [(hs hy).1])

theorem measurableSet_gaussInverseBranch_image
    {q : ℕ} (hq : 0 < q) {s : Set ℝ} (hsM : MeasurableSet s)
    (hs : s ⊆ Icc (0 : ℝ) 1) :
    MeasurableSet (gaussInverseBranch q '' s) :=
  hsM.image_of_antitoneOn
    (antitoneOn_gaussInverseBranch_of_subset_unit hq hs)

/-- Exact change-of-variables formula for one positive Gauss branch, valid
for an arbitrary measurable tail event. -/
theorem gaussMeasure_gaussInverseBranch_image
    {q : ℕ} (hq : 0 < q) {s : Set ℝ} (hsM : MeasurableSet s)
    (hs : s ⊆ Icc (0 : ℝ) 1) :
    gaussMeasure (gaussInverseBranch q '' s) =
      ∫⁻ y in s, ENNReal.ofReal (gaussBranchDensityReal q y) ∂volume := by
  have himageM := measurableSet_gaussInverseBranch_image hq hsM hs
  have himage := gaussInverseBranch_image_subset_unit hq hs
  rw [gaussMeasure_eq_volume_withDensity,
    MeasureTheory.withDensity_apply _ himageM]
  calc
    (∫⁻ x in gaussInverseBranch q '' s, gaussDensity x ∂volume) =
        ∫⁻ x in gaussInverseBranch q '' s,
          ENNReal.ofReal (gaussDensityReal x) ∂volume := by
      apply setLIntegral_congr_fun himageM
      intro x hx
      exact gaussDensity_eq_ofReal_on_unit (himage hx)
    _ = ∫⁻ y in s,
        ENNReal.ofReal (1 / (((q : ℝ) + y) ^ 2)) *
          ENNReal.ofReal (gaussDensityReal (gaussInverseBranch q y))
          ∂volume := by
      have hchange :=
        lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn
          (f := gaussInverseBranch q)
          (f' := fun y : ℝ => -1 / (((q : ℝ) + y) ^ 2)) hsM
          (fun y hy => by
            have hqR : (0 : ℝ) < q := by exact_mod_cast hq
            exact (hasDerivAt_gaussInverseBranch
              (q := q) (y := y) (by linarith [(hs hy).1])).hasDerivWithinAt)
          (antitoneOn_gaussInverseBranch_of_subset_unit hq hs)
          (fun x => ENNReal.ofReal (gaussDensityReal x))
      simpa only [neg_div, neg_neg] using! hchange
    _ = ∫⁻ y in s, ENNReal.ofReal (gaussBranchDensityReal q y) ∂volume := by
      apply setLIntegral_congr_fun hsM
      intro y hy
      have hycc : y ∈ Icc (0 : ℝ) 1 := hs hy
      change ENNReal.ofReal (1 / (((q : ℝ) + y) ^ 2)) *
        ENNReal.ofReal (gaussDensityReal (gaussInverseBranch q y)) =
          ENNReal.ofReal (gaussBranchDensityReal q y)
      rw [← ENNReal.ofReal_mul (by positivity :
        0 ≤ 1 / (((q : ℝ) + y) ^ 2))]
      congr 1
      exact inverseBranchJacobian_mul_gaussDensityReal hq hycc

theorem gaussMeasure_Ico_unit :
    gaussMeasure (Ico (0 : ℝ) 1) = 1 := by
  have h0 : ∀ᵐ x ∂gaussMeasure, x ∉ ({0} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp (gaussMeasure_singleton 0)
  have h1 : ∀ᵐ x ∂gaussMeasure, x ∉ ({1} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp (gaussMeasure_singleton 1)
  calc
    gaussMeasure (Ico (0 : ℝ) 1) = gaussMeasure (Ioc (0 : ℝ) 1) := by
      apply measure_congr
      filter_upwards [h0, h1] with x hx0 hx1
      simp only [mem_singleton_iff] at hx0 hx1
      apply propext
      constructor
      · intro hx
        exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), hx.2.le⟩
      · intro hx
        exact ⟨hx.1.le, lt_of_le_of_ne hx.2 hx1⟩
    _ = 1 := gaussMeasure_unit

theorem gaussInverseBranch_image_Ico_eq_firstDigitCylinder
    {q : ℕ} (hq : 0 < q) :
    gaussInverseBranch q '' Ico (0 : ℝ) 1 = firstDigitCylinder q := by
  simpa using!
    (gaussMap_preimage_inter_firstDigitCylinder univ q hq).symm

theorem gaussMeasure_firstDigitCylinder_eq_branchIntegral
    {q : ℕ} (hq : 0 < q) :
    gaussMeasure (firstDigitCylinder q) =
      ∫⁻ y in Ico (0 : ℝ) 1,
        ENNReal.ofReal (gaussBranchDensityReal q y) ∂volume := by
  rw [← gaussInverseBranch_image_Ico_eq_firstDigitCylinder hq]
  exact gaussMeasure_gaussInverseBranch_image hq measurableSet_Ico
    (fun y hy => ⟨hy.1, hy.2.le⟩)

/-- The same branch formula expressed intrinsically with respect to Gauss
measure. -/
theorem gaussMeasure_gaussInverseBranch_image_eq_ratio_lintegral
    {q : ℕ} (hq : 0 < q) {s : Set ℝ} (hsM : MeasurableSet s)
    (hs : s ⊆ Icc (0 : ℝ) 1) :
    gaussMeasure (gaussInverseBranch q '' s) =
      ∫⁻ y in s, ENNReal.ofReal (gaussBranchRatio q y) ∂gaussMeasure := by
  rw [gaussMeasure_gaussInverseBranch_image hq hsM hs,
    gaussMeasure_eq_volume_withDensity,
    setLIntegral_withDensity_eq_setLIntegral_mul volume
      measurable_gaussDensity (measurable_ofReal_gaussBranchRatio q) hsM]
  have hzero : volume.restrict s ({0} : Set ℝ) = 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton 0)]
    exact measure_mono_null inter_subset_left (measure_singleton 0)
  have hae0 : ∀ᵐ y ∂volume.restrict s, y ∉ ({0} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp hzero
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hsM, hae0] with y hy hy0
  have hycc : y ∈ Icc (0 : ℝ) 1 := hs hy
  have hyne : y ≠ 0 := by simpa only [mem_singleton_iff] using! hy0
  have hyunit : y ∈ Ioc (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hycc.1 (Ne.symm hyne), hycc.2⟩
  change ENNReal.ofReal (gaussBranchDensityReal q y) =
    gaussDensity y * ENNReal.ofReal (gaussBranchRatio q y)
  rw [gaussDensity_eq_ofReal_on_unit hyunit]
  change ENNReal.ofReal (gaussBranchDensityReal q y) =
    ENNReal.ofReal (gaussDensityReal y) *
      ENNReal.ofReal (gaussBranchRatio q y)
  rw [← ENNReal.ofReal_mul (gaussDensityReal_nonneg_on_unit
    hyunit)]
  congr 1
  rw [gaussBranchDensityReal_eq_ratio_mul_gaussDensityReal hq hycc]
  ring

theorem gaussMeasure_firstDigitCylinder_eq_ratio_lintegral
    {q : ℕ} (hq : 0 < q) :
    gaussMeasure (firstDigitCylinder q) =
      ∫⁻ y in Ico (0 : ℝ) 1,
        ENNReal.ofReal (gaussBranchRatio q y) ∂gaussMeasure := by
  rw [← gaussInverseBranch_image_Ico_eq_firstDigitCylinder hq]
  exact gaussMeasure_gaussInverseBranch_image_eq_ratio_lintegral hq
    measurableSet_Ico (fun y hy => ⟨hy.1, hy.2.le⟩)

/-- A pointwise branch ratio is at most six times its stationary average. -/
theorem ofReal_gaussBranchRatio_le_six_mul_firstDigitMeasure
    {q : ℕ} (hq : 0 < q) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    ENNReal.ofReal (gaussBranchRatio q y) ≤
      6 * gaussMeasure (firstDigitCylinder q) := by
  calc
    ENNReal.ofReal (gaussBranchRatio q y) =
        ∫⁻ _z in Ico (0 : ℝ) 1,
          ENNReal.ofReal (gaussBranchRatio q y) ∂gaussMeasure := by
      simp [gaussMeasure_Ico_unit]
    _ ≤ ∫⁻ z in Ico (0 : ℝ) 1,
        6 * ENNReal.ofReal (gaussBranchRatio q z) ∂gaussMeasure := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ico] with z hz
      have hzcc : z ∈ Icc (0 : ℝ) 1 := ⟨hz.1, hz.2.le⟩
      rw [show (6 : ℝ≥0∞) = ENNReal.ofReal (6 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
      exact ENNReal.ofReal_le_ofReal (gaussBranchRatio_le_six_mul hq hy hzcc)
    _ = 6 * (∫⁻ z in Ico (0 : ℝ) 1,
        ENNReal.ofReal (gaussBranchRatio q z) ∂gaussMeasure) := by
      rw [lintegral_const_mul]
      exact measurable_ofReal_gaussBranchRatio q
    _ = 6 * gaussMeasure (firstDigitCylinder q) := by
      rw [gaussMeasure_firstDigitCylinder_eq_ratio_lintegral hq]

/-- Conversely, the stationary average is at most six times every pointwise
branch ratio. -/
theorem firstDigitMeasure_le_six_mul_ofReal_gaussBranchRatio
    {q : ℕ} (hq : 0 < q) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    gaussMeasure (firstDigitCylinder q) ≤
      6 * ENNReal.ofReal (gaussBranchRatio q y) := by
  rw [gaussMeasure_firstDigitCylinder_eq_ratio_lintegral hq]
  calc
    (∫⁻ z in Ico (0 : ℝ) 1,
        ENNReal.ofReal (gaussBranchRatio q z) ∂gaussMeasure) ≤
        ∫⁻ _z in Ico (0 : ℝ) 1,
          6 * ENNReal.ofReal (gaussBranchRatio q y) ∂gaussMeasure := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ico] with z hz
      have hzcc : z ∈ Icc (0 : ℝ) 1 := ⟨hz.1, hz.2.le⟩
      rw [show (6 : ℝ≥0∞) = ENNReal.ofReal (6 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
      exact ENNReal.ofReal_le_ofReal (gaussBranchRatio_le_six_mul hq hzcc hy)
    _ = 6 * ENNReal.ofReal (gaussBranchRatio q y) := by
      simp [gaussMeasure_Ico_unit]

/-- Uniform quasi-Bernoulli upper bound for one inverse branch and an
arbitrary measurable tail set. -/
theorem gaussMeasure_gaussInverseBranch_image_le
    {q : ℕ} (hq : 0 < q) {s : Set ℝ} (hsM : MeasurableSet s)
    (hs : s ⊆ Icc (0 : ℝ) 1) :
    gaussMeasure (gaussInverseBranch q '' s) ≤
      6 * gaussMeasure (firstDigitCylinder q) * gaussMeasure s := by
  rw [gaussMeasure_gaussInverseBranch_image_eq_ratio_lintegral hq hsM hs]
  calc
    (∫⁻ y in s, ENNReal.ofReal (gaussBranchRatio q y) ∂gaussMeasure) ≤
        ∫⁻ _y in s,
          6 * gaussMeasure (firstDigitCylinder q) ∂gaussMeasure := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hsM] with y hy
      exact ofReal_gaussBranchRatio_le_six_mul_firstDigitMeasure hq (hs hy)
    _ = 6 * gaussMeasure (firstDigitCylinder q) * gaussMeasure s := by
      simp

/-- One first-digit cylinder is uniformly quasi-Bernoulli with every
measurable event in the future tail. -/
theorem gaussMeasure_firstDigitCylinder_inter_preimage_le
    {q : ℕ} (hq : 0 < q) {B : Set ℝ} (hBM : MeasurableSet B) :
    gaussMeasure (firstDigitCylinder q ∩ gaussMap ⁻¹' B) ≤
      6 * gaussMeasure (firstDigitCylinder q) * gaussMeasure B := by
  rw [inter_comm, gaussMap_preimage_inter_firstDigitCylinder B q hq]
  calc
    gaussMeasure (gaussInverseBranch q '' (B ∩ Ico (0 : ℝ) 1)) ≤
        6 * gaussMeasure (firstDigitCylinder q) *
          gaussMeasure (B ∩ Ico (0 : ℝ) 1) := by
      apply gaussMeasure_gaussInverseBranch_image_le hq
      · exact hBM.inter measurableSet_Ico
      · exact fun _ hy => ⟨hy.2.1, hy.2.2.le⟩
    _ ≤ 6 * gaussMeasure (firstDigitCylinder q) * gaussMeasure B := by
      gcongr
      exact inter_subset_left

/-! ## Arbitrary unions of one-digit cylinders -/

/-- The `n`th positive digit cylinder, retained only when `n+1` belongs to
the selected set of digits. -/
def selectedGaussDigitCylinder (digits : Set ℕ) (n : ℕ) : Set ℝ :=
  by
    classical
    exact if n + 1 ∈ digits then firstDigitCylinder (n + 1) else ∅

theorem measurableSet_selectedGaussDigitCylinder
    (digits : Set ℕ) (n : ℕ) :
    MeasurableSet (selectedGaussDigitCylinder digits n) := by
  unfold selectedGaussDigitCylinder
  split_ifs
  · exact measurableSet_Ioc
  · exact MeasurableSet.empty

theorem pairwise_disjoint_selectedGaussDigitCylinder (digits : Set ℕ) :
    Pairwise fun m n : ℕ =>
      Disjoint (selectedGaussDigitCylinder digits m)
        (selectedGaussDigitCylinder digits n) := by
  intro m n hmn
  unfold selectedGaussDigitCylinder
  split_ifs
  · exact pairwise_disjoint_firstDigitCylinder hmn
  all_goals simp

/-- Exact countable-cylinder realization of a one-digit event. -/
theorem iUnion_selectedGaussDigitCylinder (digits : Set ℕ) :
    (⋃ n : ℕ, selectedGaussDigitCylinder digits n) =
      Ioc (0 : ℝ) 1 ∩ gaussFirstDigitNat ⁻¹' digits := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    have hmem : n + 1 ∈ digits := by
      by_contra hnot
      simp [selectedGaussDigitCylinder, hnot] at hn
    have hxcyl : x ∈ firstDigitCylinder (n + 1) := by
      simpa [selectedGaussDigitCylinder, hmem] using! hn
    have hxunit := firstDigitCylinder_subset_unit (n + 1) (by omega) hxcyl
    have hdigitInt :=
      (gaussFirstDigit_eq_iff_mem_firstDigitCylinder hxunit (n + 1)
        (by omega)).2 hxcyl
    have hdigitNat : gaussFirstDigitNat x = n + 1 := by
      have hcast := gaussFirstDigitNat_cast hxunit
      exact_mod_cast hcast.trans hdigitInt
    exact ⟨hxunit, by simpa [hdigitNat] using! hmem⟩
  · rintro ⟨hxunit, hxdigit⟩
    have hq : 0 < gaussFirstDigitNat x := gaussFirstDigitNat_pos hxunit
    let n := gaussFirstDigitNat x - 1
    have hnq : n + 1 = gaussFirstDigitNat x := by
      dsimp [n]
      omega
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    have hmem : n + 1 ∈ digits := by simpa [hnq] using! hxdigit
    simp only [selectedGaussDigitCylinder, if_pos hmem]
    apply (gaussFirstDigit_eq_iff_mem_firstDigitCylinder hxunit (n + 1)
      (by omega)).1
    rw [hnq, gaussFirstDigitNat_cast hxunit]

theorem gaussMeasure_oneDigitEvent_eq_tsum (digits : Set ℕ) :
    gaussMeasure (Ioc (0 : ℝ) 1 ∩ gaussFirstDigitNat ⁻¹' digits) =
      ∑' n : ℕ, gaussMeasure (selectedGaussDigitCylinder digits n) := by
  rw [← iUnion_selectedGaussDigitCylinder digits,
    measure_iUnion (pairwise_disjoint_selectedGaussDigitCylinder digits)
      (measurableSet_selectedGaussDigitCylinder digits)]

theorem gaussMeasure_selectedDigitCylinder_inter_preimage_le
    (digits : Set ℕ) (n : ℕ) {B : Set ℝ} (hBM : MeasurableSet B) :
    gaussMeasure
        (selectedGaussDigitCylinder digits n ∩ gaussMap ⁻¹' B) ≤
      6 * gaussMeasure (selectedGaussDigitCylinder digits n) *
        gaussMeasure B := by
  classical
  unfold selectedGaussDigitCylinder
  split_ifs with hmem
  · exact gaussMeasure_firstDigitCylinder_inter_preimage_le (by omega) hBM
  · simp

/-- Gap-one quasi-Bernoulli upper bound for an arbitrary one-digit event.
No finiteness assumption is imposed on the selected digit set. -/
theorem gaussMeasure_oneDigitEvent_inter_preimage_le
    (digits : Set ℕ) {B : Set ℝ} (hBM : MeasurableSet B) :
    gaussMeasure
        ((Ioc (0 : ℝ) 1 ∩ gaussFirstDigitNat ⁻¹' digits) ∩
          gaussMap ⁻¹' B) ≤
      6 * gaussMeasure
          (Ioc (0 : ℝ) 1 ∩ gaussFirstDigitNat ⁻¹' digits) *
        gaussMeasure B := by
  have hset :
      (Ioc (0 : ℝ) 1 ∩ gaussFirstDigitNat ⁻¹' digits) ∩
          gaussMap ⁻¹' B =
        ⋃ n : ℕ, selectedGaussDigitCylinder digits n ∩ gaussMap ⁻¹' B := by
    rw [← iUnion_selectedGaussDigitCylinder digits, iUnion_inter]
  rw [hset, measure_iUnion]
  · calc
      (∑' n : ℕ, gaussMeasure
          (selectedGaussDigitCylinder digits n ∩ gaussMap ⁻¹' B)) ≤
          ∑' n : ℕ, 6 * gaussMeasure
            (selectedGaussDigitCylinder digits n) * gaussMeasure B :=
        ENNReal.tsum_le_tsum fun n =>
          gaussMeasure_selectedDigitCylinder_inter_preimage_le digits n hBM
      _ = 6 * (∑' n : ℕ,
          gaussMeasure (selectedGaussDigitCylinder digits n)) *
            gaussMeasure B := by
        simp_rw [mul_assoc]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
      _ = 6 * gaussMeasure
          (Ioc (0 : ℝ) 1 ∩ gaussFirstDigitNat ⁻¹' digits) *
            gaussMeasure B := by
        rw [gaussMeasure_oneDigitEvent_eq_tsum digits]
  · intro m n hmn
    exact (pairwise_disjoint_selectedGaussDigitCylinder digits hmn).mono
      inter_subset_left inter_subset_left
  · intro n
    exact (measurableSet_selectedGaussDigitCylinder digits n).inter
      (hBM.preimage measurable_gaussMap)

theorem gaussMeasureReal_oneDigitEvent_inter_preimage_le
    (digits : Set ℕ) {B : Set ℝ} (hBM : MeasurableSet B) :
    gaussMeasure.real
        ((Ioc (0 : ℝ) 1 ∩ gaussFirstDigitNat ⁻¹' digits) ∩
          gaussMap ⁻¹' B) ≤
      6 * gaussMeasure.real
          (Ioc (0 : ℝ) 1 ∩ gaussFirstDigitNat ⁻¹' digits) *
        gaussMeasure.real B := by
  have h := gaussMeasure_oneDigitEvent_inter_preimage_le digits hBM
  have hreal := ENNReal.toReal_mono (by finiteness) h
  simpa only [measureReal_def, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat] using! hreal

/-- Explicit gap-one relative-mixing inequality.  The constant `5` follows
from the multiplicative upper bound `6`; no lower correlation estimate is
needed because all probabilities are nonnegative. -/
theorem gaussMeasureReal_oneDigitEvent_inter_preimage_error_le
    (digits : Set ℕ) {B : Set ℝ} (hBM : MeasurableSet B) :
    |gaussMeasure.real
        ((Ioc (0 : ℝ) 1 ∩ gaussFirstDigitNat ⁻¹' digits) ∩
          gaussMap ⁻¹' B) -
      gaussMeasure.real
          (Ioc (0 : ℝ) 1 ∩ gaussFirstDigitNat ⁻¹' digits) *
        gaussMeasure.real B| ≤
      5 * gaussMeasure.real
          (Ioc (0 : ℝ) 1 ∩ gaussFirstDigitNat ⁻¹' digits) *
        gaussMeasure.real B := by
  have hupp := gaussMeasureReal_oneDigitEvent_inter_preimage_le digits hBM
  have hinter0 : 0 ≤ gaussMeasure.real
      ((Ioc (0 : ℝ) 1 ∩ gaussFirstDigitNat ⁻¹' digits) ∩
        gaussMap ⁻¹' B) := measureReal_nonneg
  have hprod0 : 0 ≤ gaussMeasure.real
      (Ioc (0 : ℝ) 1 ∩ gaussFirstDigitNat ⁻¹' digits) *
        gaussMeasure.real B :=
    mul_nonneg measureReal_nonneg measureReal_nonneg
  rw [abs_le]
  constructor <;> nlinarith

theorem gaussOrbit_succ_apply_right (n : ℕ) (x : ℝ) :
    gaussOrbit (n + 1) x = gaussOrbit n (gaussMap x) := by
  simp [gaussOrbit, Function.iterate_succ_apply]

theorem gaussOrbit_add_apply_right (m n : ℕ) (x : ℝ) :
    gaussOrbit (m + n) x = gaussOrbit n (gaussOrbit m x) := by
  unfold gaussOrbit
  calc
    (gaussMap^[m + n]) x = (gaussMap^[n + m]) x := by rw [add_comm]
    _ = (gaussMap^[n]) ((gaussMap^[m]) x) :=
      Function.iterate_add_apply gaussMap n m x

theorem gaussOrbit_preimage_inter_later_preimage
    (m n : ℕ) (hmn : m ≤ n) (A B : Set ℝ) :
    (gaussOrbit m) ⁻¹' A ∩ (gaussOrbit n) ⁻¹' B =
      (gaussOrbit m) ⁻¹'
        (A ∩ (gaussOrbit (n - m)) ⁻¹' B) := by
  ext x
  simp only [mem_inter_iff, mem_preimage]
  rw [← gaussOrbit_add_apply_right m (n - m) x,
    Nat.add_sub_of_le hmn]

/-- The same explicit relative bound at every positive gap.  This is a
uniform quasi-Bernoulli theorem; it does not assert decay as the gap grows. -/
theorem gaussMeasureReal_oneDigitEvent_inter_gaussOrbit_preimage_error_le
    {A B : Set ℝ} (hA : IsGaussOneDigitEvent A) (hBM : MeasurableSet B)
    {gap : ℕ} (hgap : 0 < gap) :
    |gaussMeasure.real (A ∩ (gaussOrbit gap) ⁻¹' B) -
      gaussMeasure.real A * gaussMeasure.real B| ≤
      5 * gaussMeasure.real A * gaussMeasure.real B := by
  rcases hA with ⟨digits, rfl⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : gap ≠ 0)
  have hpre :
      (gaussOrbit (k + 1)) ⁻¹' B =
        gaussMap ⁻¹' ((gaussOrbit k) ⁻¹' B) := by
    ext x
    simp only [mem_preimage]
    rw [gaussOrbit_succ_apply_right]
  rw [hpre]
  have htailM : MeasurableSet ((gaussOrbit k) ⁻¹' B) :=
    hBM.preimage (measurable_gaussOrbit k)
  have h := gaussMeasureReal_oneDigitEvent_inter_preimage_error_le
    digits htailM
  rw [gaussMeasure_real_gaussOrbit_preimage k hBM] at h
  exact h

/-- Stationary two-time form of the explicit one-digit bound. -/
theorem gaussMeasureReal_gaussOrbit_oneDigit_inter_later_error_le
    {A B : Set ℝ} (hA : IsGaussOneDigitEvent A)
    (hAM : MeasurableSet A) (hBM : MeasurableSet B)
    {m n : ℕ} (hmn : m < n) :
    |gaussMeasure.real
        ((gaussOrbit m) ⁻¹' A ∩ (gaussOrbit n) ⁻¹' B) -
      gaussMeasure.real ((gaussOrbit m) ⁻¹' A) *
        gaussMeasure.real ((gaussOrbit n) ⁻¹' B)| ≤
      5 * gaussMeasure.real ((gaussOrbit m) ⁻¹' A) *
        gaussMeasure.real ((gaussOrbit n) ⁻¹' B) := by
  rw [gaussOrbit_preimage_inter_later_preimage m n hmn.le A B]
  have htailM : MeasurableSet ((gaussOrbit (n - m)) ⁻¹' B) :=
    hBM.preimage (measurable_gaussOrbit (n - m))
  have hinterM : MeasurableSet (A ∩ (gaussOrbit (n - m)) ⁻¹' B) :=
    hAM.inter htailM
  rw [gaussMeasure_real_gaussOrbit_preimage m hinterM,
    gaussMeasure_real_gaussOrbit_preimage m hAM,
    gaussMeasure_real_gaussOrbit_preimage n hBM]
  exact gaussMeasureReal_oneDigitEvent_inter_gaussOrbit_preimage_error_le
    hA hBM (Nat.sub_pos_of_lt hmn)

/-! ## Sequential packaging -/

/-- A finite future block shifted back to a prescribed base time. -/
def shiftedGaussTailEvent {r : ℕ} (base : ℕ)
    (times : Fin r → ℕ) (events : Fin r → Set ℝ) : Set ℝ :=
  orderedEventIntersection <| List.ofFn fun i =>
    (gaussOrbit (times i - base)) ⁻¹' events i

theorem measurableSet_shiftedGaussTailEvent
    {r : ℕ} {base : ℕ} {times : Fin r → ℕ}
    {events : Fin r → Set ℝ} (hEvents : ∀ i, MeasurableSet (events i)) :
    MeasurableSet (shiftedGaussTailEvent base times events) := by
  apply measurableSet_orderedEventIntersection
  intro A hA
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
  exact (hEvents i).preimage (measurable_gaussOrbit (times i - base))

/-- Pulling the shifted block back by `base` recovers the original block. -/
theorem shiftedGaussTailEvent_preimage
    {r : ℕ} {base : ℕ} {times : Fin r → ℕ}
    {events : Fin r → Set ℝ} (hbase : ∀ i, base ≤ times i) :
    (gaussOrbit base) ⁻¹' shiftedGaussTailEvent base times events =
      orderedEventIntersection (List.ofFn fun i =>
        (gaussOrbit (times i)) ⁻¹' events i) := by
  ext x
  rw [mem_preimage, mem_orderedEventIntersection_ofFn_iff]
  change
    (gaussOrbit base x ∈
      orderedEventIntersection (List.ofFn fun i =>
        (gaussOrbit (times i - base)) ⁻¹' events i)) ↔ _
  rw [mem_orderedEventIntersection_ofFn_iff]
  constructor
  · intro h i
    have hadd : base + (times i - base) = times i := Nat.add_sub_of_le (hbase i)
    have horbit := gaussOrbit_add_apply_right base (times i - base) x
    rw [hadd] at horbit
    simpa only [mem_preimage, horbit] using! h i
  · intro h i
    have hadd : base + (times i - base) = times i := Nat.add_sub_of_le (hbase i)
    have horbit := gaussOrbit_add_apply_right base (times i - base) x
    rw [hadd] at horbit
    simpa only [mem_preimage, horbit] using! h i

/-- Strictly chronological one-digit events satisfy the recursive relative
mixing record with the explicit uniform error `5`. -/
theorem exists_sequentialGaussDigitQuasiBernoulli
    {r : ℕ} (times : Fin r → ℕ) (events : Fin r → Set ℝ)
    (hEvents : ∀ i, MeasurableSet (events i))
    (hOneDigit : ∀ i, IsGaussOneDigitEvent (events i))
    (hTime : ∀ i j, i < j → times i < times j) :
    ∃ errors : List ℝ,
      SequentialEventRelativeMixing gaussMeasure errors
        (List.ofFn fun i => (gaussOrbit (times i)) ⁻¹' events i) ∧
      ∀ epsilon ∈ errors, epsilon = 5 := by
  induction r with
  | zero =>
      refine ⟨[], ?_, by simp⟩
      simpa using! (SequentialEventRelativeMixing.nil (mu := gaussMeasure))
  | succ r ih =>
      cases r with
      | zero =>
          refine ⟨[], ?_, by simp⟩
          simpa only [List.ofFn_succ, List.ofFn_zero] using!
            (SequentialEventRelativeMixing.singleton (mu := gaussMeasure)
              ((gaussOrbit (times 0)) ⁻¹' events 0))
      | succ k =>
          let tailTimes : Fin (k + 1) → ℕ := fun i => times i.succ
          let tailEvents : Fin (k + 1) → Set ℝ := fun i => events i.succ
          have hTailEvents : ∀ i, MeasurableSet (tailEvents i) := by
            intro i
            exact hEvents i.succ
          have hTailOne : ∀ i, IsGaussOneDigitEvent (tailEvents i) := by
            intro i
            exact hOneDigit i.succ
          have hTailTime : ∀ i j, i < j → tailTimes i < tailTimes j := by
            intro i j hij
            exact hTime i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij)
          obtain ⟨errors, htail, herrors⟩ :=
            ih tailTimes tailEvents hTailEvents hTailOne hTailTime
          let base : ℕ := tailTimes 0
          let H : Set ℝ := shiftedGaussTailEvent base tailTimes tailEvents
          have hbase : ∀ i, base ≤ tailTimes i := by
            intro i
            by_cases hi : i = 0
            · subst i
              exact le_rfl
            · exact (hTailTime 0 i (Fin.pos_iff_ne_zero.mpr hi)).le
          have hHM : MeasurableSet H :=
            measurableSet_shiftedGaussTailEvent hTailEvents
          have hshift :
              (gaussOrbit base) ⁻¹' H =
                orderedEventIntersection (List.ofFn fun i =>
                  (gaussOrbit (tailTimes i)) ⁻¹' tailEvents i) :=
            shiftedGaussTailEvent_preimage hbase
          have ht0base : times 0 < base := by
            exact hTime 0 (Fin.succ 0) (Fin.succ_pos 0)
          have hhead :=
            gaussMeasureReal_gaussOrbit_oneDigit_inter_later_error_le
              (hOneDigit 0) (hEvents 0) hHM ht0base
          rw [hshift] at hhead
          have htail' :
              SequentialEventRelativeMixing gaussMeasure errors
                (List.ofFn fun i : Fin (k + 1) =>
                  (gaussOrbit (times i.succ)) ⁻¹' events i.succ) := by
            simpa [tailTimes, tailEvents] using! htail
          have hhead' :
              |gaussMeasure.real
                  ((gaussOrbit (times 0)) ⁻¹' events 0 ∩
                    orderedEventIntersection
                      (List.ofFn fun i : Fin (k + 1) =>
                        (gaussOrbit (times i.succ)) ⁻¹' events i.succ)) -
                gaussMeasure.real ((gaussOrbit (times 0)) ⁻¹' events 0) *
                  gaussMeasure.real
                    (orderedEventIntersection
                      (List.ofFn fun i : Fin (k + 1) =>
                        (gaussOrbit (times i.succ)) ⁻¹' events i.succ))| ≤
                5 * gaussMeasure.real
                  ((gaussOrbit (times 0)) ⁻¹' events 0) *
                  gaussMeasure.real
                    (orderedEventIntersection
                      (List.ofFn fun i : Fin (k + 1) =>
                        (gaussOrbit (times i.succ)) ⁻¹' events i.succ)) := by
            simpa [base, tailTimes, tailEvents] using! hhead
          have htailCons := htail'
          rw [List.ofFn_succ] at htailCons
          have hheadCons := hhead'
          rw [List.ofFn_succ] at hheadCons
          refine ⟨5 :: errors, ?_, ?_⟩
          · have hcons := SequentialEventRelativeMixing.cons hheadCons htailCons
            simpa only [List.ofFn_succ] using! hcons
          · intro epsilon hepsilon
            simp only [List.mem_cons] at hepsilon
            rcases hepsilon with rfl | hepsilon
            · rfl
            · exact herrors epsilon hepsilon

/-- The exact positive-gap interface consumed by the factorial replacement:
every recursive error is nonnegative and bounded by the explicit constant
`5`. -/
theorem exists_sequentialGaussDigitQuasiBernoulli_of_positiveGap
    {r : ℕ} (times : Fin r → ℕ) (events : Fin r → Set ℝ) (gap : ℕ)
    (hEvents : ∀ i, MeasurableSet (events i))
    (hOneDigit : ∀ i, IsGaussOneDigitEvent (events i))
    (hgap0 : 0 < gap)
    (hgap : ∀ i j, i < j → times i + gap ≤ times j) :
    ∃ errors : List ℝ,
      SequentialEventRelativeMixing gaussMeasure errors
        (List.ofFn fun i => (gaussOrbit (times i)) ⁻¹' events i) ∧
      ∀ epsilon ∈ errors, 0 ≤ epsilon ∧ epsilon ≤ 5 := by
  have hTime : ∀ i j, i < j → times i < times j := by
    intro i j hij
    have h := hgap i j hij
    omega
  obtain ⟨errors, hmix, herrors⟩ :=
    exists_sequentialGaussDigitQuasiBernoulli times events
      hEvents hOneDigit hTime
  refine ⟨errors, hmix, ?_⟩
  intro epsilon hepsilon
  rw [herrors epsilon hepsilon]
  norm_num

/-- Unconditional bounded-distortion theorem at every positive gap. -/
theorem gaussDigitPsiMixing_const_five :
    GaussDigitPsiMixing (fun _ => 5) := by
  intro r times events gap hEvents hOneDigit hgap0 hgap
  exact exists_sequentialGaussDigitQuasiBernoulli_of_positiveGap
    times events gap hEvents hOneDigit hgap0 hgap


end

end Erdos1002
