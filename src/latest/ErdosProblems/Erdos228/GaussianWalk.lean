import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

/-!
# Gaussian and finite-walk concentration tools for Erdős Problem 228

The Lovett--Meka part of the flat-polynomial construction repeatedly uses
Gaussian increments, independent signs, and a martingale tail estimate.  This
file records the corresponding interfaces in the form already supported by
Mathlib's sub-Gaussian moment-generating-function API.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal

namespace Erdos228.GaussianWalk

/-! ## A reusable two-sided Chernoff bound -/

/-- A sub-Gaussian MGF bound implies the usual two-sided tail estimate. -/
theorem measureReal_abs_ge_le_of_hasSubgaussianMGF
    {Omega : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    {X : Omega → ℝ} {c : ℝ≥0} (hX : HasSubgaussianMGF X c mu)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    mu.real {omega | epsilon ≤ |X omega|} ≤
      2 * exp (-epsilon ^ 2 / (2 * c)) := by
  have hset : {omega | epsilon ≤ |X omega|} =
      {omega | epsilon ≤ X omega} ∪ {omega | epsilon ≤ -X omega} := by
    ext omega
    simp only [mem_ofPred_eq, mem_union]
    constructor
    · intro h
      by_cases hnonneg : 0 ≤ X omega
      · exact Or.inl (by simpa [abs_of_nonneg hnonneg] using h)
      · exact Or.inr (by simpa [abs_of_nonpos (le_of_not_ge hnonneg)] using h)
    · rintro (h | h)
      · exact h.trans (le_abs_self (X omega))
      · exact h.trans (neg_le_abs (X omega))
  rw [hset]
  calc
    mu.real ({omega | epsilon ≤ X omega} ∪ {omega | epsilon ≤ -X omega}) ≤
        mu.real {omega | epsilon ≤ X omega} +
          mu.real {omega | epsilon ≤ -X omega} := measureReal_union_le _ _
    _ ≤ exp (-epsilon ^ 2 / (2 * c)) + exp (-epsilon ^ 2 / (2 * c)) :=
      add_le_add (hX.measure_ge_le hepsilon) (hX.neg.measure_ge_le hepsilon)
    _ = 2 * exp (-epsilon ^ 2 / (2 * c)) := by ring

/-! ## Centered Gaussian variables -/

/-- The identity variable under a centered real Gaussian law is sub-Gaussian
with parameter equal to its variance. -/
theorem hasSubgaussianMGF_id_gaussianReal (v : ℝ≥0) :
    HasSubgaussianMGF id v (gaussianReal 0 v) where
  integrable_exp_mul t := by
    simpa [id_eq] using
      (integrable_exp_mul_gaussianReal (μ := 0) (v := v) t)
  mgf_le t := by
    rw [mgf_id_gaussianReal]
    simp

/-- One-sided Gaussian tail bound, including the degenerate zero-variance
case handled by Mathlib's extended-real conventions. -/
theorem gaussianReal_measureReal_ge_le (v : ℝ≥0) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) :
    (gaussianReal 0 v).real {x | epsilon ≤ x} ≤
      exp (-epsilon ^ 2 / (2 * v)) := by
  simpa using (hasSubgaussianMGF_id_gaussianReal v).measure_ge_le hepsilon

/-- Two-sided Gaussian tail bound. -/
theorem gaussianReal_measureReal_abs_ge_le (v : ℝ≥0) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) :
    (gaussianReal 0 v).real {x | epsilon ≤ |x|} ≤
      2 * exp (-epsilon ^ 2 / (2 * v)) := by
  simpa using measureReal_abs_ge_le_of_hasSubgaussianMGF
    (hasSubgaussianMGF_id_gaussianReal v) hepsilon

/-! ## Symmetric signs and their finite product -/

/-- The symmetric probability measure supported on `{-1, 1}`. -/
noncomputable def rademacherMeasure : Measure ℝ :=
  bernoulliMeasure 1 (-1) ⟨1 / 2, by norm_num⟩

noncomputable instance instIsProbabilityMeasureRademacher :
    IsProbabilityMeasure rademacherMeasure := by
  unfold rademacherMeasure
  infer_instance

theorem integral_id_rademacherMeasure :
    ∫ x, x ∂rademacherMeasure = 0 := by
  rw [rademacherMeasure, integral_bernoulliMeasure]
  norm_num

theorem ae_mem_Icc_rademacherMeasure :
    ∀ᵐ x ∂rademacherMeasure, x ∈ Icc (-1 : ℝ) 1 := by
  rw [rademacherMeasure, bernoulliMeasure_def]
  simp only [ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff measurableSet_Icc).2 (by norm_num)
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff measurableSet_Icc).2 (by norm_num)

/-- A symmetric sign is sub-Gaussian with variance proxy one. -/
theorem hasSubgaussianMGF_id_rademacherMeasure :
    HasSubgaussianMGF id 1 rademacherMeasure := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := rademacherMeasure) (X := id) measurable_id.aemeasurable
    ae_mem_Icc_rademacherMeasure integral_id_rademacherMeasure
  have hc : ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2) = (1 : ℝ≥0) := by
    norm_num
  rw [hc] at h
  exact h

/-- A Rademacher variable has absolute value one almost surely. -/
theorem ae_abs_eq_one_rademacherMeasure :
    ∀ᵐ x ∂rademacherMeasure, |x| = 1 := by
  have hmeas : MeasurableSet {x : ℝ | |x| = 1} :=
    measurable_abs (measurableSet_singleton 1)
  rw [rademacherMeasure, bernoulliMeasure_def]
  simp only [ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff hmeas).2 (by norm_num)
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff hmeas).2 (by norm_num)

/-- Product law for a finite family of independent symmetric signs. -/
noncomputable def rademacherProduct (iota : Type*) [Fintype iota] :
    Measure (iota → ℝ) :=
  Measure.pi fun _ : iota ↦ rademacherMeasure

noncomputable instance instIsProbabilityMeasureRademacherProduct
    (iota : Type*) [Fintype iota] :
    IsProbabilityMeasure (rademacherProduct iota) := by
  unfold rademacherProduct
  infer_instance

/-- Coordinate maps on the finite sign product are independent. -/
theorem iIndepFun_rademacherProduct
    (iota : Type*) [Fintype iota] :
    iIndepFun (fun i : iota ↦ fun omega : iota → ℝ ↦ omega i)
      (rademacherProduct iota) := by
  unfold rademacherProduct
  exact iIndepFun_pi fun _ ↦ measurable_id.aemeasurable

/-- Almost every point of the product space is an actual sign vector. -/
theorem ae_forall_abs_eq_one_rademacherProduct
    (iota : Type*) [Fintype iota] :
    ∀ᵐ omega ∂rademacherProduct iota, ∀ i, |omega i| = 1 := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval (μ := fun _ : iota ↦ rademacherMeasure) i)
    |>.quasiMeasurePreserving.tendsto_ae ae_abs_eq_one_rademacherMeasure

/-- Each coordinate of the finite product is a sub-Gaussian sign. -/
theorem hasSubgaussianMGF_rademacherCoord
    (iota : Type*) [Fintype iota] (i : iota) :
    HasSubgaussianMGF (fun omega : iota → ℝ ↦ omega i) 1
      (rademacherProduct iota) := by
  refine HasSubgaussianMGF.of_map (μ := rademacherProduct iota) (X := id)
    (Y := fun omega : iota → ℝ ↦ omega i)
    (measurable_pi_apply i).aemeasurable ?_
  have hmap : (rademacherProduct iota).map (fun omega : iota → ℝ ↦ omega i) =
      rademacherMeasure := by
    unfold rademacherProduct
    exact (measurePreserving_eval (μ := fun _ : iota ↦ rademacherMeasure) i).map_eq
  rw [hmap]
  exact hasSubgaussianMGF_id_rademacherMeasure

/-- Weighted coordinates remain independent. -/
theorem iIndepFun_weightedRademacher
    (iota : Type*) [Fintype iota] (a : iota → ℝ) :
    iIndepFun (fun i : iota ↦ fun omega : iota → ℝ ↦ a i * omega i)
      (rademacherProduct iota) := by
  have h := (iIndepFun_rademacherProduct iota).comp
    (fun i x ↦ a i * x) (fun i ↦ measurable_const.mul measurable_id)
  simpa [Function.comp_def] using h

/-- A finite weighted Rademacher sum has variance proxy `sum a_i^2`. -/
theorem hasSubgaussianMGF_weightedRademacherSum
    (iota : Type*) [Fintype iota] (a : iota → ℝ) :
    HasSubgaussianMGF
      (fun omega : iota → ℝ ↦ ∑ i, a i * omega i)
      (∑ i, ⟨a i ^ 2, sq_nonneg (a i)⟩)
      (rademacherProduct iota) := by
  apply HasSubgaussianMGF.sum_of_iIndepFun
    (iIndepFun_weightedRademacher iota a) (s := Finset.univ)
  intro i hi
  have h := (hasSubgaussianMGF_rademacherCoord iota i).const_mul (a i)
  have hc : (⟨a i ^ 2, sq_nonneg (a i)⟩ : ℝ≥0) * 1 =
      ⟨a i ^ 2, sq_nonneg (a i)⟩ := mul_one _
  exact hc ▸ h

/-- Two-sided Hoeffding bound for a finite weighted random-sign walk. -/
theorem weightedRademacherSum_measureReal_abs_ge_le
    (iota : Type*) [Fintype iota] (a : iota → ℝ)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    (rademacherProduct iota).real
        {omega | epsilon ≤ |∑ i, a i * omega i|} ≤
      2 * exp (-epsilon ^ 2 /
        (2 * (∑ i, (⟨a i ^ 2, sq_nonneg (a i)⟩ : ℝ≥0)))) := by
  exact measureReal_abs_ge_le_of_hasSubgaussianMGF
    (hasSubgaussianMGF_weightedRademacherSum iota a) hepsilon

/-! ## Finite martingale sums -/

/-- Partial sums, with the convention that the zeroth sum is zero. -/
def partialSum {Omega : Type*} (Y : ℕ → Omega → ℝ) (n : ℕ) (omega : Omega) : ℝ :=
  ∑ i ∈ Finset.range n, Y i omega

@[simp]
theorem partialSum_zero {Omega : Type*} (Y : ℕ → Omega → ℝ) :
    partialSum Y 0 = 0 := by
  funext omega
  simp [partialSum]

theorem partialSum_succ {Omega : Type*} (Y : ℕ → Omega → ℝ) (n : ℕ) :
    partialSum Y (n + 1) = fun omega ↦ partialSum Y n omega + Y n omega := by
  funext omega
  change (∑ i ∈ Finset.range (n + 1), Y i omega) =
    (∑ i ∈ Finset.range n, Y i omega) + Y n omega
  rw [Finset.sum_range_succ]

/-- Two-sided Azuma--Hoeffding bound in the conditional sub-Gaussian API used
by Mathlib.  This is the direct concentration interface needed by a finite
Gaussian edge-walk. -/
theorem martingalePartialSum_measureReal_abs_ge_le
    {Omega : Type*} {mOmega : MeasurableSpace Omega} [StandardBorelSpace Omega]
    {mu : Measure Omega} [IsZeroOrProbabilityMeasure mu]
    {Y : ℕ → Omega → ℝ} {cY : ℕ → ℝ≥0} {F : Filtration ℕ mOmega}
    (hAdapted : StronglyAdapted F Y)
    (hzero : HasSubgaussianMGF (Y 0) (cY 0) mu) (n : ℕ)
    (hcond : ∀ i < n - 1,
      HasCondSubgaussianMGF (F i) (F.le i) (Y (i + 1)) (cY (i + 1)) mu)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    mu.real {omega | epsilon ≤ |partialSum Y n omega|} ≤
      2 * exp (-epsilon ^ 2 /
        (2 * ∑ i ∈ Finset.range n, cY i)) := by
  have hsum := HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF
    hAdapted hzero n hcond
  exact measureReal_abs_ge_le_of_hasSubgaussianMGF hsum hepsilon

end Erdos228.GaussianWalk
