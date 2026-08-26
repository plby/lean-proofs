import ErdosProblems.Erdos520.HarperGlobalSlicing
import ErdosProblems.Erdos520.HarperScheduledRelativeProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem520

/-!
# A finite Gaussian envelope mixture

At coordinate `i` the actual tilted block law will be bounded on every
scheduled lattice interval by

`(1 + w i) * N(0, variance i) + w i * N(0, 1)`.

Expanding the product gives a finite mixture indexed by subsets of
coordinates.  Its total mass is uniformly bounded because the scheduled
widths are summable.  Keeping the expansion as a measure lets global lattice
slicing compare the complete path event without any additive tail term.
-/

/-- The Gaussian variance selected by a subset: coordinates in the subset
use the unit-variance fallback, and all other coordinates use the intended
block variance. -/
noncomputable def harperGaussianEnvelopeVariance
    {n : ℕ} (variance : Fin n → ℝ≥0) (s : Finset (Fin n))
    (i : Fin n) : ℝ≥0 :=
  if i ∈ s then 1 else variance i

/-- Coefficient of one component in the product-envelope expansion. -/
noncomputable def harperGaussianEnvelopeWeight
    {n : ℕ} (w : Fin n → ℝ≥0) (s : Finset (Fin n)) : ℝ≥0 :=
  (∏ i ∈ s, w i) * ∏ i ∈ sᶜ, (1 + w i)

/-- One centered Gaussian product component of the envelope. -/
noncomputable def harperGaussianEnvelopeComponent
    {n : ℕ} (variance : Fin n → ℝ≥0) (s : Finset (Fin n)) :
    Measure (Fin n → ℝ) :=
  Measure.pi (fun i ↦ gaussianReal 0
    (harperGaussianEnvelopeVariance variance s i))

noncomputable instance instIsProbabilityMeasureHarperGaussianEnvelopeComponent
    {n : ℕ} (variance : Fin n → ℝ≥0) (s : Finset (Fin n)) :
    IsProbabilityMeasure (harperGaussianEnvelopeComponent variance s) := by
  unfold harperGaussianEnvelopeComponent
  infer_instance

/-- The unnormalised Gaussian product envelope. -/
noncomputable def harperGaussianEnvelopeMixture
    {n : ℕ} (variance w : Fin n → ℝ≥0) : Measure (Fin n → ℝ) :=
  ∑ s : Finset (Fin n),
    harperGaussianEnvelopeWeight w s •
      harperGaussianEnvelopeComponent variance s

noncomputable instance instIsFiniteMeasureHarperGaussianEnvelopeMixture
    {n : ℕ} (variance w : Fin n → ℝ≥0) :
    IsFiniteMeasure (harperGaussianEnvelopeMixture variance w) := by
  unfold harperGaussianEnvelopeMixture
  infer_instance

theorem sum_harperGaussianEnvelopeWeight_eq_prod
    {n : ℕ} (w : Fin n → ℝ≥0) :
    (∑ s : Finset (Fin n), harperGaussianEnvelopeWeight w s) =
      ∏ i : Fin n, (1 + 2 * w i) := by
  unfold harperGaussianEnvelopeWeight
  rw [← Fintype.prod_add w (fun i ↦ 1 + w i)]
  apply Finset.prod_congr rfl
  intro i _hi
  ring

/-- The total envelope coefficient is bounded by the exponential of twice
the sum of coordinate widths. -/
theorem coe_sum_harperGaussianEnvelopeWeight_le_exp
    {n : ℕ} (w : Fin n → ℝ≥0) :
    (((∑ s : Finset (Fin n),
        harperGaussianEnvelopeWeight w s) : ℝ≥0) : ℝ) ≤
      Real.exp (2 * ∑ i : Fin n, (w i : ℝ)) := by
  rw [sum_harperGaussianEnvelopeWeight_eq_prod, NNReal.coe_prod]
  calc
    (∏ i : Fin n, (((1 + 2 * w i) : ℝ≥0) : ℝ)) ≤
        ∏ i : Fin n, Real.exp (2 * (w i : ℝ)) := by
      apply Finset.prod_le_prod
      · intro i _hi
        positivity
      · intro i _hi
        simpa only [NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul,
          NNReal.coe_ofNat, add_comm] using!
            Real.add_one_le_exp (2 * (w i : ℝ))
    _ = Real.exp (2 * ∑ i : Fin n, (w i : ℝ)) := by
      rw [Finset.mul_sum, Real.exp_sum]

/-- Scheduled widths make the total mass of the envelope at most `exp 4`,
uniformly in the starting block and the path length. -/
theorem coe_sum_harperScheduledGaussianEnvelopeWeight_le_exp_four
    (start n : ℕ) :
    (((∑ s : Finset (Fin n), harperGaussianEnvelopeWeight
        (fun i ↦ ⟨harperScheduledRelativeIntervalWidth
          (start + (i : ℕ)),
          (harperScheduledRelativeIntervalWidth_pos _).le⟩) s) : ℝ≥0) : ℝ) ≤
      Real.exp 4 := by
  calc
    _ ≤ Real.exp (2 * ∑ i : Fin n,
        harperScheduledRelativeIntervalWidth (start + (i : ℕ))) :=
      coe_sum_harperGaussianEnvelopeWeight_le_exp _
    _ ≤ Real.exp 4 := by
      apply Real.exp_le_exp.mpr
      have h := sum_fin_harperScheduledRelativeIntervalWidth_le_two start n
      linarith

/-- Evaluation of the finite envelope mixture is the corresponding weighted
sum of component masses. -/
theorem measureReal_harperGaussianEnvelopeMixture_apply
    {n : ℕ} (variance w : Fin n → ℝ≥0) (A : Set (Fin n → ℝ)) :
    (harperGaussianEnvelopeMixture variance w).real A =
      ∑ s : Finset (Fin n), (harperGaussianEnvelopeWeight w s : ℝ) *
        (harperGaussianEnvelopeComponent variance s).real A := by
  classical
  unfold harperGaussianEnvelopeMixture
  induction (Finset.univ : Finset (Finset (Fin n))) using Finset.induction_on with
  | empty => simp
  | @insert s ss hs ih =>
      rw [Finset.sum_insert hs,
        measureReal_add_apply (by finiteness) (by finiteness),
        measureReal_nnreal_smul_apply, ih, Finset.sum_insert hs]

/-- If every Gaussian component obeys the same event bound, the unnormalised
mixture obeys that bound times its total coefficient. -/
theorem measureReal_harperGaussianEnvelopeMixture_le_totalWeight_mul
    {n : ℕ} (variance w : Fin n → ℝ≥0) (A : Set (Fin n → ℝ))
    (B : ℝ) (_hB : 0 ≤ B)
    (hcomponent : ∀ s : Finset (Fin n),
      (harperGaussianEnvelopeComponent variance s).real A ≤ B) :
    (harperGaussianEnvelopeMixture variance w).real A ≤
      (((∑ s : Finset (Fin n),
        harperGaussianEnvelopeWeight w s) : ℝ≥0) : ℝ) * B := by
  rw [measureReal_harperGaussianEnvelopeMixture_apply]
  calc
    (∑ s : Finset (Fin n), (harperGaussianEnvelopeWeight w s : ℝ) *
        (harperGaussianEnvelopeComponent variance s).real A) ≤
        ∑ s : Finset (Fin n),
          (harperGaussianEnvelopeWeight w s : ℝ) * B := by
      apply Finset.sum_le_sum
      intro s _hs
      exact mul_le_mul_of_nonneg_left (hcomponent s) (by positivity)
    _ = (∑ s : Finset (Fin n),
          (harperGaussianEnvelopeWeight w s : ℝ)) * B := by
      rw [Finset.sum_mul]
    _ = (((∑ s : Finset (Fin n),
          harperGaussianEnvelopeWeight w s) : ℝ≥0) : ℝ) * B := by
      rw [NNReal.coe_sum]

/-- The scheduled envelope costs at most `exp 4` when all of its components
obey the same nonnegative event bound. -/
theorem measureReal_harperScheduledGaussianEnvelopeMixture_le_exp_four_mul
    {n : ℕ} (start : ℕ) (variance : Fin n → ℝ≥0)
    (A : Set (Fin n → ℝ)) (B : ℝ) (hB : 0 ≤ B)
    (hcomponent : ∀ s : Finset (Fin n),
      (harperGaussianEnvelopeComponent variance s).real A ≤ B) :
    (harperGaussianEnvelopeMixture variance
      (fun i ↦ ⟨harperScheduledRelativeIntervalWidth
        (start + (i : ℕ)),
        (harperScheduledRelativeIntervalWidth_pos _).le⟩)).real A ≤
      Real.exp 4 * B := by
  have hmix :=
    measureReal_harperGaussianEnvelopeMixture_le_totalWeight_mul
      variance
      (fun i ↦ ⟨harperScheduledRelativeIntervalWidth
        (start + (i : ℕ)),
        (harperScheduledRelativeIntervalWidth_pos _).le⟩)
      A B hB hcomponent
  exact hmix.trans (mul_le_mul_of_nonneg_right
    (coe_sum_harperScheduledGaussianEnvelopeWeight_le_exp_four start n) hB)

theorem harperGaussianEnvelopeVariance_mem
    {n : ℕ} (variance : Fin n → ℝ≥0) (s : Finset (Fin n))
    (hlower : ∀ i, (1 / 4 : ℝ≥0) ≤ variance i)
    (hupper : ∀ i, variance i ≤ 1) (i : Fin n) :
    (1 / 4 : ℝ≥0) ≤ harperGaussianEnvelopeVariance variance s i ∧
      harperGaussianEnvelopeVariance variance s i ≤ 1 := by
  by_cases hi : i ∈ s
  · simp [harperGaussianEnvelopeVariance, hi]
  · rw [harperGaussianEnvelopeVariance, if_neg hi]
    exact ⟨hlower i, hupper i⟩

/-- The mass of a coordinate cell under one component is the product of its
selected one-dimensional Gaussian masses. -/
theorem measureReal_harperGaussianEnvelopeComponent_coordinateCell
    {n : ℕ} (variance : Fin n → ℝ≥0) (s : Finset (Fin n))
    (a delta : Fin n → ℝ) :
    (harperGaussianEnvelopeComponent variance s).real
        (harperCoordinateIocCell a delta) =
      ∏ i : Fin n, (gaussianReal 0
        (harperGaussianEnvelopeVariance variance s i)).real
          (Ioc (a i) (a i + delta i)) := by
  exact measureReal_pi_harperCoordinateIocCell _ a delta

/-- Expanding the coordinatewise two-Gaussian envelope agrees exactly with
the finite mixture on every coordinate cell. -/
theorem prod_gaussianEnvelope_coordinateMass_eq_mixture
    {n : ℕ} (variance w : Fin n → ℝ≥0)
    (a delta : Fin n → ℝ) :
    (∏ i : Fin n,
        ((1 + (w i : ℝ)) *
            (gaussianReal 0 (variance i)).real
              (Ioc (a i) (a i + delta i)) +
          (w i : ℝ) *
            (gaussianReal 0 1).real
              (Ioc (a i) (a i + delta i)))) =
      (harperGaussianEnvelopeMixture variance w).real
        (harperCoordinateIocCell a delta) := by
  classical
  rw [measureReal_harperGaussianEnvelopeMixture_apply]
  calc
    (∏ i : Fin n,
        ((1 + (w i : ℝ)) *
            (gaussianReal 0 (variance i)).real
              (Ioc (a i) (a i + delta i)) +
          (w i : ℝ) *
            (gaussianReal 0 1).real
              (Ioc (a i) (a i + delta i)))) =
        ∏ i : Fin n,
          ((w i : ℝ) *
              (gaussianReal 0 1).real
                (Ioc (a i) (a i + delta i)) +
            (1 + (w i : ℝ)) *
              (gaussianReal 0 (variance i)).real
                (Ioc (a i) (a i + delta i))) := by
      apply Finset.prod_congr rfl
      intro i _hi
      ring
    _ = ∑ s : Finset (Fin n),
        (∏ i ∈ s, (w i : ℝ) *
            (gaussianReal 0 1).real (Ioc (a i) (a i + delta i))) *
          ∏ i ∈ sᶜ, (1 + (w i : ℝ)) *
            (gaussianReal 0 (variance i)).real
              (Ioc (a i) (a i + delta i)) := by
      rw [Fintype.prod_add]
    _ = ∑ s : Finset (Fin n),
        (harperGaussianEnvelopeWeight w s : ℝ) *
          (harperGaussianEnvelopeComponent variance s).real
            (harperCoordinateIocCell a delta) := by
      apply Finset.sum_congr rfl
      intro s _hs
      rw [measureReal_harperGaussianEnvelopeComponent_coordinateCell]
      unfold harperGaussianEnvelopeWeight harperGaussianEnvelopeVariance
      simp only [NNReal.coe_mul, NNReal.coe_prod, NNReal.coe_add,
        NNReal.coe_one]
      have hselected :
          (∏ i : Fin n, (gaussianReal 0
              (if i ∈ s then 1 else variance i)).real
                (Ioc (a i) (a i + delta i))) =
            (∏ i ∈ s, (gaussianReal 0 1).real
                (Ioc (a i) (a i + delta i))) *
              ∏ i ∈ sᶜ, (gaussianReal 0 (variance i)).real
                (Ioc (a i) (a i + delta i)) := by
        rw [← Finset.prod_mul_prod_compl s
          (fun i ↦ (gaussianReal 0
            (if i ∈ s then 1 else variance i)).real
              (Ioc (a i) (a i + delta i)))]
        congr 1
        · apply Finset.prod_congr rfl
          intro i hi
          simp [hi]
        · apply Finset.prod_congr rfl
          intro i hi
          simp [Finset.mem_compl.mp hi]
      rw [hselected, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      ring

/-- A coordinatewise two-Gaussian interval envelope multiplies to domination
by the finite mixture on the complete product cell. -/
theorem measureReal_pi_coordinateCell_le_harperGaussianEnvelopeMixture
    {n : ℕ} (rho : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (rho i)]
    (variance w : Fin n → ℝ≥0) (a delta : Fin n → ℝ)
    (hcoord : ∀ i,
      (rho i).real (Ioc (a i) (a i + delta i)) ≤
        (1 + (w i : ℝ)) *
            (gaussianReal 0 (variance i)).real
              (Ioc (a i) (a i + delta i)) +
          (w i : ℝ) *
            (gaussianReal 0 1).real
              (Ioc (a i) (a i + delta i))) :
    (Measure.pi rho).real (harperCoordinateIocCell a delta) ≤
      (harperGaussianEnvelopeMixture variance w).real
        (harperCoordinateIocCell a delta) := by
  rw [measureReal_pi_harperCoordinateIocCell,
    ← prod_gaussianEnvelope_coordinateMass_eq_mixture variance w a delta]
  exact Finset.prod_le_prod
    (fun i _hi ↦ measureReal_nonneg) (fun i _hi ↦ hcoord i)

/-- Global path-event comparison obtained from the two-Gaussian coordinate
envelope.  The comparison constant is one because the finite mixture already
contains all multiplicative weights. -/
theorem measureReal_pi_barrier_le_expandedBarrier_gaussianEnvelope
    {n : ℕ} (rho : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (rho i)]
    (variance w : Fin n → ℝ≥0)
    {delta lower upper : Fin n → ℝ}
    (hdelta : ∀ i, 0 < delta i)
    (hcoord : ∀ z : Fin n → ℤ, ∀ i,
      (rho i).real
          (Ioc ((z i : ℝ) * delta i)
            ((z i : ℝ) * delta i + delta i)) ≤
        (1 + (w i : ℝ)) *
            (gaussianReal 0 (variance i)).real
              (Ioc ((z i : ℝ) * delta i)
                ((z i : ℝ) * delta i + delta i)) +
          (w i : ℝ) *
            (gaussianReal 0 1).real
              (Ioc ((z i : ℝ) * delta i)
                ((z i : ℝ) * delta i + delta i))) :
    (Measure.pi rho).real (harperPartialSumBarrierSet lower upper) ≤
      (harperGaussianEnvelopeMixture variance w).real
        (harperExpandedPartialSumBarrierSet lower upper delta) := by
  have hcell (z : Fin n → ℤ) :
      (Measure.pi rho).real (harperLatticeIocCell delta z) ≤
        (harperGaussianEnvelopeMixture variance w).real
          (harperLatticeIocCell delta z) := by
    simpa only [harperLatticeIocCell] using!
      measureReal_pi_coordinateCell_le_harperGaussianEnvelopeMixture
        rho variance w (fun i ↦ (z i : ℝ) * delta i) delta (hcoord z)
  simpa only [one_mul] using!
    measureReal_barrier_le_expandedBarrier_of_latticeCell
      (Measure.pi rho) (harperGaussianEnvelopeMixture variance w) 1
      (by norm_num) (delta := delta) (lower := lower) (upper := upper)
      hdelta (fun z ↦ by simpa only [one_mul] using! hcell z)

end Problem520
end Erdos
