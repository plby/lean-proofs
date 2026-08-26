import ErdosProblems.Erdos67.StationaryConditionalDilation
import ErdosProblems.Erdos67.StationaryResidues

/-!
# Correlations and the conditional-pair identity

The pair identities required by the entropy argument follow from the proved
stationarity and conditional dilation of the limiting model.
-/

open MeasureTheory

namespace Erdos67.StationaryModel

theorem integrable_configuration_continuous (Q : ProbabilityMeasure Configuration)
    (F : Configuration → ℝ) (hF : Continuous F) : Integrable F (Q : Measure Configuration) :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

theorem integral_shift_nat (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (n : ℕ) (F : Configuration → ℝ) (hF : Continuous F) :
    (∫ ω, F (shift (n : ℤ) ω) ∂(Q : Measure Configuration)) =
      ∫ ω, F ω ∂(Q : Measure Configuration) := by
  calc
    (∫ ω, F (shift (n : ℤ) ω) ∂(Q : Measure Configuration)) =
        ∫ ω, F ω ∂Measure.map (shift (n : ℤ)) (Q : Measure Configuration) :=
      (integral_map (continuous_shift _).measurable.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ ω, F ω ∂(Q : Measure Configuration) := by rw [shift_nat_preserving Q hQ n]

noncomputable def correlation (Q : ProbabilityMeasure Configuration) (h : ℤ) : ℝ :=
  ∫ ω, coordinate 0 ω * coordinate h ω ∂(Q : Measure Configuration)

theorem correlation_zero (Q : ProbabilityMeasure Configuration) : correlation Q 0 = 1 := by
  simp only [correlation, ← pow_two, sq_coordinate]
  simp

theorem abs_correlation_le_one (Q : ProbabilityMeasure Configuration) (h : ℤ) :
    |correlation Q h| ≤ 1 := by
  have hnorm := norm_integral_le_integral_norm
    (f := fun ω ↦ coordinate 0 ω * coordinate h ω) (μ := (Q : Measure Configuration))
  simpa [correlation, Real.norm_eq_abs, abs_mul, abs_coordinate] using hnorm

theorem integral_coordinate_pair_shift (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (n : ℕ) (h : ℤ) :
    (∫ ω, coordinate (n : ℤ) ω * coordinate ((n : ℤ) + h) ω
      ∂(Q : Measure Configuration)) = correlation Q h := by
  have ht := integral_shift_nat Q hQ n (fun ω ↦ coordinate 0 ω * coordinate h ω)
    ((continuous_coordinate 0).mul (continuous_coordinate h))
  simpa only [coordinate_shift, zero_add, add_comm h, correlation] using ht

theorem correlation_conditional_dilation (Q : ProbabilityMeasure Configuration)
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (d : ℕ+) (h : ℤ) :
    correlation Q h = (d.val : ℝ) *
      ∫ ω, residueZeroIndicator d ω * (coordinate 0 ω * coordinate ((d.val : ℤ) * h) ω)
        ∂(Q : Measure Configuration) := by
  let F : C((ℤ → Bool), ℝ) :=
    ⟨fun x ↦ signValue (x 0) * signValue (x h),
      ((continuous_of_discreteTopology : Continuous signValue).comp (continuous_apply 0)).mul
        ((continuous_of_discreteTopology : Continuous signValue).comp (continuous_apply h))⟩
  have hc := hCD d F
  simpa only [F, ContinuousMap.coe_mk, conditionalDilationTest, signDilation,
    mul_zero, coordinate, correlation] using hc

noncomputable def residueAtIndicator (d : ℕ+) (a : ZMod d.val) (ω : Configuration) : ℝ :=
  if ω.2 d = a then 1 else 0

theorem continuous_residueAtIndicator (d : ℕ+) (a : ZMod d.val) :
    Continuous (residueAtIndicator d a) := by
  have h : Continuous (fun z : ZMod d.val ↦ if z = a then (1 : ℝ) else 0) :=
    continuous_of_discreteTopology
  exact h.comp ((continuous_apply d).comp continuous_snd)

theorem residueZeroIndicator_shift_nat (d : ℕ+) (n : ℕ) (ω : Configuration) :
    residueZeroIndicator d (shift (n : ℤ) ω) = residueAtIndicator d (-(n : ZMod d.val)) ω := by
  simp [residueZeroIndicator, residueAtIndicator, shift, add_eq_zero_iff_eq_neg]

/-- The conditional-pair identity at an arbitrary positive starting coordinate. -/
theorem shifted_conditional_pair_identity (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (d : ℕ+) (n : ℕ) (h : ℤ) :
    (d.val : ℝ) *
      (∫ ω, residueAtIndicator d (-(n : ZMod d.val)) ω *
        (coordinate (n : ℤ) ω * coordinate ((n : ℤ) + (d.val : ℤ) * h) ω)
          ∂(Q : Measure Configuration)) = correlation Q h := by
  have hs := integral_shift_nat Q hQ n
    (fun ω ↦ residueZeroIndicator d ω *
      (coordinate 0 ω * coordinate ((d.val : ℤ) * h) ω))
    ((continuous_residueZeroIndicator d).mul
      ((continuous_coordinate 0).mul (continuous_coordinate ((d.val : ℤ) * h))))
  simp only [residueZeroIndicator_shift_nat, coordinate_shift, zero_add,
    add_comm ((d.val : ℤ) * h)] at hs
  rw [hs]
  exact (correlation_conditional_dilation Q hCD d h).symm

/-- Subtracting the ordinary pair expectation gives the centered identity used
as the mean input to the finite entropy estimate. -/
theorem centered_pair_identity (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (d : ℕ+) (n : ℕ) (h : ℤ) :
    (∫ ω, (coordinate (n : ℤ) ω * coordinate ((n : ℤ) + (d.val : ℤ) * h) ω) *
      (if ω.2 d = -(n : ZMod d.val) then (d.val : ℝ) - 1 else -1)
        ∂(Q : Measure Configuration)) = correlation Q h - correlation Q ((d.val : ℤ) * h) := by
  let A : Configuration → ℝ := fun ω ↦
    coordinate (n : ℤ) ω * coordinate ((n : ℤ) + (d.val : ℤ) * h) ω
  have hA : Continuous A :=
    (continuous_coordinate (n : ℤ)).mul (continuous_coordinate ((n : ℤ) + (d.val : ℤ) * h))
  have hpoint (ω : Configuration) :
      A ω * (if ω.2 d = -(n : ZMod d.val) then (d.val : ℝ) - 1 else -1) =
        (d.val : ℝ) * (residueAtIndicator d (-(n : ZMod d.val)) ω * A ω) - A ω := by
    unfold residueAtIndicator
    split_ifs <;> ring
  change (∫ ω, A ω * (if ω.2 d = -(n : ZMod d.val) then (d.val : ℝ) - 1 else -1)
    ∂(Q : Measure Configuration)) = _
  simp_rw [hpoint]
  have hleft : Integrable (fun ω ↦
      (d.val : ℝ) * (residueAtIndicator d (-(n : ZMod d.val)) ω * A ω))
      (Q : Measure Configuration) :=
    integrable_configuration_continuous Q _
      (continuous_const.mul ((continuous_residueAtIndicator d _).mul hA))
  rw [integral_sub hleft (integrable_configuration_continuous Q A hA), integral_const_mul]
  rw [shifted_conditional_pair_identity Q hQ hCD d n h,
    integral_coordinate_pair_shift Q hQ n ((d.val : ℤ) * h)]

end Erdos67.StationaryModel
