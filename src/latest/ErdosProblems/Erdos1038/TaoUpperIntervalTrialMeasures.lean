import ErdosProblems.Erdos1038.TaoUpperCasesTwoThreeAnalysis
import ErdosProblems.Erdos1038.TaoUpperDuality
import ErdosProblems.Erdos1038.WeakPotentialL1

/-!
# Genuine measures for Tao's interval-density trials

The notation `A 1_[a,b] dx` in Tao's Cases 2 and 3 denotes a nonnegative
Borel measure, not merely a formal integral.  This file defines those
measures, proves their logarithmic kernels integrable, and identifies their
measure-theoretic potentials with the scalar functions already formalized.
-/

open scoped ENNReal
open MeasureTheory Set

namespace Erdos1038

noncomputable section

/-- The nonnegative constant-density measure `A 1_[a,b] dx`. -/
def taoIntervalTrialMeasure (A a b : ℝ) : Measure ℝ :=
  ENNReal.ofReal A • volume.restrict (Icc a b)

/-- Tao's Case 2 trial `δ₀ + A 1_[a,M] dx`. -/
def taoCaseTwoTrialMeasure : Measure ℝ :=
  Measure.dirac 0 +
    taoIntervalTrialMeasure taoCaseTwoA taoCaseTwoLeftEndpoint taoUpperEdge

/-- Tao's Case 3 trial
`δ₀ + A 1_[a,M] dx + B 1_[b,M] dx + C δ_M`. -/
def taoCaseThreeTrialMeasure : Measure ℝ :=
  Measure.dirac 0 +
    taoIntervalTrialMeasure taoCaseThreeA taoCaseThreeLeftA taoUpperEdge +
    taoIntervalTrialMeasure taoCaseThreeB taoCaseThreeLeftB taoUpperEdge +
    ENNReal.ofReal taoCaseThreeC • Measure.dirac taoUpperEdge

instance instIsFiniteMeasureTaoIntervalTrialMeasure (A a b : ℝ) :
    IsFiniteMeasure (taoIntervalTrialMeasure A a b) :=
  (volume.restrict (Icc a b)).smul_finite (by simp)

instance instIsFiniteMeasureTaoCaseTwoTrialMeasure :
    IsFiniteMeasure taoCaseTwoTrialMeasure := by
  unfold taoCaseTwoTrialMeasure
  infer_instance

instance instIsFiniteMeasureTaoCaseThreeTrialMeasure :
    IsFiniteMeasure taoCaseThreeTrialMeasure := by
  letI : IsFiniteMeasure
      (ENNReal.ofReal taoCaseThreeC • Measure.dirac taoUpperEdge) :=
    (Measure.dirac taoUpperEdge).smul_finite (by simp)
  unfold taoCaseThreeTrialMeasure
  infer_instance

theorem taoIntervalTrialMeasure_singleton (A a b s : ℝ) :
    taoIntervalTrialMeasure A a b {s} = 0 := by
  simp [taoIntervalTrialMeasure]

theorem taoCaseTwoTrialMeasure_singleton {s : ℝ} (hs : s ≠ 0) :
    taoCaseTwoTrialMeasure {s} = 0 := by
  simp [taoCaseTwoTrialMeasure, hs, taoIntervalTrialMeasure]

theorem taoCaseThreeTrialMeasure_singleton {s : ℝ}
    (hs0 : s ≠ 0) (hsM : s ≠ taoUpperEdge) :
    taoCaseThreeTrialMeasure {s} = 0 := by
  simp [taoCaseThreeTrialMeasure, hs0, hsM,
    taoIntervalTrialMeasure]

theorem ae_taoIntervalTrialMeasure_mem (A a b : ℝ) :
    ∀ᵐ s ∂taoIntervalTrialMeasure A a b, s ∈ Icc a b := by
  exact Measure.ae_smul_measure
    (ae_restrict_mem measurableSet_Icc) _

/-- The Case 2 trial is concentrated on its atom at zero and density
interval. -/
theorem ae_taoCaseTwoTrialMeasure_mem :
    ∀ᵐ s ∂taoCaseTwoTrialMeasure,
      s = 0 ∨ s ∈ Icc taoCaseTwoLeftEndpoint taoUpperEdge := by
  rw [taoCaseTwoTrialMeasure, ae_add_measure_iff]
  constructor
  · simp
  · exact (ae_taoIntervalTrialMeasure_mem taoCaseTwoA
      taoCaseTwoLeftEndpoint taoUpperEdge).mono
        (fun s hs ↦ Or.inr hs)

/-- The two Case 3 density intervals and its upper atom all lie in the
single enclosing interval `[a,M]`. -/
theorem ae_taoCaseThreeTrialMeasure_mem :
    ∀ᵐ s ∂taoCaseThreeTrialMeasure,
      s = 0 ∨ s ∈ Icc taoCaseThreeLeftA taoUpperEdge := by
  rw [taoCaseThreeTrialMeasure, ae_add_measure_iff,
    ae_add_measure_iff, ae_add_measure_iff]
  constructor
  · constructor
    · constructor
      · simp
      · exact (ae_taoIntervalTrialMeasure_mem taoCaseThreeA
          taoCaseThreeLeftA taoUpperEdge).mono
            (fun s hs ↦ Or.inr hs)
    · exact (ae_taoIntervalTrialMeasure_mem taoCaseThreeB
        taoCaseThreeLeftB taoUpperEdge).mono (fun s hs ↦
          Or.inr ⟨by
            norm_num [taoCaseThreeLeftA, taoCaseThreeLeftB] at hs ⊢
            linarith, hs.2⟩)
  · apply Measure.ae_smul_measure
    refine (ae_dirac_iff (by measurability)).2 ?_
    refine Or.inr ⟨?_, le_rfl⟩
    unfold taoCaseThreeLeftA taoUpperEdge
    nlinarith [seven_fifths_lt_sqrt_two]

theorem integrable_log_sub_taoIntervalTrialMeasure
    {A a b r : ℝ} (hab : a ≤ b) :
    Integrable (fun x : ℝ ↦ Real.log |x - r|)
      (taoIntervalTrialMeasure A a b) := by
  have hbase : Integrable (fun x : ℝ ↦ Real.log |x - r|)
      (volume.restrict (Icc a b)) := by
    simpa only [logKernel] using!
      (integrableOn_logKernel_Icc (t := r) hab)
  exact hbase.smul_measure (by simp)

theorem integrable_log_t_sub_taoIntervalTrialMeasure
    {A a b t : ℝ} (hab : a ≤ b) :
    Integrable (fun x : ℝ ↦ Real.log |t - x|)
      (taoIntervalTrialMeasure A a b) := by
  refine (integrable_log_sub_taoIntervalTrialMeasure
    (A := A) (r := t) hab).congr ?_
  filter_upwards [] with x
  rw [abs_sub_comm]

theorem taoTrialMeasurePotential_dirac (a t : ℝ) :
    taoTrialMeasurePotential (Measure.dirac a) t =
      -Real.log |t - a| := by
  simp [taoTrialMeasurePotential]

theorem taoTrialMeasurePotential_interval
    {A a b t : ℝ} (hA : 0 ≤ A) (hab : a ≤ b) :
    taoTrialMeasurePotential (taoIntervalTrialMeasure A a b) t =
      A * (∫ s in a..b, -Real.log |t - s|) := by
  unfold taoTrialMeasurePotential taoIntervalTrialMeasure
  rw [integral_smul_measure, ENNReal.toReal_ofReal hA]
  have hset :
      (∫ s, Real.log |t - s| ∂volume.restrict (Icc a b)) =
        ∫ s in a..b, Real.log |t - s| := by
    rw [intervalIntegral.integral_of_le hab,
      ← integral_Icc_eq_integral_Ioc]
  rw [hset, intervalIntegral.integral_neg]
  simp only [smul_eq_mul]
  ring

theorem taoTrialMeasurePotential_add
    {nu mu : Measure ℝ} {t : ℝ}
    (hnu : Integrable (fun x : ℝ ↦ Real.log |t - x|) nu)
    (hmu : Integrable (fun x : ℝ ↦ Real.log |t - x|) mu) :
    taoTrialMeasurePotential (nu + mu) t =
      taoTrialMeasurePotential nu t + taoTrialMeasurePotential mu t := by
  unfold taoTrialMeasurePotential
  rw [integral_add_measure hnu hmu]
  ring

theorem taoCaseTwoA_nonnegative : 0 ≤ taoCaseTwoA := by
  norm_num [taoCaseTwoA]

theorem taoCaseThreeA_nonnegative : 0 ≤ taoCaseThreeA := by
  norm_num [taoCaseThreeA]

theorem taoCaseThreeB_nonnegative : 0 ≤ taoCaseThreeB := by
  norm_num [taoCaseThreeB]

theorem taoCaseThreeC_nonnegative : 0 ≤ taoCaseThreeC := by
  norm_num [taoCaseThreeC]

theorem tao_case_three_leftA_le_upperEdge :
    taoCaseThreeLeftA ≤ taoUpperEdge := by
  unfold taoCaseThreeLeftA taoUpperEdge
  nlinarith [seven_fifths_lt_sqrt_two]

theorem tao_case_three_leftB_le_upperEdge :
    taoCaseThreeLeftB ≤ taoUpperEdge := by
  unfold taoCaseThreeLeftB taoUpperEdge
  nlinarith [seven_fifths_lt_sqrt_two]

theorem integrable_log_t_sub_taoCaseTwoTrialMeasure (t : ℝ) :
    Integrable (fun x : ℝ ↦ Real.log |t - x|)
      taoCaseTwoTrialMeasure := by
  unfold taoCaseTwoTrialMeasure
  apply Integrable.add_measure
  · apply integrable_dirac
    finiteness
  · exact integrable_log_t_sub_taoIntervalTrialMeasure
      tao_case_two_leftEndpoint_le_upperEdge

theorem integrable_log_sub_taoCaseTwoTrialMeasure (r : ℝ) :
    Integrable (fun x : ℝ ↦ Real.log |x - r|)
      taoCaseTwoTrialMeasure := by
  refine (integrable_log_t_sub_taoCaseTwoTrialMeasure r).congr ?_
  filter_upwards [] with x
  rw [abs_sub_comm]

theorem integrable_log_t_sub_taoCaseThreeTrialMeasure (t : ℝ) :
    Integrable (fun x : ℝ ↦ Real.log |t - x|)
      taoCaseThreeTrialMeasure := by
  unfold taoCaseThreeTrialMeasure
  apply Integrable.add_measure
  · apply Integrable.add_measure
    · apply Integrable.add_measure
      · apply integrable_dirac
        finiteness
      · exact integrable_log_t_sub_taoIntervalTrialMeasure
          tao_case_three_leftA_le_upperEdge
    · exact integrable_log_t_sub_taoIntervalTrialMeasure
        tao_case_three_leftB_le_upperEdge
  · exact (integrable_dirac (by finiteness)).smul_measure (by simp)

theorem integrable_log_sub_taoCaseThreeTrialMeasure (r : ℝ) :
    Integrable (fun x : ℝ ↦ Real.log |x - r|)
      taoCaseThreeTrialMeasure := by
  refine (integrable_log_t_sub_taoCaseThreeTrialMeasure r).congr ?_
  filter_upwards [] with x
  rw [abs_sub_comm]

/-- The genuine Case 2 measure has exactly the scalar potential (2.5) on
positive inputs. -/
theorem taoCaseTwoTrialMeasure_potential {t : ℝ} (ht : 0 < t) :
    taoTrialMeasurePotential taoCaseTwoTrialMeasure t =
      taoCaseTwoPotential t := by
  have hdirac : Integrable (fun x : ℝ ↦ Real.log |t - x|)
      (Measure.dirac 0) := integrable_dirac (by finiteness)
  have hinterval := integrable_log_t_sub_taoIntervalTrialMeasure
    (A := taoCaseTwoA) (t := t) tao_case_two_leftEndpoint_le_upperEdge
  rw [taoCaseTwoTrialMeasure,
    taoTrialMeasurePotential_add hdirac hinterval,
    taoTrialMeasurePotential_dirac,
    taoTrialMeasurePotential_interval taoCaseTwoA_nonnegative
      tao_case_two_leftEndpoint_le_upperEdge]
  rw [sub_zero, abs_of_pos ht]
  rw [intervalDensityPotential_eq_primitive]
  rfl

/-- The genuine Case 3 measure has exactly the scalar potential (2.6) on
positive inputs. -/
theorem taoCaseThreeTrialMeasure_potential {t : ℝ} (ht : 0 < t) :
    taoTrialMeasurePotential taoCaseThreeTrialMeasure t =
      taoCaseThreePotential t := by
  let mu0 : Measure ℝ := Measure.dirac 0
  let muA : Measure ℝ :=
    taoIntervalTrialMeasure taoCaseThreeA taoCaseThreeLeftA taoUpperEdge
  let muB : Measure ℝ :=
    taoIntervalTrialMeasure taoCaseThreeB taoCaseThreeLeftB taoUpperEdge
  let muC : Measure ℝ :=
    ENNReal.ofReal taoCaseThreeC • Measure.dirac taoUpperEdge
  have h0 : Integrable (fun x : ℝ ↦ Real.log |t - x|) mu0 := by
    dsimp only [mu0]
    exact integrable_dirac (by finiteness)
  have hA : Integrable (fun x : ℝ ↦ Real.log |t - x|) muA := by
    dsimp only [muA]
    exact integrable_log_t_sub_taoIntervalTrialMeasure
      tao_case_three_leftA_le_upperEdge
  have hB : Integrable (fun x : ℝ ↦ Real.log |t - x|) muB := by
    dsimp only [muB]
    exact integrable_log_t_sub_taoIntervalTrialMeasure
      tao_case_three_leftB_le_upperEdge
  have hC : Integrable (fun x : ℝ ↦ Real.log |t - x|) muC := by
    dsimp only [muC]
    exact (integrable_dirac (by finiteness)).smul_measure (by simp)
  have hCpot : taoTrialMeasurePotential muC t =
      -taoCaseThreeC * Real.log |t - taoUpperEdge| := by
    dsimp only [muC]
    unfold taoTrialMeasurePotential
    rw [integral_smul_measure, ENNReal.toReal_ofReal
      taoCaseThreeC_nonnegative, integral_dirac]
    simp only [smul_eq_mul]
    ring
  change taoTrialMeasurePotential (((mu0 + muA) + muB) + muC) t = _
  rw [taoTrialMeasurePotential_add ((h0.add_measure hA).add_measure hB) hC,
    taoTrialMeasurePotential_add (h0.add_measure hA) hB,
    taoTrialMeasurePotential_add h0 hA,
    show taoTrialMeasurePotential mu0 t = -Real.log |t| by
      dsimp only [mu0]
      rw [taoTrialMeasurePotential_dirac, sub_zero],
    show taoTrialMeasurePotential muA t =
        taoCaseThreeA *
          (∫ s in taoCaseThreeLeftA..taoUpperEdge,
            -Real.log |t - s|) by
      dsimp only [muA]
      exact taoTrialMeasurePotential_interval taoCaseThreeA_nonnegative
        tao_case_three_leftA_le_upperEdge,
    show taoTrialMeasurePotential muB t =
        taoCaseThreeB *
          (∫ s in taoCaseThreeLeftB..taoUpperEdge,
            -Real.log |t - s|) by
      dsimp only [muB]
      exact taoTrialMeasurePotential_interval taoCaseThreeB_nonnegative
        tao_case_three_leftB_le_upperEdge,
    hCpot]
  rw [abs_of_pos ht, intervalDensityPotential_eq_primitive,
    intervalDensityPotential_eq_primitive, abs_sub_comm]
  unfold taoCaseThreePotential
  ring

end

end Erdos1038
