import ErdosProblems.Erdos520.HarperScheduledOffDiagonalBarrier

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem520

noncomputable section

/-!
# A sharp Gaussian ballot bound for a positive logarithmic boundary

The existing moving-barrier wrapper bounds a logarithmic boundary by its
largest value, which loses a factor `log n`.  Here we instead group time into
dyadic plateaus.  Across a doubling interval the boundary

`x + 8 log (k + 1)`

rises by less than `8`.  The killed affine moment therefore increases by at
most `8` times the survival probability at the preceding plateau.  Flat
Gaussian ballot estimates make these increments geometrically summable.

The first section supplies a small self-contained killed-walk API for a list
of pairs `(variance, boundaryIncrement)`.  It is deliberately separate from
the active scheduled-prefix and prime-number files.
-/

/-- One centered Gaussian variance together with the increase of the upper
barrier immediately before that step. -/
abbrev GaussianMovingStep := ℝ≥0 × ℝ

/-- Survival expressed in distance-to-the-current-boundary coordinates. -/
def gaussianMovingWalkSurvives :
    (steps : List GaussianMovingStep) →
      ℝ → (Fin steps.length → ℝ) → Prop
  | [], _x, _omega => True
  | step :: steps, x, omega =>
      omega 0 ≤ x + step.2 ∧
        gaussianMovingWalkSurvives steps (x + step.2 - omega 0)
          (fun i ↦ omega i.succ)

/-- The corresponding measurable finite-path event. -/
def gaussianMovingWalkSurvivalSet
    (steps : List GaussianMovingStep) (x : ℝ) :
    Set (Fin steps.length → ℝ) :=
  {omega | gaussianMovingWalkSurvives steps x omega}

/-- Product law of the centered Gaussian coordinates in a moving walk. -/
def gaussianMovingWalkMeasure (steps : List GaussianMovingStep) :
    Measure (Fin steps.length → ℝ) :=
  Measure.pi fun i ↦ gaussianReal 0 (steps.get i).1

instance (steps : List GaussianMovingStep) :
    IsProbabilityMeasure (gaussianMovingWalkMeasure steps) := by
  unfold gaussianMovingWalkMeasure
  infer_instance

/-- Terminal distance from the final moving boundary. -/
def gaussianMovingWalkTerminalDistance
    (steps : List GaussianMovingStep) (x : ℝ)
    (omega : Fin steps.length → ℝ) : ℝ :=
  x + (steps.map Prod.snd).sum - ∑ i, omega i

/-- A terminal payoff killed at the first boundary crossing. -/
def gaussianMovingWalkKilledPayoff
    (f : ℝ → ℝ) : (steps : List GaussianMovingStep) →
      ℝ → (Fin steps.length → ℝ) → ℝ
  | [], x, _omega => f x
  | step :: steps, x, omega =>
      if omega 0 ≤ x + step.2 then
        gaussianMovingWalkKilledPayoff f steps
          (x + step.2 - omega 0) (fun i ↦ omega i.succ)
      else 0

/-- Dynamic-programming form of the killed expectation. -/
noncomputable def gaussianMovingKilledExpectation :
    (steps : List GaussianMovingStep) → (ℝ → ℝ) → ℝ → ℝ
  | [], f, x => f x
  | step :: steps, f, x =>
      ∫ z in Iic (x + step.2),
        gaussianMovingKilledExpectation steps f (x + step.2 - z)
        ∂gaussianReal 0 step.1

@[simp] theorem gaussianMovingKilledExpectation_nil
    (f : ℝ → ℝ) (x : ℝ) :
    gaussianMovingKilledExpectation [] f x = f x := rfl

@[simp] theorem gaussianMovingKilledExpectation_cons
    (step : GaussianMovingStep) (steps : List GaussianMovingStep)
    (f : ℝ → ℝ) (x : ℝ) :
    gaussianMovingKilledExpectation (step :: steps) f x =
      ∫ z in Iic (x + step.2),
        gaussianMovingKilledExpectation steps f (x + step.2 - z)
        ∂gaussianReal 0 step.1 := rfl

theorem gaussianMovingKilledExpectation_append
    (us vs : List GaussianMovingStep) (f : ℝ → ℝ) (x : ℝ) :
    gaussianMovingKilledExpectation (us ++ vs) f x =
      gaussianMovingKilledExpectation us
        (gaussianMovingKilledExpectation vs f) x := by
  induction us generalizing x with
  | nil => simp
  | cons u us ih =>
      simp only [List.cons_append, gaussianMovingKilledExpectation_cons]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z ↦ ih (x + u.2 - z)

theorem measurableSet_gaussianMovingWalkSurvives_joint
    (steps : List GaussianMovingStep) :
    MeasurableSet {p : ℝ × (Fin steps.length → ℝ) |
      gaussianMovingWalkSurvives steps p.1 p.2} := by
  induction steps with
  | nil => simp [gaussianMovingWalkSurvives]
  | cons step steps ih =>
      simp only [gaussianMovingWalkSurvives]
      have hhead : Measurable
          (fun p : ℝ × (Fin (step :: steps).length → ℝ) ↦ p.2 0) :=
        (measurable_pi_apply 0).comp measurable_snd
      have htail : Measurable
          (fun p : ℝ × (Fin (step :: steps).length → ℝ) ↦
            fun i : Fin steps.length ↦ p.2 i.succ) :=
        measurable_pi_lambda _ fun i ↦
          (measurable_pi_apply i.succ).comp measurable_snd
      apply MeasurableSet.inter
      · exact measurableSet_le hhead (measurable_fst.add measurable_const)
      · exact ih.preimage
          (((measurable_fst.add measurable_const).sub hhead).prodMk htail)

theorem measurableSet_gaussianMovingWalkSurvivalSet
    (steps : List GaussianMovingStep) (x : ℝ) :
    MeasurableSet (gaussianMovingWalkSurvivalSet steps x) := by
  exact (measurableSet_gaussianMovingWalkSurvives_joint steps).preimage
    (measurable_const.prodMk measurable_id)

theorem measurable_gaussianMovingWalkKilledPayoff_joint
    {f : ℝ → ℝ} (hf : Measurable f) (steps : List GaussianMovingStep) :
    Measurable (fun p : ℝ × (Fin steps.length → ℝ) ↦
      gaussianMovingWalkKilledPayoff f steps p.1 p.2) := by
  induction steps with
  | nil =>
      simpa only [gaussianMovingWalkKilledPayoff] using! hf.comp measurable_fst
  | cons step steps ih =>
      simp only [gaussianMovingWalkKilledPayoff]
      have hhead : Measurable
          (fun p : ℝ × (Fin (step :: steps).length → ℝ) ↦ p.2 0) :=
        (measurable_pi_apply 0).comp measurable_snd
      have htail : Measurable
          (fun p : ℝ × (Fin (step :: steps).length → ℝ) ↦
            fun i : Fin steps.length ↦ p.2 i.succ) :=
        measurable_pi_lambda _ fun i ↦
          (measurable_pi_apply i.succ).comp measurable_snd
      apply Measurable.ite
      · exact measurableSet_le hhead (measurable_fst.add measurable_const)
      · exact ih.comp
          (((measurable_fst.add measurable_const).sub hhead).prodMk htail)
      · exact measurable_const

theorem measurable_gaussianMovingWalkKilledPayoff
    {f : ℝ → ℝ} (hf : Measurable f)
    (steps : List GaussianMovingStep) (x : ℝ) :
    Measurable (gaussianMovingWalkKilledPayoff f steps x) := by
  exact (measurable_gaussianMovingWalkKilledPayoff_joint hf steps).comp
    (measurable_const.prodMk measurable_id)

theorem gaussianMovingWalkKilledPayoff_eq_of_survives
    (f : ℝ → ℝ) (steps : List GaussianMovingStep) (x : ℝ)
    (omega : Fin steps.length → ℝ)
    (h : gaussianMovingWalkSurvives steps x omega) :
    gaussianMovingWalkKilledPayoff f steps x omega =
      f (gaussianMovingWalkTerminalDistance steps x omega) := by
  induction steps generalizing x with
  | nil => simp [gaussianMovingWalkKilledPayoff,
      gaussianMovingWalkTerminalDistance]
  | cons step steps ih =>
      rw [gaussianMovingWalkKilledPayoff, if_pos h.1,
        ih (x + step.2 - omega 0) (fun i ↦ omega i.succ) h.2]
      have hsum : (∑ i : Fin (step :: steps).length, omega i) =
          omega 0 + ∑ i : Fin steps.length, omega i.succ := by
        change (∑ i : Fin (steps.length + 1), omega i) = _
        exact Fin.sum_univ_succ omega
      simp only [gaussianMovingWalkTerminalDistance, List.map_cons,
        List.sum_cons]
      rw [hsum]
      ring

theorem gaussianMovingWalkKilledPayoff_eq_zero_of_not_survives
    (f : ℝ → ℝ) (steps : List GaussianMovingStep) (x : ℝ)
    (omega : Fin steps.length → ℝ)
    (h : ¬ gaussianMovingWalkSurvives steps x omega) :
    gaussianMovingWalkKilledPayoff f steps x omega = 0 := by
  induction steps generalizing x with
  | nil => exact (h trivial).elim
  | cons step steps ih =>
      rw [gaussianMovingWalkKilledPayoff]
      by_cases hfirst : omega 0 ≤ x + step.2
      · rw [if_pos hfirst]
        exact ih (x + step.2 - omega 0) (fun i ↦ omega i.succ)
          (fun htail ↦ h ⟨hfirst, htail⟩)
      · rw [if_neg hfirst]

theorem gaussianMovingWalkTerminalDistance_nonneg_of_survives
    (steps : List GaussianMovingStep) (x : ℝ)
    (omega : Fin steps.length → ℝ) (hx : 0 ≤ x)
    (hd : ∀ step ∈ steps, 0 ≤ step.2)
    (h : gaussianMovingWalkSurvives steps x omega) :
    0 ≤ gaussianMovingWalkTerminalDistance steps x omega := by
  induction steps generalizing x with
  | nil => simpa [gaussianMovingWalkTerminalDistance] using! hx
  | cons step steps ih =>
      have hstep : 0 ≤ step.2 := hd step (by simp)
      have htail : ∀ u ∈ steps, 0 ≤ u.2 := by
        intro u hu
        exact hd u (by simp [hu])
      have hrec := ih (x + step.2 - omega 0)
        (fun i ↦ omega i.succ) (sub_nonneg.mpr h.1) htail h.2
      have hsum : (∑ i : Fin (step :: steps).length, omega i) =
          omega 0 + ∑ i : Fin steps.length, omega i.succ := by
        change (∑ i : Fin (steps.length + 1), omega i) = _
        exact Fin.sum_univ_succ omega
      simp only [gaussianMovingWalkTerminalDistance, List.map_cons,
        List.sum_cons] at hrec ⊢
      rw [hsum]
      linarith

theorem abs_gaussianMovingWalkTerminalDistance_le
    (steps : List GaussianMovingStep) (x : ℝ)
    (omega : Fin steps.length → ℝ) :
    |gaussianMovingWalkTerminalDistance steps x omega| ≤
      |x| + |(steps.map Prod.snd).sum| + ∑ i, |omega i| := by
  unfold gaussianMovingWalkTerminalDistance
  calc
    |x + (steps.map Prod.snd).sum - ∑ i, omega i| ≤
        |x + (steps.map Prod.snd).sum| + |∑ i, omega i| :=
      abs_sub _ _
    _ ≤ (|x| + |(steps.map Prod.snd).sum|) + |∑ i, omega i| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ |x| + |(steps.map Prod.snd).sum| + ∑ i, |omega i| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _

theorem norm_gaussianMovingWalkKilledPayoff_le
    {f : ℝ → ℝ} {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hf : ∀ y, ‖f y‖ ≤ A * |y| + C)
    (steps : List GaussianMovingStep) (x : ℝ)
    (omega : Fin steps.length → ℝ) :
    ‖gaussianMovingWalkKilledPayoff f steps x omega‖ ≤
      A * (|x| + |(steps.map Prod.snd).sum| + ∑ i, |omega i|) + C := by
  by_cases h : gaussianMovingWalkSurvives steps x omega
  · rw [gaussianMovingWalkKilledPayoff_eq_of_survives f steps x omega h]
    have hmul := mul_le_mul_of_nonneg_left
      (abs_gaussianMovingWalkTerminalDistance_le steps x omega) hA
    exact (hf _).trans (by linarith)
  · rw [gaussianMovingWalkKilledPayoff_eq_zero_of_not_survives
      f steps x omega h, norm_zero]
    positivity

private theorem integrable_id_gaussianReal_movingVariance (v : ℝ≥0) :
    Integrable (fun z : ℝ ↦ z) (gaussianReal 0 v) :=
  memLp_one_iff_integrable.mp
    (by simpa only [id_eq] using!
      (memLp_id_gaussianReal' (μ := 0) (v := v) 1 (by norm_num)))

theorem integrable_gaussianMovingWalkKilledPayoff
    {f : ℝ → ℝ} (hmeas : Measurable f)
    {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hf : ∀ y, ‖f y‖ ≤ A * |y| + C)
    (steps : List GaussianMovingStep) (x : ℝ) :
    Integrable (gaussianMovingWalkKilledPayoff f steps x)
      (gaussianMovingWalkMeasure steps) := by
  have heval (i : Fin steps.length) :
      Integrable (fun omega : Fin steps.length → ℝ ↦ omega i)
        (gaussianMovingWalkMeasure steps) := by
    unfold gaussianMovingWalkMeasure
    exact integrable_eval
      (integrable_id_gaussianReal_movingVariance (steps.get i).1)
  have habs (i : Fin steps.length) :
      Integrable (fun omega : Fin steps.length → ℝ ↦ |omega i|)
        (gaussianMovingWalkMeasure steps) := by
    simpa only [Real.norm_eq_abs] using! (heval i).norm
  have hmajorant : Integrable
      (fun omega : Fin steps.length → ℝ ↦
        A * (|x| + |(steps.map Prod.snd).sum| + ∑ i, |omega i|) + C)
      (gaussianMovingWalkMeasure steps) := by
    fun_prop
  exact hmajorant.mono'
    (measurable_gaussianMovingWalkKilledPayoff hmeas steps x).aestronglyMeasurable
    (Filter.Eventually.of_forall
      (norm_gaussianMovingWalkKilledPayoff_le hA hC hf steps x))

/-- The dynamic recursion is exactly the expectation of the killed payoff
on the finite Gaussian product space. -/
theorem integral_gaussianMovingWalkKilledPayoff_eq
    {f : ℝ → ℝ} (hmeas : Measurable f)
    {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hf : ∀ y, ‖f y‖ ≤ A * |y| + C)
    (steps : List GaussianMovingStep) (x : ℝ) :
    (∫ omega : Fin steps.length → ℝ,
        gaussianMovingWalkKilledPayoff f steps x omega
        ∂gaussianMovingWalkMeasure steps) =
      gaussianMovingKilledExpectation steps f x := by
  induction steps generalizing x with
  | nil =>
      simp [gaussianMovingWalkKilledPayoff,
        gaussianMovingKilledExpectation, gaussianMovingWalkMeasure]
  | cons step steps ih =>
      change (∫ omega : Fin (steps.length + 1) → ℝ,
          gaussianMovingWalkKilledPayoff f (step :: steps) x omega
          ∂gaussianMovingWalkMeasure (step :: steps)) =
        gaussianMovingKilledExpectation (step :: steps) f x
      let gamma : Measure ℝ := gaussianReal 0 step.1
      let Ptail : Measure (Fin steps.length → ℝ) :=
        gaussianMovingWalkMeasure steps
      let e := MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (steps.length + 1) ↦ ℝ) 0
      have hmp0 :=
        (measurePreserving_piFinSuccAbove
          (fun i : Fin (steps.length + 1) ↦
            gaussianReal 0 ((step :: steps).get i).1) 0).symm
      have hmp : MeasurePreserving e.symm
          (gamma.prod Ptail) (gaussianMovingWalkMeasure (step :: steps)) := by
        simpa only [gamma, Ptail, gaussianMovingWalkMeasure,
          List.length_cons, List.get_eq_getElem] using! hmp0
      have he_symm (p : ℝ × (Fin steps.length → ℝ)) :
          e.symm p = Fin.cons p.1 p.2 := by
        ext i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv]
        · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv, Fin.zero_succAbove]
      have hint : Integrable
          (fun p : ℝ × (Fin steps.length → ℝ) ↦
            gaussianMovingWalkKilledPayoff f (step :: steps) x (e.symm p))
          (gamma.prod Ptail) := by
        exact hmp.integrable_comp_of_integrable
          (by simpa only [List.length_cons] using!
            (integrable_gaussianMovingWalkKilledPayoff
              (f := f) (A := A) (C := C)
              hmeas hA hC hf (step :: steps) x))
      rw [← hmp.integral_comp']
      rw [integral_prod _ hint]
      simp_rw [he_symm]
      simp only [Fin.cons_zero, Fin.cons_succ,
        gaussianMovingWalkKilledPayoff]
      rw [gaussianMovingKilledExpectation_cons]
      rw [← integral_indicator measurableSet_Iic]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z ↦ by
        by_cases hz : z ≤ x + step.2
        · simp only [hz, if_true, Set.mem_Iic, Set.indicator_of_mem]
          simpa only [Ptail] using! ih (x + step.2 - z)
        · have hnot : z ∉ Iic (x + step.2) := hz
          simp only [hz, if_false, integral_zero,
            Set.indicator_of_notMem hnot]

theorem measurable_gaussianMovingKilledExpectation
    {f : ℝ → ℝ} (hmeas : Measurable f)
    {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hf : ∀ y, ‖f y‖ ≤ A * |y| + C)
    (steps : List GaussianMovingStep) :
    Measurable (gaussianMovingKilledExpectation steps f) := by
  have hjoint := measurable_gaussianMovingWalkKilledPayoff_joint hmeas steps
  have hintMeas : Measurable (fun x : ℝ ↦
      ∫ omega : Fin steps.length → ℝ,
        gaussianMovingWalkKilledPayoff f steps x omega
        ∂gaussianMovingWalkMeasure steps) :=
    hjoint.stronglyMeasurable.integral_prod_right.measurable
  convert! hintMeas using 1
  funext x
  exact (integral_gaussianMovingWalkKilledPayoff_eq
    hmeas hA hC hf steps x).symm

/-! ## Probability and affine-moment forms -/

/-- Survival probability in distance coordinates. -/
noncomputable def gaussianMovingWalkSurvivalProbability
    (steps : List GaussianMovingStep) (x : ℝ) : ℝ :=
  gaussianMovingKilledExpectation steps (fun _ ↦ 1) x

theorem measurable_gaussianMovingWalkSurvivalProbability
    (steps : List GaussianMovingStep) :
    Measurable (gaussianMovingWalkSurvivalProbability steps) := by
  unfold gaussianMovingWalkSurvivalProbability
  apply measurable_gaussianMovingKilledExpectation
    (f := fun _ : ℝ ↦ (1 : ℝ)) measurable_const
    (A := 0) (C := 1) (by norm_num) (by norm_num)
  intro y
  norm_num

theorem gaussianMovingWalkSurvivalProbability_eq_measureReal
    (steps : List GaussianMovingStep) (x : ℝ) :
    gaussianMovingWalkSurvivalProbability steps x =
      (gaussianMovingWalkMeasure steps).real
        (gaussianMovingWalkSurvivalSet steps x) := by
  have heq := integral_gaussianMovingWalkKilledPayoff_eq
    (f := fun _ : ℝ ↦ (1 : ℝ)) measurable_const
    (A := 0) (C := 1) (by norm_num) (by norm_num)
    (fun y ↦ by norm_num) steps x
  rw [gaussianMovingWalkSurvivalProbability, ← heq]
  calc
    (∫ omega : Fin steps.length → ℝ,
        gaussianMovingWalkKilledPayoff (fun _ : ℝ ↦ (1 : ℝ))
          steps x omega ∂gaussianMovingWalkMeasure steps) =
        ∫ _omega in gaussianMovingWalkSurvivalSet steps x, (1 : ℝ)
          ∂gaussianMovingWalkMeasure steps := by
      rw [← integral_indicator
        (measurableSet_gaussianMovingWalkSurvivalSet steps x)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun omega ↦ by
        by_cases h : gaussianMovingWalkSurvives steps x omega
        · have hmem : omega ∈ gaussianMovingWalkSurvivalSet steps x := h
          rw [gaussianMovingWalkKilledPayoff_eq_of_survives
            (fun _ : ℝ ↦ (1 : ℝ)) steps x omega h,
            Set.indicator_of_mem hmem]
        · have hmem : omega ∉ gaussianMovingWalkSurvivalSet steps x := h
          rw [gaussianMovingWalkKilledPayoff_eq_zero_of_not_survives
            (fun _ : ℝ ↦ (1 : ℝ)) steps x omega h,
            Set.indicator_of_notMem hmem]
    _ = (gaussianMovingWalkMeasure steps).real
        (gaussianMovingWalkSurvivalSet steps x) := by simp

theorem gaussianMovingWalkSurvivalProbability_nonneg_le_one
    (steps : List GaussianMovingStep) (x : ℝ) :
    0 ≤ gaussianMovingWalkSurvivalProbability steps x ∧
      gaussianMovingWalkSurvivalProbability steps x ≤ 1 := by
  rw [gaussianMovingWalkSurvivalProbability_eq_measureReal]
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

/-- Killed expectation of final distance plus two. -/
noncomputable def gaussianMovingWalkAffineMoment
    (steps : List GaussianMovingStep) (x : ℝ) : ℝ :=
  gaussianMovingKilledExpectation steps (fun y ↦ y + 2) x

private theorem norm_add_two_le (y : ℝ) :
    ‖y + 2‖ ≤ 1 * |y| + 2 := by
  rw [Real.norm_eq_abs, one_mul]
  simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using!
    abs_add_le y 2

theorem measurable_gaussianMovingWalkAffineMoment
    (steps : List GaussianMovingStep) :
    Measurable (gaussianMovingWalkAffineMoment steps) := by
  unfold gaussianMovingWalkAffineMoment
  exact measurable_gaussianMovingKilledExpectation
    (f := fun y : ℝ ↦ y + 2) (by fun_prop)
    (A := 1) (C := 2) (by norm_num) (by norm_num)
    norm_add_two_le steps

theorem integralOn_gaussianMovingWalkSurvival_terminal_eq
    (steps : List GaussianMovingStep) (x : ℝ) :
    (∫ omega in gaussianMovingWalkSurvivalSet steps x,
        (gaussianMovingWalkTerminalDistance steps x omega + 2)
        ∂gaussianMovingWalkMeasure steps) =
      gaussianMovingWalkAffineMoment steps x := by
  have heq := integral_gaussianMovingWalkKilledPayoff_eq
    (f := fun y : ℝ ↦ y + 2) (by fun_prop)
    (A := 1) (C := 2) (by norm_num) (by norm_num)
    norm_add_two_le steps x
  rw [gaussianMovingWalkAffineMoment, ← heq]
  rw [← integral_indicator
    (measurableSet_gaussianMovingWalkSurvivalSet steps x)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun omega ↦ by
    by_cases h : gaussianMovingWalkSurvives steps x omega
    · have hmem : omega ∈ gaussianMovingWalkSurvivalSet steps x := h
      rw [Set.indicator_of_mem hmem,
        gaussianMovingWalkKilledPayoff_eq_of_survives
          (fun y : ℝ ↦ y + 2) steps x omega h]
    · have hmem : omega ∉ gaussianMovingWalkSurvivalSet steps x := h
      rw [Set.indicator_of_notMem hmem,
        gaussianMovingWalkKilledPayoff_eq_zero_of_not_survives
          (fun y : ℝ ↦ y + 2) steps x omega h]

theorem gaussianMovingWalkAffineMoment_nonneg
    (steps : List GaussianMovingStep) {x : ℝ} (hx : 0 ≤ x)
    (hd : ∀ step ∈ steps, 0 ≤ step.2) :
    0 ≤ gaussianMovingWalkAffineMoment steps x := by
  rw [← integralOn_gaussianMovingWalkSurvival_terminal_eq]
  apply integral_nonneg_of_ae
  exact (ae_restrict_mem
    (measurableSet_gaussianMovingWalkSurvivalSet steps x)).mono
      fun omega hmem ↦ by
        have hD := gaussianMovingWalkTerminalDistance_nonneg_of_survives
          steps x omega hx hd hmem
        exact add_nonneg hD (by norm_num)

/-- A whole moving segment is controlled by putting all of its nonnegative
boundary increase at the start. -/
theorem gaussianMovingWalkAffineMoment_le_totalIncrement
    (steps : List GaussianMovingStep) {x : ℝ} (hx : 0 ≤ x)
    (hd : ∀ step ∈ steps, 0 ≤ step.2)
    (hvar : ∀ step ∈ steps,
      step.1 ≠ 0 ∧ Real.sqrt (step.1 : ℝ) ≤ 1) :
    gaussianMovingWalkAffineMoment steps x ≤
      x + (steps.map Prod.snd).sum + 2 := by
  induction steps generalizing x with
  | nil => simp [gaussianMovingWalkAffineMoment,
      gaussianMovingKilledExpectation]
  | cons step steps ih =>
      have hd0 : 0 ≤ step.2 := hd step (by simp)
      have hdtail : ∀ u ∈ steps, 0 ≤ u.2 := by
        intro u hu
        exact hd u (by simp [hu])
      have hv0 : step.1 ≠ 0 := (hvar step (by simp)).1
      have hvone : Real.sqrt (step.1 : ℝ) ≤ 1 :=
        (hvar step (by simp)).2
      have hvtail : ∀ u ∈ steps,
          u.1 ≠ 0 ∧ Real.sqrt (u.1 : ℝ) ≤ 1 := by
        intro u hu
        exact hvar u (by simp [hu])
      let X : ℝ := x + step.2
      let L : ℝ := ((steps.map Prod.snd).sum + 2) / 2
      have hX : 0 ≤ X := by dsimp [X]; positivity
      have hsum0 : 0 ≤ (steps.map Prod.snd).sum := by
        apply List.sum_nonneg
        intro d hdmem
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hdmem
        exact hdtail u hu
      have hL : 1 ≤ L := by dsimp [L]; linarith
      have hvL : Real.sqrt (step.1 : ℝ) ≤ L := hvone.trans hL
      have hnonneg : 0 ≤ᵐ[(gaussianReal 0 step.1).restrict (Iic X)]
          fun z ↦ gaussianMovingWalkAffineMoment steps (X - z) := by
        exact (ae_restrict_mem measurableSet_Iic).mono fun z hz ↦
          gaussianMovingWalkAffineMoment_nonneg steps
            (sub_nonneg.mpr hz) hdtail
      have hle : (fun z ↦ gaussianMovingWalkAffineMoment steps (X - z)) ≤ᵐ[
          (gaussianReal 0 step.1).restrict (Iic X)]
          fun z ↦ X - z + 2 * L := by
        exact (ae_restrict_mem measurableSet_Iic).mono fun z hz ↦ by
          have htail := ih (x := X - z) (sub_nonneg.mpr hz) hdtail hvtail
          dsimp only [L]
          linarith
      have hright : IntegrableOn (fun z ↦ X - z + 2 * L) (Iic X)
          (gaussianReal 0 step.1) := by
        exact (((integrable_const X).sub
          (integrable_id_gaussianReal_movingVariance step.1)).add
            (integrable_const (2 * L))).integrableOn
      unfold gaussianMovingWalkAffineMoment
      rw [gaussianMovingKilledExpectation_cons]
      calc
        (∫ z in Iic (x + step.2),
            gaussianMovingKilledExpectation steps (fun y ↦ y + 2)
              (x + step.2 - z) ∂gaussianReal 0 step.1) =
            ∫ z in Iic X,
              gaussianMovingWalkAffineMoment steps (X - z)
              ∂gaussianReal 0 step.1 := by rfl
        _ ≤ ∫ z in Iic X, (X - z + 2 * L)
              ∂gaussianReal 0 step.1 :=
          integral_mono_of_nonneg hnonneg hright hle
        _ ≤ X + 2 * L :=
          integral_Iic_gaussianReal_barrierPotential_le_of_sqrt_le
            hv0 hX hvL
        _ = x + ((step :: steps).map Prod.snd).sum + 2 := by
          simp only [List.map_cons, List.sum_cons]
          dsimp only [X, L]
          ring

/-! ## Conditioning and comparison with a flat final block -/

theorem integralOn_gaussianMovingWalkSurvival_eq_killedExpectation
    {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ y, ‖f y‖ ≤ C) (steps : List GaussianMovingStep) (x : ℝ) :
    (∫ omega in gaussianMovingWalkSurvivalSet steps x,
        f (gaussianMovingWalkTerminalDistance steps x omega)
        ∂gaussianMovingWalkMeasure steps) =
      gaussianMovingKilledExpectation steps f x := by
  have heq := integral_gaussianMovingWalkKilledPayoff_eq
    (f := f) hf (A := 0) (C := C) (by norm_num) hC0
    (fun y ↦ by simpa using! hC y) steps x
  rw [← heq]
  rw [← integral_indicator
    (measurableSet_gaussianMovingWalkSurvivalSet steps x)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun omega ↦ by
    by_cases h : gaussianMovingWalkSurvives steps x omega
    · have hmem : omega ∈ gaussianMovingWalkSurvivalSet steps x := h
      rw [Set.indicator_of_mem hmem,
        gaussianMovingWalkKilledPayoff_eq_of_survives f steps x omega h]
    · have hmem : omega ∉ gaussianMovingWalkSurvivalSet steps x := h
      rw [Set.indicator_of_notMem hmem,
        gaussianMovingWalkKilledPayoff_eq_zero_of_not_survives
          f steps x omega h]

theorem gaussianMovingWalkSurvivalProbability_append_eq_integralOn
    (us vs : List GaussianMovingStep) (x : ℝ) :
    gaussianMovingWalkSurvivalProbability (us ++ vs) x =
      ∫ omega in gaussianMovingWalkSurvivalSet us x,
        gaussianMovingWalkSurvivalProbability vs
          (gaussianMovingWalkTerminalDistance us x omega)
        ∂gaussianMovingWalkMeasure us := by
  rw [gaussianMovingWalkSurvivalProbability,
    gaussianMovingKilledExpectation_append]
  symm
  apply integralOn_gaussianMovingWalkSurvival_eq_killedExpectation
    (measurable_gaussianMovingWalkSurvivalProbability vs)
    (C := 1) (by norm_num)
  intro y
  rw [Real.norm_eq_abs, abs_of_nonneg
    (gaussianMovingWalkSurvivalProbability_nonneg_le_one vs y).1]
  exact (gaussianMovingWalkSurvivalProbability_nonneg_le_one vs y).2

/-- A moving boundary can be flattened by paying its remaining total
increase at the start of the segment. -/
theorem gaussianMovingWalkSurvives_to_flat
    (steps : List GaussianMovingStep) (x : ℝ)
    (omega : Fin steps.length → ℝ)
    (hd : ∀ step ∈ steps, 0 ≤ step.2)
    (h : gaussianMovingWalkSurvives steps x omega) :
    gaussianWalkSurvives steps.length
      (x + (steps.map Prod.snd).sum) omega := by
  induction steps generalizing x with
  | nil => trivial
  | cons step steps ih =>
      have hd0 : 0 ≤ step.2 := hd step (by simp)
      have hdtail : ∀ u ∈ steps, 0 ≤ u.2 := by
        intro u hu
        exact hd u (by simp [hu])
      have hsum0 : 0 ≤ (steps.map Prod.snd).sum := by
        apply List.sum_nonneg
        intro d hdmem
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hdmem
        exact hdtail u hu
      simp only [List.length_cons, gaussianWalkSurvives]
      constructor
      · simp only [List.map_cons, List.sum_cons]
        linarith [h.1]
      · have htail := ih (x + step.2 - omega 0)
          (fun i ↦ omega i.succ) hdtail h.2
        convert! htail using 1 <;>
          simp only [List.map_cons, List.sum_cons] <;> ring

theorem gaussianMovingWalkSurvivalProbability_le_flat
    (steps : List GaussianMovingStep) (hne : steps ≠ [])
    {x : ℝ} (hx : 0 ≤ x)
    (hd : ∀ step ∈ steps, 0 ≤ step.2)
    (hlower : ∀ step ∈ steps, (1 / 4 : ℝ≥0) ≤ step.1)
    (hupper : ∀ step ∈ steps, Real.sqrt (step.1 : ℝ) ≤ 1) :
    gaussianMovingWalkSurvivalProbability steps x ≤
      64 * (x + (steps.map Prod.snd).sum + 2) /
        Real.sqrt (steps.length : ℝ) := by
  rw [gaussianMovingWalkSurvivalProbability_eq_measureReal]
  have hsum0 : 0 ≤ (steps.map Prod.snd).sum := by
    apply List.sum_nonneg
    intro d hdmem
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hdmem
    exact hd u hu
  calc
    (gaussianMovingWalkMeasure steps).real
        (gaussianMovingWalkSurvivalSet steps x) ≤
        (gaussianMovingWalkMeasure steps).real
          (gaussianWalkSurvivalSet steps.length
            (x + (steps.map Prod.snd).sum)) := by
      refine measureReal_mono ?_ (measure_ne_top
        (gaussianMovingWalkMeasure steps) _)
      intro omega homega
      exact gaussianMovingWalkSurvives_to_flat steps x omega hd homega
    _ ≤ 64 * (x + (steps.map Prod.snd).sum + 2) /
          Real.sqrt (steps.length : ℝ) := by
      unfold gaussianMovingWalkMeasure
      have hmain :=
        gaussianVarianceWalk_probability_le_fin_of_lower_of_sqrt_le
          (1 / 4 : ℝ≥0) (by norm_num) steps.length
          (List.length_pos_of_ne_nil hne) (fun i ↦ (steps.get i).1)
          (x := x + (steps.map Prod.snd).sum) (by positivity)
          (fun i ↦ hlower (steps.get i) (List.get_mem steps i))
          (fun i ↦ hupper (steps.get i) (List.get_mem steps i))
      convert! hmain using 1 <;> norm_num

/-- Appending a segment can increase the killed affine moment by at most
the total boundary increase of that segment times the preceding survival
probability.  This is the renewal inequality used on dyadic plateaus. -/
theorem gaussianMovingWalkAffineMoment_append_le
    (us vs : List GaussianMovingStep) {x : ℝ} (hx : 0 ≤ x)
    (hdu : ∀ step ∈ us, 0 ≤ step.2)
    (hdv : ∀ step ∈ vs, 0 ≤ step.2)
    (hvaru : ∀ step ∈ us,
      step.1 ≠ 0 ∧ Real.sqrt (step.1 : ℝ) ≤ 1)
    (hvarv : ∀ step ∈ vs,
      step.1 ≠ 0 ∧ Real.sqrt (step.1 : ℝ) ≤ 1) :
    gaussianMovingWalkAffineMoment (us ++ vs) x ≤
      gaussianMovingWalkAffineMoment us x +
        (vs.map Prod.snd).sum *
          gaussianMovingWalkSurvivalProbability us x := by
  induction us generalizing x with
  | nil =>
      have hmain := gaussianMovingWalkAffineMoment_le_totalIncrement
        vs hx hdv hvarv
      convert! hmain using 1 <;>
        simp [gaussianMovingWalkAffineMoment,
          gaussianMovingWalkSurvivalProbability,
          gaussianMovingKilledExpectation] <;> ring
  | cons u us ih =>
      have hdu0 : 0 ≤ u.2 := hdu u (by simp)
      have hdutail : ∀ step ∈ us, 0 ≤ step.2 := by
        intro step hstep
        exact hdu step (by simp [hstep])
      have hvarutail : ∀ step ∈ us,
          step.1 ≠ 0 ∧ Real.sqrt (step.1 : ℝ) ≤ 1 := by
        intro step hstep
        exact hvaru step (by simp [hstep])
      let X : ℝ := x + u.2
      let D : ℝ := (vs.map Prod.snd).sum
      have hX : 0 ≤ X := by dsimp only [X]; positivity
      have hD : 0 ≤ D := by
        dsimp only [D]
        apply List.sum_nonneg
        intro d hdmem
        obtain ⟨step, hstep, rfl⟩ := List.mem_map.mp hdmem
        exact hdv step hstep
      have hdappend : ∀ step ∈ us ++ vs, 0 ≤ step.2 := by
        simpa only [List.forall_mem_append] using! ⟨hdutail, hdv⟩
      have hvarappend : ∀ step ∈ us ++ vs,
          step.1 ≠ 0 ∧ Real.sqrt (step.1 : ℝ) ≤ 1 := by
        simpa only [List.forall_mem_append] using! ⟨hvarutail, hvarv⟩
      have hleftNonneg : 0 ≤ᵐ[(gaussianReal 0 u.1).restrict (Iic X)]
          fun z ↦ gaussianMovingWalkAffineMoment (us ++ vs) (X - z) := by
        exact (ae_restrict_mem measurableSet_Iic).mono fun z hz ↦
          gaussianMovingWalkAffineMoment_nonneg (us ++ vs)
            (sub_nonneg.mpr hz) hdappend
      have hle :
          (fun z ↦ gaussianMovingWalkAffineMoment (us ++ vs) (X - z))
            ≤ᵐ[(gaussianReal 0 u.1).restrict (Iic X)]
          fun z ↦ gaussianMovingWalkAffineMoment us (X - z) +
            D * gaussianMovingWalkSurvivalProbability us (X - z) := by
        exact (ae_restrict_mem measurableSet_Iic).mono fun z hz ↦ by
          simpa only [D] using! ih (x := X - z) (sub_nonneg.mpr hz)
            hdutail hvarutail
      have hM : IntegrableOn
          (fun z ↦ gaussianMovingWalkAffineMoment us (X - z))
          (Iic X) (gaussianReal 0 u.1) := by
        have hmajor : IntegrableOn
            (fun z ↦ X - z + (us.map Prod.snd).sum + 2)
            (Iic X) (gaussianReal 0 u.1) := by
          have hfull : Integrable
              (fun z ↦ X - z + (us.map Prod.snd).sum + 2)
              (gaussianReal 0 u.1) := by
            have hfull' := ((integrable_const X).sub
              (integrable_id_gaussianReal_movingVariance u.1)).add
                (integrable_const ((us.map Prod.snd).sum + 2))
            convert! hfull' using 1
            funext z
            simp only [Pi.add_apply, Pi.sub_apply]
            ring
          exact hfull.integrableOn
        refine hmajor.mono'
          ((measurable_gaussianMovingWalkAffineMoment us).comp
            (measurable_const.sub measurable_id)).aestronglyMeasurable ?_
        exact (ae_restrict_mem measurableSet_Iic).mono fun z hz ↦ by
          have hnonneg := gaussianMovingWalkAffineMoment_nonneg us
            (sub_nonneg.mpr hz) hdutail
          rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
          exact gaussianMovingWalkAffineMoment_le_totalIncrement us
            (sub_nonneg.mpr hz) hdutail hvarutail
      have hP : IntegrableOn
          (fun z ↦ gaussianMovingWalkSurvivalProbability us (X - z))
          (Iic X) (gaussianReal 0 u.1) := by
        refine (integrable_const (1 : ℝ)).integrableOn.mono'
          ((measurable_gaussianMovingWalkSurvivalProbability us).comp
            (measurable_const.sub measurable_id)).aestronglyMeasurable ?_
        exact Filter.Eventually.of_forall fun z ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg
            (gaussianMovingWalkSurvivalProbability_nonneg_le_one us
              (X - z)).1]
          exact (gaussianMovingWalkSurvivalProbability_nonneg_le_one us
            (X - z)).2
      have hDP : IntegrableOn
          (fun z ↦ D * gaussianMovingWalkSurvivalProbability us (X - z))
          (Iic X) (gaussianReal 0 u.1) := hP.const_mul D
      calc
        gaussianMovingWalkAffineMoment ((u :: us) ++ vs) x =
            ∫ z in Iic X,
              gaussianMovingWalkAffineMoment (us ++ vs) (X - z)
              ∂gaussianReal 0 u.1 := by rfl
        _ ≤ ∫ z in Iic X,
              (gaussianMovingWalkAffineMoment us (X - z) +
                D * gaussianMovingWalkSurvivalProbability us (X - z))
              ∂gaussianReal 0 u.1 :=
          integral_mono_of_nonneg hleftNonneg (hM.add hDP) hle
        _ = gaussianMovingWalkAffineMoment (u :: us) x +
              D * gaussianMovingWalkSurvivalProbability (u :: us) x := by
          rw [integral_add hM hDP, integral_const_mul]
          rfl
        _ = gaussianMovingWalkAffineMoment (u :: us) x +
              (vs.map Prod.snd).sum *
                gaussianMovingWalkSurvivalProbability (u :: us) x := by
          rfl

theorem integrable_gaussianMovingWalkTerminalDistance
    (steps : List GaussianMovingStep) (x : ℝ) :
    Integrable (gaussianMovingWalkTerminalDistance steps x)
      (gaussianMovingWalkMeasure steps) := by
  have heval (i : Fin steps.length) :
      Integrable (fun omega : Fin steps.length → ℝ ↦ omega i)
        (gaussianMovingWalkMeasure steps) := by
    unfold gaussianMovingWalkMeasure
    exact integrable_eval
      (integrable_id_gaussianReal_movingVariance (steps.get i).1)
  have hsum : Integrable (fun omega : Fin steps.length → ℝ ↦
      ∑ i, omega i) (gaussianMovingWalkMeasure steps) := by
    simpa only [Finset.sum_apply] using!
      (integrable_finset_sum Finset.univ (fun i _hi ↦ heval i))
  unfold gaussianMovingWalkTerminalDistance
  exact (integrable_const (x + (steps.map Prod.snd).sum)).sub hsum

/-- A last moving block is paid for by the affine moment accumulated at its
left endpoint and the total rise within that block. -/
theorem gaussianMovingWalkSurvivalProbability_append_le_affine
    (us vs : List GaussianMovingStep) (hvne : vs ≠ [])
    {x : ℝ} (hx : 0 ≤ x)
    (hdu : ∀ step ∈ us, 0 ≤ step.2)
    (hdv : ∀ step ∈ vs, 0 ≤ step.2)
    (hlower : ∀ step ∈ vs, (1 / 4 : ℝ≥0) ≤ step.1)
    (hupper : ∀ step ∈ vs, Real.sqrt (step.1 : ℝ) ≤ 1) :
    gaussianMovingWalkSurvivalProbability (us ++ vs) x ≤
      (64 / Real.sqrt (vs.length : ℝ)) *
        (gaussianMovingWalkAffineMoment us x +
          (vs.map Prod.snd).sum *
            gaussianMovingWalkSurvivalProbability us x) := by
  let D : ℝ := (vs.map Prod.snd).sum
  let c : ℝ := 64 / Real.sqrt (vs.length : ℝ)
  have hD : 0 ≤ D := by
    dsimp only [D]
    apply List.sum_nonneg
    intro d hdmem
    obtain ⟨step, hstep, rfl⟩ := List.mem_map.mp hdmem
    exact hdv step hstep
  have hsqrt : 0 < Real.sqrt (vs.length : ℝ) := by
    apply Real.sqrt_pos.2
    exact_mod_cast List.length_pos_of_ne_nil hvne
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  rw [gaussianMovingWalkSurvivalProbability_append_eq_integralOn]
  have hleft : 0 ≤ᵐ[
      (gaussianMovingWalkMeasure us).restrict
        (gaussianMovingWalkSurvivalSet us x)]
      fun omega ↦ gaussianMovingWalkSurvivalProbability vs
        (gaussianMovingWalkTerminalDistance us x omega) := by
    exact Filter.Eventually.of_forall fun omega ↦
      (gaussianMovingWalkSurvivalProbability_nonneg_le_one vs _).1
  have hright : IntegrableOn
      (fun omega ↦ c *
        (gaussianMovingWalkTerminalDistance us x omega + 2 + D))
      (gaussianMovingWalkSurvivalSet us x)
      (gaussianMovingWalkMeasure us) := by
    exact (((integrable_gaussianMovingWalkTerminalDistance us x).add
      (integrable_const 2)).add (integrable_const D)).const_mul c |>.integrableOn
  have hpoint :
      (fun omega ↦ gaussianMovingWalkSurvivalProbability vs
          (gaussianMovingWalkTerminalDistance us x omega)) ≤ᵐ[
        (gaussianMovingWalkMeasure us).restrict
          (gaussianMovingWalkSurvivalSet us x)]
      fun omega ↦ c *
        (gaussianMovingWalkTerminalDistance us x omega + 2 + D) := by
    exact (ae_restrict_mem
      (measurableSet_gaussianMovingWalkSurvivalSet us x)).mono
        fun omega homega ↦ by
          have hterminal :=
            gaussianMovingWalkTerminalDistance_nonneg_of_survives
              us x omega hx hdu homega
          have htail := gaussianMovingWalkSurvivalProbability_le_flat
            vs hvne hterminal hdv hlower hupper
          dsimp only [c, D]
          convert! htail using 1 <;> ring
  calc
    (∫ omega in gaussianMovingWalkSurvivalSet us x,
        gaussianMovingWalkSurvivalProbability vs
          (gaussianMovingWalkTerminalDistance us x omega)
        ∂gaussianMovingWalkMeasure us) ≤
        ∫ omega in gaussianMovingWalkSurvivalSet us x,
          c * (gaussianMovingWalkTerminalDistance us x omega + 2 + D)
          ∂gaussianMovingWalkMeasure us :=
      integral_mono_of_nonneg hleft hright hpoint
    _ = c * (gaussianMovingWalkAffineMoment us x +
          D * gaussianMovingWalkSurvivalProbability us x) := by
      rw [integral_const_mul]
      rw [show (fun omega ↦
          gaussianMovingWalkTerminalDistance us x omega + 2 + D) =
          (fun omega ↦ gaussianMovingWalkTerminalDistance us x omega + 2) +
            (fun _omega ↦ D) by funext omega; simp]
      change c * (∫ omega in gaussianMovingWalkSurvivalSet us x,
        (gaussianMovingWalkTerminalDistance us x omega + 2) + D
        ∂gaussianMovingWalkMeasure us) = _
      rw [integral_add]
      · rw [integralOn_gaussianMovingWalkSurvival_terminal_eq]
        rw [setIntegral_const]
        rw [← gaussianMovingWalkSurvivalProbability_eq_measureReal]
        simp only [smul_eq_mul]
        ring
      · exact ((integrable_gaussianMovingWalkTerminalDistance us x).add
          (integrable_const 2)).integrableOn
      · exact (integrable_const D).integrableOn
    _ = (64 / Real.sqrt (vs.length : ℝ)) *
        (gaussianMovingWalkAffineMoment us x +
          (vs.map Prod.snd).sum *
            gaussianMovingWalkSurvivalProbability us x) := by rfl

/-! ## The exact positive-log increment schedule -/

/-- Increment of the boundary `8 log (j+2)` at absolute time `j`. -/
def harperPositiveLogIncrement (j : ℕ) : ℝ :=
  8 * Real.log ((j + 2 : ℕ) : ℝ) -
    8 * Real.log ((j + 1 : ℕ) : ℝ)

theorem harperPositiveLogIncrement_nonneg (j : ℕ) :
    0 ≤ harperPositiveLogIncrement j := by
  unfold harperPositiveLogIncrement
  have hlog : Real.log ((j + 1 : ℕ) : ℝ) ≤
      Real.log ((j + 2 : ℕ) : ℝ) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast (by omega : j + 1 ≤ j + 2)
  linarith

/-- A consecutive segment of the positive-log moving walk, with an arbitrary
infinite variance schedule. -/
def harperPositiveLogSteps (variance : ℕ → ℝ≥0)
    (start length : ℕ) : List GaussianMovingStep :=
  (List.range' start length).map
    (fun j ↦ (variance j, harperPositiveLogIncrement j))

@[simp] theorem harperPositiveLogSteps_length
    (variance : ℕ → ℝ≥0) (start length : ℕ) :
    (harperPositiveLogSteps variance start length).length = length := by
  simp [harperPositiveLogSteps]

@[simp] theorem harperPositiveLogSteps_zero
    (variance : ℕ → ℝ≥0) (start : ℕ) :
    harperPositiveLogSteps variance start 0 = [] := by
  simp [harperPositiveLogSteps]

theorem harperPositiveLogSteps_succ
    (variance : ℕ → ℝ≥0) (start length : ℕ) :
    harperPositiveLogSteps variance start (length + 1) =
      (variance start, harperPositiveLogIncrement start) ::
        harperPositiveLogSteps variance (start + 1) length := by
  simp [harperPositiveLogSteps, List.range'_succ]

theorem harperPositiveLogSteps_append
    (variance : ℕ → ℝ≥0) (start m n : ℕ) :
    harperPositiveLogSteps variance start (m + n) =
      harperPositiveLogSteps variance start m ++
        harperPositiveLogSteps variance (start + m) n := by
  unfold harperPositiveLogSteps
  rw [← List.map_append]
  have hr := List.range'_append
    (s := start) (m := m) (n := n) (step := 1)
  simpa only [one_mul] using! congrArg
    (List.map (fun j ↦ (variance j, harperPositiveLogIncrement j))) hr.symm

theorem sum_harperPositiveLogSteps_snd
    (variance : ℕ → ℝ≥0) (start length : ℕ) :
    ((harperPositiveLogSteps variance start length).map Prod.snd).sum =
      8 * (Real.log ((start + length + 1 : ℕ) : ℝ) -
        Real.log ((start + 1 : ℕ) : ℝ)) := by
  induction length generalizing start with
  | zero => simp
  | succ length ih =>
      rw [harperPositiveLogSteps_succ]
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      unfold harperPositiveLogIncrement
      congr 1
      push_cast
      ring

theorem harperPositiveLogSteps_snd_nonneg
    (variance : ℕ → ℝ≥0) (start length : ℕ) :
    ∀ step ∈ harperPositiveLogSteps variance start length,
      0 ≤ step.2 := by
  intro step hstep
  unfold harperPositiveLogSteps at hstep
  obtain ⟨j, _hj, rfl⟩ := List.mem_map.mp hstep
  exact harperPositiveLogIncrement_nonneg j

theorem harperPositiveLogSteps_variance_bounds
    (variance : ℕ → ℝ≥0)
    (hlower : ∀ j, (1 / 4 : ℝ≥0) ≤ variance j)
    (hupper : ∀ j, variance j ≤ (1 : ℝ≥0))
    (start length : ℕ) :
    (∀ step ∈ harperPositiveLogSteps variance start length,
      (1 / 4 : ℝ≥0) ≤ step.1) ∧
    (∀ step ∈ harperPositiveLogSteps variance start length,
      step.1 ≤ (1 : ℝ≥0)) := by
  constructor <;> intro step hstep <;>
    unfold harperPositiveLogSteps at hstep <;>
    obtain ⟨j, _hj, rfl⟩ := List.mem_map.mp hstep
  · exact hlower j
  · exact hupper j

theorem harperPositiveLogSteps_variance_regular
    (variance : ℕ → ℝ≥0)
    (hlower : ∀ j, (1 / 4 : ℝ≥0) ≤ variance j)
    (hupper : ∀ j, variance j ≤ (1 : ℝ≥0))
    (start length : ℕ) :
    ∀ step ∈ harperPositiveLogSteps variance start length,
      step.1 ≠ 0 ∧ Real.sqrt (step.1 : ℝ) ≤ 1 := by
  intro step hstep
  have hb := harperPositiveLogSteps_variance_bounds
    variance hlower hupper start length
  constructor
  · intro hzero
    have := hb.1 step hstep
    rw [hzero] at this
    norm_num at this
  · apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · have hu : (step.1 : ℝ) ≤ (1 : ℝ) := by
        exact_mod_cast hb.2 step hstep
      linarith

private theorem real_log_two_le_one : Real.log (2 : ℝ) ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  convert! h using 1 <;> norm_num

/-- The boundary rises by at most eight across a doubling block. -/
theorem sum_harperPositiveLogSteps_snd_doubling_le
    (variance : ℕ → ℝ≥0) (m : ℕ) :
    ((harperPositiveLogSteps variance m m).map Prod.snd).sum ≤ 8 := by
  rw [sum_harperPositiveLogSteps_snd]
  have hnat : m + m + 1 ≤ 2 * (m + 1) := by omega
  have hcast : ((m + m + 1 : ℕ) : ℝ) ≤
      (2 : ℝ) * ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
  have hlog : Real.log ((m + m + 1 : ℕ) : ℝ) ≤
      Real.log ((2 : ℝ) * ((m + 1 : ℕ) : ℝ)) :=
    Real.log_le_log (by positivity) hcast
  rw [Real.log_mul (by norm_num) (by positivity)] at hlog
  nlinarith [real_log_two_le_one]

/-- A segment whose right endpoint is before four times its left scale has
total boundary rise at most `24`. -/
theorem sum_harperPositiveLogSteps_snd_quadruping_le
    (variance : ℕ → ℝ≥0) (start length : ℕ)
    (hlength : length ≤ 3 * start + 3) :
    ((harperPositiveLogSteps variance start length).map Prod.snd).sum ≤ 24 := by
  rw [sum_harperPositiveLogSteps_snd]
  have hnat : start + length + 1 ≤ 4 * (start + 1) := by omega
  have hcast : ((start + length + 1 : ℕ) : ℝ) ≤
      (4 : ℝ) * ((start + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
  have hlog : Real.log ((start + length + 1 : ℕ) : ℝ) ≤
      Real.log ((4 : ℝ) * ((start + 1 : ℕ) : ℝ)) :=
    Real.log_le_log (by positivity) hcast
  rw [Real.log_mul (by norm_num) (by positivity)] at hlog
  have hlog4 := Real.log_le_sub_one_of_pos
    (show (0 : ℝ) < 4 by norm_num)
  norm_num at hlog4
  nlinarith

theorem sum_harperPositiveLogSteps_snd_pow_two_le
    (variance : ℕ → ℝ≥0) (k : ℕ) :
    ((harperPositiveLogSteps variance 0 (2 ^ k)).map Prod.snd).sum ≤
      8 * (k + 1 : ℕ) := by
  rw [sum_harperPositiveLogSteps_snd]
  simp only [zero_add, Nat.cast_add, Nat.cast_one, Real.log_one, sub_zero]
  have hnat : 2 ^ k + 1 ≤ 2 ^ (k + 1) := by
    rw [pow_succ]
    have hmpos : 0 < 2 ^ k := pow_pos (by norm_num : (0 : ℕ) < 2) k
    omega
  have hcast : (((2 ^ k + 1 : ℕ) : ℝ)) ≤
      (2 : ℝ) ^ (k + 1) := by
    exact_mod_cast hnat
  have hlog : Real.log (((2 ^ k + 1 : ℕ) : ℝ)) ≤
      Real.log ((2 : ℝ) ^ (k + 1)) :=
    Real.log_le_log (by positivity) hcast
  rw [Real.log_pow] at hlog
  have hk0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left real_log_two_le_one hk0
  have hlog' : Real.log (((2 ^ k : ℕ) : ℝ) + 1) ≤
      (k : ℝ) + 1 := by
    calc
      Real.log (((2 ^ k : ℕ) : ℝ) + 1) =
          Real.log (((2 ^ k + 1 : ℕ) : ℝ)) := by push_cast; rfl
      _ ≤ ((k + 1 : ℕ) : ℝ) * Real.log 2 := hlog
      _ ≤ ((k + 1 : ℕ) : ℝ) * 1 := hmul
      _ = (k : ℝ) + 1 := by push_cast; ring
  nlinarith

private theorem one_div_sqrt_two_pow_le_four_fifths_pow (k : ℕ) :
    1 / Real.sqrt (((2 ^ k : ℕ) : ℝ)) ≤ (4 / 5 : ℝ) ^ k := by
  have hbase : (0 : ℝ) ≤ (5 / 4 : ℝ) ^ k := by positivity
  have hrad : (0 : ℝ) ≤ (((2 ^ k : ℕ) : ℝ)) := by positivity
  have hsq : ((5 / 4 : ℝ) ^ k) ^ 2 ≤
      (((2 ^ k : ℕ) : ℝ)) := by
    calc
      ((5 / 4 : ℝ) ^ k) ^ 2 = (25 / 16 : ℝ) ^ k := by
        rw [pow_two, ← mul_pow]
        congr 1
        norm_num
      _ ≤ (2 : ℝ) ^ k :=
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 25 / 16)
          (by norm_num : (25 / 16 : ℝ) ≤ 2) k
      _ = (((2 ^ k : ℕ) : ℝ)) := by norm_num
  have hsqrt : (5 / 4 : ℝ) ^ k ≤
      Real.sqrt (((2 ^ k : ℕ) : ℝ)) :=
    (Real.le_sqrt hbase hrad).2 hsq
  have hdiv := one_div_le_one_div_of_le
    (by positivity : (0 : ℝ) < (5 / 4 : ℝ) ^ k) hsqrt
  calc
    1 / Real.sqrt (((2 ^ k : ℕ) : ℝ)) ≤
        1 / ((5 / 4 : ℝ) ^ k) := hdiv
    _ = (4 / 5 : ℝ) ^ k := by
      rw [one_div, ← inv_pow]
      congr 1
      norm_num

private theorem natSucc_mul_four_fifths_pow_le (k : ℕ) :
    (((k + 1 : ℕ) : ℝ)) * (4 / 5 : ℝ) ^ k ≤
      8 * (9 / 10 : ℝ) ^ k := by
  have hbern := one_add_mul_le_pow
    (a := (1 / 8 : ℝ)) (by norm_num : (-2 : ℝ) ≤ 1 / 8) k
  have hk : (((k + 1 : ℕ) : ℝ)) ≤
      8 * (9 / 8 : ℝ) ^ k := by
    push_cast
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hk
    (show 0 ≤ (4 / 5 : ℝ) ^ k by positivity)
  calc
    (((k + 1 : ℕ) : ℝ)) * (4 / 5 : ℝ) ^ k ≤
        (8 * (9 / 8 : ℝ) ^ k) * (4 / 5 : ℝ) ^ k := hmul
    _ = 8 * (9 / 10 : ℝ) ^ k := by
      rw [mul_assoc, ← mul_pow]
      norm_num

private theorem sum_nine_tenths_pow_le_sub (k : ℕ) :
    ∑ j ∈ Finset.range k, (9 / 10 : ℝ) ^ j ≤
      10 * (1 - (9 / 10 : ℝ) ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ j ∈ Finset.range k, (9 / 10 : ℝ) ^ j) +
            (9 / 10 : ℝ) ^ k ≤
            10 * (1 - (9 / 10 : ℝ) ^ k) +
              (9 / 10 : ℝ) ^ k := by nlinarith [ih]
        _ = 10 * (1 - (9 / 10 : ℝ) ^ (k + 1)) := by
          rw [pow_succ]
          ring

private theorem sum_nine_tenths_pow_le (k : ℕ) :
    ∑ j ∈ Finset.range k, (9 / 10 : ℝ) ^ j ≤ 10 := by
  have h := sum_nine_tenths_pow_le_sub k
  have hp : 0 ≤ (9 / 10 : ℝ) ^ k := by positivity
  linarith

private theorem dyadic_log_ballot_summand_le
    {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (x + 8 * ((k + 1 : ℕ) : ℝ) + 2) /
        Real.sqrt (((2 ^ k : ℕ) : ℝ)) ≤
      (x + 66) * (9 / 10 : ℝ) ^ k := by
  have hnum : 0 ≤ x + 8 * ((k + 1 : ℕ) : ℝ) + 2 := by positivity
  have hinv := one_div_sqrt_two_pow_le_four_fifths_pow k
  have hfirst := mul_le_mul_of_nonneg_left hinv hnum
  have hbase : (4 / 5 : ℝ) ^ k ≤ (9 / 10 : ℝ) ^ k :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4 / 5)
      (by norm_num : (4 / 5 : ℝ) ≤ 9 / 10) k
  have hxbase := mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ x + 2)
  have hkbase := natSucc_mul_four_fifths_pow_le k
  calc
    (x + 8 * ((k + 1 : ℕ) : ℝ) + 2) /
        Real.sqrt (((2 ^ k : ℕ) : ℝ)) =
        (x + 8 * ((k + 1 : ℕ) : ℝ) + 2) *
          (1 / Real.sqrt (((2 ^ k : ℕ) : ℝ))) := by ring
    _ ≤ (x + 8 * ((k + 1 : ℕ) : ℝ) + 2) *
          (4 / 5 : ℝ) ^ k := hfirst
    _ = (x + 2) * (4 / 5 : ℝ) ^ k +
          8 * (((k + 1 : ℕ) : ℝ) * (4 / 5 : ℝ) ^ k) := by ring
    _ ≤ (x + 2) * (9 / 10 : ℝ) ^ k +
          8 * (8 * (9 / 10 : ℝ) ^ k) := by gcongr
    _ = (x + 66) * (9 / 10 : ℝ) ^ k := by ring

private theorem sum_dyadic_log_ballot_summand_le
    {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    ∑ j ∈ Finset.range k,
        (x + 8 * ((j + 1 : ℕ) : ℝ) + 2) /
          Real.sqrt (((2 ^ j : ℕ) : ℝ)) ≤
      10 * (x + 66) := by
  calc
    (∑ j ∈ Finset.range k,
        (x + 8 * ((j + 1 : ℕ) : ℝ) + 2) /
          Real.sqrt (((2 ^ j : ℕ) : ℝ))) ≤
        ∑ j ∈ Finset.range k,
          (x + 66) * (9 / 10 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      exact dyadic_log_ballot_summand_le hx j
    _ = (x + 66) *
        (∑ j ∈ Finset.range k, (9 / 10 : ℝ) ^ j) := by
      rw [Finset.mul_sum]
    _ ≤ (x + 66) * 10 := by
      exact mul_le_mul_of_nonneg_left (sum_nine_tenths_pow_le k) (by linarith)
    _ = 10 * (x + 66) := by ring

/-! ## Dyadic affine bootstrap -/

theorem harperPositiveLogSteps_affineMoment_pow_two_le_sum
    (variance : ℕ → ℝ≥0)
    (hlower : ∀ j, (1 / 4 : ℝ≥0) ≤ variance j)
    (hupper : ∀ j, variance j ≤ (1 : ℝ≥0))
    {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    gaussianMovingWalkAffineMoment
        (harperPositiveLogSteps variance 0 (2 ^ k)) x ≤
      x + 10 + 512 *
        (∑ j ∈ Finset.range k,
          (x + 8 * ((j + 1 : ℕ) : ℝ) + 2) /
            Real.sqrt (((2 ^ j : ℕ) : ℝ))) := by
  induction k with
  | zero =>
      have hmain := gaussianMovingWalkAffineMoment_le_totalIncrement
        (harperPositiveLogSteps variance 0 (2 ^ 0)) hx
        (harperPositiveLogSteps_snd_nonneg variance 0 (2 ^ 0))
        (harperPositiveLogSteps_variance_regular
          variance hlower hupper 0 (2 ^ 0))
      have hsum := sum_harperPositiveLogSteps_snd_pow_two_le variance 0
      norm_num at hmain hsum ⊢
      linarith
  | succ k ih =>
      let m : ℕ := 2 ^ k
      let us := harperPositiveLogSteps variance 0 m
      let vs := harperPositiveLogSteps variance m m
      have hmpos : 0 < m := by dsimp only [m]; positivity
      have husne : us ≠ [] := by
        intro hnil
        have hlen := congrArg List.length hnil
        simp only [us, harperPositiveLogSteps_length, List.length_nil] at hlen
        omega
      have hdus := harperPositiveLogSteps_snd_nonneg variance 0 m
      have hdvs := harperPositiveLogSteps_snd_nonneg variance m m
      have hregus := harperPositiveLogSteps_variance_regular
        variance hlower hupper 0 m
      have hregvs := harperPositiveLogSteps_variance_regular
        variance hlower hupper m m
      have hbvs := harperPositiveLogSteps_variance_bounds
        variance hlower hupper m m
      have hsplit : harperPositiveLogSteps variance 0 (2 ^ (k + 1)) =
          us ++ vs := by
        rw [show 2 ^ (k + 1) = m + m by
          dsimp only [m]; rw [pow_succ]; omega]
        simpa only [us, vs, zero_add] using!
          harperPositiveLogSteps_append variance 0 m m
      have happ := gaussianMovingWalkAffineMoment_append_le
        us vs hx hdus hdvs hregus hregvs
      have hD : (vs.map Prod.snd).sum ≤ 8 := by
        exact sum_harperPositiveLogSteps_snd_doubling_le variance m
      have hD0 : 0 ≤ (vs.map Prod.snd).sum := by
        apply List.sum_nonneg
        intro d hdmem
        obtain ⟨step, hstep, rfl⟩ := List.mem_map.mp hdmem
        exact hdvs step hstep
      have hP0 := gaussianMovingWalkSurvivalProbability_le_flat
        us husne hx hdus
        (harperPositiveLogSteps_variance_bounds
          variance hlower hupper 0 m).1
        (fun step hstep ↦
          (harperPositiveLogSteps_variance_regular
            variance hlower hupper 0 m step hstep).2)
      have hsumus : (us.map Prod.snd).sum ≤
          8 * ((k + 1 : ℕ) : ℝ) := by
        simpa only [us, m] using!
          sum_harperPositiveLogSteps_snd_pow_two_le variance k
      have hsqrt0 : 0 ≤ Real.sqrt ((m : ℕ) : ℝ) := Real.sqrt_nonneg _
      have hP : gaussianMovingWalkSurvivalProbability us x ≤
          64 * (x + 8 * ((k + 1 : ℕ) : ℝ) + 2) /
            Real.sqrt (((2 ^ k : ℕ) : ℝ)) := by
        calc
          gaussianMovingWalkSurvivalProbability us x ≤
              64 * (x + (us.map Prod.snd).sum + 2) /
                Real.sqrt (us.length : ℝ) := hP0
          _ ≤ 64 * (x + 8 * ((k + 1 : ℕ) : ℝ) + 2) /
                Real.sqrt (us.length : ℝ) := by
            apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
            gcongr
          _ = 64 * (x + 8 * ((k + 1 : ℕ) : ℝ) + 2) /
                Real.sqrt (((2 ^ k : ℕ) : ℝ)) := by
            simp only [us, harperPositiveLogSteps_length, m]
      have hPnonneg :=
        (gaussianMovingWalkSurvivalProbability_nonneg_le_one us x).1
      have hincrement :
          (vs.map Prod.snd).sum *
              gaussianMovingWalkSurvivalProbability us x ≤
            512 * ((x + 8 * ((k + 1 : ℕ) : ℝ) + 2) /
              Real.sqrt (((2 ^ k : ℕ) : ℝ))) := by
        calc
          (vs.map Prod.snd).sum *
              gaussianMovingWalkSurvivalProbability us x ≤
              8 * gaussianMovingWalkSurvivalProbability us x :=
            mul_le_mul_of_nonneg_right hD hPnonneg
          _ ≤ 8 * (64 * (x + 8 * ((k + 1 : ℕ) : ℝ) + 2) /
                Real.sqrt (((2 ^ k : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left hP (by norm_num)
          _ = 512 * ((x + 8 * ((k + 1 : ℕ) : ℝ) + 2) /
                Real.sqrt (((2 ^ k : ℕ) : ℝ))) := by ring
      rw [hsplit]
      calc
        gaussianMovingWalkAffineMoment (us ++ vs) x ≤
            gaussianMovingWalkAffineMoment us x +
              (vs.map Prod.snd).sum *
                gaussianMovingWalkSurvivalProbability us x := happ
        _ ≤ (x + 10 + 512 *
              (∑ j ∈ Finset.range k,
                (x + 8 * ((j + 1 : ℕ) : ℝ) + 2) /
                  Real.sqrt (((2 ^ j : ℕ) : ℝ)))) +
              512 * ((x + 8 * ((k + 1 : ℕ) : ℝ) + 2) /
                Real.sqrt (((2 ^ k : ℕ) : ℝ))) := by
          gcongr
        _ = x + 10 + 512 *
              (∑ j ∈ Finset.range (k + 1),
                (x + 8 * ((j + 1 : ℕ) : ℝ) + 2) /
                  Real.sqrt (((2 ^ j : ℕ) : ℝ))) := by
          rw [Finset.sum_range_succ]
          ring

theorem harperPositiveLogSteps_affineMoment_pow_two_le
    (variance : ℕ → ℝ≥0)
    (hlower : ∀ j, (1 / 4 : ℝ≥0) ≤ variance j)
    (hupper : ∀ j, variance j ≤ (1 : ℝ≥0))
    {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    gaussianMovingWalkAffineMoment
        (harperPositiveLogSteps variance 0 (2 ^ k)) x ≤
      338000 * (x + 1) := by
  have hmain := harperPositiveLogSteps_affineMoment_pow_two_le_sum
    variance hlower hupper hx k
  have hsum := sum_dyadic_log_ballot_summand_le hx k
  have hsum0 : 0 ≤
      ∑ j ∈ Finset.range k,
        (x + 8 * ((j + 1 : ℕ) : ℝ) + 2) /
          Real.sqrt (((2 ^ j : ℕ) : ℝ)) := by
    apply Finset.sum_nonneg
    intro j hj
    positivity
  calc
    gaussianMovingWalkAffineMoment
        (harperPositiveLogSteps variance 0 (2 ^ k)) x ≤
        x + 10 + 512 *
          (∑ j ∈ Finset.range k,
            (x + 8 * ((j + 1 : ℕ) : ℝ) + 2) /
              Real.sqrt (((2 ^ j : ℕ) : ℝ))) := hmain
    _ ≤ x + 10 + 512 * (10 * (x + 66)) := by gcongr
    _ ≤ 338000 * (x + 1) := by nlinarith

/-! ## Arbitrary length and the no-log-loss moving-walk endpoint -/

theorem harperPositiveLogSteps_probability_le
    (variance : ℕ → ℝ≥0)
    (hlower : ∀ j, (1 / 4 : ℝ≥0) ≤ variance j)
    (hupper : ∀ j, variance j ≤ (1 : ℝ≥0))
    (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    gaussianMovingWalkSurvivalProbability
        (harperPositiveLogSteps variance 0 n) x ≤
      44000000 * (x + 1) / Real.sqrt (n : ℝ) := by
  by_cases hn1 : n = 1
  · subst n
    have hP := (gaussianMovingWalkSurvivalProbability_nonneg_le_one
      (harperPositiveLogSteps variance 0 1) x).2
    norm_num
    nlinarith
  · have hn2 : 2 ≤ n := by omega
    let k : ℕ := Nat.log 2 n
    have hk1 : 1 ≤ k := by
      dsimp only [k]
      exact Nat.le_log_of_pow_le Nat.one_lt_two hn2
    let m : ℕ := 2 ^ (k - 1)
    let ell : ℕ := n - m
    have hmpos : 0 < m := by dsimp only [m]; positivity
    have hpowLower : 2 ^ k ≤ n := by
      dsimp only [k]
      exact Nat.pow_log_le_self 2 (by omega)
    have htwom : 2 * m = 2 ^ k := by
      dsimp only [m]
      calc
        2 * 2 ^ (k - 1) = 2 ^ (k - 1) * 2 := by omega
        _ = 2 ^ ((k - 1) + 1) := (pow_succ 2 (k - 1)).symm
        _ = 2 ^ k := by congr 1; omega
    have hmle : m ≤ n := by omega
    have hm_lt_n : m < n := by omega
    have hellpos : 0 < ell := by dsimp only [ell]; omega
    have hellne : harperPositiveLogSteps variance m ell ≠ [] := by
      intro hnil
      have hlen := congrArg List.length hnil
      simp only [harperPositiveLogSteps_length, List.length_nil] at hlen
      omega
    have hpowUpper0 := Nat.lt_pow_succ_log_self Nat.one_lt_two n
    have hpowUpper : n < 4 * m := by
      have heq : 2 ^ (Nat.log 2 n).succ = 4 * m := by
        change 2 ^ (k + 1) = 4 * m
        dsimp only [m]
        rw [show k + 1 = (k - 1) + 2 by omega, pow_add]
        norm_num [Nat.mul_comm]
      rwa [heq] at hpowUpper0
    have hell_le : ell ≤ 3 * m + 3 := by dsimp only [ell]; omega
    have hn_le_twoell : n ≤ 2 * ell := by dsimp only [ell]; omega
    let us := harperPositiveLogSteps variance 0 m
    let vs := harperPositiveLogSteps variance m ell
    have hsplit : harperPositiveLogSteps variance 0 n = us ++ vs := by
      rw [show n = m + ell by dsimp only [ell]; omega]
      simpa only [us, vs, zero_add] using!
        harperPositiveLogSteps_append variance 0 m ell
    have hdus := harperPositiveLogSteps_snd_nonneg variance 0 m
    have hdvs := harperPositiveLogSteps_snd_nonneg variance m ell
    have hbvs := harperPositiveLogSteps_variance_bounds
      variance hlower hupper m ell
    have hlast := gaussianMovingWalkSurvivalProbability_append_le_affine
      us vs (by simpa only [vs] using! hellne) hx hdus hdvs hbvs.1
        (fun step hstep ↦
          (harperPositiveLogSteps_variance_regular
            variance hlower hupper m ell step hstep).2)
    have hM : gaussianMovingWalkAffineMoment us x ≤
        338000 * (x + 1) := by
      simpa only [us, m] using!
        harperPositiveLogSteps_affineMoment_pow_two_le
          variance hlower hupper hx (k - 1)
    have hD : (vs.map Prod.snd).sum ≤ 24 := by
      simpa only [vs] using!
        sum_harperPositiveLogSteps_snd_quadruping_le
          variance m ell hell_le
    have hP0 :=
      (gaussianMovingWalkSurvivalProbability_nonneg_le_one us x).1
    have hP1 :=
      (gaussianMovingWalkSurvivalProbability_nonneg_le_one us x).2
    have hD0 : 0 ≤ (vs.map Prod.snd).sum := by
      apply List.sum_nonneg
      intro d hdmem
      obtain ⟨step, hstep, rfl⟩ := List.mem_map.mp hdmem
      exact hdvs step hstep
    have hinner0 : 0 ≤ gaussianMovingWalkAffineMoment us x +
        (vs.map Prod.snd).sum *
          gaussianMovingWalkSurvivalProbability us x := by
      exact add_nonneg
        (gaussianMovingWalkAffineMoment_nonneg us hx hdus)
        (mul_nonneg hD0 hP0)
    have hinner : gaussianMovingWalkAffineMoment us x +
          (vs.map Prod.snd).sum *
            gaussianMovingWalkSurvivalProbability us x ≤
        338024 * (x + 1) := by
      calc
        gaussianMovingWalkAffineMoment us x +
            (vs.map Prod.snd).sum *
              gaussianMovingWalkSurvivalProbability us x ≤
            338000 * (x + 1) + 24 * 1 := by gcongr
        _ ≤ 338024 * (x + 1) := by nlinarith
    have hsqrtnpos : 0 < Real.sqrt (n : ℝ) := by
      apply Real.sqrt_pos.2
      exact_mod_cast hn
    have hsqrtellpos : 0 < Real.sqrt (ell : ℝ) := by
      apply Real.sqrt_pos.2
      exact_mod_cast hellpos
    have hsqrtcomp : Real.sqrt (n : ℝ) ≤
        2 * Real.sqrt (ell : ℝ) := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1
      rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ))]
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (ell : ℝ))]
      norm_num
      exact_mod_cast (hn_le_twoell.trans (by omega : 2 * ell ≤ 4 * ell))
    have hinvcomp : 1 / Real.sqrt (ell : ℝ) ≤
        2 / Real.sqrt (n : ℝ) := by
      have hrecip := one_div_le_one_div_of_le hsqrtnpos hsqrtcomp
      calc
        1 / Real.sqrt (ell : ℝ) =
            2 * (1 / (2 * Real.sqrt (ell : ℝ))) := by
          field_simp
        _ ≤ 2 * (1 / Real.sqrt (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hrecip (by norm_num)
        _ = 2 / Real.sqrt (n : ℝ) := by ring
    rw [hsplit]
    calc
      gaussianMovingWalkSurvivalProbability (us ++ vs) x ≤
          (64 / Real.sqrt (vs.length : ℝ)) *
            (gaussianMovingWalkAffineMoment us x +
              (vs.map Prod.snd).sum *
                gaussianMovingWalkSurvivalProbability us x) := hlast
      _ = (64 * (1 / Real.sqrt (ell : ℝ))) *
            (gaussianMovingWalkAffineMoment us x +
              (vs.map Prod.snd).sum *
                gaussianMovingWalkSurvivalProbability us x) := by
        simp only [vs, harperPositiveLogSteps_length]
        ring
      _ ≤ (64 * (2 / Real.sqrt (n : ℝ))) *
            (gaussianMovingWalkAffineMoment us x +
              (vs.map Prod.snd).sum *
                gaussianMovingWalkSurvivalProbability us x) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hinvcomp (by norm_num)) hinner0
      _ ≤ (64 * (2 / Real.sqrt (n : ℝ))) *
            (338024 * (x + 1)) := by
        exact mul_le_mul_of_nonneg_left hinner (by positivity)
      _ ≤ 44000000 * (x + 1) / Real.sqrt (n : ℝ) := by
        have hx1 : 0 ≤ x + 1 := by linarith
        field_simp
        nlinarith

/-- The absolute boundary obtained by cumulatively adding the moving-boundary
increments through coordinate `i`. -/
def gaussianMovingWalkAbsoluteBarrier
    (steps : List GaussianMovingStep) (B : ℝ) : Fin steps.length → ℝ :=
  fun i ↦ B + ((steps.take (i.val + 1)).map Prod.snd).sum

@[simp] theorem gaussianMovingWalkAbsoluteBarrier_cons_zero
    (step : GaussianMovingStep) (steps : List GaussianMovingStep) (B : ℝ) :
    gaussianMovingWalkAbsoluteBarrier (step :: steps) B 0 = B + step.2 := by
  simp [gaussianMovingWalkAbsoluteBarrier]

@[simp] theorem gaussianMovingWalkAbsoluteBarrier_cons_succ
    (step : GaussianMovingStep) (steps : List GaussianMovingStep) (B : ℝ)
    (i : Fin steps.length) :
    gaussianMovingWalkAbsoluteBarrier (step :: steps) B i.succ =
      gaussianMovingWalkAbsoluteBarrier steps (B + step.2) i := by
  simp [gaussianMovingWalkAbsoluteBarrier, List.take_succ_cons]
  ring

/-- Distance-to-the-boundary survival is exactly survival below the associated
absolute cumulative boundary. -/
theorem gaussianMovingWalkSurvives_iff_absoluteBarrier
    (steps : List GaussianMovingStep) (s x : ℝ)
    (omega : Fin steps.length → ℝ) :
    gaussianMovingWalkSurvives steps x omega ↔
      gaussianWalkTimeBarrierSurvives steps.length s
        (gaussianMovingWalkAbsoluteBarrier steps (s + x)) omega := by
  induction steps generalizing s x with
  | nil =>
      simp [gaussianMovingWalkSurvives, gaussianWalkTimeBarrierSurvives]
  | cons step steps ih =>
      simp only [List.length_cons, gaussianMovingWalkSurvives, gaussianWalkTimeBarrierSurvives]
      have hbarrier :
          (fun i : Fin steps.length ↦
            gaussianMovingWalkAbsoluteBarrier (step :: steps) (s + x) i.succ) =
          gaussianMovingWalkAbsoluteBarrier steps (s + x + step.2) :=
        funext fun i ↦ gaussianMovingWalkAbsoluteBarrier_cons_succ step steps (s + x) i
      erw [gaussianMovingWalkAbsoluteBarrier_cons_zero]
      rw [hbarrier, ih (s + omega 0) (x + step.2 - omega 0)]
      have hshift : s + omega 0 + (x + step.2 - omega 0) = s + x + step.2 := by ring
      rw [hshift]
      constructor <;> rintro ⟨hfirst, htail⟩ <;> exact ⟨by linarith, htail⟩

theorem harperPositiveLogSteps_take
    (variance : ℕ → ℝ≥0) (start length k : ℕ) (hk : k ≤ length) :
    (harperPositiveLogSteps variance start length).take k =
      harperPositiveLogSteps variance start k := by
  have hsplit :
      harperPositiveLogSteps variance start length =
        harperPositiveLogSteps variance start k ++
          harperPositiveLogSteps variance (start + k) (length - k) := by
    have happ := harperPositiveLogSteps_append variance start k (length - k)
    simpa only [Nat.add_sub_of_le hk] using! happ
  rw [hsplit]
  simpa only [harperPositiveLogSteps_length] using!
    (List.take_left (l₁ := harperPositiveLogSteps variance start k)
      (l₂ := harperPositiveLogSteps variance (start + k) (length - k)))

theorem harperPositiveLogSteps_absoluteBarrier
    (variance : ℕ → ℝ≥0) (start length : ℕ) (s x : ℝ)
    (i : Fin (harperPositiveLogSteps variance start length).length) :
    gaussianMovingWalkAbsoluteBarrier
        (harperPositiveLogSteps variance start length) (s + x) i =
      s + x + 8 *
        (Real.log ((start + i.val + 2 : ℕ) : ℝ) -
          Real.log ((start + 1 : ℕ) : ℝ)) := by
  unfold gaussianMovingWalkAbsoluteBarrier
  rw [harperPositiveLogSteps_take variance start length (i.val + 1)]
  · rw [sum_harperPositiveLogSteps_snd]
    congr 2
  · simpa only [harperPositiveLogSteps_length, Nat.add_one_le_iff] using! i.isLt

theorem harperPositiveLogSteps_survives_iff_timeBarrier
    (variance : ℕ → ℝ≥0) (start n : ℕ) (s x : ℝ)
    (omega : Fin n → ℝ) :
    gaussianMovingWalkSurvives
        (harperPositiveLogSteps variance start n) x
        (fun i ↦ omega
          (finCongr (harperPositiveLogSteps_length variance start n) i)) ↔
      gaussianWalkTimeBarrierSurvives n s
        (fun i ↦ s + x + 8 *
          (Real.log ((start + i.val + 2 : ℕ) : ℝ) -
            Real.log ((start + 1 : ℕ) : ℝ))) omega := by
  rw [gaussianMovingWalkSurvives_iff_absoluteBarrier]
  let hlen := harperPositiveLogSteps_length variance start n
  let b := gaussianMovingWalkAbsoluteBarrier
    (harperPositiveLogSteps variance start n) (s + x)
  let eta : Fin (harperPositiveLogSteps variance start n).length → ℝ :=
    fun i ↦ omega (finCongr hlen i)
  have hreindex := gaussianWalkTimeBarrierSurvives_reindex_finCongr
    hlen s b eta
  rw [← hreindex]
  have hb : (fun j ↦ b ((finCongr hlen).symm j)) =
      (fun i ↦ s + x + 8 *
        (Real.log ((start + i.val + 2 : ℕ) : ℝ) -
          Real.log ((start + 1 : ℕ) : ℝ))) := by
    funext i
    simp only [b]
    rw [harperPositiveLogSteps_absoluteBarrier]
    simp only [finCongr_symm_apply_coe]
  have heta : (fun j ↦ eta ((finCongr hlen).symm j)) = omega := by
    funext i
    simp [eta, hlen]
  rw [hb, heta]

/-- Extend a finite variance schedule by the lower endpoint of the admissible
interval.  Only its first `n` values are used by the finite walk. -/
def harperExtendFinVariance {n : ℕ} (variance : Fin n → ℝ≥0) : ℕ → ℝ≥0 :=
  fun j ↦ if hj : j < n then variance ⟨j, hj⟩ else 1 / 4

@[simp] theorem harperExtendFinVariance_apply_fin
    {n : ℕ} (variance : Fin n → ℝ≥0) (i : Fin n) :
    harperExtendFinVariance variance i.val = variance i := by
  simp only [harperExtendFinVariance, dif_pos i.isLt]

/-- Finite product-measure form of the sharp positive-log Gaussian ballot
estimate, uniform for every variance schedule in `[1/4,1]`. -/
theorem gaussianVarianceWalk_quarter_one_positiveLogBarrier_probability_le_fin
    (n : ℕ) (hn : 0 < n) (variance : Fin n → ℝ≥0)
    {x : ℝ} (hx : 0 ≤ x)
    (hlower : ∀ i, (1 / 4 : ℝ≥0) ≤ variance i)
    (hupper : ∀ i, variance i ≤ (1 : ℝ≥0)) :
    (Measure.pi (fun i : Fin n ↦ gaussianReal 0 (variance i))).real
        (gaussianWalkTimeBarrierSet n 0
          (fun i ↦ x + 8 * Real.log ((i.val + 2 : ℕ) : ℝ))) ≤
      44000000 * (x + 1) / Real.sqrt (n : ℝ) := by
  let varianceNat := harperExtendFinVariance variance
  let steps := harperPositiveLogSteps varianceNat 0 n
  have hlowerNat : ∀ j, (1 / 4 : ℝ≥0) ≤ varianceNat j := by
    intro j
    by_cases hj : j < n
    · simpa only [varianceNat, harperExtendFinVariance, dif_pos hj] using!
        hlower ⟨j, hj⟩
    · simp [varianceNat, harperExtendFinVariance, hj]
  have hupperNat : ∀ j, varianceNat j ≤ (1 : ℝ≥0) := by
    intro j
    by_cases hj : j < n
    · simpa only [varianceNat, harperExtendFinVariance, dif_pos hj] using!
        hupper ⟨j, hj⟩
    · simp [varianceNat, harperExtendFinVariance, hj]
  have hmain := harperPositiveLogSteps_probability_le
    varianceNat hlowerNat hupperNat n hn hx
  rw [gaussianMovingWalkSurvivalProbability_eq_measureReal] at hmain
  have hlen : steps.length = n := by
    simp only [steps, harperPositiveLogSteps_length]
  let e : Fin steps.length ≃ Fin n := finCongr hlen
  let E : (Fin steps.length → ℝ) ≃ᵐ (Fin n → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e
  have hcoord (i : Fin steps.length) : (steps.get i).1 = variance (e i) := by
    rw [List.get_eq_getElem]
    simp only [steps, harperPositiveLogSteps, List.getElem_map,
      List.getElem_range', zero_add, one_mul, varianceNat]
    change harperExtendFinVariance variance (e i).val = variance (e i)
    exact harperExtendFinVariance_apply_fin variance (e i)
  have hsource : gaussianMovingWalkMeasure steps =
      Measure.pi (fun i : Fin steps.length ↦
        gaussianReal 0 (variance (e i))) := by
    unfold gaussianMovingWalkMeasure
    congr 1
    funext i
    rw [hcoord]
  have hmp := measurePreserving_piCongrLeft
    (μ := fun i : Fin n ↦ gaussianReal 0 (variance i)) e
  have hE (omega : Fin steps.length → ℝ) :
      E omega = fun j ↦ omega (e.symm j) := by
    funext j
    obtain ⟨i, rfl⟩ := e.surjective j
    change (MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e)
      omega (e i) = omega i
    exact MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin n ↦ ℝ) e omega i
  have hpre : E ⁻¹' gaussianWalkTimeBarrierSet n 0
        (fun i ↦ x + 8 * Real.log ((i.val + 2 : ℕ) : ℝ)) =
      gaussianMovingWalkSurvivalSet steps x := by
    ext omega
    simp only [Set.mem_preimage, gaussianWalkTimeBarrierSet,
      gaussianMovingWalkSurvivalSet, mem_setOf_eq]
    rw [hE]
    have hbridge := harperPositiveLogSteps_survives_iff_timeBarrier
      varianceNat 0 n 0 x (fun j ↦ omega (e.symm j))
    norm_num only [Nat.cast_one, Real.log_one, sub_zero] at hbridge
    simpa only [steps, e, zero_add, Nat.zero_add,
      Equiv.symm_apply_apply] using! hbridge.symm
  have htransport :
      (Measure.pi (fun i : Fin n ↦ gaussianReal 0 (variance i))).real
          (gaussianWalkTimeBarrierSet n 0
            (fun i ↦ x + 8 * Real.log ((i.val + 2 : ℕ) : ℝ))) =
        (gaussianMovingWalkMeasure steps).real
          (gaussianMovingWalkSurvivalSet steps x) := by
    rw [← hmp.map_eq]
    rw [map_measureReal_apply E.measurable
      (measurableSet_gaussianWalkTimeBarrierSet n 0 _)]
    rw [hpre, hsource]
  rw [htransport]
  simpa only [steps] using! hmain

/-- Adding the same constant to the already accumulated sum and to every
absolute barrier value does not change survival. -/
theorem gaussianWalkTimeBarrierSurvives_add_const
    (n : ℕ) (c s : ℝ) (b omega : Fin n → ℝ) :
    gaussianWalkTimeBarrierSurvives n (s + c) (fun i ↦ b i + c) omega ↔
      gaussianWalkTimeBarrierSurvives n s b omega := by
  induction n generalizing s with
  | zero => simp [gaussianWalkTimeBarrierSurvives]
  | succ n ih =>
      simp only [gaussianWalkTimeBarrierSurvives]
      constructor <;> rintro ⟨hfirst, htail⟩
      · constructor
        · linarith
        · have ht : gaussianWalkTimeBarrierSurvives n
              ((s + omega 0) + c) (fun i ↦ b i.succ + c)
              (fun i ↦ omega i.succ) := by
            convert! htail using 1 <;> ring
          exact (ih (s := s + omega 0) (b := fun i ↦ b i.succ)
            (omega := fun i ↦ omega i.succ)).mp ht
      · constructor
        · linarith
        · have ht := (ih (s := s + omega 0) (b := fun i ↦ b i.succ)
            (omega := fun i ↦ omega i.succ)).mpr htail
          convert! ht using 1 <;> ring

/-- Starting the positive logarithmic schedule later only lowers its rise. -/
theorem positiveLogDifference_start_le (start i : ℕ) :
    Real.log ((start + i + 2 : ℕ) : ℝ) -
        Real.log ((start + 1 : ℕ) : ℝ) ≤
      Real.log ((i + 2 : ℕ) : ℝ) := by
  have hs : 0 ≤ (start : ℝ) := by positivity
  have hi : 0 ≤ (i : ℝ) := by positivity
  have hprod : 0 ≤ (start : ℝ) * ((i : ℝ) + 1) :=
    mul_nonneg hs (by linarith)
  have hcast : ((start + i + 2 : ℕ) : ℝ) ≤
      ((start + 1 : ℕ) : ℝ) * ((i + 2 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hlog := Real.log_le_log (by positivity) hcast
  rw [Real.log_mul (by positivity) (by positivity)] at hlog
  linarith

/-- Arbitrary-start and arbitrary-base form used by scheduled mixtures.  The
constant is independent of the schedule start. -/
theorem gaussianVarianceWalk_quarter_one_positiveLogBarrier_probability_le_fin_start
    (n : ℕ) (hn : 0 < n) (variance : Fin n → ℝ≥0)
    (start : ℕ) (s : ℝ) {x : ℝ} (hx : 0 ≤ x)
    (hlower : ∀ i, (1 / 4 : ℝ≥0) ≤ variance i)
    (hupper : ∀ i, variance i ≤ (1 : ℝ≥0)) :
    (Measure.pi (fun i : Fin n ↦ gaussianReal 0 (variance i))).real
        (gaussianWalkTimeBarrierSet n s
          (fun i ↦ s + x + 8 *
            (Real.log ((start + i.val + 2 : ℕ) : ℝ) -
              Real.log ((start + 1 : ℕ) : ℝ)))) ≤
      44000000 * (x + 1) / Real.sqrt (n : ℝ) := by
  let μ := Measure.pi (fun i : Fin n ↦ gaussianReal 0 (variance i))
  let bstart : Fin n → ℝ := fun i ↦ s + x + 8 *
    (Real.log ((start + i.val + 2 : ℕ) : ℝ) -
      Real.log ((start + 1 : ℕ) : ℝ))
  let bzeroS : Fin n → ℝ := fun i ↦
    s + x + 8 * Real.log ((i.val + 2 : ℕ) : ℝ)
  let bzero : Fin n → ℝ := fun i ↦
    x + 8 * Real.log ((i.val + 2 : ℕ) : ℝ)
  have hbarrier : ∀ i, bstart i ≤ bzeroS i := by
    intro i
    dsimp only [bstart, bzeroS]
    have hlog := positiveLogDifference_start_le start i.val
    nlinarith
  have hsubset : gaussianWalkTimeBarrierSet n s bstart ⊆
      gaussianWalkTimeBarrierSet n s bzeroS := by
    intro omega homega
    exact gaussianWalkTimeBarrierSurvives_mono n s hbarrier homega
  have hshift : gaussianWalkTimeBarrierSet n s bzeroS =
      gaussianWalkTimeBarrierSet n 0 bzero := by
    ext omega
    simp only [gaussianWalkTimeBarrierSet, mem_setOf_eq]
    have h := gaussianWalkTimeBarrierSurvives_add_const
      n s 0 bzero omega
    simpa only [zero_add, add_zero, bzeroS, bzero, add_assoc, add_comm,
      add_left_comm] using! h
  calc
    μ.real (gaussianWalkTimeBarrierSet n s bstart) ≤
        μ.real (gaussianWalkTimeBarrierSet n s bzeroS) := by
      exact measureReal_mono hsubset
        (measure_ne_top μ (gaussianWalkTimeBarrierSet n s bzeroS))
    _ = μ.real (gaussianWalkTimeBarrierSet n 0 bzero) := by rw [hshift]
    _ ≤ 44000000 * (x + 1) / Real.sqrt (n : ℝ) := by
      exact gaussianVarianceWalk_quarter_one_positiveLogBarrier_probability_le_fin
        n hn variance hx hlower hupper

end
end Problem520
end Erdos
