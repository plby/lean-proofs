import ErdosProblems.Erdos520.HarperGaussianWalk

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Erdos.Problem520

noncomputable section

/-!
# Independent Gaussian walks with varying variances

This module upgrades the iid Gaussian ballot estimate to finite independent
centered Gaussian increments whose variances stay in a fixed interval.  It
keeps exact product-space laws and Markov concatenation, then repeats the
dyadic square-root bootstrap with explicit constants.  The final specialized
corollaries cover variances in `[1/3, 3/8]` and logarithmic barriers.
-/

theorem integral_Iic_gaussianReal_scaled_barrierPotential_le
    {v : ℝ≥0} (hv : v ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    (∫ z in Iic x, (x - z + 2 * Real.sqrt (v : ℝ))
        ∂gaussianReal 0 v) ≤
      x + 2 * Real.sqrt (v : ℝ) := by
  let s : ℝ := Real.sqrt (v : ℝ)
  have hvreal : 0 < (v : ℝ) := by positivity
  have hs : 0 < s := Real.sqrt_pos.2 hvreal
  have hmap :
      (gaussianReal 0 1).map (fun w : ℝ ↦ s * w) =
        gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    simp only [mul_zero]
    congr
    ext
    simp only [NNReal.coe_mk, mul_one]
    exact Real.sq_sqrt hvreal.le
  rw [← hmap]
  rw [MeasureTheory.setIntegral_map measurableSet_Iic (by fun_prop) (by fun_prop)]
  have hpre : (fun w : ℝ ↦ s * w) ⁻¹' Iic x = Iic (x / s) := by
    ext w
    simp only [mem_preimage, mem_Iic]
    exact (le_div_iff₀' hs).symm
  rw [hpre]
  have hbase := integral_Iic_gaussianReal_barrierPotential_le
    (x := x / s) (div_nonneg hx hs.le)
  calc
    (∫ w in Iic (x / s), (x - s * w + 2 * s) ∂gaussianReal 0 1) =
        ∫ w in Iic (x / s), s * (x / s - w + 2) ∂gaussianReal 0 1 := by
      apply integral_congr_ae
      filter_upwards [] with w
      field_simp
    _ = s * (∫ w in Iic (x / s), (x / s - w + 2) ∂gaussianReal 0 1) := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ s * (x / s + 2) := mul_le_mul_of_nonneg_left hbase hs.le
    _ = x + 2 * s := by
      field_simp
    _ = x + 2 * Real.sqrt (v : ℝ) := rfl

theorem integral_Iic_gaussianReal_barrierPotential_le_of_sqrt_le
    {v : ℝ≥0} (hv : v ≠ 0) {L x : ℝ} (hx : 0 ≤ x)
    (hvL : Real.sqrt (v : ℝ) ≤ L) :
    (∫ z in Iic x, (x - z + 2 * L) ∂gaussianReal 0 v) ≤ x + 2 * L := by
  let s : ℝ := Real.sqrt (v : ℝ)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hdiff : 0 ≤ 2 * (L - s) := by
    exact mul_nonneg (by norm_num) (sub_nonneg.mpr (by simpa only [s] using! hvL))
  have hbase := integral_Iic_gaussianReal_scaled_barrierPotential_le hv hx
  have hint : IntegrableOn (fun z : ℝ ↦ x - z + 2 * s) (Iic x)
      (gaussianReal 0 v) := by
    have hid : Integrable (fun z : ℝ ↦ z) (gaussianReal 0 v) :=
      memLp_one_iff_integrable.mp
        (by simpa only [id_eq] using!
          (memLp_id_gaussianReal' (μ := 0) (v := v) 1 (by norm_num)))
    exact (((integrable_const (x : ℝ)).sub hid).add
      (integrable_const (2 * s))).integrableOn
  have hconst : IntegrableOn (fun _z : ℝ ↦ 2 * (L - s)) (Iic x)
      (gaussianReal 0 v) := integrableOn_const
  calc
    (∫ z in Iic x, (x - z + 2 * L) ∂gaussianReal 0 v) =
        ∫ z in Iic x, ((x - z + 2 * s) + 2 * (L - s))
          ∂gaussianReal 0 v := by
      apply integral_congr_ae
      filter_upwards [] with z
      ring
    _ = (∫ z in Iic x, (x - z + 2 * s) ∂gaussianReal 0 v) +
        ∫ _z in Iic x, 2 * (L - s) ∂gaussianReal 0 v := by
      rw [integral_add hint hconst]
    _ = (∫ z in Iic x, (x - z + 2 * s) ∂gaussianReal 0 v) +
        (gaussianReal 0 v).real (Iic x) * (2 * (L - s)) := by
      rw [setIntegral_const]
      simp only [smul_eq_mul]
    _ ≤ (x + 2 * s) + 1 * (2 * (L - s)) := by
      apply add_le_add
      · simpa only [s] using! hbase
      · exact mul_le_mul_of_nonneg_right measureReal_le_one hdiff
    _ = x + 2 * L := by ring

noncomputable def gaussianVarianceKilledExpectation :
    List ℝ≥0 → (ℝ → ℝ) → ℝ → ℝ
  | [], f, x => f x
  | v :: vs, f, x =>
      ∫ z in Iic x, gaussianVarianceKilledExpectation vs f (x - z) ∂gaussianReal 0 v

@[simp] theorem gaussianVarianceKilledExpectation_nil (f : ℝ → ℝ) (x : ℝ) :
    gaussianVarianceKilledExpectation [] f x = f x := rfl

@[simp] theorem gaussianVarianceKilledExpectation_cons (v : ℝ≥0) (vs : List ℝ≥0)
    (f : ℝ → ℝ) (x : ℝ) :
    gaussianVarianceKilledExpectation (v :: vs) f x =
      ∫ z in Iic x, gaussianVarianceKilledExpectation vs f (x-z) ∂gaussianReal 0 v := rfl

theorem gaussianVarianceKilledExpectation_append (us vs : List ℝ≥0) (f : ℝ → ℝ) (x : ℝ) :
    gaussianVarianceKilledExpectation (us ++ vs) f x =
      gaussianVarianceKilledExpectation us (gaussianVarianceKilledExpectation vs f) x := by
  induction us generalizing x with
  | nil => simp
  | cons u us ih =>
      simp only [List.cons_append, gaussianVarianceKilledExpectation_cons]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z ↦ ih (x-z)

noncomputable def gaussianVarianceWalkMeasure (vs : List ℝ≥0) :
    Measure (Fin vs.length → ℝ) :=
  Measure.pi fun i ↦ gaussianReal 0 (vs.get i)

instance (vs : List ℝ≥0) : IsProbabilityMeasure (gaussianVarianceWalkMeasure vs) := by
  unfold gaussianVarianceWalkMeasure
  infer_instance

theorem integrable_gaussianWalkKilledTerminalPayoff_variances
    {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ y, ‖f y‖ ≤ C) (vs : List ℝ≥0) (x : ℝ) :
    Integrable (gaussianWalkKilledTerminalPayoff f vs.length x)
      (gaussianVarianceWalkMeasure vs) := by
  exact (integrable_const (μ := gaussianVarianceWalkMeasure vs) C).mono'
    (measurable_gaussianWalkKilledTerminalPayoff hf vs.length x).aestronglyMeasurable
    (Filter.Eventually.of_forall
      (norm_gaussianWalkKilledTerminalPayoff_le hC vs.length x))

theorem integral_gaussianWalkKilledTerminalPayoff_variances_eq
    {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ y, ‖f y‖ ≤ C) (vs : List ℝ≥0) (x : ℝ) :
    (∫ omega : Fin vs.length → ℝ,
        gaussianWalkKilledTerminalPayoff f vs.length x omega
        ∂gaussianVarianceWalkMeasure vs) = gaussianVarianceKilledExpectation vs f x := by
  induction vs generalizing x with
  | nil => simp [gaussianWalkKilledTerminalPayoff, gaussianVarianceKilledExpectation,
      gaussianVarianceWalkMeasure]
  | cons v vs ih =>
      change (∫ omega : Fin (vs.length + 1) → ℝ,
        gaussianWalkKilledTerminalPayoff f (vs.length + 1) x omega
        ∂gaussianVarianceWalkMeasure (v :: vs)) = gaussianVarianceKilledExpectation (v :: vs) f x
      let gamma : Measure ℝ := gaussianReal 0 v
      let Ptail : Measure (Fin vs.length → ℝ) := gaussianVarianceWalkMeasure vs
      let e := MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (vs.length + 1) ↦ ℝ) 0
      have hmp0 :=
        (measurePreserving_piFinSuccAbove
          (fun i : Fin (vs.length + 1) ↦
            gaussianReal 0 ((v :: vs).get i)) 0).symm
      have hmp : MeasurePreserving e.symm
          (gamma.prod Ptail) (gaussianVarianceWalkMeasure (v :: vs)) := by
        simpa only [gamma, Ptail, gaussianVarianceWalkMeasure, List.length_cons,
          List.get_eq_getElem] using! hmp0
      have he_symm (p : ℝ × (Fin vs.length → ℝ)) :
          e.symm p = Fin.cons p.1 p.2 := by
        ext i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv]
        · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv, Fin.zero_succAbove]
      have hint : Integrable
          (fun p : ℝ × (Fin vs.length → ℝ) ↦
            gaussianWalkKilledTerminalPayoff f (vs.length + 1) x (e.symm p))
          (gamma.prod Ptail) := by
        exact hmp.integrable_comp_of_integrable
          (by simpa only [List.length_cons] using!
            integrable_gaussianWalkKilledTerminalPayoff_variances hf hC (v :: vs) x)
      rw [← hmp.integral_comp']
      rw [integral_prod _ hint]
      simp_rw [he_symm]
      simp only [Fin.cons_zero, Fin.cons_succ,
        gaussianWalkKilledTerminalPayoff]
      rw [gaussianVarianceKilledExpectation_cons]
      rw [← integral_indicator measurableSet_Iic]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z ↦ by
        by_cases hz : z ≤ x
        · simp only [hz, if_true, mem_Iic, Set.indicator_of_mem]
          simpa only [Ptail] using! ih (x-z)
        · have hnot : z ∉ Iic x := hz
          simp only [hz, if_false, integral_zero,
            Set.indicator_of_notMem hnot]

private theorem sum_get_coe (vs : List ℝ≥0) :
    (∑ i : Fin vs.length, ((vs.get i : ℝ≥0) : ℝ)) = (vs.sum : ℝ) := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
      change (∑ i : Fin (vs.length + 1),
        (((v :: vs).get i : ℝ≥0) : ℝ)) = ((v :: vs).sum : ℝ)
      rw [Fin.sum_univ_succ]
      simpa using! congrArg (fun y : ℝ ↦ (v : ℝ) + y) ih

private theorem coe_sum_eq_map (vs : List ℝ≥0) :
    ((vs.sum : ℝ≥0) : ℝ) = (vs.map NNReal.toReal).sum := by
  induction vs with
  | nil => simp
  | cons v vs ih => simp [ih]

theorem map_gaussianVarianceWalk_sum_eq (vs : List ℝ≥0) :
    (gaussianVarianceWalkMeasure vs).map (fun omega ↦ ∑ i, omega i) =
      gaussianReal 0 vs.sum := by
  apply Measure.ext_of_charFun
  ext t
  unfold gaussianVarianceWalkMeasure
  rw [charFun_map_sum_pi_eq_prod]
  rw [Fintype.prod_apply]
  simp_rw [charFun_gaussianReal]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_zero]
  push_cast
  have hsum : (∑ i : Fin vs.length, ((vs.get i : ℝ≥0) : ℂ)) =
      ((vs.sum : ℝ≥0) : ℂ) := by
    exact_mod_cast sum_get_coe vs
  have hcoe : (((vs.sum : ℝ≥0) : ℝ) : ℂ) =
      (((vs.map NNReal.toReal).sum : ℝ) : ℂ) := by
    exact_mod_cast coe_sum_eq_map vs
  rw [show (∑ i : Fin vs.length,
      ((t : ℂ) * 0 * Complex.I - ((vs.get i : ℝ≥0) : ℂ) * (t : ℂ) ^ 2 / 2)) =
      -(∑ i : Fin vs.length, ((vs.get i : ℝ≥0) : ℂ)) * (t : ℂ) ^ 2 / 2 by
        simp only [mul_zero, zero_mul, zero_sub, div_eq_mul_inv, mul_assoc]
        rw [← Finset.sum_neg_distrib, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
    ]
  rw [hsum]
  rw [hcoe]
  ring

theorem map_gaussianVarianceWalk_terminal_eq (vs : List ℝ≥0) (x : ℝ) :
    (gaussianVarianceWalkMeasure vs).map (gaussianWalkTerminalDistance vs.length x) =
      gaussianReal x vs.sum := by
  let S : (Fin vs.length → ℝ) → ℝ := fun omega ↦ ∑ i, omega i
  have hfun : gaussianWalkTerminalDistance vs.length x =
      (fun z ↦ x-z) ∘ S := by
    funext omega
    rfl
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop),
    show (gaussianVarianceWalkMeasure vs).map S = gaussianReal 0 vs.sum by
      simpa only [S] using! map_gaussianVarianceWalk_sum_eq vs,
    gaussianReal_map_const_sub]
  simp only [sub_zero]

private theorem integrable_id_gaussianReal_variance (v : ℝ≥0) :
    Integrable (fun z : ℝ ↦ z) (gaussianReal 0 v) :=
  memLp_one_iff_integrable.mp
    (by simpa only [id_eq] using!
      (memLp_id_gaussianReal' (μ := 0) (v := v) 1 (by norm_num)))

theorem integrable_gaussianWalkKilledPayoff_variances (vs : List ℝ≥0) (x : ℝ) :
    Integrable (gaussianWalkKilledPayoff vs.length x) (gaussianVarianceWalkMeasure vs) := by
  have heval (i : Fin vs.length) :
      Integrable (fun omega : Fin vs.length → ℝ ↦ omega i)
        (gaussianVarianceWalkMeasure vs) := by
    unfold gaussianVarianceWalkMeasure
    exact integrable_eval (integrable_id_gaussianReal_variance (vs.get i))
  have habs (i : Fin vs.length) :
      Integrable (fun omega : Fin vs.length → ℝ ↦ |omega i|)
        (gaussianVarianceWalkMeasure vs) := by
    simpa only [Real.norm_eq_abs] using! (heval i).norm
  have hmajorant : Integrable
      (fun omega : Fin vs.length → ℝ ↦
        |x| + ∑ i, |omega i| + 2) (gaussianVarianceWalkMeasure vs) := by
    fun_prop
  exact hmajorant.mono'
    (measurable_gaussianWalkKilledPayoff vs.length x).aestronglyMeasurable
    (Filter.Eventually.of_forall
      (norm_gaussianWalkKilledPayoff_le vs.length x))

noncomputable def gaussianVarianceKilledPotential (vs : List ℝ≥0) (x : ℝ) : ℝ :=
  gaussianVarianceKilledExpectation vs (fun y ↦ y + 2) x

theorem integral_gaussianWalkKilledPayoff_variances_eq (vs : List ℝ≥0) (x : ℝ) :
    (∫ omega : Fin vs.length → ℝ,
      gaussianWalkKilledPayoff vs.length x omega ∂gaussianVarianceWalkMeasure vs) =
      gaussianVarianceKilledPotential vs x := by
  induction vs generalizing x with
  | nil => simp [gaussianWalkKilledPayoff, gaussianVarianceKilledPotential,
      gaussianVarianceKilledExpectation, gaussianVarianceWalkMeasure]
  | cons v vs ih =>
      change (∫ omega : Fin (vs.length + 1) → ℝ,
        gaussianWalkKilledPayoff (vs.length + 1) x omega
        ∂gaussianVarianceWalkMeasure (v :: vs)) = gaussianVarianceKilledPotential (v :: vs) x
      let gamma : Measure ℝ := gaussianReal 0 v
      let Ptail : Measure (Fin vs.length → ℝ) := gaussianVarianceWalkMeasure vs
      let e := MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (vs.length + 1) ↦ ℝ) 0
      have hmp0 :=
        (measurePreserving_piFinSuccAbove
          (fun i : Fin (vs.length + 1) ↦
            gaussianReal 0 ((v :: vs).get i)) 0).symm
      have hmp : MeasurePreserving e.symm
          (gamma.prod Ptail) (gaussianVarianceWalkMeasure (v :: vs)) := by
        simpa only [gamma, Ptail, gaussianVarianceWalkMeasure, List.length_cons,
          List.get_eq_getElem] using! hmp0
      have he_symm (p : ℝ × (Fin vs.length → ℝ)) :
          e.symm p = Fin.cons p.1 p.2 := by
        ext i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv]
        · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv, Fin.zero_succAbove]
      have hint : Integrable
          (fun p : ℝ × (Fin vs.length → ℝ) ↦
            gaussianWalkKilledPayoff (vs.length + 1) x (e.symm p))
          (gamma.prod Ptail) := by
        exact hmp.integrable_comp_of_integrable
          (by simpa only [List.length_cons] using!
            integrable_gaussianWalkKilledPayoff_variances (v :: vs) x)
      rw [← hmp.integral_comp']
      rw [integral_prod _ hint]
      simp_rw [he_symm]
      simp only [Fin.cons_zero, Fin.cons_succ,
        gaussianWalkKilledPayoff_succ]
      simp only [gaussianVarianceKilledPotential, gaussianVarianceKilledExpectation_cons]
      rw [← integral_indicator measurableSet_Iic]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z ↦ by
        by_cases hz : z ≤ x
        · simp only [hz, if_true, mem_Iic, Set.indicator_of_mem]
          simpa only [Ptail, gaussianVarianceKilledPotential] using! ih (x-z)
        · have hnot : z ∉ Iic x := hz
          simp only [hz, if_false, integral_zero,
            Set.indicator_of_notMem hnot]

theorem gaussianVarianceKilledPotential_nonneg_le
    (vs : List ℝ≥0) {x : ℝ} (hx : 0 ≤ x)
    (hupper : ∀ v ∈ vs, v ≠ 0 ∧ Real.sqrt (v : ℝ) ≤ 1) :
    0 ≤ gaussianVarianceKilledPotential vs x ∧ gaussianVarianceKilledPotential vs x ≤ x + 2 := by
  induction vs generalizing x with
  | nil =>
      simp [gaussianVarianceKilledPotential, gaussianVarianceKilledExpectation]
      linarith
  | cons v vs ih =>
      have hv : v ≠ 0 := (hupper v (by simp)).1
      have hvone : Real.sqrt (v : ℝ) ≤ 1 := (hupper v (by simp)).2
      have htail : ∀ w ∈ vs, w ≠ 0 ∧ Real.sqrt (w : ℝ) ≤ 1 := by
        intro w hw
        exact hupper w (by simp [hw])
      simp only [gaussianVarianceKilledPotential, gaussianVarianceKilledExpectation_cons]
      have hnonneg : 0 ≤ᵐ[(gaussianReal 0 v).restrict (Iic x)]
          fun z ↦ gaussianVarianceKilledExpectation vs (fun y ↦ y + 2) (x-z) := by
        exact (ae_restrict_mem measurableSet_Iic).mono fun z hz ↦
          (ih (sub_nonneg.mpr hz) htail).1
      have hle : (fun z ↦
          gaussianVarianceKilledExpectation vs (fun y ↦ y + 2) (x-z)) ≤ᵐ[
          (gaussianReal 0 v).restrict (Iic x)] fun z ↦ x-z+2 := by
        exact (ae_restrict_mem measurableSet_Iic).mono fun z hz ↦
          (ih (sub_nonneg.mpr hz) htail).2
      constructor
      · exact integral_nonneg_of_ae hnonneg
      · calc
          (∫ z in Iic x,
              gaussianVarianceKilledExpectation vs (fun y ↦ y + 2) (x-z)
              ∂gaussianReal 0 v) ≤
              ∫ z in Iic x, (x-z+2) ∂gaussianReal 0 v := by
            exact integral_mono_of_nonneg hnonneg
              (((integrable_const x).sub
                (integrable_id_gaussianReal_variance v)).add
                  (integrable_const 2)).integrableOn hle
          _ ≤ x + 2 := by
            simpa only [mul_one] using!
              integral_Iic_gaussianReal_barrierPotential_le_of_sqrt_le hv hx hvone

theorem integralOn_gaussianVarianceWalk_survival_affine_eq
    (vs : List ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    (∫ omega in gaussianWalkSurvivalSet vs.length x,
        (gaussianWalkTerminalDistance vs.length x omega + 2)
        ∂gaussianVarianceWalkMeasure vs) = gaussianVarianceKilledPotential vs x := by
  calc
    (∫ omega in gaussianWalkSurvivalSet vs.length x,
        (gaussianWalkTerminalDistance vs.length x omega + 2)
        ∂gaussianVarianceWalkMeasure vs) =
        ∫ omega : Fin vs.length → ℝ,
          gaussianWalkKilledPayoff vs.length x omega
          ∂gaussianVarianceWalkMeasure vs := by
      rw [← integral_indicator
        (measurableSet_gaussianWalkSurvivalSet vs.length hx)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun omega ↦ by
        by_cases h : gaussianWalkSurvives vs.length x omega
        · have hmem : omega ∈ gaussianWalkSurvivalSet vs.length x := h
          rw [Set.indicator_of_mem hmem,
            gaussianWalkKilledPayoff_eq_of_survives vs.length x omega h]
        · have hmem : omega ∉ gaussianWalkSurvivalSet vs.length x := h
          rw [Set.indicator_of_notMem hmem,
            gaussianWalkKilledPayoff_eq_zero_of_not_survives vs.length x omega h]
    _ = gaussianVarianceKilledPotential vs x := integral_gaussianWalkKilledPayoff_variances_eq vs x

theorem integrable_gaussianVarianceWalk_terminalDistance (vs : List ℝ≥0) (x : ℝ) :
    Integrable (gaussianWalkTerminalDistance vs.length x) (gaussianVarianceWalkMeasure vs) := by
  have heval (i : Fin vs.length) :
      Integrable (fun omega : Fin vs.length → ℝ ↦ omega i)
        (gaussianVarianceWalkMeasure vs) := by
    unfold gaussianVarianceWalkMeasure
    exact integrable_eval (integrable_id_gaussianReal_variance (vs.get i))
  have hsum : Integrable (fun omega : Fin vs.length → ℝ ↦
      ∑ i, omega i) (gaussianVarianceWalkMeasure vs) := by
    simpa only [Finset.sum_apply] using!
      (integrable_finset_sum Finset.univ (fun i _hi ↦ heval i))
  exact (integrable_const x).sub hsum

theorem integralOn_gaussianVarianceWalkSurvival_eq_killedExpectation
    {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ y, ‖f y‖ ≤ C) (vs : List ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    (∫ omega in gaussianWalkSurvivalSet vs.length x,
        f (gaussianWalkTerminalDistance vs.length x omega)
        ∂gaussianVarianceWalkMeasure vs) = gaussianVarianceKilledExpectation vs f x := by
  calc
    (∫ omega in gaussianWalkSurvivalSet vs.length x,
        f (gaussianWalkTerminalDistance vs.length x omega)
        ∂gaussianVarianceWalkMeasure vs) =
        ∫ omega : Fin vs.length → ℝ,
          gaussianWalkKilledTerminalPayoff f vs.length x omega
          ∂gaussianVarianceWalkMeasure vs := by
      rw [← integral_indicator
        (measurableSet_gaussianWalkSurvivalSet vs.length hx)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun omega ↦ by
        by_cases h : gaussianWalkSurvives vs.length x omega
        · have hmem : omega ∈ gaussianWalkSurvivalSet vs.length x := h
          rw [Set.indicator_of_mem hmem,
            gaussianWalkKilledTerminalPayoff_eq_of_survives f vs.length x omega h]
        · have hmem : omega ∉ gaussianWalkSurvivalSet vs.length x := h
          rw [Set.indicator_of_notMem hmem,
            gaussianWalkKilledTerminalPayoff_eq_zero_of_not_survives
              f vs.length x omega h]
    _ = gaussianVarianceKilledExpectation vs f x :=
      integral_gaussianWalkKilledTerminalPayoff_variances_eq hf hC vs x

noncomputable def gaussianVarianceWalkSurvivalProbability (vs : List ℝ≥0) (x : ℝ) : ℝ :=
  gaussianVarianceKilledExpectation vs (fun _ ↦ 1) x

theorem gaussianVarianceWalkSurvivalProbability_nonneg_le_one (vs : List ℝ≥0) (x : ℝ) :
    0 ≤ gaussianVarianceWalkSurvivalProbability vs x ∧
      gaussianVarianceWalkSurvivalProbability vs x ≤ 1 := by
  have hint := integrable_gaussianWalkKilledTerminalPayoff_variances
    (f := fun _ : ℝ ↦ (1 : ℝ)) measurable_const
    (C := 1) (fun _ ↦ by norm_num) vs x
  have heq := integral_gaussianWalkKilledTerminalPayoff_variances_eq
    (f := fun _ : ℝ ↦ (1 : ℝ)) measurable_const
    (C := 1) (fun _ ↦ by norm_num) vs x
  have hnonneg : ∀ omega : Fin vs.length → ℝ,
      0 ≤ gaussianWalkKilledTerminalPayoff
        (fun _ : ℝ ↦ (1 : ℝ)) vs.length x omega := by
    intro omega
    by_cases h : gaussianWalkSurvives vs.length x omega
    · rw [gaussianWalkKilledTerminalPayoff_eq_of_survives _ vs.length x omega h]
      norm_num
    · rw [gaussianWalkKilledTerminalPayoff_eq_zero_of_not_survives
          _ vs.length x omega h]
  have hle : ∀ omega : Fin vs.length → ℝ,
      gaussianWalkKilledTerminalPayoff
        (fun _ : ℝ ↦ (1 : ℝ)) vs.length x omega ≤ 1 := by
    intro omega
    by_cases h : gaussianWalkSurvives vs.length x omega
    · rw [gaussianWalkKilledTerminalPayoff_eq_of_survives _ vs.length x omega h]
    · rw [gaussianWalkKilledTerminalPayoff_eq_zero_of_not_survives
          _ vs.length x omega h]
      norm_num
  change 0 ≤ gaussianVarianceKilledExpectation vs (fun _ ↦ (1 : ℝ)) x ∧
    gaussianVarianceKilledExpectation vs (fun _ ↦ (1 : ℝ)) x ≤ 1
  rw [← heq]
  constructor
  · exact integral_nonneg hnonneg
  · calc
      (∫ omega : Fin vs.length → ℝ,
          gaussianWalkKilledTerminalPayoff
            (fun _ : ℝ ↦ (1 : ℝ)) vs.length x omega
          ∂gaussianVarianceWalkMeasure vs) ≤
          ∫ _omega : Fin vs.length → ℝ, (1 : ℝ)
            ∂gaussianVarianceWalkMeasure vs := by
        exact integral_mono hint (integrable_const 1) hle
      _ = 1 := by simp

theorem measurable_gaussianVarianceWalkSurvivalProbability (vs : List ℝ≥0) :
    Measurable (gaussianVarianceWalkSurvivalProbability vs) := by
  have hjoint := measurable_gaussianWalkKilledTerminalPayoff_joint
    (f := fun _ : ℝ ↦ (1 : ℝ)) measurable_const vs.length
  have hintMeas : Measurable (fun x : ℝ ↦
      ∫ omega : Fin vs.length → ℝ,
        gaussianWalkKilledTerminalPayoff
          (fun _ : ℝ ↦ (1 : ℝ)) vs.length x omega
        ∂gaussianVarianceWalkMeasure vs) :=
    hjoint.stronglyMeasurable.integral_prod_right.measurable
  convert! hintMeas using 1
  funext x
  exact (integral_gaussianWalkKilledTerminalPayoff_variances_eq
    (f := fun _ : ℝ ↦ (1 : ℝ)) measurable_const
    (C := 1) (fun _ ↦ by norm_num) vs x).symm

theorem gaussianVarianceWalkSurvivalProbability_eq_measureReal
    (vs : List ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    gaussianVarianceWalkSurvivalProbability vs x =
      (gaussianVarianceWalkMeasure vs).real (gaussianWalkSurvivalSet vs.length x) := by
  have h := integralOn_gaussianVarianceWalkSurvival_eq_killedExpectation
    (f := fun _ : ℝ ↦ (1 : ℝ)) measurable_const
    (C := 1) (fun _ ↦ by norm_num) vs hx
  simpa only [gaussianVarianceWalkSurvivalProbability, setIntegral_const,
    smul_eq_mul, one_mul, mul_one] using! h.symm

theorem gaussianVarianceWalkSurvivalProbability_append (us vs : List ℝ≥0) (x : ℝ) :
    gaussianVarianceWalkSurvivalProbability (us ++ vs) x =
      gaussianVarianceKilledExpectation us (gaussianVarianceWalkSurvivalProbability vs) x := by
  simpa only [gaussianVarianceWalkSurvivalProbability] using!
    gaussianVarianceKilledExpectation_append us vs (fun _ ↦ (1 : ℝ)) x

theorem gaussianVarianceWalkSurvivalProbability_append_eq_integralOn
    (us vs : List ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    gaussianVarianceWalkSurvivalProbability (us ++ vs) x =
      ∫ omega in gaussianWalkSurvivalSet us.length x,
        gaussianVarianceWalkSurvivalProbability vs
          (gaussianWalkTerminalDistance us.length x omega)
        ∂gaussianVarianceWalkMeasure us := by
  rw [gaussianVarianceWalkSurvivalProbability_append]
  symm
  apply integralOn_gaussianVarianceWalkSurvival_eq_killedExpectation
    (measurable_gaussianVarianceWalkSurvivalProbability vs) (C := 1) _ us hx
  intro y
  rw [Real.norm_eq_abs, abs_of_nonneg
    (gaussianVarianceWalkSurvivalProbability_nonneg_le_one vs y).1]
  exact (gaussianVarianceWalkSurvivalProbability_nonneg_le_one vs y).2

theorem gaussianVarianceWalkSurvivalProbability_le_fourthRoot
    (vs : List ℝ≥0) {x : ℝ} (hx : 0 ≤ x)
    (hsum : vs.sum ≠ 0)
    (hupper : ∀ v ∈ vs, v ≠ 0 ∧ Real.sqrt (v : ℝ) ≤ 1) :
    gaussianVarianceWalkSurvivalProbability vs x ≤
      2 * Real.sqrt (x + 2) /
        Real.sqrt (Real.sqrt (vs.sum : ℝ)) := by
  let P : Measure (Fin vs.length → ℝ) := gaussianVarianceWalkMeasure vs
  let A : Set (Fin vs.length → ℝ) :=
    gaussianWalkSurvivalSet vs.length x
  let D : (Fin vs.length → ℝ) → ℝ :=
    gaussianWalkTerminalDistance vs.length x
  have hA : MeasurableSet A :=
    measurableSet_gaussianWalkSurvivalSet vs.length hx
  have hDmeas : Measurable D := by
    unfold D gaussianWalkTerminalDistance
    fun_prop
  have hlaw : P.map D = gaussianReal x vs.sum := by
    simpa only [P, D] using! map_gaussianVarianceWalk_terminal_eq vs x
  have hD0 : ∀ omega ∈ A, 0 ≤ D omega := by
    intro omega homega
    exact gaussianWalkTerminalDistance_nonneg_of_survives
      vs.length x omega hx homega
  have hint : IntegrableOn (fun omega ↦ D omega + 2) A P := by
    have hfull : Integrable (fun omega ↦ D omega + 2) P := by
      have hterm := integrable_gaussianVarianceWalk_terminalDistance vs x
      have hc := integrable_const (μ := gaussianVarianceWalkMeasure vs) (2 : ℝ)
      simpa only [P, D] using! hterm.add hc
    exact hfull.integrableOn
  have hweighted : (∫ omega in A, (D omega + 2) ∂P) ≤ x + 2 := by
    have heq := integralOn_gaussianVarianceWalk_survival_affine_eq vs hx
    rw [show (∫ omega in A, (D omega + 2) ∂P) =
        gaussianVarianceKilledPotential vs x by simpa only [P, A, D] using! heq]
    exact (gaussianVarianceKilledPotential_nonneg_le vs hx hupper).2
  rw [gaussianVarianceWalkSurvivalProbability_eq_measureReal vs hx]
  exact measureReal_gaussianWalk_barrier_le_optimized P hA hDmeas hx hsum
    hlaw hD0 hint hweighted

private theorem lower_mul_length_le_sum
    (lo : ℝ≥0) (vs : List ℝ≥0) (hlower : ∀ v ∈ vs, lo ≤ v) :
    (lo : ℝ) * vs.length ≤ (vs.sum : ℝ) := by
  rw [← sum_get_coe]
  calc
    (lo : ℝ) * vs.length =
        ∑ _i : Fin vs.length, (lo : ℝ) := by
      simp [mul_comm]
    _ ≤ ∑ i : Fin vs.length, ((vs.get i : ℝ≥0) : ℝ) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact_mod_cast hlower (vs.get i) (List.get_mem vs i)

theorem gaussianVarianceWalkSurvivalProbability_le_fourthRoot_of_lower
    (lo : ℝ≥0) (hlo : lo ≠ 0) (vs : List ℝ≥0)
    (hne : vs ≠ []) {x : ℝ} (hx : 0 ≤ x)
    (hlower : ∀ v ∈ vs, lo ≤ v)
    (hupper : ∀ v ∈ vs, Real.sqrt (v : ℝ) ≤ 1) :
    gaussianVarianceWalkSurvivalProbability vs x ≤
      2 * Real.sqrt (x + 2) /
        Real.sqrt (Real.sqrt ((lo : ℝ) * vs.length)) := by
  have heach : ∀ v ∈ vs, v ≠ 0 ∧ Real.sqrt (v : ℝ) ≤ 1 := by
    intro v hv
    refine ⟨?_, hupper v hv⟩
    exact ne_of_gt (lt_of_lt_of_le (show 0 < lo by positivity) (hlower v hv))
  have hsum : vs.sum ≠ 0 := by
    have hlen : 0 < (vs.length : ℝ) := by
      exact_mod_cast (List.length_pos_of_ne_nil hne)
    have hpositive : 0 < (vs.sum : ℝ) :=
      lt_of_lt_of_le (mul_pos (show 0 < (lo : ℝ) by positivity) hlen)
        (lower_mul_length_le_sum lo vs hlower)
    exact_mod_cast hpositive.ne'
  have hsoft := gaussianVarianceWalkSurvivalProbability_le_fourthRoot vs hx hsum heach
  have hvar : (lo : ℝ) * vs.length ≤ (vs.sum : ℝ) :=
    lower_mul_length_le_sum lo vs hlower
  have hden : Real.sqrt (Real.sqrt ((lo : ℝ) * vs.length)) ≤
      Real.sqrt (Real.sqrt (vs.sum : ℝ)) :=
    Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hvar)
  have hnum : 0 ≤ 2 * Real.sqrt (x + 2) := by positivity
  have hlen : 0 < (vs.length : ℝ) := by
    exact_mod_cast (List.length_pos_of_ne_nil hne)
  have hdenpos : 0 < Real.sqrt (Real.sqrt ((lo : ℝ) * vs.length)) := by
    positivity
  exact hsoft.trans (div_le_div_of_nonneg_left hnum
    hdenpos hden)

theorem gaussianVarianceWalkSurvivalProbability_append_le
    (lo : ℝ≥0) (hlo : lo ≠ 0) (us vs : List ℝ≥0)
    (hvsne : vs ≠ []) {x : ℝ} (hx : 0 ≤ x)
    (husupper : ∀ v ∈ us, v ≠ 0 ∧ Real.sqrt (v : ℝ) ≤ 1)
    (hvslower : ∀ v ∈ vs, lo ≤ v)
    (hvsupper : ∀ v ∈ vs, Real.sqrt (v : ℝ) ≤ 1) :
    gaussianVarianceWalkSurvivalProbability (us ++ vs) x ≤
      (2 / Real.sqrt (Real.sqrt ((lo : ℝ) * vs.length))) *
        (Real.sqrt (gaussianVarianceWalkSurvivalProbability us x) * Real.sqrt (x + 2)) := by
  let P : Measure (Fin us.length → ℝ) := gaussianVarianceWalkMeasure us
  let A : Set (Fin us.length → ℝ) :=
    gaussianWalkSurvivalSet us.length x
  let D : (Fin us.length → ℝ) → ℝ :=
    gaussianWalkTerminalDistance us.length x
  let c : ℝ := 2 / Real.sqrt (Real.sqrt ((lo : ℝ) * vs.length))
  have hA : MeasurableSet A :=
    measurableSet_gaussianWalkSurvivalSet us.length hx
  have hDmeas : Measurable D := by
    unfold D gaussianWalkTerminalDistance
    fun_prop
  have hlen : 0 < (vs.length : ℝ) := by
    exact_mod_cast List.length_pos_of_ne_nil hvsne
  have hc0 : 0 ≤ c := by
    dsimp only [c]
    positivity
  have hD0 : ∀ omega ∈ A, 0 ≤ D omega := by
    intro omega homega
    exact gaussianWalkTerminalDistance_nonneg_of_survives
      us.length x omega hx homega
  have hgint : IntegrableOn (fun omega ↦ D omega + 2) A P := by
    have hterm := integrable_gaussianVarianceWalk_terminalDistance us x
    have hc := integrable_const (μ := gaussianVarianceWalkMeasure us) (2 : ℝ)
    have hfull := hterm.add hc
    simpa only [P, D, A] using! hfull.integrableOn
  have hsqrtInt : IntegrableOn (fun omega ↦ Real.sqrt (D omega + 2)) A P := by
    have hmeas : AEStronglyMeasurable
        (fun omega ↦ Real.sqrt (D omega + 2)) (P.restrict A) :=
      (Real.continuous_sqrt.measurable.comp
        (hDmeas.add measurable_const)).aestronglyMeasurable
    have hmajorant : Integrable (fun omega ↦ |D omega + 2| + 1)
        (P.restrict A) := hgint.norm.add (integrable_const 1)
    apply hmajorant.mono' hmeas
    exact Filter.Eventually.of_forall fun omega ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      by_cases ht : 0 ≤ D omega + 2
      · rw [abs_of_nonneg ht]
        nlinarith [Real.sq_sqrt ht, Real.sqrt_nonneg (D omega + 2)]
      · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge ht)]
        positivity
  have hsqrtBound :
      (∫ omega in A, Real.sqrt (D omega + 2) ∂P) ≤
        Real.sqrt (P.real A) *
          Real.sqrt (∫ omega in A, (D omega + 2) ∂P) := by
    have hnonneg : 0 ≤ᵐ[P.restrict A] fun omega ↦ D omega + 2 := by
      exact (ae_restrict_mem hA).mono fun omega homega ↦ by
        change 0 ≤ D omega + 2
        exact add_nonneg (hD0 omega homega) (by norm_num)
    have hcs := integral_sqrt_le_sqrt_measure_mul_integral
      (P.restrict A) (hDmeas.add measurable_const) hnonneg hgint
    rw [measureReal_restrict_apply MeasurableSet.univ, univ_inter] at hcs
    exact hcs
  have hmass : P.real A = gaussianVarianceWalkSurvivalProbability us x := by
    simpa only [P, A] using!
      (gaussianVarianceWalkSurvivalProbability_eq_measureReal us hx).symm
  have hmoment : (∫ omega in A, (D omega + 2) ∂P) ≤ x + 2 := by
    have heq := integralOn_gaussianVarianceWalk_survival_affine_eq us hx
    rw [show (∫ omega in A, (D omega + 2) ∂P) =
        gaussianVarianceKilledPotential us x by simpa only [P, A, D] using! heq]
    exact (gaussianVarianceKilledPotential_nonneg_le us hx husupper).2
  have hsqrtBound' :
      (∫ omega in A, Real.sqrt (D omega + 2) ∂P) ≤
        Real.sqrt (gaussianVarianceWalkSurvivalProbability us x) * Real.sqrt (x + 2) := by
    rw [hmass] at hsqrtBound
    exact hsqrtBound.trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt hmoment) (Real.sqrt_nonneg _))
  calc
    gaussianVarianceWalkSurvivalProbability (us ++ vs) x =
        ∫ omega in A, gaussianVarianceWalkSurvivalProbability vs (D omega) ∂P := by
      simpa only [P, A, D] using!
        gaussianVarianceWalkSurvivalProbability_append_eq_integralOn us vs hx
    _ ≤ ∫ omega in A, c * Real.sqrt (D omega + 2) ∂P := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun omega ↦
          (gaussianVarianceWalkSurvivalProbability_nonneg_le_one vs (D omega)).1
      · exact hsqrtInt.const_mul c
      · exact (ae_restrict_mem hA).mono fun omega homega ↦ by
          have hsoft := gaussianVarianceWalkSurvivalProbability_le_fourthRoot_of_lower
            lo hlo vs hvsne (hD0 omega homega) hvslower hvsupper
          dsimp only [c]
          simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using! hsoft
    _ = c * ∫ omega in A, Real.sqrt (D omega + 2) ∂P := by
      rw [integral_const_mul]
    _ ≤ c * (Real.sqrt (gaussianVarianceWalkSurvivalProbability us x) *
          Real.sqrt (x + 2)) := mul_le_mul_of_nonneg_left hsqrtBound' hc0
    _ = (2 / Real.sqrt (Real.sqrt ((lo : ℝ) * vs.length))) *
        (Real.sqrt (gaussianVarianceWalkSurvivalProbability us x) * Real.sqrt (x + 2)) := rfl

theorem gaussianVarianceWalkSurvivalProbability_double_of_le
    (lo : ℝ≥0) (hlo : lo ≠ 0) (m : ℕ) (hm : 0 < m)
    (us vs : List ℝ≥0) (huslen : us.length = m) (hvslen : vs.length = m)
    {x : ℝ} (hx : 0 ≤ x)
    (huslower : ∀ v ∈ us, lo ≤ v)
    (husupper : ∀ v ∈ us, Real.sqrt (v : ℝ) ≤ 1)
    (hvslower : ∀ v ∈ vs, lo ≤ v)
    (hvsupper : ∀ v ∈ vs, Real.sqrt (v : ℝ) ≤ 1)
    (hprev : gaussianVarianceWalkSurvivalProbability us x ≤
      (16 / Real.sqrt (lo : ℝ)) * (x + 2) / Real.sqrt (m : ℝ)) :
    gaussianVarianceWalkSurvivalProbability (us ++ vs) x ≤
      (16 / Real.sqrt (lo : ℝ)) * (x + 2) /
        Real.sqrt ((m + m : ℕ) : ℝ) := by
  let a : ℝ := x + 2
  let ell : ℝ := Real.sqrt (lo : ℝ)
  let d : ℝ := Real.sqrt ell
  let u : ℝ := Real.sqrt (m : ℝ)
  let r : ℝ := Real.sqrt u
  let s : ℝ := Real.sqrt a
  let p : ℝ := gaussianVarianceWalkSurvivalProbability us x
  have ha : 0 < a := by dsimp [a]; linarith
  have hloReal : 0 < (lo : ℝ) := by positivity
  have hell : 0 < ell := Real.sqrt_pos.2 hloReal
  have hd : 0 < d := Real.sqrt_pos.2 hell
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hu : 0 < u := Real.sqrt_pos.2 hmreal
  have hr : 0 < r := Real.sqrt_pos.2 hu
  have hs : 0 < s := Real.sqrt_pos.2 ha
  have hp0 : 0 ≤ p := gaussianVarianceWalkSurvivalProbability_nonneg_le_one us x |>.1
  have hellSq : ell ^ 2 = (lo : ℝ) := Real.sq_sqrt hloReal.le
  have hdSq : d ^ 2 = ell := Real.sq_sqrt hell.le
  have huSq : u ^ 2 = (m : ℝ) := Real.sq_sqrt hmreal.le
  have hrSq : r ^ 2 = u := Real.sq_sqrt hu.le
  have hsSq : s ^ 2 = a := Real.sq_sqrt ha.le
  have hsqrtP : Real.sqrt p ≤ 4 * s / (d * r) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have heq : (4 * s / (d * r)) ^ 2 =
          (16 / ell) * a / u := by
        field_simp [hd.ne', hr.ne', hell.ne', hu.ne']
        rw [hdSq, hrSq, hsSq]
        ring
      rw [heq]
      simpa only [p, a, ell, u] using! hprev
  have husupper' : ∀ v ∈ us, v ≠ 0 ∧ Real.sqrt (v : ℝ) ≤ 1 := by
    intro v hv
    refine ⟨ne_of_gt (lt_of_lt_of_le (show 0 < lo by positivity)
      (huslower v hv)), husupper v hv⟩
  have hvsne : vs ≠ [] := by
    intro hnil
    have : vs.length = 0 := by simp [hnil]
    omega
  have hboot := gaussianVarianceWalkSurvivalProbability_append_le lo hlo us vs hvsne hx
    husupper' hvslower hvsupper
  have hden : Real.sqrt (Real.sqrt ((lo : ℝ) * vs.length)) = d * r := by
    rw [hvslen]
    have hsqrtMul : Real.sqrt ((lo : ℝ) * (m : ℝ)) = ell * u := by
      rw [Real.sqrt_mul hloReal.le]
    rw [hsqrtMul, Real.sqrt_mul hell.le]
  have hcoarse : gaussianVarianceWalkSurvivalProbability (us ++ vs) x ≤
      8 * a / (ell * u) := by
    calc
      gaussianVarianceWalkSurvivalProbability (us ++ vs) x ≤
          (2 / (d * r)) * (Real.sqrt p * s) := by
        rw [← hden]
        simpa only [p, a, s] using! hboot
      _ ≤ (2 / (d * r)) * ((4 * s / (d * r)) * s) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hsqrtP hs.le) (by positivity)
      _ = 8 * a / (ell * u) := by
        field_simp [hd.ne', hr.ne', hell.ne', hu.ne']
        rw [hdSq, hrSq, hsSq]
        ring
  have hv : 0 < Real.sqrt ((m + m : ℕ) : ℝ) := by
    apply Real.sqrt_pos.2
    positivity
  have hvle : Real.sqrt ((m + m : ℕ) : ℝ) ≤ 2 * u := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · push_cast
      nlinarith
  calc
    gaussianVarianceWalkSurvivalProbability (us ++ vs) x ≤ 8 * a / (ell * u) := hcoarse
    _ ≤ (16 / ell) * a / Real.sqrt ((m + m : ℕ) : ℝ) := by
      apply (div_le_div_iff₀ (mul_pos hell hu) hv).2
      have h8 : 8 * Real.sqrt ((m + m : ℕ) : ℝ) ≤ 16 * u := by
        nlinarith
      field_simp [hell.ne']
      nlinarith
    _ = (16 / Real.sqrt (lo : ℝ)) * (x + 2) /
        Real.sqrt ((m + m : ℕ) : ℝ) := rfl

theorem gaussianVarianceWalkSurvivalProbability_pow_two_le
    (lo : ℝ≥0) (hlo : lo ≠ 0) (k : ℕ) (vs : List ℝ≥0)
    (hlen : vs.length = 2 ^ k) {x : ℝ} (hx : 0 ≤ x)
    (hlower : ∀ v ∈ vs, lo ≤ v)
    (hupper : ∀ v ∈ vs, Real.sqrt (v : ℝ) ≤ 1) :
    gaussianVarianceWalkSurvivalProbability vs x ≤
      (16 / Real.sqrt (lo : ℝ)) * (x + 2) /
        Real.sqrt ((2 ^ k : ℕ) : ℝ) := by
  induction k generalizing vs with
  | zero =>
      have hp := (gaussianVarianceWalkSurvivalProbability_nonneg_le_one vs x).2
      have hne : vs ≠ [] := by
        intro hnil
        simp [hnil] at hlen
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil vs hne
      have hv0 : 0 ≤ (v : ℝ) := by positivity
      have hvle : (v : ℝ) ≤ 1 := by
        have hs := hupper v hv
        simpa using! ((Real.sqrt_le_iff).1 hs).2
      have hlov : (lo : ℝ) ≤ (v : ℝ) := by
        exact_mod_cast hlower v hv
      have hlole : (lo : ℝ) ≤ 1 := hlov.trans hvle
      have hell : 0 < Real.sqrt (lo : ℝ) := Real.sqrt_pos.2 (by positivity)
      have hellle : Real.sqrt (lo : ℝ) ≤ 1 := by
        exact (Real.sqrt_le_iff).2 ⟨by norm_num, by simpa using! hlole⟩
      norm_num only [pow_zero, Nat.cast_one, Real.sqrt_one, div_one]
      have ha : 2 ≤ x + 2 := by linarith
      have hlarge : 1 ≤ (16 / Real.sqrt (lo : ℝ)) * (x + 2) := by
        rw [show (16 / Real.sqrt (lo : ℝ)) * (x + 2) =
            (16 * (x + 2)) / Real.sqrt (lo : ℝ) by ring]
        exact (le_div_iff₀ hell).2 (by nlinarith)
      exact hp.trans hlarge
  | succ k ih =>
      let m : ℕ := 2 ^ k
      let us : List ℝ≥0 := vs.take m
      let ws : List ℝ≥0 := vs.drop m
      have hm : 0 < m := by dsimp [m]; positivity
      have hlen' : vs.length = m + m := by
        simpa only [pow_succ, mul_comm, two_mul, m] using! hlen
      have hmle : m ≤ vs.length := by omega
      have huslen : us.length = m := by simp only [us, List.length_take, min_eq_left hmle]
      have hwslen : ws.length = m := by simp only [ws, List.length_drop]; omega
      have huslower : ∀ v ∈ us, lo ≤ v := by
        intro v hv
        exact hlower v (List.mem_of_mem_take hv)
      have husupper : ∀ v ∈ us, Real.sqrt (v : ℝ) ≤ 1 := by
        intro v hv
        exact hupper v (List.mem_of_mem_take hv)
      have hwslower : ∀ v ∈ ws, lo ≤ v := by
        intro v hv
        exact hlower v (List.mem_of_mem_drop hv)
      have hwsupper : ∀ v ∈ ws, Real.sqrt (v : ℝ) ≤ 1 := by
        intro v hv
        exact hupper v (List.mem_of_mem_drop hv)
      have hprev := ih us huslen huslower husupper
      have hdouble := gaussianVarianceWalkSurvivalProbability_double_of_le
        lo hlo m hm us ws huslen hwslen hx huslower husupper
        hwslower hwsupper hprev
      rw [List.take_append_drop] at hdouble
      simpa only [m, pow_succ, mul_comm, two_mul] using! hdouble

theorem gaussianVarianceWalkSurvivalProbability_append_le_left
    (us vs : List ℝ≥0) {x : ℝ} (hx : 0 ≤ x) :
    gaussianVarianceWalkSurvivalProbability (us ++ vs) x ≤
      gaussianVarianceWalkSurvivalProbability us x := by
  let P : Measure (Fin us.length → ℝ) := gaussianVarianceWalkMeasure us
  let A : Set (Fin us.length → ℝ) := gaussianWalkSurvivalSet us.length x
  have hmarkov := gaussianVarianceWalkSurvivalProbability_append_eq_integralOn us vs hx
  calc
    gaussianVarianceWalkSurvivalProbability (us ++ vs) x =
        ∫ omega in A,
          gaussianVarianceWalkSurvivalProbability vs
            (gaussianWalkTerminalDistance us.length x omega) ∂P := by
      simpa only [P, A] using! hmarkov
    _ ≤ ∫ _omega in A, (1 : ℝ) ∂P := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun omega ↦
          (gaussianVarianceWalkSurvivalProbability_nonneg_le_one vs
            (gaussianWalkTerminalDistance us.length x omega)).1
      · exact integrableOn_const
      · exact Filter.Eventually.of_forall fun omega ↦
          (gaussianVarianceWalkSurvivalProbability_nonneg_le_one vs
            (gaussianWalkTerminalDistance us.length x omega)).2
    _ = P.real A := by
      rw [setIntegral_const]
      simp only [smul_eq_mul, mul_one]
    _ = gaussianVarianceWalkSurvivalProbability us x := by
      simpa only [P, A] using!
        (gaussianVarianceWalkSurvivalProbability_eq_measureReal us hx).symm

theorem gaussianVarianceWalkSurvivalProbability_le
    (lo : ℝ≥0) (hlo : lo ≠ 0) (vs : List ℝ≥0)
    (hne : vs ≠ []) {x : ℝ} (hx : 0 ≤ x)
    (hlower : ∀ v ∈ vs, lo ≤ v)
    (hupper : ∀ v ∈ vs, Real.sqrt (v : ℝ) ≤ 1) :
    gaussianVarianceWalkSurvivalProbability vs x ≤
      (32 / Real.sqrt (lo : ℝ)) * (x + 2) /
        Real.sqrt (vs.length : ℝ) := by
  let n : ℕ := vs.length
  let k : ℕ := Nat.log 2 n
  let p : ℕ := 2 ^ k
  let us : List ℝ≥0 := vs.take p
  have hn : 0 < n := by
    dsimp only [n]
    exact List.length_pos_of_ne_nil hne
  have hp : 0 < p := by dsimp only [p]; positivity
  have hp_le : p ≤ n := Nat.pow_log_le_self 2 hn.ne'
  have hn_lt : n < p + p := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n
    simpa only [k, p, pow_succ, mul_comm, two_mul] using! h
  have huslen : us.length = p := by
    simp only [us, List.length_take, min_eq_left (by simpa only [n] using! hp_le)]
  have huslower : ∀ v ∈ us, lo ≤ v := by
    intro v hv
    exact hlower v (List.mem_of_mem_take hv)
  have husupper : ∀ v ∈ us, Real.sqrt (v : ℝ) ≤ 1 := by
    intro v hv
    exact hupper v (List.mem_of_mem_take hv)
  have hprefix := gaussianVarianceWalkSurvivalProbability_pow_two_le
    lo hlo k us (by simpa only [p] using! huslen) hx huslower husupper
  have hanti : gaussianVarianceWalkSurvivalProbability vs x ≤
      gaussianVarianceWalkSurvivalProbability us x := by
    have h := gaussianVarianceWalkSurvivalProbability_append_le_left us (vs.drop p) hx
    rw [List.take_append_drop] at h
    exact h
  have hpReal : 0 < (p : ℝ) := by exact_mod_cast hp
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  let u : ℝ := Real.sqrt (p : ℝ)
  let v : ℝ := Real.sqrt (n : ℝ)
  let ell : ℝ := Real.sqrt (lo : ℝ)
  have hu : 0 < u := Real.sqrt_pos.2 hpReal
  have hv : 0 < v := Real.sqrt_pos.2 hnReal
  have hell : 0 < ell := Real.sqrt_pos.2 (by positivity)
  have huSq : u ^ 2 = (p : ℝ) := Real.sq_sqrt hpReal.le
  have hvle : v ≤ 2 * u := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have hnCast : (n : ℝ) < (p : ℝ) + p := by exact_mod_cast hn_lt
      dsimp only [u]
      nlinarith
  have ha : 0 ≤ x + 2 := by linarith
  calc
    gaussianVarianceWalkSurvivalProbability vs x ≤
        gaussianVarianceWalkSurvivalProbability us x := hanti
    _ ≤ (16 / Real.sqrt (lo : ℝ)) * (x + 2) /
        Real.sqrt ((2 ^ k : ℕ) : ℝ) := hprefix
    _ = (16 / ell) * (x + 2) / u := by rfl
    _ ≤ (32 / ell) * (x + 2) / v := by
      apply (div_le_div_iff₀ hu hv).2
      have h16 : 16 * v ≤ 32 * u := by nlinarith
      field_simp [hell.ne']
      exact h16
    _ = (32 / Real.sqrt (lo : ℝ)) * (x + 2) /
        Real.sqrt (vs.length : ℝ) := rfl

theorem gaussianVarianceWalk_third_threeEighths_probability_le
    (vs : List ℝ≥0) (hne : vs ≠ []) {x : ℝ} (hx : 0 ≤ x)
    (hlower : ∀ v ∈ vs, (1 / 3 : ℝ≥0) ≤ v)
    (hupper : ∀ v ∈ vs, v ≤ (3 / 8 : ℝ≥0)) :
    (gaussianVarianceWalkMeasure vs).real (gaussianWalkSurvivalSet vs.length x) ≤
      64 * (x + 2) / Real.sqrt (vs.length : ℝ) := by
  have hsqrtUpper : ∀ v ∈ vs, Real.sqrt (v : ℝ) ≤ 1 := by
    intro v hv
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · have hv' : (v : ℝ) ≤ (3 / 8 : ℝ) := by
        exact_mod_cast hupper v hv
      have : (v : ℝ) ≤ 1 := hv'.trans (by norm_num)
      simpa using! this
  have hmain := gaussianVarianceWalkSurvivalProbability_le (1 / 3 : ℝ≥0)
    (by norm_num) vs hne hx hlower hsqrtUpper
  rw [gaussianVarianceWalkSurvivalProbability_eq_measureReal vs hx] at hmain
  have hsqrtlo : (1 / 2 : ℝ) ≤ Real.sqrt ((1 / 3 : ℝ≥0) : ℝ) := by
    rw [show (((1 / 3 : ℝ≥0) : ℝ)) = (1 / 3 : ℝ) by
      norm_num [NNReal.coe_div]]
    have hs0 := Real.sqrt_nonneg (1 / 3 : ℝ)
    have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 3)
    nlinarith
  have hsqrtpos : 0 < Real.sqrt ((1 / 3 : ℝ≥0) : ℝ) := by
    apply Real.sqrt_pos.2
    norm_num [NNReal.coe_div]
  have hconst : 32 / Real.sqrt ((1 / 3 : ℝ≥0) : ℝ) ≤ 64 := by
    apply (div_le_iff₀ hsqrtpos).2
    nlinarith
  have ha : 0 ≤ x + 2 := by linarith
  have hden : 0 < Real.sqrt (vs.length : ℝ) := by
    apply Real.sqrt_pos.2
    exact_mod_cast List.length_pos_of_ne_nil hne
  exact hmain.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hconst ha) hden.le)

theorem gaussianVarianceWalk_third_threeEighths_timeBarrier_probability_le
    (vs : List ℝ≥0) (hne : vs ≠ []) (s B : ℝ)
    (b : Fin vs.length → ℝ) (hstart : 0 ≤ B - s)
    (hb : ∀ i, b i ≤ B)
    (hlower : ∀ v ∈ vs, (1 / 3 : ℝ≥0) ≤ v)
    (hupper : ∀ v ∈ vs, v ≤ (3 / 8 : ℝ≥0)) :
    (gaussianVarianceWalkMeasure vs).real
        (gaussianWalkTimeBarrierSet vs.length s b) ≤
      64 * (B - s + 2) / Real.sqrt (vs.length : ℝ) := by
  have hsubset : gaussianWalkTimeBarrierSet vs.length s b ⊆
      gaussianWalkSurvivalSet vs.length (B-s) := by
    intro omega homega
    have hflat := gaussianWalkTimeBarrierSurvives_mono vs.length s hb homega
    exact (gaussianWalkTimeBarrierSurvives_const_iff
      vs.length s B omega).1 hflat
  exact (measureReal_mono hsubset).trans
    (gaussianVarianceWalk_third_threeEighths_probability_le vs hne hstart hlower hupper)

theorem gaussianVarianceWalk_third_threeEighths_logBarrier_probability_le
    (vs : List ℝ≥0) (hne : vs ≠ []) {x c : ℝ}
    (hx : 0 ≤ x) (hc : 0 ≤ c)
    (hlower : ∀ v ∈ vs, (1 / 3 : ℝ≥0) ≤ v)
    (hupper : ∀ v ∈ vs, v ≤ (3 / 8 : ℝ≥0)) :
    (gaussianVarianceWalkMeasure vs).real
        (gaussianWalkTimeBarrierSet vs.length 0
          (fun i ↦ x + c * Real.log ((i.val + 2 : ℕ) : ℝ))) ≤
      64 * (x + c * Real.log ((vs.length + 1 : ℕ) : ℝ) + 2) /
        Real.sqrt (vs.length : ℝ) := by
  let B : ℝ := x + c * Real.log ((vs.length + 1 : ℕ) : ℝ)
  have hlog0 : 0 ≤ Real.log ((vs.length + 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    norm_num
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hb : ∀ i : Fin vs.length,
      x + c * Real.log ((i.val + 2 : ℕ) : ℝ) ≤ B := by
    intro i
    have hiNat : i.val + 2 ≤ vs.length + 1 := by omega
    have hiReal : ((i.val + 2 : ℕ) : ℝ) ≤
        ((vs.length + 1 : ℕ) : ℝ) := by exact_mod_cast hiNat
    have hilog : Real.log ((i.val + 2 : ℕ) : ℝ) ≤
        Real.log ((vs.length + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) hiReal
    dsimp only [B]
    simpa only [add_comm] using!
      add_le_add_left (mul_le_mul_of_nonneg_left hilog hc) x
  have h := gaussianVarianceWalk_third_threeEighths_timeBarrier_probability_le
    vs hne 0 B (fun i ↦ x + c * Real.log ((i.val + 2 : ℕ) : ℝ))
    (by simpa using! hB) hb hlower hupper
  simpa only [B, sub_zero] using! h

/-! ## Finite-vector wrappers for scheduled blocks -/

theorem gaussianWalkSurvives_reindex_finCongr {m n : ℕ} (h : m = n) (x : ℝ)
    (omega : Fin m → ℝ) :
    gaussianWalkSurvives n x
      (fun j ↦ omega ((finCongr h).symm j)) ↔
      gaussianWalkSurvives m x omega := by
  subst n
  simp

theorem gaussianWalkTimeBarrierSurvives_reindex_finCongr {m n : ℕ} (h : m = n) (s : ℝ)
    (b : Fin m → ℝ) (omega : Fin m → ℝ) :
    gaussianWalkTimeBarrierSurvives n s
      (fun j ↦ b ((finCongr h).symm j))
      (fun j ↦ omega ((finCongr h).symm j)) ↔
      gaussianWalkTimeBarrierSurvives m s b omega := by
  subst n
  simp

theorem measurableSet_gaussianWalkTimeBarrierSurvives_joint (n : ℕ) (b : Fin n → ℝ) :
    MeasurableSet {p : ℝ × (Fin n → ℝ) |
      gaussianWalkTimeBarrierSurvives n p.1 b p.2} := by
  induction n with
  | zero => simp [gaussianWalkTimeBarrierSurvives]
  | succ n ih =>
      simp only [gaussianWalkTimeBarrierSurvives]
      have hhead : Measurable (fun p : ℝ × (Fin (n + 1) → ℝ) ↦ p.2 0) :=
        (measurable_pi_apply 0).comp measurable_snd
      have htail : Measurable
          (fun p : ℝ × (Fin (n + 1) → ℝ) ↦ fun i : Fin n ↦ p.2 i.succ) :=
        measurable_pi_lambda _ fun i ↦
          (measurable_pi_apply i.succ).comp measurable_snd
      apply MeasurableSet.inter
      · exact measurableSet_le (measurable_fst.add hhead) measurable_const
      · exact (ih (fun i ↦ b i.succ)).preimage
          ((measurable_fst.add hhead).prodMk htail)

theorem measurableSet_gaussianWalkTimeBarrierSet (n : ℕ) (s : ℝ) (b : Fin n → ℝ) :
    MeasurableSet (gaussianWalkTimeBarrierSet n s b) := by
  exact (measurableSet_gaussianWalkTimeBarrierSurvives_joint n b).preimage
    (measurable_const.prodMk measurable_id)

theorem gaussianVarianceWalk_third_threeEighths_probability_le_fin
    (n : ℕ) (hn : 0 < n) (variance : Fin n → ℝ≥0)
    {x : ℝ} (hx : 0 ≤ x)
    (hlower : ∀ i, (1 / 3 : ℝ≥0) ≤ variance i)
    (hupper : ∀ i, variance i ≤ (3 / 8 : ℝ≥0)) :
    (Measure.pi (fun i : Fin n ↦ gaussianReal 0 (variance i))).real
        (gaussianWalkSurvivalSet n x) ≤
      64 * (x + 2) / Real.sqrt (n : ℝ) := by
  let vs : List ℝ≥0 := List.ofFn variance
  have hne : vs ≠ [] := by
    intro hnil
    have : vs.length = 0 := by simp [hnil]
    simp only [vs, List.length_ofFn] at this
    omega
  have hlower' : ∀ v ∈ vs, (1 / 3 : ℝ≥0) ≤ v := by
    exact (List.forall_mem_ofFn_iff).2 hlower
  have hupper' : ∀ v ∈ vs, v ≤ (3 / 8 : ℝ≥0) := by
    exact (List.forall_mem_ofFn_iff).2 hupper
  have h := gaussianVarianceWalk_third_threeEighths_probability_le
    vs hne hx hlower' hupper'
  have hvlen : vs.length = n := by simp [vs]
  let e : Fin vs.length ≃ Fin n := finCongr hvlen
  let E : (Fin vs.length → ℝ) ≃ᵐ (Fin n → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e
  have hcoord (i : Fin vs.length) : vs.get i = variance (e i) := by
    dsimp only [vs, e]
    rw [List.get_ofFn]
    congr 1
  have hsource : gaussianVarianceWalkMeasure vs =
      Measure.pi (fun i : Fin vs.length ↦ gaussianReal 0 (variance (e i))) := by
    unfold gaussianVarianceWalkMeasure
    congr 1
    funext i
    rw [hcoord]
  have hmp := measurePreserving_piCongrLeft
    (μ := fun i : Fin n ↦ gaussianReal 0 (variance i)) e
  have hE (omega : Fin vs.length → ℝ) :
      E omega = fun j ↦ omega (e.symm j) := by
    funext j
    obtain ⟨i, rfl⟩ := e.surjective j
    change (MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e)
      omega (e i) = omega i
    exact MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin n ↦ ℝ) e omega i
  have hpre : E ⁻¹' gaussianWalkSurvivalSet n x =
      gaussianWalkSurvivalSet vs.length x := by
    ext omega
    simp only [mem_preimage, gaussianWalkSurvivalSet, mem_setOf_eq]
    rw [hE]
    exact gaussianWalkSurvives_reindex_finCongr hvlen x omega
  have htransport :
      (Measure.pi (fun i : Fin n ↦ gaussianReal 0 (variance i))).real
          (gaussianWalkSurvivalSet n x) =
        (gaussianVarianceWalkMeasure vs).real
          (gaussianWalkSurvivalSet vs.length x) := by
    rw [← hmp.map_eq]
    rw [map_measureReal_apply E.measurable
      (measurableSet_gaussianWalkSurvivalSet n hx)]
    rw [hpre, hsource]
  rw [htransport]
  simpa only [vs, List.length_ofFn] using! h

theorem gaussianVarianceWalk_third_threeEighths_logBarrier_probability_le_fin
    (n : ℕ) (hn : 0 < n) (variance : Fin n → ℝ≥0)
    {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c)
    (hlower : ∀ i, (1 / 3 : ℝ≥0) ≤ variance i)
    (hupper : ∀ i, variance i ≤ (3 / 8 : ℝ≥0)) :
    (Measure.pi (fun i : Fin n ↦ gaussianReal 0 (variance i))).real
        (gaussianWalkTimeBarrierSet n 0
          (fun i ↦ x + c * Real.log ((i.val + 2 : ℕ) : ℝ))) ≤
      64 * (x + c * Real.log ((n + 1 : ℕ) : ℝ) + 2) /
        Real.sqrt (n : ℝ) := by
  let vs : List ℝ≥0 := List.ofFn variance
  have hne : vs ≠ [] := by
    intro hnil
    have : vs.length = 0 := by simp [hnil]
    simp only [vs, List.length_ofFn] at this
    omega
  have hlower' : ∀ v ∈ vs, (1 / 3 : ℝ≥0) ≤ v := by
    exact (List.forall_mem_ofFn_iff).2 hlower
  have hupper' : ∀ v ∈ vs, v ≤ (3 / 8 : ℝ≥0) := by
    exact (List.forall_mem_ofFn_iff).2 hupper
  have h := gaussianVarianceWalk_third_threeEighths_logBarrier_probability_le
    vs hne hx hc hlower' hupper'
  have hvlen : vs.length = n := by simp [vs]
  let e : Fin vs.length ≃ Fin n := finCongr hvlen
  let E : (Fin vs.length → ℝ) ≃ᵐ (Fin n → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e
  have hcoord (i : Fin vs.length) : vs.get i = variance (e i) := by
    dsimp only [vs, e]
    rw [List.get_ofFn]
    congr 1
  have hsource : gaussianVarianceWalkMeasure vs =
      Measure.pi (fun i : Fin vs.length ↦ gaussianReal 0 (variance (e i))) := by
    unfold gaussianVarianceWalkMeasure
    congr 1
    funext i
    rw [hcoord]
  have hmp := measurePreserving_piCongrLeft
    (μ := fun i : Fin n ↦ gaussianReal 0 (variance i)) e
  have hE (omega : Fin vs.length → ℝ) :
      E omega = fun j ↦ omega (e.symm j) := by
    funext j
    obtain ⟨i, rfl⟩ := e.surjective j
    change (MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e)
      omega (e i) = omega i
    exact MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin n ↦ ℝ) e omega i
  let b : Fin vs.length → ℝ :=
    fun i ↦ x + c * Real.log ((i.val + 2 : ℕ) : ℝ)
  let bn : Fin n → ℝ :=
    fun i ↦ x + c * Real.log ((i.val + 2 : ℕ) : ℝ)
  have hb (i : Fin vs.length) : bn (e i) = b i := by
    dsimp only [bn, b, e]
    congr 4
  have hpre : E ⁻¹' gaussianWalkTimeBarrierSet n 0 bn =
      gaussianWalkTimeBarrierSet vs.length 0 b := by
    ext omega
    simp only [mem_preimage, gaussianWalkTimeBarrierSet, mem_setOf_eq]
    rw [hE]
    have hre := gaussianWalkTimeBarrierSurvives_reindex_finCongr hvlen 0 b omega
    have hbn : bn =
        (fun j ↦ b (e.symm j)) := by
      funext j
      obtain ⟨i, rfl⟩ := e.surjective j
      simp [hb]
    rw [hbn]
    exact hre
  have hsetmeas : MeasurableSet (gaussianWalkTimeBarrierSet n 0 bn) :=
    measurableSet_gaussianWalkTimeBarrierSet n 0 bn
  have htransport :
      (Measure.pi (fun i : Fin n ↦ gaussianReal 0 (variance i))).real
          (gaussianWalkTimeBarrierSet n 0 bn) =
        (gaussianVarianceWalkMeasure vs).real
          (gaussianWalkTimeBarrierSet vs.length 0 b) := by
    rw [← hmp.map_eq]
    rw [map_measureReal_apply E.measurable hsetmeas]
    rw [hpre, hsource]
  dsimp only [bn] at htransport
  rw [htransport]
  simpa only [vs, b, List.length_ofFn] using! h


end
end Erdos.Problem520
