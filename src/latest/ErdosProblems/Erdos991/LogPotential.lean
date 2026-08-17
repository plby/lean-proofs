import ErdosProblems.Erdos988

open Filter MeasureTheory Metric Set
open scoped BigOperators ENNReal NNReal Pointwise Topology

namespace Check991LogPotential

noncomputable section

open Erdos988

/-! The one-dimensional analytic part of the logarithmic-potential computation. -/

/-- Chord length written in terms of the normalized dot-product parameter. -/
def logChordParam (q : ℝ) : ℝ :=
  Real.log (2 * Real.sqrt (1 - q))

lemma intervalIntegrable_log_one_sub :
    IntervalIntegrable (fun q : ℝ ↦ Real.log (1 - q)) volume 0 1 := by
  simpa using
    ((intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := 1)).comp_sub_left 1).symm

lemma integrableOn_Icc_log_one_sub :
    IntegrableOn (fun q : ℝ ↦ Real.log (1 - q)) (Icc 0 1) volume :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    intervalIntegrable_log_one_sub

lemma integral_log_one_sub :
    (∫ q : ℝ in 0..1, Real.log (1 - q)) = -1 := by
  rw [intervalIntegral.integral_comp_sub_left (fun q : ℝ ↦ Real.log q) 1]
  norm_num

lemma logChordParam_ae_eq :
    logChordParam =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      fun q ↦ Real.log 2 + (1 / 2 : ℝ) * Real.log (1 - q) := by
  have hne : ∀ᵐ q ∂volume.restrict (Icc (0 : ℝ) 1), q ≠ 1 := by
    exact ae_restrict_of_ae (by simp [ae_iff])
  filter_upwards [ae_restrict_mem measurableSet_Icc, hne] with q hq hq1
  have hsub : 1 - q ≠ 0 := sub_ne_zero.mpr hq1.symm
  have hsqrt : Real.sqrt (1 - q) ≠ 0 := by
    rw [Real.sqrt_ne_zero']
    exact sub_pos.mpr (lt_of_le_of_ne hq.2 hq1)
  rw [logChordParam, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hsqrt,
    Real.log_sqrt (sub_nonneg.mpr hq.2)]
  ring

lemma logChordParam_integrable :
    Integrable logChordParam (volume.restrict (Icc (0 : ℝ) 1)) := by
  apply Integrable.congr _ logChordParam_ae_eq.symm
  exact (integrable_const (Real.log 2)).add
    (integrableOn_Icc_log_one_sub.const_mul (1 / 2 : ℝ))

lemma integral_logChordParam :
    (∫ q : ℝ, logChordParam q ∂volume.restrict (Icc (0 : ℝ) 1)) =
      Real.log 2 - 1 / 2 := by
  have hlogint :
      (∫ q : ℝ, Real.log (1 - q) ∂volume.restrict (Icc (0 : ℝ) 1)) = -1 := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_log_one_sub]
  calc
    _ = ∫ q : ℝ, (Real.log 2 + (1 / 2 : ℝ) * Real.log (1 - q))
        ∂volume.restrict (Icc (0 : ℝ) 1) := integral_congr_ae logChordParam_ae_eq
    _ = (∫ _q : ℝ, Real.log 2 ∂volume.restrict (Icc (0 : ℝ) 1)) +
        ∫ q : ℝ, (1 / 2 : ℝ) * Real.log (1 - q)
          ∂volume.restrict (Icc (0 : ℝ) 1) := by
      rw [integral_add (integrable_const _)
        (integrableOn_Icc_log_one_sub.const_mul (1 / 2 : ℝ))]
    _ = Real.log 2 + (1 / 2 : ℝ) * (-1) := by
      rw [integral_const_mul, hlogint]
      simp
    _ = Real.log 2 - 1 / 2 := by ring

/-! A reusable pushforward-to-potential bridge.  Its hypothesis is precisely the
geometric statement that `q` is uniform on `[0,1]`. -/

lemma integrable_logChordParam_comp_of_map_eq
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (q : X → ℝ)
    (hq : Measurable q)
    (hmap : Measure.map q mu = volume.restrict (Icc (0 : ℝ) 1)) :
    Integrable (fun x ↦ logChordParam (q x)) mu := by
  rw [← Function.comp_def]
  apply Integrable.comp_measurable _ hq
  simpa [hmap] using logChordParam_integrable

lemma integral_logChordParam_comp_of_map_eq
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (q : X → ℝ)
    (hq : Measurable q)
    (hmap : Measure.map q mu = volume.restrict (Icc (0 : ℝ) 1)) :
    (∫ x, logChordParam (q x) ∂mu) = Real.log 2 - 1 / 2 := by
  rw [← MeasureTheory.integral_map hq.aemeasurable]
  · simpa [hmap] using integral_logChordParam
  · rw [hmap]
    exact logChordParam_integrable.aestronglyMeasurable

lemma measurable_normalizedDot_right (y : S2) :
    Measurable (fun x : S2 ↦ normalizedDot x y) := by
  unfold normalizedDot
  measurability

/-- Exact cap masses imply that the normalized scalar projection is Lebesgue-uniform
on `[0,1]`.  This packages the measure-theoretic conversion needed by the potential
calculation; the only geometric hypothesis is the literal cap-area formula. -/
lemma normalizedDot_map_eq_uniform_of_cap_area (y : S2)
    (hcap : ∀ t ∈ Icc (-1 : ℝ) 1,
      (surfaceProbability : Measure S2) (sphericalCap y t) =
        ENNReal.ofReal (capArea t)) :
    Measure.map (fun x : S2 ↦ normalizedDot x y)
        (surfaceProbability : Measure S2) =
      volume.restrict (Icc (0 : ℝ) 1) := by
  apply Measure.ext_of_Ici
  intro a
  rw [Measure.map_apply (measurable_normalizedDot_right y) measurableSet_Ici,
    Measure.restrict_apply measurableSet_Ici]
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · have hpre : (fun x : S2 ↦ normalizedDot x y) ⁻¹' Ici a = univ := by
      ext x
      simp only [mem_preimage, mem_Ici, mem_univ, iff_true]
      exact ha.le.trans (normalizedDot_nonneg x y)
    have hinter : Ici a ∩ Icc (0 : ℝ) 1 = Icc 0 1 := by
      ext q
      simp only [mem_inter_iff, mem_Ici, mem_Icc]
      constructor
      · exact fun h ↦ h.2
      · exact fun h ↦ ⟨ha.le.trans h.1, h⟩
    rw [hpre, hinter]
    simp
  · have hpre : (fun x : S2 ↦ normalizedDot x y) ⁻¹' Ici 0 = univ := by
      ext x
      simp [normalizedDot_nonneg]
    have hinter : Ici (0 : ℝ) ∩ Icc 0 1 = Icc 0 1 := by
      ext q
      simp only [mem_inter_iff, mem_Ici, mem_Icc]
      tauto
    rw [hpre, hinter]
    simp
  · rcases le_or_gt a 1 with ha1 | ha1
    · have hpre : (fun x : S2 ↦ normalizedDot x y) ⁻¹' Ici a =
          sphericalCap y (2 * a - 1) := by
        ext x
        simp only [mem_preimage, mem_Ici, sphericalCap, mem_ofPred_eq, normalizedDot]
        constructor <;> intro h <;> linarith
      have hinter : Ici a ∩ Icc (0 : ℝ) 1 = Icc a 1 := by
        ext q
        simp only [mem_inter_iff, mem_Ici, mem_Icc]
        constructor
        · exact fun h ↦ ⟨h.1, h.2.2⟩
        · exact fun h ↦ ⟨h.1, ha.le.trans h.1, h.2⟩
      rw [hpre, hcap (2 * a - 1) (by constructor <;> linarith), hinter,
        Real.volume_Icc]
      congr 1
      unfold capArea
      ring
    · have hpre : (fun x : S2 ↦ normalizedDot x y) ⁻¹' Ici a = ∅ := by
        ext x
        simp only [mem_preimage, mem_Ici, mem_empty_iff_false, iff_false]
        exact not_le.mpr ((normalizedDot_le_one x y).trans_lt ha1)
      have hinter : Ici a ∩ Icc (0 : ℝ) 1 = ∅ := by
        ext q
        simp only [mem_inter_iff, mem_Ici, mem_Icc, mem_empty_iff_false, iff_false]
        exact fun h ↦ (not_le.mpr ha1) (h.1.trans h.2.2)
      rw [hpre, hinter]
      simp

/-- By orthogonal invariance, it is enough to establish the projection law in
the north-pole direction. -/
lemma normalizedDot_map_eq_uniform_of_northPole
    (hnorth : Measure.map (fun x : S2 ↦ normalizedDot x northPole)
        (surfaceProbability : Measure S2) = volume.restrict (Icc (0 : ℝ) 1))
    (y : S2) :
    Measure.map (fun x : S2 ↦ normalizedDot x y)
        (surfaceProbability : Measure S2) = volume.restrict (Icc (0 : ℝ) 1) := by
  let e : E3 ≃ₗᵢ[ℝ] E3 := ((ℝ ∙ ((northPole : E3) - (y : E3)))ᗮ).reflection
  have hey : e (northPole : E3) = (y : E3) := by
    exact Submodule.reflection_sub (by simp [northPole, sphere2_norm y])
  have hpoint (x : S2) :
      normalizedDot (sphereMeasurableEquiv e x) y = normalizedDot x northPole := by
    unfold normalizedDot
    rw [sphereMeasurableEquiv_coe, ← hey, LinearIsometryEquiv.inner_map_map]
  rw [← (surfaceProbability_measurePreserving e).map_eq,
    Measure.map_map (measurable_normalizedDot_right y)
      (sphereMeasurableEquiv e).measurable]
  rw [show (fun x : S2 ↦ normalizedDot x y) ∘ sphereMeasurableEquiv e =
      fun x : S2 ↦ normalizedDot x northPole by
    funext x
    exact hpoint x]
  exact hnorth

/-- The requested logarithmic-potential integrability, reduced to the exact
uniformity of the normalized projection. -/
lemma integrable_log_dist_of_normalizedDot_map_eq (y : S2)
    (hmap : Measure.map (fun x : S2 ↦ normalizedDot x y)
        (surfaceProbability : Measure S2) = volume.restrict (Icc (0 : ℝ) 1)) :
    Integrable (fun x : S2 ↦ Real.log (dist x y))
      (surfaceProbability : Measure S2) := by
  apply Integrable.congr
    (integrable_logChordParam_comp_of_map_eq
      (surfaceProbability : Measure S2) (fun x : S2 ↦ normalizedDot x y)
      (measurable_normalizedDot_right y) hmap)
  filter_upwards [] with x
  rw [dist_eq_two_mul_sqrt_one_sub_normalizedDot]
  rfl

/-- The exact logarithmic potential, assuming the normalized projection law. -/
lemma integral_log_dist_of_normalizedDot_map_eq (y : S2)
    (hmap : Measure.map (fun x : S2 ↦ normalizedDot x y)
        (surfaceProbability : Measure S2) = volume.restrict (Icc (0 : ℝ) 1)) :
    (∫ x : S2, Real.log (dist x y) ∂(surfaceProbability : Measure S2)) =
      Real.log 2 - 1 / 2 := by
  calc
    _ = ∫ x : S2, logChordParam (normalizedDot x y)
        ∂(surfaceProbability : Measure S2) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [dist_eq_two_mul_sqrt_one_sub_normalizedDot]
      rfl
    _ = Real.log 2 - 1 / 2 :=
      integral_logChordParam_comp_of_map_eq
        (surfaceProbability : Measure S2) (fun x : S2 ↦ normalizedDot x y)
        (measurable_normalizedDot_right y) hmap

lemma integrable_log_dist_of_cap_area (y : S2)
    (hcap : ∀ t ∈ Icc (-1 : ℝ) 1,
      (surfaceProbability : Measure S2) (sphericalCap y t) =
        ENNReal.ofReal (capArea t)) :
    Integrable (fun x : S2 ↦ Real.log (dist x y))
      (surfaceProbability : Measure S2) :=
  integrable_log_dist_of_normalizedDot_map_eq y
    (normalizedDot_map_eq_uniform_of_cap_area y hcap)

lemma integral_log_dist_of_cap_area (y : S2)
    (hcap : ∀ t ∈ Icc (-1 : ℝ) 1,
      (surfaceProbability : Measure S2) (sphericalCap y t) =
        ENNReal.ofReal (capArea t)) :
    (∫ x : S2, Real.log (dist x y) ∂(surfaceProbability : Measure S2)) =
      Real.log 2 - 1 / 2 :=
  integral_log_dist_of_normalizedDot_map_eq y
    (normalizedDot_map_eq_uniform_of_cap_area y hcap)

/-- The north-pole cap computation alone suffices for every logarithmic
potential, by orthogonal invariance. -/
lemma integrable_log_dist_of_northPole_cap_area
    (hnorth : ∀ t ∈ Icc (-1 : ℝ) 1,
      (surfaceProbability : Measure S2) (sphericalCap northPole t) =
        ENNReal.ofReal (capArea t))
    (y : S2) :
    Integrable (fun x : S2 ↦ Real.log (dist x y))
      (surfaceProbability : Measure S2) := by
  apply integrable_log_dist_of_normalizedDot_map_eq y
  apply normalizedDot_map_eq_uniform_of_northPole
  exact normalizedDot_map_eq_uniform_of_cap_area northPole hnorth

lemma integral_log_dist_of_northPole_cap_area
    (hnorth : ∀ t ∈ Icc (-1 : ℝ) 1,
      (surfaceProbability : Measure S2) (sphericalCap northPole t) =
        ENNReal.ofReal (capArea t))
    (y : S2) :
    (∫ x : S2, Real.log (dist x y) ∂(surfaceProbability : Measure S2)) =
      Real.log 2 - 1 / 2 := by
  apply integral_log_dist_of_normalizedDot_map_eq y
  apply normalizedDot_map_eq_uniform_of_northPole
  exact normalizedDot_map_eq_uniform_of_cap_area northPole hnorth

end

end Check991LogPotential
