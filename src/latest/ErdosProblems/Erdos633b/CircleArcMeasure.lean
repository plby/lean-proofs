import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic.Linarith

/-! Haar measure of the short angular arcs used in actual local direction sectors. -/

namespace Erdos633b.CircleArcMeasure

open MeasureTheory Set

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

noncomputable instance angleMeasureSpace : MeasureSpace Real.Angle :=
  AddCircle.measureSpace (2 * Real.pi)

instance angleBorelSpace : BorelSpace Real.Angle :=
  inferInstanceAs (BorelSpace (AddCircle (2 * Real.pi)))

noncomputable def measure : Measure Real.Angle :=
  (volume : Measure (AddCircle (2 * Real.pi)))

instance measure_nullSingleton : NullSingletonClass measure where
  measure_singleton x := by
    have h : measure (Metric.closedBall x 0) =
        ENNReal.ofReal (min (2 * Real.pi) (2 * 0)) :=
      AddCircle.volume_closedBall (2 * Real.pi) (x := x) 0
    simpa only [Metric.closedBall_zero, mul_zero, min_eq_right Real.two_pi_pos.le,
      ENNReal.ofReal_zero] using h

instance measure_addInvariant : Measure.IsAddLeftInvariant measure :=
  inferInstanceAs (Measure.IsAddLeftInvariant (volume : Measure (AddCircle (2 * Real.pi))))

instance measure_negInvariant : Measure.IsNegInvariant measure :=
  inferInstanceAs (Measure.IsNegInvariant (volume : Measure (AddCircle (2 * Real.pi))))

noncomputable def arc (t : ℝ) : Set Real.Angle :=
  ((↑) : ℝ → Real.Angle) '' Icc 0 t

theorem arc_isCompact (t : ℝ) : IsCompact (arc t) :=
  isCompact_Icc.image Real.Angle.continuous_coe

theorem arc_measurable (t : ℝ) : MeasurableSet (arc t) :=
  (arc_isCompact t).isClosed.measurableSet

theorem arc_preimage (t : ℝ) (htpi : t ≤ Real.pi) :
    ((↑) : ℝ → Real.Angle) ⁻¹' arc t ∩ Ioc (-Real.pi) Real.pi = Icc 0 t := by
  ext x
  constructor
  · rintro ⟨⟨y, hy, he⟩, hx⟩
    have hy' : -Real.pi < y ∧ y ≤ Real.pi :=
      ⟨by linarith [hy.1, Real.pi_pos], hy.2.trans htpi⟩
    have he' := congrArg Real.Angle.toReal he
    rw [Real.Angle.toReal_coe_eq_self_iff.mpr hy',
      Real.Angle.toReal_coe_eq_self_iff.mpr hx] at he'
    exact he' ▸ hy
  · intro hx
    exact ⟨⟨x, hx, rfl⟩, by linarith [hx.1, Real.pi_pos], hx.2.trans htpi⟩

theorem measure_arc (t : ℝ) (_ht : 0 ≤ t) (htpi : t ≤ Real.pi) :
    measure (arc t) = ENNReal.ofReal t := by
  have hm := AddCircle.add_projection_respects_measure (2 * Real.pi) (-Real.pi)
    (arc_measurable t)
  change measure (arc t) = _ at hm
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at hm
  rw [hm]
  change volume (((↑) : ℝ → Real.Angle) ⁻¹' arc t ∩ Ioc (-Real.pi) Real.pi) = _
  rw [arc_preimage t htpi, Real.volume_Icc, sub_zero]

theorem measure_univ : measure univ = ENNReal.ofReal (2 * Real.pi) :=
  AddCircle.measure_univ (2 * Real.pi)

noncomputable def openArc (t : ℝ) : Set Real.Angle :=
  ((↑) : ℝ → Real.Angle) '' Ioo 0 t

theorem openArc_subset_arc (t : ℝ) : openArc t ⊆ arc t :=
  Set.image_mono Ioo_subset_Icc_self

theorem arc_sdiff_openArc_subset (t : ℝ) :
    arc t \ openArc t ⊆ ({0, (t : Real.Angle)} : Set Real.Angle) := by
  rintro x ⟨⟨y, hy, rfl⟩, hn⟩
  by_cases h0 : y = 0
  · simp [h0]
  by_cases ht : y = t
  · simp [ht]
  exact False.elim (hn ⟨y, ⟨lt_of_le_of_ne hy.1 (Ne.symm h0), lt_of_le_of_ne hy.2 ht⟩, rfl⟩)

theorem openArc_ae_eq_arc (t : ℝ) : openArc t =ᵐ[measure] arc t := by
  apply ae_eq_set.mpr
  constructor
  · rw [sdiff_eq_empty.mpr (openArc_subset_arc t)]
    exact measure_empty
  · exact measure_mono_null (arc_sdiff_openArc_subset t)
      ((Set.toFinite ({0, (t : Real.Angle)} : Set Real.Angle)).measure_zero measure)

theorem measure_openArc (t : ℝ) (ht : 0 ≤ t) (htpi : t ≤ Real.pi) :
    measure (openArc t) = ENNReal.ofReal t := by
  rw [measure_congr (openArc_ae_eq_arc t), measure_arc t ht htpi]

theorem measure_translate (c : Real.Angle) (s : Set Real.Angle) :
    measure ((fun x => c + x) '' s) = measure s := by
  have he : (fun x => c + x) '' s = (fun x => -c + x) ⁻¹' s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨-c + x, hx, by simp [← add_assoc]⟩
  rw [he]
  exact measure_preimage_add measure (-c) s

theorem measure_reverse (s : Set Real.Angle) :
    measure ((fun x => -x) '' s) = measure s := by
  have he : (fun x : Real.Angle => -x) '' s = (fun x => -x) ⁻¹' s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨-x, hx, neg_neg x⟩
  rw [he]
  exact Measure.measure_preimage_neg measure s

end Erdos633b.CircleArcMeasure
