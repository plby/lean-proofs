import ErdosProblems.Erdos633.IntervalChain
import ErdosProblems.Erdos633.BoundaryDensity

/-!
# Coordinates and directed densities on a supporting line

The line parameter is real division by a nonzero complex direction. The odd
axis direction function vanishes on every other direction and reads the
orientation of a unit vector parallel to the axis.
-/

namespace Erdos633

noncomputable def axisMap (p d : ℂ) : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap p (p + d)

theorem axisMap_apply (p d : ℂ) (t : ℝ) : axisMap p d t = p + (t : ℂ) * d := by
  simp only [axisMap, AffineMap.lineMap_apply_module', add_sub_cancel_left,
    Complex.real_smul, add_comm]

theorem axisMap_injective (p d : ℂ) (hd : d ≠ 0) : Function.Injective (axisMap p d) := by
  apply AffineMap.lineMap_injective ℝ
  exact fun h => hd (add_left_cancel (show p + d = p + 0 by simpa using h.symm))

noncomputable def axisParameter (p d z : ℂ) : ℝ := ((z - p) / d).re

def OnAxis (p d z : ℂ) : Prop := ((z - p) / d).im = 0

theorem axisParameter_axisMap (p d : ℂ) (hd : d ≠ 0) (t : ℝ) :
    axisParameter p d (axisMap p d t) = t := by
  simp [axisParameter, axisMap_apply, hd]

theorem onAxis_axisMap (p d : ℂ) (hd : d ≠ 0) (t : ℝ) :
    OnAxis p d (axisMap p d t) := by
  simp [OnAxis, axisMap_apply, hd]

theorem axisMap_axisParameter (p d z : ℂ) (hd : d ≠ 0) (hz : OnAxis p d z) :
    axisMap p d (axisParameter p d z) = z := by
  have h : (axisParameter p d z : ℂ) = (z - p) / d := by
    apply Complex.ext
    · rfl
    · exact hz.symm
  rw [axisMap_apply, h, div_mul_cancel₀ _ hd]
  abel

theorem onAxis_iff_mem_range (p d z : ℂ) (hd : d ≠ 0) :
    OnAxis p d z ↔ z ∈ Set.range (axisMap p d) := by
  constructor
  · intro hz
    exact ⟨axisParameter p d z, axisMap_axisParameter p d z hd hz⟩
  · rintro ⟨t, rfl⟩
    exact onAxis_axisMap p d hd t

theorem axisMap_mem_segment (p d : ℂ) (hd : d ≠ 0) (a b t : ℝ) :
    axisMap p d t ∈ segment ℝ (axisMap p d a) (axisMap p d b) ↔ t ∈ Set.uIcc a b := by
  rw [← image_segment, segment_eq_uIcc]
  exact (axisMap_injective p d hd).mem_set_image

theorem intervalFlow_eq_indicator (a b t : ℝ) (hab : a ≠ b) (hta : t ≠ a) (htb : t ≠ b) :
    intervalFlow a b t = (Set.uIcc a b).indicator (fun _ => if a < b then 1 else -1) t := by
  classical
  rcases lt_or_gt_of_ne hab with hab | hba
  · rw [Set.uIcc_of_le hab.le]
    by_cases ht : t ∈ Set.Icc a b
    · have hat : a < t := lt_of_le_of_ne ht.1 hta.symm
      have htb' : t < b := lt_of_le_of_ne ht.2 htb
      simp [intervalFlow, leftStep, Set.indicator_of_mem ht, hab, hat,
        not_lt_of_ge htb'.le]
    · rw [Set.indicator_of_notMem ht]
      have hout : t < a ∨ b < t := by simpa only [Set.mem_Icc, not_and_or, not_le] using ht
      rcases hout with hta' | hbt
      · simp [intervalFlow, leftStep, not_lt_of_ge hta'.le,
          not_lt_of_ge (hta'.trans hab).le]
      · simp [intervalFlow, leftStep, hbt, hab.trans hbt]
  · rw [Set.uIcc_of_ge hba.le]
    by_cases ht : t ∈ Set.Icc b a
    · have hbt : b < t := lt_of_le_of_ne ht.1 htb.symm
      have hta' : t < a := lt_of_le_of_ne ht.2 hta
      simp [intervalFlow, leftStep, Set.indicator_of_mem ht, not_lt_of_ge hba.le,
        hbt, not_lt_of_ge hta'.le]
    · rw [Set.indicator_of_notMem ht]
      have hout : t < b ∨ a < t := by simpa only [Set.mem_Icc, not_and_or, not_le] using ht
      rcases hout with htb' | hat
      · simp [intervalFlow, leftStep, not_lt_of_ge htb'.le,
          not_lt_of_ge (htb'.trans hba).le]
      · simp [intervalFlow, leftStep, hat, hba.trans hat]

noncomputable def axisDirection (d w : ℂ) : ℝ :=
  if (w / d).im = 0 then ‖d‖ * (w / d).re else 0

theorem axisDirection_odd (d w : ℂ) : axisDirection d (-w) = -axisDirection d w := by
  by_cases h : (w / d).im = 0 <;>
    simp [axisDirection, neg_div, mul_neg, neg_eq_zero, h]

theorem Triangle.unitEdgeVector_div (P : Triangle) (k : Fin 3) (d : ℂ) :
    P.unitEdgeVector k / d =
      ((P.sideLength k)⁻¹ * P.orientationSign) • (P.edgeVector k / d) := by
  simp only [Triangle.unitEdgeVector, Triangle.orientedEdgeVector,
    Complex.real_smul, Complex.ofReal_mul]
  ring

theorem Triangle.axisDirection_unitEdge (P : Triangle) (k : Fin 3) (p d : ℂ)
    (hd : d ≠ 0) (a b : ℝ)
    (ha : P.edgeStart k = axisMap p d a) (hb : P.edgeEnd k = axisMap p d b) :
    axisDirection d (P.unitEdgeVector k) =
      P.orientationSign * (if a < b then 1 else -1) := by
  have hab : a ≠ b := fun h => P.edgeStart_ne_edgeEnd k (by rw [ha, hb, h])
  have hvec : P.edgeVector k = (b - a) • d := by
    simp only [Triangle.edgeVector, ha, hb, axisMap_apply, Complex.real_smul,
      Complex.ofReal_sub]
    ring
  have hlen : P.sideLength k = |b - a| * ‖d‖ := by
    rw [← P.norm_edgeVector k, hvec, norm_smul, Real.norm_eq_abs]
  have hdiv : P.edgeVector k / d = ((b - a : ℝ) : ℂ) := by
    rw [hvec, Complex.real_smul, mul_div_cancel_right₀ _ hd]
  have him : (P.unitEdgeVector k / d).im = 0 := by
    rw [P.unitEdgeVector_div, hdiv]
    simp
  rw [axisDirection, if_pos him, P.unitEdgeVector_div, hdiv]
  simp only [Complex.smul_re, Complex.ofReal_re, smul_eq_mul]
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
  rcases lt_or_gt_of_ne hab with hab | hba
  · rw [if_pos hab, hlen, abs_of_pos (sub_pos.mpr hab), mul_one]
    field_simp
  · rw [if_neg (not_lt_of_ge hba.le), hlen, abs_of_neg (sub_neg.mpr hba)]
    field_simp

theorem onAxis_endpoints_of_parallel_segment (p d a b z : ℂ)
    (hz : OnAxis p d z) (hseg : z ∈ segment ℝ a b)
    (hdir : ((b - a) / d).im = 0) : OnAxis p d a ∧ OnAxis p d b := by
  obtain ⟨t, _, ht⟩ := (segment_eq_image_lineMap ℝ a b) ▸ hseg
  have hzq : (z - p) / d = (a - p) / d + (t : ℂ) * ((b - a) / d) := by
    rw [← ht, AffineMap.lineMap_apply_module', Complex.real_smul]
    ring
  have hq : (b - p) / d = (a - p) / d + (b - a) / d := by ring
  change ((z - p) / d).im = 0 at hz
  have ha : ((a - p) / d).im = 0 := by
    have hh := congrArg Complex.im hzq
    simpa [hz, hdir] using hh.symm
  refine ⟨ha, ?_⟩
  change ((b - p) / d).im = 0
  rw [hq, Complex.add_im, ha, hdir, zero_add]

end Erdos633
