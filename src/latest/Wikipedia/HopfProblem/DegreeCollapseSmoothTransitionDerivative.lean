import Wikipedia.HopfProblem.DegreeCollapseLongitudinalBlend
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# The smooth bounded time parameter crosses every interior level once

Compute a positive derivative of the standard smooth transition on (0,1).
It is therefore strictly increasing on the whole closed unit interval.
Every prescribed interior value occurs at one interior time with nonzero
time derivative, as required for a transverse sheet crossing.
-/

noncomputable section

open Set Function Metric
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem expNegInvGlue_hasDerivAt (t : ℝ) :
    HasDerivAt expNegInvGlue (t⁻¹ ^ 2 * expNegInvGlue t) t := by
  simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) t

theorem smoothTransition_deriv_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < deriv Real.smoothTransition t := by
  let a := expNegInvGlue t
  let b := expNegInvGlue (1 - t)
  let a' := t⁻¹ ^ 2 * a
  let b' := (1 - t)⁻¹ ^ 2 * b
  have ha : 0 < a := expNegInvGlue.pos_of_pos ht.1
  have hb : 0 < b := expNegInvGlue.pos_of_pos (sub_pos.mpr ht.2)
  have ha' : 0 < a' := mul_pos (sq_pos_of_ne_zero (inv_ne_zero ht.1.ne')) ha
  have hb' : 0 < b' :=
    mul_pos (sq_pos_of_ne_zero (inv_ne_zero (sub_pos.mpr ht.2).ne')) hb
  have hA : HasDerivAt expNegInvGlue a' t := expNegInvGlue_hasDerivAt t
  have hB : HasDerivAt (fun s : ℝ => expNegInvGlue (1 - s)) (-b') t := by
    convert! (expNegInvGlue_hasDerivAt (1 - t)).comp t
      ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)) using 1
    dsimp only [b', b]
    ring
  have hd := hA.div (hA.add hB) (Real.smoothTransition.pos_denom t).ne'
  change HasDerivAt Real.smoothTransition
    ((a' * (a + b) - a * (a' + -b')) / (a + b) ^ 2) t at hd
  rw [hd.deriv]
  apply div_pos
  · have he : a' * (a + b) - a * (a' + -b') = a' * b + a * b' := by ring
    rw [he]
    exact add_pos (mul_pos ha' hb) (mul_pos ha hb')
  · exact sq_pos_of_pos (add_pos ha hb)

theorem smoothTransition_strictMonoOn :
    StrictMonoOn Real.smoothTransition (Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (0 : ℝ) 1)
    Real.smoothTransition.continuous.continuousOn
  intro t ht
  apply smoothTransition_deriv_pos
  simpa only [interior_Icc] using ht

theorem exists_unique_smoothTransition_time {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) :
    ∃ τ : ℝ, τ ∈ Ioo (0 : ℝ) 1 ∧ Real.smoothTransition τ = c ∧
      0 < deriv Real.smoothTransition τ ∧
      ∀ t ∈ Icc (0 : ℝ) 1, Real.smoothTransition t = c ↔ t = τ := by
  have hc' : c ∈ Icc (Real.smoothTransition 0) (Real.smoothTransition 1) := by
    rw [Real.smoothTransition.zero, Real.smoothTransition.one]
    exact ⟨hc.1.le, hc.2.le⟩
  obtain ⟨τ, hτ, heq⟩ := intermediate_value_Icc zero_le_one
    Real.smoothTransition.continuous.continuousOn hc'
  have hτ0 : τ ≠ 0 := by
    intro h
    rw [h, Real.smoothTransition.zero] at heq
    linarith [hc.1]
  have hτ1 : τ ≠ 1 := by
    intro h
    rw [h, Real.smoothTransition.one] at heq
    linarith [hc.2]
  have hτI : τ ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hτ.1 (Ne.symm hτ0), lt_of_le_of_ne hτ.2 hτ1⟩
  refine ⟨τ, hτI, heq, smoothTransition_deriv_pos hτI, ?_⟩
  intro t ht
  exact ⟨fun h => smoothTransition_strictMonoOn.injOn ht hτ (h.trans heq.symm),
    fun h => h ▸ heq⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
