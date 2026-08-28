import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransportBasic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Change of scalar transport coordinates by the fundamental theorem of calculus

The transition identity is proved by differentiating an explicit product of a
scalar transition and an exponential integral. No logarithm of the transition
and no differential-equation existence or uniqueness theorem is assumed.
-/

noncomputable section

open Set Topology MeasureTheory

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport

/-- Local continuity on an open set containing the segment supplies all the
ordinary FTC hypotheses for the primitive with a varying right endpoint. -/
theorem integral_hasDerivAt_on_segment {β : ℝ → ℂ} {S : Set ℝ} (hS : IsOpen S)
    (hβ : ContinuousOn β S) {a b t : ℝ} (hab : uIcc a b ⊆ S) (ht : t ∈ uIcc a b) :
    HasDerivAt (fun u => ∫ r in a..u, β r) (β t) t := by
  have hs : t ∈ S := hab ht
  exact intervalIntegral.integral_hasDerivAt_right
    ((hβ.mono ((uIcc_subset_uIcc_left ht).trans hab)).intervalIntegrable)
    (ContinuousOn.stronglyMeasurableAtFilter hS hβ t hs)
    (hβ.continuousAt (hS.mem_nhds hs))

/-- The actual exponential transports satisfy the rank-one chart-change law.
The differential identity for `g` will be derived from the already proved
connection law when this lemma is applied to native bundle coordinates. -/
theorem scalarTransport_gauge {βi βj g : ℝ → ℂ} {S : Set ℝ}
    (hS : IsOpen S) (hβi : ContinuousOn βi S) (hβj : ContinuousOn βj S)
    (hg : ∀ t ∈ S, HasDerivAt g ((βi t - βj t) * g t) t)
    {a b : ℝ} (hab : uIcc a b ⊆ S) (hga : g a ≠ 0) :
    scalarTransport βj a b = g b * scalarTransport βi a b * (g a)⁻¹ := by
  let F : ℝ → ℂ := fun t =>
    g t * Complex.exp ((∫ r in a..t, βj r) - (∫ r in a..t, βi r))
  have hF : ∀ t ∈ uIcc a b, HasDerivAt F 0 t := by
    intro t ht
    have hi := integral_hasDerivAt_on_segment hS hβi hab ht
    have hj := integral_hasDerivAt_on_segment hS hβj hab ht
    dsimp only [F]
    convert (hg t (hab ht)).mul (hj.sub hi).cexp using 1 <;> first | rfl | ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume a b)
  have hFa : F b = F a := sub_eq_zero.mp (by simpa using hFTC.symm)
  have hratio : g b *
      Complex.exp ((∫ r in a..b, βj r) - (∫ r in a..b, βi r)) = g a := by
    simpa [F] using hFa
  unfold scalarTransport
  apply (eq_mul_inv_iff_mul_eq₀ hga).mpr
  rw [← hratio, sub_eq_add_neg, Complex.exp_add]
  rw [Complex.exp_neg]
  field_simp

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport
