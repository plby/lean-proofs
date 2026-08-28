import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransportGauge
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationConnection
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Exponential transport for the constructed native connection

The scalar coefficient along a smooth curve is the actual constructed
connection one-form evaluated on the curve's actual derivative. The local
transport is its negative exponential integral. The chart-change hypotheses
of the generic FTC lemma are derived here from the proved native connection
law and the real chain rule.
-/

noncomputable section

open Set Topology MeasureTheory
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport

open HolomorphicCharacterBundle PeriodTorusLineBundleClassificationConnection

local notation "Iℂ" => modelWithCornersSelf ℂ ComplexPlane₂

variable {ι : Type*} (A : TransitionData ComplexPlane₂ ι)

/-- Evaluate the actual real connection one-form on the derivative of a curve. -/
def curveCoefficient (i : ι) (γ : ℝ → ComplexPlane₂) (t : ℝ) : ℂ :=
  connectionForm A i (γ t) (deriv γ t)

/-- Actual rank-one transport in one chart of the constructed connection. -/
def connectionTransport (i : ι) (γ : ℝ → ComplexPlane₂) (a b : ℝ) : ℂ :=
  scalarTransport (curveCoefficient A i γ) a b

theorem connectionTransport_ne_zero (i : ι) (γ : ℝ → ComplexPlane₂) (a b : ℝ) :
    connectionTransport A i γ a b ≠ 0 := scalarTransport_ne_zero _ _ _

@[simp] theorem connectionTransport_self (i : ι) (γ : ℝ → ComplexPlane₂) (a : ℝ) :
    connectionTransport A i γ a a = 1 := scalarTransport_self _ _

theorem connectionTransport_reverse (i : ι) (γ : ℝ → ComplexPlane₂) (a b : ℝ) :
    connectionTransport A i γ b a = (connectionTransport A i γ a b)⁻¹ :=
  scalarTransport_reverse _ _ _

variable [A.IsHolomorphic Iℂ]

theorem curveCoefficient_contDiffOn (i : ι) (γ : ℝ → ComplexPlane₂)
    (hγ : ContDiff ℝ ∞ γ) :
    ContDiffOn ℝ ∞ (curveCoefficient A i γ) (γ ⁻¹' A.baseSet i) := by
  have hdγ : ContDiff ℝ ∞ (deriv γ) := (contDiff_infty_iff_deriv.mp hγ).2
  exact ((connectionForm_contDiffOn A i).comp hγ.contDiffOn (fun _ hx => hx)).clm_apply
    hdγ.contDiffOn

theorem curveCoefficient_intervalIntegrable (i : ι) (γ : ℝ → ComplexPlane₂)
    (hγ : ContDiff ℝ ∞ γ) {a b : ℝ} (hchart : MapsTo γ (uIcc a b) (A.baseSet i)) :
    IntervalIntegrable (curveCoefficient A i γ) volume a b :=
  ((curveCoefficient_contDiffOn A i γ hγ).continuousOn.mono hchart).intervalIntegrable

/-- The actual connection transport composes over adjacent chart segments. -/
theorem connectionTransport_comp (i : ι) (γ : ℝ → ComplexPlane₂)
    (hγ : ContDiff ℝ ∞ γ) (a b c : ℝ)
    (hab : MapsTo γ (uIcc a b) (A.baseSet i))
    (hbc : MapsTo γ (uIcc b c) (A.baseSet i)) :
    connectionTransport A i γ a c =
      connectionTransport A i γ b c * connectionTransport A i γ a b :=
  scalarTransport_comp _ _ _ _ (curveCoefficient_intervalIntegrable A i γ hγ hab)
    (curveCoefficient_intervalIntegrable A i γ hγ hbc)

/-- The derivative relation needed for chart covariance follows from the
proved connection law and the real chain rule, not from an assumed logarithm. -/
theorem transition_curve_hasDerivAt (i j : ι) (γ : ℝ → ComplexPlane₂)
    (hγ : ContDiff ℝ ∞ γ) (t : ℝ) (ht : γ t ∈ A.baseSet i ∩ A.baseSet j) :
    HasDerivAt (fun u => (A.transition i j (γ u) : ℂ))
      ((curveCoefficient A i γ t - curveCoefficient A j γ t) *
        (A.transition i j (γ t) : ℂ)) t := by
  have hdγ : HasDerivAt γ (deriv γ t) t := (hγ.differentiable (by simp) t).hasDerivAt
  have hd := (transition_differentiableAt A i j (γ t) ht).hasFDerivAt.comp_hasDerivAt t hdγ
  have hc : (curveCoefficient A i γ t - curveCoefficient A j γ t) *
      (A.transition i j (γ t) : ℂ) =
        fderiv ℝ (fun y => (A.transition i j y : ℂ)) (γ t) (deriv γ t) := by
    dsimp only [curveCoefficient]
    rw [connectionForm_change_apply A i j ht.1 ht.2, sub_sub_cancel]
    field_simp [A.transition_ne_zero i j (γ t)]
  rw [hc]
  exact hd

/-- Exact chart covariance for actual scalar transport of the constructed
connection: the transition acts at the final and initial curve points. -/
theorem connectionTransport_chart_change (i j : ι) (γ : ℝ → ComplexPlane₂)
    (hγ : ContDiff ℝ ∞ γ) {a b : ℝ}
    (hchart : MapsTo γ (uIcc a b) (A.baseSet i ∩ A.baseSet j)) :
    connectionTransport A j γ a b =
      (A.transition i j (γ b) : ℂ) * connectionTransport A i γ a b *
        (A.transition i j (γ a) : ℂ)⁻¹ := by
  let S := γ ⁻¹' (A.baseSet i ∩ A.baseSet j)
  have hS : IsOpen S :=
    ((A.isOpen_baseSet i).inter (A.isOpen_baseSet j)).preimage hγ.continuous
  have hi : ContinuousOn (curveCoefficient A i γ) S :=
    (curveCoefficient_contDiffOn A i γ hγ).continuousOn.mono (fun _ hx => hx.1)
  have hj : ContinuousOn (curveCoefficient A j γ) S :=
    (curveCoefficient_contDiffOn A j γ hγ).continuousOn.mono (fun _ hx => hx.2)
  exact scalarTransport_gauge hS hi hj
    (fun t ht => transition_curve_hasDerivAt A i j γ hγ t ht) hchart
    (A.transition_ne_zero i j (γ a))

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport
