import Wikipedia.HopfProblem.HolomorphicCharacterBundleCore
import Wikipedia.HopfProblem.PeriodTori
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Logarithmic derivatives of actual holomorphic transition functions

These real one-forms are defined by differentiating the scalar transition
functions. Their smoothness and additive cocycle identity follow from
holomorphic regularity and the native multiplicative cocycle; no logarithms
or connection coefficients are assumed.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationConnection

open HolomorphicCharacterBundle

variable {ι : Type*} (A : TransitionData ComplexPlane₂ ι)

/-- The logarithmic derivative of a transition function, as an actual real
continuous linear one-form. -/
def logDerivative (i j : ι) (x : ComplexPlane₂) : ComplexPlane₂ →L[ℝ] ℂ :=
  ((A.transition i j x : ℂ)⁻¹) •
    fderiv ℝ (fun y => (A.transition i j y : ℂ)) x

variable [A.IsHolomorphic (modelWithCornersSelf ℂ ComplexPlane₂)]

/-- The holomorphic transitions are smooth as real functions on overlaps. -/
theorem transition_contDiffOn (i j : ι) :
    ContDiffOn ℝ ∞ (fun x => (A.transition i j x : ℂ))
      (A.baseSet i ∩ A.baseSet j) := by
  exact ((A.transition_holomorphic (modelWithCornersSelf ℂ ComplexPlane₂) i j).contDiffOn
    |>.restrict_scalars ℝ).of_le (by simp)

/-- On the open overlap, the ordinary real derivative exists. -/
theorem transition_differentiableAt (i j : ι) (x : ComplexPlane₂)
    (hx : x ∈ A.baseSet i ∩ A.baseSet j) :
    DifferentiableAt ℝ (fun y => (A.transition i j y : ℂ)) x :=
  ((transition_contDiffOn A i j).contDiffAt
    ((A.isOpen_baseSet i).inter (A.isOpen_baseSet j) |>.mem_nhds hx)).differentiableAt
      (by simp)

/-- The logarithmic derivative is smooth on each actual chart overlap. -/
theorem logDerivative_contDiffOn (i j : ι) :
    ContDiffOn ℝ ∞ (logDerivative A i j) (A.baseSet i ∩ A.baseSet j) := by
  have h := transition_contDiffOn A i j
  exact (h.inv (fun x _ => A.transition_ne_zero i j x)).smul
    (h.fderiv_of_isOpen ((A.isOpen_baseSet i).inter (A.isOpen_baseSet j)) (by simp))

/-- The same smoothness assertion in native real manifold notation. -/
theorem logDerivative_contMDiffOn (i j : ι) :
    ContMDiffOn (modelWithCornersSelf ℝ ComplexPlane₂)
      (modelWithCornersSelf ℝ (ComplexPlane₂ →L[ℝ] ℂ)) ∞
      (logDerivative A i j) (A.baseSet i ∩ A.baseSet j) :=
  (logDerivative_contDiffOn A i j).contMDiffOn

/-- Differentiating the actual transition cocycle on its open triple overlap. -/
theorem transition_fderiv_comp (i j k : ι) (x : ComplexPlane₂)
    (hx : x ∈ A.baseSet i ∩ A.baseSet j ∩ A.baseSet k) :
    fderiv ℝ (fun y => (A.transition i k y : ℂ)) x =
      (A.transition j k x : ℂ) • fderiv ℝ (fun y => (A.transition i j y : ℂ)) x +
      (A.transition i j x : ℂ) • fderiv ℝ (fun y => (A.transition j k y : ℂ)) x := by
  have heq : (fun y => (A.transition j k y : ℂ) * (A.transition i j y : ℂ))
      =ᶠ[𝓝 x] (fun y => (A.transition i k y : ℂ)) := by
    filter_upwards [(((A.isOpen_baseSet i).inter (A.isOpen_baseSet j)).inter
      (A.isOpen_baseSet k)).mem_nhds hx] with y hy
    exact congrArg (fun u : ℂˣ => (u : ℂ)) (A.transition_comp i j k y hy)
  rw [← heq.fderiv_eq]
  exact fderiv_fun_mul (transition_differentiableAt A j k x ⟨hx.1.2, hx.2⟩)
    (transition_differentiableAt A i j x hx.1)

/-- The logarithmic derivatives satisfy the additive cocycle identity. -/
theorem logDerivative_add (i j k : ι) (x : ComplexPlane₂)
    (hx : x ∈ A.baseSet i ∩ A.baseSet j ∩ A.baseSet k) :
    logDerivative A i j x + logDerivative A j k x = logDerivative A i k x := by
  have hmul : (A.transition j k x : ℂ) * (A.transition i j x : ℂ) =
      (A.transition i k x : ℂ) :=
    congrArg (fun u : ℂˣ => (u : ℂ)) (A.transition_comp i j k x hx)
  unfold logDerivative
  rw [transition_fderiv_comp A i j k x hx, ← hmul]
  ext v
  simp only [add_apply, smul_apply, smul_eq_mul]
  field_simp [A.transition_ne_zero i j x, A.transition_ne_zero j k x]

/-- A chart's self-transition has zero logarithmic derivative. -/
theorem logDerivative_self (i : ι) (x : ComplexPlane₂) (hx : x ∈ A.baseSet i) :
    logDerivative A i i x = 0 := by
  exact add_eq_left.mp (logDerivative_add A i i i x ⟨⟨hx, hx⟩, hx⟩)

/-- Reversing a transition negates its logarithmic derivative. -/
theorem logDerivative_reverse (i j : ι) (x : ComplexPlane₂)
    (hx : x ∈ A.baseSet i ∩ A.baseSet j) :
    logDerivative A j i x = -logDerivative A i j x := by
  have h := logDerivative_add A i j i x ⟨hx, hx.1⟩
  rw [logDerivative_self A i x hx.1] at h
  simpa only [← add_assoc, neg_add_cancel, zero_add, add_zero] using
    congrArg (fun t : ComplexPlane₂ →L[ℝ] ℂ => -logDerivative A i j x + t) h

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationConnection
