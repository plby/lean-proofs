import Wikipedia.SmoothSixDPoincare.ShearedFrameChart
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Transverse blocks of an actual axis-fixing coordinate change

Fixing the scalar axis forces an upper-triangular derivative with identity
longitudinal block. Its transverse block is invertible whenever the full
derivative is invertible. These are identities of actual continuous linear maps.
-/

noncomputable section

open Set Filter Function
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.AxisCoordinates

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def tangentShear (L : (ℝ × V) →L[ℝ] (ℝ × V)) : V →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ V).comp (L.comp (ContinuousLinearMap.inr ℝ ℝ V))

def transverseBlock (L : (ℝ × V) →L[ℝ] (ℝ × V)) : V →L[ℝ] V :=
  (ContinuousLinearMap.snd ℝ ℝ V).comp (L.comp (ContinuousLinearMap.inr ℝ ℝ V))

theorem contDiff_tangentShear : ContDiff ℝ ∞ (tangentShear (V := V)) :=
  contDiff_const.clm_comp (contDiff_id.clm_comp contDiff_const)

theorem contDiff_transverseBlock : ContDiff ℝ ∞ (transverseBlock (V := V)) :=
  contDiff_const.clm_comp (contDiff_id.clm_comp contDiff_const)

theorem axis_block_apply (L : (ℝ × V) →L[ℝ] (ℝ × V)) (hL : L (1, 0) = (1, 0))
    (s : ℝ) (z : V) : L (s, z) = (s + tangentShear L z, transverseBlock L z) := by
  have hp : (s, z) = s • (1, (0 : V)) + (0, z) := by simp
  rw [hp, map_add, map_smul, hL]
  apply Prod.ext <;> simp [tangentShear, transverseBlock]

theorem axis_block_eq (L : (ℝ × V) →L[ℝ] (ℝ × V)) (hL : L (1, 0) = (1, 0)) :
    L = FrameField.shearedBlock (tangentShear L) (transverseBlock L) := by
  apply ContinuousLinearMap.ext
  intro p
  rw [FrameField.shearedBlock_apply]
  exact axis_block_apply L hL p.1 p.2

theorem bijective_transverseBlock (L : (ℝ × V) →L[ℝ] (ℝ × V))
    (hL : L (1, 0) = (1, 0)) (hi : Bijective L) : Bijective (transverseBlock L) := by
  constructor
  · intro z w hzw
    have he : L (-tangentShear L z, z) = L (-tangentShear L w, w) := by
      rw [axis_block_apply L hL, axis_block_apply L hL]
      simp only [neg_add_cancel, hzw]
    exact congrArg (fun p : ℝ × V => p.2) (hi.1 he)
  · intro w
    obtain ⟨⟨s, z⟩, hz⟩ := hi.2 (0, w)
    rw [axis_block_apply L hL] at hz
    exact ⟨z, congrArg (fun p : ℝ × V => p.2) hz⟩

theorem isInvertible_transverseBlock [FiniteDimensional ℝ V]
    (L : (ℝ × V) →L[ℝ] (ℝ × V)) (hL : L (1, 0) = (1, 0)) (hi : L.IsInvertible) :
    (transverseBlock L).IsInvertible := by
  let e := (LinearEquiv.ofBijective (transverseBlock L).toLinearMap
    (bijective_transverseBlock L hL hi.bijective)).toContinuousLinearEquiv
  exact ⟨e, rfl⟩

/-- Equality of the whole axis germ forces the longitudinal derivative to be exactly identity. -/
theorem derivative_fixes_axis {F : (ℝ × V) → (ℝ × V)} {s : ℝ}
    (hF : ContDiffAt ℝ ∞ F (s, 0))
    (heq : (fun r : ℝ => F (r, 0)) =ᶠ[𝓝 s] (fun r => (r, (0 : V)))) :
    fderiv ℝ F (s, 0) (1, 0) = (1, 0) := by
  have ha : HasDerivAt (fun r : ℝ => (r, (0 : V))) (1, 0) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s 0)
  have hd := (hF.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s ha
  exact hd.deriv.symm.trans (heq.deriv_eq.trans ha.deriv)

end Wikipedia.HopfProblem.DegreeCollapse.AxisCoordinates
