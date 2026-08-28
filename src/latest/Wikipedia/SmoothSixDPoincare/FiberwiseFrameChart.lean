import Wikipedia.SmoothSixDPoincare.SmoothComplementQuotient
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Smooth fiberwise changes of an actual tubular frame

A smoothly varying invertible linear map gives a partial diffeomorphism on
the product over its open base domain. Both directions are explicit. It
fixes the zero section globally, and its derivative there is the block map
given by the original frame, with no extra base-derivative term.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FrameField

variable {X Z F : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def fiberMap (T : X → (Z →L[ℝ] F)) (p : X × Z) : X × F := (p.1, T p.1 p.2)

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
theorem fiberMap_zero (T : X → (Z →L[ℝ] F)) (x : X) : fiberMap T (x, 0) = (x, 0) := by
  simp only [fiberMap, map_zero]

theorem contDiffOn_fiberMap {T : X → (Z →L[ℝ] F)} {U : Set X}
    (hT : ContDiffOn ℝ ∞ T U) : ContDiffOn ℝ ∞ (fiberMap T) (Prod.fst ⁻¹' U) := by
  exact contDiffOn_fst.prodMk
    ((hT.comp contDiffOn_fst (fun _ hp => hp)).clm_apply contDiffOn_snd)

variable [FiniteDimensional ℝ Z]

/-- The actual smooth coordinate change and its actual smooth inverse. -/
def fiberwiseFrameChart {T : X → (Z →L[ℝ] F)} {U : Set X}
    (hU : IsOpen U) (hT : ContDiffOn ℝ ∞ T U)
    (hi : ∀ x ∈ U, (T x).IsInvertible) :
    PartialDiffeomorph 𝓘(ℝ, X × Z) 𝓘(ℝ, X × F) (X × Z) (X × F) ∞ where
  toFun := fiberMap T
  invFun := fun p => (p.1, (T p.1).inverse p.2)
  source := Prod.fst ⁻¹' U
  target := Prod.fst ⁻¹' U
  map_source' := fun _ hp => hp
  map_target' := fun _ hp => hp
  left_inv' := fun p hp => Prod.ext rfl ((hi p.1 hp).inverse_apply_self p.2)
  right_inv' := fun p hp => Prod.ext rfl ((hi p.1 hp).self_apply_inverse p.2)
  open_source := hU.preimage continuous_fst
  open_target := hU.preimage continuous_fst
  contMDiffOn_toFun := (contDiffOn_fiberMap hT).contMDiffOn
  contMDiffOn_invFun := by
    have hInv : ContDiffOn ℝ ∞ (fun x => (T x).inverse) U := by
      intro x hx
      exact ((hi x hx).contDiffAt_map_inverse.comp x
        (hT.contDiffAt (hU.mem_nhds hx))).contDiffWithinAt
    exact (contDiffOn_fst.prodMk
      ((hInv.comp contDiffOn_fst (fun _ hp => hp)).clm_apply contDiffOn_snd)).contMDiffOn

omit [FiniteDimensional ℝ Z] in
/-- Only the prescribed fiber map contributes to the derivative on the zero section. -/
theorem hasFDerivAt_fiberMap_zero {T : X → (Z →L[ℝ] F)} {x : X}
    (hT : DifferentiableAt ℝ T x) :
    HasFDerivAt (fiberMap T) ((ContinuousLinearMap.id ℝ X).prodMap (T x)) (x, 0) := by
  have hfirst : HasFDerivAt (fun p : X × Z => T p.1)
      ((fderiv ℝ T x).comp (ContinuousLinearMap.fst ℝ X Z)) (x, 0) :=
    hT.hasFDerivAt.comp (x, 0) hasFDerivAt_fst
  have hsecond := hfirst.clm_apply
    (hasFDerivAt_snd : HasFDerivAt (fun p : X × Z => p.2)
      (ContinuousLinearMap.snd ℝ X Z) (x, 0))
  have hboth := (hasFDerivAt_fst : HasFDerivAt (fun p : X × Z => p.1)
    (ContinuousLinearMap.fst ℝ X Z) (x, 0)).prodMk hsecond
  convert hboth using 1 <;> first
    | rfl
    | (apply ContinuousLinearMap.ext; intro p; simp; rfl)

end Wikipedia.SmoothSixDPoincare.FrameField
