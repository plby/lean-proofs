import Wikipedia.HopfProblem.ConstructionSphereRecognitionGlobalGaugeMap
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFlow

/-!
# Equivariance for the full original global vertical flow

The original flow preserves the actual elliptic open patch because it
fixes the original base.  Inside the patch, equivariance is the already
proved native cap formula; outside, both extensions are the identity.
No alternate flow or quotient action is introduced.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge

open Elliptic SpecialPeriods SpecialPeriods.Threefold GaugeIsotopy

attribute [local instance] Threefold.chartedSpace specialEllipticPieceChartedSpace

theorem flow_mem_capPatch_iff (j : Kind) (u : ℂ) (x : Threefold.Space) :
    VerticalAction.flow u x ∈ capPatch j ↔ x ∈ capPatch j := by
  change Threefold.projection (VerticalAction.flow u x) ∈
      specialBaseCover.fillingPatch (some j) ↔
    Threefold.projection x ∈ specialBaseCover.fillingPatch (some j)
  rw [VerticalAction.projection_flow]

/-- The extension commutes with every parameter of the unchanged global complex flow. -/
theorem globalMap_flow (j : Kind) (τ s : ℝ) (u : ℂ) (x : Threefold.Space) :
    globalMap j τ s (VerticalAction.flow u x) =
      VerticalAction.flow u (globalMap j τ s x) := by
  by_cases hx : x ∈ capPatch j
  · let y := (capPatchDiffeomorph j).symm ⟨x, hx⟩
    have hy : EllipticGeometry.inclusion j y = x :=
      inclusion_capPatchDiffeomorph_symm j ⟨x, hx⟩
    rw [← hy, VerticalAction.flow_elliptic, globalMap_inclusion,
      nativeLocalizedCollarDiffeomorph_flow, globalMap_inclusion, VerticalAction.flow_elliptic]
  · have hux : VerticalAction.flow u x ∉ capPatch j :=
      fun h => hx ((flow_mem_capPatch_iff j u x).mp h)
    rw [globalMap_eq_self_of_not_mem_patch j τ s hux,
      globalMap_eq_self_of_not_mem_patch j τ s hx]

theorem globalDiffeomorph_flow (j : Kind) (τ s : ℝ) (u : ℂ) (x : Threefold.Space) :
    globalDiffeomorph j τ s (VerticalAction.flow u x) =
      VerticalAction.flow u (globalDiffeomorph j τ s x) :=
  globalMap_flow j τ s u x

theorem globalDiffeomorph_commute_flow (j : Kind) (τ s : ℝ) (u : ℂ) :
    Function.Commute (globalDiffeomorph j τ s) (VerticalAction.flow u) :=
  globalDiffeomorph_flow j τ s u

theorem globalDiffeomorph_symm_flow (j : Kind) (τ s : ℝ) (u : ℂ)
    (x : Threefold.Space) :
    (globalDiffeomorph j τ s).symm (VerticalAction.flow u x) =
      VerticalAction.flow u ((globalDiffeomorph j τ s).symm x) := by
  simp only [globalDiffeomorph_symm_apply]
  exact globalDiffeomorph_flow j τ (-s) u x

theorem globalIsotopy_flow (j : Kind) (τ : ℝ) (s : unitInterval) (u : ℂ)
    (x : Threefold.Space) :
    globalIsotopy j τ (s, VerticalAction.flow u x) =
      VerticalAction.flow u (globalIsotopy j τ (s, x)) :=
  globalDiffeomorph_flow j τ (s : ℝ) u x

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge
