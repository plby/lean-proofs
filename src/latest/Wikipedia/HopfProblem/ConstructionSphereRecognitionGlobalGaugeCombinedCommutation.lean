import Wikipedia.HopfProblem.ConstructionSphereRecognitionGlobalGaugeSeparation
import Wikipedia.HopfProblem.ConstructionSphereRecognitionGlobalGaugeMap

/-!
# Commutation of the two actual supported elliptic gauge maps

The maps fix the whole original cusp piece and the other original
elliptic piece.  Preservation of the original base projection preserves
both cap patches, so the maps with disjoint cap patches commute for all
phases and times.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge

open Elliptic SpecialPeriods SpecialPeriods.Threefold

attribute [local instance] Threefold.chartedSpace

/-- Every point of the entire original cusp piece is fixed. -/
@[simp] theorem globalMap_cusp (j : Kind) (τ s : ℝ) (y : CuspGeometry.LocalSpace) :
    globalMap j τ s (CuspGeometry.inclusion y) = CuspGeometry.inclusion y :=
  globalMap_eq_self_of_not_mem_patch j τ s (cusp_inclusion_not_mem_ellipticPatch j y)

/-- The supported map fixes the entire other original elliptic piece. -/
@[simp] theorem globalMap_other_inclusion (j k : Kind) (hjk : j ≠ k) (τ s : ℝ)
    (y : EllipticGeometry.LocalSpace k) :
    globalMap j τ s (EllipticGeometry.inclusion k y) = EllipticGeometry.inclusion k y :=
  globalMap_eq_self_of_not_mem_patch j τ s (other_elliptic_inclusion_not_mem_patch j k hjk y)

@[simp] theorem globalDiffeomorph_cusp (j : Kind) (τ s : ℝ) (y : CuspGeometry.LocalSpace) :
    globalDiffeomorph j τ s (CuspGeometry.inclusion y) = CuspGeometry.inclusion y :=
  globalMap_cusp j τ s y

@[simp] theorem globalDiffeomorph_other_inclusion (j k : Kind) (hjk : j ≠ k) (τ s : ℝ)
    (y : EllipticGeometry.LocalSpace k) :
    globalDiffeomorph j τ s (EllipticGeometry.inclusion k y) = EllipticGeometry.inclusion k y :=
  globalMap_other_inclusion j k hjk τ s y

/-- Base-projection preservation preserves every original elliptic patch,
including a patch different from the one on which the map is supported. -/
@[simp] theorem globalMap_mem_capPatch_iff (j k : Kind) (τ s : ℝ) (x : Threefold.Space) :
    globalMap j τ s x ∈ capPatch k ↔ x ∈ capPatch k := by
  change Threefold.projection (globalMap j τ s x) ∈ specialBaseCover.fillingPatch (some k) ↔
    Threefold.projection x ∈ specialBaseCover.fillingPatch (some k)
  rw [globalMap_projection]

/-- The supported maps on distinct original cap patches commute pointwise. -/
theorem globalMap_commute_apply (j k : Kind) (hjk : j ≠ k) (τ σ s t : ℝ)
    (x : Threefold.Space) :
    globalMap j τ s (globalMap k σ t x) = globalMap k σ t (globalMap j τ s x) := by
  by_cases hx : x ∈ capPatch j
  · have hk : x ∉ capPatch k :=
      Set.disjoint_left.mp (ellipticPatches_disjoint j k hjk) hx
    have hgk : globalMap j τ s x ∉ capPatch k :=
      fun h => hk ((globalMap_mem_capPatch_iff j k τ s x).mp h)
    rw [globalMap_eq_self_of_not_mem_patch k σ t hk,
      globalMap_eq_self_of_not_mem_patch k σ t hgk]
  · have hgj : globalMap k σ t x ∉ capPatch j :=
      fun h => hx ((globalMap_mem_capPatch_iff k j σ t x).mp h)
    rw [globalMap_eq_self_of_not_mem_patch j τ s hgj,
      globalMap_eq_self_of_not_mem_patch j τ s hx]

theorem globalMap_commute (j k : Kind) (hjk : j ≠ k) (τ σ s t : ℝ) :
    Function.Commute (globalMap j τ s) (globalMap k σ t) :=
  globalMap_commute_apply j k hjk τ σ s t

/-- The genuine diffeomorphisms commute in the unchanged original global atlas. -/
theorem globalDiffeomorph_commute (j k : Kind) (hjk : j ≠ k) (τ σ s t : ℝ) :
    Function.Commute (globalDiffeomorph j τ s) (globalDiffeomorph k σ t) :=
  globalMap_commute j k hjk τ σ s t

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GlobalGauge
