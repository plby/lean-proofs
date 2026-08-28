import Wikipedia.NoExoticSixSphere.LocalInverse
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# Constructed centered smooth parametrizations of native manifolds

Translate an actual native chart before taking its inverse. Its source is
an open neighborhood of zero, its value at zero is the prescribed point,
and its native derivative is bijective. The topology and atlas are unchanged.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.NativeParametrization

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

def translation (a : D) : Diffeomorph 𝓘(ℝ, D) 𝓘(ℝ, D) D D ∞ where
  toEquiv := {
    toFun := fun x => x + a
    invFun := fun x => x - a
    left_inv := fun _ => add_sub_cancel_right _ _
    right_inv := fun _ => sub_add_cancel _ _ }
  contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff

variable {N : Type*} [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]

def centered (x : N) : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, D) D N ∞ :=
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := 𝓘(ℝ, D)) x
  (translation (c x)).toPartialDiffeomorph.trans c.symm

theorem zero_mem_centered_source (x : N) : (0 : D) ∈ (centered (D := D) x).source := by
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := 𝓘(ℝ, D)) x
  refine ⟨mem_univ _, ?_⟩
  change 0 + c x ∈ c.target
  rw [zero_add]
  exact c.map_source' (mem_extChartAt_source x)

theorem centered_zero (x : N) : centered (D := D) x (0 : D) = x := by
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := 𝓘(ℝ, D)) x
  change c.symm (0 + c x) = x
  rw [zero_add]
  exact c.left_inv' (mem_extChartAt_source x)

theorem mem_centered_target (x : N) : x ∈ (centered (D := D) x).target := by
  have hx := (centered (D := D) x).map_source' (zero_mem_centered_source (D := D) x)
  rwa [centered_zero] at hx

theorem isEmbedding_centered (x : N) :
    Topology.IsEmbedding (fun p : (centered (D := D) x).source => centered (D := D) x p) :=
  (centered (D := D) x).toOpenPartialHomeomorph.isOpenEmbedding_restrict.isEmbedding

theorem bijective_mfderiv_centered (x : N) :
    Bijective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, D) (centered (D := D) x) (0 : D)) :=
  PartialChart.bijective_mfderiv (centered (D := D) x) (zero_mem_centered_source (D := D) x)

end Wikipedia.SmoothSixDPoincare.NativeParametrization
