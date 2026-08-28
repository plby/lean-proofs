import Wikipedia.NoExoticSixSphere.FamilyDoublePointClosure
import Wikipedia.NoExoticSixSphere.FlatDoublePointGerm

/-!
# Family double points and spatial derivatives depend only on the map germ

Equality of the joint family near a time/source point preserves both the
spatial-derivative germ and the actual shared-time double-point closure germ
near its diagonal pair. No global equality of representatives is required.
-/

open Set Filter Function
open scoped Topology

namespace NoExoticSixSphere.FamilyEmbedding

section Topology

variable {P E F : Type*} [TopologicalSpace P] [TopologicalSpace E]

theorem doublePoints_eventuallyEq {g h : P → E → F} {p : P × E}
    (he : uncurry g =ᶠ[𝓝 p] uncurry h) :
    doublePoints g =ᶠ[𝓝 (p.1, (p.2, p.2))] doublePoints h := by
  have h₁ := he.comp_tendsto
    ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousAt :
      Tendsto (fun q : P × (E × E) ↦ (q.1, q.2.1)) (𝓝 (p.1, (p.2, p.2))) (𝓝 p))
  have h₂ := he.comp_tendsto
    ((continuous_fst.prodMk (continuous_snd.comp continuous_snd)).continuousAt :
      Tendsto (fun q : P × (E × E) ↦ (q.1, q.2.2)) (𝓝 (p.1, (p.2, p.2))) (𝓝 p))
  filter_upwards [h₁, h₂] with q hq₁ hq₂
  change g q.1 q.2.1 = h q.1 q.2.1 at hq₁
  change g q.1 q.2.2 = h q.1 q.2.2 at hq₂
  change (q.2.1 ≠ q.2.2 ∧ g q.1 q.2.1 = g q.1 q.2.2) =
    (q.2.1 ≠ q.2.2 ∧ h q.1 q.2.1 = h q.1 q.2.2)
  rw [hq₁, hq₂]

theorem closedDoublePoints_eventuallyEq {g h : P → E → F} {p : P × E}
    (he : uncurry g =ᶠ[𝓝 p] uncurry h) :
    closure (doublePoints g) =ᶠ[𝓝 (p.1, (p.2, p.2))] closure (doublePoints h) :=
  FlatDoubleCurve.closure_eventuallyEq_of_eventuallyEq (doublePoints_eventuallyEq he)

theorem diagonal_mem_closedDoublePoints_iff {g h : P → E → F} {p : P × E}
    (he : uncurry g =ᶠ[𝓝 p] uncurry h) :
    (p.1, (p.2, p.2)) ∈ closure (doublePoints g) ↔
      (p.1, (p.2, p.2)) ∈ closure (doublePoints h) :=
  Iff.of_eq (closedDoublePoints_eventuallyEq he).eq_of_nhds

end Topology

section Derivative

variable {P E F : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem spatial_fderiv_eventuallyEq {g h : P → E → F} {p : P × E}
    (he : uncurry g =ᶠ[𝓝 p] uncurry h) :
    (fun q : P × E ↦ fderiv ℝ (g q.1) q.2) =ᶠ[𝓝 p]
      (fun q : P × E ↦ fderiv ℝ (h q.1) q.2) := by
  filter_upwards [he.eventually_nhds] with q hq
  have hq' : uncurry g =ᶠ[𝓝 q] uncurry h := hq
  have hslice : g q.1 =ᶠ[𝓝 q.2] h q.1 :=
    hq'.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  exact hslice.fderiv_eq

end Derivative
end NoExoticSixSphere.FamilyEmbedding
