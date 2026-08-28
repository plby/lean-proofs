import Wikipedia.NoExoticSixSphere.FlatDoublePointCoordinates

/-!
# The closed double-point set depends only on the local map germ

Equality near a source point gives equality of the actual double-point
sets near its diagonal pair. Their closures agree locally as well; no
global equality of smooth representatives is needed.
-/

open Set Filter Function
open scoped Topology

namespace NoExoticSixSphere.FlatDoubleCurve

theorem closure_eventuallyEq_of_eventuallyEq {X : Type*} [TopologicalSpace X]
    {S T : Set X} {p : X} (he : S =ᶠ[𝓝 p] T) : closure S =ᶠ[𝓝 p] closure T := by
  obtain ⟨A, hAe, hA, hp⟩ := mem_nhds_iff.mp he
  filter_upwards [hA.mem_nhds hp] with q hq
  apply propext
  constructor
  · intro hs
    have hl : q ∈ closure (A ∩ S) := hA.inter_closure ⟨hq, hs⟩
    apply closure_mono _ hl
    intro r hr
    exact (hAe hr.1).mp hr.2
  · intro ht
    have hl : q ∈ closure (A ∩ T) := hA.inter_closure ⟨hq, ht⟩
    apply closure_mono _ hl
    intro r hr
    exact (hAe hr.1).mpr hr.2

variable {U F : Type} [TopologicalSpace U]

theorem doublePoints_eventuallyEq {g h : U × ℝ → F} {p : U × ℝ}
    (he : g =ᶠ[𝓝 p] h) : doublePoints g =ᶠ[𝓝 (p, p)] doublePoints h := by
  have h₁ := he.comp_tendsto
    (continuous_fst.continuousAt : Tendsto Prod.fst (𝓝 (p, p)) (𝓝 p))
  have h₂ := he.comp_tendsto
    (continuous_snd.continuousAt : Tendsto Prod.snd (𝓝 (p, p)) (𝓝 p))
  filter_upwards [h₁, h₂] with q hq₁ hq₂
  change g q.1 = h q.1 at hq₁
  change g q.2 = h q.2 at hq₂
  change (q.1 ≠ q.2 ∧ (q.1.1, g q.1) = (q.2.1, g q.2)) =
    (q.1 ≠ q.2 ∧ (q.1.1, h q.1) = (q.2.1, h q.2))
  rw [hq₁, hq₂]

theorem closedDoublePoints_eventuallyEq {g h : U × ℝ → F} {p : U × ℝ}
    (he : g =ᶠ[𝓝 p] h) :
    closure (doublePoints g) =ᶠ[𝓝 (p, p)] closure (doublePoints h) :=
  closure_eventuallyEq_of_eventuallyEq (doublePoints_eventuallyEq he)

theorem diagonal_mem_closedDoublePoints_iff {g h : U × ℝ → F} {p : U × ℝ}
    (he : g =ᶠ[𝓝 p] h) :
    (p, p) ∈ closure (doublePoints g) ↔ (p, p) ∈ closure (doublePoints h) :=
  Iff.of_eq (closedDoublePoints_eventuallyEq he).eq_of_nhds

end NoExoticSixSphere.FlatDoubleCurve
