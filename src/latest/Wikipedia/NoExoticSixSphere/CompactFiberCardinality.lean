import Mathlib.Topology.Covering.Basic
import Mathlib.Data.Set.Card

/-!
# Local stability of actual compact fibers

If the projection of a compact Hausdorff space is locally a homeomorphism
along one fiber, that fiber has an evenly covered neighborhood. All nearby
actual fibers are homeomorphic to it, including when the fiber is empty.
This supplies a cardinality comparison without assigning a model fiber.
-/

noncomputable section

open Set Topology

namespace NoExoticSixSphere.CompactFiber

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [T2Space E] [T2Space X] [CompactSpace E] (f : E → X) (hf : Continuous f) (x : X)
  (hlocal : ∀ e ∈ f ⁻¹' {x}, ∃ φ : OpenPartialHomeomorph E X,
    e ∈ φ.source ∧ EqOn f φ φ.source)

include hf in
theorem eventually_fiber_property (P : E → Prop)
    (hP : ∀ e, f e = x → ∀ᶠ z in 𝓝 e, P z) :
    ∀ᶠ y in 𝓝 x, ∀ e, f e = y → P e := by
  let U := interior {e | P e}
  have hx : x ∉ f '' Uᶜ := by
    rintro ⟨e, he, hex⟩
    exact he (mem_interior_iff_mem_nhds.mpr (hP e hex))
  have hclosed : IsClosed (f '' Uᶜ) := hf.isClosedMap _ isOpen_interior.isClosed_compl
  filter_upwards [hclosed.isOpen_compl.mem_nhds hx] with y hy
  intro e he
  have heU : e ∈ U := by
    by_contra hn
    exact hy ⟨e, hn, he⟩
  exact interior_subset heU

include hf hlocal in
theorem eventually_homeomorphic_fibers :
    ∀ᶠ y in 𝓝 x, Nonempty ((f ⁻¹' {x}) ≃ₜ (f ⁻¹' {y})) := by
  have hloc := IsLocalHomeomorphOn.mk f (f ⁻¹' {x}) hlocal
  have hc : IsEvenlyCovered f x (f ⁻¹' {x}) :=
    IsEvenlyCovered.of_openPartialHomeomorph hf (fun e he ↦ by
      obtain ⟨φ, hφ, heq⟩ := hloc e he
      exact ⟨φ, hφ, heq.symm⟩)
  obtain ⟨hd, U, hxU, hU, hfU, H, hH⟩ := hc
  filter_upwards [hU.mem_nhds hxU] with y hy
  exact ⟨(show IsEvenlyCovered f y (f ⁻¹' {x}) from
    ⟨hd, U, hy, hU, hfU, H, hH⟩).fiberHomeomorph⟩

include hf hlocal in
theorem eventually_ncard_eq :
    ∀ᶠ y in 𝓝 x, (f ⁻¹' {y}).ncard = (f ⁻¹' {x}).ncard := by
  filter_upwards [eventually_homeomorphic_fibers f hf x hlocal] with y hy
  obtain ⟨e⟩ := hy
  exact (Nat.card_congr e.toEquiv).symm

end NoExoticSixSphere.CompactFiber
