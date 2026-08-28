import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.Connected.PathConnected

/-!
# Connectivity transferred through an actual homotopy right inverse

Only the specified homotopy from `r ∘ s` to the identity is required.
No equivalence between the two spaces is asserted.
-/

noncomputable section

open ContinuousMap

namespace NoExoticSixSphere.HomotopyRetractConnectivity

variable {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
  (r : C(A, X)) (s : C(X, A)) (h : (r.comp s).Homotopic (ContinuousMap.id X))

include r s h

theorem pathConnected [PathConnectedSpace A] : PathConnectedSpace X := by
  obtain ⟨H⟩ := h
  let η (x : X) : Path (r (s x)) x :=
    { toFun := fun u ↦ H (u, x)
      continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
      source' := H.map_zero_left x
      target' := H.map_one_left x }
  refine { nonempty := ⟨r (Classical.arbitrary A)⟩, joined := ?_ }
  intro x y
  exact ⟨((η x).symm.trans
    ((PathConnectedSpace.somePath (s x) (s y)).map r.continuous)).trans (η y)⟩

theorem nullhomotopies {K : Type*} [TopologicalSpace K]
    (hnull : ∀ f : C(K, A), ∃ c, f.Homotopic (ContinuousMap.const K c)) :
    ∀ f : C(K, X), ∃ c, f.Homotopic (ContinuousMap.const K c) := by
  intro f
  obtain ⟨c, hc⟩ := hnull (s.comp f)
  have he : (r.comp (s.comp f)).Homotopic f := h.comp (Homotopic.refl f)
  exact ⟨r c, he.symm.trans ((Homotopic.refl r).comp hc)⟩

end NoExoticSixSphere.HomotopyRetractConnectivity
