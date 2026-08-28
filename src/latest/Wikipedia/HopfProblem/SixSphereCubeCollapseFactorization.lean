import Wikipedia.HopfProblem.SixSphereCubeCollapseTopology
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Universal continuous factorization through the native collapse

A continuous map constant on the collapsed closed subset descends
uniquely to the actual one-point compactification. The target is any
topological space: no separation assumption is used in the descent.
-/

noncomputable section

open Set Topology
open scoped OnePoint

namespace Wikipedia.HopfProblem.SixSphereCube

variable {K X : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
variable [TopologicalSpace X] (F : Set K) (hF : IsClosed F) (hne : F.Nonempty)
variable (f : C(K, X)) (x : X) (hf : ∀ a ∈ F, f a = x)

/-- The actual quotient-map lift, for an arbitrary topological target. -/
def collapseLift : C(OnePoint ↥Fᶜ, X) :=
  IsQuotientMap.lift (f := collapseMap F hF) (isQuotientMap_collapse F hF hne) f (by
    intro a b h
    rcases (collapse_eq_iff F a b).mp h with rfl | ⟨ha, hb⟩
    · rfl
    · exact (hf a ha).trans (hf b hb).symm)

@[simp] theorem collapseLift_comp :
    (collapseLift F hF hne f x hf).comp (collapseMap F hF) = f :=
  IsQuotientMap.lift_comp (f := collapseMap F hF) (isQuotientMap_collapse F hF hne) f _

@[simp] theorem collapseLift_apply (a : K) :
    collapseLift F hF hne f x hf (collapse F a) = f a :=
  ContinuousMap.congr_fun (collapseLift_comp F hF hne f x hf) a

@[simp] theorem collapseLift_coe (a : ↥Fᶜ) :
    collapseLift F hF hne f x hf (a : OnePoint ↥Fᶜ) = f a.val := by
  simpa only [collapse_coe] using collapseLift_apply F hF hne f x hf a.val

@[simp] theorem collapseLift_infty : collapseLift F hF hne f x hf ∞ = x := by
  obtain ⟨a, ha⟩ := hne
  have h := collapseLift_apply F hF ⟨a, ha⟩ f x hf a
  rw [collapse_of_mem F ha] at h
  exact h.trans (hf a ha)

/-- The commuting triangle determines the lift uniquely, without any target separation axiom. -/
theorem collapseLift_unique (g : C(OnePoint ↥Fᶜ, X))
    (hg : g.comp (collapseMap F hF) = f) : g = collapseLift F hF hne f x hf := by
  ext z
  obtain ⟨a, rfl⟩ := collapse_surjective F hne z
  exact (ContinuousMap.congr_fun hg a).trans (collapseLift_apply F hF hne f x hf a).symm

end Wikipedia.HopfProblem.SixSphereCube
