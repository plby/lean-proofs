import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.SeparatedMap
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Recovering a group parameter through genuine local charts

These elementary topological lemmas will be applied to the original
toric coordinate maps into the threefold. They do not put a manifold
structure on an automorphism group or replace its connected component.
-/

noncomputable section

open Filter Set Topology

namespace Wikipedia.HopfProblem.HolomorphicAutomorphismLocalRecovery

/-- A lift through a separated local homeomorphism is the selected local
inverse throughout a connected parameter space once it starts on that
inverse sheet. The whole image in the target chart is required. -/
theorem localInverse_eq_lift
    {A D X : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    [TopologicalSpace D] [T2Space D] [TopologicalSpace X]
    (p : D → X) (hp : IsLocalHomeomorph p)
    (e : OpenPartialHomeomorph D X) (he : EqOn p e e.source)
    (g : A → D) (hg : Continuous g) (h : A → X) (hh : Continuous h)
    (hht : ∀ a, h a ∈ e.target) (hproj : ∀ a, p (g a) = h a)
    (a : A) (ha : g a ∈ e.source) : ∀ b, g b = e.symm (h b) := by
  have hi : Continuous (e.symm ∘ h) :=
    e.symm.continuousOn.comp_continuous hh hht
  have hcomp : p ∘ g = p ∘ (e.symm ∘ h) := by
    funext b
    change p (g b) = p (e.symm (h b))
    rw [hproj b, he (e.map_target (hht b)), e.right_inv (hht b)]
  have hstart : g a = (e.symm ∘ h) a := by
    change g a = e.symm (h a)
    rw [← hproj a, he ha, e.left_inv ha]
  have heq := (T2Space.isSeparatedMap p).eq_of_comp_eq hp.isLocallyInjective
    hg hi hcomp a hstart
  exact fun b => congrFun heq b

/-- A continuous injective homomorphism from `ℂˣ` is a topological
embedding if its complex parameter can be recovered continuously near
the identity in the original target topology. No derivative topology
or local compactness of the target is required. -/
theorem isEmbedding_of_local_recovery
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (f : ℂˣ →* G) (hf : Continuous f) (hinj : Function.Injective f)
    (r : G → ℂ) (hr : ContinuousAt r 1) (hr1 : r 1 = 1)
    (hrec : ∀ᶠ u in (𝓝 (1 : G)).comap f, r (f u) = (u : ℂ)) :
    IsEmbedding f := by
  refine ⟨IsTopologicalGroup.isInducing_iff_nhds_one.mpr ?_, hinj⟩
  refine le_antisymm ?_ ?_
  · simpa only [map_one] using (hf.continuousAt (x := 1)).le_comap
  · have hlim : Tendsto (fun u : ℂˣ => r (f u))
        ((𝓝 (1 : G)).comap f) (𝓝 (1 : ℂ)) := by
      simpa only [hr1, Function.comp_def] using hr.tendsto.comp tendsto_comap
    have hval : Tendsto (fun u : ℂˣ => (u : ℂ))
        ((𝓝 (1 : G)).comap f) (𝓝 (1 : ℂ)) := hlim.congr' hrec
    have hid : Tendsto (id : ℂˣ → ℂˣ) ((𝓝 (1 : G)).comap f) (𝓝 1) :=
      Units.isEmbedding_val₀.tendsto_nhds_iff.mpr hval
    exact tendsto_id'.mp hid

end Wikipedia.HopfProblem.HolomorphicAutomorphismLocalRecovery
