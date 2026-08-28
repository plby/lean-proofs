import Wikipedia.NoExoticSixSphere.CompactSphereCoincidenceTrace
import Wikipedia.NoExoticSixSphere.SpherePairTransversalityOpen

/-!
# Transversality persists on a compact coincidence region

Local openness of the actual tangent-map condition is uniform along the
compact zero-time fiber. Compactness excludes new nontransverse points
near that fiber, even when it is empty.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CompactPairTrace

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] (f g : ℝ → Sphere 3 → M) (K : Set (Sphere 3 × Sphere 3))
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))
  (hK : IsCompact K)
  (ht : ∀ p ∈ K, f 0 p.1 = g 0 p.2 → Surjective
    ((mfderiv (𝓡 3) (𝓡 6) (f 0) p.1).coprod (mfderiv (𝓡 3) (𝓡 6) (g 0) p.2)))

include hf hg hK ht in
theorem eventually_transverse :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ p ∈ K, f t p.1 = g t p.2 → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) (f t) p.1).coprod (mfderiv (𝓡 3) (𝓡 6) (g t) p.2)) := by
  let : CompactSpace (space f g K) :=
    isCompact_iff_compactSpace.mp (isCompact_space f g K hf.continuous hg.continuous hK)
  let P : space f g K → Prop := fun a ↦ Surjective
    ((mfderiv (𝓡 3) (𝓡 6) (f a.val.1) a.val.2.1).coprod
      (mfderiv (𝓡 3) (𝓡 6) (g a.val.1) a.val.2.2))
  have hlocal : ∀ a : space f g K, time f g K a = 0 → ∀ᶠ b in 𝓝 a, P b := by
    intro a ha
    have hat : a.val.1 = 0 := ha
    have he : f 0 a.val.2.1 = g 0 a.val.2.2 := by
      have he' : f a.val.1 a.val.2.1 = g a.val.1 a.val.2.2 := a.property.2
      rwa [hat] at he'
    have hatr : P a := by
      change Surjective ((mfderiv (𝓡 3) (𝓡 6) (f a.val.1) a.val.2.1).coprod
        (mfderiv (𝓡 3) (𝓡 6) (g a.val.1) a.val.2.2))
      rw [hat]
      exact ht a.val.2 a.property.1.2 he
    have hnear := IntersectionTrace.eventually_native_transverse
      f g hf hg a.val a.property.2 hatr
    filter_upwards [continuous_subtype_val.continuousAt hnear] with b hb
    exact hb b.property.2
  have hfiber := CompactFiber.eventually_fiber_property
    (time f g K) (time f g K).continuous 0 P hlocal
  have htime : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  filter_upwards [hfiber, htime] with t hfiber htime
  intro p hp he
  exact hfiber ⟨(t, p), ⟨Ioo_subset_Icc_self htime, hp⟩, he⟩ rfl

end NoExoticSixSphere.CompactPairTrace
