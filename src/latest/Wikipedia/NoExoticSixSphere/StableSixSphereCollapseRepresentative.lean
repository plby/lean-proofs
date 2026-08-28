import Wikipedia.NoExoticSixSphere.StableSixSphereRegularRepresentative
import Wikipedia.NoExoticSixSphere.StableSixSphereCollapse
import Wikipedia.NoExoticSixSphere.StereographicFiberCollapseData

/-!
# Geometric sixth-stem representatives retain actual stable nonvanishing

The regular fiber's constructed framing and collapse data come from the
original sphere map's stereographic equations. The exact homeomorphism
square preserves finite suspension nullity, hence zero in the actual
direct limit. Every nonzero class therefore supplies a nonempty regular
six-manifold with a nonzero actual framed-collapse class.

This does not assert that the fiber is two-connected or that its Arf
invariant detects this nonvanishing. Those are further obligations.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.StereographicFiber

theorem stableClass_eq_null_iff {k : ℕ} (f : StableSixSphereMaps.StageMap k)
    (hf : ContMDiff (𝓡 (k + 8)) (𝓡 (k + 2)) ∞ f) (b : Sphere (k + 2))
    (hreg : ∀ x, f x = b → Surjective (mfderiv (𝓡 (k + 8)) (𝓡 (k + 2)) f x))
    (a : Sphere (k + 8)) (ha : f a = -b) :
    letI := regularFiberAtlas f hf b hreg 6 (by simp only [finrank_euclideanSpace_fin]);
    (collapseData (k := 6) f hf b hreg a ha).sixthStableClass (by change 8 ≤ k + 8; omega) =
        StableSixSphereMaps.nullClass ↔
      StableSixSphereMaps.ofMap f = StableSixSphereMaps.nullClass := by
  let := regularFiberAtlas f hf b hreg 6 (by simp only [finrank_euclideanSpace_fin])
  rw [EuclideanEmbedding.FramedCollapseData.sixthStableClass_eq_null_iff,
    StableSixSphereMaps.ofMap_eq_nullClass_iff]
  exact exists_congr (fun r ↦ iterate_collapse_nullhomotopic_iff (k := 6) f hf b hreg a ha r)

end NoExoticSixSphere.StereographicFiber

namespace NoExoticSixSphere.StableSixSphereMaps

theorem exists_nonzero_framed_collapse_representative (c : Class) (hc : c ≠ nullClass) :
    ∃ (k : ℕ) (g : StageMap k),
      ∃ hg : ContMDiff (𝓡 (k + 8)) (𝓡 (k + 2)) ∞ g,
        ∃ (b : Sphere (k + 2))
          (hreg : ∀ x, g x = b → Surjective (mfderiv (𝓡 (k + 8)) (𝓡 (k + 2)) g x))
          (a : Sphere (k + 8)) (ha : g a = -b),
          ofMap g = c ∧ Nonempty {x : Sphere (k + 8) // g x = b} ∧
          letI := regularFiberAtlas g hg b hreg 6 (by simp only [finrank_euclideanSpace_fin]);
          (StereographicFiber.collapseData (k := 6) g hg b hreg a ha).sixthStableClass
            (by change 8 ≤ k + 8; omega) ≠ nullClass := by
  obtain ⟨k, g, hg, b, hreg, he, hne⟩ := exists_nonempty_smooth_regular_representative c hc
  have hn : ofMap g ≠ nullClass := fun h ↦ hc (he.symm.trans h)
  obtain ⟨a, ha⟩ := surjective_of_stable_class_ne_null g hn (-b)
  refine ⟨k, g, hg, b, hreg, a, ha, he, hne, ?_⟩
  let := regularFiberAtlas g hg b hreg 6 (by simp only [finrank_euclideanSpace_fin])
  exact fun h ↦ hn ((StereographicFiber.stableClass_eq_null_iff g hg b hreg a ha).mp h)

end NoExoticSixSphere.StableSixSphereMaps
