import Wikipedia.NoExoticSixSphere.StableCollapseChoiceIndependence
import Wikipedia.NoExoticSixSphere.StableSixSphereCollapseRepresentative
import Wikipedia.NoExoticSixSphere.RegularSphereFiberEmbedding

/-!
# The actual canonical tube collapse of a regular sphere-map fiber

The chosen tube is the original canonical framed tube of the stereographic
embedding, with the frame induced by the original regular equations. Its
collapse is now compared to the original sphere map at every finite
suspension stage. The normal-coordinate comparison constructs the homotopy;
it is not an extra premise about the chosen tube.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.StereographicFiber

variable {n k : ℕ} (f : C(Sphere (n + k), Sphere n))
  (hf : ContMDiff (𝓡 (n + k)) (𝓡 n) ∞ f) (b : Sphere n)
  (hreg : ∀ x, f x = b → Surjective (mfderiv (𝓡 (n + k)) (𝓡 n) f x))
  (a : Sphere (n + k)) (ha : f a = -b)
  [Nonempty {x : Sphere (n + k) // f x = b}]

def tubeCollapseData :
    letI := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin]);
    (embedding f hf b hreg a ha).FramedCollapseData (frame f hf b hreg a ha) := by
  letI := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin])
  letI := regularFiber_isManifold f hf b hreg k (by simp only [finrank_euclideanSpace_fin])
  letI := RegularSphereFiber.fiber_compact f b
  exact (embedding f hf b hreg a ha).framedCollapseData (frame f hf b hreg a ha)

theorem iterate_tubeCollapse_nullhomotopic_iff (r : ℕ) :
    letI := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin]);
    (SphereMapSuspension.iterate (tubeCollapseData f hf b hreg a ha).sphereMap r).Nullhomotopic ↔
      (SphereMapSuspension.iterate f r).Nullhomotopic := by
  let := regularFiberAtlas f hf b hreg k (by simp only [finrank_euclideanSpace_fin])
  let := regularFiber_isManifold f hf b hreg k (by simp only [finrank_euclideanSpace_fin])
  let := RegularSphereFiber.fiber_compact f b
  exact ((tubeCollapseData f hf b hreg a ha).iterate_sphereMap_nullhomotopic_iff
    (collapseData f hf b hreg a ha) r).trans
      (iterate_collapse_nullhomotopic_iff f hf b hreg a ha r)

end NoExoticSixSphere.StereographicFiber

namespace NoExoticSixSphere.StableSixSphereMaps

theorem exists_nonzero_canonical_tube_representative (c : Class) (hc : c ≠ nullClass) :
    ∃ (k : ℕ) (g : StageMap k),
      ∃ hg : ContMDiff (𝓡 (k + 8)) (𝓡 (k + 2)) ∞ g,
        ∃ (b : Sphere (k + 2))
          (hreg : ∀ x, g x = b → Surjective (mfderiv (𝓡 (k + 8)) (𝓡 (k + 2)) g x))
          (a : Sphere (k + 8)) (ha : g a = -b),
          ofMap g = c ∧ ∃ hne : Nonempty {x : Sphere (k + 8) // g x = b},
          letI := hne;
          letI := regularFiberAtlas g hg b hreg 6 (by simp only [finrank_euclideanSpace_fin]);
          (StereographicFiber.tubeCollapseData (k := 6) g hg b hreg a ha).sixthStableClass
            (by change 8 ≤ k + 8; omega) ≠ nullClass := by
  obtain ⟨k, g, hg, b, hreg, a, ha, he, hne, hn⟩ :=
    exists_nonzero_framed_collapse_representative c hc
  refine ⟨k, g, hg, b, hreg, a, ha, he, hne, ?_⟩
  let := hne
  let := regularFiberAtlas g hg b hreg 6 (by simp only [finrank_euclideanSpace_fin])
  let := regularFiber_isManifold g hg b hreg 6 (by simp only [finrank_euclideanSpace_fin])
  let := RegularSphereFiber.fiber_compact g b
  have he := EuclideanEmbedding.FramedCollapseData.sixthStableClass_eq_of_same_frame
    (StereographicFiber.tubeCollapseData (k := 6) g hg b hreg a ha)
    (StereographicFiber.collapseData (k := 6) g hg b hreg a ha)
    (by change 8 ≤ k + 8; omega)
  exact fun hz ↦ hn (he.symm.trans hz)

end NoExoticSixSphere.StableSixSphereMaps
