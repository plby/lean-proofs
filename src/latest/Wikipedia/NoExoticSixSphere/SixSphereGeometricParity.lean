import Wikipedia.NoExoticSixSphere.ManifoldSphereHomotopyParity
import Wikipedia.NoExoticSixSphere.ManifoldSmallFourDisk
import Wikipedia.NoExoticSixSphere.SphereHomotopyGroups

/-!
# Every embedded three-sphere in the candidate six-sphere has zero geometric parity

The original topological six-sphere has trivial third homotopy. Ordinary
homotopy invariance compares any embedded immersive three-sphere with the
actual boundary of a small chart-contained four-disk, whose parity is zero.
The candidate's original smooth atlas and normal framing are retained.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse

theorem sphere_three_maps_homotopic_of_homeomorph_sixSphere
    {M : Type*} [TopologicalSpace M] (h : M ≃ₜ Sphere 6) (f g : C(Sphere 3, M)) :
    f.Homotopic g := by
  let : PathConnectedSpace M := h.symm.surjective.pathConnectedSpace h.symm.continuous
  let p := SphereCube.point 3
  obtain ⟨Hf⟩ := (SphereCubeHomotopy.basedCube_nullhomotopic_iff (by decide : 0 < 3) f).mp
    (genLoop_homotopic_const_of_homeomorph_sphere (by decide : 3 < 6) h (f p)
      (SphereCube.basedCube f))
  obtain ⟨Hg⟩ := (SphereCubeHomotopy.basedCube_nullhomotopic_iff (by decide : 0 < 3) g).mp
    (genLoop_homotopic_const_of_homeomorph_sphere (by decide : 3 < 6) h (g p)
      (SphereCube.basedCube g))
  let γ := PathConnectedSpace.somePath (f p) (g p)
  let K : (ContinuousMap.const (Sphere 3) (f p)).Homotopy (ContinuousMap.const _ (g p)) := {
    toFun := fun z ↦ γ z.1
    continuous_toFun := γ.continuous.comp continuous_fst
    map_zero_left := fun _ ↦ γ.source
    map_one_left := fun _ ↦ γ.target }
  exact ⟨Hf.toHomotopy.trans (K.trans Hg.toHomotopy.symm)⟩

namespace EuclideanEmbedding

open Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem sphereParity_zero_of_homeomorph_sixSphere (h : M ≃ₜ Sphere 6)
    (f : C(Sphere 3, M)) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) : e.sphereParity a f hf hi hd = 0 := by
  let : CompactSpace M := compactSpace_of_homeomorph h
  obtain ⟨g, hg, hgi, hgd, hz⟩ := e.exists_zeroParitySphere a (h.symm (pole 6))
  have H := sphere_three_maps_homotopic_of_homeomorph_sixSphere h f g
  exact (e.sphereParity_homotopic a f g hf hg hi hgi hd hgd H).trans hz

end EuclideanEmbedding
end NoExoticSixSphere
