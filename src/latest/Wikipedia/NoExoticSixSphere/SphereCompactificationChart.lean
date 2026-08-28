import Wikipedia.NoExoticSixSphere.Definitions
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Smooth finite charts for the one-point compactification sphere

Use an actual stereographic chart from the sphere's existing atlas. Its inverse
extends to a homeomorphism from the one-point compactification, so the finite
part has a specified smooth inverse as well as a topological identification.
-/

open scoped Manifold ContDiff
open Set Topology ChartedSpace IsManifold

namespace NoExoticSixSphere

local instance (n : ℕ) : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

noncomputable def spherePole (n : ℕ) : Sphere n :=
  ⟨EuclideanSpace.single (0 : Fin (n + 1)) 1, by simp⟩

noncomputable def sphereProjection (n : ℕ) :
    OpenPartialHomeomorph (Sphere n) (EuclideanSpace ℝ (Fin n)) :=
  stereographic' n (spherePole n)

theorem sphereProjection_source (n : ℕ) : (sphereProjection n).source = {spherePole n}ᶜ :=
  stereographic'_source _

theorem sphereProjection_target (n : ℕ) : (sphereProjection n).target = univ :=
  stereographic'_target _

theorem sphereProjection_mem_maximalAtlas (n : ℕ) :
    sphereProjection n ∈ maximalAtlas (𝓡 n) ∞ (Sphere n) := by
  apply subset_maximalAtlas
  exact ⟨spherePole n, rfl⟩

noncomputable def sphereProjectionDiffeomorph (n : ℕ) :
    PartialDiffeomorph (𝓡 n) (𝓡 n) (Sphere n) (EuclideanSpace ℝ (Fin n)) ∞ where
  toPartialEquiv := (sphereProjection n).toPartialEquiv
  open_source := (sphereProjection n).open_source
  open_target := (sphereProjection n).open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas (sphereProjection_mem_maximalAtlas n)
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas (sphereProjection_mem_maximalAtlas n)

theorem range_sphereProjection_symm (n : ℕ) :
    range (sphereProjection n).symm = {spherePole n}ᶜ := by
  rw [← sphereProjection_source]
  apply Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact (sphereProjection n).map_target (by rw [sphereProjection_target]; trivial)
  · intro y hy
    exact ⟨sphereProjection n y, (sphereProjection n).left_inv hy⟩

noncomputable def euclideanOnePointSphere (n : ℕ) :
    OnePoint (EuclideanSpace ℝ (Fin n)) ≃ₜ Sphere n :=
  OnePoint.equivOfIsEmbeddingOfRangeEq (spherePole n) (sphereProjection n).symm
    ((sphereProjection n).symm.isOpenEmbedding (sphereProjection_target n)).isEmbedding
    (range_sphereProjection_symm n)

theorem euclideanOnePointSphere_coe (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    euclideanOnePointSphere n (x : OnePoint _) = (sphereProjection n).symm x :=
  OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe _ _ _ _ _

theorem euclideanOnePointSphere_infty (n : ℕ) :
    euclideanOnePointSphere n OnePoint.infty = spherePole n :=
  OnePoint.equivOfIsEmbeddingOfRangeEq_apply_infty _ _ _ _

theorem contMDiff_euclideanOnePointSphere_coe (n : ℕ) :
    ContMDiff (𝓡 n) (𝓡 n) ∞
      (fun x : EuclideanSpace ℝ (Fin n) ↦ euclideanOnePointSphere n (x : OnePoint _)) := by
  have h := (sphereProjectionDiffeomorph n).contMDiffOn_invFun
  change ContMDiffOn (𝓡 n) (𝓡 n) ∞ (sphereProjection n).symm (sphereProjection n).target at h
  rw [sphereProjection_target, contMDiffOn_univ] at h
  simpa only [euclideanOnePointSphere_coe] using h

theorem euclideanOnePointSphere_symm_of_ne (n : ℕ) {y : Sphere n} (hy : y ≠ spherePole n) :
    (euclideanOnePointSphere n).symm y = (↑(sphereProjection n y) : OnePoint _) := by
  apply (euclideanOnePointSphere n).injective
  rw [Homeomorph.apply_symm_apply, euclideanOnePointSphere_coe]
  exact ((sphereProjection n).left_inv (by simpa only [sphereProjection_source,
    mem_compl_iff, mem_singleton_iff] using hy)).symm

end NoExoticSixSphere
