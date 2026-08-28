import Wikipedia.NoExoticSixSphere.DiskGraphEmbedding
import Wikipedia.NoExoticSixSphere.SphereNeighborhoodAnnulus
import Wikipedia.SmoothSixDPoincare.ImmersionLocalInjectivity

/-!
# Constructing an embedded disk from an embedded immersive boundary germ

Only the original map's behavior on the boundary and its avoidance on a
neighborhood of that boundary are required. Compactness supplies a uniform
collar on which it is injective and immersive. The supported graph then
embeds the rest of the disk without changing that collar.
-/

noncomputable section

open Set Function Metric Topology
open Wikipedia.SmoothSixDPoincare.ManifoldImmersion
open scoped Manifold ContDiff

namespace NoExoticSixSphere.DiskGraph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [HasContDiffBump E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [HasContDiffBump E] in
/-- A single radial collar inherits the original boundary embedding and immersion. -/
theorem exists_embedded_immersive_annulus {f : E → F} (hf : ContDiff ℝ ∞ f)
    (hi : InjOn f (sphere (0 : E) 1))
    (hd : ∀ x ∈ sphere (0 : E) 1, Injective (fderiv ℝ f x))
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      closedBall (0 : E) 1 ∩ {x | r ≤ ‖x‖} ⊆ U ∧
      InjOn f (closedBall (0 : E) 1 ∩ {x | r ≤ ‖x‖}) ∧
      ∀ x ∈ closedBall (0 : E) 1, r ≤ ‖x‖ → Injective (fderiv ℝ f x) := by
  have hmd : ∀ x ∈ sphere (0 : E) 1,
      Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x) := by
    intro x hx
    rw [mfderiv_eq_fderiv]
    exact hd x hx
  obtain ⟨V, hV, hSV, _, hVi, hVd⟩ :=
    exists_open_embedded_immersive_neighborhood isOpen_univ hf.contMDiff.contMDiffOn
      (isCompact_sphere (0 : E) 1) (subset_univ _) hi hmd
  obtain ⟨r, hr, hr1, hsub⟩ := exists_annulus_subset_sphere_neighborhood (hV.inter hU)
    (fun x hx ↦ ⟨hSV hx, hSU hx⟩)
  refine ⟨r, hr, hr1, fun x hx ↦ (hsub hx).2,
    hVi.mono (fun x hx ↦ (hsub hx).1), ?_⟩
  intro x hx hrx
  have h := hVd x (hsub ⟨hx, hrx⟩).1
  rw [mfderiv_eq_fderiv] at h
  exact h

/-- An explicit stabilized disk keeps an open neighborhood of the original sphere fixed. -/
theorem exists_embedding_rel_sphere_avoiding {f : E → F} (hf : ContDiff ℝ ∞ f)
    (hi : InjOn f (sphere (0 : E) 1))
    (hd : ∀ x ∈ sphere (0 : E) 1, Injective (fderiv ℝ f x))
    {U : Set E} (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    (S : Set F) (ha : ∀ x ∈ U ∩ ball (0 : E) 1, f x ∉ S) :
    ∃ G : E → F × (ℝ × E), ContDiff ℝ ∞ G ∧
      IsClosedEmbedding (fun x : closedBall (0 : E) 1 ↦ G x.val) ∧
      (∀ x ∈ closedBall (0 : E) 1, Injective (fderiv ℝ G x)) ∧
      (∀ x ∈ ball (0 : E) 1, G x ∉ S ×ˢ ({0} : Set (ℝ × E))) ∧
      ∃ V : Set E, IsOpen V ∧ sphere (0 : E) 1 ⊆ V ∧ V ⊆ U ∧
        ∀ x ∈ V, G x = (f x, 0) := by
  obtain ⟨r, hr, hr1, hsub, hfi, hfd⟩ :=
    exists_embedded_immersive_annulus hf hi hd hU hSU
  refine ⟨map f r hr, contDiff_iff_contDiffAt.mpr (fun x ↦
    contDiffAt_map f r hr hf.contDiffAt),
    isClosedEmbedding_disk f r hr (fun _ _ ↦ hf.contDiffAt) hfi, ?_, ?_, ?_⟩
  · intro x hx
    exact injective_fderiv_map f r hr hf.contDiffAt (hfd x hx)
  · apply avoids_oldAmbient f r hr S
    intro x hx hrx
    exact ha x ⟨hsub ⟨ball_subset_closedBall hx, hrx⟩, hx⟩
  · refine ⟨U ∩ {x | r < ‖x‖}, hU.inter (isOpen_lt continuous_const continuous_norm),
      ?_, inter_subset_left, ?_⟩
    · intro x hx
      refine ⟨hSU hx, ?_⟩
      have hn : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
      exact hr1.trans_eq hn.symm
    · intro x hx
      exact map_eq_on_collar f r hr hx.2.le

end NoExoticSixSphere.DiskGraph
