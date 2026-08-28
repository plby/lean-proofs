import Wikipedia.HopfProblem.DegreeCollapseSevenFramedAttachingProduct

/-!
# Localizing the full framed attaching face in an original open region

Shrinking the transverse radius preserves the literal product map, its full
normal frame, both collar identities, and whole-interior avoidance. Compactness
of the sphere lets the entire attaching face lie in any prescribed open
neighborhood of the original sphere. This is the support control needed to
keep a later surgery away from a retained boundary region.
-/

noncomputable section

open Set Metric Function Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : Sphere 3 → M}

namespace FramedAttachingProduct

def restrict (A : FramedAttachingProduct e a f) (ε : ℝ) (hε : 0 < ε)
    (hεA : ε ≤ A.radius) : FramedAttachingProduct e a f where
  disk := A.disk
  map := A.map
  map_core := A.map_core
  innerRadius := A.innerRadius
  innerRadius_pos := A.innerRadius_pos
  innerRadius_lt_one := A.innerRadius_lt_one
  radius := ε
  radius_pos := hε
  embedded := GeneralDiskThickening.restrict_closedProduct_embedding
    (fun p : closedBall (0 : Vector 4) 1 × Vector 4 ↦ A.map (p.1.val, p.2)) hεA A.embedded
  smooth := fun x hx v hv ↦ A.smooth x hx v ((closedBall_subset_closedBall hεA) hv)
  immersive := fun x hx v hv ↦ A.immersive x hx v ((closedBall_subset_closedBall hεA) hv)
  tube := A.tube
  tube_core := A.tube_core
  tube_embedded := GeneralDiskThickening.restrict_closedProduct_embedding A.tube hεA A.tube_embedded
  tube_localDiffeomorph := fun s v hv ↦
    A.tube_localDiffeomorph s v ((closedBall_subset_closedBall hεA) hv)
  collar_map := fun x hx hxr v hv ↦ A.collar_map x hx hxr v ((closedBall_subset_closedBall hεA) hv)
  interior_avoids := fun x hx v hv ↦ A.interior_avoids x hx v ((closedBall_subset_closedBall hεA) hv)
  normalFrame := A.normalFrame
  normalFrame_smooth := fun x hx v hv ↦
    A.normalFrame_smooth x hx v ((closedBall_subset_closedBall hεA) hv)
  normalFrame_norm := fun x hx v hv ↦
    A.normalFrame_norm x hx v ((closedBall_subset_closedBall hεA) hv)
  normalFrame_range := fun x hx v hv ↦
    A.normalFrame_range x hx v ((closedBall_subset_closedBall hεA) hv)
  collar_frame := fun x hx hxr v hv ↦
    A.collar_frame x hx hxr v ((closedBall_subset_closedBall hεA) hv)

theorem exists_tube_radius_in_open (A : FramedAttachingProduct e a f)
    {O : Set M} (hO : IsOpen O) (hfO : ∀ s, f s ∈ O) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ A.radius ∧
      ∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector 4) ε, A.tube (s, v) ∈ O := by
  let U := interior (A.tube ⁻¹' O)
  have hcore (s : Sphere 3) : (s, (0 : Vector 4)) ∈ U := by
    apply mem_interior_iff_mem_nhds.mpr
    have hs := (A.tube_localDiffeomorph s 0 (mem_closedBall_self A.radius_pos.le)).contMDiffAt
    have hmem : A.tube (s, 0) ∈ O := by rw [A.tube_core]; exact hfO s
    exact hs.continuousAt (hO.mem_nhds hmem)
  obtain ⟨δ, hδ, hδU⟩ := exists_uniform_closedProductTube isOpen_interior hcore
  refine ⟨min δ A.radius, lt_min hδ A.radius_pos, min_le_right _ _, ?_⟩
  intro s v hv
  apply interior_subset (hδU s v ?_)
  have hvδ := (closedBall_subset_closedBall (min_le_left δ A.radius)) hv
  simpa only [mem_closedBall, dist_zero_right] using hvδ

end FramedAttachingProduct

variable [T2Space M] [IsManifold (𝓡 7) ∞ M]

theorem exists_localized_framedAttachingProduct
    (e : EuclideanEmbedding 7 M)
    (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
    (R : EuclideanEmbedding.TubularRetraction e) (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s))
    {O : Set M} (hO : IsOpen O) (hfO : ∀ s, f s ∈ O) :
    ∃ A : FramedAttachingProduct e a f,
      ∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector 4) A.radius, A.tube (s, v) ∈ O := by
  obtain ⟨A⟩ := nonempty_framedAttachingProduct e a R f hf hi hd
  obtain ⟨ε, hε, hεA, hεO⟩ := A.exists_tube_radius_in_open hO hfO
  exact ⟨A.restrict ε hε hεA, hεO⟩

theorem exists_localized_framedAttachingProduct_of_compact [CompactSpace M]
    (e : EuclideanEmbedding 7 M)
    (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel) (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s))
    {O : Set M} (hO : IsOpen O) (hfO : ∀ s, f s ∈ O) :
    ∃ A : FramedAttachingProduct e a f,
      ∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector 4) A.radius, A.tube (s, v) ∈ O := by
  obtain ⟨A⟩ := nonempty_framedAttachingProduct_of_compact e a f hf hi hd
  obtain ⟨ε, hε, hεA, hεO⟩ := A.exists_tube_radius_in_open hO hfO
  exact ⟨A.restrict ε hε hεA, hεO⟩

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
