import Wikipedia.NoExoticSixSphere.SevenDimensionalSmoothOpenTube

/-!
# Actual open and compact radial regions in a smooth four-normal tube

The regions are images under the genuine partial diffeomorphism. Its
whole product source gives global smoothness, compact closed radial
regions, open radial regions, and exact membership tests using the
original smooth inverse. No exterior topology is asserted here.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)

def closedRegion (R : ℝ) : Set M := Φ '' (univ ×ˢ closedBall (0 : Vector 4) R)

def openRegion (R : ℝ) : Set M := Φ '' (univ ×ˢ ball (0 : Vector 4) R)

theorem contMDiff (hΦ : Φ.source = univ) : ContMDiff ((𝓡 3).prod (𝓡 4)) (𝓡 7) ∞ Φ := by
  have h := Φ.contMDiffOn_toFun
  rwa [hΦ, contMDiffOn_univ] at h

theorem isCompact_closedRegion (hΦ : Φ.source = univ) (R : ℝ) :
    IsCompact (closedRegion Φ R) :=
  (isCompact_univ.prod (isCompact_closedBall (0 : Vector 4) R)).image
    (contMDiff Φ hΦ).continuous

theorem isOpen_openRegion (hΦ : Φ.source = univ) (R : ℝ) : IsOpen (openRegion Φ R) :=
  (Φ.toOpenPartialHomeomorph.isOpenEmbedding hΦ).isOpenMap _
    (isOpen_univ.prod isOpen_ball)

theorem closedRegion_subset_target (hΦ : Φ.source = univ) (R : ℝ) :
    closedRegion Φ R ⊆ Φ.target := by
  rintro y ⟨p, -, rfl⟩
  exact Φ.toPartialEquiv.map_source (hΦ.symm ▸ mem_univ p)

theorem closedRegion_subset_openRegion {R r : ℝ} (hRr : R < r) :
    closedRegion Φ R ⊆ openRegion Φ r :=
  image_mono (prod_mono Subset.rfl (closedBall_subset_ball hRr))

theorem mem_closedRegion_iff (hΦ : Φ.source = univ) (R : ℝ) (y : M) :
    y ∈ closedRegion Φ R ↔ y ∈ Φ.target ∧ ‖(Φ.symm y).2‖ ≤ R := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hs : p ∈ Φ.source := hΦ.symm ▸ mem_univ p
    refine ⟨Φ.toPartialEquiv.map_source hs, ?_⟩
    exact (congrArg (fun q : Sphere 3 × Vector 4 ↦ ‖q.2‖)
      (Φ.toPartialEquiv.left_inv hs)).trans_le (mem_closedBall_zero_iff.mp hp.2)
  · rintro ⟨hy, hnorm⟩
    exact ⟨Φ.symm y, ⟨mem_univ _, mem_closedBall_zero_iff.mpr hnorm⟩,
      Φ.toPartialEquiv.right_inv hy⟩

theorem mem_openRegion_iff (hΦ : Φ.source = univ) (R : ℝ) (y : M) :
    y ∈ openRegion Φ R ↔ y ∈ Φ.target ∧ ‖(Φ.symm y).2‖ < R := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hs : p ∈ Φ.source := hΦ.symm ▸ mem_univ p
    refine ⟨Φ.toPartialEquiv.map_source hs, ?_⟩
    exact (congrArg (fun q : Sphere 3 × Vector 4 ↦ ‖q.2‖)
      (Φ.toPartialEquiv.left_inv hs)).trans_lt (mem_ball_zero_iff.mp hp.2)
  · rintro ⟨hy, hnorm⟩
    exact ⟨Φ.symm y, ⟨mem_univ _, mem_ball_zero_iff.mpr hnorm⟩,
      Φ.toPartialEquiv.right_inv hy⟩

def radiusSquared (y : M) : ℝ := ‖(Φ.symm y).2‖ ^ 2

theorem radiusSquared_apply (hΦ : Φ.source = univ) (p : Sphere 3 × Vector 4) :
    radiusSquared Φ (Φ p) = ‖p.2‖ ^ 2 := by
  exact congrArg (fun q : Sphere 3 × Vector 4 ↦ ‖q.2‖ ^ 2)
    (Φ.toPartialEquiv.left_inv (hΦ.symm ▸ mem_univ p))

theorem contMDiffOn_radiusSquared : ContMDiffOn (𝓡 7) 𝓘(ℝ, ℝ) ∞ (radiusSquared Φ) Φ.target := by
  have hs : ContDiff ℝ ∞ (fun v : Vector 4 ↦ ‖v‖ ^ 2) := contDiff_norm_sq ℝ
  intro y hy
  exact (hs.contMDiff.contMDiffAt.comp y
    ((Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hy)).snd)).contMDiffWithinAt

end NoExoticSixSphere.SphereFourTube
