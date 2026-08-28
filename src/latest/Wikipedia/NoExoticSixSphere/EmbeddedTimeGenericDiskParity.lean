import Wikipedia.NoExoticSixSphere.EmbeddedTimeBoundaryParity
import Wikipedia.NoExoticSixSphere.DiskDoublePointParity

/-!
# Proper generic disks give zero parity for the actual induced time-zero frame

The original punctured-disk operator extends when its native singular
count is even. The checked boundary criterion identifies its extension
obstruction with the actual induced outward-frame sphere parity. For a
proper generic disk the compact double-point curve proves the even count.
No existence of such a disk for every boundary-kernel class is asserted.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EmbeddedTime

open GLOrthonormalization Stiefel DiskBoundary

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector (6 + 1)) M]
  [IsManifold (𝓡 (6 + 1)) ∞ M] (e : EuclideanEmbedding (6 + 1) M)
  (r : e.TubularRetraction) (t : C(M, ℝ))
  (ht : ContMDiff (𝓡 (6 + 1)) 𝓘(ℝ, ℝ) ∞ t)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 (6 + 1)) 𝓘(ℝ, ℝ) t x))
  (a : SmoothRangeFrame (𝓡 (6 + 1)) e.normalProjection e.NormalModel) (m : M)

theorem sphereParity_zero_of_even_generic_disk
    (f : C(Sphere 3, {x : M // t x = 0})) (g : Vector 4 → M)
    (hg : ∀ x ∈ closedBall (0 : Vector 4) 1, ContMDiffAt (𝓡 4) (𝓡 (6 + 1)) ∞ g x)
    (hb : ∀ s : Sphere 3, g s.val = (f s).val)
    (P : GenericFourDisk.ParityBallSystem g)
    (heven : Even (DiskDoublePoints.singularSet g).ncard)
    (hheight : ∀ s : Sphere 3, fderiv ℝ (t ∘ g) s.val s.val < 0) :
    letI := zeroAtlas t ht hreg;
    ∀ (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
      (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)),
      (zeroEmbedding e t ht hreg).sphereParity (zeroNormalFrame e r t ht hreg a m)
        f hf hi hd = 0 := by
  let := zeroAtlas t ht hreg
  intro hf hi hd
  apply (sphereParity_zero_iff_diskOperator_extends e r t ht hreg a m f g hg hb
    ((e.puncturedFourDiskOperatorMap a g hg P).comp P.outerBoundary)
    (fun _ ↦ rfl) hheight hf hi hd).mpr
  exact e.fourDiskOuterOperator_extends a g hg P heven

theorem sphereParity_zero_of_proper_generic_disk
    (f : C(Sphere 3, {x : M // t x = 0})) (g : Vector 4 → M)
    (hg : ∀ x ∈ closedBall (0 : Vector 4) 1, ContMDiffAt (𝓡 4) (𝓡 (6 + 1)) ∞ g x)
    (hb : ∀ s : Sphere 3, g s.val = (f s).val)
    (ρ : ℝ) (hρ1 : ρ < 1)
    (himmersive : ∀ x ∈ closedBall 0 1, ρ ≤ ‖x‖ →
      Injective (fderiv ℝ (e.toFun ∘ g) x))
    (C : Set (PartialDiffeomorph (𝓡 7) (𝓡 7) M (Vector 7) ∞))
    (hC : ∀ y : M, ∃ c ∈ C, y ∈ c.source)
    (hgen : ∀ c ∈ C, OperatorRank.RegularFourSevenOn
      (fun x ↦ fderiv ℝ (c ∘ g) x) {x | ‖x‖ < ρ ∧ g x ∈ c.source})
    (hinside : closure (DiskDoublePoints.points g) ⊆ ball 0 1 ×ˢ ball 0 1)
    (hdouble : CompactRetractionAffineFamily.RegularDoublePointsOn
      g (ball 0 1) (ball 0 1) C)
    (hheight : ∀ s : Sphere 3, fderiv ℝ (t ∘ g) s.val s.val < 0) :
    letI := zeroAtlas t ht hreg;
    ∀ (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
      (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)),
      (zeroEmbedding e t ht hreg).sphereParity (zeroNormalFrame e r t ht hreg a m)
        f hf hi hd = 0 := by
  let := zeroAtlas t ht hreg
  intro hf hi hd
  obtain ⟨P⟩ := GenericFourDisk.exists_parityBallSystem e g hg ρ hρ1 himmersive C hC hgen
  have heven := (DiskDoublePoints.finite_even_singularSet e g hg ρ hρ1 himmersive
    C hC hgen hinside hdouble).2
  exact sphereParity_zero_of_even_generic_disk e r t ht hreg a m f g hg hb P heven
    hheight hf hi hd

end NoExoticSixSphere.EmbeddedTime
