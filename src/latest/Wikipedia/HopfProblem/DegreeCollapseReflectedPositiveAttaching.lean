import Wikipedia.HopfProblem.DegreeCollapseReflectedSeamDiffeomorph
import Wikipedia.HopfProblem.DegreeCollapseSevenAttachingLocalization
import Wikipedia.HopfProblem.DegreeCollapseSevenNormalizedFramedAttachingProduct

/-!
# Seven-dimensional surgery attachments stay uniformly away from the seam

Apply the compact closed-manifold construction to the actual reflected
double. A supplied embedded three-sphere in its positive half gets a full
normalized framed attaching product in that half. Compactness of the whole
closed attaching face gives a strictly positive time margin.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere GLOrthonormalization SevenSurgery

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

def time (p : Fiber d) : ℝ := p.val.1

theorem continuous_time : Continuous (time d) :=
  continuous_fst.comp continuous_subtype_val

theorem contMDiff_time (k : ℕ) (hd : m = n + k) : letI := fiberAtlas d k hd;
    ContMDiff (𝓡 (k + 1)) 𝓘(ℝ, ℝ) ∞ (time d) := by
  let := fiberAtlas d k hd
  exact contMDiff_fst.comp (regularFiber_contMDiff_subtype_val (map d) (contMDiff_map d) b
    (regular_map d) (k + 1) (CylinderFiberNormalFrame.dimension_eq hd))

variable (hmiss : ∀ x, d.rightMap x ≠ b) (hd : m = n + 6) (a : Sphere m)

theorem exists_positive_normalized_attaching : letI := fiberAtlas d 6 hd;
    ∀ (f : C(Sphere 3, Fiber d)), ContMDiff (𝓡 3) (𝓡 7) ∞ f → Injective f →
      (∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s)) → (∀ s, 0 < time d (f s)) →
      ∃ A : FramedAttachingProduct (embedding d hmiss 6 hd)
          (euclideanNormalFraming d hmiss 6 hd a) f,
        A.radius = 2 ∧ ∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector 4) 2,
          0 < time d (A.tube (s, v)) := by
  let := fiberAtlas d 6 hd
  let := fiber_isManifold d 6 hd
  let := compactSpace_fiber d hmiss
  intro f hf hi hdf hp
  obtain ⟨A, hA⟩ := exists_localized_framedAttachingProduct_of_compact
    (embedding d hmiss 6 hd) (euclideanNormalFraming d hmiss 6 hd a) f hf hi hdf
    (isOpen_lt continuous_const (continuous_time d)) hp
  refine ⟨A.normalizedRadius, rfl, ?_⟩
  intro s v hv
  exact hA s (A.transverseRadiusCoordinates v) (A.transverseRadiusCoordinates_mem hv)

theorem positive_attaching_time_margin : letI := fiberAtlas d 6 hd;
    ∀ {f : Sphere 3 → Fiber d}
      (A : FramedAttachingProduct (embedding d hmiss 6 hd)
        (euclideanNormalFraming d hmiss 6 hd a) f),
      (∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector 4) A.radius,
        0 < time d (A.tube (s, v))) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector 4) A.radius,
        δ ≤ time d (A.tube (s, v)) := by
  let := fiberAtlas d 6 hd
  intro f A hA
  have hc : Continuous (fun p : Sphere 3 × closedBall (0 : Vector 4) A.radius ↦
      time d (A.tube (p.1, p.2.val))) :=
    (continuous_time d).comp A.tube_embedded.continuous
  obtain ⟨δ, hδ, hδA⟩ := isCompact_univ.exists_forall_le' hc.continuousOn
    (fun p _ ↦ hA p.1 p.2.val p.2.property)
  exact ⟨δ, hδ, fun s v hv ↦ hδA (s, ⟨v, hv⟩) (mem_univ _)⟩

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder
