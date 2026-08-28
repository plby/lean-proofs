import Wikipedia.NoExoticSixSphere.CollaredSlabImmersion
import Wikipedia.NoExoticSixSphere.CollaredSlabEndpoints
import Wikipedia.NoExoticSixSphere.CylinderFrameCollar

/-!
# A smooth normal frame on the actual bounded sphere-cylinder fiber slab

The frame is constructed in the slab's global boundary atlas using its
proved immersion and the regular ambient cylinder equations. Its ambient
formula equals the full-fiber frame, and at each endpoint it is exactly the
endpoint sphere-fiber frame with zero time component.
-/

open scoped Manifold ContDiff
open Module Function

namespace NoExoticSixSphere.RegularCollaredCylinder

variable {m n : ℕ} {b : Sphere n} {s t : ℝ}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b s t)
  (k : ℕ) (hd : m = n + k)
  (Φ : PartialDiffeomorph (𝓡 (k + 1)) ((𝓡∂ 1).prod (𝓡 k))
    (EuclideanSpace ℝ (Fin (k + 1)))
    (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin k))) ∞)
  (hsource : Φ.source = Set.univ)

local instance sourceDimension :
    Fact (finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) := ⟨finrank_euclideanSpace_fin⟩

noncomputable def slabEuclideanInclusion : CylinderFiberSlab.slab d.map b s t →
    WithLp 2 (ℝ × EuclideanSpace ℝ (Fin (m + 1))) :=
  fun p ↦ CylinderLevelEquations.inclusion p.val.val

theorem contMDiff_slabEuclideanInclusion :
    letI := (d.openCover k (by simpa using hd) Φ hsource).chartedSpace;
    ContMDiff ((𝓡∂ 1).prod (𝓡 k))
      𝓘(ℝ, WithLp 2 (ℝ × EuclideanSpace ℝ (Fin (m + 1)))) ∞ d.slabEuclideanInclusion := by
  let := (d.openCover k (by simpa using hd) Φ hsource).chartedSpace
  exact (CylinderLevelEquations.contMDiff_inclusion (m := m)).comp
    (d.slab_contMDiff_ambient k (by simpa using hd) Φ hsource)

theorem injective_slabEuclideanDifferential (p : CylinderFiberSlab.slab d.map b s t) :
    letI := (d.openCover k (by simpa using hd) Φ hsource).chartedSpace;
    Injective (NormalFrameOfEquations.ambientDifferential ((𝓡∂ 1).prod (𝓡 k))
      d.slabEuclideanInclusion p) := by
  let := (d.openCover k (by simpa using hd) Φ hsource).chartedSpace
  have hi := (d.slab_contMDiff_ambient k (by simpa using hd) Φ hsource).mdifferentiable (by simp) p
  have hj := (CylinderLevelEquations.contMDiff_inclusion (m := m)).mdifferentiable
    (by simp) p.val.val
  change Injective (mfderiv ((𝓡∂ 1).prod (𝓡 k))
    𝓘(ℝ, WithLp 2 (ℝ × EuclideanSpace ℝ (Fin (m + 1))))
    (CylinderLevelEquations.inclusion ∘
      (fun q : CylinderFiberSlab.slab d.map b s t ↦ q.val.val)) p)
  rw [mfderiv_comp p hj hi]
  exact (CylinderLevelEquations.injective_inclusionDifferential (m := m) p.val.val).comp
    (d.slab_injective_mfderiv_ambient k (by simpa using hd) Φ hsource p)

noncomputable def slabNormalFrame (a : Sphere m) :
    letI := (d.openCover k (by simpa using hd) Φ hsource).chartedSpace;
    SmoothRangeFrame ((𝓡∂ 1).prod (𝓡 k))
      (fun p : CylinderFiberSlab.slab d.map b s t ↦
        (NormalFrameOfEquations.ambientDifferential ((𝓡∂ 1).prod (𝓡 k))
          d.slabEuclideanInclusion p).rangeᗮ.starProjection)
      (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n))) := by
  let := (d.openCover k (by simpa using hd) Φ hsource).chartedSpace
  apply NormalFrameOfEquations.inducedFrame
    (d.contMDiff_slabEuclideanInclusion k hd Φ hsource)
    (fun p ↦ CylinderFiberNormalFrame.contDiffAt_equations d.map d.smooth_map b a
      p.val.val p.val.property)
    (fun p ↦ CylinderFiberNormalFrame.equations_zero d.map b a p.val.val p.val.property)
    (fun p ↦ CylinderFiberNormalFrame.surjective_fderiv_equations d.map d.smooth_map b a
      p.val.val p.val.property (d.regular_map p.val.val p.val.property))
    (d.injective_slabEuclideanDifferential k hd Φ hsource)
  rw [(WithLp.prodContinuousLinearEquiv 2 ℝ ℝ
    (EuclideanSpace ℝ (Fin (m + 1)))).toLinearEquiv.finrank_eq,
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ
    (EuclideanSpace ℝ (Fin n))).toLinearEquiv.finrank_eq]
  simp only [finrank_prod, finrank_self, finrank_euclideanSpace_fin]
  omega

theorem slabNormalFrame_ambient (a : Sphere m) (p : CylinderFiberSlab.slab d.map b s t) :
    letI := (d.openCover k (by simpa using hd) Φ hsource).chartedSpace;
    (d.slabNormalFrame k hd Φ hsource a).ambient p =
      orthogonalRightInverse (fderiv ℝ (CylinderFiberNormalFrame.equations d.map b a)
        (CylinderLevelEquations.inclusion p.val.val)) := by
  let := (d.openCover k (by simpa using hd) Φ hsource).chartedSpace
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem slabNormalFrame_ambient_eq_full (a : Sphere m)
    (p : CylinderFiberSlab.slab d.map b s t) :
    letI := (d.openCover k (by simpa using hd) Φ hsource).chartedSpace;
    letI := regularFiberAtlas d.map d.smooth_map b d.regular_map (k + 1)
      (CylinderFiberNormalFrame.dimension_eq hd);
    (d.slabNormalFrame k hd Φ hsource a).ambient p =
      (CylinderFiberNormalFrame.normalFrame d.map d.smooth_map b
        d.regular_map k hd a).ambient p.val := by
  let := (d.openCover k (by simpa using hd) Φ hsource).chartedSpace
  let := regularFiberAtlas d.map d.smooth_map b d.regular_map (k + 1)
    (CylinderFiberNormalFrame.dimension_eq hd)
  rw [d.slabNormalFrame_ambient, CylinderFiberNormalFrame.normalFrame_ambient]

theorem slabNormalFrame_left (a : Sphere m) (x : {x : Sphere m // d.leftMap x = b}) :
    letI := (d.openCover k (by simpa using hd) Φ hsource).chartedSpace;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    (d.slabNormalFrame k hd Φ hsource a).ambient (d.leftEndpoint x).val =
      CylinderNormalFrame.liftFrame
        ((SphereFiberNormalFrame.normalFrame d.leftMap d.smooth_left b
          d.regular_left k hd a).ambient x) := by
  let := (d.openCover k (by simpa using hd) Φ hsource).chartedSpace
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  rw [d.slabNormalFrame_ambient]
  have h := CylinderFiberNormalFrame.normalFrame_ambient_on_collar d.map d.leftMap b a d.left_eq
    d.smooth_map d.smooth_left d.regular_map d.regular_left k hd d.leftTimes.isOpen s d.left_mem x
  rw [CylinderFiberNormalFrame.normalFrame_ambient] at h
  exact h

theorem slabNormalFrame_right (a : Sphere m) (x : {x : Sphere m // d.rightMap x = b}) :
    letI := (d.openCover k (by simpa using hd) Φ hsource).chartedSpace;
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd);
    (d.slabNormalFrame k hd Φ hsource a).ambient (d.rightEndpoint x).val =
      CylinderNormalFrame.liftFrame
        ((SphereFiberNormalFrame.normalFrame d.rightMap d.smooth_right b
          d.regular_right k hd a).ambient x) := by
  let := (d.openCover k (by simpa using hd) Φ hsource).chartedSpace
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  rw [d.slabNormalFrame_ambient]
  have h := CylinderFiberNormalFrame.normalFrame_ambient_on_collar d.map d.rightMap b a d.right_eq
    d.smooth_map d.smooth_right d.regular_map d.regular_right k hd
    d.rightTimes.isOpen t d.right_mem x
  rw [CylinderFiberNormalFrame.normalFrame_ambient] at h
  exact h

end NoExoticSixSphere.RegularCollaredCylinder
