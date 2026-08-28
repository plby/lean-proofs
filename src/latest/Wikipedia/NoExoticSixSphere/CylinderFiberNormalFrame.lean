import Wikipedia.NoExoticSixSphere.CylinderLevelEquations
import Wikipedia.NoExoticSixSphere.SphereFiberNormalFrame
import Wikipedia.NoExoticSixSphere.CylinderNormalFrame

/-!
# Normal framing of the full regular sphere-cylinder fiber

The original full regular-fiber atlas is retained. Centered target coordinates,
radial extension, and the spatial sphere equation give a smooth Euclidean
normal frame. Its codimension is the target dimension plus one.
-/

open scoped Manifold ContDiff Topology
open Module Function Set Filter

namespace NoExoticSixSphere.CylinderFiberNormalFrame

variable {m n : ℕ} (f : C(ℝ × Sphere m, Sphere n))
  (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (𝓡 n) ∞ f) (b : Sphere n)

local instance sourceDimension :
    Fact (finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) := ⟨finrank_euclideanSpace_fin⟩

noncomputable def equations (a : Sphere m) :
    WithLp 2 (ℝ × EuclideanSpace ℝ (Fin (m + 1))) →
      WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n)) :=
  CylinderLevelEquations.equations a
    (CenteredChartCoordinates.coordinates f (modelChartPartialDiffeomorph (I := 𝓡 n) b) b)

theorem equations_zero (a : Sphere m) (p : ℝ × Sphere m) (hp : f p = b) :
    equations f b a (CylinderLevelEquations.inclusion p) = 0 := by
  rw [equations, CylinderLevelEquations.equations_inclusion,
    CenteredChartCoordinates.coordinates_eq_zero f _ b hp]
  rfl

include hf in
theorem contDiffAt_equations (a : Sphere m) (p : ℝ × Sphere m) (hp : f p = b) :
    ContDiffAt ℝ ∞ (equations f b a) (CylinderLevelEquations.inclusion p) := by
  apply CylinderLevelEquations.contDiffAt_equations (m := m)
  apply CenteredChartCoordinates.contMDiffAt_coordinates f _ b (hf p)
  rw [hp]
  exact mem_extChartAt_source b

include hf in
theorem surjective_fderiv_equations (a : Sphere m) (p : ℝ × Sphere m) (hp : f p = b)
    (hreg : Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (𝓡 n) f p)) :
    Surjective (fderiv ℝ (equations f b a) (CylinderLevelEquations.inclusion p)) := by
  have hc : f p ∈ (modelChartPartialDiffeomorph (I := 𝓡 n) b).source := by
    rw [hp]
    exact mem_extChartAt_source b
  apply CylinderLevelEquations.surjective_fderiv_equations (m := m)
  · exact CenteredChartCoordinates.contMDiffAt_coordinates f _ b (hf p) hc
  · exact CenteredChartCoordinates.surjective_mfderiv_coordinates f _ b (hf p) hc hreg

noncomputable def ambientInclusion : {p : ℝ × Sphere m // f p = b} →
    WithLp 2 (ℝ × EuclideanSpace ℝ (Fin (m + 1))) :=
  fun p ↦ CylinderLevelEquations.inclusion p.val

theorem dimension_eq {k : ℕ} (hd : m = n + k) :
    finrank ℝ (ℝ × EuclideanSpace ℝ (Fin m)) =
      finrank ℝ (EuclideanSpace ℝ (Fin n)) + (k + 1) := by
  simp only [finrank_prod, finrank_self, finrank_euclideanSpace_fin]
  omega

variable (hreg : ∀ p, f p = b → Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (𝓡 n) f p))
  (k : ℕ) (hd : m = n + k)

theorem contMDiff_ambientInclusion :
    letI := regularFiberAtlas f hf b hreg (k + 1) (dimension_eq hd);
    ContMDiff (𝓡 (k + 1)) 𝓘(ℝ, WithLp 2 (ℝ × EuclideanSpace ℝ (Fin (m + 1)))) ∞
      (ambientInclusion f b) := by
  let := regularFiberAtlas f hf b hreg (k + 1) (dimension_eq hd)
  exact (CylinderLevelEquations.contMDiff_inclusion (m := m)).comp
    (regularFiber_contMDiff_subtype_val f hf b hreg (k + 1) (dimension_eq hd))

theorem injective_ambientDifferential (p : {p : ℝ × Sphere m // f p = b}) :
    letI := regularFiberAtlas f hf b hreg (k + 1) (dimension_eq hd);
    Injective (NormalFrameOfEquations.ambientDifferential (𝓡 (k + 1))
      (ambientInclusion f b) p) := by
  let := regularFiberAtlas f hf b hreg (k + 1) (dimension_eq hd)
  have hi := (regularFiber_contMDiff_subtype_val f hf b hreg (k + 1)
    (dimension_eq hd)).mdifferentiable (by simp) p
  have hj := (CylinderLevelEquations.contMDiff_inclusion (m := m)).mdifferentiable (by simp) p.val
  change Injective (mfderiv (𝓡 (k + 1))
    𝓘(ℝ, WithLp 2 (ℝ × EuclideanSpace ℝ (Fin (m + 1))))
    (CylinderLevelEquations.inclusion ∘
      (Subtype.val : {p : ℝ × Sphere m // f p = b} → ℝ × Sphere m)) p)
  rw [mfderiv_comp p hj hi]
  exact (CylinderLevelEquations.injective_inclusionDifferential (m := m) p.val).comp
    (regularFiber_injective_mfderiv_subtype_val f hf b hreg (k + 1) (dimension_eq hd) p)

noncomputable def normalFrame (a : Sphere m) :
    letI := regularFiberAtlas f hf b hreg (k + 1) (dimension_eq hd);
    SmoothRangeFrame (𝓡 (k + 1))
      (fun p : {p : ℝ × Sphere m // f p = b} ↦
        (NormalFrameOfEquations.ambientDifferential (𝓡 (k + 1))
          (ambientInclusion f b) p).rangeᗮ.starProjection)
      (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n))) := by
  let := regularFiberAtlas f hf b hreg (k + 1) (dimension_eq hd)
  apply NormalFrameOfEquations.inducedFrame
    (contMDiff_ambientInclusion f hf b hreg k hd)
    (fun p ↦ contDiffAt_equations f hf b a p.val p.property)
    (fun p ↦ equations_zero f b a p.val p.property)
    (fun p ↦ surjective_fderiv_equations f hf b a p.val p.property (hreg p.val p.property))
    (injective_ambientDifferential f hf b hreg k hd)
  rw [(WithLp.prodContinuousLinearEquiv 2 ℝ ℝ
    (EuclideanSpace ℝ (Fin (m + 1)))).toLinearEquiv.finrank_eq,
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ
    (EuclideanSpace ℝ (Fin n))).toLinearEquiv.finrank_eq]
  simp only [finrank_prod, finrank_self, finrank_euclideanSpace_fin]
  omega

theorem normalFrame_ambient (a : Sphere m) (p : {p : ℝ × Sphere m // f p = b}) :
    letI := regularFiberAtlas f hf b hreg (k + 1) (dimension_eq hd);
    (normalFrame f hf b hreg k hd a).ambient p =
      orthogonalRightInverse
        (fderiv ℝ (equations f b a) (CylinderLevelEquations.inclusion p.val)) := by
  let := regularFiberAtlas f hf b hreg (k + 1) (dimension_eq hd)
  apply ContinuousLinearMap.ext
  intro v
  rfl

end NoExoticSixSphere.CylinderFiberNormalFrame
