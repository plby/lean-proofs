import Wikipedia.HopfProblem.DegreeCollapseReflectedCylinderCompactFiber
import Wikipedia.NoExoticSixSphere.CylinderFiberNormalFrame
import Wikipedia.NoExoticSixSphere.EuclideanTailSplitting

/-!
# The reflected fiber has its native smooth atlas and full normal frame

Apply the regular-fiber construction to the actual smooth reflected map.
The Euclidean cylinder inclusion is smooth and immersive in this atlas.
When the right endpoint misses the value, it is a closed embedding of a
compact manifold. No atlas is transferred from the original half.
-/

noncomputable section

open Function Set Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere GLOrthonormalization

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

abbrev Fiber := {p : ℝ × Sphere m // map d p = b}

@[instance_reducible]
def fiberAtlas (k : ℕ) (hd : m = n + k) : ChartedSpace (Vector (k + 1)) (Fiber d) :=
  regularFiberAtlas (map d) (contMDiff_map d) b (regular_map d) (k + 1)
    (CylinderFiberNormalFrame.dimension_eq hd)

theorem fiber_isManifold (k : ℕ) (hd : m = n + k) : letI := fiberAtlas d k hd;
    IsManifold (𝓡 (k + 1)) ∞ (Fiber d) :=
  regularFiber_isManifold (map d) (contMDiff_map d) b (regular_map d) (k + 1)
    (CylinderFiberNormalFrame.dimension_eq hd)

def ambientInclusion : Fiber d → WithLp 2 (ℝ × Vector (m + 1)) :=
  CylinderFiberNormalFrame.ambientInclusion (map d) b

theorem ambientInclusion_apply (p : Fiber d) :
    ambientInclusion d p = WithLp.toLp 2 (p.val.1, p.val.2.val) := rfl

theorem contMDiff_ambientInclusion (k : ℕ) (hd : m = n + k) :
    letI := fiberAtlas d k hd;
    ContMDiff (𝓡 (k + 1)) 𝓘(ℝ, WithLp 2 (ℝ × Vector (m + 1))) ∞
      (ambientInclusion d) :=
  CylinderFiberNormalFrame.contMDiff_ambientInclusion (map d) (contMDiff_map d) b
    (regular_map d) k hd

theorem injective_ambientInclusion : Injective (ambientInclusion d) := by
  intro p q he
  apply Subtype.ext
  change CylinderLevelEquations.inclusion p.val = CylinderLevelEquations.inclusion q.val at he
  simpa only [CylinderLevelEquations.retract_inclusion] using
    congrArg (CylinderLevelEquations.retract p.val.2) he

theorem isClosedEmbedding_ambientInclusion (hmiss : ∀ x, d.rightMap x ≠ b) :
    IsClosedEmbedding (ambientInclusion d) := by
  let : CompactSpace (Fiber d) := compactSpace_fiber d hmiss
  have hc : Continuous (ambientInclusion d) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (Vector (m + 1))).symm.continuous.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)))
  exact hc.isClosedEmbedding (injective_ambientInclusion d)

def ambientDifferential (k : ℕ) (hd : m = n + k) (p : Fiber d) :
    Vector (k + 1) →L[ℝ] WithLp 2 (ℝ × Vector (m + 1)) :=
  letI := fiberAtlas d k hd
  NormalFrameOfEquations.ambientDifferential (𝓡 (k + 1)) (ambientInclusion d) p

theorem injective_ambientDifferential (k : ℕ) (hd : m = n + k) (p : Fiber d) :
    Injective (ambientDifferential d k hd p) :=
  CylinderFiberNormalFrame.injective_ambientDifferential (map d) (contMDiff_map d) b
    (regular_map d) k hd p

def normalFrame (k : ℕ) (hd : m = n + k) (a : Sphere m) :
    letI := fiberAtlas d k hd;
    SmoothRangeFrame (𝓡 (k + 1))
      (fun p : Fiber d ↦ (ambientDifferential d k hd p).rangeᗮ.starProjection)
      (WithLp 2 (ℝ × Vector n)) :=
  CylinderFiberNormalFrame.normalFrame (map d) (contMDiff_map d) b (regular_map d) k hd a

theorem normalFrame_range (k : ℕ) (hd : m = n + k) (a : Sphere m) (p : Fiber d) :
    letI := fiberAtlas d k hd;
    ((normalFrame d k hd a).ambient p).range = (ambientDifferential d k hd p).rangeᗮ := by
  let := fiberAtlas d k hd
  let F := normalFrame d k hd a
  have hr : (F.ambient p).range = (ambientDifferential d k hd p).rangeᗮ.starProjection.range := by
    ext y
    constructor
    · rintro ⟨v, rfl⟩
      exact (F.equiv p v).property
    · intro hy
      obtain ⟨v, hv⟩ := (F.equiv p).surjective ⟨y, hy⟩
      exact ⟨v, congrArg Subtype.val hv⟩
  exact hr.trans (Submodule.range_starProjection _)

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder
