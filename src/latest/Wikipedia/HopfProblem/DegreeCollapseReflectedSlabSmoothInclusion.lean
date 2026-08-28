import Wikipedia.HopfProblem.DegreeCollapseReflectedFiberNormalFraming
import Wikipedia.NoExoticSixSphere.FramedSlabData

/-!
# The original framed slab embeds smoothly into the native reflected double

The original slab atlas is retained. Its Euclidean inclusion and the actual
cylinder retraction prove smoothness into the independently constructed
double. Its original immersion proves injectivity of the native derivative.
The actual boundary is precisely the zero-time seam, with matching frames.
-/

noncomputable section

open Function Set Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere GLOrthonormalization

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

def originalSlabPoint (p : CylinderFiberSlab.slab d.map b 0 1) : Fiber d :=
  ⟨p.val.val, (map_original d p.property p.val.val.2).trans p.val.property⟩

theorem originalSlabPoint_ambient (p : CylinderFiberSlab.slab d.map b 0 1) :
    ambientInclusion d (originalSlabPoint d p) = d.slabEuclideanInclusion p := rfl

theorem originalSlabPoint_left (x : {x : Sphere m // d.leftMap x = b}) :
    originalSlabPoint d (d.leftEndpoint x).val =
      seamCollarPoint d 0 (zero_mem_seamCollarTimes d) x := rfl

theorem isClosedEmbedding_originalSlabPoint : IsClosedEmbedding (originalSlabPoint d) := by
  let : CompactSpace (CylinderFiberSlab.slab d.map b 0 1) :=
    CylinderFiberSlab.compactSpace d.map b 0 1
  have hc : Continuous (originalSlabPoint d) :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  apply hc.isClosedEmbedding
  intro p q he
  exact Subtype.ext (Subtype.ext (congrArg (fun z : Fiber d ↦ z.val) he))

theorem range_originalSlabPoint (hmiss : ∀ x, d.rightMap x ≠ b) :
    range (originalSlabPoint d) = {p : Fiber d | 0 ≤ p.val.1} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact q.property.1
  · intro hp
    refine ⟨(originalHalfHomeomorph d hmiss).symm ⟨p, hp⟩, ?_⟩
    exact congrArg Subtype.val ((originalHalfHomeomorph d hmiss).apply_symm_apply ⟨p, hp⟩)

variable (k : ℕ) (hd : m = n + k) (a : Sphere m) (A : d.FramedSlabData k hd a)

theorem contMDiff_originalSlabPoint : letI := A.atlas; letI := fiberAtlas d k hd;
    ContMDiff ((𝓡∂ 1).prod (𝓡 k)) (𝓡 (k + 1)) ∞ (originalSlabPoint d) := by
  let := A.atlas
  let := fiberAtlas d k hd
  let : Fact (Module.finrank ℝ (Vector (m + 1)) = m + 1) :=
    ⟨by simp [GLOrthonormalization.Vector]⟩
  apply (regularFiber_contMDiff_iff_ambient (map d) (contMDiff_map d) b (regular_map d)
    (k + 1) (CylinderFiberNormalFrame.dimension_eq hd) (originalSlabPoint d)).mpr
  change ContMDiff ((𝓡∂ 1).prod (𝓡 k)) ((𝓘(ℝ, ℝ)).prod (𝓡 m)) ∞
    (fun p : CylinderFiberSlab.slab d.map b 0 1 ↦ p.val.val)
  have he : (fun p : CylinderFiberSlab.slab d.map b 0 1 ↦
      CylinderLevelEquations.retract a (d.slabEuclideanInclusion p)) =
        (fun p ↦ p.val.val) :=
    funext (fun p ↦ CylinderLevelEquations.retract_inclusion a p.val.val)
  rw [← he]
  intro p
  have hn : (d.slabEuclideanInclusion p).snd ≠ 0 :=
    ne_zero_of_mem_unit_sphere p.val.val.2
  exact (CylinderLevelEquations.contMDiffAt_retract (m := m) a hn).comp p
    A.smooth_inclusion.contMDiffAt

theorem injective_mfderiv_originalSlabPoint (p : CylinderFiberSlab.slab d.map b 0 1) :
    letI := A.atlas; letI := fiberAtlas d k hd;
    Injective (mfderiv ((𝓡∂ 1).prod (𝓡 k)) (𝓡 (k + 1)) (originalSlabPoint d) p) := by
  let := A.atlas
  let := fiberAtlas d k hd
  have hcomp := mfderiv_comp p
    ((contMDiff_ambientInclusion d k hd).mdifferentiableAt (by simp))
    ((contMDiff_originalSlabPoint d k hd a A).mdifferentiableAt (by simp))
  intro u v he
  apply A.injective_differential p
  change (mfderiv ((𝓡∂ 1).prod (𝓡 k))
      𝓘(ℝ, WithLp 2 (ℝ × Vector (m + 1)))
      (ambientInclusion d ∘ originalSlabPoint d) p) u =
    (mfderiv ((𝓡∂ 1).prod (𝓡 k))
      𝓘(ℝ, WithLp 2 (ℝ × Vector (m + 1)))
      (ambientInclusion d ∘ originalSlabPoint d) p) v
  rw [hcomp]
  exact congrArg (ambientDifferential d k hd (originalSlabPoint d p)) he

theorem originalSlab_boundary_iff (hmiss : ∀ x, d.rightMap x ≠ b)
    (p : CylinderFiberSlab.slab d.map b 0 1) : letI := A.atlas;
    ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p ↔ (originalSlabPoint d p).val.1 = 0 := by
  let := A.atlas
  rw [A.boundary_iff p]
  constructor
  · rintro (hp | hp)
    · exact hp
    · exact (hmiss p.val.val.2 (d.rightMap_eq_value_of_time p hp)).elim
  · exact fun hp ↦ Or.inl hp

theorem normalFrame_originalSlab_boundary (x : {x : Sphere m // d.leftMap x = b}) :
    letI := A.atlas; letI := fiberAtlas d k hd;
    (normalFrame d k hd a).ambient (originalSlabPoint d (d.leftEndpoint x).val) =
      A.frame.ambient (d.leftEndpoint x).val := by
  let := A.atlas
  let := fiberAtlas d k hd
  rw [originalSlabPoint_left, normalFrame_seamCollar, A.frame_left]

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder
