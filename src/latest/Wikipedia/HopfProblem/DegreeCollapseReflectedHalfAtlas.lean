import Wikipedia.HopfProblem.DegreeCollapseReflectedPositiveAttaching
import Wikipedia.NoExoticSixSphere.SuperlevelNormalForm
import Wikipedia.NoExoticSixSphere.SuperlevelDifferential
import Wikipedia.NoExoticSixSphere.SuperlevelBoundary

/-!
# A native half-space atlas on the nonnegative reflected half

The actual time function is regular at the seam: a smooth local time curve
is its right inverse. The superlevel construction therefore gives a genuine
manifold with boundary, whose boundary is exactly time zero. This does not
infer smoothness of an inverse from the old slab's homeomorphism.
-/

noncomputable section

open Function Set Filter Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere GLOrthonormalization

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (k : ℕ) (hd : m = n + k)

theorem regular_time_zero (p : Fiber d) (hp : time d p = 0) :
    letI := fiberAtlas d k hd;
    Surjective (mfderiv (𝓡 (k + 1)) 𝓘(ℝ, ℝ) (time d) p) := by
  classical
  let := fiberAtlas d k hd
  have hp0 : p.val.1 = 0 := hp
  have ht : p.val.1 ∈ seamCollarTimes d := hp0 ▸ zero_mem_seamCollarTimes d
  let x : EndpointFiber d :=
    ⟨p.val.2, (map_on_seamCollar d p.val.1 ht p.val.2).symm.trans p.property⟩
  let c : ℝ → Fiber d := fun t ↦ if ht : t ∈ seamCollarTimes d then
    seamCollarPoint d t ht x else p
  have hc0 : c 0 = p := by
    apply Subtype.ext
    simp only [c, dif_pos (zero_mem_seamCollarTimes d)]
    exact Prod.ext hp0.symm rfl
  have hg : (fun t ↦ (c t).val) =ᶠ[𝓝 (0 : ℝ)] (fun t ↦ (t, x.val)) := by
    filter_upwards [(seamCollarTimes d).isOpen.mem_nhds (zero_mem_seamCollarTimes d)] with t ht
    exact congrArg (fun z : Fiber d ↦ z.val)
      (show c t = seamCollarPoint d t ht x from dif_pos ht)
  have hc : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 (k + 1)) ∞ c 0 := by
    apply (regularFiber_contMDiffAt_iff_ambient (map d) (contMDiff_map d) b (regular_map d)
      (k + 1) (CylinderFiberNormalFrame.dimension_eq hd) c 0).mpr
    exact (contMDiffAt_id.prodMk contMDiffAt_const).congr_of_eventuallyEq hg
  have he : time d ∘ c =ᶠ[𝓝 (0 : ℝ)] id := hg.mono (fun _ h ↦ congrArg Prod.fst h)
  have hcomp := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 (k + 1)) (I'' := 𝓘(ℝ, ℝ)) 0
    ((contMDiff_time d k hd).mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))
  have hder : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (time d ∘ c) 0 =
      ContinuousLinearMap.id ℝ ℝ := he.mfderiv_eq.trans mfderiv_id
  intro y
  refine ⟨mfderiv 𝓘(ℝ, ℝ) (𝓡 (k + 1)) c 0 y, ?_⟩
  have hy := congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L y) (hcomp.symm.trans hder)
  change mfderiv (𝓡 (k + 1)) 𝓘(ℝ, ℝ) (time d) (c 0)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 (k + 1)) c 0 y) = y at hy
  exact hc0 ▸ hy

def halfAtlas : letI := fiberAtlas d k hd;
    SuperlevelAtlas (K := Vector k) (𝓡 (k + 1)) (time d) := by
  let := fiberAtlas d k hd
  let := fiber_isManifold d k hd
  exact Classical.choice (nonempty_superlevelAtlas (contMDiff_time d k hd)
    (regular_time_zero d k hd) k (by simp [Nat.add_comm]))

@[instance_reducible]
def halfChartedSpace : letI := fiberAtlas d k hd;
    ChartedSpace (ProductHalfSpace.Space (Vector k)) (NonnegativeHalf d) := by
  let := fiberAtlas d k hd
  exact (halfAtlas d k hd).chartedSpace

theorem half_isManifold : letI := fiberAtlas d k hd;
    letI := halfChartedSpace d k hd;
    IsManifold (ProductHalfSpace.model (Vector k)) ∞ (NonnegativeHalf d) := by
  let := fiberAtlas d k hd
  exact (halfAtlas d k hd).isManifold

theorem half_boundary_iff (p : NonnegativeHalf d) : letI := fiberAtlas d k hd;
    letI := halfChartedSpace d k hd;
    (ProductHalfSpace.model (Vector k)).IsBoundaryPoint p ↔ time d p.val = 0 := by
  let := fiberAtlas d k hd
  exact (halfAtlas d k hd).isBoundaryPoint_iff p

theorem half_interior_iff (p : NonnegativeHalf d) : letI := fiberAtlas d k hd;
    letI := halfChartedSpace d k hd;
    (ProductHalfSpace.model (Vector k)).IsInteriorPoint p ↔ 0 < time d p.val := by
  let := fiberAtlas d k hd
  exact (halfAtlas d k hd).isInteriorPoint_iff p

theorem compactSpace_half (hmiss : ∀ x, d.rightMap x ≠ b) :
    CompactSpace (NonnegativeHalf d) := by
  let := compactSpace_fiber d hmiss
  exact isCompact_iff_compactSpace.mp
    (isClosed_le continuous_const (continuous_time d)).isCompact

theorem contMDiff_half_inclusion : letI := fiberAtlas d k hd;
    letI := halfChartedSpace d k hd;
    ContMDiff (ProductHalfSpace.model (Vector k)) (𝓡 (k + 1)) ∞
      (Subtype.val : NonnegativeHalf d → Fiber d) := by
  let := fiberAtlas d k hd
  exact (halfAtlas d k hd).contMDiff_subtype_val

theorem bijective_mfderiv_half_inclusion (p : NonnegativeHalf d) :
    letI := fiberAtlas d k hd; letI := halfChartedSpace d k hd;
    Bijective (mfderiv (ProductHalfSpace.model (Vector k)) (𝓡 (k + 1))
      (Subtype.val : NonnegativeHalf d → Fiber d) p) := by
  let := fiberAtlas d k hd
  exact (halfAtlas d k hd).bijective_mfderiv_subtype_val p

theorem contMDiff_originalHalfHomeomorph (hmiss : ∀ x, d.rightMap x ≠ b)
    (a : Sphere m) (A : d.FramedSlabData k hd a) :
    letI := A.atlas; letI := fiberAtlas d k hd; letI := halfChartedSpace d k hd;
    ContMDiff ((𝓡∂ 1).prod (𝓡 k)) (ProductHalfSpace.model (Vector k)) ∞
      (originalHalfHomeomorph d hmiss) := by
  let := A.atlas
  let := fiberAtlas d k hd
  let := halfChartedSpace d k hd
  exact ((halfAtlas d k hd).contMDiff_iff_ambient (originalHalfHomeomorph d hmiss)).mpr
    (contMDiff_originalSlabPoint d k hd a A)

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder
