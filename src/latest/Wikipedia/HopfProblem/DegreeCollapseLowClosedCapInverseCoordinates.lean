import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryNewOverlap

/-!

# Inverse source parameters for the actual closed cap

Rescale a source vector of norm at most the face radius into the literal
unit disk. On the original handle collar the glued cap agrees with its
actual sheet expression. Every unchanged handle-boundary point therefore
has a cap preimage, including points on either side of the gluing cut.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair

open NoExoticSixSphere GLOrthonormalization Stiefel RoundedTrace
open Wikipedia.SmoothSixDPoincare.PuncturedHandle

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M} (A : FramedAttachingProduct e a f)

def capFromDisk (x : Vector (d + 1)) (hx : ‖x‖ ≤ oldRadius A)
    (w : sphere (0 : Vector (7 - d)) 1) : CapDomain d := by
  refine (⟨(oldRadius A)⁻¹ • x, ?_⟩, w)
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (oldRadius_pos A)]
  calc
    (oldRadius A)⁻¹ * ‖x‖ ≤ (oldRadius A)⁻¹ * oldRadius A :=
      mul_le_mul_of_nonneg_left hx (inv_pos.mpr (oldRadius_pos A)).le
    _ = 1 := inv_mul_cancel₀ (oldRadius_pos A).ne'

theorem capDisk_fromDisk (x : Vector (d + 1)) (hx : ‖x‖ ≤ oldRadius A)
    (w : sphere (0 : Vector (7 - d)) 1) :
    capDisk A (capFromDisk A x hx w) = x :=
  smul_inv_smul₀ (oldRadius_pos A).ne' x

theorem capParameter_fromDisk (x : Vector (d + 1)) (hx : ‖x‖ ≤ oldRadius A)
    (w : sphere (0 : Vector (7 - d)) 1) :
    capParameter A (capFromDisk A x hx w) = ‖x‖ ^ 2 - 1 := by
  rw [capParameter, capDisk_fromDisk]

theorem capCollar_of_left (p : CapDomain d) (hp : capParameter A p ≤ -(bump A).rOut) :
    capCollar A p =
      ((SphereRadialRetraction.retract (spherePole d) (capDisk A p), p.2.val),
        capParameter A p) := by
  simp only [capCollar,
    LowRoundedZeroPoint.point_of_left (bump A) (by norm_num : (0 : ℝ) < 1)
      (p.2, capParameter A p) hp, one_smul]

theorem capPoint_eq_outer_of_innerRadius_le (hR : A.radius = 2) (p : CapDomain d)
    (hp : A.innerRadius ≤ ‖capDisk A p‖) : capPoint A p = capOuter A p := by
  by_cases hi : ‖capDisk A p‖ ≤ cutRadius A
  · rw [capPoint_of_inner A p hi, capOuter, capCollar_of_inner A p hi]
    exact A.map_eq_cylinder_collarCoordinates (capDisk_mem_inner A p hi) hp
      (capTransverse_mem A hR p)
  · exact capPoint_of_outer A hR p (lt_of_not_ge hi).le

theorem exists_capPoint_handle (hR : A.radius = 2) (x : Vector (d + 1))
    (hx : ‖x‖ ≤ 1) (w : sphere (0 : Vector (7 - d)) 1)
    (hu : ‖x‖ ^ 2 - 1 ≤ -(bump A).rOut) :
    ∃ p : CapDomain d, capPoint A p = A.map (x, w.val) := by
  have hxη : ‖x‖ ≤ oldRadius A := hx.trans (oldRadius_gt_one A hR).le
  let p := capFromDisk A x hxη w
  have hxp : capDisk A p = x := capDisk_fromDisk A x hxη w
  have hup : capParameter A p = ‖x‖ ^ 2 - 1 := capParameter_fromDisk A x hxη w
  refine ⟨p, ?_⟩
  by_cases hp : ‖capDisk A p‖ ≤ cutRadius A
  · rw [capPoint_of_inner A p hp, capInner, hxp]
    rfl
  · have hi : A.innerRadius ≤ ‖capDisk A p‖ :=
      (innerRadius_lt_cutRadius A).le.trans (lt_of_not_ge hp).le
    rw [capPoint_eq_outer_of_innerRadius_le A hR p hi, capOuter,
      capCollar_of_left A p (hup.symm ▸ hu), hxp, hup]
    have hxB : x ∈ closedBall (0 : Vector (d + 1)) 1 := by
      simpa only [mem_closedBall, dist_zero_right] using hx
    rw [hxp] at hi
    exact (A.map_eq_cylinder_collarCoordinates hxB hi (capTransverse_mem A hR p)).symm

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair
