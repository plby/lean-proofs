import Wikipedia.NoExoticSixSphere.CollaredSlabDiskExtension
import Wikipedia.NoExoticSixSphere.RegularSlabInteriorEquivalence
import Wikipedia.NoExoticSixSphere.IntegralKernelDiskExtension

/-!
# Constructed collared continuous disks for actual integral kernel classes

The original regular cylinder supplies the constant collars, so every
continuous disk extension can be replaced by an exact collared extension
whose interior stays in the actual slab interior. For a two-connected
slab, such an extension exists exactly when the original integral sphere
class vanishes. The inclusion-kernel specialization uses integral, not
mod-two, homology. No immersed-disk existence is asserted here.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.RegularCollaredCylinder

open GLOrthonormalization CylinderFiberSlab
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology
open Wikipedia.HopfProblem.DegreeCollapse
open DiskCylinder

variable {B H M C H' N : Type}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [TopologicalSpace N] [ChartedSpace H' N]
  {z : N} {s t : ℝ} (d : RegularCollaredCylinder (M := M) I J z s t)

structure CollaredDiskExtension (n : ℕ) (f : C(NoExoticSixSphere.Sphere n, slab d.map z s t)) where
  leftCut : ℝ
  rightCut : ℝ
  left_lt : s < leftCut
  cuts_le : leftCut ≤ rightCut
  right_lt : rightCut < t
  left_subset : Icc s leftCut ⊆ d.leftTimes
  right_subset : Icc rightCut t ⊆ d.rightTimes
  map : C(Disk (E := Vector (n + 1)), slab d.map z s t)
  boundary : ∀ q, map (boundaryToDisk q) = f q
  interior : ∀ x, ‖x.val‖ < 1 → map x ∈ interiorDomain d.map z s t
  left_collar : ∀ (u : unitInterval), 1 / 2 ≤ (u : ℝ) →
    ∀ q, (f q).val.val.1 = s → (map (DiskCone.radial (u, q))).val.val =
      (s + (1 - (u : ℝ) ^ 2) * (leftCut - s), (f q).val.val.2)
  right_collar : ∀ (u : unitInterval), 1 / 2 ≤ (u : ℝ) →
    ∀ q, (f q).val.val.1 = t → (map (DiskCone.radial (u, q))).val.val =
      (t + (1 - (u : ℝ) ^ 2) * (rightCut - t), (f q).val.val.2)

def collaredDiskOfExtension (n : ℕ) (f : C(NoExoticSixSphere.Sphere n, slab d.map z s t))
    (G : C(Disk (E := Vector (n + 1)), slab d.map z s t))
    (hG : ∀ q, G (boundaryToDisk q) = f q) : d.CollaredDiskExtension n f := by
  let a := d.exists_inner_times.choose
  let b := d.exists_inner_times.choose_spec.choose
  have h := d.exists_inner_times.choose_spec.choose_spec
  have hL : ∀ r ∈ Icc s a, ∀ x, d.map (r, x) = d.map (s, x) :=
    fun r hr x ↦ (d.left_eq r (h.2.2.2.1 hr) x).trans (d.left_eq s d.left_mem x).symm
  have hR : ∀ r ∈ Icc b t, ∀ x, d.map (r, x) = d.map (t, x) :=
    fun r hr x ↦ (d.right_eq r (h.2.2.2.2 hr) x).trans (d.right_eq t d.right_mem x).symm
  refine {
    leftCut := a
    rightCut := b
    left_lt := h.1
    cuts_le := h.2.1
    right_lt := h.2.2.1
    left_subset := h.2.2.2.1
    right_subset := h.2.2.2.2
    map := InteriorPush.collaredDisk d.map z s t a b h.1 h.2.1 h.2.2.1 hL hR n G
    boundary := fun q ↦ (InteriorPush.collaredDisk_boundary
      d.map z s t a b h.1 h.2.1 h.2.2.1 hL hR n G q).trans (hG q)
    interior := InteriorPush.collaredDisk_interior
      d.map z s t a b h.1 h.2.1 h.2.2.1 hL hR n G
    left_collar := ?_
    right_collar := ?_
  }
  · intro u hu q hq
    simpa only [hG] using InteriorPush.collaredDisk_radial_left
      d.map z s t a b h.1 h.2.1 h.2.2.1 hL hR n G u hu q (by rw [hG]; exact hq)
  · intro u hu q hq
    simpa only [hG] using InteriorPush.collaredDisk_radial_right
      d.map z s t a b h.1 h.2.1 h.2.2.1 hL hR n G u hu q (by rw [hG]; exact hq)

theorem CollaredDiskExtension.boundary_iff {n : ℕ}
    {f : C(NoExoticSixSphere.Sphere n, slab d.map z s t)} (D : d.CollaredDiskExtension n f)
    (hf : ∀ q, f q ∈ BoundaryPush.ends d.map z s t) (x : Disk (E := Vector (n + 1))) :
    D.map x ∈ BoundaryPush.ends d.map z s t ↔ ‖x.val‖ = 1 := by
  constructor
  · intro hb
    by_contra hn
    have hi := D.interior x (lt_of_le_of_ne (mem_closedBall_zero_iff.mp x.property) hn)
    exact hb.elim (ne_of_gt hi.1) (ne_of_lt hi.2)
  · intro hx
    let q : NoExoticSixSphere.Sphere n := ⟨x.val, mem_sphere_zero_iff_norm.mpr hx⟩
    have hq : boundaryToDisk q = x := Subtype.ext rfl
    rw [← hq, D.boundary]
    exact hf q

variable [SimplyConnectedSpace (slab d.map z s t)] (w : slab d.map z s t)
  [hW₂ : Subsingleton (π_ 2 (slab d.map z s t) w)]

include w hW₂ in
theorem collaredDiskExtension_nonempty_iff (f : C(NoExoticSixSphere.Sphere 3, slab d.map z s t)) :
    Nonempty (d.CollaredDiskExtension 3 f) ↔ SmoothCube.integralSphereClass f = 0 := by
  constructor
  · rintro ⟨D⟩
    exact SmoothCube.integralSphereClass_zero_of_disk_extension f D.map D.boundary
  · intro hf
    obtain ⟨G, hG⟩ := (SmoothCube.integralSphereClass_zero_iff_disk_extension w f).mp hf
    exact ⟨d.collaredDiskOfExtension 3 f G hG⟩

include w hW₂ in
theorem nonempty_collaredDiskExtension_of_integral_kernel (U : Set (slab d.map z s t))
    (f : C(NoExoticSixSphere.Sphere 3, U))
    (hf : singularHomologyMap (subtypeInclusion U) 3 (SmoothCube.integralSphereClass f) = 0) :
    Nonempty (d.CollaredDiskExtension 3 ((subtypeInclusion U).comp f)) :=
  (d.collaredDiskExtension_nonempty_iff w _).mpr
    ((SmoothCube.integralSphereClass_comp (subtypeInclusion U) f).trans hf)

end NoExoticSixSphere.RegularCollaredCylinder
