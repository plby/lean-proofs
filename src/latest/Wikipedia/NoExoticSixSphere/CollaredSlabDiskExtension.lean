import Wikipedia.NoExoticSixSphere.DiskRadialCollar
import Wikipedia.NoExoticSixSphere.CollaredSlabBoundaryPuncture

/-!
# Proper continuous disks with exact collars in the original filling slab

Flattening the source disk radially and applying the original inward collar
push with clock `1 - ‖x‖²` preserves the prescribed boundary map. Every
interior disk point maps to the actual strict-time interior. On the outer
half-annulus the map has an exact endpoint-collar formula. The new disk is
homotopic to the given disk relative to its boundary.

This construction does not assert smoothness or immersion in the interior.
-/

noncomputable section

open Set Metric
open scoped unitInterval

namespace NoExoticSixSphere.CylinderFiberSlab.InteriorPush

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse
open DiskCylinder

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  (F : C(ℝ × M, N)) (z : N) (s t a b : ℝ)
  (hsa : s < a) (hab : a ≤ b) (hbt : b < t)
  (hleft : ∀ r ∈ Icc s a, ∀ x, F (r, x) = F (s, x))
  (hright : ∀ r ∈ Icc b t, ∀ x, F (r, x) = F (t, x))
  (n : ℕ) (G : C(Disk (E := Vector (n + 1)), slab F z s t))

def collaredDisk : C(Disk (E := Vector (n + 1)), slab F z s t) :=
  (map F z s t a b hsa hab hbt hleft hright).comp
    ((DiskRadialCollar.clock n).prodMk (G.comp (DiskRadialCollar.flatten n)))

theorem collaredDisk_boundary (q : NoExoticSixSphere.Sphere n) :
    collaredDisk F z s t a b hsa hab hbt hleft hright n G (boundaryToDisk q) =
      G (boundaryToDisk q) := by
  change map F z s t a b hsa hab hbt hleft hright
    (DiskRadialCollar.clock n (boundaryToDisk q),
      G (DiskRadialCollar.flatten n (boundaryToDisk q))) = _
  rw [DiskRadialCollar.clock_boundary, DiskRadialCollar.flatten_boundary, map_zero]

theorem collaredDisk_interior (x : Disk (E := Vector (n + 1))) (hx : ‖x.val‖ < 1) :
    collaredDisk F z s t a b hsa hab hbt hleft hright n G x ∈ interiorDomain F z s t :=
  map_mem_interior_of_pos F z s t a b hsa hab hbt hleft hright
    (G (DiskRadialCollar.flatten n x)) (DiskRadialCollar.clock n x)
      (DiskRadialCollar.clock_pos n x hx)

def collaredDiskHomotopy : G.HomotopyRel
    (collaredDisk F z s t a b hsa hab hbt hleft hright n G) {x | ‖x.val‖ = 1} where
  toFun p := map F z s t a b hsa hab hbt hleft hright
    (p.1 * DiskRadialCollar.clock n p.2, G (DiskRadialCollar.flattenHomotopy n p))
  continuous_toFun := (map F z s t a b hsa hab hbt hleft hright).continuous.comp
    ((continuous_fst.mul ((DiskRadialCollar.clock n).continuous.comp continuous_snd)).prodMk
      (G.continuous.comp (DiskRadialCollar.flattenHomotopy n).continuous))
  map_zero_left x := by
    rw [zero_mul, (DiskRadialCollar.flattenHomotopy n).apply_zero, map_zero]
    rfl
  map_one_left x := by
    rw [one_mul, (DiskRadialCollar.flattenHomotopy n).apply_one]
    rfl
  prop' u x hx := by
    change map F z s t a b hsa hab hbt hleft hright
      (u * DiskRadialCollar.clock n x, G (DiskRadialCollar.flattenHomotopy n (u, x))) = G x
    rw [(DiskRadialCollar.clock_eq_zero_iff n x).mpr hx, mul_zero, map_zero,
      (DiskRadialCollar.flattenHomotopy n).eq_fst u hx]
    rfl

theorem collaredDisk_boundary_iff
    (hG : ∀ q : NoExoticSixSphere.Sphere n, G (boundaryToDisk q) ∈ BoundaryPush.ends F z s t)
    (x : Disk (E := Vector (n + 1))) :
    collaredDisk F z s t a b hsa hab hbt hleft hright n G x ∈ BoundaryPush.ends F z s t ↔
      ‖x.val‖ = 1 := by
  constructor
  · intro hb
    by_contra hn
    have hi := collaredDisk_interior F z s t a b hsa hab hbt hleft hright n G x
      (lt_of_le_of_ne (mem_closedBall_zero_iff.mp x.property) hn)
    change s < _ ∧ _ < t at hi
    exact hb.elim (ne_of_gt hi.1) (ne_of_lt hi.2)
  · intro hx
    let q : NoExoticSixSphere.Sphere n := ⟨x.val, mem_sphere_zero_iff_norm.mpr hx⟩
    have hq : boundaryToDisk q = x := Subtype.ext rfl
    rw [← hq, collaredDisk_boundary]
    exact hG q

theorem collaredDisk_radial (u : unitInterval) (hu : 1 / 2 ≤ (u : ℝ))
    (q : NoExoticSixSphere.Sphere n) :
    collaredDisk F z s t a b hsa hab hbt hleft hright n G (DiskCone.radial (u, q)) =
      map F z s t a b hsa hab hbt hleft hright
        (DiskRadialCollar.clock n (DiskCone.radial (u, q)), G (boundaryToDisk q)) := by
  change map F z s t a b hsa hab hbt hleft hright
    (_, G (DiskRadialCollar.flatten n (DiskCone.radial (u, q)))) = _
  rw [DiskRadialCollar.flatten_radial n u hu]

theorem collaredDisk_radial_left (u : unitInterval) (hu : 1 / 2 ≤ (u : ℝ))
    (q : NoExoticSixSphere.Sphere n) (hq : (G (boundaryToDisk q)).val.val.1 = s) :
    (collaredDisk F z s t a b hsa hab hbt hleft hright n G
      (DiskCone.radial (u, q))).val.val =
        (s + (1 - (u : ℝ) ^ 2) * (a - s), (G (boundaryToDisk q)).val.val.2) := by
  rw [collaredDisk_radial F z s t a b hsa hab hbt hleft hright n G u hu q]
  apply Prod.ext
  · change (1 - (DiskRadialCollar.clock n (DiskCone.radial (u, q)) : ℝ)) *
        (G (boundaryToDisk q)).val.val.1 +
      (DiskRadialCollar.clock n (DiskCone.radial (u, q)) : ℝ) *
        (projIcc a b hab (G (boundaryToDisk q)).val.val.1 : ℝ) = _
    rw [DiskRadialCollar.clock_radial, hq, projIcc_of_le_left hab hsa.le]
    ring
  · rfl

theorem collaredDisk_radial_right (u : unitInterval) (hu : 1 / 2 ≤ (u : ℝ))
    (q : NoExoticSixSphere.Sphere n) (hq : (G (boundaryToDisk q)).val.val.1 = t) :
    (collaredDisk F z s t a b hsa hab hbt hleft hright n G
      (DiskCone.radial (u, q))).val.val =
        (t + (1 - (u : ℝ) ^ 2) * (b - t), (G (boundaryToDisk q)).val.val.2) := by
  rw [collaredDisk_radial F z s t a b hsa hab hbt hleft hright n G u hu q]
  apply Prod.ext
  · change (1 - (DiskRadialCollar.clock n (DiskCone.radial (u, q)) : ℝ)) *
        (G (boundaryToDisk q)).val.val.1 +
      (DiskRadialCollar.clock n (DiskCone.radial (u, q)) : ℝ) *
        (projIcc a b hab (G (boundaryToDisk q)).val.val.1 : ℝ) = _
    rw [DiskRadialCollar.clock_radial, hq, projIcc_of_right_le hab hbt.le]
    ring
  · rfl

end NoExoticSixSphere.CylinderFiberSlab.InteriorPush
