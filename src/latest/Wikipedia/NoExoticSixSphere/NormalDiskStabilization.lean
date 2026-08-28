import Wikipedia.NoExoticSixSphere.StabilizedNormalRange
import Wikipedia.NoExoticSixSphere.RangeObstructionStabilization
import Wikipedia.NoExoticSixSphere.NormalDiskObstruction

/-!
# Actual normal-disk parity is unchanged by five-coordinate stabilization

The stabilized differential is the original differential followed by the
actual zero-coordinate inclusion. A stabilized full normal frame spans its
entire actual normal space. Its boundary coordinates are the ordinary block
stabilization of the old coordinates, whose parity is already proved equal.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.DiskStabilization

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

def differential {N : ℕ} (m : ℕ)
    (D : C(Disk (E := Vector 4), Vector 4 →L[ℝ] Vector N)) :
    C(Disk (E := Vector 4), Vector 4 →L[ℝ] Vector (N + m)) :=
  ⟨fun x ↦ (appendZeroMap N m).comp (D x), continuous_const.clm_comp D.continuous⟩

theorem differential_injective {N : ℕ} (m : ℕ)
    (D : C(Disk (E := Vector 4), Vector 4 →L[ℝ] Vector N))
    (hi : ∀ x, Function.Injective (D x)) (x : Disk (E := Vector 4)) :
    Function.Injective (differential m D x) :=
  (appendZeroMap_injective N m).comp (hi x)

theorem boundary_normal {N k : ℕ} (m : ℕ)
    (D : C(Disk (E := Vector 4), Vector 4 →L[ℝ] Vector N))
    (a : C(NoExoticSixSphere.Sphere 3, Space N k))
    (ha : ∀ s, (a s).val.range ≤ (D (boundaryToDisk s)).rangeᗮ)
    (s : NoExoticSixSphere.Sphere 3) :
    (((BlockSum.map m).comp a) s).val.range ≤ (differential m D (boundaryToDisk s)).rangeᗮ :=
  range_blockFrame_normal m (D (boundaryToDisk s)) (a s) (ha s)

theorem parity_five (r : ℕ)
    (D : C(Disk (E := Vector 4), Vector 4 →L[ℝ] Vector (r + 9)))
    (hi : ∀ x, Function.Injective (D x))
    (a : C(NoExoticSixSphere.Sphere 3, Space (r + 9) (r + 2)))
    (ha : ∀ s, (a s).val.range ≤ (D (boundaryToDisk s)).rangeᗮ) :
    DiskNormal.parity (r + 5) (differential 5 D) (differential_injective 5 D hi)
        ((BlockSum.map 5).comp a) (boundary_normal 5 D a ha) =
      DiskNormal.parity r D hi a ha := by
  let P := DiskNormal.projectionMap D hi
  have hP := DiskNormal.projectionMap_idempotent D hi
  have hr := DiskNormal.obstruction_rank r D hi
  obtain ⟨t, ht⟩ := ProjectionDisk.exists_frame P hP hr
  have htn (x : Disk (E := Vector 4)) : (t x).val.range = (D x).rangeᗮ :=
    (ht x).trans (DiskNormal.projectionMap_range D hi x)
  have hat (s : NoExoticSixSphere.Sphere 3) :
      (a s).val.range ≤ (t (boundaryToDisk s)).val.range :=
    (ha s).trans_eq (htn (boundaryToDisk s)).symm
  let D' := differential 5 D
  have hi' := differential_injective 5 D hi
  let t' := (BlockSum.map 5).comp t
  let a' := (BlockSum.map 5).comp a
  have hn' := boundary_normal 5 D a ha
  have ht' (x : Disk (E := Vector 4)) :
      (t' x).val.range = (DiskNormal.projectionMap D' hi' x).range :=
    (range_blockFrame_eq_normal 5 (D x) (t x) (htn x)).trans
      (DiskNormal.projectionMap_range D' hi' x).symm
  have hat' (s : NoExoticSixSphere.Sphere 3) :
      (a' s).val.range ≤ (t' (boundaryToDisk s)).val.range :=
    BlockSum.range_frame_mono 5 (t (boundaryToDisk s)) (a s) (hat s)
  calc
    _ = RangeObstruction.parity (r + 5) t' a' hat' :=
      ProjectionObstruction.parity_eq_of_trivialization (r + 5)
        (DiskNormal.projectionMap D' hi') (DiskNormal.projectionMap_idempotent D' hi')
        (DiskNormal.obstruction_rank (r + 5) D' hi') a'
        (DiskNormal.boundary_normal_range (r + 5) D' hi' a' hn') t' ht' hat'
    _ = RangeObstruction.parity r t a hat := RangeObstruction.parity_block_five r t a hat
    _ = _ := (ProjectionObstruction.parity_eq_of_trivialization r P hP hr a
      (DiskNormal.boundary_normal_range r D hi a ha) t ht hat).symm

end NoExoticSixSphere.Stiefel.DiskStabilization
