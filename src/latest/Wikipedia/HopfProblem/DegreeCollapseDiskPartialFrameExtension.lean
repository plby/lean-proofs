import Wikipedia.NoExoticSixSphere.PartialFrameConnectivity
import Wikipedia.NoExoticSixSphere.PartialFrameRangeCoordinates
import Wikipedia.NoExoticSixSphere.SphereCubeHomotopy
import Wikipedia.NoExoticSixSphere.ProjectionDiskFrame

/-!

# Prescribed partial frames extend over disks below the complement dimension

The native cubical connectivity theorem contracts the actual boundary
frame map whenever its sphere dimension is smaller than the complementary
rank. For varying projection ranges, contraction of the original disk
constructs a full range trivialization. Composition retains the original
projection ranges and every prescribed boundary column exactly.

This applies in particular to the two- and three-dimensional disks needed
for low-connectivity surgery; no four-disk or parity premise is used.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.DiskPartialFrame

open NoExoticSixSphere GLOrthonormalization Stiefel DiskCylinder

def center (d : ℕ) : Disk (E := Vector (d + 1)) := ⟨0, by simp⟩

theorem exists_range_frame {d N n : ℕ}
    (P : C(Disk (E := Vector (d + 1)), Vector N →L[ℝ] Vector N))
    (hP : ∀ x, IsIdempotentElem (P x))
    (hr : Module.finrank ℝ (P (center d)).range = n) :
    ∃ t : C(Disk (E := Vector (d + 1)), Space N n),
      ∀ x, (t x).val.range = (P x).range := by
  let H : unitInterval → Disk (E := Vector (d + 1)) → Vector N →L[ℝ] Vector N :=
    fun t x => P (DiskBoundary.segment (center d) (t, x))
  have hH (t : unitInterval) (x : Disk (E := Vector (d + 1))) :
      IsIdempotentElem (H t x) := hP (DiskBoundary.segment (center d) (t, x))
  have hc : Continuous (fun z : unitInterval × Disk (E := Vector (d + 1)) => H z.1 z.2) :=
    P.continuous.comp (DiskBoundary.segment (center d)).continuous
  have hzero : H 0 = P := by
    funext x
    exact congrArg P (DiskBoundary.segment_zero (center d) x)
  have hone : H 1 = fun _ => P (center d) := by
    funext x
    exact congrArg P (DiskBoundary.segment_one (center d) x)
  obtain ⟨q⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (show Module.finrank ℝ (Vector n) = Module.finrank ℝ (P (center d)).range by
      rw [finrank_euclideanSpace_fin, hr])
  have hb : Nonempty (ContinuousRangeFrame P (Vector n)) := by
    simpa only [hzero] using
      nonempty_continuousRangeFrame_of_homotopy H hH hc 1 0 (P (center d)) hone q
  obtain ⟨b⟩ := hb
  exact ProjectionDisk.exists_frame_of_rangeFrame P b

theorem exists_sphere_extension {d c r : ℕ} (hd : 0 < d) (hc : d < c)
    (f : C(NoExoticSixSphere.Sphere d, Space (c + r) r)) :
    ∃ F : C(Disk (E := Vector (d + 1)), Space (c + r) r),
      ∀ s, F (boundaryToDisk s) = f s := by
  apply (DiskBoundary.exists_extension_iff (SphereCube.point d) f).mpr
  apply (SphereCubeHomotopy.basedCube_nullhomotopic_iff hd f).mp
  exact genLoop_homotopic_const_of_lt hc r (f (SphereCube.point d))
    (SphereCube.basedCube f)

theorem exists_projection_extension {d N c r : ℕ} (hd : 0 < d) (hc : d < c)
    (P : C(Disk (E := Vector (d + 1)), Vector N →L[ℝ] Vector N))
    (hP : ∀ x, IsIdempotentElem (P x))
    (hr : Module.finrank ℝ (P (center d)).range = c + r)
    (a : C(NoExoticSixSphere.Sphere d, Space N r))
    (ha : ∀ s, (a s).val.range ≤ (P (boundaryToDisk s)).range) :
    ∃ A : C(Disk (E := Vector (d + 1)), Space N r),
      (∀ x, (A x).val.range ≤ (P x).range) ∧
      ∀ s, A (boundaryToDisk s) = a s := by
  obtain ⟨t, ht⟩ := exists_range_frame P hP hr
  have hat (s : NoExoticSixSphere.Sphere d) :
      (a s).val.range ≤ (t (boundaryToDisk s)).val.range :=
    (ha s).trans_eq (ht (boundaryToDisk s)).symm
  let f := RangeCoordinates.map (t.comp boundaryToDisk) a hat
  obtain ⟨F, hF⟩ := exists_sphere_extension hd hc f
  let A : C(Disk (E := Vector (d + 1)), Space N r) :=
    ⟨fun x => Stiefel.comp (t x) (F x), continuous_comp t F t.continuous F.continuous⟩
  refine ⟨A, ?_, ?_⟩
  · intro x
    exact (RangeCoordinates.range_comp_le (t x) (F x)).trans_eq (ht x)
  · intro s
    change Stiefel.comp (t (boundaryToDisk s)) (F (boundaryToDisk s)) = a s
    rw [hF s]
    exact RangeCoordinates.comp_extract _ _ (hat s)

end Wikipedia.HopfProblem.DegreeCollapse.DiskPartialFrame
