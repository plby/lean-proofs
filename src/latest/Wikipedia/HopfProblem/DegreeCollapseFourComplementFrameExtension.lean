import Wikipedia.NoExoticSixSphere.PartialFrameConnectivity
import Wikipedia.NoExoticSixSphere.PartialFrameRangeCoordinates
import Wikipedia.NoExoticSixSphere.SphereCubeHomotopy
import Wikipedia.NoExoticSixSphere.SmoothDiskFrameExtension
import Wikipedia.NoExoticSixSphere.ProjectionDiskFrame

/-!
# Four complementary directions remove the four-disk framing obstruction

Every prescribed partial frame on the actual three-sphere extends over the
actual four-ball when at least four directions remain complementary. Range
transport constructs a trivialization for varying projection ranges, and
relative smoothing retains the exact original boundary values. No filling
of the original six-manifold is assumed to exist or constructed here.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FourComplementFrame

open NoExoticSixSphere GLOrthonormalization Stiefel DiskCylinder

theorem exists_sphere_extension {c r : ℕ} (hc : 3 < c)
    (f : C(NoExoticSixSphere.Sphere 3, Space (c + r) r)) :
    ∃ F : C(Disk (E := Vector 4), Space (c + r) r),
      ∀ s, F (boundaryToDisk s) = f s := by
  apply (DiskBoundary.exists_extension_iff (SphereCube.point 3) f).mpr
  apply (SphereCubeHomotopy.basedCube_nullhomotopic_iff (by decide : 0 < 3) f).mp
  exact genLoop_homotopic_const_of_lt hc r (f (SphereCube.point 3))
    (SphereCube.basedCube f)

theorem exists_projection_extension {N c r : ℕ} (hc : 3 < c)
    (P : C(Disk (E := Vector 4), Vector N →L[ℝ] Vector N))
    (hP : ∀ x, IsIdempotentElem (P x))
    (hr : Module.finrank ℝ (P ProjectionDisk.center).range = c + r)
    (a : C(NoExoticSixSphere.Sphere 3, Space N r))
    (ha : ∀ s, (a s).val.range ≤ (P (boundaryToDisk s)).range) :
    ∃ A : C(Disk (E := Vector 4), Space N r),
      (∀ x, (A x).val.range ≤ (P x).range) ∧
      ∀ s, A (boundaryToDisk s) = a s := by
  obtain ⟨t, ht⟩ := ProjectionDisk.exists_frame P hP hr
  have hat (s : NoExoticSixSphere.Sphere 3) :
      (a s).val.range ≤ (t (boundaryToDisk s)).val.range :=
    (ha s).trans_eq (ht (boundaryToDisk s)).symm
  let f := RangeCoordinates.map (t.comp boundaryToDisk) a hat
  obtain ⟨F, hF⟩ := exists_sphere_extension hc f
  let A : C(Disk (E := Vector 4), Space N r) :=
    ⟨fun x ↦ Stiefel.comp (t x) (F x),
      continuous_comp t F t.continuous F.continuous⟩
  refine ⟨A, ?_, ?_⟩
  · intro x
    exact (RangeCoordinates.range_comp_le (t x) (F x)).trans_eq (ht x)
  · intro s
    change Stiefel.comp (t (boundaryToDisk s)) (F (boundaryToDisk s)) = a s
    rw [hF s]
    exact RangeCoordinates.comp_extract _ _ (hat s)

theorem exists_smooth_projection_extension {N c r : ℕ} (hc : 3 < c)
    (P : Vector 4 → Vector N →L[ℝ] Vector N)
    (hP : ∀ x ∈ closedBall (0 : Vector 4) 1, IsIdempotentElem (P x))
    (hPs : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ P x)
    (hr : Module.finrank ℝ (P 0).range = c + r)
    (a : C(NoExoticSixSphere.Sphere 3, Space N r))
    (has : ContMDiff (𝓡 3) 𝓘(ℝ, Vector r →L[ℝ] Vector N) ∞ (fun s ↦ (a s).val))
    (ha : ∀ s, (a s).val.range ≤ (P s.val).range) :
    ∃ T : Vector 4 → Vector r →L[ℝ] Vector N,
      (∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ T x) ∧
      (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖T x w‖ = ‖w‖) ∧
      (∀ x ∈ closedBall (0 : Vector 4) 1, (T x).range ≤ (P x).range) ∧
      ∀ s, T s.val = (a s).val := by
  have hPc : Continuous (fun x : Disk (E := Vector 4) ↦ P x.val) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hPs x x.property).continuousAt.comp continuous_subtype_val.continuousAt
  let Pc : C(Disk (E := Vector 4), Vector N →L[ℝ] Vector N) := ⟨_, hPc⟩
  obtain ⟨A, hAr, hAb⟩ := exists_projection_extension hc Pc
    (fun x ↦ hP x x.property) hr a ha
  exact exists_smoothDiskFrame_extension P hP hPs a has A hAr hAb

end Wikipedia.HopfProblem.DegreeCollapse.FourComplementFrame
