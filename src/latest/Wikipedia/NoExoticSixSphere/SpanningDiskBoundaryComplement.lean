import Wikipedia.NoExoticSixSphere.SpanningDiskFramedCollar

/-!
# Original normal vectors are perpendicular to the actual disk boundary operator

A vector perpendicular to both the old partial normal frame and the original
sphere derivative remains perpendicular after adding zero coordinates. The
proof uses the exact retained collar derivative and the actual stabilized
coordinate inner products, including the height and graph directions.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.StabilizedSpanningDisk.DiskData

open GLOrthonormalization

theorem map_normal_le_combined_orthogonal {N k : ℕ} {b : Sphere 3}
    {f : Sphere 3 → Vector N} (D : DiskData b f)
    (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f) (s : Sphere 3)
    (a : Vector k →L[ℝ] Vector N) :
    (a.rangeᗮ ⊓ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ).map
        (appendZeroMap N 6).toLinearMap ≤
      (OperatorSum.operator (boundaryFrameOperator a) (fderiv ℝ D.toFun s.val)).rangeᗮ := by
  rw [OperatorSum.range_operator, ← Submodule.inf_orthogonal]
  rintro _ ⟨w, hw, rfl⟩
  have hwc : appendZeroMap N 6 w = coordinates N 4 ((w, 0), 0) :=
    (coordinates_old N 4 w).symm
  constructor
  · apply (Submodule.mem_orthogonal _ _).mpr
    rintro _ ⟨v, rfl⟩
    change inner ℝ (boundaryFrameOperator a v) (appendZeroMap N 6 w) = 0
    rw [boundaryFrameOperator_apply, hwc, inner_coordinates]
    simp only [Prod.fst_zero, Prod.snd_zero, inner_zero_right, add_zero]
    exact (Submodule.mem_orthogonal a.range w).mp hw.1 _ ⟨_, rfl⟩
  · apply (Submodule.mem_orthogonal _ _).mpr
    rintro _ ⟨v, rfl⟩
    change inner ℝ (fderiv ℝ D.toFun s.val v) (appendZeroMap N 6 w) = 0
    rw [D.fderiv_eq_collar, fderiv_collar_apply b f hf, hwc, inner_coordinates]
    simp only [Prod.fst_zero, Prod.snd_zero, inner_zero_right, add_zero]
    exact Submodule.inner_right_of_mem_orthogonal
      ((SmoothSphereAmbient.range_fderiv_extension_le b f hf s) ⟨v, rfl⟩) hw.2

end NoExoticSixSphere.StabilizedSpanningDisk.DiskData
