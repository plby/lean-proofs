import Wikipedia.NoExoticSixSphere.SpanningDiskBoundaryComplementEquality
import Wikipedia.NoExoticSixSphere.EuclideanBlockProjection

/-!
# Pulling the actual disk complement back to the old ambient coordinates

At the boundary every complementary vector has zero new coordinates. The old
coordinate projection consequently preserves its norm and entire range. This
gives a smooth orthonormal frame of the original internal normal space, in
the same source atlas, from the actual disk complement in any dimension.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.StabilizedSpanningDisk

open GLOrthonormalization

def boundaryComplementOperator {N q : ℕ}
    (C : Vector 4 → Vector q →L[ℝ] Vector (N + 6)) (s : Sphere 3) :
    Vector q →L[ℝ] Vector N := (oldProjection N 6).comp (C s.val)

theorem contMDiff_boundaryComplementOperator {N q : ℕ}
    (C : Vector 4 → Vector q →L[ℝ] Vector (N + 6))
    (hCs : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ C x) :
    ContMDiff (𝓡 3) 𝓘(ℝ, Vector q →L[ℝ] Vector N) ∞ (boundaryComplementOperator C) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hs : ContMDiff (𝓡 3) (𝓡 4) ∞ (fun s : Sphere 3 ↦ s.val) := contMDiff_coe_sphere
  intro s
  exact contMDiffAt_const.clm_comp
    ((hCs s.val (sphere_subset_closedBall s.property)).contMDiffAt.comp s hs.contMDiffAt)

namespace DiskData

variable {N k q : ℕ} {b : Sphere 3} {f : Sphere 3 → Vector N} (D : DiskData b f)
  (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 N) f s))
  (a : Sphere 3 → Stiefel.Space N k)
  (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ)
  (C : Vector 4 → Vector q →L[ℝ] Vector (N + 6))
  (hCr : ∀ s : Sphere 3, (C s.val).range =
    (OperatorSum.operator (boundaryFrameOperator (a s).val) (fderiv ℝ D.toFun s.val)).rangeᗮ)

include hf hd ha hCr in
theorem complement_range_boundary (s : Sphere 3) :
    (C s.val).range = ((a s).val.rangeᗮ ⊓ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ).map
      (appendZeroMap N 6).toLinearMap :=
  (hCr s).trans (D.map_normal_eq_combined_orthogonal hf s (hd s) (a s) (ha s)).symm

include hf hd ha hCr in
theorem append_boundaryComplementOperator (s : Sphere 3) (v : Vector q) :
    appendZeroMap N 6 (boundaryComplementOperator C s v) = C s.val v := by
  apply appendZeroMap_oldProjection
  have hv : C s.val v ∈ ((a s).val.rangeᗮ ⊓ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ).map
      (appendZeroMap N 6).toLinearMap := by
    rw [← D.complement_range_boundary hf hd a ha C hCr s]
    exact ⟨v, rfl⟩
  obtain ⟨w, _, hw⟩ := hv
  exact ⟨w, hw⟩

include hf hd ha hCr in
theorem norm_boundaryComplementOperator
    (hCn : ∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖C x w‖ = ‖w‖)
    (s : Sphere 3) (v : Vector q) : ‖boundaryComplementOperator C s v‖ = ‖v‖ := by
  calc
    ‖boundaryComplementOperator C s v‖ =
        ‖appendZeroMap N 6 (boundaryComplementOperator C s v)‖ :=
      (norm_appendZeroMap N 6 _).symm
    _ = ‖C s.val v‖ := congrArg norm (D.append_boundaryComplementOperator hf hd a ha C hCr s v)
    _ = ‖v‖ := hCn s.val (sphere_subset_closedBall s.property) v

include hf hd ha hCr in
theorem range_boundaryComplementOperator (s : Sphere 3) :
    (boundaryComplementOperator C s).range =
      (a s).val.rangeᗮ ⊓ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ := by
  change LinearMap.range ((oldProjection N 6).toLinearMap.comp (C s.val).toLinearMap) = _
  rw [LinearMap.range_comp, D.complement_range_boundary hf hd a ha C hCr s,
    ← Submodule.map_comp]
  have he : (oldProjection N 6).toLinearMap.comp (appendZeroMap N 6).toLinearMap =
      LinearMap.id := by
    apply LinearMap.ext
    intro v
    exact oldProjection_appendZeroMap N 6 v
  rw [he, Submodule.map_id]

end DiskData
end NoExoticSixSphere.StabilizedSpanningDisk
