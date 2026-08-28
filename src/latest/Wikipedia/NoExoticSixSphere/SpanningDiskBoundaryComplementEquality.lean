import Wikipedia.NoExoticSixSphere.SpanningDiskBoundaryComplement

/-!
# Exact boundary complement for an actual stabilized spanning disk

The old vectors perpendicular to the prescribed normal frame and original
sphere derivative give the entire complement of the stabilized normal frame
and actual disk derivative. The retained collar proves inclusion, and the
injectivity of both actual combined operators proves equality of ranks.
The result is independent of the dimension of the complement.
-/

noncomputable section

open Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.StabilizedSpanningDisk.DiskData

open GLOrthonormalization Stiefel SphereThreeTangentFrame

theorem map_normal_eq_combined_orthogonal {N k : ℕ} {b : Sphere 3}
    {f : Sphere 3 → Vector N} (D : DiskData b f)
    (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f) (s : Sphere 3)
    (hd : Injective (mfderiv (𝓡 3) (𝓡 N) f s)) (a : Space N k)
    (ha : a.val.range ≤ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ) :
    (a.val.rangeᗮ ⊓ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ).map
        (appendZeroMap N 6).toLinearMap =
      (OperatorSum.operator (boundaryFrameOperator a.val)
        (fderiv ℝ D.toFun s.val)).rangeᗮ := by
  let B : Vector (k + 3) →L[ℝ] Vector N :=
    OperatorSum.operator a.val (framedDerivative f s)
  have han : a.val.range ≤ (framedDerivative f s).rangeᗮ := by
    rw [range_framedDerivative f hf s]
    exact ha
  have hiB : Injective B := OperatorSum.injective_operator _ _ (Stiefel.injective a)
    (injective_framedDerivative f hf s hd)
    ((framedDerivative f s).range.orthogonal_disjoint.symm.mono_left han)
  have hW : a.val.rangeᗮ ⊓ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ = B.rangeᗮ := by
    dsimp only [B]
    rw [OperatorSum.range_operator, ← Submodule.inf_orthogonal, range_framedDerivative f hf s]
  let Q : Vector ((k + 5) + 4) →L[ℝ] Vector (N + 6) :=
    OperatorSum.operator (boundaryFrameOperator a.val) (fderiv ℝ D.toFun s.val)
  have haD : (boundaryFrame a).val.range ≤ (fderiv ℝ D.toFun s.val).rangeᗮ := by
    rw [D.fderiv_eq_collar]
    exact boundaryFrame_normal_collar b f hf s a ha
  have hiQ : Injective Q := OperatorSum.injective_operator _ _
    (Stiefel.injective (boundaryFrame a))
    (D.immersive s.val (sphere_subset_closedBall s.property))
    ((fderiv ℝ D.toFun s.val).range.orthogonal_disjoint.symm.mono_left haD)
  apply Submodule.eq_of_le_of_finrank_eq (D.map_normal_le_combined_orthogonal hf s a.val)
  rw [← (Submodule.equivMapOfInjective (appendZeroMap N 6).toLinearMap
    (appendZeroMap_injective N 6)
    (a.val.rangeᗮ ⊓ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ)).finrank_eq, hW]
  change Module.finrank ℝ B.rangeᗮ = Module.finrank ℝ Q.rangeᗮ
  have hB := B.range.finrank_add_finrank_orthogonal
  have hQ := Q.range.finrank_add_finrank_orthogonal
  rw [LinearMap.finrank_range_of_inj hiB,
    finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at hB
  rw [LinearMap.finrank_range_of_inj hiQ,
    finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at hQ
  omega

end NoExoticSixSphere.StabilizedSpanningDisk.DiskData
