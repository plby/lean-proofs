import Wikipedia.NoExoticSixSphere.OpenSuperlevelBoundary

/-!
# The actual boundary inclusion is an immersion

The six-dimensional regular-level atlas is independent of the superlevel
atlas. Its inclusion into the ambient parameter manifold is an immersion,
and the chain rule then proves immersion into the superlevel piece itself.
-/

open Set Topology TopologicalSpace Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.OpenSuperlevelBoundary

variable {B H M K N : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  {f : M → ℝ} (A : SuperlevelAtlas (K := K) I f)
  (U : Opens {x : M // 0 ≤ f x}) [TopologicalSpace N] (e : N ≃ₜ U)
  (R : RegularLevelAtlas (K := K) I f)

theorem injective_mfderiv_coordinates (p : Boundary A U e) :
    letI := chartedSpace A U e R;
    Injective (mfderiv 𝓘(ℝ, K) I (fun q : Boundary A U e ↦ (e q.val).val.val) p) := by
  let := R.chartedSpace
  let := R.isManifold
  let := chartedSpace A U e R
  let d := diffeomorph A U e R
  have hd := (d.mfderivToContinuousLinearEquiv (by simp) p).injective
  have ho := (mfderiv_openSubset_val_bijective (I := 𝓘(ℝ, K))
    (zeroWindow f U) (d p)).injective
  have hr := R.injective_mfderiv_subtype_val (d p).val
  have hdd := d.contMDiff_toFun.mdifferentiable (by simp) p
  have hod := (_root_.contMDiff_subtype_val (I := 𝓘(ℝ, K))
    (U := zeroWindow f U) (n := ∞)).mdifferentiable (by simp) (d p)
  have hrd := R.contMDiff_subtype_val.mdifferentiable (by simp) (d p).val
  change Injective (mfderiv 𝓘(ℝ, K) I
    ((Subtype.val : {x : M // f x = 0} → M) ∘
      ((Subtype.val : zeroWindow f U → {x : M // f x = 0}) ∘ d)) p)
  rw [mfderiv_comp p hrd (hod.comp p hdd), mfderiv_comp p hod hdd]
  exact hr.comp (ho.comp hd)

theorem injective_mfderiv_inclusion (p : Boundary A U e) :
    letI := OpenSuperlevelAtlas.chartedSpace A U e;
    letI := chartedSpace A U e R;
    Injective (mfderiv 𝓘(ℝ, K) (ProductHalfSpace.model K)
      (Subtype.val : Boundary A U e → N) p) := by
  let := OpenSuperlevelAtlas.chartedSpace A U e
  let := chartedSpace A U e R
  have h := injective_mfderiv_coordinates A U e R p
  change Injective (mfderiv 𝓘(ℝ, K) I
    ((fun q : N ↦ (e q).val.val) ∘ (Subtype.val : Boundary A U e → N)) p) at h
  rw [mfderiv_comp p
    ((OpenSuperlevelAtlas.contMDiff_coordinates A U e).mdifferentiable (by simp) p.val)
    ((contMDiff_inclusion A U e R).mdifferentiable (by simp) p)] at h
  intro v w hvw
  exact h (congrArg (mfderiv (ProductHalfSpace.model K) I
    (fun q : N ↦ (e q).val.val) p.val) hvw)

end NoExoticSixSphere.OpenSuperlevelBoundary
