import Wikipedia.NoExoticSixSphere.OpenSuperlevelBoundaryDifferential

/-!
# The actual boundary tangent image is the defining differential's kernel

The statement uses the native boundary atlas and the actual ambient parameter
map. Restriction to an open window and the boundary diffeomorphism do not
change the range of the regular-zero inclusion differential.
-/

noncomputable section

open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.OpenSuperlevelBoundary

variable {B H M K N : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  [FiniteDimensional ℝ B] [FiniteDimensional ℝ K]
  {f : M → ℝ} (A : SuperlevelAtlas (K := K) I f)
  (U : Opens {x : M // 0 ≤ f x}) [TopologicalSpace N] (e : N ≃ₜ U)
  (R : RegularLevelAtlas (K := K) I f)

theorem range_mfderiv_coordinates (p : Boundary A U e)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (e p.val).val.val)
    (hreg : Surjective (mfderiv I 𝓘(ℝ, ℝ) f (e p.val).val.val))
    (hdim : Module.finrank ℝ B = 1 + Module.finrank ℝ K) :
    letI := chartedSpace A U e R;
    (mfderiv 𝓘(ℝ, K) I (fun q : Boundary A U e ↦ (e q.val).val.val) p).range =
      (mfderiv I 𝓘(ℝ, ℝ) f (e p.val).val.val).ker := by
  let := R.chartedSpace
  let := R.isManifold
  let := chartedSpace A U e R
  let d := diffeomorph A U e R
  let g : Boundary A U e → {x : M // f x = 0} := fun q ↦ (d q).val
  have hg : ContMDiff 𝓘(ℝ, K) 𝓘(ℝ, K) ∞ g :=
    contMDiff_subtype_val.comp d.contMDiff_toFun
  have hgD : Bijective (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, K) g p) := by
    have hj := (_root_.contMDiff_subtype_val (I := 𝓘(ℝ, K))
      (U := zeroWindow f U) (n := ∞)).mdifferentiable (by simp) (d p)
    have hc : mfderiv 𝓘(ℝ, K) 𝓘(ℝ, K) g p =
        (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, K)
          (Subtype.val : zeroWindow f U → {x : M // f x = 0}) (d p)).comp
            (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, K) d p) :=
      mfderiv_comp p hj (d.contMDiff_toFun.mdifferentiableAt (by simp))
    rw [hc]
    exact (mfderiv_openSubset_val_bijective (I := 𝓘(ℝ, K)) (zeroWindow f U) (d p)).comp
      (d.mfderivToContinuousLinearEquiv (by simp) p).bijective
  have hzero := R.range_inclusion_eq_kernel (g p) hf hreg (by
    simpa only [Module.finrank_self] using hdim)
  have hc : mfderiv 𝓘(ℝ, K) I (fun q : Boundary A U e ↦ (e q.val).val.val) p =
      (mfderiv 𝓘(ℝ, K) I (Subtype.val : {x : M // f x = 0} → M) (g p)).comp
        (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, K) g p) :=
    mfderiv_comp p (R.contMDiff_subtype_val.mdifferentiableAt (by simp))
      (hg.mdifferentiableAt (by simp))
  rw [hc]
  exact (LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr hgD.surjective)).trans hzero

variable {P : Type*} [TopologicalSpace P] [ChartedSpace K P]

theorem range_mfderiv_coordinates_comp
    (d : letI := chartedSpace A U e R; P ≃ₘ⟮𝓘(ℝ, K), 𝓘(ℝ, K)⟯ Boundary A U e) (p : P)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (e (d p).val).val.val)
    (hreg : Surjective (mfderiv I 𝓘(ℝ, ℝ) f (e (d p).val).val.val))
    (hdim : Module.finrank ℝ B = 1 + Module.finrank ℝ K) :
    (mfderiv 𝓘(ℝ, K) I (fun q : P ↦ (e (d q).val).val.val) p).range =
      (mfderiv I 𝓘(ℝ, ℝ) f (e (d p).val).val.val).ker := by
  let := chartedSpace A U e R
  have hc : mfderiv 𝓘(ℝ, K) I (fun q : P ↦ (e (d q).val).val.val) p =
      (mfderiv 𝓘(ℝ, K) I (fun q : Boundary A U e ↦ (e q.val).val.val) (d p)).comp
        (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, K) d p) :=
    mfderiv_comp p ((contMDiff_coordinates A U e R).mdifferentiableAt (by simp))
      (d.contMDiff_toFun.mdifferentiableAt (by simp))
  rw [hc]
  exact (LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr
    (d.mfderivToContinuousLinearEquiv (by simp) p).surjective)).trans
      (range_mfderiv_coordinates A U e R (d p) hf hreg hdim)

end NoExoticSixSphere.OpenSuperlevelBoundary
