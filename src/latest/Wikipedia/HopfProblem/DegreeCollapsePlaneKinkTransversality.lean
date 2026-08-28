import Wikipedia.HopfProblem.DegreeCollapseSupportedPlaneKink

/-!
# Exact transversality and compact trace of the plane modification

The native chain rule retains both source-coordinate derivatives and the
common ambient derivative at a crossing. The constructed diffeomorphisms
make all three invertible, so transversality of the actual cusp is preserved.
The full bounded-time modification trace is compact.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SupportedCusp

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization

theorem fderiv_longMap (β : Cutoff) (t : ℝ) (x : Vector 3) :
    fderiv ℝ (longMap β t) x =
      (fderiv ℝ targetDiffeomorph (map β.value t (sourceDiffeomorph.symm x))).comp
        ((fderiv ℝ (map β.value t) (sourceDiffeomorph.symm x)).comp
          (fderiv ℝ sourceDiffeomorph.symm x)) := by
  have hF : ContDiff ℝ ∞ (map β.value t) :=
    (contDiff_map β.smooth).comp
      (show ContDiff ℝ ∞ (fun y : Vector 3 ↦ (t, y)) from contDiff_const.prodMk contDiff_id)
  have hS := sourceDiffeomorph.symm.contMDiff.contDiff.differentiable (by simp) x
  have hD := hF.differentiable (by simp) (sourceDiffeomorph.symm x)
  have hT := targetDiffeomorph.contMDiff.contDiff.differentiable (by simp)
    (map β.value t (sourceDiffeomorph.symm x))
  change fderiv ℝ (targetDiffeomorph ∘ ((map β.value t) ∘ sourceDiffeomorph.symm)) x = _
  rw [fderiv_comp x hT (hD.comp x hS), fderiv_comp x hD hS]
  rfl

theorem surjective_longMap_endpoint_tangent_sum (β : Cutoff) (x y : Vector 3)
    (hne : x ≠ y) (heq : longMap β 1 x = longMap β 1 y) :
    Surjective ((fderiv ℝ (longMap β 1) x).coprod (fderiv ℝ (longMap β 1) y)) := by
  let u := sourceDiffeomorph.symm x
  let v := sourceDiffeomorph.symm y
  have huv : u ≠ v := fun h ↦ hne (sourceDiffeomorph.symm.injective h)
  have he : map β.value 1 u = map β.value 1 v := targetDiffeomorph.injective heq
  have hbase := surjective_endpoint_tangent_sum β u v huv he
  have hS (z : Vector 3) : Surjective (fderiv ℝ sourceDiffeomorph.symm z) := by
    have h := (sourceDiffeomorph.symm.mfderivToContinuousLinearEquiv (by simp) z).surjective
    change Surjective (mfderiv 𝓘(ℝ, Vector 3) 𝓘(ℝ, Vector 3) sourceDiffeomorph.symm z) at h
    rwa [mfderiv_eq_fderiv] at h
  have hT : Surjective (fderiv ℝ targetDiffeomorph (map β.value 1 v)) := by
    have h := (targetDiffeomorph.mfderivToContinuousLinearEquiv (by simp)
      (map β.value 1 v)).surjective
    change Surjective (mfderiv 𝓘(ℝ, Vector 6) 𝓘(ℝ, Vector 6)
      targetDiffeomorph (map β.value 1 v)) at h
    rwa [mfderiv_eq_fderiv] at h
  rw [fderiv_longMap, fderiv_longMap]
  change Surjective
    (((fderiv ℝ targetDiffeomorph (map β.value 1 u)).comp
      ((fderiv ℝ (map β.value 1) u).comp (fderiv ℝ sourceDiffeomorph.symm x))).coprod
    ((fderiv ℝ targetDiffeomorph (map β.value 1 v)).comp
      ((fderiv ℝ (map β.value 1) v).comp (fderiv ℝ sourceDiffeomorph.symm y))))
  rw [he]
  intro w
  obtain ⟨w', hw⟩ := hT w
  obtain ⟨⟨vx, vy⟩, hv⟩ := hbase w'
  obtain ⟨a, ha⟩ := hS x vx
  obtain ⟨b, hb⟩ := hS y vy
  change fderiv ℝ (map β.value 1) u vx + fderiv ℝ (map β.value 1) v vy = w' at hv
  refine ⟨(a, b), ?_⟩
  change fderiv ℝ targetDiffeomorph (map β.value 1 v)
      (fderiv ℝ (map β.value 1) u (fderiv ℝ sourceDiffeomorph.symm x a)) +
    fderiv ℝ targetDiffeomorph (map β.value 1 v)
      (fderiv ℝ (map β.value 1) v (fderiv ℝ sourceDiffeomorph.symm y b)) = w
  rw [ha, hb, ← map_add, hv, hw]

theorem isCompact_longMap_trace (β : Cutoff) :
    IsCompact ((uncurry (longMap β)) '' (Icc (-1 : ℝ) 1 ×ˢ longSupport β)) :=
  (isCompact_Icc.prod (isCompact_longSupport β)).image (contDiff_longMap β).continuous

end Wikipedia.HopfProblem.DegreeCollapse.SupportedCusp
