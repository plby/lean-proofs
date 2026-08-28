import Wikipedia.HopfProblem.DegreeCollapseScaledPlaneKink

/-!
# Actual derivatives of the rescaled plane modification

Both scalar factors remain in the chain rule. Nonzero scaling preserves
injectivity and surjectivity of the native tangent sum at the new crossing.
-/

noncomputable section

open Function
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SupportedCusp

open NoExoticSixSphere.GLOrthonormalization

theorem fderiv_scaledMap (β : Cutoff) (ε t : ℝ) (x : Vector 3) :
    fderiv ℝ (scaledMap β ε t) x = ε •
      (fderiv ℝ (longMap β t) (ε⁻¹ • x)).comp
        (ε⁻¹ • ContinuousLinearMap.id ℝ (Vector 3)) := by
  have hs : ContDiff ℝ ∞ (longMap β t) :=
    (contDiff_longMap β).comp
      (show ContDiff ℝ ∞ (fun y : Vector 3 ↦ (t, y)) from contDiff_const.prodMk contDiff_id)
  have hL := (hs.differentiable (by simp) (ε⁻¹ • x)).hasFDerivAt
  have hS := (hasFDerivAt_id (𝕜 := ℝ) x).const_smul ε⁻¹
  exact ((hL.comp x hS).const_smul ε).fderiv

theorem injective_fderiv_scaledMap (β : Cutoff) {ε t : ℝ}
    (hε : ε ≠ 0) (ht : t ≠ 0) (x : Vector 3) :
    Injective (fderiv ℝ (scaledMap β ε t) x) := by
  rw [fderiv_scaledMap]
  intro v w hvw
  have hD : fderiv ℝ (longMap β t) (ε⁻¹ • x) (ε⁻¹ • v) =
      fderiv ℝ (longMap β t) (ε⁻¹ • x) (ε⁻¹ • w) := by
    have h := congrArg (fun y : Vector 6 ↦ ε⁻¹ • y) hvw
    change ε⁻¹ • (ε • fderiv ℝ (longMap β t) (ε⁻¹ • x) (ε⁻¹ • v)) =
      ε⁻¹ • (ε • fderiv ℝ (longMap β t) (ε⁻¹ • x) (ε⁻¹ • w)) at h
    simpa only [inv_smul_smul₀ hε] using h
  have hS := (injective_fderiv_longMap β ht (ε⁻¹ • x)) hD
  have h := congrArg (fun y : Vector 3 ↦ ε • y) hS
  simpa only [smul_inv_smul₀ hε] using h

theorem surjective_scaledMap_endpoint_tangent_sum (β : Cutoff) {ε : ℝ} (hε : ε ≠ 0)
    (x y : Vector 3) (hne : x ≠ y) (heq : scaledMap β ε 1 x = scaledMap β ε 1 y) :
    Surjective ((fderiv ℝ (scaledMap β ε 1) x).coprod (fderiv ℝ (scaledMap β ε 1) y)) := by
  have hne' : ε⁻¹ • x ≠ ε⁻¹ • y := by
    intro h
    apply hne
    have hh := congrArg (fun v : Vector 3 ↦ ε • v) h
    simpa only [smul_inv_smul₀ hε] using hh
  have heq' : longMap β 1 (ε⁻¹ • x) = longMap β 1 (ε⁻¹ • y) := by
    have h := congrArg (fun v : Vector 6 ↦ ε⁻¹ • v) heq
    simpa only [scaledMap, inv_smul_smul₀ hε] using h
  have hbase := surjective_longMap_endpoint_tangent_sum β _ _ hne' heq'
  rw [fderiv_scaledMap, fderiv_scaledMap]
  intro w
  obtain ⟨⟨vx, vy⟩, hv⟩ := hbase (ε⁻¹ • w)
  change fderiv ℝ (longMap β 1) (ε⁻¹ • x) vx +
    fderiv ℝ (longMap β 1) (ε⁻¹ • y) vy = ε⁻¹ • w at hv
  refine ⟨(ε • vx, ε • vy), ?_⟩
  change ε • fderiv ℝ (longMap β 1) (ε⁻¹ • x) (ε⁻¹ • (ε • vx)) +
    ε • fderiv ℝ (longMap β 1) (ε⁻¹ • y) (ε⁻¹ • (ε • vy)) = w
  rw [inv_smul_smul₀ hε, inv_smul_smul₀ hε, ← smul_add, hv, smul_inv_smul₀ hε]

end Wikipedia.HopfProblem.DegreeCollapse.SupportedCusp
