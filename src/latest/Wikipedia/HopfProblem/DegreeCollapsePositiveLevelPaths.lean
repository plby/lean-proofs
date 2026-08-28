import Wikipedia.HopfProblem.DegreeCollapsePositiveLevelAvoidance
import Wikipedia.HopfProblem.DegreeCollapseRegularLevelPaths

/-!
# Actual regular-level connectedness above an untouched lower cut

Paths are taken in the original strict superlevel, moved off its full
restricted endpoint obstruction, and projected by the original native
flow cylinder. Both endpoints stay fixed. Only critical points strictly
above the lower cut need low-endpoint dimension bounds.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap TopologicalSpace
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.pathConnectedSpace_regular_level_above_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {b a : ℝ} (U : Opens M) [PathConnectedSpace U]
    (hU : ∀ x, x ∈ U ↔ b < f x) (hba : b < a)
    (hreg : ∀ y, f y = a → y ∉ criticalPoints E f) {d : ℕ}
    (hhigh : ∀ p : criticalPoints E f, a ≤ f p →
      Module.finrank ℝ E - nativeMorseIndex E f p ≤ d)
    (hlow : ∀ p : criticalPoints E f, b < f p → f p ≤ a → nativeMorseIndex E f p ≤ d)
    (hdim : 1 + d < Module.finrank ℝ E) (z₀ : {z : M // f z = a}) :
    PathConnectedSpace {z : M // f z = a} := by
  let _ := S.finite.fintype
  let J := EndpointBasinIndexAbove S b a
  let Z := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin d)
  let _ : Countable J := endpointBasinIndexAbove_countable S b a
  let _ : DiscreteTopology J := inferInstance
  let _ : ChartedSpace Z J := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold 𝓘(ℝ, Z) ∞ J := IsManifold.of_discreteTopology ∞
  obtain ⟨gB, hgB, hcover⟩ :=
    S.exists_endpoint_obstruction_images_above_cut hf b a hhigh hlow
  have hs : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞
      (fun p : J × V => gB p.1 p.2) := contMDiff_discrete_family gB hgB
  let B : C(J × V, M) := ⟨fun p => gB p.1 p.2, hs.continuous⟩
  have hrangeB : range B = ⋃ i, range (gB i) := range_discrete_family gB
  let R := OpenObstacle.restrict B U
  have hrange : range R =
      (Subtype.val : U → M) ⁻¹' (FlowCancellation.levelBasin S.flow f a)ᶜ := by
    rw [OpenObstacle.range_restrict, hrangeB,
      levelBasin_compl_eq_endpoint_obstruction S hf hreg]
    ext x
    exact (hcover x.val ((hU x.val).mp x.property)).symm
  have hclosed : IsClosed (range R) := by
    rw [hrange, levelBasin_compl_eq_endpoint_obstruction S hf hreg]
    exact (isClosed_endpoint_obstruction S hf a).preimage continuous_subtype_val
  have hdim' : 1 + Module.finrank ℝ (Z × V) < Module.finrank ℝ E := by
    simpa only [Z, V, Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hdim
  let _ := RegularLevel.chartedSpace hf hreg
  obtain ⟨Φ, hsource, htarget, hformula, _⟩ := FlowCancellation.exists_native_level_flow_cylinder
    hf hreg S.smooth S.flow S.integral (fun z hz => S.descent z (hreg z hz)) z₀
  have hinverse (z : {w : M // f w = a}) : Φ.symm z.val = (z, 0) := by
    have hz : (z, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; trivial
    have he : Φ (z, 0) = z.val := by rw [hformula, S.flow.map_zero_apply]
    have hi : Φ.symm (Φ (z, 0)) = (z, 0) := Φ.left_inv' hz
    rwa [he] at hi
  refine ⟨⟨z₀⟩, ?_⟩
  intro x y
  let toU (z : {w : M // f w = a}) : U :=
    ⟨z.val, (hU z.val).mpr (by rw [z.property]; exact hba)⟩
  have hnot (z : {w : M // f w = a}) : toU z ∉ range R := by
    rw [hrange, mem_preimage, mem_compl_iff, not_not]
    exact ⟨0, by simpa only [S.flow.map_zero_apply] using z.property⟩
  obtain ⟨η, _, havoid⟩ := exists_smooth_path_avoiding_closed_image
    (PathConnectedSpace.somePath (toU x) (toU y)) R
    (OpenObstacle.contMDiff_restrict B U hs) hclosed hdim' (hnot x) (hnot y)
  have hcross (t : unitInterval) :
      (η t).val ∈ FlowCancellation.levelBasin S.flow f a := by
    simpa only [hrange, mem_preimage, mem_compl_iff, not_not] using havoid t
  have hcont : Continuous (fun t : unitInterval => Φ.symm (η t).val) :=
    Φ.contMDiffOn_invFun.continuousOn.comp_continuous
      (continuous_subtype_val.comp η.continuous) (fun t => htarget.symm ▸ hcross t)
  let ξ : Path x y := {
    toFun := fun t => (Φ.symm (η t).val).1
    continuous_toFun := continuous_fst.comp hcont
    source' := by
      rw [η.source]
      exact congrArg Prod.fst (hinverse x)
    target' := by
      rw [η.target]
      exact congrArg Prod.fst (hinverse y) }
  exact ⟨ξ⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
