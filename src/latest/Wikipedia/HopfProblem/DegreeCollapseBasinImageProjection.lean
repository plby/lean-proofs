import Wikipedia.HopfProblem.DegreeCollapseNativeLevelBasinTransport
import Wikipedia.SmoothSixDPoincare.OpenObstacleRestriction

/-!
# Project an actual invariant smooth image to the native regular level

Restrict the obstacle's source to the genuine level-crossing basin and
use the original whole flow cylinder. The projected map keeps the source
dimension and has image exactly the original invariant set on that level.
No parametrization of the level section is supplied as a hypothesis.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap TopologicalSpace
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M G H Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace Y] [ChartedSpace H Y]

omit [T2Space M] in
theorem AdaptedSurgeryWindows.exists_native_level_image_of_invariant
    (A : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {b : ℝ} (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    (z₀ : {y : M // f y = b}) (W : Set M)
    (g : C(Y, M)) (hg : ContMDiff J 𝓘(ℝ, E) ∞ g) (hrange : range g = W)
    (hinvariant : ∀ t x, A.flow t x ∈ W ↔ x ∈ W) :
    let _ := RegularLevel.chartedSpace hf hb
    ∃ U : Opens Y, ∃ h : C(U, {y : M // f y = b}),
      ContMDiff J 𝓘(ℝ, RegularLevel.Model E) ∞ h ∧
      range h = {y | y.val ∈ W} := by
  let _ := RegularLevel.chartedSpace hf hb
  let _ := RegularLevel.isManifold hf hb
  obtain ⟨Φ, hsource, _, hformula, _⟩ := FlowCancellation.exists_native_level_flow_cylinder
    hf hb A.smooth A.flow A.integral (fun y hy => A.descent y (hb y hy)) z₀
  let U : Opens Y := ⟨g ⁻¹' Φ.target, Φ.open_target.preimage g.continuous⟩
  have hmaps : MapsTo (fun u : U => g u.val) univ Φ.target := fun u _ => u.property
  have hG : ContMDiff J 𝓘(ℝ, E) ∞ (fun u : U => g u.val) :=
    hg.comp contMDiff_subtype_val
  have hh : ContMDiff J 𝓘(ℝ, RegularLevel.Model E) ∞
      (fun u : U => (Φ.symm (g u.val)).1) :=
    contMDiff_fst.comp (Φ.contMDiffOn_invFun.comp_contMDiff hG (fun u => hmaps (mem_univ u)))
  let h : C(U, {y : M // f y = b}) := ⟨_, hh.continuous⟩
  refine ⟨U, h, hh, ?_⟩
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    have hgu : g u.val ∈ W := hrange ▸ mem_range_self u.val
    have he : A.flow (Φ.symm (g u.val)).2 (h u).val = g u.val :=
      (hformula (Φ.symm (g u.val))).symm.trans (Φ.right_inv' u.property)
    exact (hinvariant _ _).mp (he.symm ▸ hgu)
  · intro hx
    obtain ⟨y, hy⟩ := hrange.symm ▸ hx
    have hxs : (x, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; trivial
    have hzero : Φ (x, (0 : ℝ)) = x.val := by rw [hformula, A.flow.map_zero_apply]
    have hxt : x.val ∈ Φ.target := hzero ▸ Φ.map_source' hxs
    have hyU : y ∈ U := by
      change g y ∈ Φ.target
      rwa [hy]
    refine ⟨⟨y, hyU⟩, ?_⟩
    change (Φ.symm (g y)).1 = x
    rw [hy, ← hzero]
    exact congrArg Prod.fst (Φ.left_inv' hxs)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
