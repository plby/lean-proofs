import Wikipedia.HopfProblem.DegreeCollapseLocalFieldReplacement
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Compact field replacement through a genuine native model manifold

The source of the partial diffeomorphism may be a native regular-level
product, rather than a single vector-space chart. Its native derivative
transports smooth fields and detects zeros. Compact replacement retains
the old zero set and all exterior field germs.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {D E H X M : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
  {I : ModelWithCorners ℝ D H}
  [TopologicalSpace M] [ChartedSpace E M]

theorem native_model_pullback_zero_iff
    (e : PartialDiffeomorph 𝓘(ℝ, E) I M X ∞)
    (W : (z : X) → TangentSpace I z) {x : M} (hx : x ∈ e.source) :
    VectorField.mpullback 𝓘(ℝ, E) I e W x = 0 ↔ W (e x) = 0 := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) I :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  let L := he.mfderiv hx
  rw [VectorField.mpullback_apply]
  change L.toContinuousLinearMap.inverse (W (e x)) = 0 ↔ W (e x) = 0
  rw [ContinuousLinearMap.inverse_equiv]
  constructor
  · intro h
    exact L.symm.injective (h.trans (map_zero L.symm).symm)
  · intro h
    rw [h]
    exact map_zero L.symm

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold I ∞ X]

theorem contMDiffOn_native_model_pullback
    (e : PartialDiffeomorph 𝓘(ℝ, E) I M X ∞)
    (W : (z : X) → TangentSpace I z)
    (hW : ContMDiff I I.tangent ∞ (fun z => (⟨z, W z⟩ : TangentBundle I X))) :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, VectorField.mpullback 𝓘(ℝ, E) I e W x⟩ :
        TangentBundle 𝓘(ℝ, E) M)) e.source := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) I :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  intro x hx
  have hinv : (mfderiv 𝓘(ℝ, E) I e x).IsInvertible := ⟨he.mfderiv hx, rfl⟩
  exact ((hW (e x)).mpullback_vectorField_preimage
    (e.contMDiffOn_toFun.contMDiffAt (e.open_source.mem_nhds hx)) hinv (by simp)).contMDiffWithinAt

variable [T2Space M]

theorem exists_native_model_field_replacement
    (A : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞)
    (V : (y : M) → TangentSpace 𝓘(ℝ, E) y)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (W₀ W : (z : X) → TangentSpace I z)
    (hW : ContMDiff I I.tangent ∞ (fun z => (⟨z, W z⟩ : TangentBundle I X)))
    (hmodel : ∀ y ∈ A.target, V y = VectorField.mpullback 𝓘(ℝ, E) I A.symm W₀ y)
    (hregular₀ : ∀ z ∈ A.source, W₀ z ≠ 0) (hregular : ∀ z ∈ A.source, W z ≠ 0)
    {K : Set X} (hK : IsCompact K) (hKA : K ⊆ A.source)
    (hfix : ∀ z ∉ K, W z = W₀ z) :
    ∃ V' : (y : M) → TangentSpace 𝓘(ℝ, E) y,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun y => (⟨y, V' y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ y ∈ A.target, V' y = VectorField.mpullback 𝓘(ℝ, E) I A.symm W y) ∧
      (∀ y, V' y = 0 ↔ V y = 0) ∧
      ∀ y ∉ A '' K, ∀ᶠ z in 𝓝 y, V' z = V z := by
  let Wn := VectorField.mpullback 𝓘(ℝ, E) I A.symm W
  have hWn := contMDiffOn_native_model_pullback A.symm W hW
  have hreg (y : M) (hy : y ∈ A.target) : Wn y ≠ 0 :=
    fun h => hregular (A.symm y) (A.map_target' hy)
      ((native_model_pullback_zero_iff A.symm W hy).mp h)
  have hregV (y : M) (hy : y ∈ A.target) : V y ≠ 0 := by
    rw [hmodel y hy]
    exact fun h => hregular₀ (A.symm y) (A.map_target' hy)
      ((native_model_pullback_zero_iff A.symm W₀ hy).mp h)
  have hkeep (y : M) (hy : y ∈ A.target) (hout : y ∉ A '' K) : Wn y = V y := by
    have hn : A.symm y ∉ K := fun h => hout ⟨A.symm y, h, A.right_inv' hy⟩
    rw [hmodel y hy]
    change VectorField.mpullback 𝓘(ℝ, E) I A.symm W y =
      VectorField.mpullback 𝓘(ℝ, E) I A.symm W₀ y
    rw [VectorField.mpullback_apply, VectorField.mpullback_apply, hfix (A.symm y) hn]
  obtain ⟨V', hV', hnew, hzero, hgerm⟩ :=
    LocalFieldReplacement.exists_smooth_field_replacement A V Wn hV hWn hK hKA hkeep hreg
  refine ⟨V', hV', hnew, ?_, hgerm⟩
  intro y
  exact (hzero y).trans ⟨And.left, fun hy => ⟨hy, fun ht => hregV y ht hy⟩⟩

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
