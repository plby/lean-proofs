import Wikipedia.HopfProblem.DegreeCollapseLocalFieldReplacement
import Wikipedia.HopfProblem.DegreeCollapseNativeCubicFieldCancellation

/-!
# A compact vertical-field perturbation on the full native cylinder

The coordinate height component stays one, so the replacement has no
zeros anywhere in the whole chart. Compact support gives a global smooth
field retaining every exterior germ and exactly the old zero set. No
global scalar height chart is required.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {E B M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [TopologicalSpace M] [ChartedSpace B M] [T2Space M] [IsManifold 𝓘(ℝ, B) ∞ M]

/-- A compact perturbation with vertical speed one gives a full-chart native replacement. -/
theorem exists_native_vertical_field_replacement
    (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, B) x)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (hmodel : ∀ x ∈ Φ.target, V x =
      FlowConstruction.partialChartField Φ.symm (fun _ : E × ℝ => (0, 1)) x)
    {W : (E × ℝ) → E × ℝ} (hW : ContDiff ℝ ∞ W) (hWheight : ∀ p, (W p).2 = 1)
    {K : Set (E × ℝ)} (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hfix : ∀ p ∉ K, W p = (0, 1)) :
    ∃ V' : (x : M) → TangentSpace 𝓘(ℝ, B) x,
      ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞
        (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, B) M)) ∧
      (∀ x ∈ Φ.target, V' x = FlowConstruction.partialChartField Φ.symm W x) ∧
      (∀ x, V' x = 0 ↔ V x = 0) ∧
      ∀ x ∉ Φ '' K, ∀ᶠ y in 𝓝 x, V' y = V y := by
  let Wn := FlowConstruction.partialChartField Φ.symm W
  have hWn : ContMDiffOn 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞
      (fun x => (⟨x, Wn x⟩ : TangentBundle 𝓘(ℝ, B) M)) Φ.target :=
    FlowConstruction.contMDiffOn_partialChartField Φ.symm hW
  have hreg (x : M) (hx : x ∈ Φ.target) : Wn x ≠ 0 := by
    intro hz
    have hWzero := (MorseCancellation.partialChartField_zero_iff Φ W hx).mp hz
    have hh := congrArg Prod.snd hWzero
    rw [hWheight] at hh
    exact one_ne_zero hh
  have hregV (x : M) (hx : x ∈ Φ.target) : V x ≠ 0 := by
    rw [hmodel x hx]
    intro hz
    have hh := (MorseCancellation.partialChartField_zero_iff Φ
      (fun _ : E × ℝ => (0, 1)) hx).mp hz
    exact one_ne_zero (congrArg Prod.snd hh)
  have hkeep (x : M) (hx : x ∈ Φ.target) (hnot : x ∉ Φ '' K) : Wn x = V x := by
    have hz : Φ.symm x ∉ K := fun h => hnot ⟨Φ.symm x, h, Φ.right_inv' hx⟩
    rw [hmodel x hx]
    change FlowConstruction.partialChartField Φ.symm W x = _
    unfold FlowConstruction.partialChartField
    rw [VectorField.mpullback_apply, VectorField.mpullback_apply, hfix _ hz]
  obtain ⟨V', hV', hnew, hzeros, hgerm⟩ :=
    LocalFieldReplacement.exists_smooth_field_replacement Φ V Wn hV hWn hK hKΦ hkeep hreg
  refine ⟨V', hV', hnew, ?_, hgerm⟩
  intro x
  exact (hzeros x).trans ⟨And.left, fun hx => ⟨hx, fun ht => hregV x ht hx⟩⟩

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
