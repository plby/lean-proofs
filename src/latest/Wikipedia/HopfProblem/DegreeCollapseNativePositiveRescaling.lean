import Wikipedia.HopfProblem.DegreeCollapseLocalFunctionReplacement
import Wikipedia.SmoothSixDPoincare.PartialChartVectorField

/-!
# A compact positive coordinate speed change rescales the original native field

The actual scalar multiplier is globally smooth, strictly positive, and
identically one in every exterior germ. Its native field has the exact
prescribed coordinate speed. Positivity retains all zeros and every strict
descent inequality without imposing any scalar height chart.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

variable {E B M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace M] [ChartedSpace B M]

/-- A purely vertical coordinate field pulls back to the corresponding scalar native field. -/
theorem partialChartField_vertical_factor
    (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞)
    (W : (E × ℝ) → E × ℝ) (hbase : ∀ p, (W p).1 = 0) (x : M) :
    FlowConstruction.partialChartField Φ.symm W x =
      (W (Φ.symm x)).2 •
        FlowConstruction.partialChartField Φ.symm (fun _ : E × ℝ => (0, 1)) x := by
  have hw (p : E × ℝ) : W p = (W p).2 • ((0 : E), (1 : ℝ)) := by
    apply Prod.ext
    · simpa only [Prod.smul_fst, smul_zero] using hbase p
    · simp only [Prod.smul_snd, smul_eq_mul, mul_one]
  unfold FlowConstruction.partialChartField
  rw [VectorField.mpullback_apply, VectorField.mpullback_apply]
  conv_lhs => rw [hw]
  rw [map_smul, map_smul]

variable [T2Space M] [IsManifold 𝓘(ℝ, B) ∞ M]

/-- Construct a globally positive native multiplier realizing a compact
coordinate speed change, with every exterior multiplier germ exactly one. -/
theorem exists_native_positive_cylinder_rescaling
    (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞)
    (V : (x : M) → TangentSpace 𝓘(ℝ, B) x)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (hmodel : ∀ x ∈ Φ.target, V x =
      FlowConstruction.partialChartField Φ.symm (fun _ : E × ℝ => (0, 1)) x)
    (W : (E × ℝ) → E × ℝ) (hW : ContDiff ℝ ∞ W)
    (hbase : ∀ p, (W p).1 = 0) (hpos : ∀ p, 0 < (W p).2)
    {C : Set (E × ℝ)} (hC : IsCompact C) (hCsource : C ⊆ Φ.source)
    (hfix : ∀ p ∉ C, W p = (0, 1)) :
    ∃ ρ : M → ℝ, ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, ℝ) ∞ ρ ∧ (∀ x, 0 < ρ x) ∧
      ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞
        (fun x => (⟨x, ρ x • V x⟩ : TangentBundle 𝓘(ℝ, B) M)) ∧
      (∀ x ∈ Φ.target, ρ x • V x = FlowConstruction.partialChartField Φ.symm W x) ∧
      (∀ x, ρ x • V x = 0 ↔ V x = 0) ∧
      (∀ (f : M → ℝ) x, mvfderiv 𝓘(ℝ, B) f x (V x) < 0 →
        mvfderiv 𝓘(ℝ, B) f x (ρ x • V x) < 0) ∧
      ∀ x ∉ Φ '' C, ∀ᶠ y in 𝓝 x, ρ y = 1 := by
  let w (p : E × ℝ) := (W p).2
  let ρ := LocalFunctionReplacement.replace Φ (fun _ : M => 1) w
  have hw : ContDiff ℝ ∞ w := hW.snd
  have hwfix (p : E × ℝ) (hp : p ∉ C) : w p = 1 := by
    change (W p).2 = 1
    rw [hfix p hp]
  have hρ : ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, ℝ) ∞ ρ :=
    LocalFunctionReplacement.contMDiff_replace Φ contMDiff_const hw hC hCsource
      (fun _ _ => rfl) hwfix
  have hρpos (x : M) : 0 < ρ x := by
    change 0 < LocalFunctionReplacement.replace Φ (fun _ : M => 1) w x
    by_cases hx : x ∈ Φ.target
    · rw [LocalFunctionReplacement.replace_of_mem Φ (fun _ => 1) w hx]
      exact hpos _
    · rw [LocalFunctionReplacement.replace_of_notMem Φ (fun _ => 1) w hx]
      exact zero_lt_one
  refine ⟨ρ, hρ, hρpos, hρ.smul_section hV, ?_, ?_, ?_, ?_⟩
  · intro x hx
    change LocalFunctionReplacement.replace Φ (fun _ : M => 1) w x • V x = _
    rw [LocalFunctionReplacement.replace_of_mem Φ (fun _ => 1) w hx, hmodel x hx,
      partialChartField_vertical_factor Φ W hbase x]
  · intro x
    exact smul_eq_zero.trans (or_iff_right (hρpos x).ne')
  · intro f x hx
    rw [map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (hρpos x) hx
  · intro x hx
    exact LocalFunctionReplacement.replace_germ_off_support Φ hC hCsource
      (fun _ _ => rfl) hwfix hx

end Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange
