import Wikipedia.HopfProblem.DegreeCollapseAdaptedHeightField
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Positive height normalization with unchanged critical germs

A cutoff interpolates between speed one and the reciprocal descending
height speed. The multiplier stays strictly positive everywhere, equals
one off the regular support, and gives height speed minus one on the
plateau. Thus no zero or direction of the original field is lost.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare
open Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- A bounded regular cutoff constructs a strictly positive height rescaling. -/
theorem exists_positive_height_rescaling
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    {χ : M → ℝ} (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ χ)
    (hχrange : ∀ x, χ x ∈ Icc (0 : ℝ) 1)
    (hdesc : ∀ x ∈ tsupport χ, mvfderiv 𝓘(ℝ, E) f x (V x) < 0) :
    ∃ ρ : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ ∧ (∀ x, 0 < ρ x) ∧
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun x => (⟨x, ρ x • V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ x, ρ x • V x = 0 ↔ V x = 0) ∧
      (∀ x, mvfderiv 𝓘(ℝ, E) f x (V x) < 0 →
        mvfderiv 𝓘(ℝ, E) f x (ρ x • V x) < 0) ∧
      (∀ x, χ x = 1 → mvfderiv 𝓘(ℝ, E) f x (ρ x • V x) = -1) ∧
      ∀ x ∉ tsupport χ, ∀ᶠ y in 𝓝 x, ρ y = 1 := by
  let D (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  let ρ (x : M) := 1 - χ x + χ x / (-D x)
  have hD : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ D := contMDiff_directionalDerivative hf hV
  have hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ :=
    (contMDiff_const.sub hχ).add
      (contMDiff_supported_division hχ hD.neg (fun x hx => neg_ne_zero.mpr (hdesc x hx).ne))
  have hpos (x : M) : 0 < ρ x := by
    by_cases hx : x ∈ tsupport χ
    · have hdx : 0 < -D x := neg_pos.mpr (hdesc x hx)
      by_cases he : χ x = 1
      · simpa only [ρ, he, sub_self, zero_add] using one_div_pos.mpr hdx
      · exact add_pos_of_pos_of_nonneg
          (sub_pos.mpr (lt_of_le_of_ne (hχrange x).2 he))
          (div_nonneg (hχrange x).1 hdx.le)
    · simp only [ρ, image_eq_zero_of_notMem_tsupport hx, sub_zero, zero_div, add_zero]
      exact zero_lt_one
  refine ⟨ρ, hρ, hpos, hρ.smul_section hV, ?_, ?_, ?_, ?_⟩
  · intro x
    exact smul_eq_zero.trans (or_iff_right (hpos x).ne')
  · intro x hx
    rw [map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (hpos x) hx
  · intro x hx
    have hs : x ∈ tsupport χ := subset_tsupport χ (by simp [mem_support, hx])
    have hd : D x ≠ 0 := (hdesc x hs).ne
    rw [map_smul, smul_eq_mul]
    change (1 - χ x + χ x / (-D x)) * D x = -1
    rw [hx]
    field_simp
    ring
  · intro x hx
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
    simp only [ρ, image_eq_zero_of_notMem_tsupport hy, sub_zero, zero_div, add_zero]

variable [CompactSpace M]

/-- A regular closed height band constructs its positive normalization,
retaining the full multiplier germ one at every original critical point. -/
theorem exists_positive_band_normalization
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f →
      mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {a b : ℝ} (hband : ∀ x, f x ∈ Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ (ρ : M → ℝ) (U : Set ℝ), IsOpen U ∧ Icc a b ⊆ U ∧
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ ∧ (∀ x, 0 < ρ x) ∧
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun x => (⟨x, ρ x • V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ x, ρ x • V x = 0 ↔ V x = 0) ∧
      (∀ x, x ∉ ManifoldMorse.criticalPoints E f →
        mvfderiv 𝓘(ℝ, E) f x (ρ x • V x) < 0) ∧
      (∀ x, f x ∈ U → mvfderiv 𝓘(ℝ, E) f x (ρ x • V x) = -1) ∧
      ∀ x ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 x, ρ y = 1 := by
  let B := f '' ManifoldMorse.criticalPoints E f
  have hB : IsClosed B :=
    ((ManifoldMorse.criticalPoints_isClosed hf).isCompact.image hf.continuous).isClosed
  have hAB : Icc a b ⊆ Bᶜ := by
    rintro y hy ⟨x, hx, rfl⟩
    exact hband x hy hx
  obtain ⟨φ, hφ, hsupp, U, hU, hAU, -, hφU⟩ :=
    exists_smooth_cutoff_near_closed isClosed_Icc hB.isOpen_compl hAB
  let χ := Real.smoothTransition ∘ φ ∘ f
  have hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ χ :=
    (Real.smoothTransition.contDiff.comp hφ).contMDiff.comp hf
  have hχsupport : tsupport χ ⊆ (ManifoldMorse.criticalPoints E f)ᶜ := by
    intro x hx hcrit
    have hp := tsupport_comp_subset Real.smoothTransition.zero (φ ∘ f) hx
    exact hsupp (tsupport_comp_subset_preimage φ hf.continuous hp) ⟨x, hcrit, rfl⟩
  obtain ⟨ρ, hρ, hpos, hW, hzero, hneg, hspeed, hgerm⟩ :=
    exists_positive_height_rescaling hf hV hχ
      (fun x => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩)
      (fun x hx => hdesc x (hχsupport hx))
  refine ⟨ρ, U, hU, hAU, hρ, hpos, hW, hzero, fun x hx => hneg x (hdesc x hx), ?_, ?_⟩
  · intro x hx
    apply hspeed
    simp only [χ, comp_apply, hφU hx, Real.smoothTransition.one]
  · intro x hx
    exact hgerm x (fun h => hχsupport h hx)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
