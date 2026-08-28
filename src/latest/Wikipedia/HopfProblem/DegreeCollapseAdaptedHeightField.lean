import Wikipedia.SmoothSixDPoincare.RegularBandHeight
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Height normalization of a supplied descending field

The field is rescaled, not replaced by unrelated local directions. A smooth
cutoff supported in the regular locus removes the apparent singularity at
critical points. On its unit plateau the exact field is `V / df(V)`.
-/

noncomputable section

open Set Manifold Filter
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare
open Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- The actual directional derivative of a smooth function along a smooth field is smooth. -/
theorem contMDiff_directionalDerivative
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (fun x => mvfderiv 𝓘(ℝ, E) f x (V x)) := by
  have ht := (hf.contMDiff_tangentMap (m := ∞) (by simp)).comp hV
  exact (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp ht

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- A quotient with numerator supported where the denominator is nonzero is globally smooth. -/
theorem contMDiff_supported_division {χ D : M → ℝ}
    (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ χ)
    (hD : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ D)
    (hsupp : ∀ x ∈ tsupport χ, D x ≠ 0) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun x => χ x / D x) := by
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact (hχ x).div₀ (hD x) (hsupp x hx)
  · apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
    simp only [image_eq_zero_of_notMem_tsupport hy, zero_div]

/-- Rescaling a given field retains its direction and gives exactly the desired height speed. -/
theorem exists_rescaled_height_field
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    {χ : M → ℝ} (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ χ)
    (hsupp : ∀ x ∈ tsupport χ, mvfderiv 𝓘(ℝ, E) f x (V x) ≠ 0) :
    ∃ W : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ x, W x = (χ x / mvfderiv 𝓘(ℝ, E) f x (V x)) • V x) ∧
      (∀ x, mvfderiv 𝓘(ℝ, E) f x (W x) = χ x) ∧
      ∀ x, x ∉ tsupport χ → W x = 0 := by
  let D (x : M) := mvfderiv 𝓘(ℝ, E) f x (V x)
  let W : (x : M) → TangentSpace 𝓘(ℝ, E) x := fun x => (χ x / D x) • V x
  refine ⟨W, (contMDiff_supported_division hχ
    (contMDiff_directionalDerivative hf hV) hsupp).smul_section hV,
    fun _ => rfl, ?_, ?_⟩
  · intro x
    change mvfderiv 𝓘(ℝ, E) f x ((χ x / D x) • V x) = χ x
    rw [map_smul, smul_eq_mul]
    change χ x / D x * D x = χ x
    by_cases hx : x ∈ tsupport χ
    · exact div_mul_cancel₀ _ (hsupp x hx)
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_div, zero_mul]
  · intro x hx
    simp only [W, image_eq_zero_of_notMem_tsupport hx, zero_div, zero_smul]

variable [CompactSpace M]

/-- Normalize the supplied descending field on a regular band, preserving its exact direction. -/
theorem exists_adapted_height_field
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ x, x ∉ ManifoldMorse.criticalPoints E f →
      mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {a b : ℝ}
    (hband : ∀ x, f x ∈ Icc a b → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ (φ : ℝ → ℝ) (U : Set ℝ), ContDiff ℝ ∞ φ ∧ IsOpen U ∧ Icc a b ⊆ U ∧
      EqOn φ (fun _ => 1) U ∧
      ∃ W : (x : M) → TangentSpace 𝓘(ℝ, E) x,
        ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
          (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ x, W x = (φ (f x) / mvfderiv 𝓘(ℝ, E) f x (V x)) • V x) ∧
        (∀ x, mvfderiv 𝓘(ℝ, E) f x (W x) = φ (f x)) ∧
        (∀ x ∈ ManifoldMorse.criticalPoints E f, W x = 0) ∧
        ∀ x, f x ∈ U → W x = (mvfderiv 𝓘(ℝ, E) f x (V x))⁻¹ • V x := by
  let B := f '' ManifoldMorse.criticalPoints E f
  have hB : IsClosed B :=
    ((ManifoldMorse.criticalPoints_isClosed hf).isCompact.image hf.continuous).isClosed
  have hAB : Icc a b ⊆ Bᶜ := by
    intro y hy
    rintro ⟨x, hx, rfl⟩
    exact hband x hy hx
  obtain ⟨φ, hφ, hφB, U, hU, hAU, -, hφU⟩ :=
    exists_smooth_cutoff_near_closed isClosed_Icc hB.isOpen_compl hAB
  have hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (φ ∘ f) := hφ.contMDiff.comp hf
  have hsupp : tsupport (φ ∘ f) ⊆ (ManifoldMorse.criticalPoints E f)ᶜ := by
    intro x hx hcrit
    exact hφB (tsupport_comp_subset_preimage φ hf.continuous hx) ⟨x, hcrit, rfl⟩
  obtain ⟨W, hW, hWeq, hspeed, hzero⟩ := exists_rescaled_height_field hf hV hχ
    (fun x hx => (hdesc x (hsupp hx)).ne)
  refine ⟨φ, U, hφ, hU, hAU, hφU, W, hW, hWeq, hspeed, ?_, ?_⟩
  · intro x hx
    exact hzero x (fun h => hsupp h hx)
  · intro x hx
    rw [hWeq x]
    simp only [Function.comp_apply, hφU hx, one_div]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
