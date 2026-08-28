import Wikipedia.SmoothSixDPoincare.SmallLipschitzGerm
import Wikipedia.SmoothSixDPoincare.AmbientIsotopy

/-!
# Supported native isotopies realizing coordinate germs tangent to the identity

Subtract the identity, extend the resulting zero-derivative displacement with
Lipschitz constant one half, and interpolate using a smooth time cutoff. Every
slice has a proved global smooth inverse. The pointwise scalar displacement
formula retains the original fixed points and linear coordinate constraints.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold NNReal

namespace Wikipedia.SmoothSixDPoincare.SmallPerturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A smooth germ tangent to the identity has a supported isotopy with actual native inverses. -/
theorem exists_supported_tangent_identity_isotopy {f : E → E} {U : Set E}
    (hU : IsOpen U) (hzero : (0 : E) ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hf₀ : f 0 = 0) (hdf : fderiv ℝ f 0 = ContinuousLinearMap.id ℝ E) :
    ∃ (A : ℝ × E → E) (K : Set E),
      IsCompact K ∧ K ⊆ U ∧ ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
      (∀ x, A (0, x) = x) ∧
      (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, D x = A (t, x)) ∧
      (∀ t x, x ∉ K → A (t, x) = x) ∧
      (∀ t x, ∃ c ∈ Icc (0 : ℝ) 1, A (t, x) = x + c • (f x - x)) ∧
      (fun x => A (1, x)) =ᶠ[𝓝 (0 : E)] f := by
  let u : E → E := fun x => f x - x
  have hu : ContDiffOn ℝ ∞ u U := hf.sub contDiffOn_id
  have hu₀ : u 0 = 0 := by simp [u, hf₀]
  have hdu : fderiv ℝ u 0 = 0 := by
    have hdiff : DifferentiableAt ℝ f 0 :=
      (hf.contDiffAt (hU.mem_nhds hzero)).differentiableAt (by simp)
    change fderiv ℝ (f - id) 0 = 0
    rw [fderiv_sub hdiff differentiableAt_id, hdf, fderiv_id, sub_self]
  obtain ⟨w, hw, hwcompact, hwsupport, hwlip, hweq, hwscalar⟩ :=
    exists_lipschitz_supported_germ hU hzero hu hu₀ hdu
      (show (0 : ℝ≥0) < 1 / 2 by norm_num)
  let A : ℝ × E → E := fun p => p.2 + Real.smoothTransition p.1 • w p.2
  have hθ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := ⊤)).contMDiff
  have hA : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A :=
    contMDiff_snd.add ((hθ.comp contMDiff_fst).smul (hw.contMDiff.comp contMDiff_snd))
  refine ⟨A, tsupport w, hwcompact.isCompact, hwsupport, hA, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp [A, Real.smoothTransition.zero]
  · intro t
    have hs : ContDiff ℝ ∞ (fun x => Real.smoothTransition t • w x) :=
      contDiff_const.smul hw
    have hlip : LipschitzWith (‖Real.smoothTransition t‖₊ * (1 / 2))
        (fun x => Real.smoothTransition t • w x) :=
      (lipschitzWith_smul (Real.smoothTransition t)).comp hwlip
    have hθnorm : ‖Real.smoothTransition t‖₊ ≤ 1 := by
      change ‖Real.smoothTransition t‖ ≤ (1 : ℝ)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg t)]
      exact Real.smoothTransition.le_one t
    have hsmall : ‖Real.smoothTransition t‖₊ * (1 / 2 : ℝ≥0) < 1 := by
      calc
        _ ≤ 1 * (1 / 2 : ℝ≥0) := mul_le_mul_of_nonneg_right hθnorm (by positivity)
        _ < 1 := by norm_num
    exact ⟨diffeomorphIdAdd hs hlip hsmall, fun _ => rfl⟩
  · intro t x hx
    have hz : w x = 0 := by
      by_contra hne
      exact hx (subset_tsupport w hne)
    simp only [A, hz, smul_zero, add_zero]
  · intro t x
    obtain ⟨c, hc, hwc⟩ := hwscalar x
    refine ⟨Real.smoothTransition t * c, ⟨mul_nonneg (Real.smoothTransition.nonneg t) hc.1,
      (mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one t) hc.1).trans
        (by simpa only [one_mul] using hc.2)⟩, ?_⟩
    change x + Real.smoothTransition t • w x = x + _
    rw [hwc, smul_smul]
  · filter_upwards [hweq] with x hx
    change x + Real.smoothTransition 1 • w x = f x
    rw [Real.smoothTransition.one, one_smul, hx]
    change x + (f x - x) = f x
    abel

/-- The germ is realized by a compactly supported diffeomorphism isotopic to the identity. -/
theorem exists_supported_tangent_identity_diffeomorph {f : E → E} {U : Set E}
    (hU : IsOpen U) (hzero : (0 : E) ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hf₀ : f 0 = 0) (hdf : fderiv ℝ f 0 = ContinuousLinearMap.id ℝ E) :
    ∃ (D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (K : Set E),
      IsCompact K ∧ K ⊆ U ∧ SupportedDiffeomorph.IsotopicToIdentity D ∧
      (∀ x ∉ K, D x = x) ∧
      (∀ x, ∃ c ∈ Icc (0 : ℝ) 1, D x = x + c • (f x - x)) ∧
      (D : E → E) =ᶠ[𝓝 (0 : E)] f := by
  obtain ⟨A, K, hK, hKU, hA, hA₀, hdiff, hfix, hscalar, hgerm⟩ :=
    exists_supported_tangent_identity_isotopy hU hzero hf hf₀ hdf
  obtain ⟨D, hD⟩ := hdiff 1
  have hiso : SupportedDiffeomorph.IsotopicToIdentity D := by
    refine ⟨A, hA, hA₀, fun x => (hD x).symm, ?_⟩
    intro t
    obtain ⟨e, he⟩ := hdiff t
    exact ⟨e, fun x => (he x).symm⟩
  refine ⟨D, K, hK, hKU, hiso, fun x hx => (hD x).trans (hfix 1 x hx), ?_, ?_⟩
  · intro x
    rw [hD]
    exact hscalar 1 x
  · filter_upwards [hgerm] with x hx
    exact (hD x).trans hx

end Wikipedia.SmoothSixDPoincare.SmallPerturbation
