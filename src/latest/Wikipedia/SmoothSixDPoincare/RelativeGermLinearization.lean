import Wikipedia.SmoothSixDPoincare.GermDerivativeConstraints

/-!
# Relative linearization of a local coordinate change

The linear frame is the actual derivative of the original map. Its fixed
subspace and normal projection laws are derived from the original germ.
After dividing out this frame, a constructed supported diffeomorphism realizes
the remaining tangent-to-identity germ, retaining both constraints globally.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SmallPerturbation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The coordinate germ is its actual derivative composed with a supported relative change. -/
theorem exists_relative_germ_linearization_isotopy {f : E → E} {U : Set E}
    (hU : IsOpen U) (hzero : (0 : E) ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hf₀ : f 0 = 0) (hdf : Bijective (fderiv ℝ f 0))
    (Q : E →L[ℝ] F) (hQ : ∀ x ∈ U, Q (f x) = Q x)
    (S : Submodule ℝ E) (hS : ∀ x ∈ U ∩ (S : Set E), f x = x) :
    ∃ (C : E ≃L[ℝ] E) (A : ℝ × E → E) (K : Set E),
      C.toContinuousLinearMap = fderiv ℝ f 0 ∧
      (∀ x, Q (C x) = Q x) ∧ (∀ x ∈ S, C x = x) ∧
      IsCompact K ∧ K ⊆ U ∧ ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
      (∀ x, A (0, x) = x) ∧
      (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, D x = A (t, x)) ∧
      (∀ t x, x ∉ K → A (t, x) = x) ∧ (∀ t x, Q (A (t, x)) = Q x) ∧
      (∀ t x, x ∈ S → A (t, x) = x) ∧
      f =ᶠ[𝓝 (0 : E)] (fun x => C (A (1, x))) := by
  have hfd : DifferentiableAt ℝ f 0 :=
    (hf.contDiffAt (hU.mem_nhds hzero)).differentiableAt (by simp)
  let C := (LinearEquiv.ofBijective (fderiv ℝ f 0).toLinearMap hdf).toContinuousLinearEquiv
  have hC : C.toContinuousLinearMap = fderiv ℝ f 0 := rfl
  have hQC : ∀ x, Q (C x) = Q x := by
    intro x
    exact congrArg (fun A : E →L[ℝ] F => A x) (fderiv_preserves_projection hU hzero hfd Q hQ)
  have hCS : ∀ x ∈ S, C x = x := fderiv_fixes_subspace hU hzero hfd S hS
  have hQCinv (y : E) : Q (C.symm y) = Q y := by
    have h := (hQC (C.symm y)).symm
    simpa only [C.apply_symm_apply] using h
  have hCSinv (x : E) (hx : x ∈ S) : C.symm x = x := by
    have h := C.symm_apply_apply x
    rwa [hCS x hx] at h
  let G : E → E := C.symm ∘ f
  have hG : ContDiffOn ℝ ∞ G U := C.symm.contDiff.comp_contDiffOn hf
  have hG₀ : G 0 = 0 := by simp [G, hf₀]
  have hGder : fderiv ℝ G 0 = C.symm.toContinuousLinearMap.comp (fderiv ℝ f 0) :=
    (C.symm.toContinuousLinearMap.hasFDerivAt.comp 0 hfd.hasFDerivAt).fderiv
  have hdG : fderiv ℝ G 0 = ContinuousLinearMap.id ℝ E := by
    rw [hGder, ← hC]
    ext x
    exact C.symm_apply_apply x
  have hQG : ∀ x ∈ U, Q (G x) = Q x := by
    intro x hx
    change Q (C.symm (f x)) = Q x
    rw [hQCinv, hQ x hx]
  have hSG : ∀ x ∈ U ∩ (S : Set E), G x = x := by
    intro x hx
    change C.symm (f x) = x
    rw [hS x hx, hCSinv x hx.2]
  obtain ⟨A, K, hK, hKU, hA, hA₀, hdiff, hfix, hprojection, hfixed, hgerm⟩ :=
    exists_relative_tangent_identity_isotopy hU hzero hG hG₀ hdG Q hQG hSG
  refine ⟨C, A, K, hC, hQC, hCS, hK, hKU, hA, hA₀, hdiff, hfix,
    hprojection, hfixed, ?_⟩
  filter_upwards [hgerm] with x hx
  change A (1, x) = C.symm (f x) at hx
  rw [hx, C.apply_symm_apply]

/-- The endpoint form, retaining the original interface and relative constraints. -/
theorem exists_relative_germ_linearization {f : E → E} {U : Set E}
    (hU : IsOpen U) (hzero : (0 : E) ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hf₀ : f 0 = 0) (hdf : Bijective (fderiv ℝ f 0))
    (Q : E →L[ℝ] F) (hQ : ∀ x ∈ U, Q (f x) = Q x)
    (S : Submodule ℝ E) (hS : ∀ x ∈ U ∩ (S : Set E), f x = x) :
    ∃ (C : E ≃L[ℝ] E) (D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞) (K : Set E),
      C.toContinuousLinearMap = fderiv ℝ f 0 ∧
      (∀ x, Q (C x) = Q x) ∧ (∀ x ∈ S, C x = x) ∧
      IsCompact K ∧ K ⊆ U ∧ SupportedDiffeomorph.IsotopicToIdentity D ∧
      (∀ x ∉ K, D x = x) ∧ (∀ x, Q (D x) = Q x) ∧
      (∀ x ∈ S, D x = x) ∧ f =ᶠ[𝓝 (0 : E)] (fun x => C (D x)) := by
  obtain ⟨C, A, K, hC, hQC, hCS, hK, hKU, hA, hA₀, hdiff, hfix,
      hprojection, hfixed, hgerm⟩ :=
    exists_relative_germ_linearization_isotopy hU hzero hf hf₀ hdf Q hQ S hS
  obtain ⟨D, hD⟩ := hdiff 1
  refine ⟨C, D, K, hC, hQC, hCS, hK, hKU, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨A, hA, hA₀, fun x => (hD x).symm, fun t => by
      obtain ⟨d, hd⟩ := hdiff t
      exact ⟨d, fun x => (hd x).symm⟩⟩
  · intro x hx
    exact (hD x).trans (hfix 1 x hx)
  · intro x
    rw [hD, hprojection]
  · intro x hx
    exact (hD x).trans (hfixed 1 x hx)
  · filter_upwards [hgerm] with x hx
    rw [hD]
    exact hx

end Wikipedia.SmoothSixDPoincare.SmallPerturbation
