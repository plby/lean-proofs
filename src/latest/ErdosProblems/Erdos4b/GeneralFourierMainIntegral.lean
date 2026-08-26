/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierMainMajorant

/-!
# Evaluation of the full tensor main integral

Finite product measure is preserved by currying and by the Boolean
pair equivalence. Fubini then reduces the main integral to the already
proved one-pair profile-derivative identity.
-/

namespace Erdos4b

noncomputable section

open MeasureTheory
open scoped BigOperators

theorem volume_preserving_real_curry (ι κ : Type*) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℝ) volume volume := by
  let e := (MeasurableEquiv.curry ι κ ℝ).symm
  apply MeasurePreserving.symm e
  refine ⟨e.measurable, ?_⟩
  change (Measure.pi (fun _ : ι ↦ (volume : Measure (κ → ℝ)))).map e =
    Measure.pi (fun _ : ι × κ ↦ (volume : Measure ℝ))
  refine (Measure.pi_eq (fun s hs ↦ ?_)).symm
  have hpre : e ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun i ↦ Set.pi Set.univ (fun j ↦ s (i, j))) := by
    ext x
    simp only [e, MeasurableEquiv.coe_curry_symm, Set.mem_preimage, Set.mem_pi,
      Set.mem_univ, forall_true_left, Function.uncurry_apply_pair, Prod.forall]
  rw [MeasurableEquiv.map_apply, hpre, Measure.pi_pi]
  simp only [MeasureSpace.volume, Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun ij : ι × κ ↦ volume (s ij))).symm

def fourierBoolRealPair : (Bool → ℝ) ≃ᵐ ℝ × ℝ where
  toEquiv := Equiv.boolArrowEquivProd ℝ
  measurable_toFun := (measurable_pi_apply false).prodMk (measurable_pi_apply true)
  measurable_invFun := by
    apply measurable_pi_lambda
    intro b
    cases b
    · exact measurable_fst
    · exact measurable_snd

theorem volume_preserving_fourierBoolRealPair :
    MeasurePreserving fourierBoolRealPair volume (volume.prod volume) := by
  let e := fourierBoolRealPair.symm
  apply MeasurePreserving.symm e
  refine ⟨e.measurable, ?_⟩
  change (volume.prod volume).map e = Measure.pi (fun _ : Bool ↦ (volume : Measure ℝ))
  refine (Measure.pi_eq (fun s hs ↦ ?_)).symm
  have hpre : e ⁻¹' Set.pi Set.univ s = s false ×ˢ s true := by
    ext x
    simp [e, fourierBoolRealPair, Equiv.boolArrowEquivProd]
  rw [MeasurableEquiv.map_apply, hpre, Measure.prod_prod, Fintype.prod_bool, mul_comm]

theorem doubledFourierPairKernel_mul_tensor_eq_prod
    {ι : Type*} [Fintype ι] (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (ξ : ((ι ⊕ ι) × Bool) → ℝ) :
    doubledFourierPairKernel ξ * doubledFourierTensor f ξ =
      ∏ i, fourierLaplacePairKernel (ξ (i, false)) (ξ (i, true)) *
        (f (i, false) (ξ (i, false)) * f (i, true) (ξ (i, true))) := by
  unfold doubledFourierPairKernel doubledFourierTensor
  rw [Fintype.prod_prod_type (fun ib : (ι ⊕ ι) × Bool ↦ f ib (ξ ib)),
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Fintype.prod_bool, mul_comm (f (i, true) _)]

theorem integral_doubledFourierPairKernel_mul_tensor_eq_prod
    {ι : Type*} [Fintype ι] (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ) :
    (∫ ξ, doubledFourierPairKernel ξ * doubledFourierTensor f ξ) =
      ∏ i, ∫ z : ℝ × ℝ, fourierLaplacePairKernel z.1 z.2 *
        (f (i, false) z.1 * f (i, true) z.2) ∂(volume.prod volume) := by
  let g (i : ι ⊕ ι) (x : Bool → ℝ) :=
    fourierLaplacePairKernel (x false) (x true) *
      (f (i, false) (x false) * f (i, true) (x true))
  calc
    _ = ∫ ξ : ((ι ⊕ ι) × Bool) → ℝ,
        ∏ i, g i ((MeasurableEquiv.curry (ι ⊕ ι) Bool ℝ) ξ i) := by
      apply integral_congr_ae
      exact ae_of_all _ (doubledFourierPairKernel_mul_tensor_eq_prod f)
    _ = ∫ x : (ι ⊕ ι) → Bool → ℝ, ∏ i, g i (x i) :=
      (volume_preserving_real_curry (ι ⊕ ι) Bool).integral_comp'
        (fun x : (ι ⊕ ι) → Bool → ℝ ↦ ∏ i, g i (x i))
    _ = ∏ i, ∫ x : Bool → ℝ, g i x := integral_fintype_prod_volume_eq_prod g
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      exact volume_preserving_fourierBoolRealPair.integral_comp'
        (fun z : ℝ × ℝ ↦ fourierLaplacePairKernel z.1 z.2 *
          (f (i, false) z.1 * f (i, true) z.2))

theorem integral_doubledFourierPairKernel_mul_tensor_eq_profile_derivatives
    {ι : Type*} [Fintype ι] (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ) :
    (∫ ξ, doubledFourierPairKernel ξ * doubledFourierTensor f ξ) =
      ∏ i, ∫ t : ℝ in Set.Ioi 0,
        deriv (laplaceFourierProfile (f (i, false))) t *
          deriv (laplaceFourierProfile (f (i, true))) t := by
  rw [integral_doubledFourierPairKernel_mul_tensor_eq_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact integral_fourierLaplacePairKernel_eq_profile_derivatives (f (i, false)) (f (i, true))

theorem integral_doubledFourierPairKernel_mul_tensor_eq_given_profiles
    {ι : Type*} [Fintype ι] (f : ((ι ⊕ ι) × Bool) → SchwartzMap ℝ ℂ)
    (F : ((ι ⊕ ι) × Bool) → ℝ → ℂ)
    (hF : ∀ ib t, laplaceFourierProfile (f ib) t = F ib t) :
    (∫ ξ, doubledFourierPairKernel ξ * doubledFourierTensor f ξ) =
      ∏ i, ∫ t : ℝ in Set.Ioi 0, deriv (F (i, false)) t * deriv (F (i, true)) t := by
  rw [integral_doubledFourierPairKernel_mul_tensor_eq_profile_derivatives]
  have heq (ib) : laplaceFourierProfile (f ib) = F ib := funext (hF ib)
  simp only [heq]

end

end Erdos4b
