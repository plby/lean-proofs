/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Polynomial tail bounds for finite-dimensional Schwartz tensors

Every coordinate moment is integrable by finite-dimensional Fubini.
Outside a coordinate box, one moment dominates the threshold power;
summing over the possible coordinates gives a quantitative tail bound.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

def fourierCoordinateBox {ι : Type*} (T : ℝ) : Set (ι → ℝ) :=
  {ξ | ∀ i, ‖ξ i‖ ≤ T}

def schwartzTensorNorm {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap ℝ ℂ) (ξ : ι → ℝ) : ℝ := ∏ i, ‖f i (ξ i)‖

def schwartzTensorMomentDensity {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap ℝ ℂ) (A : ℕ) (ξ : ι → ℝ) : ℝ :=
  ∑ j, ‖ξ j‖ ^ A * schwartzTensorNorm f ξ

def schwartzTensorMoment {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap ℝ ℂ) (A : ℕ) : ℝ :=
  ∫ ξ, schwartzTensorMomentDensity f A ξ

theorem measurableSet_fourierCoordinateBox {ι : Type*} [Countable ι] (T : ℝ) :
    MeasurableSet (fourierCoordinateBox (ι := ι) T) := by
  have h (i : ι) : MeasurableSet {ξ : ι → ℝ | ‖ξ i‖ ≤ T} :=
    measurableSet_le (by fun_prop) measurable_const
  simpa only [fourierCoordinateBox, Set.ofPred_forall] using MeasurableSet.iInter h

theorem schwartzTensorNorm_nonneg {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap ℝ ℂ) (ξ : ι → ℝ) : 0 ≤ schwartzTensorNorm f ξ :=
  Finset.prod_nonneg fun _ _ ↦ norm_nonneg _

theorem integrable_schwartzTensorNorm {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap ℝ ℂ) : Integrable (schwartzTensorNorm f) :=
  Integrable.fintype_prod (fun i ↦ (f i).integrable.norm)

theorem coordinate_pow_mul_schwartzTensorNorm_eq_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → SchwartzMap ℝ ℂ)
    (A : ℕ) (j : ι) (ξ : ι → ℝ) :
    ‖ξ j‖ ^ A * schwartzTensorNorm f ξ =
      ∏ i, (if i = j then ‖ξ i‖ ^ A else 1) * ‖f i (ξ i)‖ := by
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true, schwartzTensorNorm]

theorem integrable_coordinate_pow_mul_schwartzTensorNorm
    {ι : Type*} [Fintype ι] (f : ι → SchwartzMap ℝ ℂ) (A : ℕ) (j : ι) :
    Integrable (fun ξ : ι → ℝ ↦ ‖ξ j‖ ^ A * schwartzTensorNorm f ξ) := by
  classical
  have hi (i : ι) : Integrable (fun x : ℝ ↦
      (if i = j then ‖x‖ ^ A else 1) * ‖f i x‖) := by
    by_cases hij : i = j
    · simpa only [if_pos hij] using (f i).integrable_pow_mul volume A
    · simpa only [if_neg hij, one_mul] using (f i).integrable.norm
  exact (Integrable.fintype_prod hi).congr (ae_of_all _ fun ξ ↦
    (coordinate_pow_mul_schwartzTensorNorm_eq_prod f A j ξ).symm)

theorem integrable_schwartzTensorMomentDensity {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap ℝ ℂ) (A : ℕ) : Integrable (schwartzTensorMomentDensity f A) :=
  integrable_finsetSum _ fun j _ ↦ integrable_coordinate_pow_mul_schwartzTensorNorm f A j

theorem schwartzTensorMomentDensity_nonneg {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap ℝ ℂ) (A : ℕ) (ξ : ι → ℝ) :
    0 ≤ schwartzTensorMomentDensity f A ξ :=
  Finset.sum_nonneg fun _ _ ↦
    mul_nonneg (pow_nonneg (norm_nonneg _) _) (schwartzTensorNorm_nonneg f ξ)

theorem schwartzTensorMoment_nonneg {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap ℝ ℂ) (A : ℕ) : 0 ≤ schwartzTensorMoment f A :=
  integral_nonneg (schwartzTensorMomentDensity_nonneg f A)

theorem schwartzTensorMoment_eq_sum_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → SchwartzMap ℝ ℂ) (A : ℕ) :
    schwartzTensorMoment f A =
      ∑ j, ∏ i, ∫ x : ℝ, (if i = j then ‖x‖ ^ A else 1) * ‖f i x‖ := by
  unfold schwartzTensorMoment schwartzTensorMomentDensity
  rw [integral_finsetSum _ (fun j hj ↦ integrable_coordinate_pow_mul_schwartzTensorNorm f A j)]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = ∫ ξ : ι → ℝ, ∏ i, (if i = j then ‖ξ i‖ ^ A else 1) * ‖f i (ξ i)‖ := by
      apply integral_congr_ae
      exact ae_of_all _ (coordinate_pow_mul_schwartzTensorNorm_eq_prod f A j)
    _ = _ := integral_fintype_prod_volume_eq_prod
      (fun i (x : ℝ) ↦ (if i = j then ‖x‖ ^ A else 1) * ‖f i x‖)

theorem threshold_pow_mul_schwartzTensorNorm_le_momentDensity
    {ι : Type*} [Fintype ι] (f : ι → SchwartzMap ℝ ℂ) (A : ℕ)
    {T : ℝ} (hT : 0 ≤ T) {ξ : ι → ℝ} (hξ : ξ ∉ fourierCoordinateBox T) :
    T ^ A * schwartzTensorNorm f ξ ≤ schwartzTensorMomentDensity f A ξ := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, T < ‖ξ j‖ := by
    simpa only [fourierCoordinateBox, Set.mem_ofPred_eq, not_forall, not_le] using hξ
  calc
    _ ≤ ‖ξ j‖ ^ A * schwartzTensorNorm f ξ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hT hj.le A) (schwartzTensorNorm_nonneg f ξ)
    _ ≤ _ := Finset.single_le_sum
      (f := fun j ↦ ‖ξ j‖ ^ A * schwartzTensorNorm f ξ)
      (fun i hi ↦ mul_nonneg (pow_nonneg (norm_nonneg _) _) (schwartzTensorNorm_nonneg f ξ))
      (Finset.mem_univ j)

theorem integral_schwartzTensorNorm_box_compl_le {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap ℝ ℂ) (A : ℕ) {T : ℝ} (hT : 0 < T) :
    (∫ ξ in (fourierCoordinateBox T)ᶜ, schwartzTensorNorm f ξ) ≤
      schwartzTensorMoment f A / T ^ A := by
  apply (le_div_iff₀ (pow_pos hT A)).mpr
  rw [mul_comm, ← integral_const_mul]
  have hmono := setIntegral_mono_on
    ((integrable_schwartzTensorNorm f).const_mul (T ^ A)).integrableOn
    (integrable_schwartzTensorMomentDensity f A).integrableOn
    (measurableSet_fourierCoordinateBox T).compl
    (fun ξ hξ ↦ threshold_pow_mul_schwartzTensorNorm_le_momentDensity f A hT.le hξ)
  exact hmono.trans (setIntegral_le_integral (integrable_schwartzTensorMomentDensity f A)
    (ae_of_all _ (schwartzTensorMomentDensity_nonneg f A)))

theorem integrable_mul_schwartzTensor_of_bound {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap ℝ ℂ) (K : (ι → ℝ) → ℂ) {D : ℝ}
    (hK : AEStronglyMeasurable K) (hbound : ∀ ξ, ‖K ξ‖ ≤ D) :
    Integrable (fun ξ ↦ K ξ * ∏ i, f i (ξ i)) := by
  have hcont : Continuous (fun ξ : ι → ℝ ↦ ∏ i, f i (ξ i)) := by fun_prop
  apply ((integrable_schwartzTensorNorm f).const_mul D).mono'
    (hK.mul hcont.aestronglyMeasurable)
  apply ae_of_all
  intro ξ
  simp only [Pi.mul_apply, norm_mul, norm_prod]
  exact mul_le_mul_of_nonneg_right (hbound ξ) (schwartzTensorNorm_nonneg f ξ)

theorem norm_integral_mul_schwartzTensor_box_compl_le {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap ℝ ℂ) (K : (ι → ℝ) → ℂ) (A : ℕ) {T D : ℝ}
    (hT : 0 < T) (hD : 0 ≤ D) (hbound : ∀ ξ, ‖K ξ‖ ≤ D) :
    ‖∫ ξ in (fourierCoordinateBox T)ᶜ, K ξ * ∏ i, f i (ξ i)‖ ≤
      D * schwartzTensorMoment f A / T ^ A := by
  calc
    _ ≤ ∫ ξ in (fourierCoordinateBox T)ᶜ, D * schwartzTensorNorm f ξ := by
      apply norm_integral_le_of_norm_le
        ((integrable_schwartzTensorNorm f).const_mul D).integrableOn
      apply ae_of_all
      intro ξ
      rw [norm_mul, norm_prod]
      exact mul_le_mul_of_nonneg_right (hbound ξ) (schwartzTensorNorm_nonneg f ξ)
    _ = D * ∫ ξ in (fourierCoordinateBox T)ᶜ, schwartzTensorNorm f ξ :=
      integral_const_mul _ _
    _ ≤ D * (schwartzTensorMoment f A / T ^ A) :=
      mul_le_mul_of_nonneg_left (integral_schwartzTensorNorm_box_compl_le f A hT) hD
    _ = _ := by ring

theorem tendsto_integral_mul_schwartzTensor_box_compl_zero
    {α ι : Type*} [Fintype ι] {l : Filter α}
    (f : ι → SchwartzMap ℝ ℂ) (K : α → (ι → ℝ) → ℂ) (A : ℕ)
    (T D : α → ℝ) (hT : ∀ a, 0 < T a) (hD : ∀ a, 0 ≤ D a)
    (hbound : ∀ a ξ, ‖K a ξ‖ ≤ D a)
    (hdecay : Tendsto (fun a ↦ D a / T a ^ A) l (𝓝 0)) :
    Tendsto (fun a ↦ ∫ ξ in (fourierCoordinateBox (T a))ᶜ,
      K a ξ * ∏ i, f i (ξ i)) l (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  apply squeeze_zero (fun a ↦ norm_nonneg _) (fun a ↦
    norm_integral_mul_schwartzTensor_box_compl_le f (K a) A (hT a) (hD a) (hbound a))
  simpa only [zero_mul, div_mul_eq_mul_div] using hdecay.mul_const (schwartzTensorMoment f A)

end

end Erdos4b
