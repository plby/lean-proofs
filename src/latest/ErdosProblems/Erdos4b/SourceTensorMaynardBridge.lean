/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceFaceIntegration

/-!
# Identifying source tensor energies with the usual Maynard functionals

The positive-orthant and unit-cube integrals agree for factors vanishing
above one. Null coordinate boundaries are handled by measure equality.
-/

namespace Erdos4b

noncomputable section

open MeasureTheory BoundedGaps.Maynard
open scoped BigOperators

theorem integral_positiveOrthant_eq_unitCube {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) → ℝ)
    (hf : ∀ t, (∀ i, 0 ≤ t i) → t ∉ maynardCubeOf ι → f t = 0) :
    (∫ t : ι → ℝ in Set.univ.pi (fun _ ↦ Set.Ioi 0), f t) =
      ∫ t : ι → ℝ in maynardCubeOf ι, f t := by
  have heq : (Set.univ.pi (fun _ : ι ↦ Set.Ioi (0 : ℝ))) =ᵐ[volume]
      (Set.univ.pi (fun _ : ι ↦ Set.Ici (0 : ℝ))) :=
    Measure.pi_Ioi_ae_eq_pi_Ici (μ := fun _ : ι ↦ (volume : Measure ℝ))
      (s := Set.univ) (f := fun _ ↦ 0)
  rw [setIntegral_congr_set heq]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (MeasurableSet.pi Set.countable_univ fun _ _ ↦ measurableSet_Ici)
  · intro t ht i hi
    exact (ht i hi).1
  · intro t ht
    exact hf t (fun i ↦ ht.1 i (Set.mem_univ i)) ht.2

theorem integral_Ioi_eq_unitInterval {f : ℝ → ℝ} (hf : ∀ t, 1 < t → f t = 0) :
    (∫ t : ℝ in Set.Ioi 0, f t) = ∫ t : ℝ in Set.Icc 0 1, f t := by
  rw [setIntegral_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici Set.Icc_subset_Ici_self
  intro t ht
  apply hf t
  by_contra hh
  exact ht.2 ⟨ht.1, le_of_not_gt hh⟩

theorem weighted_tensor_zero_of_not_unitCube {ι J : Type*} [Fintype ι]
    (S : Finset J) (c : J → ℝ) (ψ : J → ι → ℝ → ℝ)
    (hsupport : ∀ j ∈ S, ∀ i t, 1 < t → ψ j i t = 0)
    (t : ι → ℝ) (ht0 : ∀ i, 0 ≤ t i) (ht : t ∉ maynardCubeOf ι) :
    (∑ j ∈ S, c j * ∏ i, ψ j i (t i)) = 0 := by
  classical
  have hex : ∃ i, 1 < t i := by
    by_contra hh
    push Not at hh
    exact ht (fun i _ ↦ ⟨ht0 i, hh i⟩)
  obtain ⟨i, hi⟩ := hex
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (hsupport j hj i (t i) hi), mul_zero]

theorem sourceTensorEnergy_eq_maynardI {K : ℕ} {J : Type*}
    (S : Finset J) (ψ : J → Fin K → ℝ → ℝ)
    (hsupport : ∀ j ∈ S, ∀ i t, 1 < t → ψ j i t = 0) :
    sourceTensorEnergy S ψ = maynardI K (sourceTensorValue S ψ) := by
  apply integral_positiveOrthant_eq_unitCube
  intro t ht0 ht
  have hz := weighted_tensor_zero_of_not_unitCube S (fun _ ↦ 1) ψ hsupport t ht0 ht
  simp only [one_mul] at hz
  change (∑ j ∈ S, ∏ i, ψ j i (t i)) ^ 2 = 0
  rw [hz, zero_pow (by norm_num : 2 ≠ 0)]

theorem sourceTensorValue_insert {K : ℕ} {J : Type*}
    (S : Finset J) (ψ : J → Fin K → ℝ → ℝ) (h : Fin K)
    (t : maynardFaceIndex K h → ℝ) (x : ℝ) :
    sourceTensorValue S ψ (maynardInsertCoordinate h x t) =
      ∑ j ∈ S, ψ j h x * ∏ i : PinnedShiftIndex h, ψ j i.val (t i) := by
  classical
  apply Finset.sum_congr rfl
  intro j hj
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (fun i ↦ ψ j i (maynardInsertCoordinate h x t i)) h, maynardInsertCoordinate_at]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [maynardInsertCoordinate_off h x t i.val i.property]

theorem integral_unitFace_sourceTensorValue {K : ℕ} {J : Type*}
    (S : Finset J) (ψ : J → Fin K → ℝ → ℝ)
    (hint : ∀ j ∈ S, ∀ i, IntegrableOn (ψ j i) (Set.Icc 0 1))
    (h : Fin K) (t : maynardFaceIndex K h → ℝ) :
    (∫ x : ℝ in Set.Icc 0 1, sourceTensorValue S ψ (maynardInsertCoordinate h x t)) =
      ∑ j ∈ S, (∫ x : ℝ in Set.Icc 0 1, ψ j h x) *
        ∏ i : PinnedShiftIndex h, ψ j i.val (t i) := by
  simp_rw [sourceTensorValue_insert]
  rw [integral_finsetSum S (fun j hj ↦ (hint j hj h).mul_const _)]
  simp_rw [integral_mul_const]

theorem sourceTensorFaceEnergy_eq_maynardJ {K : ℕ} {J : Type*}
    (S : Finset J) (ψ : J → Fin K → ℝ → ℝ)
    (hint : ∀ j ∈ S, ∀ i, IntegrableOn (ψ j i) (Set.Icc 0 1))
    (hsupport : ∀ j ∈ S, ∀ i t, 1 < t → ψ j i t = 0) (h : Fin K) :
    sourceTensorFaceEnergy S ψ h = maynardJ K h (sourceTensorValue S ψ) := by
  have heq (t : maynardFaceIndex K h → ℝ) : sourceTensorFaceValue S ψ h t =
      ∫ x : ℝ in Set.Icc 0 1, sourceTensorValue S ψ (maynardInsertCoordinate h x t) := by
    rw [integral_unitFace_sourceTensorValue S ψ hint h t]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_Ioi_eq_unitInterval (hsupport j hj h)]
  have hcube := integral_positiveOrthant_eq_unitCube
    (fun t : PinnedShiftIndex h → ℝ ↦ sourceTensorFaceValue S ψ h t ^ 2) ?_
  · change sourceTensorFaceEnergy S ψ h = _ at hcube
    rw [hcube]
    unfold maynardJ
    apply integral_congr_ae
    exact ae_of_all _ fun t ↦ congrArg (fun x : ℝ ↦ x ^ 2) (heq t)
  · intro t ht0 ht
    have hz := weighted_tensor_zero_of_not_unitCube S
      (fun j ↦ ∫ x : ℝ in Set.Ioi 0, ψ j h x)
      (fun j (i : PinnedShiftIndex h) ↦ ψ j i.val)
      (fun j hj i x hx ↦ hsupport j hj i.val x hx) t ht0 ht
    change (∑ j ∈ S, (∫ x : ℝ in Set.Ioi 0, ψ j h x) *
      ∏ i : PinnedShiftIndex h, ψ j i.val (t i)) ^ 2 = 0
    rw [hz, zero_pow (by norm_num : 2 ≠ 0)]

end

end Erdos4b
