/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceTensorVariational
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Exact rescaling of tensor energies

Shrinking all coordinates by a factor R loses precisely one factor R
in the variational quotient, independent of the dimension.
-/

namespace Erdos4b

noncomputable section

open MeasureTheory
open scoped BigOperators Pointwise

theorem smul_positiveOrthant {ι : Type*} {R : ℝ} (hR : 0 < R) :
    R • (Set.univ.pi (fun _ : ι ↦ Set.Ioi (0 : ℝ))) =
      Set.univ.pi (fun _ : ι ↦ Set.Ioi (0 : ℝ)) := by
  ext t
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hR.ne']
  simp only [Set.mem_pi, Set.mem_Ioi, Pi.smul_apply, smul_eq_mul,
    mul_pos_iff_of_pos_left (inv_pos.mpr hR)]

theorem integral_positiveOrthant_rescale {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) → ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ t : ι → ℝ in Set.univ.pi (fun _ ↦ Set.Ioi 0), f (fun i ↦ R * t i)) =
      (R ^ Fintype.card ι)⁻¹ * ∫ t : ι → ℝ in Set.univ.pi (fun _ ↦ Set.Ioi 0), f t := by
  have hh := Measure.setIntegral_comp_smul_of_pos (volume : Measure (ι → ℝ)) f
    (Set.univ.pi (fun _ ↦ Set.Ioi 0)) hR
  rw [smul_positiveOrthant hR, Module.finrank_fintype_fun_eq_card, smul_eq_mul] at hh
  convert hh using 1
  congr 1

theorem sourceTensorEnergy_rescale {ι J : Type*} [Fintype ι]
    (S : Finset J) (ψ : J → ι → ℝ → ℝ) {R : ℝ} (hR : 0 < R) :
    sourceTensorEnergy S (fun j i t ↦ ψ j i (R * t)) =
      (R ^ Fintype.card ι)⁻¹ * sourceTensorEnergy S ψ :=
  integral_positiveOrthant_rescale (fun t ↦ sourceTensorValue S ψ t ^ 2) hR

theorem sourceTensorFaceValue_rescale {K : ℕ} {J : Type*}
    (S : Finset J) (ψ : J → Fin K → ℝ → ℝ) {R : ℝ} (hR : 0 < R)
    (h : Fin K) (t : PinnedShiftIndex h → ℝ) :
    sourceTensorFaceValue S (fun j i u ↦ ψ j i (R * u)) h t =
      R⁻¹ * sourceTensorFaceValue S ψ h (fun i ↦ R * t i) := by
  unfold sourceTensorFaceValue
  simp_rw [integral_comp_mul_left_Ioi _ 0 hR, mul_zero, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem sourceTensorFaceEnergy_rescale {K : ℕ} {J : Type*}
    (S : Finset J) (ψ : J → Fin K → ℝ → ℝ) {R : ℝ} (hR : 0 < R) (h : Fin K) :
    sourceTensorFaceEnergy S (fun j i t ↦ ψ j i (R * t)) h =
      (R ^ (K + 1))⁻¹ * sourceTensorFaceEnergy S ψ h := by
  unfold sourceTensorFaceEnergy
  simp_rw [sourceTensorFaceValue_rescale S ψ hR, mul_pow]
  rw [integral_const_mul,
    integral_positiveOrthant_rescale (fun t ↦ sourceTensorFaceValue S ψ h t ^ 2) hR,
    card_pinnedShiftIndex]
  have hK : 0 < K := Nat.zero_lt_of_lt h.isLt
  have hexp : K - 1 + 2 = K + 1 := by omega
  rw [← mul_assoc, inv_pow, ← mul_inv, mul_comm (R ^ 2), ← pow_add, hexp]

theorem sourceTensorRatio_rescale {K : ℕ} {J : Type*}
    (S : Finset J) (ψ : J → Fin K → ℝ → ℝ) {R : ℝ} (hR : 0 < R) :
    (∑ h : Fin K, sourceTensorFaceEnergy S (fun j i t ↦ ψ j i (R * t)) h) /
        sourceTensorEnergy S (fun j i t ↦ ψ j i (R * t)) =
      ((∑ h : Fin K, sourceTensorFaceEnergy S ψ h) / sourceTensorEnergy S ψ) / R := by
  simp_rw [sourceTensorFaceEnergy_rescale S ψ hR]
  rw [← Finset.mul_sum, sourceTensorEnergy_rescale S ψ hR, Fintype.card_fin, pow_succ]
  field_simp [(pow_pos hR K).ne', hR.ne']

end

end Erdos4b
