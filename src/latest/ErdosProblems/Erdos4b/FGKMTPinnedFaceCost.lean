/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedSlice
import ErdosProblems.Erdos4b.FGKMTWeightedFaceMajorant

/-!
# Uniform one-dimensional derivative cost on the face-majorant scale

Every long-factor summand dominates the short tensor. Keeping all of
them makes the integrated majorant control the short tensor by an
absolute constant in tail dimension `m` and full dimension `m + 1`.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem dim_mul_shortTensor_le_majorant {k m : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (t : Fin m → ℝ) (ht : ∀ i, 0 ≤ t i) :
    (m : ℝ) * (∏ i, dimensionProfileFactor k (t i)) ≤ sieveProfileMajorant k m t := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _hi => shortTensor_le_oneLongTensor hk hlog i ht)
  simpa only [sieveProfileMajorant, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] using h

theorem shortTensor_le_four_majorantFace {m : ℕ} (hm : 1 ≤ m)
    (hlog : 10000 ≤ Real.log (m + 1 : ℕ)) (t : Fin m → ℝ) (ht : ∀ i, 0 ≤ t i) :
    (∏ i, dimensionProfileFactor (m + 1) (t i)) ≤
      4 * majorantFaceValue (m + 1) m t := by
  let P := ∏ i, dimensionProfileFactor (m + 1) (t i)
  let b := dimensionProfileFirstMass (m + 1)
  have hP : 0 ≤ P := Finset.prod_nonneg fun i _hi => dimensionProfileFactor_nonneg _ _
  have hb : 0 ≤ b := dimensionProfileFirstMass_nonneg _
  have hk : (0 : ℝ) < (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
  have hbmass : 1 ≤ (2 * (m + 1 : ℕ)) * b := by
    have h := (dimensionProfileFirstMass_bounds (Nat.succ_pos m) hlog).1
    simpa only [b, mul_comm] using
      (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (m + 1 : ℕ))).mp h
  have hmlarge : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hdim : 1 ≤ 4 * (m : ℝ) * b := by
    push_cast at hbmass
    nlinarith
  have hsum := dim_mul_shortTensor_le_majorant (Nat.succ_pos m) hlog t ht
  have hlong : 0 ≤ dimensionLongFirstMass (m + 1) :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (dimensionLongFactor_nonneg _)
  have hface : b * ((m : ℝ) * P) ≤ majorantFaceValue (m + 1) m t := by
    change b * ((m : ℝ) * P) ≤ dimensionLongFirstMass (m + 1) * P +
      b * sieveProfileMajorant (m + 1) m t
    exact (mul_le_mul_of_nonneg_left hsum hb).trans
      (le_add_of_nonneg_left (mul_nonneg hlong hP))
  have hscaled := mul_le_mul_of_nonneg_right hdim hP
  dsimp only [P] at hface hscaled ⊢
  nlinarith

theorem exists_sieveProfile_face_deriv_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {m : ℕ}, 1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) →
      ∀ (t : Fin m → ℝ), (∀ i, 0 ≤ t i) → ∀ x : ℝ, 0 ≤ x →
        |deriv (fun s => sieveProfile (m + 1) (m + 1) (Fin.cons s t)) x| ≤
          C * sieveProfileScale (m + 1) * majorantFaceValue (m + 1) m t := by
  obtain ⟨C, hC, hbound⟩ := exists_sieveProfile_coordinate_deriv_bound
  refine ⟨4 * C, by positivity, ?_⟩
  intro m hm hlog t ht x hx
  have hT : 0 ≤ sieveProfileScale (m + 1) :=
    zero_le_one.trans (profile_scales_bounds (Nat.succ_pos m) hlog).1
  have hP : 0 ≤ ∏ i, dimensionProfileFactor (m + 1) (t i) :=
    Finset.prod_nonneg fun i _hi => dimensionProfileFactor_nonneg _ _
  have hD : dimensionLongFactor (m + 1) x ≤ 1 := sieveFactor_le_one hT hx _
  calc
    _ ≤ C * sieveProfileScale (m + 1) * dimensionLongFactor (m + 1) x *
        (∏ i, dimensionProfileFactor (m + 1) (t i)) :=
      hbound (Nat.succ_pos m) hlog m t x hx
    _ ≤ C * sieveProfileScale (m + 1) *
        (∏ i, dimensionProfileFactor (m + 1) (t i)) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hD (mul_nonneg hC.le hT)) hP
    _ ≤ C * sieveProfileScale (m + 1) * (4 * majorantFaceValue (m + 1) m t) :=
      mul_le_mul_of_nonneg_left (shortTensor_le_four_majorantFace hm hlog t ht)
        (mul_nonneg hC.le hT)
    _ = _ := by ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.shortTensor_le_four_majorantFace
#print axioms Erdos4b.FGKMT.exists_sieveProfile_face_deriv_bound
