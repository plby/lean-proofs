/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTFaceProfile

/-! # Uniform variation of the true face profile and monotonicity of its majorant -/

namespace Erdos4b.FGKMT

noncomputable section

open MeasureTheory
open scoped BigOperators

theorem sieveProfile_cons_continuous (k m : ℕ) (t : Fin m → ℝ) :
    Continuous (fun x => sieveProfile k (m + 1) (Fin.cons x t)) :=
  continuous_iff_continuousAt.mpr fun x => (sieveProfile_cons_hasDerivAt k m t x).continuousAt

theorem integral_majorant_slice_unit_le_face {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (m : ℕ) (t : Fin m → ℝ) :
    (∫ x in (0 : ℝ)..1, sieveProfileMajorant k (m + 1) (Fin.cons x t)) ≤
      majorantFaceValue k m t := by
  rw [majorantFaceValue_eq_interval hk hlog]
  exact intervalIntegral.integral_mono_interval le_rfl zero_le_one (by norm_num)
    (ae_of_all _ fun x => sieveProfileMajorant_nonneg _ _ _)
    ((sieveProfileMajorant_cons_contDiff k m t).continuous.intervalIntegrable _ _)

theorem majorantFaceValue_antitone_on_orthant {k m : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) {t u : Fin m → ℝ}
    (ht : ∀ i, 0 ≤ t i) (htu : ∀ i, t i ≤ u i) :
    majorantFaceValue k m u ≤ majorantFaceValue k m t := by
  rw [majorantFaceValue_eq_interval hk hlog, majorantFaceValue_eq_interval hk hlog]
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((sieveProfileMajorant_cons_contDiff k m u).continuous.intervalIntegrable _ _)
    ((sieveProfileMajorant_cons_contDiff k m t).continuous.intervalIntegrable _ _)
  intro x hx
  exact sieveProfileMajorant_antitone_on_orthant hk hlog
    (fun i => Fin.cases hx.1 (fun q => ht q) i)
    (fun i => Fin.cases le_rfl (fun q => htu q) i)

theorem exists_sieveFaceProfile_reassignment_variation_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ}, 0 < k → 10000 ≤ Real.log k →
      ∀ (m : ℕ) (u t s : Fin m → ℝ) (a : ℝ), (∀ i, 0 ≤ u i) →
        (∀ i, u i ≤ t i) → (∀ i, u i ≤ s i) →
        (∑ i, (t i - u i)) ≤ a → (∑ i, (s i - u i)) ≤ a →
        |sieveFaceProfile k m t - sieveFaceProfile k m s| ≤
          (C * sieveProfileScale k * majorantFaceValue k m u) * a := by
  obtain ⟨C, hC, hbound⟩ := exists_sieveProfile_reassignment_variation_bound
  refine ⟨C, hC, ?_⟩
  intro k hk hlog m u t s a hu hut hus ht hs
  have hT : 0 ≤ sieveProfileScale k := zero_le_one.trans (profile_scales_bounds hk hlog).1
  have ha : 0 ≤ a := (Finset.sum_nonneg fun i _hi => sub_nonneg.mpr (hut i)).trans ht
  let G := fun x => sieveProfileMajorant k (m + 1) (Fin.cons x u)
  have hG := (sieveProfileMajorant_cons_contDiff k m u).continuous
  have hpoint (x : ℝ) (hx : 0 ≤ x) :
      ‖sieveProfile k (m + 1) (Fin.cons x t) - sieveProfile k (m + 1) (Fin.cons x s)‖ ≤
        (C * sieveProfileScale k * a) * G x := by
    have h := hbound hk hlog (m + 1) (Fin.cons x u) (Fin.cons x t) (Fin.cons x s) a
      (fun i => Fin.cases hx (fun q => hu q) i)
      (fun i => Fin.cases le_rfl (fun q => hut q) i)
      (fun i => Fin.cases le_rfl (fun q => hus q) i)
      (by simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, sub_self, zero_add] using ht)
      (by simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, sub_self, zero_add] using hs)
    rw [Real.norm_eq_abs]
    convert h using 1
    dsimp only [G]
    ring
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) zero_le_one
    (ae_of_all _ fun x hx => hpoint x hx.1.le)
    ((continuous_const.mul hG).intervalIntegrable (0 : ℝ) 1)
  rw [intervalIntegral.integral_sub
    ((sieveProfile_cons_continuous k m t).intervalIntegrable _ _)
    ((sieveProfile_cons_continuous k m s).intervalIntegrable _ _), Real.norm_eq_abs,
    ← sieveFaceProfile_eq_integral, ← sieveFaceProfile_eq_integral,
    intervalIntegral.integral_const_mul] at h
  calc
    _ ≤ (C * sieveProfileScale k * a) * (∫ x in (0 : ℝ)..1, G x) := h
    _ ≤ (C * sieveProfileScale k * a) * majorantFaceValue k m u :=
      mul_le_mul_of_nonneg_left (integral_majorant_slice_unit_le_face hk hlog m u) (by positivity)
    _ = _ := by ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.majorantFaceValue_antitone_on_orthant
#print axioms Erdos4b.FGKMT.exists_sieveFaceProfile_reassignment_variation_bound
