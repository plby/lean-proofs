/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTVariationalBounds
import ErdosProblems.Erdos4b.SourceTensorMaynardBridge

/-!
# The literal smooth sieve profile and its integrals

The dimension used to choose the one-variable scales is separate from
the number of coordinates. This makes the full and face integrals
comparable without changing the one-variable factor.
-/

namespace Erdos4b.FGKMT

noncomputable section

open MeasureTheory
open scoped BigOperators

def sieveProfile (k j : ℕ) (t : Fin j → ℝ) : ℝ :=
  sieveCutoff (∑ i, t i) * ∏ i, dimensionProfileFactor k (t i)

theorem sieveProfile_nonneg (k j : ℕ) (t : Fin j → ℝ) :
    0 ≤ sieveProfile k j t :=
  mul_nonneg (sieveCutoff_nonneg _)
    (Finset.prod_nonneg fun i _ => dimensionProfileFactor_nonneg k (t i))

theorem sieveProfile_contDiff (k j : ℕ) {n : ℕ∞} : ContDiff ℝ n (sieveProfile k j) := by
  unfold sieveProfile
  apply ContDiff.mul
  · apply sieveCutoff_contDiff.comp
    fun_prop
  · apply contDiff_prod
    intro i _hi
    exact (dimensionProfileFactor_contDiff k).comp (contDiff_apply ℝ ℝ i)

theorem sieveProfile_perm (k j : ℕ) (σ : Equiv.Perm (Fin j)) (t : Fin j → ℝ) :
    sieveProfile k j (t ∘ σ) = sieveProfile k j t := by
  unfold sieveProfile
  simp only [Function.comp_apply, Equiv.sum_comp]
  congr 1
  exact Equiv.prod_comp σ (fun i => dimensionProfileFactor k (t i))

theorem sieveProfile_antitone_on_orthant {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) {j : ℕ} {t u : Fin j → ℝ}
    (ht : ∀ i, 0 ≤ t i) (htu : ∀ i, t i ≤ u i) :
    sieveProfile k j u ≤ sieveProfile k j t := by
  have hb := profile_scales_bounds hk hlog
  apply mul_le_mul
    (sieveCutoff_antitone (Finset.sum_le_sum fun i _ => htu i))
  · apply Finset.prod_le_prod
    · intro i _hi
      exact dimensionProfileFactor_nonneg k (u i)
    · intro i _hi
      exact sieveFactor_antitoneOn (zero_le_one.trans hb.1) hb.2.1
        (ht i) ((ht i).trans (htu i)) (htu i)
  · exact Finset.prod_nonneg fun i _ => dimensionProfileFactor_nonneg k (u i)
  · exact sieveCutoff_nonneg _

theorem sieveProfile_zero_of_sum_ge_one {k j : ℕ} {t : Fin j → ℝ}
    (ht : 1 ≤ ∑ i, t i) : sieveProfile k j t = 0 := by
  rw [sieveProfile, sieveCutoff_zero_of_one_le ht, zero_mul]

theorem sieveProfile_zero_of_not_unitCube (k j : ℕ) (t : Fin j → ℝ)
    (ht0 : ∀ i, 0 ≤ t i) (ht : t ∉ BoundedGaps.Maynard.maynardCubeOf (Fin j)) :
    sieveProfile k j t = 0 := by
  classical
  have hex : ∃ i, 1 < t i := by
    by_contra hh
    push Not at hh
    exact ht (fun i _ => ⟨ht0 i, hh i⟩)
  obtain ⟨i, hi⟩ := hex
  apply sieveProfile_zero_of_sum_ge_one
  exact hi.le.trans (Finset.single_le_sum (fun q _ => ht0 q) (Finset.mem_univ i))

theorem dimensionProfileEnergy_eq_cube (k j : ℕ) :
    dimensionProfileEnergy k j =
      ∫ t in BoundedGaps.Maynard.maynardCubeOf (Fin j), sieveProfile k j t ^ 2 := by
  rw [dimensionProfileEnergy, cutoffCubeIntegral_eq_cube]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    simp only [sieveProfile, zero_add, Finset.prod_pow, mul_pow]
    ring

theorem dimensionProfileEnergy_eq_orthant (k j : ℕ) :
    dimensionProfileEnergy k j =
      ∫ t : Fin j → ℝ in Set.univ.pi (fun _ => Set.Ioi 0), sieveProfile k j t ^ 2 := by
  rw [Erdos4b.integral_positiveOrthant_eq_unitCube]
  · exact dimensionProfileEnergy_eq_cube k j
  · intro t ht0 ht
    rw [sieveProfile_zero_of_not_unitCube k j t ht0 ht, zero_pow (by norm_num : 2 ≠ 0)]

theorem sieveProfile_cons (k j : ℕ) (x : ℝ) (t : Fin j → ℝ) :
    sieveProfile k (j + 1) (Fin.cons x t) =
      (∏ i, dimensionProfileFactor k (t i)) *
        (dimensionProfileFactor k x * sieveCutoff ((∑ i, t i) + x)) := by
  simp only [sieveProfile, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Fin.cons_zero, Fin.cons_succ]
  rw [add_comm x]
  ring

theorem sieveProfile_face_integral (k j : ℕ) (t : Fin j → ℝ) :
    (∫ x in (0 : ℝ)..1, sieveProfile k (j + 1) (Fin.cons x t)) =
      (∏ i, dimensionProfileFactor k (t i)) * dimensionFaceCutoff k (∑ i, t i) := by
  simp_rw [sieveProfile_cons]
  rw [intervalIntegral.integral_const_mul, dimensionFaceCutoff, cutoffAverage_eq_interval]

theorem dimensionFaceEnergy_eq_cube (k j : ℕ) :
    dimensionFaceEnergy k j =
      ∫ t in BoundedGaps.Maynard.maynardCubeOf (Fin j),
        (∫ x in (0 : ℝ)..1, sieveProfile k (j + 1) (Fin.cons x t)) ^ 2 := by
  rw [dimensionFaceEnergy, cutoffCubeIntegral_eq_cube]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    dsimp only
    rw [sieveProfile_face_integral]
    simp only [zero_add, Finset.prod_pow, mul_pow]

theorem dimensionProfileFactor_zero_of_one_le {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) {t : ℝ} (ht : 1 ≤ t) : dimensionProfileFactor k t = 0 := by
  have hb := profile_scales_bounds hk hlog
  exact sieveFactor_zero_of_ge hb.2.1 (by linarith [hb.2.2.1]) (sieveProfileScale k)

theorem sieveProfile_face_integral_orthant {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (j : ℕ) (t : Fin j → ℝ) :
    (∫ x in Set.Ioi (0 : ℝ), sieveProfile k (j + 1) (Fin.cons x t)) =
      (∏ i, dimensionProfileFactor k (t i)) * dimensionFaceCutoff k (∑ i, t i) := by
  rw [Erdos4b.integral_Ioi_eq_unitInterval]
  · change (∫ x, sieveProfile k (j + 1) (Fin.cons x t) ∂unitIntervalMeasure) = _
    rw [unitIntervalMeasure_integral, sieveProfile_face_integral]
  · intro x hx
    rw [sieveProfile_cons, dimensionProfileFactor_zero_of_one_le hk hlog hx.le,
      zero_mul, mul_zero]

theorem dimensionFaceEnergy_eq_orthant {k : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (j : ℕ) :
    dimensionFaceEnergy k j =
      ∫ t : Fin j → ℝ in Set.univ.pi (fun _ => Set.Ioi 0),
        (∫ x in Set.Ioi (0 : ℝ), sieveProfile k (j + 1) (Fin.cons x t)) ^ 2 := by
  classical
  rw [Erdos4b.integral_positiveOrthant_eq_unitCube]
  · rw [dimensionFaceEnergy_eq_cube]
    apply integral_congr_ae
    exact ae_of_all _ fun t => by
      dsimp only
      rw [sieveProfile_face_integral, sieveProfile_face_integral_orthant hk hlog]
  · intro t ht0 ht
    have hex : ∃ i, 1 < t i := by
      by_contra hh
      push Not at hh
      exact ht (fun i _ => ⟨ht0 i, hh i⟩)
    obtain ⟨i, hi⟩ := hex
    rw [sieveProfile_face_integral_orthant hk hlog,
      Finset.prod_eq_zero (Finset.mem_univ i)
        (dimensionProfileFactor_zero_of_one_le hk hlog hi.le),
      zero_mul, zero_pow (by norm_num : 2 ≠ 0)]

theorem sieveProfile_orthant_variational_bounds {k : ℕ}
    (hlog : 10000 ≤ Real.log (k + 1 : ℕ)) :
    Real.log (k + 1 : ℕ) / (16 * (k + 1 : ℕ)) ≤
      (∫ t : Fin k → ℝ in Set.univ.pi (fun _ => Set.Ioi 0),
        (∫ x in Set.Ioi (0 : ℝ), sieveProfile (k + 1) (k + 1) (Fin.cons x t)) ^ 2) /
      (∫ t : Fin (k + 1) → ℝ in Set.univ.pi (fun _ => Set.Ioi 0),
        sieveProfile (k + 1) (k + 1) t ^ 2) ∧
    (∫ t : Fin k → ℝ in Set.univ.pi (fun _ => Set.Ioi 0),
        (∫ x in Set.Ioi (0 : ℝ), sieveProfile (k + 1) (k + 1) (Fin.cons x t)) ^ 2) /
      (∫ t : Fin (k + 1) → ℝ in Set.univ.pi (fun _ => Set.Ioi 0),
        sieveProfile (k + 1) (k + 1) t ^ 2) ≤
      6 * Real.log (k + 1 : ℕ) / (k + 1 : ℕ) := by
  rw [← dimensionProfileEnergy_eq_orthant,
    ← dimensionFaceEnergy_eq_orthant (Nat.succ_pos k) hlog]
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
    dimensionProfile_variational_ratio_bounds (Nat.succ_pos k) hlog

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sieveProfile_contDiff
#print axioms Erdos4b.FGKMT.dimensionProfileEnergy_eq_orthant
#print axioms Erdos4b.FGKMT.dimensionFaceEnergy_eq_orthant
#print axioms Erdos4b.FGKMT.sieveProfile_orthant_variational_bounds
