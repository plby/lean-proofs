import ErdosProblems.Erdos67b.MRTWindowFourthExpansion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Geometric cancellation on the common cofactor interval -/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

theorem mrtAdditivePhase_sub_int (t : ℝ) (z : ℤ) :
    additivePhase (t - z) 1 = additivePhase t 1 := by
  unfold additivePhase
  have hexp : Complex.exp ((z : ℂ) * (2 * Real.pi * Complex.I)) = 1 :=
    Complex.exp_int_mul_two_pi_mul_I z
  rw [show 2 * (Real.pi : ℂ) * ((t - z : ℝ) : ℂ) * (1 : ℕ) * Complex.I =
      2 * (Real.pi : ℂ) * (t : ℂ) * (1 : ℕ) * Complex.I -
        (z : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring,
    Complex.exp_sub, hexp, div_one]

theorem mrtAdditivePhase_chord_lower (t : ℝ) :
    4 * Erdos69.MinorArc.nearestIntDist t ≤ ‖additivePhase t 1 - 1‖ := by
  let u : ℝ := t - round t
  have hu : |u| ≤ 1 / 2 := abs_sub_round t
  have harg : |Real.pi * u| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith only [mul_le_mul_of_nonneg_left hu Real.pi_pos.le]
  have hsin := Real.mul_abs_le_abs_sin harg
  rw [abs_mul, abs_of_pos Real.pi_pos] at hsin
  have hcancel : (2 / Real.pi) * (Real.pi * |u|) = 2 * |u| := by
    field_simp
  rw [hcancel] at hsin
  have hphase : additivePhase t 1 = Complex.exp (Complex.I * (2 * Real.pi * u : ℝ)) := by
    rw [← mrtAdditivePhase_sub_int t (round t)]
    unfold additivePhase
    congr 1
    dsimp [u]
    push_cast
    ring
  rw [hphase, Complex.norm_exp_I_mul_ofReal_sub_one,
    show (2 * Real.pi * u) / 2 = Real.pi * u by ring,
    Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  change 4 * |u| ≤ _
  linarith only [hsin]

theorem mrtGeometricPhaseSum_le_capped (t cap : ℝ) (L N : ℕ)
    (hN : (N : ℝ) ≤ 2 * cap) :
    ‖geometricPhaseSum t L N‖ ≤ 2 * Erdos69.MinorArc.cappedInvDist cap t := by
  unfold Erdos69.MinorArc.cappedInvDist
  split_ifs with hd
  · exact (norm_geometricPhaseSum_le_length t L N).trans hN
  · have hdpos : 0 < Erdos69.MinorArc.nearestIntDist t :=
      lt_of_le_of_ne (Erdos69.MinorArc.nearestIntDist_nonneg t) (Ne.symm hd)
    have hchord := mrtAdditivePhase_chord_lower t
    have hdist : Erdos69.MinorArc.nearestIntDist t ≤ ‖additivePhase t 1 - 1‖ := by
      linarith only [hchord, hdpos]
    have hphase : additivePhase t 1 ≠ 1 := by
      intro hh
      rw [hh, sub_self, norm_zero] at hdist
      exact (not_le_of_gt hdpos) hdist
    have hcancel : ‖geometricPhaseSum t L N‖ ≤
        2 * (Erdos69.MinorArc.nearestIntDist t)⁻¹ := by
      apply (norm_geometricPhaseSum_le_two_div t L N hphase).trans
      simpa only [div_eq_mul_inv] using
        (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hdpos hdist)
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    exact le_min ((norm_geometricPhaseSum_le_length t L N).trans hN) hcancel

theorem mrtSum_Ioc_phase_eq_geometric (t : ℝ) (L U : ℕ) :
    (∑ m ∈ Finset.Ioc L U, additivePhase t m) = geometricPhaseSum t (L + 1) (U - L) := by
  unfold geometricPhaseSum
  symm
  apply Finset.sum_bij (fun j _ ↦ L + 1 + j)
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Ioc]
    omega
  · intro i hi j hj hij
    omega
  · intro m hm
    simp only [Finset.mem_Ioc] at hm
    refine ⟨m - (L + 1), ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro j hj
    rfl

theorem mrtCofactorPhaseSum_le_weight (Z H M : ℕ) (p n : (ℕ × ℕ) × (ℕ × ℕ))
    (α : ℝ) (h₁₁ : 0 < p.1.1) (h₁₂ : 0 < p.1.2)
    (h₂₁ : 0 < p.2.1) (h₂₂ : 0 < p.2.2)
    {P : ℕ} (hP : 0 < P) (hPp : P ≤ p.1.1) (hPH : P ≤ H) :
    ‖mrtCofactorPhaseSum Z H M p n α‖ ≤
      2 * vinogradovWeight H P (α * (primeQuadrupleDifference p : ℝ)) := by
  unfold mrtCofactorPhaseSum
  rw [mrtQuadCofactors_eq_Ioc Z H M p n h₁₁ h₁₂ h₂₁ h₂₂,
    mrtSum_Ioc_phase_eq_geometric]
  apply mrtGeometricPhaseSum_le_capped
  have hlen := mrtQuadWindow_length_le Z H M p n hP hPp
  have hdiv : ((H / P : ℕ) : ℝ) ≤ (H : ℝ) / P := Nat.cast_div_le
  have hone : (1 : ℝ) ≤ (H : ℝ) / P := by
    apply (le_div_iff₀ (by exact_mod_cast hP)).2
    simpa using (show (P : ℝ) ≤ H by exact_mod_cast hPH)
  have hlen' : ((mrtQuadWindowUpper Z H M p n - mrtQuadWindowLower p n : ℕ) : ℝ) ≤
      ((H / P : ℕ) : ℝ) + 1 := by exact_mod_cast hlen
  linarith only [hlen', hdiv, hone]

end

end Erdos67b
