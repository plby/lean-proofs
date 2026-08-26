import ErdosProblems.Erdos1148.PellAutomorphisms
import ErdosProblems.Erdos1148.FlowStabilizer
import ErdosProblems.Erdos1148.FormActionBaseChange

/-!
# Positive periods of integral-form trajectories

A Pell automorphism and the split-form stabilizer give a positive real
flow time whose translation agrees with an integral matrix translation.
Thus the trajectory is periodic after passing to the modular quotient.
-/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma form_lift_automorphism_action {d : ℤ} (hd : 0 < d) {t : ℤ × ℤ × ℤ}
    {g : SL(2, ℝ)} (hg : Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) =
      mapCoeffs (Int.castRingHom ℝ) t)
    {γ : SL(2, ℤ)} (hγ : formAction γ t = t) :
    formAction ((γ : SL(2, ℝ)) * g) (splitForm ℝ) = formAction g (splitForm ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hρ : Real.sqrt (d : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hdR).ne'
  have hscale : Real.sqrt (d : ℝ) • formAction ((γ : SL(2, ℝ)) * g) (splitForm ℝ) =
      Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) := by
    rw [formAction_mul, ← formAction_smul, hg]
    rw [← mapCoeffs_formAction, hγ]
  have heq := congrArg (fun v : ℝ × ℝ × ℝ => (Real.sqrt (d : ℝ))⁻¹ • v) hscale
  simpa only [smul_smul, inv_mul_cancel₀ hρ, one_smul] using heq

theorem exists_nonzero_integral_flow_period {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (g : SL(2, ℝ))
    (hg : Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) =
      mapCoeffs (Int.castRingHom ℝ) t) :
    ∃ T : ℝ, T ≠ 0 ∧ ∃ γ : SL(2, ℤ), (γ : SL(2, ℝ)) * g = g * diagonalFlow T := by
  obtain ⟨γ, hγ, htrace⟩ := exists_integral_form_automorphism hd hns ht
  have hγone : γ ≠ 1 := by
    intro heq
    rw [heq] at htrace
    norm_num at htrace
  have hγneg : γ ≠ -1 := by
    intro heq
    rw [heq] at htrace
    norm_num at htrace
  have hγRone : (γ : SL(2, ℝ)) ≠ 1 := by
    intro heq
    apply hγone
    apply Matrix.SpecialLinearGroup.map_intCast_injective (R := ℝ)
    simpa using heq
  have hγRneg : (γ : SL(2, ℝ)) ≠ -1 := by
    intro heq
    apply hγneg
    apply Matrix.SpecialLinearGroup.map_intCast_injective (R := ℝ)
    simpa using heq
  have hact := form_lift_automorphism_action hd hg hγ
  obtain ⟨T, hT | hT⟩ := exists_signed_flow_of_formAction_eq hact.symm
  · have hT0 : T ≠ 0 := by
      intro heq
      apply hγRone
      apply mul_right_cancel (b := g)
      simpa only [heq, diagonalFlow_zero, mul_one, one_mul] using hT
    exact ⟨T, hT0, γ, hT⟩
  · have hT0 : T ≠ 0 := by
      intro heq
      apply hγRneg
      apply mul_right_cancel (b := g)
      simpa only [heq, diagonalFlow_zero, mul_one, neg_mul, one_mul] using hT
    refine ⟨T, hT0, -γ, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_int_neg, neg_mul, hT, neg_neg]

theorem exists_positive_integral_flow_period {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (g : SL(2, ℝ))
    (hg : Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) =
      mapCoeffs (Int.castRingHom ℝ) t) :
    ∃ T : ℝ, 0 < T ∧ ∃ γ : SL(2, ℤ), (γ : SL(2, ℝ)) * g = g * diagonalFlow T := by
  obtain ⟨T, hT, γ, hγ⟩ := exists_nonzero_integral_flow_period hd hns ht g hg
  rcases hT.lt_or_gt with hneg | hpos
  · refine ⟨-T, neg_pos.mpr hneg, γ⁻¹, ?_⟩
    have hinv : ((γ⁻¹ : SL(2, ℤ)) : SL(2, ℝ)) = (γ : SL(2, ℝ))⁻¹ :=
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)).map_inv γ
    calc
      ((γ⁻¹ : SL(2, ℤ)) : SL(2, ℝ)) * g =
          ((γ⁻¹ : SL(2, ℤ)) : SL(2, ℝ)) * (g * diagonalFlow T) * (diagonalFlow T)⁻¹ := by
        simp [mul_assoc]
      _ = ((γ⁻¹ : SL(2, ℤ)) : SL(2, ℝ)) * ((γ : SL(2, ℝ)) * g) *
          (diagonalFlow T)⁻¹ := by rw [hγ]
      _ = g * (diagonalFlow T)⁻¹ := by rw [hinv, ← mul_assoc, inv_mul_cancel, one_mul]
      _ = g * diagonalFlow (-T) := by rw [diagonalFlow_neg]
  · exact ⟨T, hpos, γ, hγ⟩

end Erdos1148.DukeArithmetic
