import ErdosProblems.Erdos1002.RealFourierConjugacy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Zero and negative modes of the natural-cutoff shot error

The positive coefficient was computed by finite cell integration in
`NaturalCutoffShotCoefficientBridge`.  This file supplies the two symmetry
cases needed for a full Parseval argument: the zero coefficient vanishes,
and negative coefficients are exact conjugates.
-/

open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace Erdos1002

noncomputable section

/-- The synthesized strict natural-denominator tail has no zero mode. -/
theorem fourierCoeff_strictNaturalTailL2_zero
    (N P : ℕ) (hN : 0 < N) (hP : 0 < P) :
    fourierCoeff
        (strictNaturalTailL2 N P : AddCircle (1 : ℝ) → ℂ) 0 = 0 := by
  let g : ℕ ⊕ ℕ → ℂ := fun i ↦
    fourierCoefficientCLM 0 (strictNaturalTailFourierTerm N P i)
  have hg (i : ℕ ⊕ ℕ) : g i = 0 := by
    have hmode : signedNonzeroMode i ≠ 0 := by
      rcases i with i | i <;> simp only [signedNonzeroMode]
      all_goals omega
    simp only [g, strictNaturalTailFourierTerm, map_smul,
      fourierCoefficientCLM_apply, fourierCoeff_fourierLp, smul_eq_mul]
    rw [if_neg hmode.symm]
    ring
  have hmapped : HasSum g
      (fourierCoefficientCLM 0 (strictNaturalTailL2 N P)) := by
    have h := (fourierCoefficientCLM 0).hasSum
      (summable_strictNaturalTailFourierTerm N P hN hP).hasSum
    simpa only [g, strictNaturalTailL2] using! h
  have hzero : HasSum g 0 :=
    (hasSum_zero : HasSum (fun _ : ℕ ⊕ ℕ ↦ (0 : ℂ)) 0).congr_fun hg
  have hu := hmapped.unique hzero
  simpa only [fourierCoefficientCLM_apply] using! hu

/-- Exact coefficient of the strict natural tail at a negative natural
frequency. -/
theorem fourierCoeff_strictNaturalTailL2_neg
    (N P n : ℕ) (hN : 0 < N) (hP : 0 < P) (hn : 0 < n) :
    fourierCoeff
        (strictNaturalTailL2 N P : AddCircle (1 : ℝ) → ℂ) (-(n : ℤ)) =
      starRingEnd ℂ
        (naturalCoefficientNormalization *
          (crudeAllPTailCoefficient N P n : ℂ)) := by
  let i₀ : ℕ ⊕ ℕ := Sum.inr (n - 1)
  have hi₀mode : signedNonzeroMode i₀ = -(n : ℤ) := by
    dsimp [i₀, signedNonzeroMode]
    omega
  have hi₀scalar : strictNaturalTailScalar N P i₀ =
      starRingEnd ℂ
        (naturalCoefficientNormalization *
          (crudeAllPTailCoefficient N P n : ℂ)) := by
    dsimp [i₀, strictNaturalTailScalar]
    rw [Nat.sub_add_cancel hn]
  let g : ℕ ⊕ ℕ → ℂ := fun i ↦
    fourierCoefficientCLM (-(n : ℤ))
      (strictNaturalTailFourierTerm N P i)
  have hg (i : ℕ ⊕ ℕ) :
      g i = if i = i₀ then strictNaturalTailScalar N P i₀ else 0 := by
    by_cases hi : i = i₀
    · subst i
      simp only [g, strictNaturalTailFourierTerm, map_smul,
        fourierCoefficientCLM_apply, fourierCoeff_fourierLp, smul_eq_mul]
      rw [hi₀mode]
      simp
    · have hmode : signedNonzeroMode i ≠ -(n : ℤ) := by
        intro h
        apply hi
        apply signedNonzeroMode_injective
        exact h.trans hi₀mode.symm
      simp only [g, strictNaturalTailFourierTerm, map_smul,
        fourierCoefficientCLM_apply, fourierCoeff_fourierLp, smul_eq_mul]
      rw [if_neg hmode.symm, if_neg hi]
      ring
  have hmapped : HasSum g
      (fourierCoefficientCLM (-(n : ℤ)) (strictNaturalTailL2 N P)) := by
    have h := (fourierCoefficientCLM (-(n : ℤ))).hasSum
      (summable_strictNaturalTailFourierTerm N P hN hP).hasSum
    simpa only [g, strictNaturalTailL2] using! h
  have hone : HasSum g (strictNaturalTailScalar N P i₀) :=
    (hasSum_ite_eq i₀ (strictNaturalTailScalar N P i₀)).congr_fun hg
  have hu := hmapped.unique hone
  rw [fourierCoefficientCLM_apply] at hu
  exact hu.trans hi₀scalar

/-- The finite natural-denominator reconstruction has zero mean. -/
theorem fourierCoeff_naturalCutoffReconstructionL2_zero
    (N : ℕ+) (P : ℕ) (hP : 0 < P) :
    fourierCoeff
        (naturalCutoffReconstructionL2 N P : AddCircle (1 : ℝ) → ℂ) 0 = 0 := by
  rw [← fourierCoefficientCLM_apply]
  simp only [naturalCutoffReconstructionL2, map_sub,
    fourierCoefficientCLM_apply]
  rw [fourierCoeff_allDenominatorReconstructionL2_int,
    fourierCoeff_strictNaturalTailL2_zero (N : ℕ) P N.pos hP]
  simp [exactAllDenominatorCoefficient]

/-- The finite natural-denominator reconstruction is real in the exact
Fourier sense. -/
theorem fourierCoeff_naturalCutoffReconstructionL2_neg
    (N : ℕ+) (P n : ℕ) (hP : 0 < P) (hn : 0 < n) :
    fourierCoeff
        (naturalCutoffReconstructionL2 N P : AddCircle (1 : ℝ) → ℂ)
          (-(n : ℤ)) =
      starRingEnd ℂ
        (fourierCoeff
          (naturalCutoffReconstructionL2 N P : AddCircle (1 : ℝ) → ℂ)
            (n : ℤ)) := by
  rw [← fourierCoefficientCLM_apply, ← fourierCoefficientCLM_apply]
  simp only [naturalCutoffReconstructionL2, map_sub,
    fourierCoefficientCLM_apply]
  rw [fourierCoeff_allDenominatorReconstructionL2_neg,
    fourierCoeff_strictNaturalTailL2_neg (N : ℕ) P n N.pos hP hn,
    fourierCoeff_strictNaturalTailL2_pos (N : ℕ) P n N.pos hP hn]

/-- The literal natural-cutoff shot error has zero coefficient at the
origin. -/
theorem naturalCutoffShotErrorCoefficient_zero (N : ℕ+) :
    naturalCutoffShotErrorCoefficient N 0 = 0 := by
  unfold naturalCutoffShotErrorCoefficient
  rw [fourierCoeff_naturalCutoffReconstructionL2_zero N (N : ℕ) N.pos,
    fourierCoeff_reconstructedShotL2_zero]
  ring

/-- Negative coefficients of the literal error are conjugates of the
positive coefficients. -/
theorem naturalCutoffShotErrorCoefficient_neg_nat
    (N : ℕ+) (n : ℕ) (hn : 0 < n) :
    naturalCutoffShotErrorCoefficient N (-(n : ℤ)) =
      starRingEnd ℂ (naturalCutoffShotErrorCoefficient N (n : ℤ)) := by
  unfold naturalCutoffShotErrorCoefficient
  rw [fourierCoeff_naturalCutoffReconstructionL2_neg
      N (N : ℕ) n N.pos hn,
    fourierCoeff_reconstructedShotL2_neg,
    map_sub]

/-- Conjugacy of the error coefficient at every integer frequency. -/
theorem naturalCutoffShotErrorCoefficient_neg
    (N : ℕ+) (n : ℤ) :
    naturalCutoffShotErrorCoefficient N (-n) =
      starRingEnd ℂ (naturalCutoffShotErrorCoefficient N n) := by
  cases n with
  | ofNat n =>
      cases n with
      | zero => simp [naturalCutoffShotErrorCoefficient_zero]
      | succ n =>
          exact naturalCutoffShotErrorCoefficient_neg_nat N (n + 1) (by omega)
  | negSucc n =>
      let m : ℕ := n + 1
      have h := naturalCutoffShotErrorCoefficient_neg_nat N m (by omega)
      have hs := congrArg (starRingEnd ℂ) h
      simpa only [map_neg, starRingEnd_self_apply] using! hs.symm

/-- Full Parseval energy splits into two identical positive-frequency
halves; the zero term vanishes exactly. -/
theorem tsum_sq_naturalCutoffShotErrorCoefficient_eq_two_mul_positive
    (N : ℕ+) :
    (∑' z : ℤ, ‖naturalCutoffShotErrorCoefficient N z‖ ^ 2) =
      2 * ∑' n : ℕ+,
        ‖naturalCutoffShotErrorCoefficient N (n : ℤ)‖ ^ 2 := by
  let f : ℤ → ℝ := fun z ↦ ‖naturalCutoffShotErrorCoefficient N z‖ ^ 2
  have hs : Summable f := by
    have h := (hasSum_sq_fourierCoeff (naturalCutoffShotErrorL2 N)).summable
    simpa only [f, fourierCoeff_naturalCutoffShotErrorL2] using! h
  have heven : f.Even := by
    intro z
    dsimp [f]
    rw [naturalCutoffShotErrorCoefficient_neg, starRingEnd_apply, norm_star]
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hs]
  simp only [f, naturalCutoffShotErrorCoefficient_zero, norm_zero,
    zero_pow (by omega : (2 : ℕ) ≠ 0), zero_add, nsmul_eq_mul]
  norm_num

end

end Erdos1002
