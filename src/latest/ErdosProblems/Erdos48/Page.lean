import BoundedGaps.BombieriVinogradov.Analytic.NonprincipalExceptionalZero
import BoundedGaps.BombieriVinogradov.Analytic.InducingEulerProduct

/-!
# The Page uniqueness input for Erdős 48

This file extracts the cross-modulus near-one-zero uniqueness needed by the
Ford--Luca--Pomerance good-scale selection from the logarithmic zero-free
machinery already proved in `BoundedGaps`.
-/

noncomputable section

open Complex

namespace Erdos48

open BoundedGaps.Maynard

/-- A real zero of a primitive nonprincipal Dirichlet L-function. -/
structure PrimitiveRealZero where
  modulus : ℕ
  modulus_gt_one : 1 < modulus
  character : DirichletCharacter ℂ modulus
  isPrimitive : character.IsPrimitive
  ne_one : character ≠ 1
  beta : ℝ
  beta_pos : 0 < beta
  beta_lt_one : beta < 1
  isZero :
    let _ : NeZero modulus :=
      ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt modulus_gt_one)⟩
    DirichletCharacter.LFunction character (beta : ℂ) = 0

instance (z : PrimitiveRealZero) : NeZero z.modulus :=
  ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt z.modulus_gt_one)⟩

/-- A zero lying in the Page window at scale `Q`. -/
def InPageWindow (Q : ℕ) (c : ℝ) (z : PrimitiveRealZero) : Prop :=
  z.modulus ≤ Q ∧ 1 - c / Real.log Q < z.beta

private lemma lifted_nonprincipal_zero
    (z : PrimitiveRealZero) {L : ℕ} [NeZero L] (hzL : z.modulus ∣ L) :
    IsNonprincipalNontrivialLFunctionZero
      (z.character.changeLevel hzL) (z.beta : ℂ) := by
  apply (isNonprincipalNontrivialLFunctionZero_iff _ _).2
  refine ⟨?_, ?_, by simpa using z.beta_pos, by simpa using z.beta_lt_one⟩
  · exact (DirichletCharacter.changeLevel_eq_one_iff hzL).not.mpr z.ne_one
  · rw [DirichletCharacter.LFunction_changeLevel hzL z.character
      (.inl z.ne_one), z.isZero, zero_mul]

/-- Page's theorem in the exact form needed below: after choosing one
absolute positive constant, two primitive zeros in the common Page window
must have the same conductor and the same real zero. -/
theorem exists_pageConstant_modulus_eq_and_beta_eq :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Q : ℕ), 3 ≤ Q →
        ∀ z₁ z₂ : PrimitiveRealZero,
          InPageWindow Q c z₁ → InPageWindow Q c z₂ →
            z₁.modulus = z₂.modulus ∧ z₁.beta = z₂.beta := by
  obtain ⟨M, hM, hunique⟩ :=
    exists_nat_nonprincipalNontrivialLFunctionZero_character_eq_and_zero_eq
  let c : ℝ := 1 / (3 * (M : ℝ) ^ 2)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro Q hQ z₁ z₂ hz₁ hz₂
  let L := Nat.lcm z₁.modulus z₂.modulus
  have hLpos : 0 < L := Nat.lcm_pos
    (Nat.zero_lt_of_lt z₁.modulus_gt_one)
    (Nat.zero_lt_of_lt z₂.modulus_gt_one)
  let _ : NeZero L := ⟨hLpos.ne'⟩
  let χ₁ : DirichletCharacter ℂ L :=
    z₁.character.changeLevel (Nat.dvd_lcm_left _ _)
  let χ₂ : DirichletCharacter ℂ L :=
    z₂.character.changeLevel (Nat.dvd_lcm_right _ _)
  have hLle : L ≤ Q ^ 2 := by
    calc
      L ≤ z₁.modulus * z₂.modulus := Nat.lcm_le_mul
        (Nat.zero_lt_of_lt z₁.modulus_gt_one)
        (Nat.zero_lt_of_lt z₂.modulus_gt_one)
      _ ≤ Q * Q := Nat.mul_le_mul hz₁.1 hz₂.1
      _ = Q ^ 2 := by ring
  have htwoLle : 2 * L ≤ Q ^ 3 := by
    calc
      2 * L ≤ 2 * Q ^ 2 := Nat.mul_le_mul_left 2 hLle
      _ ≤ Q * Q ^ 2 := Nat.mul_le_mul_right (Q ^ 2) (by omega : 2 ≤ Q)
      _ = Q ^ 3 := by ring
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 3) hQ))
  have hlogL : 0 < Real.log ((L : ℝ) * 2) := by
    apply Real.log_pos
    have : (1 : ℕ) < 2 * L := by omega
    have hcast : (1 : ℝ) < ((2 * L : ℕ) : ℝ) := by exact_mod_cast this
    simpa [Nat.cast_mul, mul_comm] using hcast
  have hlogCompare :
      Real.log ((L : ℝ) * 2) ≤ 3 * Real.log (Q : ℝ) := by
    calc
      Real.log ((L : ℝ) * 2) = Real.log ((2 * L : ℕ) : ℝ) := by
        norm_num [Nat.cast_mul, mul_comm]
      _ ≤ Real.log ((Q ^ 3 : ℕ) : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast htwoLle)
      _ = 3 * Real.log (Q : ℝ) := by
        rw [Nat.cast_pow, Real.log_pow]
        norm_num
  have hthreshold (z : PrimitiveRealZero) (hz : InPageWindow Q c z) :
      1 - 1 / ((M : ℝ) ^ 2 *
          Real.log ((L : ℝ) * (|(z.beta : ℂ).im| + 2))) ≤ z.beta := by
    have hdenPos : 0 < (M : ℝ) ^ 2 * Real.log ((L : ℝ) * 2) :=
      mul_pos (sq_pos_of_pos hMpos) hlogL
    have hcompareDen :
        (M : ℝ) ^ 2 * Real.log ((L : ℝ) * 2) ≤
          3 * (M : ℝ) ^ 2 * Real.log (Q : ℝ) := by
      nlinarith [sq_nonneg (M : ℝ)]
    have hinv :
        1 / (3 * (M : ℝ) ^ 2 * Real.log (Q : ℝ)) ≤
          1 / ((M : ℝ) ^ 2 * Real.log ((L : ℝ) * 2)) := by
      apply one_div_le_one_div_of_le hdenPos
      nlinarith [hMpos, hlogQ]
    have hcRewrite : c / Real.log (Q : ℝ) =
        1 / (3 * (M : ℝ) ^ 2 * Real.log (Q : ℝ)) := by
      dsimp [c]
      field_simp [hMpos.ne', hlogQ.ne']
    have hzPage := hz.2
    rw [hcRewrite] at hzPage
    have hzNear : 1 - 1 / ((M : ℝ) ^ 2 *
        Real.log ((L : ℝ) * 2)) < z.beta := by
      linarith
    simpa using hzNear.le
  have hzero₁ : IsNonprincipalNontrivialLFunctionZero χ₁ (z₁.beta : ℂ) := by
    exact lifted_nonprincipal_zero z₁ (Nat.dvd_lcm_left _ _)
  have hzero₂ : IsNonprincipalNontrivialLFunctionZero χ₂ (z₂.beta : ℂ) := by
    exact lifted_nonprincipal_zero z₂ (Nat.dvd_lcm_right _ _)
  have heq := hunique L χ₁ χ₂ (z₁.beta : ℂ) (z₂.beta : ℂ)
    hzero₁ hzero₂ (hthreshold z₁ hz₁) (hthreshold z₂ hz₂)
  have hmodulus : z₁.modulus = z₂.modulus := by
    have hcond := congrArg DirichletCharacter.conductor heq.1
    calc
      z₁.modulus = z₁.character.conductor := z₁.isPrimitive.symm
      _ = χ₁.conductor := by
        dsimp [χ₁]
        rw [DirichletCharacter.conductor_changeLevel]
      _ = χ₂.conductor := hcond
      _ = z₂.character.conductor := by
        dsimp [χ₂]
        rw [DirichletCharacter.conductor_changeLevel]
      _ = z₂.modulus := z₂.isPrimitive
  refine ⟨hmodulus, ?_⟩
  exact_mod_cast congrArg Complex.re heq.2

end Erdos48
