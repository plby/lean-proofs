import ErdosProblems.Erdos1148.RealDirichletSiegel
import ErdosProblems.Erdos1148.RealDirichletChangeLevel
import ErdosProblems.Erdos1148.ResidueUnitLowerBound

/-! # Siegel's lower bound for all nonprincipal real Dirichlet characters -/

namespace Erdos1148.DukeArithmetic

theorem exists_realDirichlet_siegel_lower_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ), 0 < q → ∀ (χ : DirichletCharacter ℝ q),
      χ ≠ 1 → c * (q : ℝ) ^ (-ε) ≤ realDirichletValue χ 1 := by
  obtain ⟨C, hC, hPrimitive⟩ := exists_primitive_realDirichlet_siegel_lower_bound (half_pos hε)
  obtain ⟨D, hD, hLoss⟩ := exists_four_pow_primeFactors_le_rpow (half_pos hε)
  refine ⟨C / D, div_pos hC hD, ?_⟩
  intro q hq χ hχ
  let : NeZero q := ⟨Nat.ne_zero_of_lt hq⟩
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hm : 0 < χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hmR : (0 : ℝ) < χ.conductor := by exact_mod_cast hm
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hmQ : χ.conductor ≤ q := Nat.le_of_dvd hq χ.conductor_dvd_level
  have hχ0 : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, h, map_one]
  have hp := hPrimitive χ.conductor hm χ.primitiveCharacter χ.primitiveCharacter_isPrimitive hχ0
  have hsmall : C * (q : ℝ) ^ (-(ε / 2)) ≤ realDirichletValue χ.primitiveCharacter 1 := by
    apply le_trans _ hp
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hmR (by exact_mod_cast hmQ) (by linarith)) hC.le
  have hEuler := realDirichletValue_le_primeFactorLoss_mul_changeLevel χ.conductor_dvd_level
    χ.primitiveCharacter hχ0
  rw [χ.changeLevel_primitiveCharacter] at hEuler
  have hmul : C * (q : ℝ) ^ (-(ε / 2)) ≤
      (D * (q : ℝ) ^ (ε / 2)) * realDirichletValue χ 1 :=
    (hsmall.trans hEuler).trans (mul_le_mul_of_nonneg_right (hLoss q (Nat.ne_zero_of_lt hq))
      (realDirichletValue_one_pos χ hχ).le)
  have hdiv : (C * (q : ℝ) ^ (-(ε / 2))) / (D * (q : ℝ) ^ (ε / 2)) ≤
      realDirichletValue χ 1 := by
    apply (div_le_iff₀ (mul_pos hD (Real.rpow_pos_of_pos hqR _))).mpr
    simpa only [mul_comm (realDirichletValue χ 1)] using hmul
  calc
    _ = (C / D) * ((q : ℝ) ^ (-(ε / 2)) / (q : ℝ) ^ (ε / 2)) := by
      rw [← Real.rpow_sub hqR, show -(ε / 2) - ε / 2 = -ε by ring]
    _ = (C * (q : ℝ) ^ (-(ε / 2))) / (D * (q : ℝ) ^ (ε / 2)) := by ring
    _ ≤ _ := hdiv

end Erdos1148.DukeArithmetic
