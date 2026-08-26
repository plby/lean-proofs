import ErdosProblems.Erdos1148.PrimitiveForms
import ErdosProblems.Erdos1148.PeriodPellMatrix

/-! # Integral Pell coordinates of periods of primitive forms -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_integral_pell_coordinates_of_primitive_period {d : ℤ} (hd : 0 < d)
    {t : ℤ × ℤ × ℤ} (ht : PrimitiveIntegralForm t) (g : SL(2, ℝ))
    (hg : Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t)
    (γ : SL(2, ℤ)) (s : ℝ) (hs : (γ : SL(2, ℝ)) * g = g * diagonalFlow s) :
    ∃ T U : ℤ, (T : ℝ) = 2 * Real.cosh (s / 2) ∧
      (U : ℝ) = -2 * Real.sinh (s / 2) / Real.sqrt (d : ℝ) ∧
      T ^ 2 - d * U ^ 2 = 4 ∧ Even (T - t.2.1 * U) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hρ := Real.sqrt_pos.mpr hdR
  have hm := integral_period_pellFormMatrix hd g hg γ s hs
  have hm₀₀ := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hm
  have hm₀₁ := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hm
  have hm₁₀ := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) hm
  have hm₁₁ := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) hm
  change (γ 0 0 : ℝ) = Real.cosh (s / 2) -
    (t.2.1 : ℝ) * (-Real.sinh (s / 2) / Real.sqrt (d : ℝ)) at hm₀₀
  change (γ 0 1 : ℝ) = -2 * (t.2.2 : ℝ) *
    (-Real.sinh (s / 2) / Real.sqrt (d : ℝ)) at hm₀₁
  change (γ 1 0 : ℝ) = 2 * (t.1 : ℝ) *
    (-Real.sinh (s / 2) / Real.sqrt (d : ℝ)) at hm₁₀
  change (γ 1 1 : ℝ) = Real.cosh (s / 2) +
    (t.2.1 : ℝ) * (-Real.sinh (s / 2) / Real.sqrt (d : ℝ)) at hm₁₁
  let u := -2 * Real.sinh (s / 2) / Real.sqrt (d : ℝ)
  have ha : (γ 1 0 : ℝ) = (t.1 : ℝ) * u := by dsimp [u]; linear_combination hm₁₀
  have hb : ((γ 1 1 - γ 0 0 : ℤ) : ℝ) = (t.2.1 : ℝ) * u := by
    push_cast
    dsimp [u]
    linear_combination hm₁₁ - hm₀₀
  have hc : ((-γ 0 1 : ℤ) : ℝ) = (t.2.2 : ℝ) * u := by
    push_cast
    dsimp [u]
    linear_combination -hm₀₁
  obtain ⟨U, hU⟩ := ht.integer_of_scaled_coefficients _ _ _ ha hb hc
  let T := γ 0 0 + γ 1 1
  have hT : (T : ℝ) = 2 * Real.cosh (s / 2) := by
    dsimp [T]
    push_cast
    linear_combination hm₀₀ + hm₁₁
  refine ⟨T, U, hT, hU, ?_, ?_⟩
  · have hroot := Real.sq_sqrt hdR.le
    have hnorm := Real.cosh_sq_sub_sinh_sq (s / 2)
    have hpell : (T : ℝ) ^ 2 - (d : ℝ) * (U : ℝ) ^ 2 = 4 := by
      rw [hT, hU]
      dsimp [u]
      rw [div_pow, hroot]
      field_simp
      nlinarith [hnorm]
    exact_mod_cast hpell
  · have hpar : T - t.2.1 * U = 2 * γ 0 0 := by
      have hparR : (T : ℝ) - (t.2.1 : ℝ) * U = 2 * (γ 0 0 : ℝ) := by
        rw [hU, ← hb]
        dsimp [T]
        push_cast
        ring
      exact_mod_cast hparR
    exact ⟨γ 0 0, by omega⟩

theorem flowPeriod_of_integral_pell_coordinates {d : ℤ} (hd : 0 < d)
    {t : ℤ × ℤ × ℤ} (g : SL(2, ℝ))
    (hg : Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t)
    (T U : ℤ) (s : ℝ) (hT : (T : ℝ) = 2 * Real.cosh (s / 2))
    (hU : (U : ℝ) = -2 * Real.sinh (s / 2) / Real.sqrt (d : ℝ))
    (hpar : Even (T - t.2.1 * U)) : s ∈ flowPeriodGroup g := by
  obtain ⟨k, hk⟩ := hpar
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![k, -t.2.2 * U; t.1 * U, k + t.2.1 * U]
  have hρ : Real.sqrt (d : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  have hU' : (U : ℝ) = 2 * (-Real.sinh (s / 2) / Real.sqrt (d : ℝ)) := by
    rw [hU]
    ring
  have hkR : (T : ℝ) - (t.2.1 : ℝ) * U = (k : ℝ) + k := by exact_mod_cast hk
  have hM : M.map (Int.castRingHom ℝ) =
      ((g * diagonalFlow s * g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [conjugate_diagonalFlow_pellFormMatrix]
    rw [← pellFormMatrix_smul_div _ hρ, hg]
    ext i j
    fin_cases i <;> fin_cases j <;> dsimp [M, Matrix.map, pellFormMatrix, mapCoeffs] <;> push_cast
    · linear_combination (hT - (t.2.1 : ℝ) * hU' - hkR) / 2
    · linear_combination -(t.2.2 : ℝ) * hU'
    · linear_combination (t.1 : ℝ) * hU'
    · linear_combination (hT + (t.2.1 : ℝ) * hU' - hkR) / 2
  have hdet : M.det = 1 := by
    have hdetR : (M.det : ℝ) = (1 : ℝ) := by
      change (Int.castRingHom ℝ) M.det = (1 : ℝ)
      rw [(Int.castRingHom ℝ).map_det]
      change (M.map (Int.castRingHom ℝ)).det = 1
      rw [hM, Matrix.SpecialLinearGroup.det_coe]
    exact_mod_cast hdetR
  let γ : SL(2, ℤ) := ⟨M, hdet⟩
  have hγ : (γ : SL(2, ℝ)) = g * diagonalFlow s * g⁻¹ := Subtype.ext hM
  refine ⟨γ, ?_⟩
  rw [hγ, mul_assoc, inv_mul_cancel, mul_one]

theorem primitive_flowPeriod_iff_pell_coordinates {d : ℤ} (hd : 0 < d)
    {t : ℤ × ℤ × ℤ} (ht : PrimitiveIntegralForm t) (g : SL(2, ℝ))
    (hg : Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t)
    (s : ℝ) : s ∈ flowPeriodGroup g ↔
      ∃ T U : ℤ, (T : ℝ) = 2 * Real.cosh (s / 2) ∧
        (U : ℝ) = -2 * Real.sinh (s / 2) / Real.sqrt (d : ℝ) ∧
        T ^ 2 - d * U ^ 2 = 4 ∧ Even (T - t.2.1 * U) := by
  constructor
  · rintro ⟨γ, hγ⟩
    exact exists_integral_pell_coordinates_of_primitive_period hd ht g hg γ s hγ
  · rintro ⟨T, U, hT, hU, _, hpar⟩
    exact flowPeriod_of_integral_pell_coordinates hd g hg T U s hT hU hpar

end Erdos1148.DukeArithmetic
