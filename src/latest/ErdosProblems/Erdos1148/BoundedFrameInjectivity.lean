import ErdosProblems.Erdos1148.EntryNeighborhoodAlgebra
import ErdosProblems.Erdos1148.ModularOrbitSpace

/-! # Quantitative injectivity of small modular quotient neighborhoods -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem entryCloseOne_integral_eq_one {η : ℝ} (hη : η < 1) (γ : SL(2, ℤ))
    (hγ : EntryCloseOne η (γ : SL(2, ℝ))) : γ = 1 := by
  have hentries := (entryCloseOne_iff_entries η (γ : SL(2, ℝ))).mp hγ
  ext i j
  have hlt := (hentries i j).trans_lt hη
  have hcast : (γ : SL(2, ℝ)) i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j =
      ((γ i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℝ) := by
    simp [Matrix.SpecialLinearGroup.coe_matrix_coe, Matrix.one_apply]
  rw [hcast] at hlt
  have hint : |γ i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j| < 1 := by exact_mod_cast hlt
  exact sub_eq_zero.mp (Int.abs_lt_one_iff.mp hint)

theorem integral_conjugate_eq_one_of_entryCloseOne {A η : ℝ}
    (hA : 0 ≤ A) (hη : 0 ≤ η) (hscale : 4 * A ^ 2 * η < 1)
    (g : SL(2, ℝ)) (hg : ∀ i j : Fin 2, |g i j| ≤ A) (γ : SL(2, ℤ))
    (hclose : EntryCloseOne η (g⁻¹ * (γ : SL(2, ℝ)) * g)) : γ = 1 := by
  have h := entryCloseOne_conjugate hA hη g hg hclose
  have heq : g * (g⁻¹ * (γ : SL(2, ℝ)) * g) * g⁻¹ = γ := by group
  rw [heq] at h
  exact entryCloseOne_integral_eq_one hscale γ h

theorem modularMk_injective_on_small_right_neighborhood {A η : ℝ}
    (hA : 0 ≤ A) (hη : 0 ≤ η) (hηone : η ≤ 1) (hscale : 16 * A ^ 2 * η < 1)
    (g : SL(2, ℝ)) (hg : ∀ i j : Fin 2, |g i j| ≤ A)
    {u v : SL(2, ℝ)} (hu : EntryCloseOne η u) (hv : EntryCloseOne η v)
    (heq : modularMk (g * u) = modularMk (g * v)) : u = v := by
  obtain ⟨γ, hγ⟩ := (modularMk_eq_iff _ _).mp heq
  have hγformula : (γ : SL(2, ℝ)) = (g * v) * (g * u)⁻¹ := by
    calc
      (γ : SL(2, ℝ)) = ((γ : SL(2, ℝ)) * (g * u)) * (g * u)⁻¹ := by group
      _ = (g * v) * (g * u)⁻¹ := by rw [hγ]
  have hrel : g⁻¹ * (γ : SL(2, ℝ)) * g = v * u⁻¹ := by
    rw [hγformula]
    group
  have hprod := entryCloseOne_mul hη hη hv (entryCloseOne_inv hu)
  have hsmall : EntryCloseOne (4 * η) (g⁻¹ * (γ : SL(2, ℝ)) * g) := by
    rw [hrel]
    exact entryCloseOne_mono hprod (by nlinarith [mul_nonneg hη (sub_nonneg.mpr hηone)])
  have hγone : γ = 1 := integral_conjugate_eq_one_of_entryCloseOne hA
    (by positivity) (by nlinarith [hscale]) g hg γ hsmall
  subst γ
  simpa using hγ

end Erdos1148.DukeArithmetic
