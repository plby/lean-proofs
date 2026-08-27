import ErdosProblems.Erdos587.HooleyIntervalExtraction
import ErdosProblems.Erdos587.HooleyCubicForcing
import ErdosProblems.Erdos587.HooleyFinalBudgets

/-! # Unconditional finite square forcing at the log-log cube-root scale -/

open Filter

namespace Erdos587

theorem exists_delta_finite_square_forcing :
    ∃ J : ℕ, 0 < J ∧ ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
      (J : ℝ) * N * (max 1 (Real.log (Real.log (N : ℝ)))) ^ 48 ≤ (A.card : ℝ) ^ 3 →
      ¬ SquareSubsetSumFree A := by
  obtain ⟨R, d, F, C, hR, _hd, hF, hC, hstructure⟩ := CFP.exists_delta_interval_full_width
  obtain ⟨E, hE, Tmin, hforce⟩ := exists_delta_cubic_structural_forcing R d F C hR hF hC
  let J := R ^ 3 * E * 3 ^ 44
  let m₀ := ⌈(F : ℝ) * Tmin⌉₊ + 1
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hmin₀ : (F : ℝ) * Tmin ≤ (m₀ : ℝ) := by
    have hh := Nat.le_ceil ((F : ℝ) * Tmin)
    dsimp only [m₀]
    push_cast
    linarith
  refine ⟨J, hJ, ?_⟩
  filter_upwards [hstructure, eventually_ge_atTop 2, eventually_ge_atTop R,
    eventually_ge_atTop ((R * m₀) ^ 3)] with N hstruct hN hRN hNmin
  intro A hA hlarge
  let L := max 1 (Real.log (Real.log (N : ℝ)))
  have hL : 1 ≤ L := le_max_left _ _
  have hJone : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hcubic : N ≤ A.card ^ 3 := by
    have hreal : (N : ℝ) ≤ (A.card : ℝ) ^ 3 := by
      calc
        (N : ℝ) = 1 * N * 1 := by ring
        _ ≤ (J : ℝ) * N * L ^ 48 := by
          gcongr
          exact one_le_pow₀ hL
        _ ≤ (A.card : ℝ) ^ 3 := hlarge
    exact_mod_cast hreal
  obtain ⟨m, hm, hretain, hmA, Q, hQpos, hQrank, hQproper, hQhom, hQsub,
      hside, hsize, hheight⟩ := hstruct A hA hcubic
  have hmN : m ≤ N := hmA.trans ((Finset.card_le_card hA).trans (by simp))
  have hM : R * m * N ≤ N ^ 3 := by
    calc
      _ ≤ N * N * N := Nat.mul_le_mul_right _ (Nat.mul_le_mul hRN hmN)
      _ = N ^ 3 := by ring
  have hm₀ : m₀ ≤ m := by
    have hpow : (R * m₀) ^ 3 ≤ (R * m) ^ 3 :=
      hNmin.trans (hcubic.trans (Nat.pow_le_pow_left hretain 3))
    exact Nat.le_of_mul_le_mul_left
      ((Nat.pow_le_pow_iff_left (by omega : (3 : ℕ) ≠ 0)).mp hpow) hR
  have hmin : (F : ℝ) * Tmin ≤ m := hmin₀.trans (by exact_mod_cast hm₀)
  have hsurplus : (E : ℝ) * N * (3 * L) ^ 44 ≤ (m : ℝ) ^ 3 :=
    delta_final_cubic_surplus R E A.card m N hR hretain L hL hlarge
  exact hforce A N m Q (3 * L) hA (by omega) hm hretain hQpos hQrank hQproper hQhom
    hQsub hside hsize hheight (by linarith) (delta_loglog_of_cubic_ambient hN hM) hmin hsurplus

end Erdos587
