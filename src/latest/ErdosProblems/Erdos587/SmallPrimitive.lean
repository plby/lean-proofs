import ErdosProblems.Erdos587.UnitFiberTerminal
import ErdosProblems.Erdos587.SmallFiberScales
import ErdosProblems.Erdos587.ThickFiber

/-! The small-coefficient primitive terminal branch. -/

open Filter

namespace Erdos587

theorem exists_small_primitive_terminal (C : ℝ) (hC : 0 < C) :
    ∃ T₀ : ℝ, ∀ (t u v H J T : ℕ), T₀ ≤ (T : ℝ) →
      0 < u → 0 < H → u.Coprime v →
      t + u * H + v * J ≤ T → u * H ≤ v * J →
      (T : ℝ) ≤ C * ((u * H + v * J : ℕ) : ℝ) →
      (u : ℝ) ≤ (T : ℝ) ^ (1 / 16 : ℝ) →
      (T : ℝ) ^ (1 / 4 : ℝ) ≤ J →
      (J : ℝ) ≤ (T : ℝ) ^ (1 / 4 + 1 / 1000 : ℝ) →
      (T : ℝ) ^ (3 / 4 : ℝ) ≤ (H : ℝ) * J →
      ∃ x ≤ H, ∃ y ≤ J, ∃ z : ℕ, 0 < z ∧ z ^ 2 = t + u * x + v * y := by
  let C' := max 1 (4 * C)
  have hC' : 1 ≤ C' := le_max_left _ _
  obtain ⟨K, hK, hterminal⟩ := exists_unit_fiber_square hC'
  have hD : 0 < 8 * (8 * C') ^ 3 := by
    have : 0 < C' := by linarith
    positivity
  have hevent := (eventually_ge_atTop (1 : ℝ)).and
    (eventually_small_coefficient_length.and
      ((eventually_small_fiber_ratio hD).and (eventually_small_fiber_power_budget hK)))
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hevent
  refine ⟨T₀, ?_⟩
  intro t u v H J T hbig hu hH huv hambient horient hspan huhi hJlo hJhi hprod
  obtain ⟨hT1, hlength, hratio, hpower⟩ := hT₀ (T : ℝ) hbig
  have hTR : (0 : ℝ) < T := by linarith
  have hTN : 0 < T := by exact_mod_cast hTR
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hJR : (0 : ℝ) < J := (Real.rpow_pos_of_pos hTR _).trans_le hJlo
  have h16J := hlength u J huR.le huhi hJlo
  have h4J : 4 * u ≤ J := by
    have hh : 4 * (u : ℝ) ≤ J := by linarith
    exact_mod_cast hh
  obtain ⟨y₀, t', M, hy₀, ht', hM, hMlo, hMhi, hMnext, hidentity, hsub⟩ :=
    exists_unit_step_fiber hu huv.symm t h4J
  have hJM : (J : ℝ) ≤ 2 * u * M := by
    have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * u)).mp hMlo
    nlinarith
  have hM8 : 8 ≤ M := by
    have hh : (8 : ℝ) ≤ M := by nlinarith
    exact_mod_cast hh
  have hMupper : (M : ℝ) ≤ (J : ℝ) / u := by
    apply (le_div_iff₀ huR).mpr
    have hh : u * M ≤ J := by omega
    have hhR : (u : ℝ) * M ≤ J := by exact_mod_cast hh
    nlinarith
  have hambientFiber : u * (t' + H + v * M) ≤ T := by
    rw [hidentity H M]
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left v hMhi) (t + u * H)).trans hambient
  have hwidth : u * H ≤ T := by omega
  by_cases hthick : 4 * Real.sqrt T ≤ H
  · have hstart : u * t' ≤ T := by nlinarith
    obtain ⟨x, hx, z, hz, heq⟩ := exists_square_in_thick_unit_fiber hu hTN hstart hwidth hthick
    refine ⟨x, hx, y₀, by omega, z, hz, ?_⟩
    have hh := hidentity x 0
    simpa only [Nat.mul_zero, Nat.add_zero] using heq.trans hh
  · have hthin : (H : ℝ) ≤ 4 * Real.sqrt T := (lt_of_not_ge hthick).le
    have hspanR : (T : ℝ) ≤ C * ((u : ℝ) * H + v * J) := by
      simpa only [Nat.cast_add, Nat.cast_mul] using hspan
    have horientR : (u : ℝ) * H ≤ v * J := by exact_mod_cast horient
    have hspanFiber : (T : ℝ) ≤ C' * u * v * M := by
      calc
        (T : ℝ) ≤ 2 * C * v * J := by nlinarith
        _ ≤ (2 * C * v) * (2 * u * M) := mul_le_mul_of_nonneg_left hJM (by positivity)
        _ = (4 * C) * u * v * M := by ring
        _ ≤ C' * u * v * M := by gcongr; exact le_max_right 1 (4 * C)
    have hratioFiber := hratio u J M huR hJhi hMupper
    have hpowerFiber := hpower u H J M huR hHR.le hJR (Nat.cast_nonneg M) huhi hJhi hprod hJM
    obtain ⟨x, hx, j, hj, z, hz, heq⟩ := hterminal u t' v H M T hu hH hM8 hTR hthin
      (by exact_mod_cast hambientFiber) hspanFiber hratioFiber hpowerFiber
    exact ⟨x, hx, y₀ + u * j, hsub j hj, z, hz, heq.trans (hidentity x j)⟩

end Erdos587
