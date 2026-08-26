import ErdosProblems.Erdos421.IntegerLogIntegralCount
import ErdosProblems.Erdos421.PrimeFreeDyadicStarts
import ErdosProblems.Erdos421.PrimeShortWidth

/-! # An unconditional vanishing proportion of prime-free starts in each dyadic interval -/

namespace Erdos421

open MeasureTheory Filter Topology

theorem primeFreeDyadicStarts_eventually_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, ∀ H : ℕ, primeShortLength X ≤ (H : ℝ) →
      ((primeFreeDyadicStarts X H).card : ℝ) ≤ ε * X := by
  let σ : ℝ := ε / 4000
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  obtain ⟨L, hL, htransfer⟩ := intermediatePrimeMinorant_l1 (e := 1 / 1000)
    hσ (by norm_num) (by norm_num)
  norm_num only [show (9 / 10 - 1 / 1000 : ℝ) = 899 / 1000 by norm_num] at htransfer
  filter_upwards [htransfer, intermediatePrimeMinorant_reference_lower hL,
    eventually_reference_width_small hL (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_reference_width_small hL (Real.log_pos (by norm_num : (1 : ℝ) < 3 / 2)),
    eventually_ge_atTop 2] with X htransferX href hδhi hδlog hX
  intro H hH
  have hX1 : 1 ≤ X := by omega
  have hXr : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hXp : (0 : ℝ) < X := by linarith
  have hLX := Real.log_pos hXr
  have hδ := primeShortWidth_pos hXp
  have hminref : primeShortWidth X ≤ (Real.log X) ^ (-L) := htransferX.1
  let f : ℝ → ℝ := fun y ↦ |intermediatePrimeMinorant X (primeShortWidth X) y -
    intermediatePrimeMinorant X ((Real.log X) ^ (-L)) y|
  have hf : Continuous f := ((intermediatePrimeMinorant_continuous X (primeShortWidth X)).sub
    (intermediatePrimeMinorant_continuous X ((Real.log X) ^ (-L)))).abs
  have hi : (∫ y in Real.log (X : ℝ)..Real.log (2 * X : ℝ), f y) ≤ σ / Real.log X :=
    htransferX.2 (primeShortWidth X) ((Real.log X) ^ (-L)) le_rfl hminref hminref le_rfl
  let S := primeFreeDyadicStarts X H
  have hS : S ⊆ Finset.Ico X (2 * X) := Finset.filter_subset _ _
  have hpoint : ∀ m ∈ S, ∀ y ∈ Set.Icc (Real.log (m : ℝ)) (Real.log (m + 1 : ℝ)),
      1 / (2000 * Real.log X) ≤ f y := by
    intro m hm y hy
    obtain ⟨_, _, hfree⟩ := mem_primeFreeDyadicStarts.mp hm
    have hmI := hS hm
    have hs := primeMinorant_nonpos_on_primeFree hX1 hmI hfree hδ
      (hminref.trans hδhi) (hminref.trans hδlog)
      (by rwa [primeShortLength_eq hXp]) hy
    have hr := href y (integer_log_interval_subset hX1 hmI hy)
    have ha := neg_le_abs (intermediatePrimeMinorant X (primeShortWidth X) y -
      intermediatePrimeMinorant X ((Real.log X) ^ (-L)) y)
    dsimp only [f]
    linarith
  have hcard := integer_log_integral_card_le hf (fun _ ↦ abs_nonneg _) hX1 S hS
    (by positivity : 0 ≤ 1 / (2000 * Real.log X)) hpoint
  have hfinal := hcard.trans hi
  have hscaled := mul_le_mul_of_nonneg_right hfinal
    (show 0 ≤ 4000 * (X : ℝ) * Real.log X by positivity)
  have hl : ((S.card : ℝ) * (1 / (2000 * Real.log X)) / (2 * X : ℝ)) *
      (4000 * (X : ℝ) * Real.log X) = S.card := by field_simp; ring
  have hr : (σ / Real.log X) * (4000 * (X : ℝ) * Real.log X) = ε * X := by
    dsimp only [σ]
    field_simp
  rw [hl, hr] at hscaled
  exact hscaled

end Erdos421
