import ErdosProblems.Erdos67.MRGSA9A13ShiftedThreeBlock
import ErdosProblems.Erdos67.MRGSA9ZetaMajorant

/-!
# Source-shaped A.14 recombination after small-prime deletion
-/

open scoped BigOperators LSeries.notation

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Abstract A.14 handoff for the shifted finite A.13 estimate.  Once the
low alternating factor is bounded by the geometric mean of the actual and
positive large-prime products, multiplication by the common high factor
recombines them into the deleted full L-series and zeta. -/
theorem norm_alt_mul_high_sq_le_deleted_full_mul_zeta
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y : ℕ} (hy : 23 ≤ y) {sigma t C : ℝ} (hsigma : 1 < sigma)
    (hC : 0 ≤ C) (Alt : ℂ)
    (hAlt :
      ‖Alt‖ ^ 2 ≤ C *
        ‖∏ p ∈ gsA9LargePrimesUpTo y,
          gsA9LocalEulerFactor (gsDeletePrimeBand f gsA9SmallPrime)
            ((sigma : ℂ) + Complex.I * (t : ℂ)) p‖ *
        ‖∏ p ∈ gsA9LargePrimesUpTo y,
          gsA9LocalEulerFactor (fun _ : ℕ ↦ (1 : ℂ)) (sigma : ℂ) p‖) :
    ‖Alt * LSeries
        (gsA9High (gsDeletePrimeBand f gsA9SmallPrime) y)
        ((sigma : ℂ) + Complex.I * (t : ℂ))‖ ^ 2 ≤
      C *
        ‖LSeries (gsDeletePrimeBand f gsA9SmallPrime)
          ((sigma : ℂ) + Complex.I * (t : ℂ))‖ *
        ‖riemannZeta (sigma : ℂ)‖ := by
  let g : ℕ → ℂ := gsDeletePrimeBand f gsA9SmallPrime
  let one : ℕ → ℂ := fun _ ↦ 1
  let oneDel : ℕ → ℂ := gsDeletePrimeBand one gsA9SmallPrime
  let s : ℂ := (sigma : ℂ) + Complex.I * (t : ℂ)
  let sr : ℂ := (sigma : ℂ)
  let P : ℂ := ∏ p ∈ gsA9LargePrimesUpTo y,
    gsA9LocalEulerFactor g s p
  let Pp : ℂ := ∏ p ∈ gsA9LargePrimesUpTo y,
    gsA9LocalEulerFactor one sr p
  let H : ℂ := LSeries (gsA9High g y) s
  let Hp : ℂ := LSeries (gsA9High one y) sr
  have hmulDel : IsMultiplicativeOnPositiveNat g :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  have hboundDel : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  have honeMul : IsMultiplicativeOnPositiveNat one := by
    refine ⟨by simp [one], ?_⟩
    intro m n _ _ _
    simp [one]
  have honeBound : ∀ n, 0 < n → ‖one n‖ ≤ 1 := by simp [one]
  have honeDelBound : ∀ n, 0 < n → ‖oneDel n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one honeBound gsA9SmallPrime hn
  have hs : 1 < s.re := by simpa [s] using hsigma
  have hsr : 1 < sr.re := by simpa [sr] using hsigma
  have hfull := prod_large_deleteSmallPrimes_mul_high_eq_LSeries
    hmul hbound y hs
  have hfull' : P * H = LSeries g s := by
    simpa only [g, P, H] using hfull
  have hpos := prod_large_deleteSmallPrimes_mul_high_eq_LSeries
    honeMul honeBound y hsr
  have hhighOne : gsA9High oneDel y = gsA9High one y := by
    exact gsA9High_deleteSmallPrimes_eq one hy
  have hprimeLarge : ∀ p ∈ gsA9LargePrimesUpTo y, p.Prime := by
    intro p hp
    exact (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
  have hlarge : ∀ p ∈ gsA9LargePrimesUpTo y, 23 ≤ p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hprodOne := prod_gsA9LocalEulerFactor_deleteSmallPrimes_eq
    one sr (gsA9LargePrimesUpTo y) hprimeLarge hlarge
  have hpos' : Pp * Hp = LSeries oneDel sr := by
    simpa only [one, oneDel, Pp, Hp, hhighOne, hprodOne] using hpos
  have hHmajor : ‖H‖ ≤ ‖Hp‖ := by
    have h := norm_LSeries_primeBandCoefficient_le_positive
      hboundDel (fun p ↦ ¬ p ≤ y) hsigma (t := t)
    simpa only [g, one, s, sr, H, Hp, gsA9High] using h
  have hzeta : ‖LSeries oneDel sr‖ ≤ ‖riemannZeta (sigma : ℂ)‖ := by
    simpa only [oneDel, sr, Complex.ofReal_zero, mul_zero, add_zero] using
      Erdos67.norm_LSeries_le_norm_riemannZeta_real_of_bounded
        honeDelBound hsigma (t := 0)
  have hAlt' : ‖Alt‖ ^ 2 ≤ C * ‖P‖ * ‖Pp‖ := by
    simpa only [g, one, s, sr, P, Pp] using hAlt
  calc
    ‖Alt * H‖ ^ 2 = ‖Alt‖ ^ 2 * ‖H‖ ^ 2 := by
      rw [norm_mul]
      ring
    _ ≤ (C * ‖P‖ * ‖Pp‖) * (‖H‖ * ‖Hp‖) := by
      gcongr
      nlinarith [norm_nonneg H]
    _ = C * (‖P‖ * ‖H‖) * (‖Pp‖ * ‖Hp‖) := by ring
    _ = C * ‖LSeries g s‖ * ‖LSeries oneDel sr‖ := by
      rw [← norm_mul, ← norm_mul, hfull', hpos']
    _ ≤ C * ‖LSeries g s‖ * ‖riemannZeta (sigma : ℂ)‖ := by
      gcongr

end

end Erdos67.MRHalaszBands
