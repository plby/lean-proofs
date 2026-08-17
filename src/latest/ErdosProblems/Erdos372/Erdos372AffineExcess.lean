import ErdosProblems.Erdos372.Erdos372AffineErrorLimit

/-!
# Positive affine Maynard excess and extraction of two prime forms
-/

namespace Erdos372.AffineMaynard

open Filter Set
open scoped BigOperators
open Erdos6.Maynard
open BoundedGaps.Maynard

noncomputable section

def affineSieveExcess (H : Finset ℕ) (A : H → ℕ) (N : ℕ)
    (rho : ℝ) (w : ℕ → ℝ) : ℝ :=
  affinePrimeWeightedSieveSum H A N w - rho * sieveWeightSum N w

theorem affineSieveExcess_eq_sum (H : Finset ℕ) (A : H → ℕ)
    (N : ℕ) (rho : ℝ) (w : ℕ → ℝ) :
    affineSieveExcess H A N rho w =
      ∑ n ∈ Finset.Ico N (2 * N),
        ((affinePrimeCount A n : ℝ) - rho) * w n := by
  simp only [affineSieveExcess, affinePrimeWeightedSieveSum, sieveWeightSum,
    sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]

theorem exists_affinePrimeCount_gt_of_affineSieveExcess_pos
    {H : Finset ℕ} {A : H → ℕ} {N : ℕ} {rho : ℝ} {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Ico N (2 * N), 0 ≤ w n)
    (hpos : 0 < affineSieveExcess H A N rho w) :
    ∃ n ∈ Finset.Ico N (2 * N), rho < (affinePrimeCount A n : ℝ) := by
  by_contra hnone
  have hterm : ∀ n ∈ Finset.Ico N (2 * N),
      ((affinePrimeCount A n : ℝ) - rho) * w n ≤ 0 := by
    intro n hn
    have hcount : (affinePrimeCount A n : ℝ) ≤ rho := by
      exact le_of_not_gt (fun hgt => hnone ⟨n, hn, hgt⟩)
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcount) (hw n hn)
  have hsum := Finset.sum_nonpos hterm
  rw [← affineSieveExcess_eq_sum] at hsum
  exact (not_lt_of_ge hsum) hpos

theorem exists_eventually_largeAffineSieveExcess_pos
    (A : largePowerTuple → ℕ) (hApos : ∀ h, 0 < A h)
    (hAinj : Function.Injective A) :
    ∃ alpha : ℝ, ∀ᶠ N : ℕ in atTop,
      0 < affineSieveExcess largePowerTuple A N 1
        (affineTupleMaynardWeight largePowerTuple A alpha
          largeTupleCandidate N) := by
  obtain ⟨theta, delta, beta, htheta, hthetaHalf, hlevel,
      hdelta, hdeltaTheta, hbeta, hbetaAlpha, hthreshold⟩ :=
    exists_largeSieveParameters
  let alpha := theta / 2 - delta
  let I := maynardI largeK largeCandidate
  let S := (largeK : ℝ) * beta * largeKernelMargin
  let eps := (S - I) / 4
  have halpha : 0 < alpha := by dsimp [alpha]; linarith
  have halphaQuarter : alpha < 1 / 4 := by
    dsimp [alpha]
    linarith
  have hI : 0 < I := by
    dsimp only [I]
    exact maynardI_largeCandidate_pos
  have hSI : I < S := by
    dsimp only [S, I] at hthreshold ⊢
    linarith
  have heps : 0 < eps := by dsimp [eps]; linarith
  have hmain := eventually_largeAffineS2Main_normalized_gt
    A hApos hAinj halpha hbeta hbetaAlpha largeKernelMargin_pos
      largeKernelMargin_lt_coefficient
  have hs1 := tendsto_normalized_largeAffineS1 A hApos hAinj
    halpha halphaQuarter
  have hs1Upper : ∀ᶠ N : ℕ in atTop,
      sieveWeightSum N
          (affineTupleMaynardWeight largePowerTuple A alpha
            largeTupleCandidate N) /
          tupleMaynardScale largePowerTuple alpha N < I + eps := by
    have hmem : Set.Iio (I + eps) ∈ nhds I :=
      Iio_mem_nhds (lt_add_of_pos_right I heps)
    simpa only [I] using hs1.eventually hmem
  have hH : largePowerTuple.Nonempty := by
    refine ⟨2, mem_largePowerTuple.mpr ⟨0, largeK_pos, ?_⟩⟩
    norm_num
  have herr := tendsto_normalized_affineTupleMaynardS2Error_zero_of_primeLevel
    largePowerTuple hH A hApos hAinj largeTupleCandidate 1
      (by norm_num) largeTupleCandidate_abs_le_one
      htheta hthetaHalf hdelta hdeltaTheta hlevel
  have herrLower : ∀ᶠ N : ℕ in atTop,
      -eps < affineTupleMaynardS2Error largePowerTuple A alpha
          largeTupleCandidate N /
        tupleMaynardScale largePowerTuple alpha N := by
    have hmem : Set.Ioi (-eps) ∈ nhds (0 : ℝ) :=
      Ioi_mem_nhds (neg_lt_zero.mpr heps)
    simpa only [alpha] using herr.eventually hmem
  have hS2eq := eventually_affineTupleMaynardS2_eq_main_add_error
    A hApos hAinj hthetaHalf hdelta hdeltaTheta largeTupleCandidate
  have hscale := eventually_tupleMaynardScale_pos
    (H := largePowerTuple) halpha
  have hpos : ∀ᶠ N : ℕ in atTop,
      0 < affineSieveExcess largePowerTuple A N 1
        (affineTupleMaynardWeight largePowerTuple A alpha
          largeTupleCandidate N) := by
    filter_upwards [hmain, hs1Upper, herrLower, hS2eq, hscale] with
        N hmainN hs1N herrN hS2eqN hscaleN
    have hS2norm : S - eps <
        affinePrimeWeightedSieveSum largePowerTuple A N
            (affineTupleMaynardWeight largePowerTuple A alpha
              largeTupleCandidate N) /
          tupleMaynardScale largePowerTuple alpha N := by
      rw [hS2eqN, add_div]
      change S < affineTupleMaynardS2Main largePowerTuple A alpha
          largeTupleCandidate N /
        tupleMaynardScale largePowerTuple alpha N at hmainN
      linarith
    have hnorm : 0 <
        affineSieveExcess largePowerTuple A N 1
            (affineTupleMaynardWeight largePowerTuple A alpha
              largeTupleCandidate N) /
          tupleMaynardScale largePowerTuple alpha N := by
      unfold affineSieveExcess
      rw [show
        (affinePrimeWeightedSieveSum largePowerTuple A N
              (affineTupleMaynardWeight largePowerTuple A alpha
                largeTupleCandidate N) -
            1 * sieveWeightSum N
              (affineTupleMaynardWeight largePowerTuple A alpha
                largeTupleCandidate N)) /
              tupleMaynardScale largePowerTuple alpha N =
          affinePrimeWeightedSieveSum largePowerTuple A N
              (affineTupleMaynardWeight largePowerTuple A alpha
                largeTupleCandidate N) /
                tupleMaynardScale largePowerTuple alpha N -
            (sieveWeightSum N
              (affineTupleMaynardWeight largePowerTuple A alpha
                largeTupleCandidate N) /
                tupleMaynardScale largePowerTuple alpha N) by ring]
      have hepsEq : 4 * eps = S - I := by
        dsimp only [eps]
        ring
      linarith
    have heq :
        affineSieveExcess largePowerTuple A N 1
            (affineTupleMaynardWeight largePowerTuple A alpha
              largeTupleCandidate N) =
          (affineSieveExcess largePowerTuple A N 1
              (affineTupleMaynardWeight largePowerTuple A alpha
                largeTupleCandidate N) /
            tupleMaynardScale largePowerTuple alpha N) *
              tupleMaynardScale largePowerTuple alpha N := by
      field_simp [hscaleN.ne']
    rw [heq]
    exact mul_pos hnorm hscaleN
  exact ⟨alpha, hpos⟩

theorem infinitelyOften_two_prime_affine_forms_largePowerTuple
    (A : largePowerTuple → ℕ) (hApos : ∀ h, 0 < A h)
    (hAinj : Function.Injective A) :
    ∀ R : ℕ, ∃ n : ℕ, R < n ∧
      ∃ i j : largePowerTuple, i ≠ j ∧
        (A i * n + 1).Prime ∧ (A j * n + 1).Prime := by
  intro R
  obtain ⟨alpha, hpos⟩ :=
    exists_eventually_largeAffineSieveExcess_pos A hApos hAinj
  rw [eventually_atTop] at hpos
  obtain ⟨N₀, hN₀⟩ := hpos
  let N := max N₀ (R + 1)
  let w := affineTupleMaynardWeight largePowerTuple A alpha
    largeTupleCandidate N
  have hw : ∀ n ∈ Finset.Ico N (2 * N), 0 ≤ w n := by
    intro n hn
    exact preSievedAffineSquareDivisorWeight_nonneg _ _ _ _ _
  have hexcess : 0 < affineSieveExcess largePowerTuple A N 1 w := by
    exact hN₀ N (le_max_left _ _)
  obtain ⟨n, hn, hcount⟩ :=
    exists_affinePrimeCount_gt_of_affineSieveExcess_pos hw hexcess
  have hcountNat : 1 < affinePrimeCount A n := by exact_mod_cast hcount
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcountNat
  have hiPrime : (A i * n + 1).Prime := (Finset.mem_filter.mp hi).2
  have hjPrime : (A j * n + 1).Prime := (Finset.mem_filter.mp hj).2
  refine ⟨n, ?_, i, j, hij, hiPrime, hjPrime⟩
  have hNn := (Finset.mem_Ico.mp hn).1
  have hRN : R + 1 ≤ N := le_max_right _ _
  omega

end

end Erdos372.AffineMaynard
