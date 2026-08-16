import ErdosProblems.Erdos6.LargeParameters
import ErdosProblems.Erdos6.GenericS2ErrorLimit

/-!
# Eventual positivity of the prescribed BFT Maynard weight
-/

namespace Erdos6.Maynard

open Filter Set

noncomputable section

theorem hasIsolatedFourPowerPrimeShifts : HasIsolatedFourPowerPrimeShifts := by
  obtain ⟨theta, delta, beta, htheta, hthetaHalf, hlevel,
      hdelta, hdeltaTheta, hbeta, hbetaAlpha, hthreshold⟩ :=
    exists_largeSieveParameters
  let alpha := theta / 2 - delta
  let I := BoundedGaps.Maynard.maynardI largeK largeCandidate
  let S := (largeK : ℝ) * beta * largeKernelMargin
  let eps := (S - 3 * I) / 8
  have halpha : 0 < alpha := by dsimp [alpha]; linarith
  have halphaQuarter : alpha < 1 / 4 := by
    dsimp [alpha]
    linarith
  have hSI : 3 * I < S := by
    simpa only [S, I] using hthreshold
  have heps : 0 < eps := by dsimp [eps]; linarith
  have hmain := eventually_largeTupleS2Main_normalized_gt
    halpha hbeta hbetaAlpha largeKernelMargin_pos
      largeKernelMargin_lt_coefficient
  have hs1 := tendsto_normalizedLargeTupleS1 halpha halphaQuarter
  have hs1Upper : ∀ᶠ N : ℕ in atTop,
      BoundedGaps.Maynard.sieveWeightSum N (largeMaynardWeight alpha N) /
          tupleMaynardScale largePowerTuple alpha N < I + eps := by
    have hmem : Set.Iio (I + eps) ∈ nhds I :=
      Iio_mem_nhds (lt_add_of_pos_right I heps)
    simpa only [I] using hs1.eventually hmem
  have hH : largePowerTuple.Nonempty := by
    refine ⟨2, mem_largePowerTuple.mpr ⟨0, largeK_pos, ?_⟩⟩
    norm_num
  have herr := tendsto_normalized_tupleMaynardS2Error_zero_of_primeLevel
    largePowerTuple hH bftPreSieveResidue largeTupleCandidate 1
      (by norm_num) largeTupleCandidate_abs_le_one
      (fun N h hh => bftPreSieveResidue_coprime N hh)
      htheta hthetaHalf hdelta hdeltaTheta hlevel
  have herrLower : ∀ᶠ N : ℕ in atTop,
      -eps <
        tupleMaynardS2Error largePowerTuple alpha bftPreSieveResidue
            largeTupleCandidate N /
          tupleMaynardScale largePowerTuple alpha N := by
    have hmem : Set.Ioi (-eps) ∈ nhds (0 : ℝ) :=
      Ioi_mem_nhds (neg_lt_zero.mpr heps)
    simpa only [alpha] using herr.eventually hmem
  have hS2eq := eventually_tupleMaynardS2_eq_main_add_error
    largePowerTuple hthetaHalf hdelta hdeltaTheta
      bftPreSieveResidue largeTupleCandidate
  have hscale := eventually_tupleMaynardScale_pos
    (H := largePowerTuple) halpha
  have hpos : ∀ᶠ N : ℕ in atTop,
      0 < BoundedGaps.Maynard.sieveExcess largePowerTuple N 3
        (largeMaynardWeight alpha N) := by
    filter_upwards [hmain, hs1Upper, herrLower, hS2eq, hscale] with
        N hmainN hs1N herrN hS2eqN hscaleN
    have hS2norm : S - eps <
        BoundedGaps.Maynard.primeWeightedSieveSum largePowerTuple N
            (largeMaynardWeight alpha N) /
          tupleMaynardScale largePowerTuple alpha N := by
      have heq :
          BoundedGaps.Maynard.primeWeightedSieveSum largePowerTuple N
              (largeMaynardWeight alpha N) =
            tupleMaynardS2Main largePowerTuple alpha bftPreSieveResidue
                largeTupleCandidate N +
              tupleMaynardS2Error largePowerTuple alpha bftPreSieveResidue
                largeTupleCandidate N := by
        simpa only [largeMaynardWeight, alpha] using hS2eqN
      rw [heq, add_div]
      change S <
        tupleMaynardS2Main largePowerTuple alpha bftPreSieveResidue
            largeTupleCandidate N /
          tupleMaynardScale largePowerTuple alpha N at hmainN
      linarith
    have hnorm : 0 <
        BoundedGaps.Maynard.sieveExcess largePowerTuple N 3
            (largeMaynardWeight alpha N) /
          tupleMaynardScale largePowerTuple alpha N := by
      unfold BoundedGaps.Maynard.sieveExcess
      rw [show
        (BoundedGaps.Maynard.primeWeightedSieveSum largePowerTuple N
              (largeMaynardWeight alpha N) -
            3 * BoundedGaps.Maynard.sieveWeightSum N
              (largeMaynardWeight alpha N)) /
              tupleMaynardScale largePowerTuple alpha N =
          BoundedGaps.Maynard.primeWeightedSieveSum largePowerTuple N
              (largeMaynardWeight alpha N) /
                tupleMaynardScale largePowerTuple alpha N -
            3 * (BoundedGaps.Maynard.sieveWeightSum N
              (largeMaynardWeight alpha N) /
                tupleMaynardScale largePowerTuple alpha N) by ring]
      have hepsEq : 8 * eps = S - 3 * I := by
        dsimp only [eps]
        ring
      linarith
    have heq :
        BoundedGaps.Maynard.sieveExcess largePowerTuple N 3
            (largeMaynardWeight alpha N) =
          (BoundedGaps.Maynard.sieveExcess largePowerTuple N 3
              (largeMaynardWeight alpha N) /
            tupleMaynardScale largePowerTuple alpha N) *
              tupleMaynardScale largePowerTuple alpha N := by
      field_simp [hscaleN.ne']
    rw [heq]
    exact mul_pos hnorm hscaleN
  apply hasIsolatedFourPowerPrimeShifts_of_eventually_positive_bft_excess
    (D := fun N => tupleMaynardSupport largePowerTuple alpha N)
    (lambda := fun N => tupleMaynardCoefficient largePowerTuple alpha
      largeTupleCandidate N)
  simpa only [largeMaynardWeight, tupleMaynardWeight] using hpos

end

end Erdos6.Maynard
