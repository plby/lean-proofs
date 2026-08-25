/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Util.MaynardTao.FiberLower
import Util.MaynardTao.Parameters
import Util.MaynardTao.IntegerTransfer
import ErdosProblems.Erdos6.MaynardParameters
import BoundedGaps.BombieriVinogradov.Analytic.PrimeLevelCutoff

/-!
# The unconditional Maynard--Tao theorem
-/

namespace MaynardTao

open Filter

noncomputable section

theorem natural_maynard_tao
    (m : ℕ) (hm : 2 ≤ m) (H : Finset ℕ)
    (hH : BoundedGaps.IsAdmissible H)
    (hthreshold : Real.exp (8 * (m : ℝ) + 4) <
      (H.card : ℝ) * Real.log H.card) :
    ∀ T : ℕ, ∃ n : ℕ, T < n ∧
      m ≤ BoundedGaps.primeShiftCount H n := by
  let K := H.card
  let A := sharpDecay K
  let δv := sharpDelta K
  let q0 := sharpGoodCutoff K
  let q1 := sharpFiberCutoff K
  let γ := sharpGoodMass K
  let F := tupleVariableCandidate H A
  let I := BoundedGaps.Maynard.maynardI K
    (Erdos4.VariableMaynard.candidate K A)
  let C0 := variableShortMass K A δv ^ 2 *
    (γ * Erdos4.VariableMaynard.baseMass K A ^ (K - 1))
  let c := (999 : ℝ) / 1000 * C0
  let theta : ℝ := (499 : ℝ) / 1000
  let delta : ℝ := (1 : ℝ) / 10000
  let beta : ℝ := (49 : ℝ) / 200
  let alpha : ℝ := theta / 2 - delta
  have hcard2 : 2 ≤ K := by
    dsimp [K]
    exact two_le_card_of_threshold hthreshold
  have hHne : H.Nonempty := Finset.card_pos.mp (by omega)
  have hK : 0 < K := by omega
  have hA : 0 < A := by
    dsimp [A, K]
    exact sharpDecay_pos hm hthreshold
  have hδv : 0 < δv := by
    dsimp [δv, K]
    exact sharpDelta_pos hm hthreshold
  have hq : q0 < q1 := by
    dsimp [q0, q1, K]
    exact sharpGoodCutoff_lt_fiberCutoff hm hthreshold
  have hq1 : q1 < 1 := by
    dsimp [q1, K]
    exact sharpFiberCutoff_lt_one hm hthreshold
  have hslack : q1 + δv < 1 := by
    dsimp [q1, δv, K]
    exact sharpFiberCutoff_add_delta_lt_one hm hthreshold
  have hγ : 0 < γ := by
    dsimp [γ, K]
    exact sharpGoodMass_pos hm hthreshold
  have hshort : 0 < variableShortMass K A δv :=
    variableShortMass_pos hK hA hδv
  have hbase : 0 < Erdos4.VariableMaynard.baseMass K A :=
    Erdos4.VariableMaynard.baseMass_pos hK hA
  have hC0 : 0 < C0 := by
    dsimp [C0]
    exact mul_pos (sq_pos_of_pos hshort)
      (mul_pos hγ (pow_pos hbase _))
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hcC0 : c < C0 := by
    dsimp [c]
    nlinarith
  have htheta : 0 < theta := by norm_num [theta]
  have hthetaHalf : theta < 1 / 2 := by norm_num [theta]
  have hlevel : BoundedGaps.Maynard.hasPrimeLevel theta :=
    BoundedGaps.Maynard.hasPrimeLevel_of_lt_half hthetaHalf
  have hdelta : 0 < delta := by norm_num [delta]
  have hdeltaTheta : delta < theta / 2 := by
    norm_num [delta, theta]
  have hbeta : 0 < beta := by norm_num [beta]
  have hbetaAlpha : beta < theta / 2 - delta := by
    norm_num [beta, theta, delta]
  have halpha : 0 < alpha := by
    dsimp [alpha]
    linarith
  have hF : ∀ t, |F t| ≤ (1 : ℝ) := by
    intro t
    dsimp [F, A]
    exact tupleVariableCandidate_abs_le_one hA t
  have hdiag : Tendsto (fun N : ℕ =>
      Erdos6.Maynard.normalizedTupleMaynardDiagonal H alpha F N)
      atTop (nhds I) := by
    dsimp [F, A, I, K]
    exact tendsto_normalizedTupleVariableDiagonal hHne hA halpha
  have hkernel : ∀ j : H, ∀ᶠ N : ℕ in atTop,
      c <
        Erdos6.Maynard.tupleRestrictedGKernel H alpha F N j /
          (BoundedGaps.Maynard.preSieveSingularSeries
              (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
            Real.log (Erdos6.Maynard.maynardRadius alpha N) ^ 2 *
            Erdos6.Maynard.tupleNaturalScale
              (Erdos6.Maynard.tupleOffFace H j) alpha N) := by
    intro j
    have hcardOff :
        Fintype.card (Erdos6.Maynard.tupleOffFace H j) = K - 1 := by
      calc
        Fintype.card (Erdos6.Maynard.tupleOffFace H j) =
            (Erdos6.Maynard.tupleOffFace H j).card := Fintype.card_coe _
        _ = H.card - 1 := by
          unfold Erdos6.Maynard.tupleOffFace
          rw [Finset.card_erase_of_mem j.2]
        _ = K - 1 := by rfl
    have hgood :
        γ * Erdos4.VariableMaynard.baseMass K A ^
            Fintype.card (Erdos6.Maynard.tupleOffFace H j) <
          ∫ t : Erdos6.Maynard.tupleOffFace H j → ℝ in
            variableGoodRegion q0 (Erdos6.Maynard.tupleOffFace H j),
            Erdos4.VariableMaynard.productDensity K A t := by
      dsimp [γ, A, q0, K]
      exact sharp_goodFaceMass hm hthreshold
        (Erdos6.Maynard.tupleOffFace H j) hcardOff
    have hfiber :=
      eventually_tupleVariableCoordinateFiberSquareDiagonal_normalized_gt
        hcard2 hA hq hq1 hδv hslack hγ j halpha hgood
    have hfiber' : ∀ᶠ N : ℕ in atTop,
        C0 <
          tupleCoordinateFiberSquareDiagonalFor H alpha F N j /
            (BoundedGaps.Maynard.preSieveSingularSeries
                (BoundedGaps.Maynard.tripleLogCutoff (N - 1)) ^ 2 *
              Real.log (Erdos6.Maynard.maynardRadius alpha N) ^ 2 *
              Erdos6.Maynard.tupleNaturalScale
                (Erdos6.Maynard.tupleOffFace H j) alpha N) := by
      simpa [C0, K, A, δv, γ, F, hcardOff,
        Erdos6.Maynard.maynardRadius] using hfiber
    have hcross := tendsto_normalizedTupleRestrictedCrossFor_zero
      halpha F (by norm_num) hF j
    exact eventually_tupleRestrictedGKernel_normalized_gt_of_fiber
      halpha F (by norm_num) hF j hcC0 hfiber' hcross
  have hIpos : 0 < I := by
    dsimp [I, K, A]
    exact Erdos4.VariableMaynard.maynardI_candidate_pos hK hA
  have hcoef :
      (41 : ℝ) / 10 * ((m - 1 : ℕ) : ℝ) <
        (K : ℝ) * C0 / I := by
    dsimp [C0, I, K, A, δv, γ]
    exact sharp_coefficient_over_I_gt hm hthreshold
  have hcoefMul :
      ((41 : ℝ) / 10 * ((m - 1 : ℕ) : ℝ)) * I <
        (K : ℝ) * C0 :=
    (lt_div_iff₀ hIpos).mp hcoef
  have hmargin :
      ((m - 1 : ℕ) : ℝ) * I < (H.card : ℝ) * beta * c := by
    have hfac : (1 : ℝ) <
        beta * ((999 : ℝ) / 1000) * ((41 : ℝ) / 10) := by
      norm_num [beta]
    have hscalePos : 0 < beta * ((999 : ℝ) / 1000) :=
      mul_pos hbeta (by norm_num)
    have hscaled := mul_lt_mul_of_pos_left hcoefMul
      hscalePos
    have hrho : 0 < ((m - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < m - 1 by omega)
    dsimp [c, K] at hscaled ⊢
    nlinarith [mul_pos hIpos hrho]
  have hpos := hasEventuallyPositiveSieveExcess_of_diagonal_and_kernel
    hHne htheta hthetaHalf hlevel hdelta hdeltaTheta hbeta hbetaAlpha
    hc (by positivity : 0 ≤ ((m - 1 : ℕ) : ℝ)) hmargin
    (Erdos6.Maynard.preSieveResidue H hH) (by
      intro N h hh
      exact Erdos6.Maynard.preSieveResidue_coprime H hH N hh)
    F (by norm_num) hF (by simpa [alpha] using hdiag)
    (by simpa [alpha] using hkernel)
  exact infinitelyOftenAtLeastPrimeShifts_of_eventuallyPositiveSieveExcess hpos

theorem maynard_tao
    (m : ℕ) (hm : 2 ≤ m) (B : Finset ℤ)
    (hB : Admissible B)
    (hk : Real.exp (8 * (m : ℝ) + 4) <
      (B.card : ℝ) * Real.log B.card) :
    ∀ N : ℕ, ∃ n : ℤ, N < n ∧
      m ≤ (B.filter (fun b ↦ (n + b).natAbs.Prime)).card := by
  have hBcard : 0 < B.card := by
    have hpos : 0 < (B.card : ℝ) * Real.log B.card :=
      (Real.exp_pos _).trans hk
    by_contra hnot
    have hzero : B.card = 0 := Nat.eq_zero_of_not_pos hnot
    simp [hzero] at hpos
  have hBne : B.Nonempty := Finset.card_pos.mp hBcard
  let a : ℤ := B.min' hBne
  have ha : ∀ b ∈ B, a ≤ b := by
    intro b hb
    exact Finset.min'_le B b hb
  let H := integerTupleToNat B a
  have hH : BoundedGaps.IsAdmissible H :=
    integerTupleToNat_admissible B a ha hB
  have hcard : H.card = B.card := integerTupleToNat_card B a ha
  have hthreshold : Real.exp (8 * (m : ℝ) + 4) <
      (H.card : ℝ) * Real.log H.card := by
    simpa [hcard] using hk
  have hnat := natural_maynard_tao m hm H hH hthreshold
  exact integerPrimeShifts_of_naturalPrimeShifts B a ha hnat

end

end MaynardTao
