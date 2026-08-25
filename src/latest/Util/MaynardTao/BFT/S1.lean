import Util.MaynardTao.BFT.Diagonal
import ErdosProblems.Erdos6.GenericS1

/-! # The first sieve moment for the parameterized product candidate -/

namespace MaynardBFT.Sieve

open Filter Erdos6.Maynard

noncomputable section

variable [P : Parameters] [T : ShiftTuple]

def largeMaynardWeight (alpha : ℝ) (v : ℕ → ℕ) (N : ℕ) : ℕ → ℝ :=
  tupleMaynardWeight largePowerTuple alpha v largeTupleCandidate N

theorem tendsto_normalizedLargeTupleS1Main
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      tupleMaynardS1Main largePowerTuple alpha largeTupleCandidate N /
        tupleMaynardScale largePowerTuple alpha N) atTop
      (nhds (BoundedGaps.Maynard.maynardI largeK largeCandidate)) := by
  have hdiag := tendsto_normalizedLargeTupleYDiagonal halpha
  have hcross := tendsto_normalized_tupleMaynardS1Cross_zero
    largePowerTuple halpha largeTupleCandidate (B := 1) (by norm_num)
      largeTupleCandidate_abs_le_one
  have hsub := hdiag.sub hcross
  simpa using hsub.congr' (by
    filter_upwards [] with N
    rw [tupleMaynardS1Main_eq_diagonal_sub_cross]
    unfold largeTupleYDiagonal maynardModulus maynardRadius
    ring)

theorem tendsto_normalizedLargeTupleS1 (v : ℕ → ℕ)
    {alpha : ℝ} (halpha : 0 < alpha) (halphaQuarter : alpha < 1 / 4) :
    Tendsto (fun N : ℕ =>
      BoundedGaps.Maynard.sieveWeightSum N (largeMaynardWeight alpha v N) /
        tupleMaynardScale largePowerTuple alpha N) atTop
      (nhds (BoundedGaps.Maynard.maynardI largeK largeCandidate)) := by
  have hmain := tendsto_normalizedLargeTupleS1Main halpha
  have herror := tendsto_normalized_tupleMaynardS1Error_zero
    largePowerTuple halpha halphaQuarter v
      largeTupleCandidate (B := 1) (by norm_num) largeTupleCandidate_abs_le_one
  have hsum := hmain.add herror
  simpa using hsum.congr' (by
    filter_upwards [eventually_tupleMaynardS1_eq_main_add_error
      largePowerTuple alpha v largeTupleCandidate] with N hN
    unfold largeMaynardWeight
    rw [hN]
    ring)

end

end MaynardBFT.Sieve
