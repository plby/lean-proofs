import Util.MaynardBFT.ProductCandidate

/-! # Indexing an arbitrary tuple of the selected cardinality -/

namespace MaynardBFT.Sieve

noncomputable section

variable [P : Parameters]

class ShiftTuple where
  shifts : Finset ℕ
  card_shifts : shifts.card = largeK

variable [T : ShiftTuple]

def largePowerTuple : Finset ℕ := T.shifts

theorem largePowerTuple_card : largePowerTuple.card = largeK := T.card_shifts

theorem largePowerTuple_nonempty : largePowerTuple.Nonempty := by
  apply Finset.card_pos.mp
  rw [largePowerTuple_card]
  exact largeK_pos

def largeTupleIndexEquiv : largePowerTuple ≃ Fin largeK :=
  Fintype.equivFinOfCardEq (by
    simpa only [Fintype.card_coe] using largePowerTuple_card)

def largeTupleCandidate (t : largePowerTuple → ℝ) : ℝ :=
  largeCandidate (fun i => t (largeTupleIndexEquiv.symm i))

theorem largeTupleCandidate_norm_le_one (t : largePowerTuple → ℝ) :
    ‖largeTupleCandidate t‖ ≤ 1 := largeCandidate_norm_le_one _

theorem largeTupleCandidate_abs_le_one (t : largePowerTuple → ℝ) :
    |largeTupleCandidate t| ≤ 1 := by
  simpa only [Real.norm_eq_abs] using largeTupleCandidate_norm_le_one t

end

end MaynardBFT.Sieve
