/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZFiniteSourceRowMeshLowTransition
import ErdosProblems.Erdos1165.HLOZTransportedCanonicalProp49Row

/-!
# The four normalized endpoint rows for Proposition 4.9

For a fixed tiling, the canonical/opposite endpoint class and the two
temporal orientations give four possibly overlapping source rows.  This
module constructs the finite-row low datum from the literal transported
candidate families.  The remaining hypotheses are deterministic stopped
observability and coverage of the filtered next event by these four rows.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZFourEndpointSourceRowProp49

open HLOZFiniteSourceRowMeshLowTransition
open HLOZMeshCandidateFutureFactor
open HLOZMeshCandidatePolynomialNumerics
open HLOZPathEvents HLOZPrefixedProp49CandidateWindowRatio
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSourceEndpointTransportTable
open HLOZTransportedCanonicalProp49Row
open LazyDecomposition
open ScreeningInstantiation

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The four normalized endpoint-source rows for one tiling. -/
inductive EndpointSourceRow
  | canonicalEven
  | canonicalShifted
  | oppositeEven
  | oppositeShifted
  deriving DecidableEq

instance : Fintype EndpointSourceRow where
  elems := { .canonicalEven, .canonicalShifted, .oppositeEven,
    .oppositeShifted }
  complete := by
    intro row
    cases row <;> simp

def EndpointSourceRow.orientation : EndpointSourceRow → Orientation
  | .canonicalEven | .oppositeEven => .even
  | .canonicalShifted | .oppositeShifted => .shifted

def EndpointSourceRow.endpointClass :
    EndpointSourceRow → DominantEndpointClass
  | .canonicalEven | .canonicalShifted => .canonical
  | .oppositeEven | .oppositeShifted => .opposite

/-- The literal candidate family belonging to one normalized endpoint row. -/
noncomputable def rowCandidateFamily
    (t : DominoTiling) (m k : ℕ) (a : GapScale) (low : ℕ)
    (previous : Set WalkPath) (hprevious : MeasurableSet previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (row : EndpointSourceRow) :=
  candidateFamily t row.orientation row.endpointClass m k a low previous
    hprevious hm hk hwindow harithmetic hexternalArithmetic

/-- The four copies of the literal row ratio sum to the same envelope with
constant multiplied by four. -/
theorem sum_rowCandidateRatio_le (m : ℕ) (a : GapScale) :
    ∑ _row : EndpointSourceRow,
        prop49CandidateRatioEnvelope prop49WindowRatioConstant m a ≤
      prop49CandidateRatioEnvelope (4 * prop49WindowRatioConstant) m a := by
  have hcard : Fintype.card EndpointSourceRow = 4 := by decide
  simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul,
    Nat.cast_ofNat]
  rw [prop49CandidateRatioEnvelope, prop49CandidateRatioEnvelope]
  rw [show 4 * prop49WindowRatioConstant *
      (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne) =
      4 * (prop49WindowRatioConstant *
        (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne)) by ring]
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

/-- Assemble the four literal normalized rows around one raw fixed-clock
mesh decomposition.  Rows may overlap; `next_subset` is the exact finite
source-cover seam. -/
noncomputable def finiteRowMeshLowCoordinateData
    {Index : Type} [Countable Index]
    {rawPast rawNext : Set WalkPath}
    (t : DominoTiling) (m k : ℕ) (a : GapScale) (low : ℕ)
    (previous : Set WalkPath) (hprevious : MeasurableSet previous)
    (hm : 1 < m) (hk : 0 < k)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m))
    (raw : CountableMeshCreationData Index rawPast rawNext m k a)
    (hpast : ∀ row i, IsMeasurableAtStopping
      (fun _ : StepPath ↦ raw.oldCreation i)
      (trajectory ⁻¹' (raw.pastPiece i ∩
        (rowCandidateFamily t m k a low previous hprevious hm hk hwindow
          harithmetic hexternalArithmetic row).someCandidate)))
    (next_subset : rawNext ⊆ ⋃ row : EndpointSourceRow,
      (rowCandidateFamily t m k a low previous hprevious hm hk hwindow
        harithmetic hexternalArithmetic row).someCandidate) :
    FiniteSourceRowMeshLowCoordinateData EndpointSourceRow
      (4 * prop49WindowRatioConstant) m k a previous rawNext where
  rowNext := fun row ↦ rawNext ∩
    (rowCandidateFamily t m k a low previous hprevious hm hk hwindow
      harithmetic hexternalArithmetic row).someCandidate
  rowNext_measurable := by
    intro row
    have hraw : MeasurableSet rawNext := by
      rw [← raw.next_union]
      exact MeasurableSet.iUnion raw.next_measurable
    exact hraw.inter (measurableSet_candidateFamily t row.orientation
      row.endpointClass m k a low previous hprevious hm hk hwindow
      harithmetic hexternalArithmetic)
  next_subset := by
    intro s hs
    rcases Set.mem_iUnion.mp (next_subset hs) with ⟨row, hrow⟩
    exact Set.mem_iUnion_of_mem row ⟨hs, hrow⟩
  rowConstant := fun _ ↦ prop49WindowRatioConstant
  row := fun row ↦ meshLowCoordinateDataOfRawCreation
    t row.orientation row.endpointClass m k a low previous hprevious hm hk
      hwindow harithmetic hexternalArithmetic raw (hpast row)
  ratio_sum_le := sum_rowCandidateRatio_le m a

end

end Erdos1165.HLOZFourEndpointSourceRowProp49
