/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingOrientedAllCreationStoppedCoordinate

/-!
# Direct conditional refinement of a literal prefixed creation fibre

The old version of this module strengthened an alleged unscreened shell-zero
base.  Such a base is not source-correct: at the raised creation clock,
stopping acceptance depends on the away-total vector.  The reusable literal
fibre is now the supported all-creation fibre, and every consumer supplies its
two honest direct screened factorizations through
`OrientedAllCreationConditionalRefinementData`.

The declarations below are deliberately only source-compatible names for
that direct API.  No unscreened source or replacement equivalence is exposed.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.TilingLiteralPrefixedConditionalRefinement

open CappedCoordinateMassCertificate
open LazyDecomposition
open TilingOrientedAllCreationStoppedCoordinate

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Source-compatible name for the honest direct broad/screened refinement
of one supported oriented all-creation fibre. -/
abbrev LiteralSourcePrefixedConditionalRefinementData
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (piece next : Set WalkPath) (cost : ℝ≥0∞) :=
  OrientedAllCreationConditionalRefinementData data piece next cost

/-- Build the scheduled conditional factor from the two direct screened
factorizations. -/
noncomputable def prefixedConditionalFactoredDataOfLiteralSourceRefinement
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    {piece next : Set WalkPath} {cost : ℝ≥0∞}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (refinement : LiteralSourcePrefixedConditionalRefinementData
      data piece next cost) :=
  prefixedConditionalFactoredDataOfAllCreation data refinement

/-- Exact coordinate-mass specification for the direct literal refinement. -/
noncomputable def coordinateMassSpecOfLiteralSourceRefinement
    {t : DominoTiling} {o : Orientation} {m k : ℕ}
    {supportAt : WalkPath → ℕ → Finset Point} {S : Finset Point}
    {z : OrientedAllCreationTraceCode t}
    {piece next : Set WalkPath} {cost : ℝ≥0∞}
    (data : OrientedAllCreationPrefixedStoppedCoordinateSpec
      t o m k supportAt S z)
    (refinement : LiteralSourcePrefixedConditionalRefinementData
      data piece next cost) :
    CoordinateMassSpec (fun _ : Unit ↦ piece) next cost :=
  coordinateMassSpecOfAllCreation data refinement

end

end Erdos1165.TilingLiteralPrefixedConditionalRefinement
