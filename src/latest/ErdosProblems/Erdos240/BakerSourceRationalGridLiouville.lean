/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos240.BakerSourceRationalExactLiouville
import ErdosProblems.Erdos240.BakerSourceRationalGridGrowth

/-!
# Exact Liouville lower bound on the source rational grid

This module composes the source-faithful, level-scaled growth estimate at
`l / q` with the exact radical-degree Liouville product bound.  Its public
endpoint has only the coefficient-box and parameter-ledger hypotheses that
are already part of the source construction.
-/

noncomputable section

namespace Erdos240.BakerSourceRationalLiouvilleLowerBounds

open BakerLemma2Concrete
open BakerLemma3Instantiation
open BakerSourceAlgebraicLevelMajorant
open BakerSourcePositiveStageGrowth
open BakerSourceRationalGridGrowth
open BakerSourceState

/-- The exact source-scale rational Liouville lower bound, with the rational
grid growth estimate discharged from the source coefficient box. -/
theorem exp_neg_exactDegreeScale_le_stateRationalLiouvilleThreshold_of_sourceBounds
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (hreq : initialUnknownRequirement P ∈ P.kRequirements)
    {J : ℕ} (hJ : P.LevelOK J) (state : LevelState P J)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLast : bLast.natAbs ≤ P.Bsrc)
    (l : ℕ) (hl : l ≤ P.R (J + 1))
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ P.Sstep J) :
    Real.exp (-((5 + 34 * (13 ^ (oldRank + 1) : ℝ)) *
        rationalHeightScale P)) ≤
      stateRationalLiouvilleThreshold P J state b bLast l m := by
  apply exp_neg_exactDegreeScale_le_stateRationalLiouvilleThreshold
    P hJ state b bLast l hl m hm
  have hgrowth := levelAlgebraicGrowth_ratCast_le_exp_two
    P hreq state b bLast hb hbLast hl m hm
  simpa only [sourceHeightUnit, rationalHeightScale] using hgrowth

end Erdos240.BakerSourceRationalLiouvilleLowerBounds

#print axioms
  Erdos240.BakerSourceRationalLiouvilleLowerBounds.exp_neg_exactDegreeScale_le_stateRationalLiouvilleThreshold_of_sourceBounds
