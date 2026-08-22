/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceDistinguishedEventProp49Family

/-!
# Proposition 4.9 families on the structural rank pasts

The rank-two and rank-three structural pasts omit candidate-overflow
payments.  On canonical source atoms they depend only on the distinguished
coordinates, so the conditional source ratio can be restricted to them
without requiring a whole ambient source atom to lie in the past.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZSourceStructuralPastProp49Family

open HLOZPathEvents
open HLOZMeshCandidatePolynomialNumerics
open HLOZPrefixedCanonicalSourceAtomRecovery
open HLOZPrefixedCanonicalSourceLowRecovery
open HLOZPrefixedProp49CandidateWindowRatio
open HLOZProposition48Candidates
open HLOZShellZeroExternalWindow HLOZShellZeroReplacementWindows
open HLOZSourceDistinguishedEventProp49Family
open HLOZSourceStructuralPastInvariant
open HLOZStoppedHistoryCandidateFuture
open LazyDecomposition
open TilingCappedMarginalization
open TilingOrientedAllCreationStoppedCoordinate
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedStoppedProductDisintegration

noncomputable section

abbrev DominoTiling := Tilings.Tiling
abbrev GapTriple := HLOZFilteredTransitionAssembly.GapTriple

theorem firstStructuralPast_distinguishedInvariant
    {t : DominoTiling} {o : Orientation} {m : ℕ}
    (eta : SourceSupportedIndex t o m 2) (hm : 1 < m) (gaps : GapTriple) :
    SourceEventDistinguishedInvariant eta
      (firstStructuralPast t m gaps) := by
  intro cap q q' hdist hpred haccepted hpred' haccepted'
  have hcanonical := canonical_mem_supportAtom_of_predicate_accepted
    ((SourceFiber eta).coordinateCap cap) q hpred haccepted
  have hcanonical' := canonical_mem_supportAtom_of_predicate_accepted
    ((SourceFiber eta).coordinateCap cap) q' hpred' haccepted'
  exact sourceCanonical_firstStructuralPast_iff eta hm gaps q q' hdist
    hcanonical haccepted hcanonical' haccepted'

theorem secondStructuralPast_distinguishedInvariant
    {t : DominoTiling} {o : Orientation} {m : ℕ}
    (eta : SourceSupportedIndex t o m 3) (hm : 1 < m) (gaps : GapTriple) :
    SourceEventDistinguishedInvariant eta
      (secondStructuralPast t m gaps) := by
  intro cap q q' hdist hpred haccepted hpred' haccepted'
  have hcanonical := canonical_mem_supportAtom_of_predicate_accepted
    ((SourceFiber eta).coordinateCap cap) q hpred haccepted
  have hcanonical' := canonical_mem_supportAtom_of_predicate_accepted
    ((SourceFiber eta).coordinateCap cap) q' hpred' haccepted'
  exact sourceCanonical_secondStructuralPast_iff eta hm gaps q q' hdist
    hcanonical haccepted hcanonical' haccepted'

theorem firstStructuralPast_prefixInvariant
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) :
    SourceEventPrefixInvariant m 2 (firstStructuralPast t m gaps) := by
  intro s s' N hp hfinal hfinal'
  exact firstStructuralPast_iff_of_pathPrefix_eq_of_creation t gaps hp hfinal
    hfinal'

theorem secondStructuralPast_prefixInvariant
    (t : DominoTiling) (m : ℕ) (gaps : GapTriple) :
    SourceEventPrefixInvariant m 3 (secondStructuralPast t m gaps) := by
  intro s s' N hp hfinal hfinal'
  exact secondStructuralPast_iff_of_pathPrefix_eq_of_creation t gaps hp hfinal
    hfinal'

/-- The canonical rank-two Proposition 4.9 family conditioned on the
structural first past. -/
noncomputable def firstStructuralPastTargetFamily
    (t : DominoTiling) (o : Orientation) (m : ℕ)
    (gaps : GapTriple) (a : GapScale) (low : ℕ)
    (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    StoppedHistoryCandidateFamily
      (HLOZOrientedAllCreationStoppedCandidateFamily.History t o m 2
        (SourceSupportAt t o m)) Point (firstStructuralPast t m gaps)
      (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) :=
  sourceEventTargetFamily a low (firstStructuralPast t m gaps)
    (measurableSet_firstStructuralPast t m gaps)
    (fun eta ↦ firstStructuralPast_distinguishedInvariant eta hm gaps)
    (firstStructuralPast_prefixInvariant t m gaps) hm (by omega) hwindow
      harithmetic hexternalArithmetic

/-- The canonical rank-three Proposition 4.9 family conditioned on the
structural second past. -/
noncomputable def secondStructuralPastTargetFamily
    (t : DominoTiling) (o : Orientation) (m : ℕ)
    (gaps : GapTriple) (a : GapScale) (low : ℕ)
    (hm : 1 < m)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hexternalArithmetic : ShellZeroExternalWindowArithmeticAt m
      (shellZeroExternalLow48 m) (shellZeroExternalHigh48 m)) :
    StoppedHistoryCandidateFamily
      (HLOZOrientedAllCreationStoppedCandidateFamily.History t o m 3
        (SourceSupportAt t o m)) Point (secondStructuralPast t m gaps)
      (initialBudget48 m)
      (prop49CandidateRatioEnvelope prop49WindowRatioConstant m a) :=
  sourceEventTargetFamily a low (secondStructuralPast t m gaps)
    (measurableSet_secondStructuralPast t m gaps)
    (fun eta ↦ secondStructuralPast_distinguishedInvariant eta hm gaps)
    (secondStructuralPast_prefixInvariant t m gaps) hm (by omega) hwindow
      harithmetic hexternalArithmetic

end

end Erdos1165.HLOZSourceStructuralPastProp49Family
