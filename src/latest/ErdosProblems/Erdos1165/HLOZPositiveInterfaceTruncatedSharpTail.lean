/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfaceLocalWindowData

/-!
# Truncated sharp tails on exact positive-interface atoms

This file packages every analytic and cap-coherence field of the honest
positive-interface sharp tail.  The one remaining input is deliberately
pathwise: the event being estimated must be covered by the concrete stopped
coordinate screen.  Keeping that containment explicit prevents an
unbalanced adjacent-shell event from being silently identified with the
canonical negative-binomial windows.
-/

open Set

namespace Erdos1165.HLOZPositiveInterfaceTruncatedSharpTail

open HLOZAllCreationCofinalTruncatedSharpWindow
open HLOZPositiveInterfaceAggregateRecovery
open HLOZPositiveInterfaceLocalWindowData
open HLOZPositiveInterfaceSupportSelector
open HLOZPrefixedAllCreationStaticSupportTruncatedSharpTail
open HLOZPrefixedAllCreationStaticSupportTruncatedSharpTail.StaticSupportRecoveryCertificate
open HLOZPrefixedAllCreationStaticSupportAggregateRefinement
open HLOZPrefixedAllCreationStaticSupportAggregateRefinement.StaticSupportRecoveryCertificate
open LazyDecomposition
open TilingOrientedAllCreationConcreteFamily
open TilingOrientedAllCreationStoppedCoordinate
open VariableStoppedTracePartition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- All local analytic data for one exact positive-interface atom.  No
probability estimate is an argument: `transition_covered` is the literal
deterministic reconstruction of the event inside the stopped screen. -/
noncomputable def positiveInterfaceTruncatedSharpTailData
    {t : DominoTiling} {o : Orientation} {m k externalThreshold : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (hm : 1 < m) (hk : 0 < k)
    (harithmetic : HLOZSharpWindowProductClosure.SharpWindowArithmeticAt m)
    (hactive : m / 2 ≤ externalThreshold)
    (piece next : Set WalkPath) (threshold : ℕ → ℕ)
    (shell bound : ℕ)
    (atom_subset_piece : orientedAllCreationSupportTraceAtom
      t o m k (PositiveInterfaceSupportAt t o m externalThreshold)
        eta.1.1 eta.1.2 ⊆ piece)
    (transition_covered : piece ∩ next ⊆ ⋃ cap,
      positiveInterfaceScreenedFiber eta hm hk threshold shell bound cap) :
    OrientedAllCreationConditionalTruncatedSharpTailData
      (PositiveInterfaceFiber eta) piece next threshold shell bound := by
  let cert := positiveInterfaceStaticSupportRecoveryCertificate eta hm hk
  exact truncatedSharpTailData cert piece next threshold shell bound
    atom_subset_piece
    (positiveInterfaceBaseLocalPos eta hm)
    (monotone_positiveInterfaceScreenedFiber eta hm hk threshold shell bound)
    transition_covered 0
    (fun cap _hcap b ↦
      positiveInterfaceWindowRatio_inter_base eta harithmetic hactive cap b)

end

end Erdos1165.HLOZPositiveInterfaceTruncatedSharpTail
