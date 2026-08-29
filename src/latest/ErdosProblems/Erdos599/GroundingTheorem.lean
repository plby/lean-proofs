/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAssertion818Decoder
import ErdosProblems.Erdos599.GroundingFinalAssembly
import ErdosProblems.Erdos599.GroundingStoppedRootObstructionCases
import ErdosProblems.Erdos599.GroundingStrongTargetSwitch
import ErdosProblems.Erdos599.GroundingTargetPureDichotomy
import ErdosProblems.Erdos599.GroundingTargetPureEqualExceptional

/-!
# The grounding theorem

This file assembles the unconditional finite decoder of Assertion 8.18 and
the simultaneous switched warp of Assertion 8.22.  It is kept independent
of the regular-cardinal extension argument so that both the regular and
halfway constructions can consume the grounding conclusion.
-/

noncomputable section

namespace Erdos599
namespace DWeb

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-- A completed Assertion 8.22 output over a popular auxiliary separator
already yields an ordinary hindrance.  All separation geometry in this
statement is discharged by the unconditional Assertion 8.18 decoder. -/
theorem exists_hindrance_of_popularAuxiliarySeparator
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (O : GroundingFinalAssembly.Assertion822Output
      (L.popularAuxiliaryInput hL.legal) S.cut) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  exact O.exists_hindrance S.separates
    (GroundingAssertion818Decoder.terminalCut_isSeparator L hL.legal)
    (GroundingAssertion818Decoder.finiteDescentDecoder
      L hL.legal S.cut S.separates)

/-- Exact integration boundary for the two whole-family switches.  The
target-strong branch is normalized to a stationary same-index subwarp; the
separator branch is discharged by Assertions 8.18 and 8.22.  Thus the two
premises below are precisely the remaining whole-family realization
theorems, with no chronology or local collision hypotheses exposed. -/
theorem exists_hindrance_of_equalSwitch_and_assertion822
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (equalSwitch : ∀
      (P : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target),
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source) →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (assertion822 : ∀
      S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL),
      Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut)) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  rcases L.popularAuxiliary_equal_or_separator_targetPure hL with
      ⟨P, hP⟩ | hS
  · exact equalSwitch P hP
  · exact L.exists_hindrance_of_popularAuxiliarySeparator
      hL hS.some (assertion822 hS.some).some

/-- Structure-valued form of the exact final integration boundary.  This
version is convenient for the construction modules: the equal branch supplies
its literal simultaneous-switch realization, while the separator branch
supplies the literal Assertion 8.22 warp.  No geometric consequence of either
structure is repeated as a premise. -/
theorem exists_hindrance_of_strongTargetSwitch_and_assertion822
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (strongTargetSwitch : ∀
      (P : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target),
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source) →
      Nonempty (L.StrongTargetSwitch hL P))
    (assertion822 : ∀
      S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL),
      Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut)) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.exists_hindrance_of_equalSwitch_and_assertion822 hL
  · intro P hP
    exact (strongTargetSwitch P hP).some.exists_hindrance_of_stationary_equalSubwarp hP
  · exact assertion822

/-- Witness-preserving form of the final integration boundary.  The
strong-target constructor receives the target-purity certificate produced by
first-target normalization; this is the chronology invariant needed by a
sound simultaneous decoder and must not be reconstructed from an arbitrary
target warp. -/
theorem exists_hindrance_of_targetPureStrongTargetSwitch_and_assertion822
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (strongTargetSwitch : ∀
      (P : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target),
      (∀ p (hp : p ∈ P.paths),
        (L.popularAuxiliaryInput hL.legal).IsTargetPure p) →
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source) →
      Nonempty (L.StrongTargetSwitch hL P))
    (assertion822 : ∀
      S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL),
      Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut)) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  rcases L.popularAuxiliary_targetPure_equal_or_separator hL with
      ⟨P, hPpure, hPstat⟩ | hS
  · exact (strongTargetSwitch P hPpure hPstat).some
      |>.exists_hindrance_of_stationary_equalSubwarp hPstat
  · exact L.exists_hindrance_of_popularAuxiliarySeparator
      hL hS.some (assertion822 hS.some).some

/-- Source-faithful final integration boundary for the equal-index branch.
The whole-family grounding constructor receives the actual first-target
normalized warp, its target-purity certificate, and the stationarity of its
equal-index subwarp.  These data must not be collapsed to mere stationarity
of `exceptionalStages`: that set-valued consequence forgets the routes which
perform the grounding switch and, in the strong-target branch, no popular
separator is available.

The second premise is used only in the complementary separator branch. -/
theorem exists_hindrance_of_targetPureEqualGrounding_and_assertion822
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (equalGrounding : ∀
      (P : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target),
      (∀ p (hp : p ∈ P.paths),
        (L.popularAuxiliaryInput hL.legal).IsTargetPure p) →
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source) →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (assertion822 : ∀
      S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL),
      Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut)) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  rcases L.popularAuxiliary_targetPure_equal_or_separator hL with
      ⟨P, hPpure, hPstat⟩ | hS
  · exact equalGrounding P hPpure hPstat
  · exact L.exists_hindrance_of_popularAuxiliarySeparator
      hL hS.some (assertion822 hS.some).some

/-- Direct-hindrance variant of the source-faithful final integration
boundary.  A separator-specific repair is not required to manufacture an
`Assertion822Output` when it already finds an ambient hindrance.  This is
particularly useful for the finite-source duplicate exchange: the clean
case can still return the literal Assertion 8.22 object, while an
exceptional duplicate may close the theorem immediately.

No geometry is weakened here.  In the output branch we use exactly the
same Assertion 8.18/8.22 assembly as above; the other branch already is the
desired conclusion. -/
theorem exists_hindrance_of_targetPureEqualGrounding_and_assertion822_or_hindrance
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (equalGrounding : ∀
      (P : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target),
      (∀ p (hp : p ∈ P.paths),
        (L.popularAuxiliaryInput hL.legal).IsTargetPure p) →
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source) →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (separatorGrounding : ∀
      S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL),
      Nonempty (GroundingFinalAssembly.Assertion822Output
          (L.popularAuxiliaryInput hL.legal) S.cut) ∨
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  rcases L.popularAuxiliary_targetPure_equal_or_separator hL with
      ⟨P, hPpure, hPstat⟩ | hS
  · exact equalGrounding P hPpure hPstat
  · rcases separatorGrounding hS.some with houtput | hhindrance
    · exact L.exists_hindrance_of_popularAuxiliarySeparator
        hL hS.some houtput.some
    · exact hhindrance

/-- Construction-level form of the final grounding reduction.  The equal
branch receives the stationary first-target-normalized family.  In the
separator branch, the simultaneous switch is stopped at the complete
literal boundary `BB`; all relation geometry is then automatic, and a
failure of Assertion 8.22 is classified into exactly one of the three
source-faithful boundary cases.

This theorem is the preferred public integration boundary while the three
exchange arguments are proved: it exposes neither a false global antichain
hypothesis nor an unstructured reachability callback. -/
theorem exists_hindrance_of_targetPureEqualGrounding_and_stoppedRootCaseRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (equalGrounding : ∀
      (P : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target),
      (∀ p (hp : p ∈ P.paths),
        (L.popularAuxiliaryInput hL.legal).IsTargetPure p) →
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source) →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairFinite : ∀
      (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
      (R : L.UnusedGroundedRecord hL S)
      (o : L.Assertion822StoppedRootObstruction hL S R),
      o.boundary ∈ (L.popularAuxiliaryInput hL.legal).finiteSource →
      (PopularAuxiliary.Input.LambdaVertex.old o.boundary :
        (L.popularAuxiliaryInput hL.legal).LV) ∈ S.cut →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairControl : ∀
      (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
      (R : L.UnusedGroundedRecord hL S)
      (o : L.Assertion822StoppedRootObstruction hL S R)
      (c : GroundingErasedDecode.ControlRequest
        (L.popularAuxiliaryInput hL.legal) S.cut),
      c.1 = o.boundary →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBlocking : ∀
      (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
      (R : L.UnusedGroundedRecord hL S)
      (o : L.Assertion822StoppedRootObstruction hL S R)
      (P : (L.popularAuxiliaryInput hL.legal).Fragment),
      P ∈ GroundingCut.G0
        (L.popularAuxiliaryInput hL.legal) S.cut →
      GroundingCut.IsBlockable
        (L.popularAuxiliaryInput hL.legal) S.cut P →
      GroundingCut.blockingPoint
        (L.popularAuxiliaryInput hL.legal) S.cut P = o.boundary →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.exists_hindrance_of_targetPureEqualGrounding_and_assertion822_or_hindrance
    hL equalGrounding
  intro S
  exact L.assertion822Output_or_hindrance_of_stoppedRootCaseRepairs hL S
    (repairFinite S) (repairControl S) (repairBlocking S)

/-- Source-faithful pre-stopped exchange interface.  Unlike the complete-
boundary-stopped variant above, the underlying simultaneous relation keeps
all selected forward continuations.  Its only two failure certificates are
therefore the genuine construction obligations: an unrooted literal
boundary component, or two ordered distinct literal-boundary points in one
component.  A repair may modify that component or return a hindrance
directly.

This is the shortest sound final interface for the separator branch: the
finite-source private decoded exchange and the selected-route ownership
exchange both target these two certificates. -/
theorem exists_hindrance_of_targetPureEqualGrounding_and_preStoppedRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (equalGrounding : ∀
      (P : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target),
      (∀ p (hp : p ∈ P.paths),
        (L.popularAuxiliaryInput hL.legal).IsTargetPure p) →
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source) →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairRoot : ∀
      (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
      (R : L.UnusedGroundedRecord hL S),
      L.Assertion822PreStoppedRootObstruction hL S R →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀
      (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
      (R : L.UnusedGroundedRecord hL S),
      L.Assertion822PreStoppedBoundaryObstruction hL S R →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.exists_hindrance_of_targetPureEqualGrounding_and_assertion822_or_hindrance
    hL equalGrounding
  intro S
  exact L.assertion822Output_or_hindrance_of_preStoppedRepairs' hL S
    (repairRoot S) (repairBoundary S)

/-- Sound final integration boundary which does not assume an all-seed
strong-target switch.  Such a switch is not derivable merely from auxiliary
warp disjointness and can fail in the presence of seed collisions.
First-target normalization turns the non-separator branch into a stationary
family of genuinely successor-new records.  The first premise is therefore
precisely the remaining
whole-family grounding theorem for that stationary family; the separator
branch is the literal Assertion 8.22 output consumed with Assertion 8.18.

Unlike the all-seed `StrongTargetSwitch` interface, this theorem does not
require every member of an unthinned equal family to survive one simultaneous
relation. -/
theorem exists_hindrance_of_freshGrounding_and_assertion822
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (freshGrounding :
      Stationary.IsStationaryBelow kappa L.freshInessentialRecordStages →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (assertion822 : ∀
      S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL),
      Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut)) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  rcases L.popularAuxiliary_fresh_or_separator_targetPure hL with
      hfresh | hS
  · exact freshGrounding hfresh
  · exact L.exists_hindrance_of_popularAuxiliarySeparator
      hL hS.some (assertion822 hS.some).some

end KappaLadder
end DWeb
end Erdos599
