/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingAssertion822InessentialBoundary
import ErdosProblems.Erdos599.GroundingPreStoppedFirstFragmentBlockabilitySplit

/-!
# Removing nonessential boundary points from the pre-stopped failure seam

If the complete literal boundary is a reachability antichain and is rooted
from the whole original source, any nonessential boundary point already gives
Assertion 8.22.  Therefore a reserved-source root obstruction only needs
construction-specific repair when its displayed boundary point is essential.

The only additional honest root leaf is stronger and simpler: a boundary
point with no root even from the whole source.  This file exposes that leaf
explicitly rather than incorrectly trying to apply the inessential-boundary
compiler to an unrooted hanging first fragment.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open GroundingRootedReachabilityWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- A reserved-source root obstruction whose exact literal boundary point is
essential.  Nonessential points are discharged by the source-faithful
compiler before this structure is produced. -/
structure Assertion822EssentialReservedRootObstruction
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) where
  obstruction : L.Assertion822PreStoppedRootObstruction hL S R
  boundary_essential : obstruction.boundary ∈ Gamma.essential
    (GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut)

/-- The stronger residual root failure: no original source reaches the
displayed literal boundary point. -/
structure Assertion822WholeSourceRootObstruction
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) where
  boundary : V
  boundary_mem : boundary ∈
    GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut
  not_rooted : ¬ ∃ a ∈ Gamma.source,
    Relation.ReflTransGen
      (fun x y ↦
        (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
      a boundary

/-- Total pre-stopped reduction after applying the nonessential-boundary
compiler.  The root alternatives are now either essential with respect to
the exact separator, or genuinely unrooted from the whole source. -/
theorem assertion822Output_or_preStoppedEssentialObstruction
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      Nonempty (L.Assertion822EssentialReservedRootObstruction hL S R) ∨
      Nonempty (L.Assertion822WholeSourceRootObstruction hL S R) ∨
      Nonempty (L.Assertion822PreStoppedBoundaryObstruction hL S R) := by
  classical
  let B := GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut
  let E := L.assertion822ReservedPreStoppedEdges hL S R
  by_cases hroot : ∀ b ∈ B, ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b
  · by_cases hanti : IsReachabilityAntichain E B
    · by_cases hessential : B ⊆ Gamma.essential B
      · by_cases hreserved : ∀ b ∈ B,
          ∃ a ∈ Gamma.source \ {R.record.initial},
            Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b
        · exact Or.inl
            (L.assertion822Output_of_preStoppedRootedGeometry
              hL S R hanti hreserved)
        · right
          left
          push_neg at hreserved
          obtain ⟨b, hb, hbnot⟩ := hreserved
          exact ⟨{
            obstruction := {
              boundary := b
              boundary_mem := hb
              not_rooted := by
                rintro ⟨a, ha, hab⟩
                exact hbnot a ha hab }
            boundary_essential := hessential hb }⟩
      · obtain ⟨b, hb, hbnot⟩ := Set.not_subset.mp hessential
        exact Or.inl
          (L.assertion822Output_of_preStoppedInessentialBoundaryGeometry
            hL S R hanti hroot b hb hbnot)
    · right
      right
      right
      by_contra hnone
      apply hanti
      intro b hb c hc hbc
      by_contra hne
      exact hnone ⟨{
        earlier := b
        later := c
        earlier_mem := hb
        later_mem := hc
        distinct := hne
        reaches := hbc }⟩
  · right
    right
    left
    push_neg at hroot
    obtain ⟨b, hb, hbnot⟩ := hroot
    exact ⟨{
      boundary := b
      boundary_mem := hb
      not_rooted := by
        rintro ⟨a, ha, hab⟩
        exact hbnot a ha hab }⟩

/-- Public compiler whose reserved-source repair callback only sees an
essential boundary point.  The sole new root callback is the exact stronger
failure of whole-source reachability. -/
theorem assertion822Output_or_hindrance_of_preStoppedEssentialRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairEssential : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822EssentialReservedRootObstruction hL S R),
      O.obstruction.FirstFragmentBlockabilityRootFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairWholeSource : ∀ (R : L.UnusedGroundedRecord hL S),
      L.Assertion822WholeSourceRootObstruction hL S R →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R),
      O.FiniteSinkReducedTerminalFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  let chooseR := Classical.choice (L.exists_unusedGroundedRecord hL S)
  rcases L.assertion822Output_or_preStoppedEssentialObstruction
      hL S chooseR with houtput | hessential | hwhole | hboundary
  · exact Or.inl houtput
  · exact Or.inr (repairEssential chooseR hessential.some
      hessential.some.obstruction.firstFragmentBlockabilityRootFailureOutcome)
  · exact Or.inr (repairWholeSource chooseR hwhole.some)
  · exact Or.inr (repairBoundary chooseR hboundary.some
      hboundary.some.finiteSinkReducedTerminalFailureOutcome)

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_preStoppedEssentialObstruction
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedEssentialRepairs
