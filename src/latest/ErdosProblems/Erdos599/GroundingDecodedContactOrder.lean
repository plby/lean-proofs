/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingErasedSwitchRelation
import ErdosProblems.Erdos599.GroundingSelectedContactOrder

/-!
# Order of decoded old-gadget contacts

The decoded vertex carrier of an auxiliary route also contains vertices
represented by edge and proxy gadgets.  Assertion 8.21 applies directly at
the literal old-gadget contacts of the route.  This file isolates that exact
contact class, records its inclusion in the decoded carrier, and packages the
order conclusion for the strongly selected route.

The request apex is excluded because every normalized request route ends at
that cut vertex.  The order argument instead uses the cut-avoiding first-hit
prefix supplied by `GroundingSelectedContactOrder`.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace GroundingDecodedContactOrder

open DirectedPath
open PopularGroundingBridge
open PopularAuxiliary.Input

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- Original vertices whose literal old gadgets occur on an auxiliary
route.  This is the part of `decodedVertexCarrier` to which Assertion 8.21
can be applied without a separate gadget-classification argument. -/
def oldGadgetContacts (L : PopularAuxiliary.Input Gamma I)
    (p : FinitePath L.lambda.graph) : Set V :=
  {x | (LambdaVertex.old x : L.LV) ∈ p.support}

/-- Every literal old-gadget contact is represented by the route's decoded
vertex carrier. -/
theorem oldGadgetContacts_subset_decodedVertexCarrier
    (L : PopularAuxiliary.Input Gamma I)
    (p : FinitePath L.lambda.graph) :
    oldGadgetContacts L p ⊆ L.decodedVertexCarrier p := by
  intro x hx
  apply L.gadgetCarrier_subset_decodedVertexCarrier p hx
  simp [gadgetCarrier]

/-- The off-apex old-gadget contacts of a route with a distinguished
terminal gadget. -/
def offApexOldGadgetContacts (L : PopularAuxiliary.Input Gamma I)
    (p : FinitePath L.lambda.graph) (apex : L.LV) : Set V :=
  {x | (LambdaVertex.old x : L.LV) ∈ p.support ∧
    (LambdaVertex.old x : L.LV) ≠ apex}

theorem offApexOldGadgetContacts_subset_oldGadgetContacts
    (L : PopularAuxiliary.Input Gamma I)
    (p : FinitePath L.lambda.graph) (apex : L.LV) :
    offApexOldGadgetContacts L p apex ⊆ oldGadgetContacts L p := by
  intro x hx
  exact hx.1

theorem offApexOldGadgetContacts_subset_decodedVertexCarrier
    (L : PopularAuxiliary.Input Gamma I)
    (p : FinitePath L.lambda.graph) (apex : L.LV) :
    offApexOldGadgetContacts L p apex ⊆ L.decodedVertexCarrier p :=
  (offApexOldGadgetContacts_subset_oldGadgetContacts L p apex).trans
    (oldGadgetContacts_subset_decodedVertexCarrier L p)

/-- The contacts between a fragment and the off-apex old-gadget part of a
decoded auxiliary route. -/
def offApexOldFragmentContacts (L : PopularAuxiliary.Input Gamma I)
    (p : FinitePath L.lambda.graph) (apex : L.LV) (P : L.Fragment) : Set V :=
  offApexOldGadgetContacts L p apex ∩ P.path.support

/-- Exact Assertion 8.21 order bound for every off-apex old-gadget contact
between a normalized request route and a blockable retained fragment. -/
theorem normalizedRoute_fragmentContact_beforeEq_blockingPoint
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)
    (r : Request L S.cut)
    {p : FinitePath L.lambda.graph}
    (hp : p ∈ (GroundingAssembly.normalizedRequestFan S K r).paths)
    (P : L.Fragment) (hP : P ∈ GroundingCut.G0 L S.cut)
    (hblockable : GroundingCut.IsBlockable L S.cut P)
    {x : V}
    (hx : x ∈ offApexOldFragmentContacts L p (requestAuxVertex r) P) :
    GroundingCut.BeforeEq P.path x
      (GroundingCut.blockingPoint L S.cut P) := by
  exact GroundingSelectedContactOrder.normalizedRoute_contact_beforeEq_blockingPoint
    S K r hp P hP hblockable hx.1.1 hx.2 hx.1.2

/-- Exact Assertion 8.21 order bound for every off-apex old-gadget contact
between a strongly selected request route and a blockable `G0` fragment. -/
theorem strongSelectedPath_fragmentContact_beforeEq_blockingPoint
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (r : Request L S.cut)
    (P : L.Fragment) (hP : P ∈ GroundingCut.G0 L S.cut)
    (hblockable : GroundingCut.IsBlockable L S.cut P)
    {x : V}
    (hx : x ∈ offApexOldFragmentContacts L
      (GroundingSimultaneousDecode.strongSelectedPath U S K r)
      (requestAuxVertex r) P) :
    GroundingCut.BeforeEq P.path x
      (GroundingCut.blockingPoint L S.cut P) := by
  exact GroundingSelectedContactOrder.strongSelectedPath_contact_beforeEq_blockingPoint
    S K r P hP hblockable hx.1.1 hx.2 hx.1.2

end GroundingDecodedContactOrder
end Erdos599
